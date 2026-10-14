-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3429
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:37:57.25917+00:00
-- url     : https://prove2.me/submissions/fa22e4bf-52df-4054-a643-6fdb7ce82443

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 616546762 ≤ n < 616726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 616548012 1250 616546762 616546781
    0x120f100606030e120d051e09060604180c2309010e0109060f032001050d05070905030c01051317010e030d090519030f080c0d23100b0406081005120d03 66
    0x102000008801c000c4e4180c411100141d0b102a9154081020528200e0201101805084161600341800d050761030311024241c1e5060b12851410419907120b8054101c0c2620483d0440d260341c0e00c2c54909061a0780c4481c80484070584503403000d20b5501d041d40e4240005001e0090440d172100e540d81480d802400b01c5645402051008118031350400c001900110b209507000d01c1550100c0c0d8041c020001620365015005010707c00a0901c0c04003e81160320a0580040700c000310129040c050b5040015070b681e200d000d40d100f01600055000307015040c2a00750f102d0088111500020798490358441c85030444c1c021040c0d50348c0031034075600407600388101080b605502c8003603418030507003001541d900a4007044200c0c0c4084240b12143c0300040004640310203032605200d0787c0c40142700401c103041b20454070a20181409060040d0f030400b141230000380320446020740d508204560700e4242001025914520024050380c0982d40e0040b0209103a10341090403038800040d18014141101c81140180540d990f0b80c0b0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 616549262 1250 616548012 616548041
    0x11030f060f0a03082a0c01030c1134080a0c05040c120b011211070b0f070503011a2a0f010b030706030b041118030f120702120f10060603 60
    0x300c0009850b03031058016030031260301c6a842a60f40418580902c5040ba140c10041d440303145a05107641250341c0401c0f01145c2c0c020907601005900c402000903604210904880c40305ca40c08010310b40400308030180000c07611030081546007650000401f10140c84207032900580c440d40c20151800b4204921603004070058441240c003071101407050f540003000000040070b00030b449034070b078440c0e842241d0240d003200d03251034640c84041c407540019910840050340700d0f0f03104403401140080012001c5944401003170041c103080d66039a28503460f0040c00d10548581110401ca4500d0030401403a840c004800028a004000320380007883c20046106036090101b0741140485690604005040d990380101c0e1b01030a0b070740036040001d80b46c601e40020500800c0d08840c50310b1034070740008074007151500c0c07840c003140c1e080c8048048030261418040c0341a11240b2100030340b640d5842c00c3c00300600514048120b001821b074a181201c4903401200d01c560324021099002d801540d076030703038414040c0da640b40c001c1d08018075096 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 616550512 1250 616549262 616549279
    0x40609020a110607080a0c0e1302041a0702030c0105210f06040c0c050616050706020c01020414100c020f041103040308090105010504060602070e0408160507093803010f11030f06 78
    0x40000761242c040240034a01140d40c45d034080c47c034980156501c004400d0050501400c1d81c84040018000754494006d015840402d100b00744855002d0400312069198041c020384039030a44000155120380022422680381c04102c0c3c1e15090390041d951704144100240c40d062155420003009005c1241c074a4070107a020081038880d80c60200b03600081103900314030310901a074024200204121080e001d0030400400e013600008844284d440d054010b0f2041d551502d640c041000032140c1000400755015005901040d4840c2d0080094a0441003001003120043d2010506880d408500c4680754001c880840114a0500900490f80c0091248901400060300c0c02c00060741002400781d40c8500c5d81c464003a000007400000390030000c018003940d05200e0301901403c46200b05243c000d48881030303400360b4000c60b85002c0358030340c104400540111009407038848880703910802c0d610a01030440c942540030740540d00c41002c0c0e200f42105100e2020400c1000c0e4010f5100d00f801000c84003101806004e83d44076115a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 616551762 1250 616550512 616550521
    0x150f06011106060d020103020f04060c0b0a06060f050c070b0301031b0504180b04020604050d0f05061501090311150313050f060f0c03040614010f062309100905040609020a1106 77
    0x9032180c2143d4203e403013012142e514401200680702d640d903200080a00814001030a5400900d007809451003803020513010342d5903a145504031b0303005125502c0052581d44440c1182070051008001c0c1c0b4400d902039800d400e8071521040450b620a034402c66495445d502e020f03990400ba0030307000001d0f060842c0d00380880d02850303582c0140001c500d0006030800e901c0300c01003000c66807804211001080080e140c2203100e002e904291b110070015501c10b039003500400300001d40004420034404500d00d0140c4903880c40605640b901030301c200b170454240750030503100c240080080410b80080d510400c1e10000c26000384445185c0a41000134110300c00c4c10a0f0310180c10b0082c8035000c02d61140e40302d0a00c01c0c0c081c2d220f5a8904100f40503281c0c2250401600300101c0001c64100405c035a24025280291a50300304032850f070f03003040300340543ca00980d0758418041c42041e50502d4040304004d9004154074043c40c0c038503294000201101c065500c141d03034807a400207103800c14940084010700c08907142c1011300b800d80751 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 616553012 1250 616551762 616551797
    0x1217010f0e1509072006090a0b0903090a0b09010c17091e09180a1e110904020906060c01150f030308010f06080105131410060e150417010e150f0601 65
    0x101034982c0713081c45516102c48440b0f8103100741d100540e422100444800d41081402e450302c401110070141e0b5015034010000d500e140002045035481d80024243c08102e0340f034594901807a80001c10b9160400142011100205002090150f100c03001d02c90659550138103101041401f007030020794035034802103280d2007806a6850300315896020404c10150141000700710070440c10300901181c001e02c0c01000c0c5000314403041e00d8191001760140b05a0210030420001410062010012540250f1082c1020002600c500744040546029480140041207558000c11054010885d5400418090010032020024190b20445040c01803140f00d0659005030700b031003002000c01c48140100f9004a0607080402c4804400364031020081800c8145c511003400e21a00b0b125030f00440344102c00000e40c1c040c08008680c070b40300c2410415138141c02030b145c0c0342c5442c0200101145600400c02c100729507884100c101317000c2081c4869400075584108140a40c90401c40224082801503c114104008004040307460035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 616554262 1250 616553012 616553029
    0x30a0e150619061e0c0c03050703110901081c1e11060c03010503060c0c10091406100803071b0f0b040806160c061a040f061802090a031217010f0e15 65
    0xc00c3e084240c03200e60344410303003602c90540c5004006c14003284104000107000d40403d408050340d01c26200c034585250000100309402d00f0a0090180d2a04082c80c00200d18050641002c0c480f50345080001a8000f86400070094045003e0301e8000705000c0405500f040005000e550782c821800020a41154140000300b51381e00c0c0c0040005900c007000083d80222060104008120540744130001d00035903116141110f40585581da0b4000036100707101c0490007c400c0d036101c1c00c080e5002da8005609145031070b120080060324480c2c480310720851003c40410b202280b0b8200d80050004060761550380c514041003546004001000680301c000c810020000c2180d110007603c003015001100404cae4025141070500c400c114800f44a50300910380344040542000541040045500f840e80c50310700f1144600200069214402e0300700d03800480c074002800040e0503104003c4c840151441d126516182c01c0c2c080700c0301c5050a80152901c1000c1a03020403000991010140d4846035160241c1176910034035005c15600c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 616555512 1250 616554262 616554287
    0x30201180317040602040e070f020d0c080315040f0207050a12080106020d1409030f0c030c090411040e0304030506130b01053f01020f2a070b030a0e15061906 69
    0x40040b01180c04d210080d015103000d481f14016548890820350000b0300001c0aa08072000580590f503400100c0c1030082100c401481d402c0400030780743d51740b9241e501c4480300701c030f40c12281c0c810b0f522905854502211300c050044540f24000030200840241030a00b120340422030701404001c1d00354010b01506a0100d101c2041c060340b400c1200d1900700042c400343c120f00039051015003610400c0e000390485130380064802a801000d805032006001c3c243c051184c0a241118007900c20f8440440302d641c1400d0541c003454500070704800340c030305258481d56200c0c1071140642c3c0519040c501c407418401030010704a1003e0050204440359110b184413040c0700028520f000c0030346503c0005542000e40803040e41c00b0710508880d10200210750312100d200725018190045508881208086d1550048441d020b030036607011540500d0003049518a4501e6480b981c0e07000804083d03440382c444122408064040088140c40941c06c5141c00342840c14030b00f404a80d404880e44005001c0440c0310400869803c00360b4803202 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 616556762 1250 616555512 616555547
    0x15180609130504051c140f070201020708060a1b050403050c0f190303110c01020111040e1f15030c050322050c0901182f0703140301060504030302011803 67
    0x44901400025290507184480d448081e818002044104003000c521015040c02010410080800342d0008407101150115240d660080800035011a144c4020140c0030380d52051044a10761500d9001b52410001c0aa414941c1c0e01c0e2218072805415100322945980d44a241c5089400c0034907503110700d542e85404c0c1031240d0142c0011140145961900454503d80005a441c02c241481e038078600100300c041c603000c050f15180105000c20200750300c11b010302081b070000c509138175040c142410721091426102503c0f9040855003151a0300c4005031142d400b10051440541141005942c8003001d070903110941d40d070004000040003000004490300d48440002c00c0d0158180a800c09503140c01461300d02c040d6080c07a030000306000006810302550110302d140e0840c0d8082442003a041554183c021a1801c01703880c4602e2101d4010000c1c00c14a101520762180a49419140d82002c0c0b030110049520a80001000442c0041c3c180280758090080305803041c9180d01641100c207403920000d1000d1000782000d241d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 616558012 1250 616556762 616556767
    0xb0c07030309271806020c030a0e030106030b0601200a060c030e0109080417030c010513020111031911161806050f0a03020907140301060e18070207050f0102030d0204090b151806 78
    0x5010801c1401040d00e80d6100d20115607e807600541d9070303500c3d000768603428005010b02003520790a042c1801220201d0350b018a00780900d899400054507603001c0b40e214403885850700c0140e0b011460302000040c01c50350180c4000503022144140c000c0c01e40315181c0901c000b507810400980c0000f010641141c0c11036a45400100300810030004c401e00314800c40205d03800e10341c00e2505006200115840c20f2111728400d0321070204030b0512041c8551070f402444980782ea1004d0f220203044a06e40141000003201900720180e0b000c0110031000740b1103001540c0c001a101c0d44d40c064404061240522850025040c01c441d414030500701e40c400203036084118000203000e10036407004125290f0003100c05038224010724070300c15129a142c0d1401070908081e203241d0b500c070b1a074040308045d00301c1151307140350300540b203982c00380c2103290501041c0004011403905486c11803204000d032550025007403000d0000b52910311001b1422040240401c11017407a26070042c001c0c480208103c1103101c0b004842040810000c0d100c064 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 616559262 1250 616558012 616558031
    0x3020c0703021011100e0c0307060f0305060406031202070314160b070c05090415230703110408151008030c0303010e1005220c03020307091e0b0c0703030927 69
    0x32003504002032140035074400c4485d081c5040f602c82e00421001d40441080b6107a000745942050341d141c14034820400422166013200e0443d40c840d03004a80c0c801c0c0080e0010510964a9a400e83d406540000000040c5c00581742441040840c0c03420b00000c46251006109000308201c2c0c42003001801d10a1025402c800a461401c01007044400c000030640201009074500d0241402e41c88007440f80c4917521390303038a040030a2400c0481031304205408504594a803030342d95600e000170f4009046c03841014400100501c00003034001c2040200c0c1c13002410b20540c00c80c860526140400426020780c1140c1101c1e00181720140c05000c0000550341190f4030340c1016400d644500c0c1d0110713100503845c2c20071a008000c5101c00c6401c1e10300c1403800c001c40b06240c0000c01030035500344002c6007203000c259401d00000b052044108000c4010003001c031a040d071031001500c0c1d074541e16102022700d0f600a000c1d0055680042904006254000030084002c1036856460450381d0107843c680030b01403c146083c140100d035110180c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 616560512 1250 616559262 616559267
    0x31101110c01050a031a06040305254403040503010515060307081902040608160c26120a05040c0e0c0904240620010605090a02070317042103020c07030210 68
    0x501b40c501814442d540e03070300c9040ca1921202100c0320001c04004040000500c4910044507130120b50451409800c28480200c001d00209094041007400607520680080c22411984601041e2007507940150744e601c0c47e08051509540d0000c05001c1b485825000c40300b05915a2030813241e1001d000d04e03003003e940d9100d410080c40312001f01c0f40004000e03c00310b000302c1c8a50300411018060b10440e5400300c0d445030803940031280325019030b0004090100c152540c2c0000340300b8100301000c08618220f194204400d0a1010100c280c040f41c0c0d90741c48544800500c8144512851281c003d000e180348065006c1c5425107400f0800e2007403e5655000d07607580c0701907001300030071096100b003038015500d00000c4442c0e41e1a4014644802031000300c80c01c01540108910083d01407052200700d900240c0000a01e9942840c600300a4202e8101070302444904582800414038480010780300e03520a1200c21008000417450400a500740603c031821b0610402c28010608400207a4a0480754100d0303020001e2403c104c0704 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 616561762 1250 616560512 616560551
    0x5040c050c0d11190f060615020703030302091c0f060506100f14091f03050105040c140711090a09030f05040e0411241e0f0f0d060f031101110c01050a03 67
    0x7180d41c500c10844c50071003088030403182290414003c034824854641c0b500045241030b900c0c507003108003592200700204006030290f0050200500d00904400354103403001000282e4050818044a0484105c117801c0100300b800e10400b9002801961952200c00000c06d014100c000d65503400818051500b00500c960700341a8101c404500018241d032100902c40010310b1070b4050340b00142c0c0082810309001003501d040a104078480000d5540da0360355000e01c50710b04a0090b90040f1030640b40810102d400b80440c3e210302031f8090148104000024060900d0f050003440342450030b400d1010000d040008200e0800035042d0703a40c202e600914520402810000002d100480c00c08808803104114000303841002000d034090b00070000f5150021806a080391800b035000c0c40303010400882c000307061140d40c03801440b40c406030006840c5c400780000c0e515100e01004003a14050b920459442c5441d5030003d1842d40c0c0101c84000861102005000c1d201c85180040c3c4103014601030758041507541c071580700d080000300d83e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 616563012 1250 616561762 616561783
    0xa0b0307050d1a060705010b01030e06161d040e24010b0703110a0b10050a0f0f0b031008060a0222050a0603020c070f0314210702040b12070f05040c050c0d11 69
    0x110302d0350780320503107006c50282a0941c991400b003442d01201c08245031010440d0317881840c6140d002001810650010b4454100c086402448619403404051050701c1d18840c01c800340700d83c20000e1449c000090207a07005040003503120302640085800400c00d04184d40191141c9541c0f40c2041c824090001d00380c14508100c02d00c0c0605460010418801078020030003041c0240ca10643d1200d940383d45601c074480d10445284a09290190071000030014500035030003554005003402421704140c1d5845800c50314140003682c0081c222307076001400c60303003002c00c1401d1070b1132080a5007015030304075207002c000569078421307445210103040e00000d6542c0202000d11a13100a008078148440059481c2c0c202100e80300c0c0c043c40580014414500c4043c144207036400b2810180c00c1851480e4a0051580e081c480541129103055810911048006500d03202c18440d500140c482c070b82c2600403180c50642000142c0b54418401c4c1c0a00c04108021200c0d003102091601c031030022401c0c130250070680115010f140018008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 616564262 1250 616563012 616563019
    0xd1e200f04032a1e060804050307060e0f0a0b010510110606040c030209060408060711070e07051317060402010201060510050f18130b0a0510020312040c12050c0a0b0307050d1a 77
    0x540820f40480d8642d0721080a020001e500110300d031a01802d40c1e446e0741c04d5130090328a6000780030500009269801070022181d02e01d013690140814514858900303280c0010444410f03280600500450400c00c414600490003403034000407803804000001e445d10005008a03015a0302c0b8464030305114000e0701101d003203060140c105580e95649079019500d8582c140c0d21200041c1c603154210f21030040014160082d00c505c07900c0341c0e5031500d81c024107071401d500c0708605904101801c0e00011340c0c0e403074090380307425076030398240107030041d840d00d40b00081c2124540d400403881105800061411640c0c0442602c40c68080d00d900281d89003442a81c81d82c8114900303840701c1d44401c824000340c010510702d81082c0418082610b2032920161204200403107481202c6850005074018840c0a514090034005250405d02400d20590020b8581e21440109121355809440c9030b0700408011002d0b00b00480c5480061040c0b80d4120f00f14141804002c14074818802d01050040d00c0d4112208045251490881d83d40c0005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 616565512 1250 616564262 616564343
    0x240d030314060603060616050c0a030320061005040203040609020301060f0306050115080703020702010c140c0a0801060b0a0c030e03060703050a0e07031203020d1e200f0403 76
    0x1450010003805107501c0c1d0414038450a00454880d00f0580140ca00868004040ca801c0c4405042501e010440d10741c02501c10707116003203440b190b1f0f89401d82d00b40c02640c0603658040040034841005640d0070f03a210082251a401074081241c0401c40700343d00300c1a524100c5025030f036034903141080d0300038214403c00070b90b165190507000100074603450134200843c1c0c071422040c07007140e0303031402c85100310017502d00b0400100f50f481d000602400c0c0700381e008042d103602c1410560f911001d580c440002284605a2414855002d12511850351914400c140014680000244400fa042244540749030203500c004805200d5220000da08260040d040a00c1301e1001a045448618203010002c0103003100707841c845a021320f0202243d20500010030400203803a00480c0100c440c5240c00c000303c0003588000c50402d0450b64406a036090043c840c46550160495101e002ca5a045210755840d41510300d0402000095010031004c206410300c2d40680c4d00300c0c2d400c1151842605d024641c0010000d0f0607542140181100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 616566762 1250 616565512 616565539
    0xc01020f0a1803030f0309061d100b040612080a020a080f04090605010806031b030106030b0c12010815010e07050c0d110c042013150e030111030f24 65
    0x40c80c06032944404503550900307109040038040341c5284541c000600020282c00e02c103001a070280c0c00030124140304220000342069024003a08840101117000340c410303000401590b0f0850a1805610f591180898007044180e1400121071100e110425006000010100e0501003190083c008116103c1d0401d061951781c51103017585074515442801410705082c500403020031954071444800f8480c080c050020010788510018460000da243e603100303645503494060100c00549804540c90044082c1b203007681d11001ca4010544020034142c105105940c010840500c0e1041380e044281d04542004491240c1511001401c44051140688480c40782c450901e10f01c5013103070300000d030b04c1180001c0e00a079011030541c00b042200303403031000c0041401a0b10400d00340c0c4002049900805445100e0038080c0055035543d0300c50108074190280c1140404c0b409802090903040c28001c446020716100c1143d0f02d103207002e0350b240300c050300050440031601d00c000040680c10b50034800c0103130844500402d80c0c003000301c9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 616568012 1250 616566762 616566787
    0xe0a210b0412080a02071520040b090a1413051f060513150f1202041508011701091a04060608030f0d0605060f04053a0224041a0c0102 59
    0x820008250004014800003130f681140c500c290303401117034040490800d403110180c0d081c029045400350b4446400282c0d004410a9070700b440240004c184c1410415101e215860800c406c0191581c860180c2d20340001601100356a441d408000c4e400c142c0200082c00d4584500030380c00280840b0b22400e4001000a0104003150004e0180204a42141600204584400e01c00101454411440e000302e924008410585070180d000f10002131500340006081c42d9907100c0d007040c11481c0c498a074010404100042c092a1400d144407031904803844020b204560943e500c04a20440e003411002c3c5240004007c9030030460b494201000920041d02265259421203415261070b0b0301c24009004580d251510026a506140b4169980f0500d03204002c0c0c02c041c40d09040c059506440318405108135640d68658841d0892401514409445041e114001c130302e0610504c107007403100714030b204101500d0f07044204030340c04071400303c4059482c44d580032142911030b05101d017458003c0016814440d40089a055079410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 616569262 1250 616568012 616568033
    0x706060b0d050f090d081515030a020712030908070b04060212090c0111070f050d080c0d0c1a040c1e092901090812090604091d0d0e0a210b04 62
    0xa4030b00d1040f0961241c44e6055541c40b1701e990164081b07601c3d407001906c8482c01d0700034540b0761303080500440309080c0c2014000700180e104550480382c0681c041121020301c140c2d08111009443ca078201009401d000d6101d0b014940603519000f04641c00c08000101000b100c3d4040c0d880c3c41c01c000b40303030f0780d010f0800c0c484003511190072000050000f80b5200c0d2100e00c4074000155602103030703281214408110f0805080c02044040c0d6031080e036000f4030402c0404180d000c10005850003111030303612125060300307a1400d41301d40c0040c060200f4400b06c6c07000c1404041803001549504841100b41e03a180340501c3d244003203550781003580c804c4071058034041e800700b100c614442801d42010402c01d000c0072410a084019a0240f50500a40f0010382c0715140b0701d0720416030350004050b100703002040325045c6941d4094403000d0703600961050501c2e1f02c1c0c1c10301801c00e0280400650421400c40d00700303041d00c08001d001140c6403100622030200140f0300e03500103031805090001c0304441550000781041c02c600c2c0a041c20150b0390b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 616570512 1250 616569262 616569271
    0x6030f04031d06030c031e040b0f012301030c030e01090807061805060c0703020c060d021902010e10090f0605040c030c080309090a0b01210e100605150706060b0d05 72
    0x140b250382ca000c080607480c102e08508481e0041040d03007580c44070702d100129034100600404031080002c4046000d4000b9048a61085100d0700d0140040c0ca8106074150101700181c0c050681e405001003081d01000261941c0280d840082c40d0005884100046c1200a001d1241160300e595182c4400f441c18020080700030050075010748000e202181b20124058a81511003001400680140b8003040c1d000c03543c003004111803402441100d85691b41310f8002600d0754854000c2c82849580018600a018100000b0040140c0c1c00d0000300070a502c0092126180c0d10194003035200d25503a201100104204a905800c0442e0440c104101a182c0b901c0c0600146041d07000c02d43d005140e0000020341900000b041381d20351400946090100e85683c44440d018050541c400c506000e40c48400c050008060001c00c000b5841c882404580d40c60070030000b90608001c0f20f0807144e410305010061150341c490030074844440300400645039031584503003003180080030160807215030070350001000e5010440c65000341c1d008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 616571762 1250 616570512 616570517
    0x821122e09061e0326070204061205010e07030201140a0917010e0f0d0c02060d24090b06040b19050705070e010932130609050d021504080d0504030c0206030f0403 71
    0x1412035225280d140e002140c40000c0042201035140803c14030342e04e02051700034040000143c10410103500050958032160011410780c0101d4850509128090041482860804c8050280c00d421a00020807181038180c100c010160002044152540300e6840c001c018884040f100e4004403078031104501900c0d0710b83c00c4840c91300c02e18000340843c10000c98100d60321410f548a07403c1c8400e0755820310409410094200810680d504094408040140300d0b4075544c40719284446000c03801c00c060081113a44699400b401128184010701546030b5407000c80e070118000c0110584260b0407800c007251144035801001f08180143c41d000901e0203a500441410303240e0060081c001c010201c5003040e103a0b2010301042101400c00d00c2c19101113403000c03560540000d0100c00c01034a405458450600b5650740403021503255114900b1415101d0b41032100d9684614620b55003001c0c3c1c1816203890b40329001340c02d00c040c0080c3da1074000c941018011424141083c0d40640039503140d02c1e014030001020360046030103401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 616573012 1250 616571762 616571789
    0x4050a0609060f12020928090b03060c0903010b130504030e040c120905030f070b24130e0c130e0f1f05040f020303040821122e0906 58
    0x801602441d003074019103005030345600b4405030100040f50340c080e1000c0071006482d420860700e13407079031034203061031070802482600801a200d1036100722503a42501d40c4004826440c16800a0701c41d40c0220303810b6013005c1c4400764a40c0340c0c0d00480c0000d0040c100401042d6024001200c9500485090b4200034411400dd441e44180401d1075810b21094a145400150005041c20301c01d00040e03056030300510782580164112420010410518036042c0e12181c02542c403407507240c0401070010281490315441480c80242860703050f4110000c505621160000178032030702e03224100d001c61000c0c00c01541c06131580040840380c071010382100312001800e00e10344a864038000e0760280c4640e02800298288a08072120034440d02881454901c401800c001e00704680c0b20000c0040040940e6081020300b025095510250541d802e1201d6410030162060407010741c0c0c510280546200e5180c41d20300360f9804078a1103054111054803502e040c490000d003018120341905182d50110f14548564424000d07992043c10245 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 616574262 1250 616573012 616573019
    0x71205060915100504020a11031b0f160e070309060231080618030408070e010f06031e020a0507060507110c09090d0f1407050102030604050c07050604060c09050d050304050a 76
    0x80040d00115241c034448400003d04002d2030810741d004110380502c602d40804a2500e01400340d0a581c02000074000b00e0383e80941d061a000014400da4082c120070000034400060010b001d42d81e4600c0c94072950408339202c41c0010b50301c9000b0740003202c415501c203008540d100c45100c0400c10703a10300d0035043c034520301c0300c0c511840581e00700710031b26000e03030301032800034101c6640d010728581c0d07080c032854078134032a600050000140c025020018980900304c150100b16843d03052003030f54801c03141c05030320103420541040c0d00c0c0c11070f03001d0383d000c8400540340800016954820004050390244201b41c1c0003005203161008216010398810000000b105050090301c0f12507240038100301007003400f0740e0460307220b410010401c2031050061a022807034007101d05028420040301c2900340c0325508090300aa0355031f5000000c02005103028860503910481100e419810111039442e07607540c500000304014140c80e0748400d010819802507402d80c0003804010009015a441803428603120b03041341c0b00d19030254460400c0030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 616575512 1250 616574262 616574293
    0xf0601030e060c03060307030c0e16180b090604030b0405010603050c010f021506220b01020c01030903050a032423060a020a031407080a110d02010c090501110712050609 74
    0x1030450500d001c0185407548074800c0d030012aa2000d0003c90b4984116540040000c210404440040580c80c040b1b0030145401950340b40740da00c18441100420050320f00c2e0071690034011075200240c510a2950700e4a40c10142c000c90040c0c410390308041e0112030340b90304200800c401500090309a0748034600384d465200000005640111551303c1e07800150304018001444103160400d1103a12080062030703441c00707000c4002504a41c9507000c0d41ca0b00c0c0280c80300f4446116580400043e042c40c4001c0c03804021039803164400504600511040104154542d903403100d8690a05c42c501071051100c4284054181d0340e00d1141005c1c2da41ca00c81030002e1b000b15284800d044c60014143c0344007100075009010400550346c0d0460303800e04590701141c64414180b0a100108030190060320201000340c0320345000c071b184c0c0541140303450002c2c4050070444e0b0528100086565200412500319042802c0005000e07a0801d03280742040c004d50055030400402c02c50041c240300d80095124020318000c02a03420700c00001a51 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 616576762 1250 616575512 616575521
    0x70e040f0c052715040e0d0905090f160c08040617060409120809010f0903091806030507050d030203091201051f03050a0f080c0708030901021015141f05030f060103 72
    0x744001501c6412540d50b44110000613030003400c10001102c0012841c000034121804c81110319241e5110a90a17100540c0218020010f030004079441ea120b8038114000829003a40181031090a18410b8062040180160804101d0550042d041c58450f6103500004007000e1034600c61491400c00c21020401a040030310134441d4943c1c114850319485400d2034415600344901500b00c800079980c4100a05064403280f00b00840c1d140b0940d2025a130314500303004048000d6006010004051801c2e50800024400141c0901141c0c41600d03c280b09442a0406900754007074190703015002a0310070510241e000040d48030034440c0c000c0040380001001c1030b81c04a00015041e0000030007580c0829035540118000a00c2008450b21130700b034041c030f40b180c0d4101700c509129150340003a40692010812043c19a014070001d140e00d90a00c0301040303020500085100d429000340304024140e2000302400006494201c8200c05214652140e00c0720a000628014515801259980c446c0d141c000c0103d51a503119018 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 616578012 1250 616576762 616576789
    0x1e03020301080a110a03080408010218061c1107051e0120031314160302040f0b09060d03090e15040b0904020618060903070e0a060f060818070e040f0c05 67
    0x1405800c043d0395a00d820b204980507125445001c02000000244140f0010805080b007603001503241d2201c100d02601c480b00507018244200070511507480c000c04010071000107488030b1000800c405030180e0010200d4420760401800a014103500284a480503c0e201c01150104000070030030400718940448005d00100c01c590034030035080001c156204030340355a01a2075400780e01d5400c3e002d4203c140d554035110031004100c003406c005880c10000d501e4180705059030100d1080702444004035100001e600000024503c034841c510781e440d040e041c10322840151000d00300710329030480541051282c0c40c5860070803070340340c1e8411824034a46003842d04040f01018041c65000e0051818041040c000f00d0000e1458006590060b0050101c0340140d074040007100700800d0040da00050a0034030070300c8042555490b400440074441c0001003000000d0340240c20643c402d9100384070104900c03110319a2400c2c000c9981c8145d07189021038043c00f05021b23001804105940c4145d1140b005165114244004e400364500f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 616579262 1250 616578012 616578029
    0x405120f040303080c0f07050c09010e15011103071a0910020a0e0f040f020d02040e06030f03040e0709080a0804150905030c1c12031b170c0901110604031e03020301 72
    0x101c1000002d0150810540040042080f113041000700740300e0400680002030180c8103684482503541450400072a101c1c00342003c4107004d00b8503d070070700001800c1e0701c003e80a641001010705c1141d0120505000b41c0380c9596010908682002c035010341041700c0d4105450450181c0075985400340c100710030344212400c803085070b194010f15003881010410350130030585800d904181c0358040c150441d05030384028141e5550812005850b5400d01c101c0d83c1511300001c001074080d9102c6c06520701c8014000043e2002c860300040740844a541d40b000031600b1140b00e0b070010030540f0a00e0714940800003640003074070542d20036910820502c0040b620031200054640b0640c6c1d01038000034a000e0107030500040da0748440b842d00190b10428641c070ba407082034101d03008001c0b100080e0703100302c15031030f60680500341030f418426440c103020783e4450402d000310003050141040f10b400000007094002c0f44d0080c81c0c034800a0341c1c1c05003543c89a25041c10040c0501d40c681d4524160b0317100c29040715254034000e00c20b0303a0585d00c201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 616580512 1250 616579262 616579267
    0x70807031107020409030207061103071e020a03050709020a110114160c1407050a0e07080105090a0b030d0c2f06030703060e0115030614013e060405120f 67
    0x2520540080c040054100c107518000c01005002d61a207008a4008611a5004002c81c0e403500c40b0061007807241c0746a181031500100007032004980784845d0781a0200c2510703204025104c503440020740c1c83c2200c2d8070003001d40c09114000210260f00d81d0140010318040e03101c03490610b02001d4090300f01da403000c0d20f000c1c502800381c3c00b0524081b652003030300b00500c54504140c01c1140c11a201c806440c4107038500c44030142c3c051402404a8288603061200a18481407081c2c02e80c20100400f401c009414003030203010342c10f81070000341120101d810220020402800360740308419240e13401800b0f031a010205440c2a000c1e24911040560084103500c285c03c59492030500d040c20403401c1101c42e90000c1c1403902010b4079010042040d41d1591805402441030601c410600b90031100054165a9207921002c9006142c071a46402c59070083c82c00305240410784a910149858014401e5240211800b03c180d071034800c10100f42c007400d000a000380203c1c0520200e0b01040714206603055a8410000c00040d40c01c1305 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 616581762 1250 616580512 616580521
    0x12070801031e11032d01111602011701080a03080123040b0612010f18050c04050607170a050421030203070b091906060303030e121b010f0e150f0708 65
    0x280451080314502c03c0c01d41000764000500002d183c0442004036449554044ca655000d40403440f221019101d0590001c0c4443c41e00c01c5854059030103544102d0722401d00340300100c411a88207400e400c0e1440c4454400c02c0c13695840d442050b945e0300400741c0807808199084e0010404118001d07501051400a00100c020100e8034401c0c00060300c40201c2380e07604228248070400d1000c450000c400c0c045c1c405142030407813940c80d180103e80d0502c10b50030440c0e4038520f44001d0010240c0100200da068440554031941c1d90300e000c0c81c201c460150b40310380800040b0340100700c40d024198044001d1040741c8056260300004414901d0701c0e0303903820b62003100401580c03080140100054040100b59403080040d815651f00b950800e0070780c7c05d02c6400e248101c3d029592400b05104040d05841150a1708000400410710354144111144140c401e941407540e4210750030178070301d01c4c0d00c10942003000170206446007444076400101f801c540d594101001c3c41040c00140d00010702c0070b1401c1007110721031180b959807030189469 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 616583012 1250 616581762 616581803
    0xe061f03111614190c05010e01110106061e0203030114010c0503160305030403030c020115030308090c15120115081504090f0b0f130b0103120504150201021207080103 73
    0x451540100c1c201c00c0c0502209402c42806036100300c3d0007819015a80b1030044a103c0c10003408000400000301000b020b080459540507160003543c0c803e0031703d10400c245032030040c0c40000402014082640c00d1440c0490324940c051006025183c40f98030404840c818008243c0c0c9a01003406484003c01054010008070742c466120b4040160082069900d45495650b81c210f190740c403100c05030081000001400704069040c030403a412406648000c000c090501c0b42058006181d9100c050108039110340441d0349840d0038080703000c00c0c68004100c0c0750b03003410307003940380c0c0e444c3c1c0040c0132414180d03074004d00000b0407000c95824083c070412181e80c0c2d00324960341c140003409004d1101c103185030455640c1c002e40c0e0000c0c2e07a01050a044902070002540c1a280c40240b50750b1031080101881a405400c180710700018100410180c19207174007094002800d100740e003044500d400fa0764003c428480c00e01c451680e000344c040d402402000a180ec0e03c2401da591110180d940080a200007001c0d80b400820b01d0740c260b030703 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 616584262 1250 616583012 616583021
    0x61103090607020415060306030b0a0903080403030903110d0c0215120106110a150e07080129042a2c0607030306030602030c12090d020d2001020304030305010e061f03 73
    0x603c0180300084610f0004104109000150440d0000c81d80c1c4440070f00902c04e6140321035502070b260366002d01090a50f45c1e0010304080000d480141850b440350181020540100085600443c8160458a840c69408030040c94100c004800707a015502400c0c202c8820200407044920a44030843c80d411541d1a08000710b40b07103040409002c00c1130052142c2540081d40481f503c51301c02098140c0030400d00521030300745045c0f40d902e80c000300582e07260490b400920203469040e40c00b074045094241d032042c006d00001c10043c141a1b8440d901e0090075101d01c03c01e54050b1201e14010790090b540740c0e0343c0f100012002400304503c4058104908501c084a200d007803622000070400e4910900c0c012449903039a69a0005030f8006940c40d008540002c5140f07807101d203102e8401c0d070780062010000c0046801068001c0d481e640d80380209000c020307514983c0c2580c0015044920302103507150000f199a46841d040080007810b081c010f45030100940e03408140c291911060b0514400d0105410001e41d0742e403141c05a0051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 616585512 1250 616584262 616584277
    0x10509060705031801060f210c1206020d0203010e070f030b010e130e06010305010e0d08040f020d17030a0506150712031a04090f06050c07170702010314040f0209010611030906 77
    0xc050311000300ba4281400c0c081d04005005075030787c8038150343c02c10030303c8405142d05600000500c02850b08240c0803c090110480854682e9950070349145440d08241000e445000803420440d400000001015410b06035850310034141035031414200c4d4542da00480954580c00c4002e800101846135280c82d41c60303c40ba8040a11003616800910301603900221810201c00342d20543d81369560355882d03050301605020301c200b400740f189029803040c030313080ea01d212000c0300041003e030280310410361400030130180c105003607a090925410b8584a20f000303000d01010b02012104503000c0c61082c190b48500303500c18001c0d1014a0751000c100008030a44400407001440e01100c8801c100c0312401c044000c41c1c68910404110303e00645001074060800e040075400d6a10103841c1c090595420040000400d1520300640c001070b08a0348083d648501a00048015124002642c18000d040390103000401014000030040039200743c0f01c4031240c0c0c1e6a010169071308002c1c101928516002003060215901e0301c607000708141d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 616586762 1250 616585512 616585531
    0x40b0f1b060106031a010207090c0e1305060a09050f0a090c170a1a01031a06010507060e06091203100927080c100c1202030a0e0318010e0301050906070503 68
    0x824480c00031444030614003152404041d004040148001036050050b50108105901d00c80501c101303620000350b8980b000d21480c9541562500c1c2c08001da0303c0349440a1949400030504c00c103140c54100888003c2900340d4a41d4030592054000080c01c0350580211407064407101e9182101d944d8500c051800342a05900440d8485800907001c40c031204130344010500508403000400100b52949005045541d4034040d201e8640b800b10010800240c00c6000d0440c0e035502090b940c00707280c07910801680c4d203001d58000100740c5800d000403025803250000e100c1d440b51039800c1c02c850401584081071003107440190745070190041c13644018025080190444d4040705001c43c0300c80001a800b03900303564414900c8000310740e400e00014082c200004100300d8070038010080758003046107900e6080302500d40303503260241da0100c030b0b0040f0000340e0000c4903504c175070b02d42d92210041e0703a83c600c600952890346480700b9024502103024813132415030700e08051040602c9917103210002c1800351900b5405403002e400c020040b440d07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 616588012 1250 616586762 616586767
    0x10b220b0402030c070317090a0206130e011814060a050f010c080a0207080d020f0a03030b0301090222320c1902070312020105040302070902090303040f0f0515040605040b0f 76
    0x1064032a84002c40c031544c1302401c1191181980c2c0b800030300c010884c2c0c41268014803c2c0041c40050400400c500005503411104686e60b01202d265000321402d590b444030082e0050100006402d07480b4003110840031401074030801210203200280003407560281c1f0359642141100b6001d010078108003030a034001c103074141810308100b06c080e80c9803ca2039000d03505890040e044107004000409080020201c4030000b400a000c0c0f000480d02e10a640303ca24130000b80801d40c43d0588404503890a40c846c880b540e40141c140c4c48401c103100d01d403a000799044040b0391615403600141c504140c091407002188804100d51401e03001c07001036515520100c0283c030b61460340d41304011840c000501d104884041c00e001340c01030300110f880c1d81011111001c001e0441c1c400c0d039041c4010400003950100f0710000b074800c400ba0050310b403500100864030b58000c60b00300e650603801c50a00804ca0056005406013100e4044403107803160b0311544459000c90085114071004660103110030700c14200c6040242c003111241c05085030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 616589262 1250 616588012 616588031
    0x172b0201060801150f050d030507060b04060e09071a0c07090c050f04080708060a020a05030612190305120a110304080a171501020c030d170c120c0c01060503010b22 72
    0x107013141c3c0484900200031500c07440c108903401c4525034010080c06c046890690784100ca4401034140d2281d040004c200c1070307039040810b50903582c9074401c601400c00c0424000c03281c540403513041c0c1c0ea00c405c0d000719100b144808200303107030020700b00341229440070b0b0311000b5010341c0d482c00000c4000740820241c4031040c040107219011681042d84042c2008154203001485180d00c0c01070000e00704140503218180c1c060040107035140c03550b0401d08a940103a02910315500e29400a15100d051400d151303104a80e180c4614419010f00d944038018006d13240d981c000010054a4840c080400c0380c0700c0407564011894180001030208047c0740142c1240122030911a144c1d500341122400b1002046403030321a07a00c00100001030a59041220100c000c070158024441c103079000c03a024000c96104d40fa00c1c6a0b00d1409800070360b09074045015503040f81d6a695403e18036040070400000030b6044800e03061403a41c07030043d00154903c1d050207203410041c00604005040c071a440140780c2110042d03560040440c0c1c0710400c05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 616590512 1250 616589262 616589279
    0x16140a0e101e031106030c070803090f0313080105100321050706021303060b040b06030c0c0a0c0311010809060106080c071a0f0105120a050d05220b04172b020106 71
    0x41c10140b100701801000ba0440c82e181c05003101111100d80500010300c01c001c442d403000000c40300b900341c0006a4030746aa03108a0500d03c0c3c24030504192005002c0402d01d204420803200141c1c056a041100a2080d56142000402a118184005031120700710030f41c0221100d04115131448a80b66618006103090200d896000603a84080c4041d6110899454100103100079445421307100e10382100e0500c1207110207800030341c840c0800341c00000c00c40300c0001ca045280008003d12505658031001c45041c03d50350f4113044203001c0c0b40c030b00c0c45404aa000d40000d4240d0502040303250680e082030f1940c0d1343d9500c0d0b4022011b4260840c8000300d5420111b803000001c0320340796850440c854440305107203400560501050045204415038800000e620020007100021800700380c41030f540c0c40524040c1e031101000300141d005046042002036000c1030311240070070b5070f44184000340251004a0a107604811060030314503507403d40b0008040003585c0d0304400901c0d8072100b589844a98401d072001091594541006 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 616591762 1250 616590512 616590539
    0x190c050307080307090503011a090601050403060f0510081203070c1118070e0a030b010e1e101e03110918030d0f0b0406080d1215060216140a0e10 64
    0x1600c102c80c0100400441c01d900486490250805500a00c07298001c1180046041d0280540c075203d0b20030a400101240d2040c0c0a581c01107400c500706100500941c3c884c2c2009180a42d09000d402e0380110010520400018401c128150300e1102d841c51036076029011a541001040c1c11160b0290006414030075541c2c409080d920070fa80d030720100c0d0050500040180c450900059140c1c00ba981c036039000c0010070244131a45044446041645c81c4036500c24445000c4425040c0800301000341d1602480708070044100c00701c064404510015010070001000a403001d200c620000b441988540c003802c0382c1d81800ea0304187c1000208030034401c001c0314280820706507040b0f914202350b6165980043d10511599002c0c4082440050310104095400c00007001d89400902800c1014000900c803141d900c983c1941c0005088000391202c6812203072980c4000751585d4401c8200e00c43c00b0852140441e0305000044a20351040000f4002880c1c03d00d803e00c6220311200c010914851104082c5000130b1220704483c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 616593012 1250 616591762 616591777
    0xd02090a0b0a180f060c11030316050f06100b030601050c0c090703150b0a050406110f01050a0b1216050d05070f03030e091f05040902061e1c0908190c0503 68
    0x8502101084003012115243c2c0c0a41c00700540c01c4000c2d604106098000004078110b07500000c0d250840f9604202192440c4211400d41c00c280840c220198180400801d4508501c0460f00c00d4400c0f41d00d400001c440c3d4900c0d18007400010401c2040460700300d40c0590020042c103542074043d54124000d540000c0c454107030449125010130344031080c14110500c3c1c3e049031005000c89400c2503040c60707100e180c005c000e40594040e0009001008000d440310340020450b090814a11030002d00085c03501d800d000f000f620000d030040d40110300464407210040c7c0c4c081080d0202101c8140d0184540e413400040000e4034041d0201a100c5009600e40801d00b00d098011900155010340c55160744880c2042c1805007402d001014003096400a003d59043c034113002480c002200c8040b41c0200e400c2900b0b0001036194410070250084900311091096145100d400241009801d0b010700d844040000b8400b110a481d80148028411707030b000c0007212070b121101440100c04c11140d150809159900303688003860741d4410350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 616594262 1250 616593012 616593017
    0xf03040f1416050103020c06010905040311030406090e071b0b15031605010f080420040f1b020c03070e04170c0703061e0c0e040c020f0d03020403021804080d02090a0b0a 74
    0x1111154078501d0b00c480c01004280703021442c0860b0141d86603140c51044c080d03011416155008a01494480c55649103040030b21341c19a0760720b65a5800180c119074461140006030750070a40094503207401150310b0030b4034030f0003c2d2030031806044aa80d50307000d030b4000030035400000c0313002d0071404207544041000c00c1d02e000d8a619200802420034002418804c0d083c80d100d000c02020008200c002811415007005a0509030481800c44c000321001502401d0070002c1851118070f021148029030003202c103d8802d0105580988a052001609141d100c071800e02034001c10886190200300050541c446042c04070389280203030f90410300035000c86407d1900c0d40d40240c0c2c480b901d0303075403a0010400b135030244000310014071f5003001a0071003200d02601d084024500f0fa4800e90346c9414034454a0f00170312030340340826030703800a035045c050703800e04082e0003901b00d030205a01035000700840f070b0781780186440d210b03005a4012080348d0409003c0d5611344040d40c0b1516100b6006a01c0707100000d083c0c0d00440190201032103a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 616595512 1250 616594262 616594273
    0x61e0c0504091d030d020a0e120c100201022106060904110d06050901140f010903021009081002040501020303040210020a020907091d06090a020703020f03040305030c12030601050f03040f14 83
    0x9104881a07500034a10b03e8003d141c0c500740e240c0c03c0f9000004407891170140d21005a1130b0051800c0941c5d90140c0500300b01c0d00110401103800041001145c1c1d035841040449000d005442900d80807800c0b0300035642000c85290090396526101403a119086501c1b081c0100107a00e031450050215098a049651940442a0214422035000954001c00010708000e8403906069803420a110030324800712a6114014121b03401700c05010791040c290710002d0364000d40f83c07100c014409000108a011a803041904030b004036508400111180d0007154200e940c141e0041d42103440f96020401d61082c10811b40c13080d40700d000c001c2c10050703d4034243c491043d8040c0d00d50103269442c01607141541490100148502100f0b030b010010f0b15a144a6901c0e00103908500044e200c09845c03078240c0c5003943c2c0d44240711603803001050000c10043d00000400c0101d202c40305440031900c45080c8410140010b81c3c116000c50400d00450328a17110600156a005010310030a8016102d141c850100c509005091324005030000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 616596762 1250 616595512 616595519
    0x9050304050d0b061f020312040f060606110f03070b04080f0705010f020403020f01020f060424050a090c0e0903030112170d0b1212090d050c1216050d050604061e0c0504 74
    0x5801c1d00c5440c0c65807907451240043d00b45c01c00940728032907040c1c2241e40084081c0854280310645441202c0c0a90040003004029210000548102d052151030302d000c0c81600c042c100228000720640d11100c1d4420f03084402030300e40da41c030313142e041c1c018592a403003246041c400b9a011030024011074010304080c01d4010307138035402c500512040700d520030b0000d030541d4070200c00862200030020b4801d901640240405071001000c03100c4140210015400c0d00456060900340070b50804130360300c500049440b452415004079070700d010700a08400c04580c80c4c0c0c0d194000f40b004120281d0b200b2203003440300b88130709800a040c00c0c4441000305141c20071003c1e8100181e840610b0442402c1000400f12980030900003001c0680040003074502505c10010007a01030302842c950720b02000420003800e004003d0040c906074005449a9015507a81c0c21041c00118810f40b0f5100040c150071710b4003001040c00c2e0404050280c6988544404026001c03c207101c10070322882c8000030950b542c1c1c038400c0110050b419a501550303640b5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 616598012 1250 616596762 616596769
    0x6011d07050301290c0d08060a050f010f110316110915030d1d0a0608221203240b0406080108010209240906070c03050f01110d09050304050d0b06 64
    0x401010441441010801070012134502e46007000c0c0c843d08002d50955412018003034140034082c3c840864507034401d442468405540201c940781c4505c106031014031a459980080003100344040d000680070500c21a4807014852150000032540000700b421203161401d0500c90040000b146101542d01000500440314240b40c580541c6070004010980d45c0c58041311a0000f948805100c011003040c05150711000248101f40a1600101e0310000c1070f00d11040c0c0d46440280c11004101d0344080b040b02102003007156003298a0481307050035001400042500b000c28410742c003c007160f008c12600361105036014228071410501100c050100c1158141c0c80c0c2c0c1c0360941c003400e100e078181c2100d14980d005104078803030340c0c80b8080000107007800c80c82180e0a801815030140f50740e21403210343c503030403600008000302404440d0819108480c031840440310011310981c202d42c200c41040c400e80202d80c90820030140352026a80120340524021816246416070341c42c00204001110403049960380e11010800100b4038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 616599262 1250 616598012 616598069
    0x40308180306070e10090807060206220302150c09042a0c020f09041a0103050102070b13031e020c040e070f061e030c0e1207090b040b240c0601 63
    0x290950040c10941011000908034405084a0301d0040c01a801181c107170031b11850310000140344a1042e03401617501d0f0f40d00292641022600c028000c010b950038000302080e82c80003180170720781503405030018000d00e0720001c00d402009001607002c203000b4000c00c0104e5413244a4660078850104c0c0c84110303801400c04542140504840841c1448641d080c41005130b2600b80c00068041c03411074040150f9515850704100c03002151010750407442030007001004000c01540203101950141008c2d07401e03903039400d206041f9142950b10040c0002e0310425401090002100220303c10fa0712070056542803550710300490107c6604e40d00010301030340016020040f0103820740c000c001900c0300786048042e04070a01910b5134240c04402c000000c166881e07080006070b5120f41c0d02c01032591f900520b0007920780c19a821141c0d5400e15401070519142c949628232602d45042c0c803510b02c0541e80544106440d080b0b490240880c03140111b00201414420846500410005e0111501034552420250100c0400c04614110750 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 616600512 1250 616599262 616599307
    0x50d080711010204030c0509060a03050613020108280e1f150812070308060121090b0108062701110310090b0117040b09070f0602010b03010e070614160206040308 71
    0x2a48100818801b08155103103483c26110103039101096030321400c0c08240f42c0c0025a10140841c01010140b0403c51280400c109002c0e0007607071482c0003074840403225140c0c0103c00d44004507401032540004800e6101c0d8000d01405000042a13070003503c103102c5a960b1648070624405010341c0d5440e00d045256411140e10780103004c0802c020b00b049200c50803184903d2040060103010f1114401c00505140c0c829241d00e992440902d9145081c1d0403045199006801d161004a4007417200388000319020742c0004116115900c054404103040290b8104000901c8103100f800c644e079501c0b4078404000069003801036000360a44192000742c2ca00e00300d0741c8000c5588000140e4104612808002007507041501080d03049a004412000300e51070b40c449943c5000c200768040c1b0342e04001034900151480d0190b0007981c10721025802407004403c416441501c0e821140070754000700d240d210300a414440603402800388040c280441c203a02441c1c50b0009100e50300150301c101c807680000a4504109500c000010168 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 616601762 1250 616600512 616600547
    0xf1b031203010f061202040305011a03011a0102060c0a020c060301031208010b0307050f0901030209090705090406170d050307090803130306060608040f0201080705070f050c030f03070804060c030903050d0807 91
    0x1c1d5410b1070400350a0b41c409100f10790400a002c40c1c1035056000c02d50480c0c0c000c1d6401002084014040a145803038140c038201524440d51a044201c04815030300144401d2180c0e05901812603650b40007203d819580020702800d0442c8224660b4038902d44600c0c0081d40a103000b001001e105201e602401405480160440c0c0c5003004207005024050b82c2120640390140041c54610f40c50701c001c440100c0084c0210070300180c0c0000c3ca0400d1000e110341080050882c0300e015035050010648030304180e50b40b0343d544420584240d0028120b40c140c1072181d0301468000300c071450705003034656440c1a01072460f007128502c84000e4040401c10002c018507446403200500441c1800c10441c41d1a444140c814101b500e0301a051100350800680d07528032134011128810342c0b00c4000c00c90010581012981c440e8000c0b4502d00078400c51500d89100c850000030b0b110026030040d4064509401d10100311026081110101c0600010103400710010710706108110281035076982d40c01c29494900da0041081c181503201d806c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 616603012 1250 616601762 616601767
    0x18140c120f0736230a051602030304060507110307050706020106050d11040c09170a1a0f241201020a0e040b013e0703030206061903140f1b0312 63
    0x2e81da5583d07440b000352041100160408012002020013500c08802409070100c00300075010100c0d420030f2052400780b100e80300d04110366070b07a43d05081d56051040070b20310056482480090002030840c0c010300c0d0f00c04c402e880c2a41140c0100c14009180d5000a00201c1da5a00068000d0144980c24454140203007400c0f40d60014101d40c5071141d00742c00c0f40c8480364038000c548401e042031413140510300902c002d141300c10ba4036001c2001d90a807161200624442200d0b0b1881c00c1507032142a003044511280299803c45280c40e058441c07000e111210540b005843d64500500381000070140d07a1086844450103460002599400d004034005007000c5107130b41414031540c0307000c0d03107104540d9001c4841c16585004400c0030824261007010800314000301503850b186600031414513017610300c0c080f0301482224440e4007110305540f82c0c58100300e80d070103800802ca0210719404a080000c0342c440304024516200f000c0c1078030500c40005031000c0c14401240c040083d800e442140801c000c0c14200a08405003840054190 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 616604262 1250 616603012 616603049
    0xd0606032d03080109020705070f060f0e03010218101b030f111f020c0c1201020913060e07030c050c15150405010b090d0201090902030a0b040f18140c120f07 69
    0x1820b40c003042c0502d05c44240c0c041900c0b010070004200940242000d64000c0c01d032142da800004010381160161000085c41c000b04d203401500b014001d41e0801c0d0107195000714080500000c0c00020904254040200400c02000300303000c035001400e0b8400d01c2e0007603030b070000c40b41c05801010b007504404a005409641c80064031540a00241c100040703000021000075903034160301001c940c80d10003e4480c0a5010740c054070001071b103010540c001d104417107064400300b45025405a50101f12542807040c2c0c030007018540d0018920900c04d078009824400c450408608040d11070302c001d4908403180f4a0000041d5141041c411001207e001120407c0030458003030010350b04065801c0341e80d004500d00d840c0940c4205503000110f80c01100c4242c044d040e03105045403245040020740c0040c0c4000610709010780c0c07424110560601e418014400c035454a0780705030400d6102e607541c4d1900184c050322111464000c84022610607505c0d1005045034040c90001440e096080345025400c0c50f10a5000b080241d1080031b545 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 616605512 1250 616604262 616604267
    0xe060105030412200f2d070303182304050a0c2f0607030f0f0e060610031509090512190f021006061116140402090d0606032d03 56
    0x1201000b0f12490400643c140054800344503001c00d0009500501038240c2c15944d501c07001500809520289005054114801001d2290b50070021601a0300750040c460034800700703010b0440b105840c1010302d640d4600c55034030046552505580c100030151580c0b07603155030310039150501900da00200c0d0310504014008500740081d02c411002d03080e80c8101c9441d621005008044004912000103060341030b0b4a80c1c0c030701620700034010240d03a000c100e0140e24041080700445120b1181c001c0b0441844000d0041c0d490b242c007041007040c05121a41c082540303400f004080c01c0ca614006400a04900b90003084050031480c0c414104074a000f401015403c05102c2d140d005104406030a9141055007005103151100c420103e05042c1022001e44603103040490004040382d0040001c000c1d03440340c4043d074003407501615200f01e41412502c81c0c2c0803c211401d60803112481c203503008015214005160200140d403660300c1d1000d440b20359106640300007071201100741189a40481121510000380d814920070910b540c003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 616606762 1250 616605512 616605533
    0x203060a05091b03100e01080706050406080a0603080a030207020307093b03030f0601120c121d07030b040c0b0403020303072d0b01051306050904021c15060e0601050304 74
    0x72140300d44840b02c040350b01c11a4560100803100707905061160f40c1c0c0b4050003140c3d2034142a20448020f10100000001d8450000c503040301550071030b5079003500d0130307191080c21989030402401012210381c0d104400000140d1000c000d11184030310703480140c2c9500c0103004041c207100859110b040c4076801d02c000030000040c03400d1040c1d20f5070411010401c04418250118049049000300318a0510000080c40f858450341070a081c403406090b43c1d109207803d083c00c0c81205072032414600d1008950341c1d41a51b10412000c1e00003d142600c607801040c1009940d60405281000c03e40c07042d00d180e15518140310900480e802c02a0181c00c04020303061600d440c660210340d8074451650050304c2c4483e00311101080100400004402001c10031001454600300e00b086030000d4003e1160b10302c01d90280491448586d503502500c001c90b0001016107180fa6a036409004080040181001d200388821246600003444280e0000c4c400141d0440020054101260f00d081c1c481c0c050001414000280204000280c1980e83d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 616608012 1250 616606762 616606769
    0x18020a03031103070c030f0b09010c080f1b041502011d0a330507031817030402060f0a02030301030204110c062a180f0109050a060807050d02030106030905010f0203060a 74
    0x14403201c4402410380b100d081d1300a00e00d0040030040c20002c00000c0c0146180070316501402002c585551741c4604943d0b5089408034000c403c0801c0c04840001c0e0418a118003003507011403000e00f4101d0141c400c02120705154450380112549202200c00010065424800d54518004200d0103002004926940e281c0c1e43c2d070302c054001c012102c402198038030118818041a5200d6001080f2000554224000d03400b8040c1100c1c2000080d24028100d1001c030303544440150581d4001c00124070a107802d0b020000580c2c0000e105076005001007000801a040c07040040094031f00d0b03907014588950640c410402600c0505101c1071500500f80250103074420041000794000788901300b4000c0a84400210780002c040681e201101d07807030017082d130301c0d00d08501808058004008981c014084a1702030015100036050340601504517042a4082c08042e000750711803501316004e4141a820030303078100b00301e8059a000b60080000661074107035001c2001f5090203280e0300d814151009504525096000ca42080340520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 616609262 1250 616608012 616608017
    0x31e031b030a0522090e06040303110f04030201350f09030304080f0304020112050a021206030d0206070c141b040f05070e0402090103020913060519030302030f1b0d0207080118020a0303 81
    0x40c0c0c4201300355a8003100005040e203040c140311440d0300403141d50f1540c800701c1e02940031a0920502506a5007000100d4522915150b00c0c10f00301819900111009510300c0b07180102d1025800004042c5482a14010808202c004005103113240840100700078400103049a0f820781d1040c13082c840010005825940700c941c952800304e489646074001210345044031628064200d01d4481030084500d1b01750028984200e0704401c48840e43c4401c401c0c03690b100088240c03a00160002c00100c0d030281e2040c41c5c4243c42500501c101485241c07103c400c0350802c0e0412903050246054000c00360742c642172501561000008000b0b04005510704058003070084111030030941d11495001844902980c0264183c5036251000b0f00f003446000243c1003604020300080c05814815880c015a5807001c0031100302e03800589030300d42d014508001c0407100d508916000310300b021440e10040c40d00424401e0b4108121550740342503a00502c5005c1c0740c481000c0c03c40301102c3d00d20001030030501c0010056181e07407240200b00d80d07052 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 616610512 1250 616609262 616609297
    0xf0c0b061c0204050103050606030c1903020105030414030f0406080c0909010608090f0102040b0a02010605030a08070609020d051005060109050d030915021c0504150f1706031e031b030a05 82
    0x5804141c00c00c010368800a52240c41c0c4070020060001c002641403150106804981d065105002001a8400000fa06c594034070741400f024001940715601664001d4850203001c008c0b041740d818860701f5604516101c0c0c8520b10041410883c080d17100c20025000324199034a146400c1e0f5160102c1c6203c501401144203001192011444c0804100201d190121100000b1911143c480d006449190302040d09040158209040440c4900e00458800022540f00c0b104502d81450f540c2c800c0d0140220500c181d902100c05007004000c10000c0c001c07510780315560900000c0a20b404000940030000310380003e80225081455a0002a0412941015148040210307041049034810481c81c0c159560f561380c64845012502000450300300020b80155070800902101e908500e00c01241e1441d003090004000030280340c0440700d000506c620240c1c0000c1d01038169040c165100b807250082103860100ca09495000140b015102c403070140090f215240d0b0000614078200388184000c10034060740203a540b25a000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 616611762 1250 616610512 616610539
    0x10e120a02041a060a090302091815040f12020a02011d0d060e03130b13060807050307110f0d0c0512210a2a030513030207150504120605070f0c0b06 65
    0x90003460740300c0c01805650f80d04c0c5c0020300144000381c544012401044202c0102e007132078800c4250301207080d000d44010b2800385241280b101c944a00540f00b69500c1100c140300002040c1d0b056040d803880000b58000348211085880010701c0200c4801040140403c203040410301a50740d01e030084c3c056900f142d000b041c0031070051080c50441c450344500c00021110100005202c1041c0d0014040c0d2500031900102d44954400c4151b40b01c00b001c80b000780c001801040010560790103507040b030541d05130240460300010708c110002480c1c0221046894089440e034041001001810059411803a0350054000c0c2007190749980d064501142c4950360600c0052500025100c80c8607078490f1440e0001040040703c5000703900751403d050b0003040f510702d000070304000000c4c8010380801045140142c0c036038024071a00d49080b150001509501c1d400b141008401c010000340c4550302d106180000307002e00310004290078042030261528212110b20010700c820341600c000841d0403d02140d030b01400648070140240344 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 616613012 1250 616611762 616611791
    0xc1e09051201090b0702010603051f0e0601080304090f060807050d050f0a0f0b090a1119050409050d0e09010e130f1b060311120a0c030e1b010e120a0204 67
    0x180e0009074020385100340101c81144150060025240a58032864060b03d400904030700f610300d5400b0203400c5500030215050058035446001c082416000c000240ca0156070003418142a001e03842140f06030b101240030301030b0004038801c40c08082c0b41007004010b11803034150070f191500b03100e216182c840c1c40c190115005000c401d10015001001010680e407c42c1d0b10b41c40c0405102e480c000c0e0995402035401b00051818000140c025500358000044240e101c080c00c00700b08400f510000c107400004003040300060759032a00d002d031040c554803030005040110704401c1d006080600c0380030321502c21103411340100950700a8401044d0804806458166039840350f0502041881e04004003c142a000c5409a1b00c09100c2d0250201139840b2641c06000703040e2600d00e0b01c0c6250207007100b1648410395450204014412590011070041040d003008103100b07a002d4045810103ca44c1561000c903103030451949155a444064580030010031606829038114084000e80e480d11043c000038080e683d82c2141c40c00c00384 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 616614262 1250 616613012 616613027
    0x60e0126130b0c040e0f0c0d110c0d0203040e1012060c0504121b0b030123120703080307030c180e040c030b0a0b0f060711010f2c10030c1e 61
    0x41e005191400b481c01c2c40714022916a10510403a990a8034240220b200921400d2030300d405245040a01030426440c541c0b41e1005242d0090f4046038803104000c0d5104100040c0f00f10300160140350040c6858500c4e1454100341e00400400b4010700c4400038506210601000e210090143e03007000d4002510503c000041d600c1c0d21860304190840c3c1d14000309002080052108002c1080740c03d640503803100c2d07440c2103502c12800203014000081c3e00e0070b41c0003420807200b2052800c8400e401002c04400030b80585e142c604242c0680c005031005400003080000c0c11390540200f200c0500765184c010200c1c0c40400c5c404100000c1030064228000680c00498180985102c3c00006103410a102c48090b080923041d200c0102005195507005100854880c8003a16121703055644458000b40c2c0c00c20000920300045504030001c0400c5020b01c907400d40425a01b07203c42d0600c0c030218803c0030410160380c44101c104107045610542000030182081d4489070011352048068071182e05248410060804000d419924103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 616615512 1250 616614262 616614301
    0x304061e0603031205160302071505131b0e04030c0305190302180409080f0903070b0d060e0c0a0c080f04050312030a0b06041202010e04090212010501060e0126 70
    0x800d0165000c1111804541c80072003203a01c2601c8030340031a5902c90315882a43c2046407642e8070510280c030145002400394005012151142c02011840700070740d41c6040850784c040ea895525404070190540411424015442c0b22420895a40c03078a0340c41c10b005007142a40c01000101042039115000c000c05001d4030668401000e480c04000000092a8004000f50030030708609c0c0c0001c00386081180b050a091040b822110342128000c1e1030b0181108440040768450500603030548501800002c841d6001400390414504195010550515000301c41e088200081c00303540e2203110130040d00b4130040e007081c240b03254241d200640b1502c41c03840c20b40341121800b0780ea00c031235018028500800302c1540f20303400a511a00c280d04040061000400c1842414000d0340a00503100c0785203079100000d980250700701008050010b1010031000303400d40c003060380d94580c00310417403c07a91100010301c81c150304140c44404000081c80c00544031101c1c40c261110a1100c40580c01c110158400403549444407001c1d0213054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 616616762 1250 616615512 616615541
    0x40302030105090a020109060e0114090307080601120b0c0a050703030e120d02040e1006051e040302220e0609031204020310020406051306020c0d1203090c061124010b030406 76
    0x1146015660540c0795661400e080b80022200700c4040341960203107610701502c11040cbe40b402115a80f00d22000b541d0b60001244a40c1032060300c03c0041e00c80317010032a041c080c005404944101400070324041d0b001100240021091342c50034010711450325440400d50700d42681629004c10299004050700741000c0e820411040b0540c07000032514032000143c0c0003401202c80241e8041c0056543e03603468400c100d054051240050010403d0301e140310204900c071160300c0d030030640031450141d4a50000e007080d520b0091b80d000305000400c06030b06131081403152660402011000c0c0c50f80e0300d030601800752a40300e0098440311404044010505540f02040419141075a500003150b840741c40f89000b030415004480c0303600300310501c04000300310144003151001c1c2d5124007804808816000341c1e03403104600c040c003282600300740c0c0c0c0d4141e6074045103101d250039009000503101d800103418071007a454200303c202c82101c200d05895600100341c1c1c04050103d03074111402c808a031902c0ea111840c02401174803120380c10584 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 616618012 1250 616616762 616616771
    0x60d0c0602030a020f1212070201240e1003020f060a02070801150305331305070b0406090b070803060d15140f06030f0606090a020f0c0c0a0b0f03010612020403020301 73
    0x400030740000c0200a03c0701d103a0205c56010151213100c550302c49045c01d481e41440b03411310080a07007440300790f80240c00c102c8a000105c1c1c600b40030502c12160802513440d00c0c46274030340850104844425010125007005280400081d03040c11500403074031281818a42d0350050200142c10381c0742c07610038441c20001c0c10b5064020b210040060415080c01c2c000343c0401d03180750040c10346600c1740e20481711400300302404c0c0c0e200301800890a281003030440c60004018200b4514080c403074a0004405009010280c9410049540c90f10304001c002003000c40e258002d102000340c02c10100740881c0802c0d0035258401c90032103030760052207628604119200c50b0010100d1106003040214403510f001c4003903103071142880081000d03080d03840030101607680703d0065146246d0b0700f002d00840c003d4100685200d51182d4440c101500c1e000031760307800c0d03481c0350b001d07a118510a8211038490a07071440d00c2c1621100400b4020100b0741002d541c00c0b81d044c020310042c402c00090200724281c038401030303a00e030701070710f0095400400800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 616619262 1250 616618012 616618019
    0x8041502070b1f150206040305160f0f11030309030309091f0905160c030c12020c120f060c070b010902030a290f010207060e0603060d050d0908150105090a0203060d0c 73
    0xb43c190005500080080084110115115000703510405040001780d0050481d510740b03403420b91702c59101000303840c00234940310f284c070001c00d240d010b2250140b4400c5a01d02c0fa40325a9003481c040800d4501d050707a1280e0020482c942d0640e800200740c64080004890024560712507884c40c44d0944011401c2210905c1e620000044641041c4d000350300c10305441402c46444140315000704c40682c1454030050100c1c00c20030035540840c005040200e00c1900034011680040c42c0349000604003030b8505124041c652105250310703040b031014003041e03400108038850107042048603030700c0041800f014002e06450640c044005503400001c1e0704070303112800e5060340228208001e0071440c181181c0ba400c4445c0030310280386401c0e210394800104041280c1c02c0766030b00103141800c141004031540c0041c24030390b0312100202404002c50402d02c030ba2240a803064440c1e2a800b881d00c0d452908251055030551414140d40b4010000c944610b4080d0340e0100c60041c005a8a60700c017000911540c4194902a245000790180030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 616620512 1250 616619262 616619281
    0x81b040c0509040f1b021b010302030c040b07152f03040305030f19090f0204051e06040b0d05030c0106030b09070303020d030c03090b09070612020906071b031e140d08041502070b 78
    0xc0c0303040da00c0c0040034a41f10560f01c0041d400c1c1c1c03000365802a13585508000c00c2052414000140805d244106a6407070340b60307008400340080ea946c2c1c3d540120480c2d02003d00300740343c140e0b84012640d030100510310315086180548001d845800001c10b04000ca140d00c60000d9100b9406100d4481100c1c9501405c100a0106081c4208140f1034064200e00580c513003c01308401480342d80c3e01c240f01000211101e009603841c0d00a000151440540b2150001c02580760000000d03410701c060880d1003840c40002900780d10b54182a02c240c04050807948042d0004174080c80443d50100c0c9070001e05109003070100b2100f46034901100100300004c0c0103840c074260b000c10b000420750302252043c01c80e40c8941c0c904070551050415801244036000410b03a0194003000350000007078104440038a100f841c550803000c0340d513580e1200024071070110710104220020064100c10010040304101c50350308000e0050803096402c0d800603002000152020300800d49101c200d1044040540450b80c407598010031000e81d034180100c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 616621762 1250 616620512 616620523
    0x504050a050724030b0a0504020906090402120603120c06072a050105010f150905240d021e07020904020f121204170a0c0611010b0406081b040c0509040f1b02 69
    0x5422003d032010344034910381e00c41d00506480700c0d4014042102c051074101004000d41c07080c11401d40116083c0300855035a81c4610181001c100300004801451410a0815007465051202c01c0815502802044c402d0b40000820319070140080c10031840c80720001401c40b90512410100b1602c0681c8224050204138064108034102c42115003000c094544070b80400e034211030035860a400049003450200701e01e1078800000701080c0b884075000c000c1156600c510346a1944410301841c031250300000d801c81030800020495040340200c1c035202d42030612503400112040d40140000c1d104440085c04040b1903500c03401c0c40c0c803d14007040c0c22035401c0004055210304503085032280040c40e07403011a402c0c95101011403070501b0280c6c0400d18840c0c076414000284d80403110506c0c0c1482d0303590780e640902d4840d1924450341f00504000c10080100c01c400030702c460a40c040c0e400720540079030b040c8000c40056540040c06e076010980d080b600443e5031b5001180c004c004054441140e01c50380c40c040c03d08200a40c02059 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 616623012 1250 616621762 616621799
    0x18100c05071a07050d0b120d17060922050c0301020a09140915060307050d0903092c07050901030f1109010909140a02070f0f080415020a0b0a0504050a0507 68
    0x602c01c40d0080c40d00032890400800311507810105508000d10395002480741d0255074100c02c010400100008103c5146151000600b00c80d008903418030020101d800c401e10394a0740c0034008603841e21140c0b43c82060955103c0503c0d402d448000b1285542c03804002d000d2010480e1200060000c40d144c40c0c44c100000c1901c83d4501c900d0513941c480e100300d04074a05010ba0070314800e16601d411044810070040070b12807568401000b103c02c02000f8001d10107400000c1c000d44411500a5458190460406040700e61003240f40100070000400000c2c00c6650780f149001640d400149418a01d0300d9081e03140058028180341000b00c8000b61920100310000011180a490303915004e07a10b0710011a02d404503001201d520019006518a90030700051a0341915001400b18a214200c003801110301903072041c0c1c4603060150202d460340c01c04a0305018110318040e40c0a100c52141c0300070003002c0600e803240c00c1c030a00080c0c64a000140c4580006050200420010801741d90290440c0c00182d40c44000d69902c40040c0e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 616624262 1250 616623012 616623023
    0x90303050a021f2304020f150c010203010915060302120a05130c0f06030b120c10111009033b040608030406030212070c0305090118051003090212031218100c0507 71
    0x10703030304d20440400041904c2a94050020850010607008014803c01c42510070b12200104220305020814280040c5001303010340314012079102258840001d0041d00790300b011080501c184040c00601000010190300207520000004150319446a20121190425409010324144480001d00108100c500c0000c550032950308006030040c0008000000d4030000002d505503208508400161410090181103507190f424161800c50305070022505203492021070380984c0743d4030890001419004440c0c0344a0000d004012a025202e03050264030042d2914810403014140145850907a2038643c040e101901600f07003100d0b11079581300d10040180d40302c00000e0794046004000b062890780918090080958161900c50600031004011102002d17211040301450048420003d955207800104111038400da5601168020150041c0038440818100240046c0d01c10080c0c44d00510035814150781010001c1b88000241c03070717a06041d91034031040b0100501b2007071074070b107664035020307000784c02020301d41d1044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 616625512 1250 616624262 616624301
    0x120f0b1905041409070303050a0509040606020d080c040807060507060f02040b041a07080405100909050c0a08010815130602070803190c0c050c01050d060e010314060c0a090303050a021f 81
    0x1a4445691101a40c84603139a9000c104180006401900a01000d400514209044c0210f1200040590341190b000d6405a002140c00881481c5c2c0110101e0b40444103001f2540707000c0c43d058006903541d801c1c0c80340b0810000045050410010b864100f9070070715680d41000e42d111031301d55414021325440341c801e010041d440a41c030310560700c203d8001c0c0d600e890b80121141e4240307444c041c1030100c15400c800401080105291002c564140c05100301341c05094042c0503640c5480c84980d000e445140f0607000722440f0b40c0302c0a00d40e01c080d01c901c081c10b036104400b0100808810001c0c0f07030180283c0203078040100b01e07039004070400501c0c02d030050081c03201004040c41070040c0100c440081c0c402086959000d80b1a40000130a6500755004400030702119110900000b056652003545004144085c0c01c100c8880c10310031a90b805040d020060326402080d040301092910760100405001a0740e5480b001301030040c00315400481e2802401420209000d0003046500c507105240304400508a2003800700b00003030350 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 616626762 1250 616625512 616625531
    0x201060e0709080307020d03050c0607090602010b09130f030203131503060b0a090905130b04140105070f0e01030510080610081209010c0b04050a020d12090b0901120f0b190504 77
    0x140042c031080707891110295180c41a01e4080c08900c41c58404281c0c240071040010301d4281a041080c83d10030443c65684401403400e080b030007425100d04000c80f5102c0c040800511450510b5041000c62559004444ce501d2800502d8240d046003c0c050003061001c801c0a000100c6045030f0f1036604103126582c1d020860b0b55100c1c0cd00755400d0040c2c3c004440025101002480040322941c41107070015080005084607810507540c080344044110750403250074403080c0c03407000004824052550820043d06101410a80c125030040c0341d1944c03078200f54105502c03274010031800e2081d80003104c00b601c022029904645004042030303207444580d00c906e8a0718070442c2d01d000100b141081c10345034031130016036880b0540051500d07804901c0d54050415100340c0240104400103964015045c400c3c0351040e0000003036003050950250201c4030305d0f40003494400041050490503a80400400c0850324070302000510010012441001001c00b843d541d90460495101820404628164882158807c450078401030380c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 616628012 1250 616626762 616626767
    0x50403030206190f020403060b0f060a0804150b120d0207090203060a0515040801021218060105010c15091506090608030f0a23030f180604050c1912030201060e07 71
    0x114400900180c01507000300310349600080e05520511081c0001242516100c040c00c012640030380e2085400c20703030b00c41c610318642c140040c1c403241100085440380c1c2805400b50b8040c02506005200408000181d002046080034951040b0701044025042d5a01103100c2c8400320f40c0d6000500041000d4459280c3c0014428294001c59200b0300010b824081d544e4030b02002d00501865101007004601410300001c503041c5803d1018085900300b8001f182042d0414690420607800059100041c0740c100e41d0040c000350b60031440c0301410b154480d007d071891603000c101c080002d01d940d5900801c40c915032502d04400f01420741002098030700d4048100901075883d49096940e10441c030060006401c02d00002592a0248042d1100d4000c5a038403111101202c1c580100c0d140d00440f212007416115406019001600c14280c1314040c28110003012103080c02d45640317594003102c1d00303440e104403961000c80941d40d4090600038020a0a00e110b0030060000b0310f0081d0282455010f0f02581c120340b400024140c52 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 616629262 1250 616628012 616628017
    0x6170606040c0905010c0321022109060c0711030d0e030d020c0d061e090813150e12070909060504030e190303030b01030e03070c1401090e060f0d120e1005 68
    0xc1682c5035980b000f4545001542c02e40c2e00300205401384034007040e000203540d2300706075112100401464016502c0005000c03081507200702c0840b9039803034410b44082000070040051100d4103c4044080c913034030703401c4503e4801031458002c201d840c4c00d80503540c44105c0703180d080600c400d03005c1c101300d05450800100c0b82c0700700c1c1d544800e5000ca0340e0001ca2400c0d8803021500d6984001d00d18401d28203506800b180c200201001c0d180101c0040340d8070301c4005401416400d5040f07540f405040da60795284445500e5103002071215003801c100901c0b650b544c941000803070504001020007840950350074444030800d410607000803c0c0494082d40400c44401a519080c5080900381d400c5107404820041d4190071610224010700c1c000180700d0505a4038040c41c0b020700c40400140046034480d142c2220f489007480d071700b1105400c0c00203805040c0b000c10203041c0305502120900300d500010603107508100940400009520550810001d03140c2207454140807452a403260300645d101c00d080c2e80700641d50300300726411661071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 616630512 1250 616629262 616629281
    0x120f030e0c0a09090f02090c03010510050408031c06080d1d0402030c0313052e0b040b03070e040507030812010608090a150902190b12010b040f0b030c0c010617060604 73
    0x42c42c03541090015002a52140681901500214015560550100c0e00e0b041c010303502600c1e445400b1004101c1850f0004450400c03400c0c0307190507410180740c044800d82e00d0154001d540c8030a10030000c0040803082c15801107004210200071a1414010b40f607001d002d60309080f00d10382d81401e00300100011810701e4001c4074042c5450021080c99035440b0051200b00c0300045108071201d01400844104c110342130443c4000aa80d0803028000001d4600d508104480360030410750300960400465400315540854a42d00315407503000c14903515500c61418609000c21500700030070300c4001258035044101280001416034500341c5601c0e40719103805140303940e100111403004140900300c82d030000e8291001d4000c801c2561020300044250080315104000f8180340380c11000c00003c0c04541c07003020100303c0342c503e40117020980e100380c034081c2811040440d4000303900405038881030000100751044849002c40340712040b0742c4000c00c1004d441c1e52101c24144441c454681461280201145903840c00707220700b8034503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 616631762 1250 616630512 616630519
    0x603060609090c041a091206010b0a051318090b07090506030c090d0b0c1e0c07301b051e010305070302070c081c0c0308010504020d09120f030e0c 64
    0x616030314404200c0065401084514002000c0c00000303060f20010141c03c44e611100005d141d1225030740c1007400b0b21021a10390380d203100d6104c5070040100001000403200c0b400040e01d0010b5942c150300c0840f5409a0380781d401030b84480c10025030349110070299881002d8030351207000102041d880c0c00b10104d901b0a01406001c4e4009400c0020405040c1c00100910300307400c0242800c1d00000f0b003901c400d81030380001c54140c28900b40001d103051b400310340b000054014040c10b8180354100480c00c50b010f40e5480d505c3c040d00607040025400b010074204107542044a950080006800c100700c4c0e450258036880480e030916030700e8032100402088500d49108200782840444000303180c00c591000044024000240a1509241c1d00b0000b01d0003280c01c6030200b8003c0c01c6601c00a01c0501500020810100c4078403c2000800c907500184d100002d074080e00880c1142c100712005612202e42030304110091007424130007005034500700036030518903800c083c40c001c0100d0244c81c00c1140401c0703503655a03103590300e985e1516407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 616633012 1250 616631762 616631767
    0x9030a08071d060a03050619230111030408010606030b0423150d0f050d0311041a0910020c01120b0d06111210031103010b090f04150f1a06030606 64
    0xb0b02c10b01900161007400500c80d207054880b040425015030004400100198035a001c1004074144140c02c0c4617414031043d5503030709462801c0245207000440b599039100f110554201c01d8000d03031140020720401c1d06d1090542e42e8407982e40e01090b000741001d01c1404042400c104001c2c10b507103401d1042180c652424001e0703d110000030009031514a0000f00050b915181700c0d04e105901d51101030750000414031034000f200c0c0644050810134a000144d4490504060819011101d10030344142603500701d48540c0280f4000c00802c80ca44a514010000003e421001e88030b920281e13150b0010701c00c81e4500d030030f8940e0009503690b03a60000554040000c0ea50700000c0070003000780012541d03030000304070313001d80040f040c104003000504054050b070507210350718400020442801800610580109601005c4000308016090313540850380a031001040e21002c0380c0000001810301652200110074810f60b03403c104181e00790051000010000b0102c06c0341e0035030045002d42c0045c02c1034006c41e8001d5200510250 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 616634262 1250 616633012 616633021
    0x41110050304081b030c0f060a0603030c0209130605150f0114030115050c01150806010e0921190305090c030a0b0a0203071b060204030b0a020a09231c020909030a08 72
    0x280354040710901303c1c00381800758100d12031070080c0b000d00040d41d559000380102021441c0394600d008405804400300c24500802040000d81110602c0c88131039069034010b200b580c64414080100c040c559014190500b40341c10400358503c1d0942c420004101200d554080340c5c3d44c0c1c0011141d51040d44214400e40c401040107101460b01d140024500300303d02d280651070a8003140503d401d4034490081c0c00d00d12400e03e9424811400140469030142890031024a05464903812440d031b220741c54403400398158440700c03511490444c41d50031501e5680000b102c900001403500c40045c010300c0d04032603080c000e0243d1410510070346008500e510005030052140102c81c2c841e5000c000c000d500107081501403200140c0582245100138801e1a1458041d090040c0c03142e08d1814003028100300103120340c3e00310340304000900350780350062800420303504088500d0340401920140e424a10349049600741d400180c9007000c120704204802c800700e030588282c42400c070a84500803503641e00d0290001c0d65010641350300015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 616635512 1250 616634262 616634273
    0x41401050f041b170609060f150904020a051f200a1101090f030506060f040e2a03030403050606040c08101701140c0304060b010207050f0609030309030105010e041110050304 76
    0x3c142c0c4008101c000c1680c1681d604074072404082c403200c070090a80100040112042e0103021413a030001d00380f00c06100c03e28044454041100b084000c1d01d01c95050400850103540b01c441e000310141c03802400102c1703d450b41c800182042c0c101c4c82841800950140f4100c1441c0d034070301607042c0d800c040d450300600d2082c2083e40ca03400c10ba03c8209825042100b465000a400c1030003840c5140210701420141005040040611545401080c100c1d8004d0b0f090000040c01c031040050490a2040b031424407481c48261550200c5200aa484519500d03220101d030110502030003080260042004a404100000e0304800c1910a48012a810310325440f0040d0200201400301d084078481c4030441d0000982d07020300b4003c414082005a131340d02002d030008020401084481d1180348070901c002d0008150862601c400030701c012200c0383d003c9004640105204810fa20200300b034072111940140248429a1200500394103000c00312825291030111005c054803a00f09568a4448500702c0c4d0340f120318550392601c1e507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 616636762 1250 616635512 616635533
    0x1b080d0b15030f060612222003070906030c051201020d140601022b03020c0a0f03020120040f050f0f04051510020c090403270608041401050f04 63
    0x8091216121a1100e00ca41e907400819440100342080c5540c8a0800c1e0300204032000000301454040c010401129091885503040140c1c4046440c010092a202c0b4a0b1201c081c06848107004021240d01c00c441a0300844030f5210016024068045980181d0b0380d0403640d050741c107941700250455018001c244050304101c01d19003110700c1c48400151402003201409412a81c5001e040880c02000c0d80034001250ba040c48444101b007400da40d07042e40781200b0312002c4001c0700c02080345014103070b00240c440d800130420300644010903000300d400303a160211400c01134007a00c032566200044038202010040e410b90007200340c41c11340324140c0411403484d0401c0d0a01501c0d28a000503644e01030b0020070500c20990b11405810710a10b000d1410302c40010400c4140f00464030006040015500300d8208802661680803074a80d0080d010703e04400740c1c00d04000c1491131005000803002c1d0300c1e00364410100e26a070b0010714281c0603d21480e02c15060244001003070b42214400d407801d03216440c0e0312001c9800310342142e48 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 616638012 1250 616636762 616636777
    0x6031205130b030c03150d030207150e031203070306060518040506040b04050a0c0807051e0708040312050918220825120e0a03030c03030b0a0b0c0d1b08 67
    0xc10340c40341c41d1a0101c40245800c216440e0110f8840001000900c0d4910000e000e09040152545c3d500c5080d01c0d900130b500e89865025441e48440382407240141a4030407480c0059813200581540d0701552000c3c100750b00c1d42d2003220400b000c24140900003908911a40c21906084842c0714254501820802008080c10703018281c1d0754001c3d21841041070a580700e204a501900f05808000b070505030312080900b0b07041000300741400784081844010403155202500111101652a030700e95100c0051500541c03d015540014280000c00c2042120700d50300036000384910042100c42904012402c09240c0b0301341800c40b9002e0848484103c0c03900c000145079009500548144881810894072110f01d681e150a10000301604403c00d020620920009903c8902c1c1409289462a050710103080418100003003448010100309054101c0030515100394083e03101d10400809400f840343e60341c91805159000304690b1082e6004d51101c66401030b005100d1060760b45828038000d05615070948813030f81030350072652 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 616639262 1250 616638012 616638037
    0x7030503190c1e030e011d0105160b011706340e0303180411040807030b0a14040f0308150102060628030804170105010e0a1d0f030a1206031205 63
    0x4038250000f943c1c1c2c1e080760f84815500740e500d0300070754040d0500402c00300014400906000100d5960300407284604040c0041d00400c0c2071903550388550124840b032801c0000e030042c006020340300c000f01c2c21151543e40c030300101450358100e40803500c5194251610b4001c41600d28003444a080b1302c1c000540425070711000c0281c1d0350038002d118007840780110f410b640c445409500440302440703000fa250711b030038460502068928140c080c20f140c101070426503a00c0d0140030107010101180002a50100b2942203840c166011449810550429162001c000349103ea000c40116912100050500d510018101c2c0e410310140d000b00116250368040c010160b0b10008988100011207600e60f00706400800c034000118482d940c5551703513507e040e0800d4805280340c1404d14403641490010464248140c0c00c0980140e0007103070005103030042400e140150803140d090740c40f03580503403585071030034100110141440340c400b500c82110520071120701e4030848016001c02400c901070000c01e002600c3c4140c001c0c0ca2002e2110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 616640512 1250 616639262 616639277
    0x9030606090c2109071a0a031512050312090303070206010303080612061f080d050a030f09050f01050604150e04060234060b040504082b0f0902120703050319 69
    0x2e031007250f8140e150b404100107a0f60003444520a000c0090b80010702c0b4010609031411480740b003200e080d00c01c0c008100f08150b00e40207a03a0910040079030301c074014010080441440c3d20145009512504138081a00b0503070340007000221404004001c50b4450100d50303000d40803503030075580c09031a0541c02800c03854002214110301d0500071070403c1510f0045030421201c070900c203201c1480108440c0290880c00054020340e440740019900142910885401ca0070081801c1c03140c101050014060510050140d2182140c41105820194001400f80341c0c1039a061002c201c0200c8030840e5100240704440e20388000c02c00050104280c0d40c0640020304407904c0440d103040b03020150b81d0484a00501524100810b00741410130011940314041038000c0c05c1e18240003d181907166642180988454440081800c107583d50520fa034a052a407041e00b21083e0401090350000c012034002c0120100072405061100c155000c2c070900094454104c070790007c01545440824101ca20003066078032511400c1c0301c0344 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 616641762 1250 616640512 616640527
    0x115050f10140a0e09060307031a130804120b0906090d21050106021f0b0a03030c02032107060f05040f0f0309080717061602030a05160206071a0c09030606090c 70
    0x180b800800405680e543c800809202803030801800440c060300c9544280e116031400c02c0010700c009880250b02d004100c0b2480c0503034885100b09941420704500030310b0240300003004078801c41083c001268680c0544100c8140b5920451125034684080c0c411945981c420030315045680e00c241900c501e2209000983e07200d9590030041d020590f18203810800140e000001000501e0201c04107020018500e40400e002c151640300215550030964080641048002c200f4032056440c208903000c3c080000d0304562000405110105215030418241140c1403418165807030030302d580034021640203a411022040c0d404180e03583d03215100322071a07011001c2c0a650900050160014003040d401400c40641000c4241101c2038480c0c10180c00415000da58001415182e040b6a03000099031101102418030b0341c1e0311003c1c2500039008102118000354000d600007140000c200d00501660043c014030302044419031100c0c090308045005031142d294040d801500010303142d1415455040c0c10140035641c01d071501c4034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 616643012 1250 616641762 616641797
    0x2109030203041206140c1b011a010e0301090b01080c120105061c05070312080411010f120e07080307051023040f020d12020c030d0c0807080a050f070b0402030115050f10 74
    0x445e036460000b10080784007c0c0119821540f5080d01820b880200500404d107103110070f015214100d01810070008559500c3c0c1e070344095100c4421290410010500e940e03641c0c0900c3da840359400d208074054000340d00d9141040505002e241d000b024020700c43c11046c1d1210300c540300c4c2181051819202441083c0b00080441c03404140c50300c0c040c4542d59528140c1c40e25040441000c00e01100d00c904105843c00c00704603540e40080f1f40024417501d003074007041c50700391910080d240412940100751035004c0011180200200018848100c9110810a0240c13a541e1035002d0180113a031804502e41030b546000082c00202441c00a1b0031741e520040c00c0d5400315656483d4800e0ba03141e40550040960f03c950f41220f92071030104212540b8070094500b03015048466034801c0318070701564034000d01c3c00f00003182e0503903c50700903020744d0f0b50f581140c04104d071a050300b4145400300c54800c0d1016400b82d440c20300d10345060410145480c6c20b640024058101d402010b20600c126482d5494110040103507040d24400c40c0403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 616644262 1250 616643012 616643051
    0x130602070b0a060303140a08040f08190e041d190303180b0612070515030a14090d0e04090f110112150e06120604030f05040906062109030203041206 65
    0x65503840012514114900582440c403081b11b0036508840501041e038040350300c02101548641d0003c010344400c201890820042e02035800c0300320030903201c140c0d54542690f101035246000703802101c0030310158144c403021040e90f031500310400005400a403000d803030030380c558110f501c03140303202c2c1c500000c4c2c080d90445003003d10840100122013404a0b01c2c0ac1c007696103048090008807260704009000300328903200009003a00310032140d01c04080c101100213520000c0d107600c40d05240000311200500c2d49030850400c0c3d00c988100060700041030a110118043d81014490000c02a41c045003e800b41d10390303905e8a1034410b0341184c1c19030400451307000c042002140703401f80740c9061640031131003404141403004094100000410007406200c07840340394141040e00258017600035405040200940110038000caa06100d203400492065050442c0011003c0d0301a1201c11fa12140100c0c00b1800050541010166901d003000030b00141e0052105110901003d071078038401c544544000160030380d6201d403201469 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 616645512 1250 616644262 616644271
    0x4030602041203020d090b04090e0a05010c02031b1b060f0d0f06180203150607020109150c060c020a02090106030e010e120a091e060807030b030a060c0905040c0503130602070b 77
    0x124032002c0352104168041041e41800201401c00c8078030b660400d2000d84841c0298802e8400d05a00c5a20481040005001101c81250820024000288142406541c0703078450247d272a061803220704001500100800c000c641c0000886c000c103207403101c0344100001c0b41c100b40e28400c0c004800308244e05414000744240e00840c05400d4002c9005450002d600080201c2180c884240b83d00400030095031503e80100c0040b0361800300d90a5803190f400e400103c0300707280150032005800b40408001d9061542009444070100d204800034012100440d200326140c80e04000000d4200d10b1140c01070201c02e01941000c800d018115000240d801111000e243c54060710f88070103840000700044001e0b205500c104000007a00c2a146500f413420f4200c5921540c2945034800c3e642000103200110b045140302c1d811035191024010104c1c0d082c03003601c0c24124007c20749643c040010404031403000400e41003901481c92a00c03442c3d101d0600355580c16080c120950180c070000c9582079401c101c0107001812010005004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 616646762 1250 616645512 616645529
    0x304091a04090c0e0c0a05040302040e07030c092c06060f01031b1d01090807060e0d0807050c0f0415120c0906150201051317071401020c0d030f052a0403060204 70
    0x7040c44c05800d004220b401070300f1031200e0581000680c41054200c1c0855045039410341d4005024100c555400341400c1d5240c01c014220001c0a80004525034030f0b4100e120412028003200e04044203904032042d50000750b007508001078010700d000503102d250003d54444041018140400c49441a05d24144440140610080402c100c801c200001c0022000048100324007030070100b030254100720810790b544542e032040300104000308201d0951612140150a15294030801d56a00c94515140043d15402c80c40b10690054000003a081210300e0070f8050811919015405118454102081d9003501e140262040d50401600c00b00014610717661310942000700350303c041c0300200f05d40c0d40e0002800e4801c094000351540c4810944000489d201c040000b212800c01142503a64101070301e80030b86900e01d100009104c652010807136034985000891001c40c06503040da410040707403095207103000c03c4510a840095440f0702d8124403805800d020502800003043c003030340342c078286070352036480d10280c1c0d1017600510b14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 616648012 1250 616646762 616646783
    0xf0501080d0206060405010506041518180f09080f0c0a0b04111005090604061220040f061b080705150907050112051b0d0b1c0c15020304091a0409 64
    0x720568144181900508100d03800d1055515000004106020b01d010b0506c10744401440000018041d03020131040804940b03c03804c0e0141c2c0c3e8000035161455000381c80c10003a080011400362900d1520801e008580c0c0209024240031003526018400d40cca00860000b900c940c0707021001180000e02c03210b11a611500784081c002203000280100d0440560744001030103400d0250071025600d0b6420f540c01e5540780d00d44100c1400c40c0d6480140038089e22101500c0e030100910035800c54005d054020000e1341c405031410f14886a8139202140c2025402c0205440056500245800900317408010030496000300101c403d50090141e0350f406c000401d035070616950340300b00400c1040e03503080310040010040007041044a45030505800d0081c001c1d003101041180d0307001640c00e00109580c0c0c000b038a00768020340401071500c05264003041601181c44160fa0061040340c0010f10f0384056205510060b885501540c06c06113042400005080784031020b0206540c1460880c1d05074a91b8401d1a4845014800001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 616649262 1250 616648012 616648033
    0x1d151c0204090209031501030b13170313050d050a12180c0f0509010e160807090b07062f0d0b04091410050901060609030f0c030503030906070e03011505040504060f050108 75
    0x40c6841c0400c1c4411b181484148010804920507800c0c40d6070081c10070781c0c5040d0350a00f80ca00114180704403801300743c540501200f40700d1658000203420b107404c0c0c0b00d203040354640030b030302442070f1030b079005004200c400a18001c44940364a00c140c0c01c500c90f040041c5000c2c102c00c1e0081d03038550a0320b1802ea00303c01d080e41c00d01e0704200520714148000500400121212200508154914401c08803030320011b0020310000e40045540544146110401020a9034110341c8500300b910705032000d480a0540f2000030b0700700c20050101700e24003400e000941c443e0115070501c0c0c0001c0d00ca03814058025901c05581c0540da030030444000c191300842e07035038805070850041c00410680804c034504881015208030700e10307031601505010345e981201c40d0105a83e0880307122000c0c00304030700e001036002045400c002e10600001c03040c0400d01c0000507140707022300803548030000d40c0c1d002c078000c6c14202c54083e40c158000c2007401c001048541055400590014002c0c0c42c00304072400300f108203400396a001e0340850307216444503113401c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 616650512 1250 616649262 616649269
    0x9101701060f080103020628020705041b090e1003080a08010620061503190c0807080d090b090f1e0a1403070308030c0d060608071d151c0204090209 65
    0x54003401c1c1c5810142140325040100500d00c01050000a002d030200050740000e0b03045a140580f40c1d0790702c42801d000c4000c440e40c1c0c000d40b00ca40c0c510401d070207541481c2001003050381c14548290a14003540c1c0e14440180f511080e0200100083c1011000112802c400b0001c548a10010452070220381c441e401c0d554174040004102c840e0600304205038042e402c00b0300314880c0011400135002841b40c001040c20540c0a80000c0c10140c4d16902c048805407848042d204021440c0d0380c0300c003102c03c0581503458090b0f0300c481540d159409c0c2c1c1c8001e4001004681c0130703c8441b6004002c4c05a20740e02400e018507132450440894020210b00320b001c0d80d80841d48a035040145800e0b4419005001060000103031608101c0200b40e0700c0f4118040100755007004030004600c100c0e00010703070304603100c89901031116a80d50780f4040c10301401a525070740000c1d0004613050030200e40022401d6a558042c02d080c0400e02c0604900c07042e90040c240000b41c40c95548400c2000d5078190000d0070160981e65001682e420640040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 616651762 1250 616650512 616650557
    0x2120d27061a09100611070f15020d180306050711030a021c0c210c12030b03060610021c02010f060f08160501090e0c0910030902122d030910 62
    0xc01d1190360001c0811078200c81c010448030071a2500e05160604206d408146402c000c055080300c504500d040c000040e0142c2c0b014048455040260291005c1c0c0d0201802126400d10100c04c0720124061250708100180c3c07603600c40ca502c0405458884c151800040c0e01c103042d42d01034140000107074041c9030008042808424091200509803e005550200079604c0020043c120454851212003407440c400400f40150900359500d50700141e0a01202c000c0e840c0640185503030100f040c000c2c419140065218103141034800149400c9400415001404400030643c2c2d1180900050840d500c6400c5240900042c0c040c0b04090031050304648040790401e40002d141004480480303003c0320720030008000b1645c000780d81d50b0a44621072035881056030f5451265030709100d0807800c1c5401c8480c407548036001c3c90381a4800580d1300e1080325804080a0303105a00303076440c440452104c802400c1110126a1404021180114400c110003601d05003141c40000a070740f00c090a50100219840c1e020034200b005070404d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 616653012 1250 616651762 616651811
    0x41a161410020721260a0e0102040308190302090916030b120d0216031109040804080601140117160c151104180501060c11040902031e010c02120d2706 66
    0x1401141030304000105d20143c540c1001d01903116078520085082c1da1340507004140c14100c0350b8020b55071a42d0700d05d0150400e030700408207080020350103c0c42c41300d200d01c40e000b02c074480f08001f40f011201d500c4000301091a160102d40074024140e170356001022a031610310315501c0303041002d409032a0204a024002e81415141c4413465000300001d8010300001d1a9518504404082928240c0856a95141540300e5100d1500040c480d4400c500001a1002c521165051400d07800e036907006120418183d403426484058800b2221602c1c030090032040b651051244020890103080308c103402c00041d010038012684800b03800401203000050a2240b841404016540300020090800c030b40e6241c01d01c01002842c3d55000201025030350b51004109036210381080c0a8107030000e069505011304124000341030b4070480c0c54a0015420a000100c5050021074242d004a85100c0401d28010f01007403c440242045070040c4179507080f070354912604024905800344c40e1403103200c002503061004c1001c0190302d4080c81c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 616654262 1250 616653012 616653017
    0x108100b031603030c0507081606030b1801060807051b03180105070321090812160306140f060f0403080a17040f1b09090602041a161410020721 63
    0x80b030740340440d14101080c07040700d0301403910a02401c51440c146041022607840060144100c60500074a44010b41d82c00b401c0305c059450410040102030305200d1200c060613422094404203100401266002d59151684207520389001890031000c21005c3c0c480c207040c8210024180d1011400004071004446543d0b0621000d003080c5040006550380100421214195541e054001e40d17000106055507400c0041102c2d480380c0800c0c1c070307404902280d4039094811246440001c00342c40c06000c0c800e00138403800042d5051030458000c407c20a5040c4043c06429110746500480d0030403419542d1840003000c1e1000d54843c212070750f0380d5031151500621003102042c035110445080018880020110381c0c000140300c0d4011080e01c201c0b507490212000d52001940715000d0340e42070040b071000300300740c650051041d00c0480000d0130701d101d860f4440c6041800340c894511908141409480c010811a85508002950384000c54011883c04500032007640c001f0001141c43ea4a88050980c581e005902c44070001e0401c0d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 616655512 1250 616654262 616654273
    0x203240901030f05030904020d0b030c011d09060a090507050d0f02040e0f040f02120703060509010219050c120703120b0f0f13200309062d07170108100b03 68
    0x180026501500610009258121642d600000c0003018416110340420040085482d0b44c1004c0c10720003d0010141c140303129018652203055036600032815402d0406480c294542c034512080d041c44a14100500078031713480300070502c00040126140c0189031103400c1036660755884045034a800829122b0300000342c2569030042c4424003109865545c010b40c400200300c1100b2190710340b418841c1c4d000d2003007a40070f900705403610728140282000042c164100c0b03102e00010825a036501500500b00d020b502c0d4454228804940518042c034407580c081c0c141811910161007418034498055420750b801810200c0109800e5040442801d00354401e50780015003e0312001c0786207030b5050000d1004142c01002c10322807001c0d40720300f070210fa819074050714a01030004007070310540400302d464002d15002100d04809070f21a400c0010341303008100304445a1000805001c04145407a0341021034004802400c5508000241614104041820011034000c0008a01602540c01c1c11302640702500d01303216010780280e114 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 616656762 1250 616655512 616655581
    0x10f0c14031c0219050706020d05040b160203091810080d1805030a020a2c040503090307060c050d0804111e030106090b090f1305060f0105090105090402030604030f090f090203 77
    0x1801111840b070002851702540e0780b401403a010000740a9101104011803611040104121120f001e06000b0369031000d0008400483c5001240c0d41e216440e000e0390002d00e41c01d600300651200030109504000c0d911000d0004a88a0b8142c80c0b43c83c0030032030300f000040e04551281e010340c5106d1480102824041d0050300300b54040f0740109182c42c6080c4030b46c04040079185c16652802060801081c88650400346010031703400c01c0d050482d5690071030300c0c5642c46801210400511680624000050b1030381c0100038080202d16040c00341d40c0d4480040040e9160b03a10440822810b541d00d03a0720340c0b0340582c4684280c0f58100c151090500b12415a04440d21951614011000e19070ba10b114055104044803034a10781980e030040445a00000704c00c008085105190a0207400041510400d06a038010360700030583d41e0b80e50081007000030050303c02035016080400804c02092041618000b10080e6042507400c0c240e444419081040503a80f018400c1130740030081c040c5040c1c081c01d0501c84e0100b900d507002c155115 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 616658012 1250 616656762 616656787
    0x30318150c080f040305032218020906090406060807030e0304060e12150f0a05090601031505100506030c040924152c010f021b010f0c14031c02 63
    0x6110590001c0c05030380199803040045510032a41c11a61148183d0348507a0f80789015a03a98100782846103c1556686015403008003020038141240c500c480c10f8140000c0103100d601c003c0d440002c4641e0400c0d420010003100d900e541c05600000e15086e59900a545044a401021642c5851504086400800c800c11030641d0200d1142ca4000048400c144075002990388945404269000303400442d40c81030401190701c8181d03950728400c4941d418140000c0d07903145065900c41c002404000c00990004004052120180d0300c0035a110301c80300185d441c8641c45600158094102b02d804070030800e000181849414418003070100580d01e0800704510307094501c0346401040706227002e49905066111900c61041f807040180400300044101010103174101e0f140110621200800c2070740c08241d680b034403c950148005229401e2803a0500a0f0501d010420011030300049920f000904002903038117000701040721071584d101c0c0cc02940000b19543c0c1c07841114419030051810304203466510504c1407502418 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 616659262 1250 616658012 616658039
    0x1e0b090106020d12090b09030703021c050a080c090d06020c0c0108090304031202121305151c0203070908100903090e0702100b0a03081204031416020927010501030318 73
    0x11850401404135901c00b82090002d010f405000ba00c000c200b82c0511081e0324011006100d0341c4c1c025800c0e1000100703903022441018400100d0400080c0040000d504064410040720342c1007100d25010750725180300758000400283c001d03141624bc06034001030480c41440c081200400481083c00c2c55000351502c40d0301e080e01d901030740c80301402c403003500304092105500c00e00401c04d420300c001d00b26540703c08007021b10942420403402220701030516100c080c40c00005080c15184c0e100807101c51154180002800c440289d007000c0e000105020401c000420404810700080030148030081d000541602d540c14000c1c074039202d0f84d002c20340030784d000300074029400c3d4081150718524025038004070b900201580482c40b586225070010b400c4080106400c0010704100c41194005d5000707540e08000408000206845489501c45942050001026a40c0142090009542d000c0310210b51103002006628041590f581d58000d400c1140c1d540c0c00042c130415812444080c0303440c00460401c503050b0300300039040f00c0b0300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 616660512 1250 616659262 616659283
    0x141510020c0405040302030c150f0c0f0915040510030506031006051815130906060b03150d150216151b0309050705030d09050f030109050d0f121e0b09010602 69
    0x383d0f00d90303000400b45030080048400442d03000044498001001d14070168424050383d00c3e515500041c00414a9115140d056480380c00088a80394a40020441000b0301105010030312a8240c109001c00103056031110b44410702070b102520041000e05c0e21008050034000c541402c40070107840c1460600c01926404013070300b501e1803010760717045164075004030074004903440f089015031240403e01011a100420b40080807101c0c82450300b800240d49440c4400d8450008440c1c100c4142d42c880120045850302d6030031002820702070006083d044125510bd413040ea4040064100100d818604d10301c1042044081004940c540300c800704490044100d10003000610050b21008140d00d60b42103406000c0140034540003030800508a07150424000360203484484a481402c1c400e06c90822084e81a003010f01503100c802e50302c24003418100080540c169017516030300c5054401c2040542c51003030720459034425035200024005e1a0045441e860705441e0a03500414402d502511404004000090300042d01000300c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 616661762 1250 616660512 616660519
    0x31704030e1203040b0712020c090412030903050c060a0c09090c05071106271903050304090c021e150a09020a0303030203060f130c0206090d020304050f060c01141510020c 75
    0x140344455000b90302c1c501403900501d418060006609080150484505c03180ca281034003a00c10030050b032070030040301a01c21079020384000005514071510341e00c0b81e070018800a1080c181541404e42e03030720200d40707058000c580050b00590344200003905103400c9408403001342803400c1c0601c0040350744600203110740100c010042a103118a42c414070a07940783d03415101e241a081d5601c40d00c0d040e480030001101040303980715900481d00d1450307a402040b004040c10382965044802540fa151400c4003020041c0010a6803404600034215175029103181c1c100c0c2403000d407140d80007c10038210a0b038680c903142c8002924540c400e610b41142d0703c0044e122001d2a80403242c050800584071794540020030000100d5241d075513481380c0406104280400719600a410346a203a41c01c880d000c1e5200282c25560301e015802480c00740e0704c00e1004010914082c602c005043d00301800c0c041c20800c90054860940c0c500d021648020429201004050b0b01d02011071410700c2c2044500404400720340310080d480f000c010708850f00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 616663012 1250 616661762 616661779
    0x1209060901110303130c0b0a0e0f030a05101a0d030f0e041806020d18051005041104050115030c02011104060e0d02100c1a0f010e061503070c031704030e 67
    0x510742e002e00c1c40d000c035503103220040d2640c91401e0724440a445504000855500590150108602d0f07105015035058120030303161040701c9521a01084071201c141c4081560600ca00c684400c0000d2090141c1c09040c4111720f00880d1240c001c007815912500c4901005003e000d0510301c26001c01d0388802e600000040c6424170b43e85c09103001022074054400f0003c0c030001180541c50080807ca0310b54010306441c10103130800c0004c1100d0909803440c111406801400ba54840100c51205101980c803085d0400d120385d824000d100060008102520b4090303004014081d00241541d8109415014945100301a84000c01410008070341164032070040340160420003505a400141c03c1d1070b0130401000c181d40007803e910400780e00d468002e0050045203421184440c42049640081c0400000903000f48a112000000d0f81e003044c40b1070854036402000c5542c00f000d08407500d005241e87d40300131070240100f6913490030214000e09000c0d002d90001e0a482104040316410031010030351002d814031200108541c40c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 616664262 1250 616663012 616663027
    0x320041107030827030a0909050708040803090118060905150f0106030b0103150807051503010f15020c0a0311030705060c0c06130f0618050d05120319060b0403060e120906 75
    0x14680c1030000c1090340009541c4d8070008202c00004050640c403401d80ea00d86c1182a2110448030650740140c4168000c543e240c40844c00203010311029685c0051341c2000024070300721155100c0c0c24040c0e06402030314840d643e180c403082405018040098118150380700600d541c10244915031012405208050405940d081910031a0303110b038100903a140106940e000c07440d511889440e032900d80ca07208051184094851180c011105081aa4102c410f8040c54500c1c05180c03142d558111240c2204090031030260059041c0a135544070301c000041c44c000e0900e0f07070b4554200414580713050180e80195100f00381c18084180d081034000b60042c2c0410058900f030b500e48002d01e64421118400da0401c00b583d03030200c0d8000c151541e11a190000c48a1080c0f1902c010307581d1401401041d00000303002401e95000035114582442d800d80003180c210400081800300a6104484c040c1100d5441d04102914400001c00f0010b010481c081c14a803141008060031030100d0b4044c41103058070401e001c45001d51408500302 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 616665512 1250 616664262 616664281
    0xc080403030c1b08190f0c0602030402060d05040b040c0b18120316080d051b0315210102091512160909060e160207140d021903200411070308 62
    0x81103c0a400211098889180c0c80c110300325030041007030089a0741e406440b65989a20405002d01c401c46a82c42d1242ca511113603d40c80003075840284280d0701b1040402c03407020343c407100340304151042c0d00411070080c9030f0400b450b01c8030000c01594007070544a24240300c0c9640600e00003296040c400f400b00c0d0350901601403000329034103500498103448a03e01c0024990703402d0014080c014490503814200030080e07987c444042d022f03110b040b20342e2041070050510000d040110103100c00c0e941c421004000c0c614071030320340440b01d0b102d4003d03880c259031300e17500810f08071030f14200f84010241221512300001d0a00c41602180050440001c183c00100403c0d0389100c03540360b010350396003005091a90740c107000f103d4036900030042c03c0c1d07400c1d02d01ba01400d10310540c44050a01c081000b400b920711070144100340c101d00c070041002ca410504010303a808406203007046102d09000c0c2075031006600c034420900b4040003080203d6004003c03500450f0090342818546c108440705c400481d1090780e03040c01d00f40803035203409805 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 616666762 1250 616665512 616665527
    0x41430030907031407080607050f1909053303010302030307021314011211010809031602210601061d0d0201080a0f090804090c0207081c1e080115030c080403030c 71
    0x2400054521805100910011917010250b600003002c8840c0b40d11044012a428401c5610100d2200782c103000054640641e02012285500685880250790f83c88500040d00c4031b0a07041146a01e0604600c118425240810401d000c038202e100243d0942d0300d95000300c1d4403032081000003403198000010005c4851082d07400400d104400c0842484690384603400391b00b00f5032160390103451100c84e15940021540c802c2d00d03854418002c003806103082c020301840b1b14418641410089922078201090281c80d1108003410102c0d5101000040c012945001e2016005040b00d01c1c0d04081d80100110241d9035840d08042c05082d00d60a01e170080c0c4640d5054402c1c07008041000c00003806506050f06e410138000d6440c0500240d59601c00100310310103100f00c0603a9640702038407400741150810350580d440c08500e100501103284050030220510ba4403149102084490521807a000c502d040c0014000b4420104808090207050304007000990000000a0801c950003003008080640741d10030120b07414480c401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 616668012 1250 616666762 616666769
    0xa030c02030a0b0112230d08070c080d0c11070e04030507030c0b090705031002090d021306030b071e0f200c0d060f0c03050c0729041430030907 63
    0x403030f802541c507000c0550007055180d40548000c0040b0b2084403210320000034a00c410b4080710000d0411000752401036441d81ea008140c0000e10025400f66070110740c02000400c1080c105100000d003d0b569a80041c0021003805190145076019080c2070140351003c0c900c0c542c02a07014180240c84224034601154a44011302000b00b003641d0030018011440d5001a0382015070f24106c0948030b107000505a104100d0040e02e848a238042e40c00760140015050502c1d400c40045202c0d400441c0c00c0e0784944034200d41ca40103440503400501400001c40c44210b284140056080d914a852010712050100c010280383ca030a02d038900425420030b5040078642c00300188080c4000140c801da840419500f40400104600040c10001c0390400d14910013551292060340d00c5030004032580340c1800c9140d19941d1507010078200c100c083d60000c9000402c40c1e230801c04031720320580c071503550403422100c030168030390a1a884c03038422001d240c000080540c40f03200c04406441c10204d91036541c0e4483d941d000c002443c1820315030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 616669262 1250 616668012 616668023
    0xe0117070314010e01060b0316050d0213060c0c050d0c140a0503010c03020d0e300705120301031407180207030210060902190207061706030c031002030912030105030a030c02030a 78
    0x1104000c811010b4000819101305540200005543c6140d0f00c011848126074041c04a0b18819910740314601070740281c03600304d451000041c1081103000701e5a22000c41a0440c20114100d0450402003042c40d40152019000941d09603000b090701d981c0e0001042d07002c0c00b9954049421401c80001074440d05901c1008001c014002e00042045e008050020b41c400701e1400d0100c1d091803403c01d500c850005000000849030040400758110b58441c041b0055980c1c202c02890503010041580850004c02030030320034040c0d00702e05681d02e5145191548202c01141700241498107c1341040118032000400c006190111102c0075a40d05c0f400d24049042485080902c80810310340b510120f04004554041c10030440c0c1003aa08181c0f01600e0416655090780b489888000b4070030394103c4d00b05014a41105400c800d0140031a076102c0f066000090500f91480d42c203140071075000c810010b284d03a0400019209240441074145907505003000b0030348505038400040c0a2018a808450454a0401c040d2a050340c019 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 616670512 1250 616669262 616669283
    0x20111190e1305010807051905190e0114100e030d0809010f02130303230702011206080d0f02010b0103060b04170f030c010c02010b010503130f031b030306080105010f0e01170703 78
    0x181d848400400f42801340d40001d11450001040f181480c0e40d000c81c580c1801c0216625842c58407003004004080710890401481c013850000400e01034020f1258042c1c261041c0f10208041d842051040400140700181c00f0420080441c04076610042142d8a002599241c28251951828640c0340540b60b4410900030242c40000c654848800c40030a071030030b03280702c0c0c0d0300d41340c142660b500d29944070881d14807100440c0346e00f044043c0056004908020b80b00242c0c1c400421020741c2c07056400d007461541100c08021800c0d5081d0030000ca58280310318000d6050074201009454204200c031201402203018502144681c40000c0344014410004102400030800803039075505054082c1c01d01900c0e28001d00000340d030030032045890721340c019400d59205500c41d1f00403034206034054654042440700d101d002d4042c040c100c1864072003070540f000d81c6403190340246c8000c680d06241c080100d0031070310141d01000c04c1f43c1c1420424825099080070b4107045400e51a40c201c091040ea14240e800d05045a1004200d410803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 616671762 1250 616670512 616670539
    0xe030a03020705090901050705042d1805090f1506040905070f031b050603060f0a05060d1e05040b070f182705070e061303080315030607020111190e 65
    0x9140030070fa40c1c0a6030301d40600c2d02d0b034001c04d501740d8105071401030215100780420b01c1034910010407050f1000b01e8003138482d602c00c413041000301881e6079900a01f040880c00c81c105043c4403040e0140603008089030300203189281000c07020588580c1c041404440d03020032100801c1080e5070b0354108503ca95040015a008150b40d12000050507100d44811074201d2001c1001d003680c102302d16000c1040706c0d005000c0d1891030b682e180c00c200c02c0c6e8072800b00480d445681e40e0008103145c0c0f00e11010708128414442c0002d010254443c130703001c141c62195140107020303050030f04000026808046542c0c01080300c1c108500b03442c03050300094078000c10415036003200c2d4800f06000100c0aa26000c45c0b80450500c0314030520304202c000c81d440039a401250132001243c1d212004014504240d0010540e88145c2208000c0703240c1c0b01e540e001d4860740705852039203405801003103140640c602030000c260007090a000030003c50b000380400e00e401d8006c100211200b20105c00580454500035042202c51017401410036660514 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 616673012 1250 616671762 616671767
    0x50613080d090509151c0303140901060602010f05100b0c0a06020f070209060d1a07090e04050c040c0c11090c0c06040b0106111609050a06080d020f0607090b0d0c0e030a03 75
    0x9485900c0c0306000c1e89004c00c80c0c403c0c03d440c450710305c81d6010f0803c1c680705c4584641e45140381d070464030450801d543c0f04060b072590750040c0c130ba081c024600000040383c03031450800c00a0a4509054201d2a07c0d403421041c000000300c030040705800c54485004660316410158021414a41c0168010740001d000089040c1110b100708000e0010034421a481c00301d85d00c40d203090002d0301007a660000c10000180300002e1810700301d80c101951003103c1e41341c4000000c0e260044482608000d403001c440039400042d0390b140902e09400340441c01c2005251403442e100140d15200e020b0000124428007401c4003002040441c03001d0000c841440e6920011203155040c030b490038258404092180388005070852541c0e804030280890303480305411829008000d4076003414040e81c02000041d0030481030aa0321000083c0c012000e104502c84140380b5009840c02030640c2d1162410110024100401c209400006201c1c150008068a05101ca4110300003140c1c030b00c904080d114112440400d0f5450301c02e00411404266 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 616674262 1250 616673012 616673027
    0x9020d050619060e1918050c100314070f0207030f0f02030105010501090b07060f0b030f03030708010501031803050d112208010c02061b1c020301081b0604050613080d 73
    0x11000988000c8900c1c50035502045410070700555012805890201d0f0441400c2128805c02d84004440014107415080340c800381074031400c1d4100d505410581400c1281e14100440b0310710310042d418140074018146040d04041a401041d400078418582c1020325403902c00c220010145a0054510441d42c6c85400c000719009031030035049100303600f0000041481d505c00c16082c41103d0b401d0050714104412995800d002c1c01d040041c03000f200d0307661942088070383c0d820840421750755040310207141d03a418280001040110143c021a0516003800818403000b01041c50aa10258240c9403441d254007040c0d100da0007411451540790b52502d004203205002000c6d00c489032078030150440c40250300a036aa0541030a84428000c00000340c1c12900016401d00355803604440c1220344400f04502d0316046030800b0010900005008054690102c0140202041001507024502c100d2541100c041c410342c000811510036405035a00544000c40c2907190609010b2811014102c54010794146910f150030017017441c23 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 616675512 1250 616674262 616674271
    0x17060112030f1412060f01020f03040504091a0a1d010902010f0809010b040c03020c070923060d05010c02030421121202041809050c060304050a0305031504020a0f11030c07050906010309020d0506 85
    0x15100c0309001241c6e9800001e581d030340210700d14059402d0914100801c00188551082902c0d503a80e010140781e624072100103e607105082020000a0300070300324007100d241245c840b002407030503891300b4000b0300542e070490294030b0705034260b251a25865030362120043c0504241d1900b1034019003410b080b01c25a5400d50041c21046a40320119484039030789069003800d0702e15511222400171404459201080070302c0c0d00b2994088006050404080965961a0300319007206500000580011030280030420b214000c4140c020302ca00b50194401409071224402800094003000a0115045410b49168419010741d002400d0906140d62814054002c9401030300903044d08880d035008040340b40040c3e14000c0103483c02542c100c0020300d00311070a0780e030507105ca070700261107510720451100000300c1c00d982e00e000034503d52000d942c800b07404204103c00a84580c00c00c0e049100c02da0400d00c054884104000341d01e070100c1e00200c0b000001911400c005a00400c40c0e00b10194024420032075400c240500003455038081e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 616676762 1250 616675512 616675519
    0xa0c05090a060e040f0501110d020405090106140a0c05070815040506090102070c091505090408070b0106020c1c080c1c0206060609010905040504110a0f17060112030f141206 76
    0x859807080e08032000c90320346000384014410031102007408913503c8100d40604c24070031000082d811050075000307060b039080000110320940d0001010712560800c03d16103401070816087c0000b0040d402640ca0031580184003c04080084030360440c000d204042002d0340c010b00d10070040da041c03020f003404441d00300c030360480303013919a48900300118181c59014401c032100280c000d407491000750304062402c8007a04003003032108800e0383c004101107966601c0140341d9008521608600340e54041c01c0c47c1c0307030201000580c0144c0540d08403855041a40e11414030030102c107580c4d12101000c0d14203c0c6041c000c64003820007001083c0c8604450620004021040300742c0b00c140c1d580803180c0076a03942040208601c16007070303400d00003194502c0401c69030a040c8c1006410a10480120309407040450120701c1d800d2055000304290304580b04100803030020b0300c7c01c17544050303891005810f803503050041c1e081d024001600001d040003409107185900314429070196500500f030030000f590340c031a03603c0c211114641c107131143ca10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 616678012 1250 616676762 616676779
    0x2410030e0a17120f0106090b072f09070e010e15070813082b050c100c1d06030408070f0203121215040504050706051804060b0307080c07031b0204060302030a0c05 71
    0x50141c40704c01d009040340c4170356480030740c91030901c280131f0007a811554040714160b0640714000b0f45003000842c8001102e5544a258944a13070410401140103005807542083c003041d580c0c80c040507640603030f660581d800d095510040410091805403040d01c15868040c210350300108446d4a40c0203100c4d0507808584d030f140116240c107245200201200340d4414901044818499806100c45000b41c000d41304442d1428161900004800707089000d485400341b9070b000040701c210502d007200941c03282c072452695096840314110700d000c2d41c4004280c0304401c0c0150051007204401e40c00c45d0342c00c01a1503030100003000c4036a15540c02c4d840820208200303030349002d02030202c2c12082019042c9880380500c030365006002042c0103031030480305442a0b07014030002c064428214401c0084c070740b9140115002000901c00941d683d1070311410040490002400070032400c20200801000b1a60051156151203038a003030b22048a001407000400600745036000a405028203d00d000a02c4401100c440803a401a500042d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 616679262 1250 616678012 616678021
    0x180b0a0b09340915090f0b0a0221070f06020304020301050604020a0c1b0902072004061203032c010515030607090b0c0102212410030e0a1712 62
    0x141d440365000a03511010940c150806403030789284001c101040098140581c1464440300001841c02d11400000041101c44004000c5940c0940941b0000d0004c0341e8924102455500002d4451000c01d40224903403106a0b1400d21010325071080310343c0d5a90008101101d0f004034074102c4043d400849050b4420b510b044001240ea04150003144d00d0500980c5e40c202d6411025a517207659001c5c0301d4008202c1e0b403a240e401041e22a028802004d15a0140c2202c0d0700c2c3e942c03401c0300c0755030702002c0109540c000c5040080400c89014030b01c81c4d43d042d0039403508010869401850340d40d824110400c0c3c180c601500040000b410120065204a005000300e01207007406100c8074050545e5801c1c1a1402c8000420240c000c01c0b06491400103004000c149a0000d07140500031000d0396002102e100c81180f840c07503850300b40008548031000410582e40d00c002c07104504c11441d000a50f616880d0f121407802d15864001c6003000c45170a121100c01030350f01000c01008010228440d141a400c00240c0d0300c2107500190204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 616680512 1250 616679262 616679281
    0x512070807080c1809011e0e0c06041203110a060c09060206060114030705071a15090a0905102a0e04060e040f29010e2d0a180b0a0b09 59
    0x20007024a010344544c940440305201e4051503500208030389455540d401a00d00000c01c2081352041301c05816a02103a06604588110300b0b181d00e030081184124010001003154200c20090902c6294241c2009030001c40d20080860800314448402440545095002c160b000d800c009400c044c0c3c1c40c0350f400c41e14141e132010b0041d200c0d0f811032210384c2d20b407801c240005003600744100c00801f40c540c42030b10b001c3c0007255000d01951000c182640c0c400c020640001240d103481c24480325a540c4690010428040c2818940759941c07200003507a8140c1c00580c48035103203a6440c2e9185180d02c1d201c0c001001162455604030702c01482080500401c40c82903003480c800146441000c080e007030049400405601d28034030943d41d04400342607140244ac001c080480540c00713160703c01640c080c2c020440c8040205091500c12000301d00e0364002100c001c801c00d1f01c0900d515000540140455000324100800601510005100c0b20466000c280050401c043c240070010001e071650030540c3c0b00c00042d1031406160303c13100c0f800c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 616681762 1250 616680512 616680523
    0x60c0c0507030602030a0204050d050f06090d08070e0d05060703052505180d020306010305010903030b1f1101020c0f0705030c010e0d06090807060f0b090a050720010204051207080708 80
    0x2a08550101e5028004038409500441d000039143c0070061034180e4071000308041020307801064619400a045000c150341080c8089940245840040d0240308030600340a0320918015000f2010040103d40700080c580360551120040c9410000300c8403546401c8038000e000d040112803464401c003906200c484041d03245040a20302c00c1c160780300c441c1408611500801d41d6003011100c554000940c0100e01301688082c0815800b0394042d10005c078491625040c040c055800c00c60040c0d000d88003c1100071001c0700008008404c001c442e1803c940d0f0401d499a4103400790103150064106030181c00c1c00c0700d01c100400500d501c22034105606507400280700c1e500644802400301c034225003000c441584940080d040c0c1d48080f01d00d9118841203810181141c50b814101d891101100560726a200a006e02d13078174101150340d0b408010f0b032030306018074600a20010002403c00c00c40f18000c50704c0b00e4141c03990300001e405980180c01d01078562041800c89030802590b0301010300c608010340c014101c0c0451f901c0c402080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 616683012 1250 616681762 616681787
    0x1a0d1209080f150a0207060c050c01060e010f0603051801020c0d1b0803010605070c08061e0907050f040902060415020c01140906070210031b1d0f1005030702070f08030403060c 77
    0x1e843c00140300e2010800d40e102c003c0c40249881d50070842c140003d0b000744a00b00300e8103410703030700d203625000c40401440c06c54126412802c0c100b60254010800501100c10880995015240100d15a01e46895000340200482c1c60031806500200d2407004243c4005401031130b0f50f4203a95a2480084070700c01003204104480e0000c2d00700d44080005205050140006104c100d200303409052a0300da40d11181414114144d0352401607486150440c82030855020b000382e0440d01c5032018003191480c000026030010342070482c003401151905902c07030a65a030369081c0c600070302c0c2e0401c0b444265103140c00020b40354200c030489540480c442c4600701d0000c10f880c3e01605c100c2e6038090b1483e0b10b80000c5408100084103a026050b0400d9210b418007185101008401e001c0100c05440c1d408030400c0c0e9244a503416061a05824024550081d81c1c3e40c05075a036400040410505092042d501d480f0014203e003058006d4204407101801002e000030030400003c004d0045034001d81c020407801c0c400c00011078a0b41c0f41100b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 616684262 1250 616683012 616683043
    0x20a120908030103020f0303120907180e070e0a090503190206070203250204020d1b030606050c07032a1202010f0809031b030418060e0105040b131a0d120908 69
    0x20044c00107041a1040c8201460000d044a040c0789500340b0055110004480c4140141c0103484100700e14510001c101507448104070b01840600b580c65a451713070300c000e2446000c4900c101500070030007154950344074128060b0011b00352680d03454400b015500e000c640800d000d00620031703400020845817004c004d46142c1d0307000f600740788410b44130850442001c05d800138081c1c0e8090741c00c10012503c41664824119060b0310040a11600303060a8030240c00c50300d0b15170164050000803c01c0c2d5682c403c010601c4801e8030360101407561035202c4207003a4169144181c113060280c0080c27075404039031f2000c00d05402440324400d0743d030600c1190700424100c4544005403144081c60b4018441c0b840e1481b00d40418281c0e82f107452088a0610f6540c0d080e128584030000c0c1d4040f40c05964080501c94040c0d5442c2090140009840a0200401e5040070500c00ca110f80700540c40d15a0304c0303102840d4880c80402c0d00510340c8008010b03544980080c1898a81c01520245800109460300c50000b270543c0085111683c040c03003007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 616685512 1250 616684262 616684267
    0x130f1b090c1d270703111b060a270f0b07090f0b070308060d211101110c2a13020c0f210c0c1207030308310206090d06020a120908 57
    0xc0c0701520f04950054140c02c00e1584484500c0030091a000192041c526444101d151240346010f01e01e042c03801c00b074513a02c005410002403c26101c034280c14011603c105840a100c032413828200003e2189081f41c00130002c218800c01d020405501111140c00d8440400044208541c0d40048660f548a00040107011500ea040002d68502d8154200c1200a00903907a1800101c484104041824091442a40811000074003107a41c00401d10401c0008004680c005140c46080d5182c55502c00d40c1c9203001401010f00d040c0307000f68820510700511114006015000381191968040019401a0f5140603a80c1f04601c2424154000040e4811070b58803400501034540035092500c0b8043ea020343c82d001380ca0720403841941290384a488448170f450b4101c0010340541411894010070400e0301074000c0210349010908414240c154600d4880e81c00891040410400c106101090072401100113a030703030144e0008003500c244510354004040003440c0307654402c4842d1034098404211102c04a0250118105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 616686762 1250 616685512 616685569
    0x623070f032d08090f0606030604080f0d0e1b0d0308012603120901062903100e0a0b040506061e030a0908030c09030105130f1b090c1d 59
    0x951007603141041c56400400000c0303002040c40010301d4080d040000040d20f100030403800740c2081c400a032200d03040c1c001618650400c840060756500c80603002901c0034200003480862440301c00212203600712141d00900141c020411401c0d00e075141c3c40f411111546009524040900d02032003c0011a0f03850b4961141070b90800c14042e410f0190016541e00302c1c1030100c0b0f0310b26180710400c05052091103008545c1c80070701c2c200c290365007940c2d450f6000003c1091107400104504116001401058501c07000385c0d501d03603543c0000100701551540c00442d4030740d1907409121107002550001c40c4107540030354040c030080e140c030005d004540c0f00c0d42003010312001d00c1e410202e4414105000864200b101420b0208610707030325446c1c0c915180d01c103454404109c60700040850060400f030081503800841d1840c6002030940b242c560003142e1308030400c0102001c11503a03000514a034086000300240a008074100006541c00c03001030880f0211505076803803000a03040c407480b546000b65880f54207a44661194991824 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 616688012 1250 616686762 616686767
    0xd0207150f1d030f0106050a080601050a120203030706060b0304170c031b0f120d0b01032007030309150f0b0906061c020405090f180a0305090120070623070f03 70
    0x44034001c02c02842e41e0a42092041e0f80c0400ca0340282411100c0009225440c00b002c0007100030180c0e1258255402a0004001c1d40d0342d05000e0104551b9040300500d100041840024194420618024406481c10601040200404000d5480385104070411112581130405040060103080c0c54003000e0780c8100022042100341c042d064001d80c01d4042201c04020703c140f1904c1c10001100d1128102441c04525074120299500800341c45100a003400c004100a21a60300806c0848400382001c401000514004040c0301c2e80c0240c0300e45410042ca00d140d1440f4100410280a0f082d0b00384030b4250410200380312354134158103a40d01034800202102c0c901608642400005004901d216403244c0d03003840001420744030782890a11903e001c20380308c1503078603200500c1d5416484250f1000c041c2d0740449504170020350080e0032140c40e00000d080c0482070094400c0c0f120070081d460350f00e85809000f2a81e0000d800c942107401a200c0c6c00d03085000000403034040740c0304042c6006400002d0a0f03509030f00002c0c00401d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 616689262 1250 616688012 616688027
    0x60c02010b0306271c02100e2109040606030b0406170606091008060403031b0c020f060c1f020c010516120b040209120604020a060c1703070302070f050d0207150f 71
    0x4143c4e40034040d40c141215140c200400c1070710070090748001448048032213505011294040200311010803507000c2c100340707485da0b03090b403c5507c07003642405074480902801c40000f03072200404000c100b400026180e4400401802c3c403003c00314003a5040c200003050f012001c2061094030702d44800142000d6480208100401030b0107480d0080301c040b0020007040340d0809000071481903010740c8000c81d42c02080071458070301c40d010680d01010080b4002c01c10700140e56140010100000403078078544c440d182d01801d9420301d99050b1b15402042d00f0043e10590040d4540c0207060706c050010000c001c01e60703a48600d82000c000910b0301ca400203040c61030000e922860350f400a040310001820050401041802155000b42d0800801145500c1481000110f10700a1901c0004d0070561a010180031101c3e51054010400c90312001d0510318041300013500300d8425415549280d070029100441000c0030304101c0d45543c00240580014010148042082c030112160fa40c51941e1503642c103044450f04000465006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 616690512 1250 616689262 616689301
    0x11a09150a0308040e0c04060c020409110a060809070f061e030b090a050a0f0b011b1e08070308060415030b04030207081e061003020108012907060603060c02010b0306 73
    0x490488859000603214072105802441c820755025a4840c2440702c03088251100070710b030403c8050704000a001c8a54442c80106482d541901c0100e2110074604e09011500c45820140e03400a440c0140010072030750150b41e02d80282c0720340c002d6a8049486d002168a21441409414045840704030128050911641104080708803490300090100300b000025a40c00d1082e200c0c00f00326915241403080082c1d0b43c0c0f05a1110101806041103e0b07013100002904078560a10448520031946003070b0000e10440d1000a41607000200030302c0300041c2d552910a01681003182c05500203032980001981c581043c1c880c0c002c51a04680c4e11103c0f89103140e43e45280e840004008034114060510009141e1404000d09800c540d20310410340039200c08203141c04c0c6014401481b070215425920b0040001d030344c12422a60664021482c400380c00c03a00c00001260300c070a0703004e06130300400c0300099180601c8080e40c4000c080c0ca03c00c00d002d01030f20907074075802c07400c1c0c4403043c0c001640f41c0c02010110f8009014000340e02411f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 616691762 1250 616690512 616690531
    0x3030118140408190c12120e0a05010606140f2710050a030c090e0a0b150d02070c09020324040b03070f030b0f090d030f0605031902040e011a09 63
    0x400341d012040301c0000242d03821030303a43c1c0f40881d10b081064260003215240b1807807850040c00c851070a8441c2071111018182d01000e2007070b890001040c507003c0350010700720104030320200c54044003a4030f05180203218521500c80019500c3c1c2411100c243c1c884101c404084845069900386113200982e9801c0c4036809490000c1640104020100c5480315001201000305a0700d0b11074580549440c0075042d100712003004010441c4090013400b0600c944248103030009022800050741c41645008a2042c01a18503861046640030a0401c0d21040540040c03440b648204801d0120b1030f5514182c3c000c1e400107403854000d44001d0013180c00204400d40050040c443c0003080400d8484885011038184443c1e60018525001221024020720040c00100c03500801c100618440364540b41401d5616050881001000c140e212412a400504503400c00700107001e00a09548039000e000d0901e404200b007131f0710202e00803410301303400300340742901032041c030084034030701c48113490220350740400c0161000d00188500031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 616693012 1250 616691762 616691771
    0x3010525030f06210c05030a03141303080409150906061b02010306170a05190c061b021215070315032603040f140c150304061e0209040605030106030503030118 70
    0x1e64002503803003d19002c0041303003030808080c160304007000800d146400041c001c2d44299008800240e00c0400603129240905016407285040e000c80c601000303c50780080d12091000c9008100382d0210f60000c00407165080068040959405042c0f040c0c400324803580010602800f42c643e5101070761583d2141d02e40c0305140014940f030b202d00140b5681c0310340244446d50741c1e0013600c6110400504000121203194649689079086506941d080480082400703110308100785d125688101c1c03001c00380d80c00c1c501d650061104010030100d02d00c40fa6146030340307216502c1c5031080ca80861204da0080c41001400039144840c21411811a101c84513980d40b410b0722000082d040c8110700c04001000030145010b10f12a00e80d44600d10180c5c01c104154005452a4150303540210a43c0b10082e80c0f04044c01400c400207400b240c0d01c03966941421002450741c2d15906101e441c2000a014007801d003076000340340020044808002035030700c480505007211303000e000003081d0786d00400042c002088c11604000b0400240c40e030216 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 616694262 1250 616693012 616693019
    0x6020a02070b040603090c080120130902030403031b09060504060e01200304031a1306090302030702040e010636020913020d02040f05060c0d050a020a02091503010525030f06 76
    0x150282d0050f1300c600002965074412008000c01d1441c020700403c1c851000b030106c140e070b06003000042d140c10310351501d02080c002303060250710815445090041600441c21512803805003000303000f90100392103a0301c40080400e20805d021f401074040034252480c60352004c1c1840d0a1a0703054841d07181e05803080e4144910408202c544103c10401c043c001030a50000e162518514980b003407510540207454000d59030f4803810044c07076140b8111031f01c0c42940c0007100842c10b1142400c00384c0c110b1080d60001b075005814183c042c0f0f1403074415040781c4111800c04541a11100b1803220b62035034100510003000a810101a0300700b0b07900e1541e005810180001841142d000241428510481c0c1c00030f000310207402d8000c142040641c10002c484001844184e0300c0506d094455403000b5100e556152004082c004080b0344150007070310800c019001c065014000d2560780c108800b9440c2c80d48804400ea40c80380d8280f8002401c040042c8407080e0102d02c0302c4940310600c1800c0c40080c0e01601c01d845841d4203507541c556000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 616695512 1250 616694262 616694279
    0x130803070c0b0a0606031515051c1a0901150518180a050601090501030c052a120304050c0607021e01052503020d021204030b06190303020f01050603070f0306020a0207 73
    0x5000702c0f43c0880004d4403e00d422805002d1710002414159500c80c0d50000700440c03c141c100700340c1d01e441c540c940240d0303c00d10303860900400c00036001c611501600d840011402e118030908040742c41c00f01100c200741140e0b42c844500320034100788070140d400a9003c0c40050000c2464214000311094020240c100d500190b02180503052401c0702d0041c80103840d4010f00140396001040c1b18040c11003841d081c0948400c5c080c0c007504910070421569134002c490030740301c810405030040450041000e0400c1e40e0440181c42011081c5800a450a60305030040b8609018285410340c2101c2d07209501600c0341e081803841016091075021004e10541c11301c202044040c50b040c41d0501c0000403007040c15114007039000c05050003840c1182100b03184056500040c1d81e00b88103a052401e48040301d921508001c41e0341d9070700c00483c7c02e0341401000340700d0302081d41c84007004060700447c40d10b00c0c42029070000c10032640c0d0340c0b0401d070341d81981e44502d03058141da101042c000b084035500200342070003060040324903081c0d444401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 616696762 1250 616695512 616695533
    0x604180215281e08040318051903060b0607020922290a090c230d0308040b0a0c080402010509060c0616110601050306070e18040305031509130803070c 66
    0x30603020510210703410000e036400c02c107040c50300030f441d00c102004203404500280a825001c2d1001c1c0c184406d810a0b034032580c45000e40d50300500005409900d000b5051802041100d015003c01c40b40541010045901803c244081d1120f042d0010262045510341c0e0302c680c09005200000c0c01b85541c680820080401d004544450585180014880d03152030350300c6089106900c06030510000354200303078017500072428034000710090f1514011490324404503601d40f40b03914144030b003649401210103260f0b44141504284450720581c02503200c140350380d5901c80c0c0c250844140c0701005004c1100b400114015521440280420001c050402441d040d00081e08503d40f44046074100a400c0c460b600c6000a9036204503141041c00e014030080900354100fa001980700c050083c00c0e40100440010b481050340c0c1c2c4c0450850307031070808540780342181c14581402451907000f00d42813040c560b8908014001401d21a413054440d000c41c171030020700d0054503540c0d140c0c1b13a03202030280010800d0301e100c00301c0400c012002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 616698012 1250 616696762 616696807
    0xc020f03191b121e09090b3c010c0c15050405130507030e03090a050609010504180204030638120f1b04050c03040f03090b040303050c060604180215 65
    0x3e440f8406180c0140103200728521242c2000030b000c8091444025034000d107401c8180da100d85404108a4100d001166402c102c43c18003515031030982003800d441811180b004083c0001180c4400e078100000030065404c0d0a40e04c5008200200c0782804104440000098250786655460300501d404d648070001801e14401c0c451111000b55190144604540c1500c201081d96840f81c01460030a050200001d420074024030504e0301503040080c40d010568843c90807038024081919100d00c0e03000d04038681c01d00a4100340003c40302135103030030f809a44031001154055085810b211005030000b1144842d00c1240707080101c0150803800080001c000d030101440345806501035040141001000d02008060701281d0305c0100d8081e80c504428840450200300850b0b034403a030455131110554420f454202c40b0001c00364440654244041000300403d41d00400a110700d01c101030407201c50f600e40c10304110072918850aa080c81d0400d0303540c504010708128100140700300c030550f9000d080c41040914042c6031459400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 616699262 1250 616698012 616698023
    0x70510030c0f09270b0607140708070b0307110106030b091b1203191710090c030b06030105011202040306050129070b04020d020d02180106030c020f03191b 68
    0x2011001e0300ca030710400c0482d01c08000d20742910110318200004003629407058100c03030400741d0b01407640313507442030394012605242014044a80e1a02c0c00d0074808c984c1360100382511803078092410001040400040c41800380c4410100345865030721040300580fa120002440e604030365480c2e2074004003050411039441c1c4104090310180c1862121050f0007d00740b185608081c1c4900205c101c0311090003070010640342c01e44507118290300b119034581ca080c0c40c0c0408101383c0700d0b210400d081c1006603519401c0c82d0882111200501488040c4030004203a00b13039120b420342242c004400784010001e640c8510054281202c00d2440103107003030380700d8a03245c05440090700000c509030300108840302c2c000355920b58509400241c81803942045103541c1c403203000c1c0c01c01030310103441a6210079265040d540c43c842c0494030954000c01c24580941542d415050fa0103003403140030046490315045400203400803c5100d0917649140c0698649062100c0c0580840404803031f07402004074956007490189540c80d50f21901c10b0056 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 616700512 1250 616699262 616699271
    0xc0e190e2508010c0201110a03020906040305010608010c1103160b100f150905060f030402091b071109010504060f050d11031b0901050406030b0414011b0306050306010b160b060307051003 82
    0x1d982540d818002c84c104682c54558040b10a043c2d203410f0381c0303152081c0d2030301590710303102500003a1850096030005003095107010800100c400c815882041e0a840e1600c031200c81e14401034010f40c682c01010b5210360b0a540c91840070000902e000189035101c1e028410320a1050385030603406108442617040051400003a400a1020381d411200c9113005010803140a49064070901d40b1481e14000030300b0007030154280c5030100d00c1d10551441d141d150003400d64000380e203500150600140b80310002c00010f00842901001061508140c0261020365000d404018249441d082c1440440c0e5030041081e40c43c10441e00400100c0d507004d21050a4901c80108101603030040b0b5400c10101d050107078040c41c81680f4100d001c00015041400c501c0c0d00c42e130008007040300c446204103450f01400c100c035011138940b80300c00b03101c0484e19099800407040c1e900580485003260b03250f8107000e0841c4218000380c049444484c002350006a8400e445a41c4404041c1c191034102d80c2d41d00108154400403071440002c25203d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 616701762 1250 616700512 616700519
    0x414011d0c09010e0c12150d05100b0619051b19030f0503060d03110f0102040b1305030c1c11100c110f0f0609010c0c030c030c0e190e25 60
    0x80324401d409030012035444d14450411149031420307481101d00c0d10300c894101100091003400405201d00181c040541381c0070f540c07026440d14503100c024594018407601d01d0703d030084030709080c010162004014001160340c01048c11311015201e54001741d4100c00744282c2280c6054154005100d8004807241001062228980c41c0c60050440c007801d0040300304008091040020555403c2074250b8440e4141c10a8624098400340e000d083c100c05685000c419800080c00040440700e410050507084254110b210b41ca82e2075004040e00c680390f1603d15035110650031001b50800f8595040c442925101d030346811601400000442d21507103030b4134203040104a16216540034003010f039070b0f00c0c14445000c64111000c0751007280003400e84910188071074043c280c080ba071541c040c0d009071541e01840e904581212415035030b070f152240a0007014042214080060f902c005500c040d10812180a0140c168410309a0349160039140300410a090414070940301e05640c10b81d140c2505400741c0040c903840424030a03000d04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 616703012 1250 616701762 616701769
    0x150204030c051c030f05070f140606030f011e0510031208160c020108011701060506040f03061404031e120e0a0c3201020c060a0804050601060509090414011d0c 70
    0x2003c14200c18806a030161480081d41c0310013580030615080c1041a16007410742850004980c0a0400411055201c10015002c1c1400a102c0d807280030124120390300303120824104c2d4261030345030801e0300d00c8503140d0309881461031040e00060b906c02c3c1400b8031990000d5480d101d03034903007001205400011a8406040c0040000c001d90109000a028140301510f90034960008100d818144034218280030121129205803c0a4100034014980280003a84603130303c543c284241031910340f008866080c030b01307048641c802c00d540005071311480e05519900f40e0692000b19080006541c240c14500b084007500c039040c5405514400e071148200c0709002440c0c40109407030642c0141109400618888810321640d20080d50308100c41c90400c1c101041841c1e101c04207900503807a11203110f0445500030404240081d40c0c40c0d010301a02c0c0b00fa030017801103a242341d0ba1030000303940d5440307041d1040f43c004645100041c04078604001807120000040000140300c00d4480c0d8000d6200c010044920301c0c1c0e0440c0d00c001c03d4070301d13 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 616704262 1250 616703012 616703029
    0x3150703020d060914040204051015020303060a08010c0219020a030204060311120f0d032a02061b04120201030c021f090326011a0705030406030e0d030e0d030207150204030c05 77
    0xa403c1c00802c0001882910b1410105e8001c0c0024400e0b52604005402c2e41d040c451400000c100400c055204000e40e440043d407aa00100c4a203800784c48407120000d0140e0050041603200707080b41d00a02440810805042850030a160b000e9030041c00440380080143c43e1171040350011802104404074190452040024441c402c50913444c1d10360108503054000140401d042c074600c2514140050701318112400840c05990030701032801c41c5182c2c144518800c6030041010352144180910400c25400c0c242d1828029000b0741c029035201000c0c1c0e240c1c01d0019402a0320100018200340100c0315542e01091902003417640504490042e00c0d11000603004141d0403001d031070480c16070806290010030080c00c00c089070050520503032480518042c080c0600c0f80d02c034800c440e4640e80082c2980d90b40d60301c2ea900074001e0440d00f11201514803403840c1480d1210311034807541062103404e0028204524401200301d02940080009440b039080c0d0100c81c09001c025032000300010351260150000700c0340707400e04122444 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 616705512 1250 616704262 616704269
    0x15090219030501050a060c050705152a0303010308210702030405010212030606070809120a0c0f080309030604080f16120207061404061409040e0a0b01080a170903150703020d06 77
    0x15040100610081d9200c004e90002d403949460307e200c0c00c07a0b55041c003528010329a44500c1c2c000902840300d02d031840091008020244150005810a8001084546003c18502c842101540062005100050200004020040641c6201c03c1c00120805840c182c100d4207843c6040540d00c00202004907503011f002c3e81d00c0c01c0754000c98a9043d03103408808900c951085010090003417400050404280d0380e00d07c3c1c0c01d80002c80407422540d0314042880c180d03e004a04e8000c10308000c2d440500024400c80c00021540c01402c09070281416494694501c0255046000e080c49140c80520240b4002440c1c0c499540e11280502030241280300c030f250001e81802070f039402030b00812140c01d00d04200c0201e941c08481c100e82d194030348030301a814440c03080c2856004011205503ca0305000d1002c0d01c8050010b502d480d600e00894100000b0f90b81c2d0041e083d600c64000400518241d084046400050f0312400a0600008013405480c410646004515203074181101d03800f001c240d000c542c1145004041c8610341c00b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 616706762 1250 616705512 616705517
    0x60315090f091c050405040c03020f0328051302010c033506090702280209090d0306050306160c15090b0a051006050f090a0915030b0f0121050115090219 67
    0x4605115038000d044c0d00c00c50040c1400350340c07144507070402d5134800d5044510108030031540310b441b400d16904114a050518410401d110704034500480c00c60545d00c00e0b6405a072006101e08008103403580155450f215011080c1c0501803031103030300c0d44000443c10140c07825044040c010041c181c804c074050034580c40e002e810180210001010015402e4002401d4980c608804d4000c4403c000c0d10001c6400010900038025000044913090101c01c4500261060444440380c03014800540c6031300c02c2c10768501c02101c42040c1009a90034107401c60307010341e640c0442d00c2e0207902c542c0d8000c1c084c05403802c10341780b02120450ba214885410000c10074180c6c4a00da8105a02c0309550040c18038064008115020360904400d80c0e60000550310110364801c00c1d61801485020410f000700344494004c0485403003603110030781d441030000c40040d0b203070b8241000c4141078032084510491103560055056400b404100403c482941d0b071100e03d102c0504540884000419100e10056a0342c5017654195030115a0354458105 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 616708012 1250 616706762 616706803
    0xc0209090a030801030308041b060509010201140708150f03011b0807090f030b180d050301060f03050108030d0b06130806070f0c201309052407050702060315090f09 72
    0x3a81c40f203403143c1120b402d450815080d0710b85040805220458500c80c80c4036150b40080010441d0300003000e0079144400741c000b000008170040c620300f542c1c0011508900028104030010381704c1c00c184060070341c841074043c000300382e00440100840d003100e19500c03210f42869000301e0a4110315512080441d408900340c5444a259483c101d0b03070011028ac1c030f010050405503002d0015602402c1c011860401310085002c554141543c604013410551003030180314000380c00d00000e405400e010f03002d120f04072003084008510340b008030700c8110020114075034265806001040b0483c0c450484c0581100a480306030064022400d210358044c20001d01d4032112014403035110302c4c24010ae42d21640042c107100c40240440324058802d4001041c000c3e295103030049291074042d020052200004030014903058150801d201800c0f5021711010744042240c1c00030001740708100002c01410051b0182d81c20000030420112138500c01400901040001ca030035034200e1904e03a04120340c50604014281400501803402407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 616709262 1250 616708012 616708033
    0x5120408180117152206090b0a05010504090e01061a0a0207061d0904080f042d050306011a04050a12030f050c070501050906040801061205010608010c09260d0c020909 73
    0x341e200004044c0d102e030301402405041c040d00d41340c00640070300348400320b002441c407810110880100f440d8080c002c6883d00c0c10031503c116091000103041664016100c55040a142040880c043d06c100c1032010140d540b5a08001181c035a0074070b40000e080c191a007040e40b5211a000d000740303040c035190b110300d040040360352104002c0072004a803422006002c0e0381840180e6203600303226140340714a0007041284c60000078001a00d00138945001e180075010f480300403a401e0035260910b891402c6004c1d0b6581504070400400911451818124851100850a5084c40c0c0e548000036140d25250340080000081c1140040415500c440301d09000c4045042040c14005207080321a5110300a0080354140b02002990210540e0350809690040203410300a01035180c0f0b410789086400e88a00c1c0442c0c142d070814001040d42c041c1802411581592603a5103005c052603d2812000c840030680c454000844c10700703030580545824171003941c941d0301503210101c4400301c0d031041c08035400b00108001700b07a800005020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 616710512 1250 616709262 616709297
    0xa081621020c1501030c15031a1e1009090510030506010e0a0e150a0c17010513291903050312060d050708160b040b0f0318160905070203120a0c051204081801 69
    0x20500f10603141c99140000c0c2c00c1042c1a88482b8400581d03000f1440300c000c00c4c2480d03001d5040130a035a00314205104646440c000201c031103180c0d001c010b085400c50401840340a5802c00d51300d0b401206250041501c1414916080c28000c80f900c40365040080e8808024200c0c1140c01600200c80e8207280c0308408480781202004540300602032203105100390070412000441c0c40d003007160044d840c009644031031459200780c08000300b078408066000f146a05004e0b1994036000003013504498000740074614102c500d411140c03189100400581d80000e50709000c1011800070000e0724043d04000d8020541d0f10107036142164040070a602001084504000c18044012500305950103052114403e0351a41c5030382060a403400320465042c80c1c14031850516940d000c600c00c20742d000f1561261070030845512841c030100d80b80e10445005011056800c1c0200f40048140c7e4000140d8603803d00c0c2c21800c10411072132043c4001c406440549103440049144204907902c01d00d04010320100342058203c091140314031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 616711762 1250 616710512 616710551
    0x7030f02060403210f18060e0a030c02040c05190e0306010b04050d110f030f03030406051e16020313080c0f010206011511010207080a081621020c1501030c1503 70
    0x40c0c40002ca0089051100043c0503080706045a2400174280690f1400e08003800c1d40780001030080c6c41e12410078042450b050008240f100c10150035a0301c008203001c5070740a00c0050400c4a0800b000c0200030402e40001d098840d00d19022414950b40d48495440b07078004061400c230701030f00030760480d25040004000554800304440c07501a8001204072840d118100026a1120030711a0182c00d400b514403800f0082c40080000c600c66442980100041e440c1d00943e19010740103503c52100c101d290740b010855113000c403564180400c010740b040340d1424403040c1280b56040c40b02d50140925134400c6010030010300e40308012540c5035000303200800743c41d850704030051829040741d003040707051003281c0c00c0001899a00b9011603e030070b40c2280007281d8407843d4034030050a80c0c608454080820f15007418841001d03203d981d00e240385144041c83d501b02081c40f007250030000d40c419240d200d518420030910f500098084015140218080c00c140c84071146403043c60100500948815810540b5004a04005050300940c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 616713012 1250 616711762 616711787
    0xf06040501201908130e060a12060b030f0f0609010203070905010c030201060b070f060e07030b07050c0c09151806011e020109050a11030706021504060e0a080f07030f02060403 77
    0x70401d610550515036080c60051200c60050210190b24001402004c40c01003d6485444071814807550341e540c05691004820b903102a40700703210413003c20190448074084000d580c0107400008503030404000103071400031882e00103000d54002c02c40c084141417013172042c150301c80305c820000c0d0310b1460312441c000d05d00b00d10343c0201414003000c0220a0141803007580b20802030404140902d03540c13045410b007a01c99504240044031240e05010001e000840d000c9030190403070f88c2c000e07200010380c2c030f81442c1030b0f40d140c2204440f00708074410142d100100b5603500d220307140a80700025000109004540901500d5005d407640b481191507400248280381e603003c84c1c101511002c00c10358041092404c030040f4098110900090040d20a0054403400c0c031100d46034024200b01c01300d044031089903941e0f4090b0380fa180840000e000e401ea4030702c0000c000c5012904040805507240b8162000d10400713a03206881d41c0c0041d1000302100c84081a000100350708a0316100091045000402c2d903442c0c90383c4d000304994544c50703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 616714262 1250 616713012 616713047
    0xb09090106030e030f070b100918030f0e030604080c01150e0c070f050609060117010902060f160212060702060f09061920090f0402120f040305270f06040501 69
    0x2031180f1550360090042e5801c05541c4c0c0f04ca00d40e55a140c0c14800150b40c4252140c042c104607420000174183c00500c0303040e04040016035040350020594070151902d10351040280300b4003441001408865409025040c440c40c85440079a4465880300e03a103d003103c0343c4448103090076401ca503081c00300c101c010f0070710366001c0c000503002503a40032680313041e9034907006910009046118080900a40b50b070082840c0d41030300d16201c00304550019400c006e9080e2044820080e410000c00c00c018101d03090105c00070543c0d04000b05032a0705091a59000c03601030710801a022070190003045c00c1c0a00d40b03605224441d0400b808008502490600c802c802d5140c001c06019040d5581c9031a52081c411044c1d0781082c04030f1071b0406070040d00c81e030f4800060000caa0105102c01e03c2204107580c090f601d45000d10a0301c69a110125074601c841d95010a07200020f04084c3c801c0d070030301409001a400c8250070b001c0030303841e21740001c105041500d1198148002450706081940c40380c002408280040c4e40d04c1203c0740850081503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 616715512 1250 616714262 616714271
    0x105041e050c13091b021b0d02040b090f04060e1f020c01290306010e2e12060624050f130e01030609121107090b0414090f070b0909010603 61
    0x140102d003a00d10810490410710303010201e00140700f140301c0d80640390b03800980420102a0542c0e90302241ca40842d0b8003851010305030101040750504002c401076081d07078406800051211201000562403941c1100c03c00b614201240802081200a0068500c0e1000e03a1000f021828409000d00f0781d1140c0c00000b14201d25804103103a40d444409411030035800c9240344100b181013030401d0240318882204a0114040d10401000241c10010740030420f10540c2c004644080010350a00300b801600c030701c1c1d950428014801000820141280654480a0347c0314641c00504145070442c0340450040c105c940c00e40240c0b010220340c0c88680c00400300d51142c1c40c000f030304907510a40581c3d803800318050754000380040c3c0c1c807200000c8204511984070f954114080c50002120040682c0100e40070800105007040c250032500d010400b02003070340c100c901c4469000f000840c80c021044d0001031a080f04840e52180b581c001014402030307420902075240a4005810428500312815010a001e50410b00c151030400d035a9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 616716762 1250 616715512 616715521
    0x81311031b0a0b09060913090c1410050c0d0806031e010204090e010b09010611010e072c150904080d09051c020a020a0509060a0e1603062427030b0f0105041e05 70
    0x141c0e20408d0700d20b6102008100c1107441c5e03201c4030000790780300c03030715072300485120b806000d485010308150790b0281c100c1070041c072290841007002c403446640584066018896940f5031021551000040340d4000401000181c03501c0c500000e400640781d038660702d8a05640b40144242080d142c12081d54107554450074104110448400b00340d00600720702444040502451202084600d20080640074601041c1e40c4003948070a40a1440d018400540740340d88441040109000c00c0d05007814200c0e8001d0185110030305003c55040350905486490008031a507030007002041c04898071152441401203160310040030804c60f80d07804544000400c5c01403910130014000040d207940c4d0783c10420750103031500414510b11420044984041d51720644420303808241003113000b050f4007100900003840822641c100024451420740183c52546894280c028020040c40c162450356440f1003504005510400c4110319516002001ca40744200603042140b01d1400c102000c504824a18421440008140e40004c0e05850303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 616718012 1250 616716762 616716799
    0xb030708100b1c06050616030831050706090501050403060b04060306060b34060f0e03040b0408100902011e0e0d080c100c081311031b0a0b090609 64
    0x505a002c540040c2000804080c0091110030034520342504210910002d41c8900400240e8085d07403208180310210050780a0102c0d06c9a81d000d0741111022424103240303082480c0c19004510100d010000b46d80350b80101c8010407400300b12960040070700e4501402440c0c18480001d165201c0ca02c0702420454540d034403641c4550b0b03281d02c40001564070001c200803942c2c0e5201c424040b90000000004540703808020b810041c1c40140720622100560703070382c4102c2040c8503034503140105684042c1341d210366910300f12614a2102000200040c03e4520040c50322107283c0060711749001c00310700d2100b4860b41040030500c0141d81152003002a0b080280101c13a800c080c200c0c044405600c210b030825846588064840b00344082c00c2c0051072184000f03000d550190300d01714404001e89409100580001d82e06c1400181051034a8044140c014030448081002d00040c000291801c002c01080782c07103650340c8900c060070602e44040110010094001c031340d41010780c1c690029000d805034083c2a80036000040d4004403900 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 616719262 1250 616718012 616718041
    0x120b0a050f07230d0603020a0e07050f0c030d05040b0a290d142a01050a09030b06010c050f060f060901060903060209010e060a020a0507051c060903020a05071418010b030708 76
    0x21007200c066464200130600e450140c000c030711050323000c1e0b00c0c8858040703110031040d04858420034032500c07041d00d8400c4070b1620240742d9105051101860000b4070200444a1a600442c0c1c0624010651f261441c1042508072045070308000401d140701d00d212a00d10707a00620580046d03540303807003222910300a400d81d0038191494180180080c080e4040d10603016040034891a49100c0c4500305c1e80703200d01c50320014005440501c41c0620000100391500d5041002030580401507034000410b14108180c031102d0360f216840c0000307605405a5a81140c0100000d000c1c805400c142c2c4008201e9440c0300f5940b40810140044c000c0340000b61032280c0002c0d01e441d180e4010b490104400e43c000e07107080d507186500c1000030b480c0c0100c0102241c4601514100090918200114040c4811601440e10022040f5a034050040c1601c4800301c080d03010386400302e400b062090021000500920100410074a408000c000d20140881901e11841640b900140090121003081d0b0342d010751300b420260050703141c4032200800e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 616720512 1250 616719262 616719317
    0x5060a0c0f0c08100b1f1209080711061c230f07181404090213020f070507051e1e060309010606200a0201050307030603020307120b0a050f07 62
    0x7001514001810000c50081e40c030708403041c000a84111401120481e801d031810081041d500c0201100e00121035250050344d88503000c018100101042c0001c0144029910145030946a00b90f0120b40d41e03082c01001d040000090358112245450645c141c40901e0345054038032a0983e5a5940f8955011000001200080a40d050f014603582c54034000350a18000c403801ca5542c13001448040071046001d400c0c10410302601c10301e00603400403400001c1404010700401005a81c40242d0040846c004d28943c07000703003910490540f07074a81d610043d0500e589014013561210307014241c9200c13120340f01c1807400541c03840c11604030b95045940300d505400c07101c007003020680950300450001c24047c2d0b0410550246044801588904242c2000c4d204100501100405034003d40d030400007142c80190b20a10065501641c0c0d828002856501c0b9000f003480c0800d1904049841902165036205000d000c100050740721005072070900c12071401e5134010000713240c0601110180804000c62021060a020340d44140c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 616721762 1250 616720512 616720523
    0x60c080d09080304110405040803133f0905090103060506040905060708090d0e060a031806060902090405060d050a110609060d06061b03090b0d090605040b040b0a090c05060a0c 77
    0x458500b0014142c2d8015202240c28514210802000d03082502030148203680244005041d90703244d00714030030f10511044d27040350000d40741c6100c0300c1050030140c104424a03000d91040c40031036100901c000302c810345c0607481c80c01744848004101b100313690355076240307041d60340c0100003141903124800840c0c06003040d00340080090003002c0800c418594800b040c0b078401c1d80c20400b04c0b0030388182d40c2c200340d454080100325030390040c108205500aa500a81002100c0343d4140c070a01c40c94005038681c24112403a50b00300002d40340d0001b0327860074140350500905400003000c80d0203005c84240c540e0788076580d0899180040c508405001c94041994845051301ca00b400081d0a42d96145075140038880106600d0083c034010030600101000f41c1c0300d8014400e02510780c1900c85075941803d00301c121140b031b00322006501f441c503161518140003c02d40d009440c000c91140302c0085060a0514002e8803104004221000143c9400030540c0800c24a032401421540306880060b070301d81c4048812074000000403005000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 616723012 1250 616721762 616721771
    0x16020607060e0c01050a1d01091805190b0321040b07150e0a02030d030905120a1106180a060504020f040903020a1b1a16170703090509010f060c080d 65
    0x5110050300b0025003142070105031115007120300015941805925070180c0050000019240305041c0961510380c8944141405021940c1c4d40c200440504403000102ca0030f152107405104413013485552603034038410070303000c01d00419080c0c1d4082540e41e000e1700e220303000704400c00c20708005800f007400450b4060301d0700c0358405a07102140e00b050b03010740c4202d81c28684020726145040b46070040210f44150000e5004000c0c1410700ca28000460240c50003580c01d4909005000100824501c070b034000b002042c0042d01ea00d04902ca07075800160900704010040038982e0322004000f00f8505d4042006c2070920707848100000c031a1141d0010843c00c00041e902641c0280ca4100364205040d00000d951180c1842514020500240f504061040881074413409115142c44d03000c42a0150a4034090010f5024080841030350209071346501070b020301c6c2c00281e11166480040d2040c140b580c040d01020151000f580c035100386500d0078508194450440c070035a42044240c400340402c01c0680c200319015281c1d121801e00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 616724262 1250 616723012 616723027
    0x30e040c020313050303030408090d0809061204050c0102161701090206040b0705070b0f1911011406010908030301030b221212060e13030e06121e220206160206 70
    0xd68036403041c160294082c011403c00200c07882e0001c00c82c0d214660284010742003030110b0040c4403544543c02ca0880c0c0300c2609001e00700d029140c50014001195400ca81c1c0c984031f0400e414541e0400c1c0070011850704540241204c0782d0b6070307030702c00741c80301c0c22078120440718031020780d14405260041001c40c100a6000f000014005000c0311560040c0076460701480c140c03001117944441c50a03083c481c000c5038040121041c42141d007201781d0f041c5502d4400680c1d003000360340044c50b031000500311103e00c4003150b1054009400c2c45819603002c01c1200107801c00600031861541143c40d4240303c888020090020b85010040401d21b964919421010050313024041c00105590f010002d080d00c0d07242108001c03805c3c600640090f0740000c1d411814010880c400300750301082044c0d1401c5558600358502c080e0041c200304070030320a040c08c40d606170744500e16010180c16100913140301c03c006414040e041a041c1841140c07803060f480c0d0300c20352408105504454855031381e2074a521b040c074011102c46010b07601a4003ca41c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 616725512 1250 616724262 616724267
    0xc02091b0706050a1104141e1804051011160507240201050a02041815082d0c1c170a0507061b0203180a0f0b1213030813030e040c 57
    0xf10301032690b00760140f09a10301000c071900540103500c546032007048500707039403401d6007807903052100ca50410b584013031035a90381140410018021841002881e0510030100b200340003050200b01011500024103001900034602d20312210b00079003c0901208a00c0c45080c01085000c1140c00c000b08664090030858504107803800d440c0031450850f42002d0f500b020300040d00c0c40414170845040d500d4001d01074400d2000c41011a004000d840048145207a071b00501140c04002000b6009440320f00ea06407030500d2141010400c8183c503049204c00d02d44e0b10800c101185551182c1d40c584800c61420000d01000c2d60380d040c280500e070b018900180c00d01200140d5010712642c030000800c05203010790000c0c000c0410004000480c9141202004010b80003480300d42c18521000c3c154040f186001801080c51948808140c00c0b0300c0d06950096802d2a0000342c01c0d030011030b1000c4e5040d80000b41c2d60300b181e122001c030789001e007442c130340207140344030501d02a80288105801030350807090144000d07108100c2905d007407402 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 616726618 1106 616725512 616725521
    0x904140405010c02390a0f06170c0714031201090606020c030a0314160206030c0a120204061d01020141270f19060501050409030c02091b0706 62
    0x24032006d42e82c2c01000b01c0984003812204d9086454010050302c1031061614440c04258803204015008140794166501c1c680c120a9010502c0d03c0e9156150540c4035148000c00c01c001048004a840f4265031b010200ba1740a0703800700c0300c001c4034440c109561034211820080005281c0b1741b2184010b0400006001e041c0d2030514801030188095000603d40e8000301c815030320098003c41c51840140e80200f11240c001d40c0118110f29044c01c0101c0240309142d2200d078000d0151112080e00c055910075481031101e0700200889040c150900c810719601c5651070615000d4240e98040582044540800c0d058000d0004d16001c0351140207800c803502c0301c423035291490440c0e4050400c0315211854180f00384000f0052072030b44944030610901c1c0030b000f00c4134181c00181c00356141c8115240080c2e003004880c0302107901203420320595500c0c1400c60303003500804000e030300200001007000420400103801 = true := by decide +kernel

theorem cover : BRFrame.Cov 616546762 616726618 := by
  have h0 := BRFrame.cov_init 616546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 616546762 ≤ n) (h2 : n < 616726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
