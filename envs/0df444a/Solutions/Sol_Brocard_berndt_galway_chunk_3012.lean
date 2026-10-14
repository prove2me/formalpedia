-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3012
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:24:11.136649+00:00
-- url     : https://prove2.me/submissions/cc184a97-d59a-417e-88a4-3e2c14bab210

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 541546762 ≤ n < 541726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 541548012 1250 541546762 541546787
    0x13020a05190207060c0b09031308070608150603010b09211f20071509030f1b120c060b1c0b091207080d0f050a0f0b0904020f01050a170403 61
    0x825055070a16018100c1e2a001203100e13240100d2032002114000940ca0f0092070b511004220450b030400d058810200d5210400d41d001030b030542c210127024412158000c48031980518080c000b0750f1942c00002c0030884a1105104202c0344450200703110310a1703650f554100113010509043d40c06030440c0000d034540c541c450400b4103802941d96400c03c03c190750460040150380c2441049090b0b11141c00505250309602c00c1c403080315080e0350740171840c15042e41381c4070385600103000ba6a580174103403000d0000380c003180d4007821a80c2c130800000d82501c0000c1001d500c0403200003003460f00d101805858903001010b458802d18040d4804400049246260f41e484441c058050241d01c151000303884e070803440c07078444040031660790034020100100c0c1d0101e1403680c01414016180b03107000075031b42c20ba17242107400c41e03200781c50a08115865074107455009515000341c000c90041201c40c0240380c14154001041c125080850314180440403c07000a00760203202e10050317400070b000340620185820301c1c1c007c00c203490244 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 541549262 1250 541548012 541548037
    0x8010e010e0f03030f0612030a030609050c0c0705010f050c03030408180d05060714120a05041b2706051c0c0906080607031a03010f020927040b0613020a05 68
    0x12242111a0800656001900b0034200030754a1a180e03400b40c03000d800c100504035508040003450099500c00d082009080081d85960001035240c103105044060795405802d1100702902444039010818012030b44104031002420041c8071100303480006d8402e8004c0a40d03400c07082c000401008103000040b0000c0802510481156003040a43c000b044003607070760201e0103402d990224000505542c00b0b080f000009031945030809007070402c0d40c03410025000c0c1c11200c2134041034032802480100851500c10328101002c2c8028010b8050801c880c1908910354074a040802e100d0b0340d40e020300d400c8020350012015201c064001e1000728030750440c80704605101403003101c140f0020f40700080c491525204403415503d07100c010340b40c00c0d16090b50480141801110902d00d0b102070300c0560030103940034401e080c040b00700f1010140e02d0b42e400c5400c1107841d41480865100301032b11152002c0008440d201c4559000307501078030401040e00ca07100403075610340b504400300341c0d820700c0000c003c11503c2d0044050580001d154 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 541550512 1250 541549262 541549271
    0x31c1e0c0c1a040e070c1e02090a110d02130f15110307080412110a1508010f0608070c080904020a0903061a060f0702030a020604030303060f14030a0f1a0108010e01 72
    0x40304509440c011150303003502c60031000d0106000d40c2c6036011072190043d040d4501118510025210170a14071101d0070300c2043e4a407031094000450601210b0355a01c2076084104015000406484000a00c0b81079035080c0c103e0350000b5030b0315140c40344082c070b00040c0c8091286220903644402121a0000d000b1016a01064460b01103104a80002003240e02503a40803861a09151a1003d04d0102d003013001400c485100f00d1019480d103c1d100c0501000050501304404100d0031240c000103001802c060b0040081450304540070f210f07083d00440b4403030308040103240561250005041ca451207000b0103400c59070242c0001030a52030b09900040741b0050320300900003041504081e800030242e01a11080485e001902400702c1701d00c101c1050041c1c40c02900240540f00004c03181d078000b403d2940a6042100400d6485074180400d10071300e10b000001e40f50700c04890341600300200009958441818004010516641c400c0b030420540892008030034800010503a0345503101c801c103074043c0034005000300e481e61a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 541551762 1250 541550512 541550519
    0x10602062802030408071b1809050d05090102150a02090a12050601060806030a0501020f031006090321030b0d050d11030a05090613051008040506100302031c1e0c0c 72
    0x10010081050a4580c55280345550700c0c0307545010303410041c025101e6030818402000850781d040419480381e1018100030345040c0c106490500c40540e450205a80c1501c1c000d440c00008500281c142d11201c402d0801680300c120a0380101d24203104214200d000350810800c1c044000320303a030040d00c009c540c1280c2c0d060030309456588d01c920320b010040002c0c005520640040045600809602d40c10003c0a400e4941d0100320f0348400d400d9130300c8041000360700b680000400419001d0040348801400240c43c5c0901d07070500d03540b13465148100d0341e1071101965a08a100a4140d4000e9100e10f8000320068046c2035140780905016850340340526642001c41c106900d85902c0c41d030702000322485503040d03031074280c10300141a05020403901321900340c5040c0c104c1c1c40004591607568403d6100743e10006e5440c40058505443c0550074100050444911a1480d40d42400180e40204810000c102c51100211410050ba40c0031598540d602c5012512000d414070b4956100d948000f259142500600e20400740030303603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 541553012 1250 541551762 541551781
    0xd02060a171b0a080402060c03070f02041d060c0f0403061b11070b0d090203070801061230030506031e010c02010e0601050607030c030c020a0e041509080412050a0f0b01060206 77
    0x40c00d42c000c00b6801d8104000380d803da000e0040715422600260150b8201000341d00b0700da1840d84558005e450100240d01c41404601e09801a1010040242c0c02004600c164001250351000098200d00c142100410100031034a820f80564004641142050104505000d6811004a02241102d001a00e041d980c0440e42e140020702c40c0454805040952406000f0070f101340c01000310071000c9a041c080c00c840001c60203804d01450018101084001041c10070758030300203d840c00e0340c00c05850f40b80030711103001043da0030110400d11882d03a1814041841e83d541e000090a110050360402d061586c0241450f4540c0c205620070200c000540e0020411241007000c0295551401d1240c254010170400010001a10800b4001c403014804c0c2050b912400c0a640018800e100755000143c0b18840d0340c04000520822160f20700301c403401304c00d0030016812107446406403441540181c4070074401e403000020800000304090200380d9001041070807000c1c06842c1c8400242828840c140041c811000420190341 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 541554262 1250 541553012 541553041
    0x20010810030507120303020d1b17090c040e0109020d050c01020f0a0210050705120d0c03050a1503082b0603061d060103060b040e010e100501060e030c0f0d02060a17 72
    0xc2d00301c402001034030710b4000900404204480c0c03c801301078003400f42c10050301060041140161065072408005920b000b4000c04c50f00d0a02145480282d40006000d4500d201242c010030407001611701180244408000f140541380c1414006d40140b40c1002807018000d0209040e500400268203440080740c210392400c0e036949200130b02a50115481800da06801e00440081143da031281c000d40c0d0180d500703810065141c0d0090b0160001540c2c40b02940424a0750621a4a42c800d003da0010481d080c508004010f036140c02e404014020740300040c07001805080750020200d114250400074106801d040d2512003d000780d84012583d1904185444101c8444620b2041c040100400103181aa00c0e545a541c00381500310207550308281e5401102005410078040d40800281040c010010350030199038000480304142d000004001c500312072002540d60205000d8001c5500b12a60405401c550001403210402d20200a50003440052148466a0031a020750100d00c000081c4003290b5646464400303a55 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 541555512 1250 541554262 541554269
    0xc0607030e2b0c121101050a0203012304020d0c18051f05091903050114100602070b0c071706090c0621071e0513080106080307030c0f20010810 63
    0x5404001061400c2d10300c552101050580340d2800100c2410746444e05001d084c54183c1c248002541c001c0f442d1102d074024000c09400c049055000c51440d0315140307511600c191031280040e4000030011000308196a203805542d01a603400c2c030200b04424400c078018004500d1511481034040d075005000a4900e070446429640c0600c962566190000080003207031568020844142c0c801d0510492001692000780130b000030b140700d08000188000e0040e22100746600040c6020003a101c40f040c00c0c090140e01241d0700040710380c1120507680b607881182d1150300b45035940c3c0004c802c0c61140401010b04490008080c0e02030300202c0e00340c0380010802d10501011384115440d0a00c0b5200c0111410007c1440781542c81c0d00200c1e80c5045200126210013400c0764941d0605c00200080002c108148110001e5000d40010040d0b070b4001c000b11890511102e40f00c0c010390802031b046c0030b00700002006020340c2e0b405002a055014240d8103041c0900e0007040c42c20b500e0403035400d00281c0640000340400c0298101c000a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 541556762 1250 541555512 541555543
    0x62306122a270c030c0c060a0c0e0f0604060f030212130b150105030c0c030d05100602010c0c0c0306051b0403030201022a070e090a0213230114091005060c0607030e 72
    0x840c0e6a0a030309054960015001215090013003090101030720003030087c640034603481d00001c9800d0304010030040c07000340407043c00f5100e441031001003050303a80c0700000c440171102541483c07441088455002d800138028510341c580187e0000040128840c00c41c3c49141c051f900c0713143c2188050300c40f40e09108004100360742140c0403900c10130105100c0310340200900401501c500403a840d2a8000c0f16100c03c2c2c0d0020345003040c01019070b6100348003094081c010034500c07010525090300510300c05e8445000c2c2d400a0311015103899a603401043c401100719405d00b040030000d9000c0c40d41c0e16528a0024000d5200e40490002c503c00030121b11040000d203040c006000004400400060381070801e83e000404002d04032285a02c10021114016282e00145540c5011804000225421a680122041d8054000310750101d00c600c0f0041c010102d004c03070000742402c02500d580c0e01da40d035090008410110b80e0f4100c0d9501602c04140001d000390000b1b10319120740c500d40d5042c0a403542c6005d201d9a1072494650080d203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 541558012 1250 541556762 541556839
    0xd060b0c0604020607020a0815160f02190f0b070801060e0f01270909140f0109031209050c0604032006092214010f03062306122a 57
    0x1614004000c5c10704140010085d078002c95a85174041d151101000503002da0002d804d0421a0361901d0100110b000800c81c1000484215040b00003500c81d032082d040f8800c1458031130b2207242803000003d403507503410b54801c8401c849400d25260181402c0c03c244900e5000404034026a00d4038240301143c242207600c1038581d0340e951001c2c5000180c0078001d21059030442d02e440700c40040c41c0080c40c090b40c8030032409a008038111100c031050b1203061040c2842601364607810040d2000020b68040c55110700c202c001c070030004941c055031501c035052102c150009580503001150200511000800b104810983c0d060b1500820b6600014081070340a0680110b5118413a001003442e00c0d24100520510302ca4407580c005042201c05c994000001700030b0700405681101c40105008000c030b079100d1246500f0440a1030080c00800d50030680c079994006010300c1c060500c040010400718010051500b00034070a6117020007141d55601c01c5200105e0900c14280302d01001881c84080d034406030700081104044407880301 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 541559262 1250 541558012 541558021
    0x1209011b050309010b210601090504030504170c1e01030c02060601230f070507030b0c1207140c1c270b031003080c010b0f040506010c02151e0d060b0c06 67
    0x5078180c0005014610b0355407100b145c0380036695004103068081544a40d0901d0182c200c04440f880e00304140c1000d0340280c54041484007090b0400c0640c0c0813904006110f40180c44541e1106082007ca400ca03103400801c0703907030001000040e0000c05910844c0c01e81e8200556180c1c0003041f641c80905842d014007051110f010038080d41d000e107030110740012800740d1803413034100e0381b850980460340b0812082d40c154111503000e0080003100c5e039003203401000d1b02d405103040c01a2038803e501004005070001c01071252030316040c1400c4a0060954490b55059019140b2020100040060078034030200798600244415840d4010782101e4020030b0800d1f0601260501c2c16030078641c410b4180c0d07001506010072008220400000565420001c01c1d1544c45940046040e809006c00c5c001c0b50b550b1140381c503204608110030080940da20451020780740740c040365080c42d5044000a0070007603104101c00d2011305281e6441844040c4021402482942d2020004101c51569110a000c0d207001e0140644c500d608140040b5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 541560512 1250 541559262 541559267
    0x30c060f1e0d0e0d120e0a1713081204050d1104051311030d050301030b070522090b0d1a25091d010f060c03031104060c02011107050d0602071a0108031209011b 70
    0x1040401911401c0391f03603882c0c06480703d401040030020200080b810001c1da4154090702c8070316030310081c05044001c02c18003140501114084c080c0e400760902036592400454203104841c030075641c80c044c001e0020000742c00c141240e030118000c0140181e43c580512603003901d0078200080c80c61000b00840e6500fa04503400e5544111001c1005400030b400c1041c103018104603a0743c81201079032000d064581800f6040e250a448109071090541e0b036502c24520350b085040071030014000e54050484240c10807a855580e813214070310071840c1d8054034042d002c5015940a9103900306541d242503590040a02ca2807415400c0641e021070302c24001c02201c034458910030840d5501540b000e048980c401e05022980001002c018001500070768401c5000502050080081d5600032050512201e4900302400b0000c0c00c000c040741031041076400003055154000b0f680400c3c09180116114913a6101c0c0d0341304003d503550340c8495071300d8009400c044555000080030825004051040007038101d600c3c112400d22245802c000e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 541561762 1250 541560512 541560521
    0xf06150f09040204091a01170303010b0703050c0f0f0c03060a09080f18040c0e0f12061902130308070209010801020a0827060c0409060f05030c060f1e0d0e0d12 70
    0x101d0300152144001c0c5c0000303842d40481c80e50070580100000c590340c984650308803140400303d101c040316001040184001000da078211188140c050504a9861481071980e91405103c881d8004090184071108010103101283ca4441040c1c100e0803140a600c03641811411030310782d4000104882010880c8180d48084480904140200c4822564003180c8000124042d40c1940002e176000500d108220a00c1e03103005646c11889000c19518082c1c81c24900c04050380e54103014010159082e141e52440c841e000180d011500c2c5031840105200010780e42c0d1504020076000a1402c82c4507050540000ca02c48070140b095404c120707244e0b07407070046940b191100b00b9100081524010030311031400c581104910303000c011450082c007a1070911540d552a003039400084076503070b4100884101c00300c0300410041c0d5000075124054801110303a00e66a000f0442d10b0085440341f440b0016480b01c04805805007508044040c06900520728414041035000b01885a11038002c01e200382c000c59808284040c040100750f11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 541563012 1250 541561762 541561771
    0x1b0906060d0f0c0809030702131e0e0601080d0c08030f1003020414010302030d0201140f27070801180b0403030b0a0b160203160b0f0c0309120f06150f09 67
    0x401840c280c0000316001c02e0325006100385680c0c0f41c0365207148410960003076845a100e04000040c0d420f20410f0b03030010340140e04000e84084290b8a0744500f013004006212000c25903a10b11808112000454036241c0d110079007442410300c140914100381c81654004c1c00800300b007503030065801d85580e032051400c0e513a000d400b9054800100e041c1c200880181c40314880d4400f1b0b203104041040c4950f00d9071040600d00040c000c222021a4106425070503c2a00e182000750481d128114030009540c949041c0e0000550300443c0d19043d0f0890900004002d0303003c1101c03810b5802c0c0f01c1c024409062013240155841c80c49001c001c050b104008001808030b8441c1c3d0043c201003100034000200f0780d40d17804406407190032100440306031007a0002d03407004610b030400c00360484207030340801c0b5410307586007030302079840e50040300b11801000c072b000105804403620601c103c410082c4004c1103080f81ca0202c04401d9074803200c40e004214944120400b0640e0803001020840300c0c400b008090b90b00850407017090041c000300181 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 541564262 1250 541563012 541563019
    0x240601020a140705060c0a0b0601050f04050111010207060c08011a042d030203030307050a03061a03010b07050102120f01080607020c1e01050d0c11060a06060507031119051b031b0906 80
    0x1000425580d41c2c2e0717001070280252845c02894000018104103242150150095041c080d04100282d00084c0721029201140c1090038400c00c0340c61380000c00b5006e4030810500804880c5020014007400d900003007120b050322092000005980481807120b20a842540501c03036040c9900c5030000d001440c8020000380784540740241c0b6059595a5002c40d04d5a0010342ea5440440d201240852072a9858070944000f07100114496071031480004a02c0c28502c4107000e8541294000203118040c0a0250101c2d800c000d4a20b0114201e81fa0161010711208020702604c1402d02130000456006480040c0603130002a0092018036410810940c038200e0711003140ca0103051210a00031102c100649206c2c02c14600010f449031f005840d041d200c001e090a500174900c800143ca005824030440360f0000aa03101c0310b80c91b040992130040105400c40c07034107080112030350111102c6d400607004c0120220b2112401071844010006110300c400c2010345600000c2940d0381010702640d54440503241c00c00c0100e80000015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 541565512 1250 541564262 541564273
    0x901030605060f222301030201050a050c061018021305010f090f0b07120810050603040f0f051b041e0c111b010e010507080d0c050408030c240601020a14 67
    0x200c04104c0c11039150742403001001481d00b400d089080113000c0d40420f25030405c03091204001c03a0a18455040c41800302030704001000c41c5005815000c1c0048a03114064002110103a141010141c1a000c91038000d030324003080d0b1090410640c0a00e4000d03a28100880d030443c002c0c2ea41800c00466082c20441000010400341080000d501010054400c0141907003114455940001c0d0a082c1a000380c8200b1260421000c4070422600e240f000301e010061341c504640ba07668a4441d070070280b10b008410a0b01501181000003103404010002651124080e12003c54030000e90030541004100e54041003503010b00036503040080000d40e1680c0c88a0142d15142c02c01e146066101c61800d490100c40440419500e040203800004541c3c0080103071040040910b00a8500402c1d03503507040c46c42c095424040c182c1a210510441d159004e101502c0183c00f02c04100c2c2c1d11600d0900d18160307a1503c50124078003801d48e0074202c180a43c2486030702881100107230003d126482003136503480c42d10700719040e5900950050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 541566762 1250 541565512 541565539
    0x112020304081c110408010504050c0d03120b03030d0501180f02041a0d1b0210110424020723040e010605010e1c0c0b03070f030b130f0f05010f0e011202090103060506 73
    0x4c0d540070340060031102000054501c6c6c40d1500c10300e08a01a2010f43c8180c0b14071914100090307100e41d105450b85080340000c41e0500440020902d18010203010012180c10140003081c0300c1c05100c5c03240382164031140c00f80028450005014200c0c8124010030040340c0c031842c806080645000010402551901c4000600ba08441903215010300c2400c03481005800c01040c000b500c1040e070250000303441100b1102d0745400c0c58141c0700b0640c080d07810380c100b000c00044240c0404082c02800300308000e0451184003884003546006400008286902e11842a850f141c20109860014070801c1300303a603c1a100c0c800310b4440d10307041003880c0450780c5d441c2c0b108100b80c000144c00a22506156401848156001612410103182c0500f548081805c0c2d50100343c5080102500d0740e0301d01500c81a0000c0240e00003401904680c0b094010703060078400714010305d0410300005110b030882031260045030801d00c3c0d5030240d66240c001c00c0039096011440030b50b203d082d0390010b10102c0d490b58015508840e005144038100140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 541568012 1250 541566762 541566791
    0x3090409020d150605130501240309050d0203300109050612030f1b060f040605090c0402042301050a05430b01080d090306020d020c16050112020304081c 67
    0x44500c06020510b483c1c04c0100a03500306a80c0402504003040018803066043ca41c10f400719488028010381050103102005001034000d510404416400c0f00075070b00c46030000d4030302030341d02c0d0310048000b2028081030b10034030800036a0030b046d0303c01d18446443c9465079134640410035000c0c1c071b80075001917400b201d2040d0070340303425604000400c0300c40d0b4580100c64892440a91003064040070308048910ba0f08143c0400000d0700c2c02e042110381c03081c1e1003400090507840d9030618910f06080180c5058003d480003901007080d0511500b1000c2c150102d6940c9400102101c0c01110240652a00038000c51420b0000011402d51028194404080540503c1c001070480011402d1440e03882c102e0112145264500414001d0301c4c4070707903800b41c50b1083c014000080440340080032459684000742000d940403c2e49013400324141c040f00c003100d04a0701251041314060a001da00320389184aa18017198a00700800d5408100e4001d8901c100e401c158424200b1645003082c01c26013181c1d44038200040d507030392000001c041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 541569262 1250 541568012 541568033
    0x210e06040606030c0e060112110c0a0b0a2f07030302070602120a20090f033a0e13020a120609020c120306030303062202040311031c0203090409020d 65
    0x10701074600803a640340f46042c98928600701307400c840d21110b20071082141e141d800c880068a802d08000b03001600365400d0729444203602416078400b4a600650120400b071108030b40c2c06900508104108024202c80340405111244056006c01c104522800d400e01401800c41b010b841898060300700540340c9141c540e10038007241d11001a50b00d00f045000180000150944038050745450f03040111115141d070340d520148140120442640302d40164088104240c5044c40f40613019500c040840c029950032004211030807030001d880b14081001e43c4942034120780f0403910410007120182c0300d02c0d061090080010040d44c00010900203200000c0d2221010a00d2881907100070301882078010380340c00100340c140c0d041002e09101d0540d01d070030a006000311542e0200480340c100f4421120b110905c9041030000101010913882e072007000384041000028441200d21070f600810007113054034000840ca5a03422410441c10b0138103001644140042440e5081903440480c0090004144070803000c02541c500a40303c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 541570512 1250 541569262 541569271
    0x90a05131112070e1005090d05010b060d022101050a030803090f1b0f090c0d02030709080a0506010f0b120a0c090302041107060c051c02031b1308060a0c210e06 70
    0x2004850108644194400c6030302008001c00c5900c0f001c0310a84070340060047c054104064402c06151014108000007580725903102030000e00700540310b5050a00950094000c102c00c10001001c05240e000d22050042c034160590b08001c00007410941991070300411034100078076400442c840c14206104200c02004216254111000c1900c8010b6250050089070030807041c160703004e04003003828050144490400d5900c505001080181c60303640fa400c0071030b0703508401c0d0b20982460280c00720003400d2200c08550a8141d4055401c0062040d5658080008074810a00c030130b8041481c84020814004071034000b484080f81c1c2c5d2402010240c0c803500002c044a402d4548000e400000061010811695000d500030400351800c1c00b03800d0100850f513800403e04007294070000c06600000081c80d42504030f011801c8850060040f541721100141200300d080d1041c01542050722a40c8005140016980211100c8a10981d500440803c0c0300691140460802c1034400500e07803540a2442000410000d45108 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 541571762 1250 541570512 541570537
    0xf070209040b160306140d0204060b120621060612070506130e0603060106020a0b0405071d09060a020f040905130f03121506080112061d071703090a051311 68
    0x16003000f88a40443d858004454010f140c00c214007000340d0750b588045241c100c81c09403000b00003032200c0d2001400400003500026400c48000c1070740403002400e8400d40b88588020b6030302494a011060f201060034968441e480440d41c0420000f031001e0900318480382a140421048501c01a240e90010b00c2b940c1103c1440958000c045e001007155030310580c1295005603060300505a20b5040c920025140d482c04800a402e00b14840c0c081307800c0000c1000a40010b001c10350250147c600110001c0403101d20556100b841441124080303414003030355100300c5040450654445180a14001902014120041c591a0860904681e40b4003103507200c01c1030300b903051007941c61013150030710510700c042120451303c03402036040c00c0400140059600300c00d5082c151803455240303c698a000e480c200c006011800c5940c0c8c600400560840307040000002e111003513460b41000f00c2280c000761b41d002d6699004074114942e200301070710001c00541c1000300b0045040c400b07021000c628440e1000c500d04c01ea0703000c620200320 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 541573012 1250 541571762 541571783
    0x904150f120b01090c050f0318031602030606030c0901120201110d0201150608010308120901090203010c05041517220f050a0210020307051f020904050a0f15030503030106050f07020904 81
    0xc00007054541809041d80000411902c0d401100060090003001c1e2000304010000003c6010100980d03600c003418000e48046aa82f080b0b0090210b2040c04601c404038040d1140d1804641a8900400e4001007044040c0c2800b076143e2a01c0342c0c0007007802c1c00c4002131341440485078025940070400d01c41d0429031502038001041c607030365950027140340d000d03140d00040c2004205401400014a040c08446503c4400d1040f51919151510b059005144041000b50f00d58600350003140790700d0700300c000307002120182d484411002000e4041039403d850030588a1444464075000074100c40c01e44108081e1031041044411040c6035650354030801030311800c2041c2c442d54400404035045241c41380c03003540e648034544003840c10641d0b90b6555070340d6483c6211100564848490020514500940c150f5840740e0700280140094141010714000400700c51024000706400c054426150549400501040b254070000441c0b6507840c4c42003c5416400206250200100402600740540c0d2401c0d0340b50b0081c5e00902e083c18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 541574262 1250 541573012 541573049
    0x31c1505090f0402150711040f0e0316170717070c12080408190209040f0524060f0d031e0c1202030a1106090d050f1e0406170402060904150f 62
    0xd1120890176204080c020f0400010000400081540440d28001e54001c14152403981b01200a44241042150988000b05400b01000d02401058a00c54004c2c9803141940d0760300d6201d2100c0784100c2c0c42c05030400495440680b02e81c0316080042860601811030451004d84400540e8580700c1607030016a81420045014071030150140702512a001801d104041b58901c0707039000c03500203038000b03002424110720941060180b080600c5004041d98801c1545007020726481c81147d800401510b1a40c0544841800743c01c050a1092400807c60b030141c4650441c0280403141900c1500f0b001088130402964840c400005001c1c50724081c0c5040054000d1902c400800200618070b00035003e403090540c0c82301d003d0001c1380901240300038a200350b92070043d42e00c0200c03003000a514400c920701304803000601602c00102e80c0b50000600300782c1d507180da14844800307076a41c1112041c2d80b0035503000c0c0d0b0002d0100b00f00c040d5031a01d54420440c5400f9080900314441d584c0140780c81c65145d903030040028070080400c2c070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 541575512 1250 541574262 541574269
    0x302010b0906090a020c0a021f142d07021842060f0d0501030b0c040807140103091502130b070f020f0a0f0803040f08031c1505090f0402 60
    0x1a6444900352049400c52400b0b000080c19154094000164640e001070303110510304040c0114a10980c006c1c0c440c001d0b0304000c80201c0302c3d6500395006180041d800d80841c3c10000c0c03181c1e044800054528000440507800b502407040058000c4482c1e50312000704026041c0140c90b407403c1900826000c40c10850300b45084507084e4035092000441101e01c6000700306d448001307085d411800d002d80c081d00050710038011300d000c0810441e100300208003c82282c0441d00b00004440350700564140c2c1e00c203240c00390490716101c080c8403440c041ca009141154118190520036110414411002e2040514000c1810000c40d103c1c540d50515a0303000035660f40e00050070340030100003104404005c000280c035043c1343c52041d45171140100c019100091044403800c02c52001035a541c6c0084010704070481514940650381c0b114665250b12511038882c100c202031400003000c0d0fa020090b554000c07070003884409040540d080010003401040c0c846024500d0b06900411030b0703241d03040303164440c10542c08841c0140c181130041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 541576762 1250 541575512 541575521
    0xa091d0103110f1e061e03040c05031204060e0a12030305010e0106140f1303052a10200f03040b03011d04050703030c06090b0403030903080603010b0d0803151c030201 73
    0x4a5004840040f4160a00d03103075805032440d8260710501080f031821003c80014154403507403130045000004100108010281000254095880b1321242c0c1400382e590f406040c0c546664154820701c0072411b000403c1150301a0340702d10545000242001e05454590481d17107006c41091b80c003600000d65400040c45115940078585c0d000d42001d003090710b80d0110340f90a140750b030310814412565a010103d4400e90250201d50100061a4004152202441128020b443d1207000040c4407d501000e40a040c030b65082425072568082c070070381da400a901c88100e58590071040c0d0a0021401072203007201c40c80000034140090009800c900118555a5143c00320f45240c04074040400403268100e4014080046c000151640480364542885040b100282c100100104003290001c2c0000007100208000c15501d5403001c01c1c264801d80b1403c0031038840700203042c204e400c0c2403a95a000300307614421201141000c0042c6500c0481040b101d40c00036180d030003140310014092a41e14100900c2c0040000f090380a00a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 541578012 1250 541576762 541576793
    0xc0103110301081f06080a030f02010b011706010809120313020f03030f160503040b0d090303180201080109020c0c030703030c0302060a1811010c06090c090608030316050a091d0103 79
    0x5090075541007283c03003526000d2503c3e0002c540750501c0c504c20401c01494212500a10701c401c10b486141c043c50501034400310311002200015407804104054940c0100040c100040751604006015070b1100c00544100c40054003c003034520030300d6504401488030000440c86500717841120409048d03148184042280c2c01425107100340c00c00e001b09500309522000307903419115488507500c0b0500150504074194840d54000e84d804010024030316400b550b2540280c7d0245210750340401014040e2500340c0ca0780003801000900044032003004110b200c034150040c06c02483d018080e280c81100d07400c0082e00d0003030550302c100c001c540115503403018141c040c0095980002800028031030701c100b00101c003045d240714070401050880d00c0c5000f031000340d2255200581035a40300908004181d511300f40b075801d40d0060b1280101d00c505190340425410380100c1900c0c0694081d884906541000325016111a0032840b0014100b0100000009007041001058040318110200b54201c3d5415030510070070070100642d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 541579262 1250 541578012 541578041
    0x110d080d0b010212072306090102031902090f0402031504060807031e030c03050a03110d05010f12050c040f140a15090b090a1a0d061a1503010b1303140c0103 69
    0x10682500c44d803420807944100e92102200b0400566541c0340304c0c6500c0c10b405240c40a100b0301c0108551500c055006500801d48180100301551042c62031105920500350031982104014040a1450500360040c6400400a500c10720f60030703a0481c0480c04681c0306074000c0321154010881001404180440003034000460b00150700307401c0340750300c0c041c00c000d29111001307040040c0010040c0320740b4400e90100614090111520340d68614812400010b02020701031841131400301c0380b001804e00c82d15816180800c0e8400b018021008409080100420034104c1042030151a440c44a404802090320584101200c03440080c6d5401c80102c668031003c80e41e0007481c0090f140290040656440c8049164844102140400d40390005014404058490568941c10403001c01103501013000d56000000c54054a00310f049c078140d008020812900006034000a55203000c20042c0f003141082001050520100003500030480e983e071350f40120b00c440141c44c00002e9041248040003a684c1401468250359440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 541580512 1250 541579262 541579273
    0x10605121803120f090c010f1403041e0c030308090703020928050702151f030201050a09120309050f041103060d0203070e071707020a08090d110d080d0b0102 69
    0x4a1189810a4001e4541e00801c40700500e0402200e4080080780e00480002205500a090010145003030b40b0b410f5401d151180224a2640101c0d48030700070a213400c031165610000030841c0c402a0713041650015005403030405101444071401d4840c03001d2418458420111144002d283d414014603203240036040c02c842d60070040082007d030b5500d9201941014039400c003401000f0040f060001c80381c04042110024a0522040080058006c5030f169814160b0f049200d0481e03075890512081c80c0c400740711403000030703001b00780501c05540305502400300d40700f00c1c1c10095001501d1740c048030640001c0c884118000307001c400041c402400d2440c07402d10240d0003542c052040d0a000070401940740401028980600d003842003490542d17900300107a0b40241041c600c1c0145900740b0040c002c10741a4a8040d04003040c0e003060100f00254400503010307529030b421282c6281081d500d0010450005400281550003403a4030003040070b15501d0400d1a6900c0740f0840c0ea00c0c0d560f10000358a0000d88020200d19410364011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 541581762 1250 541580512 541580527
    0x20304050d03031a0306010b041d090d080c040e0f10091406010302090303041a03101203140d0e030a0f03060605040501210207080f030f0105060703120e33010605 71
    0x5805030988140c1e0702d4100810340c01301c1c05080d090310b91144200309a0501c24000009103400240c4011300075901c000e140c41d610710002082c80e02c4240c1e0162041c5109a006043c040045071241200700e030401203010529162a0f510702030040040425241d0781052208071050054104060400c84000e10009105000c1c0c1c0042c9032031154464070080141d4145034001030b005003075a8045c000c4030040c00c1c05400b9410f0910000703032081c410360802c40d003003031120b001c048001c140b5022901d5034484045d45a5540722062005c441001400e0304274803402c000c01c50719151421a01c40c814030181003040c02e07951fa0105420f500e0030009041d5140d55000c1805c0c00801c1205103d507980c070105800e6007440c440c4200307461414140e0060024814a00050030300e040c040703042050300800e10011070051203050b400c4c000c1070f41c0311010040f203031158210003030120b0070090703401c091107001d80c0014440140700320685084070340d0054240c0015440580c4040c10041e0384581482c071054840301a40940741d030303107071907800d0001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 541583012 1250 541581762 541581769
    0xd0306050307150518011808100b09060a030f02011b03050c01060e01050102030a14040509010e0109060801050118200d140c180d05030d11070b09010c0e04150b0c061602030405 77
    0x103001c0c1740301609510b4800c58105034060b48001039080c119407240000d91b640e811a80d601c566807003416200b01e604002442d115403510401e028040d0340001d00170040303985150707942101143d10307920403414000c0c401c2c2ea40300c80780c880d0001482000c0c029101d40c1e5803904000c600c9400c40d880340d00030245414100006011590340081a5070500c0410b007400c04030700c1c051051455407400380b40d22190707000310300d070300003092204c400220603040f1190349000740a141d0b100c441e0705090321000d00a4141c039401440041040740751076000760200385010741d60110342d4100c9500000302c0b64000c00c414042a6100d13041401040c210005c1540e002d4100c03a055424600c0c424070381c4410205602c0e40c5c0f4441c090120f9002e050020500c21142401840141000a000300005134003480d080a4010f5038948031a03000204211410b00800c180070800c2d07510200180c4042041000a20124682c504825100034020505011341001041c03090210340041c5164644403009800d40605608000704541080c80304010645 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 541584262 1250 541583012 541583017
    0x5010e040c0e0607051006080a02011206081914060f151206011217030a09030306060203070b06210f010608070f0e0a1107080715050c0c15090f0d03060503071505 71
    0x480880d000c3c0c0ea0741ca042e00b4020300d080d9049058000540c90002c0004405100194407403209100382c8464100072006240c110482e0424400c40c0615040341500070004c22004002d041540e1141c10484603011000c452a46003881c2141c5100c0520341c8070003402500c03500c0010345481034500711581c40ba030411405200307481d80018401c1a612441d07030070780304082101c00007002d01860281c00c40c075900ca24162690740c015040d46481030300400d20703250000c03a0541c07001c0201c9030095005040f46807a170b1a01000d004d151041200005054625404480b000c1c410030b001d2030503482d49400011600741d04021000e41400d1080d841f800d1108400141040442e040a0225601c24140040001d800b58081d102801d588104c0d10014401c02c400901c1d00704222000c88204500014004200f100b50b54200c5007101070303c038401084a442d4051b0f800045000a043e036400ea029a5840640394031110305902d1918044440c56050003003504c0742410700c41030504020140051142101521030780000030005040340c27 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 541585512 1250 541584262 541584287
    0x30506060703051801020307120203090a0e06030a150612110405090619090606050a080105251209020f060301030b150312040e060a150e03011506080f0411180105010e040c 75
    0x190005135125216030003070040c1d0b0080c50704042d0344440d20307961440003501c0e50301103030707015104001406011505d948000c0805208200280040034400e031700d034440b103103070758118481d0800882e122140410700101070155510440c1c4a240b00c1070800380038200704070666800801d903224941c05401040104508005583d91402e0034103400203515446007010350140c41240c0104d500702d01d4483c0009103061055004511403005607110440c2c20b452086c3c201100100c2d0043d420000788841403000040d1142e0788402080380c8000c0c00b20510b6400b42c400300d40306030000da10a9808841c0c500c10040d10002d44122a0181e074030460140009046445102d46180118060301005042040c00141147c80d40e40c061030150121030b00c0c12001f8884108020041c0b40c94020030b0f4000d5003031010140e40c660701140b210041e22899281c50107980d4a04001034450f9900810a37151111100c204181640f41c456a41d4640c00c4500f024078100e40c1130000144c003111082100d540564034120030014159403007446607901 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 541586762 1250 541585512 541585537
    0x70801060906031709180903090a26150601050c01060e0a0207050f19060c20060702210a0315120503030a060b031315020904021215060310120201090e07090603050606070305 76
    0x4a80f1152039007481c501449c45040d410040c50346c3c001c1010065490451741031041072401050700301c070b8810019240e44215818496000020b000304040e5030080e0041c0100242500000505907034500038041c0e984400d61f11100d00c0c540c0000e43c14280101403107046a1014800c00401107070140380740c60182d8904020300541060b91302d44403030202903c41d203d6290203401861a2030718421000d4649626040d003641e142001d4890070020f8400031020001407010700000d0310307180b420211402025400341500000134020110304050100d0421244500003500f280510004d607103900d85007880030b040310600d41110300034000600c02c02800409050100c0079007a031000080c0340c4a011302c1c480e48040d00403443e40c540d008d4000302d5039841c003561114400d480b50508000041140100b80c080c0a4244015031b044800110003420900410304556040307031541d071041c03500c042d08541c0c411244a075007400340c8180000882480042102651601645401200442e00c3c1480c203d450ba4014000348100d0f00786202 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 541588012 1250 541586762 541586809
    0x1902010c030509090a15050d150513020604031a061509010c030216092a02030703030b2101050603060606182103120103120801032003070801060906031709 68
    0x2050300c10419039402040151408580e400c2210b050405070110744000c4d446c03610500c1d400590303480e0445403410300ca500180d02d00b2845013051f00000180100038114031800e801c80c04d4890040c2c0345e15000300015409010000d014040092a81003030500141000c0d1081640c0c001240c1c10724828011140c0e0320788242003814071400341d490140c0c00c240380c02150402c1000f0940e000211031010b40c1003680321003081e000c4070410300b054401d0078023084a200610001a4800d00684002174001e500c13510381103400509413034411500002c21076140115031049a040d035101d10030301140742001c010080c0c010508a600c94205080c145500d2a0000c1c0b00c00881d12031404240c60445040c00c800d10036001030b00480030390f0380d0b0743c01e01018144942020302c8200c2d24010040340e40d40f1100c1c0f041c045036059035480315a00940030040340500c11040700801100703a06000b0800001039450f42442140010620b40c040841c00c075295044ca6420350b10650102c2100c03d00400503110300303641d03c80484003404c84400d4401d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 541589262 1250 541588012 541588037
    0x140706050f0715020d0c230306091504050a0204030203011406030d1220040501180510111f0b10020a11010311160f021e150904020903070312030608190201 68
    0x46220340d43c1503160722644009485800608076800c001010402901c600160ba00040c1d04640700340f0a10706900d00c038000901c04160180b600b000c02d26040751804020800c403400c0c05002404803007054910701107440d8009400c0046050a0140500c1e44915101714103c903d441008a030312403a0880581d810880b100795000d0381310030b0b0b503441950822241c00c2c1c11401484000c0d80c0130440d82c4113014590225801840031900070600342200f005698019103481440447e68005480407500000c010740c00d40505002885044013411001d0302d803030380701ca00201d4a004500b080c032141c80c50801009086400040700e90001c2070720800c00c4800b240081c80d000908103030031000d43c10940546e108890800326400b004400740100d01c0c092510044c002c880145219014030300008884c920340c0c150a4000c60b040c00c902003440810b80142100c00b40c09000585022032000000e802c11219820803180c050346031040058659061151002610149000301224210380d55403005120550000074100702c203402400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 541590512 1250 541589262 541589273
    0xa030c1101020a05030c07082b0f0306090e0709180209041b0803030705090901090c0806040506130e030c010c0c0c120f08040b0702010215010b16020f030a0807140706050f07 76
    0x300c16250b0060181c90300c8031026041710352034820500c0340b00b4030f030701c0355003a0010244400c1408207180e15200c50108800704032780a00f613454051005d21345007403582e240d00000f8008510f0060070034500808000d00080c0741003000e6030301126000721140c1c410b201032a09000c01629096411a00650802000c101c000200d01d040c1d051030245e0340001020340008801e11070159004005082141c5040351102020ba80714600a001c49240c544402d00061848002c5141410550f200035041030024202c0d5418500700d0b246401501d8034001c07640031592000a0b0444003d03828031805000e0606403400028106503a141c0d080380070303180d0240000141100c9400030800c40e010403108407840d407140380942c039650703140c007000400d801c001002e80c0907000f104060303041d401a00804906a4032115129814a002e034041008014039119040380c101c4840442030206903004c001c1c40c080c162060442e0360307540324986002d01c140c4898200b02200c1d17510000082c024160800180d5182d440b148175100d440714030500b0507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 541591762 1250 541590512 541590523
    0x12190b0a0b10020a03030e0303280906021306091a1209010b0a090506030c0a0317090a05191a1c0513020d030807030c1701031403120a02030103140a030c110102 70
    0x1181d40c0300e9010500b841e50182c0104a030001c5600076101000b650480c009000c0c2c4a100c103c80d41032503802940c0d1060454505005c41414172856482c000505540c04e98402c07049038010a00414920130712101000701d40e6000420748050b11120072603407a07100d0070f403401440e640a0790350581c02c0c00c022030340041c2c0000000d50004846800040c505400c0315550305140c0c00400064030a5406802511445c0005003841030701241102d50196942c14a2806c00c201030301e40d50020716803168070800300c21000441c0e96484160400b0184805000303c0001e00d020001e0b1452031403081d0014041206000c001015002e00708a008500c144450201e45030351400248030b004c14030240001c1d4070091592070b9805060340000c0741481008141c0302002605034605041d40c0225038280c403803024920101c014000204002000c4134600d07081e0301186d0600342005041c9051010442d40828055400b00041040c8400684803406040d02600544000034203520000e041d45842007001e04a8901d080e0310020700c3e4420082c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 541593012 1250 541591762 541591781
    0xf071401020f1b2803120203031003030e010c02120115080a080d0908160302150c28090f061d0117150f03030406020a2315150d060b12190b0a 62
    0x244c2c1c2c4146844030041542d03011050000365504500c0c40090414180000112400340813070140380c8820a18683d4112010349280381c0303050410080702030f0400140c032219100101c1c00c042c0400071403510502c0400c559410314070f0b0b03c26803c1c5d46c0942c402c01b005c02d00000c2100c02600c4007a0003c12003d801b402c0c581e0f0b140c8581a86d0780d0741c0c440b005800d101896030116001810030703000c802c545c0070340d01c0710030028405020f0007109038403440454412005406c0c0c00314092088456074100101550b0343d80e42001c80200e0303180e02c80e90201e00c44600070581c250740d15040116402017403c00807405001070204c103558000082140d800c0c0c0300410184001c40c1d0b00d49404101d5000002d084a03507668542100039240c0c0d050f5201100e21300c60303000007200d40b4403043c02c803c2202942e480041503a07118001c54840b00130710180c20341e0711612450380b9030b070490b1310b518007980c03103180c050040810940806000c0c03000d85e00081100201a8008c81c0b120700750091a0400110000e8100094203000e45640c0c004100400d02c0a2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 541594262 1250 541593012 541593049
    0x306011b0503070b0f09120c120c0a050c010914040b030f0102210a0e0c010c11090705030403170c0327060a1e0204150c03030e0f071401020f1b 63
    0x1298802048400002800207522502181034140c179010341480402c1c03400c1da214070303840d08820746a103000c0e1b0840f000b4010500c044d404940c0b1080da1500704500a0380a010904010340103441030f07100344a402c10100488010030318080e070071b29151a00e04211a01e0683e0003900c502d4a9542c455216942003000307800b01c000084c004c554621019080c2d1040e841c2a0038480362201111001507008841e612804d42140064000b4080c4046801c00440e00c0300c180713910444210790b9010742d0b1400b9496440303c55110741100e481d0a5500c0c00c09003000703407200102d0307110880007540e91020800d00150b410180c0303070020740301020110f02998811851826101d9503030381003030724480e1400700b20308641c090b003110b03103a07602c01c0012a450341c4071b088066060b07105501401034050142032144245500c181d924442c4113000e0f01e000200300c04003480c41418071050184200305644985403e10082509040820910000340010a680e280b00c0b0078031503c44103460144a6141c0c80700072617080e85d450b100210f14401c00d008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 541595512 1250 541594262 541594307
    0x15090a0c0e0106031805030f0906040b0406020a0201080609150114071505011e1d0a0207050f0f1612020d03050405090103030c060c050a0e04050c04090906050615090108010b030601 79
    0x180c4840711000e07070074490303c000681007001c000c01090560b1803058080ba00b0002861a00040c0940c00c4500c0c1e10451205030041020000080d40070f880401902c003a09030359024002d84000b031300004001d607502420f0325204141040500c0810140e5480f9401a950282000c4241041002c500c00341405024409804184014080d061440d074562020b4143c4020b061040245606034821900704819400360585030b845810041d140031000c04545a031100a580c0098034144175990340505014841da800a10b560005009440c0002c0c00d0001c0c016450b0244249080a460a200d61001c02c1c2282c6001e07005030b940242c0201814030032001c0720003614018024181c296500e107001440c41c03510880541f840c3e407500741d04003520762007401141c0f4454030079a04c141c0c410442d903003003000070040541000082d020030800080c0d110060b000e404e54060040b8000036140c43c0c80320502c079150210400515204c0810443c411290703811544440c152018001121340300c1e9180c00c0142e8409102c550806c0801110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 541596762 1250 541595512 541595519
    0x30c1b21240103260315040204050a0909020109141509040204050a0b07030807020118140106090f02040f0f030b071d091303030c0e0604060c1a010e0f01080f15090a0c 73
    0x19018072034102d0348500080035a4080c5084c41c1820041d101068001464040000c203010031a4140050302001004000518081c1c1e51000160140020391056803103079115a041c1d4203640e0004160710082c00210f00050100d455030001030440445032101400c0f02c84041104074203070310749905031030282002501d043d02c80780d243c1a010b030040c0c002d140304a0018000c500001c000ca072040c02809500c107100001003601d201c040e07968882540c2c0c1000700c01d03110341d61b40e80c001800d284030f800b480c6200c040d0003000685d0f680c140722052075001d00719001071a8020300000d00300001a0120f110720f9000703406203886040c0d248400f50342001b44107001c0e41641c1c00b004210902000d02c0c100e10060f0344192281c0c50400c0003482400c000d50b2000e0143d60305650000c428002000014010100c20b401c49110350710101861095040110b4202c50a810642100340e00c17008100c1c0700c509a4869601408013000144400104144400c0ea40c4004030343c5400e10b680000040f07a502401041401021940200704c404e4840c1c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 541598012 1250 541596762 541596823
    0x1909080f0714030414211c09080109020a0603090f080f1c05040314030c09041b020601080a0803010b0d06080102121012031403070c1202030c1b21 64
    0x5a4416038100c030542d2800e0341254000070031181102d80d103520a452032045582048200c4070303d03114140030b6032810518010600401e001e20359007800b00d4618181c290704942c82c028908015504210440ea24020350304000d070751600100400c640307151802082c0c20300c8915010740c0e4107400c41070041c08100301044000f60910306034007030060942502e00e003000c00e1008500000c107555040d5005008602074840140140c0340003401907a12240307aa50701407034048130300086021604d1910364610030040840004a00782c1d41485207a00418241e4010046403074540c0b03500340c280c8010f00ca2030740002d5002601c980c1002e91500440d00904000b4021074546020f80e4450203041130858002c019103000890209000c80c5903198028055015a18a886c1c1010345400c0045a030015004030188402581070f40e0000d441c0c1c9420842e800540c1d800707903442e0144107410a01d0160000e017004140328518041c3c0100b40c4a040e0a21549040c0011000147c0642065030f0309094044444805051460005490000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 541599262 1250 541598012 541598017
    0x1012030c02040f050708070e031614030f070b1c140f06032a120f070816080c010c11041e090c05060a021507020c040935031909080f 58
    0x80c0203903410f00c0001d400c800210229541259a00b010030858400b00e04400e10481141c021020081c044541201c1c50507190490020142d102e0100e040b2889042c0304642020b210a20003e50004c2c010191702d0b007008903240b424003c0414400b111fa4201405500d40440d5800000d6030900302803079040319081c0080c1e80c66020f04119006402407280c0e8001889050006502c6030802281016800c51082440b04000c0400d00c500b114152511134001c80d094184020302112005003c080000d00403e003040ca00c0f4141d2201c10780c02400c0c540c000c0b07103aa0303005176000031085e248036a10240c807485e02200c46000034000c0061040c07244015040b0704031014224856480000010b01540d4079a10142e84c034001c00c4414451041200e0050304220046600c5403da1a80703607800c1013143c015112491800340200d000c90703485400c2035903860842001d12a0300e0441c4d40c1c00c444240e00c01503516200102e01c05641072a40b1014200b140c132087c0703801c044420081e05500c90a4100d03401380c1e005903500c0c0d180e10407414a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 541600512 1250 541599262 541599287
    0x161e031b061e0e1605010e010c05010b0301020a080405060112031b080c07030c050103060f290705060f0403090e040b04033504060b0607050a0b060607050f1e1f05101203 74
    0xd22036001c102d60503500010224040317540503503034040a200341d01c1c01151040c03020f50044541e90349580211079203980070b0001e40309545107561340b80b04610700b505005240103c1a0f0017a811502e040001901090748070a045101501e00d5441c0315803880181340580c1c0c20300c5034455100751402684408010080000002c8048400981e001c0c4509600e454480c242c01480c3c0c815107040714a6420f040728119103020001403011850b00440d42022003a44449040800c201e40702441d0918980c108410541c00c584400c025110710200003155190a07039885001000c00f510190902900340e583c501c0100114000d40c1050109854980c06011080100200300405590444000703050040c10b0001d400c0c8001074800c50390304140201000e2482da116000444005895a80c000300c040081c48041241000100d00c0041d100004005000e04007a00481020403d0035240541d08000080101c40400140c46444603640800000da07688480c0200560714029070f02880001042050900a0540020f40503540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 541601762 1250 541600512 541600541
    0x60c0e03060718090905070506040306050609012114160f0f080f03191202041d0c0c0a02090c0409050408030f09010c0f0c0f08161e031b061e 62
    0x82d4544450550320000c4070407005214400305101003002e0400c030f030044a1094020b005607a280d60b1900080340c52603100390000d0354940c1e100c0c4148444c500300400b109004045402190f43c4c2c020445e400c1c0d10f000000b90308042c200403ca4449444c2d60001802260014055510304441c615136801c82101e070300302c261003940c2e001c100140d00011107503404202208202c0702c60000c0c520f0202c400e089426540c542c0c001020800481391141400a2940d10007407002d440e03082c0d901c1001c9491a5030001c11207100030815520410f040c4800e03000c45038005204840e841d4101c40750740c010f581d009104185800b03a54040c008031400c10050200303001d100e40046000b60754111200035207684802466090b5854011070400103103860300c100c51058800c1b094241c00921480403410545a507807100412500903074560384190004400702000c1144104182c0d030740031803071110110150480d890103402a4400f580c851080c4108504160402c41607a00206048a204a0348c80804030f60030402802440842c0c1212070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 541603012 1250 541601762 541601773
    0x11070b27091e010e2e181a040b130b0d1a0106021207081b030d060603060501030b0f03060403080421020a0218150f060c0f0604021c080414010c060c0e03 67
    0x482c2401c98209901c0b80e01900c24074030240501602200395040701c02050b13044a40b0001002c00d414165071040b8406c00c14103500411900301038200a84034681b10340c511807159190250071003903030700c03504c080400e4002182d500080f2032907150042420310907141030080030750b034100303811158041d51241e090f0305990041c0e00b114a250905285000503200303102d005060303010b05020148c0c000c52502440d801c00e2240d041a6803c20342c24183c900151115a0071140209032560400e11165070b1610885250007000c07502d2030003030700303134180460340f154405000a02001003240001d4240100c001c8030710388080000e1118000c2c05164640291981c0d800d001c200e200f000a0070080c001030f0059040980110030201030030754a86031140c10442c100c000b07a8207440c0c120f1000d000b6468144d400380035000c3e20f00c108001900b440c0c6054410400e0324041c034100018031500030f4030b50340007042c0c203c015034003980c9040001460140e905030041c1c0e4004030002008003071509151003078101c0d0b54054035158914006508480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 541604262 1250 541603012 541603019
    0x180406091202030703050f070c05031009050d03021c05130209010b0d0606030203190c02211815041503060e090d0806032e060b0f03040311070b27091e01 67
    0x82c2c80c1c4c880c803000a0000381c4140414501058408010030900b4172420f101e410295550003c241400c24240d1040b00460380c4580351380a018041c00340f0203800003645811440c01082e10006003000c850030744100c880c69594000101c034a024040c40100301d58004056140c1c9680d030300810b00850303000c0c01e02e07081c086060040000d02c00d4060300070350b809aa01c0c1d44990616822403000600100f4016245500310f03ca0000c80c000041201e007040300315912010301c40c03a560380b4030040b100b080320b00300070400740900709074030044000a58010a1303c0540d08a90644101d08440020450180041d604200b4040c02410240b10701c14070006460707580e0f206980c5a05103039607100c00130151184844159451021180d2050754100e1b2642d02d000356a040d801d00c400035107181c071501c240303005d600080c4001ca42c444c0000107010a046c1c001007801d091060400c0180702e014102248110300c5e0080d0400400880318441402035600c02c01140c900d9001c501800eaa40b1f00c1c83c02d16034010303001d607015443c02500000f803c00030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 541605512 1250 541604262 541604267
    0x1381606060b041211130c0c02040506030a020d26040b0a0f0c0213020d0f0e01140901090503041401030e060f01180209060412021306080d09060e0d111804060912 71
    0x503421036011280130b65500809407184800385c0308030014154810b826000c80c81da8400148505102c142e900c1d9255034241e40580705120446501500c02803295020800e094010ba40f03040301d0000b42d81d40118180c01d003400d01e1005403140c9181c0013440b0000c40010074041005006080071b040c0340b00381c84c2d031540705505903000166245584054065000800c181054108011a400400f15000c4e021000511807400300c14500480c2e5031200d08080383e9440300010101c900b80b88800710340050019008001519096480e265248038a2103444140c0c25454912070850303000f070b4020480740440f14184c440900e0b0105c0080c4600000740940d007000b800f0b01702a140080072920aa5042401c003070045441c050410315500c41042101c0400c03680b2504c41840d90f408c071f8115024040040c200d01c4010700c1c441444001c0136000140340e80040c003c119503a11260029a41c90014140c03854000c120740d0141101d600c041030541d070003030031081c101407550414003041200c50b80c4843d019a00428520b80e00c0d4061107000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 541606762 1250 541605512 541605517
    0x112030e0109030515270c060c1009060f0501050108101a0c03030a0e2103010311041806050a050a0203070c0b2a0405041803080a020c03070210031e0501381606060b 72
    0x42903190b4080410901f480c00d0450080103446e69400c1281c06030122401904142e07140c00c0f9040f65003584400400310702d000f0314010640501803d00b802416850002c40e48880400f2511034000c40d00709103078422140150540481d1904040c0200b500d94a14040411401801c4100c2000045115401d070017403036041c28010035103004403074025152445e46140c4407050208031072180c041d400b960b01c4a000100080c0668640a040d12503240800c00b4a0114110411500c004041d9850036004008114004c0e03408280b581000e607000099291507150001450b1034403035403d10040b079031000911a030058040c0e04000d80f080f180c00b21400e10403120100c86c90b51071684108030003004220400e01144035040b49802070030340f0007002c108990a00c03143d9000203100818400403030b001310b6036031f031140c0d015030740d48406c0702c0c00c091200241840385501d07292702e00310846034490848410600d50222030407240756001d4149004040b00500e291a15245041c0420780081d60070100c03151850240f0014001465205 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 541608012 1250 541606762 541606831
    0x8150a0b0a0f09083c0a03020607090f12021c051e0f120f0f0d05190b030106140402090a09060b0a1e0c0f0201030e060a060f08060112030e0109030515 66
    0x1208807006141500e14075030301040d982c25101740112107803280403200802440000c01d000e98010720030b0307052844010300b0207002a0800300025181d6001440b014021141c001002d41c1e05996080303403201410107a168001e80e1010040c100d0044941615030001200c0c3d10303040c071440b010141c03005034444600f101d6890f4402d000e0071003549024001c04079030600c9000034205a83c0000000303403800d500c448542044400844107404804940d0f8000804010188104020410103078000c0010508140303905010700d0480f0702c4107100d03070340001e42c0c440e0546661103c40014034140c00c0510440c6e0312a81c1e80606500003240107800a03c8800306000316405112501c0011b05040d2290400440561030703a070715980e81070a003681855180d0b90030416142c4c0402400c3d02c10080715100086007070610710090f6090190fa0300215581e03004d54014403e070903d0312220b501c1254581800c0103250840001030380e4881d082c0d4406802ca029511354458010391440784c4610405d00c400405485051481440070107a4a115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 541609262 1250 541608012 541608043
    0xc0c0e01090b220c0519050d0c0c0507030605060a030f050105181b0f0409081902070902090a0e091c0e030606010c0b070c061b0201090213060608150a0b0a0f0908 71
    0x580c03c01408002d6002c549009024989245806d0000c0c007161070081c0c4002504000810025502d484000f03140f013043c0352240f42d807820140525441d15056a50680f138003003d40348541d0b65010481c41d83e00c1d102808000c41e40501845145455420494002c02e022507504501d07901c0341d195241400800b081d0b105000910308440200101c40340e0130300aa14000302c42080d0400d664801305400304518401801c512041c00c840031608400e110802410000960f0085001038010b021103c02542c6000440041c5e4448008801c559503610000d01d00d4030000010340d0b4a107480303074017501c100f49500081100c2904015421522940c80320030045428064444001c1c201c080c4000c0030a07401d900c0340842883c190301505011422100420114802400300039034103001d07030340d0742c2e07118002c60401801c1c140b080204000708010080c076103000074102070310080940c0094800100011142d0343ca070f0b4440c00c007601c070961071280c680081200c00740c5140300c00c96001012944d520000580b82c003000662091000e00a07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 541610512 1250 541609262 541609309
    0x31c090515041a0f04121106030a0b010f050c070501120f0504080409051f0e0709080706110730060222090b0f01140a020c0904121803050d0c030c0c0e01090b 69
    0x181c1c1e140000741b4044001c5600b82e00000d80a80e203540c400c000395000701c4c010080011103040c8040090055405045882c080c46020b00000310f440c00e0216400003220000e09101001030208082200208141c2980d071003041e04c1c000601007805540800f600c2502c1c0301540401481d141c45070b420300040240c140410031100204020311040366000c1a041d080000307400e10440d4191180c07001410020590080c07400521241c2d0210700c82e082c100108401450b150748850fa9410440751680c40c04100042280140d81040a500302040741e568100c1c0c003583c0341c0009401c00441c1001c0746104003407451040701501420316980341201e01d0180b40c1203291500586442007000030100c5014a83c1c0c000d04025425805440241d1441c0d44401c070008e84503900c01e118848880c8440d5101400303200d50b1030040660042034803020f20000b40005521754a4400508040d6488109898100c52444404600a10600851400240284240d86024140e811054041c0714864450051000d446041004020340e070014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 541611762 1250 541610512 541610519
    0xe0d0803070512010b070b0103031d0a0303050d1d0d080414010e0307140607120b06090a0e04140604030504050d080405030a110907030903050f09012601030204140105031c090515041a0f04 82
    0x3401d01803a00488011051039a0080e00000cc10340c0f40c0070b50054010903400109a03482811034420a00002d080d6600c1c5803101b15441401c0e581c950411944005000784000418117110400380007840c0704290000030300906100040e0a80c0301c0d00042c0c030803200322000b282c13140e003d01e001068191007006260b451070100d041d00c0948202074040e803480070360481c03c00c105c10691341d10745200301009001001d0590216050914002051034060014042c07244c20141c2408002035000045404a0f10111094026246581070004840c402c607401103515100301100c260401122645890180c0002ca5031612503940f01c1c2c00640542d00021402400108200100580b914051001e44038950040c50204034080d180715107001d1889802100c1d00b14104d488004108501e824040c00907401e052840160495150070701081d504d02d036282e80058a000101005202e540c85805000c1c02480010201104000408590301c07866001d4000c0007406007180708103110118140b812106544d42d00f04220f0b01c4d1618 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 541613012 1250 541611762 541611767
    0x9170c04050640020910050309011d0c090108010e0c1908060711010507030b01051b0c13140a0207110112020f04170d080c04060e0d0803070512010b070b010303 70
    0x200400301a0f2100c10080004090300400700725908110a24409041c114000c5440326410300c01d02004914035801002044403030740314092110b02c45401410407607126140e10003864003520024580200c00c00740101d4600040b040002d403400e194105803100286a621802510b007030752501300030504140d120b0300c918019030409520620f80300c0404500d4401854980fa005d5040003400c1d074043e0000b44600d291240700e01820311445030400a1414104044070444002034040e002e4000f031401c81e000c0e01810310b2405071042c420084900e000a0030024200c9111509c0e100409020300904c02d0000c454000807031101b039910880e1505a00280e0208003100d00034011102d0b521945240e416864091140300c0c0713548035001c003a001130120520500d043d4911001028988804480c81c24200000b003014043c80c0e903096070440e002d641544c600300c051011038901040a0180c00c1701e00500c9034200008000000c0c0d03000c006048008101c0802404d6642d80384c1309020980502d0300041c20140803907004000003070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 541614262 1250 541613012 541613021
    0xe0906010c030909050a0c0f0509090a1107050d02061504090512030903040b04091b02012c070308030a050105030d08090d0315090c0905030606040603201c050a0309170c04 75
    0x18480d240000f00c25440303921038000d90764103a03109001e80ba281c0201c1950300f0340112009803400d140e4a0110700b00b40341000040c664500183c88840c10a6030340c0c03403000c201b40000040340c2e40d03990020202d410705029950029503410044807803602c40c03c3c2012888840385450300a098207d5000b10003081808900450311006500107040c8031020310007000000307108101c24000e040101403a00c40000c007004100b42000f124401c0c05203400459161150308640892441d6961004500c140480b4004515114140345070a440350400b40c00b14201100f00003e900c6990803140c11380c4c0d020780988cc1901e400304415185118280c0e06850260024223070320350298406c0e40941126949980310f4032200d5944d00c0e0200454042910400000b104400e0a1002e0300701000704507084042035038108503940c5513031600e60b60509241b010941182d0b43c0410099213a445600c140d884040d40c0d41c0c06800d01c4d89902d0f1459468a481c441107012500c0000c000a48030310000c070300c0151200350030280c0603056540b03007004000c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 541615512 1250 541614262 541614287
    0x30e030c060712090f1e0e06030a11040f0915140405030304141c030218030d020325021801180903081305070f080d02010b0a0b070308070306030204020304080405010e010e090601 78
    0x10130b40300003c00e0314450000c0710042c240344400104032065000d2404403d542604682c640c4030b02c2c00e052043c1900c1c001505c071030690300044000002c41800d00068050040414054280d50230610000300317215071035130b0400201c2905102004455a41c03101010000000c41d0003600d150010b000250120f26410710b122913100104094852044644d038049864240b030b2040c080000c0e41c046140c1e0f48520034000e16030480c40089004042c4401d851a000b035883c460000c2103006000403031150800f100d070f40c0da861101c665001741b004803035199580761144010800d1141500e240c441118480d1710300d90768824203031340503010f540d03040c019030700c4142500e511308000d14100c805100d84400011102e0220300c1035005000c500010305203410410744020b09407900d040f0302e94858211040300b003100c2c80000c000c94900769410f0920840c81d03501c4080c1900107281e103501c0030b500540000100410451003000400030350340241c842d442c20645841c01129517100d9290016084005040802c08030f6004198030400c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 541616762 1250 541615512 541615517
    0xe092509051f0c150f020415030506011107090c1e0203070302070e22151a030f120a0e0303070c09020a030525080c07020402071b1710020d230103030e030c060712 71
    0x4005d110501e40c0407a031040e80f050a40707011520485d0741c156818041c0ea9013000c8241780014064244d01c0440f07840b00810710601c01180e54800d801c8940324042c0200d0040694171000300744082200b01c0f4065240d40c80007108400500030b140300403424240307000540d0f0244807200000d2400989400107803000c1d003041c5100340c50303820920300c00d10208002030058910720024180e0035414200b01000745880c144003281d002d441600403540c4c4161824684090352000c8461381360140f0b000038070360082403d500c14041d000c1d0444001110120b1030f1001500104050107665030100115695412000075101d1085200c042090380c2c0314040240c14496444140c004542030242450890182e0004080307a00ca00f000310307548865420128502c52918203014000c00c3c440e0204400241010315003510341070000301d150340055006c220300840c058554031401e4403880009400350140c1c080a044440800c007480120009403c04440391440d00300843c0c460190381016101350304200304c07950f40d0a0710b1605240398004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 541618012 1250 541616762 541616771
    0x3150f0114160606050a03030806040b01030e0d0302030f0c070201020c0d0611071a07020102280504030605090c0307270209121f0e0105070e092509051f0c15 69
    0x1520505a00920007010045940c040d0030b8058940f92007990300036401540705284480c400c0001c03e1700004010761003070048138006807030f030714a10044e401001c1031b224141c0c040c0b091250000000750503600031801060141ca5400c1d065503814002c0b2014802c0d80b20083c016004402180098100442d800352a18455500858001c080280075009500310f03001c252144950851241107080105d4149508861184001c0d481c0112854198801902d0340104c078205550201481009034030038000d40e80a50b0b03201c0e40c14802d500b4000f03411a614078050194500c40e0141c080c0008218102900c4480344101c84902601511184c0e030a0100a400c00c41d903840d0800b2403060490059041400843c0184001d058841581c2d4031082c02e00c0201c54900980645a030716040900c9406600000c9506980504503110441a0340b001c0b2100d1489c4d403846210782c8402c0011b10048205500052030720140c9a05580b01103d800c6031450600c803299085501101280540e0302000218409202078012030003a4400481e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 541619262 1250 541618012 541618037
    0x809060c07090c050a110a0b01050907030915020405040b0d05071a09060d050702120c0304121a09061e041518081c060b09012f0105161403150f01 64
    0x300760743c00c1c0300200c00051070010b416010190001815401880b0000091415000720398444d0760840041c0585803003040004d0004128501c2a001a006254010700715107886a040388460040d40060041d0381c4118101104642141880d0741d20100b045d800000400c2c80d41e1600740521030500c132209406003d41c60400c0080c0e03054440c0c0004000ca15402d0b40d0000d0f052502d100020b00303100140381043c169040c1040240f82002000041d00c0c184d5100e004110540c1d82c60340380c81a8030f8a4a24808035100b002d4100f00010b110021403604d110b080750500c1c07030f014040e41000d01200041e003214020704085824105500403203655021a013400d001e04c050300e00c1e00c0c5464507411801d07001484000c80c3e0908104160840451500034840102880441c06040000c07100000e8055003a4041d0b1090102140c41c0310b07061040001c2d00e4480e030089601c0200700b541040150614803c1c9200400004142d0350074030204c03000d00f4442104d1080140200030105045181d0401501c008031900e180e04009501c0d142c1e9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 541620512 1250 541619262 541619279
    0xa0506010b0c01050c03190c17040b0403020d0e0d0f11030a05011e020a050d0b0112021303140312041403130b0a020f1b091003081b01050a090809060c07 67
    0x100d0291101401c21500c070030b4212021425074000400c415007443e418014021030444868150031262440c1c2004128070780707242d8044811551f2880e85103207070004031050205108140b00414000d500070350956480301106c0d40c056440380c0400c88070540186407800c00402103626403d003849034030700c12011816100441d030002032034242c403604184c0d0a80d540c0d0100d901100591143d480c0480303010402941400200500540140503c0d000940b100b5150012100c42c0d03803103000500003105001c501103458108040038050711172001d010480b110f48102e030084201c8840002682c0e40c0c003800410b0000280e4407a0b17102401c40c40400c2e400c01c4188800d0010711443e07660030354200b01803d14401c4072500c03110f804000030716010102000c038290390009841c100c160051400c01d0003500e03409441d5001c15864000c006040c405055101a00a001c0440d41e01c4000b0a211242c0c041c00d80084028802502e59466020445131211001040e110003081000250f0900102900352040c007403050f0360140d44c2e01ea011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 541621762 1250 541620512 541620523
    0x30405010207050d08160e0d0303022d070c0e22080d050a0e060a06180b01050c06091f0509030301060309060b03060103030e1206221b0e040b250f020a05 67
    0xe44011817a00010000c8154003032001e595149940c0c5000c10b24040b039800810140703400302001400301a00010847c0c24291001c02e290000410fa42e40c105252401c80103580490304881c000320b0f45004002d00002d043d01c07030040514000c0100d030340380c2d40c94070f5000f010f0540f10740c4082608031041c40c418172261000d41024030030188030300f42c20203021402900d4040614104000105030380541c0345045420711a20070319050080c40d0103030b0b4550000750112940c0040c2c440380215245482c440c4103107000c00821900104d103040c14940c0c03225500c80c04009465803030003a58011a481e50a90f030080c4010880c00744607401504a460052000040c0000040d0202e410300c1402d800540205404c06000c0d801c60402402640c203185100014000600b40440e05811000060040c9080f04030884140c009108040f40e083d000d4440f5082101545556507a08100c2150104c90654240d1b0801d00060800c260700042d001124042d485034400101a890054540e121101404401c502c00c8150850010b0001c018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 541623012 1250 541621762 541621783
    0x30c05040f0b2a030d1107052113080d180617060d020d0c1e06020634020105010f09050c2b1a0301060609030b01030f15181a071403040501020705 64
    0x5582d464802c170202d0350640e2101035130724407600300402441022039008260404e10300c190240d5000f4480c1000f42c41c2116001e044140320a40b81820000502e500002a03102c151501c1c40c3c542801c004c20702800904d24940900c9200f0100e584d46d03814050102c2c09481e00b6500c00700c01018040401c0c403a8000c50a4031243c810101e4205041100505c07108076107c1400340f822030602e1000340c2c0c650600000a49861005d880d813541d4144e2614650b5210205110303041c045020100700301100c8058500c0280640820310410380c00e01c886a0011511045a00805201e0940141c01c1841c21061201d043c1c20050441025a1145100c2550005249150081c2d00c0c0e24140310410b401e2a490507410542141c0356a4480700910140060070000150741c4003c3c0d40c112a005400d40201c040d00e402c18182000b004100705003070300c1c60070602c032804000c66000504a50b010760b60151880e07407000b012040040b015644c11000c41c05c6152050400d41d80c000081d507210f0b100c0c030b0025080031a00d50b22503190040900 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 541624262 1250 541623012 541623097
    0x152c0c031b0114030702031b061b03090a060513060c0f0806090103121d0604080a060e031801052d07060510050901090c03060803040e090f0613020108130c03080307030c05040f0b 78
    0x50030b001080c000ae0116000c0c40e0f03400310b482851414510085950b541c00c0031401400f441d120030016403040d20502c00d1211480c0c00a4003800004d00c90392000340540428400040421401030100b00c403030a207140b056040c3ca47c0842200c2c80d4010b07140007510714090b07080b01080b4007140600650166224040a40700500b08000204104040b510b44a82900d4650880c03071f0b42a030040c00b0b2040d0800d039001903441c2c001c40a091040e51805030110a0680103101d10b40a020003d0300d80d100302c61010b801c40280035503070084004022940b40e050203440000d4061140581c090001c400600031440300d41e001c1d6004030128100010702a035240c881e5421504070b6445140fa00c842d40c0104844070f2010b000c004914800c00000e015949004081001849a5090007904011103100000c0b02014041c2409100940283c40c07000315581c0c1e482c0c5098240d0085588030006420085540a1903006005071019200303003071201251306007804200101034000826030f0350141c044001e28a400703802940c60001c40410700c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 541625512 1250 541624262 541624273
    0x105150c0a0606060e0f06160f080408060403120c021f020c060c04050406080609030a0509042309070618090e030915091507152c0c031b0114030702031b 67
    0x4c0003500710090a0455070041d40c4c0303181d141a00e0390b5103600311000900342200d5540d640d111410301150340000200003e140d0701c00003034003007484103000074054411442070380d07442c00c07100e060400b020544442c2006c0d1009079202039034030400c00300d00002541003600244801030a095184210b10b140003400d07240d40040380b0002074180854103203405944003801200004184900b003104480c0d075a8070544124408000000c0b480030519a55604017900720301c90f0b840320740d0301c00c100920b04500d2450142d4051215200349a80011b6890054054003003040740404450325091920b41c442010303000c0950744608a010411891540d903452900d00c68802e940b802290b80c07130b69800390a200120f1003042498001007020b220074800610340742c501103041c04000704082844078030b640b140c18009000c0c03000c400c5014814121074030082000142e40e901100101c0403181c0c201d0400b40f505014045407680580012180e21401503484c852600944d08504584101c038607190088001d000224148140b82d207a54012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 541626762 1250 541625512 541625519
    0x30c040c0314060306010b0417010605090108030d20040501111e061603060e04110111031c0b04060308090d0c030f0305040e0f310c03060b010908010e060105150c0a0606 74
    0x180b020b2203501c0301081e00213003001d505080ea04000e40c00340d442610222080403a001c00031500c00e400110091901805c2a00c01c0e5844d000e11546039041081d040c2680b42c80c200300c103180042d19400d513000d20703265000358a141c6400ccc00e004482195044000d81c0c6c0d40e21400701c100390b506e890040414009186440600018208481d90340c0c48104600441020582000418000700100b8280d0b10f82041d8001400e9a00016140040c1c0c0d0038084004074014900000c214040d0102107180307041400e03140301c03000b0058004400100030444d1070307a00002d88542340034440e0604505109901e000b0880c090200c0c00000d43c0d41e80d90380d41045d81c541c84210005580801c08001031407440000303d803c452442d42500c00e526001e81c0c0a20304023299a0700c14102451341c60000350301250160b8041040350000c00b0841710360307200d08210010700740340e0960340e001070a0048005000c15041c0700d514228041030b000752800da40303007104000a0402e450560007040100700090f0300c18050800021a02511629012030004d14 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 541628012 1250 541626762 541626791
    0x70204090c080f0d1716020a05060a1d060c030a0510150e0108060904050a1506080102040902090a230d060212100f050616150204031b08060a061d06030c040c03 70
    0x90b400f541800780712911030518500356070396805d550b105c40c840700c40c43d1100d41010401c0786000d039413900c0075040e4014041480f042c03d0395504121955400242c4000581711000e0b41c1c1a942c0e0401c83e020940280c0a1011401008482e001241c000c00100c080803c0e2903180d03a0010641108400300401154900342811060f5030085c00d090340c002d1044801141d135240c03580360300f520340e10280801000c2c5542034108405110190b4001e4000c0d1070746c54005c540f03940d1900c180310f000350300000400340b142000e140000b400c8683e200104030719605000e85003010700080070520a5000361030800302c03141a0244004040c40e102c620b0214400c0d038030b0302004000d141c60168444c882c001c2c1c5810240c02900100100d000400c28040b80001c4294003107090b000301a03481450400902890304018040c00d54112165181c0b501c0d40c04240c07c1c1c0310700c0f80036121035480d80c40008045402d2446680d0000100385094800c000162031f040f07500041c05415150310b1000040028115200b40540d0f40119035115400b040400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 541629262 1250 541628012 541628023
    0x170403090308181c0b0a0c051b0303090f0c01093f0605090f0309060702030703020303120106080601020309010905190911070b0a02030c0304170f180907090308040506070204090c080f 80
    0x15004503460000300309075100d49101d20001041c444a158841511f1a134003403042040b500c01c80380000e0b00300002d580000166441e5807050360040002c5c850711000a0f00c1c5400420f81c400c4100c03058484080252808400c03820020501d604454070081c23013801c9160603a21454494820301d2801d030034140c55581864440112640907088944035482000d00610441c8008100d80380d2042c110f50700d0340c40d0300703082c40001d1400d00c0f180c1009415000100b081c243c89000d07a00d486041c2c0d40c054946224907a41d91004aa032805851021800121310350810429401d00c0e1841c0e584e21424000d840079101c1d00c0d40c90b99412b54000f400349440c007020000c0d4070b1007405102c0b06e0391508032000c401c00f540b46040c031003008602404058005800034000c0070240b1a4015044101d0700e00c203c1d011495900e4664466400d000d00d003860741d03154000e1950a0025440ca40304076405404e40354481d503194285802e1000307110080e0800b1030202e0304542d131807860502041c42e1040740c1c4018140d203401056246001d05c915070071300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 541630512 1250 541629262 541629289
    0x6061e02060103031d030a0606060e010f030c080103300f1206030f060b01020a12050a0e01020d1403100902070c0504061e031115130806010f030317040309030818 71
    0x1500300c01c00500000c2c1d03000c0030b08241c2c000340450807440301002e02d00080c00c10041000c02000c8030314000000a0b00c6400101e40386024400340c0306c100c918107500d5415000d80e030300c0201e031000151a01e001480003d011401e1001404104000c2200b0002444100f1844240c020701100100e00c1905006036030b16408140105000d51a40301440514510740c0c418480e0b401d00000100707a582c03a4020f809403030b44208130020030240c206040f01c1154030740960107041c42d4032104024000400e5003820003015400014821048180369440041d442142030107507070650005085941c01c0005100c00142c808482d001801007580140320782d0540074a00030400084030f006038800a0115418030504400003180448801200d4200b4001101d50919100103038500034800707060f090000c008101417031038902c169551b405a0b9000ea003150801e989030700d41254031410900c0000c0001d500000c00420204101d076446030403030320904014150a4590b0345002058000c018200041d10140e1010010b902d0301ca142e03080300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 541631762 1250 541630512 541630517
    0xa021b1c02030c06010b0d020c030409020409050a11070308152805220905120706090201120e03040302010e060d05090303160507120f0c020402040f05010305091b12010f06061e 77
    0x810b80d40100f501d4075604144550111028046810600001d03650101e502c911441410749a446480b0003403000290040c2c00b070340401c64500000500003990b64401e0702142e01c8414640c1d42000d00d295001c854000d0020841401030b010044c40c8901500d40820005410045500e01c403901c0da58541d01c00b003404001e501180c420390030001e440d540240c22910810403c04d551700b01141500b401d0805501d013031060361506100460000d80399050154941c415100e4601c01daa5400e00c500c00411004180c130b40d882580c1c0b0454000b040100015801001b52404201d0050496410403048240c80c6013160b10032664003195800010403c4070840f80308060401c44150740c2400741c100340e00340c4c6404040c0e17030300740d80c003002071000c060b52040400b401580c4128010303500420030340da203a480d25021006490140b01d0540424103150104070140e0001c00c3c0745203a541643c441c100100d0041e405c00c04140d0070aa9440065541e60681800b08000c500800d4050580c81c0c0740c101c2c082d41082e10404c054121008032404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 541633012 1250 541631762 541631767
    0x1501080d170c04061214182104091d12130815181009030e0f1807050724050105100c0b060f12010203010f031a0705030604050a021b1c0203 61
    0x8101882c80e066409491592403d03180503d000138005000b4800c00d5148040c0c0e403d000b041100c1752145604030f601d412426015186410800d90741c120341555064aa810705090500c024010400302c0d500210504c18080c0384105203c0101001a0401d1058a000f8240d1480062008000444c01e2122802000104020080c203540b80052600d12840035010400c0025035841c1c4a0411034100583c010403104040200806107281c0350162100f0f00744070009004040e01c0641c140c0354540310001300703030610f2502c0f0191210342e202c401c2268250b022000c1120108400d0144032245040400b45420a110380d190003c0e1650400042084441500301c074081004106090600010610001550015070541c0c02148071580040081d007400f1113601d0321001c035131021000044d96180703050b541007128020a030032a5050100d400c081c46090b411180c05022550400110f0b0301f9013040d501050340011400b0f001802c0981c26086d0b01c0d0150380ca40c64114036548110803002c0d07820380c2e00317012030403880d5140000e51 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 541634262 1250 541633012 541633021
    0xc150c030417030112020d02011e0c030207050103150506030402011701030f0215071a1005040903020717011803051c05011401020c0307080703080304150507020303090709020702211501080d17 84
    0x40d00700000745e0080c011411015031008590143e5500c0c0b40e5840645141c0828404009000384030708103081c0160018480c0d4500055154000d21502e0300008806209403455420030080c08801c0e48050822030400000c84404103618240a40d4076000c1d500c1603030514a02c0b039540c01000502c00e4802c030200c801d8502040508000740b03106084e40f8509034103020b0b1400c80d5440400301c0210180a902180c1c0090034510244201a0b0200300181541d80481e100d136540140d04940701e00303c903000b84034400c1001014100c0400b0034007030809000744002c1c0714030765800035800030300000964074207a00502c004114810410a1907805000650400781d042d0300a0001914003d80c07030b9901d0409100c083d010b070000001050a00c504582c450890744030300541070166003442c6400070342e04d60080700e0011207030003211000300d0915210b000300da85440d00202860085401340701015a59026132140300068403030390750403480210088600e0344c02408884040e0951005401028003002419003142c88910301c44400c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 541635512 1250 541634262 541634279
    0xc040305120301052818020403030917031c060b0f04090c080f1302041503030221031501030203060d0b07080703110412140304090509030304170c10020c150c0304170301 74
    0x819030300440700409505043e400d108030402450a41102443e454543e03100c46c11210b96030010f00c00c0700e10994a81003600d43d03503c3e805c40c070802890616001c9030020031071001c0c0b00944803444916603407460400910160b0b130b008640e41c50790040e41111402d0601007010000d022003807040c0c00241c1010b00b010000c0f460020000b0258007001045042c10005503101c0c50155180c592000d0b1004100040b035449040e00d1b400c0280da42d00d4500c0c400d06040b190801030301701c140300c401e0980c2c0c007503032030214010b222010346401500a50002482250485000c1115002080000c603c0c2802446162100d07009030800040060a44141c1c08112003c1d9800300070410001104200f15441142c000300030b10700c1d403102640c1e070728110301c219844801a60b00380018480155008001940528031a4226001c80184004a11014011521310300344c2030300b006180b608d031001d0a8006140c00c41c03010082e22100c00004400b0940032405403040200c4600100412082080f200807036002000c28101c0c40f8290361420240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 541636762 1250 541635512 541635529
    0x40c0608070221070804080708011d0705100e1807140f120408070b010b0a0f09260106081f0b010302161103150a0203150a0501050d090c0e0c04030512030105 69
    0x1e84400144140740d2804000b24503041c2c1d56020385c02070340035964940e5820010359031940c60260105c0d6500e0014a924131103281d400040317040c580700f4080d0420a19003810061078200c95803448c0103014504002d15220f83d0ba280f00e98000744851403904046090920b0010003000344200000d96144003042400031048148080e944412003505808002d07a03102d140c003491a014803d030082450310f40760300109006402e80094404928140c3e500d54000c10080c10485261f086442100c802d29000540036909440c501c030306c01c10355a0320b00d001141c4607685800c200c0c03410422460800400c0301500e032000c0d2940c010700072100c201c4800d290560915503000d6020818280c3c1ca540180420361820346640182c0b02440441549200b200501246103002c43d6120083d6000322200119030410500f0f018052400540305425030b5410b81d5510f007001405250344c0c2c014801c00b241515651580c7c0390010b8982680007510384144643c0307030f95a841754914645286094610241c0500c0d0110520043c440768840150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 541638012 1250 541636762 541636783
    0x106020a080904021b0f240a0b360a020a02120c0a0c09020405040b1f05181c03090f06051c150b0405100305040b0705071a0a05040c06080702 62
    0x1d51950b0340e000400000c0082c0725040340711164070000800c0030400107021030b2910309600d440065540003010120403070108806c00d01e0589440c51540042003108140d944030840c07140000e403080102034855004d05074603141c0402000c01080068200f0200045000105a04512122415030038180c103140d0180d1501b161b51686000168040340d4001c8920f410000e48404540201603002c0d4a0b0b143d22860010f54424010329000d00d0419002d0020341c02c150880c08420313568050b44040e80b100b2290211840d42c4006109a2544107041320b0340340070b6a86c0030341911120802e480340c20f420612464040c1c907005140d88813400c4095103032010400c464004040724404d214843d066000e080c00c12642e40010b0070058464503481a00c0040840c2c41c8a1280003441565411030320a030041e049010100c0c141c070341c01c0b200103118076001c40c0450b0742a401070000d0404140708450700b0312901441440c0c69510a1300b2940c03906065255424842803007000c0300d031030f806424985482c4000e0718100307001950381c0034800c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 541639262 1250 541638012 541638023
    0x1b0102090420031f0902030702010c0807050a0206010311150c010515120a0209131506050f0a0605180a031416050f0d020907020c040c030f0b0919151a130b030106020a 73
    0xc054130210142140701c009002010000c64403401c00c120024001c008842c440c10102d0b2094010404060156090b41c0320b0420b994000e0600c0c1c1e007181d481540c800c900c00029074000c5090352000c4240d87e290b402a045603050f000c00001c2903d4070481559049040c400341034020360600b861140c4504000c14183c0c485501541c80910640350700c2c003e920b0140115402800340c1c10050240400403140303030804004c4680c21900139646d004681d04203d5006514410f140103e00104849001e080f141c01c903001d124100282221681a5242c407414840d4488081400107900155a4048401018480500a00720503119a012080030101083e107001c141c45020344260302c0e031000540c3c014400c110074036480e08003030014403540c022110041d024040c0e20b03440e000d01c0340c1040548811410f0898956100355035040318131401c00d004140010042c000202c442c808003ca500d4040b8244249047d4104a030121000300e41e40c60004901c20204006d55810030842e0b0441000100107140e0700242403d20103070441c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 541640512 1250 541639262 541639291
    0x12050616020a06140618011d0c0909010b041e050d0b1003200909010c080105280f1d07020607030e01060f0609060210020309120c01021b010209042003 66
    0x5002a45820403100b4000c0a0034205400c01c2c500e90400303031106000d03aa003a60010a414040e00c000c0d82c1d400002d015820364103421550f01918500312003540f6400c4005c035102c07241380c03400903404141b01d850709802c4a041d42c000010100440c0910b0b80354155002442c410f4100c13050300f028001156041e0300b000c094020b44100004c50080300d200c50450000790382c8954402d01c200d200704400d03030a152840740e034248605140c80002e01c0050301800b400c0703404100c646e04e800103682428100300405202ca000c081000000e66461140003943c690442d0181c4000040c1907111490a8100442070380e03400f114071340b0042c12109100c299070b000542180c1102e5103003808203c002c8102040e0b4010500d980c4102d50094100d940000c14079040502081038812a90030344040c100320030140400c0e44025119075015611982411640b002c20300090076418407201c00151504e15020744d0494005070f07407900c4401995001901c0c91040c500b038440c00800d0700e542141c40300c0c03800c040022040d0790f0000070500b40011071803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 541641762 1250 541640512 541640551
    0x213050601050d1d0d0c0c06050f25060e0a0b01090203060303090301090b04060e0601030f0320010e0c090a111206041e09021903120e03070b22120506 66
    0x7030030940350120f20f0300f01c003040340320b84048001d01caa01003c0c0d004400c60080c102c641281501ca0140440785503004014500000e01e440411103070b075800809144c50380301e800d00925800d030200c001c0002015141c40140081800d49080c1101110540400002c1f070754010400da100146012035107a044501c88030b40141c803030740e640003c2400e5204504001d98554039101038070040016894045d401180941001c0041004d440320070b941d501001e00000e003440801c0e10b46107000070b02c220310101d0420b43d40e01035044100900c842090070740b1560040d0000742c0c0c1296101c09491b052040040780d00caa40d141060005001c4038003004124403d1001030366000041e000015400e4455801400015610f0000d424042d500050700d04014800454128450b0007000c3d010002404814422400d07243c11204107080502100000d9a909601c1c44415416000d590000211100404041c03d08030302c0203056118113400d071400b01c0700300f0300b2590403e2a840808855080108030001403459100e1044100800340707010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 541643012 1250 541641762 541641767
    0x20118080c09040309180f0608030306030a0813030b0118240501030b03011121010b041a070201030b100210150b0a05031005130b01080f040818010c0503031e130213050601 75
    0x4160300700000200300321b09441c3c1d0b44101680410b00101c480d130010406143c13180d02103604c83c801178401603455445041c4410104816074000c00e03942c24039960503020b0690320b6a48000e0500240e00810240b200406a01040b100e00c0c010705513881a1003150151401e0b81d00c401c000c080b00f43d8016a070415544014402c81600c0c2588a039180810f9000c031540c40c2e41c021042080c024500c4580540b410004600001d081040070f4180c9040c0c0f1503900038003c00c40c011410055490308a604c0a038109601e880390036842d5203940d5071010041c81d865001d031401c210141ca50009403180c030300161180210741f0008101e01d1800006407559100d10f4604965292101c04a1101550068104c9544a10a075400c0b144a40c180e034801c0b10340c0c10b002e80350024655245c9481c69000c0c01c003290050003c060410a8110845041041015200d0141040e01100b08030707480d02d6241d0340040383e00f4542001f412102180303282c442054180d00c14a420114844049c0541c04500d02c0003060400302c00c0207844101007034985e030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 541644262 1250 541643012 541643027
    0x20d0917280201090e09070504090f171306180302011103131d070309020a05061303081c0e06010f0306020901110f0c010e040e0303060d05031b0703020118080c090403 73
    0x250070352104203040e0941014014400d8100120f0105100240010f0060b00c404203440c82503c490300903144a07494041484060649400d013201c030b6488030034950b0005124111541d0511954040b80b0f500c0300200601c225a038000d5030882018062180c5d601d04d80741150001c6503003a02d60a107407031804142485009031550141180360030b40480d01e4003001c07800d5480d4500440359030300f0410b035008554946000032b508843c02e81c04065000780760070009002070f0420000801c08204480e5800480c1c0d40d0f81e03240c45032507070071042c0c4040304684125480d0308007901c107019043d0751541c054040d280b1035150658202100c406440010f10700b41d0003007401c2415a004801c2101d4110b840f5080e186100302c06054940c450f00140c01c55070200740c03000412540760425201d4140c03607a0581d0011840c3d61200b0082110b00c0b125404216254801000302d0462454800008005104036900030718140782075200260141100200c1304c0e142c000c0108081180c08400120103180700000c2d01c40380201c2d00c4d5428119441d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 541645512 1250 541644262 541644283
    0x60f120703140118080304061a0105180f0d0c030b0c0313200a030311070b130303030203130c0e070206090102070804090b030f0105011d0901110a080c040f14040c020d0917 75
    0x461070342c1c4e440818081444000c5200b1841850104242c01001000e1003107082011a400c1c0040d609000307442d0340c85075104040b00e10040003016500c1124840b40061000090004119030500390303100c2c20001c00c1500380020b81c00040404c106811407800c0c0c5502004031810440c0503100740411007013148181054a012005040094010409652203007000761280003c0440d4083c43d1192060009074000d005d81520110a0103594040d100d5141d500e0440103504040e0070340d00003203c48a51b2070b001900c80d83d004c100800f1509041c011500c0c00c050064102400100030103c0760340104840703000500004210780c01c0d01c0302440300040203030480001c24507021030b0400c0d01d40e80c0d610300700000c180b00401c07030344811007000752851001e1947d6410a50300e09a610404940010440500c09052014090f9207020b40c0124814031290600daa00c8041440e6130000d0390000b1075500c10310300798000d14105401110b48012441c001000c560464001c0104404410322842d015004800305008202034180300d4208003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 541646762 1250 541645512 541645541
    0x201050a1209060228020d0f030c020f0106151106040b06040c03140a150f050d032d0306060909020702090103060b1521100605030a0203040606150305060f1207031401 73
    0x4030b40c000c1c0000248036050002d240d899002c0040510003080c03001071207c001e41681d960b03840a41d40381c1c1d14154050412608a00b0a600440000d02005c0300309104440007072078010200b0491020001e400340c10300002510391035042e04444100804210400c0015400034400e980000e9501d60014048009110025007034601342c0b03100c0103101e61000ca076040426040c4544031601440d40e50390030384440c52183c512416030082c0e800c2c85032401290241d90018000100103640b100c04240021100904506448071600465900c3d00103000700d0340c0c0310300d203074000d44503103801145803841c1500083c4900c030703052000522054840c511b801d0700343c84e48048a544105905400ea071144040008010010090f44c849117121181500061803400d24200b10401c0703404546407985103466074074105010750310041041d181c0c1074035074900003505210f10280704d1400d0584e03900000c0c141001010000007015441c41940300310a01c00b220029500041548000c90360300038866600b81c24650250350240041000700c0c40d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 541648012 1250 541646762 541646767
    0x60507021c0b10030b07030b01080402091e0f1f030305121005060c06061003050f040303091a0c09040e010c14160c06050307020f071a031305060a06051c0201050a12090602 75
    0x80d200000fa500c0400d90f44591240304c0556074012084044409060301c0da800140380b103005c50054145402030907001b4000c007c0403544101000c0344e00607819025501280d4481ca017000f000083e44c65132110302d6000280410400d0003d04d141c800078014041c00051102c240341090128000703030443d03a1130718000c0002800c19a184c2e1620301110303440e5101145c64500408a030030021086610a12030a4440d00b031550292a480e1200c0c3c50490040c8040f510840301480d11a44490842d41800b0710284100d85070480665207808000c188000e41e0585d0303100ca41983c0c1400342c04240300f60043e14504400c2c1500040036101d1703441c40c0104210455001d0090200c0b5994407003c0345169104009510400b010303000c035004400c0039a02c042c0c0e600147d219500c040c59614560000c007024100046402a03800c141148400d00251240c80c10008240d0310b10085950713820f0304001d181004041080110b60103105100030407030b56000601203208d8a44c0400403c901000d6003141e000361075100c1115240c00400464 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 541649262 1250 541648012 541648021
    0x50901080a0c080a0b16030b0315010305010b030625050f0d140117060a020a020a230c0d08040e04050f0d2115031b050301110301031209060507021c0b 66
    0x6072110200d040503124503181100103d25050001140d00ca511340c0a103404046503036a00d1140d03c6d224091807068100b43d1a108071f480030340d4003085000c010556414115666503d145886421070b01901c012a0003070b08440104a600d011500d00e072604840440140b40b068030100380100c1d4035101d01c543c3c450101c1400310303038a0500d1000c0d610003400911001d00a001603600c5e04515440c45d001010400141c1d401040020024401a0017a185c41c0059004075011504240c1d40d11412051400d1000d000200c800380314078002034200490040c0b144155090071304208c04d03840e1044644120701603c4818840a004282081010800184d92100420989001c600400c50046c003080b9041a044500030203030300f000d401007c1d03602c81d9610390380c550716044040741d00d140d84001c513000360094002c4901c9080c1d480084e00e91403c1c0109070b444513011112654030341c1146400c00c00c030f0019071010810071158103018041c154010003120005a012285140c16503401d02080c441ea200341c3c0c500400c0e04070f0384004d10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 541650512 1250 541649262 541649279
    0x40915020d0608031c0c0507080316090605090105030a1d0307080901031d0303060103090206191112030103020a140607120816030506030705090a090b0718140105070318050901 77
    0x1821940030204080c81520354843c0901d070b07a401880151042241088078000c01840780c0d031b1119204002c24181542006426220784010f90011180d400028080100d032026540d07001a80c113000c0c184d28245241403400c2200000c28600008280c1200c0030341e24001c5c96100380c0100030828907120f00c04102c03959040c6501d0000010b801104130745000c6030070401c0c00000142c1e055030003001d40001000035800c694954004401604a40a069810110801000301441110707440e000d003400040e19401c58003098498142d1904541401460726800240010300c01030b507401c10610125080c1c50660760608031000c00041f030310f10956400038551181035034011a23442c1c1041e032803846050304600b401c0c48074025500c198252030080751016410b0300068010b20242c86c00b1303a03c441e0004c018640001d2021a40d50b201c01140d00141d420802044c4021000000f0070a0910500040e1000450103c40034882800103407031801006402810b0010300d104200603130bd0300c080004000c0c070303000b4440d0303c0650707590030392 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 541651762 1250 541650512 541650517
    0xb060a09030f02130c051b070522061a0702030c04020705030301031202011103070e01170108120c19050a020a0b0f03010621050709081b0307060f111b0f101d04091502 73
    0x51403442a80c1f051350607102401250070004c640000d40404400c2d10a049140200240304280d24000d035a075030004070382c4040400b14a0400e404035141c6541da20f026004040c6402c03030f2800c0b040d10681c01002070754000781001c01030307a04682d0711034040c040c0c2103900fa00907070142885100c2c4050b210300101c02c21001e141c0c09030004001e01800e0b03c840d038090003041001090044240603164607640b040303000c0c1880d05040c0000300207104206040e1005d00d010110040000f0308408429515940030011140552400140200040051160461070500c0703d0022005501051066a0601071910744c0e1a5050340c4120700c00c06004403142c001c03c002c7c40c041501502110141c02140018492119241d8007480c581c0c82400801c0070080080603020300d013440444484108040c02000c010110794920f55102080001a608000003410b91000c412144240000a4002d072242c1d886035180459804240341c203c001c141100d400c21019506045100c00850b000e0000c5000041ca03480100254000d41c0034241d01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 541653012 1250 541651762 541651777
    0xc0d03300c030b18040b131514010b0c10020702130203180c062505010e0607050a0f0807080414010b03190c051f0c0c090e0a0201030b060a09030f02130c05 68
    0x141000724100308000c0c13100d0305a030042503401140400c0c02060204244d150501e5004440c111100030381240355a40d9010201281c1a9548103922000000000070030f128105000d401880504d03428018008140c1b81e8a01318814203003e8030340d0000f60031080d521640045001e2009801007135560b07041600728001d24070128492420b05003d440310052175480c1c58021210012140119800100c8038403c4140140340d134500100c4842d9660028034030040000c0c010180304402d540c44e1b1548940b040c1c48046c1c01c55031506294820400d9110410a840e42c2065202da081900320a200d807401c440c4040e0203004281c2510360b03640c184103450045500e4035440c0282400340d4403540d0f049061b039681e4010f004000f0400100d1f4031002980d00d00c41690103218403582144e02d030003002c50041c02c607a51a1101c0c115001564054040e400c4510304d04191f5816010b000f41100060790414600003030020001d10301c1c0410300008080801b01c62140c02595600300c210300c07a411303d0071810040100f4441c030140071a8050030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 541654262 1250 541653012 541653017
    0x1706150f0619030b09010506070b060d02030d09030c050a03081213050304080703020a1d060d030c06091a0907050f190b16050f0703020d03080601020f0f1e0c0d03300c 73
    0x61301000b050401d03a0300b2504850000d440181802c18540d100d0703541e41001003070325811000c841c0c00382005d07a508102001a03440c0940710f02d8030540c10b6040c9841759140c10f0304010f0013103c00e01c108200180c241011501e001c10740710f00e0819240c0b02d00350707a90040b985107503010b00540f0001ca00880c0b040c00108180049070310071140020441d54030010154441c4542c0d4215250350385000000702d182c10010000c90441d4483d02d0203a4000d03801d503071182c0c102d4001d84001e4a000710862001d42c2c050102e60308498001c10140005d1601d0381c64000016981d0b001110303298081c1210f461240d00000c0502250800f4058004216444044c803460380e21007480d41c0c0310140c6081c41105440b0295220201b10b007019a50040c040c0c103010300036510142ca08910240801d411071081040f010003091081c0540a035103041000644041401178040754030204080030a2400c2e82c00a140001c400e54032075600d0b0122681c50b003402034111050040034807030b50034689490481100113440d024980101c90707010702031102154 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 541655512 1250 541654262 541654271
    0xc17150a180609090b0c030612121206010309170c010204090212091c020606240a170a0e0a15020f03070e0411120402191508090105011706150f061903 66
    0x18809101a20041c810103814006170710045885086014011648000060121144403129100c410724002c948428003240660200311900e510804500c0c05400540918080c0a000816141c01c0d041d81e102c02030300381c1e0201c0b00040700703018440217406503401040d00030f004541740d040143e2801440041290b92542d140200b40702078042e0040d1010300300e1001c0c200d81c010f0040e035480000340440340c600d01030044400b50480000000b80c5d29050000d01c03c9540f680e40d081d00007001001071800060300901040d403e541001070720609118005022094203802101c20001680c089195600034030420038204450303000041007007c01604100380305611800ad440420800304c02617803035070b841c1c000e01100524402c500c101003005480e04012590003134500c120b0308d80200b59565280e610b0003400c03030103041c00700303c03051b0400080340000c3c8940342c0108088042021000c0013100e0003038541c90010200c0540351807038280c01310f00741c4540d03050903038002c0003424055031003030308409184241403014844000603050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 541656762 1250 541655512 541655519
    0xd05010e1e0613051501080a1106040614031807030f0c0e0609150a0801020a0e120c030307081305060417010c020a0203100f020d0515010801090c17150a1806 69
    0x180000c40d01c2070060014001e60f8489803000e01142c001803100b80ca451050743c1043e050301648420042c0202914401000450903038a024070001141d081030912400c014807003003000913000750443d0a03403a42128115a02c1d61a4151020038841440404205200d03400000c81044220002038450a000e900e0300340e44107680ba0a9240c80920417508290403055203404201e81c2d5070805801600184018110910759448042d15070032030b0006032a8500182030400044420f080a501146021582d00302505168045c00701090340c80c0300300780000f400c4490010742c08400f109245155005040e0081416546680d141203c02c1e00b910000014070b001e501e0444100c0a090001903003020150b405005400d052a00c10001c20003400302c044004009a001c0088143c0c0b40d010f4840d50b40f1070400710162604100c001400100b0400c1c0580200c40700c140783c0708900c100c2c07903000300e144a009603560346481095683d4184040b5255018101250469105e203800702d40b503510318003004914600c23680704101041d41c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 541658012 1250 541656762 541656793
    0x620030a0908060c070f1e050d02160602010e060c0922151712030c220603110708030424140414031608180307120606091a0405070e0d05010e 62
    0xd170560040c0191001041140016240303007000d1985440c05420900c6016141c507070358100700490b00c4d260010f810861004440c041c000600c000a800c841c4003c02c5038120710b00c65960703200400382c602c610241000c82d240c586955075035003110005990000d02c4118220072803c40d0302400700345000d020400e10015012a8114614420341c071854042d2004148091101c0c0485205600181c100b0301100d10420440344501c04021404070140848966406190300d080001011600b21982110403003d0811600001c039410f030301626042078011100070b090f03054410455036801002c1d880d24160b01d00300100030080403a08241a4841c074029043c00b88041040b01025407244a1512003007001d40400044602040300301002e0081481c0c0f00250200500351003002074508401640122040f15808000f02c0800000d4000c2e000107040300c1c84188011201e5044507080045842402070140766213000080015104905280000c180034000c8600789240381483d074040c022500c41c40d032261044005146107050b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 541659262 1250 541658012 541658017
    0x3031c050105090f0c160c0f030b0a1d060417070204090303050405010f020412030305060312030f0403140711041806050109090309050d020d0209090a05070609081b0303040620030a0908060c 83
    0x40098001d0b24041302449020302040c403009054409074460b1f0700c0411141c0302c60304628051740c0200001519071422503041c20075504500013403946c242c801c3c54002050b0500040306a0429441600e45801d84601111102035028000003c3d50050a14041da0305041c1c151f400b00380154007501c0240103501c40c0b070b02981d00b07a01c514424079a2070042c04d1540c0c004240309a100303682010006040e6a000f42b0b10200c450001c0c0c00688020501140703a1040c0020540c1140520f0034402e040100b050806049488800035581d0f0146201d0099899084000d04001400c6040b01150740c001001c00995844201e0354000b0041a90110041130310300601181502c2c2c041d003005c03007084d402003120300c02c048113500b401700d0200c1c017511031171840c401e110501c0700141042c48600080c1c060b039030300c1c0c207803051400c15280d1900e82141a403002d42c00044801da00c0f1620080116416203125040c021911118010544c009140d089025529400041101440d095200a218003100d00c0341007200e0700c54841842c0e080462 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 541660512 1250 541659262 541659271
    0x1a010f050406110102070b0703020a080a0902090a020c030c06040c06020d0207050a12020d050322120b1503030c0a1b0b130329090c1c05060f040203031c050105090f 72
    0x98010301080044620031240702e4007035200f000000d400c103ca80d42d5005103040b0300303454110100350082051001564070002140e8041810300003800790750059004286000c0c0b0180405001030780000390f0140c0710808204071050540c2c42c6044a0281c40e1904291b48004428041c01d030045c028100c40e80040782c80041d00c00241e071402491109101e185c5242c00d90441102002260403614000b546401303da002d2015100440340d00058800440c400110040c0356101c5800c20310803c1d006c00b0b03804c801f180502001d2580304c048003107591441c085000c002440c2d4021303440485110701c0341c2c8400c04204050281c2c100b480030040c05604660319210007440d4428056061800d0791380728400b8040002c6080541c0c80c0e4020644e0091070030840740c0140c2c50f60b0300c126040307945e402503510583c0e0140040c1800714a0f6401005ea88802c17410b00c0540303035100c544802c0081d11a1030702d026084049400e42d1380c140101c4450411010403240c12100d100e0016001e000244100d91155081c08000340500a1549205114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 541661762 1250 541660512 541660517
    0xc06030b031f0b130f0606030504052a030a06020c060a02070503160c0504051303110c06041e080708060a0c050703170403090504020c0a170901080412030f06091a010f 73
    0x7200c60204440c454242240c002d80582c50b1104081c541640756240d0700b03d90092800800305920511541100c240c81203030341703c2d50802d4508010040440d0700451340241146088084041c62004400040705411038800d40550600036071050200b0008158020030304080c0541c141c1e01203540710720704e0804034040d210001d005500100310b03040c2440e0f0151b41511120744600d4034809010b4441c030104045605c1200c81c4061040500c483d03109054112010780e6111b40024006c10300303d035403800403c005010350310485285014a03c0b52040c40382c0c0c01d0f2610000780400d013003190340031a501c03103070703550b941600b0358442801d54540805050124407a0301200ea500390181c88001c0a0754000719030609a041c000c0050b02000a02d61000c03d440e0355a000414111540c4401000400d07004e040c000c82200c2540700f460080501004040c125903000003480d544940c001d180f5a515038801502500a421250701d40d0270494030305440800c882480da4000032240c0031050b032854106505c40010740351620040c182601 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 541663012 1250 541661762 541661773
    0x91501090509040c051003020d0207060e010f06030822030f0b061507030c3023040e042a090606122a0207030807050721030f030b0d1407030c06030b03 66
    0x24506109a0130161306c007191400501c0c5c90007042c6400d0880e041200215102a102c800d0156031802c24021010b041801d01020804503103035036180a4070b031260902c103400040c0d09140c4030101c060141c1d8848003e43d0810103131360600600340303000c0c3c1d40c00300103d07021481202400d4803100710100c0207060b200100e626885422141c400e40d1100d140200300b0f07440005600c045450404044204034002d40800203d58884080080d0055610b0f16034010460401d030ac1c44800f0700c81008680b0121a445030070640081e020800c0214072011b803d81a03810601e03e40820300400c84c0004c0d226065445501290019070322807100f141e0309001ea1082e02c08041480c04040c03002c9100180360101e0b0400708101320303080d004a681c2942ea958448159400c140b409440c180c000c3ca801304901c40032100c1d410400c40140404442d55000e969000c0d017000c64405080f000c16a9034490680240c642c42517a1a0b41504222403d00d003e94104100d0307038503541408110f4240399502d40000b02c8074040d009440d03440c1c400401502 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 541664262 1250 541663012 541663019
    0x6060b0a2a12022b12090c030813050306070804050c010f111b0f0301180b0c0708040806190216020105090a03060c1e1d09040c05091501090509040c 65
    0x281e48050394060300200d040c1c110420000502c1c02030303419409411940103049050b40c1c2041c07408041d200e07100745041001059030290703c03240d400200403003640c0324850000780e9040380c3e04040709510442d403c0284540b5000444d02161018868000e040324021002c0310020f5803890780444e21100c0c10b03140240b4951000e03ca130704480d802004034400d600703003e03c0d241801d1450401044e02d4140c1c1d00c19600300118000401d500241001001505449801d030024010a4018103028070441c1c1c258101410080e042c802082c43c4020755811246100d8001d802107848985401c00d00782c441205440851250000035204503662601e0300980d0841408000c01c44084170240d00103407519401000d0845e4080c2024101000286140c071030106203140603a01c45c1c0606140701c2c401c402072110703101c0e09000d01c84080c400a01043d8044000307c85c0d404196041c4010b5200c5240c80d100400c8036800a55001c80d4507420810300005241100f40c1c600401d036074204101e95954141b100415041c4c4000d0408030301d80f402403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 541665512 1250 541664262 541664297
    0x3130e06030a020f0d02010201111c060f050303030f09070f0b0306090f370e01150914010b180301050c0d0f020c0d03020f16240b030c010f020102041a030406060b0a 72
    0x21700c441401030001081000110385c4408440e0300240301c0c1c2c81040782c00c0c141210400f1191240e20081c041484480c0c08160503c4002503903800004c06164000c0c022200164081d4401c1c03100380700600c4219201e030726261300c0b8141521a5002102c0140c010101c100020354401c00824103c2d0081e004062a210041004101140d08090f010485090f01084810040324818540305510115404000004550201d8174048a8440340b40e41300b551030350300700060600300c0c000107001e0604503203000541a54a848102d01036021100796150164154070780070400254000c03210051003043c3d00c0d25401c200f0075030031001ea43c0480c05100c0000307189034000480f6008090082e4014120f69034100710541c00c0c0804140c0a013414030310034404480d2100280348540c0d40500d00e0440c3c0e80501440740040c40003004c14000300e6919400e25032064100501c0c2030040c0d0005000f941110003502c2080d583c05210045002c0102c00c07a84244d8081311981d142044c00078089016006403900c0000c103540d12000c408103041c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 541666762 1250 541665512 541665529
    0x50d1703041b0608040b4212010905061602060127050702060109060506040b030c070206040b0a03090201021e0a02012d020a0515040f03080604060e011203021e0c040e01060803130e06030a020f 84
    0x1200304800c000d070003071088d54449200210074110180080b51038403491500c181031030000741ca0b003048075403042102c80c82c01b500410500d056490400507140600340e0f41801d4041d80c60700d8981d040b2000c2c54001402001a40891401d050314034404c01840760300c0d1742d0070500105201340d10031491400c0c070a20101d0340d500320840080154600003041c240c202a150300611000e6401005805c0101b03955150302c80031540c0521460380781c284001d420044c450030900d011a1a80780c0e20724009c1c10003112402d421401b0300c225440b0101c2001c1c1403840078403050785040c0699250f4078164207503650b201d0140d200c0000d02010060f2441280d00891074100c002c01c641d019a20102c000c1c22280d0700c503407640000300f400c0c103142d14094028415541e161100c1034031814040d080ca0360164243c01c039200d034104284001c460020b8203854400c001d4500003810701c80743c20154014041d0341c000e003910b4080054500203025034070305540240c84560b0110746a43e01d401003050741e1441e00c0b58000350840f510506200440c0f80088030b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 541668012 1250 541666762 541666861
    0x20d0e03100204080709050105040506060a030c02252420030c0d0c02010e120d0c03110f16080c09070c0602070b0708010f050d1703041b0608040b 64
    0x449404841e500d021009036003040d00a042568004101080042c0c2503002d024014a4141c2c2e00300001e003000004180d0034462400b04805142d19140c0344d40d0310b40d108200440c4036804155422040410f5200040e03200078482c4551180e1b1005a084100003c0e5101c1d48038980b584180c442d060f01101c007150401d9520360800304410a8001440300500c481e8090042c4481c00079155242c0e801c1031554400501500510200240500783c184120085800c0000780810004c0240c1031070074a6161619044440c18582c10ba040500e004072091100100c1d00083e840244004007126210543d1302c40302a00e070784418405030315511001e0380000c52700080c0504290607009002c0e640141c601102c68030b80c41c401c0002a503402d00001e400074010080e08680c440403402424040320308940400203070702c2daa14010b40700105002903c40000c0444c0c104281017010701c14030001c0c6a841c3d628141d0f00c0714003070300fa08821101076a01080d01c03400a51080c6070300403800481006050580324407031211005502159a200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 541669262 1250 541668012 541668019
    0xa1e0905092103060108160e130216060f23060910080115060f090803040b0903150a020c0c04090b0a0c03201903020a090b0c0c0405040807030816020d0e 67
    0x62034454a500b403909140c1c00d800d911607256070b90401c14001021001c000708070303090503003c1003842940d081c0d2114081c0c1e9001d108550005800b0880309040c8000d1190783c2d0303d000c0000440b010442003107040d8000d04a01c200303005041000c0c1021480242d00400d030400326402c055003800000c4c0c41446c00300210354006808a500f008003980b81e214040c01c644241d0f40105400c0308041c5d00300070503030303020b04640039200e20391802055681c80c01500503a280158002c01c03c01d5000411444000c0d00e04101207c070b04556019110340e10f00b480c070b01d00070095008035104040c5003e1041200d282d4106402081c500903803101482c0c3d041d507694100180244100511402056112031341c00000c1000d40640303400703001d8541c5c102941c4d1020307240f001c07070141200b50b207440074103006222021901d03410203501800c454071030307094599400580c02d007a8141000c086050782e00c5883c1c0030500080c402410040c100840c403d440307585050705e812070a00301e8240d00c40f542c00c0c0140d02c060001000f8500c55207e01420100c0a03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 541670512 1250 541669262 541669273
    0x6060313030e0a03031808281a0c030109060806070c0b0601121a03010f140403211104090f050103111e10081e06030c060702030307200a1e090509 64
    0x100006083c110294001d400041003107620070030100ca901e038038400030080c44004203039400185100d60303e0003a00942146011355481400d000703200ca54402c03061924500043e02d00d4628101b01500d405800038014141e00900d400f07008210001c00150641c000c680c90745440c5030301c800075a907401500100410440c100321381100400d070031500b60f002d2429810f01548800d0368455613803050500710342c4101d0b60b400c101d6040c4075603c40300e005556138150b0450b0301481e12400220340d400388030101c503109c01c0320740785400d141c8090303104101e410304040d20948001003c103110743d005442c4810300381c54081c04041c000b0031000841010501d801000600e03440711400c0304000c4255120000b402c0010480c040c10040b0f86440108040001410014204d041c0003240107459410701001003036a0314011300007540203490010382030b425540d0030170030740700e4495200c0711a10140302d808030282040c61840d030b292170146413181000324032000500c0c0c54003c64060402c0b018041e5240c81081c0015001c05440f03106640500c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 541671762 1250 541670512 541670537
    0x309090c111c030f020301140d1407080a110f090105011209140a120206040b0402040f06050603040c0504050a14130c0512010e0c0109060c0605060103180c05040c05030606031303 78
    0xa020402c00c00c504070b070145140a402c00320180603107a56028052089104200510890128540e82c0c000480c0603101e036100c1b00d004c1c0c50000c0c0420031101820f0728a01c66100001141200060f071180b2882c450000403a04050100600c044086020445a400100d4800600803544100303101004407800d107a020130748006c1034803040c02154035080010300035084480d070202802091415000c034508180700a28403407401da2100f8405e0307030f0042c00091003951900c2c8094400713042c070342100d07001d00001800b07141d032800c0ca45010301c1c140250b0b12940e40110705210005000580030302c60b00950004004000009655000000142c07020f001001c580c1c0d0201104080b075140c50f402443d000001c201000002c03290300c1244e449213003802d0244802d04101ca400402c2c408584d201400142207079019a01061b280c80799030050b0058110540d0410000046104c0c410510032010703030110840e04203603010804203032080002c80d12444201c0b4490b4110400f0400300d05a55022124601c04502900d03140003503c54 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 541673012 1250 541671762 541671797
    0x20618010204050a030b060f060f03040623090d1101060f090e0111040f030506010504020a0509010e0d1202031b06011d0702100203040b070e0f090112170f1e070309090c 74
    0x1540c0081e1800f03083d1b00b04012031400c0005c40c4000303140c022a640c42c2041850300001455100041000300816200c0a07103490412003840b800b28400110742440c0c01e54685074404617550750120b0f000b40000b8000081d142d0380c68106200b604e081c6c45540311154052070511042002a102d0307101407448542d030710395244400e645440080d0010704070685621020500e18200b0320f183c0301060b0041403080d84100b1003507452076009012203030010002e0074000b640190910001d40200140500071b00b41e05414130f41308d0b01c0785e58003100506038200400580c2c0400403c080c00565250024003541c0103ca0711101048441411b0b0000150310060030720456040109840d016810b90700140c1d0200c031080d1141b000d1000141c0c04c40618072445000351106041e003c491400201c00b548180302d86066010500720300380a1105200c070f141c4583c4998080e4696030b03400351303203010000d51010010140c1406800b516200040c00d01e0100c0d180c15070180c0e1b8400025051006020007094840c44900610800c886001e52101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 541674262 1250 541673012 541673029
    0x5060f0f0c090105071a01051005030705120414060f22050a020103270812011e091a1f081f090b041e0501050102190c0909143a02061801020405 63
    0x1c6d5221a9100700c0d4509020700c0f041d059103134030103c00d00000b4010030071901e074460261b8031943c01d041c03200141601e0710304100000c0206c040c46841c681c0102002c00c1091203c0c0c5000b9809078481c09402004429160362050071881440310041c03041c0c214000c0d000166201741c001c80f200c108804c03041089180c0c441c00c080c03651a030050301101d01c030901158120142008103000d03070040c02c01c2d5580b82011509403d0300135210365607008040c1130f95500d20708030328025242e140e451130020002e4000c0d83d01000301c66519078207007282140240000d00c8000001c035180681c5010710880e004004030f11014a00709080c8001400341101c140b9085075440610707201c0754a101e9030071154004010000511541400002400c114011001040258041c000640043c1c2452006c404590030680c000608186524007500c5020b5105410f140d41e10a500d400190700e003201c000100081c25868441c4991030403427800c20780094111010740003580021000940f80e0200c038502c0c0084500d42e4000510300f944a8000400c0364 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 541675512 1250 541674262 541674293
    0x3040e1605120f0601030c1e0c03020304050613050310060b0f07020f0d0609060b01022e0917030906132a0b1902010f020c12070c0f060c05060f0f0c09010507 69
    0x40004901380999542c2511a1403c0d556041c0381200038550700c6042c2e054120207501c1c4600800183e4048002814403d000f80e4020b0b20000b440a42c1c2d5401000c19010010035500810b0300c64059800d43c0e668030360b51880344104075506690b08d0b41c00e1000f2a2a180969044a80300b41d030401c44102e0f20100c2980c44080042c8282d1062000140c003090f9030401200301c80079000c500d4103660010340d030b0b51800d07400e101c0d0119154510100710207500200140c00000b0713183d500801445440480800110540f14501a520404002045643e00d66452000e007440a002680c007810383d42120700380302005001102c800d20389180313400348104540d640c0d000a0600d0b61045038001903480500c900380c01031503428020b1980c8848141ca003982082541001c154450100e1189845140707800200d90040208126915000300090441505101d030341d401c014040820400003214580a4400007407080400001c4090040c001045030090558074039074404142e5015401c2c42e8103220f014070018001600403001454078 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 541676762 1250 541675512 541675531
    0x6150c0a060906050a0b0604050411090a0801021207020d09050927010b01170c0301150c0602070602180d150b0d05031827070c03030b030a0b041403040e160512 70
    0x100b442c01c00c0d5003140c0c40680800d01d040d051a804000359940c03041a103054a80841d00021382c070780a00402006840b0318404243c101052140005500e401940038004820000c001a1126174880381c0403602c4040708068040440e507229000c0c8141c0c1071155080da40216101d01d041c10490b40301501405103c2806040c45040c0e45a40103101d42d540d0119010b10405000c0c1650321135410303c03181a1600340014003455030980c440b692000d40c070510440c2d502143d1504000c0442d6501c3d501d080c510041d6100070181082e404004012981d14180049400c40075600407007095420001100c850014012a180c0c950b070100c00d641c00d000102e0001e0000b801d080402d03240300491100090284485642204a00d24030b00d007054492000009620740816484074081c501801100554507041d4004c1403940c59943e05441020665000c0004808a8501540c002c201d4900051103002c56255288614002c00c0303510000d080200d500445008225245260981041420404050140c08080004a0b400c440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 541678012 1250 541676762 541676771
    0x70e192c01180609330501021b030114010303020604030221070210140d020409060806091917071a0907050d080702150304051f090c0b09040617070f080a050606150c0a06 74
    0x3081d44c00c10b203200b00c1c254405031405035010b1511002275112030900c400c4503842e03c403500080e4410340c6c0079400b0340070b4804408000d5016507181d0170025901c06049404401512802000103840303c08118411807644824004031314112440d401d00460401c2804a4414010a8441a04c0e40040c01c03001d003084460020b40103031076904e82920341c016166281c0c428600368000d1010300124620105840c3c0c0d00380b0007080060030440300ca1a0440102c0c85a40070803844000219840c02042071041700d090501c406500300f520341e13848000c07541e5110000c0740300f501d03071208507003c0000004021401804035207000800b0070b89545c2c482c515510725640212412aa80c0c0c01c481711107070031505442c0c903059583c1080202001900d01640c3c03801e01d26100e901480326101404140000c0ca9619030708080041c14141050100e00d4100030425543c030481e034021518903607204640840e10b0f11002810a080756000001455030392a45000d02c0799401c4207141c80480d098080084e501602420041900707803510a038400a03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 541679262 1250 541678012 541678061
    0x1d1f090806090d390f0b0c30180109080a02060115030501050f0906030c0a080606010e010c150e030409020307050307080603160e070e192c01180609 65
    0x20800040e101d00e4403ea903c00c0400d81e005549500c1c04c2c01010700b440c034032441600120f81801750480340030b0f060082032100041d0401004002e170700050100143e030034452100c00e40d1a011041c0d5506000101c84035507541c4400001c40001031040007140400c80e94000042c1010720761924101980f0003d100c0000da800341004128001e244034803180a089146010051035045c10005002a10040e0059204030800c01c0443c0e020750307007400928101d41e0000c1c080c0c04c14566492500d602d8a01c200c5401c1d011070143e030300e1404154001c8445a182603844503400c002400d403a003e001c0101035440000c040d80c40240301c003103009052071000394050340300361700c3e1191a0320b03110348010b011040c0200954000d4100380002d11402003142c180205403281c0c3c1e141420301e80d45241c0f0840e80d0100e16080154008031408551114551500b10714080d64034600c05c0004003410980c00d41d0364034841e035040e04443c5120360010400d41110505991146940c0e8071f000c102c1c1ca81e111001000e803012270024985a01d01d03d60b202 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 541680512 1250 541679262 541679267
    0x3010f0b0a020705040504110d061a0103090305160c0f0603060f1430030d0204170114012c070206101502030d0f14090d1d1f090806090d 60
    0x80090114890107071414200010003500d0308610b02c03c080c051500c800c00b040811929210000042c3e002078004061032a85080c100c001e07045403040004040e03002d0106411035442030180c010241e030181c444e68a0724402d0161840c034002d0309441a0390003400b2400205a4114022605c0001c2c440d0b9030780422020b04007103d000c0819401c1d44040c4144500e900340d44070685403031028040380f0000540c0207442c11483c916000f0303600300b254410402400001540c0c80058101e90242050301c4401c1b628641c1d4800740640b05013260b4481d0302c040c1031004401d00420800c14011540040710f180c5c40d08204102d0038040c142900750300150b40c0070000d42c104004105038035240243e01802403090f40110426000030f100041c4d26407061000149050b921500703103044056036504090300101218441e51800e140c203024060301d843c400742a410018143c40003403140c85c0c00113006080c1c400340042601140402c0c0e2000d250540301102442c3c414405640030011b9030003418421184290741c5c1b0782c098a00c3e2110304400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 541681762 1250 541680512 541680539
    0x60f0504031b0b1908090c0d08091906050a020c040501081221070306141005180604050a0b070c08070305030f071104060303110d1d011b060606050d060b070218060a0810020301 77
    0x24030340b551f4880d161145455884081da00541504040d00603036a1946102052010442548400340080c84010015019074407100500b034900e4503600380c4254200c041c04100940302c0a1107075110541c4090300e00032108244000134110600030903c41d01d09070304503400c014441c1300221960404660340341810403d018014a807000710000445104062a4a44c0d50203041c6000d2002c810820129040049080d501c4d0ba4080b10f0160034010141c0e442541d4498580a10f58801841142c04000c0180001280c000c0020301500380c80d8002c026500b484c0f2007004081460700a141d0996542c9092800144681ca803807151002960090390383e48002402c044029250126640d40324040005000d180c0c0410031034884840d138950024078000c01850b18800d440b50103c00548401750602d45443d000240030340d0444003d003400208030b401480001d9807a00300380d009010f00302c0065040000340341e08004180255880039030080c8000e2a05a1507034442c103440389070404103050241035035030000061008442c071300134 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 541683012 1250 541681762 541681771
    0x5091f050403090608060d0503032a180f04020405041e0e0307170304030903080c0604050c120d0806030708010906021c0c02070b0d14090313060f0504031b0b1908 71
    0x180081d05066030300521404041c41307420300700603041000c101c15a4500c0b80d4804540d411404030790712400c2c140c08905140401c1112440c0e4210901c620303102010020003521501180b48a500d01c03202c0a000c144601400d03400989503100d5802c01000c5050f035554400ca8064041c00c0109000403000c007907000086450400189800703500034842d00b000215620f0150300e14909000c8003070340783d40340d030302d820794654002d9040100244004681c82c0e03004000010103a205038001c00c11103014144000507c201c08441480c00c1c1055007150030001145070013101b92a8006d0400780c120384040360b945040c1e0b400c452100c04101d803441c0e0001503082407422503444e5081074122081e01040f004143d200d01032b6844150b0302c01c04031070480108030182034001550004440303d981009001181c9004848603480354401d03c6074201d0005400c1000c20743d079116015001c0762492948503607241034115203a400b044600840204085d1016500c040750100201001d804082c40c0d2402c0b4541e602500794000d003400c01c0c001c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 541684262 1250 541683012 541683073
    0xf0a050c0403030e12071205060a02030f0705031f0801061a0408071205190f02040f0608030d15081e0d1412090f2a01030e0a240509 58
    0x60a00950030049001c44003120340c1428442800400c40012071008000304c0300b00b0249004140000a214450603815a500b0307101d40155940c81e601c076a00b400c102d0000343caa04810011120000d0541c501940045400c408031070224040c02c00d0004a9070260200d6400400c2c090751211001c0003a52828014a407581d200c400c0003a05190410905c281d41e41c00342d01c00e0340d10f46207441503040d0034444280405404940141c05544d2804a0342c10000e849446009040303004038544200318010340c6a51082c3c8080d00d1407900a103140000c1a07143e64041c1113140700250360180141c000050b0704804101c00b44214014405142001031400700305400d00300c00d07801d0581480003810800e90007052010841e40d07081c0d4034a80c110f005480b1200c5e0540740910341420001039100302c501007801500824960341c845c00e02418200c3d0b1250a210044090780c141c0441000b082c2d10180441c4000fa1000000c041d60024402c204ca03002c09410031321009950050b990307400e00382c0001000f401e0106850502d0010244030300d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 541685512 1250 541684262 541684271
    0x406090f113f0c180d0c03030f11030310050a0b0309100207060608030d0509100c08040803070e0604060c061b27080a15060f0e0106080a02210f0a 64
    0x1100326003921404103102100d00050181208005120100b41c4408903014229000092078010410701d16a408450981da01101144d0100c4c1e1518059603006141c0740e00c07906548400d4616a0150340c02018599404103112420010410b403002c100050b5200d030310500b101d0105070345000f05000d0380100340d80020182c204104100f01d0440c00002c2c55810b025529040169101082d04005004200c241c000c01c105020004e01e601d40c2c041640c00c8507001c3c0305078406903151003a4081100c8115401c625103807000c154a180000d0200d0110006554449030301c2c1040c5c42d5100300400000c1865026800802c0440d0f41d010700740381403000d1445045680e40303030003060590203000414050045100407a840c540c80303110004010030b404800007250700800320b1000711203011180d4645804004005001502601e18052001405401c5c030310940044aa618046d4812030f400c0030030485801340000c21906000380c080101c00103415800c039440070b00e05901d0800981d41e080c81c0304a0303c1c40c840b001c0e0007540a181807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 541686762 1250 541685512 541685527
    0x90b010b070327030b092103100b070c03050109050a03080f01060504050f150a030204030614010b0f0a03110a0c061401030215070510090b0103031403090303150f0406090f11 76
    0x11035038003a0308900e80f4400f456100752010700200320080d8000821891800d401c0c003207500ba0005030160141d40d42c21641d40d02083d2810301d15440d00046a6041141407441c3c0c0400403400312800518001c0c0c0500e40c00c045040d220348802c1c1c203544803900211915404207070020103041d44106195048034008c08281041d5241c100014107a0144d070090350711405a80204542c2503903041c0304410b88a6a2000c1c0c5a102c0007402c1010300203400a1005443c0c041c148182140e050b20b100b01114180d45982800b03d0500d0010041c1c41000c0c0c0103c0042418141e90b6404411004a1600a004108031320741d240048100107141803000c0c1d412a07006132003122011401400184d5a510034060000c0d4141c042a880d0310142c2026451322a04c40304042c40203140031845018042d2200c50981a02d0098a5241c03000441150100da40d01c0101d80c02d03512600300780b001c680040c100e145081c48110303000f000b036030301d031200a000101100c0c0242e0000402e10740d1030700000d61900c103a0081d40c10045071800700c0d6040c80300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 541688012 1250 541686762 541686767
    0x9021c03050304380604090b01080d020c03150708061512061002160501032304080c0d05040b07080306041b030902030606030a0b3601050403020c0d120809030c010f090b010b0703 78
    0x80904013100c00c1000d000030585d48440e030102d0000c0c6e0300840701e2402135035a60900354451603040c070703104018064001e070781c1040d0800140442148030101c0c10765015036500002155908006024181d20017441c2a6103400c065120f000b82c0100c082031410308940341011410401080d08484410080d5080700606010490300201100d0072280c01b800c001c0382e0f00201071031043c5032a04a0864000c24180801071000340880302005d41448011441281c120030070340c0701c051718240200c2c400c10050010400c511000506034401450304804003810101354603440c280c041d60080d219518600000350b0301c403062800c0d46420019590081401d80c05084204501c0e140c02128a01c020030040201402c1c06428030040307400314a550f51101401c0b820103010714000d850758080d10080c4c40a030010300c54035010188503e003105a182c00c155015802e140304201405055410940040440703007540010b00c08600f03210002e0042040300c0301a10360000368900d05103401500000d0603040800b40da4028070001d8000794 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 541689262 1250 541688012 541688093
    0xf09060e0103081902071e0306050a0e07090b0301290405060603060310091e0302070611010501120b130803010906081c0504171f0f050a15050409021c03050304 70
    0x4200000e04021064904d40582c903120196100f24580146810620b002d0320401c0b0300c00f4280c912948040c001c0b610b49540c024182d548544261070f00350042d900401a00700a0350281c0580702c1c0c00343c00800d4030540d0a400214070a00410303030741e05500034188112403600c0d0510500c2d50000e402c5881070b040d410884007213641d40040c20030052800742d4412680f0288003548120a001c00c4034213801c07c00c0082d80703180007900c82c4611300c58070020458a0151030819941801410706903104000e0803c0b010340941c8908640070405000a40d0902c441e50f03012010a1044e0011406842c000001154051800504030301c0e10269603d445014000d103046d445905600500700e1303080340c4048034104510500d4816150070175900c03a200d9450450301d41c484402e2604160030008030b000c1c18800c2002035588541c8520152036164100040ca544203510901051510b603200000d071900141070f0608050800400e000c1184042d07034250040346012003008100720101c1c0303419000048115490051240541640b910700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 541690512 1250 541689262 541689277
    0x100f080601180b0a020102070b1302090a05071205100503120f090f31060e130b13050f0307020406060903080f030a0f0212070e10022107020306010f09060e010308 71
    0x8080d81c54001106040010442c0142c40030b4001c03140c0d100c114540290003988002c000315403a403e400001242d450b88541e2444800350040c1c28020320b5035030580a2030003031500421560902c445121384980b071100e03900c2064410b400e13403803100c2011414401003600d0410248260200980700300301980141d0150f0055540c81e21050750b0802084c0d030940001402c0b81c00030710501e8040c00e0041c0e944a0400b228600f5981240382c901c81c1040025224520610605021228100100341c884031000008214003240341e84510701031010b41c14401207a0b6070174144088119445d00700e0340003007503400c00d5103010700c01d55009050364144550210b256a990395040d004452142e49400004800101c003088580c06c02e88507081020320865a81c6015441080340c843c0544038040003480080d0080d0481c1400000505041c2454009060460105607408669001120035400c1c15105000890058900704055406400d41d451040489814544ca5034101ca03c643d101d04480400d4100400214802c0d40864084 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 541691762 1250 541690512 541690517
    0x130b180f010c201507080103020f01050306030a0212010e0f2503120302030604150b070309060f020a0b0c130f080c04020703050901121b090e1003021005030a0603061802100f080601 79
    0x101000d03940f03c075003015200000300e44540c00b860304204140f5400312406059900c01c50b40d406114205400441d0719020456a19801d98080c0d010403000d03181014070341c00307040720380c00000c198080507554035401d01c01c00403512503590380409121982409101c41152660b100e03031070400d28a81c550b0f2542c200071081ca080386410f00d54000007145d11915640c006141202d6500703980c021076070f621044004e0580c0680d80a40000b4000100410f145105584200740448940e000300709503801c030348484070300d80e00142860b00049001c0000b289026240d4280200074540300c44100c003650700c0d101240b07083c200300e001175038851032040202e4070020780c2100c00d540640c0400c2c40c01d80444d458451101004010080150b81c1c561441d40402074425848a40c3c9800ea400c2d0341682e054a49502499a0100c0114000250b0000203444a03103250b81c03113403000d0340e8800119003003c10a95680e0310b81100716919110300d100140c820042107025800d0202110a8160840c48d14a0b407111108000900c1c503080505070a04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 541693012 1250 541691762 541691807
    0x319050d0507031b080a08090d080604180b0a02030403021605030a0b06040b150a03150503030901050901020a12030b100f09140301140f01050f030303040515130b180f010c 75
    0x140b501c10351002d1300d1200803020082411849007030984003038109030816000076010304002a49a00c0104800321403c81c11340350058a911001c0400002e40365074000401d05101800410011410f50140640505e0720500e00503034904040c200241461000c04c2100310300ca00072038040003d601d0010300c40c60310301c0d081000c0c4412512103c0008028292890364994084130040d604141550030b407004210000b5151020000d1040304191f42100795801e100e001d9140d00f05001250255004800400903c0ca0500c1a5030281e6250f40d608003031032848090010010b81d80318603419003814510100102c00c1c1c118242910094295000104034040d94029201000ca10300840c42c001d84094201d58162511141268454075005240e114966400d1041c58071514041074104803d0601008690160350028007801402c40e0080c0c545000b10f0740039200f00360300c0c411003420101044224441c5402064600003044942d4005900f59241004403400c2031050f92404c3d440c1c00b403142c1c12504c2030300340950550600c071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 541694262 1250 541693012 541693027
    0x3020616170907180e030d0203090109080c010e0d0e030c010c02031c12050c0903250302040f1a030133080706080901110405131805030c0c0319050d05 66
    0x124111546000710021101c4001800201d540104524094038800c1c248101d0841940a508060364054802c2c000c05400070400c0c03100c0c101494004591111540d000031030070980c1a030355484182d1040303001d0207081e550b80c0d48048010780c050000340341c1c10000d4502070719072002000001c0e07115003004070b80e141071114110000007117403001d100024030480c00240c502034030a441e070300151020080f00d0416418a1600000078120380d6040140c405c11400a402010b45802c1207049100040800c0380d450740580c507010340000144e5840c02440c3e00803042007804601c0c02030012070b0074040b0251100c5181301c1e9050060300c1481d88200e02c0a41020707101040404003912282140090301e04668000c01c506010382c000c007050081c1c018250750700400340c0c000200130407955081001460300440c0251540142814454480d00d0800d8000b40d0403030449054403000c1300d0803540c030701e8955400612400c92503086a03103003500502d814003040300b2603803408416003884d85099459036144c0304420049030501c0b002080c0d44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 541695512 1250 541694262 541694267
    0x60309010605030303131a1006082a1207080610050921011401080106030b0c07060b0d15061a0703031113081f02090a060e030a020d1b0503030703020616 67
    0x80c00420028060b00c4c4d036400c0c03058000d2074441c2c40810555048547c0300301c0700c1d24050540d5000e80b080d150303c10f80421040c20044102e94501d800340841e00342e03d904074100c08400e402c2206034100c950052071129a10011700b40e049800303c5000744050148001d10042102c0d0303488503560070003102690710348a91307104000400100d007e41034604489088505442242405505620810740b00f81c0d0588181d2190b030380d59004900f41c031842c2c0001400d035429800400d11206c00c41d8041c24480e403040d80040764440c041404120801013501d001d1740c20090035031161140d502035200f03140c00b0b840765910708000d40505c500e41c180b00344200600101015900c80e41c0d0006001540190b510011507000114201070f502e00802d9601d00f60700e006100c280384080f10300c1202c01000d10848500101c09403080508502c0d00200b600c8a0b40144100394250041403003110040c0d07260900e0300c0b2503910662691039030300d44980d0144a4203030150400c0d4040c2d801000002d001c20b40004103507611030b45c514004940c40744d004004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 541696762 1250 541695512 541695521
    0x1e0504030c0b0403050f030a05180d02031b3d051b01020a1e0f0804170d06030c05030703150203090709060605091002160923010f1401020a0201080606030901 69
    0x1501c81000100301190510b0482d00900c2128001c01c1150704401701000443d40b6449070881c40c002180c010080080310140480d01500f8420f40208401050308041e00404d003016107507481d8142e2451944240012031a016503481000840110b0040f403482e0501842e407500000780e482d048031403102c01c0260704150b2040302142d00c1da50200381c0300c1400e9100600c1c81130117134000f00120000f10b04600000092101c200c0820495510300b80d0f41c5a540700c4c1c0340c49003642c0d2608042d000750b0b080000b180040c041d00c42c030702d0b0052400b01400440040ca841c654100121001083d8000c148241c20440381000440c0d107829104440100071880140c0c2d03900d0320034010703203402295031010803ca03040040004a90b0b801001800e920740c025200c0d00e0b442c43e41400100d0702d40c02d07004054455143c201d441403140030201e6001c09025954a00355140c0d110303100352603165005d4264407544402c4600340b024452400760b5203c44581e0700c0300780020550070714140d00203004514003c14a5008050200019840d035009401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 541698012 1250 541696762 541696769
    0x702041d0a110307090c0507051902220e0115050901090903051c090507030624030b010b0a020a060912020d05030f04081c0519140402030a020402090a0b030907031401050402011e0504 80
    0x4002e00702d441c06c00030302550020001900e29000e04240400840c4140007046000c95000741903211800070400c00e0701101d00211064034861ba5a001c0048248109103e4114000175070205800900d28040810242d032005030880106141400560340000750400c065070310a05404422802c004600545040140340c12000a0034a100b0b0810000611049a003c090180c0c450030071200084e8000c0c0d0359800c0c07150107201c024034451b00e100040103291240d1025000b807080c0b07803059a100301d9050b16800c0542d01c4448064071030000040440b0050b5404100708440d0351100d04003d411803404190030301f04d40400500243c402000000c032039460b44403c84000403d1a0200c104200070b0030520060003902c45204200c07201c01c0d1170a145d640f010448900000e200c5d5500400401d0542656030a0001035000510399a8001441800c007050406414000c1c601c580c25040040c1042440c5003004503034105200c0010b1410391602040c8000350342d2002c14860f000e40f9146525078a4004140d0480d4140304135031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 541699262 1250 541698012 541698029
    0xf07120507080a080105010306091b030c17160215071b060204081b0a050604050a0302040b060c0f10140103080d0903180303021b190e090c1002030702041d0a110307 72
    0x1903c02056420185140c140d800a9a04110340b54544500c041100c0c400802d07510f0300c40f008404048154825000750300070f07020754508890300c0340001c0062030382d032f031015101200104c0400000a42d03107541000391100c041c982d04e0700100d01e410055006044901c5c881c0000d070b900c1c00086140300620140c0d404036001004280b01f240c2c006014a5007280307058030200d010520503501280c0029403850804103031020b681000380328820f4540b0b90b0703003040024029500d1051700220144540350340d000302444280076207004c40d00602001c4050303603031140c104c4005003100c401c0911014014030106543d50107507540d034901942c00059660710340c00c0c207880c901150b500c480c0e0304110301000801050380c08568078601a000c00c1c0c9044400a01c007040042009010b04401b09202d02c4d088200004070140d201950403503005000e032035901440002050254807884100c0015900c001101030450409102e8402103101c3d0056495200702c003480030585807a4143d0001d0004640e819032002c00e0356052060800810500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 541700512 1250 541699262 541699267
    0xc02130e0c0303040b04050904060f090b07170103030c020402090102010b03061e010e070203031b0d020d020c0d02060103050303061e1305010609060302090a030b041e0501150b0f0712050708 83
    0x18144501a040505030101640105400e14000d41000400e43c1d0a03245000e2285007010300382000d10035144c170010301c15100310303403680100e00c4180c0c40c920921454600400314103480707290000700642581e807035030074a01040c401540100082503006411070030b059811180507a440e2810f0780102c7c0509080640240c0c1401040188a080005e084458030100318802c0018680c4c2e0f6221103048509070100c4903480941c0003080040c1001e200030380c2c1e060204c0100c401d12820b2182540405080360440d82200c004907074000b8540c0e8400c10308101920540a092004200750340c115510562680009407020f40101030520007184803003c140380c0c400d0183c001504002106001500c55406848207100c1ca50104280078000b2444078400c3c0201c0e251484054641482540395556102da40b443c000c1081d41c851510041810840d00820020b5407510b01600000c40c8e1040c20346a2011131620660001d20411010403020b282d00400905455080360000d109018141c2c1d0410183c841b0f12950030f0040240500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 541701762 1250 541700512 541700539
    0x70302030712110a021209031e030706021201090608010e07030204021605150601090f0308031611100b09060f01120903030b280b0918060a050a030803061503060913030c02 75
    0x3e101030120591240d007110425440e19090f01a5031150000301c641503040546503095105450300141800000201147d10708861500c03600126009101440488080940100601211b0f400f03040d01810849000700500c280140a882e0303940c43ca88802030182d5000300b200521441940c0d64503040c541c1100a851100700d00444542602804445e41c1c1d0100d00070300340100d41070794040c1e851010349603c43d02031461074840b0b0207851881e9100c0041c0b18100100319900c00304641060090040580510b0b0300070a050600008000000c600201003034010380080c113000c41c0b56030380841591101200c0110000c1e114115050803005046040603090300700441134009125880c00d00400844804a101070401c0243c40d91450b24540c45080b28142c1c0c8141032400c1910340c00e514011703d503041720707004286880c1680d5900c045004100940c1c41628202d81c08010007200317042240c50118000071109541c2e10f5442d010001808042002c0c124038000411810710780109401801040c00080d002060311150046 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 541703012 1250 541701762 541701791
    0x60708390703171602150411120c150a020304170123091507050703081005210105010807120f11090a0c1706100e0d0204091101020712050303070302030712 68
    0x129900818003c00d40e101c00030b45003100c84507400101c5180b40e0301500d40004c9030f586150ba1404040c2042e65141040421001150f84080341d21480003900d801074404103448604200380c40140398100c0c81e011400300028032900e0307404801c803003c0d64140103248020340c140304496401000d100d0069182d114017043d0f80004620560503c42c4904841c80880b284020086801032503810143d400e43c0105000340044000607002e240b002c0e60121a00030386450090303035680010384060310303e00301440007505c4680d40d04000b0030a00503140500010001040034507d02171150f00c0f41140e01802401c41d641c05803c0a00b048940d40503403c683c0b10081c8102050700741581c08000500b401c2040704042929040308505441c100401c0030301c10b0300020002802d1210744030090b82c124070501001640061b40403840c60042e615446109019030003202030020365030070315001900d08200d13034001c10040b554002c00d01000810003c00c49600082d540350150301c90711100c4082d52000c0ba0842101f402904180c080084400d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 541704262 1250 541703012 541703027
    0xe070203031f03030804020609121c0f032c070f0602031201080a0f02040b061611010e01051303080a0905031903021b03100c050c160305060708390703 66
    0x100318150400b11514841040c82020051000601089000001402515249001e01089400a040104551510b10940b4142480d10242c8845184603c10040010354404049a06003c403410100503900f5070307200200001580f07030149840d0f2421542d42d50340703004050003070a0007440304600502c1801e4807204065102e42050440120a0900500000d52500001000c0d02496040725640403c18120f400340b01c0034000e01c00100e900028200040c440994221205030311442c0030341d0780c1e508240842800100741180401045041104c00d0290058640d8216000300469070300c030903850750300c003400c000995000301550302c01e5500d402072000908039102450301500301d140c840ea0944013040200d000d06203484864203c190382550003401862500c07201948243e50400213414102c0c1070201f0710f0311591518088240103510300c14056410807c102007000b20301e07045112800c1002040c503203102c1503c00e4503c010f215040b0b1a008801107812150b42003401d49030503800e460078a5895005090152182 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 541705512 1250 541704262 541704271
    0x60207050f0a0302030c10020a080402010e0613030b04060c0f0f05030603070b1207020f0d051b03040f0f030b400b0109060e100506040b0a120906050f07020705090606130e07020303 79
    0x20700445083c0804030800380b02725035060a5030b44130082152541d400441c2d1031610b8a02d2640c020f6004c221140f160500c4c17040c3c03100214400c0c80c0d900740314901454240e05440d0420094000d204401c0d404489040d003180000b81e0b00c000f41e11740340e80c6a030790b8580024580a19940410021038001070714441d5007600fa03444902ca42841e40171141110320b1060000c0e656a078076015100059000e200020303400010100078540d0030b10030070032641001c0d2140c4d010342c02c40354254401c00f882d1440109c10420029000361941d8070659241d00044c40200304200c030487c10754008107000510300702c0712049001001224800300d21a40001c00c0b40c082c2e42c0c542da50340b8000c0c80c850041c1880020017100040c04a052095124140c40e0040c00680c102490401c01c4200c60700083c46c0b10b02400702c0002044410042c501c00e00b9880750041c3c5011506003000c078045035942d032008e0849000c540052800303004c0c0d41c4404200c141c008806495940c1d40d4071110f00306103d400c2440d04010303c1d4014043c180309403240d0002c040c4d40207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 541706762 1250 541705512 541705537
    0x907110609060103080406120b0a060905030f0309060f0706021b101a060a0818030a1d06210702011e0b030d05040f06140705030c2512060207050f0a030203 68
    0x2038441c0c84525503221402d100c01024003a0400092040d544a4940782c04090500360300400d202c5a0790f0000390300d40c5419000400040d24500042016240c10090300048080010240d89098121000320f83c040c468400240c00d0380c0f90000d06601041040d60440300442903084041c1c01150000c00501d855504e2110040c1680c2d00b4410703000c3d07804803a1940074140c06401084e013854131003455010780d00c200008001c07840031482e2180b0505100c200707000400f0002d900350f41e55000780840e0680089000d1a07000aa80111020301c090811910f0503003e0078040c9402d007107100e80135902c030a0100c1c0504482444003071583c44207841141d803607900c1e030070221221408030262030402c00004021a040c0c0145d11405c000c1c00c81c210001c01c21300380100c01604000403100c000e646804015143c5600d1680048130313188150744880000d40d640007906690825400c100c604034103d10b440c0100b09000d22207849005012030742d001980d20204001000090880d200307140554400389403608010b0340302d4200b07500d40c084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 541708012 1250 541706762 541706773
    0x210080f070509061c0902090112050610030503090f19090218010201020a022a120c01020f01180b0a0209090c071101032009040f0509070f090e0a0b0a0605090711 71
    0x1d2980c06803003030310b02e000710280200b4100101882d4481c0b12240d03140341101c40d1541d902c41400941c40700328109001c1c04020040c7c2910301901d1030f0140c80e0400041c440666814540310600c0007540100440e00990f20481e50210114034203400a46d1703407903c0c1407100000c03d144980c002441c20a0742c01502107003021101108084c490000160700340e10401ca40c00c00140c00c540d070b0200803010304400ba09101281c82c00a51a641e0304840440c0308200d081f803141c0c000d0b81c0074420341681980c1c10420260b044035400020702a0b8001d0b414050b400c00040350b4020b181e1140000000d6400c07419505446844900528901e8107090850500440364403084082c0c8504c07095009120940d40240510400548085140e5405c1e28140754500d429070015a80564026118959001c00315141e00416006054500250140740e19001c002010f0710b9903540052600c03070410071906109003021800729051038210464206560f6218040c01c002c10b0a904241c0e40071000c9018090a254004048000c4140309401c030ba0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 541709262 1250 541708012 541708021
    0x30c0201050c16120c050a030306090b0a0803030a0c051c0e0607080f0112061d0d090603060b030106030e03120405070323100c031529161205070210080f 67
    0x11518410168000d40d076140f5000000700144100803c10300d070034030340d140c6101c5842d010340d5028149000111309400003a2500d80921040e0428825a0300c0948201c0d110041e82d49016460f82d1203000040200001665410221213118011821105d01d01c018648045159440354402401484005075118440c4980b0780064a420b01604c1200c3c059180c007500041c40360b2910000c1d205090501c841202c40503202d9000c0d100380d9429001c03801048020b080500f182000c540c000904100c0c0c5540100105403c0032000c129900c2c074101102c3c1910110725010a034170b02c1b40c01c650f62841c0700c1e1a0304c00b00803002240801c403c0c040040341220613a0b10a0100814044c101c6c00d00030400028840919016040300111105907400c40d4031201d0498114280403c500701100713541003600f06281d1092207200d041440300e148080f60f5100601a00c0405da0009003060011540451003e403110401000080c0344202d80615030b0207030056854661707006250803811804404000d02c00c441c1690200c1c2c62001030300108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 541710512 1250 541709262 541709281
    0x18010506010c05072913030b13021804050c09010b0406020d030b4b03060c0316120207062a0e0d02090402041d061e01030b010501030e0f010c030c020105 67
    0x21940c0300e8000d802000c1003800c05017851031050505241d6820b0820366206040c0520141e000f5102114080d450301c1c00d650710f0b605115800c4840140503400201c21154160010303640d0800350040d905004028030004d40e15407074241c0c501190f1040d61038ac06a00032000080741d2110000034815507485070b080d16502c20301598180c00380c4001410003507200c00015030b120000d19017103485040d00000101c440e6050940d1000250104030824103031500b42c0d040342d0749900d03141000c10915400c0151000ba1038510300e42020604000200c0309506010490046010304d8100980d806480040d0b810000400100322041c204010204101009444880c0c47d9015003803402e004065004140b1005807048512600c00e60800140441c0200200d034416650f52110f401204040d21142c1c10145510090045081c2080360800c01000c16850380c007071514403801880020181450b07281110b00030700f00440c031214101d803070500303101c520011109150b185c1069201c2e07255041d00140c100c8420764008004030348801000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 541711762 1250 541710512 541710527
    0xf070b03060d030e030a0c1d010f030c060c06110301090c0807020714061309050f010611010608120a120509031c0204080a02060c1203010306050604291306050303031801050601 77
    0x5056000c00040481030109000e481040d8042c04000c046e9110404241c3d903501d62400305800c12031480d81a650b12020740d084500603117015046040c1c582d800c0c140346030380f00d224102c01806040b04120142550b8410803450390000c5104080c21501c264070303581c490f40007400400041144000081003103012560160004c40c040c0c06803404010040314144c288800c0c080e0a601038101d408080120b4000001d600301988034460140240030a80d48955242602c01402c2d550307400c40380f40b9580d1400742c0030004510002900440062400180c90f1240948502504c4180c40300c90321f901682d04003002c00070161008030080c852065094846100240550b03038005c06c9028034003c2150691069203e44050f24200340035211080c91817040711603400c006030f4440c00c10303003007a0300c00c80351907071101c05201c51464540920845203401e0300d0b86090002080004100401026401d140201340c42058512400119000310b0054400a41100d60ba401c0c4200e104d490058000b846000310351034040400c04540c8101c16 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 541713012 1250 541711762 541711771
    0x806060903070603320f1e010603050c0705030a02010e1204030c14062a190b0604090804050d15050603010626161509090b06160c050409050f070b03 65
    0x52000d981800380590042c40511740321a01405514100d6049284000c607185018180b2030703407084242000d18001c1000c0348060312a45400d030341316544c82c11000d5116503071411540545408201e540b55281e584031144110300307020748a4040001c0d4608559015005080c1544072602115002c8403101115030701d40c0200d000013800300c1c123001802c0209001e80c625042e051040146558034244a034101c6c92030340c5400301400140506900000c542c010b10a20a030030f080c900a650040444200703551b8100391207001040c10f403140f542e4031400d200703120000c015140507101c0034100d2a20b03695181411402a03502e141d070305200c1401c220004105007018001d041c01c5820070070b40e0b8003e43d20580388010300c42d00e49c0000d55649105917415000303810380401c84480100000000424109003c0c40010402e40b56900041425410020010100d85840040380c800f24203036a02101076201600d4a01400e204070f9001c95441420106000d0030700c000810030038000c0268108407400181e4a130107003980c0f8001100d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 541714262 1250 541713012 541713019
    0x9051e06060a120b0a171005070e040f090204020c01091106120103020603070c050d1101050901050c04141909151403060a050402010215010603020c0d0903020d0813090504050a020108060609 83
    0x741d10b1901800d1040400c024541c0045401c4400c01c000c19450444d69205540400035040003200300380c824041e40141405001c010701061405d0780300a452411109081802141d0b00e0101c14130505003503000c40f80d02540100159036501290030a02d018241116058424121070f442024851070200d04489042100c920701c0d5805a29680800c4040c2e04002c080c1c02c24850b01150410000d0010b000c4c1e440701c6001611a0158600031005407800c485004060f02100d038500010701c10600801c109072800c40718800c0785d0070402d14401c808030300501300c40c11390085a0240000003003a0131643d6042210307604003181c07481031410f80d00c952507001c00150603e0310360160030044c00300b5010a029041154071900600455034003075a90200404148000d074454000a5804940d81c81b40c0300d02880079066000c02d43ca40114a1821500002c030303a64524800102210400105e11300c0c0c54904041d854010043c0e11400c03c140d160a01b4810f444140c9524101d002031031001c0003407820707d0000141c0d0010803014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 541715512 1250 541714262 541714267
    0x5220302030a02040c14030702061b1317030706020d0606030c1d0d02040b0603090a0302060105101704031404030804030512071a0c0c030c0c030d0503040203060708150a09051e0606 79
    0x3e800703100041c14100d4014040150000000050170f240c107005501400071030303004200510b007074000c2040c2004000c080080d02202000032215403144c4229210130341c2c000e981400003003001750000d607140d8814120b0041055002007500722007451150700520460b0031035142441072081002c407c5501400505103441503808180c0c403004541080d03da0219038a1021744005502803000000450300e8104455054040d40140c0c2c9440c03c06605000711801070a090f0345088003851003400142c07200d050240a80c030407010a40c0002d00303044c825001070b038107414144092903640c0e441c2d041151030381d405408240d50350320440504040981d049400c66076155000f94509001e419105071a021012000c0c2c000328206a05004601ca100320a20042c41c01d165a4001001e0746a0745909060420048090442c140503040c000c00c00941c80200304698070840700e10301300c25103030b54046e41d801c20340b4035840358a80c00c9000008041200344440d844103000312002c0014034100303240c170b1706202e03a400c208036a0300350403540a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 541716762 1250 541715512 541715533
    0x30b0f07050a0203040b0306060f030a0903480f15050108030f0301120f0c06180b041d10030506011211030a0201021e01020904021303140a030f0e030a0f030522030203 73
    0x46d401840d001007005254600d00850282da2085982041d02c0e100d1040f80d842c1c00b00b201f0503400881d9840b205160b02c40515100895085002d0101c0daa9800c2a40a0f1300b01030010a900058040384841070303502c01022201c208150900540c400c0c14805100b00c0a40742000105040c4000002c0e180e03020444080c851850f801c003c803100d4100c00b0304900300c40300785005001400199010a0a0010301503c0c1d8a044818110001400301b880c3d4580c4401e1140204007c28040c0340c10003000c803055410310314858209030b00c440c01a5000c0750260350000c1c0640c002c090001c0f03800d030303411400071401c0d40c010008805180c041000701911000e0688000f03000d688840303601912810f032900c41e40c82c09109c0200040c100001240480e0690b400f403010140803200e440000d20402a5001d41410140d420714018201c004103640c010f480c498500f002030051090580d074080d2556000c02c0f207071038403aa01905011807a2a2031402800a8000c038004100c0513502c648401506204034000500310b079001801882030014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 541718012 1250 541716762 541716779
    0x9040804180b0904020616141b010804080d0905070803041509170a1202011d0717191b05060d2c060f1b0a0207050301060e090c0f0f0a030b0f07050a020304 68
    0x482e591002c03224403801d00710804a140308c001c0034820310188014200e4451654041e2100031029640c05040c4000b036418440070a00c43c1d4255440042035690000b081d40780d40c1050351902d503450380821418030000501150714100c0b4044018a07140369291100f20540b5913202040c82c1d903440000701150b60203d501c0501041381114003018698460000162041030403c1c101407107405060040420307400304500700040d40505040d08516035100000d071555000885034402e00c4011303c1000381c03001010310600b0b0605100902510010403004100b240d846008140c6034000e807229944d020105000b42e0742208400218001c00d0035040c010601801003940e03040307544c8660010103401d404280c2c240e000c806040b145c80400500d580c500503001401101d01d4030081500b034a03400d81180c2d115104031400d0007401350b00004c1100740074404482006080754003402290343c007040c03415819800f090b0003070000140a084080107003c1c016000700c1004550b14403900f81c61612461850f180160301c104070400a618 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 541719262 1250 541718012 541718017
    0x911310b031506130c180e0702030708090121140c04150c0c050a0b040905011e0509090109080313060e0c0105030412090e190b18060105070303060509040804180b09040206 75
    0x3c020704100610b15070000000c01c9a07160342410020504c0c0c0010f089000b02040540300041c858110001610300d40204020740324042c4050041c841c040115051303445030301418a1a4801d0420f110203400107021070700b0100030b0030700b204850780c018000e500400c076010010000c840949105003038480400000a41c108e0342d88480c54402d8030614100c08021030030360340d0400740e0801088000c40c00c81e200c9007000c800608481042c0c4c0000c818441000b06011a246036803480421103200f202d030502c00b40d40b0380c417105004d807485d020010540304001080202d4401c0c0c03010602c44003806001d0400c64080c03083c004541d01d40400d180c10b80800c006200044c001005400b115458034054604010441d07034031481060300c0b11055501010b0074030303900300c0000e51417080e1041d000740d030780c0882d101c246448084c41c200408050107000c40341017090000301c6409040c02a0015001071202520503130241c030306270500c1001500140910040b0311070102c210b40c0c1d01040c50180240c003100c0101100001e86461342000a1039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 541720512 1250 541719262 541719271
    0xc0810050f13050a1425050a0e040c0f1115010506090102101506110a0b0c0310180207020a06110303060f180a06061e02100911310b0315 60
    0x60184545028420860f000300b50280071844000709012480708050700800100401d0b080c151a000640c0b0030640030400c036201e26410f42420700f0f540e601268041220070b80f1303465005980003030406e00410f62940d8414440e1042d500540c0c1c4074000012008001a02e074a002c4606100c01420782c0d005000d40e01e400e000908001c60b050045840780040c1500d03c0f001c0e41c240300350741da01142c503002d010454584c20024200c1c0015081010700031068495940f030305816405007090051601c0400020741c82c43c212042540a460030345420a0026071405170000694003180c012406401d842070001405405040b003a460000b050025506580e44c038000e000c81441010322096010020507003440c00710100c40c40d428001d004425000c240701d801d001d0054400c100c01111a04960011034140080642c003080000e04102c98010118a05007541000140c1407040d40409610070350703141000b80c0e1183d214580e030704144c0e81c0394060180980001e40da14120f421030740c00242c040c0c10103c0342c030f40748a41449030035030302 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 541721762 1250 541720512 541720519
    0x80604020a090806150a14130917040306060f05041b0302090105130909050c060a0f08060d060c08070e040b1c03120f060302030c090601090b0d0204031a04060c0810050f 74
    0x80e50350f80c00d075468030800ba50f5000701c0c5401ca01d86040141413041504028150a555000440060030081040708100340000c83c0350f944d6400c4804200040d41510626071108040c4d03031342d140c0781c82c0e08120f001030000744102c1400c03140d003400c00102420140125400c6200901001a82001300e01098000c0d501541c00c2c1c90411400b0402c042c500100d40d54008080c1040050000c4c0c59801761800714513290054000d144180c10510954900c164030002c01c0000402500d80307030180c1d44a400100307125400c2140020a0181024000c0108640c0a0051881046560744a820601510040c00101c0340c2000006800070f52240012111036202c1030844180c13031003450141d030a03490b842c41c0041202d00d4006288001d0361550b07010015031070200004d640007582142d007040c003401c0c500000780003240c0510a0105000000c540525211000da0581c3e0065030040c900d101080000c1ca0980f80044040b1803c4415138605803200320b55030720618016109181d81c016a00a080c100010401c911a9600c81c143c4e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 541723012 1250 541721762 541721777
    0x809030d0203100302030637090b0c030f150102030403031d0307030507140f1305060612040302010507081807050909010e03040e06150f1c09061503020103060f0501080604020a 77
    0x80010107407000394400c100c220003500116065104050501c1c4024090400008404140c45403020003600704011074100c080003c07841e10165a20b8602500c005100030b4040c06044042003007481140e4005c6200e01c07070740e8005440c0c035a0388035240c1c07044030701032000d080c0141c4c014801400001c0c050b0900f8400d55403840b002880710f0981e40300092805000d900122a560088031007000000c0c3e41045500d0303e84411100d000c0c0100b00751000c60b40c0308036005142901c3c0f03515000480c1807902c401c5d040703510400c0601c00103061890103003400790180000f665220000380d4618009009842046403038040f080b0b254000e003440038074102c2001900d03e001b400220655694500c42440040104014001442c0d0482900282c0c5021010890309420103a0400c01101d4200718003020122450215014211030120001021881c00f100f4001810082c500401382460101c0c2c2c104010310951202084903c00d9070300744549611800c0c96000a103585c4030f00c4c2d001c203501c080443e000e850160050700b0b240c1004e20f405035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 541724262 1250 541723012 541723027
    0x302180423330418061509111c090209041101090b07030e121006170f150a1107080a02010228141b19030e01020a0c052e020114060906030c01080903 65
    0x10444c0d007810f508031203030ba81d903002d015286031184911038002c01081070108007014030100701c0e110714402c1300204000014280213034a00a01654422806541c0140c404d440c20b00c3d00e4900701c098180840d405034003080e680d0400284140342c040c00c42e2400303603240d5144414400e0b20f2003032001900101c40200514041c1e54030324240000d6612544004240c104e101041234a00c0035205810102031004200c441c2d08072056032030010384015241900080d1010f070005400d0208000400e0038094004001d00249000900b41c44240e415000b0b440c600d0342e00481c2c00c400c88802080717841d0021180c0046004503841a20041805501c00003810400004071341d68160002070090407424940d111203004480c949202c221401d055101c48410100d090a00041c41d040b02c0c5a121500410560f21a032445542042d003180641070101c1c1800c0b40d42101043ea014103605140310181c064180303001100401079200001411501d410790003a4062400580509054100d0038011151440020f10b4040c03540300402008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 541725512 1250 541724262 541724291
    0x70807030c2f060a080c031005041505010e010305011802160b0901050403110109151d010e03040617060d0201032c030301030c0e060307050103021804233304 69
    0x20b241d105403015406001e220701c2d40c1c0712080050780d00566002e51014054026816007082070b03181c1102490340d01644a9446106c0401c0c0c0d5051a0411a000343c213042c0f00000350b411a080c044240c41007601c0d403815090301c010044084900911070010200408040009800982d40c01403203040800e920680040b04240c032140390120782034640c904a80c2d918420402490b03482400f00284192840003888100d5441d1121410070654000346102c0076070f603140d0072a2003150408001c1011035000c3c028008410134801c555182d40041c820000800da00f8000681710a0f00310070380318850140101b040b01d50036202d8004500032724a0b401490440340280c18039044200d4070300481d2202d4020307103005690700c1d0f04500e0003c0c0807050640c000310303255620344280031003590f0101c0c504050310400e01c1e0050b16405210a607010600d00018080c0c1c0183c41c0042401c40c8004c0c0301a1907000306042c41c00c850312030f2100d00101610350000d884850820708500320351304411001c070340c0320f1a8081c8000d0001c6003007818400fa0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 541726618 1106 541725512 541725533
    0x7050306071e0e0a05100f030e0304080307080d02160b011d15010806130f0203100b03060d030e0f061809070801120b09010e030c100609050705070807030c 68
    0xa045a10b41d0030148000f0417004210701c030b0351405580c020b40501c460088a0000905001e0303500f10305440002124111814440110310b44901500d4000d03c81d000050080340f840c0c0c003003020405000150100803180307030107019401e43c1c651421499082c5c010603104040383c041a26000c1040c203001c0003601c560601c00030f003080c1140b584c8120001c1c0072403040b002c0c0300c1d03409072410100c20b202c59400e03130145110b081000c511009284c3c031076803050030b180001c50740507a00500200154000a00c0f80b80320114469020b413003c8040b45007907001540c0c0d40c024034000d011012603e12802d6070b51030301700010381c3c0010309410326032620f50606000341484003040b8030203040c6821250105906a900354481c2200c6103006050301d480d00300308989a81c5403902c19400c000340500703141c4040340c05c5d03801d0b200d200c0c091134280d2203052520041da6074055140d004100c0039000d00242e6154034000c00c42c55081d = true := by decide +kernel

theorem cover : BRFrame.Cov 541546762 541726618 := by
  have h0 := BRFrame.cov_init 541546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 541546762 ≤ n) (h2 : n < 541726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
