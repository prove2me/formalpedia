-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0091
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:47:18.185694+00:00
-- url     : https://prove2.me/submissions/0489f0ca-cc3c-4662-88a2-99e1abe6174e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 16187057 ≤ n < 16366913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 16188307 1250 16187057 16187089
    0x3060f0a080f0106051f0305271e03030702070303080606070b0406060806060d120806150d050f070504080606060304050307140102030108070f14010e0406122414040b0403020705 78
    0xc00300800080c4007442850090103040b1b9070001c2d42d003100303040d200daa485804049000c042c0c4800100b060231381c03119036840802c15517040000601c00d54580d43c5540302c90420049882d21300d40050704642d090040200d0b4012043c1d68060a01c80d81107440a86190001030805a04281c0802480f00814480390041c0d0141c1d10481700812683c0c50300e802d4a00d040406400c0031303c1909050008400900d40c8603064001d621181059140b99980c5000903041c0072300c8581200b410a00010a035040c0304569000368401c411500d480714035038640900c125118042d0f0300440680d079020001203103051600e5000741d03610500c6001100e240081540e20f556040480c00d002c07100d20307034001c401440500410b204600107002902c0000103618644000b800d803144120035854144070b4880b100509503190768015001810b00d80c0c403180d01c400501c0c40e1101c4400580c0000550500c030041c0e4481040f816030250313020a00c424041c81880f5200c80c0c42d42903000382d0191084055128334800021981c944e18240891140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 16189557 1250 16188307 16188313
    0x20d05040b01050a0b0d050c070c0801090501150b0d0e010906020a0c0302070602060f06090a0906021305040e03030403050306011103070c3203061308160602040314010216060203060f0a08 82
    0x2003518101c80611010782146204441c82c55091001c804c0107000c0d1030554806010104950b250041c01ca1071910404202400c1c482c00c868020a206005402017005648074100802c40c116005083c0d5452000600400344418000c2280c002d1404035500907805150b102c800014528100f0f617140030880e40300d2150030001c40ca466080c1e40525405000306e100900c80c80c0054031240c40c140c050407110140007400c0c14424401000405e20030715995000600e002d0340500215910030134120034240f90f0500d8401e140c401c90600c401c0700c2005101005807401264581c44c2c0d1400d540b103c0b4015286002007071414103071340c2310038011203020802c0791411800501002c005060407a0b00034418a0168008030070520003103440c40e081d1805a240000c4855110fa40307951003111400551a000c55644501408491100c4140f0310706824040a9801081107074800c003124542c0c801c04c0310740e4a090f40a0040d482112040d02000c06010a20b5038000b150711030700083c05010092484030020708106a540c000d407000d40c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 16190807 1250 16189557 16189561
    0xe0a11090f1c1b090203131205090a030b090f0304050901050f0d0c0605090f0103020703090b0a020a08040b1b07060203030402062104060506040506040902030703060f020f0a020c03070f03020105090907090801020d05 94
    0xc4280a404041c104d403040a603e54030701981d00c1d08075a04c038114000e041034180d0034070b00c0e1081e124200f680c1841c40000c001840140d903034100119050011313203452030580200d400b41070f814140042264115640135250200ca0303840e00c0d0030041070303010b140d40c0c9903006186001c0400014185109080103011a501c1d025115003000c0144001c0034200041e46042c140b041000b40d01081d003003100082251004021140c0c1c5505c90780040b42420340e45000185082404600400c03120102d50152003d240804220402c02800340312169980003144074490143c4c00410125001d400c1c01c07001043c0c7c01c6a541000504403141000040c15880d003114142d07085543d60090054510f01401031641081084500f8020088550006602e40080e13100c014402d03551040f0410250209405503551200007540003034541d1014a0069180c210007508240f003070052420200340c122a43e80f0450a407038043e07590a0408200307006014480c10043d1001b0140104000c0028400f5402d0005290086802601023018 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 16192057 1250 16190807 16190843
    0x302060703051e0c03120a020c0d0c052b0807020304030b070305040201081602100b0307050301110301151b0f02030f060c0c16060e06030403030b03060a02040e0a11090f1c 75
    0x2d002220f50300288603420800400900e6000042c0c81d03030112145201c4c2038545918404a0080c451400c0442c0700707014000c070305103007103420642c201031240c040c4007641e03200a02d41c6820400c0030354080701c1c02c00250208015099546c800c4030819400885401264503041e201e850340d102c0c11004640d6200082c1e00d4408110465031711103001c541210705400684030140c61a80007035141d100c124283e002855440302c3c0d040c10b943e0108200b000034030f006002013156450f4129603600c19030007405103001d072080440c5040300d042c4c402c44502c0c1d074001e0510800600d4111030358070607031840c4140c482680d151203000302e1180c104600744240c0d0301955005800ca580c0714003007900c00303040c034000e103100705201c91144004006042e0880c40400351807004440c1c01d540d0b1350319803500380c008180c0d09002d10380610400b020005042c855034014001d0750040c0160620641d00c132240f410135101075450701e400701d04c4140a503916038100004028803142008000003280e0a008040814401c883d00d01960a2100885140c0381 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 16193307 1250 16192057 16192087
    0xb0c010e010b0616020109050604030f020102120307170415050106091d01030203061305030d020408060f0a05070f03020a0207080604150b030a0c031101050702030316060606020a050604060c0504030206070305 91
    0x40000d010002c0c07202011160000301e150141800d5882d0140c2c030081c482086a04c02c2e07040001900c0000c051a44071901c07030400074006109514201d015100300302c14035612084007030580c2d2082e005030f590140c42d907085800320010b100014104440c084928440c00707044410718090240a850b5654540801c10b18281808681d204c21404030b2401e20b401800500140e1408500661f01485076a06210101d9107807900d24618480c055890018078400329000c101d481c000700d49503008000844110480c0e44521440800700d034410780f525404510a5200c2c001e201e0301035005410412243d00554070466950340140b03040034000c0b1400c607904040d64500d4406400b007407040c4180d405043d8010a42e0101c9580d41c2c0841004a01004d000032220750f4a0501c1a032090003103600e07240c0c1c0070303054a880d0400d5944040020109403400c6500c64202200428954400907018030555042001020552900d803078640040203491061030400004010200158a408006000c0d4038800e588066480a1107414000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 16194557 1250 16193307 16193321
    0x180b060a0504020a090b031003020303070b07080c03090604030c02121509010e03040602060703020d060b04030303140106031a0105030a060e04030816030b0612070c0209011e05060901020d0c0305130b0c01 89
    0x4030451044c0009a90039600c810142c0aa0302d4842da42980c0c1d07143d25861040d40b90142e8402075140c84000750071406c10000e180f0640c01240303d5151024a0385440610000a000484a41c11294403e40000300820321a203a4144c0c2640045c0070034000740c0da003411603814024202040c0115107840814405132200921400c218284180091405d007420302100030344800000e0034080070144c002ca24504030781c019500c4030004060303000c2500e5840d984c81c80c014002c0c0061840420303080b11203c2c00050602e0284c006c4410403001c2c582d000300600c3d010001503031550800f610034140710307543d001e02003460160305c61803900070f501940383c00036245170ad030901114148010030f019003050b01b407604080380740d202c0c1e90607a69098920710070401540d5611b5001ca07144085400301075130080081d00002201f600c1c4031030301d03140ca01e901c000c0002c0c281c0e00d843c20701c403c41c4607590301c060045e400303e580f1004891080e03802c00009841381c54130b285000740580350080c20706a16004061441c000194101d0005002d00c43c070340c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 16195807 1250 16194557 16194559
    0x14040506010c0201200105070804061406030c0d05030c010507020a0c0611060a02030a0b09010609090b0316050402090112110405010305060d02030a060b041808030105010f05130902070303180b060a05 87
    0x40540c0c6425400240040d402c048028107112203c030410101161052404005400c88030080002d4540318000078a08102541e081d54036a02d0440d0206038400000c0d0018400c0750060004c0407a0705096051042d5141c22200664481c0414131036100410001e000c0d4034041c0702184d00130903181d0f0341d0f814a02100d0b28076620a00920030549030503040100041504e40d03104016240041e03c0b60755607203841c80a000c00380d00b00ca510003445000440c00035040016071080c1d13040c641e800c00002c0e25031014584e58030841060704500d400e1001b420400e0785855001040c0c100ca061600b40e001d0215031420500341d82c0c01c069850f01400f4082418055540e0606c9140da01c41030498030701c0800c4043d6000309460b40c15030003011782001d40321000021240c449822000504444484e031070030b030014078103200020713400a00a6900160a610001000d1481481905c51881001d50910700851501c10500003e5200000c218181900c880500820513030407412300c0c0210303000d5911a500c501d0842c0c200142502d07950003407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 16197057 1250 16195807 16195811
    0x5010f030c150206040602030a06090905070602060114010c0f05010e03030406020306090a0c08040f060e070b0408070e1605130e0c07050708010c0509120304050d0507090f060b1801030e0102131404 86
    0x503200b80b540040c8483d0090340101c00142d40b522083e0510001e003816400c4a05402d00b8806040f0070020005558800c8441035030940d511a41c07200e562148868848211a00003040300c3c1d0b0b064080303080c0391500d0303c80d24402e40000034030340c40702100c0c103056030000c90341a5040755010041040504111180703076440b601001d01000f12a44080c4094454100a44050201e18140c1160f02c03c000b403640c48400121850800c842c503599888001580720761103030180c20802c3c000e4140010f07c04560500480c090f00c18109692260740d403000c4212110703000641921043e500d200300009143c04c01d803000c0b500403021032900c0c0380d548c1c40c2400d040b880c088003540a10701076031401500042c100d41c807106483e03890743d045610002c0c0348044a5003500d98000d0341c0086612441d01c101110030003000081e13480c211400c2180601400b10805284000c41e038451080c030701000c40c2045500c031903106641d0301070b0846105060004e200441c1c0c1d4030752422600a840002081c2070346e610103001264940c4106101c0707080880d02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 16198307 1250 16197057 16197089
    0xb0d02090103030c02031204090b1e0f280605040302010f0815101101050a09031706090103080d0f060b0408010b04061d0903160308060f010c0b01051207050405010f030c 74
    0x8200c0300c2405200150820001d00102c10440d9824002c131041c9541c804501d60f1240c1d11822040001e05240c2e01840c850080704403208200d03020003130016510080240b4100341720a401041c860603030880c0c00e5580900c0c04800c000701c0580303034800c90000034010681d9019100c600390320000d072007101461060410f10070203104002034481002d9125440343c02c00d8a9200c4070000303c0c00c05907500485094888000c0d4248004c1114008055010f2130f8000d01a50f02c0030030b1480350003400c90030440705844a5410032801001800401d07400c10041482000140c0d001449045c1c0390b5404003280c0003174002d03850540c4000380c2080085000d0007908260502100c0400803546048100e82101040007447c01c90b094480b00001c400c0401071081d01d081a09500401e2503407034261074014030000b811100c040c41046031a05050555124a603944001c503132008625259074200b000b00800c850020320505210700c11444003160340d454501502d40245102081c0d049000d0841c5040100f0170800d40000f0180a80000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 16199557 1250 16198307 16198309
    0x7030e0610030816080409020c01180f0b060f060304050706090501020111070605040512030411010201140c12090f1e010605060a050f0702011b0b07030507030507021209060c1204090b0d02 82
    0x81ca084030780c4150100d544e0003c40c091440c09205803400548030080224000683c00c681b070300100f4114880c4c174020401203079400d91f028070360b56820f1400392202c40d10600d500c000504003d540c81d00241c0050104045404540000704550300444040300c241c1c0002d0b001700004c41e081503c3c4006003101f40001d102c600c502e0030180c401030190301400f0f061640c0f03500101d01480800e210000180d840201c040707581e4030701170910301030488583d11120b0056103041103190350400810b270110700690444451502c0d145450041d06001440500440503900450549503d1820200001000e6042083d000d41000c0540558030f801c40b481603128074043c49040050800c203641c0101118070196500b8000740c0c40d203015000403108203001d86070007004106100310b00814884e41c986100d20030013061b9028402c0c0d0b07640c403c003242030325030a03280680541d016a018940f00c8440302c000e0204400003400e0a03007410043c59045141c01e90005403101d1444001409001c103407054080c402d250310041c4d5260480586981c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 16200807 1250 16199557 16199581
    0xf01050f010c060212010324060b040b0c0c100306050102010e03041a030703110a081f0308030c07081201090501030c060215190209040c200111070212070807080607030e06 75
    0x10400c14100031030072255104201c0c00fa41a15155085a100c14580b07603101d1520341004020b050000d4840e121401a25010007107034000d040650700c0341104030b8205407402003a441c10740c2058854441c580282c0418402c1c03900d0f10540d0300d80c0044140d0300820501d2030700001a013107810002c02405030390270400050100c03403c1031b00c2c90078005103a454000c0d0b60340d442000440c01015050745c003002ca03640014640c1581a440302c82c16008070610249804031680303017005854035414611004024031002e000161112042d6405800c0c1980038440c10361501d80140c000000c490f20982252042030b45e960014003e1040240700e0402900381070004040020500d03020010135407004007510350000d00c00d884120960000c0c1c040c1c40520601130300c2880881401c0b43e0103842c0d48101c0706414460b0380f407078103c10800314050164000c5400d9400240340b80c03482d16020702503082000740c4c40040d18400c14800240c0d1000420410008000d1803000d0503250808450080079141c03040320000f6142e00c94014001d010000d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 16202057 1250 16200807 16200829
    0x170606030307140712050105070e0303030402150315040603060903090e0408120402010e060c0105010e06010309080405040c05040f0905090c04050402010e090a150801020715020412030e060417010207020102060f0105 94
    0x40404100c1c0c0d02d08140180c1d203080c010b9040010325a01c02d280b600301b00001504414010300080d00d0700c4134540d0240041c10742d44c1c00b0489010354040c48207a44200c914140c2001140c0114181302d41c11074101070000454103070b4403944d008071207d42d640c107144028103900c0f210b101c0203803500310008000307418191035000300c0d40502041d01c480f007900b90000c1421a0b005a0020301f0402019003820b480f181c00100e03050080000748502c120030501440092044d45c482c1c4144c10043da4450101403c02d0b080c5010f002c01010078040000a11001b04004503004038022a0b103001400b405501068910308841d0103800c00e06035000c0e0b070340160300741000d00005070b810146001003078200760341d001100e54076909208098201908003620b05c0700310728000b060070b40041d0010401d5500408903040f44c0d0100d60304c01d00891060b8071507094120708504292002038032600317100c06014002403002c4d040548900d40b02d0707001404c1c000c0c504034685d400140383c000c42d60140304840c1e00240c0d400844c40203600d0070000c51003078600 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 16203307 1250 16202057 16202063
    0x60d020901020106030f06050a060503031606151707081002030408030601030b010c12200f07150203190f081f060f260108060901020901020a120519030501170606030307 74
    0x4906140c0c564801d43c0040020b40d008002003040160605161004004c1a1148400582040000b050341e060001c1180e14945850807140403144d21911040020294510b00b4254042c803404000384c0151000b24240d21f4007294005002250301d0031300103a1801c410401501c60720f50050040101251501098982c440820300300400d2200c0840300480341c0144080c0000c1a0340004501c1c000003640c013002e07004007000700d0300c6000b1040080d01807203650707a400074070300ca1000c2e404202c0074816502206501c800503180d80c011a8202901300001c000551001d1030600b00060f244000004035a90001c107051300200d180d9844030b80164880410419200c00b03020b07e5017401207245400120612440b4030551060140034218201d64100c0c81666000100b0702c1070151500ca01c03408142a0001813086503000c0205800034040181160341c0d06110b00c100d91003c009101040c40b40e00e18071216807102c0120070101d1f90b400201507060180c0d01c05084031810710609603a01034401c1100740c1d100041142c1a282e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 16204557 1250 16203307 16203311
    0x7060f0503130f08040501020c030604050c01030903110d17010909021005090f09040b07030509070f0e0402040908030a0b03070603090503091e130504020f010807021504030905060a020304140609060d 87
    0x1807411011030305100710600081c82d41c00f80c801018240482c003000703041035a80076800d84412903000d000700743c2d94507000e40c1c01a20036001124030700c0c030b190b00a900282403a8880d01700a10680a404082418032801d21408004207aa40c001805200d51000583d805464003100c1000500419000304485c0311038103d0900600000040c100001d07990010345001da900300a0690340b10f40fa044c5401c0103802401e591000c0800d0500011807490200404c051099580c2145441c0c2a81d292454280e601c01d0044c0050f60050b03603814408021481140055210380c07035000001c40d031081c1200c02c3c140b0300f012540c020020103142c50340010004001104454a0308012a0503003d2184698220001810411217055002010981c001c400f000d42c0e4111511541c000c6800e500c10f071882c4801503038103030300c102c80410040c1c0003007602d0b10544e21014491a0858001c3c5041d4110729258004220b0581c030110311b000140e800401e00700002c41c201085041c070603c0643c4c8543c2031107460008188503004000810b61429 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 16205807 1250 16204557 16204561
    0x30403030f0609020a0908100506100305040201050d090b06030c010f0e0d0602090909061005030105010302010804030309050709060b120903040609120f0501060308040302030f010c020c040e0109020a080d08070207060f0503 97
    0x1e03260400340291031444011940d8502450000d41441614030500b01b16000e00c4c1c80c810300800c618032a681c8181d101410321883d248040780c044009001c0204100e050003014000040034088034403520300c2d442d201d00c0ba009440c1c200081018588485009810304101e000310b1140155580b0030311852003c40165964805021549490400f13402102c190f1904201e050b010001120300018001e4020b11040e1102100d55407180145400e0312400d000c064082490800420002031003a88440f0038140038200344c0786a103442c1d00070391058503559800001941d001007540e1400205c1a1074458000c2001c42c01503186c60724150340601403041c1c1b44920b401d46d412240142090045c650120300203942d00c00000c1101c56180d1409084a40050009a0103071150840350448060140b0440360a52100c0d0010312f101e84c1d44c8010440544189000b1400c0307075403110001c0d001622001380a601401018000e05990340210100400d1900020000b03021903104510810070f040c0c1010354005062450302c4d102d541d03a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 16207057 1250 16205807 16205831
    0x30c0905030f0303070909020a02060606090607060e07170a0f0f03020a06020f0414030313030605090a02040504060209041512030804080f07030c0302010605030d0504140f0603070306032603040303 86
    0x50145511281e014010030408050405011000318070030f112a40381d182caa1600e60800104a000c0d510410001da40001c0204613280303000c1e070280040500c01425076150104a0f511203040d65101943c0074144e602ca10410310050714400440019940c3d810b000700003442d00c0e0780702d48a400134030354009000090b01e121000b09151007030003209900d41d0806000d56845010f25014407560b07020780303c0d6032646034403801a0b0749640303008800c03210b14800c05c0100b07501c040c0c03d41d00c0d418000c00b07003d04040d0861282201080068079240102440745008000051b10384480c10240025504003c181001401095174280525015000c00981d1103803d40340c1b845007580c0e503107800622803081366911840c2820124401d410994028204601d451080d4002d000c40c95032542415079819811410201149081c4814004c102e8161480d10134100018034010b40b458150f0089010341c1e04c259003c070700007034a07400d040c4203005001036402c02080483d9401040030040881c0c7d00c0c11400f02400c000c0c00c05031105898500c0d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 16208307 1250 16207057 16207067
    0x2060904020f03070809060a0e030d0f0f09050c0f0306010602030f030709090e1c0e03030702060d09060501030c152d02070302130e0105010b07050a0206030a150b2710030c 75
    0x40c6009151483d0f0301d081c000b001030140d48085480c3c444601c01c0000040132074017203004452209d82d914000350b0070000c1864510000d0304810000725002540c442c100c00c40003c0714003c001c02c0c14000e40280c00e201801344c0620000c0d040305410703240aa805040100603141c0d0000449140302d0f80d2082c55602c9444220b01265000b180780c2c8000030440c1030203049038010b080071403510144401e9548180003000c005209496a61140c8001a4160414440c1c1c101500b0301000904031180d00c0c3d5000503068003541e80d0001120300a0b002607500003945401804141c54650003d00381c00461300341031604849104094052068031080c6e154081918480810014020400f400103503a004098150226503d09a42c2c01050120707014161582020000202c2410410444011507041409000018265002d00460f948050616400c0c903950f180c882c280035405540d0309015010350003416075221584507112000940e80600c4040c00740c041c5503a24034507036030b102d034501c0c40740418100400e030b007a900b00003611 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 16209557 1250 16208307 16208317
    0x30518070605070c030506181e061f0305010c080702070f12020f060d060603020a020c0109050f091b030a02070201030506180105040c02100e0303010f0806070504260a0b0103030813050a0206090402 86
    0x44a4031a80007403010450344140e40c0700c820040c8d0310440d04116030b4085c1103580d03480f2085250724039402c0140400c00640441c02003004404c041100861101d640e41d8819084840100c00c60000440a80900030f43d55030520010b40100410f050480c000d074205881002d904000c544000d10440110039005000e84444003038170203034042d00380100711040e903d10014029600c000d00403030043c0034a0040031019030280c0201c0042e101c010344110078400320101400b0300c02202400460f40f1082405541046410042c0118881d4003107110142e21000e180c400075040e504080c004c1072040042c500c40d51408000440c0590445c2e0080300d0204400064207400d0b401d1002202242030502c0c20203503161100300c80000110b04903502c280c820341429a03140e248507203505080d500303000001d208000c1000800c0340c007400410301001101459100e20580700c0d070301e032400401d0303201102d040411500400a0603084a845a401301012825000c0780c5802d9948686405007000300034442c05000c11020015151581039403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 16210807 1250 16209557 16209563
    0xc060f04140a030f03020a021906020304050904080c160609090501060206130c0b04030b0402090a050106050f090a0b030a0507080a0209010504050d17070f060b0103090803060d24020a030518070605070c03 89
    0x3c013081c9404c2c140252542c950440903801603000c2c1d0404226440701e40707441c400300e17441a0f02540c10b09003004100007030000050b0054846d000c2c103024004843d0020b100c800c010702c90010f14000074602e8294082c1440d00315a000803d441c2c6800010420700e6004202c10b68400e0400c6450441e00c00c8514000c0400b40240c1c1084502c41d20108002c400c0020307811111380124000c0310f05141583e00c400c140f00c183c03002409034600040381482049510b40f5a00701070100140010040040386450b94034400e040e820803501a160350791203106000049801010042d004094040d065152503045000178009225602c11039010344190001001485201c0000407690100c6045142e82d406a50130092024050b042e4141c5000f440c290b1080c01030340c040c1c49444072442e4400d4006045540707400402222840009041d2820318039a8290302c0d9418440610f07003000d0700a2200103071180b8500800404641000300880c042d2492010341803500b81c00055140200c413603a20b0415620842e43c60404081d000d01c0d4130007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 16212057 1250 16210807 16210823
    0x20a0b0705090315040809060319140a0b030d050901110f01050103050c090702010c0e1302070210030509070f0305071502030d06030602042c0c0306030a050a05060402030c060f04140a03 81
    0x1105006078410010110b000c000c4044621320703110071002d030011600646004100c01d80c20007004807241080401785500008981040034182c1070002e900d01514040060b04413107004200070001c0ca00160710403015010010b4004190303500c0101406800d610484090340d040c4460012150300e268801c1000307207600c41d4000000d21207541e40c0c0c13508030380c0c888901c3c500504c65209140044d1005205204000e0700b01d1040e6194007004804000f031203450385048800908080d000c03c04031025841e08551b40b61514019900021700f854903898135800d006040d0099030b81380b40100020808100e0004c1c1040941c2d24100c0c01c0144004144000d9203107100c0d103201402903905100300003051004580c058412107226a2200e5050700707036010701d034174a4012002d0300b220500720807002c282204a008050741e8820401307802c9074a052041d480d0540303000840c481c02c4134254482c208000440c1014031a0351003911003691390714200700e0700460341e02c003500680c040c114413028100c044003410f64400600d5070003103800c02e1907 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 16213307 1250 16212057 16212061
    0x6040519060312020d140a0e010302040e040309050906010203070f08090a03050d050408010506060304030f0c021903050303060a0806090607110c09070807030b0a050a0b1c0c08041109041101050307020a0b 89
    0x204000403d00882c00c4000b501941c8107616215006400c0c840f1010a1726065502d00091490103403500c44286508904140d801e100100e4014a031000f2a80036501070303129406150b00d02400c11040388002081241190000e1080710009404a0812003543c1c1c1c0c8141c90300d40751504000400e40360000c2d41d00291062080c00c3c9840c299541060092003600d0810009008540c3c583c07003840b04030300c0309450090001d080c207038194186521826454030180d200130514440d413074210420191300881e5070000d440541000050040901c1c0c28020345005001c6030001c0d2103c1d00c0c28040701a1180030090101c01032000543d01444000402c0c04071401c02200207000540700d0402800041c00c0d07507400c61b2401e000c07a1914000052600c0e0941c4120704591008000a010500303042d4601c806e500100381c000c4060424642c200100281401501948403040d07403000c1952400d400c9c41c210b018840d640150080100b4000c0c440071075a481d8459803011404c2c00c20325a29114000100d140c50070029000d003131001c101c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 16214557 1250 16213307 16213313
    0x50c0604031406070215040602030712020409150f03031e0e06070c050301050603060c0d020a020106050d0b22050703120c1208100602030414011404031403040603180b060405190603 79
    0x52090000200b08111041c981d10300310300707a0f6074209907501641e2000340d41000500181c01c035001075074481901e181140c1d003070703040490180598006410402c80181c890030f440c100a210100c0420061440c08045c0c90810301d0340d200540134064885107461035030718441d04032249030700076541241d1507000600502d9441b00741c1d05040100600c01c3c0102c40c4030f0350a0101103012071400144007400f03286040d045528200310314060300c00960000d481b00065548134400010726548088280c1141802420b54207c10300d000740200032071070010100c43c030114407007440c100c01080c400140c0c002941d81c80b031043d11503d81030510940f01d2928100004040c0680303052100e0400c1e07880000c00f801510f007034a03901080c0383c41d140103030788a0207540240f15499007031104042c0998412513140c1c801150380d42041307203440d131681c031014800a50950022040e80c00000c08010f0b0a0303140c40b0300c0310058603008014103020455500c43e69552800390440d8812510745000c0f41d800d014203071084004a28840c8c0c200a501e0741c0746 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 16215807 1250 16214557 16214573
    0xf0c0812040c05030616030b0109080625050a020a03031802060304060608010b06090102030304020f0a0b0a08010f0609050105090904060b03150109050601030b0109270606021e0106140d050c060403 86
    0x7a4101d44a40d00400c0014180c1400070364030b0300445100a201006241c601003c03030040095000103810003680880000382e101c424401c49004003040d450604007040242c1003064030f030094076207600401c8820011224900e501040b820290f581c18030300480c001c20004201c102d100c45840300a0751000f000001e0004005d041e40c0040c0032601451300030301c22501540d04211581c082c0701031780303409030300304000280051914055110521800a0548180644454594040e604409241c8020824140040c8002041d007403464006020764501100010309000008045c3c0c001c0040780c500079110000130404101c4607400048503030401500700c81c055440d000301022101701c01c0c49a10f4000e1320301404180254403038000c0402c1c5070410f8403144041480c1c400d410031100c58100c3d0f01403101046440312071040c02580210401400194002c101041403008540c0d0b0000003201081c5540e80f5040b41088811106000c1c00901c0000b103c50041002c400e007001c90070300800901c3d195201c440007401104120001c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 16217057 1250 16215807 16215811
    0x406050702011b031a0a0f030609020409050f15060603130b090a140c01030b090402030c060304050102070203030d0902010e031605040e030d02030703091e0b060405060d06050106090515031302010f0c0812 89
    0x10070a810600c811480031b002d01451a40180120820321020a0000c99480e0b0042c1d139009201410004508841d500c1f000d090840c002d550744800d03004010706600b086440c0780340d280c00c0780c0300700c0d1a9446e40c01c15070300341100342a10040082c000d541c4d010001e40596000e202e410f950740d400c0395803400d164040c801f1660703c030082c41c1c040f40e000c02d00e0440c8003455400d002e00c00503c40c90b4050001d02c11210303081d00b00242078000510407280d1f99001c00c0300d500140c40c140080c1010019606020402400030320001d0101e8880803505c0740a548500c40700c03000591103070343d00002c480c000c0d2000103803540c0304228542584a024001d110031030000040c05900c0d41c1c981e205105040c0105842c0a40002400240c420703020500409009030b100100410fa4a20b890380c813040d004100184400719200d0181d0752201a903209901000201c1c075003840801480c100511480020020140e56625610b4900c1d01c91a00181040000c0d040145000000700340501505018100c1ca801c1101c19071544440c0141ca0741000d81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 16218307 1250 16217057 16217081
    0xe0d0810060903021005031009020c030a0305060f030601051009050a030b07020c060c0606010305070302120906060102100603030206040f020d0512040302010905010504081015051003090b1605030406050702011b03 93
    0x1845030008240d44241c2c407500c10340340c0c018070411644035040c50071115a0000b4002c0f500e50866400300003081c500e02c0c8014900307286041c0103562034441010010382204d20040c01180200700e294041e030041da4000c920f050648100b1624001c100212000440f00181e080d00110380001550401005001c40c01070b0041c801d03860fa078226001c0c0d04000302444403074000c3c4c94052819030b201c20081141036000303412165005038545001401d00129840d150011a426110310360203400003003e0181c10750341401070440c00c1016403070510a0525540d0025581c14004001074000311042407441c0442d9200008030b40d006400c0000c850740605414540301403980544812404107600300b80002e142d5006109032804c07030358008007510880314030f07900040c054010700b1681e42da1144043c2001c12650f81f003803541d2051090b10b41d00041c1b5980c09180c003010501020b000034200824150b4400c00ca282d00c10201d03a44a503025102041075182c5c644142d002d0300b06520500d441e91403e81e1030302a06903141e40b0203c01e46003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 16219557 1250 16218307 16218331
    0x108360d09080f0a020108010911070204090609060606050301080727141905010b0306060d0f0507030209040501050402040b0307050a0207030501090308090d030c050f1c0c0806030709052401030e0d08 87
    0x910050130b5803002c080c10b000f0301080c80c03030b801080519069449600d40c8810352100500c2e001496001a0440703284c020100c440c27580d1440345d1814031a2a2041e500a8096804c1291130f550400c406c1036a00e40701c522034540411038034a980c0f015002c4d03070841607189121900b01409904d03070310340c0203c0d12450201e03100d4413880d0040c1100c4140d010140100382c122101c0007146c1e45943c4a55061160a610070702500c100c82d5100c0701140e03000c207928071955229208595005071940109020013064030010f9001c01d201d41c0c0180001d02601600f030080740d810417401e04046554032071102c0282d0410038180d00c081e0965180c240c2d044c00f4103401030881d80c41790302e006003600c03c040ba000c10141d08407200c00301c0680020b1000c3c000200184440801400c80b580c25101041c4c100402c000000290b6541200820005005005100460030200300c2c02010341900001408145002e1a024222000c0c580d00d0200d2000342e030303020480ea039000c0c5d4801040b03104244280c401080e000c4d40040c2c804035084d201e40c0300b080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 16220807 1250 16219557 16219573
    0xe01020904052508060a170f060f010504061707050108040c0f030c0302040509062a07050708070609050111030d02030406062c1803120403020c1002010e07050108360d0908 75
    0x180700d6604580b04107002450300e4845030034110380c401c7c2c0110b40400c4460300c0c4a681126030244d034080000074070400d02510120a158144070900c81550300035806000003101402e455600c074a000314440302614020f1a04010b1603030b0742d0802210202040d4001950005102000703c2440040c0e1448019280203031814000303500e8414000d65203078070480b03e0388000c841c1500d40d0580301000c0c800031184212001c008170300b0301e803458980314201101c13540400315950205004000785a0000003004c01040242000c84407403009400d420380340e10400c60a031404580c0003001408110f419440f0601500301c08101040609080c0e8041c002c030920400101d1880e00094009011480240400d44030314820501450500c2502ea802c40c081080c0907200b00d00394082c030881d151243c2c4601000402c541030503030003c00c806000240303071400d04509410581c100003109040180c040100621845140018a02800e24444010741045180e01480e0b4442240c003840810100d00769100035080c0540f007118060351024 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 16222057 1250 16220807 16220881
    0x2090f06070206070303090303150603050609070c03021f0603080705030a0801090b01020c040911030f030a11011401051c05011d0601080307031704030903020303040e0f07140d0e0102090405 83
    0x24003078040d0003584100204803502c006840394100690841c880d040100c0c4140900002c020b03460800d401070307000290f94100f008103601c0c0921445030080840c0c208558003165a4900030745524283e000112045e0b06403030880d09148140c0c0c0290b0042d500f121702507884144502e04030751281e005203803080010346c03a1000030407154910b105200600005800a04402034010140805800b090001740c8400d511551600e0803034806002c00718084e5031401c0956507078503c5001c054402540d207203061b40e15a14007085008078241101580e0305581c400c8811240b1180c3c1503205c00b1400c0e50340440200594207111065404104000b00010310700d06140c152056607880d41c80555aa0041d0391000d000500398281c100310103058500500d0700705000f450302030121600e0b03801080c03465000381d00503140e640030541000940a00151a660000701d0b07850040c10806a0b5185800d240c003500c10b0754031100355114031000340c00c00250304480703449402820070320051914403002d000c0307200c41400740700804044200124031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 16223307 1250 16222057 16222069
    0x40606090b0a081b0d08030103030206010513050105010c0b0405010f0e010b1005030c0406050f120103080304030f030c0206010504270501060f0503070e0109020f071a0108070609182a0302090f 84
    0x150340e12400204030315440304400d02c0c42e101810044036003100c200c5e1803060200b10580c4c01140a58020340040c0081e504d02000e010f032046880440d12290703868032005000ca0f03079200074240300e0281c00800440c0280c549040850061508540e684d605e00c0ca03095400c000c4581c103401810640104035180b401c40f80070413105443d28401181c800001100c10841170000501442c00f4110200301c07140058248075002006000601c000c4c1c00568110b4004010001050350084640d5a0f4030418a4140130002404c80084d40e03403801030080034803d0b91901c400100e0801850301920040c403107004400302c09031403818a01e00803c6035011702a0a000c40b001c0224076824000380580c04c07900c10f0022100f175607281000610013900802c040907090b020421203003002c03e28500011400141100096285500d000c043c0b502e80b0f540da0707100c0000c1c0700968008010040c6103103c5c5141010002902144c0481d001203000728030f0f440400c50055010780c595146001903850b0740900784107032003600d5200c1c40c0c10203a410040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 16224557 1250 16223307 16223309
    0x5010908030a02030d0e0a0b010f0e0c18090405031908090709060b03180a060c1d0307121509050604030c1205090607150b0603011d060418020904051005040606090b0a 73
    0x1001da8400c1284501104166000308005800b19041c0d9554044523503603100f0400e02039103c0b4215070309000c01441440c1010502035000105242c8003440c02c002c00c8000c80c0d042e01103820380c0d841159000002814004240708403511107140c901910512880c0f0080601006000ea404411070322847c04085030030f09140c82084190360300030b0b030028210361b646001d040c4d81c031085025285180c0030f08050640058842d0103260083c40064031440504005034240c2202001d5203c100e51082e80404002c1141d00501c01d010100140c00a500301942c0c842e400022014010065008041e44290020070080c5071b80a0210b140c0180705681110180510001c02c46407809604030700390b8000f00812803500000d499174a10b2811000d00000416a14881c90000e06160426803021400c5400c0e071000008842c214040e03c0c4c2d01a104a4040203030818655941008440e10346000303014900c103c02150502c01d041140d542c208036912001e2249162603d0210301820f50340c4101c0e500582003801a001600c0c100c5540e0f8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 16225807 1250 16224557 16224577
    0xc02150a050411060a05040e070302031e040804090e0a02060c030c06070905210c0306041202010e06040b01030b1b03090a030e030c030d1b061505010906090806070c0204020d0f060501090803 83
    0x40d01504502c04c2048990002403a10240481084009152511104c00e42d218000710384005071686400001056021000840307000b8845c0c03988100070010340540103443c1038070881100000d140c200d0041440c83c11000c000083d6001c4008100e044903000004002d00308038120406860103511041419a012280d9000e030661103901e10304081703100c60b45445101e51007001201225250246031020070308040c0250340645a82806000c00ca5860750240204035084200100410452410fa103030107103104010300000b400d9401010116100a00720000c940d94480d81454071941c80c20000c180658540c5c0c7c20f2012004140707001d132110a10703d0040781e0f4007100c0c4806005841028189101218a20740d070408114113101000034820120301c3d548556421b04e2100d41d420a055070402c0005459080c2940c000410041022070030f1010b504042020358101d20f080c14001407804030742c80028080d0182c1c078546100741d482e04460803030307080031900700c2c0e0f007221000c5c1c8070700c043c07213407100b400f01d0702c1c3c0c8914040c030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 16227057 1250 16225807 16225823
    0x30f10050a06020312040201032a020d09051e01030e120408060a021c0b01110a03030204090501050301060f0e040c050d080a030c021c081003060203010f060201060f060e040209040e010c02150a0504 86
    0x1038481c400c5281d5076944280705140010380d5a000740501743c3d580c0030030814ac2159840510001048a8041044002c0d452260a149000c5450b0000040c60040040340d851444440e4050214203039000c3e40107020070718160b4055030780c08070503451000020f03045071048054500c2074001180703440c03000e8800c46c0c56022500703101c464207401e90881c1c800508041c0e00028104500f0500c1118001c40c03d000000320310384640c0c0c0260f43d503864420b000c415103006030081c034401c0c0d151181c108103041c0020b000800300e03071940004003100c2d5582d040068541c00140c0c4910b4018566102250810280b04020b00d800781040e2000c00260702c010b902240d40e41d442e0300240061003514410b10701c02034000c80381d181c0d0203070742c0c1c540031060184c407a03803014280e07002070380510120010340e88144403254080c0101c0d0302400c1d000744100c06030703460440d00514210303070508128012540000e00204946a80e0030240b07192000200902c480007500760f0080d515084584403001500749003010400c040c520b030140d540929041420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 16228307 1250 16227057 16227067
    0x70b06010516020405090a021e0d020d03020309060307030606030c080f15040204090903180e0606070602090d020406080f0c0108060307030602090121060e0603030703170c0d02030f10050a060203 85
    0x5441940c4801d20b0241c250741d0a0b42244010380c2c580c0900c501c01e0120f503003c1d0101020320701c1406258a4841c1611048251503110109a6102c00b1907035040160129528590f00f0161f0405074210b1003110083e40d0001400001c104909400d07402600440b010382e5002c11250381c800108642501d01550b02d904050a5440800c40401c8003005000c007020008000502d000c7d0317240d43c81b500b2152140c3c01100410b06040c0034040d0007407044a40b800806110110100500d419030000f0007030300c14424010819903001c1050740761078446601c10590733503501501c02c004882d2240301c6150743c3e282d001e0003103200b41700e03603141e0f00042c0d480365010500801f00a03000301001c1e03080d5038070840a03404c5581524100070301000304090a40600b01d21983d1480c80010004400781090380350b0281000c0140380c903000390b03c10429100000c0c0d0207080100d0a03c0c0e120320088081d240c0070b40c4081c1611950300900c6121340040144402036621341c1c242ca0090354450122000363b544c41040c00880c190318480c040c003580040c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 16229557 1250 16228307 16228309
    0x20a030513080304090e0f0f060a0f1407020a0b012903040318030b06130203062d0d110306010611031e09090c0d0e0102031005010507050f0d0f1202070b06 68
    0x1410a09a111030070300020750310750102502d15007007540440034841d01c900c25548101c005221200d9107802c00c41c090450490414592070340c490000e028a1400d6580b1540c00700702410b10b901010000c40c800d002d021070350900107002551007100c0b04054401c1c5184c200009402d05580d040e040b0484040c9462060303070300002020a4003600028415000d00c241d521075500f40c004801e0801c006548540d005030510f080800c10711003006030144100030024810000e1115a55840b02c5d202d400610800891810701c0030a200c8090341c0c20a8042d070f5410180e0500c449041110410000d0140d400540854074907a80c0c605080322181d5505503580c030160410060703c40210700a00c0e608015002101d540c078500312140c00451011b0031300700c4d854003901001182014507688176024424900000c04025800d6042c07100c2c1030319031070100c1c1c4203041c1071102c0019440e04101b41803100e0340c0d03185407c106642680d401d091000d04041400800c030400168010824000800035200741e44c105ca8024030340c0082030b59418 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 16230807 1250 16229557 16229567
    0x601020c04053402070e01060c140106080f010c030b0a0302010f0f0302070807030e0102210307050717040303030506090108010603080409020906091203092103070b040c030b010303020706080106020d020a03 90
    0x40c1030000740e00c0086007143d05035005521002036520880c0b11242002200d03e000030f04001c507641064107140480001000016030198100700c0003900074241c480f51030001b203217090042045a00000e001d00908441000048065004010f80c0e60207403410f02655480500704101e00d0000d00000340411083c3c1007c44245125250782402048503040051802070a0b03111a241c40d009080c049002401c1c4080c2845207581c144292000c0005c0c03104c2c2503031001c0302581045098003004003c102000b402280100500441140541032202c1c0001080e540d10746078100180608801c8442d103028400540c00021240014883c9100302da41003c00c031411300d410514908040d511100d03400d0340c402400e006800195840c00545841d82c0a500021640c6010000900045c24003614000b00d2501716034082800007903000c0b04490800740c5c840c1d0140126a1941350032101661603810161129551710008420507400144800550f0115110034050380ea0f42c81049a4900c0d0104ae00001130b000340c400000000e00507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 16232057 1250 16230807 16230811
    0x1030206030a09050a08040b03010314030304120e0102030702090f0406050108030307050405040b0111010e0706020f070807050907110a06020a021209031c03061e03140304050105070b0604090209041101030b04050601020c0405 98
    0x134802d90760b13845456294242036400075000402d0140c0d001004000300a400b000c4016042d500c28060340c00c501e0306445810b40c1150000c10341050100f44140040b86a1091080710303881c640c002e0001e03406040040b80130b034082d0b204a404070b50440c80c11001148038040041540c0c071440441e07075010300d014240000d100180c80700b1066a03051001454200070b01d17940a00030040381420000c010410646403240080c075000384000c181c42190845281808001c00c0072481c03500351030707090f80c580c01c17180c0740d042c400c90321700e0700c454036041c6680610500b440402c203854004080303000081d400c4401000c0c041d0300c3e041c02846140050399050b4010381e5980000145200c14094248007401d0015041e5a80c203018440b00300f01301a2208000745412003801000882c008035a0080020340040d030401e030401002922900c10824090105c42840d80003840641c1c43d074118140c59a4045c103082d5541c10549400c4004045040c0e426020078144154049541420b03c50940300d520f05070300030500c00c075500c010300008046c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 16233307 1250 16232057 16232063
    0x705010204030b070518060405011220071212050c03010504051302120f120c063103091d070806120106120803100b09030a0228090b0f0901030206030a09 67
    0x788000804606010310782c0d485051580ca503140d130340214914860b003802c20702c26001c0c415039041c40144460390740544e1003035540d0110100082e0706040400112102d880a0030f11203184140012a5000c2020070060a882808a515158520301c0310304100016a6012240c2c11503150041c130041243d86010381003150040c510321022580e480c11a0040341800201c410303014016803009503070480c2c90707004010100902c101040410308103440a1003050701c030000500b14400802680411401c1c101055a01c021040c0400c000c1211090071407401401098452242107001c40c44200045152205030103a64440c0c0070681d500c1809560f03007010003d420f00d99040f044500c0d9a6078502007600c909108550781da440c00b034a41aa20ba151191602c1004e05140d003020031852401d108880c00ca0328002980d0281d1641120340311130b4281c084010070364900c2c196041c028404c100c00c800080300900ea90240e03009002c243c41519401059a0034402040020320009420070010000074950401581c000320356684 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 16234557 1250 16233307 16233311
    0x60803070b041b03110112020c070504091403070c050901152f01060308030604150303020a020121050f07030b06070309090207141c030c0903050309040e031b010209040506010c021302070501 83
    0x2140c001029100d0100c1e00200c0c5d909130840d800041640c2c1013051541301540603103065140010141c4070b141c40e102c8500c41d03207000700d4880406604010f07184013440c141102d42ca0489441d07100c1400c294000c0d940d603108603801141c02e9000498034501581c2c001c100a080ba440c0c0540d580500c0401007503002d00d50340d00400382115110706100303c800a0040c4002140610f400d030351242070680c1000f0444802814414407400d000b00100000b0303401041c21000241c090030b100740b03029518050002010b00d8070307060051192a01c0100041c40b90b80c1d0001600820456500304000e15880003800150702ca40c07080a00403a1540b07504100481d42c54004040c02841840880e507554000c0c17580703502d80481c0c400b049100108800a0110f02503152152a030342200750301c1c0401c2c00d6882d540ba080d03168460b1004050007603407600012182c59100b001290b043c101d5140100c44002100e20b043d6000f50801411f87c0c1c400d9003450086202e941c800c0c1e04aa40c1560010300310050261480c2480d0001d510251003110f60755 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 16235807 1250 16234557 16234583
    0x3071709031002030105030c010509030d030c0c060204260303090c13020c0303041a0f0105090106120905060106020d030e03030606040501120b10050405040c09080606061b07030c0f09060803070b04 86
    0x41c80c1446050010307441c248025860394100010913081c800d81030043c2e810013005022500c070075600010030b21107a011904000810050940c8107c5100a40c0c900c0503100e24000500041d8600c0d00c1c2030426080020800c00e0800c003d40744040799102e100c01ea82c000001c3d0f01501428400385081003440c07404644103813005140020070700380300307041d50030132201690100d0b01c4041c0c150160420a0705a9031064941c0150080f942c10840090b05409041c001d517020000c840c140c04070854220340c8007228182e04102199102c1da5034a030025500c2d0038185a071030000e81054142600d8130f40c004141da018007002003405050505000c011903070199035050500d640c07a08d0760041c0c1e219860304000d00d0700e000c000795034039961075042009000035690340306100010046440010001d030140402c0540c2c10040c00c48a0b25540c004503840e00c42d0750170320003851200301d0003514400410008846c0410048907040e203025103040e0340c1c46ca46030781180e203548a00030003a0010400000022034001f00700b07901a200790b800c40068 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 16237057 1250 16235807 16235809
    0x30209010e01212006070b15030c0d0b0f07140a020c1810030803130b0901020702040506011403010308070303020d020c010b0102010f0603030e0f0109030215130605070503071709 78
    0x2202a8000c1c62020808001400390504185106412012441c0203408150303055560b0300c04051088415154480c095445800300d9840b0400ca501c8260880c41c1d0300154104070b8851200c0b4941e02c00d0451291140d960b2a50443c186482c4000401e60051680c4d406a43d8a00610042445c020f150304d00b044034061270741e2600d60503031025203940e50050340100b01c40d00b5114180009150f01580342c00000e11210108014000700036140c00a40f0f80c80444242c598403044205035243c0c110040c02000711561004002503030f50158084d2400381d008880501c80750b16060010b4070f60743d0880c041c120103000100010300205145400511566100340380051402407200100307402c80e040000c14404907511610720046640c1d090140101c2d100c03803106c1c20040b4601d50354000e001c0016801801d80038000c200343e07004041c0e004078210310095401400000f800c8070141c07180c50155200806100700e402202c00081205441402944e030510342c0030b0025407a0000680340d614140600c885440d076206420002e034001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 16238307 1250 16237057 16237069
    0xb09040c030201020606012f0304080f0109020f0907020703030509010e09151002030307050d090204020f0708040305010e0303160e0f0a0803070c05030102090a0b03040303060f0308070b09120301060e0a0302 90
    0x2086008984180c012800c0d4400241440700c042d2009041051803c0c500b05c0a58240c05a201d20b40140300502819859150300103003180115400602140191204540143c10641220041610844074803540200e02d000b0020000f0095600b000182d01c521800d0001a00441c010400140c3c141408041000c0c03a00020312000f00440e040c4042511004a14a040c1408900100070513214009507055107850b0200034018010703e13400001d201e854404050940d11160304442080202149140d0b44403c02e003000303040e80d40240f1003103c0075803030252000403000020007602d0280204101503584824082e00850f299007184903441d5200d0301c0304290302d40c00da940da00300348010404100a0760702d4035050304002d040c08459070b21a50003640104030503031144c1d941e60043c1c0c080d1250648805d0726601c2c0c506046001323003095080b40681521b0300320084244100d41014002241c4250341d903001a59845100c251568042c6c400d50030101028001400201e004100c14542000003500707442015640e5000212 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 16239557 1250 16238307 16238311
    0x2c0a0b060a03090605090106140d031101020d050103050d05040e0601030504080903060103030807020708120304080a120504060204030c09180204020903030c0102030c0c010b0109030b0411010c050d02070e01060903050601090f0b09 100
    0x2181c3d884200c081040043c1c0038460340003002c50b000704480b502d00f400c1c1e180c11010b04000710380300f42d09110581c010580104d400c2a10582008021501c41c43c00e00e0071003000340030a00043e03a440c403403045900304480c840c00885041c0c44c000600d406850b11184015005000027800440c0d10305802d0003201120f481c10840c0f180214021f9072098414141344d5401f909124450300800e8440e088001812846419202200d402640c0004542ea980108440c22540c4603611444958441d007040240700511100fa005001540c1c0920350005026981d440f20808071814804d6400000700b502d0510700241c0f070280d010309a5000b015059918207801612846d08a07401210741803100b0380e020a181d104032809100310007081b802070070003c10150440d1186030003003100507c0100f12400d174141c1c06509920a591403554140c1c04400c842c1111441000a5100d101034000d044040c1c080c0d400014809205500b5101104e8010018007101d90030302421902410b4010040755003607407280c1c10307807080d0380754003081074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 16240807 1250 16239557 16239577
    0x90509040804060c0f080d0b0901090e03030f0c07020a0803030703050705090f01031a06070b090c1203030a0f0617030c0d02011a040b0303090904080304060c030c0905010f12060902132c0a0b06 84
    0xc0c8c0c1c04e002c4003000801841070b000b5400c25854444014548500002120b42108130b4011090b001c1e0f49101c5c02180c00d20031240029000f11440100003110071000001e580545403646050080f44d450040444032402400c80d0035921904882c2c0c1c00d00ba55002e644220010305840c840340406000c2e100100301107034000c1c2000c55000302c0f80300400030891030031b10034005038a0003241c0085207201030707000d01036030703800082d10507aa041d983d020004070102540c0d0000c2c000306049410308504200d410fa0594a94000e0581d4114a0003160b0007050800d00c10720604003030304103070f5030200a0409820144002480101c030015050701c03007000702a555a42d89507410784514414850340750380e0715040c646001611800f04240c07040c14200408000c042d50000c11031b005a50080c60300c001440b4001100311140800890070480140c5010f6012802da41c803a0010b11700c926081d4400c0c0c035102d5950030301207210b40d0400e0950840c0008030608074203444000b45c5694104141201c0030031461004400182c4990041d0040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 16242057 1250 16240807 16240811
    0x1020f01021611060f04030305180301060611060901050c0d24030606030309060201020901090b07060f0f020901030c0216140307080f031e1305040506030f010e06010501090509040804060c0f080d 85
    0x300003006070030003250400b043e0503980c00d070820314082450300e03039801240001401e01c440810701d1303201045003444da10304c0d460b8020300070300050340c0d03820000d0040c070681e130302d015070038091200024a141d00501515009103a100200c914003070703032819028000d0480c00340a444081040c950121010800241c00c0d01450007030400040301451440d0240081c040b90b8440d00942e401442038102d26078018026108660007a1601641d4201d14548100140014450009500d1501c016100c0c1d150080d40581012002030b2810400c20940780402c2c0d944074190742c00e03440300c202e600d04180004482000482076010b03001c4e040324040c41c0c4683c0303a0b41c24141181020511a800807400c2d5003120550480d4142011040751414a01421000f0f25424040709008650240c0c2d11007010840d65142048419078512400c1c00070020301d40e540505a44500c005e205440c001031640ca000328007850202c91030b90141c0d500454462500c0e18109043e980c035020020180d810b0305028001d6008100030f50010081c0c002c0070500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 16243307 1250 16242057 16242097
    0x150e0a0803010e0916030f020103060b071104060603020c0604020d060e06090d03060e01030206090904081b100b0f0616030c02130209130e0d0513030512030106030c0804120e01020f0102 81
    0x446600f410300030800304090748000c2d60600c16407013002e015402e0b40c3d08900502d51b942407500041e0043d00181d0300c1121045400200c1070284140c030018014000001c0390b00b03016465840e84102c05034018a082019240c0000c07010070300516002c26403c56441c441d0b0340200707400e07008110640c10f00d81d04480b018a40d8102c0300b0280100d0340d0500c10381024010038000701c545035066402003602409180349540c043c0c54605c02003418424001c0507150341c0c101d00380d2620b00300301010600940700c0d842e104082e0103940c10968003c0141c0b410388101211240302502e458244402d03a045141c0303040060380140c0910441010075005602c84400c09180c000020b038000d42d9a8802c807051200c0c1000190040b00700c2d82c5800c400c03417410031300400e14001c854002e1070116110710344100d01b000b45400c241d0009000d4828400c80c000d4122403600554101d03061510708100b80444c5110035200d400d0300312001020321800c80c070703605800c50107811786811800e01841106c140a45100e021400ca0b484842c100552401c0d01e01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 16244557 1250 16243307 16243319
    0x7030506070e10080106080a1104080d090e010b090d0c080d0509030c090106140d02040f090c0206010b0403080306060a020a06060303091401110714030a0507030b1e07020604150e0a080301 82
    0x84003480e04800b59110082d48800790750081c500c40c0107003d12405c1240b113002064280023503411002c01020302100440e60703140d4400324180d944c038001c008980803524070003001651244a2a04d28121009115041d18114080080001e241c410300c0e0106c80b0003806400220311510100302050f402280b40d2100c2d50f4038540d0104240c60000044e000034898100e510045c096540e000c0035a1a118901c482080e0312010560002c1c00680900e421007020541e01800000f805056500600c06d458980c1d000c0e5500d40c2d0300d40c0200e1070030380b00307901018050106c1000410b085003082401003000344101c0c03040c1c1e002c0d09042c2c0e4988003070701c40c154030075000580410018020705a46000303c040c0303203501b401c06d80d150790190001592500340c2445402c2d442140d40700201210388060041040c0254050300745c0e81441c0d12403800020a4905907070306954154016100d007070740d00261340228065401c0303030000d1280b0f0781d0310f6450803224440f15050096041d180e60306110321140800c21445114412040e1984030342c1010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 16245807 1250 16244557 16244567
    0x912030418060e060f042003040606030c0b03130305030703020d0509010c020c0102010b0307092304050f0c0103020918060a0801020d0605030d020c1e060f0a02030702040b010513051e030703050607 86
    0x50403003c6142c000005001c100e43c0c601007900e0720300c0c006460200d0941071f4400041c0e46840002a41c14032503400104000030011a544444142e0f481000340120003a00d0300002112030000701c1d1b00a4071030184100c041c01081c0594003540e0f21460a00d005441e10019146000c02d40d90150381416260b0345038102a041c041e0140f21900c41d4001c2031000f003045a1090002980e600014465050000d0ba15100301d03614a40d00403042607c00c404040020f2242428034285541d42c440c00308816150041003401c42c0c00d988a030085480e10030005040c03201d5525001c1d254140210081c0005500c04009040050200b43c280064070101c048150000740c9145890280340c00c0151584126045401105240110b9560302d031a20391040301804050243d80e080001052030b601c110411500343c001c000c107500501c29800001400d0507032090300c0a100005130074006407454010720180d0b0307003102c01c408818022403c06840644c1e00e0300341e25902d8958002e42d00c01083c180900c0b9042036449800400410101135084 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 16247057 1250 16245807 16245809
    0x605040603050c03010b04051003020f0d020603070f14040f17071a0a09050906060313060b06070b07020d020a0b1f050604030309030b0108070501020d14070204060b09040f0b090a02091203041806 85
    0x162070603c801c2c927149034128000c14003800000d05c0b440104600780e400362207510140c0c0711a903000e00180e641e41418480500901a0044c00300c2c0003079150182190342c1c0d0b81d00c01c02c0d03034200d82e64880018500d0b403d0090042038130000400450340e0380b02d8030100140080c1603150a9412880a40b09507640d4409002d00420b0070aa035082503014072030400070b000180c0c0301c03c000c586e4403402d1241101c00513580791402401406441c040198030030004602d0f001403001a8503828000c00d090f4007115000a07520400b0b80c0c50303c5040d84050000300b120400621001380d4410440c082c0c0d000011026829a1120b00240c442d4102c0e401c01d40004a9000050040006144165000d014014010b01003240341c640000c0d0766030705504440c02003010b10a0840600d0028005440420368010810f20920b912000c40320210b07000322010900c1907040000c51101c4141c1c6120304921000b024287c0042c5a98175003c1801941c80072480d00d0704000324420a411310141880500058012091140e00341059401d14806a40349 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 16248307 1250 16247057 16247059
    0x323160203041503090f0b151e010f08070c080c0f0706020a120e01120c0e190302010914062502040f0c0203070201080a0e0304060804120806030d0804060605040603050c03010b 77
    0x40200f80315500c24042d0700aa15110307803030007040c42d80c01072a10400013506807400501098108080c025140c0e000703506664940801c0e02c1814444000000d0044a100d02d1030416011500d0407003585c0d0b0491040312402c0e440580c83c02d120520002c01d075100700c506c0c0d002d900c400200b500304010100d0710400a01129005004034401007940d52240d4403541242001c1000400600c10f4514200856034011704d560800203e010700c0810040e180b03c040948080000c0e16000e1161211a440b07038036810015010a080c2c81e010703540c10060130700340b00b4118034030b40c010341407682d1042050100d40701c8034100c075480b9860340315908131800c40343c4954818042a1204075007100c1340c86040c08011340c3d4140c1d0002c02d964a1903024a000685500c80b1002e110040250407440251804005000b04000c0c1e04100028080c0c2e03c0340c1112140107490700320864845100342c401c03c1e4550400080c52000610640c1100d070843d0064100182c82582d4000240807031300254411202074105e07040d944550300e0300784212003803060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 16249557 1250 16248307 16248313
    0xd1115030103051f0902060c010504030305100f120204181a0705071109060a03080307020109030e040507140315030616020d02010e03041203020a08070b0115020c030a030503040303231602 82
    0x10555645a440b40d01d404000500405080c4c0d94a600d100c242e0441603480d40c014280380e42d00c0700301442d064040d2004507020fa0200e4103000119414140c1020024110f6132640b118041d07481c10708242808801da8010182d0b03200d81c40f41d0481000042d006c00c100e00407481080074810505a01084032030a84000708420b0a00c58107000d0340d40801c4941c40741015000048400b121183d6481d0002052174541750005070840c20040100551960154402809240070f41c031600107800c0058200401c1c2d0304221aa24002200ca01d030500071300e05241d002d190882340c01044a43c42d044031170301107845c0102c1200c2022000400309400340c1c103940c0601405203048001d100034000b19034961030b2640d49100390f03c500c5203184003801907102458824420700048070f600a45030ba5880740d0310304006800290a0003440300d1104002410302040380005074802d10301c070004d40600081181038a0176101504004c0055013456199000e000324600c00d070450f507850320003410311405a400c00c071700d40f4070301c9601c0703141c0750702c1594 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 16250807 1250 16249557 16249559
    0x612050402180403051908010906090204080a080715020f090132090d06020f090f0a030b010e10031a07020717060c0d020f0a0203090301050a090308190204050d11150301 74
    0x20311100c03803000c880900c490741c0d002c060710b4624048900f0b1003009410318441941c0d40005240e01d501044080c121071013080706100c4591240d000c20201d100b01d202c0c2501580c0700d6908170380001c5003c0040c0c03002a0003500c2d480d000344074181220090ba4014103100707004407000a2641d0541d078005c48039806101c9a041c007845400012507040c824140d01c8444441418404203500c0c603075641c0c0e602e0b420444d41e030244c010745d2500500d0a5043c1c0c2504600075444c801c1440e10700ca11054184035a03040100e07900301120b0345150f481c114600c1d444030300107003280101000d86840440440c2504404030020107903041c580c407a42ca04001c000f8100740b026041141e40050395400170503005000100e85070400c5950f281039913281351580e0106d0007803260441260700404d000c2001145507030003202030508103805a009005940d5107205100c11250804001401300e0005c60204200030000d01c90601c1c0041030700d00c010f00e05500c0700001a158032100300226610f00c0404000c0c01e69090980e020b00410605c0034040d409d43d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 16252057 1250 16250807 16250809
    0x112020d02010c05031605010603050c0108070f080601050f070f0209010509070507021504031202060915010f03030c020a1a041406030114010c0c12230d050d0c020106090509070612050402 82
    0x100c03890890107810040a880301c1400c0c03110500840d1041954040c605460452a20740107010740309170b01c0705541c503028003031001505500800c0080d21800c681d0392000440742d008001541c0801d0083e0115040100c2801000001d401040c01040314034059860210001410710400000103416000203000346c0c400c006210a0b6504042520701c10380c0d044801d049914420806072895004680c405450030200b00020a5090b401240d003a00032039000b0265100c0d064015000d402c40301d000c4c41880703404849903500f00003180c070a46110032031a2004080a400c107a899a40c04096003510241c44003040d40010100804401d4a10348030b00302c24280c1e9454115807400404c12100e03140f991030b403030500c15581001010404191002c102503c10940610056882c60501048224007070b08040301c182e0a0103996099100d000403680f4030001640c0e94645482400000f0f81c0c082c02e00c100740d075010b40d074842c07074003181121071406014461a002e00092150a140c8800240b4015031100e20b12600c615100500c405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 16253307 1250 16252057 16252069
    0x90c0102070612090f02030a060203160c11010f02031308010507180e010303030506060408030307030c030c0e031c030e01020c0d03050c0a0503160c05030c07030506070e09010e0703091e0308011202 86
    0x5900c4149000904c00403506241040402d000f40003981030140141510030031120303a01070340c01514070070401c54400c524080141c030605654240644401030280401402c0c0d0310a003c1a5140c584610540b41801210684008810380c16040f64100e81d440d0410054081d46c080f0715196140540460701c8400e46c501910504125410301018017050b03290030003d652030b1540c20840317000306204021690350f03140c200d00040080007008002c5000900742210308507054896100c0180e10700c2d0081c081d0010041c82491300da5003201406090b018140c0f43c894134190700800b03102800c91041c504016100d030540c02c00303004084500040c850207480d00c041c0204550260710005595000d841c8203450b008500520700180d47da00d11040c40202a840000b500b50014403011032140102c074414001c5650540764401d060b54003444145841d500042c9020040106000840c00786411500c1c0b4240042d401407240c0b962508880c8910a40e00003c40e440300310020142d004510600402c0c00f0300c44c0c1c215000780b039400528 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 16254557 1250 16253307 16253327
    0x60c0708040902161401020301050108011202090f0a0b0301060608060a0f0605040306020906040504020301060e0909190f02120304030b040c05040506010905060306130216051002130e040f0206070b090c01020706 92
    0x2c026980410301010b2607807142400029190801c040708521020720310258003039802400b503d40000c07042c100015501c0102ea42c040c40d0319900030300b5591982d032244044403107094004c280e01c0ba41a181d00682c0000c1c0c40a100d142c020380040d644805841c601101840081c0c10a42e00100c0c07804000740f0300300401d03980710003034406680e03000314050780e40c0d1259070000b9030b68081d90708019031040c0300000006d000e64100038484050b038002d0300d07084030315601d6000c1d064807000c0c11082d011184444001030704c00a0030322001088840d1004041c03c040404020f146855034110b0b82084401c1c3c0310300024442071180116001c0000e0104403001c1c881481c2140008020b00340030f00c40c090007110302001065041d0740318009800f444800c54800c41d103030386039000750807500300d2811010b407614040d145000d00c04035528021201d6407401c41d44100c0030719180c043c0080402100410a54001200b00400c0006030f0740c420050060601924180c00f0601341102c0075030800c00e83c0f48074141558401c42041200c01e82003182d583c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 16255807 1250 16254557 16254569
    0x120703080f040303270210030c050d020d0f06030f03021504050703060203070318030207090b0d080304020603070c050102070506061512070318141506011103030402090415090b010602060c070804 85
    0x2092a101c519054001e0441c074030404d402c642c02c0d2000d00c29440501d206081905000b118000e44401003884268100c40271180c0450010340c040010230940205030700140483d400070500041c22840e9900700500b10f03000d03038104403500900d074280d0744185130303041112442c1004650840320345810700c2d5840301c0d500c4a492200814003500800001c0000d4000d91026070149038007814503074100c40c04d16000b900d44407640030340f0103040d00d400910525400c00301400085e0540c01031000e442c54aa039000c10150713400090040e02000070f440c1c000e100044c000e00180c5100c03072040f070082c107035401d100b02002443d030202001c60901030000d0011030040403000f4905d0b030f0014580d050000e04040400450080030305030b0300f0081c2c2140316101d541040740340c0010b1449a441002e80070f28440351100d00044a28544070984214941d0040c030100d00585070110499803c0b501c9880960081074140c4074070011384400c1c039400d82e0705c11014001000440d8040c40700c254490b80c002171492910740c8030f50702c181550096004071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 16257057 1250 16255807 16255831
    0x902030a0e06070806040f060806070f02280f02030c0a0b040f06080c0313030e1002071502030301032315040605040506010b0c03040e090c04020f04080d0306060503040b0a1509060812070308 83
    0xe41c003940848e84004041c05515080c0e0350a4a41040e016051401200e50038005105241c0c19051401e01c5010708001c0c940c4110244001358880d407114500f03548880000c1c0c0e410f0095551042080d61540d5401008124455013281c655280840281042c442603005800744122002040094010701c0e088903400303e0316a85a010503222424102c0d0140c550241c5c01d41c020400007280078603144c000881500315090621040d08000707440f981243c481c0401e11004229105c042201c4524802d1240034801e45c0705100203d4a450000304401150b0100544050b00c0403913440080c001880300030710900d80909200141d103880d103402201300a5581c0710b1840780d01c403081100d1000c504c60000900c0700002620b0000c0c419529a603002e061410143c0c03062007003039214414100d80356415030207406800211011501c560f811561180c0315420306550041800c482030359244140c940c050407800d9000d010303010903c40001c0c19030800b00158136024041c000308003d100b0a020840000e039014514991000340310780a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 16258307 1250 16257057 16257071
    0xa020a0611011b050706060f030b160210050a09031101060302090c090301020906070c150f080a0b210705040c030b060304020f1201060305010c090b071a0705090301060902030a0e0607080604 83
    0x102801440d81d0f002d1912103400e5081d01c0c4030007980c040082c280c118003031002008000c0e650701502d200c02e90b06200041c502003400d400030300095007000c070422060000d13006445c451403042104504403401142e40050322a0b45106e05024554007090612600d04070300c1c000c00219007140c002801c1b401c402090f0080c00140011b072844075403800e405076403d040002d840c0a880704030501c3c1c19401c800003800703440c001001c11040210324901c1132000007050f24480d00c4015642d25483c040c0c0b400350400f50250b80d00a0549009245108140e080c03249015805001910380241040b0800c0243c42580174076108041c00c01140300c203d952088101c90f0840c0d070460316107482440f0720002c65411500c032003044005510301a000400c1c0503040d00440e1149642da6a0310b00c08581701d075503c03020781c011b00401074000303101c00601d80ba444803001e250b00d070001c03d20309015003003c0300d0000082c04c0d82c080b9008040e01c150080180001c2440c41d0054624808203400505003c0c503111100904e1510010802c4d48225100c0c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 16259557 1250 16258307 16258337
    0x902090102070b03010e0405010c0507030e040203070306030f060507020601080d0504050f01090e0103260307170402030c03010906020c010501050d020612072a02120f070b0702300f0a020a06 83
    0xc4000b0f1207900f80c01d41d184d6944c1c0910f02c04456041310103071800d508220032140e00c1c5214100701c0c3d41d526455184c0c43e42034140c0b20248030003900010500010706540f2203010010074400498800365a02c01e000100d618070b02108001e00f02a810390221a05a014038404a174454019003030b1400e8880c19203030000e82000d9480101e800240c2035115034003407195000003205211002d441240c820001c903010340e002d6101c85103182c0d103520085998034002043d0740b1010300d52008081f5040d8229000404803182108005c2c006400c4a0401000300c800590010f01d81040032428011680101000c441c000000b4503940c000c40c0007171050300040c400815018000036000340c0120400921a41c03121a201e07500720710341540301c0800c032100f9010307407144001c54518a48148001000e000300605100a844620302d0885501402c0d08210000c907800884490891003500d0302407110070144000c004030b01035545c94030420700d0802c8001118140075810070000c480c00342e101d04c0003082c2282e841d4504068800100c43d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 16260807 1250 16259557 16259563
    0x16140312030a0b040207050304030c060905090f0a0e0105070203090109050a06170c0c19020415080c10020a0602190f08010303021504020f0d0b0709080a050a02060a05040305010908040906090b0a0902090102 90
    0x70041541c13143c030204028041c0000080035009482c4174006180309182c94500582d4034040310b00ca5a03502c4000c2c003000555020702d805400303070448003031000440e8030300b0714004042c01d4a0302140c1c08c4005910100c1e141d8005d6034018511700c000d01051340c0d8002c2c01c03410264010406155014201290401d590218058403a010200d40160b43c0640c00c0e601854202c850284d0420600750b401d91299041280c00c01c4102e10803075054049550031001401455064402d00500040d0300102000f540201c204030400724040d40001d01c0046500c003290038070741c1000c0c03c01819200514031800108868a4014030009800160180951b80d01180000171a40da40c40020001c00401010075045032000751008104454200042e016260381e032982000c0d03984a454a559540341c2c1e00003c0e00542c0034001d01005818103100410a100030752030214505500c0751501030030345580040440e06017000203000c2000108a200310001380c610140203001088140e40082c421760303460b00800140942c00559415168020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 16262057 1250 16260807 16260821
    0x180105032202030a0f05030703120b03100e0c04090605071b03020a060b0a080d0e03060a0908040308090612010803030906060d02011e02030d0c02060603010606030603020604032402030916140312030a 87
    0x1e882082003807446c41d01d2501c0c0d8102e41000c4001c202c1c07240305c400030321450340540d0720414001b5000b0582c00c10043d021030043c0810849040c4280184460031605494030300035209034602500000c551401c01c510010003014111500c07052081803d031405002a9001c917061104c260860008580060960001140304401e07a10548040c0308140003000001d0700441c6061100008400f03a070035980c0c445c0400c409503102c0c104001c00c61542000144000780c0c840c409041d0400c40a00f08030b0501c2c40e1280ca01c404200d00f07802980040e4004010041040b03410040c540d40102c05451030400350072954000b0380f41d0000c588115540300103161000d1f108503c2003094894940c0e000740300b0711255800990207034130344205a030308034040d500781b10000c918036009010b120122640501250710380352442c0c440b018100351000c06028a171031807a403014a00302007400a14012401880540701c01c0040700000310314211198032025880c00e2900700e1401a64010510f68018070310180415566910161454010408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 16263307 1250 16262057 16262063
    0x604110706090506090d0215100506041206060902090a03020f0f062b0203010605090607050708030304030801140307210206070f030203031902030115050703031b05180105032202030a 80
    0x80410240140081074011900c0240150281c40f126260b0307007203541d2550b00001703400016a10031a8400c072040000c07008540d00483c0070140d0b4a00307640b182e002402d203a000d0b610081444020002c00c8003440a2071080200030860140110701e041d2070140424030050142c403010744140fa1840d0030a20a03181c1001c080e54481c0006e01166407041d5181c078a07003807589446500c40f018403ea0400400d12010703442104d060b95402c3e21420308242d410020003c080d8841e4100b00c40758050100009540d50302000654051031107a00c034101150b06114014201c10b080019561090f80700540821110134014680e4581c116100602e01c00b070005400403a00d140b04100000f05030002020f0800c080c1a40030001d54080d0f01c210405504074543d5103e01010fa00081c06608000c442c1a2601424140244002d260384e9209003804201c0d01c41c42220300121030101d80448003c9800060840c2002d00100d100d5003a024007400c083d802c40c20900c030130030100c4488100e603640c0d90300d030480201c05660f01000008003540e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 16264557 1250 16263307 16263341
    0x2130902120615010c020a030f0807080304030e01260c0a050c03040e010303080906090d050d06030602030a0c0f02010c020316140609100605040507050a140405040f0605030f03070c0b030604 83
    0x3545002079500c42c02222108900c00000c28101c039079610503100c1e413136215002803050f0f29003070564850f4240441d10030401c46031078504004810000d080c50340618441c500076247d40d00603000105c000340258003042254448500004660344240c81912403082d00203403408211a00c3d00584242600d551003200b8a01c5041d00c004600040c60403510641c1034140c03440303562440d105403107103c1c503a175a40c002958240c0c2d03941c0100c01940c0026129001800c81c0d0030040c5000301307280c0c3c0ea03510307024126441510a4840ca9823070305540354583e0781101c440325090383d040c03008200c0001e4120780251240101104010408584000312003444606100082101080d00076203400b410040b20003a9504080301320048001d0404500207240c1c80e1a00c039980c4030740001d49a02d40383c91161981141c8a84140d141d1121039030042c440462543c40d584284d41c1c4804401e0400507025007000c0405203090700d54885074009074010425030b00080c0218100c0d508840e0f07050f801540300d0315040c001402500020f0540d0421b90 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 16265807 1250 16264557 16264579
    0x112020d02040305010b150a1d040606030504050d050406090603090501020403020a0b0d0509011a0f1801120308010819020d050c03010504031d010804031409040b0306010b120705070c0302130902 85
    0x440c80e030700074012284a80001c2002c1e640100170b20580c0322814801141c964014800500b0b0103004a801030740300c0b034190201c4e4a600080800150440d03c054208100007540c41003080104007003006190015182402e0440c103003481e014000742441c400b4016942010303101e10382107042010940590f005545e005100c0c0700c4044d00c9000c0aa403036080800b0b003241c56824000030546202c018850347c1e0f40c60f039038809000b550180a03024040a10304000344117400840705002c00d0b15004603612201d000e004000000352001d0040c0c05d00600070b46040c0c202c110076030071007052454031103c1540c03201340d6a9030507208210080c81c0e42c20310301c1c20620b8581c8044c0e015402c0c4010803041540c401200d81b002c100030380c1481100c2c00c140b001100c030010211030041c00b003800020a0a036200c0e014010b0241c580000b00042500003400b17011908285080e8801406844045001c25034480502185644008a458468105051a00c8113000303143c49100c00783c0100180480b10103403454a8012460a07a0081c051821071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 16267057 1250 16265807 16265827
    0x1a04090504050c10090b030403050a20070501021203010e01030b09030c0304060807030f0203090703060f0b0a090b010e011107030615080115031209030308011a0c060403050702010306050604051e011202 88
    0x14203c2050b45449a0300580801a45502440e03003901950850110141503075a10342d800d40b819030020300100180040a805840084411010a034024041c2e201910440d480c0000191500420341c8920380c60200500041c424034528060181c1180d412101c0b03080f2640791100343c1c0d421846210030140290100040104940f500480e0395405a501d80d41d00700b0061800c885103034101d00061b21a1807050308200003c1000c1607094004034482c041e02007000841302c01500c00114000c4883d031002c1f451a8558100680640e00048125100e40d02824030b504000019a002503c1e61103501000b0000c42e80c0300d03080d40487c0c1d4072000e07800152a0480c02040700c507400ca40c0c80710f104515440112004c02151003080c03920780c410049030381201d600d03445401e1540d08101f002d4070440b030308940c2d0843c00001841000d02880c001c00515001c0c60007505c68030382e0ba290500005058444a811486c048d01007040200001d071145c5503800e201e210b00c00c424880081031400122500201c1012a02040380089040b20780b0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 16268307 1250 16267057 16267063
    0x503030901060e0a020f090f150a020109020405060306011206050a0204030c03050a0210050c03041a0903010c08040b0f040807030f0e060c010f0506030706050f0a020a0b0a1d0c0a1a0409050405 84
    0x15201c80b490702d02240d43e6522040f44c160302c220121815190400d0082108504100d0800f140031a802407410030400d68a44a8109a8228149083c0180c0d168000750302981054414240c0244069005d002c1c1e96041a050216180010100400240da81c4000442e04401541a9000f0f194011200c2140e04d2340d9050446d910300c6002d0003a44180c04286840e40c0442c00791080340c1422420700c002c0e5050a140c01200140518001c20b00056540200b00e120f2556500307200341072190301d4030303140c00d0748908250811111282d0000c0c03543c02d403a84401c0034000072507070080545619039803510303092410607641c040403203170b00c000d40d42d40640090f400b0a1141820030b040d00080c81071500100d041005039102c4041690b0350f8068811100403820801c0703035444001400c801071184000900480e04203421b030740d5a082007c00100d42d51000b0a5a4409440207509071400019000e01d00100500c07007001440f0004a50185501c00c8000c41d51040038400700c003c0c001c0c003e4800618914004002030710705410300b252 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 16269557 1250 16268307 16268309
    0x3090302060f0609010512010e1203040309080106030305091203090d05030a020d02010501030c03030503280204050108061e0f130207080408060603060106020a0b0703020903030a030f06060c0f0f0609050303090106 93
    0x40035006450015000301518520940f10b014002c0110a05900e00000d0254000c500da0322644155200c4290290411003046444403a440544086642e071900b401c004206414a400000c41a41040c4080020176800030036210507a4045442612603542640303a03034a103200d9082500e0b0440400b000d45418080c000c4080d0000c40007540030f1702c0c412000280120300726542400014090360b00039400b840400e103c5d002840d8410b0042000351940c40700961601c0308086959400e00300e4980005060009583c0603c20030340100c0141e95425241d00300b408041001c5041e400014010600c40e00140400d949200c4145500c010010f41107680e1a00c40c203007800709070f00030700504a8074031407100400c0b032604000488030704880155003c0d1a9180742c2c4d030741e5a84136080182049042580a01040c21240c2d0140024075004030180c400041d841c20032200c541c01d03100b09600a005104200c04210045600d041215032019030081c00f40e0024005460f180c0020058428060071910001c41000404001540702c0302c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 16270807 1250 16269557 16269563
    0x7120605041b03060b07020d060b060c120301030210090503190312020715060f0501020d03050601020c060301060f230f0310120b0f0105040504030c061509020d0b0a05060c0703020d030c050601060309 87
    0x40030003511420340049900c11104005c1d040048c0c0c10b880c0e0f001c24003c0d4040c03c0841d8000702030754070302101c454619241c000c0300a08001e004400000410452030404200d81c940605820090b40091034140007948a04442043e0b048118401000800b014450324110072118000306045450f00400d080803021440710503401c007070062401c100420a91501000c0350304582050303009182c2e001a150f0210b000c0c1c00082c050605522801d0400c089030380d24803020754007074a40d507078510b0007a1015400c001c201d58060300040e00d01c1c112010842c1c200c0702c030580c21107180c415015101950784e06d40b0540c107400b4010f030b80d220070300c4148842005c0d0100006140d01c580661391154520700a179032101c040001301c500a0ba0010b000c030301640e045800058450f00000c002814000700422220755580c0441c2c1680d220942200341c580c1d0300e44c482d100a14000801402904060350010305100720310310b629a85801c0d60001138810b403507052240c02018030608110144551103401e840180d659550b0103009890180e00031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 16272057 1250 16270807 16270811
    0x603070810090c050a0503061305070f0e270303010b07051501120212030310090b01030902030a0501050603300f040b07031e080402030604110625021002070e07120605041b03 76
    0x1040d00d841081c10b011b46070020301800c10303519040800c034078503041104210f45074080c10030001444440340c04050000c0036001c540b00c1003031034440c81100d00c9803005007561981002d0001700780340b200800000d07281991a08071021340e43e4079036802c2a5180c01840c0c0307101c07494051403000201704070f03454940c00c444080c402e55048070784034024009243c50380812500c0f025a4111032301c1c10002c0c1002c1d80c0004054080604000821948030f401007400c02e5515201070310706a4403402403001c2810100b00d42c1481042505124010700141d550000302d0040d007c40540d0502c40200e0901440c54113030342250004c1c41e0300d40006543e91035034030740600304401d18040b001c9012503803403403e113045006010240c03289a0003005004241ea95684500001303140c030007000c1c0c0100052120400306180100740001c140c0245064403440c0c0c515204200c0c84991302c002c5035045410140040010390010131364541c000340c050401d10000f5204a104500904071580540e91260420350414910b11009220b400060010750701 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 16273307 1250 16272057 16272059
    0x1030617060601030207031b03030504140114060904051e0d08070c0503070609110d1104050601020a0b01090504080f0406050a12020a022d03030106050a0f02010b10080603070810090c 80
    0x34900e009640d218042a50032000008600f5807190707005086252203402c01c94440004c08900902d4031842041c100d0100765202c0500c03090294075085418803000c1d0384003d2020b200c220f02c1c0d0402030712000d003165000304900400324007004000e0203a0f2040c0ca4604c88240300042e5680c850a5a925824032480701140744200402e003a01c0c0f00f500d64607440c5410000640c80c01103584d40d410028130128a0030307120300c3c01c10001c2e07143c2075684001c080c1e813040c000c1c0009100502d00408020031030b400504414199807040820400013001c0f4042181101c80c2d001000411350f4075820400e00e40d00c1505020a442d11000401180c3d564000010f440c241c10640c1e0b1f00043c0304110b001c05012482a0100e03000542c1c040004203c1e41d1405004400c52440e400d00d02c2b10802003c10f0703480e45150002c0c1c1008000c80c0c80840c01c0065942e024003400040ca80314402801001d50303040c0803030081c41c6960200020070031a0387c001001900e04000d5503008000d1f04084480100500305028010300922108865000c102c041c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 16274557 1250 16273307 16273319
    0x1c05060a06050d0b040213060902040f0e090604020d0209090a020d03030204032003030f0a050705070303020718061203050f120a050105031002030f0c0a0c050106030303140a0504030c29090a02010306 87
    0xc0030b03c0300310380c41141c484540d04e560f020003c50858280401e00800d0b00c80c1d0300400c8065060002d0b10003802d18801c01004103080c00941506e9400003000d601c040d90010f010000582d440709110003110341c0684100d807007030b107607181187c0c2040c00c5401301a401c0752403050350b030b030405074940d00030802c030f900640d5211005050160326081a000314025546e0541c4240300641d4000090700080c00e4000301405c01e245011043d40d11a4107100e415807064000d6008100204103001408081c0150f20001322400c10210741801107000c0f0025020802900700400407800360301d80d440c1502141c15044040c06003d50394900311900c1d002400090158034040d0189a4008070f9003103c90090300e0182c00c10702401e11a03540e030001d40510a41041c0e40d0031003040721403036642c000b0450030710a12024500236900130801d503034041030034082d0010152046c91003610300030070400402e612403c0c02c60119071050b100035041c03080c0480e8072000554480c2030384400100b0004d00441c0c000016089280c54404c0e2003d10106035110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 16275807 1250 16274557 16274569
    0x7060515130c020c120c0306180c0109060f03020306040605060d0507020d0e030a0b0907050a03030201020c06070905010c02130609020408010608010b0f0315070207032a050609010f0503061c05060a0605 88
    0x25a201c016074444e60031425146010104c03482e05111000441c0c1030307003119000085c40c1443c16900300c2c614003404103100f806e1f0301f000e000c0040c0d481c1c401e00b080c400c12460210010085050b80500400301a03011012841c19035458000c00001d001c02400151681c00da19014801490103444200240c4100643c80c0340103401181c0505421130014060300d405e104545818001403001451080140100341d00400e150b5a10300b0307000f014500942c0016128180407030345c1c924000d0050400c0091200800c030412450381e0002d0848022541030f80d0440103400f8005400e03000c0c1480750094401180081004614654154002c2c4100d806e008002d10400d187d10040c0081011126501600b5400c5407400402810200c400250496854811910319541d0307a2906026043d1103844c190108207502c0d12010804400342d080c0010703040440f4183d280043c1840040d00000020445a05201020000549955420410920582c03242d1f01c10400c01ca0503291140c0c5441007140c05803021450100c02041e5804c0c24 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 16277057 1250 16275807 16275821
    0x60b09030c0901360203070216050607021e0f030706030207050c090609040f08070501140103150c1215030c06050406140705060c030a0b150418140601030b060706051513 74
    0x1480d8101c00c0910380d69207080c50000d100084000f43d20032001001c03c2d00c0701c03e1005601c0b1f00c895070b01030007080300902d041410300700481d1b102c00d21410092001c400580c0c1c6405130101c6a0852100380c20300344d0080c00104480a540d4580a60305006151001030702c41d4242c3c00a04100d4840c1d802ea5520f0b07541c010070072103401400d4038a150030480d00800900000d1b03418000a50b8140514865420004682d903801c0c01e44404c0c0b4550420111b40d04010003c0150000c080b814235414080c05014200b580a07008054010121080c803c2d6500d80040c25210f90f21034083c10082c43d0004060350005840d40307000b800750f03809071069100091950380400d1246c081c41c2c058410305a400006000c0700e03220070074038034440e40024188144039942c03090030401d0355603000c0c242900039507024109500c3c0e40c0740c91044613a5141e0b000a06503800e0800005540030442c000916a200b0300c00d090000c7c1092000000c14914014094000c000b60f00d003805109100303514001607440440100d03540030401c2e587d100e602c001d84001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 16278307 1250 16277057 16277069
    0xe01030207050a0201030b0a030b190e031204121809060e100e06130204050418020411090f060a0302130801090210030b09040b0a020f071b080a0201080106050309030409060b09030c0901 81
    0x800f0040c80019071080c0c200c1502c0c1031000b40108007142e2691038001d017184069815004021030311141a07440f1410f4040c240d0a44501c2000e0b500346504e1540074003139050020130091401c588000f011045d140140130010711000110f1a050456403100584002440c007070003000b20200302640003910900d11f80c0040829903040070350940b0152100c0b0240716800c0084210011481d0f001c2c000416981c40300d00c91070120105420044428011a0042c0411550090741da19000e541c1002580401d4036461b0469042e9a000ea565582c0c3c1d91001d88104c0c002c2c007944c0c20440c480d90604000284035001504010140e82c001c45041c0d030682101030040d0102d0700702c90f00d1903400c60141380c0060041083e00d28441d902c4120310f9805803524a42449894155100030720849000441440000d0600e5941d841900070b13100e100c0007414074589580001e088010144106410080c00000164101c071080c801d40e0000c041303809003803144070f8840105100f01e800426120340207108031207200040d840d000c40300b02c0c12166 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 16279557 1250 16278307 16278313
    0x901050c040f03030f0c060e0c0f0406050319050c030f070806010509040b01050f190602161706010b0c0106031e050d030c05030114010315030b09120406020c04020309010e07030c060e0103020705 85
    0x32070340d0740c15541c0345000414001444221b661450100e100c0703005181098038010054407100c450101000034289051000034001c42c82c1a030b080c00140c50015100c4400e00c1c3c3c91804d0b65102d0034500d0241d10f040e0410740b010790107001e41061800e68074130015000060303844c08400d841583e0f072101d040c030904000440d000b03096648000c00401460074410030201d1101000350501540c81c02117003a030300001d40168000300040c2c0c0701003080340300f106c084807050001e0071740f031003041160a02065040350f5072041809000f4011000180c1554107940941c0700b0b20086a016080e12000151003150042511101409640c40d005040c49046054800d20070000038204503101c89055909140020000b044421030541c18181c1e50102d0500502011412800841c421804000c0c03600c4d010000a04001d00034203000502c0c8001e00003808225000301e800715103180242c40050722655840b181c01d0142260821003456401203440c040240007a11007a2000d450b10b0b0384908140d550b205004504078030030640064001d030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 16280807 1250 16279557 16279559
    0x50303010509090c0d11030d110c04052a07020f010203070f140f06010f0512030412060203130213050703050601170412050405190302040516081801020409140901050c040f 75
    0x118104914035040b83d1160104c0e90b24612040116066404401050b5400c240e45800a05c070740c98100720440001c946458900400c6550000e0a0b07920003002c2d15061240ba11800016100041c03003201d2000c0740703100078558003005070400640c0d030f00350f00400c0141e004801213201600b055000108841e04154052070496084155441d901c400c0c2c155228a01e51a0044001c9004199020400079002e0807040600c01d01c000e1802c41001031090742441e003812640c00c140820864880000b1007000850b4100d2405640c070754600d004105a4103800f1781c000e6000c295160f00c045890b174103a0000c0d105000c1c50314200010707180c02005407110340100031a800c02007005000200010074003600e04800c5c1225040140c00c190300c804c0050a4026100e08404c08202522030400941c5068082c0b00d401c00c903d59681018407a800000600c203000007480d81d02c11000303124210101e100250f045134014a99900e00b0042e020071031a1041c4506001d0391903d0f041d6081c040412030011340082142c08442c1221400c0000c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 16282057 1250 16280807 16280809
    0x31203040b2403030a02070f050405091b010912080315030c10030906090c080a050105010614030a0c11061005040b0303040503031c0612080c010f0506130b0f1c020901080a0503030105 80
    0x600b032180c02d0a000000340c0250714000c1c1c03000c101070410b010680c1c01034103009060498201e006800f81d84410b03c560f08207400d000d8071303103400f03c0c5103e00740c1070a02142d280c60300001d0040e07412404552050221a10000701c803818040184061400348284071515000100d181e010981e4848000c440161301044000c800341d0b080d3300075440200703624807440001c620700820b0f031078200940700240c2c0560401d40001e40c0100811100784141030250a0034108403030600440c4508040501008040340f08556542000403600f41c0100d80b030088030301c0075808907020351900442101c000340451150358012030501e03069098a16000c002c0c2c0382911800360045060010804004400b010150020309606644940114242d4040380780004081d01940c9100e5981c81645042821610701e034200b0407480e840c14003031068650f945580940741d06281000440d00391404070024045841c600071890f0b0242ca0001e01070700c20300711b0882134612a40200c1c1c000c0113580e600d03984135890303a108200042c90742e0030400040c0300d6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 16283307 1250 16282057 16282081
    0x105030705090f0405010b03090d090608010e0601110615030708060f0606130b070b06100305040c0b0c010617070e0c030c090d03030605060703030f06050a0501080a02031f060e031203040b 82
    0xb0b00e140003411002080d00c110003060440b0020781120ba8402d074000204900c5480402c0b2080d4005030900d821a0800e24103c0024098003060041c403040d41481c1002ca159684a1074016810303408401c160b074118240b503218503281c0b00b9616004c500a02649100240140000c0f890f50311035130000001b1032955503600300b08010f80e0703c51a4941501c100e24000842c21f00f0156020b00a507600c05c200c04d25450400d5020402202c054490741c0040504042c200400101003180c282c0071122400c03103054441d10300044e02400b51038190810741c2501d46614240c40305403000166542214294602c1080a4a0310006c0134411720086850341c44078802000905082c0c140f041c56a08590301924000070405c0d103550004603642d00429055000940303035003402c3d004500901c14000100804c556600e46140f80c500081c011510003880c03003000030350110002c0d442e0800c076020020603070f01403c00020643e4440b04064146113060b04200e020707100e235820222400401d14212800740b40c1150805d0415550310a4500d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 16284557 1250 16283307 16283317
    0x3241501050c07060f03060504020a050702040911030d18090e0304180f0609090204050106020d020a060e121201030b09010204030c12020a0b0c01090203010e1204031b0305060115030f09020105030705 87
    0xc10031000300140a4881018000d802c060000b40c4e840c52254a00100c0040c280d0f20f554010781c1c1b02d03d20402ca60144180c0280458401d10790690307000c23070403d255003080f0b401c4a01c2542420f03058011007481e605555440052405003803801c1a82294403a154a000b5040350000ea8030854594010041480340880051100e0086200c04801242c0b038045c0e01001000e03904203510141c1031603250710584c030861a0a00a20b400f514082c401072500090345800299204072410002e00030903902c40c2c42c5034240c1c0003400308081e44045141c90399515402e160390142d1845092000740d440c11b0b0000f003c244010018000c450481e40c00c50460600030b030424a40c03c0302e811078041c1c00c90340038811b0000010001000405040e40408850001403a1a42401414256008c0300c076480e08076008130710880318180110083e1010380350804082a5050440186420381c5250f58201600c1482540300019507004211501c40d04142d241d9000c1c4091520b0881c00e80c01c0d06e03020340d4000d011031000d0001500301407081010300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 16285807 1250 16284557 16284559
    0x602060118020c070e01051e0102070b130503120703120504020112020307021f0c0e010e0604140102031e030a0c0206040c061107090f020a0807090b0306061803011a032415 75
    0x145400e0f01003a15501e07144103580004c84803855580100510f1034220140140211002c040348000104000002e4441390340d4002c103061518040349014442d42c600c0c000401410b4040e08550b1000c0008081040c150000902200024025110b505070b410460007290f00070b41c1c2c107849204981c2d0040e810507019420080000046110712030310720900c12641a1051801d501609000503002c03d000d00050140e680c50103030303074140101484143c16a03103032031007113604440d0703400e94050102c594040101d04510a00902c0780402d40b01c201d80303400c0302a0800045005042c030f00c0c0b0801c09442500c4040e40c58000441f4040e0185403403040400c180c030300480d00028030600e4442a52080c5440d085c42c00110380b8045031000b1816408214983c280b504508440d03000402030400300700551070403405130407034800102498010000440c8a640304002c800e02c20540240080080c000000000360802001032240c80b01482842400514004504691045504124000721001c119a20300c8081c60520305242c0d00c1c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 16287057 1250 16285807 16285811
    0xf03020405040f02030d080601021209010905061303020d031e11060402040b0a0b0a09170111071203020d0e0115090c0903030309020310060b1902030909040b0402010c05010203070f02010509070602060118 89
    0x22001070b13070300303000303907013880c1c81b640c951000e01e08100000920380302641052485821040007207450603078010358603030129442201c560703686001c40005030a41071210b41c80250401101c030099810141c000b0200c0060400603c1e0f500c00301d075586c080c02c540595045249a0040d003080000c1405420b140e000b0b8030804001803d00c214095950075100e02c40d501140d0752000148480c1c00a2003068001d8450381000c0c0d408000034031000030000c5240801c0d10804200400003a48004425200c60107501176416000c10042c0410035000c00481c0c040c06810891084003c118070000c0c082442541c521484080c040150f03a0041c03254119031303040d002400041001d80c0d25201c0e1801e0021004698018000585100c02900791a826211070b280c01c4a12708a0141c1c05541040c005110300d526001141a8000d4002804400c176444a000503207000c400d080d0080c0c001d50001007040030058101c4c03d00b20760081c190b4000c002c1551035043c160f444450300d005400041e040300c00108000604000d080000601c0d40b180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 16288307 1250 16287057 16287083
    0x30315150318070e07050703020105010801050124030608030301090603050105070f080a090204090f060204050901061b030503220c150813032105040b01030308060d11011107030203030c0105040611040f0302040504 93
    0x3003400c0e05070048505c0d0300060b800040b14410141e084c00b906005001d6034000784000e5041c2206120a81c002880581c249074034a07080700c1e181840b035001a401000c11105480d5696150030580e0090f152030300054544d5803d010114003401c1c49108045107006255582c1c16130703502e0303000d10680507000000050f03a0158170340d0f0b41980032400002070404010700c244001079450b07140405003c04090168800030a0040300c0d1060302e45120180320701d4281580c540b0b41281d4a0b075904168550101c0d802c1c54482c000c0700c10008020422010544a80c140d54070820f41510759854150105d4000034200c8901504150360860321340001d01810820100380c80038a1a818521034030b21807030045910443c1e0a03100c0e10080001001030540208040d43c21040c190381300b4241d200e071078842d07446071001d00f4682c07410041c00140102030b004043c0140c0780603680c0182621364030341c0c02c103490038086d24059800b640c8441c6000c4600000c40b0114080f83c0460f2088203081649a00d16002c00c0000c0500a005a03100d0f422590 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 16289557 1250 16288307 16288319
    0x1501090b030a090b010803070302121614010501180b03070509040507030f0b070e010e060304140309060706151401080109020d0609050705070b070516020d0213020a0203031515031807 80
    0x598842c510240340020080340c07900f450302e02c00206900062442d04200f2501001c40d03800300d030506014056440759036440c440741c801806140c400e18800390a91006d900700b0b05008a040d0001070498a0450000b8552a002c0903420211901c5961840e41940802002c000341c5c00c0a180c2580c2c441e006030213990613155262107420700c00c200c1e150102c90482044042101054011203802410b01003880c01101000494000c54403620000d40054540304851081d10004802007044490a09019088544034a281c2c5400b10151680b5005c0b085805844000800e01c2c0d5074800540b81511016950b01180740d181404110080d8420540c20146a4442c000031504000d6801481e000e180c1c03e554060740d0b9140e50418000b080005480541000010400c803107001c1c1a5101303c44205404590950400000d4400034440c0d0b0300c1800d009003454004508910080c0d00480507602c2501c14900c01420445003908101c07161078000c036000f1b8901c900340003148000090310819010403031880f04880c142504c840c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 16290807 1250 16289557 16289579
    0x3031505040e03070b0109060b032712040302030609030702010c080c030904060b0406080709050a1401050706090309030308010f080d030b03031204060204050f0607050307020d03050409050c0a080f060306150109 92
    0x200700642c0c0350b4800101c41040000d0840024010b10010400300a1981010020119888090700580069250807000c2c507446010101c205c03200f8540074100d40176003400500140c1c1b16042403105a00c070f40a0000011140d001c01b01c119426143c0c140d5402c0e800d901685d45180c0c50b5002036100001e50701c0180501115520344d845064054203c070049035440f285460402041224000e00036000c01060250030401501d43c0c5c400c0e41c1c1999103901084440c0c0c40c1003c0101c42c540034074980034012905241101c0c0c240360f0011540c40c1600e00940e1064826030b2103142c4002c120a00b4400d4000c1907201c074010380801c030b209901c91792050304c2c000c0c1541d2908100754030354000c002c0305550544001d40d00107000c101c60300c0c00c01200344042d48159429070800c8410344400c1d44074040c548019009011040d0031000301403044c001c0340c0c094882035100300054205140302c00d070f680d0404e5840e80e0218050f04089440c002010350034134400d00c0b00500400c3c1d40d82da112403071721802e490b190805040c0200f025004c101c0070105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 16292057 1250 16290807 16290821
    0x122502030f030f071e0207090506031c0e010e06030103080a020106080d021b0d0506040501050a0c02012d090c09050405060c04080a12230d0605060c1011070f030e0109050301060b070303150504 84
    0x51b9004003c13507424101e510b41282c2e00a42400c0c440e911409040c0516807240961021a0080f8101401400540300c0140c80c501c6411408070f6001e00e0000000c410002a00d000c0c1441d4410741d402007040d261100035055a07000b0603071100740582d010001005490f283d85050030b241d014082d04220075410b040c0d94084c80c4c500e060305d0464040e5115410024400d10522070840000040d100070b11224038101a00c0c0f00c1c85040a5800c0b40300d0b00040b4264540362401d0304100d0f100c50303200e441c2080b602c0d580c26804c0000c000a0310300f12407030f010b24000729070040910707070959091f07e030755501505941005a44030880d0381c052504000501042d01c407101d2110004c0c2e0a41030242c1503560f060b40d42d41083d51105011100c454028600c64801444071400115001402d42c110191030080000d07080c031804080c0c03105000c1c81200804500c4e10710303000c104055111a400b0140102a00ea141000380c0303e10130035003a40d83c40e02030340c03148200a000080120344642c01c82061802102d03198840661a00041410303103c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 16293307 1250 16292057 16292117
    0x20d020d02030609100b180d02030f0604120507080d0b0d05012c0303100501050304060204080123090601150318060e070e070e0603010306020a05122502030f030f07 72
    0x10200c204201404d10a12180e0f003c0c6040d81d02c5d0503080c2c14010884940e000e040c05a20071042079a005403026102c0050305140d031500142140d0100308050f07001552031a040307a0880d401c290190f20a42c459014205503a00300b6404030089080020b01a0383c00001e091064601d0303441342040403450040b4030203104854502c6085002900e401000000b4042c84d480c440001e00c10580c020020407001401d28885501680d900b480d00c04e980e511603080c0b2202134086d0b900301e00595481e24011441c1c800c40785019a03002c0160070880081039883c0300b001c5031504c00900c1405441000f941041105034443e070303c4054045458940c2001c0b65645864a50888904a081d400c0b00e03070040c0c100380b01d500108800a6406403261030609001c518406c0070030041d000c1880300820325074000c83c0325504540540180c03945030244500d000c225240001190701c0c000c010b81d20908980e200800c0c814903c9101200b140c00c0c01c0000082c003861074442c0003403035882c400000c100b80c0401400410315641e9a43d142513201e40850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 16294557 1250 16293307 16293311
    0xd140c0a0207080604020a050405070207090c03060509070507050a030305071101060b070203010b0303030405070e04020a0e0907050109050301020423030102040b030103050a020108071d04090311010603060906060905010b07080d020d020d 103
    0x5214503000e45446800d03000300b0400c1d0302503003c0200507921005224160340c410344000c105030b1100c2e42c06034074100143c0c0005e100c190070a07a0500d10b0302d074941e0080080b16070449221130385032540c42082d12203110385140503107990009842e41c07011030300a400c01500003106180c841c84843c1070320000d5085070010341090510440016180055281c00d0040440c142c0c01200558610309103a95920343d10083c2d8400d00e82d03804204c00000b02550fa4404002d0004c003900240000705140c0202c00d80e4407850980103141c0031445e600070100301410f0500c01e44003980e00f5001c544507072850702030743d184005886183c403075030540d0200004101051078801441c029403141c00103056003401407002600003040108488100070041d8030045110003400c03102c055501043c0c0b0b0001d40500c0e1810200c0710041006980070303807036092410000800405034000e10f4901c0c0698410041a03032133314540400d4603828416590480020f00c01d103404610003e005110b500d900c45801441e01d002920040b00b03980018030752072544c40d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 16295807 1250 16294557 16294567
    0xa03030e100c02010e060106090e01210b0703090c080105090705190302120a0b090619020a02011508070608090d051c0e01050f04120306150509010e0306101d06030a080d140c 76
    0x45c8100503071405860344e400c00c58001420160321b00454036051003080d1520b00884012810203002c0121107190f81d4014a1070351691030320746000342c06001c003154200e9080322924400102d08006200c2c541c01040013a01818155140104200142500c01602c44112011060001c0143d4580a45600040700c907401f03410803003101d0410382c9000000a040c55400d400c000c0070000c014280902d50070001c14081070060710764503202c408034010101000c0c43c48540140d2000070844840010700d140c1112413958070f0304c0b4591b9074058072580f02c1680300c1c14100411002d01800c0c42c036208034450f440d903071880c005000594003181c0900c00c3c2950015500701110640300310600003440116260342c00782945034101400914034020340d8080b001010340450040160200310481c081e071149030544950b4034010111603280c14064082c107041d0445110f0940c0b8811500e07040904c0113040703d4140c0c403c02008000d0f00c0181400d4039207844e44c0c0c2c40481054070141d40c4001c0b038903c0d4031801d00c25500992442a0300e07070f124 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 16297057 1250 16295807 16295831
    0x2010506090c041d0703020903060405031b0304050a0509130b010902130e0603060103060b060706020403060209190311060f04080303071e02011415010c02090f0403180501020a03030e100c0201 84
    0x107036405481e112010004010a114400f201c62403d42070304101c0700520119076030190100c1c000c0c02002c2025506004410500040c0900007007c1d0038003030f001441c0b0800c3c122003884102e03070700c0c171a40c800d658002d42c22200c20852454048121988481e02d4013400100010954482885a409070071411142da808103c80e07000c842c200e003600c40901410307000711001e420600000f82e0f07903c0c8140302c0280380644507141c1070f42d5500c07503030152200a81d0190045d92103135168038203500607401c2101554060722039400340b40152040d51801300c0403260410210804002c1407814030001d07038407a051030441038008020024001600b08000d521561725079031040c042c010f90b00700000500c0642c181000071681080c0d0301c10070b1103100000c85500500c4120000a1210712103005843c4a800450040d500c405000c0401035403d00c981c04003885a482682c0d8210404120480391020074004c2c0182d600503403009820200090082d030102c1c491032003070000c55601000c003070f80720010344a40031b03c5480180d440300216020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 16298307 1250 16297057 16297069
    0x110706080f01230f0f0d060504060b040203010501050406050304050307020d081209070f051e0301050c0309010c0c030e04092d030201150311100302040b04032d080318070e0702010506 80
    0x900501410f1101428081c6020782c0d0034030140840c688200840d031182d209968a0004903002c03090094040301c400031590030008020402100c081d11481d0034110b0034895031030a40f00b106d05036107050f11018200750074624129120380006000b02c0341c0d44010004200543d851130b982c00241c52113200d003540c0e80e040f2503041c0e040b541009400e086031a40110810310100080200d5141550021769262010720364420042a00c154041542c0d034041d441e241c00d10420f510312100840c031401c0130350024001400807107411240b0b240f400340064001840101c54414601e802c0d007190007680c5c0a0900340a014141c01b10034418092042a0402c0700003180000f001050740a01030230000151104141141320b03d140c0b0b404000c0b0000c0250240302c1c04105136041e0919000f641a41c0c084c1034a00395640e1070300d840346441c60a0248200401c0d41b0311030f40510240d00340192600c0070600a41c000f82c11805c54890144459607e600184c80d1011405040c40200e24003511001702c6100340303410784c001701e46428403006002d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 16299557 1250 16298307 16298309
    0x20d02032401020d210f051b040302010f122d0c02070302032d070303022103070c0602031803030f06010801060c0308010b0912030a0905040b0402070c03080a110706080f01 75
    0x24610344400d60700069a03801180c464402500c41c1004a080320303034043c9084402c014040c0c0507a41514100c056980b1500591007075218540261a51418025410120075503000701e100003030024106100c0e8030382280c8103000d450b49000325400c01007010021004940b5200302100b0b800c6443e248140040000307883c20703006d005504405130014000d030504603004652104103c11750800900c00364184208051000d04113000480300800a844441d600d03441c0c000d44941304104409102020f842c61482c043d5a06400c0b00d010760003d0700c4204218501e80c1c0c41c08065000248402e6143c00d440e0303100441040140010742c0300342d100200c0e0713400ca8a0128000340c000c40d8181c100700d00300700e90108030340002500050b0309415a00014035403500c41d00e49100043e130314981e01800304840e010102d66188690b40115880040c0c0e0380c210340034405109141c007071004a002e01c410103072403003a01140400100d50700000400e07009589140800104100d120f605103802c020f907011400003500300c01003003503049000f50598 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 16300807 1250 16299557 16299601
    0x3070206040c1202010903020411190207080d050309030304030e040221060a1203080f0a0b0a090507021b0d0b0402130203010b030403020c03010c080708130605010b09010210020703020a0b0c090301020d0203 90
    0x40c0100f65030380000303010884502000340100e64501001070745005050650f40c1c1103940e901d4079000c130382e5241002500d604591148218034031031b08980d1001207006006482c440c0d03160f000114150381d070b00d0310110340182c441a50117801690030444c4000310b0140d414250140501c03103c4818032810203c0600804050317a502440c0c00c1702018402c0000240e00c0403c1d1604241102908036440d120200c4603801000d800c201c0e5540450503d0000034840190f4000c0d5106004607020f0759001c52800341c0300d8200c24150b03102c032548062205003000c0015226044241c00c14005800c0310340d400001d1150070f080307920a030000d156102020040204040d410841c1c010b11800c1174000f40140f016403040030740034034400741c80300c018000a0400210004429140060301a80106041c005542c1d0350540c450150b0051810900600986d00441403200880c0200c40006a165008002d20b81940c0c03141b910b8448040e00c075401c80b010030004400340d0f0b0740900140c04000009000165031f4141030820f4a441e481d5840d1301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 16302057 1250 16300807 16300829
    0x20a0e120a020123090d060f0b0906091303140a0903021c030801030204020d090203011509060605030f010b0a05070501060906050405060f0307050121050a1a061207050f04090203070206040c 83
    0x2000140d0303100011141d0003440134030f822050704001000c1002401405003440d000f008420040061003003940248210013071416040022120000c10300110240031503546400c085c4144c04609203011341d03a07802c02c4e55402440c10001ca80103144c0203442d254416400c0b18001104801c060003540740ca0585c503804002802c1c100d4040c00e01c40d6401401c4014144406071195901050b0300c207480300030350007800105070300500801a841c00c2004100c1c0d0703444a4041d88034554942040807401d07a000e14220380c001d5140c5641400c0d180e1911042781c2c81341c0e0003160f44034100201406080005182402940040c10300b08801154003800c103002d0004640c40105050b1207482c11006001c0651004542c90083d40d00070f2800511901030040c01884101c4844000820b02d4900001c100b5140b00715404002c4804440300200300f9081d280041042e240a28044c0703c44803034945001c10f144034003610050080c080b010034007508190359440c1344400c87e002180d000015030865001c100810072407215400107089800c0303034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 16303307 1250 16302057 16302073
    0xd050604060e1506040c090902030406060f06020a020607021905060c030a0f1409010f02070b07080d0506060306060301060807020a0803010311040f02040b040308030a18030f0206090606010c021012020a0e12 90
    0xda8071640c0084c003a54001c542d0b8040009603180300b2a00900a0143c130032042d5038a00309442c042d001083e551060a50301012001c0115810748046400c1540c039400600079828210142c080113243d81420b034041e0b1f0f1100a108000034241c54110141213110f00c10000345807a24890310024004c0c0301c101400344100002214404050030320181541c80100003131134045203c400501040c2d01d400955080480101e201140e18010045d1407401000c540c1e149e1a0b090010f52120300c14401030b80002c2ea01c0580c401814401440f00f9441102d40c1c1e5401002441120b410f00301c1901c3e0201e4030f501c01e80040e0345800076092003403650b040c1030246030f1008042d18400c519252030581d0702d4586002e140401069428004003086008100c3c0c1c200030800e14003107010020f41403151501402080c4884601030140c041c201c0020070310f40020400b031348240c0c1306846502c10300c040d541c00c01030069400b8106405001a2400c2101c6000c03013440500b11a07078050300c448094030000707020464a074554842006003a800200d03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 16304557 1250 16303307 16303333
    0xc0d0818010905011709010f0612030909091707030314040f1e0503030c09060403020312220e0601110a0b070e01090e04110603040201051b060103060605030102091005030903090d050604060e 83
    0x41904000000d82c41880c00d5480310212140540380395000018614108080801c800120250b200c24ac28481c2d2228070842c0d5035022000705817220b0040c0038100c0c401004a10f891f1135603400040032070511903d000650781c511440c1c88020712000390342c1611403141014441040101c05200031007640303503050740c005201106540d610794a10008050f880c2c03c44000c9041043c41d01d40105640c09503600030140c41c2c5c941c4620580702080d411400b00e20130010102c14040e00000701d4445940141d4a055601e08071640e43e25005452008004442c16614400d860f4910080f480481826000f0300c05036940000d80c1c05980300040031520706411194001c0c1c00c401c14800095544401461b0552003502c05035103a5880c2d000507140c0740100044401c41000c0c1500b000c81c07582010038a58181c03841140b041248030740320f0b4107240c200e0152030501904030000c41e181d43e428a000d00f016551082030fa00440b40380c14441e074041307548d082d0074103070440c0c4075031058052004029a5000e030503039203803e1000406003840135174 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 16305807 1250 16304557 16304567
    0x1207030c030b0c090904120201060503070b0703080f07022104180f050106050a0c060c020c030307060204080111071a100f0815070201020304030801030308040807060e0307110102010605030706030b030c0d081801090501 95
    0x82c3c4001d00720311f4040c0001034024001e402c10070080000405940750190b80e1404000b5951060303108800050807240001d000380d8181031002c4c001c40c80c69006080c4d50240084070181c980c11300c1041e0804000c00d202c00900000700001c94214a03035520340c00304a0841c00d10071502903c0041c2c1082c41844424400590340da41e002c43c2411645401c01404581c1030881c40050342404030703600000e500340c040025420148140c68000700215014040200a06844240c00c04c055004088004100140031440042e8510f103000700c05420600e1056001d103096941c01c0020034001c40765202c0d004540100780c842d17803184002c01142e540308420780000d515528042d58014019241404000e0030701c0740d5480402e09200c05c2e03005940c1501c1d8071a1307040000c86509060b081d83e176003120800719590b500b1070300030038095441801040e04568004d0010241c503401c0c40c00640142c80d0103c151501485101d0713403000c165842c0824032000c14015410980e4841c5180321400c00c0380154240c10b414820442020001c903607000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 16307057 1250 16305807 16305811
    0xf06080705010e0904060905060907061403070507060b040609150317040f05101404060c050606040e0325020d110a09020909060409020102011b180f0b0d02091207030c030b0c0909 78
    0xf20b81c01e900c617a565103040002048900000ba0452181e0010400660300c001540025a4026250002810030643d00b58000307100460b4003000040083c4a1900014131941103400b19400040000c2042c6803903040f00380c2160840f5840413080c1d0b815000400c1840b81603050705900805103d116440d0509242d16181156064890107005d024074044600c0c100e8891409011002c500c900703c150b50310359a88004184a0700000d007a00c80c0c0c02040b01148140c81e06118158050240710084c500700890013542d04c40340c50b0366400c51001c084800e02c031440180c0c3c1d001d8241d80024800c042c900700701c0c54080300f4482e07100d220703802a950b5184100411450b580d40c1041c0698010000c45010a5804151004034050a82c188111030f5040d21600001c9015800100060b84001c1400e04501c146590344d0340405400300a120740103880030100420185900d168004001d51700d0054000140c03401d03915400ca103842e0003070b48150392080c020141882000242c211007600070310101d100c50704000078400001c800c0600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 16308307 1250 16307057 16307059
    0xf0201061203081e040602040e0a0e0a060509030c010501090204080706090b12060f120a0209060414010308030901090803010807080d050a05090108090106050303040303110c0907020303010b0a050d09060f06080705010e 95
    0x440710001d12000302c07801302080c042d502610080c0241c00c1074641000650082c2c000d2130284210b0300300040056690303214642c0442090001402c00c0006070f190007008010241481d410b41c00108a450401c0340700740200e81c028080807000580d22841c01c0c084074100042500441c08200329030008001445000d0266490040d0652407540c00c1d41350394000a4411101142d419000701210030058070710580424003500f498000d0710300344d4450b070780d90040008852103603001c2c1c0c2c0010340300001800400e108401565000c00500300009840581d625100f607681c009a020720783d02e170b011080a11403000e00348910300e00000c49081803410807005c1d40f0080c0c0b0500070301d00d40340d04119040002a0008030300b50400c40c000c104c041c09980d40c842e26800c0081400461101c83c1d800340c815800100120b04000c0200d51007082c00354061030035642400046c0f0707000d52080d05010f0400909004403d440000c03445546403c0384540c0001699000200c0301c4400d0301d040742c0c07004616800c010010030069070800c85103800c2d848 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 16309557 1250 16308307 16308317
    0x1e0e030c090c04060e04020403120e03011406030a06050a020f07140c010306060e0607020a0905090d03060f05090606030411090c030601080f010e1305120d020705070906030302030d0905190303020a0f0201061203 92
    0xc1752a02144c028080e0780c1c0b01411348012452220301c4541c000d1002a440d8500750001e00200354040c8421494003c1501c0d41505544005407410200718941d010395000080100050315124000404450b01d1b04016025030304d1a84403501000a890204510500d8603420708052111524044018011195000134203005e088000382a0045540e800111700c05403141c00000c0015007445400f81d9a14000112510b000c0303450104080382c000c616410300070443d00b000740728075629500c0c541801a950030181003180c10000ca601456130556420051600c5408030411040e16460032800040202c0d50140a8400b2450010014810940030000c500d1b84014081b400741c00444107031500c5450440d00e900d5003198400e0101c1c1c582d140900c2c030780042020354011000c613400240c440c0306080846200340301c010090b074010842007a203d07200b60841c41a513800391058440003000200070038041d42d060302040f00040d42c001014560780790802d05103034a509451008001c03041c1040d054040e4811036540203000c2c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 16310807 1250 16309557 16309577
    0x100e07091805060a0e010b0a080c01030c1107030305030601030b010503060d0b1009020408060601110313060e0a050301050a14010f030302030412111504031a040209040609031e0e030c090c0406 84
    0x1d4540d00219580e0060480c1d4440c90034407030050080c03440e00f0a4205950811207105054a401190b100c00c4d1008440a8075404d00180c1c01507008041c121505003d20103003802803511054180b1001c0000c60113510f60955a10b0700d20001006c80701410742d8a03041c05000d0003400440d031900340340540d05580c480d18007685503d60100075200703018642c0c4400501400000c000c10041c1c00030410328010042030300c40d1113403500480242c1c2c0d200d00801200013401e01d05101c0070800640f107031506000c14139029080c007551a84a0700030909440d8101d6921068540300c281d07000e005040030001d03c1c010b00c405c603500d041d02e908599000b5142d200d60320940300038880f501340e050f00707002c4115804003201d50018002c1c0000714009002040301e410a1105543e102a4400d20100e6480800346891040742c1c000c0c80a803090ba034a07540d50000704bd40307030307425070800c101c80103c1e405030070501c4440005910241c441d0f41f100711411b020589440d40101140740150701d040c0c1400703440613200042d00d09646042c10003030115 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 16312057 1250 16310807 16310831
    0xc0a0308030f090c030708011d01060810020d0f0f0c080a0606090b0306060c0a0b19061518150306080111040506070b091903030615090f0512011409010e100e0709 71
    0x104c90850140c1d0701d80284400054040300540c80241403c141e07440d2001c11032041d14103982200c11500c2001082e403c08494030641030081d500030410380c11003000005815102c604548115241c5c2d4101e8031034250b944404018003034002c81800d90000c2d524400348282400d1800007400b002d280d224603850034001101203556a5503110548010360b9480c1c007200c0c0c10400c1e0b4180150110f105503007a603141c1071f2030841c00250302d4079401404243c984e003031201e000007503076807004442000c030091075220002e0b040031000c14042103001d40e009143d0300551b40400d0050810841501315a2000000e0a0552040000f004607844140030f0b5001e4541080c1c64220039581e401c01d19007440b03c241d889840050391010702004250301765100700190382c1900c03290900c00c43c5070042642c1079400d80c0203080b09004030300000c1100e49091503403940c02d600303281c0010540d002288080140c4010a6581d61320694581c40e0300c00e48120100445144d020341311a052102983d418202c1303880c0c0d443c9000d031035081620303070024200c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 16313307 1250 16312057 16312063
    0xc060c0c080321070f0f080703020c0607020d030f05040c06030b12010f09120c020102070b0c03040806040515060102150a0b0f090403030b01030509070b1207020106050607030305090c0a0308030f09 86
    0x60050109070703580c40d0b01040690300440ca1150a00540030f10800218038001e04c80c1d16010b5014480c4d8a41540d803540024064407110300083c940410950200710500c2c140030141721340c3e405103406030014042010045005000c2d1506004244452441d2404100200e0185c8602204680e003034103000440c84000e101048001c544d46001c0180c81d0300740120032039000c0b43d03584981c8155000d0490030088101d82c842c01c40311003010703400280c01a801200300744008465803004044807990701080300d203800c0e07031070107082e0405600726401d48503904842042507a6203128041987c0c8480d0900c003810440564a041300e0b1201e602808642e031103a0f441c500d91400d41c407102c6200c0310343c450081201c1d025113490701d00100580007607045d4900080c10304c3d02182c1c4140c2c0c0000c1081c1074070404801d69082c481d982080c06000c01004150f007045640707440c0000340310346844006044c11406a0b50100c0d4074a4500c509910305452801d034140203c0700c2c14000c0010a400d2010390350450410040c0f424a61549400d0601e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 16314557 1250 16313307 16313309
    0x14030f060108030a180509040209070905030d0e030114090d1b06050123010e06070303020304050a08040305070608010b270315010801090c080a0b060904030504080303040c061b0c060c0c 81
    0x400e105100011448100000c0942001c40c0c0943e03603a8046284450200d601104134462039410001c000046001031410f14000e6a01017003d10b03000440c1030307803100000d10b0203440b200018003282c0460303400c81c01400c0a006040d5012071040c0119118200f81c0741e465954180b2f070604d03100b00051064000d018904007054550502e03008401401103503126004840c031600c0d00301148044100031000704101d54003c2c8801240d584d4002e00150820115450070341c060360001300100c6903801460084000a143c040280000d503024000a1007103c1c205040074116490603000503122034824000e110110003034268151815001c41c01003088000302101091030100380401c681c5080c8070950002c500b00300c055100800c00d43c010b2240b040040c0c5d4402a060b190a080d14010302200c103007000041c0d00d41011045076030081e1091038154906903480c0210b60540c3c00c1510121000030301a03008118242d8802d8001c0090504421b003040444210307a20000b96030950f2140300c5c01d001e096003d090502c02c1ba490104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 16315807 1250 16314557 16314583
    0x3010911092503050105120d0e010c0f06060b030f0a05040804090e0115060e010210060b090405071b060227010807030b030c04020705010e1e0613110303130e010603090c1403 76
    0x4680c802896001e0084c0a0034000c0c0c500540c0c03c000514828a800610b980d48020380f900c8810a800100b001110360f4a5031078415220003402200d45000118503104005c010021090041e8480c18605e801c1c0d451201d0203002039100c0750a0405203c0800c40c2603084130100c0e419180d0004001011030b21250160400e02c4e80d003d07142040f2240040d6454020b070000c0b1500200368262030301350712000f1002e4115682401044000f15083c04803e0b114241680301d542c1104041c10320780171124903140000000e140a010450700d5513000300700b1000010003144801a1078802050414032050a18002000340c071008200f20704060316048a42155181442840d814820181040d0b5813210282003d03070191603005c45545051049000d60460640340c0300f01e04100c1c600f044080c044036168907800300300008003a04142c803080f00d0141c3e0b001c0c00e59010401416100c0216492040f0585048100c444420059004405050400990000050540741d0403c2914144c0160700e26100348800424075200d9104400703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 16317057 1250 16315807 16315861
    0x903020907020d032007020607020409080d090203060601030605010815040605030f0109110916030507030f050109150503030f2205060a0504090e0c0d020103020904111602010e0301091109 82
    0x11007074855010650880780102c54805004028050840340c161800140d10400f01030f40c1401031000500c1c4c600001c0042500090020a40c01d11540340d6000c00ea010b00e440c0c415066a070082c2104504043c01320b03d42c810b600742420040b0915106c00a480600010007020f044164080c90200b07a954580c0518050000601113500c8821000340b61030003401e940030240d5043c4400707042c8549c1c0d4a403203030103584a040395040303c420810b454002a40a4480500480c040c10345540c000a07694ad59131180354000d110480d00400d050064400200481d90250006e5002e82c108200080400492a0884020400483d000000322020b078104071500341045c0c0016070301c084001880c000c096801000fa00580344940c40130800c0080c03100c0041d075100b60b21a0510303045580010b4a070050f60081e4040c15945101500101d01c0c06080c0070700d4212a48064915001071103000605829940d00482400c000e8405400030403d200d4203403030704140b83d0039404446100380e00100000f081540e40d9072000c2028405007081c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 16318307 1250 16317057 16317061
    0x20409050f030c030c0610140d030e09160f08060a0b070201090503030a080709150801171c050a02010b04090203030f160507030f0b0f0f07050d060305030d090c08151609030209 77
    0x81640c0f00c0c1e000c540d05405d140310340c0d404105020f40c04498503007112140380c2c410074856500d00500c160752002c004150140032803a49590b60984440c60b086200340101583da000380300e040c07030700030b8039203200c0704501010061290100609600c50410136030a4606141c442c035103c00320740c40101d542a2040e0400c64040c0008200c0500e0244c21201ca01d009071000c0d140c840c1029241d500e030102c03c4030504841c02c00034112600400010107280340340410140f07401f090322400b129109105680c50352070300301c0a0020700e0010328850115420310440f0721200342104d00b800f03611801e40000340e8a010b124440c481c0041c00142c0c11030b40001c1f07804501c00169102080c0c0318403940da0b00340250405812401079561180030000a0320b00d440124131544110140c901b0907403c3c2c0ca039103100b01e440350003401203048519a10003002c40480c408002601d40070b0000600864440e580d841c5c4004010340c0c0740e0000f030060b4840b4038100e0440d10405260b0354420100024440c200c001c4043c01c584100280d031001e500004c1c1c03901 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 16319557 1250 16318307 16318327
    0x706060902040e01120807060209010306080d09030501050c070c050f010509091608061008070309170c1f020a120b011b0f050d0f0c0f050304031703090c1804020409050f03 75
    0xa403040f6035840c8070000703640c4c1c1e0707841c21440e03240500ea2004204030070810248000030010b9024112090041c9000540325484003145860b02080401510200b4880c001c00c008201090092640c0824000061402c1c48050b6444075107141190003210320039040b4224000003644901d09455078502c0042a200280c18a007400000e1b008217001c0303040000d2111000100c0350300b040300b0342c0d04030b00311955241c1c889a542d50300d040300200300d0560200c0303101c0203030440381c007440c4200c00150034031810b940058060711030f0104d804150010b811402c0c0105900500c04444240d4000840c1e0301903003460303400440c2604043c0012941414000e081c0701c66a01c00d101440b045c0100c607803210000328440c5045815140048005030b0300f5028180d5070301d00140114a419000506d0f01c020b14250510600880382095200c2c0c0d5030352101071100c100800001d0b00441000b0b40c090003045070070300d000c10548030500d401c0030728007144a54480c01803010340619126075502d800c0000401184944403002070540e45c541002c0302d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 16320807 1250 16319557 16319561
    0x60937030b06030c060301210602031e0114061207050d09060f0f050910020a020f07090510060804050304120305070c0b03011d0112030c020604090603030203040509090d0f050c010207060609 83
    0x1000030303507400c000d0000203030307007410000f840c0344070038030b006000d00c2c1168a400200e0403207031800340c034002c1e180980101c8a000101c10b400a10f00808000620407000140300c0c00404581d00c0c140c1c0040454448602c01c281e103611202c046410750a144000781031181d85295095440348035004e507858055207415400f10a211543e805504034100281d024031048180071444820b40303100b0390308030700e45400520080d01c004040754000c2143e00900d0054400402202a8090501c0c0456004a06103a1a1400c01031034050743c0a070000034003544c0c140300446062a450b401c2d40d9000ea8084c01520620080c400c400b41406402a201c00582c00f89055030724a4480f0514140e5404c20321414642c014407022000c1c8900040840d14162516400ac040c084850303500d0458619407034030f40076a004041004081003d008500801000d035010750021a80d5501e81024051802001003070041c1e9034111404e034420b096400364500c0b000000c1d900e00980c6940608003100e00921400f0302c000c103000d180002c00500c1003426 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 16322057 1250 16320807 16320809
    0x1003050403211a04020702130218040509010e1203070e0d021305071101061403060a020f0702090403030203090d05070b180106090612020406050a150c05160e060406090b060937 77
    0x1c698901c3e9001c861000c0c441030303010300080254030050130542010300424030780c064a51a0140ca00c1e00022044010100d4100c5100341d0301c070800c0381d46600d40307400b09840401c528084540c01314961495032a044030300401d044580340082d4031401003039a207001550348440d4110302c40c22240c0d408015030b04000c040580301c0350031928030541c0e40d420040c002845a54840240540d500c000e0090441c03550b4100032280294800348072140424802d010304405030303d94045051207544a5240140d0740e0409110705807800310384a1181e02040340410821001400c00c80030a9040381c0c10140066074a040785540c40d002d80b01d583c1002d007201e03282c04c0000901c150341c8442074a0720748c0280d9007009081e480b0004c1c08942d106601544440f0440c607240da0417000c1c4a6200c3c03215079400744c816114901c6c24907031a01036061140d4801103002e00c0141c140804e81c64144940c000070190182c1c100071211420001c01d81c030b405010340e903a01c241c035038006c031440d28141d841d8010b1840d0350b2200c81c0c100d010025100460740c0e040c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 16323307 1250 16322057 16322081
    0x50607021806010e061b061f0e06130606090806010b030606070602030601030e01020a02010b011202030c160302071505030103230705010c08040e01060c03110706051e0c07030308150102010605100305040321 90
    0x47d03140070a9400107a0942c8401c0c114220a44050a904100344540c030a40b003d04003640104140fa0310500722401403041d98041e01d820b568844030a80b45c075175900c0c50900183c100c01b940c484200280302059a4800844e500c0c2a0300900150300c81d80c2d2007005034024074081c100200c0c3c95000180c4041415810b6112500c40da000340c03905608100301d134008500300d001c11101c03010091001c00400841501183d100c640703051107031040311102c0752204210f460210686000d80045400400144200700d200c0d6451120010186a43c2c0b0721040d80303020843c1d590840b40303d00ca050000048404c01409080e004036009051049000000755944410092142000c03800540c00035082c14a210b80c040d8010840004441e00b5035a581d003046070301090031307080301b07911302603040480030400100461120074040342000707600a4a03400000e1801200c445004005600740700e0440e45030020074001c5503201031408a010360380d031500203015a1035142c00d95940c0741c3c1e80f00e0984c4e442e00341c00000c40e881c46603410241e07030646 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 16324557 1250 16323307 16323313
    0xf021e1c02032a071205030f06010f0e10050403080304080304060c020a1106090406080d020106030606060201140a0902060403020d110109050d03021509011e0b0a050607021806010e061b 81
    0xe01081480890000f40e420800500a02c12000440c0342c40d42d80d01c40882d03603810219482c0010b50380d240010310104100807004500088100400d044400450b40c1d03002000303003411040c420780407a00401040b89101090310544001615290152040302900d010716030122640780d6a003820b003030400e000d030011070702114018280300c10a5080c3d40b000c40c201d05d510b5032204140580048075010002c0e10703005200c02c1d07504256904030008021a00300320040c43e40b8003580000800387e0a50030008240e0703015803c44415a07041061051099004c181c442e81c0c03148a0340400a400880307803001880300c1c13040341c0c00a50311040c111074040a101041c1d031189112002600c40c0d4510907595014482d12007802d00019016030001091901c23054000d0014550007085400000f601d0745c1000c0d00d00304807030300004200070f056660340c0500e42a802c0c00d2042c00080d00048400781d06240d000d0340003440d54909070f90080354040c1c81e000411010703401000203800c5140014002600c80b000715809200d5112615200102c901c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 16325807 1250 16324557 16324597
    0xb0a0e09100f1401030216062c030d15090204060f0809011a0d030c02120307031202090303030105060a0504050904150b01090308030610020a02030303040f030f020705130f021e 77
    0x200c070880da500c1141e9100744850350a51400034020072510079071103040c0c14150200300083c0e03500718105009070b210388901e40004141601c44d2005006050031040f404200101d6a42e002d203ca100109403819089555008500325400f40e0240a10085030b5026070b81d02c600200b03011a031190040500d62098406680300310315941d03034200c051700303941c03050941400010b80100129041e0900701c98042c0d0300e50007400c2c20001040035502140d003490b26843d010704290000f1510000300740d84510b9082e01030031080c07015802c0002440000380c980c4010b110b098814440003c0240703040380a01d0a45009000082c0903620303030300d02401e0a40c1c00b04000405007214a01d040555281507000d000700400b5039411980d03290541e907603d01880181d0b55080d8842084d0b105004143d001a0740c100000e600ca03601c101c4841c0035054803442c018010305000c00361041550001e95051016849140b49050301d95000b640109550321012030b0316000744100e00014034800b2078640176000344148800148094007041d00254980 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 16327057 1250 16325807 16325821
    0x20c0607020a02010f050708090a0609050102010b010e031c02150f0402040b040213090b042705011506020307061109030a0606050f0d0c0b030925050411041214070b0a0e09 75
    0xb00c15254000b400f00e440c203980d20841c0303841000a010100e00c039202e80c1c4e10b458544400101c0d01e030741b40d0388440005040c81d0401d01203035034280035500b054470080c02d0080c04000032000203a15007020110034800385040c021101ea04c1c520800041d0101ca442030030700403450402040b121680c001c100d800b40c1c003071030405d04803920a080502c2255910a00c0c44c019101450030b0101d040044d004014259a0054079140c1c103004900d0b0328020700c26080514103007100c201c507003450030f50f080d0703084d080301940f007040b015a0810089402204440c001648030074000f0b600006821528a1402158411505446119115820440c0990001c4140c5004a1303c010203001d007001000003c200c24840200742400300881002103103510000b442c1c200e2504415034004201c2010959130420000240040d00911040100700c51300342407140b100c0d4010704090003032403d401d211450b6224290800002c190707070110085800e04200030301c200009401c052003656a0f8100c0340d14000c0c00000400d070b10f036104083c1c1602050304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 16328307 1250 16327057 16327063
    0x6070e090c09010c06061701021803011104060f2a1406072c060f03010e07081605030907030212010e0705060405030a03050c03040e0420121c02070503060a020c060702 73
    0x7081c1404603280e40380000c04001140c100504001c1150700075203074100814900031100c4a071100c0011403000580301d0580c41d01c824204085040d11178000d0740b40c41c10007c8108050300450b0140d401d14240300702180c0d000401150050340700c80110195002c5090208030540c00c01d00b0a0002e030b40107403a00c0040c070101c400165202d0b0415250100458031400c00c1138075141150803880e440614082d5044200c6003854049007560b0300041c04c041e80b40e00000014030946840c555002c2d0840160315000b01a49010007440900c00e240b14003200c03d001c0003000080901100700085406103601622001b40000c4800440b03000c0d28005801004a00441c40041500d0620b14281c1c1c0c200c5100500070620350a00da2410f5070960320039000c0d200706001c20007000c600500301c1c45149015030710a103800400441020944810710f640c86140e03503c103400941c240f0705a8030340080d130607804610320f550701282c081d8041004c1c2c4c40c10406511490b01800b40000300621102180d02800c0700c69240e170148c1e14031f5541d21400702e072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 16329557 1250 16328307 16328311
    0x210203010507020f0615010302040905010806010503070f06080103030806030a0204060b03060a050f060405040504140609100606020a030c120c05100e0c0613090203060a0308160c0504090b0f070203070b0906070e09 93
    0x139550340b040300060058040303004141704c0a44181001072820352100080c038255a002d030803180071540444010001070508014035001441c40350a207040c0035041a0000b0410760381031201030100290b1074041071441c0da041c403100d82c003280c1c010020010556252800c0850341c004854680c840c038000540050a420001406041580c0040c94103152034144005c00008040c007134000d80302c1e2070400d80744000c186010002c881c01609182c0c02440351011b527000410982d22650003100840d0413109400c1d00003601309969450303003948001031440c40c402d5604100e8074500e801c0405006403080304400002120325034800b080c0b004000307050b00e00e121500010311030548504003080c1034079174010b2000c00018001ea400785802050042892822036925161080c10340c11440818122845041c80c4004000d56500e0b0700005040984083c80214510f854000514400800400111002d50001600e9038403c1c1b0480390075a0b442a1011b500d82400c141c0c4039520b200072144a40400d6240e9480c28891a03c3e9200c28 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 16330807 1250 16329557 16329583
    0x30e040e0c010c08031003020306040f050d11030a0c05011b0504030506010605040e041104150e0907210303020c070504090803010305010507140406031503020a15020606040608030405011821020301050702 89
    0x310303601c3e0301655205480c1d03000400d82690003148607408070040e9014041180201c3c00764407907854100d001d0409a09202c1600f00e035400f4800000080036000d440403041d60054625401e22052240d180c1c00c0039030160440d8a0441a0401800c0e030028080740c012014205070380c0074034111038181c0e0700c1c2c0c0d0040da20361045000d0740400385090000a40050090314404071550005000030618940a0b52560110f00c01c23604980d6003600b000f000c1000d2030b40f042103c0801020495200e01e0724020008200e140592121743c050109600001c40300c07030003401040a034000b803c001e40100201c03503480c02c025541c0d401c00c0c0411100341d400c1401258041d8809c1903028070904680300041c1c13910b0f02c0c00b072081d00180080d14007074001d000101030010141ea10003245000415100d0040090b401d00400000c0c20598000e100c98420b51502600f44120722002080d1000d903042801d2903e50180780d2504100c01302040d51040d12a96240700e0400c8003040d40c2540e500c0140d00c00e500030b114a032603084c010303a160200c2030000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 16332057 1250 16330807 16330817
    0x303090f0e1801060b0315030115050f040c1b05030403030f03050f0606070f050f010501092406110708010e0705040c05030f0a05150904060905060108030310090b0105090d030e040e0c01 81
    0x8202c9520880800311201d40a00b40000b80143d030f1050142c800750030031200307461445c0502400756080d04003806503a1540a0091091200310305100005044e400150a0140255910101c1201c0320303000d00c004104450a107080002140702d9840d06966030303886808210002a0410034011280707010b4051203004058070451f901e01c0d6074400e01440300300d410041007920315080041c02d007000b148050080e40f0800031120004546d9605000307100c02603400108007039101e0800419442008040b5582041c10340c1c0081c40d01c074100348003400384580f07001001c0c0c12100440d4a8115920f10361030001418a040f54030a4500f844604003446090b5914001102c0d85010a075039840020031118079644115032220784521240803540d44e140208a20b0501100c1c122078440d502c505100c00e10000f001f0060043c04030a000b1032640c07816000e84d0098040511031400200e0701d0f404003100d903a0181064900c54500684661000c034100d040c0148a82c0d418100140101c4c40c203400b0b020044030100d0400b035410760607160 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 16333307 1250 16332057 16332061
    0x90f02101d0d06020706090b01080c030d0203090f240c060f01120204050403090b040e1506031608090a020d050c090a020c0d120b030a0f030315030308040209100b0d060303090f0e 78
    0x2030028040402c03000300c6080c2e908000c94000620380f446855003c46c02041004115810f214045143c290320341d040b1440780d0f00c03407104d5140c0f041c0d000040b076030800003c3e00c0400203004d201010404072044804900d02561400d00c1a1004003060409440c101d000c40c0122003007601c48402d0360100160078065040e10805d411010710140c100307600410b8100c4c0c403a150403c900e82c2e0300c40d005041600030303801c100c820f0201002071151114121404400307410040b5403a0745941010050040c00001142c505424043e4441c000f42c89540103101d640700c1e09801900c07031000c0d003203a441c1c601d17183c005280e01d0500c83c441800c003040b24007009100b92105c07006138600600071400ca0303034800d0ba282c104c50b80030703103918079140e4584400e070341c500740941e06c1040d100d40c0882c03100605601d405015958a10700078401681d09420030000b096000e420709400030307010b0b2030b121045e031034400d010000c070045600b0501380c10344002523888800010b43c0c000d0701280d02aa0700c112800e40c03581c0018008010034440c140c4d1004100d40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 16334557 1250 16333307 16333309
    0xa1805060706020717130e060907050304140106090c080a0c0809070b1b15010303090b030906040b040809100f0909021306050a021006080102090a0803031603110904090f02101d 77
    0x10081a1a138010b07600030070550741d07180c0003201703542c4130303421035000c10803144010004501e640d601d191300440d04482c039840910b002070005000780001400580040b002142c0c400d01e00800b9030010028001c000014050050b111030050302075041500d4401c8480d10b060407035042603104003006401007180401800c007041c64001c8150706600b02d040c4440d081c081489600c41410f4041100ca40d044180c0c0302c03d054558950f0074041d1448409034480c03c4c4101d410400c00003001404105694041da112000042c2a104d60804200600803141520782100c0480c100746c007070340c2c2c124076901805111130b51418901d03510380840764103074054110704507401505c2d15410700a0500800c060700d100545481240d2070100c40100c501c094550980c030070113440e5800139100103607040520154010702a1940218514100324184000d200c00c1c002d5a0400c1581c0d4a9103449020080400c880c60316100901c180300c481903d0a05441521556501300d21550101207000000f50090f50940117001c1c400003200040c001d510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 16335807 1250 16334557 16334561
    0x2090106030b130b0a170d090608010303051c0b040207050705031207050a0b070e180106030b06040503030901030b040f06090608010b0907020a1101020102040e0a02031501050315010c02040e0f030a1805060706 91
    0x40c61312070340715030060000b2540400c01140e01c0c6001c90b13860020b0500100410019103903080ba03030410b404224000d4010b03c0840d4100c0304440c000c4d250001841084008405403c0003856002c21a0f94032a00010301c86051003c0003034910f055500844c203a400d1091145199000d0f40b007158001880c0ba000096010042903014004c15807202c11420944220f6190500043c1081d800300c4203070100d0001c000c01405690b6151280000c007200646a091405041c800002c1e900d0040c4c03460b940c1019150b50050440717454542101c000030000740814864152a04a0403020746902d0240c0841503103402c011520f289010307214940103200341d4024044020f041d40b16000c4001c1c1c1d041000b810340d07408000004080e20090f5059110b2202144010b8803410107038a00c58052041d07003411030411406105000c004e001030400000706100900301090314a1a41c070200d8041d080203081c90580e03010b0146500000e140100c01001140c410b90740342e40d011000d40c4000344109509002d6140c124400740004070000f1459 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 16337057 1250 16335807 16335821
    0x15020417060c0406141b0a0503030a0b060301030b0411030a0c09060302030c060403020f1c0b040f02011106040c1202011106040602071506030503030604050411090c04090f110f090a090c03020702090106030b13 91
    0x501400c1082c1b1200701d9009182c501043c0781151264030002c01c0007000c404c18441c0c0e41000404440ca18515491034817198218100503101a0441501507081c1844e50380c1042020005035010f81820314140e034072080c000061a840c071081e80240118003c220003890080c0c2103a0a5a500400092200c825074080c40b03100081c00040300d40506005003040d001c244060041c1c0e01c00c9109410382080d10300644001400c0b0305c03d80007611242c0c5c1c4100c040c0000900714000b0307041a542c3c03007208005c020205000481d651001c2e0113050703c0754054041070009202d51500249100341c012403004091080043c480002c4500d03038403014004d0341052022602c6460540c2005810601441c00c40c80090500000101490410388031075084a000003001c00c80c03030015001d00c0c11072b8200c0c810300700a0340010381c040602900c1426408500c428000400d001281d46106001d00a8072030700b1010400074400c00720180003036001c818182c0c80b4151260001039103070b200f4000c000c0c3d0088054498007003024801d00c40701c042c1041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 16338307 1250 16337057 16337077
    0x90203030d0e070b0d020405100807020d08060a0302091504110a021908090603150f0402130b070303021e09030106150f03050411040e060a060911040b030415020417060c040614 77
    0x20f44a40068000c0c240805401180f155034001030703481e8588000c200905003440c5c0141d00340081310040000040d00450310f002e000100303041100392039858900041504030141c100075070002c026014030038518527140f4113142c030000170f8a0401450311201001a00b50045543c031400580c0a1621160300720701003005081c20b548240c0e9201d0a08880e480043c130300d9002115000d03812105aa0021500d1070540c0c10169601d100750303130451400c2c01300b019601c043e0403580101000f11a0004041041602c2941141d03910f1303143e00d0302840403a01d100d11039040c03927014100891003582040408115034066a000b60321854007616038590000245400b40e01070030008000381c40c84095100143d07065240e502681d4400406803010b023245150640000080340c1c420340103080382c1e5140c0761a0404244440301150250341910150b80e49035560391070110405044107005840f00c90001c2400a03080d0304000016103542c1c1d100d030561340b00d980c604078030106c580a144104000030302080002110304c17241c1e00040142c919 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 16339557 1250 16338307 16338313
    0x6151103041512090506040501050106030b060d180206040e1501030501180c0e150a03060b030405030906220b07030323060d060e3004030818042a020f01090203030d0e 73
    0x10115662000712091804c00380c0c0c8903044041080300300b1500380300d01405042c0390304003003054018080100340d080c06031101c1c5040c1c041e9188405c4900c0c02c0c0110500140f5039004000682c3e0300e440c3d491155505ea0141c400f0035031103c0d0003802d00029030081c0501d505a8001403402002c65228104020290000006803420300c141d0740b200700c54507260100c0c0c803a105071003170410a55074800b4000040444825901402c4890070034004e1000045000c400c0310421b840464409031070b03075080c517901d01c4400c64010079500a103880040005901c0080006001281e0094a0401003d0480b10546a030540b125150960304101c40700080e4103480c00e40e003050300250180000041010f6040c80c81850b04120582c80f043c08440d030900310103a07407080c001c19403c0d00125501d460805140d40e0702c44030035004007694031040300071122020881c0c4d02c559010b401ca0a407640741ca001c030a00d6110300003a41000144c6030000500544a013100310440500900214a90180c0250718003151402404001d112290410f04180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 16340807 1250 16339557 16339577
    0x30601080408130e0108070b0c0303040303020906041e18050622020d050f01031205040b04030201080c07120f020d110304030f0302030405090702070504050106210509071701061511030415 82
    0x1212180500f40074041007800304403254140603440d458141d8541c80602d40d4082000301400001020060765080755050a0141e150b0b840080010f0b154003694021498850400c1c4ac604031540d40050130720120ba8190000e10a80b030403010700c02040d0340c002c94559404c450b6241e0003800001c1c002e0003281c1c9061090100609103034000440c1c001b92802910350150a210f50001403050241e040144100c007542c6082c0207242c1890f100c8890354034002c034070000c2e050044400000c1e440d18201022211603a6100d0100d5201c41e0400d0030103010b000c0340c0046640103200d50031960310210b010314030034200d21440c0300045041500d1a500e690010f100721004030b04501003404005402d844000e260360045074a9006440c0240c140740620080310740503070200003042141840800e010540703089805040e810010b0100c2d890f594680a20707e084d42c141d0005509111803400036803940419804030303060751512180b003103d9101001040f03a007401c01c1140c1032a90381040200f0440e01e0180c8120481c03d5040b0308000d4008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 16342057 1250 16340807 16340827
    0x1d0915062b0608060a02070302070e040812010b04060203070602071a010303020a060e03030c030123060d021c09080a0c0516090207050d020f0c011409122a06030601080408 75
    0xc1d40000d600c0200140403951442a805940303000030000354020102041401d160521643d61040d010b05201500b0303038001a04001d0520074401c003405813500e24280316a5080514008000f648400075841d031002c5603500102e0042e0040782100e0498407507900075414000035032100c000941c0310701c4040300c5903950404983c2480512108460003103010390041c006884050a1500070354003825040031240e002001004a0401e9500a81e81920b83d9140701d4924101d500c01c03401c1d00309100320402a8040800f01b454501c00c242a00180040c0000445200b541c110305c054000549040b440c0c0180100824080c1c07405003803090401404260003a42101c0140d41100a4500c1e4289203820911003160001007850610208100b04100c00d01c05200401a5135502a442d40e00d9002d13003100310381000365048500340e0f103104210070313218003001c000c0c09400210509070b81142c4d84c40c5c551501c512003000d00c00c9072040c404004a6400500390340030301400e00d0340c1d61fa00c004403000304000b1b104989001d000c1c003201c418 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 16343307 1250 16342057 16342069
    0x60903070906210209010e0910050109051803040302060d020304020604030c031101090602060f0a0c030f020c07060206010605040e040f020a0801050f04030306080d050403060c02030c030d021305011d0915 89
    0x4100c4098000740362400d00344030820200f4080c0042d40007540003114240161503003083c15044442500c0640c41c3c580301c0004450034003c0e08481c815800b4100b00c00482c280d40207031f01c024080c0f00e8000b10000d01a05500300da540301c1c001c510001e54808010721400c40000003a80045034014030043c0100c0c81c1a03100d0350340140d02041c0c0e40081e82c810b00c545001caa095600b003001c03640644080e0004010034a8092150380d040b01c0d00401c4220819100c0c00d80708500c1303010b5000120500c091901c155100c03100b0050076a6603448078850740d001442100d0000880f01e00030001c0383d081c0c4111614500681d0348a840d00c20b050183c009040303821641140000941c05030a2086500a0f42c42045452240c1420f040c01000e6a01c2c1e40c0216144e41c010160180042d5045412101200d51000340422546142c03034041e030441c0078007910b1151a000028881e007142410b54006c1c442e800140c1b0344d131103089446000440c0d45010210030445040240c0600c4070076454440030300c5511104120100310009207240102d01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 16344557 1250 16343307 16343309
    0x203040602090a09061e031104112106090714030a020f040f09020712030204150c020a0b040e04060501080a02010e0402160813080c03010e15040302070f0e151504050f06090307 77
    0x80c0a5a100001c0c84050300018440b807075035440ca240d4501b100c0c2581c95034880d5440c613407101d5100c2da075a5a010341c840f030403900a40e041c1440b130000e441006021900c4011140368102e4015101c0c40e11000021000c50064000c1000344401207412811640d404d19010025031040c00d00000c0c00009000c0010701c10008846400a03104205016031105070620746803c0144120b00c90400781401804284103154912810142a0415180a5000140a00202e9070358411a00910752007400000d004c22044159910f0714086e51040c5020002c9a0343c0b101415294405404000d00043c0503d041204914090b000380041e0400d5041504401c00f0641d6460321540c011041d00450389800305082007014024043c0b204030007001d4009000303000c00012641d8450004000c900c04049958010405151007004102d01808613020521007071a01d4001007942481d040303a0300030502c826002415240e00304204a1115004141c002a0400342008200001c0707941c004649500010240031440e5aaa02084004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 16345807 1250 16344557 16344569
    0x5010c050d0e0a02010509010e06090418050f010905030307030f020c07031101090b03060d060203101d010f05010c020102060c030601020f07030b040c0e1b03040303021b06070807020a150203040602090a 88
    0x81d6515074101c540029681448541c140d036030055201000076036040f4045030300c040001d1070302c0da0032502500b0000d19207005914a1036040340c0b410f10080f1481e1b0505009102950007407040700c2510041110017401d84d86510301c010b250360020301c04150041d000b078101e044091003052026080c0059620558906080c0307901c1514201100c0701545c000d96000780d1040b01800201071414694980b0001040800301c8401e80107081d19800800501c0988105142e034014158071051825400234282c1948900c010a00422103141e200e400c0005483d8085c0300720300483c0381c0c103070064045c0c0e0750b0348a41d41c141030b000204158154020610710f080140e509000040c003640c07291f040c1e040141880d041c01d00c2045a1600610345044155050001103078882510300c40c01c00c0d080c119243d80b980c8030b00d0100c020340a240c3d4141091391844150800c8190045003c0340b06290f640d5a1030389981d034104040740e40b84544d0b24080e0101c824412406400d00040c1c0081d81d0083c06940050701c2c0002a074045007044120358482 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 16347057 1250 16345807 16345817
    0x5040506040b01170c13060305060103030801090614030604030c050c060a0314011a0d020702012307030e03030a091703070f0c090b030706080c091815090a020301030c120305040305010c 81
    0x700400a6600c5210301418804100c01c0c138201d4140d503901c5d43da00c40c600300d691143d401c0f002036010780419600050050355000e010740300c05503943d16000c3c001080a000e2200c1083c1003078804248071310103059104003000018000d16450b19261015160b4841c07c52041d1454002c041d12002c044d251100288030382d00c21903800064040f80380711040004a01138202a03c0e825500c181014031451b04401d903103086000400040c0c0d41c840c0e61005903032156150001201042d070044100b81c0040f11400613065680c001e440e1006010320000400d52684151307400c4101107441c9c80300910044801920303402c407154035081109d1a254064035004401c40080e20704880d840c0003001c050203600800d01440d400c4090940080001c54100000030740608001404100b09003000b01e00100c943c4d070340c1480c0200d40000721742e060426040c40814500a004401000c500a080081c0402c5000c107461007100d040f03980083d0518082d030b061007000780d0503140140c41541003020510010020440a106102c08a8125290 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 16348307 1250 16347057 16347061
    0x204080c01090f08060402100e13060815100b0703020705040e01050103030f020d0c120c0c0f090b06030c0708091f030504020a06050c120c011401080c0910060203040303050d0207050105040506 84
    0x42040c040760f0040030520520030300c1040b281c48001100c507046079049a01c4240150441411185018582080f80c1d000d0004800905404000d074008400c0d5215002075980c001032907207800411401c29107403c2007036401d01004000d8688602c019040961291054807540c9030f454000030140c4442c8260750200d40d540301300410130550014044a844600c0b800130f8242643d2894015003010a105030240081d2080c540403812207124401200c2e40c6507011001a003c1500c6030211911410240200901e070351903c0c4201405182c402c1c00d480c030a60100d1415450520196038184840d04818030b5242c010580d242c0304102085107500c00181c505143d54000b606142500400241010580c001d0003402410407001218610105410152811705107400350341d02c0c0e40c240700c58010403500c15030070341c00d82e2410008500104013095000d0b482c103080300c505903240c851050740b910820481c0703e0503000d40e004110400c002406407016010070711100c00014148800fa84809094480440d07040340c6613085002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 16349557 1250 16348307 16348309
    0x180503120414010804030503060d060b090a090302010606030207150b040b060f0a02010c0c020907030e031303030e03070501090501050403110f060307020a120305070e0d020402040f0f0611012705010e010204080c 92
    0x50b0703007688000240380038656400d060b14040d02c00d10024184074081c0c42c1690308041400031981040786582d901400b041c0c1c0d07616180c40d02c00018200084110015401c040d000592140b090095030351058120103d404546031a50700e00300100025440c0e947c0103600c900b010031659503164054049502c1c0402002c0c0e4034012071400030300711105030383d0907024403140710000409030321640016544282c46080002c1c03200180c0c80c8541c0341d400b072400304d507501d486514808404c041d4003140c1c0300780c10841501114401c40e01d0f0001522020883c0c014140041c600344010404170348101001540c0705400b0341a4500481904048ac0a6a00071100b03100568400c0c80e00700100803a5002040c10f14106103000c2109040c2908010301407020440140d1180103018402ca05654440e41158028801080d1002c4902da55111803020b82603544100340129502c20b00b4540942c0701130240c2088024828901c02036001040003041400135100000c0e9444c0d1358030f00a0100d0403c00b44010806015103600906052000c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 16350807 1250 16349557 16349579
    0x501080907080a0507080c011409040504060902060d0b0f0a060f050d090512031f030506010506090f060d0b010f050301030506010b03130203100203010f050303190c0302100903050403060e0c101805031204 89
    0x40c0800d04000c0402270000040c407120094803c0d00d2000c6401140340d0301c940c1080b50140101c400301035032001c400182001c00c01d1050788109400441980e41110000d040c0d0304110080600c1d10841011503410850b98036035a00c21802008203003e501030002d01d02d20184c4035240b134034206c42c6100c100c602e800414441c0703000e070304041001941c01c07226070582d04a0940c1d48003500e400042c82054018a0082055071040c1e03140c0b05403c000c0708019020540364028825500090240c508943d801704910303150124a40b4403910841c0c1c140c0b608800245075617403800e4502e1324580d0004001140c0ca03004a050800184d6052141c42503840390110003607143d50619010000741c00099004900c00d80c8100111a1f040881e05125046580035003407040c00f120503030038280c0c180342803201c0390031084d46000000b508054011000d401a68000d6404100c910115550982d0311420640c41c107038045d001003009003460b44299010502c40320b8240001d12102c0c0e4800110385042c4d0314144801c10304201040030311a100c002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 16352057 1250 16350807 16350823
    0xd02071401051009020307031e06030b01120f020f150d14010b13030b0403031803020703050c01030903170612010c09080d03020a17060414040302011a010e06040501080907080a050708 80
    0x708064145030f0b025842010180c41000030349500031000482c4140254000030310303440c060302812480d0040002c45401400d45000c11111060090000300b00d00100407400010581c0c4240340b503980741150303000c0113481058044a5540581b0800340940d100c0c403140301502c0c8402c40040049100910030b044502400e905801c0068250800d0054590a16107140014100e88d0041034565484d1904d09049001d04410603030300344000c8402d0840c40425030b0004640341200d00030b50941e2071a0080344011800e80e03c5a0740e01500090320704c82c038000c0d403c0440d4070703064104400400244800c00c0c2c8402403030940d524410f070000424400c1908011242081c0708009010070145800c5191880e039010280a0024401951000b2851f00340007a1140c0c81c7d950140c5d0000008403170040c0185400d140007806020580f0700d060300b1250205002c229540140e08050b00c405000301650b0415041800450b103c020040c0300411600c038646000a01c86024130041d05d00c039003d580505030a80c104500545000c80d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 16353307 1250 16352057 16352093
    0x2010614030a03030f0b0406031a0604110301050618030d110f030301030321060b030408090f040501140d0804090903020708120f03010311010c02030706030605041a0d0305031b0d0207 80
    0x1000030150340d0380c0100b0b100282c95070608000400390308260142c001080d05d140010b4000d4580400801071145440c4101d8507400503442ca40d2840d590142404191000a590341c418a00c00707000601c400d2030f155001d032603d640010703254108222044c00007440c000c0b00d0090400820141c0c1105c0303001803810b0050048054200008620719403460754024080c0e0032401c0381c54414032210503d5641d401103a0040402041401c200b85c0c1c072803c10f4180240550f001c004141d103c0c0c4410b01040300581424007540c1e04a8080111100310480e45030144184011008400c442c808010440410342c4420340c0b0401c0030a41c0640d00510300d2904014401e89040300140c000580c0442c10302c5003d450b200380c001140c9c1500d910000d11064107000d0390050310340712504000254540604640400c00c164103038401b408880b001c543c240501825200039501d480031000a0700c0e04400140e01c0680441e0041c40290741103405629200c0500300f0039603281c426900320382d100c440050340016001003031140e07004142c000300203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 16354557 1250 16353307 16353329
    0x615050112020f070201030c12020316110c0d0209070309050f0705030c09010807050613150305100f080303010b0306030f030f0306090115120906020c030a03061d04030503010b2805070201020106 85
    0xc0c03111419000e4004c8040080c10075841380132044003039100c0c0301c1030050306e1000c490540d224100700741c22644805103150100d0000d05006401c0410403800511035800362405485182400007035001e000c081e40b00181808241503c0e9031080d000508c08200c190161a2a40042c24056080c00101420174080103c250320070414640180411000840c0210454900b00c81280d95030180e07050b20807034581164010411031601a04004009030150016882039043c2c0040320f003440d07240d0700411907540040c003070396641d40d1040c401400860b080000840e0089002411512207155001c15245958085500324841681c0030040c4112410034505113405040814030020000469543c018000008140880501522020b050741441099411500001105c07016a549c4074407186000e400b402881c80390030690014054889466015a18181c0c0a00da140d502d2a18591811181b518650042d050055121074920440042480d44100c40c010703884485e100c0072344540590002a0840d031642d800fa42181d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 16355807 1250 16354557 16354567
    0xb060c060f0a140a1a040c0f02070501051e03040206040e07051b0303070c020f010e031b120d0e21010204120618110d050a05060a0504050d020705060409020d09061505011202 76
    0xc0c0c3c00c58091035100c0ca090340002400441e41107224440288011416049481c140c0200d1015030f011070740d500303d0030144c0c08480c699640c510044030148a0284414103100c010840726500310310001c0115081800182980d0515403a1250101d2150007079403850081480041c0309a0b100702038130035540300155160301460851400d0f440203400042c05802c02846032405102812640e0b02540203c4140301c1c0c090100c50312007540700c901c0ba400310000c6404611039256002c41e6620313042e00080740d009812565850803420541c140511466880b42100e9401d4404890000003074040d00b4409800100700c0e02c11407503290810b5080c044101c030750a00c140090002c43d103000c03c0c00302d0954400c2030010803003501c4510320084903040c09800d01040010041441c0114400d025040a03a900030300c0c0214028020354029101401c016079403541c032442501d070485014401040030034081d9008e0600300000c00c002040e6a41c1d00d03580c1c0c0c01100c903240c1c244210b801d01c4c950240107559000c880d02c400c42007142030841c500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 16357057 1250 16355807 16355831
    0x60302040513050a0e01060303230915030405070806160908011a01050f04030b09010c030e0615090a0b030d091415040905090703051002070204050c120403030f0b060c060f0a 76
    0xc0c0c210b4050700000310384070408620070001660298100b041d604000304036040d124a00140841000035841802e01954051914068142c0007190043c0710020301000500310300f1450410319401c002c0003a10540900307100010003032001d10003144608620700c150719000c0c0301286d000c0c11f1051980c0000300d55a00d040819414030615081400d0611007d0074815118515028400b505120700c0e0001400c089522061194620f015001007205210640f02480075a40440c401942d451040341d0200006000710300c02682c50402030316040d0400c6108101144c446c1c20074010a241c42d8012084c400040c1c41710310100300f0240c60301307118104e51400b118500528910000189000c1c012405822009a03071000800c0703854204120170401180e104050300e402c49525070241d0002e411844060740900c0c1002c00203072819031450212950f1014400c0d10320700c2600e0350744085000f4050600034010165551034444500c3d66072001410708a244003000304504d141288901500303500c050aa81e00d50740c2400040891 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 16358307 1250 16357057 16357069
    0x3030206060f06090d0302010f0506040207020307030305130e0103030f0206010f05010c1b0317030a050c040308180102010e030d0e190201090302190b040902030a05130c0510140c03130603020405 85
    0x2202080369100300c000008400901c4030b04c1600d00d480d60100072040039000701501900b180b51282d144820411482d56410288800d900c00c0d114000d5044d00041310600000380500050034440320400c880108180d00c44184041100c42030b04260042410b500102c0c212642c10040640900a100c0020141c28a4000045c000075036844005003107400035003405c1c107068206ea032410021908118502100034100c2400c034225441510000041c608010003d080c84920001b241d08490348102040c0c64100500d5840a011413511410750442d501da44215540c01010000f0b0b00c0800c01d410340004800d4110440071b440c3c910100ba03202c0780b1607091220103015071b80240800e01125015100300c0c0204182800c8020180355a400100e2501c0000c034012580310ba65034051407146040d03240030042c0c1d17100d4034080100d4540121004007960700205060010b41083d034402581c1005034204602e0f54008122034030490307008044101d010f81d002041502d068100301000c24024485820214a0141041c01080c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 16359557 1250 16358307 16358311
    0x504050702012c01020c061003050f010203060105070b090a05010603140c01031b050304080f0408030403060e16031103010f02030a0c020c100504090506010c02040903020a060b01051611030a0507080c0312030103030206 95
    0x440d00341c3c0d0301060308007600c00e404039604116820199019854000d09512584d00140401d660510800301c45429484c0305101320303409514142c40c0c407070401c00d050b5941c0c90740302c00007005000c1d140100a03120000900c00d0007240c020750301c120b542d08409121200f4071840e06015461407410903052158038400103031094604c00400c000781ca86159291b54906101401e8854540546003051300003600250b40c15010000e030041e2482808140078244002c070b0080d40e9640020381210304844400f00810000310306d8002c2c0d0038954070140020a04254400c3c402c01240c004440781606141c66907080c280c402d6042c055000c4a101c1100e501444071030004000b4814011402141c1240c7e9907040450741c1ca80c0220a07840c8001c4c0c3c014418810f902491800175116600c0d00000c994076410150080ba60350f00074419180800f103070028005048140d51980c200c0902d0041869800d4002d9203089004294140a04800780028500410141242e41c0515140410b102c0c001003014ac014401800026400b00c1c3d0b0320703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 16360807 1250 16359557 16359611
    0x30503060405041a041b0603020a2f120c071502100b01031806021e040b0a03090f0b010b040f06080c07030c1403130806010515030c0304111504050405070201 69
    0x2d542d652072921521003400c503c031100c600203807502004104101c1444920107403440c400d180307182c140d1340c0c031040d13040c1e009803000704000c0b03900040b080030304944000e030240d080441c6403e00c0119400325400f0a007001c90690040d02d501e84001410300380c1503810090000140607400003140140f0080344025101c40c014000800c12580307852030213032075170321a4005e80e440c5120741c142c0c2c0c4203130800c2c3c7c50a40700a600c03500c84101400d030071264111403a84e845040d14102d52441c5c032994036010001c00c0841c000c003420a0700315507030003602d4407100c0030600c62500540a4104c20b00b2183e038a90420103001c14403022a4800d808019006040140400010382030b10707400c69241c1403c454964080c0742100c100251081d207411f40d8030011600b9000b90045448082c100c45030282503417441e90722841440000360703410348590b905100400129100416001c02140d216018550082c910320301c2e480051103c0d00041055251044040380031f000c18a42489060340004250000f00b0a00500e120315131481c400d086134007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 16362057 1250 16360807 16360811
    0x319050c100c0507050105060307060f030905031611031603150c030f0c05040f05030a05150c0d06080303240f1e0405010e0f010f030515040303090204140402010e0307030305030604 79
    0x58032868104005252140e00001814011100079440003000c0d600102e60507141582841c01181c1b45040100f000c0c0305454035562813141d1071441d044240c01400046008603aa484104102d50f031110107402481d0000c1c4c802d28040d0b001c80c07052002c152400680c90b100344c01c2c80b481304d541000092075a400c851b111408001c404181400303403080c143e004004603807141142604086003c04141d03840350040c0300362000e000c21080b101c1d868509140c2c2c1c50b5107940004000358440028a80b403000448812039000703240040041c90305240b4207000090716401da020900d50392010041c0b21560458070114044c102c0c4c10310040921074004000110b40000403542d05024285125001103410442c0c1e5141c0ca017003501130414005e40d41d64074a040c10740c14045500340d030502e404074000700e11000c844520b14220b0360000b004210003017520b1031641601001030000c40515965a16500058550f8003504109034041c81407a03a442c505800003610440c218559103100c2d4000303480500000f504403066070b0308003d0036031300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 16363307 1250 16362057 16362067
    0xc0f01050403060207030306180b031002070f0f0b0411060906070b0403030f140402040c02060c04140a1502060708070f020703030302031306021b0f010203010e0606070203120a020102090a0503031905 87
    0x503500da20450300068203160000805009154158000000319404020b62843c086500c00f103500440780301214803607160300568261011540590003910003103000b001c8440c01d106003556030400420116004803100980c80c0200414030500c0b91558800c000191255490408024009086071280707060080c01c144200e07000c42c090512070703400003440d405501c4e41040030f81c0c02031104a083d10000c50b402c070312490a00c40c2680c0950710101d01c00c0e0080e501910024141402d1104c2c2924038074084c80240d8114045031000075135400e541c1c145407504540c64000d445a400c20b5000200030303960003003200c0c0600030301c0b48541b900e0941c0040c06504030398041c600140c8035210340f03880004d0302d00308040161041d400885c400003244241c48040d4021191141100c0e00441e0741c904041c00c1c0c1c00244105240f100400b0005525400d1410080c488140b000341039036903c0f0b030741655850850300041c030701d03400507980400c009045060680488001c0d0008034019030803c0c010141e5503600e643c0010b00d42041041c0030034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 16364557 1250 16363307 16363309
    0x100e07080c0c010e1b09060303090a1a0f07060b10020601030c0611030405060703080708010e040203030f0a0201020705010e06070e01021506040209010c0c0e10090c020a020906030a02040914010c020f0c0f 89
    0x1104c2aa441600700980705e0040c40d40014941d007800c405003982c410700e2140c0202d486c40c0b90000c1190400341000d40300900c030600d009080040b20640716083d0001301810080b603100b00360300a004004451081c14000384054510003889007900340c96000400b50342c010001800481e50b81c000c03072130403507001c1e190810681d48601251815801540d00640d007082010a5500c10150402c11091041c2015502c150340d503a0b03a900300f15002c80c015200650550810040044802090001051035000d180009403520503e50784080c2103030482c0c50a00000e41109088c032004540c401c80c3c0300c000a074244014003600200140100c19071031f01070a42849075500249100c000c2c0d002c1c01e51510400d40087c0c1d032690385556454401d0303813a00101d8a44030b81c0c85030100c02003942074952003081651280c990040c1044030595081c490800c03c090080c9070305100d252403240050b5214012404064450317008401e40c030b80c0712688070342501d160082800a40d00409002c1103982c00001d10b941c00c40104a45404241301900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 16365807 1250 16364557 16364561
    0x507090b0c012f040302100e120c010809010b010203090910030215030603070b0412030e01050f040305030403050c03070806071214090606031606051204020a050405040b100e07080c0c01 81
    0x1500c8000d65900209095101860640c00007000b0540c21194500c0400040f406150603420341c0b40c541c55500b400c1c0000d00240c14601c518012101c01414400d54118402c80000c0c10f04004800f8580340e584610341080c96540c0c01001e9039023105062b0000d0000340da40c4400070b503c90085410701401041d0403c00100340c0361348044003400460b000360400101c08120a0a074041b0b0340b04603005c500901c507629000030011000421142106c0d407507458070f00b084256540407220a43c80c3e081c0b0504103d41803040710a85204030700180f008510842c0250794880c5545001c6003010b40074410144a41c000600402c01c0b4034020a44075441001807802a8a0400e080d10760301c01400556080070124a0030010804042d10004505001d80d208030300304c44061151544c3e11840c682e41c0d0050380c000807400e0000c1c0802d103410300c0b04140c02074401084031000c69140c1c4085011240103d4080d40c446845034103100e15103d01c40514005008451314043c524501410098903412029000e9810500c1c0040d440c41803403030079 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 16366913 1106 16365807 16365809
    0x61811030a0b0c031902040906030501060905090706080901140f01060813110d08040b13050109080a05070e04020f03010e1c021501030305070203100c120b0301020a080a050709 77
    0x240540d103216800117002d0711504c4c924204201000c07003190000d08060302500000042592650402070b0a4076003d5002043c80c61604c0b040c44040500440c1071010f40d905420403d28031b8a41c00319031801800011030800001d480700c13041c445018080020b485c100c804943c0e42c200c00d500c03004c05902e490090300d00d0040000d6918244e409150410041c50300c000f07405034110700c1c102540c0307402010850348a01e070700d1015410520018007541d0b07045445400074051382c42c0100901c10465840d55a00c80b15809203085c42c1754014002800c56448417598007072403401034001c1c06074400d03c0264903503a410300e01010060a410408003400b60344005030030031300b021130071128940d2079207541c4056032a94400c0070166090b008040405003408000d004520b41b5a4060f0359508103016260302c0c4104548008041912030790041003254001075202000541003440158005172075125104156000c0c100d17 = true := by decide +kernel

theorem cover : BRFrame.Cov 16187057 16366913 := by
  have h0 := BRFrame.cov_init 16187057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16187057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 16187057 ≤ n) (h2 : n < 16366913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
