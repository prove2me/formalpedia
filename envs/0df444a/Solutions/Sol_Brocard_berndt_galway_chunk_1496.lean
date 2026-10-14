-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1496
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:15:41.688508+00:00
-- url     : https://prove2.me/submissions/bc8d3f8b-7e02-4e61-b087-9cb37afa310b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 268884892 ≤ n < 269064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 268886142 1250 268884892 268884947
    0xf080c07020d08280801061b2a030c080105151903021c02090c0304020301051b0405040c09120b1005010e090604050402010903051005090721060e030d020f03060a06020303060a1401 79
    0x17846120f09014490000b0b11040d07440c0e100410a0401c48501c40e04185100d44e40d540401c0c04105c04042c000000700701161141e40000015000700d40f110080c50260000206400c05031501741903004900340e9103100d5001c103404180200a121150000c40b81d040354584042e2060000303502c110042400042d501a40b0b120422002c01000001035100318400c5008214903a1044540e010500b143c0c0002d198110003800140302c3c90030079030721220a80800d410240c101356642d028007031290007003641c100c0d82c1e10550070030301070013049107071501016003800d003880d030a07444041002c9000c140c00180b07a20310441e11800480c2c1564020341c9a84d000c0c0d90080140d410019802032034002406090b503101c1010b1099610001d61011411100c81800b10049078010f4402a5615802c0c007501c41121440304a0008001d02d44454802c1c0c03009101000400e0046500c03458020100003000c0c0c0d150307004000b5908200200203169807000201015191440c14040d4850700010040b9030b0001000e001c050700000720711015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 268887392 1250 268886142 268886147
    0xf0e06190e01020c1b0102060906070804050a120f020c010207050d030c080909071805090c120403030b1314090304030c0b030702071203091e080706030b01030e0304060f080c07020d0828 81
    0x30807444008541c0c5e1803100404001244d5070902110880016004400800c4400d0311440d0043d4100340030b6012262a40000d03100c03d144902d0045500703020804c040c01c40c801d015010310219500d200c1c240040c1070340c2490304000c0b031480d0303000c0369000b0308024003d01c0010410046400391803081130003424096561421322000390003d0182e10300d4000945080300000703858604030070841e01c00c0c420b50080b14180f5080d42d40c5031030b042002500c21824151184184502c1c1e407a05200c1610a0ba8107136008612205419041402c00001404000c842d400401c01400881c18070000d031400c0300c45060403507650350341d6200100e09100240d0000c01c1e43c02c0420341000c0030302d6030000e001008c1e0f404d03054402040c802c10030714815055000344116034040d000b03810200704040c02944800046e000604006c03c142244900c22400e50344103400c0790740070600451484603c0303607024200079400b16551100c2c5240505e1900055802405414014624000010440940110080c040c0344940301852944030002030103030301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 268888642 1250 268887392 268887403
    0x2100501030b2505070b04150e16060302040b071106071515060f12021b0604050604051203070c060c050f072102030a0504090e070b0a09090f0e06190e01020c 69
    0x400e9603d0200c0441403441c05034640145000d0f1141ca51358a09010783d0365400291000400594840017580101c0b02000840d0003081812a00076014150500d050b4000c24502a80d9400c1141014810721080c00942080d4048640490b002080c05030106010b0b00020300030b07c580c682c010a0100301811300f4036a12000d4202e142090203040310f1045d500d44a1000f1980c4940c020041d4002904a41c190020720701154018141030342c1450010790030300b0f01d0384440c924090003034604982c41e030b01030010001845814820841f0b9001c0300824071345141003104008000c0d041000d40580000e42d1100000b905c43d010748110ba0744440034a850710b0f16511241401ca1441d1403015034203c48485401c03000d44001d10100c121010210f0f9901d485082030304001d441001040444a21140c0313100300e030b50210704c2c007851030080c1520145950710200c2c0c45003080440426158801032114103581040c401018101000c40e41d01d91201c601e0031a43c000007400071020010340700031054206954030001d62400c402c080401c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 268889892 1250 268888642 268888651
    0x110a0807020c10080f04060617060f010504060303020607180906030302030a020607090605040315060504020c100b010219030305070c1b030201171012030c021e0f1014070302100501030b 81
    0x981d036207180280b0511000d20303014a0b040000071a020002000b440e068402c05402c02c0c01307981d00240351600c84200c03141c02c0081500d00007a03070380001e04010700d00c001a4445805030000b070310309100f8185542c1d4041d594440141070a02031001d071280303c4a02c2c0c0310309903210b0010007102c50244074403541c0f4200030351030b41e00c42c1102400500071940000c05280c02a416402152995502d0601d007900e0364944044400e000c5030031104540d15000000b90641c0e45001400b01102004050030b50108040340c01c82c1140c007000041819074004500c0a0300c401003506019410035010b00f000f00303e66491610883d000300035000028a42051107141400068528060b641541e1003130f2541800c88084040510315076500b1542c001d00b0042c840c07018400801c0c1040f0440019109092002003882a50300003505c040d429401e16442004140701c0201e40d20740032840c4102100c003074412001044c0090002011840002d041c00c0304405d00144035010140b080046c1d20810720301d8141000556103902c0c104402940554 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 268891142 1250 268889892 268889897
    0x1207050105070306150e0a1503020903280b0703140403020d020c010809070b0a090f030609020405010b07030e09090304090525090f061d03030304050105040308090a03140d110a0807 79
    0x4002540d070a01034420130060307400c0f0364070141310114a6041280c0010f0045941030304004d1007000010203c085115145d60540640ca015803188003180c01e01d45801c5c04a504071092014801919400c154101c1000c4e14040e007102901c14655240c00e410b8014203130074080b02d201040c0740300401041c9a80484d400030005c01c0f550a41e0008208000115001d940a0390b40d03110a03005020204041c0d21b401008102401041c1004480240d0b55115504000b68550040d11016180c08809085107080d100c1c580c090841c00141e20706041954078002c210008103080107000340e580c5000300324842000c00a42d402001181b00078001850410f46048040c510030040881132800d035440c000030140601408010341e004020090324082c64650215200c072450380501511171850700308044c10352024401540726034004d10020400342041e2400401151006004001036004448031000080c4d010a0007004c0313080300c3c4c4c481512040c4494054000b0b00c4c0c4820907040c0d0a60010b170388407a02e5003040005100300401d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 268892392 1250 268891142 268891151
    0x40324061202150d1103010f0602061026010e0d02010b0a0605030705031b070c03050109030906030b06041a0c0303090a03020c0103140a05090a060519050a06060e15070512070501 78
    0x44001c603038411003100c0020f5000880e500c6101007800c50f10050036484502c2440490040702c00741029480b03900170707008401020720000c2c042c40041d0301040643c0c0c201c01030401c403080092030302d140040c808480c135030030081501c201450054411401d411100062404a0580744044400200a4000d150040e082c500601010100282c11402031081c1c0e031080711b0584800d861540c071156440c407041092a101c0e000500c2c18041c02d40443d0048807060042c0d84910000100400c03c0d05004d8440c0486502c0303d8101400d0104290042c7c85030400d95040326801d107881d051201e1100ca00c802c130b42c010034402d40705030310000c41046603558002806501c450f000b80c00b514803040d1554011800c3d98082e49241d00244617003008030342e42c1c05156210940c4802c60905a03006041e16a43c3e401c00c0d903109070380c440703504038602c116045006050b1040d150014a44101003018500e060000303401201b001c07402900c1543c800070b10f260103108043c00c460000354001c0944551001e0b5418011241d007254109842c20b42c40c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 268893642 1250 268892392 268892399
    0x90606090108060108091606050418090809060a02010204170102030f01080a0b040f240204052707050915030406020301061b020a0b0f040801050a0605011b08090f0604032406 76
    0x55003165120141030755100400c3e036a00d00199403c1d0000b9103a841c00e40706c1c03c40300106800070310f6560740c041c3c5100d80c0d46654941c0391282510001d080c0312410f140803480c1007800c00010310321000300c0b01d4100d0240c444540b0b03403000c8001a802030042e64000303e46d10b550306144e6404150190f0081d0304c074200c00402000180d0300c40c03803400d94400c1c40c25002804d045604010402240707803022961103d07032081b01c00081d64060062001c1e0760240d40e90130b0102da5600440d0a0100e49007002c59103e0f50101c0e038103240d41c504049c55042c85064000b078409401d0060006003254203854080314040c0c802c070021241076990801d440e014000f035000344120400114480001070404614000c51320300250020301195685040081100141d880f001e04002806801c020004180c40280143d5104607200d90000451900c1c01c1d0000d4030481ea0820150080d0014107545400210f20400f030340c130031003000c1d1403c0d015600345402062507449540c20182c100807141c0b102d06009614050590440d0070510700c103000031540c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 268894892 1250 268893642 268893649
    0x8100b041409100e1521010e06090a0317090c0d03090807090204051008090c030f010902120102030c1b0a0b0a23090709090510150f0806130204020a1e0c020906 70
    0x3c900490010000e00e002081c0b84003031014500c61184c0004090204000344a041494000e80c060f5403100b4507515111b4170f0052074030a22903146d00c42c003008023504e0303094010390b0001c206c001c449008070114641400480e144c81c0c420032034040302500c05002d02c4201c11007401e000d0603070200b80c03086004501c80c02c6d4002c1a83c0b403141c02030300d003111406449206103003484917040d0b500c030b04010110102d41c0f1071850704003807075a4100302c14403034800024000180003849006000340c203800c001e00c80c40d041e0300402c10f108221502400319850840312404041c40fa05000d08550f06241c036510003c1c000413010424819103034001e600240001001e0351340800101c080144494035070350b088417020059004800c080209032159040401c1c0c0b00e114506451881010340c00360320032100c0056003a0350b00c80000c0c03c140960000c1c5078408000c5c1545000504a40c9840200c880345103e44c0c02000b8052034001c83c2800c080d0b03000300707201090b540c21070705c05003002c1c88603900c001c02c00e40401d1002d82c03107804000082080d504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 268896142 1250 268894892 268894921
    0x1051b01110c0703050c010f0f03021c36031704030903020307060509011e020303010b07060b030a0302031b062814010b0a0e09010302061e04080d0c0212060609040308100b041409 78
    0x40c05c607120409227140300e0f1000e800a400406601c8000070022413241508081440f90a080c001010815403600c84003419001c1001c1d0450034103121124003042d50b03030120b5005807288409418486510901342d680c2d03c1c0c115204092988025010700c11808041145d54221001d8400300d0340a81e14169042c0002a03584040a840c00490000d03800400060080034000c40040ca44c25003d12400b14918214201091030030f00426800e8005030004a650141031160070408425070310004001e118504210704005d48200122048005d101c0000301e2a800700407050308074961210400d059000b103907a41d500c01490341d034000080000007030308800d0480190f203084640c542c1602d030041c10150501928401d038100c0191030036070502c20004184000105180100160180c403100c80d5180380c0162030a20501c1508130f0002d500c0c2032a50048403c1054035101d030003102d64403681500d003039445a2100681100d89403050780158150401c00640840c91598080790f032018000c2c05d0b1a85441d50313031070710500c030110f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 268897392 1250 268896142 268896167
    0x40305191b260c030a020c01051305010c020411030f18030406140c03040506040909020108060405041524060503041403160602071505130b01060e01051b01110c0703050c01 75
    0x103032a4400039201050701c0407400c2c1e01c0314081d90340700b030780607803218102034100e8108400141d0180d00008640d90215810703c01d1000c0010282881070500300703035030700349280c1c0507443c0212410001c01c940200195038030344d0030400000002d00e207469668286006c0e0581804400c0354540c1600601d0003d40582280000c03c60381140c0341540c9180000202181900c80f941c41310f002d0341c485100500011445a90f50380040009240300080040c0081561001501240703000b810b00f44034500e440200300108078003100301d8034030b03605d0700f04002040342500040710210411001000ea03001001c00c2d010525540002c002d6000314001c5480c0c02001413480c02140d628800c0c0d00740c2c10449811441c0702000608240c01410b28a48281c04168403260031000c03110484204840c06002c030210200c0940a100301c6941c50f034054610341c60200080e143d2040003070300b148203421070b011380010000c40a0701a10029400306014208084089684800120340560790302c10030700054074540101d111401581d8002c12980b03084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 268898642 1250 268897392 268897427
    0x10c02030a200708010608070e010602010c050406050904060f08011e051005010f0504080d050304061401030503041206021605031c0b090103060c20160e190c0c0b04030519 75
    0x2c490200c03482156100d10b12011024490f001001c1151807081c010030014241e00c0e0018102c840c9000315400c28003d06902010941e4507100040d905640d00404581c19907440d4101282d88282d8000890b00520182e03000403100580e000010400342c1040d0000340c40d090305034040c1444200718590315011244240c410f9407401c4869181000554094009188041e0003400c1c4035042a03680c3d910f40c0d080c00001078007034000540010810080003603c1c81101b03081111403090424641c19546d03410b5a9100d503000d10320303010701d001c00210300308181c507012141120094160216406020b00e0420355a401504023151201c024044803c0900e9891003000c80e0300390000c24040e1546d10b140c9691008106c0f0390001c00c104800e90480c820702c41c0085c510719444e01e020384010010b66242c2c20079401188950381007000000031007401c2c440e4280036220506c40303a032401e400024400f00f8440041e1350308401c1110080c0403c0004040100381a00200600308160001d04241c0318044500f10031242c00d000080101130 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 268899892 1250 268898642 268898657
    0x302061501090b250501021218060f06011218080409060b0705060f070309023f061621090506060d240b0307181d1509070909110102010c02030a 63
    0x120b5a40308103240041a20390714a1044c4c01640f80c0700c2c2a40c0c00310380c1d61084088840d040c0b01034403100d084052042849840681602c0c00e01071031841a200010309850f04011408a03415600246541f140f04886859582c803580c41005207024483c0e6009407180c0c0c4031092030300d00001a80d10004017241d0016174000c4c064a241d9403141d80760b0009481c081d004004041d561410b150041c1c440312204203616608100d0b0410007190ba0362000d00d00c078815154078071034a815122400840d50300144054000b842034000580a401c0e541003200d5040500c00c0b047c01031151f4a9503c1440740c0b0681c82622014061416165181d60b9802030041600d000b05005211614a04010804070320011800c51041e002100119054480c000002e02c0c0803016001800070700004241e00e507040225200d604d841180740d00061b00162a00020584c85190a2100304000303a0603500061a8003410700074480904105001080141c503581002e8182501240005001d0741c40c18403109205030002080e113596510a070744411 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 268901142 1250 268899892 268899907
    0x30d0c020d0b0406090602030c090f0604230324040302070b0406080402060d0e0d030c03061212050a1101021809070c0b130f02130902010f050708040e06030a020d0302061501090b 78
    0x70000781c2d000303005030b440c19510304c0500002071090001358000e480c01e03200c2e0741d00c0d2a000e40410625180003000c05104007810482004070004003070340b042200b03603041404940803211801003400c1000b007840701d0b1141c10111101c2d8801d0081003d041d030045009a0803244110746408061076140300310702410000c42c0c00782000a0041c6480801480095140c03030b80410503011480c10585403880e515030000c0400c2c1c5914010754006d5040c8182d00c02001703004050030144503292240101e111101403842c0402c04009408401607009000e600d4041260348021503072030310b207401404101c041d0720070307031520400c007400100300614030031615058011b40200e140307020385e200c01c540d682402034189000c6070010450001e42001d42c1d1b03100740c401c1a0f4003c40350003241d904510b10004090011240100c01444028440e80700822804000d4030180c0e5048a20950300c0c1d02c907400080e01e01084200000e42c42045450f84100f01a408202d081c042d59072000350348041040b020041d520b0f4107250140300d400300014403000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 268902392 1250 268901142 268901153
    0x1513080a120809070b1c050f07030e01020f0d02070203190c060f050c100f09050303011211150a030f06080f07080706030605060702040c09121101080c0306011b05121206030d0c020d 79
    0x62211b412074004040c00c00c0d465224082c1a16000c6800c0621048100200010300750107005840221300c00030000c500c0e004002024818500640c044207800030303404500b003800c64804000115100c1420b00c4080603100c0545004501582507010342d400017030520700001d40003400b40054642d84803d01000d03026101582403460001c1c1544c001552015840c0c0c1c0300310001c41c0090009501070200703040400c221541508021100c140d0200105000c0d524840f1a00c403035580380820340b00040c14a1401103007110040b0342c100082c24640d000101d0a0013505040360310342900044040c1107400a03810f403a010b5541781e10a4088810621070542c01c041b00b04120030041c50694025a07020380c1c0e60074113118258a98651801d9080d0009044403030180c0710080c1d04a81da0803002241c2c2c065000030b10f5a245243c104002485d8410415880d1040b264400403541001400d0060041001110b254141c5420911001030315407081580d000d8068043c000149003040d229900d007103021038010b84152502c0c5000e5844 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 268903642 1250 268902392 268902397
    0x605030d111006090b040e070302091b0d0e0a02010801090b0a12140706170609040f1101021002030a020a030510050102060f09120414100305010f051513080a120809070b 74
    0x1541c81070207082c03101e035002c040c00d108078006803598500009044290900f800121006d07000009400d5021003410001a6240501c440d440101159018002c008202802d0076500940e00c0d85034400e4240074000031036a000040700b83c8242d000b40e94144180c1d9880aa03070045800f051b9101d50026034000060001030505030789446218800d000b4000c8100d07400d0082403d03c0159042440080c120090001031040c00e44552504171800b140c10340c0803424a0754844c090b11030216001002080192142603141e0700070b020115140803400c0007556a0b24100300c0d42c6000f507210300454000300b0314010118407043d400318040000d070b0700c042c0c008101a44034441d400c0b660400c01048034101344035114078041c03519120000b0380000c0010007440d2840c086181c0400807007201c00380f00e003400c00d842d050041240e1280480144101c3e0f90940781c8224104170b9200400c202c2c40b40812031010000c0c0c245c0006510100040e6014410f4003a1004040d58400b007030003150710f14410b40d40110a58000e01c0103004502c440c000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 268904892 1250 268903642 268903667
    0x4061e05060102030d0e1c0f200706030903030b1008101202030a0f0c1a0301030c0b0310061b060203010f03050106051e0f06040503010f0b03070801140c090a0302090a0506010e040605030d 82
    0x80301c100d8181e881f1800310480d028030030040050510b4420914494100401101503080d0000403c0202c6028078013a41e61040c9100c1c01c2c1c201a12000d13980b041c940a035020101d5070001070b01c9034100c04103458025140c003500341c03400d102060181c94005442d400990a0020099004010740403a40c503585035644070090010060350560600c0b1300000c1d1426401030000807036145011466200d40c90340c140021500015032002c0000202003041103030380c2ea0392403041c400307460160030000da840071001c100c800e090242c0030009000038030020000c9501c0c0300304c3e55044100ca10840c000c2c40000c2d15841800601c030b80c0c071b9000081c040c412042458480c9004111341c080400040c1519080940d02d0002074203440340c001e2036100300c036916814540c483c2420700c00640a024000000d12200c281c1100710720325644010504480d1f4500861908025940d41542c80c0003181c0043c000459810094030101c0105010b51300a80800d02c02c0b121a842403e160040a0480d013006005d03281400281c0016601840040ea = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 268906142 1250 268904892 268904921
    0x8040f080c0d080a060e040b0a0c1e11010e12031302010e060720060309030d0e0a1a1e010b0d0b150d06061704120c08040e04061e05060102030d 63
    0x4101003880e501004109030000a980c0d4014a074180004c01d00215036094104207604030502c010030020036113070031107603422005030f02e400507101d4005d080403034186a1503141c83d4400d443c440d9005103810f5000c00c610043c1d0721640020800711818200750340d500c501002c1942d1090009100141a81c84481028003800740181420b002c81c0080300d0014072242d0180070102c07a9280b09001141100603c00d103482400c0405491042c0342d4141428070a9903401284115207416485010380280000180700510780c00c2e9201c5030b03220902c1007440102e00b050744100c0d00300813003c4c0b558800007081e0100040b018103c1d29030115403490400e101201d100585580400e85801ca65224008903001c00b0200081c00050b048160000e111821320304000c044c6105100800c00744181c4009010202d10380001150600740617003410800001545806142401942d008105081d0038104100a00506400261191240c480000703102c84031407148008031007060f07500500603070081c0a690300310324943d402482c50a03c01c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 268907392 1250 268906142 268906147
    0xb030720030c0d0503010312031a120106050904061b0c02060901050a1701080601170a120c05070f030c05090a090c031502040803181507030f201b0102160608040f08 72
    0xa070a0703d030140c04000100050400001001844a482d046114241951030288140ca50801c1a0030380c42d41034500c018802e984c100c07044071561809601ca0001040d019226501a18050130280003d004107a19844201c1c4d1224040348418400c1155080c5d16034003e01c0c070340c1003600d19001120341e074003c40d108200b40324480b0514041191504c403000d000305803d04c000c2860b9810603d51b0760400c1081d034483d0301c0c140d00c108920b40c00a980c2c0c2c0701d110113620551820280c0924241001494101079a12643e070003288a000801400520700411045e2481175644202c035896440d4000c0803150855405070415a081c00103100090314908903035103580d00450050300f49030703e525035103042da84030b00340000e214035005441d40b00d1801d0100c0e0301da01030003030f1703d0075607041c80300c2902c01524036804030036940304008108541c018076514900321980700d1032040d801c80b082014075007000d060145c0071300c590740d01520807101011208050000390809032000b690b01c692654840759035030b100e020501d0500701d0f0301e440203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 268908642 1250 268907392 268907407
    0x412060605040e0a0c14011d01030b1305010617040f03200729070c060e2b030e09100603050a020c01022101090204050f0f030c0a0f030b010b03072003 66
    0xb81d020720000031a414020b42042c407002c1c5840c11082c03c01c4d622803c0c0741c100f0061491026a003000c050510041c0803d40021a20b4840004034020a054030b00903603c4840d03202c2501e80e50400354801416a00152542c8448000c08600b08034244030489005000b0404003040b200080d1144100d00d6421440008140691407070710001400c14410703821506008448000900c2183c1c803c0310070b0420303880310180c1940740001079110200c03400191702504051281d14991a60251101980303082ca640407100e0b201c0301c44000130b060680700c0500d0001513001404480b041c901c6494107080540c01000c074250040b014900d008400d03005001d0040021076182d600340f116280f040c400380028003c450201c01d6815000c3d824410200f0341240680001e4155032045c00706001644601440a41d070003021500340c21100c0c441300c0080c1c0f038500b21460f51504250050300000d06201001a8001960300c0340008035800e03a00c84400c82e00f1400200d98031400180d014401d2050b4030711881c2d0b1058155070075815603282452 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 268909892 1250 268908642 268908649
    0xe1305070b0a031e060503070e330f1005030a0903050705010504050c01110706080402040504150906021803010e1209030a05070b0403120c0b180316120801050909030412060605 77
    0x56142d90000c40d40340c0d0080708018400b00b060400f015003040e4200203050500c80400e0b620307456400390b00702405000c80070902502c2c843c50110108490352000c00614028415000400c10444039024095040d0ba1020f04541c03528400480035290a50350b020704503a5450a00005001107940c00d0f000d20004110f500007050082c003640340b185010342c1c000c1800700d00c0c1e080010250b03a150300e0070340240e8000f220144400c50f40b0440f02508980c0464001c20035846a04180014480000c49140300e64a07001c082030400285402030152101c40240880b01c06a082042c182640d43d01058a0850740010010210300c2e4100c401400703620b2800b504803080502565641c62074014150000308825001140c10820083c90b204650b80004451900301130241445c0d80d400d40314080a0321602480007140c10712030b0780380004c01c00d403038209503000b5007610085060f04000c0c0c4141054843c2c0d5000480840020070f003030821030000740c02390f0340400003145090b2400002c015034050158089582688038000082c0540c0c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 268911142 1250 268909892 268909897
    0xf030103240b0d060f320702070308030a020901050d0c08010602011808030a021818040b1003030e22020d0204050a05270702100501080c03150112080f1911160e1305070b 74
    0x3140070312070241c450302500246c03c14040102084219405900240002980d05064941004500d000542c486689100607039440c09009034420f6500c1c0b400e8009035000d5881481c440c100ca1083e002000014508844401d10044421015007d00c0080000c0717000b004c415070080c03440c41001c0503641070350b020100c0041c103901c100c4e6401d980410b0551050100b40072421668030381241c0c0f0854041d041c1451594040c02c500c40180c0c42c0340c45440c41e25014000001414030045a0218804045540711803e080d124001c2d0094064039001e0480e00c01c1c08181070911640900e0040092000c0c412003000e41c00040180c072030014007180c00c40c011401c40391300807030707907400f80c203028103509006481e80a4103030040c1882c1c1220704803911400321442c00100641c440080c09010019040780c5090f80d2002c131906c14407954403402d0340c1c88010000b0710040e03206c0749501005076148600c04005540c804490300880307940f50009401038903060204100410f09584019000c030800d2449030040c1c4851641d100c0740c4200a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 268912392 1250 268911142 268911191
    0x709050f0a032103110909060d1a100905090106060206131a0f07020105090c090105010f03020f0f040611030a020304050d050c0a03050c011725050f030103240b0d060f 73
    0x704081e040c2c103e4440d014054401c01031120a403183c00c0101b4100000d80d031000c0a0710490245040e203015409000d4a41698905044600440141da040040403510195820701c00c04060a02d03000115007200030600482c0100c415980c000d1502d0380b1128003a00301074010040445400e10b100311502070782510b0525440c0b02d0492100b20501c1da00e40054042c4c20f6070401030004003a40c100002c80606640c0d4072090034195502841c00c0340c06918980e4003070f4001d106203a0300e080d01c00004504d40010324054401042520020341c2d408149148110b001d0b540c0b030080124030800742e00148014812801c14840c1c5444446c040d80485181d9a40d03080400d01201380780c6c0083e1030365001700704d4520003560041038000700040b00114100359450b1080401001c0d06112800d800261034483d400000b00c1c3c89401a21100010b003880599a03594a142003d0704003400482c0211160369600d442d180c40300c1c18440d1031001c2c140502081d0f0402d500e9070b00d1400805800e10901c1d0795565802a004128010b98006d0111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 268913642 1250 268912392 268912433
    0x306050601021c09090c0305060d030509030129030d0801181104090c081b0a08010e0702070509010b1201140306040303240902070b0105030102070503070303020d060b19080f0709050f0a03 82
    0x3811705002c481420380303892460900500d070800c001c0c441c43d515101ca68030120b5405241c9582c03103141c0c00000038058100030035a6217549001c0301171407105180d289110b84005904034216545d40c4036460381618081001d105050850410490300c01c04200c56400400f182004800d034245020b4961402000300c6180c1c0c0c0805c00040d50038010840900003030b5040c01d05400079070024a050500d5481c000340308004c140144001c10b01c003900807840c4240200042c1000d000b008000c5d220541c3c50b901110001d0700180c00510306012120000a18010160300740d0307210300000b0700988107a55558a044c1c01400155600402100c1c031402c48501049800c0007800107041d0940026903035070348500740400140010781045109920401164001520000c101d414496260402685820414030900c004148a80c007080344414006000b0000c513102031034038441040c1c5501d840101d41c50b1061180c40a00c4111410305c04500c05441c2400145031030940b2030400d0304000d12000030309890342d1300c0c010700e08158121241c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 268914892 1250 268913642 268913657
    0x13080910050a120612030c06020d060e09240c130f06020a02210a03110307020d1202010e0d092702040303090e1302130b010c02120f160f0306050601021c 67
    0x6143e21078108000c50301c0a24040c4003040c208082e08400c0e061503003000741801404174288040140d1501903841070700e480c4504020309992030000089403801110f1488d114020350500030629221000841c0300100702c0201a0002d0303403007188062045d4002c845000602c2c5500e007000400c8901c04c0d4468000e0304c00707503015000400d5070303106103c0c4048201146940b000004215004030300b000040e00308120781c05142882400986030015804e40c41038410203500700c01d141c65440305012021035a00e0355401e00b60300801c21082e421019684501d2000c41c802c0c0024a48042002040602c0001030100001e03a401d00c03002c5440100720804a81c4581d208901042c2d82800c00c0024241402013181d006100c01121643e1507043e60015080c00c00c00d03032007000b006a4840d0503a001364803480b01c0040f10b0382d000e880140c3c2804030158140e5603103a000c0d01c6800520403031150120813050010000304441d1852810324659042d0395420014200c0101210b0440c4900c0c0b282d6503440125690f41210442a41c03036211 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 268916142 1250 268914892 268914907
    0x1605011b111506010c02011101050a05040c0b031006030b060903190308070809030301120c08250501111903020f1f0b010908030901030e0309060d020408010c020c091308091005 77
    0xa21a0761203690001490704802001e6081c0c655001e1020750100092138070b088944541d20050310f0310361040201a485611340700c100720781000c00d540198000c0d80601058601c00303665141042c5a448101d80c000c44082d1107150402040b8007070f40008404032001081e4904014039040401d107042d60344800078400600c0301c1c40c1c0a0601d90024126034012120345001581e6191030406280e07244018072a5902c21040b000a00051080d40c40480015280a2040d01c0d043e580080d801070703c0000340c14130609840450880040d0644c09410000361281002c8003900008080c4416002076a200a005500f075000c1c28101c502e80500070321202c0400c018240d12002140e12204105045800c04910141440f4401e14180202240002500c41c0d2000904e40420800f04000c0e04038190b00408240360307000400410b82861148040d0050010b40d9510030081049650b6200100d0b50340000c81746c840e4000b80d820000c140c150080800e80301055005502e403600d403007000b1000c0b07108039103540114000200c0219800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 268917392 1250 268916142 268916147
    0x21b061504020403021503060604090e03030a0c1e0c0c030501020708250f08071a01090902031002040b0417070b03040c0e0f0606030703020d0906060902031006050c0c01051605011b 79
    0x9040034a4255400c504090075a404203035100320304000000804008400158035594a80480c1c010b840d4900c0288030700c5141d074140550701d4000341d0302000300a0400001091503485008902d40c1446048d421038410785082209403412504600c2c16505060321007008008504240000c01080e841004000d035036009095881040806a00c6c1003002040d4009109020505134000407a0403601301c2506951a8910315000584920402c0d008003030a502c00b00015820800c1c2c1d200d050704d18000e5083c1d903c0d6a040e004040308a100e6401070f035402081c10700040c000c41c4518640e081c180980304048840303079611281d400a0719003003154211900c19910406105041c59104030b503820002c1c0c800c03c410b0506061002600a01005205508041d80440d50b80d14002c403517080103d91940018003041040e44542440c0701079802214113100b202000e801c0010301da440f07901268550f19680b8060518190624011105070b4041c14005640311a40680c58001c24400c0c85480503150a40781400025904a03101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 268918642 1250 268917392 268917421
    0xa020d08010e0f061c1202071e050a03030e010210141b0a140c0a02091311030304030f020603280c0201060803090901090509071d010602100b01120b04021b06 69
    0x120416060712401c0c00791060000c0320041d0400001c9907065240d480705c0b80c2010104250a502600c00e40004140180302900840e40009490b00340c0301e5100702c8001c4001240c0c1c203894512a650704840014010000300707207e90315940078180d05105680003288c80c0311900080e40c11210385081020380000c01d000184038036010452000c50824040e908203041004017404c0c0d00c4440b02820300b040c000141050031300034140040481554000d1601e038103410700184054040020960484424946001c4030409180010555048a038010090064112981c2c2030221a80000e080700315096003a4400103180011303c0c150403040d00d9030f50400514642c0e000c4000782541e1f015031202907a42c004102c50040c6444601c030050640c1c07144200801e45490b4104c40c11700c3c18850303034031518400e40c0c5045a4401e402804c85010704035061582250220362000070703020112800c4195a5001c40c020300c0d140385c2d203005941c000b01c0300c80a00034030040c24000104030600d16208200302c180c04940009003004840c9078030004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 268919892 1250 268918642 268918649
    0x207050f010507090906050f0111030f0a03051906081e010f0f021806090a0306051305030c0304030b09060f07180302030304090603020a14090103020904081306081602011e0207030e060a020d0801 85
    0x1040c4080741c94240480c21443c0100c40300b83c1040032140350ad440c0c00c2c004000301c0e0700018000c0c0744681c0c2c4880f81c0c00000c00912054940010350700088444100b0f00c2102c0c069102560400701c040c2c07892001c040e0102030548120603005584d5501c2d8a104041442c00e03204071540c030031400402603650b0b4160a010820321900c03694585c4a00010300c01d0703511030340340c200510f82030f26485100041c0da5201c14140c050704503880c4000400c1480000b035003100e41480400a002264482d428845807034179400700300f94590100f200c030500070440c2000003848143c404d12101d0280c141c000039414003a42c17290082400c66010790400b074aa00d4842a0401c11410f003c210741d4010501e00180c10003800c03c1c88005146504107200284c46182c100011900f4041910101c80003180240091000c5540e2018080c01601c4221240007042100c000d03042201030040c050182500c0b542031072501c0400c2c940c1b0b0403100039009150150308100c50140c03225500d442d9000203000e00900d83d001442d5180115000503d1004140c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 268921142 1250 268919892 268919909
    0x27060b031f0e010b070807020604140901062c180103081e030c042702070506070807030e06041e0602040b0301080f030c0c0d060b0301090c0303030516021509010207050f01050709 78
    0x100000d4941e8002c0605640d10462030940d1283c40b0f05265245015400000c0d41c8810002400524083e10fa09002d42614080da205051a0380e90002a81c040c1d03d100c0f1050300d078100c15041420142c0c07a221428990b4a0001e08021081c1454180c000306964240c00171140380740001040d901040da003110444400406441e168610324042d01101c405005a128580f03407440c051b445400703040309607080c8000020410034110345858003800d03c5a035560041d120344002c11450404101103d210307000306164904200001c1070540c440d507455015611050540005911074040350308000b0310240001e100078030001503800c0c1c03254144503540d806c2181300c1c801b82e00e56500400c1085050100031038010080002203a00705222010760600381c010b0b08155100c503616502e882d50450030080e41c28200343c142e80c041e982c10441c0d42c2d150700c2c11440d1078040705000c1003d6030003920000214502600c41c1c070341c016540c0d00007504150888ea100380c0b80002e00c800c0c060007a5110401c200c1170340c0c2d0000c0240018500603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 268922392 1250 268921142 268921201
    0xf051e0106051509240304050d14041409091207030503010801140f1605040506040e070f09140603090a050a03171e01050402160816030305060d050727060b03 69
    0x1401c009034036110381c3d06024010828405100b00f100005d00301503041c0c41c140d219540c1d0720b01c0c00e45082c80c1c448440d0951140032074613150609042140c1314060b00c0c2910581d61000300072943c02c03000c03c031070400000c0c40d0070ba5510600c4041c02c1204800c5014103000b612a4a4650701c039410300e090301d4259014824100814100d080c104201d8050842e42c44d5042090014400030603180301e40c0c101c4140c40f483d0069138014400240018040200046191090103190fa850a6500c070f20581220004540e10a4240c082c1603544000d4183c0751002c001c58210001c00103c4e405189a0f565640c2010084042a000319000c501200888007505141c1030f440003060300d00307100544c2d070b20500744030071141070086500850780402d100b6001902d01c4e0b4030081141d0800c03400d94981d0600040305090042c0c85900300c0000382030502045050512120101d449584000038180450502c0c0b134903a01d686070310b0b040410f6800341144803800d0b50341a1092001034245101500c2d660328040e0000750001000d288280c6030315460 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 268923642 1250 268922392 268922419
    0x1a04050a0509280b03060115170c0a030c02010207020414160e0901030b1503100606110c030d0c020d06050108010606082d06010c0c090902040b0d0506130f051e010605 73
    0x340c05502e00303c164402e240984140d1000c246005001d02c0201941500c130f0f0b000041166001940100c040d840255124014502c00d04400d0a2540742a24003441050050151342c0441c4d02a400c000300080031032000600344440d580024042c0c80c1446024064005503400740703c048414110000c5d800241420034210926140000c20140e20052101500107440040401c1401c00f600e4140c0c80074090080c11140c0481240007160001c020034030409020800c80508102ca4400200c1e0f18041240300801510004402d1003007540c661013124400c03640510000d4202e000500c02d845000e019128041c00002c4040c24640c01400a640190080c0d02c0d5015416407800255401599940380d0682030700700d01400d131549001640c0f0b8a04a250041c001042600003007868440795200c40c1d141ca00849007031102c00e0541c07080c0078030b0f42001340d03028003940c010000003a4031203e00d07010080341511514941c22001c0345600d82030705000c0d204185101c15200c10266186050013402043c000c0c080450b002c0904112 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 268924892 1250 268923642 268923661
    0x30c0403050f160306050711031909170717011e0b090708060603131e03080906010608040b010b030402130e03090108060303040b0d0b0409050109120306080d140705071a04050a0509 79
    0x460781304c01410103441308005881903100b0b1000b880780880810890383c076505080da00030f00da00c0181070120002100710701e000503c41160302c620540e04c1080005401402d060100881002c040721101c03200300e40d00d541148040c0f1071254020b2011448413030000620800d0351003000902800540901c003007203010818420b850f5904003c0ba074000c548035055051f0410036180c4482c1605800131460308002c8042d4282040c980c1000c0310901c130350b0400d4103903075190381c0750b510070b5510b0700c0159800303042020340c20014070049803810000e50300503000130804483c586c0084102015540c6400128209810200f82200b50303580000446030440d004401448c2803d01b0104401524042e01c0c1c1101001c548408d140340341030301c031584160f020035003000017844504080d04241ca00710f02d48000c180700291516600041d81503000c40d051303281c481d81e599130140c132850500000c0e643d900080c400f60388a02454000103205014004001600c82d001818035807118a882c0401c16000c03030f20f41c40180904800c5042220415 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 268926142 1250 268924892 268924933
    0x150e0f152401080402030a082a0d05191101050a0e0f0d0e06180603070203040e0c190e01020f1b0a2102090c04091a040507031a0103020d11030c0403050f 67
    0x1020f10302030320195070f40e00002c0d01c0c0101c07082020700002d01c00105003201c050444100c14801c5d03a1005901a0b4015001e001c598840b52003403e40005003003030002520150003006840d02c0900c1c00d2800f50200a10b198905085610a91380b4200141c0d441c0d000e0b6a40e0841485410007050f41180901042030421001901311080400a5031260070005004604512000780c00310300d0003000361540b034036440c150002a60741e9201d40910400001d003d000500c82002030f5040311540c012062001d007000c224902d003030700c41165090441d419401400380d40c85821404201d08410524803e1800c1d1040c4104002c0c00000040c0360030984038958a2030728a40000028204162011f50649404010342d075a44422100d501940c0c200300360359400c0c86100e03102407900c048861540c01089804222540300c0810035412941030f110503042c18180302c94102c1007980254064248010300490100d400481c6101e100441c1d401125a888110000b150030f20070300104001050f080d22564005190300c902014803002d464 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 268927392 1250 268926142 268926211
    0xa020c211507050c03040806040615120602070303290907020708120d3c090201020c0d0201030b041e0c23090303090907030b040e0118150e0f15 63
    0x5100001c1040c00b4414011228155411405e807500c943d1218a1162500380941e000d42d40c0301c1c10408000c100842148000f0100d401200d02141003141955032000a50041c9c034065051650300d002c0b6882c1e5800c00c0d0803084075040380f161810f0000228404000d010040030300340100315030080e1000c1c04000b0000030300385050f54006241c2c0743c6400e401c2510780c000c2c1c000c00341400505202c081d001e480710007890303c0910049590016014240072041c441c441201d08030580640107920960780c07a1050b06210314032a21150040c0740101e021500c250200e4141c03401c4010480c0c031115603440b00a01d01f03c41d803042115401c41031508400500000290744074409244003854200b40001490000aa82c104216501034802410f00c0159281100b00034000300110480e03980614107003c0d501020701018420550180d22401c2d07003000b12086c80d203620b44420f038003001f1000c0165076010f00c5029070304c08200340035182c540340001301030700740800c81c480700c20704000750558145180d002e107842400e01410084480c01e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 268928642 1250 268927392 268927423
    0x30c0904090c052d010c0201050f0a090308042d050d0318230f040b01050318030c1005090f060408030408030403031506030209190e0a021308030a020c21 67
    0x2078682030508030b008110691000d40e00840c811410840d0342d0920050050700590b042000102100003001501d030040c800f640240041d0341008601001d6200101800c60b4610034074010303205c1070303c1c1c1d070b18075039107900c250802015860122114520b00c0d0024102c40b0f000f106c20f0025840381458180800d0581010110003814442344440c41560710780750120711001015030106140751070724616134044580602000342d40c002c5503c1145100103041500802c090030300c06958952443c0e88600809000b1907180044c3c4001d40410004c940441d40d04002c40d4841c150720100c001541d040c404002481e204210450403e140c208400300000704225505070782d405504000e11a58130f42c1ca03440c1c2203000b0300807070300d07000400881810081a00361381507000e00302412050394025000100c80b03a580c80c5049180c0f0804201000c5403000406044058024200d4520341c0d038428400591102420340c21600441c080000507801440c0341069440c20220038613009101c10b032682030140040600e21788400c020f80001c4c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 268929892 1250 268928642 268928651
    0x1e0515030f131a0613050f31080a030b0d030c030f032301060908070806040f060902060706020d1505010806041d0a060608060703020f040e0c040e1515030c0904 70
    0x141a454a1601d5007020f902003190034203169560440c0764440802d44004d0700400342c5085108581c102481482d0003007503000c4101441c0c0d500c1901000d691407003000340881c02244030007165940704070542c0d2038180f04d200b50192903c0b102d500c3c40c0202140d02031600710b07201e200d40000240c0801d8020b01c0482c0569014602200d2240b030429003600545502003c01c05100c03441c81c021040e101e41840780d07a060301c8095544203811642c4800d519500c8400e80a00001d580040300840e00107184d0005014500b4810603000c2540c1d2900d0700028559000210107075a625000119280d207412203108000d0b8042c0040e1345840400d0400c00000c15054000f0106405940d840e41010301051150121036a0001c0c24812281231480520b0b024000d0051813049505500c100804511094020300076504d0940103e0059400c0914160700e88480400180214903510401c0001103690340c4c07044041449004580d0f01d03d100c68051006001d1360080c500d044450104051040c0716010164004941082a0485000c00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 268931142 1250 268929892 268929901
    0x12080706060e09030a020c030c0a050108040c08030a110106050301060303050d090606050a150912050a080d020f04090207050d181e0b0d0c1b050703080d090501061e0515030f 76
    0x801082542c00001030441c01d4010000c025200100418400300e83c3c3d826640c1d248000d4040c5035580b030084101e80c0d40300b03e00c404107101651148007110345c820b0058111a030b00d50f64541a0a083d0b0380a400d40780006074000080c00704805090090400419058000b0803449141d03481c001c00a0046100c80b40b01c3c29200c1030010148030b01a00560040e080c02010000c0303c5581e45c40320702060700c8500000d00030441c1e00d00009000d0180142913000c440e0440d0143c40c014046030346000c00c681c0900380b01100e0683c00e11542e60000c07161006003002e0030840100595a14807420300925051604100d1001c10070b5400303072803105c4101e01d030b4020100d840c414081c6481c1c0c20581c648800c00d02080e0420400880003180741201802550403040d002ca80d07d071128400d0f440008941c01c00180061405007459200803000c00000310204002c201924815200048002d029952103003036440c41e5000300b560441c1824580701c11038460300d07001300420040302c040341da80710708060369003850000603c0210304102140014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 268932392 1250 268931142 268931153
    0x2030a022a15091306031208220f03081503070b1b1209120a0305070f0c03020306090f060709031e06090b0103080a090605030f180f070b0d0c09120807 66
    0x941181100900c0500602600242c0788029000001554810a21242e0b081d40703454141c4640b0007920342241542d501140001700a54120401901001d64500032030f0100c0e41c800226084403114900c0b41d6103036005042c0b81c0c24002c03d41c03200070f0b001413100c1c20090240000341d0f8000814a0868070181c4045885410906000080144075200500140600c0c00b00e0790051303408000600071110102c800400b0144081020741d51012024002404100e08200c1c190100704200204881140300d24041c011054aa0340420309041043d1400007040c0d00103ea80903180308248502a4018074a02e4000300c01443e54840005040501c1c44552228082146040500c040c4c1d03006a0f00740750300300b0030b4800d180d40d40346040c03c3c159000001d40c1000460750000410000e2051007203038042c0c52100078080c020780750354581200441c0e5000c4200c486214005a81d9070b208000d004d40401410038000d06503e40d0360301450801a074813068100010024040800c2c005a070340d078400708544c190842d440a49400c09460312 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 268933642 1250 268932392 268932463
    0x1260403030e011515030b0a0e10030c0810050f0c0f030c090a1d01050102010b0d060b0f100c050114040201020706050c0c0d0b0105010e04090c05010e01030209041a01090602030a02 79
    0xea082c19402c280460311074003100030019003200e1030540e0030301d404074440703600300c3c1110041881c00798030803165181000000d9000c0d14960300440c0c1d42e4624807410780d4a9413502c1c8510b60303652110350241c224540c0314a1480041c07190a50040004a85542030b00d001c0c1c40241c070521400549032241000032010600d54001081a106102c00140c03030408a9034032210908002204103441c00442417148001142d913500c1800360204818014001100e00e403460f9640d403001c0c1089080c0c46410009440c84011180d5455040d4081b0f50300980f280b500340e00c100c0c01c095096812003100c403032454400c1400c1c400140d1b4006481d00844105151040e1a8a500d090190400100f20196980020004024414862000e502a048072001d0300d0f140c0c4030051410a00042e80c800d04000340c00a0030b403800400640d40221442c03c0f0300742051400503d4400070100040072a81c00c034049410251402c1c448007025600302000300080c0c012800114205101044002c3da1902034581c05000b03005c40042191911140c0081c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 268934892 1250 268933642 268933661
    0x612060f053a1214070204020d02120106030213060507171e0301060203030f090109030c1509060203090627060a0b0607052a0d020f0405061507030f02010b0126040303 73
    0x702c1c0001c1215401c440180503840e801aa0704454180c02580800c3c01000404c4d00c2000b10424981030070410303000c100084d0001110307603800d26001c2045000d43c04030b50205501801c9280c0b4016112801d91707540d485000d106070048018400c003081000c0c086061004022030b00701424010542d606007a40045402c5030184090800d021004000030450640200183d0320544c01682100c1c1a555151025800d0311000e41024000c5100104c0740c40100d0380303103020903695881110b0041036a42c030507600c240892780100c6030110345800030f409210300c2140c0041e00c40310481c0140001c5800029104056445070405001c02c40d4841c0c0d10707886685240c5400307041c0c0740f181e82c000d82511614918510004180f11070011080c10107400d40e400100140381a1800f5407403170f500034186d090442c0e109001d2000800000d0300c2c6580c8950891140c1c0092a5070300c00030a40ca0344655540c001c005a00800030f030a48103820500390502400c0d4000c0213186051030108049001840b1001a143e100c0f41000e4000f8400f068 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 268936142 1250 268934892 268934959
    0x30a050a0e0f0a0219141005041a07050d05031b16061103040201020708030f0a1112070305120609040b040b071403090a020f090108060105090405010b0a030c0612060f05 74
    0x2502103081c2c04001c1500000d09000740c131030820300d5040303401d0108104124000c1114825004000d8100c50030405903908420a041c1001441d141d00c03520b41514501c4510240101c03481c2c0058160108001800b802e00a07005030304025045080c43e083c20898445000c1310004100382c0400e107804002010b1070240318040c0c020500b00400801403a602c61503520454040e4050321502c00300007011f0750700004a52001d9100d80e4594203100c14084216540300c00c903544851203200f10190301d030a8040281c000e0074003602c40d403250b580c4e580072035030020070146c40180050700c40c100d0b80003004081124484c91550065003c1d0344951705503120001942c00c00b4007070056220f0b01c1808410481c07200d10000f440e10140e402111310f14407010080b410082000424020300c3d800342c0210300100300f941010101c2e540c001e481580045003541d44c48000c01c01d8409154016910300024200030032005400044c00360690301c0b001c400380b100390b0074851200d070500114480d10780136414401044a080d042000f02002c85511807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 268937392 1250 268936142 268936153
    0x40905062a030112350705061005030309040f0e0d050a021501080706050306012d09051f0f0c0b1906080c010903080d0f02030109050103050f15040b04061d0618030f030a050a0e 77
    0x105074100c06421038a01107c040c4904004203000710301c5c1d8100030040303420080055180c41909005d02000e0160340409425843e02d55200c00402042402602c0c0d10001d1750b510301e0f890311848403009141c45083d00460381200840b0005000c1c0c1c200214101d000c4c4c5410b81056a84c0e0345840004883e81940441c154050914440700401d250340c40104491001c1d802d41c1d16101403503100c00c00c000000c1807443d02d1014140303604101c101502d004200700903013680c0f5410b0011165800b601d9401501400311021340401d14462000b40411001c3d1050b5800741006034000d203041030b00c21001810004c0f01380405041000041140030b25044250405000302c42400300035500c80d60340381c404602a000a0108555900400c4000095964001915070403d0082c1d0180d510f280c036151920324900c1e81c054002e44a007500d600400c4160712502d04401142d040e414000c03c01da280801e108454491041c0c11104140c00030001246040054026240c104480380302c0010151601444000180784200c00480c1034040c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 268938642 1250 268937392 268937483
    0x81306150b03160207060215060906040623150f07150b04020403030306080c0105130e0702010b0612040b1008030f031e0f010311090c030411040905062a030112 70
    0xb0383e0104064058580890380c03410348a14060b03131165070310690000100d140c080090383c14a44030040b6500901f000c0c00001e216902c50100e0700380002c4865074101840c60600b91a42c0071302f8619500c40090f000340502074240f01515403110104c0c03184220240100c42c0d0303880d4032201040154081110034034000d0003199202c0e41da00d405000340c882d52190603098098a0308018a9501032000c44054185070620b03c1d029605051a104810102400f2541159622010300890b925000020400398070350001c02c81d604d24140c5429621200c000f030403002903502e0700360b041102d40000004d44400c1e8440c9801c9030f4480c3e0f03800184004100d40c0d0740d124040b0b1043c3c1c03005d21804010461115051700d018400850342e0008680074400c180c2002da49600c18620300300005404600c0500240e10600d10061001c00d080e5026180c01d0f207042000d40c0d001b0588145825020951010034100c1101c1d452080005030a6602d4001459405082910003038984c0381e0031401c140e110072800300c40d03903c2e20440300d2140d0010f005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 268939892 1250 268938642 268938661
    0x50108060405452404060204050a030b16020a050727090c210b01060309081908060f1804021c050d0e01090e06090a0f0f0e030706050601081306150b03 66
    0x7031003815000e2000b10a54803400340031021a016000c401900004a19404131001000c44c240b0001c0080e00c00035824800442c06689040809008500880d0180c1c91810010151a82e8041e441a1076056611898040d40081c070045120340c2240d410008a201800d00d40c803000c0c8024a084000d28007061400c081c100411281c0102001074502900c4400d15024000080e01c80448000c080900000782c801c0c010000c82d07110703801104d4524410070520f0f080c600c0003188584078980c200b60200c0800c1c032440070031843c0d061800703000300311a5044401d0841044d103000c00d04440b01c4094000790107001000c00d814504070071030b0b0b150103d00794840c0c1140d03505001300d40020444410b2604490018034a0080011202c0403d4081809060000c10240403500c804504100130300c2403100c02c01e1403546a01c00180012030300c0c41b81014680304100910780d1180e140c80e1400c21190300034015070512079044140404e01142d0000d850100e503000e0302c00920108054140c9016800d01d80c440c040342c0d0000410046c00340b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 268941142 1250 268939892 268939981
    0x130503101505010807090e06130c03050402100e0603011712030a0b03060c0408030d1d030403110a081903140403061802100e0123090402070b010f050a050108060405 72
    0x9503000d0025210354030b42004448a180595581c1c0000315400000d0014404d402c01c3c09070840c6004140342c030403040721001401030b16a104903000119a80e0701c200005e6041090080501d140946800710506010328001000d80c003060040d610340680031616a41080d50400440314042c0c2d00d90020b90703c0b40751607080341e005007130500c40590107800366801281403000f901c401d9a0079160424060360500b041c04070010010045030703560200c4a40c00000041c4a007200340001c00266010b0305103004126590014088074056541c407000d0181d1100c01c04020807500d0400a80540d1341c541340070100d11000308601410703070180381c201414651810760886060b46c142c0c040e00c0c40c0280b007601c40c03040d04a580350068442c41d2551990a020940460819841d0110409000d00220507150201d0a0801c00c0010404030707007140704100c4604050740300510443c4501481c40000300001c5585e449034a00b403000007424107001501150090b910380d4041111101d4005c81460042990400e050800302581d10003007002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 268942392 1250 268941142 268941161
    0x2040e030c0d052107170a0c030513030203160309030b0c0705010b0117010b0904150609030c0b0408190f120228120507150504050a02040606030b0a090213050310 71
    0x740b0038464052040c2d030041c1d06903100d141d0522000b14032641100c44510341018020300b01000c101c00510710811101680d00c68500503d18210001015207044030050211107020f4004a620810702d034064000036800003c40300d0901c040904071f803c4026900d400d54841204e500000e1039031001000f0000144000005030030b07a24026002030000ca010707238005407513560300002880c004600702001400380404690082410b9400a0305c0000e9451250140d203003c40195048107000880400c010024445a121420054100750401d0380ca450b2401940d281d64407866480a041484400d81c00f209001c00c510405d5051500300321500d08150048200944903400480716940b01e074901c18a440703600c04c801210a140603405040c03400480e50000040d9095009240122035003d5015492010f101d468000c0f18000c0c0d200304000d000503080ca1042005482254100504140c5002e231254a6956400b60180841744032180050341e8a9024503078240e1171500e60442509481528880c0c2214120f907400410310 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 268943642 1250 268942392 268942417
    0x31908192109120e090103110f060705070305070b031012150f06170a0506130c031209031a0603030a0c020a090c0507060c0e031510170a0c0806090d1b02040e03 70
    0x4400e10f0350281c0700c00e15040d0b001900405d80000500000f80002c0e060b00310f103400101000054004007001405951240100721004e41101d002082000020020140500a40341c111411460f040c9041d92400449100d480682c4081304541402d02562100c52013611318954010f0000c500e801040c1d40c0079282d14450702481900e400c0c0c1c4111002d5010415031113642d842805042035032110205410b10115094043c1c0d038500010f8030020024003110a500640703001c50b207039507503c2c51031820406050018032005504003030000c810400c480c0d5004c800c031015000541840441d5034002d0012a40001182e0010f80186160051000071b294000b00034090b881d10074803040c0300488440d18116130901741c041c80150145c0c0603440c2c408000e1950f8555541c04420f48100003aa00c3e03440f00c0140071440320103101348890b0820130995042c449282c0e8410090811130005201d54200201c036130740d441e101c1002078010092243e000d00401510062070000c4140c00034401c0c000701040190b402d450764444a440ca00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 268944892 1250 268943642 268943663
    0x100b030f1006030213062102030906040605060406060e0d0507090e0a052107080313020409080a030534020c1e090a0902010e0609040207020d060b031908192109 70
    0x4002d8803a000b01d521042e81d035480000e0342d500d01300040c1e0f014492035203800740c03550140011006069480c806144980d80080050025003080c0c02d1010480b40302500341c5010710305011040c070220b50070025140b0482803c0c1c038888aa0342c001c0c20600d00704002ea401400050741083c00304402840000f4a00d8041801182540d00207200d940842c1c407021441c100c8480318030300a1101c100898451405140d102841c2c130b204803103540607a400982241c540500032034180303501180301802240e251158562180c0c0c1860f2080781a801e0002403408400003603a1104184000d641290b8003e10074441c40030403240203001017403161079552000700204800c03901d8601800d2801d0001d080200d490142a4003190180c68003683d040042041c05900d5221501d1250459003c001c3c00f001a2031703c0c0c90110210f40038480c0003800002840c105400c100700c1070042c82000c6541c203086004a21a1403c690000c440280000d920324102d0780107482042c601410289a1440000c2c5941c0c40d405541040303070454400c103a400e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 268946142 1250 268944892 268944899
    0xa05010603060b12071a030702070305010e010f320702010609090c05030f070b0a121112150103060305060609130c0b0304030306090203011809061d0c040606020303041208100b030f10 80
    0x9a8600940c418201d40040040046d040e51300d00070b00554000c032041c03041c0d84116440e42c8845094034484410407550303a542c0c42c1c0700f031144109445a26681c1c0640079040400c2a8034251203490900480c0209414041c160081a8054000d6101000800e4004000e00c010901420490303e000041c0c49031350b00070700403502030010000004c100d02054a818001d407a04107415607030115070b003010100c41c1c000d10507540c00d540c891020741000505950706e052414190b0307a15040f902001e810503025142810726080032404e0001440c00b0a4103541b02d40181c403424810f0f911409a48244410034a0240c8002540c140c0851440798100c01144114080d0314284046a55040804200d00c405d10810704000e561501c24101800b081c0c00c120700d03141c0a41c20100d448800007031200305403104c1140c1c140190303100b000403041604007809000c000380340c0d50001d90b09500d001c2e194005001c0d012201c001c200410480052444044501d411010717011480030f458807458140d00440000310180c0303014941d001c00703142c0007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 268947392 1250 268946142 268946179
    0x302040f02030601023003010909060b0108060307050105180a0b030f0f1302190503070602030c0f010504170a0c0b160e0d1709040b0d0302060115090b12090a05010603060b 75
    0x99000d103030180c4c02021940d4100c030306ca4244079019034120883d41031402c820048500c0d0075024501030549104000751420032842c000048801307070903500f814004920100002564045100c00443d6070a0a2403030f039401300c0b40081c821004000c140715901082550001c5145492140514030481c0a1454074225490301440c402413150120344460a8441c001d0801c4010708002c0158800c040011082442107529840040d04040741504000c005a1010610500d540010010000080000b90080109007019103d0707901c4900e4121054002c0b23a800613020311807910400e14844025000800416281426a50401505000d00034400020001220760042d071034413550504100d584402e452000006900501d9400e42040d0302c0142c4c03050380c0c3c060030b0b940d0381c540448644010f403007a40600a5036040890980e2468030612a40e001c0003c130803410301190300ca403011074900001038040245a940c94000b46442c04a015400412650070042e0000c20000319030003540b01c14204403081400c05480200700d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 268948642 1250 268947392 268947397
    0xc08070e010806011503091103010e06061014030c0a110106060c0b0708071d180a0906051308090105030411040e0c031014012108041d060402071109190c05040302040f02 74
    0x82082c5c0d400d528020161660296100540044c4541c3c0c0300c02c000c140400000c0d00711303901003640780c840d50424000c2040c68901040311b1200b5003a6820041c0915a0888108150340402403000c007002c0390002d02d01040380d0060030034001c0010510024840725071100030003842140540011034076000c0d0343d80400c206500802600d44260071742d6807000c030061803400100c2d12115203014000d40024001c0d525161901050040501c52445040c01007450440303841e0000407100c4c001e0a00c003910b03840c0181c500004811400300c452084091078059100c0c0c5950600c000381308044403925a0052429052031141c52000c43c1c40f0141e584214140c5612017005c80c42d40e010384142103540c90180d0038402c0144a1480c01c2d188d0040890a80700d208601046180d0b075007109035106800241144c034034000c600d25a8040d035404103602510540c0c0540c141245a0b8601d010005846012481200c1120002d1013a06083d0705200300700303003817101c148124410400e01500c55407203800141d026a041650000031034546008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 268949892 1250 268948642 268948649
    0x1503030503060108190e030910020607050a050d0b0919060911070206070503160302070f1505040308090f150903070b0403020d0807030c080301060e0f01020a0503030a090c030c08070e01080601 84
    0x40e0107207541d4941e00115030540c0001c2c54078800c13a1400c0d110150b80d0980b4420420480090002107a6808c0c2050400c0310500070042580215400101082009984407099030034184e110300300a5155002c0d1440c020246c1240c40c503082e08105800d0811038204a41c1900112041281004005650307c6603140829644418100c01010700100400f00041c24150000d140d02409002078030304151000c038905e004c5192045c402d800591010a0030f00c09808600c8404c0014a001c40349043d1111052001410a004520000e030a03410040b46011240c1c8440741c440462200003004400c0b0002110503448181c0c03c02008103020740320704030020440c8041c1d08115404c1d030750000d281070141903890b036500013990302000e070403010003094907a0500050052005940a00b505071a42480e021407a0705210f54051481400347c110740c0000c4034030380411008030840750030120150700420440c50504040200302d40036840208000d115000010b00c803e0045520300503074121a604000c540d07a98015956034400c20300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 268951142 1250 268949892 268949897
    0x16061706101107080601031b080c1c020102010b10091e120b07050d05131109040b0f130f0b0a05010515090108060a030b0906062b0803100312050c01150303 68
    0x1001e100040c003401880a0600310103040310307400ea0700c4554080c00c007602a40100d60f03442180000c00c01e0712003101d0b100c4003e800340320000e06a101214000841c810242d072802e071040e1707940507010300070b5903c02e4010701c0101c80041c0020100502104e4020300202e41d0f44189250034a182c1007481041c641e00d90500d084548a42c0c0300608210661204e4031070f4540502050144001008032030b070054010302a030303031141c1d90603034144210164a04100641071040f01099205403120820040044c91041c0c84079000243e0b10303010b071601c1da43d24007042c61990100e0400740035600c5c61517549040081c03112595218600f00d1005000c0c41c0d90710014803071665a4043d2102003032a041c854081c035075100e80e007039590000d4004c001001041d5691120070403001d00b071380c3c8000260001801c01034141030a5011109100c4c0e500e6003003101604841c690304150b0f520300c5009100c2c070400404224a641104020005150014203081c00703541c55100292043c1e010b500705000a50070303c5000d0b143c8031100c1005030704698058 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 268952392 1250 268951142 268951159
    0x50708101a0d150807030c150306030312050406060b13050f0f09070f02010b0a090507020606061306030b0409020315011e0e070c0c230f0301020c1e010b0316061706 72
    0x2c40444001e00b60441c0000a200081c00e800181e410040003a0b00040d8000d80170041e40c5410040700e08d0704c9071141d141070401d01d81031040400002e5840001044550a001c06c002015240d0b450000058082c1c9d0f0b1041966000c013185c8800d00d440101e00440403110116881c81d42c1801503418801d5aa1044031410745c0600c802c40014509401038075541c0c0045c0e450300c00029400c00100004108040f25040300210390b0f030355003c024074142c042220603042003007122803d0800400c00054200740300c02c0d0240d441050388a500f003481c26140d640000d20842d034004d05a07611510780b12400034825009108000360706408519050040c44040e1252068038601c561081442d41c0f102800e0f6415003844404966010019400290480c401e1614007c03100d82101a6410101c001080000c650240c60034548a0b91041050502e50500025001902c1c50843d40d1141444815200300d8014030041d060b140d0980581e625884030f00b0080301582042d80d0460b1a01d942542c200402095890070840c1c03416008038a1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 268953642 1250 268952392 268952407
    0x1002280f0c0f0210050309010f0902060a27031419081b0c0d08030105040b0613060f05040b07060f05090c0102060f100b0c06040204061208041a0409050708101a 70
    0x480c04a07520342d000d41c0820040031a00c0c0c0c04030b9420300f8518120f0000807404814400450800e0080300700e00400840180802400c5400150720f500c15100d840c42130103885284c1b00501c0b010b46103d80e650340c2ca018041039100355241081c0e014015040c45991a034000e520b1807503290035045035004140d40d0010485824807142c616418180071075586842101e204d00d5081c5080359076070055503500b040c42403003180e4130b9514100621055a020402a5200d50303414404000c0420f079408000049500500d0300500444055505a0f507030b204603040071000c50300000b603803800d201c80c0740c1181e031462503400001c00040e5214540c2c6615040400845401a004403000c01d14070b000c0708403510f400240c80e016610302d055858554000990041c6117003800d94000d50100b0056151520612005210701d800d042d20b58022551042c0541c440d500400035127001d10340c3c03074403c4d100340d50003a1005048001010050790801d0300c0040d203070b050215601c2134000700c02100800c0c3c42503000762000310507030708940c0300e42403100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 268954892 1250 268953642 268953647
    0xb0d02030a020f030a060e010602120f030a020403120306081002030408070308071b051606022b0c0b010305010f0b150a030b1906050309071d070e030a051002280f 71
    0x350040e10780580900a12000039400c00085000d400e50040001c1d10901c0d243c004140c5481c141c3c400019074011095800c911141c2101325010403005100b503960b41e54035860040002c0c0140e80001c0c061075059205105059095403144003036815080444518500000c5040164030007150000d124503014821000000d00a02c0a00d8014259041c05d60341012481c40300090040681d03410b484a03449801110710400c448041d0102400c2c1c540301810700f0138419909074001d8244031603080054032104050280c650b12407007105a030136602c0100900c0550307407820a603002e0300710303034818003806483c00e5400c01c1c45251108800c42840707904902c0606200340c3e001c0c01c0d4010100c1300010303a005a8260fa0851410040702542c40140c915516402d03100e05162140c0f41c94501d0580008084090303804040c0c1412244102d006e9100b0040d14001010303503250780c0881c2c1001d862003c0101a44144c2e403150752074541359005864486480308114140c0f280f9902c131424480c00040c00301c3c002c5002d014149480c2407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 268956142 1250 268954892 268954897
    0x18060807031e1502030c1305040b030d2a11091513090606170109140102090108060f03150c0a14040b03062b0f062405010f0201060b0f0a0f02070b0d02 66
    0x14014000070300c3c4640c0718081d5109a900480b0070041d20400003d08440e140e405103034440190009543c00c0048612110120313540d40741d850305600c00d12081c900d0006040d034503109030103140603c8844030134040c0e40c140350441541c43c041c1c09152144030030328005500151032104c0c51040e0704008060a0101c041e001d460401840c600307d040d50000d8842c1343c003180968078090750501c01c03c10b40c0c000091420305818400c480c0a200444080e803039004000700c3c1450b030792050301150407001c12980c900b8142d60010010f072410070103451076442000c80780100641321100201510343c415040c1c480c0c1061040b10300340000588960b0044001903001440800c8243c180001a00804282155922000800b0344440f0b8500505c100303007160b0305840903900b40200101030103480c07896444504c60b0101d681c400b00701c414103405580101410001d4900200d0b9129200350410b10082c00d24003410b40d680c0c03550660100c199404401c54002040480104032000c9100040d42c108440b16003131001e05004103111140060f6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 268957392 1250 268956142 268956203
    0x50709050609310c0b0306091b0d0519090c0501020706030c1409151224030a0f030203090a0f091407091203020111030712141302091305071806080703 66
    0x8080d83c204800003048079070030070083c0c4208204607403285002020410100c0c00100300006c030b4201d2014684140804c001580e046020803030b000704443da1008013401c918000084103c07210703400c0c0030b162001e000d861114072042e502c00ba400d82d40f00d503445903010b9065980d20380b0300c0c00004c0c24440281d61840c2a030000f500d00350710000d1600c1d07160740346108401e95130f81194207404601c1841c0700500031342c6000e12800380d003000710381000c503a2004a04000a0348410b008200507013458460a170b15800c041c400e108071620410000d01103406203072140c01002c07a035011401040c00c143d103400b448100e4420b115501e18441c840955400d200035090000444031200b5100c0201c09542d254125080110400005144184034607034442040144952700c0c0b1085d1661700310b4080f2103500002c01d00c042c407003040d12070400b441d805480090954680590072180c400d0034040103003280c0282c003000f24600d02c2c8014284914000180180903854645102c43c5d00c40c030030744c80010b140740540e00d214031000d0740c48000080c0d0b1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 268958642 1250 268957392 268957471
    0xf030307030815091602010501050411191418040e16051203040305030a030506040b0a2616030609030f09050102100f0e010903030f0e15060607050a0f050709050609 72
    0x1010f510008203041000545114480424119130f217060700782d09125840c014a401c44007807150051b0301840f000b00c0e10501c200e1504150a104008030300500900e031030300004000401040c3d442030700c8101c4240400443c040305101d50704048001009620002d0308400d10300410f0003410701c40b4a03000800c524161941e007510064001400b0000115800744042d20354261251404215403804500700800c5420002a03603208100e489024001480d10308408104003000c0521002e103001034691680c5051505003e28150220351f0002004104c035a400070091644aa201c0804d440b4241c001501d40301d409016090060703000800d00c0040807155002603841800000b030018400385442c46050a6690718241038001c02e40700d100d411071202d000d200d8684041007110242c00310740c00c4408a030313595000c040e041c1c9100b001c01140990a1100c203110b031031350056010106810000d22850403540b140580d02c5100809840e20b4005440c0c0e0400b103141c07a101743c075044c046407904040310702105883c10051510124 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 268959892 1250 268958642 268958671
    0xa05090a0315060f03051c0c0f0515090105071202030717040c0524030c0f0705060702070501020601060e03030910020312040b010504050703092102010b060406020601080c030106030203100c0e061605010b0f0303070308 95
    0x31503270902a0318032903030044026140d984690008204c00043c00f40401c00716030f14007410020881d600c00c00e080c1c0d922100031000350b941d840d030700b2003243c0300b00001d80c4481d401440310b41444100001ca5641c10304450050b1110300c880300705021141302e1013080400700014807208000041100700071200404200c0100306106080c4025a01c0c4c443c03070b20301c2c01c403000d10140e4000c1c40140310560b01008080d00601551600035102500d0501080c2c0ba40600c01405005000c0b8a00f0404101d00074019601c0c0d524244024010701e25107030400f420b1081081c4601409189490041800c1900c01d0040c0359180381c0201d031480140e005a034a401c0c0500881015030215541d50106100d55a034040c010f0000300300a50003001254101a511810b0100d40705103a4030a03072402c5420001a10081140140c032030b02d15000160301810074105482903440300c4040380d031203000000d01482c0720003240c0c0e4140c4041c0c0980001c02c070350303000e10f0180400740b600740010650642c0240420400248940b1140d584048110b40110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 268961142 1250 268959892 268959917
    0x703170a06030804030b1506030106023f03010314010c142a030703020f0a020109031211071d0f0c041206020c12040302030d0504050a0603020a05090a0315060f03051c 73
    0x20840d4200d0b800445204070304c0810720a5214103403a547c003031698200c6905155501d80100139642d0700078100130f0b03080109240c18050020005804032100d12045000b078402c3c8410340c84a40c1600d60007408121481e01c080b1001c454000014421840e01c202c072901c1d00120800440076a00380c54101e084900019294200c40304040c061800041401c2d1040300021502c490003485c002e410181455580c0240d0760000c0e0340040981e03401800030085940085901c0a42680c0010072070380109401c401603054820040d00180c994038030409032941c1c641800751540c140c0c841a801d5000080280c6000600c02e90030300013400301c2c1031035119802d15544a106e00524081d00e0200035400c5c58850200c0700d43e44800410100158241030000d9002000342c4c0c64214501410200002c41c4c003111070160381c0030181e001c600003603464000d0044850018004000f24582550392030040c41d40d1400004000840d0300f0300c100080d05088d82112102076030b91140c050075122159a10340054991014080801c1065841910 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 268962392 1250 268961142 268961153
    0x60411150903010906021c05060d0219150c060f0209030d030b03152502280614040b013002241206011403060d0609080f040b030f06060703170a0603 65
    0x1c181341c810500546c8520030303160700305150400215451380450500003000159a200721204405e03541c1100c8100542040003070002000c00075401819084640b51038481e950740d0003030303912401c0611a4800b80909941c2ca40b8a101381d0066000d00c0f034240d48200b00c03104041d4001e82100c404108094121004407080c4c881480c400380066451a001c600d01052152030350800d560300c01044c40b2280018a1a90341c034000000d950046c18620904030610341c8605010003029400180198008161010540c10241010001010b00380300d003c41e9040110f1561141c9400031000c9940d80070100080080d0300c16a8080c003002c081224800800b0503c0b0560700e40c1001058009400c0d01d1210300c814540c186014000507200c1440a040c000601605204218880e9140340800041c1e80c0d1040020550811907d000211070050744500600f071200803c02107280d2401c4006140f2414084116280700d480d0003007803000d14400c0140180001d03050442a00c941952808003a40104c0b00d0b00b40090340742c3d0707280c0340d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 268963642 1250 268962392 268962401
    0x12070c021c0212101506020105010305060c07021c061a040605011205040615261203010b0d06080f030703030b060306090f091002040f0e06010e1e0f040204240206041115090301 77
    0x2130b88a0b15500d0640140b800d00e5190324102824050000308415411a250240e03107400c000e204030402c0200056980464464000200c42041800042035183d0705600e460b2015142c00002c06003144440c0e610300c00c1c070f45014044c40702158411307190407001c944030307a0380b98002d42801041568410780b9180c2c011140b1a0314180d500060007050a4503903441012945080c6c03c41410b01c40c0c600642c4140d52214000b031009089904403503900c0144c954400d03200750840040d0103d80c3c40380c1454004c1428104284d4404001010b855101c4c0c1d9081000036044010484103010588040d0f1300901c0e81c20000c0d100c000d0265103190020808001c860840c0c010400c140140c0c2e000340c1001c018032141030010085c002e2a00318071030304800c2c00d0a0000840c04180080750402c210020b05021041d04155281143d0f292126404140c13030000c2e205559450311214001c680c0c0c42c10017107840c89200401007068200340301280c804e001d203038051554a0001c0d620010080441c02c4008038600944007000803403c02d60b000d206 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 268964892 1250 268963642 268963663
    0x5040207081e070213061a0711031f060503030301030f0201050c1f1b0e130b0a0f03050109050d020d0206010e06150c06090c01020c1c08040302030d0512070c021c0212 73
    0x2c00c0340e9030300030303031051100c40c074614108010b000b41040d1042c060380041c400301a81800c0c0038514551102642d08003221034459242c0030640501038590f011103082d500f0042a8152003d9500c1130005a549500b45a541c1c4000d12003d85199007600c1c000c0c005610a10060206034103030f0003101e541c0740380100c00c1d00b0b49034202140441500d5031070764200007049015500c021001c0403814407000120150011454407021040d000218540c0c503000c00e4015a642c55249019004517008100f40c42c0d00c900c0e002d1700800040d8800d9a01344641400041000e100080741c5910074880e070b0140046910341000c281c3c4075240944403651123a801c416020304d141c800400b41c60701c00c410900608007070501042090405408480490441d004011903260035210340080140c000b281c8602d80314000094241600103008903000294503014800a000354940d00402411081d4084034150340c00b0745500d0802d0702c14180a240c000c0d08040e10944200015020100203682030780054420040341e00b0340d100041c1040c00c40e03407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 268966142 1250 268964892 268964947
    0x1a0a091a10020a03231b030d020c10050f13120306090216031103040b0f090a030813150e1809120a0c0519051c02030d0c0302030601030b0a050a0504020708 68
    0x190032814035038400940c0181d000700080300d164140f10514071740110f104d407070100e21144403d900281c01c0400c0c20412200c50000051045413524030250103d500c8641c40c8422904150426000c07615092002007442e0107540340100b10003080c41c5035038851100c04411045034041c1a0764460001d2034082c01d0004200310341c1e40381480d00031490540b40141c51940340a8140340315610034002440784505481c126400c4400307030343e40b050312200003c0001d40400003540002307000c404c000c15030540300b463300004035054802104016003045208842116412a03080040b0340c010904a400610028035000507900182c01034192100340c3d11100e003c00740341c1c0c00780d00704200107140e10130010103104051101e00c04074849440e01c090000c905440d403c3d51502780388000d0b00902041d01d00d260a050003001141e950584c518006c1c400e201c1441800707402504200e0741a0301103800c25000048038a4961341c0c4009071180108100b103007138140b83c144802500325000480e0503003030801c00707040640b420034400500f04440300c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 268967392 1250 268966142 268966153
    0x1030320100b040f050609070c0221031b03030610080406090f140f03030c07230f16090c17070302070804030c05040c0207030b0609040204090b0f0103061a0a091a1002 73
    0x450070f1204441480301d445504504c1c140038032001d50b07622482036130002050300e04804444004d000040b20314200701d00694100c07200c61304540c01c044e0007002501803008111445900e0100e903404403501e0344411241c00b940410518024a2034500440d81c254001d13000f04070000c0c52101030b50314001950044102600c140c580140c040c1c408080411171103000b8a0140060340c194145060b07110450b00804c00c0042480b4098030348900d46e40004840c16882d03e4850301240c030f00c5e0000784580354850712012181040380c8210a00800d444025016040d01c03a03030303181e9428450b00c55072888800f0306400641a8406c064003004040003080303090b07002d40043c5026682e41d900852424080000b207132401d800420035500550300070000f10b42c044044d0f0b82c1c014401d0f203142d0555a42c42c80001c1c010b20300c1c21001441c5205031824041001151181541030780d11074102085220500c02d1182d5007a4072090407154890000f10b006d110540743d5401640000850b44401104003008900181000401c50007650059221 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 268968642 1250 268967392 268967411
    0x81617070e12010603050f150414031e0a0813021e01090b0c03040e010905010b070609080d0e010504020909120901030b24030a05011a030403051c06060908060a060e0103032010 77
    0x44c860200d00f4100c040003040b8200101092211008e00200050b0031500c4098260317080020034002ca030b407000d150b1020380007480021040f03801a508800e1f6110001340594002540e43c000100e00c0006c0150000d240140c003803801c007075201d40480c0340b01c2c1d0281007185030100020300d283c500000c0c02540203220050750f181d608000c2c500c0000c800507441890140d06201c01044006034900c101c4103d1070b04032501103070714941810100d84c18415100a20100c0e850b003128045407900641c0928040d81c42102c000000d03854084200f80d0750045030800007413590042010400d5580a68031004407000041c02c55440340c01ca01c00e2030010490190f941f0120820000100030310b2002500c585405007204400141c0000912074004906000090004062180000d030340c51000c000c0b410200040d00802600348007030707070315464000c0c45840302e072060168500c541e40108104000900a0f070080e0b0303045901d1100103a01e03640f41103680080890782203400ca84a0a180d00303182809000c03040c951042c00d000030aa1800303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 268969892 1250 268968642 268968653
    0xc0305090a23030405130516030b0303160c0503030304110a091a060703050c06011401030b1225080f010615020a0308071103040504180201081617070e12010603 70
    0x1005150320340d55040341c58220001480c1180321440101900c0403909203010000c6403c1c618856a00100d80c0300f60100740f8500500c0c01500001d110700c408000c3c0685500424200340c050b0307100240d040703134150010700058a030344051b4100071380b20701e028003000240c0d03071356506c0441d04540c404e444c2a00c0702407044401002c1400c2c0030690303000030405e03c001041442c442c070440070f8242c45841c0009103d210b0004441040c54070886c1540c1e150b26a6030107071441c5582d81d403c1d8080c5034101610300342c0400e00b800d40481c1c0302d01d4121401401022401e0107485800c4100e0100d40c1110001c0100c1e1424280c182e10104006408000181d043e400080c00090b0039810145101c10559548510004540c0080102800030b60301c450311541103059030034006c3d901750303004458900b0b5000365004250041e10f0702180350001e0080b9000003c6181c000c0e00c2e486e1194030b07080140c0c504542d00440500c042103514903011541a0804046580300015290400d22144060005427888032140074000c42d5a4454001741b00340013 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 268971142 1250 268969892 268969901
    0x1e040314060103030206010902030a1d01090501050c0c0604060504030201021c0b21030919120609060506060301030804030807030921050d0f0e1908061e06010507020f1009030b09010c03 81
    0x960210007440741c0e40c9542d400a54591050181501c0d0540100108c0c00d851855040120346078100f207c1080311340c0203042c4042c000c19000b40c007607841d582020702046003c20341008941074032520f440505480e03074454403048090300700a0720840441d90700b08144144402c0810502244951a51010540074524820841e4140d414a560b50801ca0028502810a54000100c442c101000d450012a102446207120310012483c0e10414010b6500740091003040215400808403d200720410003060300c031403061103030303900003404010005c4c00308000138008600108064222035220b441c1c15501380c2e0b1911302182510315050102200d591800030341c00100302c1d06101001c1030445501d80003200991000d8010415442c03c40d40034002c00ca04010300c1309200c108403542d40030f022580b08031805810802d403010f5828600303819030080070440e4408284550301c920201d464140c0c005004a181807445801c001941c10a03144410a0101c45503001001518400001e441340b480200009982c1d22006805020b0f00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 268972392 1250 268971142 268971173
    0x40209030c0d2613030209100e07090509130c0303080c0c010204150206160f0f02010603140307031209080703080c0d090b07020c01090503030304032109052107020d021201021e0403 79
    0x503e0030300064142224588440301102d404031503050340c544500011604001540e005289031600c0c940410072019000b410203400c68900351303141c06e1599141c03045107200c0d40300750b84e00500c08401c1c84010030210b44206010b582142242d1704070362400903907201e00d17801c9900c990700c060b110014502c2020340840e014010301d030f4081c02c2d00d0b00030340b11a811040001e1000320560342c9001400052200030202e81c0c400d41c4248091580310030462118104018107d680780c00c2040c08600144c2e240c007a5a45d00c41c6a03026015000f42e000032280d05107202a075060700d1060f0014050154000c0c00e00540350351842c1e40c0100503c42d8002c6000800a08001070000d0402ca40315902605000c141705003003116850000460750722541515140b0824068003070203000304443c0c091120315850804038990240311010813040c4402c95003000008180b140e6403103c2c2918020414061750000c294540d02000d401c0044031420000d0320f000005140071440e028071411141c5445545441d1072001c242481003000741d81000e040d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 268973642 1250 268972392 268972463
    0x120c03020109051c032a060504110105040303080a020706110a08101e03020f040207020d05060a0c1e0f0509041a040605030127050a020a03050f01060504020307050702040209030c0d 79
    0x40340a510b0960b21282d20440c01000c1000e071581c2c421061205e030b03041c112003228820080307030030a170300381041c7d4064442510261100200146000001e40c06035003180d00300d0790305882e468125621800000000e4100400583c0c9a54880e00d00c541c4428240d0700410044481e604c1d40c0901c3e08181400c01201e020726081b0915441c40c5040c000c41d46a602c8624000300c9504807100d141001000d40401e003e8012118000e40280310b07100402e040010218030503221b0340c00d62900704480c0300c82c00b504581c40c80300c5901d44203190410301c5004a003503103e1110100502100e08145140c05803200200c0c003103c07004081510036054108041c50750f407800b8001c1d1002864111700a110040d2117251040c08040d03589650410b1005001c81b000c00c02409029036030100750010314240c1050354908045490f40a03010030400c217540303440000f1801c0c1c6407a00c00e42c2d0094110365541805c00c1a10390900c8000d500503414550325100d00d40b02141507903241d10342204010b02c500c02d80c0c030341141c10044161000040032080d82c2c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 268974892 1250 268973642 268973659
    0x9011e09060b091909060e070f030902010c1104091e150e0312250e190305250503010207050d171308030c070b09030301061403040c090510120c0302010905 68
    0x40c81d4520010758208400c2200e8806074407101c0c4403030f20760000841d4401617915080040001c0c00249443c070003445020715446400c3c0c511408038040b0221010050020301003005d58051401040905600c0450380780080e00014089040381c40f100e00c80c050401802c1d08480c40c03030340080c0030405841c00b1000038040143c014040d00c802c1c00441a100c1c0a8a14045000110000050f01412007102241042d14941d0f40b10000da1101000050020b84400c1d034441c020180700e10320602226100d51a00300b204e8004015048184090700801149889903601040c941403817000859580c0c1c0c00e01c018014584281300403c1c0450042001a080c000e2410b400400d5602000030004207006103070030510b80381d0f84020031b10350300c0c0da804000308254001d56501074110401e01c42004081c5000000450590310140c44a4041654460344180b4078071040360018041c500070101003000c03580307070740005805c00d1065521100007510f4111084050406a906039140701021b0790800655270000c2d180760280c80301347d41c1e010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 268976142 1250 268974892 268974899
    0xd020307150203060105041a09010306050f0f3c04050108061005040b12100614030102040311042703030603030905010302030705090f21011d0609062409011e0906 71
    0x100596902441c0c0302080340c00200080060b13105000311406404121002c1c00d81c5002900c0c02c1905030042c0c03d0044c0481c2c40c084020616280c510008000c8280003000e5512205020701440120702c82d030300904110301c1c94003003100503038080d4a100917540143c094181f140c1d0105003040200f5240180d1044e042c0380c02420034054103500c0b042c402015604252008644280c0d07410200342e50240c1c6120141d00c1d030081d51041480701c1d96a803c07501c1166103048031020304114810400d800c038440c80c40000c0c03c3e60160b00080c000c500f4990410a01c0b038044081200080d260020011500b2450060850009544003001e00c105a0880101800341c40286811070443c501800f0141c043c0c800c05082c188030300d45c0c0200440083c0c2c0c0d510300341c01c944406c0117402c0c0c20009807802035901800329141e5502c0c0e00c0a044080d40d005241c0000c01d54070452041e4010310b05611030182104103404045a85083c0e03115000c0201e040d600c035100024002c040d41d0714600454960b401c0028882c0200e0382000580c1170a156081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 268977392 1250 268976142 268976153
    0x804060f090b010e07170f040201020d08011d0c04050a1d01060e21100606090305060603340e18060f0903030a0b0a0f03030509030607080906070e0105090307080f0d020307 75
    0x881c159580c1401e81e000f16103580c207050b5040001c49210700c500140b000104900d403803440700b0301f50041c2d100381c0880321606001da000341c40c030b02c0090190b450070f0104070b001c000503c0845019036400c0b04070903026501e01625500810350160842d0401d00905400000000215a034070424a0060000346011001042c08000080d01c49411441030740781a4642d41c003541c10303004184908001c4035228002040201c4c1d960202a0002c002403000b41c43c10b01406000920398100822403980301222000c1155940c0d0200d41d40030414000743c103000c0714a403070b0b204c408a90b07016032111142c02069410420000400d80e06002d03460588020550030040c1384041c00e001e13a01000000b42d07a0403a0001002240300111003000c103d8041096205883c02000290300205240c3c001006000c40c80c0c094040e503007070b40d49108094400c03c0084c6d8280c0c26a40c01070000540861094000c201f840c00149041460240c215001a15141168202603810b4000038686486030ba42000b801c500801180080d40c20042a0703103a6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 268978642 1250 268977392 268977413
    0x3020606011409040c090911040b040b0a2a021f020a08090f090a1b0804030504030303110d020706060609120203031204020117070305071d030a110a0b0a0804060f09 72
    0x405050100341c40202c00030829140548642240162081184051132000101030903d10b1084410051a19003444050b88205040314140c45020070440c4c03a0501d40001c2c02c0142e80004031841c00c1103020fa500b4226004840d11202c002c4207039040d00c516080c29801000050356a104c1454041900780b2602c1c5400c03a004034481d501d05810811542d02c0301201c001140380164004401ca078043d0041e0200f1581d0050b0354000700547c1d041c030a05c40043c4651140564031440e05403800f8020600074001040000c0c440c1e004110010158940c0c2410192050502c0050b6008a80221000c0d0740ba10410b2201640c090140341c0104040c00c049100061150040b81e1a44a0450320509402e1400009819640900100c0c08103c0801e1001c0c1d540d441c0c0200024014030060381c1a1000640300b10814070940307a1941d0201405030024080c0004035200d2b034400540160f4044825005400e80d500040c41e4404507001e08406091034585011078540341c40c0c000202c2d40c4044081207094601005080070840e070918 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 268979892 1250 268978642 268978651
    0x3020408100b12070306090c060c0804030b1504020a170f1e1806090703030e01022a13021804051f0303050d020c100e0d080f0621010507090501080a09030206 69
    0x1c006031001003040480da114440c501082014407501000000b0806a58090074400d80101445000213071514001c844030202014060210380090000b0700101d003203443c01d250003590904001070188088804100ae0f03800004811000c24007034030010700d0148100b200b680d444030040310307c2402032a0120002d149128900c410510800a9200080442c411071400510203120282222110319141c0003140d66002c003404101d0001ea140d003100101540002000c030307170800501655030015400801002e80090b103020340c0d01c3e030009440d44c1d102402801c1d03200402e540303400035010310982154482401f040e81d60141038042c0c8545840340030a072000d1031105c20400d5070352600d070859950f69000d010790041d014000c0d10031a21b004041e501d00040703000398000c1043c42030f6041680e2007c00d600d1019508100d0455603000f14083d030500103141807402041e03049004507441071003500890010445800c650040755508046501c1100c240499a04107005940c031811003c018043c1440c25500291140380140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 268981142 1250 268979892 268979923
    0x80603010c0e0109230402070c180b010816020114070503151c03050f1c0203010609090504110111031c0609110a050403020906010c02090907030308070513030b04080408100c03060603020408 83
    0x54903d6200f2001161788010a48003c00a546034100340c00d200302100fa030b41c4900401d40d0300e03400c1d24a40c180c015014102c4504e40503103a20400f5944c02c220030440f580c881c60302d0340840d541c8108400d540484030556a02903003ea0b0f40f0035440340741c4043c1c03408075000340144a034458022400014000015054900d042c542d2515025844841d003e1415110340280710444800001e00d800400c03811001e23030302031412145c056440740c8047e5582c81c1c1401c1200c1c001d4901a00380d058807203144407a940142e4002c4c408a03119400c5918011141d181c100400f1341c88500403420a0f11400c08012000c1d41c0c0c01508403500010820070f1610030303000c80190061081d84002405402c2040018000341c3c0200c100f20240364000e403401c0203610b05a41075980f500800d00080300412100b002140714148103600341c4040309042402c2064003030854441786251003009200329594141084081501c0606001c400000b104800c40403d4800c07400c2000740035964039402c41410544140300c1003000e5000050415401c501c01c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 268982392 1250 268981142 268981169
    0x70f1406090c01360807080123010605090405100b0c0a2907030b01031508010903080709140f1903051b091510020709020307050a14090102030702011803050d080603010c0e0109 77
    0x109010242600321750302c00000c07405207003000183d003101900f200310081907640d0113440d8140403224119421600307026080015100780300200311420954007807500076840d540c0103a42d0507503c1000800700c0d80141c2c00204a900100807440c1003141c0d10600c1c80c00040b2103118280c0f0101c01c00703150000740f00018030120800d5100c19402815902903802100123600c541d0001c4070050700d03a51640d01038000e440c021000107180034009010203104038200c40903a10182c20031400c4c2e404460821460325415030001e0b030310080c81c10301880c8246610140c18001d51207400036142440760a407108a500301900705181c010b42c41e00041002c503041003002c0c0c200042c4102c07011001480d03076240880c0b900100e600040e41d024800030a1100658002015058048150362580d003042c0180d000c04e145400703001d6805000d0390081c0204001980103500303000e601101040c2c0c1c2240140d494603080e00d00f46440c03c030540070403901d6082c00782c103003400c0c05000c0c0034442c02c0c102032010841c5400001d03c500154402d040c0c600205 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 268983642 1250 268982392 268982477
    0x9150c0a0c1b0312020c10030f2a080c0c0c010f0c05010606080a0f11090103091a040b0f0903070209060f010c080f0301061701030314070f1406090c01 66
    0x8960300542640c0042c80c103008400c00d0428111504190300040c0d443c0c140120005400724800903a64103810b402410640300c1e50750034002030f00900000c2c101ca01c0e2040d1120003000040000009015202c1c0007108858030341343c038031030020305560301c05405c0e04016001041a0751584800141190340c001080c40c00842c4065a4141141c0f0307030b450f0540051282d400d03d00009022648594040e0103681d840f4002c02c039180a0020b03040460381d0241300c00003224018004401c2640c002d40c486001075018039411344001d100b00c400181a000110740880e0148040b00920007c00082041903a000450350700035442c0c1004d640008001480041501d84180505065007a00c0d13441010b140c040603602080c480d0b00c46040000c990301caa0800d0161000292881d0411403080703480384035041c101e80e010340b1400c03030810340b0188108155001b07513026510f08250200e20f00010b0040c81e140b030201440203010341054201600918103005900c0320383c9040004c00d6445900c003c007001c0e84807036074002524a602c4810340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 268984892 1250 268983642 268983647
    0x10f08041109190911010f05070c030b070e03070902032403060a1a0a1202130203041e02040207140c040e0f0c0d290106020106080706080a0903020703020306071709150c0a 75
    0x1688a44211240c1004c0d4110200140424151007a10090325200800d9143c08800c540500410b080507050411201c41003000c11010030405070400514509944801c0000011900e010341315406000c9040c0d00108105100700c1c004d81c600340818882803210481065840020b58070503000c2c0840c0440f0740d441103011400754014055802c105005440310702070b41c1e44d810007011030f141100c005038019200e020340710004c61482d108683c4540d80c00665545044850390549074107144d558000c81e0065070800085000c80c0c518014825242201e0000f02003540307000d024001640d0001d1588803203a40001052030440e0f40104080101348815110480311031500c3c10b1200d10500080400c010b1083ca00705000c07102e14070a000c440c1600d00c150001d101e12a030340c0000c00e5803420b040c072400300080e4044c008940410242d0f00541c92403400b038411905004d8881c1c0000c1d00301401a9030b040d01003246800382201a50406603280e5101c1035860103041c81d001d400c2104a00440001c1500c003580600140c207070992070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 268986142 1250 268984892 268984921
    0x20306130608070302040e0303070801121401051602010e1c05090d120905121506092503020c070e0c090906060403050303010305060a0f0510050402031023010f08041109 74
    0x80c104400744070080d520a002600d0700d20502003a80210300348241e0790b50078034001049078010a200d58408071541e20b030030150a0141c0c58200200c480491440e6134003600142400780c0b5001e92991103801d48501030b0440c0c041e0842e460440d110010350020031008090b61907030000181d80500c1428219500c5040000042d2000007a410091104002c0400b80c540c5c1540200d0b6001904d2050f43d4000040d80d1052007223680700c10844810551520320000030304142029110f0f560040140d0102e240080320440c03800c1a441c091407c0080003a902140c0e24150800c100200001420104ac4150982c01d05044650280c13141d0074100f40510110000b088440d2107000c101c44c0119000003e8075100e503101d241540c1c44540c150340000b81e10b828070458442848940c8036242c051020303034079014005442c0c1010b2001075080207102500040720b1240c001034a021609070b45111560044150581a411000142400303506880300b608120000d41044005680300c071010050f0b640031920010316503210119000f000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 268987392 1250 268986142 268986169
    0x12060414010e0f0a060605060c070302040906020904090f0323030c0a0c12020105041a2401050408070b1c0e100b04021c020309060106020609192306011406070c09020306 74
    0x522034580c8091003d2404550000ca1034071075101400180e94800420065008000003202c0c6a0000300040005150543c00740800c507109590142c10038110000060840d01038590079180c0751190101c6004055010f60358103a5407442010510b188070340314080c6130441c000140740f01029640051031300c01040c02451403a024a07480b45080e0709a02040c00d009000c1d01080e02c04171070720b5908024641481a080c0f8030548100c0208150b8500184074010501820244038034250600c01c0c200300c00715210b01c050000b00e000d06421108690340f882c1c01d0b504281e081c200d2040c0454210716080000d01a2039000c103461444402040000c1040e40010700098001d2050103001c000c03400754001d0352004146030785c024502c103605031700c180e80d4143e070b07079100990711044100c40d001c80580010b43c095084e07030f07810007003452103d0091520744c0d20381022010401c522103803100e203149103a0109004000b400c20318000c4251982e4161502410030086581e0101565000c0c099035902075004400034600e901d400380c2a4490 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 268988642 1250 268987392 268987421
    0x807021b0a090606020d030608010c0c020f0a05060d0209030f0d0e0d1502030a060810110405060706090803010b0310090c050a0804060e1221010b041403070b130f051206041401 77
    0x3c842e6110000f0f507072a004500e2a80100b420182c0000344140103101b0f404928540d40c99140c07580c00349a00304400e12070301c150419889444018085265120103000e40002d0351358807001a9a03250301020117107000541c291903452a4400d11030048400d9101c040c04c14207502c01d4900c0640da1001c1e1500500010014a0034040c1c0c500c0882000740ca02403540142d812214014180d038a001c1c400030045060f960751981846440b070080100300f2060800c2d0703004015032401850b002420f00c965030307640e44a036442a4002042000e011081c454103400c40803c1c031000b40040e400801c46120111405081070041200f9541070001c0c00c00004c0a10000d90013896202848000b518008030007004581c0890708418040445542800c19507440041d01c5c2450340c3c141c640071072806041500d09a025000860413051058042c0a000c00000b4034030f04800242408510166820208a040a0210403441c41950099110305400c220301d01d801c0d00085030181c0c015030401d1f060038192040d0041680580404040c0940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 268989892 1250 268988642 268988651
    0x510021c0807080105100806060309030409060f050f18070c03110f0f011a0102070308160b010e0609070306060c150e0a060501140d1a090a06050a020c010501060807021b0a09 76
    0xe559000440300d115544076115030450703036200d0043c0446005d8103c840b10200d45400c0100c2e080b8501000030350b600c01e09140441e4507140e1100f1480c0182c9009600011441403100018440f07468086a80801c500382941e101030f02c04a01c1031583d80d1180040c14a90a102604000100340752041290440c42070103030085840903900c003003c0b0340d0307a4107130560000300039460040700120030242804001d071950f00580c0103182c510b0960f1101c00d000c1c3d02642c0c00c10f1380c01000e002e203080082c8080f001030b8004c15002810718403c2c6041e070103008910070300401c3c031010185001d4052000d030307412140c10943c040c0c0140400c44802402d000000090110008882c0c4611a1a4514007080581c1e00190f040e25034242022802103140c4041c02801c0c80109001054480c1c000a040141503030619071b1a030220707415003110040651601d0f0b030000c40314113451400c0340e940c0000300d1400169003406032900501d45864040303014078010100070340b60740c0c003120845041014940c3c8006117903582000d09014024a600802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 268991142 1250 268989892 268989943
    0x3070f0f060219171006142209060506030c040b090d02030708030c07050a120803150603040f03020c0d03050313050304091a1011030406050a02010f0e101d07051002 72
    0xd0705810400c504002420058100705481040c91600d40034050440c107484005042c003200303079040080300304880018402071280d10100a40f0f600c540c2d031080240000f0282344d40c18404820103640d01c90700100d000f5030082007409100121901241c040b1410100016201c005c0070001401d0b002c0000f5003e9454030031144085642d11021006121641c0400226420305550f074003441103000302803241d01c040c03124140603070001c110707190010b580c00a0300c09581d001c484080760008045401c165800e0307030b04401a00f850303402c054042104e00070341207048802800c0740d0302c02e0750002c1080c4001044000713420a080c62003800c0040401c291809404058414000300799400220504a8000042e2500c110040b407000c035a10f03405600240202c108180c0914a45428424140c0d429400419548210343d40c4119044622200384115400b511003100a45000154201801d090b1118003408140d49801a83d4110003100001030345412520141d84074000b401501c1c42c00d07030802e0341002e800c0080c020840c80c00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 268992392 1250 268991142 268991167
    0x30302031309090c0501050702130509030405100318080d06180b030616020c0409030e030f010c03060b0405060d09110604080d170601051b030c0f01020904051803070f0f0602 76
    0x1081ca00030500e00d5040c14941c0d90ba2144140c0d584090003130031300c00c003c260500c1079501c5913000340402c1e80058510009041c04d801e030b00d0203c91080310080001d030401708045c01140340036100c0c10b441002d249002e101000460f12000d600c200c04520042c141d440006c0c00b004482c0351170304054000d1075805060034150345103410000141c059007a92922078001c400000b99030f04120065070540222960040460b0900e50003400010700c0410781c25024408403900f07c0b04950f904200c80508800300c4400800c801400c688054240e170450b070030081c1040414002444103440d00403c1c0c0f52036461400d004220a070260400c001d0800700e540c00141c22200020300400c0b0100e0000d03044041e0b020b80c0d1b542c1c068100010408040c8440103644550016008224002080c0340b081104881c80804c6404c4e80d26012040310024039000d000c030071303114490b50041840320075441c091040640c030400b10a600200500b0804080f9201e01c10020002d0804d6540c0380d54400f40b0040d000400c581c1d55001904655030b20840d80324 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 268993642 1250 268992392 268992397
    0xc082413140108070b0c0712110d030302070201171302060d021b03040e060402070f061a1908010e0c0a061209060204030807050d0c080315060c010507080106021903020c040e010b0a03030203 83
    0x5000113842200d00c0000c5246041e412900d846581074047d0800c40d0402c00c07101c581883c110360070b40b06090032070400d4003039560702c0d445800414841e860051740d4060074800580003441c6000d4102d200e1001c07404220201c40b01c02043c500c03055040b03038816074901c0014003000082c021702c2d421101c016102141d07840c01030030002c010302c2501c40800c010500c0f5900c00080200b603100d0010020180b070480e046080014205800c0740060407080015200701c0c0540a0210780d840058100303900c164040701104001d2a0800e225464601c80040042d0280401140109522203010304c106000c02000c1030741c40e014600075900080c19140d20040544d5034a03645d090450642e0415103064665001c1c8500021200307008580b8907a1260303000840c01c1c1943d5680446004075044048800d13041503080000e89001c1c01c0a01c503c600c18001600d8203141ca505140000b490507865100d45000318030b05c0e54408010980001d446c400d04582150041a000003c2c82e625001d442c00c8010b95410011f02140881050b401001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 268994892 1250 268993642 268993649
    0x1d06010e1009030b010f051203090a1a0c0133120201080618040302011a1e1009030b090114071803060b011e02070512030f09150f1c0c0824131401 64
    0xb0311001c02304030384881588070310a42844980c80500100100501900101049603812144a000e82000e20000846007500d01e445401d4000040061741018607007943c00003ca0008030101000d01068188411140a140400c0e00603050000740000980640d450701c203140e14442500654110034281403178080c2c040d0001c04103034800e2103a00003050300385040c540340201018180c210019003600401c814044c0015002500c4400c1240c61000480490140005207001d44180300c0002095507200c542200c4032074001c1d00540401c224581d4a440140d0103041d03603001e89411080c001000400400141c41000310700801640441d8440704c0001c40319000300300102203503800d40d80d0518070b04552600036180c1c89503110120310040140000c80c0c05040445400079038508040c0b0140c54100328803240c40840d003115204814015040000411071200b41c0103405054a1500340b510041c203054400c0801071031031840f85005500501d23f143c2c2c140d0b4800c101180c2e10041d40e00c081141d152003601402c3c07100000d01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 268996142 1250 268994892 268994899
    0xb121203160c020f0d0c0909110301060b0a05030c18040e0d0206090309060708031003060204030f0c0e0c04140f060a0f1b08160602070602040f1d06010e1009030b010f05 74
    0x290100295002e40010403100358002c00ba185104114400c000005260b6907040e51b070310545c64000300310004c55200d101ca03114040c1500101c182000d204150940b070380e43c0c103c881c0500d4244081c40c20716800c581a00d030071a00e4058070350344070105c210030f6030140f01070005510b034013a0501d007501e814000f020a00c4890000c8503800c0c0c6001c0e565011055640c3c0c41070143c40d50708110100010070100c1d17855400303150440351405040708220f94a484510590b007140d0070680b0607014107400d00080003c101c0c0701c080100400c2500000c40d05d403483e400c00040c095480340760244840045600e40715983c0403030100012000500281e181c2820f20305c01400b9158041e44c00c00882c040c111821003010314000c03440503055201e150b4034603109105000c8070301a00c24180440b01c2507001c0c400c1c0c4c000904070740040c2010300041803001e40c0c2e03e0710f440264203000518107c07140b8081c07800001d20405074ad201d0000c0c0683ea030282d8009002d4200581d040303c0120b07050b80041e20b404840000842d4404189100e801255000c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 268997392 1250 268996142 268996171
    0x20612090c091501031508030a090e07021b040906020919060306090216030c02060c1203100b0705280c09020307021608071823160e010903060b121203 66
    0xa014001044000d45600f0341003164140c5080c03240d8803036040108008050754103840ca0319a100d401c140307181c04c0583c0d01804160103010500200185a41c0c0c0c540c03003031551000b405547c681981001894410030f020078011500c40591509000c055011a400c24902400c4500f105124900c1014610f96601910000038205180082c81c400030f0b0080e00d29820146030155114111a0b50980710701c0c140302d01c102c0e08400140300c80c084104007480740c03a441e10340320405242e80780b0301140d01880941c55500300d0060200e003401180040380000440b141d100001c0300c00c414607940810f82d61360f18241e4403030005200005d20000030640c40400e4000e18043c2a45400701e6004010500144104041a00030700095a101d246e00300101005101200c40d5202c004800050b8201184041d907100c403e2410f85495140c00c11003840411641740500301c15540280c41d052107c422000c000924442003840003411180d01d4161041c5166030b0302d0641d031407100caa80222114100040040300d11500111005d44041610 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 268998642 1250 268997392 268997413
    0xc020a08070621090209090d4104080102040b3415020d0504030c050c030120030604020405060a020706080c04121203140709090e0c100f0c02061209 65
    0x841d00261181e0340c45032100e0202180200e12240103c0c0d94000c521501e0350750080150322207a2019001d6442034002d0103e400750500054140c1c80c00b900c0b20341124040c0e01c00b4038401c0300100d40300300c0746024a01018000c000040d101c4020350007150040510765100081c0061782054600040220509240060720111214031038514405291180d4030b8280300c0c80000040007680340d85070320304040744014006040240600040f021208107c808401094449100c801400400c00145030070280480c0244003e040540242d54160441d0761495082040480800d03010b64442d01520007509004d0441074844100b284005e40d140d01510443d80440d680101003500425070600300c40175110504407801c0440c1940d41c0c1c1d88155140c0007400f03410907640c0c03103064071400071130100e4034041c1d03600d81c0d0303280078190816004008845600140c801258000d13942c1c440030303442d409020301003080300703082100313500358028001e0320070106042c802540180c0000724000c02e00c800031026401018410200c0380d0030141d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 268999892 1250 268998642 268998659
    0x2010b030d0e061303170a0e0904020a05040b01140f031006030207020102060c0322030e040c0804020f012118120806030718090203060103050a12021f02031509070c020a 74
    0x4820300c20310000d4000b980d00c881c2400d14400400070000806200064181e5a0b01c811a040300100700c2083c030078000290400520f61f21a1801000c0001141d0042c0700d03042c1540000c90309134081c0300b450b0041e500d519144103182c2c0234504442e41980c0c8688101d80d101d200b001041e40d9a031048a040740824107464010030150710a1098889140d8180c000308002d0f11203200b000700a80000b81480d0043c5c1600301002817140c0845003804503240b2a41300c0340112130a0342d041101b52910101030104000c8918100405170ba51a415202000001c4c2404511203c0c400d0081490704030a00084800d2820040c4001201d01c2c0011000c0350036000350b407038001040644000301c55104003070b15955810351110100740301007090301c0d04400c1d002c494854000380c0240320745d000c20f0511500364000d0310290068100d400910016100100400703906d48007030b185850002559144141050301c500c050a0303804800900850211a07040c2d0340c105c002410030440b4501504018100407458000301e02406012000058200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 269001142 1250 268999892 268999903
    0x3120b090a0e0a140a030221030c13031211070b09030703110312070b0717010e1501020c0414060f0405101401020c180402030729090a030f0f061104050d15060506040b0a02010b03 78
    0x10a1072343c007a00d15215020200d4441d00800e00f10902d0700f2207000000001501d028950000e54415103440c804083c00c0403d0606040542e44042e0920b00108600803403598040f9004060340d5002c81032081d4451010042860482114000c00e010140014000d060004001020340320701d4a41d0f4030145207000004658100c12000c0c840c40310700b08508400326105103c021f1007100740b01c00620480f8282c544800004065504a0100e03003004001882844050304202581d28641c00c01920300b032005091075a1550441052031103240a001d80c1c0f00d04070321843c2e20a001c587c0300e800c002402c441821a085910071407102050303c08038841e100e08440002e00955a07088110024401c211101a44428686040d031903881840f209601055400c00400002c003c80000c0300c50300e00950442d112641c8501d032a2048800d5120303141c020303d800b84000c106594607120440540c550060b0319501c44401c14038203030043c140365000b003540a140440c021030321800c13000140c8648400341d0f000b030055000c600c06050300da0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 269002392 1250 269001142 269001193
    0x304060f05040528030915020a02040c180503010c02150711150f10030b07110a12050304140a08031819030e100e0603070f02100207030c03120b090a0e0a140a0302 71
    0x943d46d510104240e8158100800d078040e1036005580020700c0e642d000404850240c06914003050301028441e0181088841d0f0201808094008104100501c0741c003030350700c41300a850f001125881740000b4000e94454238441e1824103010f030440c0c1c00d0a02400103a0020f65040b60320003810300f1050002001180f80159540803690041a40c50701fa45900d1011a407402400c0704d402403911610300e00800154201c1d02c552a460b055a607540d48230700746450036901d40d41180403411001d0f07000d80e2500c80883d003010100c94000300812105002290000001401c1010702d6200c0000025807182160506030400c800381d0791082d040340c2070881c80040030002c2d10001e1188011a4014000f0300010719003500400310042e40a98900448000100843d900130030b9900622041740001e03e0001316204154124202800d080c0c00d100091101a9440c4089020400c0040c0405880c54880d200c00e180d01c07400303202c08100c49400000300c0c4180424650b240b80d90f4180d00d40b080380140b10b2110254146d020240c2c030800b09 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 269003642 1250 269002392 269002397
    0x30a170702040c05130302040f0207021801050a1a0a03050a090b1e010503010c02060a0b0d0b130606090516030911100302130806010b03040305091912060b12030706020304060f0504052803 82
    0x217071030030750302400010110418080200d644c204003c10141e656900c0000c001c1112110341989503040a0501c01c020b01030361700640c00c13404000304048042540809803403e4032950719001601d5070765442c1c00e4024182d200b5001d840e200084060001c0c481500b14034000924082c82c864440ea680c4005060880d0f01d080030900045e0010ba011880000a0360041f14010100604800059456459614042c4003c0c0d410340c001800c04003445040000c2030180703400a1561440411045c6002056091050010301b42c4004060782c1c0c903070b034100300104003043e1040c88201506011004220b0341c0c01a00a620a02c802d030360780d81c01e031000055103c0e40010094181c864090980f4150b8540e580c0940e8160071080c02c40e940051200c0c1c50051280c804003400005040c0f0601000700303400542800000c54503802d040034010108481c40c44034000c000800c0f0f40649602500050b920394950900c0002808262404c14007507051400388000d0060001d085519009081000c10440d24009180180b4501070b0100402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 269004892 1250 269003642 269003677
    0xe040509070602100207020402070c2c0708040f03020a0804090c09050a05010c020607050316060b0414040201090612020909070207050102062202040c051608030a0b060c030301090b030a170702040c05 87
    0x1004da415005041e0700d901c0a031001d4206103071956180c100e100c4a4009114403140c06000741c030100108002c40c0e41304c10181100401d542056603000304151001400a4010300c04003a400301014420414000f1140d0407403580740d2503d48690030ba8000e81003007800070300022a00340000c14540361140c0d0200841e00305031608200c006440c0d0a2149c0e88e00240c038140c0f0507010a2009031003003428a240c241da140e10411000410310720703c00401c42110664000546014603c404210060f6000030100c0161411403c15040307408000c0281000303841500466500a0000c8040c890901d40020f10705040e11000d80070b1380e50755074400c44d00c14100f0704400c90409030340e203007001281e0140c101070344005556801d501d403c1e46016221a40b10039035922412080b03d603104004100191821303180302e841070559045500502d4041400c0c0304c150340b0b01040c043d0040141da540d0100807183c0e820048250490b038003036000c01d528681440320450540008106902441c206111412864455000c0742c0310300c00f81d03401001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 269006142 1250 269004892 269004913
    0x504050c041a0c0106030b01051c05060c0c0102040f0305030408061605090d02040905151005040212060f040e060c0a080c0a020a0f02042403050c0429030703020a060e040509070602 79
    0xb10502801034209424400308440761140c0801e014400103580556869045c1c0c1d403400090145d04a40386590300d601021080038400000d030081402500080c0803142642c031250311403c000d00920566011443d05280e0b0800002005400300162084130840e0040c0c0ea41030740c400c2a80349001010748400000103d042000007030341c6c580000ca8a0380345001500007c1c2c032484a80d10f02d0325014500340d444104c1300b280800c002440c2080d002d004094403050390103600708035541144044040e0007802842c03180840a40183c0203403200c1d480050101c1e2000120f40c03442c1007805419034241e00190801000400c054002010030301d4041c00c490702c0242507030040000007400d88545243d0040060200e038810b485940d01415a51942c107155108034003052940000b5146160030362170a1041c4a000d4003550800c039042c4082c0782c0c580e0324441c0600c19070f10103a201d0141e00001030f0500e0725a420080d4400c4a00380045002d81c1c1c0720020100c09c08081d6801c001c66101c032008180d0320100d6100340340040c2d1000f50404c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 269007392 1250 269006142 269006159
    0x402090402121b070506010308031f060309060b0102010b0f010e0303090612041203060308070204020d060b0c015402041127062d0705010e06070309080f16050f160504050c04 76
    0x116070003000c000181003100861801348140bc0c0140c5d000f0000a5220902c41c0c003801880d02c2882d4641b07401340000c220250110b00030400c81184841e441d0306100800b81d0b421000d44090045984070340740185910b41c0c40039800c00304c9101c1c9000340d0f0f098400b240240320558140b8001d10440040d01c0c1c101c1180c0341001c3c2c0341c0e03003004042c2d0701590b5501100e03621760200044000321000a09070740062040089120340ca040480000c10a0709200b044034100c520700c440407982444400e00c207608400c0c03a00500403007020100c3e18a50140820001e4015141c008803036a5034106c00068442d02600d860801640c3e11080e0884048031810b9461542c072240411000c03c6402206029071414080b444007500ba071380980c1030302c186503007041c0d005403842d94640902e01c0000c0014001e20394000d02c1800d04110905642d101c440c0c0703034040c0c0c04042101480014418100780000081803400740d5101c0d046801d041552004141c4a003001c04105c140029070320000f02d840d2070580510780c401c0100114060500d840d04401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 269008642 1250 269007392 269007397
    0x2060706050601020a21030e010506060313030215071d031507050d110301090903030c09031a060109050d0f12021513080912060f060402070f0201030b0402090402121b070506010308 79
    0x3050561040b000b01c040010500c1c0e081c4211000207406c018403811482078090182e400300740203a440e0707914141c10070032030741c0d039800680381c0042d02401c800f20305494a1174240d10380150690380300304030780c05041081480d0742e000b174025002c0f40400c0a8404000007030824981d0701c03c00944056985501140040c146a12640151103008458240822010104d00c2c071308009601c2a0003d580203a141c0708103500741505402124600b006070300d40140550305d15203a180612402c0c9420140e4012113801140345a0700c141d40b214064000108000d51554051601a64041d5004421101d07055a43c5c44408500e001203018010b48003081181d031450707a104a00320011065403441103c0301082401541541e4a88605050b06040c11000030485810a0040c44d0107501008101c1031052b0300401c40304000501e00391000340d40302e5087c01e001c1a02c2c0340000014000c0d003e0030f007000c0c1d005840841c1c52403402901000341c9000d0050761541d00e40ea550a40388100f41403080020140c80e40d4041c0c0010000609003500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 269009892 1250 269008642 269008651
    0x9011704051906020d0c090b0f03040c0509010605070c081204050d060e150106080c19110a06110702010e0f090103021e0a090c0e0301060e01050d020604090f05010f0902070206070605 80
    0x59030b60340e101031440000080304400003a10026804100e400c640304051080c07019450281c1060003000e49850000a070512544030956460003010001c1402c20240a42c0d0401400000307169104943c2c460070001d080b90008102920700400c80c050015410601140c41e642c41c0c8100c210446c034180c1043c0a00865001c0c1080450f0032607550402c000510f081400404030824041080036455454028010201240900100f800010401074481d01040250a880e20900b0f141000392210b0f141050355810521041c0d0040c0005003403540008076600080001c0c1140c600c00d8880550726180007040c4066500c1d4031034541d401942c458014405031803c0d1509a02941c442c16000c1e04940c042d101090b215540c41d4819545903844032000c01c6425048000100300700d074250000c2251502e0f000b01103c0124042c4640d03801001d080d2881c505545400080304c020748200c100910006150581d0071000f01004d104005102140010128215440e402280d100c250002c0c03a0318200222a281c0200801d40a030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 269011142 1250 269009892 269009903
    0xa030f060b2a0109062c0a0b040519051c030204140d02130e070f060309230a0803090d0f020d0207060503150d060b030c0406081b060c07082109011704 66
    0x44640b80c024009028410364584203003000f060075541c1d07001d5400482e50300d0500502180e280c15030790002e000006401d03842d40707411019147e010b48441c24810300700043c0d0601402103c480307044850a114000805400c070580051401404800d685000c400728021405020081e4415051a0b40700e45800c10321a40c01c84c2c00201580203220318201200f08440461840ca02d15400a0008100b806c100040d40703170040c525070030140b00d542d0460b511f1310442407103001010400703089000000c20581b003c001c61010f9940c411100c40d6a418103051903a6a1010010014002240d2040ca800041d201181900d40b105450b0003c082c10340c101042510a03810041c000d0321441885682100c203680c07083d401211241c050080090160001c4040c142001e940d110313943c0c051410302d401000ba0100003e0501d4080c0c0316060307152258a620800070f1028802d00440802521039071501180404011680b02c80c110180660b001d0030110400c04500c490041001c0300703000c0b0710540705c4402e013103080c00480d5078094441e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 269012392 1250 269011142 269011207
    0x4060c050f071b060305040b04021509032d0312070f0315090507020d03110901031a181f06270e16080c0306210312010b0a030f060b 58
    0x1110520380e1504990030544412030707030009045034031005020f0712014040c180b80901c42c61038981c80710350b2600c00c050002402102068114018118894182c80c02841d004054918900c064264030521112401811104071040d14a10b01584000403c46000d86007018920000b540c1d051403e541c581d844254001c103240d214103011074034013100000040070f172498907000a242c2c10942c0000b0326111440a0440c01e161609541d5400c1d042d0402c140c80300a42c013440c0104401d0b0000341068690219001040d400c0800d92520f1101d031003814002d01e2003800b5042c0c0a18800f01c00e28a004002c02007846180080b50b43c24113003141205188624030a03032040b00c04131300f828942d2440b41a205140854400800403000285245d14690240903d0741082011b1a010305600300440043c99024591648006110b9005100d0070150800c2c0300340e03940104513206410300c42d1395541181d08a50300041c42c0c600040c0c40d106d034100c0214598410071040d124103480c410b00f0404c00c10381c100c0f0100d200c0c2c5032982503468203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 269013642 1250 269012392 269012407
    0xf0607050118080d0c020c031c020c06071103061b1e360d020a1e1706150102010c08061228030f1e050702150a1d0a080604060c05 57
    0x180e4094000d1900c2450307151364610b0180d0f945012603c17802600021900004030500b0340d5500051062100103c14000b1014052013030420fa1510000d140c4643d040100440c5500500c03881d84c00040b08480c058060310002c3d500c0b18011041c180952954580a103418000000c40862020740107182000090615145c010400c004c2001c140c1540c982c40c00c0419101650034a9a4007a00030749000c9000362100100c20400307600240504515000320300ba0350f0f4408440007410050080c1c4c110040c1540c2c449440500c80302d50307240c0d0f2282811039100e60070302150700c0c44403d01e52051060480c2a82c01d541e030746100b5222107041000c20100f25101c09600e00c40c140c002411421000662078001488000e500520100d03858042c1000701400c01100c203000101412001010416482111501244c0f400d180d4941d424800501c81440083c1144e603503003004500520055003040c00440710300c094000f040801181c80003000308204450040a4160300410301103800035180c0c0d08400c1610b000d500708641080903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 269014892 1250 269013642 269013671
    0x601050a090306050c0c160801230c030901240f050a0b090f3c090c31060c021302040b041701090b3903010302190b0a1701050604050f06070501 63
    0x1981f207241070300f1b04500f00007410092080824840c400c0c0d50102e084580500f29080c905802481c1004002d07000000070800c4500b9401065800c08080b00242400b20f42c02c6860100d403442d010b00b01d400303840c404000c1064641140c101045a0280b4402c514082d031b11410700050a60410442c2e811090104100d582c101104511103901200c84507540c00d0a0007604160003401c0043c0d4140303000745118418071045090700d070111401c41c824103d5800c1d03801040600d143d01a007040c414004070b100c0540002c5140c50307104005000342c6000319000c0038450b04510240040388641e00c2600f0042c00100010054031075000800403035000508000200c5541030340f500ca070b0192040354841c54540b01c881b2400840d030300600340905504071050b2214a2519100b0318070030030b48010700003e40b10701ca80030719284030074000383c0d03044001e007548410031502c803240624064090b01c5036005100040e10548000f0079242041e506542c1250300051800340400d69810500c100c0341d0040600751000e540b2180b16240d400c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 269016142 1250 269014892 269014903
    0x90804080f01050a0203090c091504051008010c090807140604050a0602030705121608030a02270f0105070b06010e13021611030604020a0303030e0c030105010b0a080601050a090306050c0c 82
    0xca001416a96005040039400c4030401045001068818401d02c40c1c0703480b0014a060080405441a40131604ca14503100c0b059150600016449410301041241e0881070490b07103411290b1145c000d101c4240d041e801615a0303000d5000d42c0000e64450340040114090021001105c6003014044624044d25580031501c03185094104d540580c0c4002840c00402404001850070031401c0000b0b036042401046082c01402500030000d0700e040c00c040040f4940a0459040395a1003100803008006204542441c00e0303000300d000c0740c940c07048544080c0700f0032079401403003211075850380f00c18014260740d503d00054400e03601084e21290407a850520095501c003035840101244000814401e1406400385441d004845214124601a1b00654284001038540850407030990358103007808552001d40804091405802c0103101368036600b404000903009040c1c10007031045c041259102c0d02075950b04401500c451050203042c0000840c140b1041002c0b9180d40d204a4020b660001403618050620403240e1614 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 269017392 1250 269016142 269016149
    0xb07030e0f070e0f0405060402101202030702071e0605030609071407060519141915240302040510031a0d08030907080d020c0103090501111306030b040207020a090b04090804 76
    0x9510004050041c82c0f03c1503a001da004d800102106611310701a41c0345c6440e1000a00000d02540e12203440ea8402e038092101c0420f1b00140d12011900c0e4074000e14000c0d1398410700d1280b07185030035000410001c0c1c8030407441c0f0801170710807685a151030751722030409105030048010068001c0047c00c2d01a144070020420003440c0440c003401010503582000c0710029940d40182d402e0140b518038100700c0c0b03003205048001c0306500108030341104449285007007491004c1c000400c01942182d0010401241046070407860f21000c000840488062500d00351055080348079a0013080d41c01010050f00e1282c05200ea007080c43c0c40301e82c13526200d48944c40800428901840b030802214490030210800844041c100428402040d0040040002c000003900107502c0f5074044010703504154680e0804014000c00750018400d01341407800c001c1c2ea601ea0001a42c400b4013030b074000c140000381071814402c120314060003030326003e03900100f00002a510302826140140180e010141d00180c41d03000c80004140c80b0b00c0500000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 269018642 1250 269017392 269017423
    0xc060708070e1e0d0b07020a060b031605130905120306120109121d03060103030305061e0f12010f0905010f0b0a030c050f150a020a11011106040b07030e 67
    0x5a0806080240991000030080030030001c0c105849000c9030f940d01c552600040d000c9181d400b082900c5400708210404101014042c1241d1a040c002c440d80d0003e86078044902401d810031280800b8001c154842c3c071100661803800e254007009010a18006030203e1a80b02400c00001e120115a80d9107400c0075070300110388540c08000b104014550504046030500880560001c000d45091561500000702c2d99026440030001200c2c4c103402d181170103480010803860018100e44056a692800401500040324030900865561010303032003007840e0585600604100504030050410b042003448022403110b5112071456480d06100d400b10312203403040c003400502890000c101c150030890800190b13010815400d014042d0007104002044540302c000080e02c4080750500e20b0802c00c500054500021400804025440061107031502c90300000c940e51030b07a10956550103020134500064030243e103104811596608101c2c009800101d900000030f5000d402420001201d8002c40360b9940341c040640c1c4070010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 269019892 1250 269018642 269018653
    0x12010f03030f020f070603240e250507110105091c02030708030c070515040509010f03060501050411030a0506030f0a030207090e01050c12040f15020304020909010e032b020c 76
    0x2450781c0151602500446800140040c41301340e040c2da66111040c3c07090000301030303481e0031412002c8078000310000c2e111580e0100102003621000d589210000039a440c050a6810003803c06044900041d907050208554031180d041c802c05840e050040c103c00800c1c2c9041080030405c9034031a565000b241050303800c0180404c041c440d0140706251034808180c20609182e031040c04170113500d85c0e0000d030540c00d0f501c00342c03100f10803200030b110400690300490f00116031001500c070000c140c140000120f42d0449006500904c8981d9a0700c0a01080f650074941c00c0341c01f61130400001e043c400c10390300002c1d086000502120f0403081c00007100c50030221134034002c1340103802c910000c1240c2074181c01404007054980d4020021814401071111462241e1034582c1ea00350103480c005070034080c051050781c5000b42c22840e45d109202c803800b0210001e5204550403481002e5480c08240c440005101c0d41203c3c82801004500e00400e1300c044401004481d14100326002d9024a0003580c0c801c1c900150070114010401000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 269021142 1250 269019892 269019899
    0xa03050a2303190b0d1e170c010f020a0c0308090703050106091d0c1c03120c051b0a0c0513060b0a031506021203360c0307060305010b12070512010f 65
    0x4400c600f0b840309424903030b05004080800781e5641080d10310b6030340d00200c40c805188501c210f0912038000712001401500407000000b0701e0022100040c40711803660b200030045040c2c5c00d600e0800301c0c000c1d103100c000040c01030402034001a0141e0000c6810003902c404030341b03440342d50b603032428251200d98100313540541e154000054021101c405058a00c4d441d0304c0074041d100703d078001241070304103850307101c0400d0180929508185401003c084a1040d0394010500003080981070252440c0c1c0002103590f00c110621365920f0f000034003c50f5441e2201d81c0000c121849500e000100b2855048505c00d80600c41d584030800104110840006c1290700e0440e100411000a8503030070351030a4890b5400901550461041d081405600d41c0880c1e51144400080000796200b20452800449201000f5900444012a2001c2c840e10014080103901c80480c100c4007181d45490003182901c20078840c035502e0210a004d40303440303080c1e00170802e03601011910300141049100f000c0e000b1940d2081e8000c4100804014051 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 269022392 1250 269021142 269021161
    0xa0f021f0209042a050726090a06050c070510020c06040e0a1b120903090503030d1409030705031602010e090a0501080d051213051c03060801050601030b030a03050a2303 74
    0x43c48043c00c079805140c030700d20890600131001e01580f2210760400030005003c108104441d07080d40400e4a00540d90320440300000b060842c0c1c1e5100c095800e218644a0400044162003030b801c69811003003410180401c07918090a00c414502c4014503c0c00798050091102c8141d19800041c0c8014000590050361a041c02e8400c402266042e414095120407041c145420700e0b40c101c1e03900e16852140034000940040541030480ea86480c03038200c254107000006901d82c0341c1106800c81810141d030350046080503151000d0040e501c6c400c1d0000201160014001000c1d61b0110304001d0300300e580181090805903001200090121508680d00310046540c0c000601c6141703030130090034a01c000203051040c0703003c4280d1101e01c0d004000401102840c1081884d40040100032f101040b100c80130002c84900d100f01c00d0801402030001d600407144290300c1c110000340c0562090146901034000a000340064440359113040340c2d198000740c800700c00e101d03000d0803191040c052210882d00072a0450b40082d228280702068 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 269023642 1250 269022392 269022401
    0x100b241905030a060f03030f050c070909050a0309050f0a0303141b07081204030b041202010906020d0c080c04030b0403140c0a0303020423090a0b040e030c150a09080a0f021f020904 79
    0x4105c101c3c4400c642400026001035452803803e6440c2416a10ba401e03908030720b4604001c0b0341104070058240300c000303000c001c030004900000c24403d44406151a071168103100000119402c0150f201d1130082c01000464000d5061101c01c044810751549030100c02100f0840f03031714417035516030140d0f8421801004503d90034040490100c00103000185031a01d107071a20210040d0107031025029100141c182d03d0814001d5201e028281d03031141c420354554401e04000001849003540c0311000c80c46100020769020403020032036064036400762008140d601c540d00c0c00c403000424130b400c05221910401104044010800c04c0850b003510035500540e40380d04200184804040c4809451400b2208400381c022030f68400c40300340d5002c0c0c08444002903200e603440008000d082081c90b828920300001a51a80391003020503001c1070705845169902c203c1c5c803040b4500040340c003249005020310341c6c10f020f52003030301c0e01c0f4224a141c40da05a01c101c0b2074403200c000519001008091041c00313000c0c2d0000c0d820710f2038140b5016 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 269024892 1250 269023642 269023649
    0xc0e19050f01050f040f090503040e0c0a12020a0302130e01080d08061005090d0506011827171204050115080610150c0203030a020d090b1e0a050715060503100b241905030a06 76
    0xf0f41c40d0510070370040150004a400c1060041340360080354801c10031348245d064840030098503003000c0d107076580c4a005041c4000d0a005000c80741c01000e80c2d407015036010307084260049002400d82d10349000c804c00202c030700e40c2000c03a5071a84040c6404201340460420000213000e45001c4405106500c20300904a040b034207101c00301650664507000c00b403407841d406282400b060f904140c10104115110700c1e414803034814501144c4011a03484103000034850154480c081504203107000308403403034482c441d895860508960910309420314400512010030900d00481c10406a03040200940c1003540c0001d0554101c1e00d42c0100603440042c15400040c3c1c0002a800200154401d44d17103003415182050800000608101d2000b00c8001000c403044ca02c108100e4400c1074101c007403242c1d1188032142e1407001e05003a100b010721a205181c404401031045104440803207800130038500000c00103040a106511102400401c20340301806022007800107400b512480045940e2a90b99a10340103c0110450762180c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 269026142 1250 269024892 269024911
    0x4180f0b03031b030408030703090e0709050d15110c0f0c01051303060e0c0402040b03041106030c040e06130213030203160308030105060708070c0e19050f01050f040f090503040e 78
    0x340d488041d00d011049480c4195508070050441a0703901c0b50b103103144a644d005100798480080c0300c0d01450341c03005c1b0042c06c0c2c8124190102003074480e800c044403810713031034011a030740103000c543c0b49400900707064142e00301c204c12110089400e014000031400b140c0c11002c1e91540300e0b0480c0034410141e8070140040d403103106090a049050000e01c0c140e00d42150380c14000200b056070f0b104c0700d0b203800300001c110134030002400602c20b5659035110280718000350420703101142c4003200c0700c032040c404c8e280c0182070300d1191088031441402c00b8a046002c9000c0c4002034611604050484104c0c483c50415000034011039100e5604c2c4801c0038074500c141444e220032a0502000440d1040c01030002820310303001c4030b04588003210744988508043c18005050b11032204000c141c03400400e0f0002d00410852540c512030007260b100c0030114810342440750291241203030030b40c0c000c0300180014821031070541010706049402800000e0300e4580b440c64501203d010a800307444682c800703c2c081000102c00900741c0e51042041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 269027392 1250 269026142 269026151
    0xa020403050f060106050307110c0a030c0f080705061215040603050303241309031107061206060e0d02041802040203090606030c030712030f120c0e01031b1704061104180f 75
    0xb890003081400090f140c00b0800480c0c03c02442d6270f100800c01841042c0004006a811a0b941d1400014400031486481218008071030300003290312000c036112080362405400e2074a4030700d0100003104811070003000250845880c0104e60700c10707200e500c580805544140d00031907482c14050100f0319081400071800c940825084560070081d02d034544194898035851502103003d020740d11b0140c4000d420404074500f50310400ea00050403541c092000281200281810840d00303484100844070003031103d03402034010010000741001820658880c40c407240000150303c0350384950340e00240681c0c0c0305072642805540908113200c980c0c5024000404064000c40081081f07510700008489400500403025050040a21911000d54014481442207515501c810003092000100c007a00510800e038034180028070f4107a600040344200d1150010040d11529604044981100a640a904000e100300d462a841c1c446c03242580f41190f02510103806e14a003800f2282d10760700c11503000c80e0000307102c005015040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 269028642 1250 269027392 269027399
    0x509011107080315060a031a0609011d060c0f010207021c0b0103060b0409020604063b09150409081c060308040b070f0209090c1e0913060f050a020403050f0601 70
    0xc1004949000e6401540c490301e80d6281c81035903e02c0c080c40d5560541202002401c00541c07981503000006c1c5040324450b07408444000703c28013846000300289140483d131565030313121441604036082c081d401402001d00e0326190540115074140889000c40802607034000c2009411468003c03190007000071107040c01000d100071030711200d0b4100e01c1840007410080d941c900c04911502c0f10f07084080041c0c0c000e4851070303850f55a14002454035a0070305502280041d05990340c0700c12a00085401d4800c020300381200c401102d59403c000d2940000350800c01c07804010414540c0c9a10b130350040000407405803104c01d40711040ca9600b003000502ca4510450745901d0400d0a1000641da2001e070b03401d882c010071400f03460381520714200c0310600d0302c1d42002c1d5010428104003e00c52000040c00c4180900076100f4194400b5a49000300148030250540c0b41c0c4269101c00284008900305156000d003800781201007009401c5820107011281c0a03a0b054241680000c0c0130b00c103201d010466100001540401401d1703030340c903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 269029892 1250 269028642 269028671
    0x703200304150e0405060102070303080702121207020114060a050f0109032a06020304060c060c11100b1e090c03090a06020313030311070f1b081c110d0c0201080c041e0801050901 78
    0x1103032b00004050042801c0800c1c0b040b0f2082050100000140181d560340b020f100e0303d1407901c0003040700c18200660804076003143d074001d5a141d4038050540504505203042c00d240400c1404440e1030240c0341080380d140340010100702c8400b400c425252151202c0c0c040b415011358021640b40194100c0e10035944204000c104490b401024240c003580c100500286044014000321510000c012621207584203810002400408503480885000e604403402d2030062407045100500442c001c3c00203600c108198000784c522810203004503403201c6900f0580d9801c1d40030f5501c01080b0307041a14401100c080c042c5c921800c03d0b4040c4140421901520300c243c0c10045107039113002e00e0810b00180109202d1403040b251204010410050010f07026407000e441c64200c80c10051841700040088100c00a8613900304006603e8000c96040c104070096601d2205448198005490b001c0018000075800d410400000811148888081720b2224a00c541045036514140d1103500391034000c0c10306413032a450032007010f40300c40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 269031142 1250 269029892 269029903
    0x1b0305060a1206051302040c0e1306030c09020304050f061311010c0b0601030902030c0310050406060e07020d0c08040314031c0203010f050d02180c120f06060703200304150e0405060102 81
    0x243d210074041101e030303903050382d2107038001041030029040342c2401036180400c4e0700020b815030241029a0b12100008040c14030b00141c8240d4400075186240c074a10910070f218140d002941d120b40282c0803200511840c110651810104841e14403003a02541c000b0030170840003484c4150300800910300030040000700d0311905113503a4054809414550784410403421034a051014080c0010000c0c15900003c8200d82c031007001e4202101c1c12a0824544103000c107510994119041c00350541d6401402d0100981d90103a031801844c0780c0a0b0703141030003888000009406412000b210501d1038000c0c686400111180319030f004003808070301c1212401800188419a40a20380004890048420142e0200d080c001b08002c4541c01618040f10f500746020000c2c426040402002080c13464000014186d4510345121042d800c142d80035030b40640c04010240c046881000c00403603800000e0140145401e006581c907145501c40c4c0e0040c0030341400c16445003000e58000d0f05032100c0400686e4180071754682800001d4494 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 269032392 1250 269031142 269031179
    0x160c09050901050f240a080106080c120304030f060609020301180e010b01020606013905100c0e0906130c020606040638040b0d061503020723101b0305060a 68
    0x11100e5000711400c039495a007821620710002d000f51b0021515441414044c008074050034629100f20210a401030402d8109012105140c4015500345411641c3e0031401f04134001050764403540310f10011660400f0381c8010350007041c1c91a03000070507150240b0120f041d0369111121180d542d141010544591b6000304003242d006500340382c00b008141d00c00f040701100c0750034207490742e021039510003109000c583d1078495800321a000340700303c0301c00301d8244561a0a031086120b40380006128400402941d0812800564205500412108160503080500340485a10850100c0180e01980c280f01d15401d01c0d201c1c00014012200402111a00c0801b4814030a40a240d810749c0350b50b641c0071a041e012500101b030b03c01a00d2003036002992600c030044038101030891806401401883e204100f52910300a100b10764040740e05c40e60351000c01c0c2c44120300700c0b01600a85c140d42c04601542c0b071455034440701885488a10460401810100001c26400038211803004010134000c0550010501c011940c022001001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 269033642 1250 269032392 269032411
    0xb130c0302010e0d0b010312090b0f0a030207060b31090f110402040305060403050309100c0c150b0d08030108060106050a020613050a0b0406051b0a050403030e0303160c09050901050f 80
    0xc0c24000400300d61301000800c4003802c001d4041c0004403c01145a00c02012580240e072140b105948940c111440e9200741010031040c040100191228140250007814129020310400240c440001c00882c00d80c0c020040300b1a8159144090b48091a0400102e2080043c1804080003818a0b5a8032400103241203003000d040f10780c001c040ca9030720750346640446018590020664440741420300d0007810035041a240292980540030011036001c0e9544109808400c0c140d03506030008165449000031800380070071a00c841d40d1100803011440d21582c040c803004c0c07481500c40c60b80e00d600d000c4d0b14504184e0181c0140080040412206500300e17400100c09411540c0b403011052440041d240884ca00030b01791100800c08040802000700703008082d8030051040021020310340c054400c2d484001001d100b03c401860104070b041c401400440d100e41100984001c2c0030301220302d0081141e1200b90780112101003114506e9001c9400d2010708000e004460b00001c6620080c829800c10300140c240c00780c0001c020000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 269034892 1250 269033642 269033657
    0x11040519030512070302010c02160b07020429130c050909101a0306030c0901080616090801050901062301120b0d14100c1b0303360b130c030201 63
    0x150346100031404801940c2c8001240d800c1d104880c84030342c03960001507058005d5480c0441c0026224008600b440150a0428035402a14100001c904003a08864420398009035a83c04503501c40d04640881115080340b544100c04020b07503042000402581c443c01c802a403810b00245080c01038002c000d4603415081210f0704002070b0b030b078400400b0031070040764007140c00c1140c0da003001d50051490070001c5001c0d420039000d031183c54031aa070522880761028800e08070b450340a440024007a600140081c41201c40b9403a042c00710950b01d4800740d081d140b0039507107c0d000c0c0e55200c20402c030b107503804088528100c612030f4401c1c0f001d480310b900192001e008251100b9030305841d8102a00f0582e00c207800510320681c003a280310702a42c0210b00c0c65550781c540c0f480b0903261305e140c820303d9111280558528000b80140301c900524071402541c08078081c1036940c40c8242009118100d00316500d14101019200d8080085800e41c43d02c803a0811000c20344014003203505a09104561b040850407800b000e00c182e070380a003802e41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 269036142 1250 269034892 269034919
    0x31c0c020d0f0c06031b0f050912070f1e06020c010e04090f030816051804020a0306080712030207270905030d09050f061e0123060a0503060108070201110405 69
    0x10000c0a10801c020280c0c10310300a00c804000081400c1d0054a480c0e0f03804004014840203404180d02a495100001c103840701c00520b98244510014424101d015194419441982d0b01c417a00d0844590040d44004405a5051019400c1d9000b1780c074524170080400c0a0311841c0640181d260340f51340c1031082c100322030100f150049031560380040781d02c0d540c42490355044803034504008002030410f590301600200c46044954040b0700c50002d86248599103017900e041d04820360100802940601c0c03220080c540c8801e40092101024400f280081c0240000ca034601169860001c0c185000760301300600e0b6020250410348055810710703960380c03210800701e0700042c80d4960f800c4c070741c1c03450040b40075480d400303400c2c0308802d4204180030170b0003044421500104c4803e51603078500d4007101c442c00c0c201c5408190f64403004104140d40400204050801440e045010560120104072598440d20400307000c00c01c00400e204241d41d02250700c56010950784020000301c4403e01360040c80f0310940c81840d11817200c0780350a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 269037392 1250 269036142 269036149
    0x5010c091d0406091401050a0c050c0c0418060203010320031609092406050405150d020607031b03050301050906090c3405010501030302121c02072f030c031c0c02 71
    0xb0b002c40ca801c00705c07030380300301c4c0e1100c100034040c0400300c031446416410007403403070780781401003081e50100c000d2a1301602c50f50320341c082404010f01c18440b51094084001820b50081140c91009501071401003110a448841e0304808000b03c0310171994040c041d074070002d10b880004090f0b8550700e0640345004404603214207282005041000d1403a041ca50b000c0d13030140c0c055425602c0342d01c042e0480741d042d501440190f40340001c0c100b20746140a00d00703070010420103034180103141503001824000d100342418081c0c3c400c84140f05001111404c0110013003040000103000d07604d020078006500c00f13000c443e14210b9240890031181c890156500c11b0054481c6407000c180414044000341a00c115034400548884242c1c1c00c1140c081d050030302c401e4008d40100c800b08624004640308072030100014004156580c0700620180c00207501c03515080e603020440f0f5a0340244020240744005005d402804040d031500c1c1c10104140c00e010305002d04520030b620408034084a900070408043c40e8454174203009504146a0021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 269038642 1250 269037392 269037401
    0x201080a0b03070e060111010e0c1002070e0109091505040f0803070c240605060a02030a140403060926090d11180a0c0801050d020609040c05190c05010c091d0406 71
    0x8042d8140502c000c00b0a807070841a103080d200300c00907620620215240c0c14014229202c43d013062181d900203204a1500f410000c88070049000d4520454070110341c0d40340c8080d4000fa080c2c100e00d00c0d140e1a4007159092180158020f00c50200c00c4404002c070741450742d52082c840300b0b8404000c1014ad000300000365a2401811500384098215000d00c1c030300a406004a10007084200c07017049218503010003c00c0300e00b00602a00c01c04511600250310f0030030350807000d940d2441c85050910020f44100f0000c030000e080d074020201e10900c6000c040040740d190500007444041a40c0b50102c62103420300400703910340d5070f1042a084080d00505400700700704003480440c19042c0c0746c5038010080280c02090264045080e40611418002903072080d074680d0b2a001004911010001d010354400c40a1040303e410b0b2500340e00c842d02070445400c1049c94020352051011030201c3e200600b00114201c144c150003408800e0046c00350b40c00760340c0340c11130216062401200500d42060600411140420700080401000d940f1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 269039892 1250 269038642 269038661
    0x10e0601110c061c150b0f0711040f02070b06100e0607080405040c08040b060a120b06040921030501050a050918010f06030b011701060605040b0c071505070c0e0f040201080a 76
    0xd541e8407400304001c02581c070010011303800c1e8945400c500c028880d5400c1a904140c074406400c0c00c0c9007210200d18207030780340c003c03e0040e60b1880314094641c4455845115600e00201400000740e22502c0c10b080260b50f11304d008200c940650300700708100901c1540400130043e8810215156625421a410544840c2c0201d4012580080c03a003880c6a00302c58120f002c00d0300c114030030760502c006551114140302e078505040c031401c40300b181084221000514a01800d42c2d0017070b400b901c005100c0342c694503002280650700c0c030300302620340d00c1d12001030840380c0c0b502409025000640e1b10314151403800c40400c40c1080001c003451000788003400400586e542c207400800d080c6040aa060000640328101548645020b00c01c94002c4071004620071200401801a5022a8041d403a410700340351514165000a5205103600325072801125000b2a14006200c01c0c4e6407000303056520280c8a0320399141c1a04084a540c10001d005011130040000e103040e4803440903070040d8203107003003291900c8203c0c0b8072024220341030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 269041142 1250 269039892 269039899
    0xf09090510020327010b0607061d100e0708010e12030c04090f0b04060905090a030e01020705060d200f0a0507140d03050f0c07030905060f190c1a010e0601110c 70
    0x14051814400f02c4501c0280e8044c0019080d04000710000900b211201307007055030002c1d400c0c0030340000300307009620469082b024210358401801d9000095410305410720056002a60b50346500c11420504005500107450b50200800c4000111000c140d55042903894206181d0340002c00210315000303c1c800d6a000b4080355005101c00c0401080e02c6001e80390b0222a140103a11744503000a0400250040e6805aa80e001c06042d0481c4961012100d084840300442d040d4828a400040c4603206c00c8020400114264400694817008154004624942a202d8085c41ca0709005042d58620301034100c1d12015034900305955606c24506e0320280100012189840302e01905070b00d5420540c05410607480760140680d04001c1d55952041d24030180519403024002601c02e1100344040c0c14004000e00f04964a40100b90410001c2c101d4481441091a4484001030384008180c01300320380c860440d6110311071041d840784150306003c0c01c9680d180c030040c00c4074100304034140c0011022006100d4903461005c0075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 269042392 1250 269041142 269041147
    0xc03021303080c0d2a0303020f1308070e060a170703060204030f03080705160f0f1e0507050603040b0c0a17070c03120c02060c0a030623100305010f0909051002 70
    0x24107003075046070014808001680580200000300c548200e0054044c800624000c40741c114000a17984800d1124150840625608103d42c902d54905032016046600000c5482000c613401d290056042c65040c0d030040d0703030301803096091081c66511840c0e500d05854030702510310308e00100002002d02d05003144e44060700441c80046c011080c482c80386601c0d500c40b030181e1a24101340e151507008035001d10402424001c0713884174030111130004030b040125602c0b0358040c0d410101e600308180c90b012001ca00030401d980c0041c010820940c100042405048000c0000702d0b5554254038064460603542400182850301c0c11310000ba040842d18003802c2252252001c100030070300540381c01880a0702424008006a01260b003116180301e074020389018115101480d9805040c075030711440740c4900150000c001500034141ca4400110f209606952040780e50410640c2c400c5010b00d030b84040c400c601c0c1e8601c41420805003803400502140307606000e200700302c401800c00002c000300e85081040c20002116400e6103110b000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 269043642 1250 269042392 269042399
    0x12021c02010516050c0d1a06030601031e02060706020c07030203150606090d140a03021e010204030507030605190509010c0305070c0b1807030b0108010c140412030e12150f0a1e0c030213 81
    0xc98000107e100c0ca40c10604201d6100c0f6401c1640d01c1800b444001c1c0540e501003c0d40e040030402844600203144090312982c00c00c0d000b65240416600481c0040490b5404504100154641082400703000700d8003000350358281c01d0010214129106200c2c50340c0c0551030310350700702003003110010030b02100402c86c0054448545003854000e46482c0402030180301c1d072111190b01c0e008900103108403800c895003e002840c21381e207035070343d003102502d8010a9a51a082d9820940b512080c185c01107a03c6910b2780000010b0450010801508442c0d001d0902d1041103551208040012a4a40d803550070062009503a9030081c0681c00d59464807049400003043d03d41d01d840001070103103054200b0504000309071254400b0000c06441300d640d6010b58825031516800c84868000801c3c010740c482000b80c2009050b4003500d40001c40c00d0352504068600c01c0400c0b079001c0d0100102e044035400c000303401c0034601070140010340c2e440320103100e2811120310750f00400e1b43c1c9446258101d4000d038102c030351860030108200600e80e603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 269044892 1250 269043642 269043653
    0x3050307060605121f0c0903081b0607050306100804111003140f090d03021c020307050a20030a200601060c0302070b09060318010e0712021c02010516050c0d 69
    0xc16118560044540c481c455001a4000c02c074008098420000c5042e84810705070800e0151000440c58030070711101e58404404248040c00a210015081c88000b80c142c5d20094640d107041c070020301c1c1c0cd081000500500c00c0301e640e1800091403e42c694600072401d48c03120b0a209460f0180307040f480340e10440c4814199643e030740503003107107880d030a45c92010790380355895204601c1048000c0324100b52036040070f07420121660080d40500008080340380032000310804031054100300e03402030311418040390001c220402e80b980d0008203a0103ca407680200744104a083d1100e0b036690203a59546820300c81c04180e680d2415080030340202c200040d42040f120296514000901a000c00090a40050164200c04a202e0301c18508441c66400302401d90381c0b841d034401d14100d4105070105442d190b07a549030032451f40c0340d560411040300649505084400c48500501c104554220001508008258071420380f0700943e800505441040c1a031100307010100030719280080c10709901c000c0d0306071b00400120701d1205020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 269046142 1250 269044892 269044901
    0x905130f022b050c09010807021c03050108100c0e0609120d03140c03060306060607061508030c07050102010b030604020d0f050118020109091407030c020106090207081e03040f0b100305030706 84
    0x484011030b14401ea00c091403090240c81040310a001040c80800c0490381c01d5101d2104d083e03105d0020b20664519010191904041040c00c02030000080d44840c01800304501c2880808007418913a1000c000f50507010001030500a443c003101c1e8031030321010840c0350081c0c42d995120b0345c0d0b200000042d60614101c01c44050300030002250a540329042920000320720f0610b40d000c4a008400040c0200042e6039502c08001555200750700494010780c4500d6203400104034041c118011381840c20140d5105c0c100f5220081c508000c9074030482c11a03050880d4200162004545550050f8040d1802e05030a070007070501044c0280c22040c028619031900c5905207003035842040c2e40c0303100f41c400d81c0d030245c01a540b0358000c001c1d1405411160783c0c00701200041f0702c102d4001e500c15007640360203000103c3c40c183c0d02d01866080b82c0205104ae00c0e224000200103001400740c83c40c2c9030001c10b00d09440307402e6003841d0321784001c24200c5140050000c500c10011078403012405808500959020088030360b5920320b40b82c000e0141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 269047392 1250 269046142 269046187
    0x1080c0c03042408240d020f030610030210050a080f071b12030614130f06120c0509100e011224021b07150302130f12110a03030905130f02 61
    0x603440340100d03991a070050900d1104070a2002c4036044405c50200b00002c80040c00000c903844280180b00c5401c64031305000e510701ca101015040f240c114a503005000c0494000c0c5070b0b20741040700070008051120f8101c4600e64014074810280a225510b007501034448564281d15000f0842480300e0360801c114a06101c1d1940e141d0b1b0f40e6042c41381554a445007282d0340c0c800c00c051035201004a220503417030060b951101c140c1032a0054003080c400d40d1081d400600b49801b1009071008801d5110034400d0381000311b50f058008001c4c0d0344034101c40c0c3c42c04002c40c2480343d06000d08030b8010480701c1510180080b0110360101031100310803c2c10700d4207588804030001d41c040414504401700f40e400282904030042241e80445513001440c11105031065001c40084d070092400011518409801080381c00f00c0900b144003800302c10561400c40c4000c1d04242821a0000369464480d045840c01840040d40c0005030800b255010f88040e00144a11401d00740030745580b10b032740013915202040020b02e0b01100385214841 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 269048642 1250 269047392 269047397
    0x1050408030a0608010b0619230d0506030a031407080408071211030d0f0c06020708030f0910110f0d0e0f0102130821032d0f0606070201080c0c030424 66
    0x81e1340c03520070310b00ba0b80301d0001059100c501032100c0900140d90800d86a82908203142252034204111081103a07221900310700611200046600514181540304041e00b04508500602c3e18040030354005107071140e4003444403240342020605a0421034001c0695015000b11400d8450030354540f001c2400251a54030103a490b190703095811300700340c103000c9003144c0b50b01c406035503601e840c807a042010707510440503180483d05c1503400c11810004c110601c002c1c40c01051a03030200030903030800d07802c41490443c8003e81c258a4074038001e00002c40886441c1142e100c5c00c0c04510f07041c0c403101c4946803400104a00140c600881c0540050440c03810010340c020700c940c400d0380c1d5103150107030340315414596a5400280c010f40150301e4003042006c45020400515445011546c4c1c0654134910751090b280070450b058140201804400203220b02c03031680900c006c1d44880143d8240c2d003800e00d580c00007010440e01070b11201650000203440e003441b01060040303601408441403140407048204030040000000403010100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 269049892 1250 269048642 269048651
    0x504031b03080a02030c210f0907141504080f06240a030f020d080f041802090d0b10080a08070c0503070305070b09062134110f01050408030a 62
    0x8040101001403804941c1665811541c0c1d500d0b155040000e61000e42076181424040c04103800401c80360207000c3d0300d00c020407040c5205003031071042040c00d04806004501503402504042c0000c02c070042204c0340c402d100720b860308072a43c1010040040c07482542c101201c01d0098140507600c00d1300000b80c240c065190b91885809409040c15010a080e103501100c9600c428601302c1000820050030b200c034250b074002000e00c900f40d8507956039a005030b4081284c056014001140400c401900b103c11014090043d15066192030a00300c0054400041203000901401d112008038500c0c1070707020108009004420100ca040b444036080000c6560004401280c100e0041200811030307013004603011044a40c0030f0010081182004c0503e8141d41003004001d41010092210540749400c14083c60129000d40b0409402c03804c044c60385042c0d42c181e001051515800c0c2d08c0e602450004180408000781e00070f80b8060103014002904981007014154040c45598244810711003400f003c2001140240600c510802 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 269051142 1250 269049892 269049917
    0xf0301061e110703260a0c0311030405010c031d09150901170616020c1c05010f06051302070302030906070303020405011b12050901210b03010b06040302060d0e031c050403 75
    0x45041100c4012080c80fa04001070400000d80c0101d02400c1c014240c4401c1800c03551098041c95440d00551004400590a45280814150411030a1240c09404005540707090704080000e000040b200c00b0043c00c11010508002d40556080a1300300f50070401045482c150400d507123981c014a42d81404a4030403a5130100003d10850621480f1414040140203003104d43e80e22021102c00a040d18000c0d401e501810900707412681d40e00b810b200000c2c0b4003140d0721505450f2410f10a0849032a51000a125482c0c0441031115a8610080e4a00050a030b240960b03248141d1070200e04500943c1020f0341c10600200c0c03914101a0990003500a91b042030b030b505025500c5502490901486005002c5c261403040c2080054441c891710003005c0403103041c140b04c448842011a0f0700c820b03100101802d202c45549200b4002145000e0240d204130035401c80d140703800c02d411030300002d40e40d100700e10f035085003107554962900954a0910a41d0325040e030452040404e80303046610040904011a0120002100c9503900c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 269052392 1250 269051142 269051147
    0x7030c140301030b07140d06030b040b24100504030204020414190b0703030b010e130903020609010b01090932040506010e15090c0c1623030a06110f0301061e 69
    0x103030704903900200d0305a2103403185d10041c0e45004c400da0010455100810220501c0b01d102e001e0350006510070320b0203e886240a0178071001c015005481074150840c031045400002420383c502c8255600e00311502c400c0c0005044040c1d4442c03040c0d9000a40050000c00c0c0007a16145011141e0726002c001e485090403074040000e040c0b07441445024200c12802c007808030301c01113407090b40611100c5106040c034983c41200d400014641c0140444100c0c981d58070b0303030000010998144406a003200b034141c001d00c00c9a180c03c0c006007030442140544880155201c1c001c100d01507040e13039145240081c0c0a60b440c031000403109200c208400480701910720344642000003582c5011000c003980b20f140b2441d604807400c262a800c0200e20407024018400041003070154030b00405d010300007500101845c0001c00701d860f103840030702482407403060307020000c0050f003099001141e1804207496410640c4002e0003c0ca4201da40c1c2618200c0c0664041c4151104001c400818540d0700523242c52004543c40c20205080d21805004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 269053642 1250 269052392 269052397
    0x70b0c0f030c100504050304091a03010c02120a030e01060e0405030a0810061215031704031e0c03083105040f051b0912030d090213060e0c18040507030c14 68
    0x1a80742d0b0b4859801d0101001c1c0c80c0d480b081d000b600c1134050742e140a5030b0b0201401600e40081510300001180c01959480c1c1c80c0910800c140c19560b4000340503129080300c4002410701820041c5010f0640751001406113502c00e500c07440152028070b080c5007603402c20341010b40d42e9400c02e6a441021680f90000300e0211085040044211842039440b00c4110009407002409000245041d10080222880c08800100a56a00001905155020341e29940385041001e2081300c0008100740c0d0300058020100441c0c1440c00c100142c035000382455070340344081d599016a01d1406503040c111002ea2004400e414031080c2d08072000c454040b00c05010a110907403100e001c1391030a84092403500c1d1000c510616160141000e000e1220008041501e11140410018250340c040c8080c40708403990f600f100720451408012400000b424404204070090400715107420a10016012341011007021540c0041d4400d010010b0481c043c2c09481440142080c1e00c001d0068180748903410041080182600c0e03038094440103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 269054892 1250 269053642 269053657
    0x40309050a08070506040b07061401060305061c0503030a051e0a02030f07020c010e040b0303040e01080a061b0207062a0506060f0d02010903060b0609030f0f010f180b0601020708070b0c0f03 83
    0x5041c07609142c0b000d07030840741d40460006c5819a0302cad0040b0b1203030380d111048554001e14207034502107941d2400500300074110040b21210703160901c032400e0340b10114100000b0303a42d226506410010381e40d120101525a60203140102d0100040d40c1001c018292420380c000d10300815030401700d140f40b61264203059840c0c0c10408881d40c002015100f001031b5924094020000307e00300901681c1c0761170346034003c91a03028001d0b0008040c1c3d80c881c002c44c004110461091600c10100d00001510480c00800e0094a03800540318400806c90400c040f800480030700100048031896096903507405660518015880d1841156080d01c100c0300c001e01d01d8a01d040035244580000e034142d45009042e07040d5030f500c5008040403615241c0000c01480308042948080007035901d070141e280d0090448034100405076003554103070790b280c903042420700d801062012004c2c1742c204003c5a10094602903a590480100e1400a42d0761000b030711072103440d4002958100c0320006000b0183c18506841003503603030b144c405640388580007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 269056142 1250 269054892 269054899
    0x3080901090515120a0609020403050a050f060103020a090e120315010e03030c100510081f0c1b030507050c030601121106030907060809010b0301111b010b09180c0306040309050a080705 81
    0x15604003046451344581d440315a24000180f4192544409000c03604990001c60b4254080d00004088c01020420b840d00408400001c0c6050341c1903038085005140300348a215056500c1d01c040700315800c1d00f84020203105108c0b4558a8607440c0c215810080091a00d02a6020422006102804d8240441240ca040d10140300820b840307518800c40710002d040003400e0f4581e0501800000c1000c0c0c40070320400ca24900001e1078a065140c10031450801c0381c40c0d0711052400c0c080c4802d0340350030801d8000072403904580c0600b0095124055070806d40d00348410481c0350b907450300900c03002040c600b40350515007001a00034110310040640c0c1c4002d01140c0c0c4007e0701c0d601102d0340014801c01c54507225502c40350b4440428000412515078034000709080d01c85110107019008030110300c030007000b403004250075140040d4500034004860120042580100068814514941172407500c4a0b10315041000825040002d011180300d40f9180c10020010a128002c951003190070000c00684020005000001d482000307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 269057392 1250 269056142 269056147
    0x912051c0501230d051c021005130b090109060e06011809081801050d06090b010e01020c0d080a140d0603120503010305151b0a0206060319080906071103060103080901090515 76
    0x2c4407240c2182c4402104194410380c44032800b00010000d1046d083e80b0509500740d842d904444401c0a17003132865160f00c281302c0d0391401c0d0800a040c0c03c580282003442c2e8000024403403a03114010392501500078441c010305400d00f0003076100c800c5207002540c3d40c1200c40008206084041c0e2452080a03030f2804ea20251900c3c0c07090141708010300554100740b404480c14109549000107032220700741640c510f03921015805580302102c05403540c101820903d903072400d10290042c9410035001501c4d036142000c01401c0140041514581a802150f0380d000c04001c034607500f0345400e1001300480c0946801d01040b42d40300c40c3d049d502550217000d681a24162613102c4d0181030942080c094101c90703160000c1a080144600151085011b10113034000c0079045503e9028201d54504482810f28000d10020482c0c8030191400d0f10b00c0110341c00b841651203110301161400e07555010340c00c02c0026003040305051581401854000070402c1106001008505d0081c0c9555920580d51010414045203080003e04100c508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 269058642 1250 269057392 269057429
    0x60c021503060a08100b190b030a0c0509060d06050a170a0b0402030c04050711070806010b0a08060301020c06070c0b060603010f050409031e050406032a0c03030912051c0501 76
    0xa40e0040c50740180d000e001102d00301e0741d43c070440380707420280b1201c2e1601c0d50307961000d044641040701007202c60140300f03072503034a0031850b05840b880c42c1d100007072451145035910603a1040c0c40d4404c00854625030402420b640d1221741101c0e03803600409051103110310407482c900000030704451000110100c050140013518003020f568a9240103101d00a03c2240c1c1801494448034050361030384a1140505c1459132440980b0f60080d200c146040b82c190003200550380803900401450700074008607000f4184038035111449844a82c0032a0290164a584010600070f030020400c44542c000d62003078a50b8011090b6401c641c0b03c1c541440b420307200a02406000140d600002c0c889405e007600a20200c500c80d00d0300408c150722400380034030254403645200d00021000201080490b034907008802d01c041398214090180c0c0d036809040300460340d00d10810f00510020700e40b0f02040c18080d60104a0403600070303035040406203500c10700a00b00e601a00b074510b120030300b20251000300c00c168441c0034141c0381c40040002e01d2419 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 269059892 1250 269058642 269058679
    0x5030c1e0105090c010521010e0f180303131b0303030506100e010e010309031206060504060e0405010509070e0a030b09010c11010209210c0303160c0806040f0b040c2d060c02 76
    0x2c9151981c0340c0907940c854848104000b482c7d0b80200380d492064544da04254105040d41a805002004100c03440c424507584000c0120481c1d41140064100e801004000e14001c81415070101c0e0f20300c2007802840c4000280342e0160400c41c410881125014007610004209a9101600704000307400100945820f80c140c0d40260320000466000303081601c5280b10310780c450015a20f480d0000400164045010043c50340c0205d0070038840304048401744420340c1442d0124080701401080c840c02c0042e40032949080c0d0301c40202440103103070094503141c018580500501e000e081e21249000000b5021450005402d0061082d0303131801c64018090b90749035449480108501c00d00400614682c02a84d10041c0c0079641000140503404552000070f0303c0240d51300709814510041d61040ca0a504035408101c0001c100103184004070fa440010203101d5151420410034510541c0c00000c543c08001c180f04e024191344c000d044410aa010340c54040454a03045d0480d049015160025044424540060261403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 269061142 1250 269059892 269059897
    0x513030c060f06030807050a170403080306041109030706030e1603031d03100609060f0503030a051e0d050c070506160e0402070204110708030114100507030f0c05030c1e0105090c0105 80
    0xc2c0d0740002054690b00e0f5203138240f1641c0690f40881d401d074028041d910802540854a8006200c1140c1d06800c1c103240d501da44c007251000521075841159101280044000d15030107841d029507000c0d0480c0c40c400e4441c030000d001090205d45082d010f2040f1f240c0c140242e00c14004542c183c03541079441e04402c8a5070302d0300c070b0841c0b48172a02c1b207540340c000d04d0000d40d007031b03181403141100a01002c0001314016180111501100701e01d904554000c1c1c000b045081d244036002030403038402400150550f0ba9505d610001c4408a0080115000405082009011035413488201030700c83c0703138001c1c4261100354a0b10801c460070384028070103400104580003d580307101e01d050780c0508103d500140000c5000000792001d0001d0f0750140100b145c0085003c4014030901d01c80d150780412078107049d901075118001004019100e400b03401001800c10a11b40022585d0b5481544140d496030b0780030003106d0f2034441c0410301c5501c81401c03045160080216084d07105280130140100e40c003a19031032000c0e00402c2800401110f069 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 269062392 1250 269061142 269061161
    0x1050d11040e0a0b0a1a24030c1606020702040f0c09140a08150412030903120b061e03150a0f06030e070b0a0509040e0c01140c0123040302010513030c06 67
    0x1d008103c1401e02040724012064407511a002e800582a1101240111a1005501c00030700030300c56107203000460340740d2000c90070311f110844103140c1d100d5403042503c45040c0314480c0f0107030070003041c00415030810035250040c0c0032862007203a0501c0410303c2c6440403c00c4400b090b0016000404c101c034200710340c0c08205294442141d000e0076409509891304a03081c9003030135100000c150180c101c402c00040c030a03096a2031100304805d141c240050750803910020160a415035100c26255581e543d0543c03907540d24401c40b0004800b19140141844801c2c4140845410481c0c0020703a1140c89003c8828514220003c1419600c207079594540c514202181180180550107401035240300f8800040703180c20f40003020303019520b041c0d03540581d41c000807003d02054801c842e012500036840000d018015a8200400a080d24100c08071551900c1000300c01a000d0300b000c11000e405421141c0c42c0035604130640d810944180c0c003a0b0001d001e1a203e21103100d04ca090789440150002e901d403120700700018515017105011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 269063642 1250 269062392 269062421
    0xa0c0509041a1513142d0f06040e0a09020409020d050a2906040f0f060321140a050c0c060d050a060501020705030d05070c0906080303010e01050d1104 66
    0x144a61034000c0741c11500780709071a484190308051259a0b500d446030440d0303610030748190524200054594500400300c05409103040c0000504030100320b0351104c900414035542280442d09000204c1c4025064450b8450403240c000e8440d0084811030b81840c1c0120703001c80c2d00600065080c3d0740c4a80c01307030008050450040303a1294440304c2c1a80581e803035405180010b8040d0010b40310065452030110941c0040e2a40307010b05c2c07245a0041c1c108140e0094296034810010f88010481c048100858002810044560216a450100c0120520654031584c1c1c05414030700310a040c44100c07400040e00d1240852039240e40e5403404102c48064103101e40c002d0303c2c0703144440b402c07600c154400c2c00c0000e8103900450210700b0011354803410010740701e0850040800905003030001d4049141440e0205e5160342d8440e50080901c03c0014101080011065071040207050703e1404015090704d8640203504d9600032703c82c00b0300c0b4a1031900041f590b89003400140c05c2641e0b002e10100440e001620510000d02840c5884004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 269064748 1106 269063642 269063647
    0xd05060d020a12020d061109010315080304170f060406050f1311041104090501080d090602190213021e090307060804120e0d06090503030f06010509090a0c05 69
    0x41e10300b180e450a190f03901038004a11490031415000300396902d0580b2403140c00010101400118809030303000d206a44800c00b0412400c0c80b103015100c141d4004200422840003141d405e410300005003410b9078047c0301c02e07909490074040125000c0e0b400c162607c007003091450000504a601100c06440008900025183c40111504a03c004c40c05103942d074042c21042440f42c0300b56401000d18000910080da11094001c0d2119080c441c5000880ea07030380c401140860011440c851001c50000319081c06407400c0d0204150300e28a482501d203038942c00c01035503100210000120340521030000007907981e02d81200c01d0500e465001e5001000b0000900e052100080010420600d5500280b900340c58901c41040002c0111190000c0182210301e00171406c0c0803c04040080c41c45602030224000c04c030741d5100010746451180c0316846a1003c2d688002a01c9544940d02000800d100c41c80c0160 = true := by decide +kernel

theorem cover : BRFrame.Cov 268884892 269064748 := by
  have h0 := BRFrame.cov_init 268884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 268884892 ≤ n) (h2 : n < 269064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
