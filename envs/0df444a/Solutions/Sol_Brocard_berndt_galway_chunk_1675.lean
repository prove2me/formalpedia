-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1675
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:10:44.654456+00:00
-- url     : https://prove2.me/submissions/7e3716dc-1c09-4649-bd03-e187ee00f5ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 301079136 ≤ n < 301258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 301080386 1250 301079136 301079153
    0x20d06090b190c36090905190309030f020f06070b0406050603010b0a1415070c151713060b06040f18020a08010b070c03060c030c0f020106060c110f0409 67
    0x10b82a000311141901000b140c1410454000b49000c001141c0c0944400d0f40300342d00308008020800c12070340d41c860403140300005220706003260351040114548550707162003000002d20a0741c400003090f9020045090700c5072030080c0092100e2101030881c50038000d1010554844010000c7c0b4440c1c05405103070b544c2c49030324004400d50411501542c0d500d2600c0f01060340c80c46d06009104000754000c04413000603042c41040c00f20281c52071001540009082c1e0040e079051290005400240e0040031403c20562802000000000302c541000040060340b2000481460041c81402d40104000c59420794180847c40c219004202a4107095404180070500088907804c2e820050142c1f81c540180e190f1424100c0d00c0a000c1e40030305e40050010a003108014014051048040d00741c00b80141000c844d1243c0c0c1c3d0f1201021035820340005000603032910f1803800301c50b4110126950100080c030007003290030300d0840c005010501c81100144030003120a00031096917940c48080c3d0f260b10f001401005914040c0c50000d04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 301081636 1250 301080386 301080391
    0x3070e01020606091003080306040212070504031704050a03110a030804320a030803090a060219020d0f05160204140106050405120d080406050702100603032003090f0409020d06090b 79
    0x40c480c41000940904020043c5070262070b8580c03d2100d05c904641ea1013100e50401009280c115600f4428002a90301460309140656026240c450340c890841c20070000f2140c0405030381100c280208402c11441d115011504212504480d00a0a0b0031f100400900e003909181d10180124001040100b9101c0c0f80c0008586219000710204003145540e034504103444260180b5258402111907042002c901a0381c021603005146c1c3c000d8418588055540000b240c000d103c40d024945030087d500003090341c0400c4410005002424406100600200010f1252050400c5000c01c040c6176a843c0c0215220b03600324104603141d00c040d050b542e41c0c41d890010700a81280c801c00b44034140015400c0b070101c030045110302e60304820303036100c1c42e02c0d6480b034441501812014100c002107100c3d40090307074000c0e03085c3e01c10300010750b1003a5a00d04800340e40028806901c0c0200c0408045030f04104000c3e0b0f880c1d920f61000101c210310a9402180131001c2d03000084500c5c1041c0ca0207481d50381441d03e03290400c6140303102da51 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 301082886 1250 301081636 301081639
    0xa0f1d010204092018180a020703030f0e0c040c0903050a05010218191e030818010e100c0b09160f030c0e010e0711011d10050a05040203030a030c05040b03070e 70
    0x38140450302d44401c8071100580c044801c4c040001301014408007000300c0529101800c0c1100d20202c00e880c0581c030040c102c3c0c44450017580030a50104040d07050096038007108034003100780700021030451b01036110340301403400c94410b642e1600c00240290042e004600155000011390715813038042e003803840c040d51080c600b01c8900003803000407e02078640400f2003c03082c0d01104242c00040d06040c2d40c6100e21070203e0000ca0918140e80c4000001441c0d00010500340c004003581c840141d1036600094031104415070850700c20040341c904200b40560009031140041d41101b94038030580c81d106402030a215842400810400041d01c02007024078040e00340200300d910400211421551310750041000b80030078040c541c0f0f40c902e0000480d84030b5204a5080b85a00c1200e0000101d04008903100e10982c515141031038002c6d0446080b07000103003920705c1000e500649503003080c0141d1400c0d500080c0c40748074948002090564412451075014400c000355800b0700001c0d04400d60ba4204041e01070240f00c15011180d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 301084136 1250 301082886 301082891
    0x4020f03100b190303050403120302040510050712140a081f0e04050f010504030905010809011d0d090f030c0b030901150321020c09060607030e030706210507080a0f1d01020409 77
    0x310602c20f205080d15040741e0300f50f503807541001d0071603441c50034010240e2512000c05400384000300c1c0319900c034610b0b59200c682580741c0d540d55110502d0000904040840c0d88410b2001002c0640c000f500c000c030449c3c2183c1c0d014034105905d42c0e42c0f6001d0f10156520307811030b0190700001d100c01003035000d801040c90b07000d20b02a0084903030601030904100c0c02e03900c003290001c0004041400400865014007015a004081c00b8004540320081003003208184030488a00c040715031004020050342a08a204100a0201c1440d1030a015045456408a107040c6102d0303280e010b1070001c00514691001e5001c03a041440d0001903450311a5641031520b00c07105051100b5142d6101c2480d6100c042e800001d450152500c094090b020310b503103600410002d5001040c003075051103904002066255810b0007100c01502c0e140d141c0c0c8110703d9114030384a40b01d011202400000c10316250522441913008408a640403180c0d002c04250441d8180d42c20002d40160340301228404581c1d04081b010300c2c4c0c1900584251144220304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 301085386 1250 301084136 301084159
    0x90706020601080a110d03120e01061401090b040509060117040f1101050a02120a0306081e011b02060a020904020c1f1a150f0c190314030f0f04020f03100b 68
    0x41601c404d40d1050041c401e51840381850103505029140e05c40550090820380c0191400152140a03500ca000220303440e0796544c00d042c000f0526030100b40040d040203180840e02203040c105c14141d00c0c03245004075031003480c070800003901c1030303200c2c40d6148a1801c14040103d2142400d15040707403564900380048518446003a040c82003548600188c5800320001d500034441500c2c07210201c449a406441180c0c1015100c003c00704060408000101050021524501c501d099038080c190031240c2c0c000c10641000c0d021500e11182a0f400100d40d500017007640b40050356201040d001900038428054900c5013030090a803444d600d04400348a4a4200410782403d100040c20b01c0c030b092413842d540e20000d60744404902c0100308000c40403000341080d4034165468510349452011500c1c40c010144843c0e00104110500000c01c00da840861461040e00403a034060440c144002c10b801c07021070051a5003640300d028400a410b650b01d1800440c49084080c00303441c40d030a00c2031003007805000c20006060203290352040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 301086636 1250 301085386 301085399
    0x170a0807030c1a0c120403020f1b03060703060b030c0c010b041e050f010803220518010303030c090605030610020c04020a090503011802030c130b03031c0e070807170a0803090706020601 81
    0xc01c500c10045040050b10b13041100514176106440600168214818030200c040c5508003003004200001214030240001e980070020075113814402000417003050304010341013144440507002d607500030340400140c0da03d40b840118440d005004074040c055000d810924000c0310041800b030b46140d401d450010a10841c0c0c0c80e07482d0589254000c1c8205c0003070703500c00c00000300b190007901d01c00d25180d000d403220b91203480d5071800018100c40c202c00031051185010801081010b40502c14900c1c80c90b940c2c10000405440c00c18003030254000180014051250052041c00c0c8510030300070603008c3c040c004c7c070441d10340f207081c40c008120999900405000c2c0d0300c4d040c41c1f50649c200424000f10b44503401801000849420018482540c0f005c5000c0c06000c0d48074148100d4595007400a040c21008480c0440f83e0088210180c8080e202d80b0040d403101a0081041805804004180001602c20b0a902844a1500113900c51b00d02500c8100142803003034040306020100c030020510b40b0444440c4da01300d400716600c640c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 301087886 1250 301086636 301086683
    0xc03030a080702010b10021209040b0901090203190504020108070509031e0706020c150307030e0a061b080a0515120709150e063f0118020109150207170a0807030c 71
    0x70f5406c8003582c4109488103a850515000305034204000c0c0020501129079030104020100130b0b080840d0203a004401c200005221520245184080b07610520243c00c25400180408101a00d00d070700b0808000b820b020b49403010003c8081203000c1001c4844907141030850281c5902142c02548014060894421070618000c100041440901039501d07185844a01040c0c0041490641c15240b0780100b21909000c94118410003c2100c2c044415005259280302c0080c44414010401101d4516182c02c2c80580002e020500b0030010040c2c844484940d1085101807506001c0d03440321385010f0420407004041141441e90ba001c95182552800168441c0420040403080c2085841f0b100503100c10041805062020389048401002412610603440108501e00352006214106140c14080e100c81c000c550b40300d00c1d02c00041c9090207081d03281441c00c000094a80342c040c0b14140480c00c1140640c1b40713225061041e5000c4a40c0148259a510300300d1038050006450040103640001d603035080000070344802c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 301089136 1250 301087886 301087909
    0xb1609050406060e040902150c03040906170309010f05041703070b070206010812070c1208090306010e010612151e030309050411070305070c0905010b07050f0d0504170c03030a080702010b 82
    0x40d04c404040406440500004098000050b03a1004c06104201d2030702035207500600c95180e01001441d42e4a05049004041da0016480a8140f000c40380b50300c49000004002c0d03800c021000d00c0c0501c40e01e0030840c803c0340c19000e60303001712485050a0320042d82c1242c0010003403005901c03803c28420720351390f802d0b01a42c4641e02480b8607a5280c02181e001000503030000d009000349032084e203545003807a865204625120f00ca24800301d45000c2e00160085280c5000c00a15004201b100c002c0d00141d810f0010042140c03081c52821180c9030f4031802c0450f20000c9003a03120020b07142c40401c102035a08026032049503140544400d40c00f203030301e2101c0401d00d81042e001d512480341d01480b0440c03600ca5165403ca800e42d2001b42d081d9030301815641c2c0800d01c50554050039000341703000c0d03603c00c0d1241500e007015424a0481000c8504950041d1101d0b0b95998101043e0342c100c0c0d55100e841000c035000c920131541880946d4460f40c2e454080020000405500565400c1c041d501c00d5000b0001250544140020418103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 301090386 1250 301089136 301089149
    0x5040320090106121b03050a0f0603031d0303040504050c031801051003200307180605010206060f041104091e1a03060123030a050d140301031a040f0b1609050406 71
    0x7000500406001d007103020300758000d4007000100502c0482103002030000c90309100001a031903405000c010785081c050040c5245400b40200040c030b107182c2c0c021b8000a4400c2d100c500c4070704142400d030900c0d5024410799000b024040d00078130817464600da081c240c1d80c1c812034541c25240d142552140030035205201b03041c03007480c403a0703810411103003152140300658509820300d150001c0c0403460303140652001e200362001001c04080e80001c9002c4880b0300c03404e544468200f14119070003907041043d250b5400140701e8140200782c400140d0314004801484040c45a5000142c3c0103040420310b100d4104d40b03004a20040c041400100050505100715442c80d000d24004a40c0c158460801848400e1144e42c50a2015100309010100d407204d0101190820245120545440d00501c04034140907400c002c8502c3c12030007141c00b03507296604595074181c805014083c0f41e954201d0b403500050400c2141f10171213100d00e03080400004103240481a000201e40c5c01070200001502084000070340d800d19001d80f5007610803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 301091636 1250 301090386 301090399
    0x60b0a0f030504060e1c0807110705040207050c100e09060d020f1e031905071a0d020708041205010c030b1518030c2205070c0f02100c0b0705040320 65
    0xc001200720701520018000b0b03103190381c2d0b50900d10b0140804008683c40300042d039400b40f00c400c2078101d0207455280010450350502c07020344140007a021010a20b00c0035600c0844006807038001a083c40e40c44c04150f41400c80d0440c142500040e089a0003401c43d13101000d04482d0001540d440c80284920705d412100000e4000e44003000209072841c0500039011820218401103080c211340000007468800cac4801d0b00550040000d041d001400414410a005400c4810813840d021501c0c0440900038402e04022840c030b29800303d02d440401c4141d00846000300559240142211070b542072039402044840444404245010303030a0f1040d081c00b0320007050310090496407a082c4807003101d140500c40a200c80c247e03818000c00850b00c2d038560701c22515890390341c0000f10005054150118650494001410b007034103004a038003401c40011503a02c40c000c10079074103591141300602880b80a84001c810741c200100001e0701c88040000e603580c0711029000f01c901680300080c10030303185840441e42c00704c1031444a40284 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 301092886 1250 301091636 301091657
    0xe0403030e34080a080405100513180f05010303230c0a0b01031205030606030103120c0501091217060604060c02011110060e01060f02070513020405040504080d060b0a 73
    0x2402a03000c0e400c0398980905545480b401504000201400c0e02010391107161240a00501000300c040504041c01240c8000e0511554035101c0712424000c1c2d20070749118403c03508100c44094422420b50f450380c000c50044048140d260900514115050300c40140040e04e0704201194005d614040d5604032505a00c1d0000b850100242100640040d0301d1080004070702042881202d0000300401c0c200e181c0603045129895046140c030421680d00c1c240c40c1030030480240103012450303482200300c9046990164400c00900200c440a684500c40d410020f0300c65403030030b800303903052021144d818640404c3e903a6071249003201401ca16414041c00351000c0350403080610040c041107020f20380b040402e900506041401d022118103452030640c4101010710b6442c0c40d94070420000c100e0202c014003401907801c040d4106c07480307004001d55618191041611420030480411641c50b40356044501504015001b0b000500d01381c20680010f42c450070342020060325110002424610300307410f48080780820390b50f45a000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 301094136 1250 301092886 301092893
    0xf0f0807050f040b03130b070c030203180f060a02010509070902040609030605093d05040f02010c0309050301021b1209011205060406050402030103050a021e0102150405010e0105071d0a0e04 83
    0x54005100c1c2d0345424000f08404501042c000018501c41c1000034103404103500c141c60190103a520140c41d003c144004007800000023600441030329841000d1040d5118a00310a00c00104408100c4031410707000030b400200039110340e5041d0095485201a1000c9580c0c107542c90103d2000c0b440745200e2100040d403001c4082c400140207400c580d0b08a5100c000700d8151011a824145002c410706142000741e408403408082e1000c880c07100c110002c00110750401141c501901c8040d08a030b08448020704101e181c0d00d88004050180c814100605800b500854484091a142c0540c06003000c61a0700207103e001c104105102207481255440b00307041c0d4a28613520302c00d4071800058040903002540c010748418000c0b0320340d00c44e48081e6000314000c1000b0f0441d0300460044c8001444014465080124025420002030740c00080c082d201d41a0f1080852159445092a03030042412000402d215404c02060140307081c0c2c800c0380c0607102030000046010321201c10041281000f46449103d255039207007000079011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 301095386 1250 301094136 301094147
    0xf030a031e0c1e03060605040306021c0507050703080f070207170c0d0f020f0a0308191103040e01030c08011509090f0506091f02030108060f2e0302010f0f0807 70
    0x4440c0340d290403840981c0c0103403800c001d0700c2214038a8800210b144101d008010a9418070281140c514141084018240394004103603110b18040a04543d80000708400c01e11400312144c0c50790040f4590812840c10300c00c0c00240b4560002600b50001280d850115003001c10700b500c00c1d030040c0d440f40c00a002c40c6141c900c2c80d41c00031741c41c6046031040d03000710724204905440e5100b151084034810041c1c0b0080340010300c100444905000303901c0c8d0142c10043c0301030002680e2441211901000c3c0d00c11421149a140d07001c41d40401c841c14046001d00000c6000180a2644044035060f03c0c030070b04010401580700e5044d142211a40b42140c1214661513000308100b034002e6001d00e801c10b020b40414485a0182d40300c3c1468507206581c124030702d1f40032400182c1141c011034080760421030f00810562071540b5000c42c1c681d6410010380320200704280000403031a91a020b90b82d00c605080054401c40c0c1010322030f259441020024802039020510080f0500040d0f88a015081d0580e1a191901101c42c0c0301c00c403040303c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 301096636 1250 301095386 301095401
    0xf0909040f1a0106030e010b21070b120f06010c0b070c030504051206150d020d062d05010501020c2e0908070801090204061a03010603151211010207080f030a03 70
    0x6806107070140e2032011881c00c20000c10344410400004009514141e801002c0354100b0510b04400e901d0152054600c0d541e48d08200503000c01c00926250800c00b6100d498149a000d62002003108000280300e0b2a600020138018419490070940a1540d5101d4005440c44851100c0041c0800c464000240445010f440c0884940d402850920705064941c0007054000110000708549a4844001c0090b8135a1040d01400a038a00344d400f0820060a41e003c100e02009030072009085035120f400019800704a00440304503910140209141c0090080c0241c0080c2001e004050040c020801d0b541820f040c00807007013205030300003580e11640501216041e0005017140d01510f040000c2080d00003140c0404001020142490307a00028201c02580304000444915900c001400340c0c1100c5049040030441003a00d0440320720f4140401c140300419581010761000360020000c1c0401d0716424014002140203410310028280c08540a00391605000da41c0c13260030074030380e00310740c3d004001106d5480e2190708180d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 301097886 1250 301096636 301096643
    0x130f0e070608130f080d050a0c020313090509160f1d0f06060a12020a110c0a1a0703050c061005121506190e0c0705070902120c0f12010b091201020f090904 68
    0x30461090341c5c0d0701d01c1d01d5400206c0d40354403141c0342c0d028082541d00c43c0c86084076401c2103000540c07404030402e040750b226041602c10500ba03942c5c2c4400180c001501030008420120380c070b12580c105142c03030300b080c1408521240548415100e80c00d12005628540301c0c5250f01030303551780d1455240c6607903810810517198420382c1c81138208a102054418607101c5070025000080076515448002102503003001e00e402e00d010340d002d02c50320a4100812683c020f158a21000302c2000480c00e540b650035082c16102403040080080d144e00c60b1004001c46601c3c1040d0220540d4002c482e48205a4070f4200b140d5595610301041040d5030074503502094880c03601c400c1d045c09003040300090701c040955500c50300c0e51400048559412078000004c184007004803d004c00405404459400c41c20b08500711400ea500d4100103004980c05d941c00503010030302c200d803c002d4500440120400000700d684a01000045170080c05105000d038540c1c0c003000e00d0404c01070003691121501c44030541c4c04d080d0100d01300b159a010242099 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 301099136 1250 301097886 301097903
    0x6030c05120a0213031112030708030a23100e07021f0b1302040b09040c0807020c3706030b0402040b0906160507090902030d03060303020a02120c130f0e07060813 71
    0x2d00300081c44c01d000b200450044003696402240c042c1800b107442d4840008801c180c01c2044400d00086000381078a411212084c00010803566212100d0082c4a40007600d0718046406010081954110000700d000d07070b240811214842d4031422003da0b036541e49003c0b1000e40820f480701c00312104a1036805088035520050200f0318a4840b89610b0003207902582141300310f090001040c0300d603403c240c05000642c01e06880c1540891401060007911003e4042d003180c46a0340d00e003e040401d03040b4014183c030f445503980040c0994003c0018003041d02003540300d0310010030705003054800c01c0d2501d4400d4400711200c0704a070902d4000720070104140350b841300c48001d20b00726122181e2400300300c0400c00300d80503210892000501ea01d890040600e04031441070502d0400d81844014000079070f02040f6040032547c15a01500c00c1e5079020460350411140c0c0c801c09400ca841e1521407110044550003800921012940030000c2c010b030300c450141c03646418007812000c17540b5180400c211a0080200e100c81390702a5109 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 301100386 1250 301099136 301099147
    0x506040b0a0605030a0c050c030a050307140309060405060a0c0e01141b03030118051909020a03020405090a03030f0b060a0c08071712090a0203060c09030c151306030c05120a02 77
    0x714400869008600010340120812818014a218107244031074103060081c00d1036101c0450b00c0d900c2c85416048801c010000c8045500c0501843c00802c421200140c21a00c0b46880c2070a0355444400302c0381900c00d8802e400100341545000e11903043e005000341d0300d004031241c40500565441c40a60341c00c0d500030f0b00c00c0140d0f5118250041c50140140d500502855a0f540360080d240c1c2d4041c1c83c0020712442902d04000c1c00382d201003031001031504c501071003c003050880f01c40c0002413000580ea400030b50401e040400f0021901408600702c68054420b880811510013466006022180144691500700500b0005981114003036550500d40500c240d050034504420340e80d40041040301c3c04481d40940d80003003402c0c20f451514080e25030f44100054024014040c040c1c000176514100904a0b500518001581c00c505032800c0c00312003a0310b18060328141005c07250600b0303802540e024807400400300341501c601240851083c0600c0000501e036503070705800c19000900d248803200000c3e144070010340d4200203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 301101636 1250 301100386 301100389
    0x1d0901030302010b0324071b0210110d0216030803061906020102180306070c06050a060e040b06030d080c090108180115080106060201060303090b03070e030a080a090501051c0506040b 80
    0x4014040c511960001c600c0d03a20603c00d06181100c0380e41d580000f91200380e0302c401079801e07140140e03501c95a00e1a004200c803040080b40881e038803000c0700c069042176200001550051b0492030414a500304141207a641102c00c81080343c440b030480003d2020858280800c101081d4204080c1d608050010400700e50403205006043d88441140e11040140c3d4000c02c007440c4075500da581f1541000350a44c0540014500304400501c56800008018881943c0d100400d1804049900c081b015000903256800c071400c0c14240f0007071680045074058400d10840700801c841505c04c03180315008070441011a402e0441030030064a10000003031900080c0034030104040d590307031024011990940107410601c03203024200400c140c00c2d41c610360054000e5a04040c000c0000075448508402180d02c01d420250f102c0d203440d07004031090380c40040b00c582d25200d401c99901c00e21400d00010a5007215039141e9852042d075400040d255400f903030804103e12000310101c003547c003c1e203800641d48030400510000e290502e00d030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 301102886 1250 301101636 301101649
    0xa0902060f040305150105151209030f07030c0c080c0112020a03022503030f060b07110307090c090806071e0f021e1006352415011404061d 61
    0x80c000d0b44caa80c450450035501c1d180111382c0c10b02501c002e1340e86034034699026011400602c10b60b0056100440e0100001c1e282e46001e1041e5400d4040035001e5550340c40072418018001030000e2800c0e11150a13a00b00000c14403800100105a2071060716045186d140236902400250030104101d4141a000c00c02c00c04039155400b080c1244489203441c01c4040840d03420014226142041c10302051271400000344100b0745801e064601950b4400c2c0302444100c1c80c00046810011594049030100d0305060348a0f140c245c000510405543c8000704490841d903910404132060b04085011002c00d04014010012582c807032400c050042a8900454200100040000301c0c01c07404c003102c0c1070f495004400c0ea4500506c41c5d008060040010f10484c0c090544460090245c00498030038004214035403400c641714140e018408580403009591a60003104503142d0310403024072040780e41051902101314403620b558002c0c4924410301950304111030405041c8141980d00c1203191040105110701d0391107196040d034a10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 301104136 1250 301102886 301102889
    0x303081b04180b09040b010b070305040801020d061a0f120408070b01141e030c0907180b18031605060901090806180601080724030f0f090203071a030a0902060f04 71
    0x9854a500320345916016000c40e0144038400744101341da8028030001c200a8004141903410300074141d50746c2c902c0380c5009e5038039220b5580502c0307441d400801c050304074a00d2988140103d03445039185210048080090b2016803203507041d101d078110300c1889030403510900c411305264010f00c0b803003440b031405245480395000e0840c240d00800f61034109824580702c40c14216141156115010020301014490000180d00c0c2e454401010380100202e0b40050107451240c18541c1005191100f4158415180c0d65480699440181d0103150403c00c041c01030b0450400041d4400c68000038801a134040e400c0c0f008001e0541e200c054058104541ca013400710f215401404550f0013000d825140d120030402004001b402e11b01c05078041c3c440b86d00000307001c01c440000c908150200110807c080e40701c0a40b48074041d0011b243d94090305a00c1440d0840b00240b501d100d41c40014418021130490350b000751b541c0128409540303000025a580c42e02031001c1200403800d81c01440340c01c0d100074081c0d400c0c0640841098080e0708107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 301105386 1250 301104136 301104149
    0x507050d02070b070e06040e13110a0303020a03031b0516051f0b100c030c030315030f05030a020f070b0d0f061208280f0c03020a081809011e0303081b04 67
    0x8a4050113191600f1800341d44869034252103460a1620389400d03c55460001815a2410001e0700c81c42070400c039000c058400e0b0032800030004020192241002950f0749680001140820b20b00211001c40303c202c000e9000250410f5600c0e5807409045030421640f007142031504880501c2088480c05040d20366081000d1140e40c042000601c20300403c04000749415004094401d1201c01d01080022987c00344402c500c50750541804075001e101d080d220702010340a030b400600308100030071082d020004040000c05261803694201e506100c4156a01912000c01e481084141e0078100600b6039a140550000d190070715070040000f54007950b652111301501c19000080b9005076002803101002074800002202e00319480c1081e07282c0e9550749101501281802c080d510034850114400410184200f04403000720703900c09001521070540b00310341f0364602c0d24039a00c03520822140d0004605415004120101000d1201040000b1440c680703054035006400381041c100240054500101640c280c03000300001d144d07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 301106636 1250 301105386 301105403
    0x20f0414131707020f2e050a02010509070e161806020d080a0c0518060913050610110a0b100b13090c0e0a032009010e041109010e07030507050d0207 65
    0x1040c0c9880b500c2012454482034484105001450140c2c881154080d605641518a07603103054560300f00d002c140401100e40c00132142c12050300c041c41d5501c80e0283c044001d8070780080c80f0076114034484175200e800c280a10307c00e6800080001b5007140e04a01205001151818120000c8103010003880201d5260380000c0d025074403003e900d1f019140d0240249504c200d110704208401c90540c1801402c910800400311203030414511480000e0b62244110b941458000b000009056440010385001d400300305c41c06481707070300300c80200843c1600801e20140041c0c60100980b0801c9981e03510803500c00c40203010709850001d40240825101101c02c01409806c859180542d000f9180a210400f41c07062107540f44100003581c0c010742c1c1c840e214560008281d03a4840b0040d20098a01169070b40030240c1e00341c606501860b01400010a1080d241d0100d010f140114201c02c03030310341c02c03d0600100d14028401c0c00caa100e146000200e0a81c42548070541026462400614040351000d10304140e810801c41919540c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 301107886 1250 301106636 301106671
    0xf06080a0b062403010620031b0706020109030225030b0a02030a0f09022218080d0516050d0e031303080a11010e030f0d06030615090c080f04020f0414 66
    0x1d4040700c0003c030a1201100d000808041510f001982e010601c070b92800d12032403240308220f013620200e000c80701802000869807261884030140040c540310850f4001316024101300070036030078810f000e1045a280c00d90014000a00c100500b0340780e80180007560849042c51000100000d4242c4104500400d610b41c005a104e08191502204444089884960592a190303230320300140c4800a00c00080ca0320300d103a02c4007001c0d442135404e000c1c2001c0c062980d207040d1001c45140400c03104030003900141061500c1000304e0b6036401c03d4400c280514060480105409001d141c001c20a40d420001000b11103500f0b5a080000643c1c580580c044281c004907405003004c0b420301425513025210000c03404c8038400a001d90038510038095120b104010104030144030000f0103060291883c0c1007a0000c542c4200204088940c09800c01d500000d80d0241281c50f608054a1004080c4a200114082c400c004d00b1035100e500c4035400c201d207400b1010b41c0c141c0c12544480c40b0b00000200800403600c144640e00f81d000044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 301109136 1250 301107886 301107889
    0x130303060e070903060237020c0402160b1905040c0302030c01090501081812041707090213060e040f05010f05010e0126180f0a060b040e060403030f06080a0b06 70
    0x8940a40140689001160401c04150380c0f0083e032100302c942040740184c0e100074000b0b00000c6840d0740e50405810b80c0c02004185194500310501c44804401035080e10031900d0043c00700416441206c14004d00c0501408619001c01c49814401360060603024840c58181c01c0c81003000181d80c81103806595110400340200103604081c0301100344810709203003001038207081000103051124064074903107204032001f2040840b10002c11089001a2a0f91034203912140d548101a08841c20342c0c49060860280301d0000a00c10703010300a460752811010382c14130509040600840307c0201c44039800ba4040d89891203459501c05a00c1558043e06218201d10740d5241481b0016240c81048140181081140f42c0800c0311004a800b2000b0210300c0004400d41d181c5500c00750f09801e20503d4051960303802040781c1681c16140020702100300170b02ca020300307210003008502003100f160042a921141d9400420000d40001d2080d4880f6800441c225400110162500d17001071610340151000c80e9070384400020b21030b15 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 301110386 1250 301109136 301109141
    0x2030412020309030a060b01030905101b081311040b090a0605030f0d020715090815090d0e030c0931020306060307081203071e020a11010e0a052403130303 68
    0x28003858002180f0b042e40c080040303641c1e80605140a00b4135075a90140e042c040e803280c1c0111245681001c102c9000b0050700314000b000340524401681c00f80c440d85c3d9002c545071300807941213101d50008814008a12015120608000d2408641c25407055484c901526159a1904442d00034840e01c400010b8281c00c03c0141803410111b048222900d40c0030f443e100c43c80c61b9000840d2001e660144488004040c00b00000b55a4003110303400c4403080d0301860200700c488220b0000602e20400d604011214132030407c4c00203841c0c1c10328400207580c0640050004e038000b801c1100d03590341c01c900d0f2800000440308455490071203090000991110b40d4080c1c44510040d031804004860300030101f01c002d048041c0c64110803564414080d041d443c102d001c0400000e22460250754030000090556040b807021000304a0020341720442d0f44412a8007803c1450710b04441d512410049d540501d002d000880e815051208101c013402c031083c0c01204c016180340445024000e214051401b40010f442c40c0d400d07081041c90040c09 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 301111636 1250 301110386 301110413
    0x809040908120a05010b0714030409020304050f0d14030f100f080c0312030c0702091302130506010f030c1407050304030602070c050a140904030309050c0409050706030c02120a030e031c020304 84
    0x5056040a005100d06e0702020101c64120340d12080200a001e58080440d0071409079900c111201440841000140500490160012a5014151540d11b103900b0000d071a2291078a80381ea014520074000030302600c5a00b420160002c01d804038814040f50348140c40c190070103d541055009801c501c42c07494450a003040340c005680260b5501c40d003141740c040c2442c00640240348010784604124404a080d4103a01c0301700380b0425070050240340c600308041e48400d0151405a404a00244032002e140120340e10030700c1400da84040035515002c600c084040d42c0303d01a000084247c4082c041000000300158070761004094044c420801a1989840e020401c4440c030000e40c030000340c0d0113905104514559900350521341c85545130400003907030201802d119103010100108240c2180c0390080050502500207014412143d541e81d00388914403524404030f031601007071803099940807018000040228080e4003d000d9101d4104110707410680d001603890129203a204203020b2407a0300000307100034003140c5a0341c42e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 301112886 1250 301111636 301111651
    0x411031608011d0c04180b090304060e0402130e06031014010f080307052e1401080609010903092d0f03060b0406050306071133060103090201020316080904090812 71
    0x31480002110786620780c00c5000b544c0d807040b0380e1200c0454200c2c2c114254511107030b801440e0b0041a180203400143c6c0da074414023a40e400301c1c0d00c120751958540b5040c0204e51600007920844e50304c10345000d4507000131100282945038103024210004505154902c100c550701c0d1195121640c55503d03200f1074803c0d095441d0020a02504104071042c00325000003240c1000392078044029403203c0c900046400554400c0c1402104107082c411030b48012040941000d05881c002d1040d1555038880300c180c6805c86501503401000708014810030000d040003404505100035501c1600000380382c5071001d0083c40e48041d0803050036186040300071300512009105e0000804001d91f804c01c01a814880081d40e1100018008400c01184c00d14490182d4000c1c0b01240c6d41901e002c625184d00c2c50801c050541c03c4a40c190303201400c684410025550398828011711034281d406801070341c5000014000f48d40c03003c1c1c41d45019030726040c0c200214903042d29a4131812240c58000c4242503101e2031031200441d020200504040d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 301114136 1250 301112886 301112921
    0xa050306012303010917030906010603061d04060207050303040c0f060306030c090236010e03121c020415200d08010603090501150f05150301080a0b041103160801 71
    0x14070207441100c80014002e09041820015069110006805003c080d4070007040c0c0100b10302c43e9655000c8140c083c60280030041d091381e4240ea00c9580440454013240f1441000500c11340302c0f1000708a070500d4030707074205009040140c549001c0c2e403a0285182e1050310201c41d581400c89080100b642c041c0c0402029012615060106c80d10355100d150f41c6440b640a10050b0560002c5c02c4015400003000c2070591841c040048254100090040181160340c2c1108a011824459040c281d501d0701149000d00d490781070000500b0920603028103a041d002c640945c0001541c01c20021403241c9903252841d552140f141d840c2c0011440c0c40c0794002200b0560300720051396a001008a6005a402c0380449041d20814503001403805040d040c010301403d040801144503080010b00401e014101c1101001981d0b0251507000d242c0d002e00c4041d18151000748594940c40d000034080500003907208113031302d4015004d00c04070780700e8007040b2001900f0252029041c2202829800702080181030a01403480c510103141c900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 301115386 1250 301114136 301114139
    0xb03060a1208090906010e030d030e010b0f091308040807092702010207030b130632090703060504110913020a05010908070506132d050a03020607020d0302100e010204050a05030601 79
    0x340b80040c01070310300543c840c464143c0040e030240d1041d0705401000c0c0c3d0080071260454450b01001d801040c0c000b445500c00e5007400070030000d031b0500d400c446a4495003d0309a03411550f41c0c2070103002001d40c9003401c5400f06020800000d141c01d0402c01d91025003498013000403e034240f16107284501c1144060802110712a4202601603038000c200101161b030010032100b11030751031140c00682100f891100030003d52428600c0001407a00b005400d042a00008104003c0003801125203880303217084413801019413286105000240094114035045445451100c800415500004446440032680b001d1460003009040040d407400d1080440100300c2800c1040c20b540c14030300322584801d40c50017414001c0c41d0014000e08100141141000103056400c0c40b80300340c2c0c99200ba119401b2403200c001052586d00c40307001181602d403a00a04003103070b80c0100700030f16014469080c00310000007072800b50f0650040c2c0020205d541c441340207404c074a0095a00040e6150b00303107020098094400c2d0062802036021000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 301116636 1250 301115386 301115393
    0x3010e0318033304060e0708010e1204030507062303070503040c0b03010f030813050301060611070806010b0a0c030908060109140901050c030708130f03050705011a060406051c060b03060a12 83
    0x2c450340c40108a071000c0f4560742d0f142000e070098040500104041c1c03081090005070300c1e006603c15002c4001da00240c48100190701c0c0c0400150245000180c441e401c1130004100e620700490613654103112a660071410301384c40b60442c80c060b070421502e541c08120000200010003210484101c05807848502c01400c65040c00c40c110300344141804018142140000c030520800e4082684074000c1400030000e100342c5880d483d00410400f140807903540c07184144000403075207100218420f81070b03d50948160f03040c04842c2c441143d12455408043d01406038201c03020464813030900540e406070100700fa000c0360314445103803200444200213000100e107901d82070912041e0880ca9003100d80104452070501c4081c1c440900915120030070081c01014900d10000c2402015001005000c1580c0500c008110f07100150202f068018142602c8030303440b480400017444080c1c0148050400d481a5080d111040508448404102c511300e4006076260540801041010320f410070151001d024000320301c440403806d954 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 301117886 1250 301116636 301116703
    0x3020606150903010501120b0a060303020d0e011701060f12050f040b09030f0d050403030b0f1324030602090f03031e0304030c08130806070e06041403010e031803 71
    0x60006101c1d0400d000a16546008034058540200006008200795655125138001c8500742503030880b081c0c01c03004006001c91400d40701d0041126010740141c00503020200040b2804000f40d10441d06022540c881e090200205601c0c2074040d0003681c452000e92203030040d028001e8140300301e8a80c981400c0000300881d0855140c03109130804e51040112a81c4e49503081c24504500030303400004000e140100c0e40003c0301e40c8980165006600035201081300d08641014050b08010341c500ea81d400c103401d60300352003601015130300041c043e0844181804100c00d48030003041885140c1c0d1300688405401180440b007903e072041440709140b108270002e40c50030b58100c6900b00d0300e044256094041c10750220025040c9170142c0345a080c010f6000e5442c5907602d01c1e1001640018480d8090840580b0a91002801a81c0a48001e21125100070802c609140c030346003000018201220201740c25540f2200d180301c900d01c04002501400f16481441c42c9500010b200703061a001400688010610f0401201c120b4a462207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 301119136 1250 301117886 301117891
    0xf030a050904050601110f0102040509130503090f0301020c0a290712090203030708042702040b0f03040c03020319060e03070809040f1d030a0e0f0108060118121101030c0c030206 78
    0xd032800301d116900c60740142c50022446884586c01d00682e444071440100660062090f50f004aa0000f1192a40013141800015441d402403540d4020418482d05180110b6440001000200094941540550307140c0c10300c0c00d810b404072a980491848070200d03412401c0c04800652080d045900c403450042c01c0102148401b14020f03120640d90b014003000c0d902c0510071101390381e41151001d030343d485c0c2c0c07080307010001c001c42c0403828803081d15400070382c601c40c40f40d000300d0301180c103030104103406c00d640180c07841110340c00544202c99000311803d000006880a000c02c80c0000080c0e25055200303040c9050101c00e45059a4560030160000c1208100259080042c0d0f08141004d035000180195880b016500800101110030006926400704500d8480000020710401c0844e40d60042cbc4a2443d50034044038840e45001540403410f044005043c4c3e51180d00706100700303075620b5000030700c0b1a40c4814118503980d0308001950310700500e82805089503098003039610f9000c141e00d04528140c006803030007511034501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 301120386 1250 301119136 301119139
    0x11e361b030c03240e041505070c1401050610110304090509010b01091710020f090909070501090e0c03040602090112020a0e0a120309090203060a080106170c0a360903110f030a0509 79
    0x110000c64244540b29032000d545011147c010030460a1100700601050300119044852040300e40049417411030600425004200c003034188272132603454480540e01a1603400d80d854903480f0074000000c05902ca800323070714011300300389000064096140e0001004841c50303401082102c10408404868040006040c42d40315000041c0127864481c0520a0a103520500d010316a00800b0b59080c04164071021810b83c0444e0340c240c880c00c80740e5076242c01210340481c0c1129807151008060000801088554004240540c070515005024826040400080343c100664036400100f0300441c80030b0768200340c81c00e500500301ea46140c0c038803030038155002000071400e802041000d5402002040094441c0451100500520002844a0340e11a042c48040090b0700080c114a807103112900142410b140c0c50040c02e0740c0c400c0c0041c1c41075000485900d4040c001400811025149200d400446074226100c2c90076100e203ea07944008060a03082c03607a245c4003002d0380c02e00894008102004e1065085000c54562000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 301121636 1250 301120386 301120409
    0x90a081c0813020904050c010206160e0f010314010902120c070b0a09020301152312030a0c0201020a0b130303060b0910140c0303011e361b030c0324 65
    0x110b0603a105044003080310025082400e42050004001000c5284440300340282d01300c0d40140d56600c2e005582200001144012800c228052801800c0959102d00b010406040115000d81c90b030b10301c8100030384264007400520b03901040045400c08a41c00164200002d8445241000d841d602c6d042600f0380c02510400d03816a9440d55402151000e410107160001605c00507100c05940300d565990b0091005a4225803004580489060f4907003c0390030304503199070744000d40c28001040030136650700300c0114051f0b0640c803482041c1d0001a05004106105600b088208848000c86180203401d4030f20980160980107024403c40115840c0c07507440c20181a503d20380806204a04000300040b489000b42d2101240400000450341001c02c3c540700c1c00354811084d0780300f103082e50b890305805064040c1560f014032062400c012000e205584801c1e00303042ca1404000a4100740644034100354044085c8404042501c07840c180001c0d58244c89170000c0c1029030000400000300d0128091000ca166025000e000e68 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 301122886 1250 301121636 301121641
    0x7080307030f091512110d091e0b070f032a0e01080c0f071103030a0302070c06050702060708090f1305010906060305090c220c031d0f0c060a0c0605040602090a081c08 73
    0x1701a00304610780d0f00d1401d081540c800d10328607140302501c080602a10003401d45914000b4104480540d41d03541c0e41c000e00c003801c440d2504482100c0c0c040c83d82d0f5240c0201500e82030358201c007c0d1130052500414143c0348500e0040841c104020b032551000c0514141400b03040401c004c8078049100c11503501664560450f541c480940c50080ca050300c0e8240c4940c5c0500c0082000204507070554020320045014581034081103949581c01c03211031040880082d0031880030321010000a82e100c010344000d1200800a6003c48101004148500180d1101004540d2541d004100b403852a1055901800043c9828080392804841e01a51004044641d0b4010180704502002c1340c07040c48c0d110f0500341ca480318248040f41039035200902070104280305595150380222100c41b41300000a42058a4031200d000d0041f0315080c104010050b000f80c1111024006441e06860014002e0700c00d0a20440c801c000058540c103841c1e040c010341c2d99842d004050f05500c580e0405801506408118141c003c4038613200d0400e5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 301124136 1250 301122886 301122917
    0x6031a0a061b0c0e06311505031504030e1903110f0901032603040b06090702190b011415030115052107080907142107080307030f0915 59
    0x700b4507040080d1003901c6510004c20310860305249540220400c64016819955403140122083d0130415002c0c5180840c0c030161080c865641c1083c000c03044200c0090344541d03900c0001c00d00b4803140d101c81041526083e0200010180c0120241401c000191040c028050a044d0302c00300ea070302540409040441d1650986c60607660b032078507107952280003400070242540c2d02d1410b50402d043e9a0900020315450005d0311200740c3e031071800e52344540c0d04090121b0b06d54a40c10207015211101a016008500030031624070b1000301c40d0071a21207660710441e000e512540c0361004801060f05101b0045204040e40600115180c181d141503c2c1903aa6080300d100c4984025081610036100e110762481500003108500e00c11a08003c1c4102d02c1403410340c07034078240755136100c5003103031110741901a000c00701c0c40340481040c540c00d00c05e108803280403070030020344404100700500d145404c207e580024100d9000261030710405500000500d01000e42d4205180c030740d030070883e4a9a04540d901040e4003007040e5520b110000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 301125386 1250 301124136 301124177
    0x50d02161a09040c090303030e1209130f0e0d1d01050307050c48090109021606021201030302211605031902030a11030705060412091a0406031a0a06 65
    0x20700b400800800c1141c10f150006081520f507840140e010a180c06100040c01c1004608865682c5150300b103680f030034440408200b603403040747c244400e00b20b80d82c078620156081030b0f110b44569580c542008010f0300000403001010b406500d914401490400d00b010383c02130343c002e425030b908100d66080007510303200c2030180b5070300d041c0503070030102210181d0468481d0320644403406c440c400b000460542646e44a04903580c540405268501d5410060b081c0041094807142c0d40030780445000524404200c2c07455407283e006a820000280c0c04481020004000709a01040480c02e031403007e10604000b03403644031840341d15004003251010b0034083c80c0101c808021013402101d040b40b1100381242c40c102c00040d002035598020420b0040810b40e002a1000025000000e075070250340c0c050000d005a40c1c4a0b03071130700103414411001c0300c03d00294550104074002018030100345003901210007511140b41c0440141a6032030700c5121394081d92010095030031501c4152403c002d9034084e08104c80b0750000464248013 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 301126636 1250 301125386 301125397
    0x120303060f031903050d0e0a020a0303050c0c06040914090f0705220507020c03070f0b0f0d02090603070512071e0c030207090c0e210304030b061804050a050d02161a 72
    0x12003c500d0f00200804d90800045c1500603030b1030740b0800280c030f0041c17005640c9900010005e50711200b400401c2001910401c000e005100381da0098800c0351480d1004120709402c00e801c02c00c4940e03103070100d2602d1310064012044c0d1107030054006040d02805001c080703484410f180901401032100b081304041104942c90760001d80c00241e80204541e20341900001d449403800510300d842401a82c600040843d007524800f02542c0440001a1512801c40000e684582c411131100d42c040340c0074008880c0c181d03a940081c61052180e921000d82d00c80b14001d020411800080a4400b8441071001c949000090819042c202d651541013100c00d034802030409924080540d0300c400010742c01d0010403540300383d0145074000c120400b9150440124000ba070001030300162640644a0380c1c0c8188020400315a05d10050342d001100580494040c0c011214224841c400464066441d9030244c41d642c800c2150801016504400c40d201030124801d4107000702c000383c0c0c003e100f03103440030583c011940180e0f010803084a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 301127886 1250 301126636 301126663
    0x5160506030a0207020319140705030d020709022203050d03050a1104270f060f05060403031704030e13020a080f01030b0112211115150d051603061505120303060f03 72
    0x162840c0515002c16040c1c6450048e0842c0e0043c1c070000074941c01c0c001885d6200003220340181112a050540c00c400035080b801c100315100018a00001d0344909644c10803000d0340c05070000e800310080041000d81510009480072001900c0c081c00120340321405015501036032001030b81e02040c0300c0841d10941c004411001c407107199a151400c0d054400090f030384a40101c2c0c3c840248181c0c42503aa204022190042d4440038001c1400301daa40d0144168982c01103074041c0c407a040a24544079258003107101c2e111201d0980b0340082d4001140e0340d52135008210954404a4001c14140943c1541d80d00142c580041c82184014140d000b68481000a9550a03009281c0b1503035060b0b0300007086680041c54002940521140e03406082c421000b20580c115915200c0d42207081c0700e80110400200744050b00140d20025503090080c600055138114078460420002c600030000413420301d0001281c00030f214501d621561146503011b40b0040044004019a41d00c4241240c01d070381b8020a943c0840d060160803140007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 301129136 1250 301127886 301127923
    0x2060906032d060a17030726030903032e090203100b07050601030308070903030804320105160905030c0402070503070b070c060b010807050304060507021c0c05160506030a02070203 79
    0x9040c41d0b22407140c5144a55412943d14814030754525611091840c0c2400d4451541c20811240c0041181110446000e2100d0560f45007003014882c0340440341e8100351903003001d0b50000424081000582c461980500500441544020030605001811001c0b188903070f0000a80120000b5090300206060b0402070562030704403542c414480c9000d40c0c8901c801d00003100441c0e82203001c508158860003c07001929415143c400103921647c681d0b2064181400c0b0b0320b0050412042c2208041486050015000003071100205071401c0c410b10b805100141e00c04220100003100004005070758001404000410050b540183d565501d424414114840c1540150102d101501805800c0c0ea200881c803825a00400c000c109028041c0011a4018025100000064001d0000c80c01203071140d0b024a800208900445001110382c00e440c9050440c121030301e5001c5914980710390203100061110250017501c0f0855404aa42007100182040c04041d007625a01c83e8089582801c43d01c080040940007040c81c0b850 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 301130386 1250 301129136 301129201
    0x2040b040303090513020c070902031f060e0102100e031b100501062a0803011403100606170f01150f02030403020409060e0d03050f06010e010e1003020309060c03040206090603 77
    0x1600503d031621409000707401407641003070000180c0c400d0310904803440b800740032900d1408003584040d4101500f4010300404c1c50b10f103c5400c2c81c3ca03001040c02013006444104400f00303200000380c180713181c0c0d0709403064081c04d010703010324000d0380401103030b0a0f0000d0640401600d00580341c0c2c24039140d1042c8201c0905031500d00085602ca03008040148009083c03041590181d040c020f580c007201b0044900206039401c144014400b2490303084459681103005401c85981c095100f1002081c2c8000c0c0c1c0c01031020808819002c6010070289513140c3c0d00001200600c652545021100c110040d0381104020070090026074440615200b441200d000b5a00208140040001070070000024080141803c056109142c6c01280d198040d001d801e02c10b001c1203104107074940e038800066500301402168241048414110514550b0322814040c1225000d95001600c0380b5204010340e10b0403074040c2070a94581c0d403e0040000590700c090842e4074454098540917200c0d100e015011120030011034078031100480d201d41 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 301131636 1250 301130386 301130393
    0x110c010207230c06040b070f050106090f0b0f100c0201200c040c0305070c11040213030602090a0501080408090d23010902041a010e040b0d21030b0f0d03110102040b0403 74
    0xe08820380d94a10b0440c5007480b5203614000c1d5a504030360500c07904501306101c100030802000002c2d000007405012403e00040325542d4060071501d29410007401c0a40e5083c40c09140200c5102d10612030b03100351603c000e250803500c000b070303584c5103005450390801c44842040e01c1164030503001d001c3d4200903085442c0c800501513000325261050b06403914010340c0340c04081c10410340300703010312030042026880d600d000031702c2c68407101c142d090403140140d04250204009150b00b544202000025805603c005031115546c000f0800d5031380d55a4030140c10002d03448244004259040c088441088040350709100e0120546001c408100c000d0040b1451a6514001481c20040640001c1640b0384221030821400300202c00044040ca00f942d4040d0000e0035000040e281c80c01d05030300610324000010110f640014460340c5034031801200c0c64003481419210b80c09885102d030140103c4107404022241a080c0b0548c800110b42250403c20001c5c0410151900700e010a1500303504440c0034011092046585944a09 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 301132886 1250 301131636 301131653
    0x10e07030905032b0c0e09041e0b100b07020619030f0c110f1b040905031312150912082a0a090905010303020a021203090a090903030f0b090109110c010207 68
    0x3607a0680c11341140900000001c0d1604c01c1070300089090f02c440d22242c521000344040c3d1000204116000c0c82d0261807808604001c01040c10f580b441010800d25916050070400f209105540c0f014215620900901c1c1c0103a641600b6100e2072451260201549058404214080e081c003080d20071196180c10b542e00103080d80904103090f2245040e00701d030704d009061894159590501178818200c03d250200c010001e244c59007245403951b0083c400c5030701785458030607070141e42041035000c1088610000000b40c100409405d40c031840c3c4100d07103002c000401054882e100142c80301881b803402c004035807002842150139216a4843c07041221210000d0042c015003100355544200c0c021070105407400f1001510106c14000c0700d0507282d02d81d0152401810070350900681148240480d0341d1790000b401032082c01c0e152103450724003d101188000c540e202e11030030040c003141d80489400d5400d0707003000d0318003940f0f4036045103180c1140c80c0c402000034509140160802d2a00800308070302515400060f0840c240304004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 301134136 1250 301132886 301132927
    0xa0b0a1b03060501030506030d08060f041e0204060224010b030c0d2c06040f0209100b0310030233030c0f03090d02070e04121b05030a02010911010314010e0703090503 73
    0xb03880810182d01d8240c02c00d43d54081e40243c920020b11041c001400506048031000ba1010000d440804c85039480e41c41c0a0401d081e08038003840ed20b80c0850104061030b070400c94003291145002940842a0740c000000c4003003013050252000b080f000201241e00c00c09420200c41140101e1030f810490012412003901103180c040c5804803192a01c2c5d90f4004190138042030081c0125400010506401280e50900480c041c0040c503407901c6c03040e840c0000500745010002980b00e281c0c00454003500e18210300c104003500380107401010070b581c8600740050001c5482081045141c08a115241e10303940c65803440c824070301c560368032041080c402000f844101c000018a20030844103640a5984841d200d01400d4410141103501500c0c150202c40c0a42c802c2d4040c0314030044440150170151500202522010315580c412402d00c0010b030340d110711100a008580c5c040601c0f40c0024030301844005203030f500004410006008407108012107401042825001e944448452a40242520303101c4441408120804900b07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 301135386 1250 301134136 301134139
    0x90d1403040521070b0a1a0307060e040b01020a200102060f15010c060204090603030c120503090a1419030c03080c030c0406081317030709051903141501080c030705060c0a0b0a1b030605 81
    0x190607c041e02c62401061100c180da040c0c1c0e851364442c43e012001c00000d031400c143ea160540c02403440c4a008100d40000f12280010352100d1001e081303608100080ca408002400b0199015041062156105a07040c1c443d107074a03802d103400c24695044e402c2000081c807466001c5d40e002803904200100f00b41c3c004082c8201a0700514080386c0948d50501c00790788500c01160a4412600208a070800084a15150258000d80203048441101c5a8044900b0411680500b0b4002c604408102c03000c059100c03c505d64040c80c22517001e421405c200000407042d004a00441c070030312000c000000c0f0740078800041c0480594100c40b1101100003805903006a0703a009a8021f4005001d118010071941000f001480c013400c62403601030b4800303103075444d0342c08403003a20661041c2c0e070f0082200301281106004851400390054002500c904201e031010180b4090181c0d200d58040c03103080c0950400302501203071141e10745030804001a21590f03410842c200520300048013450341800102c1c9000601d0f4164042400d44d03d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 301136636 1250 301135386 301135421
    0xf04031803123e071703030105150d0f0f0c090302030c010c051002160512070c0b03071e03020a0e0a0e01090c0504081510120f020f040f05090d1403040521070b0a 71
    0x3200c165105d90a0036100c2c0060041d4420001000203051074820000303140f50b5080e036542405030b41308200c410f44094444159145448441c4106500b03041d00c6031804080681c240b55403142c2c0342d5400f0a80740d0400c50400c074148180a410a01480401c0c004641c0c52114410708564600500c0500c1d0b4841c403034240291840d1064410707000c0030055140464580c4c54104c00c086140e2864001409003581c0000d24034810030007440342264040c40c0c080f01141c0d11300c410f62009030721100101401080191461030491080020303807010802040032568081c19242d81c5580800d862201c010306a0701c42c800e9900400581c494901c0500409200606541c040d500a00200b00c01075518528603503080340f0810094214202541c2040c0145400c034088281444098404034103d900c0b203e4240498500700d40b803011a0304849850b003003442c0d20201200d015018000d40303074103504103074407041d940303003040610be426008003172141c0300c40071492205440c0302680c41000e548142c40c15240000180032415150036103201c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 301137886 1250 301136636 301136639
    0xe0901150212040e01030f291801061202040c0201090203030703030609050f0103050c04090c050d060e0606120312150a03060c031d0a02041e050f04031803123e07 71
    0x2c81400b10741c1100e110b018041e9080e42192140080c02001744411200d54030400354099108200c0c0c90710030045038401c00d00100c207190001851259005840c50071180381d00d001da0611074010b0908000d6080d54055a00040004002005034014542540301950507c4042020020980e141d0030580941e80e852030b09110580359460101504a801c0c0402403440d0484006403109013081d0380621445030064491903111a6105c0c0400d8032485046419140e241d1510b1010800e004c0401065070810b40646118616010001f0801e07140d0050301d885481001109000c15a00d14403001d0b038561083d40100044052540c0f490910300034890746a40101090500b050307040e00043c118050000b80d41510301424114100d9400c0100070a00e02005483e080d86050304062203116501c104ca104206001034045c1c0c030708003030402400700301c00c0600b002c01c0642071850500005401c509990f0010070542481800701c4000c00c4503d03160240303070400c403002d00c1c4c0100c40c12403c05503011008060080b94030039100090b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 301139136 1250 301137886 301137913
    0x130c06030c05040303120f0e160f060504180204090f0207021804020a1a0c0109032304152006040302011b0215060904020114030705030106200a02010e010e09011502 72
    0x44200749901c40118109000c1080824081c81141842858000c0d0004280031604c04240480b040170382e1250083c0d01c54803c3c12012070310404054083c0608090000c1034600c2c240f4020329a01c41c43c014540f10000380c80c6109800003107a0140d40250040c5c1805102002c40343d003000c07009401809040c0d00c200141c0c40e01c044100c101c0c1e80c070b041c09150042c0091401e10f0601c0e5021038140e90000c0840c01d441c00400c05030000b59401e10a42418074400e61f00c49140f4a110752290206442080d42c034580140300b00001c01110000e61401e140c1001e0b03904040d013101c140368a000d22144000c007034415050140d1420001096819882407a00d15020340c0a02468203610100700ea40e012042b6003d507a051440011900c28a01140a250b00520514011411566404001c1d44a4009032118008540048018801103800140007000440540071800310606018141990340e955500081d042c406130800154860344652a0061004000303407201c0036a50351600203c00c07501841d450003005000b210b8441900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 301140386 1250 301139136 301139141
    0x30506100c030c0b07020c090109020d050711210f0309150c251e060f05060402390706090306110a270306050903130602030c030a03020d0212130c0603 66
    0x100790b09075844040300380d03682d500e4030b0410001900200541c8200828a88541e580340642c50190205200144c0ca0b2401c0c14000346c195680509007009000c02070403481107022000503980c0750b038071805480c0780400c40007046491440c071400042e544030b400d0001c200900c04100150100340b2400da40070b8011299030300d9404078407500480e61521304000c2c034000c1c071202021420401c000c6141c02074000c20030b01cac02c0c0c1d042e41c1c84480030403001c1140c4054540410305090b8070948500d0360f0001d019107041d80b4003003541c205100303906e03006004440b5070401421010002590724082c03e1203005c242d0110381180f600c0340c00c0070300031902c1c502c81103c044d4140303850070051222100503900700350440e4440c10030558107201c18000412203840012514400c2000c00070100d0001d008950140b0f81501c040c40e580d03480081c800f03e031b9000b01e400104c15540100b0401c5800c0d20000111041d9070054580161540c0111010001a104d400748130550540d25a0500c00d403d6219008002c2052141980c0e14031142d891800342d05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 301141636 1250 301140386 301140407
    0x40f1101030b010c110a0b032502071503020c0f070801060f1e050904050309130e1606080703021602150406180302030307020105030916140a0f1419031203050610 71
    0x162000c4501c50000344110f002000481008242c8002c0da07071590752005c0070b40c0044420100641d240d40c10270800f0a1207124101d00000240302400500e03003015403020000c01d25540300c804255000600d4204210280020407400c840001619201540c03034050314042d00d407034054008011890b501c0012001d86101b07501c0b000c9440c0c44940300b022072600c010010320180c01042a900b0780020000c40e980781c3c0e02c14208920300ca00940001540d00f81100d01d0030328040b01c62900e01c2c1c1028410405204090308034038504c0e400000707450050b036a000c406459240a00448074000d4201800200c1503c001a4005c00307401921055075030440307025400c41508404410030f01c0065059002001010055481440119800302c1c000007114900701d104c0c44d072125042e4040e48550070035808903283d21034526007962420000c116074030501034044e042080c0f25140300380141103107201712846101342c5101000002c00720011904029003c204050268000d0b010340002c0b200c0b2840ba8403414240d51040c0c3c0204551030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 301142886 1250 301141636 301141639
    0x15190b0f010e0a09020301030c030b0105100e041e1e0e030a081f080d0206040510061a031308030a020d1b0203030a0b0f060a030b10020105070c03180b03040f1101030b 73
    0x4411161210041d152905581e5100740c100b03c244a003c204c0f02154001140210711410030354800d2840e6003404503081d0010b8120724801c0150a0b00c0d107040c554018030782d07422804200c6001a01c040c0003821035007516403a00700204900e04000c52604400c00d000140c40c424000c404007070203580a240c005940700e103d555640403300b07000a01145c0381c0301d11645070708410910400340645140d2600da903146480800c03160f040040e448441000104441404003503074031180317082c051145d1810607520359940c28082d06541d02c01407001c80002c0781203071003a00d5002c541da0042c0d5110356038113281c1d100703102950144680c0c84403141001d01003034026031108807850b04843c0a03805036080d61280c2285e40c01606d102c4009584c40310060007080c40710741c0c0e40300041400090a4600141c051458801e00c42d212101d02949c0081da4500010011520380110341e403032000b0b5140c9414481d0800c1200f4956000346c1035000b5500e81440070080000f0000681c820500c018020b5001c40b6072041c40d08011410740d104100002e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 301144136 1250 301142886 301142899
    0x80c060c060a05070909090605060a1703041a120103050f0c010f050d020304030c050f03040608090102030103020d02060c010603051e010f060b0409021810051902010203010b0a050d0e15190b 83
    0x1500021583c0d01450300b02c0789518080c0c00c0c643d40d0b0100c010a4403030ba21006d99100743d039001400320a00d03203540c4a6000b40310034010481030080007001182c0382d010b1703445400128526100901910040c080840b18102a03045400f0070558403820401d41d601d2000481c0c1d001d604c80c1181c04000d542c0102007110002001e0346d100c9107030020042091020b03400290048043c4200c22048c0070001e01e003802003001c100202401141c46900d04070004101c0c48016004c0c1080b64030400060001d030f210031445600d82030701501e5040e0b581540c940058018100c0b84e002401c3c0c2d01411503180b481007104001610a107280360001d00c540e603401204882150450f2180800c10039080004200220060b00680313024940745d41c1d660b0800100c0310115000b0035001903d000020000540035a0400321100035002c1804144001c41c1103604040ca811103520545240009101022403025140070b10341e04141c4000b018502a11201280c0200f40380700c205040d540031202c0003c0c229001118819841062000c11340107060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 301145386 1250 301144136 301144141
    0x17030702030c010c0809280f05060f03220302010603030311030f0118140a06030215031e100b210a0c0206040b090c100e030c01030c0c0209060a05041401080c060c06 72
    0x191002e00342c40c04e003140d4440c814064000d0340d584079000b0f2841d583d40c19422041c2c4000115201d2030b00c8104d904055050756042c0f609010369100d0a00361642001044031690b42c9444845903840180e5001c003c821850450300310790402c259041d001407003140d11907201800386200711181c00c9031a0204442c2c2c0c014004104004001203a4221802c034844506103000181d2030711900c0c8000c50358001150900a0f80d03032078101c02c1085082085014034101c1c41c01d6032907421401e0071144142280c03819414110042e001c480400c42e600100443c840040c200e10710b4050b520244031f61030f40228440c0f003411000e01c051020000320180024000c480380b03040c103613010b8015607a49546444070303142c010701080d10a202c5c0d15450155a16424000c840c081902d840d002e00581100d41010f181c20100d00d401d03410035081803100145a80c0218200310a203504a907a29483d80d038030404506224500c0d0f12895205003020145610405052400ca050719062010368202409442c01d001c8603105490008070303c1d60002c0300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 301146636 1250 301145386 301145389
    0x1c11040504080d02071a01060503010617070215010e0601090503030f042c0106050d1a0d02040b031f0905060f04080a0f090e010306020408251509031b17030702030c 72
    0x8100c1c0d12a00c1002d6031802c105000016000700d07004141e04803030018401c03059400c1c000f20240e201c0d005080c1841d0183c51076050880040c0648102101c1c85026408900031a410758001c3c0b00100e14002d140000c050a0b607959900d00d40e1111042c0d8403580813400141c00400da03810080300302c544240701100c01034905480c01080c03145070861950000941e55011070441181d13481101d4844c0207000c1e5640f0f580d1620001c81000d02124180c0d4012039a803181002d100c2416120481d500e00769940440380007440c2e01d010808030b0704280b01c6400d10301d1030b0060b81300ca020000c1619404058070501440449419070780d01010030080f0704003501e002d01100814400e0750800c0d0b11620001641c0d9000386400340f0082d07030715443d1000e001c0e030a81007182d8840d000b090510400b0300800140d064004610180c1d0f590034400642581550403500070400c0e1007550710307012040d8a01880260004540c80381c1948400441d0700c11264004005014403805070f82d4182803041ca0703d60000039100c4a0350001d0240c180c1c5080c2d0070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 301147886 1250 301146636 301146641
    0x70b070801051903023d030203190b010206011406120f07020f07030f060b030709020c0c130b01080609180604050c030d050a081f1211030f0a031202090f060a03020403021c1104 77
    0x698034912248180c81241150400c81a0100301c3d05051f04d000d6201d003410020741040c2c0c42c0d113480b1501e000c0e2522091900c80c0c1c1e0300150080c115542d1403010481501040d020800394400e482e03a840c401000401400881e032208100b051203456160f00307491a02c80542c550585641c00f500c0043c3c81c801c14001d8440c08a030841c0d100060281004045036030350740c4d5030340c0b1200a981040b09868001c0e045803a01002900f002b81c030002041c01c0c440c2c410080842d28030000303003c00d078020b84030900420320f00000a100f10329145800c5c8143c51032904940007890300d490000d640e4000000784c3e6000f40600019150940d010b5030550718460590703200c00c5002c1d07448001061608009040d4040600a048800611a40420903504846009402101001e002c9105142c80c2600c081d039030354115800520018082a4400b014807802c45a5800141e44d6800d94000642c2e44008002150382c008030010380440d115070154002c0049034800d440c400e52a425181c025801190002e002501c400c004280701e003003d24165 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 301149136 1250 301147886 301147939
    0x50c03180a0302030d0c0606050402030f0a1d1b041b02030412080d050106050304140f1b0d1403041404020a0903020108040336053003070b07080105190302 68
    0x40d1041d07110396a01d40001e4500751450710603c0c0820a65131a1006008460088001400d01614154614201a18050041e5100402c848000d036552505203800c1c0310900d001d8400240800116031003064400403d444a10b000208288203e26090600b0401d103201404140410308980255060900c2c00140e0044401d402d282110107100400c4201540451482420701030429a42c4003900c030300d000d19040c0b1040380c1407209d00d005036101d41074812103404002141213507140c2c2000c040304050056400325584401940e001400e60040300e110650340c0c080040a08200ea100030340c00414180c040c81400224405e8054480000b60020b1007800554080c204841d00300b0b210b440c02611841d10a43c03200320641d22010110310044184d0004183c29203800145009850100c07440a4541c1120189106d1500701c41002200d4100e08100803124200910644d01500e03000310780b0350900d01d0b00446c0101198024020103120b4403d001c81c080861810643e5135058a0b8040c0404215036040c0c99030503008142d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 301150386 1250 301149136 301149139
    0xa0308030a0603081204150509030a0315031709010207150c080c1f020405100203040e01150504080105190509031c0b0d02060c0106080c0111060a02090105090303031e0601050c0318 79
    0x44680000020301c252008003c17000074020039103042e04051030038954000d81c00c00100c030010300380303000d00070054000b00480c0d001d002d290030005140b1070007000c146d82e220b0302607002820319040101c00100c0c48404800030210094260300703035002c10742c0780c009150201015074000c03000112410411400a81d409009100300844001203c0e820f0510032080261074203048405c079003807a0042010406818101e010319003c074807500245041900748148107031140b6051050001214a99001912246c010400c41e409000050000c0c4128a40a030031004201c200f04400307641e19180100044514030080240d82105501800685071700c2c04500d4454007030702502044e15409038980e00c1610050761403074000c10300040c1101c00840d00750700d0294200d05194024004606106034403411644281c80490700319404030034a0401600d40e9005401218a4010701d101c0303a0b0544400002e00c08026a10320500c0b4012103540504e1806a56074401180c65022341000b28034645d205100c3d200545440317414090441d43e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 301151636 1250 301150386 301150391
    0x30a1707140d0f03050c0a05030604200d0504021903050322080f010504110103050c040b03090304030b130b07110c01031812090602010e030702090f1902031519050a0308030a 76
    0x691a41d4144014601c41102040c8401c1c160b0007216010b009007580212040001801c1645c0410040e10b41e20000300414412507582500e902c49206014a00100131000f6040039111226203120100814040c0c6040e03108080d000104541c01c0d04012940054a40c410061421301d905003804007032007610340c1d4100042041421010400d200d00704003041410600070300114842c2440c0c1082c0700b141c2143d04540d4101400c00741007181c4110240200c0b0100c80074a032055940c0e13035510320100e0541c001c5420082c599110700c0240200030681000c10960306005019a107039a03201d80b04156070030001003103002d0664110700354101c1c442d800395105210b60f50a0101101d84100f2a560b15044041802d0740c110100d48210390a01040348d09110300e07401604441e005500c1d007074803900019805500101074441007850f0b100001c242075209010072141d4440d01350250b441c2d0400c0e400e21000044448405c6000302c0200c208094220418415070040b0342d00500f080d40072500f503403900007170380d440109800e0007241c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 301152886 1250 301151636 301151663
    0x60b0609360a09030915081602070807120203010506010c0308010510050f0f0c0d0c0f140f0706030608010b06030103170918040b070905030319030c0311040f03020906030a1707 77
    0x580d860101c07445407821000c0002d4904480c98044c10600654102c0f040031141c000310342c00295082581039401020381800701e00400f04240080745040404d80101686008102001645400203814404024400ca0013400641c1c3c0303900046520040ca070401800040030f003401008030b410301d034a0002c04018649400c500c0d200d24182d10316000e601098500c2a640000108907882c1481408010403c82c07440c81d200012040c95140c034407501d841c0503400b070041500981145e01001c0200050304511b45040c09850303081e9540d11019004115520071965603500780340184440386490421070b4180c0c0e5004620701c0441c031200c40c0e40340c00e50304040c00081d00640b409100403008000329500c103104d14450308250030b462500f2580200910a103610841c080c5d030060001c2c800b8480403101b80782d002d000f140340029110440940450240c6044248160182000140426039140c50395428064034001c2ea2600c1c0c00303494010925507580100d42014102c0a290301013007040139118402452080e0080c4c180c3c10000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 301154136 1250 301152886 301152979
    0x12180705150904140103150b010912050f160617040501060f0e090d0503070f1d04021305101814061207020d020606010f020a170c0d0c060b0609 63
    0x1400d1000da0003822210105901074240f82500400400c007098138100401d951640d40d0340c4142c1840c541100000c0f544490001e086640318482d4000140751190203d10500c0260a00a0300c80803503041c601320b140241d00384e080801292406920132105941c1c0c1d400f840c114403c000705646200a807081b5059500c3da0400a0b040003000d5401e400380140c0d0310300900d82e0500500251800901700c44000510100740200844281c12800c0780202506601b081c00d0441d9240e104041c0c80b03081c0320310196119101040d80c0c1a482c074908568410703180207486d800012980364134190351500e02d0060b0b184130140c0e031a00511041324000b2040c60144800703003031181411481c0039201c00c4142c0403548040103034400400481e03019410030640386c00040a003800f482c1d00d000080d0080d11404000400350501c071103200341c58428607080b0201c406082c1c031308041d18080d68480c40010082044501c098070900d007003095035071003854480c0403104651002002000c40c5010100c01c0041803c4280d12102c03224444120072010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 301155386 1250 301154136 301154149
    0x618150324010801110301050f2101090204050907050a1e0f0b070b06040b0a05060f070506040318062c0d0512091c020d0605040c031a0109050c12180705 67
    0x16214105001a160500660450540140d01074000f907810000940100100c92080303906694040d40d51640312914040412002c0c1410ba0001c80055800c000503500c5504c19407001281e180308030340c103008544840d4000c5503a07800034042c5a600400000d02080070b01da44441c0318080c0d00121300484000340d07442048600c002e8640d07000c1d8000501c0000e10307400708056100701346da01450441303042150300305507008031700348106074080c5c85d0244800044001c80392401c001600c814662040407106280307014603004091910312a02c00e1720f0071095000100b03460b4011001106078107101c40141e8881c07080f0419a60718101c040881542210311030110342c02203101400b410420626041105035240c5480301440042c5006030700c2003010007041106040107036074260320b0b4440c81e5045580440c55444505106c40c0010b120b0340300828410305140652581501303541d0850413213480441c01c000740c0e90f40c20f200b411584960f110500942c3c2500b00000c8502c0c02484500d15800e0380402162109a104d10202d03c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 301156636 1250 301155386 301155403
    0x15030b040f03030f1a0f03010612060c091d041b0e070305010f05010e13051b160302012714030c03040906090b010e0a27110306010306080606181503 65
    0x94411880c4203107018190940190703600c9489801003044a1102424128a1203040039840d0b40f01c0c4100e07417250a80d59801750498400b40c80b101d510f000c140b107480d2510034010001680040007252700860006140400103607004c280c0010800340841d1541d49075500c40b00700004001202c18101e40070750103d41c00d107082c031900c0d220f10140c6e1000120795042c4032500c802107000b580181e0401c2a8425050040c0e00d50907000070055400d41c6000c02e103a100c030881a455080900608095284089112440061070303840303e0000c80c1c06900200451101c1d032194030360240314640c16515040351740034007900086091018640400000058905110303684044e01d0843d8403540c0950100e40d200c00741800114a58803588114000909294039134240c0306000c20f02001c034911940f0310a610710350303010903841b80300c0b28201440d00c08207504100d500c9000101d500d4030340065620a00013072818101007559500003807094081c060040100c090601d841c000c1540812008120007005591400b00c1402501c08118014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 301157886 1250 301156636 301156643
    0x109031a061c0302010b0a15210609020f1207180312110303090a170c0715020a050319030e060603030f0f121018020322050a0215030907060c0506060415030b04 70
    0x411b8000242048071051158004503003442d05500010f8134036400c04245088034410001c0c900000309080319000040c00c0e250700030448a8000908130001c1c0c0c009500500800c2d103910004005900e031030340c0440d9409200d000898080c00c841c80300344046040101e070344010040a05c1e12642e0000519040341c155007068031030070100ea010041b40b1007009040140d04814503c0e40b40d082d418050b2196200d0b54490651147c821092180344a1a9242e8401e20416040681000c12203645910341c0f00728844141e003c00300400040e10300008240100008206140902d134020011402d10300d102c00b01c0d2080364081c2e0b066201101e8104510000300f03141c204000c0c411400c2d21b980340f209a1030055120a03040702d100341d01d00301c60320410401c403d80411038960702032088032159000030040b007460103d107002f40201d0003940c8540c9244e200401030f00040003d6210f203000109548a8581d2a40306aa0706221b050005115800900004040d400c1660086400d410911800100f040e030300e0325601d004000644050703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 301159136 1250 301157886 301157891
    0x40e01021b1501170a050307120e0d1203050c130b0909061c032f100e010605010206010524030408180a0b091519090905060109031a061c030201 63
    0x140040075040140d0070640341c400c03014105908001030069440b075814080c2c14844032410600c884450010044000d2059100007165a40c281c81e05004101e03002c4a240700d0001480141500002c1c1001c03030342c4040443d4000801505220102025006000014041410b902d414400864450420885e4034018040000165914520141031084441006042c140114034640d68040c0145c00b0803140111280c0500d0000b540c1108a080110004041100b001c1303189107269403110742607404182d880f00750844030303003c00c861901941d03801d007030300c50500c02c440c050b0300080c004000500b802012220b60300300040d204c2405c81c0c800080040290403d4030166810000461050320072402c1746003070b9581074000c60710384940624040d00c905181c854241c903a07004400698032240e21165a0081c0d49043d940158480700115403d1300082c00d00c1c801d8490920310070b09280c0400c1c0a54040d06450003540d80042401c8802c0c40d0740b054240319603101402058222842e10011400300c00884c42542200d41b003a80007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 301160386 1250 301159136 301159147
    0x6060314010509010305060106030506031005070305162307020a0803030721290f1e13051b1305030105040b0103021009151d0306090723010e090405010b040e0102 71
    0x16000c0c08201604003901600001006101180300090b441d81121820300e0085407654035100840e040c000f044072080711f01030404081c0f241494240e08414451018003441110414070b169040380c0851922400c2c0c41c2403003500d008aa0f005040b2402450000d0000d481100820341d1034540d14a140d00c121480000035174545e0f005071007000200c800703618641d0700320000d000311000c000c81c0c24402003020003000040c00c0c8222034082c1d561114512550030031401801d1101e0003200380180b6480f48041d01c41640b28109030140e4001d070816521419000340c00340b41584040710044555000258000e69200f0388081403114000780741d680900030107224522801292f4100d51545c8103012004502c0140b000600c058075000380302586150134003900c940c1692420b850201021000381103108499500c254240c000c9401f00107030342400107140030403075113038160740060030500c48071141a6a20107110680019100c0116a2032440c103070078410f81160144000040030a410300005086410700614100c5c1a50013151 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 301161636 1250 301160386 301160411
    0x1b0e06070506090609250e0a0912030b01110312040201270902180f13110405030307051e122209021b06010f18050903040e040b010e100e0415020d060603 67
    0xf224054806e03d20143c071512640541d03281416602c1c0101e41400c00c0400001d07a88041680008071600e400c2404007107616107012000b00902003040d039042c0811034040d02e40c4804000001119107001ca004409403483c0caa59004551040060340400c4112000c03407004101116900391f61030003815142c00050361104c8918280c041100d0b01d0031320070b104080c45824540309884031088100c0c501c411002c0000d505074020201c18441c051504071a030144004501e000410400051111881d1540140c0c2c40741e103d01405030540d43e0548d0030341c0c0c10b5043c1c4240420f5140108503000c5070310b5803046045151250b40c076080c0d07210480c0c0246544944408103081c03210142c0300d040c0190740c05007501000d00e5101d68184000d0503120f0403c0c500509885698000145040d002442035030050840c3c20500d08580c1001e040207809003000303008165504001d003000c900301070f02a02c416030407542540744034041a5902c1d16041e00210201c100c41c000950200881954a5205d104400103040c090b140003940111080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 301162886 1250 301161636 301161643
    0x7020606090106051911122b06060915051b060a06090e21040e180c090f0406020304020a03170d1d03090913150902090603011b0e06070506090609 64
    0x7071040c1d0922004108164040c15017041050850031542099800c032107440f200d4a141494070841e00b421110b011030214aa01c440340020043c1c1c1c004201d2400d418031500f640801116498400c02e00400d540718004c02025140b5260010000c0282c200303642881800100341c50740c18041801600c06400110800c03400740b616104640c0074007031200c401c01003102d000a160360b4884201440c6800154403c103840c10f0143c102040b50050145e0400b004030f0342c2402d840c60394110045a541d05140e0160a0650b0058100488464170a22080c0704c00c000a0f00c550300c80c1ca0003903201502c140d070841c1c844a008001314400400c9441c1c440000c0900941e43c848080c00c00e021612015400c0c10508100e1031342101e50075002041d58160b440c11a001c070400e481e4030b12042402d1103414401031000d0304588072402004132a40c41400294000c0d1200c000c159641070030103088645404001e9240904214020b042a200d26000320103400d02601d154641421601c0d124a081800c6440e002e1592240701000551042170 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 301164136 1250 301162886 301162889
    0x60114010806100327021206010305061519060807090e06091305191101020f010b06040e07170703060501031a010c14070e0405010e010b06120c03071e080403030c050403021309050114070206060901 86
    0x71f00940455415559442e4030f569001d00980000e288513070b640c007555612558203240c1c522146010020140d500e803000b600c0031324111a00000714003040c200040f0359014140d114460080180390340c0c002d54840c10144841e0030f00407425503081c806c03580705081001e40c20300401c001d00e01804c501e09680903400002172810380d00524402c0d440c0d062401c034031403c3c0c50b408240c40950f0480150340600d6500c0c42812980c03801c0c0d510340d10404041207010300494503055400007069070802c1c0d80500116000c0b1f0742c40a00951358040c02400200e80d80c2540d03002c6a040d110186002a45009903010709644020070b0110800a031800c3e40c0e03995441001d00d0003400240b1a84803e6907040d00c8960030808850070320310500d0401004481004030000010714031a03c11203060503443c00324149001140b0a114005000c940211000c8010a01d440c140c0d401c29800381054400300ca900800480c82c280c03880c94071402804502c44225000c0d0f480c3c12540140701e518401840c4201010350041c05680b40140402c600c05030107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 301165386 1250 301164136 301164169
    0x52d0313020906120604021c0f0c09061d1303030e0a0311160803120a0b0607050102181c0609060212010803070c0b090a090c0c020604080d0206011401080610032702 72
    0x50060b0080c1300340c8041801c13a4041c3d0121442d0711403140340e01d0402c00300f0104403001018504c0c46070b01c900802c1049041102920003c010810185442da9000e6601858080038900b8660b4003c0004525002a040c2e000031140f0a1401094051400c542c980c034000085c4800c5001c502c25109001c01840d0401880810504030345c0101800d030b14002000703480c4c0c03040d882c0074030f1280795002c002105219503410500440341c001e0301c05951018142031190013074014036101040d010484004002500d0152030650010010062400c01c40181d0743c3ca01b4000c190031070040360403980910210003a01a111917050080150801855941d16a86400d442c0358056400c001d1904e902800303070701e4072521102245020340710208000a1034801459090f104000f150000942c007440006000c00d10f13050115a114481c40982c007292883d90f2075802012010100c0e074040e0340010700b90400a2002d2904124050f801e10141c10300152010040708110390f517403e18485142401003403404901103052900000c400300c001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 301166636 1250 301165386 301165399
    0x8070b0a0314070e010c0503120403030207060b011e03020c010e10140a060e0a11070219050a0f290d1a0108071d061804090c03170a052d0313020906 65
    0x40c10300001e0b21066101130102e042102001201040103410001c480b10001c16101e50f142601d0603290040c003035400140d08070380762410003510103c254000d0840f245003c40030b401c140e580740003401c000c0340290400810f294066484001c98014240c0500000790300001c807a03000f150640c101c0e0440414a4009803008080c285401c10030031070601c54801d002d0f003000824101241c05110843c0c1c500007401980000f030f60101d06522100c01c2c1a180c4076004c81150030030f4a40803001e0b503450402c20501c10740361051031400441248448500c020301120540280c45c488001418890a0708030308044402000443e06580207180982070690f8000e07155561142040c40c0000404516a922044e806006549180603100100d031058030310079244200b101036100a04204003d04182c101174440b03500d203100969106440103040496020078500b1243c3e905140d850700340c0340080405000c6414141071003210901c00444514201c0307101c654000b14024010145e070462465294010442c51100181c4190f00c01c80c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 301167886 1250 301166636 301166641
    0x302030f070b07080f0405060d0b0906011b02190305100501031e02010f080901020405040905060402040f0b061b0c12100b030309011d1503100312020a02010912020a08070b0a0314 78
    0xb0880c8003140d071600d0744450301e540c58152485001c0d6aa01441c0c00c2180d03c5400031030142c400340e020740c0c00351002c04002c80300b40380d4a8030f80100566800618151101c00001e8198480f03000d820001e50002d0850841c1c000000540d5a9880711410003c070304003000445a00c420040041c0200c40d610210101c21215801c00740105550010705803243c034405110612403000000b07403240c1000c0d1b058a00503d0064000d0044c07240b10f16100e5210070048030220704c518504a201c038410303812031084a803500800f410f40e40c904141c900040c440783c10a10701440c49481211170103042030321001003040d0926000070050840d0850f56101e0420340c0d4494540501035481882045c05030382c0d10000328102c401c03a11402c0d440d40b0704003002041c0c00e4245c04069840584000042c401505108480c160403680241c2072120142100c040c220b13243c0340d88000103070004440c20800c5c050b240140307000c1c544480c401402004000d5a07045154107141065201c07001109010034513501c041d4050040309008000416103d14a2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 301169136 1250 301167886 301167899
    0x7050607140a08090f010e0a050f011406130b0616060506010c080a0f0306081213090203150f0f03010603030f090605030f1b0d1109010e04020c0d1805190302030f07 72
    0x900651681804000380c0e03001003803101400b8010556000d09005c028064140007803106962611354403c1158130f88150310a5203a950410710a0886200800005e41c1c45a01c0c3d5004000c220803941a50300c04403545c0745260381c1c0c5569842c0080003040c03600c174620704181c030b131030305180d402c849008244906210783c04031060700040c0c103202103d070f46250030b0400305a03000d40d60008a0040ca9181c100b40380320310aa030b0a580b144a075400c090002c22401030014100c5d2512504200c040e4001035603031989100c0520b08940081c54800d80c0c010420801800e08a010042c107400a42910090f83c0300303401054407008034090341c5601c01c43c2c0740b002d440c2d9070034030a00c1e60034810348075411104010841c28000781c040181c05031704002c1c1405c95141c949074080c2400040a42e01c4112226031003c00400d020946600c09558542098020f44020064940203884100c8841800351500b010380201d2170348100141b50041242d54600c0091414040030303d00f4001e0013820361040c1442e1404c20702c1c03070f20710356407241101f0890f4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 301170386 1250 301169136 301169177
    0xf0b0721050a0b0a1d1014010e1302030f010f1401120e150906090c0406030b0f0c0412030504090b030102030412050f0d39020a14190807050607 63
    0x900c4004400180a5850700c416400030000c3c1c014890f48281e018000240d0000780302050700300703800c0a003c4001c454542000e08100080ca0340304d04035441c480c10501079020b40c007400b1b5961000c0c1d0007411081030f08408030f40b8034040364400ca6109d048800018010700060712a0b9001c1c1d006044010b0040c2c122545540020b45141d81d5040a5480c0ca526030b00000c05580c01031080700c601c0140c550016000341008050b0399100d1b4000c540d80c0443d4480c0c102004c81c0da290a0042204407600300d05d102c086d5841d807220400c60310314001d020041c21750b410440001e00880340f0708a880114025940c0c40d448505020303040c0140e802d0307100680c0c401e078014010b100105418000c102601a5642425a0389113510f1a294103240140b0744041c803407070f25040d01c84807942d5850030040383c91098081030304d08284004082e16103404c1643c00c101e0050703100000001c00a110f841204500624181c105c5440140c4200311068a000113402115000d0011400d40c08024013002605e070440a0b508103030740b001c4240e020003000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 301171636 1250 301170386 301170437
    0x30611130b070c291b0a030c050d08160f030b120304031502090f01050a1205010627030309060f05040b03040f021c0b040b04060209150901170105030303041103190f0b07 74
    0x8050005080480c0c3c00944402081c0c44008170a8590b0343c03600d420041d240c0302652405443c00d01a03c0c2c0f80d0341c202440303100500d2190030f200c10141d0510f00541e604030f403800d0b21204004185a9075002c14015039a8000c4140d400415843c000c550b158103501d84405800003a4104046480c010301140d0b903556035804001c04650702c28a401034403a0341e808411a01880e0382800c5c103c45030720701000800c0040c0d105e4110f003807142c0700b880e0710809000307500413251195a66110103400100141410f02840380305424440300d00710f0500d4600d09140e2510803442d11980151011a0206082140071046003003914100001150803400003c01d100b0948603c000c185004000600d100c03204030010301000900d5040e242010b8003d0115018045444807235020383d07100100503404038580f9030186080002030713a80241600d201501540c2180c540b540c13008929203684203c3d543c580101c103182c80a2540302038811040b1030041c0310081112500d400c0c40b940040000e01a1742c1000310304d04100025001001c9445d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 301172886 1250 301171636 301171709
    0x6060f0103051b070b011a070506040212030d02030f0709050d08070b0a111b12091507080708030a06090f020f12061f020105090705031501030611130b070c 68
    0x1d02c640e140c040d80c1001c002c3c000340d00c961020300801d06106011030b045031181a0b6948000c00120001c00040d048980c7c025807070000e0080d80058001001400d1080180440c080700f20304413820301c0020400d0b2000e0ba001124202c3c1c2c050220002c2100a41e84001d0729001018107035801950700744a03880c1c2c221140300f000405001e80344d03602c01140c40c80c01c0d1540030600c1034521015940e1110548583c19034460417404200c2500d2180f5003038401d0104411044500c5800e000304208001c0d084101113080c0c54000c18000e840c0d0f400c05002d89000306e24008001d40c895221148006911800c0004007811118492200a8003510502c1032070440a802c00440e044070a00c2240c406d5907548580010f401582c811100302c0c2d441c03034410105d402e1150150401402030403d5005c2d07442c50342e00c400a15a6a460050703110b4004d87c0240c3c01000800c525500080080520300d0303100c0d14008000c900e1114945c0c4a03409059948030000ea85800d110300000f02901030000d41441d0f50b9030520050341480802005401003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 301174136 1250 301172886 301172891
    0x806030607270e090c01112802040203011d0906070509010c020a2c180a14010906090b0f0906060a14040f06030f0b010b03520f0206060f0103 62
    0x60b824050b41056048003501d228402c0c0c0c142d02d48070302da003001003007058420300d65520036200e2100441d8007035800c10072400300460040c0349468201010a004201c82c1001800000800304008050f8890340010342c080d082800804000004030b4100814201c00104680170a42080052040d15640102181c610356000d182140c02c0140e40d000180011004d03500240074049032000f0400c0081c009070105880e0008101c504a030380c1e842c0900c0608070340d2000361021a0390845154000040c07141d150076089031f01124000140b9641d955115001c0715003420040d14400b504804000540c0320507440c5952041400e0090101802c01038041501c0748058004c1c0c488001e03400c040d0f10003649441c0c0c000a440c0c140a1018803d40d9620709114480a5806400f42c2d6140751450000c540b0310407400c201c2c1e00502c0240418024441034014503c41040380c0c5046004c070303440082065010461039820380c81c000008102c45404280d42c040e02070503c8041041c0b95040d0b401080c100b02e41c0341e581e00000c80591000382000b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 301175386 1250 301174136 301174157
    0x708030103121b211d0108070513030f170702011d04110d0903140c060601051803030a02010c030513080301091a090c07111c0f030504170109120806030607 68
    0x5884540441014042c4012080c1a400901454985520403003070000c80744101d108006004940444030014142e40c0d0580244074880954070888183d5848023840ca0290309250002a05c9590b681d096402a9102c80b100012072003408810000c902e16003003403003a440e1405c9034a0740085c00349010b583d41f07411016100c030b200c118181c03542d0b04240c905e50402002281c1d19102c0d911a90001d1480d00c40541c0013401404094030151f40d81d6088501d0700c1c180d64000c2015965070001110319038030224241401d50900d00b51950203407805c2000e480711210580000c60101d0402c1802411200001c0940103103603103484482c0086031104003100d055402000e0040b4125081307a01d0000344485100d0078680250214007080011046c105c007611007544180040348100320440f041109801d0000412400c010515040c403000403030034100300c00760500c2401c105050130303950005001583c40c101d2040880d40d444405010400200061070880071040f4100309101d0b0528a020a0359060b00034040001d02028490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 301176636 1250 301175386 301175423
    0xb0402120a030215090601060503010e090304030609120305100f050415081501061106071b21110c0a08061303021903050d0c0e0114070f081603020607050708030103 72
    0x2000003a420090407101807a801d0b1400950b01c05040810341240c0107000301040c1c0e40e0401098840c100d400302c2d5105401c41e401c20030510381d02000500507082502c402c001c00000510340703001e444000d5010306200e00f044441000007609640009059030414004e82c2c80512142d070544941c44142ea20507980014104542e04a0741030041040d008560a441858030920352006d42900e95410380f4a00d5603105445100c0e020400d594490030744110022883c8604461801c4544d06041e10360703a40100440b81140f501c550600c1c0d1a481c0d04804100012107007681e040700d40800704400500c03031009542010303c9600e0702c5102500c840014040064418500076400c0c1818820414850300080c20390a41d040001c052a01400319801b0608a003003440c01e040882c030f5400d026a2106800a0060319910011520884030b29071942c81242d0848951924000a8011406200c090103194035201c04d004004407413410041d16060b00104024104181007084900050780310301681c5c11254007400d5040c1c034a44185 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 301177886 1250 301176636 301176649
    0x9020916030605090907180507020a0803061f03150b0702100e030a050d0e0907081e1f0305010204030c0f2709120306090e0d210912030e010f02070f0b0402 68
    0x5100c950700808913800e0250415001c1492411101d50811000c802e2031000440416a40100c90100244c2c00c0303a0381c01004290180011644040020a41011790240201e10000e0140d0101440000b81c0e84000307030765107030040c5900513028100800100b1300708070b0b456002401040e480c817812001c0100080440e83d035620100000c0081f650b02c94140c5a040520040003050b1000100070148111425004070f10313241d01415546024a00141c40e0304100c0d880040b040001507009400c181d4801c2e103a08034401784290441303905020b14400c1001507030b114550305050f0389032902a00403070f603000030700307001041000c6c126039014002101040f480c40c40c465642c2880c400403d602d020107440741c2071011600b00c00307030341c564171410541e404002c042003805510707284142d0301c15044030a47c1c08154038480403001e540b00b020302c40c03858010118011401b400d00b80c0e1454607035002c3c00030340d5011030b845889648004000b070085800801030b200c070071401c104103034442092038101c8110103450040380101040540d107545 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 301179136 1250 301177886 301177889
    0x60903010b031c0801050603070c0f020a120c1a0306030601090f02040308040314070e07020d1b050f06040b010602060403051b1213030506090606090420030d0806030c0301090209160306 81
    0x8059400025006004000f00c240c4640482e001070a4080082058648001524050000d030b0f901c2e400540895038424111210120f02617a00c601c4280000440d02d00821960810f01c6c0b2440b00060f40c86c0c6452150201d140c0d2283c00400041c00920801c0840d4800107001c50445807030b160701107520f00d04c1c0f5403000003d01c100d4001400c44c08001501009004020070390340d401a50380000c41b1442540c9240d2140c1c4000251403450040e0886400b40c800c0c548510128024203400603030a00361104207650342880c00150500b02002c9800c824200828420200c141c0d5004104a0010f0490b031f1410755001403151041006041d0000c0b40010180071140c4108030041d110f071168014560b4039070303110701c02c1300030001a40b108441e03a20400300061048a4081480d41c087c0c640600010751545659a503441084109114442e0a0f00c24104610031a60200081c10080c0115200d0078000d0800c403051505000c02c1c29125030007a814010740c800141c03601c074000d652199a0912240320003103204000c5002e450207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 301180386 1250 301179136 301179139
    0xc020d06060305070f05010f021b06071b06030509100c0207032009010605040f08120415140307181e03110402090d110a0617010603020703050c060a050115021506060903010b 76
    0x4d0480124072107a11860703840590740c090300d0390380c038101e0a00f100f00c0e80c641e40d40c2c180840c170130b801800b550000e0910b0300181001d14410b0108012000340c0c440455104006030b0b20400001c0d4070b84003030000a07a070520082c2d0501e00702d9001400b40b0f66034004080d598000c0780c03100505940b1404c5075801e00000680c0c0c200433107070008045040550303403100010101d401c035000701c2c8400017610707000103040d080000e440e5100405114025040074a03101d44a1601501c80843c802485107011b02000307800424001140300d210f040e15284440403c15030204040e070a10307005014070350a021040012800e81e1242c803022243e002aa415420b040800450040c1c01003075039040d0040c180303c182d541000440c41a00d00071f20403d032140481240d541508a60360224001c089002d9a0800c0052101c03a201ea0020403815000341005407603c2c1100c40d006191034011078040351402c2c0e0700c40c0144079040030500f101912812520040c4054041d008040d141e151740500718501c40c100004941d42192800e40140d81950030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 301181636 1250 301180386 301180393
    0x1062c0d02040902030d0e090a0b0d110102011404150c0e2808030a110105091603030e010315031101022b08061807020607020115060f050901120203180c03030702010c020d06060305 79
    0x4100000c1c007d0009890b0003485080c509001803402c1295100c1c905c0c3c41d07040100b51000820b01a250810741082401c541811075407112410340d03080d01c000c09020700442c4a6500341c82c085d2140c1055404840c0380003419400c000c120111402d50796285102050350b1201241000c1c10612a051607425026544e44400700740c2c000441c0411080d82c10038201200005400004c3c03046580b600c18213612400c0c0580f080c41d800300011014004a071007000c420007007503c10f040001d0b040f4911242e840c1c1803001507004540181c0070700d5007980319590511540205088a05180c034540003114200303155404800f514004000f078400010b0304a6550a09c0200640700c07018031b240301801c295000030f4a40308100c4d0098050360800e20781c034154250400c00d9400300c4001e81e03248854200301c0c0d1821640c0d41d0000400c0b45c104400c11440e010f44502c0307032004502070404510103c941108103814903040111000c4103070300c07a8100348a80b00150740c00c039007010000d07541240d21088403003c1e440d006000f032210350001fa10920 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 301182886 1250 301181636 301181653
    0x50108010c080901060f0e150604090e010c0903021e0d02090408070c0605040305030406030c03200307031419020703020f030324041e0e0705060d0501062c0d0204090203 74
    0x641944910095885955120b0807543c070101c0310340c241d4925228081c814400c1d4541001150301203007049400071580a0781202c2c99100c1da00150203a0826048032440d0b90741c520146891030b4003480388124041e0b460510303102d56403035900014008110340c865283c0308410040d925a1032f40d19102542503650f07000b030268000d82002c2c00e00204c5a0000320b030072101d0324400480450954000c1e01690105ca6210300190b03d0319040c01c1045014044406070f01c1c4c1803540f140941c12072001d06d50707002c0380c120011804141c0c49140c81040142561903c00003811603004e00c1303090141e0344080007129004c3c6140040c026a03904003c1c90200d14100c16a810344119000100a100c1d00140902c803d401c5280750810029038101401c0400040311804204184a01000e8603807403100c02c2c85d6008484600301e0003064585046d85e400106e031386a03014614059010b0781d184010702c001c80e000f411030031025030385105e00b1840003658080c8041c4001da08203524840d04102d0f404000710b641d0743e00b102d14041ea01409179040b66 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 301184136 1250 301182886 301182899
    0x120102040b0711090103171b030d0e060a0903090308071e05100b010f05030f04020f0604080618031c0b0d170711120d1209060e0f010b06040f03060509100501 69
    0x140c02081c400c50b060f00003640b00920614020714864160381d000780c40c41c0f002d03031136060b403804031940b182500e490322036009610070996078001e0020700490342010f034000c01e4861044100c80e0500000804411150b8640703400540441c1c0e100365000c06680d0300a208680d03c19060a06680002c1881c1d001510840100320310703400c204021500901215000c5024007010b10504019120205540303407007800100288009075440c80300846181d00180064040007640c0202004220641c1c000d810842e410342c802c40601025405050140c0341c8640c0c40d001441c10104410040d104081ca10304903e540584c640710303200c2e00b42d95840302e0b1801255000041a4102d0004c103042c2d00e6a0b0020b90058070056400c40034030016082c41802061201c0d000000391a0401d00144d06950b0710031a0f04050803010350700c08401c40010100c2c0b0440c0c0c10364010000408210415803411401c0d5a40d418030680590f200307000800101c200c64542006584d80304078080b509554284215240103100081150070030b080c4000000e46 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 301185386 1250 301184136 301184159
    0x1201020d0c0f0f0206073c020f0f0f0604080d0b0303071202160e180f03120103150c0e0112090605070f1206080307061104090e070f06020c030703020f12010204 70
    0x5082c0181c076000c00d0005403c005030303201c5804035600d202003056241a00381c0506112008454811240c9400b0080101942c4000600f0035801c203502c0075902c46d40100031461010031665620001403c014074144241141c0c2c0383e01d0ba000a08003c2000740040b40030610410181c0001c81464400f904480d12588141410312200f040c2c01c09040260080c880f80c012003198010010003070f00d06200314000e83d5222440d0081920303094103540f0351540030304800b240201da010300040c40c504a008405954550560400055260803001014412454071062008030b5811607100c00c00728000b402c1088450f65403014003005030192000080940340361108101c011a00315066418008481d5905a01c2441310003010080340e0283c05143c00136801840b003200084d03083c0d003003203083c1c007441e800080c2081e40e15042f540c2030318410210551f403504050001c1c488454443d05840040c0030620007048844041004261035800307502019020f0450200341d50b00b2512410155951f404114000f150760751381c0d0b0080d404a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 301186636 1250 301185386 301185407
    0x6090312040c151d0402090d0b06010c2a0e0702060f15030f01050906090307020307030206070807050f030a0e010e010806090406390302040e0f0907180207021306060e1201020d0c 78
    0x4c00108644881c1080c200781c4213803529181c1c0030740000d50b120101e40b034184c5000c01c0180b0850400010003900c2d40007130780761a00184050002c4940360031201c418248200448041c2d041200199521010000c025600041c0349800c4080e1025566107a01c40741c40b4079592111101c0707150b8240c82209444c0b9001c1105502a61056000c0f8081d10640c1d01da020304d107600e03441032810103545030b8007010050016192410040c514684100c00c1c0c1483c05155540d218240007519801d0b25258101203030941840350002c0c4241c1981c4001d00c4c19401e0320140700c0001c2c00e038043c0507041a0250b0070800000703082250543c082a40900000c03400d0301800d1034030107403024102ca00c5c0c0180041482c0c1a20b0449864002c2c001e03142a903103190700d141e01e240c1e40d0041002c4400b5008213a10068821424006103c2411840d8600418004031000d0fa840c141360042c171150029032010841241c1c5414000c1220303a60010700c069260204a0f039484103c0054591b02d8060b000c2d69041c02a44c520b808116250103800030b40ae0340317 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 301187886 1250 301186636 301186667
    0x180b10090216030e0603240609040615080112020607030c031413030218040b010b03070c1a01031e0302030d1a041409070801141503031201030303021b06090312040c15 73
    0x1c04c03002624050292600007512021014480301100b04048009510b024011090107010541828480310000c0d0685005134041d0b0305880c04592202583c95119480c1405840c550600344184200d950220b0345512030032034040c04100d00e00100b074040612803803061403a02c50007241d00781c846242e1049204506001d00c800c81c80b5041c0360f8240d0145c045042d503c1803007030b070b0401d0890400343e190002401255000410400400c940f41d11200001402c042049448410b09034104015604500c0e0880254212035050b00c144600309040c2c00000303900200315600305801e07503804a00c200204e09c900c1c42d51031040c46400d602c2400c2505c080b05d100d441c11903241c422030001c0b0494903050364806542d402c83d0b004004080700c0040b4200001e46c5d140100713071558001038004e4102e0b032822041c0f00181d0350606080e001200000c0d000a4041007902d4182c4060301c401130b408001c0e100c0340c10f043c0c2c0303034542d01c1c89020003040003182d000001505118844030100c008001c07011800702c000c160328100a080a80d002e0844 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 301189136 1250 301187886 301187897
    0x80a03090c0923090703020f0d0516061103120402011d030102070503070215070b0f04020105040e0702070305010c09080304090504020f030a0b0702010612050a060f0219030b04060603180b1009021603 87
    0x40c0700f01d90108460602075901100980317081da056030240a100b046043e201c035040072540b40e9403000a0b80411032200c42d1005203008000352801c1290090403403a141c1a42d203110741c03041c81340c0c0c0100030049204c142c0180d0709080c03580c1d50318644a440ca100000c2c0c1600c083c2d055101144100a020303002c0300501e0b072644220b580c248034044030034004156026264000c0d03c50710401c8000754600700c4001c006070b00540141001400c2c2a0790700300410350f2a40c02c84d0700704d00607044085d04104103c42400b50381180c20003402c1035003140781000405952406640300300704440b42c44001203829500d901c40750f601c0302c0e44054241c0e0464000c80c00c0c00480700c0b106640810064bc64058002035608061a194030080e5010b40580240000d58650a02400c0814803610041d9030810440b164203070011850324a003d469140895818500410401129425840340b000d0500b40541c044410141410107115658800d0b1000555107407503100d610b40c01706540240169030300c0020300c444559105002407841c148079a50f20b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 301190386 1250 301189136 301189181
    0x916090b0a090501121e020607030e0f060f0a030b0604031b060813020906010f020c041a031203070507260d0518070302150c010b0303120115020304050607080a03090c09 74
    0x240d800b00d0743d0074030035007182d5070712441c94000007100580c0350310210b07003403540b4206c6202483e00050241d520041e411000300300b070410a495941410740401c0030702441220402c1c24080400945000d61142c400e007001010f07603607600440c041d652b4205940255801c03514080c0f02481c07007030424111840c180104d402142c5500009411100700484242005501818013203217a00c5141c0103461180101c1d10304019401510928142d54580d0300c200030b0400700c00c66150b440755100006050030066140354182c203800080040010359600300c02104c9880754000340302c2c4c032540720a10b01a900c201c4001410014810002030701200070b44d294211380e00480d0a0042d265090b118503201580e50b005901c0025081100740f811230100c8080300c0b002d000203082c0d9030b0000c18245031400000742958051480361a170783d500b6000600845030448030200369248140000d500e400d081c0300002d00c4501031030900074118040055140107840c0320307401102045600012030703035201d43c6903010480540045003012024a817040c0e030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 301191636 1250 301190386 301190399
    0x603060e090c0f090a020d0e2109030c01051606060b030103060b0f0a050103050a020403021206040b010e0708010e041e060e06060a030215030c0f07030e03070b040513050916090b0a 79
    0x1e4000481e10b00070008025101d010051000e900e0b00140703000106982880805002c0e101c600690006500d140c0280940008076500ca80706140c5017906440e1800080c014124941c400040c420002074090800a44a6402a5886112032990200100081d0810500048070351070f58014505030b0b407143c18140703d02c2c409039080c00b415030b8038038144030ba10a981c0c400410070ba5001b40c0c01035030000c010080141c0313080d4803500401c0001c14000040c0400fa405030040109011001e60113a001d410000ca5450150408020080800106006071402041d400001c031b010031026181d00c0c40304206520740c15200b0341c1c0b00c0c10b009000f4504680d07031000c0b138000c4500251203850090302c0701f0103881d4000c10000300c1c42c0000043c4442d5410052280c00707031031000c00c884400200c0080240c485c15210342e64400303480d40444245800c145003a4000d0410352010f1100380704c1640c0e13221203c04003503210100040d2a43d6540442c5282501c060039504141401646c0425501c41607007000d92802d000740c0300c0b003803003954a18 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 301192886 1250 301191636 301191643
    0xc1e0b030f13050c030a0f1703010303120c09150f02060f06060715110f181c030e0a0b0a1107051f1805180a0506030a030917030409060603060e09 64
    0x4a050255490040020300503080710742203204050b02403c00c0f01c2080c000000400d2401c941801c0a1301c01c3c4c0e80001d00d500410828149a84264510070046800c65140d40d8002d000c102c500800301c2c140c1e685030754020042c40d100e0340100c80140a0746544050180840202800341d040001c24800140903120024408020241300351380526000307444545081e019449048140124001480016840326412030301419610040e22507402d55203004d942d60301c00344081c0ca00c4400180d04a40c0a07450201301280300b140c40c0400340c41d402da0107040580b81a05128002070280455801207070000d403020505407a680c0e07108800410300100740040b100f929440300201300d50310080400492040d0034880c582841c041c45040781d611400100500f1f14001a111400140c0c020b0b4100019501000c5400c1005640c1a09003c1c02d81c00c1101640034100c40f68160301c008103522200e00a00391003076a4510061f401c41d4041080300d008040303110081203420340303445c0b0084c081d2000d03224910b51444800b02051000710b010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 301194136 1250 301192886 301192891
    0x1030e011b0e0d0605070e0102100c05160f0c0e060315040503030105012102030c0d180f14100932030301031106070501140406060f0506040506070501090c1e0b03 71
    0xc81040080946860003118402c0c2c00020380358100406441020018141d8041c0741d00542c102c0d01d030904044a900c000a20300681ca1030440d42950610508120391034008041790040c2141403000b4000d803441c2d09068200700d4440300020075001c0e8400000601725103001c4104c1c01260101d0581c0c07001c04202c000ca5044840589010b40150030420041001d503020701c0a078480760381c60b84428003034030202e4604201260011074500389100800216039a0707020740c1d80700d0b01101802034109003500321410385075062860000748008158110022503118a07140812500240200a680511068143e841e040b00701580420592180c0410280501c080c5c1961714081040320b0000350056003560320f5601c07051000310341c0c081c006030800000c01034000429021701171500c2d082c4100c85900e80c142001c1c81d144048400c940d00c0f18504504051003841b140c0c2d140800c440c21600d0440300251245c1060414a00514a40400400d0f440341c107000042c40c1d11401d02ca0720150200b01e8074580e66256203070094012840708 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 301195386 1250 301194136 301194161
    0x60c140c030d0b0307080a0803010f170c1207051c050111040e040308130b1f080316030c1e050714030a120305040f060e01020d1a060f070f020a0b040501030e01 70
    0x620040e103401205a00043c0c140c0d60043c05c0b114019a50102c0c581400d102203070540307813044000300510201c0d5001100c8001442100364004501801c2d0070516142d0048010701c1c3c3c032641411050f9180e00c00d003004194040c1c00d00a040c0ca10141e01e100a403482c1c280c0503c41181d4075400c1c21030310308050030340c0001d80303046a09180182d2103c0d40c803a9400c45480100034806290503d0070314125012508a201c0d8034032604d4403400744084500c110441603d034840c1503202d42a2540304001d00250900340509a40740b003640740c10000081801450490114820741c0d4003054880b2150250000303000c0c1c0000c134101190000c1003080e10240101c1c0c207050300c1c0c0d120720501030102d42740610b2091465100354001e9030b0103405030410189a81d000d654035416102c0034100d40e85142c0d0045626000c5122078820400c0181c52600d05604002c15030021a41c54045c0040c10350304c4080110300c4d40d090004000265a00301d500801e00020691501a811850740190007101d000901d0a10700b101b050303a05200d05400e0864 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 301196636 1250 301195386 301195393
    0x302010203120c0c01061701050a111603050417070510030606200a02090c0d0c170f0c0c03070b0106030b040902031c050903071712130b090a0305030304060c140c 71
    0x1003a510b0407031080c5020300003402ca904100032001e42c80c1030038070548020781440019884032040b94503c050940d5006844182101c1ca0107941c0c0c03040650030f20072100820400d80882c20201043d04058810b801154040c030540d0304001e04102c3d40010104200741912021290340c583d44070482c000b1422101140034200c0400c102182e00c26004504004402800001d0000c030b440d4903140c2d5001c5180c0c4c02080c0c070122164400800c1c0400817441d01e00420501c1c4829182001d403140503a0300a14940f48040c1c0800d59a912400105004482c4001250b094100b40c80c00c80340e88456134075000c0031040302441550000780c1b40110b0b001d000c2c034050244104480e0020010501c91040f19130780c217900071441500744d060020030000c2400c41e807010f02030719004280c001809562840302c0b070441c500300711000c0751081b1102d0007082916012040400560300347d50804a490b40c8510a40d000301e49a500756800240640c4400b008000c1042a80c2e000803850000907a00c00e42a414026140141401000d130105401c0c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 301197886 1250 301196636 301196647
    0x20f0307060b040f020d20180913050607020a0b0105013b0a03150c030c020d110a060e031e09030a0b0a06050603040b070311091e0a08030a0c020a0504060302010203 72
    0x703419800440880d940140006140140030000700704aa01c00340f003010b0314613110703501141040350360404070807040100c5044514060400110b801c101c204807803620721810708032012452030f0300c580c44000090f6502500b119154240f09502039610300c030044049901103850070011030706521985e43c012440304e580c00751312111002a80010006081039144c450103585203880e007102ca50303402c803a4000460190031006002150020b840b0142d43c104020f030400d2608004218032010ba0000d19031039642c0c04c078900b150050010b441114240b02e2612409000c00d030401164152406001c002000e460a50448200221014a159100c00e000c0d021074954160000c0d42c034000891620310100341d00c0002658001101501c1d400002c05907041500c003603615207050000c100420b07416110f0040c001050f1600d1504102c80c1c030b40000e051102d400780c103050840c0c02c011000d0441c1c441d51426070141c1070003001d60b5102d1400120050007c00400030681c4560000400041d00782001c3c0303d2141a40c0e0180c1c061441c02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 301199136 1250 301197886 301197893
    0x170c010b10050f1b0d0f080112030c0b090c090408040518010602100b0a15020307020a230f0f100e010e0a0b040e07051c0f060504050906070f09081501050907020f0307 73
    0x603045550501c491304907010902082041c10302079002c9844203622010042201d000d80103042e1071050304805003503289042d058003c2a04071308035441e89548420801d1142c2d490800032400c00b442881500d03005840e4000780420001d58501030000e81d1400d8078a19150340340142500e90000c400e105280150308004c250000040040c1c2201c9180040908040101951195000c07006400100264010b030004507080d021454006040c034000c02c441c903044000501d40302c105030300c12054092400c2c81080c40340715418564036092100d40441c070004203200260050080d014080d0700f022042d490000e0b400c10010382d171070f1404921240613111140f00060030542400030303404c41c04c07101a001009010703050058a940790f42d141400f0082d0aa80a000f00d00001a070b2000425a8a1a04034612403030505041003861600010722a51148152600405070b42d13048005a40441e101c0c1c100e06214010313081030240702484480c0d501c0c1280d0060342c04460139525200201d8450390b5140e046206c1d0780040041d940403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 301200386 1250 301199136 301199167
    0x904051614161505090c190509101e0906050d0b1501020c060301090c030f020c0303130804050a09050103140105090d260a0e0d031b110703170c010b1005 67
    0x1003044042d00324114001c82c1c841e01c0340c02c0c03070700304403180d0007030b103400070450341100078020003c42071010b0701c1c001c00d40c2002c040e40d0802c0390040d02459019100c0c1500140c100b0080d4800030b40204000c41140b80340c0b100140f158448089030703000301c1038403904011000805003007030b0351550345032500284503207070f5038a464040d00082d42c0b40a036564114440e440744030072113548182c021402070210013000160000082000380075104407104a950b44c501c1030182145070036001c41101c0c0e0003480d11404c103a04c5400c0746011862400750750082e541150140c0b101140000c020b81c40305040c1c0b4022541e480c2c400414400c0c450a0390001c41d004a02d60b008081c0005442d800b4400001043c0c02c2c082c4402400000e031401c1d0040c10341c1c1101d4007400c254840301d8041080301c0910445807030307826616090004003000440c01d6920b1305421091420082d41c0164001205003e006540c05103520841495032031000710b58095058022080d800100d500c2c20400301000e11b0850610315098506440d00cad8203002c0c068607041756 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 301201636 1250 301200386 301200397
    0x50715090b03041112151005150306040f0614090c1608030c07120818060c0405102a02181506070201030e010e030309070603020909040f0311030307050904051614 71
    0x80c0c000f24000d003908a17607111318108203c0d1040d800101401040500c0b4000c0c0700d0805004003c01c948020814440c90b103640d8003c01806840d03030b031140da030b079140c113030200b8014024007101d48440c925052002c205840d040000000d100412100c0100c2074850443c050007921441d1404030440961241d00400510303c2805141d001c001d414085007010002d4540b100c40c045250804000a5116810001002c40d00341049001c4c5562400400c0203182145c2000801c0c402d90003014410610050300f13182003807103210030307950844400c4034141250070526000c00d808000030204074401c03544a100510042d960b040000d1144200d8002d041e003842e064024402e46500c40b090507410903845405505401c0300034010301407184803c0000f5079480c980000ba080c02c005954012a0030940100300c0031496030ba40724010b5030001e80020380480d194042d85016501c0c0041d00c03501910700c0c0008400c011242d078108001d425202d601f80e9003445140c0c0d8220911b20801105000710f40031500d50559000854000030103040e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 301202886 1250 301201636 301201643
    0x506060a030b010207170a020108070318140304080709060609080a08070605040809190e0c070201140c0717030a021506100e030c03070e06040b04090209040609080405060a0507050715090b0304 84
    0x8142e02e8031511001b4000320840d2154000da0700070b00b1000215603005407060b5018610f46001c000036906100d8580050340f1283d07016140c24041401500941e44c2801150000d0111000704d40d0b02e1607a52a0381409041d451103100c010030151071b800501014045800301c800759100c51403e2070000c00d43da84800805020380141d80382407040c00010079680320b410b90b90039840c110829500c480c2e441e110a10410401c010300d14034152405101110042c1d0300805000051f00c5005e01d0a82c0760031010b01560314103d0340b43e020b1802c4203509541354200d100080010811300115500356042d003004401d5130404030500ba030700b0743d4100780e4011740780d0a171911441c01604100c0006081da1400d5500f50002854109541c204242d405401014000c10746814800d034080c41d10300341d40130300c245107542d00041c01c900303030050015154079110902c800070803100301c2c22100507110042000d5203801c90444001c3c03081d00461411205d6100c2c1c0003010800400c50000d428086965a460351820f81c20700800b040035800203401103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 301204136 1250 301202886 301202893
    0x16050108040803070921020a0f0b120c0706020307211527020f1209060405060402060d060504050f1f0f09020a17010b031611030316201006090506060a030b0102 70
    0x1c9800c01e1224420690006c0050101020003080e0040180441c8254085400c510111408100d48000801610064907020385030104643e40c03500542094401d8900050601e4400802c010700c00360010ba9480c904080d10504101d07200014082e10101c840404085a440d01d030420f0030481c01d00312881c4886241c003134040d1130a0303d180c050b029034107907000002e90311200400840c0b030318585880703140b699034080d00c68001402542804c2e220700e5281c4802401c040c1c003070000012074590055a41c5c0058000742030107482003102d0315086441c03411031081503960b414800440c02c40d1501d4003071429490b40a4031525500c03500014039080c03080380207501400d00a000d02c000c5003c070141c2403110a0010b4000c00050401550742d282c0504000d40010301040d6000911110700c1040c0004500001980d81c08121410100031180c1b401300103072a0701c00000015528903c20081288204401065104c2642c21110040c0070032510780c0f81c40425210200c8615801c06400d10240d03c0c2203119400c890310041043c0142d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 301205386 1250 301204136 301204139
    0xc050c011b0f0201060f0603090c0e0108030d05070e0102121c020d0902030d02070803040b2104120806120a060903050426060c090d1203020d150503160501080408030709 74
    0x2429224140d0484001c1010200c07070001580d000741c2d4200420303445100801500e1300700100340b905480503018000400d0b555118610030050f0f5500c08801400713100f441100b003907a45126640c2d503688400a015011814076012940301405501100e0111314140c01415074011100c007020b2094200340041c80c0c3c140ba10540c0c105600c98030740700400a1116040e80401c840905005061800d00e1000c1510b007151310140e4200314224010040e90b040c0c0d209489400e64480c540d00d00d0342c02c2c20049034800c00800c0f506200380400c01c1110400b24401302166100c074085640d030b00d01001898020300c1115000b54001078140d00000d0b50640c003004095100c1e08245040580301d40708810940441d103408600c0c41c0014900141031841000074551005019142c9840e2040d504041441c0140c2523070010001c4c0589000c41c01040d020350143e80b0306140f0b050041018480c10010840303000c295200e142d00900540c0394400703000102c0400d1106968040e11050440d0b296503550400c81c0d40000d00d00420400311600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 301206636 1250 301205386 301205407
    0x8030334030b032112060402091210050c0405010c0335010602011410060507030c080307030b09060a05030c090405010b100306080d0903050c061608070f1e020d02040c05 74
    0x10032000344855400291020000c1d09041c50310300003d40800d12143c0034802034150044140855060b110300034554291503d41e00f0100d000f030301030003034200c2e0f00038003400d102041598002980d810803010032405010035240c50702a4502c45c8140d004003800690251451008a0302401c010844c842d08444854221124400e07260a810001546821a01d20042c010850107a090007000081404c8443e00300d47d0342400b155901e482105449140700b8482f005c100300050500400752821003036000323490150307a451705000c010300426022650a100da1015000700710107082401100b0182c0b03001a004140c030b040c0c03010412070001030080040303030346640b943c1011072140c407908120000348401791008520705080080481c1000408158a000c00052410400100780c000039048943c480940d907642d55214860340e91961208605d1003e401c20800041ea1002c1010140340340c014180900101040e0f441e04020703c0380c0d1180340c6040a03600104040f000005482e1541c01020004054109240360070100039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 301207886 1250 301206636 301206721
    0x2030712080405040f060812041202360907080a0c1a0708040602060a140411191a1305100519050702090a0f06120f060209010c15091209080303 63
    0x180d02e041781e81c9541d07003001910700411003095985604407a250a0508100c40401c001844c010040d02c035041504a11060b4001042007024a030040054801142c0c8229510100d11200b070b12594010302c1519400900c0050206950310b0f100e502120107200686009600b084985584141080d0807a041040b04002001100180000c0031145c014052901d44201070310211a05d400c0c400c0c020b00c602c50100400150504c1807440c980c02c00301c1d00703c2c221110032102c640e409101070708100540c140700b01000c03094240c18400b800c0c0c80800300b450760030180d40b106e040c0880e650134407405801180342480601501e2400c0401d518000405141c01345c1400b9440e00020050f10f0207681c1c01030403a58903002c0000465480c01210040e11995802082c0b01100342d5405407030520161010f07003001d83c08100900d841e03100e40e442c0000c89800c1469290721001d40d0814500500112404903070811104040c8003045000d50300c5a0304845104c4061400c680d2101d16400481051450300701c80940c0010800c50002c4904 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 301209136 1250 301207886 301207901
    0x2040e06010305011a1030060b1306050c0a1101020a0f080306040b060c15060a0f0b04080c01020111093c0909060402031e1c080906130203071208040504 67
    0x20400410301e503aa0500c10f0300d260314030b103642c0e500501111071000305068008954a10b840350f090b142c2e400030180c0300e40b00c100d1040e09410100090f41488c000103802441f6101900d002481caa6688450360354901099509100d024001410783c0c000c2c02039840800c0322141754009191060040e100761014035500e030215450203410881d40781c0c1001c01404043d0400340300c0c00d02d0011007a42d8213460a510b0351191a9200c0d10142100b114111020004550341c83c1c1140e14802410386080141100740c8500860440f9040b40c0201d03266403180c007102c5100c0790f10500075828182e4501400038940281d21003800641104000b1040f44111040e0101204404010fa10401d94102d403d981c00400c800c6000c01602d00405007402001d0b0b403258080c440917030b84c0400d4506a003a1136841c000104018940d000d03040481d405a0f1204440d046540c0751959504200c040d40304654560039101e06a444098000b03189240c000081e4140d40f1181c400d00075109007031300d140740f541d019003080e80c10599194001400d0b0b5102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 301210386 1250 301209136 301209143
    0x7080307030903030b090c0d272901050a03020402210108070503010c0819020306150a02060f06030a03080106110a0804090b0a0b03040f02210a050606010e0d1e02040e060103 76
    0x740c2c0405414140e141c0700f00341404004070742c48495820b144c030f105000c50151422407207240e69201c0880c0500901501194143c0250500044400c6d030182000100c1103010644c2c202c000300b05541112060502c02c0466050b00e134000c141e01d04085c115000c2c40004d407c00c0d9080e5440800c001d201c4400308180342050f41c000c0011310010320103941006c042c107003511500f0914005000d9900113000201c1c08000b03076900c02000000006803240d5032240000d6560f1904a11015054000600700101aa000c940940301d414850032010850725801d0505580700c0200c2c10160001d02c29000500542c0c0c80b900d8038030a0300d0b40c00030483e40c90000304d8032001c45c0c0d40c1c425401000340c95960104040d042c1082c4030240d009040c4040340500711303d415202c41c03030b450405500080c8500c5005600f41420000d4415880b4100c084000b19405442585041507a030b002c2035401501150140700c002c0d100e0f2802041011000340d20500580072a41030b03000060b010522100700700d034026200c0941f60301007241045402c0c000c501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 301211636 1250 301210386 301210391
    0x62006040506090d05091f030603080409140c0406020c0904050f2e02070201091e0e04060b04060e1e040c08010207030215060103140402210f070611030304020a0611030708030703 78
    0xe000740014903201c16512130006001090044d14103560390041c0340030150350268084500031040b050101d0051030342c0d810040150b800850b002c1840f60843d844210119107248220001744c640703d00407040da01940c402c0d000180d12860710b013611410102441504984520304548421a02e00c2c1c109082580d0700d00c041440700242c0d00140c141c4260806804180510100c003149000d000341c0008160751281e00412800d8030101010314080c011a40140c4001c0007014641c09a904040c0b8044000c0c1c2200038a03107102e641000b002007580c6504008140c018101c02c40b0135015250603500c840d140000c01402501c000c0c84246c400145d0f9030081c0000c16046100b94060b2000140c2a90360750340c003d8019040b103040610706034011201104014509801c03175011104160403240082c4412903c0582541410b580c0c0500360b0911340c0c68200142030003d8030f5003500e6040340c1814884a807640d03070000701c074041d612120201d810000c01e40118040040201c4100a507450b00031213031205441ca41c41903641400103607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 301212886 1250 301211636 301211641
    0x606121406030705100e19030201180501050d0902150f09190602060a0209030a05010e03030603151006030e0307082a01020a021b0109120c141801062006040506 70
    0x110540300d103104402148080c0c804905001000c607030380780c2907401010301620f541c0321480040d03030041700400f0324000000c00120420052002c001c401c01c1d1188822400b18138072070040b02801d100a1007004c15610b0603950a81071941001c032100103452070000580c2c0100c048040b9002e0b0342e40c548014500f008814210565481141091205174070f91304c46200040504c22900307010240c2e01107003ca40108005102507141e10070700c1e0002c2d0401d0f0b80090000c123150701e0040c907103080700c20110146100706c2d01201038030b40101030300310184403603081100d01d00e02203d40c10030305103c92800b0f680101c1620226a044034204240e59441201c0b640c0054401c4c00c0d042281c211800b9080218240c14403603400b200001d500f880d000080196031146108a6500c3c400c0c405050100d450b40304170f820200501b11801290800107550403d40d210792018024005001a901214544d60030b00c03d200b03100890307045c01c02d5249a80703000c1d002c8131800c1840340080e9060b0307080305107a484440b08102e443d000d103001e9400ba001c6030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 301214136 1250 301212886 301212917
    0x60109060e060a030b0a0207210309120f17040c05090a0209040b0d05031207020c0310020c07050613060e0f090f06040c020c0307030201080414120403060b0108150d05010f0606 77
    0x70640100b110740b0901e01d982042c070000318800c0040c0e4000f500100090780742c910350b00d450314403007a40b1103801d010443c3d42d241022a25a05821244440b8007406100040c410504c00840e001030700c00d807924010801c0d0344510130000a003c510342e5031260103101804245900c940c00078401c01c0c0d0603214000d5084d00815031030010315052203612070344502196950020812995501c1d02d900402c440b404015030b4590001d21700c42c2c001d02806900c5280282921050280d106891009422511182625100b015000300b038a0900904031041511a103095088140c9884002c98812401110060b045001010000c13515100c0b5480742c1d0107401d030841099940d24022083c4000c4401c80c0c40c5402c1154442c0e07504019640340450080262602031030030b05d44035592810490901144e5000c803031090f20a510718268092511400380007a02e03c112000d111946611004641d0a00c00303459614450480d0600a17801d403520040290786140b2413800030498044140c40e64003102d1950b40818003041c16410300c102c45 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 301215386 1250 301214136 301214159
    0x60f0c03130609150c020f150c07080601050d0201080c030903070c031103160e0613090503030a090b070c0b190b0a090c090911090103090503220f06020616050a030e06010906 76
    0xd4130414101d100303084840c1c00000d280a8680070040e000e83d10604005003107460f41440c0307034400c0c030500307181d00e0707903408070038076a65445409101e084401d004003000424149072080c40320800680507545c00c0c040751a031000c070301071075400509000314611042060f0310020f061201c5002c010344c05103011032103d5410000303160400103960000c1c0c0415480f103030140310030f4240700340c42900800c00351642e802654520742c82d0002440c20380b1019005104c04810000038480540001c000035201d500c0742a025240c0030307415074003602003e400414074280d1074001040316081ca10f03a17201c1308485013030201e100840c040c0442ca0707244054000c1075903a511204a40c101c5608840f040c001000500000c1280040c480740d01c0081d8000d40003168100742e120b101c2c09003803041c20003d071b9002c150303945200000011101c803144420581485280d07003034002c0c100002581b80c0003248003407181a10070a040c00020440308119103aa12030b6803030f8424541d84000c0c0305e42180c3c04002d140e000e8590b0500009081d410040c1d030015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 301216636 1250 301215386 301215389
    0x30204091b02100c030f110318061504090f0212010b19030218040807021804052b0809250305120306060a0507060f021c0507030e0a02060f0c03130609 66
    0x15079140310034100740d2003030740040c0c900000314051100003802d240e500000c501030a581e110645940f420720013100d64800074400154012016844080d05110202c10500c0d01c1d20011250312800591080c4503083c10b09154001e000f0803403181c04404600b0810307a00080388c8240c2c1d085207411580d03543c001100c06042c81450008009203055a540c1c140c1d02c0c5500184000003100018034409084401050403c4412030a544403240d0051651802403045402005154400c44058030640320b030200c1c03860b143c400c088021150354950206002e00b440c039a0010f036252040507107050428130503481c43e00c0704100c4012069404080c54182c1c5d40ca100e165040551509422420200300c801c1c0410510210b40d0700c00c0e00f220742c060f80ea410b19540781c106c0b904280000f040310b01e8201d50060300008a5140c0c1052040c09100c4510109030304000301e4030340361030440480383d510030810b038198400c02d40d410151400e030003d40b110341c80c1c0b0002c6501d00041d903584281103402010310254030419848040c048990001c10000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 301217886 1250 301216636 301216661
    0x30201110a0c0507141003020c12040308070b010e040c2702160c09062702040801050f040209090609032512090f1a160602130e06041a100e01110d03020409 68
    0x110200c88480010300505846c5900505041d800030b0060614142440345851380c442840e02d0f981c40725524248400903a01280c003c85110810700000304000c45a41c094501039038200c260b0700340e210704001150084d1400041050441d22110346540a401840d0008051075038003800c40c154459860310300f5100522868102c80001410b1240c20301c5030340e1641611480006036032000108468071002080000e04c1160082d0440e54204030803c002c02041c142114041d92007640d0104041d642e095203561548402d43d1000c04942040100d111460380b0a100200303101290a0502c400440503516910f40080c655003000210341c03070744000c00c8402d485003510801007102d04912407622030048a144501d1240c220102d40d150300c507840960520280b5415208144501c440050b01a0789500b005824050100e540900c22030900c4003861800f9120054041891000f4010381d0304440c0f5414107031940c0c0346194a003030410502c004182c8145008001604e44004951030040e85c8070b08099480d01600c00284a81 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 301219136 1250 301217886 301217909
    0x30b06212109090f25030b0a05100801030204050601030605040f060305060f1012060905010507030b040c0207030201020601051e030d0c060c081e0c090a0303090f050109030c12030201110a0c0507 85
    0x800c2c1c0e41c03150714a0a92021566118113410b50b1240e480a01c00a024014042403818100110002e907802d6031007481d101108890444c40c065581c01040060071200c5d07135400000b84c081c40100018141504016040141410302113049921032000c44e04540c480030941500c00c1d2a5a01002440350900141d07421183d11800c90300e540c07420314409114080c1c203105040c064203001c0355500078011141d1109907510342c01070080c00f9600300601c1c0140603010030301c0154403aa00c0d04002d418030f5070000440c2c0c02102c0d03068001e0205a0f181c40204101200d09040c00c20361401444030310303100c40e581849002c1c0c0503100e98440f403001c1000e9080c01801c0b600130440103c14095408144502000e0245c01000d55801590340e00c8415a200040d082c040e01500c003003581c0010b415400841055000540442650262100c0e0819160740300f004485d0320040e07100242540c0110202445117683c484860444640a4000800c125005040702e10b9940c0c00761619000241c0510902800c00c0800e04c0410000d042c042043c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 301220386 1250 301219136 301219147
    0xc0f0a0209181507020c040c0f0e0a2603040f120b0105060406080a0506030c04051503061b22050a030605180607020303131406010f170303010f030b062121 68
    0x660ba943c5020440403015181000001e000c0c244200035207038404d80064001e005008018074003515a0514083c1c610210340300c50240c9140f402e0034460802120500007100800b107000866a0154200004079460706d400104004500300b080282220000d201c1d1141509100d1603d0800e407105640c1a00902c0c03185804000400825501000e002d40141c2083c00c0001c1980314800001d181c04820800d45400034104800c00900c54443c404401d0043d1094083d180582e80341680c0c0030301d95007601c031b113540111014080c24a83c0e1a4510390604ca18411110b94080c19454400041c0d8050050b44103c0300d11792103a042181182d40c20104031440b0b11120000d000500f0721141c060740b40e02006000c10186a807290460060080010800c40c003c622072040d10050358503141030062201c220701440340c0404950420001f2100002f003101d048450303101c403a203041821951000040c2d0700250141c0c0c1e003c00c908046c0c034841c4014002e04200c038010100101881145442c0c0f287c03521145200c2404448810b018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 301221636 1250 301220386 301220431
    0x12040303020d080a0b09010305030322021f050d0f0f0c020f0706030b03010b180f0907030f06110405040c090816140d020103090510060806010b0412030f02030c0f0a0209 74
    0x182d40c1d0082c1c07850300300166aa40c601c0301001c0140b21004807941e00130201000001030020200085008100c080a024042a45030070340c48000204610000d400c001b0b828403480072901d10780d0f0003011021413490700501d80104030300120159102c0390044450680e82c0c0d042c0c20603056a920803548201d0703150014082d0078850b03500d01e58840e81c42d84a07044c03c4c1903c0355a2070000c0d99081d070180401d603c00801d845000c40c4013131001400c29000f00d450701e000c0480240403030055240000c081003182c0c1e01446000700c054069803000302078005480c0c81c1060880900c03010500f6500c40c09096820038056a4414070f01d403901945a00d0460565480703003c00d1071600c4180400e655508441c80101d1040d600c81494151510040300103010b2150003800c00d0080301c6007041d446040d0781045040ba0f03440c000302e0394180d8840c1000c034114821489071004140c6065481d00020f4000c149044101200740180c0c0e08013500c0d408a98240f03500c0c0d1611030020707040003003500218a40361184541100300d09101003920f0038601c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 301222886 1250 301221636 301221643
    0x60a050c03060925080103110a080d0e0a0f14100f0903030e12030f0304120302040608040b0901090803070203040608010909081b01060306020d02030a0518100c050405211204030302 79
    0x600c024003600403000000d00c40d584101541364000244900c41c0e0f01c003c1d01d007030018001c590a000440f01441c0368201c2c26002e180c00040c10701550302120103851040b00c642c00c00c0c1c840e650f039404110f401403184000041c41488ca4100a80244100c1c01c180490050f800208248000307400c20200902210900300040d8581c003122183c02d603607141c1000c100004041d00000e024842d080354401c4c07680320006820030380b06686405180214851000350380c004807458415001e90150340229000140c0b4807001602148030b82480c990458480740c000103d800c0162540040d0b40d00860303a40d000b5034400181040351a41c418202070041012000811a0b540b00350740311340980c8551450b0342646a0104c045504409080d80f002000f144d00010842d980c0c140c0c8503903080a034004076251215145071000095002c00210409c40b620010700000c1c3c5040311300070603144003e107400014001040028400403c154480b001a10b020f4210b06038400000700811b9440e901e8010740603d1489200020f0104100194000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 301224136 1250 301222886 301222891
    0xd02010c0f050708070c0f05011409030613080c1005241302070c091a0f01020a03080109180203061e100315050711011506020111070b0f090a0b0702010e060a050c03 72
    0x34600540c1c1e8183c1410103c9207800b4040e0007030484d401e502400103107103038254141c4040314402e03214071501c240340d20809543e0340034904079582c16030480400210001c1d8450402030f03d040c800d04199040606901103e880c025120a5581403a135a440c1444400c030f072103055a04141c5c40400216a40101c040049103051a540c81d09211258000c2900d004002c41010007030060640101d0400191041c0d03a93340b50900f4600c000705020b0040264ac20046d5480070610504882d0992903022060f440d10021100415822030760160301014000214016a0280002400392100f0142090801c0b00e0780e48540450a02600d01c100080c40c44030100b001414607a07244070424411400050b10b070351428400d41d401810110703140320703d500e000390400792030610b01038400655005600070420016400380c03c19040c41140f02c0608903175400c1002581e100150150254410040f2042d14200d00e0305644251100c002070f01e500c00941d44586404804000c00c11415a010131048800e200906244407500710a2001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 301225386 1250 301224136 301224167
    0xf0409030207180b03060709090f05160c05030408250b16030503060109050a0b0304060f0606020a150f0516030b0d0305030f04051c021e01060e0613060308070c080d02010c 75
    0x61a114082e00c03da80e444150310f420041c080c0c408034030b00070300c005000b01b04034010088158644403070300b216003400b4032032207205203c071072181581c0585014090756001e403600d0049072180f004001c080399524050101c0710112000014010210090341c06900042006800070100402c0622100c1c03032143c00d0a0a0380c40c4903403d17080469490700d4000048a171081280c000640000d403008002400e10601001148103900a50040010000000c4014165a850b100300e10040e441604c02034040741d2003220785040c0041013a400103442d40040b03440d4095840c21104d014030203c081044c01c0c9100d4050103400074081c4102c490f200c80a01c40d541c060300c00c1c040074104032901c000301000a010400200b04d036041c1181c0e105a100d1020b140d094009588038010306216400a81004200c694080705001d404169a00d00c5c4c0e9503031003a6a00014804004a19038064010750345580c80080421103002c010300c85940900e40700c4500d182010602c41c90030324034916680c00c580c58803040442c801d82c4200201c5103400c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 301226636 1250 301225386 301225409
    0xa02070315050705040b160b150103050a0c08012d0305151f09020a0c1b1409010e0c0a021c0207090501060e0f122406092d060109090c020c0f0409030207 67
    0x100e4604050481b0032420042602104100348000410140d512801c09c0790241c0e0107101d50390b00c104000313080c0d6108021101c0400d07103074001403108001810040c103528841da200c00b614030a24042c256100020b65105403640c2d04160740e00610251061100f6910140229000c0b0300300c010f484101400c84854490304500503030104030f00e07507014401e01e50149100e0700281520a9003400507500c107640c2d94203110b948840301c41078a01c0d41242c141034401604035110304c0b5000322550b0f01c01ca424945940007404003011801641e40501d10b80241b00b0340035800c6116940246101404c181222040b02c0041c5c01c90000d010307010030031400715039803800480380c081000c1d1606402c0d2840480001c0c507283c20140c550940b00c0138241040b4042c01c802022511840045a0847c00741c0c58044411008288140d1091005a2014011130754940d00201c190380200701850300140f407603564000e10f0200e5000062410060b08106005142c0e403800f5028000c14a00440e03080040010555010303569409a2090800042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 301227886 1250 301226636 301226647
    0x1419060b060903010c0905030606032a04060503030403050a0c0b0306030c01031a04090f2a090c02030d09150c0915030b0d02040603050303041b03120c050a080a02070315050705040b 79
    0x40700e010595510050140091051034941000580b00c05446d004040c002c0c8103001c0001c0262a0004203611030080d030114519040e00f00d08020507408441a41450700542c40742000142e0f610100010310056010707c014240403102841e0161860406900c0460040028003e1200c03036500420510342180007402c0015a048141f292446400d00b0707110301c41c0c8c1c003030b28000d503503014021a00c04c940c10b514030400c00003804c9020550407005940d4022240e5420190320b000a00c10040a548216141c066500460741400f0291000d1001d0f0340c0c40c0401201c1d080300914002c28012000e01070401c19a405040c0948140d0400c210f1100c007103441c403e00700030035807291060140c0c4d85031240c2013803075550050410700c01180c41e418810307925401550121035011000003040c460041c400c42540540381e101d600d0418034451445c08503a03602c1d00c4401505d0b0340c084c0c2172800c000280321100801800080b80c020f800c034135103542412544440310420000c00c043c00c1c0f90802001a900004850580d5001040a521036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 301229136 1250 301227886 301227889
    0x30f0606081317030702010c14030705070f140a060605010315080d031503170306010906030506031905011401030c0f0501080c041a07080f13080a110405130614041419060b 75
    0x9031441d401d040401c0f40001808141c2d6030640043e107229045440f039900035207a40c4404244da100440344000080c07024000200054907101204403103c1c040c3c2c05001c074400320125140c0c00c00f48103900803194540e0b01d040c01c0090796014003441041130344440c1c1d480309151a06d0011a1181c20082850040580e0303032440d1a0700c1070314605201d0107542c111038150140c0c6007800603595244d00503281d05001c80d040e29000a510b900c607000d2584074400c090098091084204280c00e0001310000007101d084d502c440401c82500d440308070080c000c2d80207442140c4824584064502d111a482d00094100725900d410070084520b2401260b044138201030608091462402d031038095809160401041510700007000b1408a00c00350103040040034088081c855169282c074403550760300315005d00802c10440d4080d5000140ba20b0381c80654000900e04141c01020015604d0078200c1d41101000040944164240010300020306401c07608000c0601c000d00042201c078683d109448440c90004210a071034078a5020309 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 301230386 1250 301229136 301229153
    0x90f020307080f27060a0b090c070308070c020d0b04020120071a07170a030501060309030c03030f020f0705151012081c0c0c0213060f1e03050a12030f06060813 70
    0x805100c180d100c4c503c818100c8896440d5401501c11010840c14030890001d07a1074a03803c143d0140701c0110311b0604d0090265001c4e9512403008004034180300c00191307501c0c0540c40381c603001c0d00d9280c07248076003003000d01d02440098900301c1c801c80011078000c0b03a40880059a400016618103131000e18010b1070ae0410b900b0802803552090102c000c20800081d905c3c880d0340003411002e840c10742c0507928248116a00c402048040b113480b804040c00051070b900d50480860301a44c40351000c4e100040c2c0c090b15045a0103041a540d6000c00c00c1210380354803d00c400c000340640d41d0090fa410031102c035903900849103032010000c1196060b0202405c031040000310040c80740b20059001c014000300a905000d40900c1c02c9000d06200304004080c1d014806131074042c54285c407d40306610980c0d1148032001c06841c20403045801c1c0c6c4800d00c0300040c11310181e040120100d1002c00c01c3c0c01040740f04000019180c400304c00002d041d190b0248441000900302041446402e4205444660050403c8141c075000b400c1410b04400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 301231636 1250 301230386 301230421
    0xe01060b090f0a090c050408240408030601110115050901090e0604081b0a0606051309080307050f1201090c1b020a060302070201050d0e030a170603070b0928090f020307080f 76
    0x402c2172a00c0008424290004080d10071281100141c58101401e50203108458071840740602004100e1400200081c890700091508640c1c10302d0302c070244048010030b09003101c03182c14007110b5070020b40c04200428503019140c01c0c0544400007040c00b4884490001555545020300014084803021801002061150f0008103103042d9200031190f01441504203180141164061540600000010401030391150700034880a02d502a600528665480707004480700d4120300c23010310b4403200411142c1010041c542a0314041d1006520006900d5503482001e071650700c90902d582c03030910303154801001507030b524590390048907a0340c00e015030341c0c0c1010720049509108001c80c1d03004080c90620403103590900000540b0460445868042000140380300c0380035402000c940c459070642c0100024000340450001800341400064900850b4448070800800c94140c10000003041070b80c0d0180030414035042c0d00501c00503164100c0110324504080000a100400051803202c100d80c6c0c032404503c4100500c80d4400c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 301232886 1250 301231636 301231649
    0x20624060412170409063201231c0c111903050c15090111120c0703050c070b0306031221040c21140c2107090f0e010e01060b090f0a 58
    0x260b495440c1c1c1160b1000b003245c0d010ba0407214500380c0325656003503002c013195468040c44440001c00c3c542684011596080b41d4074440b0b580075404c071000e0027003c0441c006044007180f141400440110042d000380d048a1000c6121001c01c01068a0f29031041004074040f029207190100f901d04131840d6080a03141c510a40c80c058601e40f01d032040807022130b544074910304e004101d140000c0c441a080341e0b040c80068011404200d81c0c009440300818032201c003241c0146862403103800e110381000026400542028080e901c19542e003440001080400e28043c004a901c0f080c0e070a41450500389100c40c1d070100050703070501020042d00c030702000c030b410310081409010052810022940350100800065490005000812502e8100b50031a0f82c4540001003112044810040c00d2081c25402d0b80303c58400001101030040950b0103183d501050801803406840c06020342031001041100703590061608546041c010032400b030b450b190f0f092040302a8041100c04000e000c41d419503101604400140ac411590351044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 301234136 1250 301232886 301232933
    0x102090d050105070314060f0f040b0619021501030b0f04020d0606060905040510140108041a070c0b1014010e04140703060314010504080d02070303140106020624060412 74
    0x30010004150407280c804e074802d660600241c99400c0c3c4001d030b11003054410550202c8101942c2286052058902031401c02c01800402d009e204000070030b203158003603030303203a030349140303000580200e1a40400028661444402e4020741a41c99600c80c940e00c00406440d6101c02c40b4030380f011400f5982d9494000c1c000304e802c42000c12460703a503404042c0c441d02d907030b2051900a90900d4000341159181c5107a03981200c559034030740305405c80600c0c011140440700500442d1000102ca902e00740120030001c441c0c0c4904a44e480c0c000f543c420301d00300840f5850000348a6540d4244001c010700c1001821070f19114003d83c2820025a95000d40001401501c41d402a2a407240078120400400503810380010b07045070b0041c9040010702d60a03001c02800d0321000c0f10040d0000b0385c10064490030b5a003550041c003216001b8a40040c102d0400130810003990780a80c42800141c0c846000c2c04021200c4009100d100b420007903410604400c40004529280110b21560300d1061405045805100341188014108120514a03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 301235386 1250 301234136 301234159
    0x7330302040614040f12020a0308030a0c0e03010b030c100c050609100e212104030c11010309240216030c060b06210414030d060510090501080f0702010209 68
    0x40094000b0702c980000100910f40e00e0610b40280c000300d41c2504c081042904002d410003d1850a00c13450b41c504036040b56105400001142d4100003450046510040110b100803411100900d041c10b5007220038800d925141c00c80500d41d800103201d400c00b0f10f0544614180c2410070f40190703654826441d028000d801a44200422010040380700100b01d03003006c10420103401409005990b4140c20b8403d0441c4180f002010480035072103074040d10854021440300c042500e441210700317420740d405840c00c80c0070525070321000040020902c9903150101d803e1804000549454507200017841c01c400c82102c8e90302800303c000c0a160241d4044a2201445a600b003d61401e80e240043c5544005001940c20a1624011400c0382c070300502200d4811420380200e010502e1510110298140c01030422074100407034507194020001d092010341103201201c2d100040003458902449681c07090107c1510400c031a00c1800d002503030700102c20700e4200008a030803184603a1a200183d00900c10002141d40c0413011444 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 301236636 1250 301235386 301235489
    0xe010e0607111c03050a11240601080903090303040513230702060901021821011d070906050612070903080f030403030b100203180a090204030605071d0307 68
    0x1161400041603c60160b4040c11000040703414103d1400103000a0040009120b035034403e21900c00e640940f9002e6980100314070740640c040c0310894007003000c09031740c0004102c00f940c1c0040086500c94040d402035480c0040a50000c0e40f00c2c4030b240100c074070030207840c6010803540c802c40c0d00003c000c201d01d923446024081d40c130a511017980b000b1505e481c014460100021014001802540c400c003007001950b444030f241003000c201800c2007518000301c500904418203c0040e600b400740020840c200c010380021078400c000d81d5800d02841d60042904a41045070800090b200e64003190b496a0101c076900041e43c03100c0c90210b9601141d6403015040c3c50300070520b1055a0800702c011030086109441c108040318141c3c0502c909000c04c0007641000da0403c0c00700206d4452200c4c604e503846030f030082591032140e8603441080c08907001600251074030303a5940100311906400c42c01540d6040110f0489059440c034400000f50340311410b0285008054031100300c10b11203800d40c1d1107581080444600d41c4001c80c0e4003030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 301237886 1250 301236636 301236653
    0x9030509061201050306090f0c0108040f060c030b0a0914070e221416021e16090b100c0b010909060902090405060403031a06030c03060319030801050a1d0402010e010e0607 75
    0x11107219004030404a0b00d0701c80e00046031100d04023a80090480c41c2020001555913400080041d600040c0d80c0c0e01c0000054002c1c440c0c10014082c5490000300e8100d404180100321020780c000084d0b00d454211002059107101c0082c55216100d032a24545030b040e1071002c10220303460380101c0c004001094680324124005038201c2c000702c0e91044210030f020b070340d110340050380d4041c840704070b4000d6000640211500305622035218030321a0403404481e0420a9480c00c0041704d0310581c80384401c0c0359507a541e661a03140807402d0001c001e03c907103410304a5510580751455680d8040c4141381c8903581c0e40c2801020401580c20928410380c0003426102d49240a06000d601c9130811901280003925003070391400b00c3e0103a005811a500790142c4200e082d55104042c0b640030750f1014100d280d2504c92422460159030388402c035003620328840d0f84d91110715458003050240044e140e80050000707902462520180291040d1203ea02c6502441c0a00b03000e04041d0040c0c894006040c150707a002040064403c0511103001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 301239136 1250 301237886 301237889
    0x304060501061b0b190204082e02093a06090506100b0f0903160303090807090221040303090c08011a04050408030103140f031b0d090f0909030509061201 67
    0x1600d032200d0a101070343c0104482503114000070b00d1442d002e13011561101c4044440c9120080d41c031801480d1948450308a403030004c580e120b070399030442c086801e10004005000c0265a4030300c848801c1d410802c031900001e101c1003045410451060020004203101440c030050411102c02c2d0301d0590031201041e00b0190064010030b402039a0601c1040e01041840d54018003030b20032114a604d1103420502584180743e0581e0100c50010392502c070300c121004c10003101e0318800004500c2a107030060030510340909141007425a50106220758030501108100c070620400b4994580e2090340b0301c0b4495503e6140a40050005010207003100380150004910f52605600050306807107030b5040540b40c490040c00300710a80b0f0040f20001c100607814001000060905004214800d250000b52031865044c020b040780740d6000751003030208014a10400b00c40c040004d1000d9480301c0a10300c0c00c0f03080c241c140070003d000c00440d481a00c3c00035035541507940c1414400c20990b8240300000708400d0b03480703031820b0040c000c0800a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 301240386 1250 301239136 301239149
    0x11120c0105220f0302120c03060606280509090718050105070813140406211101140f0901090506281b0804030c050d0b0a0522050601030b09120d0f020c030304060501 72
    0x101c04281b005140024043d803151710700038002e0409a440809100c1300c0d4000340b4050143c8645840e030030465600101082004540340e69a490315103421100300f120b1103034081e02c2c03d424003d00311611500c040100600505884007821f206984030118a00400310f84150380c003490903800301d104080f4105412071845005920211802d000207500c03452040010004e1007518103080748500c3d103640c00580640e0030010b64070727014101800c007010740045040d01c40e0b01c0084810034805c0001012000303580c00404040c0901001d485980c1007a500741002c1ea00c1c0d021180710720003c002400400c1020f544501c440e000c081030b51005c845602004e92408800e66000b03400200c4400b8414000840d0b03030b041100840b51141c1d004840c0f4078590b201d8a007203000a2001812541c40d62999015002036041d440c210451241d11400c010001589103080600b82030300003800201440d040104022072001c00d8905071100c3c03450321900020485d0307565500c5002441503211030550b600010003004103101e10343d03100324100c550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 301241636 1250 301240386 301240399
    0xb070206010603060609030f030e060f03060a06090303120f1d010e010b0321161406091e210405090705030129030106180e090a11120c0105220f0302 65
    0x1c0b100415800d860b25401100f0004400d10341c1080458000c80c8100c2405001e42441201050380001044456200a00d0340041d900000180809800e108414900034407080c5050003d45046035002095010301c861483e11040c0c40d5469090185440e80c40034190280c215111000d401808180760701804803070814200c2c039480c103400d030080341c200030850840c0110410b0b140e17140030b00100c403c0345550b048541041c6c00200501c1c60702000810740e071115003c60000c500100700030f14202102901e0b286d002824282140351103104980307410790004820150101580750420300201002a8200900555100a074444224020f0040c0d09030080015810303225044020710040b031000070300780c25a044104c82907000c0c003402c0004000b0b1611421024804c12401500c1d0018181c0d907010110300524159000b41a940246240400700200280ca0161001c019500d00d20600e1004043c1d0381c4402646103054148100000e029100756025640088012804240d5942c0307140c0300e4800b192901303000c0c042240100c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 301242886 1250 301241636 301241639
    0xc01030b0306011d040314031326041a0d020310030308010e04020d14101b03060e250215041b0803030f010603020d0b0a14040b18040b0606070f0b07020601 68
    0x1d01242c42416261580c80488118581d0b40300c803400c1c1c920040c8207400b004004400d4042912044c0c0046015444800040031410000d080c03100301e4000d10140800c2d00c0366103a0b6010b09514112081e14203d488101140c000c3d641c00f0204d080e041c0c0724580a1490882c800030801091041d00035001c0d090f42e0090751000c10583e203800c4010300f10082610080e601c000b001200000044018100a0541c008442035036840c04018408005030b89070301c2400164004407040d844001c0d51f141c42031000418801040c6800340c100440f03c58200803000800008808481c6004000103000f04281c0131400300d42e90f2035450381c0c030b01070070441c030004c1c0a040c4110400d420088001517404c0c0000a490040301220240c2403030364600b403001d45c025400014100006038490038201c4c0c480d130f110402c0b00010140101d05035401a8a074080004981c074040c9030500c00c4c0250000b81241c610800b06c1c0583c400d030b11001d615000d8a800001030414000e01400800400300d03056940d0400c003032507040c83d0084105400700c0d58281d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 301244136 1250 301242886 301242889
    0x3060f060b0406020c0f040608030706060e2a03060307030c0b09090c070302100c180b0c060c0c03040b0702010309060c02030d141513020c010203010f03030210020f03010e0a0b0907020c01030b 84
    0x41c4a10300c2610b0050b448844031702c075145005141e048903060010800564156280380040c15a000400e056603604d55543c8108032400580780c1c440e9209030017031042e002d0b80f100d603d1403c07032210420f1302d0302a00785004000900031780c504010700406190010380d01003906542d42c6c1b4040c07446d848003100c03d00444114000c1410208094256901a075264001d0a004144c0605290007043d055800b40c0420000c0d545000e10030718038104d010080c2081442284c1e4842036580401e15000000c0c0100070091420031002c004004040140c40c25600c2d0a844c1682d940154001200070305a64603010b410b442c601043d26500c250008005c2001c1c0c92007100500c20546100c0b00152040b00c1103802a48006880320403086600e0700101e094180c2540c500014180494010700c01e00320f030400d0300b100e0103c4224180510506404111015415070f1204c009e610307240300315941d030045000612806000030b030303032002003001c07d0b4440c1c001002c2030802800c000300b01d142040000756908803401c90540440d1424030380113201d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 301245386 1250 301244136 301244159
    0x307080d081f033e040c140a03060e090304061e0212040603020307020c010903020915010201140907030c0902040609090b0102010e010e01050109060512061803130b03010e090102120402062203060f06 87
    0x2000780c3c103130030b40300020b60440900c40605045c0b03040b03034100408140901c0212032168050701c0407840c0c0c1c0d034001800600b89030ba502c44a00c00508018616031041c8810803003140c0c0001c4242812a48880040c0843c0020005902e80118130403100a5200c0100c0e000c2100c96040d4040e500c0f40200350300301e41040d6202c50043d100b4114030f001c00380d0007121190004407000c00e090401101c1040601c0002043c41041400c0c0181080941d48201540c01100041050111000c1954050300441d141180b400740b0308800900300c440c8510998451584032454014140c0c000c4d4054020794500ca0001c2c4103002c500c0141c107000300f07400d0090100035886c00070041681d00b0a00040c03100303540824000c044a8507130520001500021074000c90b001c0c8010030003406085200790310440242248103140d0307129410326120610321040104501000d0b0310500886210101822a42d5006a010b4510ba517136202c400c014160160903ea460500c41480e59a0010800c00c0d2a840900f0014905504000c243d8403034818040c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 301246636 1250 301245386 301245473
    0x1109040c06050c03070c180b06030c0d090f0209090606010f050901080109090606030c06030c0215060f1011030c06090d03060305060c0f04030210030e010b0307080d081f03 75
    0x890445032105100da140148010a603469a82d42103e060001560710f01e5101651600190644000407450310842a41409800601700c02200c2644c258a0700b241d400b807641c09442449901c03180c80380703414410f02030316a85118a03190041c1c403540c5503140c8141c0880d900e00094a496001900103003080c80d03003a01c01d1040c0ca01c140c605a40d1850940d01e001c0241c00135004810007900c000303944840010004180d0401c560040c20b8a03100450700d00410030020f828046034400403010325240310304200e016650f0a2907d2880315044840140c00e0a41c260111058610a01a0007a9200000d054030b080000001e075030780729008e02c0045824000400c801102034891521004040341c2c84800400d080d0448071700a441408902c506c00c5042941c0e0780c0009141d804c51007a0007001c41d1340c070980307805ca52400303004140a0030400e40061250902d800f11043d0b0b07654850045008004410700820030680c4224400810050740308140c0c0740d0f40f51079042c008000311051207615440242d441e118071400505400805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 301247886 1250 301246636 301246643
    0x3005040b0d020c0712050f282a260a050c060318070303121505010503060613030605010803370f170a0218010e090a0c09030c06020307110904 62
    0x60a0030032802100340070b07401032440c0008038060340501080a419171010760b80d840e805003000304800300203001c9681c01c084a00c08040c006401b140f00200a00d00141042300c01c2c180e101400a440b01c403600000a0b001c0c41c1c9041c52025090150800221455010005d503541c55402103203107145d20708203001c10358441c00c03ca00180144c201d90742c268017902c3c0800c0a190710401d840c0b40a1f0340704588016480c00c0564582049004c118100e0008042c07820510545030100c0940342c54a20107070926001801c28000100301c6486854001882c50844c0c14505030b220085034000424401d40d6181d66a0b2500c07a004522091000d030f146440d1014044030100f000c01c0414241c2c1000d0301d0f00c901080d821100d62000610840600040500544020049802c40c40c4101013070038005031150108840c0c0c0c021500802680d40c100003424891019961320000140e4000c1c0c0780381d000050440c084001961210b0080e84060180a00b081002501d250044000c0c6a002d116000d48005c6655400400c845884c00f900d028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 301249136 1250 301247886 301247909
    0xc0616030807050c03070c060917100c05040909060b01030b100f0503060109081006031b0e010512160608070201140c03040209180a050f010e0a031218300504 69
    0x150200c0d0207901d040d600940c0900e04503113441c00c1101011714650041008481c07107503141c0000c00002e0742c002066406007540c40102400c1c40c0c0d007000c180395501120740d51041e0041d90394000100050007002228020042e070182070200720700c40d081120003080fa0800081c082400c0100c1c0440d585040c809401c1444550746804070200701c0d0301703c03c4503503401c01000305041c8807290b540880c0c4503c0410a00c42c11101480d03003c80c400f800c6282182c40246100740c0c4004101a105007400501c220500d450b0554600f0f4a010b854440300300005854152241c902e50340d04030306440c002c11001d42c0a40c05600c1140103800034850b031103104a441c100841c1c00c849123218620148040340040c40c04031941d50704407030700381c00a05903002d407010898202132644404a4a40d4040c1c0d01c6e05031147d42c00c0c040e441d910b82459000c0c0076004c1310740d00d01622454003007504409490741c40c100c005024201000f02a00c1c580c0240001c40c0f000780e000d43d400401c00044e200840031104204024407024803034070840303040e00c0c04203280 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 301250386 1250 301249136 301249177
    0x804030605061801120c0b0a120e1203010e1b03010b0d05062404031406091207032a11040606050a0e04061805040c06030b030a0b06010c0c0906080c06 66
    0x1000020300c0090400d030750201a0a5800c0000b000099449018000c0c3d07035407001c58417040d031403e440f0201550b401801c040b10107100640f4042e80050801010001c8804c02060107680c2c051401d00300640c0b01c1360b44200d1880400003142c1c1944412031071344540341034bd412550408007014400c4850000b4410844c2c508020400d04040e4981c40d0446a000b00c80500303118141c000c0c15448003190803405402c84022032000c1010014807590700b00300030402900d5005003080b81481ea49072511490f0100810101c0b40300006c90300d08244c4240c00c40c0c0c040325000000580c0304602081b400e044a208840151740c400300c1e080d000c0d00b0340d203800e11441c811030700783e511075501d0240241c8007902d8851541034003d92103030f9180e03000185405d507a840280c041030001000070303003890700385408401c078510b40d0040c0040519003440c820441d24006161031440742c00c1001d1080c19601c4000480303940303440305e00003887e6043c1200001906c040c290402415a140c07102a034100c0000c03601486118003d40030006a840b00001d034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 301251636 1250 301250386 301250393
    0x1020408030405060f160b19051605280203090112021611030304090f02070c1505041e180b03010f0c0c0204020f090303120717010503030307080907090c050c0106060804080403 77
    0x1401c5610240340141d040c01c011400304606c01500110070703100b00d90041c0230040c0150650009401c040c00240c410825421300b03903000c0d5500b00340ac0c410f02c8240720b0300044c0c081e1564104406a900c9200300b103645400c502c03492800a403250005040103000c81c1d5102c0514001d00050b0081d02c080118081008003d480e4649a5200c1c1401082c0f6043d0540007c2201041024440c0a40715903000e02c454090380d150010300d0301541c480e1850b0b00c100c250712030200c1d14900c002d44c4a011101121007510703285815000345c240d9080031800e10f41c4401325100070301100c080c0001c4c0c150026201a00c00310f000300041d058035440c0e91300741e84002019400068410780840018a0158040e280c640d00d40c4110300e003052030701c0d0082031440d070023080c1040068502c1020443c0c89030b8484d02d600c88808040300c00c0d41a070351625000c00d94070701010380600180213084002407007a41d4200310300e81c02070600c030f03206110070003c1c0100900103a100b1000c071441c65003003030004200180600300c1c4d90b00480c0e11071482481e2519649 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 301252886 1250 301251636 301251649
    0x4110907051b0106030c0b03010602030d020903010b090f0601030c0513050103180602070f0b13030c060903021219020114131e0206040308090405062e0e06070308010e010801020408030405 82
    0x6003110248031040c0580110110110444103075000b64200010f00d4504509040700503100b0355106459842c020801404110740c044140e4141045100002d030702d034082900001e0141c01c00303004003078100940c2e404100040d01e00300c019074043d050a072803c00c014582a502160a8840d6401c5001901c00c800c40421280d41b0070b03402485e0007a4045503020100c80e1541d01c00c0140c0e0f001182c20b0b03a80060492100080c020f202112641140340360883d20000340309075502803c24480d880c03015000310b0703452010b041418002d1001342503c038401019507540c2d600c1d020058061401d2002c1c00b000540c40c00c000c1840c600106d652146c040c2100f00811850b50010703585203203882c11407280003d00d290214220000584503c405480658806c2902d5600c50444000b48411643c00504040c80343c0d201d260440380d00392412941400012000100c0000003204080640c0c1010070003681075040f00780020079030141640425014145d81c81071950000a991741e503400c9003030303000d14050380581d40c00403c0100214a02007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 301254136 1250 301252886 301252891
    0x6030b0c070501062d0f050306061507060c02010c0e0306010b0f0a14030424090b040b060a0b0304110405090d02030d0b0a080d0f0e120a0204050402040b2e08041109 72
    0x1c0b0004110541c031042c600c04170100003081d0251107100752140c1c2c00064454038043c0302405103424418181807805d40000c0e0345403c0513011900506003c0510200d04843e082220403451b00b14900340110881d80000900030800000d22000040c09025405098600070500c81d0480707000c08003507030900884644204072640030100640c00d20945030f00114540040c94040c510960060410911000015602c2c0c3d907641800d4040484041c40c01420b20001013404001603045500725210700390664442000ca40c9403049600001d060130408001c12003001801c000710030b40030409580600003510303450803a65441c80385069110140e041031217880401505540007081b030120040181c0300c1155508a42e82c02c041e440349144001030b12090003140415003007406220071140070390b400c2e00315040c0342e0aa80e0325105420f40082c03080d0b44440c045800c2d55110703000b41010400050038175118920494005c850081007038400f905007044001c0705520140101d01c1184519008041d0200b0360250504011918070300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 301255386 1250 301254136 301254143
    0x206030c0705070806011d0106081501180e06040e0a15050a1e02030405011b050a0809070b040e1009092d06060b04080606190302010804060905030f0a03050a06030b0c07 74
    0x602110010039410010764004000381c5000d4861541800400c41d1f82d011801c4205040780d40c4100101719007640503220075030120044502d4800481300c00b0048481b12030a01d10610480070200c03000c2044400c040c011406084201d4003005403e003c0310f407058890000000280ca0001c0c480b000385c60300c01460704000e501c5082d041c00003510b28420b80d14400500450814141a240d0210801c03040101c04d2041e1480c0b84106540c00d410111032400c001d18501c2206100800c00c0809004a17030141420880316018240d90b003003594843c1c0d1545080d69020b274048401c84c203000c51b04200011905c0e081d124001c070390b85e00044e03000806c1c4418403011503a080b40440c03180300a4080c00400010550510803100a060b401f01c031207940b81d2034181070600d4110050b25142c8900044000350008640b0206070a00703c1b6170a00701100b842d0380b10704021009204071031001e0a40d002c001026548a0300400040c01d9415068800b0000c40d12840e0641e811620300e4000200303a91105804208009403a2000e804403501c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 301256636 1250 301255386 301255411
    0xc010c050c0d121706031e0f010e0c0306010e060117131406060f120604111311070303110c0d030b12030d09030905030d09090b0f030d12061d04020603 66
    0x1c624040755a042d003100050b10302c0a96841c0c0b1481e055840400380c4181c90380c1c0003c061290a2103400252113a05111420070700803128442d0000f42102400500c0710310514000800104a07280071507078540c0c210708a010b100380a41000815039418940406010702410307507407615a0400241d401da03403004041c3c080314040342038221000000d24181d254000710f030954009040f007030030408140314050398620303640303440390700c0d40002242c1301c0d00009010340e80541c01c82000b014054106012407841006804410450790403d030348400820b684100510203613100365030411101454044c2855607000e6203450790703480d03000031242e03582c014800e40010312016001880d115812100e0031496155174001424000300300e4541e00d82c042490b400410b080010b15040d005820300041c44200105460014045c0d425403d540c3c40032152103860703d0300c10004554018003121280d001c2e0040103084102840d40f200d182500300103011a00e018030080207495482040c881020301d41721039081080b1900003c0001d0104034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 301257886 1250 301256636 301256653
    0x140313020d060c090807080c012703120203030403080c071e06020f0c0a050d02010c1709160e091b0d0b1e040803071b030e010e130e01021c05090c010c05 67
    0xe030070f4400c9085140c19912241111341c0341117405030a0884940c0081d03415080101d003403805903080900410440002d05000c8465029030280700c2400380540c0014101103045068000c8858000008500480c02929592490b80d604a00b0340c0030b40c8995800104032901c8400210200904800882100303845540090700f0052040b0412082da00404800e000d95400607080c403060001c140015196500144000c0c0100149003d0140801400f038144031400095103000520000d82400b01e24510205061002040381d40c0c1c42e0710001e02e0740d06403211106402803a9000070010020701000031000005040103c1980403500c6040c0c40f003600404c98208040c208450781d040141ca00100c9114900c2800209c1d107038144004010032254408013109104000c21001d000840c0c3c101244d0400b0342d600b480c04a81c000c281c10049210f8541c2032801e0f4245c0c0341091101d00311948190083c107080005aa5820344044968400200361213081c0ca0303c1c409a0000ae0320780665501c43c00c14007004c0d5028200311070004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 301258992 1106 301257886 301257893
    0x7050111030a02040e06040614060f0c19060b0d1713050d060c0f0c0b130204020d05010303090510031406040c020a050d020606010801150801050405090139140313020d 73
    0x42502150b0f600c0d40b2880203080350001000c64081d2128033740007091807100001d00000840e60300e0f04003241c400d51424000000d0302c000c1c1c1c01008440c00c801c92001c00c00803d5020300c030101c40c010009140803035640c079221601175242c1d20850b8002140f8032980ca005201c1c1c9500c140240800c00440035071008101065103280c0c10003d410300030031480c0b4841c40002d00910a00303806035001070510b0b00000034560801d1038501110810760b202000c6001c2a40110101c450840300802503e0f20700d408945c0300e060980c00100b080356540102c8102c811940c481c1840c180c048926800107030300080400c4115680884200d006180c180040d02c0e0802d24a10040d0452105001ea0b42c015541c410005030300389401d4000703030035010350582100080701ccd00c00c025130855284020000c54401c6d0310000718081620842c1c0007014688551032b0305040d600c408a04002040510a00740c2c0c2c059070342030b80352010 = true := by decide +kernel

theorem cover : BRFrame.Cov 301079136 301258992 := by
  have h0 := BRFrame.cov_init 301079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 301079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 301079136 ≤ n) (h2 : n < 301258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
