-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1230
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:52:57.250801+00:00
-- url     : https://prove2.me/submissions/3788be89-ab87-4dea-9330-84245c12f111

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 221043165 ≤ n < 221223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 221044415 1250 221043165 221043181
    0x1080403080a1e060b09192106021204060606030507030b090c090a030c0902071e08181207062c0303090103050910110a110102030f0f062d1009060215 66
    0xc904500707424a50404c4404202001600082c28030902d003a1140c034020301081382c41a003009081e001e071480c03803603e1403942050075916004900c1d9440c0161001031424803054004401c03a4400c41e4180c1d00207403100f070100a0361758144181c55100d603180c602040080c0c002c00016501d07000141202d1407001c00415034602a030354469895008503480381b540c001361651880058003a4101d0750044e54003120b030100b184a9021000d480040140c0c2c0812603034901545040b024401c81c480310349064000c880c0c20410b1281003000c10803000a0091603e801c48200400344120096041104480c03101200104035407807136803000800c0e02c00c0d12809080108050303403401a1140340943d10602c207000c1d141041c44800352030384804001c1c05500c00f2580c0d01042c50b0b2200c1c080b45c0c02d0b4481034509054801600b00012000480041a00e0304854001c001403d0207500c0b1700b0f182855801450301c3c40b0712400d294050940c500d4100d2082c4480002818154141482c00b400603450345200c40303003246a190032400040c00b41c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 221045665 1250 221044415 221044451
    0x140a0c031404060c081006080a0908040e0709140d0503030406020309031608090102010c0509100e01021204090b03010507020c0904060c020c09010914100f18020f0408030a02070501080403080a 84
    0x40040a81500070780c9024100400500620054a00480d00c0000403031040d0420421020039100640c8440c00503448400a0708028105054140e03206107050001007082c02480c81014050802e80c3d541100d01402d205c1021040140072540611409540080f400003880110599a01c01d03041f03c40140c41c6c2d61826031660a51050702c0d040314180d0440c0c0954010061440c0141101003404c0e8001c02501400c8242503d807881481217441c0d00c4000791541042d01c0f482010800302490040c410385021307050350240001076801c29006112141d448440c0e007403450a0911407980e0080c07070f40c0b0083c544c03400001c02050007108040d0014040310b803580064221203008020b41c865144026101d5445982d4a0310b1540041c026141c4131119040ba0202003454200c1c142c40300c02c01d5480d000e8894620600c0d041e2080441120034801c00c4409400744001950710b503004c0301400c000c0445070069559100800c078001d003030101c2c2e500094144540441823001003944104029409045134000058a07241c031502c007204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 221046915 1250 221045665 221045681
    0xd021c0803011701150537060c1104060605032a1204140708100c020f070807180603110409031101050a0e011805030a1809020a051c140a0c03 62
    0x1003900000002514000d03040000030450299000b00501c1752010034000b43e0450354454a0740c0200070903510b4080d00301071104034941c1400012240807101244441008208440d4040720219181240030414000d01c4034950b14140307400c403000c00c81142400000307030140c000030b006400c45e40c00c00081804c0210a80000741c05203046620303481d80b5802500c02524007131b1000c8800310f4046107040d5182d003080c04002078140c1a502030030040e14048060f0040130300142062020182107105a10b00d00306200401c0c810b8501515220014012250510b1600400b40000004ca880f100b03240c03220800c0443c071750066200c040f103c22203001c10200e0403400c00f00c54000030184410030795482d007018880654416070062910910783d0000740b000c0142c5000b6000c0c1071580b1600078203507410800c6034003006132103400e8105801200c1d1943c20112615409294100e8125958010100300c1c0040e0040d030b5940c20014140642d40351050900120119900000c680c1001410181d83c042c1c81e09401944a8026001058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 221048165 1250 221046915 221046923
    0xa060207060501050a15020c0f01090306090f14070f0302041109040203070c020306090a0f06020c0703080c0102251a0c1b06010315020322080912010c090803090d021c 73
    0x5103803503840c107109008007800e1003110701c0b903e0b0741e000004680103601242c511415654002c0d08140c04040144205103404180301410028881000710002c1d48522641d8500c03400f030118004412464940f8226100d42c060800ca440e0b403110781d042208580c001405c071700fa258142d0380440e0100a81d0f00b424114052000400c1c0e06c07500100401041036030104080b20024001c40413102d990321954403040d110945444080c085151500007000450038a030001d04150651400b01c5245036944d0b00c64210a80002201480b039075000100c02c1c490440581e540c02c02c800c0405a5061581c03042e82e9005801c4807240c4249502c2c1d180540001d6106130108140e9025206c030402c000c10ba14000700e0202c2e16903100f40012075072088140022030080549100356441600c001500f82645961504241e02da600c01d0b51084030005420015031450fa00c07180424041100040b001107a034600c8a540980000310300c1e0841d020503030083c440c0e0101c4d83e6460041030aa190103641c401e1004500b40110748120010301c401070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 221049415 1250 221048165 221048167
    0xb071815020607020114130f05070504021c050105180a0e1f0603021806060f1305030307032d0f03020a050d140402090114090c09010c02100f110a080d0c020a0602 71
    0x1205240c010503090310407030340f40c1c2c000c11192400400d0a8000c00040d03800c840314908450140c80010804426021901d019004030f82200d543d940000e0140c3e4001900306500c0308081035207805205641c064075002d06011240103000c0303e4009425400b50000829840619403030344d0214180707000a0000c0c00091403007071902880d01002c1400400502010300c0100d0281d02d045454501c9043c800800c41d0040200521729407030030300300300070741c26940e004110f211401009041001909507400c100804080d88240c549215a103e420821101c100c0400c02003152100c0701482c40300201d070300100d0950360405c641001603c0d507030014812286809148104007d1500d80465200c02040f08802d4a210307602c22207100c515682c0361600c41742a44c40c41764215410504c02d902040c0880c120034050000404180b504c0001c2c1d00b20b50b000210801a03550030140420b541c80816100c2942c8860340d006105d840100a06030651107a40311884d80c4a41000f50201e02c3d078405003003880d140b00b0300c540c58074990031078825 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 221050665 1250 221049415 221049449
    0x507151a0402030c071b080d05031501051b190605010902090d120c050a0f050c010203041d07050706140108010e12190c050303091f06050609130e0f0307110d0b0718 72
    0x1b0b03000468002c440051080c03051090401d0310420489104826010401152250403c01561140c1050202600a800d441e554502d025400c000d079000c0400d4103c6043c03904403890408104490041e00a80721080c010041d14403640c81d48040070807019400000341038401c504d00c800300c800300000b250003002e5000d40d65840044c060160305140b0790a0140d07050b87c86082405c40160790768030880c071582d09000c04140003500c210b500c0440407580941e81d410001e00d420150340c1d0703074400c446444512000d0b40d14002c00501c082502413042c1080c0c0a1604000c212862124074820000d00500c24014005285400c1081c210703032045280111095012080369100c0c14480c10107038841c0a54201c0700101e42c42004031242c0c4040a001e5142160006000140f0b0701000c5d01c01d0181440d041580d04070682e07111101c040c1c07074240070481c401004000401031038860502d481e000d40320346110180b05210b608001d074650040b4220000b4190007401c182010074105821140d4483d40842c5580039400d0000c60280f4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 221051915 1250 221050665 221050703
    0x6061e03070e09070e1e040c24020d230c0c0904080406020613150e01091b0303180e011502010e060103030e09060a0e0a090c0b03070507151a0402030c07 67
    0x4503e000d4501d110a0790300c0243c880344c1e00d04458604499003618510060040070382c00d10149801030f0018014040c0d0710b40c16448040400745c10415001102028a82c1c00400751001d505224440b40049a4074010315030150317060b030548c4100d800b0420b40300031440002d000c040c002e074100200d81381800c1c0036109004074689801d00040d01d4202d1f204050141c02581e000500b107004200f80344640541c86902c0b0003140500c4c82940e001400504074400456503544200c0000c102d18035401107401c90075407060f4a84500714039008140b0480c0000500305441a0350043c400c41c1c1d603051466065492554250f024118a188124058010380d42d196156004280012042c150700c00c044064107001610141116141d60301030002030b8606116220300743c0c0c0b00c0e2000c03410900d181d8115003e43c03405524240304183c0c441e00f1a465030ba03c01c0e11003c02144000070408104030320342ca081c5040d9582c004040003101510402081c0e1404c811000a2195038008005052112050203945944d90803026040d0b81050a041c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 221053165 1250 221051915 221051939
    0x301020c011517010504030c0f02270a0605030604050d03050618010b0a03060b0901120c0e0603011d09031813021c05010801050c0c12070825030306060c030206061e0307 74
    0x1d2403d04409000c1c0d5482c01c2a014064140200da02d0b640d6108036218a03110459450101c1404990186501c030700000b8002624642050155020300c1c03004070f0b8280029948200c0f50503a0000e4065042103040002103034010074003440317459040c03d012840d41d5910000603003c10440701d2240000e50401d0010070a0020207028180b403071331a0301c0820800e41c45d888101e1590050b4a01c0da8001421601c0380e00707198290360443d80c5402c145041c0305035259104d000060045e08240c01c40804081c0b5000d0340d42402c0a40c0d04c516804c076a049028614058039043d1001c10107195001881c001c11742c40006e01c0540020307030704a426868107504102c48400c0301d170710018054002232181d2030b40e540c02c11011414141c0c1d29411584410f44c10002810004540c034801c407002c1c1c0140f641030340d02120900201c2000d03480012166803070000c2c0701c20440e01c012645008be040700c0c010703000720040215860300280007940014000e50000780c00c5031100d280e039007258121451700c031400c0d00150b0540036211000411441c151 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 221054415 1250 221053165 221053169
    0x306070509090f0105130b0a090c020f06070503010b03040b060a1d0403080606030127270c0602070605030601110c06180901090203040209040201050c0f01060e060117070207140301020c0115 83
    0x496000140c0ca0740003c5020280d000c1c000d082d4000009601c844041419902000007039101808039042159104114421503164500010160308004508050b0080c1403188036404052800c2c00390455051031010186030100400041450a040d404502c0a0383e400728948000c0020b0040304190782e48000c41c2c48404002545d04030081002c0d038000c11054540311040e04e050300c0d111040c0101306400c408200010354488510006580c0d542c110000c060a90506601c10b01e507800070710f80d4013547c0e807032600e03c105003507940c04501150808803050008540c080c003160b40001c000d190010080601c10302070350034000001c40311944050006601e00c1c01c034495510307001b200401101c410402d42e981740e000e602070380b200b202c0095214126100250040d030082001d040681480400c80710001030b41136829003101d004c7c3c0c104045801d803030b10401100c0d6900c80e01141e515152024424900e050100004c2d40d0380505000d4042c0d4030b80d5412007001a510b0945c1540c914240100c000e000d0305440190340b0041c7e600c1c42c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 221055665 1250 221054415 221054419
    0x906030405073f171608030a0b0102100b0d11010216030506010f050315010e22030e09060d02100e0321030610110a1e061a120706021207050c0306070509 67
    0x501001005415909140d040031070300002208030141c4200c00244290740442034001200085000490115003120047c500c85e600c003140004401e41080c0c006403034140004501c0100c0c600307020f00212551142c184924043e6400308580840f0760500005034109045030344202209080800000103004000036000e040b1508090160b00f03d41d155810301d501d8280d60b655106010031100d0042003c241c581802680c04028800e10158180003140007110382d0007907100580002d45103170000b001c02d103010110b1581020040303655500743d4201340c0c0072034803d649a800d1a0103101d8410748268042e1018003400348002d0501000c02c02c5c1c10441c0b07100c000d0a40050350040d0190040041042126008040909001030b45500074a20700d2a0307a074441c0025481c3c9422b4110030b80d02054840f000403000c0c00b42007042d600d100c0e00341101c09121401c3c8045074440000c028081e41c004036040002c240c001c184680000141700c2455620324040c10654506080c03524041e0709841040c08005510342d00c04080d110803241 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 221056915 1250 221055665 221055749
    0x7050102070b27120a050c03040b0406030b0904120c021201090c03050c062b0f0515090c041a0708040f080d030f0b100e011e0e040b0306040305090603040507 69
    0x8000c850310410010703a54514021360100a0400c0c00c00d161201a02c00c2c1c8000740f501c3c6180c542a000da950441e000356000303c1c240382020600f800380f10303094000c00c03580880c2078804412620300390701d4201c07240014a010005010801942d4015502d80d035011120100070b000080c04501c0705444c0000050180344010740b00b40c00b9005500714945003d404461761080c441882d40081e00b00103944107119200303015164002a603c50010590805500038584148140503181014144101c1404a0288000d02c107560154040005000c40b5a0065050b81a403003c100c0990722840613103000d40305803145411404495071101c41c0007600720f500007000810f41005581c11b0042641c8880701d0000c2d1030b00f4014030b0354080c020104114078284140820f60300308105150070881c103400d4901d0030390940d13122041d2200160000c1c00b03288160920380518580110150000e24961904d40c400408502810360a140b01d213800101082c280b00f4100b20003000b0703203010142403501c0710210303103680507202c0c0c07401e0700903100c0030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 221058165 1250 221056915 221056951
    0x30a09061821050301051e03070b040e070e0a0603021312051c09080601030308041a190c09030c140a090e0313080c01090b0307030609150905090604030e0607060207050102070b 77
    0x8100d2052000410394491600b16400d05041106003101f10f00801d4441203c0050606565801c000e20001040c628001568a505101c50301802104c010156400d1140ea414013581e19100c184555040390403901e401625140310141c0f910304261070740e100081e03c400c030010081c01c0c0300c40800e0064010303600803010304900420040a4400b0000791040c0700b0f241d0003203c010030100e805101410303031083c800c40b00074075404110300c0c0524100405560003031240400e545000b4111941340300700e6040601d0303400e242c07140c60b01e141d841d0900c80781140100100381e44001d2828001c1d480d2000d00d0405032202000a1100f6094040310a40d25001510008444850020001440c0c3c1c008610701d0000300041e510007100c54101482d040c0940e202510890415a46000020f1049100c1c4034000135081d180c2d00e01c45031280b81144a90603203c000d0142c6685420850900000940008580765048415030368981c403121036041c40c030024040c415019180d0750002483c03000f085519602d82c0d10070303d01782c2d6200609007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 221059415 1250 221058165 221058203
    0x60105011107050103051e0702010c090803070c05040e03090a030605060117010e0708090f0f030d05011502061b040f06050d0e0304060e0f03011805070e090102090d020105030a090618 80
    0x4081020220503030b00000014046948290021644641c110030384a818019040c0b80c4403014008503a818011b075550440c0881040e4031030544401400604000c6040c040c6944510700d00494a1040c68800ca40d10854045080703014800d503280402c0041120314040d6032030130017402500b800c0f9445400a034000384070300034807501c4078806c6041c4c40071080d4804180d0388001c2c1c10780c1c2690018015074924400c0030f00100311300c5801c0041209101514010f9615403080b406050292541a005404064580d100f405a11139001982e5079100c050b210034a28100340c5640c00780c1c0c03184606e030010740084070980e02c0458400d402500034085614a10f8041040801040b0741c00d032280624090100083e24100800a03140380c070840848021a00a00000e154450101c2d200d80c03150a21504641079040000100721101e4400c01c4039a00600c034400a41c42c1c0303426080050074140e20350800034140700c408004211000e04540c4140109076010b5420000040b4220900841c4201c00301c0440f03085135080b500c42000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 221060665 1250 221059415 221059427
    0x90312060506120703330303080a0504021f0903080a110f28050c0405090d020d030b0303040512100c0210060f0e0a0207031103070309030b130b0f0a020903070b0a0206010501 76
    0x301000e00c0c5840070301d865044045000e01b01100460030f44000d9a11041413240301449105030751901c03010080d162070f14610b030180c0558401806680d006180030100409a11010304040c03a00c50600d4160603030b040d4214040e5500e800541018001d04004101c90303481c03a41003d14050f5034140802221030105074070b0061503540459240c403625250120310f0303c02988001302c040600c05ca00c20425100000b920300b0200d021180f00300e404ca101c541c4060030040c9126010b0090888070311080c40c041c0111002100030964911a911400b4020900c0c3c07803800b1801d0b80c082c0150200c0c0c00b940c0c0380900c03400c02000c034000e540350010080480c08602d8204001603407410f066801c802c1307030717071040088586983c0c03020548002d400200b07094007408451003601c00014014001071030901e100e41c030780420041c110b00707020307404081c010102c1d042c60410b28000000305100c0401180d1051030303054500510b0383d4812075500170f40280a2f080e0b406109044021840d1070015010b030039101002e81c2100c07010ba030b0722001141c10b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 221061915 1250 221060665 221060677
    0x14030a0317060d0803130212060108030304240513060f0c08011202010c08040b030108060c070f1401060b0406031b0302030403120c0507150209031b060a21090312060506 74
    0x10550980302407105400a00205500403801401e5514070805034490110690080ba008090314001c51204000c61920002c1c500c407a04440d002040a58107151070315981e0f120142000d828180c004060800c5400c1c640c4201c1e0104c80e801e5003d01550074800f01242d02c141c0030950032180d07541450211014100c030b074820200c1c100540c0c2e4404105920f4507a6048180a011005904000c0b00380000400706000600a00050024851895407036151113450313401c001001e424400401d104101c60310200d010001540b4000d500030524816046040500900404882c0e01004010f0008500001c42940507400140ea40301e24885412610300038400481c224441100e0080110b0308049800041e408141c0c8644e43c0035070241440344c034108294030f0b082d01760b480900f050010b440c5c0000c0e214410741030170710040e0001700d00820300004402001c400030b00c140c0a030394034800812890104c45050078440d5000c036803510245031400c101c0340300241401004c0c81e41111102c41d50300e08003800018542000022035007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 221063165 1250 221061915 221061917
    0x9140f0a02090a02190801080c0102010219050912060c0c0f0601150f0e0402030114030c042703020109020409060b090c030c040303030c0c0c06020705010e040501030b0a05040206070b0108010614030a03 88
    0x241114564204000e050020782440c3e80b1a44c24002e4041015141150194248480e21188180c1d0303d02421545030141c42503240c0d0440e4010300c914900da080104000c0603119175820304940368241040424680c01c0b070015056810312a807000d0004400031000100ba1400d062400e5a080070041d0086980d03890f003e01c1000c291480700749514009920805800301c04807a94640880510000c40019007660403c0c2c0019212200c50800d100c603a00d010043c016030450151000d01ca0035030340c06090301003102a100f017000c1c02c4428503403403800c0500c00c0d0b0041203043d03030091080182420310700b0f101008100c24281140a0008000030030400d00384101546e10521840200500c0c1c24203542d03080740a0041d0708030040c00e00c440211071400152541001c00e02910b510b03401000c0e640e182c80d00051141d44116405030003076103032100610100d050448800da100380792060124840d1628400300d52a48540c104c00340900743c1f00000440c1812041d007000c0304680c6010b84462441c0301c01400c16865a000c040010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 221064415 1250 221063165 221063173
    0x30a1416030c260708010e0601020d0f11070902071712150d140d0f0509060d32010810020f09120c0307030602040f0b16030804170d09140f 61
    0x545544240c00682200c000780c074244250160490582512520701c843c4201d0b0700d4900810803011603840102035005042e1405c00000038103250b40003075202c0030364540c01010003201503010308465000d07031020030300010a1001c603010a42d440c07540c2c10003034100310403c0303a070ba0100c015080401c2107004140da00645100c203041078130362529281d0140310205148040d4100119102150100d01c0903040281e854800c2005400e00c00300982c0700400c6203106405c1042840380902c0300c00070300d0f111101a80c0030520341d110001041c000c04510980341d9401202034100b0f844401c40a4004149196407050403903000d50100c0d0300c0312500b03500b100242e0081d03a5a80102e00020300c00715985107070002d90820314440c0842038850046105002ca814084203410603241c85800007005c100d0b04101c41030202c010a4010807243c10110008020b0500400900700a01000a2140443c0c01d020161011a851400d00c0141b41d07502d20074a24520040d102615065444882000b98a14a40070215061080314a884007078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 221065665 1250 221064415 221064451
    0xb0306060105120405010902040509030d0c18050105030915040c0e0f0408070204020702130c0905190302090117030f0703080f070306030803070c03210e1903091a0c06010b030a14 78
    0x3141850041081d640d46d034032544a0700158449200341801054244059590707082a03d402c00300760303442a445d400400a903604d10340903090f44106c4820580f107003440c00c5070303484e10f4010516150840300c5030040017070b83d5030310284402c0003c04440c010440326654105086079848440c0011030000c1102d02600441c1d0400010780140b40603802014102c0c030040c00010b40103011103030709045507040d9131010046443c00c0c00c14402490501131130244041742c4140b07a560310b8111382c04910f010360103124030f0100e6464050b08943c040814000da4408407a09d58031140c8408031802d00900509082c2c500c44140042200425107140c072038003982c0140c82e000500d6614507159034200308c0340300702d00b100144c04003c0b202c3c5000c0080c058100000028102c066804179138807901852890074052250110b03000c0c8075a64a40c80001780c1c008800e002210100da8800640746003000181c6060b2003000303003044c05400b6400c004120495a000918012003801404000011181038501054642a80c0040b1000a040c0c40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 221066915 1250 221065665 221065687
    0x3030106120915060906050301051302010c020d0b07050a0318030e1201060915050906100207210f03080114030106060504030f080702100512240f0a0f0902030a0b0306060105 76
    0x2a4014504140c07900240c005066115018198550103c94100781c1d160042002510b469000d10340180100f10020041828440c2c4031048002c0380140080c144403007000041d0075991803403e0700b0078454001d0020992898070300d000410f83da000c4000240070903c4c1c80074482085050b0b4144812145d85511894043c0c01d060040140c10896418500b00c00d64a030800412540c4541c000c4000c410203010f000b031106401c0c01c003000985580240101d001e1900500f119410a0340002e45d0000c07580c0304900c038644e00c1241580d0101000d101c0501410f905035202c07040c003c00d544103c1c1c041c100c62218000c00c1d03200c848001098241d5410380b164400254062005101088411409040300c6210740512898004150f020403181c0f480d60ba9100d020800c04a0784040407001d00e0b0b04280d0005039030244818800d58540441541120042031a0280001500b5606280c490b01505030150a1805000b1341603075640c44440003035842194215502810001040b01600300024258040d203016140c4504007142c00791 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 221068165 1250 221066915 221066927
    0xe0a02030603011406092806090e0f0307020a0902030415090f0c060e061206040605030109050610060c02060301060518042903010509060f091015051809030a18050907050c0d030e03030106 82
    0x1881d080385000c00c021f400c41981d9442040020014207101040d1000000002c6042c019030b4289024943c1080100c0801640c03089007800540300e101d01c0c0180c803900c990800e06100780c0c281004241d004d140030b010409001800c100104102e00c1500b0101059845000480710003408100007500000d05215a001346a04c1510040e400000540000b9807140e4950010742541c0c072019041e5801c2d0008070511031540c00340c507180c601908060615801350121a030204600344014413079001004000b0908029122560f000307060304040041c0305001d681100c1d0422100c191000030154041c00e07103c1015100c5047c1130003114419402d04000d800542d9840c03105c1110700e60000c0c03010000703008051182044078441d01c148003680c14254103002003141404240312800f64000d84c8420080ac031882003060403000003044940010700c62400c50034810428442c4a10300081d600711907803001250080003403155001019141440b11348003103c1c01401216000e404403100e190700702c401604108018002180130344 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 221069415 1250 221068165 221068201
    0x1002090d0c0b07120203040b0f0708070c0902091318060c0527010e011701030809011101060315140403092c16021b010203030f100e0a0203060301140609 67
    0x28240c5000c415080c0e8510303001c07600c60b0b0801c030700c0c09201052102c00d0150540d001030712440355000841c94136081403840045070007a40c1c0500305100b800944081040883c0d001d0340c00c09540103903901d4010b901d86030858040d40001c0c0170030740901c411401540d0622041e00940000784501c8200c00c150703800c00d4403a080541200e92070340090040801c60309c074044580d8150103000343d90703031055030b07440d03a01080c00100400b006042d032a04005001d140c94004480341f100440c1142d512041c0140e4507400840181e48103900180c0881e03455203049030000a100840000c0c050045d4071080801080403c000c00300c1c0d440030b040d41c02800040022409003c1c1140b41086405000c66a000001030b40d50080c0c1126100c0c80200c1d030700d144003910004003042c1c06404009803000ba031004e0300d450090141050000703540740001071440c00302c0000700001c140000d1900c410f41010b4a0350050a041d50303c1c262180002950040d0380c00360003503280105120b0ba0800000300303203006076801450a81035441d1162090704643c150 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 221070665 1250 221069415 221069419
    0x102010b0f190b07030207050a06050301380705060103050c01110a0b132306060103020301060f0507060b0405040803040b01140a0509040213051501020f070506191b030c060518100209 80
    0x40070010039603410000c003601604c0d11960051201c1400d0a00344032450300c0d01d50106040c86400c1c401440300e03100031216510350602b880c2c0c00703c6c42800c0300c03000108004102e94510b0101e82002917410180b0a01150396070580740104112100c07103242800440311014135242c20100740e0484504203001500321011281c00400c680c00000324540302d6142d00720b2204280c8413008040003004803201d00488140002039200c2c0090034210300310340c50400003030a40f42c200e000c000100900001c02d90100141503101100c1c28030082d0003085035107040d20300060b00c1e40c800e54007500c0c0d50503400000100807908140c81003141030017519405200c0e2904040c8140000058000c0313030701c0030046515803200e004512130340744a80041040c01810151803000a410031120000c1c03800590841c4100344481e44401c4111144107038051820143c004a603235049806152584d207162035000800420b8080c15403140184001600618080015803a0b0f4043e80003002e00d01c0820004030b8016455540443d9030990203048a0500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 221071915 1250 221070665 221070709
    0x6140a060f0215010b0702130c09120c031a0718080d140c0d0e040c0c02030c240c0a03030c11060604020d200d0b0109030506040209070e0402030907140102010b0f 71
    0x18103c0d00c1c4a0040f401d8210500080020416600b585442071003202c010f141408100485068800300420724069030242201d854500502c685c1002443c0307007003000542d081980c40022110016613a05c401405440c801c0028071012491401c048500c05c2910440311200001c08000c0c0440030140d40c60105d01340218081c0c1e2051000c03290415007408a001c103c6415a80c0514241b0080b00f04800c545480e80c4d98000c11448295400c01600c001411000e6580200c0c3c90006140d40c80d0740d80464214040800507610744c000c2800c1c003101e407000070303010101446524207011202d6071003022580100070b100c0d01401a840a004608a41046c0d802000c2c2110440400720b4203d0390b0380f60014210780c1032404115012000202200c21010078420001048400d1a20f900000d01c0c6484d51682e079032b00908081d20a81440010540036400741080e201c10500181040d5101c1c50300b94600da40710200b80c03003408a49524809003644071340c03061041e1459070381c006000b9001600d6031801d10103200314006515280f604 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 221073165 1250 221071915 221071933
    0x1a07061509020a1110092f031009030f0809060a0e030f04271e0f020d0912021b1c080f12010810020405060f07030e06030a0e0106140a060f02 62
    0x7180d40000c001045081d00c640001c1c094829409103032803140030900c2031040c903007500e140000321901101e00400d00101d10320350114040218040b21242d14034030a44c0d1600c18240b0607004d8204030303002040761502071b40b21084082d441e880150740d005400c54040c0c04a0700190700103540e089980d031149005000e0725003100e08104003d8003c4109600c42c0d0030510954030115000303071920000714a900e8501c0214a010300061101071500344424003a55070801649898034080e40f440340855040d1209504207000c12301550404e401c0610203140030310344600042c02941e60b0117490701c10501c0e1442804002900e00554207441e0302c40780c00c0004039013800300c0b0b5200301005218040305010014100d036a1050880e800c084d450250524a01082415055001401803008220644d54202524024501901000d41d5030003a840c081742c00803086140d031680b2a002006101c41c8509079407044440311640402080400e80321440158038580c4828200e902070710a036001d12041e40300308150303005140c1c580100c1d42084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 221074415 1250 221073165 221073179
    0x504020f04030b270102121305120a030e0601090609051008190611131d040201020c0405060f041a0f0a0b0a1119050d0f17040b071202030f070305011a070615 69
    0x4c8805062015a40203d11146100c010002250f04405140c0c00229101d00340e80c2c611b921034070312044001140001281ca40074213400380d0403826a1180c0e04040e5889583c68880501c0181031602445021910313040004450034142240b14080c0c5402c04018500c492914500c030fa070303850b4001d904454168482e00c602201015030805050203008107a07400816609040740c00441003110019030411031810018040540d8010a000044080a98000c2919561980400c0e407801c3d507400343c250424a80711450404040c000811640f040003100d00c01943d855a808200c0704090034000e655600400304900b01ca0302d4065800101501c140d941902c241340e140504100099005500648054100d2450008901d5000e44400d005d0200307400d019205203402c1e00d0b040c0007064020001040a0644000b14120901410042c5401da01303081c400d41d1303139162054100c240408240c4046011a04100001ca0302501d0b250a100809620798189402c0c007c107901d07010007802c281ea5031042c0c007075807207080131600b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 221075665 1250 221074415 221074471
    0x6050c0315040b0d0203070e090d0203030c030f0a0b0607030201090b010f03020f10170705030a2a0f23070c05010806090c03040f08030901021902010b0d08070507091407090504020f04030b 82
    0x101620074249248d49840001c050a26015101c0c0700111f4200f0410024400030340713004e698201d84503000c41481035a903443c4174001428040a81c683c030200c0401e22100b01641500140030407403040200c1c04082c0d9031900500642c1e1214040258401d5103025005400c1c101041503044504640c6890310390011424614840b002c0c00380c5506001903400810403801c034805014080400318299100003080f440410403140c50014158843c04000540a4020416210300842e1211048041d2440004650031180c180340380c0c0321000440b5840500d400c00201903004071010b034498000a0b000040799030301c0d003803245690360004008403a90501800801c0202d003013000918441e03160600010790f05d602c0c44007503440b6800c08c401100116070402942c20310740d0b1140b58290500c103501160250300c0e0040703440c040d0b04005141c0c02c944881407034006030a5800b004100414042c01e0301d91200c0a402d9154401d2000ba81700301e0119116a1000300000c20014044c3c0204640c0300f1550500b42039620a203241500031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 221076915 1250 221075665 221075669
    0x804060f02030c04080f03120c1b010f020405040e07080303060d0503120103061a0306090c1504090504060902191409070201090f060e0f0c10030c0504180906050c0315040b0d020307 79
    0x404007001c079081c040c11004020001c540070030f0701c00640c106890b69003e86a07d2000904801050327202140c600c42149100922500081e5503c00a0015030001210070000b500684902445142000d9039103031004008104081942c8c02c0101440c6180c0d10b59041c08081054910202e6007480200420034201c0c59030000507010b98852500452021a04070050144c0d0901c80c9e0740c10712030b030401d0040c000d01c1c0038001100c44401d182500c3d0050640100307204e4851900580d03201105040c101400c21041018030f60100c50594070844030030060034140010b081101401d0300401c41860031088049100745864201d00d50b1000c02ca00c00070070640040e5413090b00c0d200403a8001c03038601e9220061070312001c2e401e1000055055051000305406204c580001d1402c1d00400c003840145a981c030a042146403066040301d01405100c6000711040505010030700040c101848251861403814001c0742013540d00c0d1049900034203041703201c0e00210300c00c14100001000c00318059a07103c0701008070440107880500401d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 221078165 1250 221076915 221076931
    0x210062408101413020c060703050603011514030304030f0b070f02060c1e07050307060603050d050901120f140708010f0b16031206230f01030203100911130b09101b02010804060f0203 80
    0x1c03150030502c2c8c0180c00c5c0d840281c60188039174142201c02c0d4410002080da50220f440548001c1500c43c041d00100f810b601c81c5800140910410b1582c60301440000044103025105659030712140020b203071022a04c1348401c0d11047c0c0c0c03810701000111081c000160603214601290032080c1c0c41c0c402c9661710580ba541c4082400c540d0517440b144200103010081c011030320000c0c1107007041803810446100003000314140500c00400660795071284400340c507041c0d101000202054400c01c01905004402405182c3c091192008403010480e0108403810500d05985072061900401400c00d50155015a0400c6058502090155944c0c20000700421100e680c54404104020035140c0c41c0021000e00c41c3c50032551070001d06240c01007042c040111010200d580c210307082e0180c001210702004801030f030180701c0e5001215000054140108801e050f41f001040100d100b16000740400c00ca100e4140c8441201203031840c00f40d42526841c3c0055400744a64990140c030070307c3c000814a00079240c180c1280c20a86581c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 221079415 1250 221078165 221078173
    0x4020a0e1902031302130c0c02121207051006060e061c141306050109060b03040b040c0306020a03020301090b03061b0a0327052107030f0210062408101413020c 70
    0x13021340c1005070000c0c20100309514240715455820310f02420405c2d1000c0003c1c01005285031241d40030b403040c4001000d405840940c240e4810302814031503507078501000d103203400519001c400661140200146014030402410103818403503905203115034440c04009207229a500c542d03030924000c0c8860041842204030224180300d040c0141400c0e01100c8050300311408082c6008801d00591162105896025520050000d0b007541d4602d85038038200200d901c0249954000708690411a405802640c1030310102c00382008000c891000b010b0342c400040d5064500c050300051400c0c90f42e420800184409015030601044961641003000358400190700905517080d101e2541c0701c10040d0510503036104100000054034031807c01c643c101c14500c195803006080c40301d0018603154443c0203120319640304480e403104204403076440c0c1c02a058111082804c0c044c1d47d0b11002408802c41c0105c0c900c50081c0344010104040a00340413004000c21459000154814070100d4000c1d2810081d0000303060f1000791a000d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 221080665 1250 221079415 221079451
    0x30f030210093206010b07080f0f120f0f04030f110a05010507170c12040c05090405010b01020c01030c090e060d020d150c0302040501050a2708070302120604020a0e190203 75
    0x1c0600d00c0c141540c05400e1101003e1500c0320200c0051410b040d642940315944e550411480c1c080d8680c4101c4203000f400d0140402c403810300c60110f00180010000c01110140c0603620b40c0d442c808198011540755207c00b10388004500802e210303100c8221000e0700350400e8426140c54088842c03500340006012580350391070f14200010198080c0e20070300e0301c40201e90784410783d040c0310344a200305002e440c02901e4400c80d004005000e20444c65248001014081c095000070f0400c1d0408a01800b084a4400e0162160b5400801d1552080c80b41e1032480c40c1c542d685411190812040c0e041c460b0001d000710780e0120b108050240507950341404015031501c904485045c0600c07600f4201c00790340c42d16000005142c4140420400c0b030b6041012900548802c0ca454400c22a0098800c4440c160301c4242c0300e04000780d808040b580010000341d05060b240200c5042e41c0c100d40a01281d5a0b40108850080d0000c01400e0200042d15106280f02c1d0040c1c00240c0c1d05400d09a072010002c03c0b03030000c96a00403070f07001c00808 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 221081915 1250 221080665 221080703
    0x503040503150412140d0207050c1c140607120506030f061906050a0e07051e0408030903120f07080a1e08071e091202041104060f09080d09030f03021009 67
    0x1c00c011110f00c3c100640c07015070201d05e0110030301505a82d02010f503000900304080000030300888015001c020000450103020030300d84981c3c00341c03d0804a581e8100b50751201155100000c3d075a204084650b60507088003c0c3e0790185000d0300d00640119098841c400c2a42c042e80c4051201901c2800d802006101082c0c0f6040200306482199020314040ca454040911011080f500c0303c50740581d06081c40c540d84d00d81c0f407100c0107510854030100c100d0144e02180100303107884040020100310301c00b14102d81c51607007030900d5180907100f1b64035181d9809008000500000301010094400c011036410000c0c003041d61071a5a004c5600c04c2181e100c00210400c041014468111260060340300060100400c1e42000c2d0130043d0080d0b4081c0619542c01c400401c440c811507803223401407040d80e20180b10b0903441e103680301c80c060700703054220385003201040c1c24003800700d1401400524002c42000b00d0f928200d80320714585a962030409603003c241e085010f00054610b041c445806465a058801e90f1030855421079002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 221083165 1250 221081915 221081933
    0x1516110901060903051e0a0209010e010f05120304050f190b04060815010c020f220209030705030f0a02130e0109030e030d0914062a060a0f02070b0a0905030405031504 73
    0x100b81e0a00003620300902c040703240000c0c4540c4415000c00306180304251100000c3c50a807588100a6000041000205094036529850780c101d800d184140c2c0c02d030540311820440b99051040f18209a54424401000329240c041c20442c551440649110b00d41851141c0c1400341c6411a003003403102c950001002c11040390321000c0203600480c10700342c51555141c1200024101300074540003038400c40c00c00100d10703103a030344284981d50628110413584012000159110000c0c6d007002e0700070b61007030140800000385410082180314070040182d0140840040039420400c804214440301c0350202da41e0300c86a0b0042200b44a407192180c084d444010102541d80100b628051040928604200310f801d03041140800c0d00011300d191036401c40e00980c4840707659002c254811113890ae00071461850b41000742e509240880c071280551504002802251b00228240e4203034801c41c01c004002c4180d0000040072140540e200011492041c003c0d20f140035070381c0d0000382c50440c88000907502d00d00214148420030480e10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 221084415 1250 221083165 221083169
    0xb0102060606030421050405031e061003051c030b27060a0506090607110a0e0405060106020d05040e180730020a0614041a0d050718051516110901 64
    0x4800925629155031225054400310517601e49542030020400600340c064003c0d035003e403e0103011501001300c0706502c50314001401000807941c1c002c0c07101094105074030034903001c02e60350803a00908a184403019940d8000040c09158400c045d035030541070340f20755038a401d20550340900b014168440000e80104407c82840542140e12581c003903801008192225815507000c1c1900701e443d552154a541031900105109140c004d5001010590101e203868000c485d40380100c0c0110200d0b601a0380b1500705a9a0f440146415804200c05010030040d11150100c5030f50b00440c444030300c8954a80c1d009055240442c6504206440e441c040d0580c108151000801e200d90a03d9401c1c4503001245500400c643c4449401814200604010700c40c80000705030b412100104bc40b1840201504441302c50610035810400c5000c80141c20b0002042e04144600314000e848460090010baa40d46000c1c204182000e028500703644440701070201e000d40d00c00081740d141c0d12502031480000c4690090f420031510f41e07016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 221085665 1250 221084415 221084419
    0xb12011e05150d0902090f070f050a080a0905030d110a030e03040b0412021c0c06170f0f1b0313030201061e090207080408030c011e0b031c03110d0b01020606 69
    0x10000800c1aa0750312180c50340c044a2600c1d00b00d98540b4400d240001810060401a4025000d01c1c14041440c100d6507200b480740001c1d80e01c060000b1400d40e0212800c0c4101132450b00003034201d001103103950742241c0c400e1445510a5044034506070500b5072035819511800794074841c450005c2900104c0721381500480c40184001c8001d10f207014100700050047d0701882c06001c020701140c0b40d260741103440e14001d81c041c0741c80740010440c2d1290315142280b0040001d02820000030001c4c0300c01c050040842c00028091100d030841e280a5a4035407071401288000145403024400000102c1049183e01710011401405100390648080d12541400707425039207154001c00300d0012800c8900401e0b01e0400400d07046e1045c0341405691100a820014134602a540141d25140000564010003940c15407294085040442e00030f0300c40d92000030540c040761202d060098064000c080030010204a0690000720448a0709001410080f00002c141040d00110505d6101c280d5440c8490000e40c5c040088903031103541 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 221086915 1250 221085665 221085719
    0x90201030c02030f040e06210109020118032013091a0f0403091518080c18060a0501111005090d1713060902040e060a09060e060c0a0f02070b1201 64
    0x180c0444d10071244100c0c0304901c007001000002c90156614038003005506079840c0c007094821601c45405900801342e41b54200e001c01c4800c2c101003054590701c19000122a00400049810309108190322030400c4558000341d408107a0400c1c1d082c0501c9244101d02515006d002c40400d2a00c040801c6a01020083e00d00740720041c030b40b4204400298040845001d4034210740ca50340b10840c3c0310000b0744502840c12001004005102804254244005a40c10264a00311084049040710346500c06180f07406940d00da40040d40c0020a10065009600080700300343c00c1030440e60200941d104c0001104d80940c0c40c0f801d01c0d001184055090350344620681c0e110a818840714100307040c04140f02c18600c1c462140186440d48402e402006e40d910b41d8040e500a0016000b940d07840c0c503005003400c00510000e04103c0d1060301e4001d003c0d000960024105105400010345149004600e2405503901c01c0302456880c218031441c0d80201c2c01a020b0005001c03980d106144003030a80d41801e6140d0305100f1032010481e01c0440c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 221088165 1250 221086915 221086927
    0x302190b0402120712060c030f0606050d15170f060c190c0f05250f0f05040209030a06020a0c0b0a05040b06010305090c15092d1c02090a090201030c0203 67
    0x10100c0300303280c2060b41221182c01c40302c90402d449040001c0780d40305040c3c100842001c402030007080d0300102c048000c107590400c08807400c0101401180c1040c011580010b00074440360705406556480300a16190100643c46d01035a1801c202410100003401c1c0c117080d800040f20781502c0d4070104081500480505001801d11500041c48850b4605001d491400c0080703011081003070000314007900041c9070b042381c2a1240181c108103800b914016141d03c0c0d0b40d040041190004080c006c052010b41500d030b42500c0010003514040400c0f0194000d803074100e5060003603d4001c00050b080e03100500f8240c0300c0d170300d411030b5945940c144510381180c0103001000d6903003400d00b0000002d19050b01c803641700d00300b400c0008158480c0c80d4603038a803010710b440182e0080b2a029800201c0388a00c0043d0603102c0080707421580d500215250151105548032040c204010855071850f80b03482c18800e040100441d440d0466401882c1d600080c490b610191024a80d0350ba40342c5a40c825542d0600840da000d0080740000c500d008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 221089415 1250 221088165 221088173
    0xe0f0a051e1f0f02070b010f0609030b0604020a0233060a0303020c01030e01020903010c110610080a0f11041a15090d03030b0a0e011e060f0f0507020a21030219 70
    0x9000c03119244039200c00c140482c0310040c2590702001c0b0b0100f04120440d281c44580c6803042e0100000c6c041d40c40d0200d0281d90009009104054200550b0703401507100e03985480e01014040030750420725000c01540245400d10110a00340c40c030920310328007208109080c440c04e180c104040b805015014070701602d00f0001c24801309400180d000b41544083c6000590070410030f400500a0080b03200c980d906500705041c400a040e4007440c15034900e40041c003581c3c0385448501c5441c0c0111018400e0102e90303003021010034041100f03c4002c0c1401e9000303421920910f43c19400007403ca41303400007491440c9036601184541802c103500013503c60388801050601d010b075203000265035800c6050005082640351a800308041e20380640010080c003020320341950030b503124804410000d02d488403070702202211450000d600b81c81541c0c0503070b542826845110810510301c504841c03c0d40600c60503a00300004560000310250b20345050502580d1842e00c2420110b10340c54000d0504911009040d250300c034514030f00b008a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 221090665 1250 221089415 221089423
    0x903090d080c0d0f120b2206030206030c0c01180c0605030c04091404050c010c3243030b090f0d03061509030b130302190302060a0e030c1f0e0f0a051e 66
    0x7803610180d44100740c00b0a4081f00040c0143d500002c1d0001c402105021503c03d40c08086c10000803104004c0c03085d14620340c0049185000d40e140680400c1c4004000c0101743c3c003600007503410a401601d801e00d03154131900e504003510b03102600b822860740e41d04100428804103002c24011541c0910301605440e000703840e041c81c03007402c61520303940c2000400038080035921000d4003503c03150704100c03d8481a02105182000c01041d9129140c0502c1c4c40002c5400d08000c0030a141520341c0807003c84070443d1b42140c030781005104d0000d0481c031302d9202d140c0a480d170342c0d10b041040a584086a0380c1c049942410203400010b0250720113506018001c0d10301d400c1c80043e020000b9954031803000619a400205641000c03032400789820750781200075000801c41024540c1c0421154828403070004188103201d51004203541e40d00c60b082d107111458000a21a80000c018900c104c003276055803a0010410b803410031515820a244030140c1d00d485e51003c0028010001c046c4030842588008068004a80804145058036 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 221091915 1250 221090665 221090689
    0xa0c060201290d0c08060a0e03070c0902160b10050a14150c07050d150507090e060409031e02011a06250516090e010b0301050903090d080c0d0f120b 65
    0x105202d14140072250340c03549000608443e4012030103048041e034500c0c2c9281c5801044d243c200e03079507082041051407141c2c00022500171540c401c1030320104503e81080c07030b4000d4102c038402c09006c2c3c1010700c000001c40c131002134070740c0501d0310800e44c0300065251804002c80f0000a5100e2a284800c070f2010110594881c1908908440d583d001c1540c3c94040041c0603007404440c0c0c003c960300052805090f400c1c0001d00c46e03c004440d01074030080001d600c90403010340740b1041c0c1d8070880040c070304410002000e606194000f001128802d08140307c00b125043d0390180340f100f0704001e400050390b6a4042d080d4144481103d05255032041e40c1103864403809040e0a903164001429800c80d00c0200e0301c5103000c100c000c1000d0b0080180005000c0300180d01d0700d1140c4050500400407040d1903003030200b0070110746410f02c0b07000d010301c5142005602e000c240741d017844060180364100755003881c001d10000302c0c0c1c034005020700d07902131344255101350100800308005000d003410104254807440c42d00204d84021340b01c101c40050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 221093165 1250 221091915 221091971
    0x90609130b04170c070f06030501030b010b0d06050a06050a020717030a2715110c061803010209090702010e071e0303030518010c09090f05060a0308070f050105090a0c060201 76
    0x4820b54071400c150b01c160b4035922040c031800000064043c03626201141c0102500c00e0305180c02400c1d039585404406a40303080c00080c03c690201d400401c026609480100860a074180e804030f202666100016040300d4a6482400801e100151264131240c1c1441000080c1003501c5051541424100e44151340c2d0013490054014049012210444440c1c01c60402c903042910b001c3c2c0861180e141d005501a09901102e6079000c114541e0b6a45500d000101e505049690040d12150800d603010aa56405401d111456178155508110390130050720740b410f40911941d980d400125102c1016240945448075541c010007004031a1841c80340c540c0c00035200d88007120341610b4080391546a92040b0f030040308026501441a600c0c200c0e0500505400118140c11580c071040304100e0190000070000c04d0b50800c40b203203540045d40c000d0602c0080c1821000c0c145039401940700031801d84171950ba0508560094804c03074840c2e4080b1501500300140d6520400107848103200910000390b0307000e0841541e0080143c254 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 221094415 1250 221093165 221093183
    0x1110105220203030706110904050a0b0325050d0605041122021e0a0807020d09050d261201030c0b0a0c030e03100c090f090908040b090109170c09060913 67
    0x4070565408100355040c03240c016000f006005200310b030b005420b520800b5018080c900300710004da81d0b1402449a4020750402030080c0550110700d6060031040641000c030803281003c91500400d4544400e956501c44901c1200006140d060a04242c0c6410100c0140d2500c0b4842140070307005240e07410134541e80103649ea218007603100ca41c20015069080b05800c480c41c803030034012800c6032401d5817112080340541c02070313001d0b035008242203e421640c150b0140035454014042220440c0040c501908081c1181600400c0c00c080b116203040c2c6003142d6006c0d00140c2c1d1919296801801031000000079580282894403c2ca4175043c1c40920280250004c0c140203400d000c0044075660954a040c000318844295402c0c0c100070103085d06401529201d0540a60303501c420602c0c0000c1059401c0740f103603400c0300360003aa0043c04c003071800c4144080e5a1046140074104803d20800048141d0070004c2215102c500070050401096076105200c20301c03038000c00c0c1030710540681d000c0c402030300095000c808400d9000301201d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 221095665 1250 221094415 221094481
    0x100b070f061a12011b02060105011b0c0b0712080f061305060d0510020a1b17030703110403080307030c090e1303020a02180402030f010606080610030906060801050601110105 76
    0x800a036900c00e81455004070324a8180c1403003030f00641c806159041a0400d04c04100a41c65080b41c0d501000d00416001c40c0d069038100468014040c902426288a4000000201c0d22401d05144541007964120344c0e00718059070301c002c541e4002082541c400c0399000313042c0c298982000058011340100700c441052660780e42c04a2142d40340c880c40c143d0034a42210454500c003007403034201e07802540000305c1400014a240c440d8901c0502c228510321080b80c004958042d06620103c00d801554006071042c8240341da1010115001c103c600b025200071343c080e541c41030f164a0210405410307201c0d11140b1404010031010280442540d101d4400d030060858081c0d5158445146401e074548900e0f6940658445001a41c05d02203c81010010f803141d403007507050781e850440300c400084c01d841240c00348070b02044525002500d03030700700141c0ca1681c001c110b01e40400c200049443d401c040b41d6540d0801d200c0399445100700507080d40c0014442806141c000001c101c640760407004030003d0f04151185101080c000d13070341 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 221096915 1250 221095665 221095691
    0x11030f0a020a0e0d050a0b1503010e0105090a1e0b070909110910050c01060b07080a09270506060f03040c0501090602070f18091403030103031d0f090603030d0c08100b070f06 76
    0x7600724886d0b01200c1c008560408d01f00952076446440b0f142c2d0b101f0340c01e1055260301c1b2a01170080c14012041e035002060034504959038a0410711009121400010a1500020102e00e40601080c01011183c0b00c2070407040c00d240350041640e01400782104428010080c2c1c07070b02c644944591201d40c1c0f02500e032464583c5002151580580000e50122801410200d845024800914005e0080341e516894680005d595800800e04103103640c9100d10210380b0f0610710511030104c82d0890f0340c1c00080140003d01d404415509450550001d49003507a01400d14031082c00b0300d50304899208040c0090740000c004407460100e880744d40b210f042c011b9000c401c1070100c0c1702c0c4c035440c01030300000d50b4998040710090f0304030020380d000340e5241c2003488103600141e2815070312175200c803608004603000c5d100a400d0481041303800742400080b54003c0c1a490f0940710411580c80d290f401031148040d0307107425079110001c504040c580728046851680200c10f040304200499000545180a15401d02e5400311001c00c2e025901d0f60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 221098165 1250 221096915 221096923
    0x150e090a0b0301090c090506010c0c0b030c1b0d02150c1c0906060305030a0e0f0a03060209120609010b0918070e07030603080708210903040b090609030111030f0a020a0e0d05 76
    0x7040390558204540c4004012080d0210419900843c008010550750386c001116148160b03078003d0100c5459000900110011400440e480001e00104510380296001031304240d000c1480d0a841c950401c41c0007021403035044c40802604a505d0322142a035081461144800d1321501901e0400142510101160095590002c5402e20381200c0208441592030030210384070387c461441d1200048012094009500d0b2440b02c1341c04540c0050b005a9095042d607481c603000794840101c0c2075000c0842103c3d409180d01c00c00240c2c0c401c0020000207d4007036520001d0111222018002c0c030310340204868030054007500004c8050407160303029100300d002d4903803410503001000036800c09010b060000944030144010180113200203860030f5501c00d8048000c4003a40144d25003a2079202c0c9607001013104120011248022701610031008101528140c0703040b0000c0d08460040380b032240340e0f002c00f01c1000301281001100582c0411201002e6180040710031008043c0d03000400d10f83d10801c1c20552040c00d201c8100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 221099415 1250 221098165 221098181
    0x3190503011409090d110a0219060206010812040302010c030512090106060e040e0613210327020d0303020a0909060f05040b03210706240801060b04030c030b0a1112040c150e090a 78
    0x127043c0000c400c040031904c61b8a1129801807001601c150320002482c0344000500b420445c8190b81c2850402c1d0035076004541c0420303804003c1e0108001441a0f1114030b05540303066000e040350100009071a480d1600c0a048030407106003051090380b8100c1900500c41021030f07400c7c0c0c0400d91050714030824060780f411240e100c00002e800034030000302a55001480750150f000d0340000f01002803545003544c401c030080c564041741c0d4a00a40003000a040c010020b03000390080c085124881c2001450161140c001c0001c98409512a00c0081f1240e18208020300300361040d84003003942074000d0003e0a48100e40b1540ea1650140b5100c10a000090078a050028035030140c541f0605103103000f11030800010020540c05814042c510042d460601d0001d0b100503884c08480860340d00c0f40ea03e0107803034515100c0d002d0710040140a00c0714a0385440040003090005002010543c0c090740c0d981815081030700f000914650030380c00c45d003142d00302000c1c0c0101003500503c08100303000d03044402d030040790f6480301035001511084c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 221100665 1250 221099415 221099419
    0x31602070b0a050a1d060a2a0b190b0d0b04170304030c0510020c0d031509021303030e0301060b1801030e011803110607050a050c03190503011409090d110a02 69
    0xb080418406500500a00c40e540c1c0c695152441c05107110143d49840d0000900d00d1b502480c02c02044a806000e43e000c0d1000c22000c003254444200c002601c0301c03c5614945040b1187d070000401c12490107141a10014000180d250801415004034042030803c02420f10251854085200081c1040504608980740800d0054221b03100c0c1060310300034008030004034007200c06000e100c8d009002d1128620a81c1c03207a04480c40100380d500f84901080c0c009200b625551090b6524140c0d021807180503a00080c03110b0030607500d41c0f2040d80d2071824010070141c0001000ca00c6a41000802c01280d80e942c0b0607108940c1c28100d4103004042c0c5580140e000b0004900f1135402542864003801d100040703c029416901c0c0a600c031409041c45007038000c1e44032501140d061010070001c0c0003040c2c900348110f010380500100c2e04220303071510314007554012004a080401100252000006110039038400003142c0460000b542c2aa802d03041541900b52180481a240001c00410b80e1005040c002d04208103c261500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 221101915 1250 221100665 221100667
    0x501051006172d090105090c09010909050c03031201060210060f14130504120210020712080c1e0403030e01030e07030809060d020705010b100903050a02100e1c020a050f06031602070b 80
    0x1100c03540321050403c0b139040080c0d51030100082d0354060003048041c0c0c0f6000044c01e034481d981c20324050500610105c0410344082c829040c0080c15034400b000107089402c3c400041301515850b11400034a41408000540f600d00d0a0401c100113105c50704054100366074440b020714079680d482402040d0303004840794017101c440e130502003844280715100903050104140381d4244ca500d20560100c05d401c0e8410504020400407841d00d0300012188111000d41e080341c0b002554910b0809421100840c248250715890390060000500700308041e000207130810600c3c001c1c2414080054015103081e200c02d00384c40068038a2400041185890759036404031166114044000c40d00c0d82c40b00c0c03c26070b009048a0120300d0050000031003202000c1e000720f030041e003103a5000005280d1407080e54240f0a0900c0c0c034261280501c01c03600c5c0c0c1e1403c01c2c0d07500c01c1c0604140000742443c0c2200c4c41c0f035004100d200c003040d078130440c0124000321582010b610b5041c1102e6101542c5071003c1700000c807040c0100e1500d80c2a40c0710311203401c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 221103165 1250 221101915 221101981
    0xb060c0d030c031a03071a0f030a05070f09140d080c0f0102072006180109030c0e07120515060912030313060c0203030c070b25020703050105100617 65
    0x14042e40030070b407071501650b810044080da032480e84041200f00441907500d94045403042222560130384050107424002d03041d90f400e01401c104000c0709a0010f44403c008240c607903042104640d4880300d4075000b07110b58904000315a1034038004d1605140003420030b50003108128a41c10510a0107400ca407403034100c0d00d080381d070303004140e40d400c0b4000c0d042503608440c140b03885240d04280110700d0300d2085142c180102040c0c507001005441d503450002da40c1040381804201f00000000c180c0100000005150032480305000b850008001040b4030840c00c0d8581c02c81d0f1400080c060b08005030b522145800c134082d60102e65600302000020faa500c5001805d100d103100000c00c0000401c2a1074201c0780941c406d820901102076544000c0c0c1c0c582c0400c544a501d980d206004030710201300b040c030700c40c7d82010030f400461540800202a0310508038041c00c4e2030015a02c4200c8c10020840240b10702d0b5801130010790100401410410020705021801889070325048078400400d040b0300384421620710034202c021080346070003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 221104415 1250 221103165 221103167
    0x1002070e0901021c0903140304060603020306070e0913030f0e04090c1205070801020408030f03280b01110c091b04080304060e0a090b0d080f0c01020310030c0b0403030804060b060c0d 80
    0x16000301e00341c001511200c215040078409074011240410b506d601c5180e81503e07071406a0906d0f80005105580e00d503140d03030740003002d40c6003804002d00900301599940c814010200034071518a00142820008075507880240003c6507021001d480841c40b01c0c0b4012161300548400030300600345000019010b143c10f000001400c0c0408800350312124030403410396000c1d5a50b10100c1d4200d000300d1090a089400c00c1004000100300356000b107a004901e40118422500740840071000380e040c5541c100040341d61600c02810079030700f01c402022450070b00c400410000701c12102054249030081c000c1c3d602c1e4a01c402d01140000e0b20317001690003400445c4101c2c0c1d100c031fa680314014854010a80c1c070354001c0d650b0f8000454200d40382e02483c1840000034100115131441c07076503205625444070341c001d4130041090000c1c260100d42800110f01a240304a0fa50b070082d801c506091200d0b44095000c804915002c01040000a8211049903442500f044000400d168582c01007182c61080c2d1004007114010f05404139105 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 221105665 1250 221104415 221104417
    0xa081b060a0605030f030a0e010804030c05010c02060628050405060102011d030d0516020a0215090a0b030115020721020411030c070c0504060f0308090d06060305030307020f0c01080103021002070e090102 89
    0xf81c00c210101c0382a60080c06070140c1381d02c25508500d00080161601c1645540038285c4c0c660880e100b458048084040c54030b40714219080011a180160019424098280750006804d50940911290f07521060784050700d08030001d904e07200d52805181c0f80c90020711141c1c000e6000b14283d0480845441d8107407001d1065540340e80c401003c0b40d22042c90700c0046004d8090207558034505242c10b030001c144c54150380d020000a80d032488062204000104110b41d800d40b583d519140c0104070141b981900e950524024044500c3c4003610041154001203080045c0104c05102ca030090288411880c1800c1c0c01c0d0000c5809013140d181b0b12401401c00100b8041001e034080003c3c00c1940c0641d0394003030003a495404000650310130784182e9034090003030003050010440c0540241001c0100602c004004806550754609490b042d5006407060381001c010840c2481c1c0500030020282103000c094204180d4200019101d640c0c10701010340144000c0c0305c118035650003000031001600e00c1c02c440b4802c07860304002050107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 221106915 1250 221105665 221105669
    0x1009060b0603010f060f03060e1801090c060c050c0405060603040f06020d05040b04050f06040b0612031201091b090f21051005060315160e0307030c0902070b06120a081b060a06 77
    0xd191a42030f603032580c841d01c0b03401d044d40e000441d03060340c41c0c0703c044ac900480040b0f0908840c07195070315840c6000244044140d01e00908650312007546103030090a06500f00754201c42c2042c01241840200301e05a035800b404c60750320690102e44940351440c40e00f0504005c1c026560290600c500d01000d000601081b03100d900d00c1548100308460a945040801503299402074400403c00e001c080080f40051038040c0500c44500100c10440c0d0909440300300c06150144281c3c440346c402c990321005040c60748108200c140790070b1118205001078614240d044a452001f500c90043c00142412551042030b082008190b5441d03001811500071a14044062008090666020f8400e100b641c0d008403d5101c0005c0051240113186055441104c182800740c0310021480604c0e507050140c4480480001c00142d0300c1400b8150f0843c0060311a910791070b25485a90000e80214030481d0030810800001034009403014100d5800503a89490741543c0d021000c1801c45261094540c1c0a9a0108181120b0035030207070301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 221108165 1250 221106915 221106917
    0x1e051b010c030b130b03120318061005032109040207390602071d130c062c06180a0b0c030706201e1e1b010b01021009060b0603010f06 59
    0x12880c50000e2038082201d480d034035817a4068002600316044550705030050f5a015405501400c0280c0848503000d04200080312480c002c407007131007402d22403801e0421062580d00440000b6280500030026940064000c1c2e4108a2040da0001046070405c104540c2c0700201960408105462100480706d01d034510b0040d54040662814020000414920001e0502c040f01d0b034030301026441d1200e8441f43e0361501001000b141c0b9190f00300b0388400000324203250040040038155201101c210500710880d58502018040c00940304041090011556428089402d0358881340c070000c00040840c008070352592016441140000000310f000c0003d50804002800c22520a00007002a0b448680b150905120303603d044001200c002e010f190344030717810345041c42d409c411018411401c0140c140024441c0b4103181510055040c0c010500d25180c00007241d02c6100d0440b403000a002c1e4010140000790fa5080707501c1c5050b41c058803141c0b600d0030f05c400d50344440341c40740001c5d103800d07965a19007810382845080d51107404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 221109415 1250 221108165 221108179
    0x9020d020a0e0a060e2103030f0f0108061e04060e0319020601051c0f050c03010c0f0201050930090312030118090c180213060f09061e051b010c030b 65
    0x24409141c03a100240a4904c03949a20f01103486420500c20321001c010811602c0403141030f00c144406408002441c07082da002c1c03d800e0078518040d80a05503400c0180d0202d440395001c00c081c030035a0400031140003182e9854400504940d0703598186500039186901a43d1520700001801c0c2c8104030400d00b0b42c5e14282816000c07075615036611002e01080b0200425180390000c00f0a55001c00590030618000300c0901404c100c0d00410f10340d000083c01c64001001400111706550007107001c0a03028004d09078025091030107000c00090f403002002e041c158011140d05a00b11403020740002d012110103692120b04003500729030601c00700c800455442e520070f00603005100841c5410f1105201140030b03060b001c13030b40300752900291442d00b1150042043c0d082e6450404d250288800440d80c440044007030002c0c6000d6542c0c820011080307102410b1001d81e5000141004200401d41071400700f40c003410b134030214140c40e28907501c041c0b82c4801c00c200f5040150b10300700c9509200040d407600d58150069002e28201b12145 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 221110665 1250 221109415 221109437
    0x903070b15011d1e06040b030f10050102060f0403050901091e0306110c1c0504050d12030e0307051c0203070b0405070e160f08060f120109060b0301020c0a0b070909020d020a 76
    0x8008044032a0501c030764420b480013203481d81550040c0384441c030340c0302c007800807070404d0744404c00101c45800031142840c80030f031500100718611411001500003050203001800310390502106401d1070660003400501403190014405160f07920464008008000e9121109100a414405e0043e158614070090310a41e0800c140045a000400c7c21102824040030040141500c107003084001c80f80030b0424001402014400090707107480d50b1881561051044600c11810070a04002038115030700315102104a6000703001c054001030000a99585014070441c20b10350750b02608608078594410710340000d000e40042030501c410088001822025136444154112a0340e807500700c000c80d12034511180800181c80d0351121220039000362840d0b078200d071018001ca8005c05008022400b8101da08031802070b540e41d1440100d09210892141d0340342031300120b000f5850a000781244e165030f021032140c05840202031b0800718540a025803c00b800500c00d0103021754903070304200c005c000250044100307600421681290307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 221111915 1250 221110665 221110697
    0xc031404150905070512061f05011e0219050f0607020105150f060f0c0601080c090601360605090a0f050604210b010905041e03050301090c0c05070305070620060f0903070b1501 77
    0x1809003602c3d0b040c0c0d40c039055043c04c0201129141e0b09421154194044c07544001d02e80c1c00c540300740031380302c600404c018013f0703d02c200c044030f03e4900300612032400c40e49040c2c14446540340f850f01f4105510821200f1040c006842e60000e0354231b214068440140100c00180d0b484041c0300400c0d10360407203131a00152446c00c5140d0080c4812120115407890009203c5258110207124800c1c0e12801c101c142141c41c000e03945030481c221405031850304610041400810403030180d15101c995480900552910300704841d03c0d00000c40c01c10700850080c601c604110300b0700c1e010304a83e8131100103449130b0851804601c550b0740d02e10300c04c010301003a0340540c0c8401c91301100d00305552a445160320510740c0b6035542451a03207840c0e0000f0041c0450403082080003d02075a00002c200204a070002440c00f82001d0b08485140102c0640070004411540d00003000444e2040c42060000c100b151f848183d15180d071002c0d507030354401c07682144101c3c500146075401d0030060003014441c0300c451681c41002a04c88250320105000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 221113165 1250 221111915 221111971
    0x80906070f02060402040f18031e0302070c060822060501030209090d170c07020301090803010608010f290c010207050606010806060c1c09180c03140415090507051206 73
    0x101c0c0d0310150380032070042801420160312000300039100140000c0d00e00c2c001400c104800c0c80001c001c5d030004011500c4c9015515040c401000d101e18030341811450031040380d44100800c41d1038810081071000c80c0d00000c080103000140781c00348910001c0c40030324500c0305290a0005000070701050340140081d0001411054000400081d000d0700c60b101c03550a43d90f2440031101c0b50030000c001041d008014821400140c40034060354000900c210f18550f02c0f9810510000c1038100142e00524440c607046000700b28418124840e510b036440282844982050701e00343d00300061241c0030081d202c561001a1940c2030000110300c075805040300b6038074010b2035103840c800c018130340c09004000801500010340c01031894845410070b0b0500d54290504450540d62103c402c0350100e84998401805520b81d200c05104641c10b110f6211560704201c0700c2849414642c888480ba6080d0032010001141d5900f003030b805001041040d01e00501c8010f101800d54800500d5a0f519041c081c1c070100198444c40f110901085156a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 221114415 1250 221113165 221113187
    0x40311040507170c09040207030503090d02061605030a060f14041103061012090b010f140901060f110c0301020f0409110c0a0308150411071208010810020c010e070608090607 76
    0x141d43d1429410480380c550308911800b62481c1d0044c50704215519880d00d83e80042d0201030f00036201c0d191a441c0c0245060704089030460a4800c540103a81003103108a0031640b5070a5050052803c5d5840396500d02c0900000c050581241800c9400c00c000000d000584001902c4904410384003409030508610000b20795000507501980d002c140090307148680361003042c00d45464502400081200305842c1c0310004001c100b130b0046042da00c0000c405200340c0b017507c032038180f402a064403c40c56a601d016002047c121800c1041c00c2000302442c0801410300d010494100c446000400843d5610342c458103820041e4410f00ca0054035500b0400c19104401152082c0d13640c021181000e00914800361f5403c035000c9900410807030440c1421210011681c44601c42c0107090145d031001c240c0d5645490500d04071680c4180403c40c2084485001070041a07000b03c1c01a941d40c076070301130140c0c0301e20141c00064050028107255909600c600303030700002e0a80e80042018050003405041e22180c2c1c4412000716641c0c03c1d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 221115665 1250 221114415 221114417
    0xb0a0b030d0912020a0b160b0702030c0304030201300b0f0d02092d04030302090f0906010f1103040305031206040c0203030c1c0b10030b010f030603020d12140f040311040507 76
    0x90750b020001c1c1c40800b8085a6154401040080e00b2511845000d40707036040b00c020140c00596040c000420020026821074001041340000e504100c19611903540d00d00c240e00000741000b02c41c4e8491207240030392041d200050900744542001240d680d01c0c001004210034190107100d14804001c060080c1494002480d04540250520400b990f420307200d6003141c40e104811200c4d081d400044000003108410190340120b211b0b42d009a55410b01c102003042c920400c1d0034a074412541841404000d03070300689030716144ca056082c4400031880c00760070542140901d901c081d00c18040001d140c800031941000040c0704003400c981c00c00c0002a20b44040ba43d83c00704840d101c80c1203800b0003031061011415129408800030750040031601c00d0a01d004103030f0016990740040e000c40c0d107660810015607040351280341088500e01d0100030040c9550002980a0510f24011306108000c40131360741c150388180184000c00001e014407696400f80d040d041146940648003d13912800c0c0021030b800302c0e10303044c000d081c000c50072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 221116915 1250 221115665 221115677
    0xa02101a0a1a040302030a0b070807030203090604030e010e040c0806130203090706031a041a011d03070b3a0f0624030b1e03060c0c19050a020d0b0a0b030d 68
    0x240031480c500d02c0310002621545000a100c00401a0307810048580c2e260301c500ca1402903410214405446040003500c0303401454014410400c9020740003035226805601850301d5503004100300c0050300c1d540301c00d03c00c0680217404d00413240880c6030080f202a006000c03d40d011038a100301c24519100303d000039a04140c082e0403210b82040303114440d800050010981710001c04428808100007030440f050010317a00311000c000b66200d4801c4d030308403c51880f11201800b5080c69a1216400241c40350880d000d203143c07070503001c41c500d0700910072913a2407031a803c803a0500b500c2c189001030f0300c0c1c107100380c50802d54000e140c10410070f84801c4029000d1402125284a00829050803181b58408105d012075050000c040d55240651017603130743c040300104403861100c9824044010201803500b03095006040d082180010050701c418100c0014503070760851011003030303081050b84030f1030080e0509003440c40283d8030403100e103840814498281491030081c06811401c20696014009064542014903404004144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 221118165 1250 221116915 221116919
    0xb0f0313060e03074d040501260f060604090f080708030f070903210201150e061002060c04170f0f10061e0519080604080d0e030403170a050f0a02101a0a 67
    0xa042100140400785c00041c5803185e502408501102c0003680900071140d15600e80f05030540140b0000c42c3c2d4810440b000d080110542660720780d40343c1c409400180165565200002440700c07041c04002070640c09080d40e80e6801c5a4100854290000e8400c0743c540c3c0c44880114885a0090714800e0403a584900c40790848082e0398448200140910f500500b9552038008540b180c080144a40303000e444105103003c26410400e050281c015803040010f07095602c00c5040c040308003401400e680885440e2484207100c20f0103009054108005041d80203000d22030003101c64580e000204500c072691100c49820005590b84002c16040440500050460303c3c107859411310003410040e001d0b10542080000c458885c035503e0440b203243c004100c800341c6603810040b0701c0d5102c1c003007240100024524a00b0085041a0030358a8901c20000c3c1c2c0c0300d41070200b1200048950040707000b1001c0d91001c0d122140001d84500e60b840001e074486070b40e400c60a081c1490041c4a03804100c07109244401807801506800c1d8045c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 221119415 1250 221118165 221118263
    0x7051c05060f04050a0c08060109060e2404080114060d11010f05130608040b01080c100c02030109060203130b01092304051608030a03060e010b0f0313060e0307 70
    0x30251005801040c003105031a001e44903401614001c0d140d03e04c001410301402500208104400b62206040140c40345c2c00b00034845d84520500d06a1504441c0b5482585426007050405d00d041e41d043c4400c120041000180000d0640c404855445104001d400740d0340da4808204101c42840401080c514a5915001255200f858141071410083c00d0a5151200e4403030b002c6217400c415030103400091100303001c201c00c1014402c10a40100f80c28801880110320710b400052400304251040c0b410015032110318001d540c1c003504104012500100110b540c2e0800e00740240c0c00c0301c00c0780ca0540390f5100e0040006002411403103600780f2400302081d80b040000d0140d444103040580600191068800e000c0d110501645807a8280001c0c248030f0020342ea5034409046c0581600c103554494410381d0081d10040003542440021240a4082d800120b0b0340d0351ba0390041040445c81c0c105014005030300e0280310012440c8008000c0c6440ca000300342d18108040d50881441c03130303001c0110303a8070100c0c020411000c41c91 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 221120665 1250 221119415 221119421
    0x36060315150302090a050a0801061806061b0501060b030f0103020102011a09060f04060b1204020a08010c020a080f0d0509030c070503160905090a050d080703050c031006050906072907051c 82
    0x80300c0081185c2c00682d0b8600004148440d1500000001e0355124001c1100e040179102c000c04400400d0024410b0624158001d85065001054514201542114002002002c3d401040038007151441c40f510b0b0b0130880e07002c1041031001d0202300c0c095840c03c5000118006040301c50940307800000d003d20031503502c100034888840c4148012a400c591903c0001c100505503001420352891091807a018501e440e00400070700124170f5010b034a240c2d2421105207002ca40c0451040c8a0b02c0d044080242c0d9441d50004211151080c4280001072500d06018003140c80b00c08001002e10385031700c0044403030668540e420552640c0341c09480f2201c80010000070010180181c00155021503480155403000300719466150411481220560010b0480b41c100664140c00d07110f0240c200d24007039480d40c118035185a10044000c0140074103800e12001007400072041c0e0341c0504035008030350b100c0e0016140340e014450300ea0191080c44120010000b4080004500341d12450680f0200e440d160103409031020400c07868802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 221121915 1250 221120665 221120677
    0xc0917032701170c0a03060506040807140105070506070809010c1706040e190f0506010b090102190606080f03040e07020d0207031509140f01270336060315150302 71
    0x1807058000e5003c10502d0120507542c440c2240d201403a5136401d40c94001411a000381e0811840f4520030b0009110740d640009244042c2d883e8680d81e011500c0305400140c0c1c0178016414010410310502c020403501c2503001c00032601a141487c02030118485404013034401d00d500d8102e008000003180300103400ea1415030400f4010350102026640740106c000740c0c45050f4641000e0660b120100350140c034003085410015103004204081c03005090062020000b915416491003071100e840c2207a000209100c034a0b0700c0b2400900101040380c0d075218210f44101c0d00c940180c40317441d0000c8006000918080d0021501e040046c01980c00341440c942103a94110340c80080f00c039039005550342d036100c1b180010040070103e06442c1200d030042100c2c0c1943e0001c1e609450746031021941c00a0075000243c60811104990041c5981c5400c1c00032074950640710f85c450400b143c04101050100844c03042500c0c0c0c020b6000f15081d0b851070f940500c5000d402c1c5070072041181552003000d802c8610750303a04d1010244240e001e441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 221123165 1250 221121915 221121917
    0xb0604020c0d02061801020f030a15081b090907030f03050705010212070302040305010c0f080c0f0d020a0309030f0c0804030b06040b040e060121120807020a060c0917032701 76
    0x10800e001808102c2c0341908600008002d0390142c0180f0012031640030320031658011110007985007411400d090307100f501025092441c5503845400311918000d8485091010300415012608408589407400005508000000d8001d150350f0300850311101000c900c5405482c2c01c41044045404c2c0c650b030440f2541c1c8228015540c6540c04d2003a0740c068036070034550307034000d080c1d5550140e2501e0850609500b100c00d640d00000500c4040b0010880ca550009041c0d60301c000b031024503a441d5580c00045038814401c11090144041c0300054017040290154000302585002e42d54054070b0684e09502030361440c00070540a066640140010000900c1c0469030340e6001c0d8010300007240c001c1d100301c00300b400e403203804030405e9140d0060300c0140031828003510020352850710500184610710760b1703448482001444000314400c1240c51f4002a10782c0c0e00030410304c030046074801001c0207040341141c00200b101030a40076444a46101c038028101481001050f01c40d04600882c0e56043c00509124038401544800380d224 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 221124415 1250 221123165 221123167
    0x302060316020708190212010209030a03030f140a020c010c0503010b0f0d0b03031606110703050f0702040209180403090e04030f0c1e0c0806010b04030309090203040f0c030f0b0609130b060402 84
    0x1085030341c0c3c05d01900719000d02d0360104610a251a00c10003404040500f15000306a10500804030b1690b0006a1149440d03014100060801c4005202e100600401668000074000403000c1c403200351126801012490a80c00003003010b820412001c4603d48820700c58801c600d0340030321072121590084001040e950241e00c0002525041c482c020901796005000c24440d000080b591010a02c49140500c00c8102c0b4452016450807209581c00f9010b4041d14200200800010039207400319103959045034204d80c2c0080030343d501034442c500d03d8007440030126011000244180b100241e8a9500c1d000d02e4003480d070540310401003152542d0b00326481000700034296800c2100b122423181c0c8603a03409540800c18007807562040d005040c4001c0628101042c1d00c03d0f501c0550030801000426032005c51481551135a000c05a134a8480f41800d203412016464060154200d01d100013041000308035800c8051407207109040d00c542c0e5000c04000444508903840600c1428020804000032030f000740059109000801c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 221125665 1250 221124415 221124419
    0x2160f060c0207090507050703050309013804050705030a0506010c1b0321020601260d050a080618070c080c011404020a0b03010b0a0f1e020717060103020603160207 72
    0x259aa02812501910210740e50120001e5040d41440b990001d804403440500c002c0c1000400100700e4440c0e82c80183c02c0240c00f1000c581c2444007034024040074940c402d1a51488200c020a4240c4800050301b501e040c080030004941140c1882d02a00e4418540d54861038250b82e02c103d503000c080c00d030091070141005000345442c0f001401403c1208440d405100306580402e06510700031300440708031704419802c002c40e182c2004135540c1c001555815105065504150004000c2c0764000d104810070400107039024842444680725030040150050444c03a5480800c1501c42006001c3d011400740135402e624401300c000100c809002c1d441d80941320b449420818500412440200c3c21a6200301c0c3e20688050010140000d5290042182000c1d1202c8180c00341707154074201490b0001e00c00c540e2840140040c501c14410554001d0800d00d42c045440100030005212401c13000b91503485034003880c00d08181d403880e4031080c480300080f0141680d501401051554480034000305140c4580010041180f00e90440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 221126915 1250 221125665 221125673
    0x201050a0201020717040f050f060702040903020f0d05030a0612050c0105090303040509040f050c100203390f0d0309111306231305070c02010c080d0c0801140607030c060216 76
    0x710302c0300c600151441740d1100c2c01c1000c1d000000711550300191081a0b038a1050741e240d40c03000104ca881c0c030345c122400a05501545402c1c5c0c00d016004441c505540101144203140d0354020b8002c601c281d684030010440e031a15544804072034164040d025000340d01080105071507501480080c0721440006003101c1c1850394450000d84c81c81c40032030f011100c1000740c0b01d07090200881041402004101124580c00500500034025a0ba00898046040d20600c001c0600d24450500b1540304109035608010850200074402056403403000603980ba0592103003004000741584030380301e00301a17164445200814054000c003009045e0b00c0b21034642580355541e4a0004030710020400c115002a1958002c03021030201a081140007a021102c203e0344905082c2005038081e40032550300074580d424200201e10610f90b00301180140141424031102e2071030304c03150383c2017170f504011074a0403252001002004414000203006c102e00505400a01040f1103110207030019045401a040491610440703012246864030303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 221128165 1250 221126915 221126933
    0x41d1803092e050c010e07060828020309030304050615060a050c01020d23010f0509070f0e0927011526060705121503030d1a100504150801060c0201050a02010207 71
    0x6000c0012400c0042c5400c1411300c00c4c060210a201844c0c041c01c10180b0300030002d0b000c00300007040c121a040101c140512000e00040394031440407401c1c2ca0031501e0340b400fa110181d8a9000b51000d40c0c01380700f28000283c82507080000a0685078000d0102418601a25001c0e030307150f0440754414656540078806010003020901c80c20301f01c080f03243e6003c41c0401401168240703c05068011105d9000c200b1014852619a00c2c50320340c220130a45000200300c00c80c071600b00c070006640301d01c075680540f202092100ca9104c0090340e0f21040440820305d400d207aaa8a992401c0710500e07024882603c7d02580c08102c0c4c819805101600303140c1054915800086490915091140442e00080400e90110b41d0380141c1c04220000355020322114051206194240300199990151800741f980198992000d41d64807403c0c0d1217102000a800b519141c3c040350010742c083c1007030f041ba0044001c04544015552492440b60100d00e04840c010b4031840c500440c40d4004444030740c1b001d206542959001c028100c0021804030b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 221129415 1250 221128165 221128249
    0x111010605280905010305031801051614071d150a0305010c20030a08011503060503010906050a0b0a0617100b03090d020709060830041d180309 63
    0x68000801e41a150301e820b402c1d103400d41009100d10b02e080014400983d00008440002c820001c03142040054000125000d01c641e0041c4000d4032940e00481007007100f080d0482408400c00400e4070031580c1c660200080c0700c0ca0f9150b400302c40d1000440480d040001d41d685a50600e180a001e001115440e921003500307403062160780c0400180106145070360140d0786003440c1c601c1110040950318009a1440003440024180155031401040703400c929141c0303020785d1207031006010150090020000d203080020050104440b50302d03005043c400302c503a4034640410314400b56441030b240c0c20303c84180602140b034490310082c8100301c101350035500800c00c002c4040245100d084894014440611005002414040c00e40e000c2009141000c800780400b090108800119450081c1c1171404590342000060000d8500d403c4400d81540005010a002c52301e602c841c0a11003280741c012196440d102030350345489200607440c040e60f41042c084c15916180c1a8030200100c50503800701007000464065a041c840540 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 221130665 1250 221129415 221129449
    0x102010b060a0c0201080f091e0102090a0b0408120708030c0903120403110f060c070b09030709050702060f060321070c031211011506090b1605030f0417010c0e0111010605 75
    0xb109140110746e0f10204103540440c1e955200180b90800c28540e503030b02d0703201012903600c501030502080e4080c01d095059480102c001071403c01d50039664202d00c0c5440c0d00c21b01030f00009010b04440094185034100071030300c40540c02021989103940e83d01800710542c1020076501d0740f50103400049121000e0b950b020b000914041c42d210042964400c0800400a0040c045203004407070500100b60141c2000c1070b00300450308030240450ba1442c0010009003048155004488440e140500340a1060760000d02e02d4441c1104504441b2035403510820182d841d007985102100000780001807001e264401130241800c18454105111f820341c42c0d66480586100f10144000025000602e002181009000380c0000c2006500b15140c91820000014204031042c081c0f1040d05800056200039203240383c5104042a80250a0301e88a4203c0183ca10070766006104000340b040e0100121000b140040c4030300c043c880c2240d2905106854030000540e07c58000007440c903015581c9240000700d649407040c02910038555 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 221131915 1250 221130665 221130677
    0x5010b0a08060f0a090e0309150c0607030b1f0c020d110f0904020904031103070b07020102090a0e060108070806061201080a30031505192d0506090102010b060a 70
    0x440320000c0c0160801010305101d10348041882c5100d44519200000b5140c403a18085039240b060001c040c654030981164680010710189c07082c80031254100034141c54003000b410389580d80c031581d8048080d15a4540807036880304820f11040042c801030060340890781424180814006000d4000490703001c405007042c1c88161141c19524818940045400c146407801ca580b40441d04041d000f241182000038801000e00c00101c280e0b0316502400c100381c031846603010340126403501d00101c0080c081d420050815000302000003004c1034110710701909510414040c0c1d05c03200c0d1562880411615054041d10b6203420000402c10000c000c075440060070301030060b031001003420301d525240c1080301150143c0b4920010380040d00002c802014801d82100e00c120501e0041034500f0030b46492840104140e00181c0d01400702c01c40101c10f41c21b000786110840315040c4003500600345203c0003502c405030941000e8002c5c540c2140500c07491078810040c00c00003a044c80002011080d10010506a0340441c3c80c1e070010602d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 221133165 1250 221131915 221131927
    0x60103020906120703020402032205010b03070906030b0708061c0c18020405090c07150e160b030105060d02070c080601030b19020a082a1306140301080a021003060905010b 75
    0x748041d05641019080d22150300103009480702c1500c0c1d648030b02009108070303000001b040e440304001014500c00c200c0b00514104100e5580340c854002c1c180321400360b009008004000074224940d106460890350003044a100740d5aa04d10101ea0032000201340c2640496a0710308900d4024140100313010031403050000507034250a0261010070b0100071182101e048d03004100602c010b80f240d1213204c1d0402c1c5a611200e80310071051402600060042c580d5588561800d224500620740020b284c058041c14040c650750300b242c55444070100e40c4024007515400100030824125850f005500401a0a02507a0441d800316202c00790942800020b901c1511500b032100140f180424003415101c0c4054212032046203845e171508000741c15101e0003000d0741d4030024010407400050300c9002e001c0020541a02d54160703502c1080d0710507100071015028440000b4840391955204086c0c1c141201d0503900000020a60703955182d00b00001103080051085c1095181e00000842d8442c9000b114060002415003030344400b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 221134415 1250 221133165 221133169
    0xf0a0902040612050c2104080d020a0309232d01020a21090b01030b180a0302100608070803090d03090f15031a010e0f0d08070f0209010f0b1c091406010302 68
    0x71006000004802002c00c445415064031b82a000079400580181c0314403951141080c8116014200060460394000600c0490b55545503222103070310f9100d009100c2010400b100c04c6803240c0a88500301103698030502c01c450292102e14214400032861121011607480d45042143c01c0e1b0b08042400030108448940d00c0070800000f64404030142c400400c100071460041c0c6401d45084d40610024240c04e00704004915590744814150100c2003260080324201211f07803400035511441888a000260321b426004141e00703801191120848940000450030700031080c0810219641245085092240792030340054208104484e100080800c0400b0ba0503030054104068103540c50b450108040d62a661828000ba80e0090946051010240c0710707180c144001d10042a002c2c46141301c06040180301056207001c200c00b03041c1d158415482030b07032240307407599907804611888001805040440f0300184480024804131100c0a20100c0000300080b0b101c0e80e164030742003c00c2008403401c1041d600300034014001d49c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 221135665 1250 221134415 221134421
    0x7230601050603041a1008060f0f0604020408060a150e100f090b130b0105310504090206030c030901090206071202010c05040803040605030402030a0c08070806010e040803060f0a0902040612 83
    0x14003003660450f2940c94250f03605183c14050015040b004007202c80820034910a651541010705000c9080340d241e4181540d0340c0300c00c1c0c00102d90550061069000185060420340259000c40b00c1f040020b05060702c2e69241711018203480405034005454000000800010703c0500b14000c1400e01c1c100031900d030034401c40c101c0d100405d4010152450810035410040d841d40112004c2c5410640400100e905214004a406100744c400341448040ca41d22421804581c203182e000e800d0b041d42c21240d6045a44405202c00c0e929809070107507001d0b000740000780d20141c600000315808014030b00002940303043d6a0000f4000d070401181a50702c015040c9090103155024405c1035200006800d2183c1490725103032105070790313110b0750192008002000c0042421510204081c1d09110b0384031400341003040d10741c4100da031360318518440c3d041c880c89803200015032a10602d0400f030041d1740120f80340d0714598925044c040080c94104a580d00981031560014800c1030a10290000e01450365455460101051002042e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 221136915 1250 221135665 221135669
    0xc0b03070201150f03080309070e0a02040f0503070303020a0311070503011d1605030607111009050d020d0507020d0b070e181b030903030109110d0f0902100e030c040f0207230601 78
    0x1108150101c180070340b800d01109001206d40c0b250b40341d40d59560724074405040c40541e9220201d070358410000e124508010703402a1059880320120f03604c1950742c1350100356464203503200250160300714080d4074010901c694042c1c04020705520840d0451075403080400d00b150725031300c0341c46203004410f9030300c08406034240008000b40304044401e042c590304004c0029142d0401a00540901080d00040e00c5c5041050002c4c1441803843c040030000507055092454448000c850981c0060003401d10001c0c07003500842c240c806d0942c01614140309004c0740d55074112152005803184061083c40b10744244180c2d5403041c2d842c04622035454801c517a0503d00c8100ea000d520300e032703101ca1800009204000d40c1503030005c145c078115a410400440c114806440080f203030300c43c03021704980c8203041020884090401d0703082120158400e0700d2010540505010864840d10144410f6615070480c2d51a61034619140c2c0181d00071040d81c410044c070704a02a9103404a00304403030380722002d44400082908555605001c1c03030780 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 221138165 1250 221136915 221136941
    0x5061513020a090501050918100302011416060b011116030615030f12030b0307030c03050c0907050909070e0607050f01050c0f190507060911090703020f0f0f070c0b03070201 76
    0x10510b00c2100002e45004850b0103018100071022515400315600e0416001210b0440d007401101c0b070601c002c40340c14161560000b40c0c00b0824103200315071513000c0d820484045c02e2154400e100400d030700340d0b200030107440f1900c4031504021609055020401050001300d118160100548210918625003141910f1200300d01007811130101c42c1c00c202285608402c0b208082d4030210100c401e15003a44260014000721340312540520440c0e0001c02000210f030400f2061320700500444d58003000c22410086d0380102110f294002500c01d00100c03840b414081c0029801c00360368200303008010034440128000b80c000d4030060b6a240e000303440d110400802849225005200030b0b01c0310340b60010441c034021442c49a11f08406c5440c48103502d807403005102d203040c0e41101c1da210605100c0884142440340303c225140310100d2083d29094045403449020b40700b11004c9100c0c00b001e072800d102030310301e00304e8080e080040b01e120070b8002048100000781c6885030314005400e0a5461940301e0828040003800c4580b2a2a100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 221139415 1250 221138165 221138167
    0x30612031305010c1505180609070311010c170c010f0501050406060c02060d0204080d09090e062806031502130609031e0501020712092c0705070206070506151302 71
    0x1400314000d400c02050710000e013407088250b0030380c3c50044081d10041c2013400070503180c107050105110800c1d0b0f1401c1103004a038121030080c0c6400c514152128550310004106110100100256501aa035800080303030180042c480c4004040042040990010a0186541c1d43d12550b000720a606403103860b014090541d030402c10036040c502c02400800a804010380b0541020038407210340c041d95011100034100d4581a10701d001e80c01c1d41e015260b5002c5020381082e0741e04201300d01c4441c00d80011118031954882c01d407a02e0f2011011a070074026100c0c0c034802c4540075102c082c040042918400300060009038035000503622404000c3d580d00c01a0107820400800803044020004640b5000c204034035043e9034880100c2110035480d241d402441050300007030421a89800c00c0702d03e650401040d07001c0b00c0c1500c40d0341c4403c1c012800d00540302c1080407500c204040118004c140060301c108040c142180c400380c1050700d07003001901d403d45013050403103ca40d44580d0b030000c3c00c5c070340d414010982e4485241441083d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 221140665 1250 221139415 221139427
    0x6120f0603011512030e030304090207030804020f0409021003020c16030b040b01081207120509130509011823030903060c040807090605060306100905150702040b0d0317191103061203 80
    0x585448a407213580501040300c2079507080355954003402110b0003024402c03000c55030b550481c507002c0c081c0710044030140d1040903c0c803461491420707c1c0c010341203025402030421a074080e1112007680250802c12400500744640c0c0300e40341845c8070074040880a1805102000b24034580762506444803101600140902c0c0c1000250304080c075a2401602d41459002014142e40701510808840d00d01603ca59103074803126103003011100d1b40302c40d0f01c100d0154402c0c400a00640e80d03a06040c52115030821401041340e03401c240400c5040c10000804000c910802d015071346031201d0341000034a844000e49003d103201d80005000c0084040800c43c0400034a401c0d0028130070b8a280100060490100801d202d0240d814980e641420398030032540d10025050041648101c0034404d00a6003945d04014822030040f464403204890780d103003140c9111100d41c0d05644000f448880580d01c4400c0c001c02030131200c030f12010600c13464604c10700750062600d00c02404103207540340d2800200b00300c10160790b500b1b00766070380d0420410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 221141915 1250 221140665 221140679
    0x1020106080a06021806030711060f06011b140a0b1005010e060706022d0403062f070f060501061110050403120e0f01091b09060e1506120f06030115 65
    0x2103002c903a00514016216141e58001300c591203c000340d1640e000e03d00108024035150811121010b842d0703000103d031565600c410310815000415202e00c1d000c00c4a5451003154510752031910380b0b100f032050188411000749034200c0e52130003c1c005812500c844031801045455101c00c048003008010918207260501c21160101d4014400c00c0c1000d85019000070f644400785201d081300052455400e40207000c00f0018403c0008207410038041110003500301303068a0850301c42521040d50407138091010000750510b03803465810991281e40111501100c400032200170030b40c580300342d90080100d5210143d44200010f0002d0402920b0b40c0d60300400b84c503020512000c02c0d0b0007010032401c080071010008045011031211407611400c40180b00030b40d0f0900c0d040c136080140c40500d0203668002004035104030758036030b003030002510550b010303200c4180c000c1c0000954150266040000c07061020340258900041510f14201500301101d076104541c503203100380169414242302d5001e064204070921503446c0d0800007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 221143165 1250 221141915 221141923
    0xd0902090f070e0906010e0d0507090606020303040206091002070f080c130e1507090308190305070219030309061e090516030302190c081b0f30010b040608010b030c0102010608 77
    0x2c04140a404e00c04000b03025a402003041d5100c0c40e42c0280040c0044505241603541c92a060040ea04003900340b0340e00059407400001500e0150758010482d41c10300100400b40003012400494000451050a00010700000c4c1e001c0100003520180c03010b802000c0c21001808000070510118445007454111003c0003100c1c007244c901030180e0751003001d1220740c5030058126080c17100350704003401d240b03000250362800011610070000703441d1060300c0070f0205030390b0310354107980781c200301566405044030316807d103800244680e010415483c40340c600090026803001c818561001303444880a1603d6880c20f40c0c4042c00010020b6004192146090314021421650000e4948404180c0c4040d8410508042c0b410007880720080700142815108a42002410701c0103031044951840600b40900d0700300006440700d0501468409290341055400b030085210188001604d0082918100140d540d401c905101d42e616070040500a10001002280c0180800304050810102c0c01da079505581c580403080101800102d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 221144415 1250 221143165 221143187
    0x60a09030201090515090409020a18050609060607030807180f06050307140c0307060509010908030906010e10150f020f010e1014062101060305150f09010605030712050a0203030d0902090f07 83
    0x140f0b022448d80d03500d01c04070321520441d40054103000c0c40110303031100742400c41e4002845a0011120701c030301d5031940c0d818820310f8800d03c40040c0000d0300c10700001e8940307401101807102031070024902c2091300c1da0b18100c00d290b9000c650030800000c0c80c00070501030035035800040e04c070b2811225100d09242c000c80d03000c1c00396203105100c00140040d481d0000a000b00c0420352044422031703008084a0740c0d07450310b04915601d80d403090003003942445540001ca0307e10540201d482c4181d070916201d58030f4041c2c091030142c46680c054164042148910031000324001020300800300700303590f02d81c010090200480950380543c4e4000780c95801c04c0302c2d80020071400d50f41e0070683c120103100800b0348004039980303001213034050003031600090076911807080c88400a41c40c00c14420300c90045e00300d0b441d02544410903500c0c00d03104a44151507240e48018010300010400d600c03080e03403182c810402c60304420032176801300782560895030865142d80d64034a102d000750b041404006078040303410040400140380040d0041c060346105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 221145665 1250 221144415 221144419
    0x810081009020303070f060e0d140403030305061f020607030b0415121704060804030e040b0d0813080f06060a0b030103030903080d14040f0c14150f0405060a0903020109051509 77
    0x1903081c4405540b8180112480706030008101c4803406a0b6007031030b202404001c1c5d81e8087c07610960360a0603070306d44034201e0101500003244010b0700d031910390f0f10101d02422005c1c000c03640c0401490704000004490507081c031070f1251560050700480c0307402c050150440d800c407445640281d04000300740420f10b250a00e20710689101035500c0c0120b0301303181130000350400d2260f070001510100180101310079401c0550640f00d244640d881c046500065130520058030200c0b504d40d0741000d41159908006a451005092508902c2c2c07000050503544101a528008000c41004c040b50000c20501c1114101440c2c0c10014000c140308051441d41341d40d400030442211844050843e00c00428004040c02150300050381d041007021880c40103040a082c1020800d5907030380c0c1203907080b41c01c81d00013800a12103030001d416210000c2040344500d5016040202a03841440b4004090408000c0818155100710280100790b081e641d03000d50721801c2d48009010381020f07400903803003544442001c40f180c04005084407001c400c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 221146915 1250 221145665 221145671
    0xe041509121124130c03030305060405070306050603061014040f081006081f0f05010308130801180f06061a1b030f040513140106031e1107020915030313030308100810 73
    0x611a01e4000e007584e0f85000805451007400000103040c0d00d5040319004460031030f020032013511405815400c80300588101a001401030000983da071401900010b1410501d0a054a90720482d902d048416400360b0440c1c00c015681000500c4040400c002c40e21080c00e00510400c003160a000d205a07a585d135540851000c40c5a0741c07030031644070280313402c1a8840100301030705008550312444c004a15400c1041d040506080b0400d0000751490140188500c0a01e1034407920848140c68680745000e01c03000307c00303540954407a40300103103000417801d01c444051144250a0b480e4407809100403c0c0401e901e00301c0405600a10071101c082680400f202d04030307a4101c1e00a42c03002c0d401c1000001800007518409112000c120002074002d4068211807507841e02c45481016003050300c4440c00840b2801e6501c940155024002100142030414020703030030a90b0031048400003010080020329603400500d05143d0f00189820030030815410810305500030b440203004165907030400a54554a12400d15000e000310b071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 221148165 1250 221146915 221146921
    0x12050c180105091503100507030c030908040b0f0c060114010807020313060809010f05070203031501051602220c020a02010e09190213050402180901050114040e041509121124 76
    0x251500700d40c00c11130000d030586001049904540008101c11900100424100b89a0420701442441a402280c0d48011110f040c541070204001c8290414002803c0a00d010403941284290802c41f4500805050354410040c082c0039000605600003e07044e9002d41d40b050016252202c4903030203000030707100c04d03241204031590344403030340d0780501508004854181e1420327043c0106254040000d521550000086400100c4d4001c01110035105014010721004807660008006103080711010700c04c00903920b10b00b6a401c002428880c1216814016031015910ad44580c1085580040c40711141b0031045840301030600c3d008014000444080c416080c80c00c4c0c0c0060800c002500c4030096502410300a0000c540700d41540300c400d07000034142c06610340b144c08000c1c00010303198898240100510041a201400c1902e001c880d4912000060301c11219251800800140300d000761003280c5500d401500e20b40d0307405060320340142012580784000c0e002604441c0010740700c1d00c0a1b100304001000180c2403c1050742e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 221149415 1250 221148165 221148181
    0xf0301030b1512071509030b180f0303161e051c02041205100f0e0703080d06120803180c010c0b1005030a05030403050124090b0112020412050c18010509 67
    0x1d445003158a60003005001200b280b03150010340181030717800500ca200c043c00002c44082e50344501510004120000220000b07041d0198001c040250a030342070111984460640314960843e0400c44d5400541c650070280110f032954001d400d00b4402e030205141c8155004180c100805e94850a24400328580581c51081d900f144944d0444000b0021032174420841c3c422032902a455014501d03017440e80d9424241412000b0b0841d10548007041444402881e07011328540c1c1d2255503030404c50034080c2c4660b0311640080c1c0480c0030300d241c103c1c032403066800a40d6171400d41203c02e1119251100200c5590183c0c0110001d40d03081064a041503802050003c0340303540764000034581c0161038004580501684ca4940200714000011f4015603201e94001d109003001604400b04816150703242034114501030800308076003078141d800b03403130f0241041c9024030540040c0e8455006981c0310707900800741d0300040040306c001d00c0402d1107948610702c3d00310f500030a140c5901140100586041c000c16106a1222010941c18 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 221150665 1250 221149415 221149441
    0x1c12050c0720150a020c030f0d021c0c06050a02070212070812070f0503040605031009090201050405060a030b041b0f020a0206030406051008060f0403090b09010804080a05040b0d0507020d050f0301030b 88
    0x2403145850f4441e41c0c2e50f40d104000b511003c80c9002e40b406403064860319a82085c0114407010341400e15401410540208034034814035035001291001801a0003004a01088090050b80e104454080000d43c3d201c489105024482d2401c0001030400d4012010500c0385040200729481440040300c02e8507210525410072001c003000c1e84000070814840000c2c0040d1071f44d0131902440c4a442c0e84054806c540c4d9075090000107544070010001c0c00902c08100a10282c80c043e0040d101031100d40c900000e811760b076840440c040fa803a040491364404000103140441991141d0003030035904851010781641407650340400c400d0f00002d04001c0600c4e803581c00103200c006118849200030180e00048400070300f80080c070030006034000c0d41e0540024118035008985103c001007101c00200041e036403103400c0d40e01d644030182903800c4900c1c0d41040202c108000900d41f400500900711845808400080a050041001c3d05d40841146940203000c024414034141c003080c00d059034110303a040441054160fa90344145407130 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 221151915 1250 221150665 221150689
    0x11030c0106121407030305090d08071a060312040f150c050a0609050d030b0d0201030b0f06040b04090501091b23070503090906091909051c12050c0720 66
    0x10640c60008001002050760019040d00b5001e004000d4016042d03489140c1c48601034040900030520030000d6220394188594054402402000100c1c1011815030344c0d0211030181c8102010409404418800107160900c040395450014100380740c581441d16907038042040c207600c604400e180003403058014247c0103034401804c4644c4002915100c020070328050000384801c2c41d054540d071150203022501903019110f52620110001c200d104000b040e54011006004e00c00c0020350004008081e82e851512150b02a001070562140010f480303e0070145007c0c12510141d000e6001c0f60304113200043e00051040e401104581c0a140c1140c00c0390900891101e040d041d003141070840c0c1000184902407020200280002807800c80315a03203d92110b008100cc110015207210315200150003400611025640c41651707054030a00070741e140016606084c0c0c1c02c3c00382e01c25140000c1062001c2c0c2c1c119400303040c85842c1d400000000032034184402a00c0750210000c0d03028024a035031200081d544019a02c2c8240b401c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 221153165 1250 221151915 221151937
    0x109060507050f031c0f060509060d060b0301020a030b12011803080703061215051b030121020d050a0311030a0903150e0a03120c2d050c01050f070f0507121103 70
    0x180d05c1034421052075002e07140f03010100405161850390201161940503000c02c49030001c0040c800f0340c0755401000b008001040c0101e4125070b0741d603603900380ca407003e0002e01480c2d80107840c0014a85110301c184819802c25214240232a4503250440805040d01c007648161580c162411510766580d95006074014502b42e0807139a00301019040135404c00c1145507100340c01035020481030110791076605440c10340c541c0f4030b45186c5481c1814030043c4018101a105c100c2d0081085003105030440c11500440c10441d5103440075201c40d0000c4580b40d09141e00702816000e023203005070040d864094001001428003295020040c00690048400c088048464005a18401c124015110008041c2c40c1c06800082d01e0113040c400c1a0500c170240090741d0240030002118001c0d6103000d50546084140c501e052120206942c0502c2000e01407001c00c3c450034420244201c3d144800c1003028101860043d0690f0f4030210f015003080703410021107000844039034800140c40c81e00d05280003448040e413049421406081c030059 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 221154415 1250 221153165 221153167
    0x50d0305070f06060f0f171c0201150902092d0105031510030c0e010504080a020405070302040e161d060a08040819021e1c050304020d02040504051c030b0109060507050f03 75
    0x49417840398003000d20112075442c01d107141425510007481004401405140c452030b04074440a42c0800000c030a01a5040381e54400042c3d0018041200d661051968002e42e42c9698082164030740e03818082008101c1658400181d4005090301e81c640070240208681e16041050100c0400e45503125104e12014503440180709800310180158014001d2070965040070000d00908a105025405901110195038802d8060b1204950a4007400081c0402802c1c0e001010b508000001d081e1280580d810302446404440100301c0d0740f182d01c001c0408401191540d188a101e001e0102560340e0081110060302407400c010300541c0da41e0030020010b004010760700302d00d420760000089120b540421401c441b52800700c403228114001c22541c547d2100350701c12110541400c00415014640244051503000c0d01c02816031003500038541c00304082e1501981c0441f19680141a01050f01c1640782100d0380c000f0713851030100300e00140e10307000802500d8244240400d01c540003641034103001c014041c203d45114050202c07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 221155665 1250 221154415 221154419
    0xc090603060b01030b011e080c0d0e0a330b0a1a0d1103070237080702091e010515130608040203060705040b09041d01050106030222050d0305070f0606 66
    0x80740180902c0c210311400646002c107049400d41c040c001c0b00c42401c00c1021611410031200e0800d40362078001929004100d101031024420310503041c080d0154100e200405048051810b1902c05a122690a911002c4c004000c560750058401254410500002408086101d09024005c80d02d4030302035400c11200890b4a00910004400703090040c0061046014100b0040440880703c40c410f0000751810740058000c014588007445034268030344051404841c08280c00c03000752050f0716240030010021150b0789800300b00c02056190030f07206143d21060503000101c500041d88030318209000140102407094031074240f4035951840040030307100600c0405480e0100e81d0340394100a00030b02030498049100307100e08000504c83c5480740f42903030701b00d030f5000c843d2034100381003c0100b0002c1d00c1d5030305656007907102000a09401a0003401114024003045c1c800590fa42d00c0c0503101007118070600c600b042111140b040400c003585032005840600d44d05407403c81c0c0c41b8501460704030581900f0303a501401c224181a00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 221156915 1250 221155665 221155673
    0x905010b030a0b0f03100b0a090203090c040b01181503061e151b0c080f0f0606041a0603100509070e01020a080703050702030601030b01090c0e09070807021f020304050d02030403120c0c090603 84
    0xd1f4202c43c401c0341c081e04403540c0d03074800e4810385c801110080e007990807030b0f8002000c6041641245228074014107080700d00e41ca000c08911a5218240c1c0500559a1010350f07005038160940306240c00703040c002602600c1940c40415208180f0018171a000740b00142101c03801d1a0340c4210780b0310004104940113800c4038041800e001031914180e00408001d03020b40d11907038444060006120680c0d00c1c201025189590b100700c1044002d04840003400b1042c09160744c00b0f5416500e5400075407141d0790303a042c3d204105040406010f03401d28014a0442400500340001c81c2076031b0001003401c5420391000000c1c0e51144c141c41d040355207001e0001c0081d0540b103040b0012003000680e00009040e1480d05004000c0340310030f0b174000c4504111200c00e660b0000c20000c04962050300c9103000c20761001c80c0f40115031040d486030301500300e0302d140704c150307620000d90200a0108000e01800055490813182c03006605082c01c41c0c492401c1005480c0310101440f14503001c500401ca4052400740041012140411906542e420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 221158165 1250 221156915 221156921
    0xf010936060f1401090f1401050f1209010b060f07080c07030c1d07050306150a0e1e12060702151801090b150904110103020d09050703050a020108010905010b030a0b0f0310 75
    0x901420902c1d80083e40e01c26500c100b01103811a010b000c002180c10349000e00b080007682100c91020304000b002c00c581c1060748402401840700b0401851801c419140c05995542141d980145e91446000204182030382140004181d800032508400c1d0342c0c0d13540f809140d16034507102e096030004040d0880070400141d00c0409074414900d144403810032034850350f11018121072611044030104d901c254402071480c0300801d41170142040a5180c01d0a0400008000c005141e8039141c81c0c04a5040e0458078a1000ea400c00c4444400206a18402000b4604003d0400703900e0301c0e0b444426502564002002542c41c8540e020303010520041310008200e180041c2c24400c00e544000c40304030510f4030304484200c0342030800030405403045400a07400e40241c11008011000795018980c2028102e40300c0301d800011076010300c4004000c5214000400041250740b0000d00301e01c6050340000c50481c5094010449040034074101c99010410202c0000c05829117000030f602641d1120401d42c0511807002c1304444214564 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 221159415 1250 221158165 221158169
    0x904150608070809010204080706080406021605100b06070507060c03050d050108060114060a080103150917030405120c0a020105070c15020c01030b0f130207020f0d0506060f010936060f 81
    0x581c030500c00c4e503110180c0b9403e03841680301d0020160712200b02003245038030802c903a07504103100342405444c08032400c802c96480032510800391115002038031a1889000144207070b401d00003043d18407d0401c1601d4544548881e558403a01092094104140741058816801c43e088a0b00d01d0700c080001e07584408616544d840c090103844030b0102c980244420500c1d2510039255030341d03500d80d203e085030780c00e6566000950100c01c00016105031a410707200009407603003402e80000710040c22166100c1c0b406041080c6807050440c1c0128501104001e2045042d070045186451aa02800c0482d03940c5141d02d04585d04c070142d80d201e8030003c401e5a2400710501c0d40820511100c2d10240d0302070041d40b40d800e0070409191701100043c2d038001c03074841c00c080120305507401808655000619215014031294046410201d17080e500f00c54540120041102034604148422000d100030f290503444a42081703140000d020724254228031402154020b000300024407003d1141c86140700e081072103c1e9a8032001014002094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 221160665 1250 221159415 221159417
    0x3020a0f080301060933021603060b090109060308070303090201170106170c190e040207120f0305010803070807060509070503121b16060c06180b061309080d02090415060807 76
    0x8044001140d01640c2200c1c84404070103071080da100c4001b5038881c3d40e40304040d148001503010b940301c00b1403e0b0300c029403003000441c000d10000c11981e5032501000a1204140c10500107103107403d02c00d0022034000002d07141156814240003640c45003d00041c2d42c80c12800400c6410040903400100d03000d503000403402d505482d1503424103041e840e022000c82c150b01409a0b09a2150b0342143d250100b07501c07a9059502d1030901a10051810300c580e12040c40341d20700c0da403001c4080707882d10504a041540c1032003040e0040c11210041c605103c2190f99188143c42805000780c41d00d500c3d00c02080d01801c05000e44001008010f08482d0145620071852605070040e0b8a22460b40e5104413104078045008100b0540c000b0f80001503028260070104103444d080d540f48070030348100740c0d40d141c2c40084d41801c008002c103040c0583d00480032441e10b5410002d14070760740b0000321105801c180d103000004107400e0a9a84004e0405405030b01d0f00302c05008100100440040c480f41c241400500180e125007080d6198016051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 221161915 1250 221160665 221160677
    0xc130603150c111203060f010c08040801150815060d0206090d061a013e0313090606050702090f09010e0a120305010807030803160504050409140d0f0e090403020a0f08030106 76
    0x1903c01c2da5194002d51803c40d0072030404100050541c0790040c0c2040ca0100141001c2c61001220f072a031529a40203034100442e030382e40d221051207418035041c021900504162303008012200c0c04145818a50030094482030142101450a40843d601c010540d1050700380540a103609030140c0c10644050404084485201101c41030415203e5100f03140000c4040070340522000114803440d0004c00b482c45102c000c103000280c08a400045450034400ac0c00c078404c1100c403c500160800740220110745003980310b0001d02004009050050f01e079005040e074441713801d4044020715a242c10465004d02802441f03800d41e80101d16603802040110500c04152034a03c0e9410030440c1c1c2c1720011035a0315800b6000c00f130401ca000340f0010f5498200254a100d803d0403500e8014103180c2c0e0b9601203426180501021a1500b5a0740840300046000708860012840680b4050545030042d84000d0026000c9000940c0501c5030030b000102494020080b110b501903000c400c01d5045000d82c1003122050b0402c0c000d103000500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 221163165 1250 221161915 221161937
    0x319020a060302120103020931020901061d040c0e0303161a06090112081b0a050609010b010f050d060b0406081e0708181606030f1b020c130603150c 65
    0x8801d10913100002e224000c41d034600e0f405d6808112210354002d050b141100c5601c01c4004a1040341e405803400e0340d850262134101400c5034070420418410581001042100b08110040e0a81a0240b602000f01080c3d40004403102848002c40c0c44450410300c02c2d80501c0002843d000c0804054008a4882c0c081c941d4000d4007104680c80e4410110305440ca00d51000b1243e0052003d004101412244248074140d242d14216002c641c00307120404948458410303802910f6040144401888032541c84a01c84c0c0017000107045810010304400d881c4a01d000c2000408902039070071240950040c0c02074807180391402e03203c680c2c5241c01480100708451441d00c2c140808221480080c0d02d101e480d000d2409600c80b8003846d91818021000104125018601c0b84505900c0c200c00d812244214405000c0c00d64002c40e900c0c017407030403800c01d60f08510584004880707032081100b4095070105803800842000c441d1415051043e41e1070801401c81c51b00042c000011501100c0d200004642c80b0071030110f12901c03818a000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 221164415 1250 221163165 221163167
    0x403140c03091c0302120d0b04151d24060f0409060f080303090a0204180b01241707030c050c01050c0901082805090a05030c010207031701080307061a0319020a06 71
    0x1100300321001303000d82c2c80101880f0400480346c028015202d51148001508012800028155070806180c8501000308420500250500c075118441000651003210310034180143d01883e81d036100c02041e402c0300c44800554082e03031383d50320860340d01c84455401c4585981d103038410b11008003210301c1200007904080000041005c400700581e442034801e003003d4615440390740c0a0001900c1400381200c41440d04080740000a1812402d41d4007820781c20500c511b089509021583d050001c14494100307001d00e8030410f1003214078442c061076002e8013134600030072301c4d9055520a580c28029103008007929424603040080c94030030f04000e001000826a5000c078151144801030002200c1d519000c06041d041809824104141e0340060b0303000004801100c11500d02030300d4160a41c0c02c074520105099400240a2090560020207410001010f540d210001e51404d0702d0075503244100741c401403e280e16145007405c03410311023041e040f000001509a503141590b00d400000340c0c02c5a06000c038860b2114040c007051917 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 221165665 1250 221164415 221164459
    0x906040b190f052203020d12090f060b2704080d090506130213060503030a0315080307030c1104020c03160201021207050616030203011a03040c2402010b010305130b0403140c0309 78
    0x3854041c0c016000c00429904101c52140076004c960303040340c0e1100c90f4270b0001070748207000b0038403140204c0700001e60344108001c200d0304103000748038121015030340e115217045a000690400d4005038080061580d80d00302c0c1c0004000740141007005842401641c04200b00c03c0500042a045603100711446400c40c0d140d4176101c001c48525029140d0194414412070400718002c0e80000c140711042d41e050081c0c0c90352112507034a03540c0038417811030000c0c2105501008103d14040982640b000450301541000d4040105030740d00d004181c44031034010002c20400043d64002c0c05100780498143d900780c0c1c0c0d10030311818040c1da180d00644032501c0391001202c0890202e8840e200341c038180c5250304503a00c0811410340700c8259940000d401682d1406204100040c4042889241d4121a071061b8407250183d110b40e5000c1d086135100c0e0700141c189411b000402185000c7d11040410555100b280d0003103a440324182150241900f0001060385140041d026044010001c060f0440200c211102400e80302c00341c00708008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 221166915 1250 221165665 221165731
    0x40e0109051506181f170a021e0d03080a0f0203180d020d12020a0e040c20060103030917010e0a03180807030210030b06070615030201080c030906040b190f05 69
    0x460b06551000c100d066043d07400b114641e000310f050480103a038031b5018100f0441c650b080740700400d6012011580450400f5400c103000c440c0b10700e940d03d10290800010803100800000020304001401001400381510782e48005900000030700d085441c1e1409900c0c3c00080800c1680300001489442c008451041c8001791084002e80701c0c1d0340c0c4240b104507000c0c0d00340103504007003c1c007010f22026825180113a01c49100301e061945055544407400420b480015002400e04510f400b0683c00c08801400400e400019500c111840c007403903c107503016210340050040501280c00000d0740170342c0c0008424554010707014503080c03821481050b0919614460203940303080c5440000e400a0005c9103209595010b42e12482541c80d018040a03c0e0107403554528007100c030100e4070140045c4c00303800c1c14070a40d40e000d0070741c2ea4800c482d01155455030409001c826550f81c00100014054541e000010740101d1710303030012211034445642e0a01105450140401c0036100455181410112603412000b502c0707052646400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 221168165 1250 221166915 221166949
    0x60703230706060b0a0c02040c05070b19110406051606060e1005040608031206040506010c0b090d1803020f040f1509050115020d05030a0504210f0f0e031b040e0109051506 75
    0xc946c6403d83c20301000c0c082d8040c42005001c01444081d010400480e042480340541400103080402c00074100360854021504400710110140000d116540d0040c044903403001c5218020104c2641501d006000391045420810705045010b00780b241070840c1c8558842605c00444043c089035403501d400703aa5a0050400301c854110000c0301144290034540e000310340184041c94111712400407500c40c118900000e861101c2660b11003480031141c80e85c8400311000399a00140724514080c41c680001d0403890a4100c964806c03aa80c81850141c88001c0e40210b008034504401092038503920600320300142000d10465030801c0310700840822103403001c036035041d802c205a11014115250548090001e00c00104110b4400101810703440a10082009100c20b84201c1c0e0703940351050b444414010b00c402c0e252101401404290b017000714055401240b03a00340b0601100c51015154000c40018020f800240c4c645002da529014241051200104101c80c072005e100700d80d60217944880040c44024080c5074042d030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 221169415 1250 221168165 221168177
    0x50d020d090b03040c0503150a05060907050d0e010f051801060b0405060f0318150106020c010807090b0a1b0308090d09030c0b0c0c090f07021e0c060703230706060b0a 73
    0x840b00c5079511001e0340c0c21900800c00c00310b800d9142c20109142940d02c1700281388419480c0308115500051f40034403544980280c1d05e8200c941051b40c0045c10502814120002d071980f0f40590440b0000f09500c100ca4004482a040c1310a0812603403003201002046050341c029400d20101140d40715104c41100c1c2140c80140a49162440945a0803507940003c0c10904160941c0503114440b42d00420804d070320092203810306242940b5100c00a40742c181a01581030504c4401d60070415100c1c2c100c0742500c11076411010003582c80d000308200b100d20006078030341c0308144483ca8900ba4180355018103800c0c0b08a00c0c0700216103d84003114030548003555a480010030500c0c007184113220b241040e0b4050100303d4801012034000481c00c4001030ba400104440c40d40441460004000c0d00316070400c110443d850345150f40c601c5070360520032100e03110000c420f00c990065200083c00310030140301c2d207005050613001082c0e40c2511b03480303004885443d62100006650745802c2800c003051034800d910444e418080251100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 221170665 1250 221169415 221169419
    0x315040e1501060e0405010918060c0c0b1305060105011b0206070f0204090b0402030c0f0307030212120315030c010e183c090715140d0e0109050d020d09 67
    0x84040c0001640038186802030701c1c90080c0d1000040304541c081d24581e140d00201d0800b0000f40300865105900c14032407103003416101101e4958101c1410322560308a64080765015840c1026150350440c60002003580501004000d91705000500e182101c074850b005072905a60380398011607851821710740c0c0040d00c081c85000b0000602d00354005200d52881079440c80700b05400d0783c00241c119110b142d002d481e103442243c200300451505000a005801c0d04885132154402500042541d900d55800002c0c042c074102c2c411a02c2c0034004005030078035924042c0c82143d40749018507011143c108a411041c3c002d20450b040c036440fa6014060541e2080005404445003040354500c10540e00f078082c014464a401c0405009660240c04214501e0074540c0e140603d26101209000e03240c4500041c0b4501c1c0c00d402503481070002035016400904404824035000030304d0407012005202034415060b00010b001c0c600407070300585400c1900178207000b50240d0309442010004403020398540c158210b1000009140180c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 221171915 1250 221170665 221170669
    0x108011e0504020d09030e03010204230f09041b050901051f11030c0d090b0301031211030c10091a0103081902010b0402030a02040f090908040302010c1412130603020315 74
    0xd024800c0308400020505a68a2000c607080360f00c1038800c4200305440317491a10501d44c104d9400425090190002c5160514241c100c200d403905c115070300c0ca142c11400c4441409941c600340b24101b0080001c2c81545141058a8a01000c1000382403210300e1031000c2800058a18211680f035049400c042c054000c07102c00c42c0790342044002e8803d600c3c003d22444910480d550401000900302589450000742006404100007400240c260b07071280d40205000c0005000181540039a0381d00c01029050808280c4c02040c1110b055000d540d4022140b40b040314801100c8110a8008002e841c0c00b84030282800c44404148801c029800d0001a114801c10032080003000d00d1032894600c81c400034800011032084c1400014103031f030303c26200d810380c0b2034003c5401e000300c80000009400500000c1020000d0b0080d55840b50400c0c01140f1000c1e050003031034103994052181c01d40c4050007200700d11040e9040342d80b4004802c4044c1d0000c00b00061080ac0416000c1400d40c024800c0301d014030b55031702100784403000e1802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 221173165 1250 221171915 221171939
    0x703080a0902010315170709020301230d061e0509060402030a031407080f03150102071a09060408030307020706021c090315110c01020c1203060d06050a150603020c060f0402010801 79
    0x4012810542c0e07601454006420710071711003000d401030641c1030400290b40580c0c146440081e400c402c80f1a803040004100078250091410200c0d035844504124180030000042c00c0e2419600c8042c1485050104601400241d01c0c00070b0f03003038006401c0810058803038a500c1c6943c0c000485c1c0003501540100c1e03000d0042802440458050420725400ca49802c50540c1c1e01c0800360440d07108040808804000d0180342e4410000c5000303804828402480c5507071070804019007141020039111406080000c1000942d00c40008850250100300308607580c0341010741d8000d58400b02845a0401402080307184841241701031340d08481c500070b030340d5921035442c1142c1385c41c103502d001c20003012220750b80c51000121000c80d45000d0b158a1140100043c0c0302c1c0450500c19043c40c40701c0038190595041001005280d43d1444600021030343c0209000480c0d50391035550a0080010300084402040322200001c0c1541c4d25800400d06001e0803010b55405803a280c42c0f48101003010380cad000b8007041c2040010b1043e10a014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 221174415 1250 221173165 221173181
    0xf050d1a13020c060702030310181803170601030203090d121b09030b06030d0504060804020a03063303031b05010209040614040e070602060a0e0c0303121b0703080a 72
    0x10146030000820000141020503580c00404003180c01251902e043c0c20240301d100c0c0c1c4902d050000d1459460140c8107824014118003c0c2c1425025000312540c00380e1b204d0344001d60007030100020441008403410080d159455200910441e135203904001b601d0395109000380c0e401100c4000007452a041184003d40d5a02d140c10303400310b102980c40100003804030020f03240d032081130720949400103194150b08207158460001000240039a0001444405540e4842c0032201101e80c2440c01a010b61510320019034500300300c0d40050715141c10084a20240c0b81c00701c001402d07450104c8400c030303880c5100c90000802840783d8800a0041240b07000114008400039500e01080c5101e00300052401c1a01030010b0308451458200200d0500d1024100103982031502c43d0215500c03103c40203021052401d4002551640c00500703031403100303031254840741310b081040000300179805000301900d40324480c49601c0403204501701ca4600700340103c8483e1442c11410300c0101c0341e2682d091f0303881000300d0b900d20f210300018008003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 221175665 1250 221174415 221174441
    0x903030702090a0c171528091b020a020d0809151305042406111e0a120512220f06050a0c030b0a05040c090506160507060f050d 56
    0xc214400050355403041c007600c66010007000141e60740004d54010038404a60034a0007401000d207050044030105503901d0420490704a030a00b0720141403814072030302c03a51042c540b2000a0038481c008100c1d1079550304401c604038110750240c0440d950b4020100c1e82c550219501941181e0030344a0380d40400c949000900071034502070200c54605000100c19081607000c42d20612600c40756107028401480c082c010245c2402207a040d03200d01c4110301c49803144420952080c1c0041c4100643c6450076114103104404441a400320744e1007101890450003926604000f8040324005200f07034550500320301440c151040c481000c2034a04507955010008520b40318001c000c0500301101421120024802058440e803051180002003030b1424011480400e03204a0b5082605160401441a40c84d848802225045a008036000304522070615020380307080041d500059040080062001c495014402c144452548200304582c26586c0e03440d0212800300c1c0180c00180007801c10030101c0c0480c441600603480d20014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 221176915 1250 221175665 221175667
    0x190306020d02071407080105010f030b070e040b06041d01050d0b1518040303090204050c0f1e0d0c0504080d022e0f1503050622021002070b0d0204180c021002090303 72
    0x703c0d84500001d400e106921154980c006581805000310a0040c240182081ca030048600d5065a0390030708541c0008200c001041401205072704a81d0300d503084800550b0001d8006a5580d403148020310005080818880502c031240000103403d01b013003d41001e07543c0d0080f940842544881c2001d081c0c2c440008405030f8030982010344518010310784100d260066100751070000b000b607000d00c180f2056400007001d4150360f180500580008100718012190281c4c40345240c0380c200c20380c0c984281094055242c0d00d400c103614000e8080d010b0740d041070080044d6000c000c1124054847c145c030072a9500002901c1008503582400c00d813118605500c0c3c03841e605034560301e01081c80c03503501c2c407133408481d03400c035544801d0303100110204180320b000d00500b500004041103521a41c000300c103401910b0300c001d80c0d000740241100203040c1c00240c828002d00b009080c10121142e0b942c0c40455060000e500329020f2010107903440d0307007004000581407240300c00203481600900104415890403c00075000a805940c01d800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 221178165 1250 221176915 221176927
    0x70c080c0111030906070201060503030d200c0705030f030c2d060901020a0905120601030803040f120c02100206090a02130e03070c060f050313080901090b03100501030b190306020d02 80
    0xa0207550300c41411044840d440785400004d00340f6080c0e0181401e0103591401c0340600c070f50344010003142c054507000013004ca01c0f241240141800c0d41c90f241001d14a000f0086511140380382c02140c4081158021400c580b075a4041c0c10302d20781c41c1c1c400d013041d0300042c0d4020b041d800e13130300040fa0606882c091006904100a078100440c0c55080c50b030101c580f201107940c0010804845600640c0c5030010b042d00303850f110652065110346546e03030072040c00003902c1e500b03012000804110441c66114100341e07010118003101301c26110060142c4d000008200d10400d400360340f1641123440001c216100e1201c2c44002d0000785c050740c00380200f402209c00325103080c0c4e0311240b036044815001c10041c001d043c1f0607911001c840340b43c088002c04075119540030f4070412604105000d4041804520f40a8407500301040958840c2c100c1c0c0103880741c40a03544810800079002c810000b40c40d1140040e00100c0704285c8089c04100040e1007003040000b4001700d642b446420120062000c03c00b1a800b802038560b55000c018a00380c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 221179415 1250 221178165 221178187
    0x50c0303040302010b0310060e1317040603200304050a0f03031503210207050306010b0a0302040320030106090608030a0804050c0603130c050306070c08030402010c020405010b09090609040b070c08 86
    0x20340111800e80250f03455201301c007030908003003004850f00d818159042110700c1c141004d0b0450380c0d10246c03981c4040d00c403044102c0d042c0004401038555400c3d12682c103a41e6107543d03000240140c42e480c420059021101c1c9041103038520030030226032017a540b00001c2e0059040b00c0c0e072003038540ea5007003900340e080613641c0c8800b0149610112200015502030740c3c003c00a6480b8028150601000b50f24032400c5407c00341041201d500c00150042c1510240c800150311001d50044c2100240244d51014000c0b68141030a864000390411000b034454100340c00074814035803030708580b400b80d40710340c410801907520402002403242d200e00e058035007040c468000d030b03a000034440000441681090b034100c51160001d403041070800400450440040c0011340c050401c1c2c1c079000e00c01600040c01c000c005403030344d400080058210383c0f080d0104a14598014400c0100f03507120041d08059410504256001e00343c10350201d00305203080c0c07448a00c00c1da400b689024480d43d95503800c40d05810078501c1102e4102c403e21a8070915 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 221180665 1250 221179415 221179417
    0x30608010c050c0c0a05031903050c100603060b030d36060203090a1203050328060b0c011104050607020409080409180c060c031d06040f0e1e0f060d03050c03 69
    0x500c1c0a03a600c688400d00d2400711801d0a1312002c2062140041c0a410040d98501007489406002402c12404c2001da29080546d050b20038610081e01070301480e4007550f18240b090f400201a80d008040400c01002c50703405040d17440b44548044000b2410603583c0c0c5110903010050140e03902c10140f03981a08031083d82000c0903200fa6600f140c005078001150040c0c007030404a40ba03400405c1e600101d1118425240c9000d4000d110142c15103400b010020340040d040c40d01944644021814640b0070814542e84000030300b00361300040c031400055400d00c1c640c6a4080c0c4004159404d03944000d06240c54071020360f003000001c0182010480d41c445041c000000d0111092051406503440100b120b0580384892030840c0d20000345801c54424800303040ca03000042640000c0c08074030400f0038044201000b0b05e6400080705406140c0c414800511409400300f602480c60170200c0c046c2c7d6a5440e403011600340c0c000242011441110201c0e4100d401c680090303003514000703040c1d000c0e090003401d18502c1c00511a0040f415 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 221181915 1250 221180665 221180681
    0x402030a0b0a030614250e0409020907090f1a09040c0c08070b04020f060c030307030e07170a1505190f020f0408060720070306090c080106060f141309020a03060801 72
    0x40203075558280c524040a00403401e512101c0c80b103a0006504080000f1035588000c0b1b40c1110810020211840d020b031903a904c42c0f4911500204001c20601c3d150400801d4202e00d40248810540151000209262030305100030f420080307505120b0070140c00034288401040c070071905400700040d021081b008118440000c008560150405175a2450280140045100c0040049000d10007c11604902ca1f4010040c2da400400318540400d0340150014603030b00d07000d015044221501d1020880c550b00800c0002c1003030b04103200d5000a011403d000001d0b104460b011151948400002c0b0461043d0054a43c4030820311022004010304014113100031418980080d000f4100c10391041341480b84840e0004895201c000a81c0758100400380e020141e2074444225110003072805448480c6d550403c0300e4140c0d000c0240074942d000f000103ea5504004000041e02070010b008500500001010704000d402190b0f00040c9003030402c5459882c120545c13000354460101902010307a030721001704001c2030a00601324 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 221183165 1250 221181915 221181923
    0x20301061e0206060f0909010b030d0c062012070512010303052d09100e030318190303080c0a180e010518010f0b070510090c14030105150402030a0b0a03 67
    0x110310286048001a03412020803440c250b501c143c04108060b0f40b081c4880002e00320a075403402058644294050241c601c0420041d07050003013030b00c0d840c0020742c07140006400c00d00a0805100360a42500c0d401402d480000031003510282c1002650041445a406140c200140b841d0291500d9010565038003140001e8000f2000103c00281c1901e403025032030381100d40884040e50001d0300600c0b4040d01c9a00b40300d20200c0c03c0c040c03200001c802810718013a00304610740c0301c4060b090780d40c0d0307611525a9141c9407001d9a0b0341c5108025417203049520a4919910074142c9030705032075988850711034240c8485103030002d00500c401c1041003100b07500450b1340b44204000810b900c130718020882d4141000c00c42685040300c441aa8200782c00010400c4030320a60200e021605258050b59403040c19040c8141000480c0e0031020003541407540d0f10081050900c0d10f18215408800c1713020022444404143c00d9440036079045e4518098051141e84514040c0d000390f8204446420009243c5890300124507913000641c4151 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 221184415 1250 221183165 221183177
    0x7021615030f021611120118060501150f080406110703020a0c080307020a030b07020a170c01060b0f0909070912061b02030702090c0f040b0301090515030723060d02030106 75
    0x562801d405000e0701d8482520010154140404190f8001040d20400006060007135090b034084403d407128552004c2c0301d04400c000f8840360141b000d034503603099016141141c1c00c82c88c000000806050200800c80c08601607500c401c0d15240481702140d507000d002c2c1c07060303554580e0f42d490140c40c01d019a00410f034041c40b030740141400c040d640c1041245d0800f140d116449540080162000590b0ba01e00c11000703603039100062a5030707a120070000300c0c03511804680080c050704408086030a26440d410107450062030b071400038031400d42c135441000602d0042012a400440d002e1014400e10714241001c41e0303000400c1c0c680301c052240d583e818000064291202522502d60b5080c03241d010b00981c2c6000c001a1046000035403a01080d0303404607060b600c004003281500d9001240000705040c510048600410444070410b0300c83d6101d03008000200000c0d1079414009482450841140c20042204c4003203c108103d170f410309a801c4102c000765000d26018040d8090820080c401d44000b42d4405180a02020340d219 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 221185665 1250 221184415 221184449
    0x10209090f040c080d05090402210112140309010504030f050a02030115090501050a03080415030f11090f01111209030f010204060905120303100b1b1c09050402070807030503070216 79
    0x20400310000794004d85800c2e000007403002e544d0b0341c0080858504620030f07a4016612010290680351403140b002d01101070400c040000140d090180d81c40700e034418014004508180c40d0640c8c0e5680d24401e8103001404940180400c0010460400c12492241d000301c083e0380300c210260340040c2c04c5400c05808a0344030361045105001061152050310b000d800160392010f103040c10368950454034042e17440341c101d1801d24220707400e0030343e44280c00500800050440c18032400100c21014001c0d90040c5094a00520000030750228a6100b40794210031125844042c040c01821185201216400000d40c5505403148800c0108044002d00c018401000281d80300440795041c4010040966855030501e220f550003401031010a8031641c3c00001280c07400b11400d0799440c4a0641519001d087c4694402c6c07a001c0c241722000c200d608410a48154640c80d44d41c9214140c5803000c000403070040400250001c0d50903c410f6000030b00907001540c104803640110380700142c0d981d401c0446180c19401140440702c003406c5c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 221186915 1250 221185665 221185673
    0xd020f1008161b02040e150f01060f03090c031203020714030d1d101509020a03060810020c120315060f0d050a020405180c040b0c0604021201091e05010209090f04 71
    0x40444005803d1030861846060082614680c80118001910650382d61100e01400b940400000717600c68241c2149000503d856501e90000307402c244540e80c003081d10700c260304424500c288220301d420796015010000803800d50300e510000513408011035050581c204402c401241d84407015402400400f0000d5035205002c604102c1507031410400c14241e0910b521021003480004550120500d01c40e00f800141c040446041880d00300c111741c082c1c91410f100181001210347d041c0c02c40c4041c1e07003860301129400070000000c18124442c1154031071242c1c014105c401c6556161030001c54200c0940d03803103a09081c3c603c200040d03259000d4480d04a54036000031f01c48a1440890282d1603102c88c082004500b01442c3c40701190b248490700c40c0000a0411110009125404c080c003540c0242890304070039600c2c0e982050305207580e00e6090b1400c2c1d00c41d042c0d0300d0300d8032840301d014062000b00f107502010300c6084044a1000503c2d0111520045038203540912140c40c0c0c0b0b84412900c10b116065218940d5507504040c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 221188165 1250 221186915 221186941
    0x1060f0902161b0504051317041d0901110c030a180e0117011b0e09091b01110102071e020108061008150f030604050a1401020909060d020f1008 63
    0x22020040c1801032000c41100070200c09a00d458a40040b60411904400500b1464048298008075400341c070b80b40c14403c50a5202014482061051000e0220a031888180c0d01c024015403146000760700d019070956081c01a510055508a100440017041c03c2c905d180030101c0e16007209510182c02e500c003144c080e00681d4001410b403006494801351071006400c0101c5080c5980d01406000c202c0100f101490740d900d130095000001c4a107942003031081410394030394010044c0c14125030251007207282401068120b9170109042111206c2e40034855140d001c4d032001980c04004031850410695400c0c001c4401044840110400d440891080c011110106200140204501400c21070080ca911074040907100d400820681d00300c4104201d00312681e00342c03030000c0d59020035003504e990540120424001000070000b80414620321480c0c1241c1104030103c80306080b0701138044255800b482d4040840c020f0309000c101001740343c0c000392080215441d902c012034496040c6104502c0051000ea081141e1048102 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 221189415 1250 221188165 221188169
    0x608060a15090b0a05091314030406120e0307020111070306090b06130e06010306110c070b12061c15230106030605061c0b06090312070b06040612151d01060f 69
    0x1803c01040c581d06002c9400e030710250080c00c1c0a4040000030842040e181c210710304840d640f22170254000310340d0001840d01ca4001d44500004115110308940350340c0c0190062000907000c0c0c0c4015414182c2d05d400446400000704012421409402d070b01001280e014020b8082c01400303a0410021030500806200800c50007083c00c400351744c40c02c2030061180038040b51541c1140d40002c00450600215a0154490311400c2d040c0c0d8028421550002281d9150784064400900080d0505401356264014031115030b2112513041c102d13103074002c90703034002810b0114100fa05581c403d40000c0c0c02d4981c0441a5a4091112090890307805040d0041217915858001c000240005440302e0381044081020064031140c074050000f50581c0710030f0104203903182c2e8010746069001c01011244004030400c0b0058280d4001e032070a8920160104c0010403e0038907014100c2140d01e0481c203112050803d03110b070030425400c2d103200e07002151140010001d004000c50000426400b00d00001120b9107010042c450380041c40e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 221190665 1250 221189415 221189429
    0x1060815010305034306050711031902102d0c0203160602070203030f031e0403050406080a061512050f010b161e0b1f23040608060a15 59
    0x90030060001841c00300954844800c0001842d00e40d5200c428421106000f02000c0c0f03450a400400c0d03521040e140241803994140200c8082150340c4814604035403480c201c400600c002c1d030040104000903541900d07250642c2805205a40580d16080400d10503150590b402c0c400d0301c0d4108500b0701400320400b0041c00001c5410100b000301d4940c0c48406174803402141d400c201c14044d039000f40024800300f90111208141d005003680c0d40c1c0d6a820a51041703030b8100791000f4081d038918a402e1016801c00400c0d40e4099a01a110b041c00c00f881c00300b08940345080100300c201000d0301d4000000780420134444111004040d51240381c40c6006280000045070301c0103050180d0390501c040104030899522048980c1030300e504c0780031030010711141850400c44d6905100c01f04070f0038524403000180083d18044601948140850108034035141c0343e0b5250a0400d8020340c4016040c04c40702a64400550107000c001c090041c1c0003040c019a114403a600b040e90494801480a440b000760100d0382e1402503001c00a4125 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 221191915 1250 221190665 221190703
    0x70206040b190810060e060408030301080106060923090606120408180613030210090f30030e060d140a0b010306080d080123031603061b080c03180609010608 69
    0x10034010003880f00e05228172070500202d0140f900b403940700d103821a000340c20407074201c80d5296540d18059009000c41d108140004041a0011540020504080720444000d00f40f4458084003501041a41500070304629031054081240c40300c26200c681841e842107028000143d110041102c5600400d0055241c9602c981400c108850f8001011252182502d8041c0c2d01c2d0801e2540441c002e4803545074682160f00b528060900014500c515408015503104022502d24426900d20482c002074100644000740815112038a217402030030100040c0260480c078000c00f0030f910b070700c1c240c0c0d2621481c4191030f100749007602c410000b045560540609002040c2c000010009150117001c001c1c16a0018019001c0c01c0c17105088404c3e4440c4550700d05565a00010b0a98041c2890f1800c0e51003c400c0300c1c801100c80508100080300c040c00b1840340428480b103181c441c0c0c02c1c4c560300c0030040115540700a00b0f03505480c070340b0711030008071000c2001114451070a90b000001c00904001c02145010f400d06903003203413014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 221193165 1250 221191915 221191921
    0x90801090b06090112020d11040216050a1a040302100c09050a0602071406090d030c0303020d110307030f0c141303170409060801050103022808030d0207030e1c1205070206040b1908 79
    0x190760030030a030103d42001942303242001c1e070000070f000392107441121140581980e40c4c01c0c0622070003041e092804c6105213001403042d108480c084201410468003d4050780103440410140c4d0950303040b20351070600d02d146c40160161500005200d10b0070b0b6401950069000ca1400d024460096072912200b590071110141499502030000b241401a200d004003040403159543c010180260151440150148002d000344040d100390990250401c940c00310000b410001000c2054410b40701d80b01102d05544e8aa0200b50701365807803051654044250510a520120400008141035000040106041058041c1d80e00d1a0541d0402620119000700d1303840c0e4540001000180e40b000d007100300c0d01c110499103055440800140c050035039001e600854482c04001210b00b469400340e030007810704030b1181d1103441c0c0d0b1341500b6052100f5000c40d2000c60031084400078170340f4086003980600d9aa0300e5450701e8141d25144840c0c3c0420b0ba00d0300554000c2d0b5400b18003045030030036942824564404400a403602c0c807050300d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 221194415 1250 221193165 221193169
    0x601120b16090e010e160801060206130807060203090136020f03101a120c06090d08040b0c0307121b0206030a020d090b1b0f03070f090801090b0609011202 68
    0x44007520000c1c20821000c88506014050007041d0b00410010204103c2c0d5179565280f04400141101c040201c20071480650f85068000e00189041c2d901070b81c010240f40e9185a40e10920301c11050b02910740d0300041c060b540000e02c55000540c41a108040046601c10501c4407482c7c8101c18050310007a10410b2406400181c8412408614001c0d01102e500036401c02e200046424055a11407014000d42000964040c1c01085c03419142d91060030358540c0030858410801c2502c401e55101c240345c1c803100407c0710180d10b151038030380b0b40d840b540690861440e281d684e189045007940314400c3d101c00760708013243da04248150301403030000301e03400d6003098440d1100844400c655540d06841c0284a010080081400d51109a040e40c005400012040180a01074140310588000c104d0f240202405101c1a07655103480b11815619940d9103448250308503101c95409540c98146000b400081101103000081d5070742c02405070680b400c0c0a04158900d0703080c501305001d81013905821040c440f0000c0f04d982d038016 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 221195665 1250 221194415 221194433
    0x7110a05012d050c010c030b011d0105030408030402061204031e0e090703110c0304061806090302060a0327060218060901090e0c160b09010f0b280911040602060112 72
    0x10b01c2080000e015240450aa441d40100144005158a0140310442458140d4800805c04109880d800044010000034070145c541181c541c9000800038404500041c039900061600302e44010325943c1412503000343c000341c001d000c0320180c00003410f9203c0c2c109251141000c1e0703d83d2180a203442c1c002414030f2004165141005001042059a21001604814144810f41d034402100c42c0950740d4a580d00c100007031440b0708070b42c0141150103000000040c0203003e00d4025040f2540500040d04001442d0700940007000103070340d1003c1c00540012000c0880c191820b008104602c2200c0050b21440d54100c0c00103022190041d40780200d01c20020401640e0b040901802100c1c2c3c0c000e601c4d00960340c0d410f10300c45d0f28065a0004071000603071213914005c004074094450307c01d400c800004c025a00c164000d4a050303a01018400c0d030801058407420070880c03406503100014000a83c1500c2c01e0990340c40a60040b60311000c074181c115000810f0034041c00e54144101c41c0140980410f284248041e51241580c0b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 221196915 1250 221195665 221195717
    0x14040317040501060801020d0b0301060b09150f12040609150603020a090c02031210030510020301050f06090f030a0507060e060702030601060e010918060608010608150111011107110a0501 82
    0x3440c44820002820070009421883c00340180ca4001d544500d5200c0001001c0c103842041640300c0c4d400c045010404010502c19150403600083c400e4000b4605201202070542c48240c0c8018a400100b160745442d01c080d040c503d0103284a03100c005034000690610280e501e400840d681c03c2d05040050800c05a5107080c1808103617100c1c4030000404a103034401c140d00e907124414440342e4400d0070004011503503207103c4090b800c481c000e0007075802980c0300307030140700482c4424003a065010504038444080360a01c10040c000011001c0d1501141800144c0020f00e8819090002c6503552320403d0184080c81d030158411010080c1a10941c0c00c1c91004d0f030009031102014019101003014043c0c00000b240e00c2200504000c12030141e00c0c800e640c8010700c102c800350665020355400308011500000305903100e50b001da4843c005003103034249020340c1000112820f2036142500480e0750f4031682400300701c030080001015081e10404820f96002804002e2090303013410355100d14103019005c0c6000703000355040007444c21 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 221198165 1250 221196915 221196947
    0x170105040308010510030906150e091f180f0c052b060e011e090b2206150f080c0a060807020a060b031203040b0f10060203070b0402130519140403 64
    0x403085051070040f8010a04c401f0087c0082d810040791000c802410341008003a2036034041e082066035030300d40d4025960f0024030343d01c4440c0d544000e440103560030303c2e500030132482d00e5a011091228072180ca601032104815001602c88048003003003007040e071609016101c07008000c00240c1c0c843e0800c6043e04011401c155038080d0070300c2c0c0c440c4c0040c8843d0a00798041c3e104503c403640e0356102d40d0030188400c0020b00c1b052208544500d158408520300f40c20419001c40d41130494404982c0358112a9600c07000303024401c14903041742601660101f0840781e1913400c80040c103100c50003400100303171000c02c0022600090f4095000d00941d034081c020300d2540400c50b0300440d50440b0020804411480119241c50001901e40e010500040b00384010083c46030132181c068080d100740700324181c4404074030202c08007a0f80304000142c1e10410484000a80181155500c507000501407040150520070590039180101c4070003800c2c09070300403501151109807090030b0500e03200e52142c06032843c0c80da501900308241d414140c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 221199415 1250 221198165 221198179
    0x605010216170307020301020a05070b280e0c03010c050d32090f0a1505063012070803100e040f0206031510030c200c0609030a0b04030503011701050403080105 70
    0x10b03401c1c60400c2141c68060b405402103580d00d26000b4024441d4204050850780380c0722241c08625074121440c1d0b05a5142c08020808401c40c40c0c00c1c101c0b1000f0304082000701e4080c0140c940b16103565500384035801a8082c00d0302ca2942d1100da10b03d42c85c0890320b40070400d500340e0002d41101182021642503400c901c03070101d440c1010a0701c80441365840c0520391041860680b140014000c10054500d6001c5aa00100712046c807031500c8880422010513082c50041201c22440c0d041c05c6e4142180b486000c1403c0700f61003d1300c034501c2c2944400c41c85507210b048203480d101d00007c14004108400e4039800300400517941c2e5044607060585d91030090100d8150003910440000c0041030780324075000030004102d2070080c000301101c600784201802400c0c40b080d0000124200c2c07441400382c00c040003140c05070841014054104000c502d03042002d0350f04aa00b403d50184203c410013800100c07a990364500a90080c0c132069120b43c5400b5844400ba0704072001d0f06482d0b4148402d03c000260400501419188215a01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 221200665 1250 221199415 221199449
    0x8190804080d090f060e151b03040b0a20030904090213090507090e010e0c1e09010b040918021008070315030b0412030b0a170a14060a0605010216 64
    0x1004980515004806103008070b03038014100c19040281c007802c840034029551506a41c4842c1600c41d52140140c0c140c0001240ca05000b10315183c00003844418407000103d01c2d181c0d00b00f526a0700c2c581098100e143c42000004e14042820303008641d542c0385401d100c1d540c9140c1040070181585a00030b000b100ca00a40d1103580b40d02c115694164441031560131940200040c40a0381000c6030f0300c40d1144241c004036441c046000d00e2846060207488000403890009242d940040c2050008200440d40d13041780500c2c0301080c4005a5070307055201d07402000081a400d8a42c1c0c03c0c04095821600f1130b6440403016401d6985401c0180c0b1410014107001219080000381c903a60110194090040020110b0010340d1448010041011244e1003900841c043d4400c5c0350401c1d41c0b21020380440d5030381000c1690040e80344604003c07492910100c0c0ca200b440300c078143e840c00006503442c00d48444080f081c0c29556042081002201360b0588078440003013509100030200703071034841c0d11180300704418000c20801e00368200748 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 221201915 1250 221200665 221200673
    0x7030f0b07140a0e0111120405060c011d0a05010c051207050313021027050a030222021b0c0d080307110a0803040809090a0b030c0603040203010b18011e0819 69
    0x3002a1482c403104155110116a001042903804001d00303400b042c0d501601e041007400000e00d000481860601151070242854100206600900340c00c001c19902c481c40c50040e08103800e138100300c051060005000c100d405190203070070340b2441c00030041046010312142c4010740080380426005401820055601e498500c944a015403004d040a501f0240703181c515511a40d11403c16403500094003e0310b40010031707003030342c0940f828210b2103841e0740201d8000d41800036141c00451040060f1010b010f00c0b01985d5403850400a071b810000301c0c48017007900a80010f200c080306000c1140903000450b402c20900f10300703503100340c05c40c00b001d0428400c00482440c802c401070010882c00c2500f44d00154025164606860703c00450745c80150303403a026242c00d90224002800b640216060340e40000e0241040c00012010f020290300010030503641036480310764080f01a01d0b0644a410b10302ea4105c5000215814001c4203c0440210500c41c1e8040c80c4901c001c000ca128045200d107080d48108110100340306040c20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 221203165 1250 221201915 221201927
    0x605030136020f0d140f030d0b04060828060f020310060203070507090507050702120d020106270507030219020703050118110d0201030908160c0e040807150615020114010807030f0b07 80
    0xc5c086020f4070500004900c043d000001825243d5415981403280342c40e183d0610050303074902d10600480754010758400f07003000c2075030010300300c0ca014090b98000c00d42155166001907444085010035010303400818000300c0d4403145490805880c80740002d40c5004000c1d5110795849030f441c8943e4440d6980c1c0d1011400040c89242100d00035034000b0081400c10340300b244503d07195501e1032290f501641c64194000354003865824901d00c441c4551030303490020b400d004886005820020074090806a0800c00007200303401d00c4520044100d020780c001e20059040d841c0035400c5400808541d80e00982e8034030004001507000001042d048010f6070f41c5a00d40003a031006801412034000001d2000c02e01040103c40c054006400c46400c1d4010700c0840d604507924a10b4004103501541c000d40081800c000c04000700d107018540038500032004500081860b6200701050244160a082c507005075110b0343d0f40031211841803aa240540454009001c0151450351341c03821140840e03c1c003c2c80019210001090b1600070742c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 221204415 1250 221203165 221203193
    0xc05220801020a0203030108070f0b0307030c020c0612100b0f07230303040506100609030803010e060a0e01081605120c0907020102040302041b030e070e06040b040605030136020f0d 79
    0xc00940d100c80101e8006504c940090003050601d00c41d80381c00107031144d803c19000f0300316000d07503083c41c0c074546521400f10050089002e41c2d605600c00c80340c5090103512804000c0001c42c0d80032041440c1400e10903881d4241325220380c0401444801403141c4514a0441012610002d500c03407422880e14a9401603001c4029613070b640065980004402c10041c001d001c43d80a00c2011005e000341882c0b51585070030b94440a450001801c13500d801c0c00140240301281d800c1d5900508004e08054920307a031507c0403600300a090304040308a0304162441440785080c03044101c00303020111403601c800403c40462135907400803440c4480c4103210780c60204812600079030441d000b964001d80148010211100341c03d0600d1007201d10701c400a803901c0c00e00c4401c0710000c660030007940d007000c0d01f0000544400c030410000c0e08a071003046900c150340e210300244a503001d21070491035040c82005445002c0c02c14100a03040c032085000b03410b07808265a80340005984080640c040b01c03200310791103070f8068039508280c1c203111002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 221205665 1250 221204415 221204429
    0xc030506060d02210c04060206090307030e04050711010f0b040b1c111f021f05040308040b1e0907150504080a020d1110020105090c0a03020a1518030c050f040c0522 72
    0x141400a80ea1385c10300244140c400c01c0d000c6861548440e003405a0b41d1240110142c001000300030f0004041c50141c020320b400190600d8210a40013410400c10f0850b0103450f2003500c070a0791000c030201d25040c20b01401110a00c2141d09881d0b954013424052050241e00100410101d40340c0c0650880b60756054000448810b024030052107405100c00207544c40051000007074140008101c0c82c12814928010984665419074900d4190f4540707541d4141020030140002c1c820006c6a02c203940559054039502d0310840b1144028000b45151010001c10302c00c1150491040140170401407065010002d2040d040c9513065440c80d284909504001c0c00b2001c0d5001120383c089441a81108801d505412071406103004070107079482a5612001c00603881414480203420144c841e0003002001644142c101d440f5034281400380e154180100880402446a04200c44c1c800422901340400c0c140040ba80400f42002d40e020020301902c9040035145001e20705048801308011049241c1046414080d90028580 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 221206915 1250 221205665 221205727
    0x1080f070c080f03041e0510110913090b0106030203010e0f060103061a0a1815110c0409081b1615020a0b070c06050a050411120a050319030c030506060d02 68
    0x118025003140358404d417401d03508424031240d001d1030740040100804030b030380e8840002d0244101c11031820001d05956480c22508203818001070089840d21041c540d21191003400000e0708803101d151440030b40ca01a0840000c0520620050064407030031a00c60f500190b01c03a00c0d0004558403200100c01030140c44d08011805403845c102240f02c50310bc1c0c2d000e062244070319140e18114a20052856290082c05d1044601c00c11444060308440c80c014141c220843e0010010b5520070703240344000c1806e4540c08801240c1e40c0d403000030300714540c01d10121541c0743d10302c50501400c1c0c40c405c035030700ca0040141d040c010343d09a80071120700d0030311060081221000f40ca0b48000c43c141207241003e0080c0000e81c3e81c10f4107461460400000841c6040b041c40fa442c843d503481341491100021071000d101c03009507619080c203075074442d900144011410405c0a403d01d090340030a03403072681d98044001816140325540480c01c0c075040c041400704981e200030030349415100c100401611000701c0709070000110381c0801d010301c151300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 221208165 1250 221206915 221206927
    0x4032003070b06091303020c060d090609030504180b030606060a11070905090d0203090a0e041505131101030b090c22090218030303040b010b071505180105070c0201080f070c08 77
    0xc400c01c0400d00c0303243c0c2240c022220340c3d540564400d07a084080401070040c0c01c10104100a46029000391003601d12048002400c00c904e96151400c80c0c095280640104d42c000c14108240b180c0b00f14415103101043c00240003284007040800d690310030140030302c2e00c5200c010910400301881400910b5040d8043c0b002c503100565a5000b4100414058a4101c40da02404800748122400001114424070f4080c3c10554114903041e0001c00d80346015104950800d51000043d81e411101d01649010300f4002c120110700c450189407101c031030300c0c2d0300c00700e01d061604009404d15030356107514403a44d000201200c1282d5910b08074420003100324420940b02d90440d810300d404107541407142e0242410410703030f00c00310000245000c205980c0f404202c4e002889640b4140c01803080b40ca000340589020b602c1344040104105440084105581084031503444c0d84100b8203440000308424050b0b150001c91070b01300808402c000d80c0009102001c0240100c4201c03140d040440c0c2c0003441030780d813244a030f5007000001c2e48402e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 221209415 1250 221208165 221208173
    0x9060c0c02030d0f05040b0d0b0d0b10170d080705220305010501090b13090201020a2316060e0603090705030a080705010c05090117060a090204080c090108150403200307 74
    0x1800c90005034060300c2030103011000e07a80608440d02031a91552500b90802d4540070f040d040c80c1d480b030081060070588a032002852500c07200c4484450500c80c0c16246900d207024a00d0183c0030440b540b001c103074614001e0580d100104085482d054803801d9150480642e6a2480151010b00c581c05c0c803000110701805c0c03150b0011942e641c001d01500d114000038400d6036a1030200c14180c40603540c103694440d1425200038600000d070b40c0b03c0c0c0c4500344180142d42c84611203443d03130410000d81d880c0d41c1e50b001000350364212104c18184443c4a2109400c00901119800d00e00d0050415400c4620140240d80000200390454410462000189401021218841d13000e10301800c05421111044030b09600780040c072401d407070044050341d0a50344180d55092803010701c111007a02141c4082c000c0394004030744020104a1b00032a0000384080e00c07400300142808500030081c8040f004059104005540005a0703004c0d416548010440e00a0f4252601070000c5903000e6900e088840100f126104501c00024207900700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 221210665 1250 221209415 221209427
    0x2205030303101d0105030c06071a0a0207020f030d0e010c0501090605090a1214120a1d0115090213140315040303061401110d081512010e010c11030f0d09060c 69
    0xf503100380040c10300c10f0110031000240301e4001e00509034140c0200c0c215501604014016000c07040c0107408416402c92030242042440c50151091184560001010b20650401280c1100703d801c0940080c6800300d81d101c001004074646000050400c202060008148142504520700442c0c01038400c04c80c0313040140800f9503500f50305200715000c81805290b40b2280d4012202d200c4d609038040c50461070601c55000092494800800c40c4454a80e80c01c1c17401244540300404100040584000041c8030100e8414a40516859445080101c0c0104000f9401d21101000e01040f03815940f0341e11101d031200c600081c00e112580d684103103800060002c000c20305078503401c130300c1c00c4554100c00040b809a80d0001180c1c40e40d0307003140c0d46507248d00504000c10707041e22449100b03a0000c14135180b0b001c2c403c0f403000001c18400c800042003455a4469900300d00301842803045030318a1015090200818481c81030031516400b6000103940d55410119180022480030740003800341d40e0b0300160400048001000c003403c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 221211915 1250 221210665 221210669
    0x905060a0e091615020a1106070f0507170f0309040b030102040e04260315010c02370807030203070314070b16030f050a0c260301030302030d0b1005220503030310 71
    0x74403d60350000541045900080346007504179405410902c00903103403041c030901c50000130b0380c00490030800100498001081201c1440c42100544001e078649181d02c2644420280104040d81000c07030100440c001c000120341c0b504205031004a58440798000190090145603c9a02d11007110300820041020f10140f0307000710080c840d900c400784810000038202c603020854680400407200074118a5070344c01600c820816a01c0100990321144403ca00100c0c026026505801e02d821000b0001e04600d100c41145d0014110010042480524540000769100200d00c4007030544400130424005001c42071003804050700f00c0d010395a0341c880b01e81d00d06040c0481001d60680024025104503650148034204907110500d0603540c0101c080c1503a2204400b0241c20f41203050a6900c0004407240480b42c50081c5001b14000c1c1c001e5912510207a1061098807070f900d1030944a51f06d8100c101400e190410300b030f58000c401c401c1d10203640c3c00c0742041e03185d000399464010035454407000c01004100090300701581c003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 221213165 1250 221211915 221211943
    0x61305010c0c0c0303180902040b09040b0906010507080f0405031209090618060f030a23060f06010903030503091f05090c150a0c020105210402090603160905060a0e09 73
    0x8841401c18004440145420200820701c10b4020b0040010a22a01e814511801d1041b0080c0089075540d64100881e070150b0300240141001007007461072031406109042c4580d106440120861504400003800c900c01c1003002402140007180a1640483e400203940113454098111601644103026042403030704003510383c0b03104041e210006001c5052400b000c08000c28030000a058a840d2802007042c00620340341c0c00c64140c4101c107150404108280015411010304503801681c441f6803100443c201a00103049807640700e6030005000040c2d900c451200c040700d82516101d5102e443d100f440504000400f035414400c4a0301c0b6200450036038507a0b1000c1c0c052a150300840e8040c10181d018400720409104000300e4213441031000101050003200382c10b08552052401c1480c001c1e48030322208840c80c92100c8885200b09000c100021410002c81039038002c8000c400a016014029018062030480e5010b002c80042d200c5011a0050319a0f41110020380003800c646000e515041d00116501c0d841d00000135 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 221214415 1250 221213165 221213171
    0x801060602100f0c0206071412042901061413080a051c03060303020703060b010c1509051e0c1009090e030309010b010504051003020a0c06020c01020c0f0c0a1205010e06130501 77
    0x841000d2261107844c2448120340c028101542e0380e03c800344c0e0614240c5e0031822a00200700300c100102c42c0700303a450b54401e9210724010b6840606143d641108469003140203c5545500001400300c590404030b803001c40008e40c040c00e60b036800c8112140380b01f4038150707101c0f038200d10030f81441c0380801001140c0b1181000f00750041d01b80c00092924103c094812510002e000b60308032480c140301145150300044445903041c10100310307074042641c65411858402c044900342903542c4081d0030401906000030000c50608881001c0d800d203410411a895a0542c52080d00c181400095a0009070040540d40300034000c18000b04168540742c9085a103a038021601c07050b03694a4000007054a40c01401a6000d90700e02038808201074441d01c1c410340080d0f122400082c2805102122400043d000c4e00040410a9084001603201c2c0c1e0001c440764a8031240b020020003940002040d4440c1c0c2d160300700400300301c500140f0049900300d00780c10010f00400701c10038816080e010ba681084000702400c111400b64074441c000070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 221215665 1250 221214415 221214431
    0x706020913180311011e0906150303050703080705090f0f0301090503030a060e0f040803010608090c1c0204050a060b03060f0d080301080d080f0106020c0607110306090d030b030307021c0c080106060210 88
    0x7007070884441d14a401c1e02c9480f4120b0a034000344440c7d025404a62081c3c2c4e0006207642c4452840e2104a107552040f80090000542c90081542c0a01d5480e044002420007030304045e03242c4001009a00c1204040c0c0c0070b030204a00c01e1a0b80d580941040b046183c2200c10380c1e85d20300700004420041c02e0640266500150400b000ca082c0b41480c00c8264401c0b500400d405085900b450f400300c0d134056000e0444001449880c41ca40e07a6a030300e080703075520710358440000c00c581c0058510500c000d41d00300408000119103807581c00c000c8000380300300301d0394020400c0700e0301c03400520743c0d40004581c0710203a04044c10381c040100c00424802800200d882103581145c82d06030340769035002c41c0311008034024011000103070003600241c001c600348103000d040c607a446200141605061900403d00c2c0080840e0b800301d5982c0036001801070a80c0600c40c400032614264042d6141c0886034000c501d8029090524001804540e9520b2041c0103400300c0b1074001e4026440240410ba0780c802d4001d40d640d007410b01e00c080a91400c0306d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 221216915 1250 221215665 221215697
    0x506070303143c0a0203090f0718050f150f010c0b010b0901020618070303030504020a180c0e060909040818030a0c08120304020906010c061b031d03030c07060209131803 74
    0xc1081000300100d141800741c4c3c0c4102ca420080d410291200200e4071800d6080e031400c90003402a40040c290803841841c4078004404048160b420180c001c6151803012014040d60384d071080d9600c5d84106050f15520f151100c107c0040301c02c0400b402001d8082105500017084042c004030007054511400d0782152816211204400c8541040c401c0c895865400030400f080003074069040300b41c1c054002440c900400d66036210729992440409035440c0d116a03181c610302115070300511010356048041c1d034014206080702010400d69180038001a149000201d00c0c000c450761082402910840d0150a440428882c0d261032002c4c000c031401801d40d14000c141c45125903041c91400e036441990020a1031700765854800c010b50b0803880d10b100c19600d0503180c400d0b001c2d01a92079104040e10b8403e03030784c0004014080c03842d40107080031150511030b004d41007041489001401c02045d90340c91a0030210050351205400300060500060038554006941003070701034108d100c84400600400c500039212a03005081c0724903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 221218165 1250 221216915 221217001
    0x40e0f010b0315150f09090102130b0a050a03020f090d030804110906130209010e040e0a030e060304050303071b0c151106060307060e042703020709020c030301050607030314 76
    0x9000c3c0b035a1a0002d00242d402d1140515425500a016240d000112000c8020801000c41290258200da40000312498003468502d603980041044001c286c0c01d0500d00000100140700b002050320406401042c40c401c0708400341d04030f03480d100e00205030720441c480c640b8000d007071340300104e4040d20612008000d5446038140504c045105040041c03110081e12901c04400000b5004650603a041210704002c0c6161a2294031403004601d88100c010031030311150f03280c0180a001801000742c000c03241030050000040d00001034a401000c1401c040b081c3c1c4142103100341e40303160300c0f007400703000d80a10100000d0300c00b905c012000380f60500b954500580601101e0310a81e10401619020340651000e03c040200318444c0081622000c3c0040010a1103040c0c1d00b1240b000c000c482d602e0b00710b0301324422032203030800d50100452401040c05030002c0d4286914001100d45900052043d18020600054003004045c07207a40000d2000003040900706a030304000c41ca1110003100210703010301d02001e002251580404000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 221219415 1250 221218165 221218183
    0x1027030309030308070203070b091b01021f05191b120903020a0b0c120a05070f0903030c120512090a11040b06031b0f040b090102191110020c040e0f010b03 68
    0x740314100500d1a5940c02c40e40070340e009000000710f00050200e00001203e42c0342d12406054004010056808c0c41d0540b5a4054200061241598014061185900128041104000702211001805075a00309101c1400080d041001b05014170b8800b090240c003680d00070401c0003030300f40d0791130444c4c0050401e049800c80e001140054003503806405d0340f900040c4491409c552003551034410340e0400c0c51811250a08107000d49603600030703d4403070040100407541700d0740ca245a50b890b4a0300441242c9540c0f0040c200c0e152400d0301802d0302c000000c1000c401c034001c00444282d070a83d03065503041850100d40390f645030503200d14111040c0251100d564110324240c02800350303055000340350300d240d91503000c4e84031b444202072843d0601401e002c0c448526500000c202900082c842c1d048031641d6801040002410f200c120409005100d0b2883c035201c1c0800e40f40995400104c00a4840d68a80168040140d21341000303e6103c075801400e0400d81000d1610210700014a1030803a0000e010001c0d8000802d07071640d00782 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 221220665 1250 221219415 221219417
    0xe0a080a1404052206050402070809030c040209060703050c0a0c060807020606030d0e2101090305040603060b0f0f0918070f1d030c010c03050f030f0103050c030c060a0309030e10270303 81
    0x722164524203204485a001c07a01c131200000a034150b920f90214059820101c2c0542d075080d408680c403151401c0030b0000e0f6069060480d400c5280c095071000040440c05610006001c01c03d011035501c6291104200003022650851401440d0594480c0c0c001c2040004a07014401406103c1c003003051400c4c0003411101b15040b50b241e158803034910005011b074602c008040f0407000c55542d551588080320a00c1940100c50082d51410740e6181032503801340583d070503688050038125007000094080c5500000341c5074041c0440100d87d40d644400c00001d6880c40f440c1400001c90016801402002034008003011148019500d4042da18084041c1c01032042e00c042c12220341540210b03012203c04d43c400c403200c9400d14407908002d13050030317a511201c0215401c21500550342502c00c0d0014810b21404001080700d8107422401003903280c1c103010115205004025450013495103c0380307504101070007554010207483e0301a04618000c41c0640b0b00400d403190703400310340000c14111010f0700c94446203601034070107483d09 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 221221915 1250 221220665 221220679
    0x105040c05100e0a06020f0609030f03061011070803030108010c02070f15050c010c09030c08010227030c032b0f050304030f140c0706080c180d03030e0a080a140405 72
    0x9031a061020040e59030500c20200010700f90408007590381c0c0300740f64001e0040c035801888085031680300b45141a00241c4a4003003907100b07103c2c1520401c03102080781c0c4e120700140c504003081403545a045d20202c0c000c4805050600542d2004203d665000000e0b50407242e003800240003841c0c0c614000c0e6111005402080203800040c3e00c140414894041001c1d4a83c14502d001c9103040350f28a00305003100c10b210b2146d00000c2d040e030000c00c1440314041c20480a841070304000c500d444410764411420381e014140344400103035100c104901580d030911203075141e42009016112007130b280d500038800e04a42e244000c0040e13032080015091107482a400344c000a43c19031a42c0d41f6507101c0307480c16900c44450a0310581000482075520350110b52034409041c004150100030059a41030040186c03450704001d05407488480180049200d01300d000c09062001c800948030580014640c1c10100c020303142e1815407622510880041e1400c2020450003031504c0310b05596050641014a22240072502c41d5105582e0f2250b9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 221223021 1106 221221915 221221919
    0xa0f05070e07020d0e0f030706091d060607080d02070c0605070308070302190e0402120c03090c0301061203080604090209011205060c070f1205040f0e0115020105040c 73
    0x1e024404214984a03400079502c0000c049850204120910050f19507140c098030740ca242c04e40501a44c078810b1311420b0142280b013541c880c1028a0308100c8408205075204040e460194000818507443c2c0400f42d1a580d209400101c2c030280c0b100c0d420000280003d010f070409400603d101e0f1181901d0300340c9401e000c1c14070080280780b0300034075004000d420300e00e04110030342240c90005410400ca43c004800d0108000b1b004989200030380502c00300c24456a402908042c40c032995440702160001c3d0000418182643d4a034800c050b000d940c00c15134280000d0049035015400540078000207940072890b0001400c4080030390110050040901e030304003d0120910820b58418a0131100c140741512680e40c4518603010386c2d801030310b40d0f5004450348204501ca4800c96000b400d406c0b859109440e00d0300040c084580d028414042c80c01c8440c5441070201c1d0041c010700d4402c0380c0000161491138 = true := by decide +kernel

theorem cover : BRFrame.Cov 221043165 221223021 := by
  have h0 := BRFrame.cov_init 221043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 221043165 ≤ n) (h2 : n < 221223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
