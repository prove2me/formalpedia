-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0163
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:12:28.815686+00:00
-- url     : https://prove2.me/submissions/9976c333-b8ff-4dc4-83e6-5e009dd6622e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 29136696 ≤ n < 29316552 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 29137946 1250 29136696 29136707
    0x9050c01030e0c090609103b06030703110111010204030b010807050d11010f030b1207050a060f0210110903060a0c03050f010303050703030f0204080708160b0c0d0e010306031203020d110405150d0e0706 88
    0x5844c8d204100302c1c1d444a000c000c1803620140c4607542c1561056008002080490740c002a40c0c84052610388020f26446c411ba5007640c0040d00306a441204120041100079000c100b200020705090710f00e4229134005440c1c02d1150a142102e4078180030582d01c454a20318400d600c240400d40f8020102c507096040521407640d1002513003e1a0701440c5101030200f80c0d54040c0c17036104001d00c01a03000f0071749414101c12403001741800112003450751009100411050350709000a9114008402002410040c82035004003901d001401f401441240b560051000c17030307441800c86160b2a0141008140c0780078221554009101e6684007c02038000d017100807031416400303e5240400d442401100310417688503030308541d0b03901c510914103034640e00087d251201280207609a80700c65105050000d2070070b0780c039181c0401d01078a1052000000c0e900240c802c4a0074254480d00320307003e9461080505103070404010512008401e80c040d401a040480c401040380e00682140700c0404034032083d2210350390b65800c06000e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 29139196 1250 29137946 29138009
    0x12050306040902130b030c060f090d0503090918010b0d02131a100903050c100c03110106081501050112090507050d0501020409020c03071509020a03120e0409050c01030e0c09060910 79
    0x1b190041000a0319149819010746800004880106241c0110b54003040125030502c00211014001402209500e0f07848080151040065001c0202c015413540d00040c2100c00d2000300310311070f04840c580040542ca805a44564509000200050b260702e004617004c9c103183c451000c035503c04d4090f05004030080d0320000a1003220b10030000c0340d140714034031000c10080c0c800e82500003001410000c0e4071b8020034400e500c1a03d61401007400029400d8540101c9030030101a0710200f40c5103014400104500d5a1140c03d4551524045030200305110203a99181c1c1c540c0164861a4031684942500409000c02981120001c02c041c002c115501c10103030b400d554582d004010203956181d030700b100c0d803010030101e4011410220f600821444e10f150070b665030b10000c1e000803400301042194030b0071030441c03513151b512541d55081d0240000740380412414000600780e0300301c0310108406420105071290951110a0080e400001c00c6480030b407940d94080c90403038103d00c640e00032000c80348552180341d00942154070980 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 29140446 1250 29139196 29139199
    0x40b1302121606080105030a030f0c0c0f0311060c10021e031026030405040203070c1b08060907120206070204020f0a030209030d170f0702010b03070303200a12050306040902130b 78
    0x100040c0c0c3d9084151280c0310244907440d015005030130b0000029110301ca020745554410700b41980c0d60b01003503c031030814003000d8000e0403807400124828000e10484640b81c11442c9030880707080c0c1c909881800e03c95110754044045074065500481c0c9440c500402180c0c0000c1d0030070359a084d9490f07140001c1d003600d45200b284111907031000244a00105880050f54159025028000a62400d8603207000d2100a44c00240004100309045004c51300007080d4400c00d01d0500c48440a061003a0705101c107090a142c40680921070540c03240b02c0800000d000249500036194044450644a001034000f0802034824002403000800d0005004044282c03d40d02822514005504480c0340d1079200da41900c0540101e00b9825050b00c507040021610342038820825448000b51001080440800c00070901e041001d4000310045640c002c4082906014040b8010500400000500c3d020340b1030307242c0701403801011110000700f0400000003802e41d1155004102090750182c861840c0c0064100c0c103c00804d010328140303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 29141696 1250 29140446 29140483
    0x308010504060f06020d300504060f051317041e060909020301031e050106030803090d021b061e04050a0b0702040c02070b090d050a0510090c06110303040b130212 71
    0x80b980d9100019100184c41c00d0b900200301d01120440c013511030142088030b03001412103208004509514075201c8042d00c00c507008010483d4107003490030409440d9082c88501449180108210748240d031200c3c540a080d8000401030340656040945080c00e11464001000c203140c40703c3c403100400c02915145084a2481d91980411a11401c14506a02c020310005d0400700c860110103103052440c0a1754400140b2030400007560303c0e40d039a2143c041e50411201051f440d040601c1e40102d80c0c1e010320100c400d959940c2080040b1100c12000541d00b4010301e028800500e00314116100c00c1c40301c050803940074040c01040101132175035900c54038080d41e01034007049020b2070815840c403004500004010b002d446d1100401402c00d4011418000900308502d010380d070300c1c8070341160342d00801d00920007800e290082c041c000c60045124141000713420210382c406010805032815610f860b40000c0b040e03a40150344080b441ea20340d01e6201c0d1b100b16070082080040d50102d0030807c00c281003200000d05c042c0d100c905c032040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 29142946 1250 29141696 29141699
    0x303090b0f0306010305060402070c0b03011d01080a080318011406010311090306060402250804030501050601050a050306040c110d03050f06011b020f0109030b01090203040501050606210402030309030a030801050406 94
    0x910501d01a410400a280d6010b0000c12142c0d8080d41125a000704050001420703e10143c440c80310184556010000d81d540020041c4200002429400c6004009aa0003a620751400d111f4950350604040007500c2d459002c00070850030303c088490490807c1d68903000340007030410326000113181c540039290103001c02e19004044c0a2204c0d6901910311408006000c0c0c0302e0360b9201c2c8140000b80d40144100840c0444c02a880b494002400701250001130064965a86840c03e610340345003100d034040c1c0f04a061100074818108030984c454102caa0028080e40c0c04a00384012000a80b007040000c01908440e024164034a0502945540702d948242d03603a000c0d11410351605c02c0191001c0100c5c0351042e0400b202e2003803040260504100302c2d45000010700d8080303c2c40e90f49803640d011140c401e1304078500143d000024003003404004d005598025004030b0b5154a0300f80d900b04410351074509003e000c0014424038001806550703046c425141d403100054150350740000d881c580200080350074003c10f44500d03d030510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 29144196 1250 29142946 29142959
    0xb09100e0609070e090c1c0203090f030f03011205030910020a1a0105010c0609110a031a090303070903020904260c0105090703020a030b0901020f040306060501030b09091e0f03040f030309 82
    0x9141c0110080d45813100307148842c000303110841d070008280070a241c9040101408803c41d17214001440402044016100e04000080e00e0070085600701d0300c02d03c2e508c28003c034018038407260704030390440d90b09200703203030f20a0424a0514158050210090f03400003240f0707001000b00e900400c048011611980903a94038110f002c5d02800740440c28000c0d10700280c142d2410308001601940820000d2b4000e0b1018111500b4a0303000842c2448107030804c64000305103200f0700c0311040d0404001c23a000600b03100a9803c51070300180050003c4030074880a0f110b0541100450240726400d006010b402c4c500c0000c00d4440c07400200300f413801340e100c0d818010256182c13500080056001060840c1a030380d00410442040703195842c0c5000b0801c0c00740a00d86c40e95030801c00259070b041c4060040000f540308800110f080d0740390100240480e0081d5090714000c042400402c4021070020035039051200c00039441030083c03004136040500d80009064aa415403000050100e904104409280220fa200b941e4280600d6228034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 29145446 1250 29144196 29144209
    0x40b0a0c050418090b15120303070e0105070f050106030b060f030102120c130f0303020a1101020d0e190306050103050c0a0501050703050d05040f02030a1506120201210b09100e06 78
    0x2548000144040c0818000801d10f80010724116000c0036000c40c06802c00e4561228070401a11881c0704410104146002c5050094045080300b80c11009181103190558010b45405050340c0c10038104480080d02c40c4c10480320030343e02c81116070004020814151246008803100c01c0a0303991901c50580f03106441410300d81402200d480040c920703847c00450701d551400f10400e4001c0e40815a85042210f80420307000c6000c4580c600550007640180751200d218104204540e400c110b02c1030442d0002c4130310903130403900040790303104840040d50180010f40410303419403488001a0070080c500f500b410b00000c24004005a83e0741e13201030443e80d00400c0e5540c1c2c00155068031461900401040702404680c0d111364496005540c054010100c2003020021a0700003810000603c40445807040a44070507a20071445104500103002e803c94014402582ca030000b034684540e0310034604c4141444226400072503880c4d080402030f45400b0380a2402c1d420400b0040c44454003d0040004c40c900ca000001c00c9450f040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 29146696 1250 29145446 29145461
    0x1030608240417030a0915060506091011070b0c010b0105030f01090905031b03030708070504050109231908190f030e12030c0705030618120d061805040b0a 68
    0x40c50070300d103100007114504582a000420680e6007603c01807000100401510080d4402e981113440000c089645142900b40303035031280c040050f403526083e424842c0b9100c5078121194048215001c0200460410303085403030045404088445004000b000906a22840c010380702d911910002841908001001102c540c042140d03420f24200282c0010040c440e01640507610441c050381c16a07240c280da0070842d0303c00d4100c14100c2a0641d0000040001c0168444560b90b0068032500d89245040d00d4900001c0081490340281c8610300e40c0e034444003d2051403407820812a51001e86810350410500e902d1210820280c4201003050081d8590070001c41c50030f11078502c110740e000031220b1114a0945045500030103402c0545e0b008050540350b1100f4040402c050034107907550400902402d8107041c140360402c00060f0000501d544824007180300000046541c10725068510222a100c03400c010501c1c01800b60340c5d12070390540100b146003a00f04801500f1030b502c40c0e40249218100740e21184c2e020b00c12103461 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 29147946 1250 29146696 29146723
    0x609021e0901140306070c06020702041508010c02010e0303070f0207030b0406061a03040c0e040312060807170f0319050f040f051203070203061906030204020f030702010506010908072c1501030608 86
    0x203d030021b92460300415070440b949014550050030071950384d020604035107112032142c070a84110401082141c809002e8102d0750201c0b44000d1145203010001c1640d01d0001920f400c0034411200342c201540b43c42000301e40002d40e0070405852481c241400c0c544014401e82c015850b4400c4a543d60290440c01c0c071003200d000b66480807940e6291840c12580b100e0801d0090b0088041061564112004122a00036a005054854040d040a924110b06444880f41041461b103c1d50018840c02011003800b2007585c08102d80505007104241594400322001e10821000329500c020101e00410b202d030321240301c203082d40c40c169100042e03e820002c1c516036034022050300035850392004d4005480f1521002200c5071100d0b5828012803019200c2e0b0004050341c000d80613980b08080301004000d0203650900415412407420b0910710002424550442c0d140c0c074050064203d00880c0040c0b400d0a42c034115981c400c14041c0c13940003800303070070100280040e0020a2400c00c3c00a0f0404a01107884140892244e990176907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 29149196 1250 29147946 29147953
    0x40c0302010503041406090c040501051504090209010905091905010b030103081b010e0d020610060302040302150f070602070609030e01110c0904050102070b040c030611160b040609021e09011403 85
    0x69540115056440108200c03030740f0501d03054070103c02204105a038040c2101402074040c1d14075881c148011101d050748041c0c0304107500501411a0701100007201e095400001c4003607070300c4580000503100c0140580c006074200802c841004180012840b0300408284000028030043e41c0c5c1d0001040c8030b020a010250000c0c00c2000b46414a502c02c041c080714440c200300c00460b04002aa002e24245901c81d200100580c02003402c102210b0320f0860384034060125414114201421600420f42043d4150a0710381401ea000440b040000c080d14140c4488a038440e00641d941c1da01842c0c6400600791000301180410003c04000c9075540c0610090030160307810b40000c0072001c0c400402c000800c0030152082e54295800c002041c04552030b8400b00c0d01c50f03030182c02d15130802c03465458078030100c0301d860110b148000002d02c4940d40860035a00101400c90300000301086540303941c14081c009000e4000300951040f822401a0324000700c603202c0c080044021511800103a9075031a074401045003034071a1550540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 29150446 1250 29149196 29149199
    0xa0f05012312030c0a06050105090103050a020d0302011113090b0d110f01050c0d0e1002010204150804020105090306010311120f0c06070c0b0309011505010c0302070605031803280206040c 82
    0x2200745610740d00d688010002d100508152505070b056a00c00c618851003500f115040d00c06110340f41c02000d00400082d9002d5001e58074549070f00d070320b03034108880091084403030031075040c1418400d40050540302d81c20070117940c3d280d1170050000c100804d80d00c14241c4c080d04015844a03146405850f8452091300200c1146c0055240401c126810141c0f0130781da07042c804c040c420401c00c1c400801100401c15502c0d10303010003c900314800c2104040e0307140802c6c4110b80c0108014490715070500320300e9050010038103125605842c0c501c0180c9440c05014100c680501c5110000420700842c42c1c041c18403000161105100d9000058807161144044102c0980300c9d8032040c182061814458001c2240d0390155400030440da0700c170641d55807560300179500b645c0309030f440e2044c040150500860207070060001b400d0181d110400de075000703915452184181c50601102000041d00b607541c002c4811a05c180d00010749603900b1144210841c02400500c14a40044182424511182c000240c05000f2030300704107142401e6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 29151696 1250 29150446 29150489
    0x606010c1407030f050c040506100c170705030a09090501050609061917070801030201080708090d030b010915091409060a030f050102070209090a030f03021e0d060b0f030a0f0501 78
    0x481c485000c20946100d0300c800040415040d2852115292099000d4000c50b0303c09000c100545101030995446000608401c4042b030b0b0708486000314031a0300c511054058241401d82c060240103540e80a015404001803149941354000340303020654860038020421030345c070781040c0071b40c41c007070f012000d03401041c100101038214200e48500900000e052400d001d8071880c01c203110407051001d450500c0400c145a0047c42150b804c0059141d000d440c2d03140250306071030020055940c8e07800b01a1780b40700b4543e5030304003148264442c20280024203804407000c0400e20b40b16800404803038861007080d0b00312000440b43c4140e8079051841c00d0294400410b403580300750039034584080540101d28122060b40d420080600182c55182c591031040c0e6140b406800b1254060802810341c40201144408042c0b0400c000c1035812883c00b4220b242c40d40140242da2100c100040c1c03640100072903048524ad4181c00f080500f0100d40c040c0045100d4078a850062042049544035181980c03800c0c040c02601102450030312299 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 29152946 1250 29151696 29151713
    0x504050603010612050604031d09280e03090a0f050d0305130810020405040f05040b01260708010b0a0605030702030702090a091202010b040c0e060922020a0903060e0606010c 76
    0xc01400050425582d60042c0011450201c0031605038121400700024127801c4061441d11b402080c8501c1402c80c2490b0009200c43d00082c4440360180c4041d0350707242e8080340c6003410b84500c1c51f003007020041c0039400c2d10259038980011200902c2022a03080208080f0f1103c030000d41107a101130004003151595076420303100c1703412545901c40b550003660300010b0411000c000c809410380f2010300c0141d60b14244810b0105a50940d842224980d00707102c02c1c40002a10381c034005044940c900c0308076034407203130070300d40c82200b0390b00300030382c001d142c030031803002142480040d4051410b138181100c2c00c41406036541c0c170031f0350a400b0899000e0301580003400303440090f0918000041d40220b0322600021a002165600c4104040e00041e18005179990f640d4103d56040034030580601c0034450400705038640c10180000c0040c49006d04c010300800742040644d0303942100003560b0701403111400c0c003076448120f0804004c15884482c80305803481d82c28800d004c202107e011400d2030182c2d006070360304001d11400792102d00c81c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 29154196 1250 29152946 29152951
    0x6210209130c03060f29090102030f0301090e06090a0b0c070206070b04030201090611040302060904090201020102130303020606010215150d020f1c0b0c030108030a0804050c120105071d010207050405 87
    0x401030988807600e00504030310b00c50911400349603100040c0300380c10401d031000c0c4004103800141c10307003111000c02104460922903070b9400300140c0b50520303510048940103d046004d10207035034403203400100002c18851f01070f40101102e04e41d08d0307040700d03480e41d600007000340e40324001c040140034400500f01065440b0143e000130030489002400c07445c03400c1c015075501c1000c450300b10342c107030010303551908480d040009034011141d0004107003008074249800e54002404910404515500c5280d44000704001c590007901030340c003da441030100210641da2403c1c040c1d191030007242c407180180221a01118501c4031960301c1c0380514245510408d02c8043d4400f440768030308142c00142c1e8407240d41090040c00340c0d03403c0107a4403006c2c141c2450090500d01458100085034010742070158a02c4c1c01e100501c40310f04000240c0d1410520342ca88881d803038985091840c00c01c0090104c01e0341002c100265150b01e000e0541146001c0c0a00c0e80c2d9802e294072800c030300700d41501c05000d100d40c01a007002404000614098001d140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 29155446 1250 29154196 29154199
    0x1908090307080705150105040b030c061b0609070303030e0a110d0c1809060b060f070b100e0c09010f02060f0c0c0f0a0f0b010b030c040e0711060709090606210209 71
    0x9140405544034110990003c0008035083d40c00865412092039900e40103a0040c441a501400071040001c0082d4407182c0d42c07040a80240e101041c02d910035000170900f442448100341c1911154209101480e8980c40d8038001540031904042c0b144003481e80c0003881c0c89515403c094140910184102046000114600103036510b0501d61400705105104503803003800b15003042000184401c15140070700070f039030080d110f0764498001800764581c0300740039404580c866a13000c0d4501e8000d5403021220f040109180d0481c0300c100c054601040b070444518401029155401d81b189044003040d500d0490351040704660702c480d022411030106101c40440700c040c2035038100340c209588101401800c600e14045004000313441d410f1031000300005020200060301e0141000c00d5110b07145240042015015201d1449206401c0b140c441c001070000e8424802c0c080311203480001e460311070814407801060f400305406000d14903807a00c3d800250040c003c10700340704612003840342c040d13101940403894402900300480c01c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 29156696 1250 29155446 29155453
    0x2100c0b0402150d050106021e0a05070905090a060204090903121a100e120715090e070c0c050303030f010807060504030f080a030608070b0d0c09030213090809040204030c03060c0302190809 83
    0x922858105d003d03182c0a8001a802040c3c0e00741181412507000c11610b001104a0f0880d0041d9404a8404250300040d121000e0010526840306580140f500c440f0060140134180b000c680414004401d40140000c603000781d464000708560000c0d0030382124043d001000d1611400c14004240d428103000343c528820071801c001d00000340d9600441d005040c0012001c5540d00104000d000344080106419107110081c500148107905041c481280380740d0140a100034403c07034600d40c1c41000744d8681da0201816001c2c0a0341d40324201015a01c0081c0420b00440710700e170041c80000306000380310b41c050318110b0b80c000d0640c100038440e689035500d681e80060040e41c10152074110114114a080090304014444107180580c2c5900c80400e8001300e6414000240c104400345d40c040000d681e0301c407071080000003c0d54000a10315118580038081c1d01c540c1885540007800494000140000b43c0840700417240145400c1c0848468114100c01b2031080c12403103402c428041c550304410301d101c1c1020a5010108400300c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 29157946 1250 29156696 29156707
    0xc0b06060c030d05010504050f0906010e06060403080a05030711032703010212090609010605030a02100807111c020708211c110415021515030c0a1202100c0b040215 72
    0x201c0d415544080e103d15079994980c4010804c2d070030184504c83e80300854181544460600d098201d460707140620595031040c2400012036550395406013110011540000220350f540a21007025002e40c004071203020100f920100c401c0c035100d0012040311240e88052140008688451180703c00d5100d40300140360709990301b0301090741c400b81d9100785103020f0140580100007914110301e015095440d01c0d00b090740690840240c000050700d9a1752140c6c60109030342001911170f80d50a07001c03203010300081740300b8036544501c030000c0100d9200641d04005184003582507a0305503403143c16691351003440190010150000d07101c0d0448841280b07002e03080304131140004000f80f00c1d0494042d07041c0c807501d000040625a00080400c581080c40c0502c510000583c0082c00302ea030460a8440d0401900030419041003010312450101c0d50b030240b110341180340b8018a03000180c1d4a82824055003800c1075000c074050403228514404480c01841c1c0301c0a2030b5400701070412566625400c1c801030100c4002e45150041c2c09001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 29159196 1250 29157946 29157967
    0xd0f0207060504050105061302070c05090702010b030a1401150b030a0915060306021309050f07110f10020309070501050c0714040204090216020102060109020c0604060c0507080403050d08060a060c0b0606 89
    0x2d0140503078003c2001081605040c400c00c0280906100510881803041010000092006040c001151012100418582c0c0c500c001a4090004400500d034107000e4000b0240421104240c10386688a91b02c0c003c008444940f0030f03c0c00891110300a00038190000c0c8000707042200180c105000080c4207101900084000c00c0a090035641260030854a00d600410614020400304170100c1c01050440028032280c00c041c1032652400b400502103000300503c0b4280034041880401c000c000c0d42c0e900718204c0c0d64400c2e44080a0000b5002650244040e000301c02d80081c2035072041080c0c03010710900c1c00151010b14a0111941e820100050381c0541150b0203110001c0e07103400920241000100c200c144039400065807000a05044058025511191046c060640d0112000502071703801580440d0009030182c4115040c6d820340070b0100700070800c05001034080708004010074281d018a4490b200c6060503201c8004001c83d044d410700501d000906509011004200304044154002070007401051610001a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 29160446 1250 29159196 29159201
    0x8040807060e1905090a0506040b060705030d1a03060c0a02070f1508010602070f030f0503070503030916050a0b030703020a12020a030608070b031003140c09010608040b0a09080d0f020706 82
    0xd1000001c106106101101070800c6480c3d0009019002c2c11100b07030390305200014248036009040c812841e5515800156907840e90b604c000e0036600d00505c15034841461346840b990300e0303001032200040e403070400318107000d5040e1840603803014400c0200130340320698940303005403819004030980c14118414181e00080311100c9129913005048141c6801e103a0760700c6004040c004110681c0181d0843d400544100502289003841070243d9501089695000d05e01781403292442c0144000a0001d01001080c061f41210000d4420203c8070314802500025594000300000c514080c030420341c4241042000400c82c43c803990091254041c203042c03007411240c2c03603100c0c4002c80c0c21903802c000c08a40e1b10927091144a1041007008002c2c10041201e03440d514100402e622003002c648030042804c92030f070113a021428003d01803c03e848901801c901085c1da500c0c20000c022901c192400c1d101d080e074880126542d8210340c010b0103100c680114101d0700d403aa602d103000c00140400000d8902541e428030a800c0021090f0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 29161696 1250 29160446 29160449
    0x1306091703040b0a05041a0c1b0901060507290f090a0803060105030406090f0c0609080601031a0417030903071205070506010e06010e030601080c03060c040f031e140d02060606040e040206030408040807 88
    0x50050540302c802d44070230340340b83c00ca1a050400855440d01045040c0da41c840381e007981502c0b19407420684a00c07c1d03241407403802e04c20611034400741e802503003605061001801d4180c0719590070b5041003041c1e12a0500c15444428088000e064030208200007841540200000c41e001481905c0000c0c503400e10b40c4803801800c0714400c00b01c0c0c100001e10300c104107840d0700c400e010f030190034074501038191395155581e008010b03542c603468890003403a00340005060106608030598034141a0440503541d1400e2545140c5981c4110000c41d50440260350300622284110103172040194840000c2031581d083c81c0303040d0107015004140c2d6040151036025060030341c90a210050003040c0000003000c01ca035451341014100000140700480600382400200440f981d5031034200e048903046100c0e01040c0d0004d41c40741d141c0c05101100540341e40c07079091000c2d507040070001e40024802d90f1039083e2121600d800e01002040d22a03807091034900c0c1c40358801b14001d4a042401590014880c00d01d41d841e06990307032400b03410104507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 29162946 1250 29161696 29161739
    0x610261b1b06060f030309040903230a02010f06060824031204080607050a0c12020102041a030a0b0103020c100f0902040617071512090f0204021306091703040b0a0504 73
    0x100741400e801c5204211040d0410000c07148405224069030100f55280110034040348981e032151041e50915000c0ca101e20300c4c001130980140b142c0039020209480d00d42c4041c40e02030041d0300e07107400100c494099209140a03503d41d940e03800704545504001101c8030704688032125041c4c41d402d510810a03541041112510381c2d5602d08941c84615200043c7e04140c8010311140922200300b00340c0c1c2409a10101d07c40880d40c0c0080c13141d1441d400704a04900901560304044444a00000850600550000135600c200b424080074001c484524004405034000c83d4444c0740c541c0c1c00080e0380480101c00d50850880d5100708240001c3d101229000282502c52075486040c02c101140c0080c81c2e049028441c90000d403222904082c0782120003c4000c140d0705c002d0039400e1140da500d02040d010040d011281c03516880e00100103546960f40c0c051003611100ea64415213010802c1c604001401d11085100030f080c00c00c1810242d03017407034039003017500031a0382c84070b21103600f000010040845e4000740062500c104074907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 29164196 1250 29162946 29162977
    0xb07150c2c2205161704030c05060406050405010b0307080d0c0516090501030309060e0f01080c1c050702071d060d0c0909080304020f0904050714010c0501050f0610261b 74
    0x400d00300b80045803000380404c20540b0700c0d01110803103a900b0920074590a03c203001000074559450038216291044a507008203180665010302c81440b80fa5003103d4065409031000304805c026800800d540c801c178070b10402c1595005803941d21666802401024090f601510999107103611180240e00001200d41001c01d4031a0b0300c030b0060042c9640010810040c1c07403541050200b82ca0500005402980c09021190410041d10006a403004c6030f1400d5548411090b43e07440070851000c0d22501c00303030008688001c0103110348500022942103400b40401000040381e81c9504645407442400450012644203a41034135054400096100240c490040e100d405240300e142c50303050a03c1004118118001b00074840c602103020f010100f01c001c07680d08100c034130b4644400d00304c0702e0940050b980450000c8000d0101c3d483e1004119a2080c03810009100d040c003100c0040803408440c00c203440c00700d03d6041c0c141c9800140c0342c0001c01c0c40681114140c004078185180e4441c00070a0101c07820a511000841c3d80100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 29165446 1250 29164196 29164249
    0xc2603040c0905010b030f0604050a180302010c031b080103120203040305070e060306070519080403030f0c21022d04150c0b01050901050310050406090605010b07150c2c 74
    0xd6108984c050a080b0001074550306101a0301401d07240c0c0940403e1040d65190041203000c812607004901c0042c0c445e803901288141814003034004e01110030214046400c01114500c4488899000c1e100ca0b5072580b41c02800c0e90864503650050300d0104181c1065200c00c11010001c10003c00641008082d80040365415151480078036040ca400500400280041401070f00d030451045542c8014202840c034080302c0c00d0b50355003001c8010b4003c0c10f92a29456180100364910150704c840601c003141c4004000c50021001015208201d1243d03115510040001a01181030400c40414018034902400b049a091580f5200c082c0a0f0b2080c03c0c034500c0101e10003003d854100041030842e9801002c080b14400e405614010100351900c80d54940c89410543d01d0000a0401440d03501c05036005401550402a641e12940314000781d03801044260b0b09104c0d0b690350081d00403158068010310803075035500c88100c1d00c8139807107800010300d07149100c4209000c080351000700d5444140e00d0740110743da160015030451 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 29166696 1250 29165446 29165459
    0x280209030f060118060b0a050a050c070e09030901030b120a023705010e030c0102030f070f060c21050106021903260a0b060301030f0809060c01050a09110301050402010c2603040c 78
    0x407055603202c0346101b50188040716046810500b941c500f0403280c1052540d451243c0000f506080183d0401d400312041641808000800003015010904084e00e00b0000480c0304010411000280c4481070402c4e4414840000181400483d100c2524590200103100c2020014a4100d9403541080a801c884498204016640e032102e07916080740000d802030000d8005110000f500c070b120b2845014040f10b000201c040170840341000005a00d81c20000402c050b280c205801002940340e40d441c40b80e0f00c018208490210310320782c8a018100c0707065800602c100202800510400c200700c4405500b4042d0140050010700d0b544d10203480c0114407074400b010b00345054026113088a1460343d415008840510040c4000f80c0c4404098907484d801191f0245c8175844400010403911442803159240d5080a0500c004003007190080200d40744a140386001a8603024245400c075042194043c0c0001c0700c90f103040c0045045014803210500d1885808903042d0000c907030000d85035005a13401c642009064200300240c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 29167946 1250 29166696 29166701
    0x30c0506041b0e1b0c0705040e010b030601061115190e010902010f0c05030414040b0604080601051c050d030b06040815010302100207320901090207050105280209030f060118 76
    0x905000c0089a5484c14520480c01801e603024075040c01800c0c0000383c210a0702c0b4100003404c02424010f00502c442c805075040d8074040e02c05440c8060113881005c00120b446405840a5030000042c4001001d420440f82d44500e80700030050004200140d41810492203000c01d401007109980fa080c0020990682c41d01c00104469060b155000030487c0c44514400040c101100f25005ca822503030410015000410004008050f40c0007456032110380098009441341020070351a048820032904440e800001121085001071503400080080d04948006110381c1d01035800318003c45030290181e82480c0d112407015141841c40c40035901035600c481c0c010021071908000d07810076041c0f2480541080781c90002e80c0d15040710501c0a40c0d190f0450b24800340031001c1c6d079060039102c1e00001011488076507901c9418100940c09040251001d500701800901480000e0074040c424202d02542d2000300120003078800e000790031800889516005070a1a03180701d01040160502920010102d0301002c0b9511407078004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 29169196 1250 29167946 29167949
    0x80d0203090d02010b0a05041505030f0d120b090f041103100906050606040608041502120106030501050f01021f0917070812070f020309010804030509040e0102040f0b04051507030c0506041b 83
    0x444e07042296130b0103240c641e079103c44101c0380e003501c01040741d40042c030300c160303254105402c0541c251049100c0c0e58580c2100180e0107440200640300c0c0e0b0980588054650140c80c10b1018503070b000602c1c0346c00324400051a078185944113005229446c50b01250a000a0070001b8521f08010680c0d19101004e09201c49842015040f0348200d5209191628185014191090040010740303c0740940c40041841c002c15011513612400e240c0b20001590386560000d0002c1000303028090254080100084031540001601100031008550f0802c0d02a00d00e004030001c0c00005038116401c151540c03008003038106400c00782180c144a5808503464807244a02c04480c14801030404007045a01640d03a02001e80110440c1c107988001c3c0703096200c80da181d04003900c0d10301c50490108d40003403800b24207000c100d0040d409403064071142c01a201c10560789030314007407441c0258000e4135448145205250201031080d002030424501c42d041042c42210142c48007814240222000c1e103074035400040c00090501c8e550003120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 29170446 1250 29169196 29169223
    0x6040b0a080a03110307050d0807110105040309150c0606030b060405160909020a0915080402130c12180b0403111203070203030a0f060810020717030402030307030309020a03080d020309 81
    0x128440c900650a561100b2869010741408800d14460708079560034000c0b85d540580203022078041075981e0600400145084851000040750841556440c5106015280c0125010303036844a40c5410b094003c981c50858420040070310204204020016820340205d42c0258044c004140340c1c0e00d004000d00064440003455100c8071043c8422a1018541280e0035006803842c01d10700603190398004009070742d06500c075000904618101030021050355401000244924400e4441d07583c0c50000d1002031040d00c180d00a6040400c240101c0441080c40f9a4480041c0082503d08a4038140742502c5c1c2a01e0803506440c160002440d00b2a004d6025000b00007010311550b03128001c3d803551034001002516404058010f03030f000c1e500d41142b00d0000f0307140d4002d003000e0420101500c1246e00a0010b1200a5100200480c0c5280c02c0710524001400c1d2501540d200715000b0340035602e4401c00b0358040303008004004040b40d001c04888800304c041206040500600340071031000503074a091200d001c2d498460145001e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 29171696 1250 29170446 29170459
    0x10c02010f05070312090b09010b06031e0a06090e030705010c020d1205060a03020307090b030f0f0703020105070c120804230f060913020f0714060106090312020a050a080306040b 78
    0x11006036400740110259690500e0660b49440780c0c1c0c50304031480944007070380f02d200f1802c1090800901441c90086070041d00450300801500a801c1c0502c007040c0401c42c3e800e02c00303000c0848050061240c2102940d40030446050015085890b11107140455100c417005070703580d03440802d10004002d000d10030035182d80301500040481ca144050010000c5034002e4240d05c03c551a803003c620240c80b00035411003c0d603401015100c0d11900c07094080c00500c020f0b48414817912903a0781d69452f03070001007080030b05441c00c0e0300a00029401c40c1c0042d203644d400624115006505903c00180c0a14817002c107442140c800c004850355207203040e05070303821500c244003213240406c02d5508602d059595404015100f0100741c5100341c407041240d001a03110030b80240c070703012480d000040d014448100800200f040324410700740b441d8000d0b040c414082e40c9410901075103003c500000d03030500209940c60b0640fa11500c1ca80304407020400c09903121401c06401c5003080319159000300a014180c5098056035007005420b46d0034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 29172946 1250 29171696 29171717
    0x504030801080708030306040c0c150c27030b04020102190b1006050c0604030e0406090203040602040504061a0304031b0206070b011a0901051902071d15040203040510050619170c01 79
    0x6132207106c007400062140340c0c0c0e0079041e02024043c09031f942c2419000700c40d00c445481d00306288009021506a1040000c0718400e8803180006143c0c040354100141000450145003140d0300c03941c030b1450160041c1c0c10b41c400ca1546601040710203100c1d23030740d0b41c2c82403645042c0741c10450080f0320760345c01540101c02440400c4c0300340c060110000544691094051074800c0003001500c021600800e00750300a00c10b01341c000000c21003403100d59002401124400e46080009a0303848401c4e07842c8078202001a5218403003040401c000c81d114003282101c01d0055520f83c50003c5c42c0e0340c0040c5d100c0d4805101250b4051885c00100101e072001c00d5071146000361070000615010300040002d22034446d0b140328641071110130b040f00107200e10810601d0058140c07446110f00c0c0000d507a000c140d1a4100b190315440c0540c0928100c0380703904148c0240e03801158004001c00b01c440143e42c51602130074000704402e41050300310380c1d035000c4244e02c101004000d01f40c410014143c5141c02240c6c41c10140c400c5819814403a60703419 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 29174196 1250 29172946 29172959
    0x1060c02100c020d0b060a0b12090706030207020d030c1505010e0601031b0504060c0c080706020a050106080102041a090f030105070302041d06010f08180a080903010c080114060705010b04050a05040308010807 91
    0xf41c8001261710450313034606642c890001650005a90f000782101400c0400d1045c0d95901081a036402400d12070100d4402070f80e0303103101310160b1048080c02034101801c0701e00100008d0003080080025446603040c403014020422088044500c01d038860b8500c402504203024055800d4031607200e9110151120500d503181d544006400c0d8451032051808010205440c00c00340300a03200030802400204040c2e07200207a41d010000c0d40c5081049080d14154600b12001070012014422030302211843d0540000b0010742c6820403c5a4008148154100d04070400c81071440d0f50a00c81c0c0c80c480c0c0306507200140c480f41001c1565900101c010f00c0c1c4079140c3c194405103c050b80e00000307031f42e800010030304e00110159207a420911085040c840d0001c0741e8410350550a040000381409081001c10030303402040324100000085400740380a10030501e400d036480c0311181c2079081007001040107034081c00000c0790010103c00031030222101151480d0081d0b80e1501840700700355014040c580180b0340c132801070024500308007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 29175446 1250 29174196 29174209
    0x51305090c010509060c060106080f010806161407020405040c14040915090311030406050301140d0c050402030702031204080403030e2209020a030b0a0b01020c180a2301060c02100c02 80
    0x4901e07505100000c190401c691390303070303000b1600d01c5407a42d816511a075a440b86c01510a9005840308070110b820703c00045050480040c503030b4442e0b103030050150003400c2c4040d02640d0000500f6141c1d640301d4001c00c03c500150b204e0b409424021803150964512082c5042c90003803400c0e04c00144030307100b181054903d5021030b1a130b842c1e0901006c2d0080c00001d0b0a0306901d026035000c20440c00c98859800007180001c0d5494104014604844072042d0440c0503500800070807850481c2d034880100a03d51615041c0410308280d406154820300e140120382c508500b8440101c44404111000c0b01c03640d02c0001c0034010140e100519903604c220980b0050001780b400c00b10004400404100310480c9079464040c0c40a40da12a2890001541c01244455040c2802070a0b040a0202c40c000e2a002d48500c031000784941c24288e0070681044400c4104c0540741d154400000046c0451140e1241d2804103180c04403043c00012501c0b1780209025113554000d10702c640b05104c4000c01601d92a010300020210003400340c1c5803078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 29176696 1250 29175446 29175463
    0xa03140304031e18090b091f03050714090109050108030d0e0c060c0a1202030405010c0f02040902060a080f1005060703050c0a12050703030b0f0d0303020304060e0f010606090515120901110d0605130509 88
    0x80352040c15103030692910312481c4100783e2014000b880bc1d5030b0000754501d00362510509905041d56181034030b1303894001c00c600341e620a204580c0960700c00c1000102141650340f105241101100564038076600a200141040c0c00581d000d2100f038200d61002c2003001281c1801c80681c0006001031403c2c9490a400a402d540201601825800041d50079101319607c50740042c10b810390040400b40c81c2c6d05803480050840c0400c684401102480348007058a69444401c2c81d003c480e4002c000d00e240601d5650101c0703094201c2030419903e4400c2142e0000003860003ca001c0c01c80d003566a41d40d4441074103041c000c090301e010b6600c4901502084922203810707228a200295250f4140c1405030342c81d190351603e000200814121300c1c0450040c5209519400b04c1034000c10110786181c0d07240100c5036100d60400020030002c0320f46200b0b10f50b00300148181c1440c0d83d2566540007003183e0000400c0701605021110b103503c206001a40e0f01d681c5c42c01809a072620940c040300d00000e00d2401c20162030310007040c0e56924580c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 29177946 1250 29176696 29176711
    0x10501110304080304090e06060904081914040608040b13020a121a0408030907080303090601030b060a09060e180109050601140a0b04120210020a03140304031e18090b09 74
    0x4298240340c82510400450300108520000c0740d1365135541b80e0ba00b000608000e05c104015001d04070205045240c080b42c040d00668020121030f141c0700d168000c00129001d5140840d00f070100509084c90082c41c184040d2000f0901a220f440003480c0074600008607400c02402d009075007801281e890090380781e0031040000c0d900200b08070071007544182448a520600c299600c224184030307004201c20040008007560003900d44e0750031900300540b11104143c61703010803180c1003500e9018400420100e22a2420039400c9840500030424140e00c5840c0b0000f503a20300d80040c1000341000c014000401e02c540141c503800012040200803801d2035683d59500c501c3c044c4141495025042c4403a141c80c0d8400146400030308503840d2140d551a1307568901010f224040100340c2c0300d0f19090440d02000d5001162030450705a01d665811303000802c054803030f003054001410580802a50241074086c80600100700450303030034191a8a0359006440480b04202e003d0780d0840d00d841c60408218541c00d440d5140c285801c034a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 29179196 1250 29177946 29177957
    0x309030602030a11030a0615020a2f090a0218060a0c0311010f090308010f0506040f09020d11070b0f06061c02030c070b0c030703050a021201050609040605100906020106090c08010501 80
    0x365110018050300751340900400d60b080000034000c1d4082c4030b50141b02140e0541c0c03400756583d801c5090581e2504242c49026010181d0185000300340803140f5101c1c40e41d00d00b0500f4507808444040e011a010440c22280d841681d40d0000b20442400804900c005910304c1c12103110345854603403440100311020003240201400010701003804400401e400a11080148480800440c0e2443c01c0c01840c01d20203204158112030303080b01c00710300c42c18400110b4003038500031580f201d081868898110000d40c400007080020030f41d21005900103540803002001524081c54102c51542003620380488a03840180c1014810101005210030308400b0540c03c0702c01c1c0c241d24100688039960782c0d241028a22584000030141c1186504110342d5805074009540a00500d940030083d40d41c0b1130400d0000c81c8908002514031140040c010815490840001c03c01060050404145a80e41e000440d912144001000f03020841014050150550911804000340441c02c0c0c180b00c10144a030780070346402d10600541e4100301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 29180446 1250 29179196 29179201
    0x50f120a0309261308010b060a2610031509022409090903030106090f080705040c030b12030c010b010801051c050a1202030406030b03060f070e0a03020303030117010513030903060203 80
    0x31503003c800312000d00704070b0101e254245221150360b02d50000301303000b81c80b580c44080810303807010500c141c0808400180505103805000c403400e40340803400c2814101034207410002e184584801031100340c0201c890f81c01c0b429055085180080c20181003020320084203180c04c8418001d80d441141511704c0001c0044514043c00d4000c16103d01d030310840100341d0b002441c1c0300034000d0080c1c00000440c122181c9559901a00b80ca4010074a03000e58144200c001b0743d03000a500340b019103441c0e489010408a5400c00046544001000c104c02080e81c100e4255190004107003540f920000b8025000010424600070300c0c20740c14140011181003e100c4d4025000c400d074003040b420404200040d5a51582002c1c5407035041c1c401801c002c0d940e0740203006142c00030341080c2030f0407605d05000410500402008560385025a12003000300d030300301051000c06500074183e000000c096181840214060a10074040781242c000c0c41700301d00e0a658010345003540101207000740c4404a588407104800703999000d1070241c0d598 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 29181696 1250 29180446 29180453
    0x11703070807050303040308091203041716030305090d0c05100903030e15011a03010b0909090304090207060f060f15080712110307030e0102040b07060b0415030807050f120a0309 78
    0x6006030180100140d40014074041032000c0007025504c928444c3c0c0d2500083d540750140c403a25034080c43c5014551400078004100042c0344044101000e524900c00c0340d040548841485040c00210301c01900401c0e580c90610036420000d0040440c50900341c00e284c41c0580b8140e543da03a030b4161034540b20b441182d8450300e00702010705c070350032024805130340c1021910000b01400b2955a218400c0c4101e074140110078402400010102003070f80e040311015201142440c06c5001401071400006000c4c0b0004d0104101c0400c9608031f510240100314000c280c00a00c15034040416011504c4a03048844600551042000030b955502001d1000419074036280915444215055481c1c0c0a00207011013413600b0200c45085100703d080185100c0c4d007080d50280481072202005078201e01c00c0c2d0003107503900003040103414041403664001021442025000003040195000411100300300b980080302c0c00c2400054850510500f009a509a8542130014100c08031010202e500e00c0d100e09400d58081c141c6480445051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 29182946 1250 29181696 29181703
    0x503070b09060f0418050601020c09040209041b06030b0103110405060a051803010c030504021e0f0105070807080301080706090f050604030605040f020d11180f0601030e0708070b04060f0e01080117 86
    0x1190510044580c0392a1100a0f80f40301c5e0348400380e1407074445e141c039000402030341c4001188607540310058240e4042d0b0b01e0359028001007040003841501c140d40034a0300c50090a6240c0b030640e00030206540d0010b501c100c0d81c400101503c0c05280c648a070f1035400d01060041c0c0e52a20100e07600300c211414050350b501619911010048001c1a109500d03500c0d1000501586400d50485d0303104a01c00c844268044208240890000740003c41c0c1d82d82245501408580d9075000300020f144443c0906012411704982e540c42040c158000d803c01542d941140900b0040d1540040c4002c004c0c1000141c0198104e040c072001c00da040c000d03888090441074446c40410706020640e00c881090a40207419100e00000504240030900c49050701e442c0650360b120f901081c5811881d00040c042e1100b20603910303190300d80400444c05008900e010540c02d002d0f4543c00100c19000308403a8005010070f90002d5112441c2c1440602100d071007800b10024402421408042070380e00c220790070b06550342c141446000703030310046800b0328 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 29184196 1250 29182946 29182957
    0x306010e13060e010b0411130b0a03020c03041e0506030c09010503040c030204142d04021002010615020f0706030501060c0f03120c0c050709060b0a08062e1101060503070b0906 77
    0x9031031803c5258405503c1c10b40081e108094144c40900106403c807802500038498401301c46011520f402082c40400d6a2500401805580745009420545a803040d41e0840e4003d50140801080c000d400600d44650041c0400050004039013503411442e01d000075000c144140005641040400400102048040520391001e03680240007000307412050240949021800d40701d036a40d61103c85080b02015684604060850070f07071194004c900d40342c80e800c0c000321006030b480180c259500c961011442c00c005d001c420b90840c202e98000c03e16032a110402034180101030700990105420b0400502c1042d8100103140d4038103900c540060120011030074102c4217180703006444410389042c043c50800b01d56200b0070003000e190160f0f06851403955260151012905d9a00c12400e200324244480c5c5c440c0e41c06034022581c80200035000001000400b034030020008030140282904155111031200015031104c50507000c41c01d140000c003d12800c0c40006940c603c2c0c5482400c4651400080c401e0154482d50140c40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 29185446 1250 29184196 29184203
    0x1605070905010b030f0a0c0906050d06030615060807031503020907120501150e030a0c0e100509010605030406050f01030308010b070305090a060207050112051b0904140901020c1b0306010e13 83
    0x3042d40c664040450560081d144118101802c00124039008001c1c4941c000381001c1c0c4c0c0383c6203030403440c200b02554546c1100310700b41c0504c0d80da0340b40040428460701a609108110700703170791444d80342041d1740a0a550005000c0300304140c6000d0b51800003403085441c117015650101d0b52040981d444100844104250444500d24981400b00009038142c3c01888180241c070503448039000c407075106080c07543ea4081c07004090a41c986041d000c1001c0c440d4003859981099188000d1902c0310345031b001081c800c030401e07070004000905c00401c000620480d40b05045e009080b00d04001d00c2d55140da01d0040180b40d042c003c80011100000c4c6110805000d1b104442d81e941c0090300e0b41c0e000b95034691000e17403950300c01c4c0f0449000c5419589d14140100c40d6101d01c80c0f2034032401d240c6c10228059107250341d0720f54200c0c81040d50417984d41c3c00b403901c1440020030154411081d00c0c0016940b01199424103003003241885000c10000d020454481443c0c2d0082910750560341c1503421140c00e60341c0e08140943c501318614018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 29186696 1250 29185446 29185451
    0x60709030f03050c0f0703030201230f0a0b120d090302010e09070e010e030102041a09011701060219020111030d0f1b120905010b060703050a030b0a03021309020a0f09090203060609070516050709 85
    0x40540640000bc0081030303d54a540c0400206910042504001c403030172044905000c00280c10030b58554040620020302600b520102d2120000e100c0c508801c85480102140400390104219079111080501000060700c40c2c5055007080000039000d805840a0740b4103205000003080c20a8078258144d81c0101212400c800032040503211910482d80000d40240c00601c101d03848440003040e002d180360403540c5d9580100a80402c1c410000d001c20320f0f400e003c904209410b003114007071220801c080e1a801f028440300055030702042e401481158118451510b031051002c049804d0aa000000720120300314041d404200b0421030b00c0d10a00506078290b920707a1100c00800d00c8000d03d42c3c000041c00144000340c808010f481d01c50b20800090300b2140c13200946c0011b91070800380d10240c623500050075031403000d841d2008864480314805c01c00c0c06c0581010f0102c550720761404056140400a6a80042054a5501c0c4504250200900d68071422003030f18000c4a04240500810001b003000307100501429004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 29187946 1250 29186696 29186699
    0xa0209180a080c0f06010807120303060306020406030203090106090e0c01051c050403080906012301440a020901140a050f0a0c1a060108010621020a080405060709030f03050c0f07 78
    0x404025084104001c0c42c40c0b051203044c0351801000600e00703060350b2a21b00109074140ca8910200c400b9000d0f81000c030105a00d540c00080094010300140c40a05401d0b00c0160f03c0717103080351005084460b40d03408a14401d080004400640c40c0100b1100c04070074083ca003c5075940100701c3c40440280307044033340c02031041c9004101300c14103501c40b0016000c0d05065095440d42d9980d815112801004643d074110030700d1103180031944541c050301062400110250040070313a043d501d880c040b042000d0078003000b1400c0f800c1c3c00c00d280d80c1541c01d941d20b40c0801004003c41c108020030300020207441c85200480e402e64400222000c03440d015105940141003514629941c41502c603034000c1c282c51004600302c90074002181c0030f110950f41c2c11a030510615043e52510910381c0703409070481e2034074600082d0803d11501d0804490800316280000d01010103603403a8800c5500342841c110385492801000701c410807018600900000e2085500000300a41516007980c544a10315540c3d402c00c00d00c644c0c40e180c20701c9203600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 29189196 1250 29187946 29187953
    0x20c0d030902010917120306010c0c03080d200301090908040e01090b0f010314060103051e010306020403050c0108010311090c160f05010b0f030705090403050c03040605040f170a0209180a 82
    0x1e0305614401e03a00c0d00846941c1e410b000490202c55107030355107141c03c001c0003d0303c0711403503501941d40403105151082c3d40c0411516065103040355600140c6003440001910001078030355015501501a110000700714894566003200302900041c01008580d07600e4503246410700c1004000d69002d441a003071400340030750f9585100d0001b07000c1003024501800d140c0740a140c05602a105a0700744000458030048580d071554011001860010702c658001a1803251030000100094461801303540310b07240c010381d22421800c286280505640801c1c1c10440508010b10000d1801c1541c400da51a0555000c441d68451a204860a01504040345200c00c5500c041205205038400c450307200900800007004000340358024800088a080c070042e07050703070000408002505103680c0090348a4040c0c40c126040607252001282994020b40c881000070b280401c05000c00008608204010540d0002084c6805082d0902c0c1b42c44080340c10010b40309260001c0090301b041d510b0290405100604001c0c2c070100c1c0b60030314 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 29190446 1250 29189196 29189201
    0x108130f1a090c01050403080a210c0509040e0c01200106120501140f06240f031905060a1203030509100f02071718060a051224030a0b07030f020c0d03 66
    0x484401d42403180f00380440c010f500440444003543c2d0040040d901c6d0500451050321842022030328800a586010304080c002c030b00c0c0c5d208441e810300280e9203a82d1780b00007030020082a9801d0158109141c3c200401048050380c0000c03c20908420119009018001082d0341c10700400c40d40e408030308119000d9008800b001010340c0144842906001d843c4c030961584040303140d1f07500c0c0486072203412104000b41a0280860090301c0c580c03040784424024a0503100c00001c403150f81040d625450a41c0b40000102c4148415015255001c8011b41c1c10040c114076203121126142c0302c0c03401c05414595200b001c107110300414001c102c415124490203221325180101e0702c000a50290710b00f5035007518000200b01c160b07902c101c2180d905059083e541d40110707200f00c0130060b16910203c10101800f40420803001000070344418607110b02e249030b0584060b481c81071004284011201003c0c0c0c8203422803041c01c00003e203007a8150380c10808914000405504440d180720080c41071310220000e5114460081040700d9054 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 29191696 1250 29190446 29190451
    0x130c0302031e010c0206010605090d05010f020706090c06050307050f0304060b090f010801060501030605030309100c1b09050a020c0a0308070908010f151505070312110c0604200108130f1a 82
    0x13081803902d03100040b61900021b014090014004101604a40c035042c1c2d081c10342c8a02031400084c1c030303120f8281e2145c02c984c04042c00b118103c0d12185801c1c00d000c40b07411400010000f0307051191861804800c0241903102d038409012846002002290610139194010040002e000c4e00b52481810b0600c0301041150091040d420700c0e60070a040410b0551107405008100d96015000350b0900d200c0310100000ca2000c0e0034010104400c1450303480206400b040a01c58411842d010401010309203220102601c0000306044000c0c0d00400140900150000358178100c80d03007628000034107403951501110001213951190f1419030074111200c7c2c43c52035036844140381316054042c1e0640b45580d0543c1c010508080051080412010b001c4a03002c0307401400001440c1610000c00204041c5865440b405038000c4040c041c540e9201c1c50402081060941d4140214090015460182014080001e03c2a8401020460a4101502c00000f00301a201c0c40c924075613845a810340e1090050050100518001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 29192946 1250 29191696 29191753
    0x1c02120a0506040603030e10051905130504090b0406110405040c0203040e06010f0503070e03010209040e010b0103150503030702010e0301110c3004060c03090b04080a0606051503130c030203 83
    0x30000854641d15151244004403a450b0721440c02c00751480d410402070180d0036100230144641040b03484181281c43c001c481604080d9154151a500740b00d40380c400105894124a00440c0740814580c00b2498000c81594890307405400445c0d00010260014007034016544503d4000d8101459665529008800342c0181ca00010aa980e50340d1504011201c0e204044140008a00c0400c04208118403c04008040300d0001e00050f01c0e0070b2462001ca0200c600c51001009183d5481d4200d49481d0ba250040000c643d0034000302054250030030340040e0300c1e4441c60340028140180d00b8132201c9a5107007034000e040090121841c2940340c0444602080d00d4287c0401e003041206000391111144080744c071040d10510074226401410642032500075901030715507070001d40510040c60740015403400302100620180c0040c501900e9071103000c2c6440d0081d41c1054210b58482d1610241c0030071390900100c16207601c400f011203907040410b41801d02c1c1da65850660000b039003501480c191201502c1041d0288071007020ba = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 29194196 1250 29192946 29192951
    0x5060106050403141513050708030a050406030b090103050c04020c0a02090406020403050601060302030c0703030c0507050615010207080c03060c070c08070e060f010f140f0c01060e07021203040b040201051c02120a 93
    0x2078109404c1c0c1c840004105412510b8402000b0916040072010b6100259211303000300c0c0c0039540c864a466107560000303012540000d0b40002c0500c005541760140c0040c0150a4402d001321394150fa03a8540c8901c080021140103d9021070079200f00d010403c00090349a030003800742c10443c00c05081c8000654000c0c00b0644071b501c110000014200d01c42e1003104c0c0701e41c5e010301081c0c2c01c150160f45c0450160000c2e1000c00d04000303060004502081d020302042d0700a204030808914020034075800a03080c0f18042d88800b000b604403500500b65a00c01180c1c1740e82c01381d1084903c980d00d4591703140c8100040c100e5000401c0512845074042140340815110318044c903021194411050128001120180002156000041d442980001000d1710a80103800b0084098021341d041992001d9076508480c42c0fa4000800c0440110901c41c40e5030701440038101d01d0541d00c100c2072a40c941900d503660384d003001401c001e04201d4001800b40c00a00800007610b03d440c000c01041d903030748455862203c032244040d54040802032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 29195446 1250 29194196 29194223
    0x5030705060601140909060609090a060801050c07030531090506040f020301050d1104020c0d02010603110907080f0c04120b04030e030c010c080d0b090c07060501060f0503060409050a05060106050403 87
    0x6000e010704415000e81c58400350b151a0803c02800411b80d4081d240d590000002e018180d015540d04150911031f4044e460001505480d100f102802d485028042d00074000c020441c03140483e5000c3d049640c5a200340244ca00015071100f03030601800d11480e40030f0702d690b01442010415440310f4001c01d000c5c0300c0480707003404800c041601001c01c82c803080c440e40d507014402c403215900081000c00e00c1d949041000740010f050401d01d00c510760a0081030203207000183d660b00028020040c070107401d04a06103054035440924540f100000d051000007074506041051101c3c00a42c4000012044901034243c49d2803891400c0b0310380c80c03c41100001030324110f0109100045c0c2c10707118180020301c0795100105030342d104002401c0381c8a21040303038002000c441c1c915468400050058803011a0980140d017424002c580d1556282418422984181c00000800550b0070404000391340c4a41520b0300494101c80c0003503203251610308103191089408000b44039014ec007000094564010f00030b8012030340500302451245 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 29196696 1250 29195446 29195449
    0x1005100e040b0a11130612090611090a080d050405011d10050c190b010501030b010c02040504050a14030304050601051c0b070302040f05010201020c07060503090f250603050f04080d06090603050307050606 89
    0x103005c1e91142c80480e8039604000c0041c14803940d000c0c400e030307482c2e00c2001898a44a0b21040d0075606035400d814071078400010f103450340b8282004020000c0210780003401d4408081840100144294843d10341000b51060014407503d14007102012403280043c00c0041806540e0000741c101c0e040f0380091200760141054500801c3c0340d041f51001c880368030150f0700c1616820a80190010305110b0307080c60410050450000043e01d80e03220301c0e40254001c10041c80c088040e4036154004900d180113402d000e42080c01404002030000404034151b80c001c0309d4407002c0b0b40c1c00700065000c00b0f1b013a050180c480304145003403013601601a0700400c00e070b801400610288507195001039080c0e203d034030301d1000150720a10080101a1161010b140c00c00ba411042d2180c909101d01070754682001c00484d065107403020070790720880c041c14002c81c40007008079003018400c915165000040d8410014405004281c00180b00485000a648590094060701e8401c212064036410074540d03e42114500715090321840c0c000c10003a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 29197946 1250 29196696 29196731
    0x705060105041b021002160503130806010506070503071e06020d0e06130b01051009080d0e0a09110a08040201110d020a0b070e03030414060403150b0405181005100e040b0a 75
    0x940b00c46400420301c050307809816400070747c000015040000e91841d144400507001340000c000c3c220b030411000b00080c0c00d04c5005400c4c0071040e07124600c600d40801650000403000300940b24000d80041c80501900340d0805846081b504038800140070510004268400110700d9002b040403242c40f0046803d159118060b149444240300f030302805a03000d24004101d5850070f074680401140c40c601d0010802550751044502d000301e262410008140c01058458540c103261411100401d4828001d101d01199004003c0151040d54054410007903100d00050a40e4018a02c00c00050311000448861200c1d0000080d1030f9a0f16540440740207a0070004030b91843e1050300c03910080c01c00100a03500c0c1518000305000008032500b4500e400c200140000004107480c00001da24070400302e1400314091140c1001c00007110300080000488180c0301d5400b000c1050006242c00d00348440500004854895002400c403420665010401c5100640d041000308030103000c040e4040c82080106010382184079424046 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 29199196 1250 29197946 29197991
    0x20301080105040c0509062103040518150609010503061309050607110f06010503060f04050a06050106080403020d080c03010902091309060905100501030206030c07081204030504060e0301021e0703021002070506010504 95
    0x1340811031800c03280f08c03068600c100980001015084901c0c241e904d0300410311080840c48038104143c04d210400900706e201d100c074007100820494102c3d00d02411480040d14a01000d07024901072503107070311500480d481a6204c1010aa000021540c0e0b510302100001d003203141d00280300c10207009000b00f04452442c00164130781038070300c010043c1080390303200c0000f40f51004005100362664440c54030410301007040741c4510b80c043c014503940c0c50040d02d06820301a2401c80141c0120382004071710010012201d16008c152410f594242030090f80c0c0300586400110240e15085245030154a008036000c10404190f0081c400e05101b107060381c2d24030304608043c400311030091202940200d400c00004004924480c000c4c1211031180d191282402800e03240720640d04d40031038040b804164002414080c00340c102c854000001e904600952600c4402e082e6544080d440d5107010721040d4000c03610f081018020702a0802003410403200b15200c052900b0060b03904c0d4401c1c412140102d01d0800710304800041003c1c90f20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 29200446 1250 29199196 29199199
    0x25020a05010305060303120115080c0703020615030a050f0105070e0303040612020d09050d0903030206090f07090e1c030f0c03140402090411060408100b0418030e0a09020301080105040c050906 84
    0x80089140a00640140800501150b0301d40402c010440445c8881c92800780607002002500d4101050b1078005459140301806040034060240131002c00241e00090440c0c1c000241c10109214040c25800700345400000130700103020740104036455410540551200f88120f4903a541c074505402e200040c141c5a01c228040c2c1d0380000c0078086050120401500140452594000002507403801a180e0605100071410b9040029981d80410024558100103581c0c0040c0c480001c1d0485801d40c1041c4c4d5590a0944034583d140f5444200815102c1014802e5100020b20980740414503e1b42c294020010300c0501c8c14001350501d0181511040c5111b4803a40c2d1101d46c04690550090302c03a9000c00c584000000c0c01115000d40168001d501505c81034090001400c50b103000349403a94414001c402a04c84a0f07071014010351400c0c00c41401031907000d8820300244e8140c20300c00041a580c001203001440150070600007640000000500040e05500582c4200c1c0030342c03981c00615855008000c00804141c0d4000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 29201696 1250 29200446 29200459
    0x1014030312040812010e07080a0209031b0328060609020702090720010218040518031603020304120f02010305060307050603010b090a0314010c080c13090b01030b0409082502 76
    0x240d40391005181e01d0390407034014807403641408440c182c0c400860300240c000c2c4504801c1c1c1e006009086400451158124540100550034056040302080d0380e0540150440c1c0080340c120080300070703502d0a20106c411507000462a081d061342100c43c0200c00503501c1e03030480303070710f803400500050780c03c003502c02d030785030190700910340c1c60180c4413000c040383d00031190021000f95080ba08412034036058244010441194088141d03e24062641c0800040f220010400d0007002c401c80e020003600038011040f0307840103101d4007982c0030010b0541812843c6008a8000300700400d07400301d0b0b81e82800082040c012442d8402d9905201c5955890145510b41140d8800c0942008051005000c008050ba018144006000d090181000d980791504600c1500011202200d031755220342c00824194000611035200b600030301c500f442c00c2381c08081c12442034100c0c800ca001c000d17036808180b2030741e070f00c00e400c440c10001000384180000c900b1170401c0d0686e540f0104491799104541c80311070725482e1401d5610310b40f040e0018080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 29202946 1250 29201696 29201707
    0x705071104020318010509010c090e040507030314190216140a03060b010320030a0c05070b04030c061418070501230304020103020417010203090d030504020907270e10140303 76
    0x14440690406025013404131090200080c45a00c01d101d0244141c040c80300106503840010304c094040400e41e0400c0c10200c20000410002c01d80016041080b2a454540042402c803c000403c050740144030b440003c03042c600140c060f541380d0006055200d5021042d000ca0340d2a561041121140c42d126012500410703110300400100748240d00c140081c404c10304022800c84081c064100c9505650407004140c3c40021083c820f4190513071144605404945c1001403601c4260744030030520000052004081200706081d8900f00000c0e5040340c490320007000122295401e140c01d2134902c1204480408034584103041e8000740e01c0d8420803203c05413403209052001d00c9680d1340c101c1480c550000b0002c1c0e0503d41c0801001800e07804200c2e100d04400c800c10001a240d06080c1182800d2000c600401003c050500d4240000342c0d03222101103822480c1030500012090804203890345e41d403129001500030381e08410002030140c106d07440c4203104803e10321b403440d0300039210352112881800040760550180d10a208 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 29204196 1250 29202946 29202949
    0xa030e0615010c0201080406240f0801090f0605040c05090103030c0b150d02010305090319050409050a1e050603010609180b0c13300f12090b0a030b060d0c09060807050711 75
    0x680d045409054041055039804042004c0c00f0715007003000c0007136000003004102c2b50814107440c0000e00102c3c1e00a0022a40c00e0f11380c0540c2191109000d00705a6613400420100050480c030305005000160554229603900e003000342010041800540d42400207100042040ca55400c015400540081130701e81c00c8011500110000c00b001000700d40343e88000c1024840e58810903550b00602c1c1c00a0f616103075030b20300702187c90341511805045c01d60f500e400c11181441d43c0c0000d0b4642e00e12500320040001d610f680f00c500090150034254804181145406010640c50301144c080111f51b600a0300d8116003070301c0b2041c10030350038403841c400c98840d14004c030010f1002c40000d2100d52003aa0305500e17505180d08486200030111000740c4004c13035001c10300c0394401e4100312242c189034400b1451411310380b075180d00d0a02e001d1424415941300c4401c05aa900c050001640d6040503030b01c404c4003049040100c082c00d10302c09031881c940340c00340b500454051740c0040c42d81e621440407224142d900655200f051201d000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 29205446 1250 29204196 29204207
    0x110406060906050f0405030601030c06020f010b010507030f03150b040f060504080c0f0307030c0b040e0c0a020705011404090905061005090c040303180b18090106230306060f0a030e0615010c0201 85
    0x800300409110100b00014860347d0030010039001e140201428150945080300c0a49050511080001c0a90401403140e455030303017000a0329030003501400c011842186004045000788107605106a10408240300801d00c1c40c5024003802c161000c3d071030010313030070b5486100a848a00075031140715a1a800b0101861070342c00c0001c2d1400072840090f00700d821650700c0e603498545056960300f000990b032402240412000030700d2003105401c503110300c2a0a1070001500300081d203444041c040c49040c03003802d603100d031040304415048030010304040c002086044028034001e40c47e090162008503800d5642070001c40c0520700385a0284c069580c445a0034a41460341d0340c113841b0411039000d04401c0c0b0315445d50024021903405c00926100e240c0c44203441c00400c03d00c0070402a5403044c1c10a02c2000000707800281e108078094010150402203050981d146c0d0b41d0700340010b202c0d10808040ea814040d0228510705103d070181c0204903882c45290a03601c031a41c46418400c50342210510744c3c0d001401c007518105c055401039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 29206696 1250 29205446 29205457
    0x609040204030209010b090103150e0402040c09080f01090b060103060b180d06020a02030702030706081905130f0b070813020d0f02011205131109011a0a090305061311040606090605 79
    0x28101504166480d00001c500000c00d0380b007492079000c0054040c0c2c070340d84d01d8800c11041c0e02162a401078010b0412a0018100d100200020700956489000c0c038910350084800344002c064003000c44280006a585d001d001e0081e0704230403190903000101080c00c0b90301074007400081d1043c0c01d5605040c80350070070310030405e0032032032a440350041220840d01e000300360540010102c40c10316400843e59403a40d0710505151200d1948903108000b00c5000344448400d1911080400d4030075510f01040e01e0701c03402188082d42011a01c0248401c80303070080030007080340ca08034980c420300480d19008402e50f950100b0218005240034025480240d00806c0800103040041d058122401032516001e8100e0100400b01200c3c1c2c15200d5851a80c030103404002048100c511001080d04242c81c2c1e0500703945400804030305070904091000b41c55401007031300d045043c8901b1400d401190440200d401901f40400c055001c00ca40c418141c0741c104a04041d04000d05250003500d08070f80c401d580d180c3c0b05500e028011a140e4229 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 29207946 1250 29206696 29206699
    0x708030304081b0a0f140f0d1206050310050403080106020a020f04020304150501170f0312010614070609150e0118080a050f07060606030b030609060705030601050d1806110f090609 79
    0xc1d25001c0300c0d21002c008084e0710f54490712070034685560605104654124540307031064581d00c0094082c44109000ca03034052906454180070307030700316040a030000240440e0340006405114014035514442e215401540c01540240c944a0250344ca51101326180d500f600c40194101c01080f1007011142490346c02194001e0150074103030010400d105030001a82c41c20790045002043c00241020080824030680b80030f804a18000c5140c00d00b50b01003070b0f0319a101485084184121409500741c240e03420000c58109a902040030070200300d49182c260900d038055040300c41940d00c0c00081e080510014440e400510742c0f25442242d0034400c2d9507030401d440e4400750341e40c4100002400f03905190700c19407000d01381c154404c40000c07038014208107004045548404043e4401c0d4400b10903c98114008501c041d00098070b80b42c4142e0780e81c3e0391001628284640c101440340d0744d1429001582640d00402c00b000014842c50050190546400c0c16480902441000032045002044200080c2c500040180b5102c0070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 29209196 1250 29207946 29207977
    0x3060405030405150c06090703030210020403030e0d0303090506090313050a03051e010216060b041401050a060c02010309080a031a04051005010809150405070e060411090d03030b040612020111070803030408 90
    0x41000c185420006c094550703000640c4801814801c250301402880f21031040e205c401c5040070300e5a1801820284401c0340c00b8080d01000301e190b020b15100c0d801441010f60014202c80090a200c05040da8903400101008050407031142c0105092809003108001c49030000c0040c103141c07103200d4180361810400380e9202880d40d400c000b8282d42070650041111164060031000a06001e00c8050105585420f0880910300c008a0b0040c006035403020b001d14140c5880c0e2600711020740c030520040c1c0c0102703034050000d045110046042c40a01e5407580060b040381044851907245202a0010300003910416201c80e480304420250038051940300b00c1c2e16039402000e0000700c0d0360805035204481d4101e4400d0b501510250860340050052402c403c030030303a030001d0090303504106003410700064182d58001e06003240e100d58200140d2005051003a040713007056640003403003040015074461404441b02500d91040340801c0e5a001170644a104c007007050750446034914003641c44e50350741c0e54800f10307158040040202ca144 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 29210446 1250 29209196 29209207
    0x70e010e010e09090a151104060809030f0f0702031903300608061609030f02040903030e06010b04051005120f06060d0e0102090a090506010e010e220209010e0306040503040515 77
    0x43c3c65600c0d01d405a9180000b9007842001400d00c2e003c20080340b00e81e000040c0c2000060446c1082e401c04560845249241042e01501d5040b00703d4294070a1f5895160020b4000c128400c000e000e05c8000c001a92007281160240346015080444450181602501140b1000f02070b40d2200c2d04454a0507409040070b02c14110359052102c240110342c402c0e04019017540c020410016075218003010000000020700b082c015191640da035100e11400c020400900450b2250007540425001e5000020b0040780316090303a0b5250385076481821075800c1841a03900c14058a80302c0111a07000314125201e03a61441140b5080f9134891030104401100588800d401c020100701817080303e1000d12405590b402420000350342d5010b000c0070842681c1081d0040d00e82e40f480e002c01e03c0503030b80e0403000e140b1062000f0b0900c14010440d440000e40240002080154105121007400c4d0700c0348800d5000703103071105c0262141d5021404110a03d5900e09046400610b6a4000c0000303114528210042240c501c41040e40d0500c0c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 29211696 1250 29210446 29210449
    0x5180c0a020c0402031003051e0a111f08070801060c0503040b0f0c0607170105010302030108030a08100807030506011e0e01030605060d020a0806100b031b0702030109020d0b0103060c030203070e010e010e 89
    0xb03900c01c0340d06c01c3d44030207420401d1040140600c04614280e800b01c5c860712543c0038030948191200e19100c001404880e405c034014007541c84510612040c8425807817607603d01028100043c28850080b03504000003422180040796850003001c05a502c21340020085060504140d2062203c0e442075106503115207040c020059261070400465202e030b145030b51807001c1288203600160754100113800140c10b050051005010000001083d940b003040c0600e0045425222100c1010b03408040e500205214000c5c414040305000000800c1360407a481141314482c2c0800483c01c3c4000320810b400380407541012040100081500c40c0c1210303070040d00040c404149600b490380080c100c14255403001c0d80c2d40e004038007081105094010f81d81c0040011800c0c162961401051303501c1d01c85101815001420800f140c8802591000d502c1410f5140d406007030034440114070309140102d510309110441b246803e1195030041030388070f8000c1d42c6c012030082e106c0c01107040b511001035800d04203c0e01da0a042104800203640c45 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 29212946 1250 29211696 29211701
    0x1081902030c2713081204020f09090f0c040903091208090303041d07090302090601050c01060e0a0207020a06020307022101020c06070302030a0b0103110403020d03020717030405010905180c0a020c04 87
    0x100e071010329046404511141410040402048141e51540307050b02c2d5008a40603008450381000d000409281070754823440011503d18000724290342010001d01040043c401c0050030403101c03200001159044100d0104100545240c2207005001561340541084482410124240d041e8841c4081070700f08100d142c0072078a1a003041d806029541c07884903290b65092800b005030760304601e1524284041c5800c3d03802040f107100d0040c091504100e0001589015032a0030342c090000f40c2010701400e101424200c0c94280690401d85040c0e10a0961102c0006d00600000481e0b107500da02500361001c0c00324800c00d5400e04031117403003c0030b025502000241c03481102402080e121350401c7c0c40044c3c40c0d0030300440240854600e924454149440c2121400304050410700340c0701107a504413000358014140e403078100c0c1800074592000301058510250a205410040b000e40240c4400382e07158100150b85c2d404000920f8180c10f104013030039081202190f2107039a41030040407846010f004a420040c13503000072808 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 29214196 1250 29212946 29212969
    0x706090807110103180206031503100606020f0a03020c0103050606160b04110312072a14010206150607200a030305090a0905060102100c0903080403120201050703020301081902030c 79
    0xa02520001e200d0040040c20445100150000c0c41c041100e10000a910340e200a030310340d80a4400d0b080840050381a01b1884150503141c0d20150507219500700c10410b40000e00164003400000d8082d002152281440000c0c500075500d800d40d0060407150b04020040d002008040c01c03641d000002000040d1948030a104406078280c82072044440c1d6144c103040041260410b0001c0901c29000303849240100c00c25401643c0c3c000f034020130719000c079483c80c41c000b060f481c8484000c0c0303200e11611040021401c11750141c02c80a14803c2c3c007594113a40c3c81213116a901035061441d607a00c103e06004480118074504500fa50414016030102d5044030540001401241c0c0d07a8011000904000f503200180c1c10040c00c42030041c090403d060280d0b052140010351070310f40006040503400c4d910700102117028401c0794000c00441d00103070002d0303172142c481c108204441209880c041c095030924001c154254441d00c212070417160302401030001b4175081c3c03401c0b40b1480441003041e42d062140c03030300e0381c00103035100e15050700b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 29215446 1250 29214196 29214203
    0x30f070312060501020f03070305030604140112050609031e0a1103040f03050f060601050403030c0510020a03050f0702071401050a0306050603100f0f050904060b01020a0b040c05041404020d0308060303070609 91
    0x1468038a0100c0c000c0d03070b980da00030710f045411440d100c19100c0b0b40003056039003444c0d150408546070703500c01000c6002440c0c0b1003401c1c0040700c18080000f03000b00e0050402c11026010700f0582e080b81d50341d8a40d40c1ea51744250b15005031441800c55050440c0450740010b40300f0181c881ca0301d4030681d50100d105901d15040f54000c80214456000d082003001001c010380030444d8042405080c0345d14000c000038005000720700c4050305204000a68104100c0c0600002260240440045446010070b860003002032070300302c0301d2002105045021989403400000c0540884201d0f84950307040211403401110290000b040d02e00a15848031310100c2e11384d075100003540c403842c41e054144104620706a24654003949503404040812480f2005103c10385882080b05d0340160001e0000c10300450481c0102e141601d1020060720141e060418801000f519491a000701d6134200c0e4144940f02004201c030401503400e80b8001c2d8001501010342c00003c0c004c0c44055440580103065034288010360316400b082d00d0a011045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 29216696 1250 29215446 29215457
    0x12020102012310120b16170406140a0203040c090f0e071811040602062205010216020907020706120903170406091704080d360305061302031e030f0703 66
    0xa030300f0b1002034109009110380e10500316095200e403650144180d000d1b01800c0d48440c0700058401d07041c0902103106d88a60360454070441ca151034141540201380e0070384222030845488007c03e0304c101d0b160007640d0007180c109044220300c0e4035020b6400020315040c20800907180d107480b04801c40000a026040c003c244c0001c808500b02030b042c00040494011140d11100c90304140414080e441d40021804d610003035800c0d20300c0c4a007000581c003010000c10094000d240350300001d005156030a07802c80e04242d1740d100703940075401519510750a81e160002c40c09082c0c0020346070182c0740a0341c2085e070000321005000341028024011000d400028480c400c407025036800d51201d480408000e41600240314540000b0401c3d820241042559521040403003899400c00040b8814684804020304962801001d116800750b4040103080c80602c1078049444140c45500925000401ca0028410301008440e402000390a071641104032808502c2d1712002c00b11102e00c0b09002c2e20700b28400a200801103940a629070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 29217946 1250 29216696 29216701
    0x1407030e030c10090314210d110c0d0302030c040e0106050705152e090501080c01031802090c03071b0303050103050d0e01020304091d010218090c070b01120201020123 73
    0x3410300d00740150400c035028045190f03844034010340c000030030b40c03d50368000f40d0341c010080c2150116180621000301c80e102c0702021303441d12240d60f045400400446884000074040a404c12824a00c00c0c000e01c544030504c0d030081c0d244441d101c3c0c07182d4002d691041c4411301243c2450f03110006145100026000100421000030b2840d007806010001450300840a008440030b40c0740014859504680d140c28144031421141a000f160038001003d0320040e00000d5070070000c0e580d403801403a6a0b03022004a090100c0d01d0640031003c2002c84050410002c0d4000d451002c883d15400c2c4a07409941c0010441020404600a915001d0012024041c001406681d020032a5411820a0b03410850307110100c0040c00f8084042c500030341d03008020389046807181140066100000c00383e02c001940740313140c061603552002034982d241f82885000d15903150b0040d00c603005241d89218589030f843c440c0880c090041320b031813001040f1142c0c41d00c11100c07005106100100b00c0c0c44144102c07100f141902d214860074414807008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 29219196 1250 29217946 29217949
    0x806010b1209010b010e01030b010203070b0403020c12010e030f07030207030803010b07060606020c010206070e0f0a030501060603140702030d0213050405040c030314070201090509061c032a0b0a09031407030e 91
    0x4441d400c115840000c1002c2520b4400281206e000901114140b58032190151000e031300900c2650398064002020700d48030718161400a44501d00c0e00382252080da04841c6404044605205170698603c044000b180b400040320801040e580165004800314800c0074004000500b62501560003803001114041c4c482919240c500c0c02e644c96900840308541c0941000d880da03a13800074020b41c008e5450706250124488d02c10111b0f4802c01d01400c099044190301c640042000f4056000c1c4c3d04541440e6400c01c1079440c0e80911100209040d965100168403d101145805005a0003400d5009501410ba07122580e0b650104055820450301581d25106000b070400c141908007964000700c003403050b0340620f414910f5001070000c1c0e50310700640d809886c28500040d5542c880013100c65154403039030b480b0b46d100c9682d442c0c01002d845a480c0034880e0101c0ca4030380740140c4070000100340c080d01da00c00741c2103003513035500c40d440b00040c807110405504110705202014110b500d241c00914581d03009036034900d0740c28030440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 29220446 1250 29219196 29219227
    0x41d0610050402030601051222080d0c020a02090f0910090303090b010e0c041a040305341d0a0b0a060c05060105090f060126010e070e100815010302040806010b 70
    0x30710079401980100200b00550b0382c00760850750900d43c220240fa003552110800e900c114140210381c600812050140c1c80184948480904601014142d0a01841d00c910a08980b505c00e041402500484e03d01d01103841c1e8034041007069444001c0c0303402c65260641c442c1c04903017501c48611060b1301280d80c8251917010704c60010070f05230141c564041d80c01820f060484c0c02c2c0b0000d12903842031540c40e810041a0801c0d9900344400c1b500103540000c1220a00c8104540690322401e0404214007600820b080441450f0310f070503654070450307011446210001c0c0e90100c103415a0f11004085d5603035a43d44800d84925682c0e10541c41000e00710541e00c03100c035101c0f10300e0000e183c284180c201d01c1c8a0400d0300e08200d100c0d20500c21986d8801002e180000e100c0c202440c1441517a55129100202140c80c0000803c9400c0e02004481c4940d94940c0d44440d0b0081700c0082c000311040e54410840090886400203210070707ca20900c070784030801850300602c0d0a035507543c0c8a05010080e00840e440032400110850000101c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 29221696 1250 29220446 29220449
    0x30114060405100513020f0f0f0903100603030806010507051c020d030606022b051c0f050f040209012918040608070e01060807030608060702010522030e0f041d0610 72
    0x3d902c00f00640d420940010503681c80140740c8401c5980014a40d10041004070956000119510010f80c480408800410803504400c441c1402403044821103560b4001500031001166015110540c0700d031a144011034841d440310303d0a0310300384168550700813411b24482406841c03040035400340003800750303000b401801e540315540220b0843d4840000c0781c03000c504803407150041e04440d01c51401c120403500800c1d2414000c41c60038065400301c40b10072802d040d1480e042403a100500b03d10401c040e80d18029241841c0d40242d4010b50020f500400502000101c403c1802929848603034400708098126074048141e8081c19000700c200d2a244a02d00f40c5007031070f01820005e004504090b065030790501c5552103d0303410510034241005200d00100364001c1c02135000c0009003954406480c1c0519040e074000c0c0c00b074003050700c0607280c10040700088100001c0b0081c400c00ca1a0303066885100680c400c0c010004105440810f4541c4995198181340c2408c0349911018048540400074040c41c2c42e00c1402c500801495 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 29222946 1250 29221696 29221711
    0x140a050612070b0324090c0a030c0f0c060b040204050303070302100b030f0a080d0b150a090f0807030822030309030b0108030708030c130504020d021b0109030207060f0e030114060405 80
    0x66024083d1402c15030589a12040225055645200c0c4480c22015020340c041c0082e00030f04644184980041c41100806040c601c6031824004003100040c12246020b21062038000102686c8440c400981c40790803e8180102c02800541010b45660010782107030b001a03004c4000d64070040c080003a44e0741e14041e00311003001c210045c00c240703900c0c030111580303030424407078018a039450010b00813090b8a96640b0200d0710f84005484400c10f03c101074020760203580600005808108480400921070000c0945a0309894000f40503080241c038694600a440e042900303c2c6201c00d80c2c500082450038100740b566402140665a4003032000c3ca103041000f0f1000040e040f41c42203400070029100894000c100701d0b034000380c5040e01d16a84081001911001480d03542103950300900000d0424031801c0300340c01500f00e848800408101c1e034000103079698221020b9881c0100540c104a200f0003119001c1e0640725844440c0741858001c0340c018400103821560b00c0221868034100354814000f841c2042c2c401d141c0e000e00d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 29224196 1250 29222946 29222953
    0x6010e0405060612011407031a0405150d0611070506010f0b120103020d0f0b07081602010926040906060518030120031e2508070f12140a050612 63
    0x4080d01e030365071078607801041c0a010b04c03824078104c01c11410035444501240c50001c1c4c40c070001d0900c034100a000d0840c0840d00245402070459810552802e0300c1a80d0041c4481c240c03000341001e0130000c2c0402d041101906a401c140d8545d560088031040b2401048001d220f400601300543c1080542d50020a098112200d40442803000050182e5926032640c10349804980a44511b0101d142c502034114140314010100d0307504070203100034a90000101405007181000c0034080d0020b401d0124200c45000002070990303641c000c840c1001504000d110b03442c43e00c00a0603945400c2e103c284600580301d07030340d10a000007600041e085170f0247d00240381481c907840440080c44100f59800314889130b00543c002c201400100000420b071191a114458005e601c52a69050b48038034110400304021a64803042a0700260ba400b40710241602c1076500300c0c4a0740e219198484030309880c060440b0104c61061400c0c0607140d0301d150b01d101d00344150004500c03920928030046043c2c42c0040900c9206d900910352400c0b40d52 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 29225446 1250 29224196 29224201
    0x6090302070f0605041406041806050109060203120a05060f03120909220201030e0c0a030b06030c0a08060109020304033f02030601050702061804090b07090602030f041e0e100806010e 80
    0x3540035080b2012071b40c1d00c40c10351040c0c500c4034001804522980c3d024000814800e4000400b150540c1c20071411918242c0301d10a040c1e0b82d0308400c2e0b03280d10405002070101103807540050360311650b540c44990402c20180c04505c0c201211b02c0484c0c50003c51403140d1f80100c0012800550303d28014441c00e52203908100c000d003d400d420b4504054408100074000c2c149501c4070704646145e171003089610f8100c10020000d1440b01d41e603041c590042001959002c1c001d0140e025440c071241070111001c0112140c44004144076071030818108000d41001d03004901300400400c040c4854100d9220041c4c892001c1d140a40030120b0800840305000599040c004401d4014020440c0c2d07aa00007003035030503103038050724010381c5e880c50301e942c40e160312074980c0d50150301500d0500c44800f8440011400c911601e02511001541a180c04050782e1380e00500e540381441071010042030098800d030500409441150008410f41c00b510f900725413105000894801e068601d89000030040c000c0d0411006004040c3e80c1c504d4102030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 29226696 1250 29225446 29225459
    0x70807050d03030507020109060203190e030f07030f0903021005030108011802060a0c0807050307050f0607050301050a031103010e0d030c02010c0302040e010611070e0106030b0108010816030b091005010306090302070f 95
    0x1001c00500240c180741d910303c0003811060003908001d001c280d001104664030b2400714010008082858001000716151446a40c0e09080c000102c82d581042d00d00359500300b035402e640480c6c21030401011001005802100000146c480e1523880790f401c0501c0d100d440d16581004841e42c00c480380707004500d0310f281250900d00050389482c41203400444951502881c00d0100742020350b514070802c00010918030000a8a01c14000081001a60200c40e85d0680d005520b031880115028002030190560000c00711408000113010039400c943c2401c1701070000320300d04d070594403075a080200c0071000314042901c41801c13000542c3d080c454414240f101e820b0443c100b03410400320f482c01c0c25050080001b48911074420b08103103541042035200601c038408820280c0e60311060014003038a00c6503140d601245005001062000000c940d80803401103c80e0306840807442d6880c0c004a40d10050242120350049180c04080542c19008403400b0710302500340400d1075452440c0091030726076039610071244a00128802c0c07092 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 29227946 1250 29226696 29226709
    0x506010203070c0e0a060305070b0415080c030126010515030d030603050c0609030c090106020102120f012718050309030f0d02070311040f020315100f02030f0304050106030503070f0507080705 84
    0x1500c0e50314240c4d48555441d004c4141c003c003c15000030301240b1481400280d41591140280705031520a036441100c501e4040099238007180a948480420105100601500300100b0b14041010490620644c0b10b01440082a085500075907808100f061029160a078909041080c408104c02030301d000c2284130b20b16210719844682490106205003000201040c2e42e5800300030100d51100018010841d65a680300d029000f5440034410703664464184002940440401c404581224455400d40c044040004002e184850070302ea6070210746035403400c100d078000d8802400104803c0c440c0c0010750340e6040f040209450000c103605a404a0750100320030455155010402c401200da02c440d162041060701800180030b0080d40c0107082d01d0500c0401007241c01c4442890320100c0840a40b00703001d521480f12400c4070500c003013030908000340e40b0400120400310740b60310081d580103025800014455489940d454107640c0038401c103481e4000c1c17140194080c48024040d032402032401a000344461403030b250100d003c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 29229196 1250 29227946 29227949
    0xb010e0105090f0d0203070e07080702030901050403020d03170a020d150503070e09010f05070c060e060403050322151b03060806010302121009120201140613050402060708070303050402040506010203070c 89
    0x2503c1510b000025500c079030b0144000290700409640005803200d200c00c1c070b505411541200001d80c40e00c0865070460010048030650741041c0e65891805045170203005d40c8000e03070030086080002510614442d04000100c5e0ba01071881001d001d40c4d00c01c1b02e54910b0054441c4440c80d45103403800018100091b035400075150b0215094100c40c03a106030b0b1003141040c01400d1000da405025420001001001a44111010f032014800c0e01c0c200f215052148500e0343d80d0390200d07002000b241c0700f040071407040d0301446203c0e600740025034406c0c0942805940c03038844000042ca0035000007600c1d4980c54400501c905140c110400240c03808120107803502240a43e154030612001c0c0c000d20403090320314142101030288101704004d40c0030a00002e412454120f43d050441c00e030315401540381801a24000110100700d500605000b44130185120b088000701005202c081c004a0780003208000800000f40280080c107640c034000d450010701443c0600500080d1a002030099046400401c194000079a00f11381250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 29230446 1250 29229196 29229199
    0x30a0228030e012025051c080c12060f0303130e060411070b0a0b28060f050c100e0109020d03050d0c110a0b0601090f0909061a0105070303020a090f080d030b010e010509 74
    0x42002c500a03021a5842202c1030250a0303004843c02d03018215a0310a1418136141e41d0b0b034070881c23030340d0724461001d00354080d00038040c1209030510049407041c5004c0d803d0040700500103040c1c0e45804002200414144ca4a0303210100184694081001d586824070400342c1110904a1f410310f0f122030750b904c0f0703503010900502181003107642d107024202c42e44480118529641162582800c10b803e61103003500090702512a0314000364084024a0404e4811001c0e1240c81c2444001416456407400740c003400742028801440703a81d980d403001c01001d81c1d126140014004d0182d2591035852207005c08010644140603c61320901c50051543c030300002c0f00007030688109812200d03002058440d900100e032450010b9106d81210507140c0700205059805921001a040c400c1d44104080c0c09805504101445408a100e0120b5010300144020900035001001181ca651034048800f9441e800c0301c407003040680c3c10a6070a80e0003c6400d02c1815094030500480036402d091611030b20402c040020a64841c1f0490306 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 29231696 1250 29230446 29230477
    0x5100306090c0201090503300c12090c1e0303070605070504030317070813020d06061d060406050607020111010b0904030f020607091a09030a0206071a0c0f030a0228030e0120 76
    0x8034194882c3c0c6944401001c140c2000300e11500b0b09d030b500300600d90040c18245122210910100341c40e40c0e000a1b200c0c400e0103002d8450b0241042c0078003000000c01c079241d11550540070030420a0005140d900c6140d105802d80e4490b540c4070b03411400c0040407000400034038949910700b4401e006075190400d8515a020b10040010b12420700b00d840803a00d060151000244560b041c401c0108605441c1103454100380580b82d0403210569500c01000247d070b0b4035104840e0084410481030015503c2580e0140c4110100c500101d2401e100c0300100e45004411603080e80011012154001d1490303040c070009800035403a15100c0c8015040c1800c2500391923408170070002d000c40000703008110ba1000d01c989414190024002c43e182c01142c2040344500c02c0c620f000d440c04420020015a0004801c01501ca904080b24807441c2035070341c0c0c00c031441c0003988001002004030613080340040f00c03082c20310309020b2020400c0d0303000b1600c8404110002c2c01c3d9414004017103e60209000c117a00c1c2c140c901e4003582c540040c9500d46 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 29232946 1250 29231696 29231737
    0x1107080f190201110f0105070e0d08090d03050415080414010c0e060a091d0405060106051204061a0603090f071a073302120a1406010c030905100306090c0201090503 72
    0x680352056a40f071348049501400c848010790351410740c0f103140f0545d4542c03a070600f04c034a69400c002e19070301c260300003c0ca2008240042c94845c01c1600070701c509c20744a402c22907e040e484605031595141003a0000d400200030004000401144076480001d10013010003e1240161001001e0144070514803e1405894081001c90141c3e2280700000c0050222610030015141c0d1600f001d10a440203e40c01e903881d106210000901c68860400c0300c030a0410300f80c00d07490030780340d41d55040702801a00c506202140a0310060741e0840e61340d0b00045000d627031000014100542d102c448641090040d50205800900d280b03041004443c00008940115034002c24a0f0010103500e814010b00400300c0c000c8582c8405209160740a18809078000c00b10200e1140030700c8025600c0e0180c17030080e503004502103110441c0000220324554003503404005641e109091072440a51550003050201550b00c0c1c0050010b5120300302000300d2003035403290170311440051000f80501010781d20b40c01d41e207210310244a0740d403c55a010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 29234196 1250 29232946 29232949
    0x40303020a12030f060f0f0509010e011701060314100b030d020d05030c0f0f120c09010909020c07030203060a061a070228090903080406180c0b09150301061107080f1902 74
    0xc0031080d13402d020400000d0740300e1145102c1d00760346004280d07801c00800350102d060714040701d06034101e828a54189100341e00307012140081d03000e0f11032541803d40d02d8440110020f60350300820300005000a00420308021100d0b1120159401e156110b40207070010301d0004c1e10301c0d601040240c0000e625081c07041d0740351144a1000007501c1143d0b460200d5000c00308440301c0183c403c0009042e50a05441c203090592101880d603415423007040003d6020a84203041000200c41d0307500544200a080030035622010341c1c90300441d051203811581c0d4410181d80d40814040728404076140f989000350f5081c018100741c2603a02003504140f812204072107a8110410411201c105040300d0005080603007024410070344640380181805030107442c1249d00300c4c101360302030b0703690105a115102c0040d080300c10541c0007854100d10088d0350f270000014a81154a0841110401161100450080c02180c0e5818190480c0c0241141024501d821051035034001101104007400d002908a400003407000c8001c441955a20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 29235446 1250 29234196 29234201
    0x91501051c09030509030d090f170109020d0c05030f0106050d02040b0a080a0f2a06120f0501030b0a0606050a08010302150d09060608010f0204050303030c0306010306030803042105040303020a1203 86
    0x20310180c0036600341500702c070401d94480094038010400382c089580654030103009440314400b901600004103914042004800c100e203420031444810300c40006403501403a00401c2a0002000e0706440c00100240704102e68101000054010305207207008100007030a140000701003600e8070070040e00c9161140f421010554840303d0700002803100310203c480c20b00032845c113189075120745801624120841c0d41d40185030306007084445080300c80c09002000550070030b0000d40b0007445400700c808445696050100306013016129042c003075070140314410210720306040035105440c00354111408001052040b610a039030440401130640303504960f14580c580042421f01018040c6007800000c06050100840c14825036a1000c4241c0d240c0364005c3c40f0340100e044801040e44103a1280755050381c0200b001540b204200009917802a00524010a9169481c1c5481441d80c2066034203440d026691254074042a51038800813080069130b00340203042503d0740d01c01940310741040320050700c501e9400d501c00c540039100b603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 29236696 1250 29235446 29235487
    0x30402040209031902010905220e01060b0c0c0a080d090909061407110f06100603050613020403051b010c0f0b0403110303090a0c0506040f0512070b04060507020f09150105 75
    0x24049031603660300d1445043e002e8070108001e90201d102c80c0e40c023180b603052410548941c283c06010311802465802d026600400c040889020507550390180414200c10300f400030507584a0300d10061102e100c00c00108030008400e580025a240d0080b4040306031079070400441000c4038a03806001a03002d00b82d003461401340c2001d480c006100d495202c00c11021a400a009181c10581001292000c040c030750201d42d92884145c0e00c611041c0382003e420440581710741c00159101d6400f13010020b900e680400c841d020ba030803580007162150030107c0c0390400a01e201b0300c9030307990500910f8034035204055034603004041440080054800140d180002c0c050500030040d0703044503c20842243e50707078900754148503200c603001442124070115006000420349080e03016241650001c0c00000305040c581010480006a03404003c04103003c1d0010008039411003034017800050001c1d0f103070340d0395802a901c10040ba501000c1141031003440e0f20380a0100800344000684030424003804d0680d030700d180e40100c807402d09824 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 29237946 1250 29236696 29236699
    0x30602040b03150915040c0e0603040309061202030c160302240a0f0e0c040b010210020c030a030c03090f17040e01080703050f070311091b0313020f0103020915030402040209 76
    0x14002812107410401107102e00c05022024031900007802c10890344c420140c0304000c404890f203020060b40e2405070b0113001c0091450802d61050f00c0004040f444540040b101900482c0c5905800c01006402100c50310211480c40802c624510b07081101540342d003d1140305021015540d0041c008240c000c21409030b109401c18402c2c500c006c2c80c03141d0914902400c8903000030290074843d41d00c80c20180b9015401d4110300603005444c85110140602004121000c12241103119101000c1d503010311910003081c00e0f03181100611303954035034608081c040d20030320b5a85c60b04040c5403e0811000c922000c0e07683c07020b01d901c5000c003000343c400c03400c4172241c0380a0f03a04211240c6001e2000090403c1000900d00203d9204c3d40603a4040451110341c01d0f2504000e21018001c0700c1c3e08035a070342140c41c02d01c00c410f03840806c403040400c820405030010310340382d0021520f4100d40154481c0b0042540740000c602003920313800346001d40c6040003030004100000468942e01440d80f0003c40400c04550341d80e015103101100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 29239196 1250 29237946 29237951
    0xb0f0703090b07060b030d030216060b0f10020f0111030c0a1101060b0a030501090b0105120f130c080a020a170d050304060902060703090f1202010806010c140f030a030e19080705070306 81
    0xf42040320040440c1714000c0e00c244620b10318400068081d00944051f0880a122102d07002803e4035010046c0611041d401c0c0d0181c81c102d03a52500740e9548403190320221090b80140980c00141c1c0c101801c6941c441d10814401200307000300007002a07500115040c4c1c0e541482c00030a50000f600c001b030301500080e00080f005500110f0718105031581a0300060480b1607074001400384c40032810054640b0720030600c0185100f40c07018009010080c41281c41d030b40100c00c8201c1c1041d071010030307103588050308010b410900e420340008280000303603d004120303a800b5025a00000c400140c2004d01e81b42d407000d0303111030032041c0600400014148101a13020b0304103290090026503907801d180c980101079902d80d008442500d800504080390001c098241020640d9060b110194207441307020054405501c81401100d440056500d00510010709204100c82030880200030750301c13040d10030b501800355840100103851691000c40042c110f035680182c80800c4a4001c400301c1d603100c0203810218140401900040e04a60 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 29240446 1250 29239196 29239207
    0x8030705070506010506031506070507030204090f050d020111180f0a08011401090c0203030705070807021009060e01021c080405070905010609090b030609100b19090c0206060306010b0f0703090b 85
    0x1a0800e0040050302c0c03007001510300680c0c84404001550209036030340b0224020100b100d5105040c600002c111583c011300c105c071301c001e0f86d03940042d007501d03110002201c5c2c0103400d0111711704000003013243c0a0f808510780000d2144020010070a0064080d82840111410481d0641d013055200c0280800700d072071001d0403452075a81c68920f654080d1000c40302000d41ca680080000400c6040c0f4810301c0e6080483d40e0185103541c1780d8480c102d54070740001e0b0090313801020400c214001603032070785007815100980b600c411220901e0440013a26050b03280c283c1a05640005460b41a22080384c4103500c2c51820608200740f8130745031420038500d400f0094016a20680c83c2200200d101c5800003414011030f40004c4080c4110b80700801415101c071819030380d0460359031160381d5440c49002e0903003080508003030180200d0202c4103420b0850300c0201c03d0381e01ca40001d50360340030a00c20315a0306000030380c1d00c0002a8001d04041d4509401358400340b0451070590803401001ca8010109441007400c0300007071050700110358498 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 29241696 1250 29240446 29240461
    0x5060d0b0a08070605070803060f0d050c010801051909090303020c0a0507141005030f0c1312290408090103020d050408120129070c0f0b0d0b01050304080913090803 72
    0x812403048910300c10400c44800042c1e000000903040c080d42c00e07640d0b8245c140710383ca564400700d035000500101e50040d84007040090300d494040e00503990701e00030700081100c90046800506010b0060300820700842011043d5410124036450f858215954520001004076903400d0450090040b520003054038000c1d01c1d00c110600c00002024000c1d10f60740c40074042d07465652400c0240a84d070304100840800c4041c00001c03519254018619404001c40c41d41510f0b016403142035229040305500308421008a001a100c103000c224856034031740351441e00c520301c402030030700e84041a4050000c1c001008401d000034801d041e03901c2501510303825102040d0520650425207080d4156400901480e440d91403184000500c1c42103084020260300b01c0312404594100c01d0a44103001d0b940300306002d0300c03815041d9800242d880c440c01c074050000d2a01611003030300c60b07201c1d62002060700e40c8020103c0c1000824030510010039403600464501180480d44000381203444244040640f03850ad101134003041c000b01c10401803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 29242946 1250 29241696 29241701
    0x70b010f032009040b0405120409020c061b041a040801140105040b040c090605090409120203070203070609050f041e050c130509010f0909080d020a050d05010e150906040605060d 78
    0x641e407003011400030400207031204034803840c2840e20841e807083e101d00124021038910001310740c006001c1c0c421340b20444180c2000284075881030348602c9003580e001504904001041c440d00381c00c1203014035414010311121507900c81c640200c0c0603015070b00c658a40c1107a44445048122030003418020000d025142c001011288500800d00c036241c02a030410991016a250512600f14110150703126644814180f4004903100e403c01e60010303801c19503608074007010604c20005200e840041384d000395916040c52041c103051241b070f580102e05000c560b03e414082603440c0d0b00c219248080c140c400003044203180c4c8000c00200d40c5c0c0c080083e11a407608040c4008802001d00505c540549a07070b0304e51602e56500c0611108480034410100844040032081c007048a05802a041d00382c05400f00904000980c0e00b400201e900c06058003010903c00680701ea406902c0d40070381c600400700800f2030056480c0c240f801e0700c40d4580030000300344500b98480c00222240e130396038441030181102804d61030b2299540e01c002e000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 29244196 1250 29242946 29242949
    0x3030e0a1701090309060309020904060b0d02040e1c02060412030c0512040c06030509120f1b06092b050306010309020301110703030204140402071a100e04061506080601090e060303070b010f 83
    0x85d0090008a5a5070180c0034a840d1194050107201c01550389071104802814040740b619801094001d4480c00750765035004800e07260b0102005000d1980401240300c05500010440e007095404c141c08220116202c4a4018000d001504010685040c0131108441621861010b641121840020320040c816509000019100242c408224648400311000c0d5103640580140c5028601002100b4114500b0009403100e0466485c0b001211824280031606150048500c614181c4c400d21013210b9039030741d00c06200c500080407500400c01c2c0400040c001d0003444010070b020b05054070b803d05401191402d5111400340c00881a85039111401d40ca0010065401841445100104107545c80d0461400b842100c1d505c551000b540782c2190301c00081c08900c0e11004080c0d02c01e480380c0e12000901d07000c100f4103407840381e4072a11000a00449026031940040725580207241009920010450103903000f98450003135400d1515103c1d002e583d000f0001c2d203140302d4150024081905d0500015040300d001c0107800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 29245446 1250 29244196 29244203
    0x90106030f05150303070f110409080c10140601051b0303070203070201020f0708060105190801020301090c11010b09180309100e0310180b07020a05120406140f030103030e0a170109 79
    0x10340b602e00703030844000d840fa01c405a06401c1040002c0000301000c45009140380b107038179608500426000000c1c221401150103481c0c150000622240e41501407045060907080c2e41c0c420042c40e69a11030664499034010100c07418888005604101101402c400c0e2003c4101032085960340d2400080c000e4594002c11400ca0141c8110142410404c40210f804400e8400c01001000260710f0300c401c10000c440d03001e00802d510300301410082071241080c0000d40c00391050b0b0f00003046410403540010000810801d5600140c2d1424012841903030f510142d1980000c0d00940e01040d00d41080780850452040d40e0303a090348519024800300046400088111400c10102c098401100307094032000107403081390900c50010317114442d03002d00007114410642e401880d24411525201403d0303032150301d40740175005440021080440c00b04080c0d03522070906040c1e450841103540c1840401c4402d0340380750006000007000e215009481030b0712502c41c404188024940ca960020106941c0a0414000d004d501030a8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 29246696 1250 29245446 29245451
    0x30c06090506071509021807030605010e03031305091009090b0f18060c070f06051003050105060105160803130f0305040f0603020a0e010f18090e07051207030f0f02090106030f 77
    0xa074901c0c019090700c90b5550000c5482958001c0c001003500141507031801260700400040740c0c81e20200702c400c0031510030310250320b0019045060a0000d003440d1a55211140b09030f100700000603c5a440241203012203405840000381074441074400f81d80c400721500310a01280c40d1011170030902801207030080c041c40c138601e10040c2c41c0d111000d00b03250307242612500c5400b40d4004c0e400310b40030ba107410005010650060f000e080c0700700c0c041d55910040c2c900c00d40340301c440307052002c5080c814000d0030b01c0f41e1a0000000d081039494501c0b900d01d594000094142c0141c02c80b003000c400144406580c2802c1c020540d4810f14a00a0440a14020b0201d811900680008601c07440003ca8030602900c202c5103614801e803a032018000ea080011118000d00911050801009608400c1b6090724921140042c4c2540f010105008040c8584140392031950351040b0f11034140c0b03401c0c00e55030346004102c00090303e401500c000181030032401e12000c222023209000350441252400000c65035407540c4030741c0c02c1a010035400e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 29247946 1250 29246696 29246699
    0x110402120115020601030302060c0f04170f07080303060d0605040c08031908060904020f040f060504060b090f0301060e040b040c030807061b020a120f020111070b040b0c03010f0e07020102090a030c0609 88
    0x40703a580001b404001c1c0560300c9800030441d43d82204010342403040308101200d1400341c42d0000b00015800c4040206400c1d40a9031846052034010710150014109800055041d4030705100041c00020184002400741c550b110042014031200d803000d40f01904c282400ca90f41d4003100e1001d044456100e04c480380004524201240040c502030407001c0c0141c1e0018104140034443c0f0040000410103038404260741c554403080090782c0c2d00c0d68020070000708940b400705500e640390b49d020b1040c02503003804000c0c4030780d03d0103200740b103160600103085400c2500b10a075540c0710fa486240c00d1310181c410340c002415400c2c0c0401d0034001c200f4940c00004000300c1c0b00d0300061030301d07000c1d4130f060742d403180c201038020b090840034040710b0796083c0304504100800205100100303548508121018056009504c140d404840400c00c00041c8182602c03041c0d0010314040c40c49207558074050092b4000541802128012070006000c90a00b9100350180e8100c800020200117890740c0e41d1928045d2100644600c0001c20042c01c070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 29249196 1250 29247946 29247989
    0x70f0612090203060a050a0207050609030306040c0e13020f12010e06150a0f0f090e0a09050d210c05091816020c090a0e071a0c072c041104021201 64
    0x3507500460340c003400400b800c0d10b40c05190005000010850a41030341c1c01e101603130224804111650007041640050b40ea06d017803c0080c0070684004807046003e11891100c0f0050036140c8003400c42600304540001030f10b41c0e04600c0d83c3d40e454800c0b424040c400507401000480d41d07101800c081801068211040209800c9424ac0c160311401039140c800301140340a0009164107015403042c4030301e1a054504441640e4a40d0112940d21000f40ca4088021380d0b07511000c01000001c00034454842100c3c14085242844000340c16403407440d999038000220740b05ca90310b0603002d0048040e036284c40c0c4000d05103481001c0d07124090941c48000c48100c44203208a1400e800807e00100e074041c403d040103824916a07135075040500f07000d40034009076100a07204080300020800390048080800302078614002e5503403031804600718038003e603540003040801c400380c00001d110350410b20f11080c405400c412069550f038850501703112003a14950200c1e0858000110154141071030041903060782c604c4569403140c081d42d0076 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 29250446 1250 29249196 29249201
    0xa050108060102030a0e030c0d03030509010513020d0f080f0a020c15040b04030602070212030f03010602070f0f14012708060a060503060f04080d060f081905030a0e03010e070f0612 79
    0x101c0305805038008029410032079200e04040145205c0280448008034246400300380c10f040104400d80009a4440510030403200a001c0c3c0d13074218000b104c903a60001d82540001d55820492803000300000c8290000c4000c100184007600e0703841030304400c1c00340c41c2d0109580c0030703458194026409200d41c015041030880d070048002a901035403007001c20b146c1000d0465481400035405880182ea01600f003001445d80c1c2d84e0100018011807a80d00190750700d079490001b0203480d20840340c00c09001031400321b10900900403403150302011a41050603118a04076400e0050f40c8030b18207600c02030fa22032040420444500360500d420b40841c0d41d0038080f01c2031651390480c1c0c08222070b424000c00c5d915400280100f104243d03825480790b00140214001c48c070f091100740041c000c80c0c0e52907020303140c8505010310411a03400d041c080d81a1500d43c03035181071090720482d91059101e2080455030018004112540e4003181c800b584280b00c18035180048404454641c1d01031004003001c0d00c207540c0020715090084030a4040360 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 29251696 1250 29250446 29250451
    0x30c0c0b0304060e060c0307030b0a030203070f051903020907030c0e090f090f01021603140d05090c0f060c070302010315080a06060509090304080a0807020d02090a14090c0306040b04170a0503060a050108 89
    0x281040e0039a08c1d10081140074090013481544d000102035408405a9010310a220090400410f01c41c0300910702010311101100620400707985465024080015072501110258403006a150008800c2c03540081651030003c255196904010036404018051403481c06181c004c0400790100c40c42c050000003c1c900f80c3c17182c801204480705800803010000380c001d850212030f26001d0030440d4107122101c100c43e0201c0e64100d806080c035900c0080a01c6040c10304241e900c803401c0b0240d40780c0f880e280e0304150050ba2507942b440000e0400d0364842d1240c0074561440c070224054682402070340c105900901741100581298000c01d4812103c04000c07410400d00017003150100c8608a0182c14401000c0e00d40c0d90b8190841351040c0d8020194419030b4005030b550650780c0c1e01c900540c280c00201030302100d1038442d10b1040200b03801c400380c1c0007210800725507400003040740d40907900420f41c00c4c403507a441c944101010f115240c000082c1201181101c0a540c00c1070165101d144259030881c50f0702c0c0d4400c0111001c030b100307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 29252946 1250 29251696 29251711
    0x4051605090405070201020c0a05070303090f0b19021c030f0605010c02010801060305060105070c061106180a08030402030a080412030806060a050301090902010c080f040f08010506090f04030c0c0b0304060e06 91
    0x42000001500b055080303180d12000e180001802c0c000c00d034a1090a2400852040f00d540e08520028170406800007448000f518040039003800c07031410240400100d20640d040e009501408000324580e141c42003210105010981c46024140c07815000081d0182801c40d030102001400d214010840303521511087c404250165640700035a4070304642600200313405401181002010040c103008500b14100c03810080c03299030794500f100c507030035500503050034005401c4203400300d00d07504080c42000c4002901c000c1140c1180c040340c3d6036201e40c400685050f4a41c4001440c00b6800700380003a0710341d03000c90009076140c001d464251017239441c20100960342c8590030003c0013080e000d10040c0b0440d049075000c603030740920604160080c0e10180c2c50300c42840d046640f07011520305e0005400e0001c0f603a8051010010841c450090145083c82030010b41c0c441001070000044401d000000f4003803500c00d404890500d03400c0b901a880d070f141c44007060b040650041380c05680c0181482700e180e002d01c00010740c0314410807a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 29254196 1250 29252946 29252957
    0xb07020609061b0304030b040b07030c09050f1903050606010206160f03090503070605010b0301050f0319170712030504110603100314070f080307140307030906051e030901050402040516 81
    0x4100800c15142c006807522611070140480d00f1400d08070400040c4040c0d4096440c0710b415182c01d14240c042110010500b00c101403c249849401c6500b00d40c845003551411112482e80002c000b001c180c444003490458910600319407400403d11102040c9540184402c1c0d00795a42c5503100c544030307003641485001040018101059000c102c600c00e5018000c418400e00c107891409880f40c84d020b094407000e030455119004c1c000700410036443d02c502d4144811400394050140c40008800c510032800301900090400c0c4612607403c1c1031510194111401150f005410881200a8a070020010310044404947d0044105a1101507280c080152485400641d486404a40c21655070380c202522181e162102c0d88610f043c0800c800da1400306c0480542010700095441d003056090031a1241403000c0c2007000c03900108206c0d07000c03951041042055680500300566120640305c0c610008010440b81841d800f280401880740482064104e9130185000711000c1c0440d032034401400099404640c0320101144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 29255446 1250 29254196 29254207
    0xc020718050a09060207050c040605030d0503040b130f0503030105040b0f060702040f0f020c010e0c0405010f090c0203090d0b0406050c090d020f030a0609050a060e01020412030c050705030d09030506010b070206 92
    0x2000c941005602015004003c00c100b545a40c400781640c04c10082201d164015422002e4181040d2040c0c1e402032104400a00009200710360113000d0b407001034000303044aa203183c00a14045002c0419083d240e50010a4078042d1203107040007a00c9400a000d01441a0305044a03241c0380d01d024a0034104101c00113100314036101140d403c0000800000014014030f40d290507043e040031000d84040c0c00b102d030480d00042884000c80f000f0501701108500d038580300e145868010301400c220411290b082e2030380220b0010b00081841d40691641c01082c080b80c0d8003000c00303003d43e810054000000c174026440781c04144000e03182c1000001c818041e09200c41e4010b203002130300030f0141c500b5204484520700043d048c0c841030300550b12080f01340d40030b010003a255540602d0078082000b2192040c04032403541600214200303030402404424608580c2000750401801203d10b006020080c080303080200f800a045600d0311004810150541019110070b03280740c010440000748140600c030850720041d50050400e031808 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 29256696 1250 29255446 29255489
    0x804090c230309010b0a080a02090a02070305070b0c0d02070305090310090201021906110408012406020d080612070f05011704020607021908060901020d0b010e0307030204020a27090c0207 82
    0xa40000300300c0354556480380c420f811546c03140300c00031014008102c0079081c2482d0300d006008078404007800804440e441040b101c0e01190703000c0259101254007161308a8940c4410f1000c01c80c90103413402021641c0d20000d00c06c410960042d006000c00e40381982a1080c044200402d5800c0b01c0756014080d0140c0c0006d8070a802c0b041d45008440c3c69503100b243c001814000100b440400c640164000508a03951030216511400c544100b041c001f4446001c0c88840b21704064000b5101c543c1040148140a04880410703400c2ea00e007031110181d200c2c40800c4406850740d580504001d001980324030780c0800c07aa00a9000b642042c10040d80c411600644103502d882c41f10350038003894021107200f41c279407220300312004150800d00740701050089014000140c2c0f11304c420070a0404a650300100e06060154040d11501a0340b400706902003203d404580050316002c4e064025604000c0f18000d0b940400c1021120314004c641c106941c909072468000200040b18205005a030f50380064003541c05410603410241604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 29257946 1250 29256696 29256767
    0x50c160501110d0212030709080a05071a0304050a0b04060f050a150801061d15030a120e0603010e0712020904150305071d010320060a03140a05010b0703050c190804090c 74
    0x5901860080700315503944601a040ad2081c0004032800d4002c88410003242982d035070303041d200340a80d00344540365041c103640b62a03031010700074801048002400e0004090041c158000d00b036485a07420244294a04a00113000a06840108006c81e03280c0140103d234041c414400e081c10b071040103681c844401000340b040c1c07215060041010200354501c840d4002d0030b032001d0240f032640c2c5111f4000c038454483c400001411003d1039014040c05402d041c80104485080503003581e800100324103150743d40c1c10040030020084c0c4141c1032216009800c0c40c010b031440d210303412071001c21030340142c0980300b001c0d03114000b50001d40400070414415554650041c00455100401d09800d000d06c54141d801c03070842000452003d4100d140c03203801003941e80c1d111000844c00c1e030704050341c00300008408120035030400030818914000c01c10040c0801c04040fa03541d44091042102505243e461100103180d02020300c1c0030080c640c0301c0d0003026065404c11b85008134142c02120350a1141da004981c0307400d00194078030442d12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 29259196 1250 29257946 29257951
    0xa05010e092d030a0810080307030e090709170705030606060301030f120909050f0a0c09050102030412060f0f0213090c0512070e090910200702040507050c160501110d021203 76
    0x1225440605080b06001c000c01c010b00d000299a202c11625160200a00c81c40c15040da10211154000704000740c00650f210792540900c000484d808030302c0d51520a000ca55580464205d140d040c1c642844280501c44001405811500128120340003a5114410301030305000a200017400c000c01281c0c9000004c0b003038525541000c0f404c0c546101d05036039074400310301502d0007501d0300c07482c0c802d0070300074403440804078020b1001a60107420030082503407400000079031728030451003039000c0120452124030401c50540c00c0b800031120490024070079400007107900c4000394401c0c2121112801511000210503816026400d180405502c0301d81c14401821510076038088000c1480c01000144032494100341d41e00d060303590203055118010040320071003201c854121124490001c07043c1d5010440307080e030000d4910894544c0c42d410b840c0441d054990320b04c181c542d4050300c3c01e543d00c40c1c002d104444d080f00656865400c1151300036079402c002d001080d407500b44c80700500e40c1d410006812002130302d40060411402547c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 29260446 1250 29259196 29259253
    0x204090305070506070801210c090e01090803010306020a0e030a050d030c031b020606011d030613030e030601090e010f0209060a0804050c030d0503100602011b120603080408060a05010e09 82
    0x6240600d83c0d51010300f0004c04550003c04601228018400100f80d18500340d4025440320310140c0d4501c2c00c5d2500030484070144125082d458442c050107100c0c9000b90004000c0a0384028455200d5840e403400001940040030b8160000321074680858291400250750703841250080d0103410100700104086000d00b01003481d00c014140c0b10380d880038030a22540900303070f8241e03034a901912490610b0300005080c400180c4d0300040380d506828800d03189a80104110350010603500c10707102001d0b89481c041e90450b080144460745405400000216548140c1000004682c40c10003000b8030301100d10074400300d02401a10607044030701403000a801c01d000302059900f04e400749040f00c0e00d441818000a20300351503040088009203000c4148140702003040d003954050181c1d40003d2141010310a0701c680400c54110440f02000400954254000c410354404005590400f0b85569100d40b00c43c0d181e6600d20003070380c0040d00f9034501000051007c1b00c1c000e82c00d0181b01c00002600042403405600d41c4048041500c40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 29261696 1250 29260446 29260457
    0x51312020118090c02010e01021306051e0310090b0312030406020903010e060a0b1206071407060f05010311010f090303090504020901050909130201022b03020d020702030109060b10170402040903 85
    0x105200540c10707100000500c9840b5011888064168000307081d103204090f07ea0032680144042c8008200581e07014081e0790303d40c0352842c2c070f40c040e0303003144072030106645002003130810004180040c00e080003590b0000e0700c3c1c0b81c00e010f10030900721100707042d660312107440e9285e1080b40c18004100042d80300e80040068000c01000400e110141400749400e010064074004400e65562a0125403402c041c000c4000020500780900f000303240c504000350401c0655942d016000b4000100d9100708000d5500074500040d0700311040101c0c1d85c5a28000500120401d10540815100c81044422511035040801075a80c19956085450319220602000e50003200510341401b00070312100c10143c850100261207841c00440102644805000180c10a801020800e0341d180150000d001c0712840030100e107485c0c4250781703001039640c825003114000901608400035403550919040d0710070702205401c00c90b42b6100484004d40368400e0f501c1e081d140081720281540007089400002809845d00754040b400d25806802e18 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 29262946 1250 29261696 29261717
    0x90e06030a060606020d140301080304030206070326100b030720070b03040818031506010f0903050a0b0403140405030709020705150c1306050304050c0409020109091406030d0513120201 81
    0x920b4166070a40d04207100580c0034030302d00041645e004a0524220400864a03491035041c0a940342d1a8826400040e018220000d00d1000b018441c0850400d10664801184010f001c14520546800e0041d0390051006c0122140410007043e00c0044900900140d01c41d1806801090004841c4040c202d121034100c0c09070034000a601c056100003544600d2007019110382d84c080c01c95803501c1c050186e05405000380c2c030000341c1030281506620b115070012000d0030910600320009508451910136500000e09030b0052620ba00c04100d2070800701405203100c2d40343c0505503081d407100f0314540d010303e201705075140c0d00040040000c00b01a0780101171030760240d000d85e80c1520b4405881d81c981c1e0310507510007802620008410700440c5458031440c0203440c103450098070750708040c1c603443e694007c1061000d200d40da5682e104070445e03028952100017010007003002e002030710050f03400c01c90460b41111118024080c182c645504603124004550300b84030410800d0307030f055040c000341d400b20f0b00c4401012030510001c07030030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 29264196 1250 29262946 29262953
    0x5010e0304090b03100608060411030319020a0b0901110403020603150a0303020714040605130b03010f0510060207080606030d0f0309080d050114011416060f06032d03090e06030a 78
    0x510140844a001254040a060501d8903240c00c035181520801c2c82c2c884140051f25022409a401640241c80c40e14072565000001e41035103d410100b0005041c407081d529a043e40105903900e006000e1801c42e00705e5600e80103154242c505022011318410001c100034030040c94030002564011641c0c120f042c2c0307081001c001141098042c1d40060300940d0100c0010070125a200107640780c81f02080c0e90a00030342c1c2c44c020109500a40c1101842001500c0718103414680c1c5007540658461502d960091209081c071040340c2500240c14012000140a001000310307082e0000541c8a01500d405402030003618020441120441140b00c500010551103103404000301e0943c0000d03012006054200060b42d52615884031100c20544c28280e060040915010a01d00c04881c00c0c4d9401c0c15091641c1d1119186601d40f09005003081540b05a0052500402005100c14544025681044941c40c01c0710703264003103041c007014051a40001c00140b2034600c01d200d0042c007121030542011020782102c004000698 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 29265446 1250 29264196 29264203
    0x301060c030c02090c0c06090304210203010b1005130803030c0a0302130f080601060809010b0d0b060103110403080a08060d0c060c030e040e01050f01050109140418020604080303010305160608060d05010e 89
    0x7917400000e00b01c0400d0800054209009058000c04100c0081d8a082d16000d5a031107828011505890071030801182d603025500c0a4114182c0040003c25484108259070030240c0560840c020080c07050258003c003068510307000045030b0040401c0b100c4142803880b1508210060341c07246030b1040700c1d01d014100c00210400004143e0000d0604503000e80041d604044005010160051401d00d181c0e043c41810010764507a03d0450124079004410082160746080058020700010200c42e009400c000400000b1300116001405000300300b907807003050648888040020300040483d003d0080712107030000300b00090140041594541c0700703050090034045e0f110005000c07201d00c3c4c05015401d035103030410840340e0345d500c8420074007400c401d0030544035803401c0810031544038200405050141c1c0c0d07100c0015018002c1e0341ca040e14455070042558cd601d0380c5441209403690401e00c400c071041d10401ea12a810042c61894840903a1441c3c1d66488650341c0f41c0d42041440721000700c0981e025543e49110108540060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 29266696 1250 29265446 29265451
    0x303010902030f100303080f091204080a050d0504050a18090209040f05010b01050415030f060f030305070c0509010509060603070e06130f0504151208040810140609010b0301060c030c0209 82
    0x1903001601c03840c0444a508990b40000c0c0303410240d50400700c060000940200180d0340003180c0507040842c035a2042c1c545c43c82e00751004190602c0070030210303000403402e60004104c120148240b003910992040b02c10b003500c0301e000710b008180c1e00c40d004510038001618800d1500c1d8010b000704c080400e000c0d0558000c1082010140d40a98103000b8060004007444024007038121280c00a01c6d0841c0781c60b240c000d140341a080d07042ca01c0010180c640c003d59440c00600d41060025000d0b080c404803c2c60b60700c4c40c0c042d07c0e560200c1c004540b200b180502c001030700e14291040904881d4050051405541d03604200450f95000078150760900c0315490700c4c0d6603035895820203081009041c40340c1e01541030400350001031411499000b1440b40e410408881202080100d041c000c407043c1c0c5a84080007a068601140240200d4109007501e01c04c0030003444100380c0b0381c0c0200d01c2c0320100c1403208070319840d0b41040c0040c00768240078449038680c041004102c6548680001714500d4005e140a07400702c10b560f4005801c40505 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 29267946 1250 29266696 29266709
    0x11040e01030209090d050901050a030608030d0203160903081207020a0b150f040509030d05100e070801060e010c0f030e0a1d0402030c0109032006040803030a1b0c0201080406020c0a05030301 83
    0x8100500842c2840030032250031840d804020560301d039005a00500364804c0000e07490401c50302041582d005402900304c01c020388220410b076038468800003035480094100f1114464030319140300c8002c009600400d81c8105880d080750000349083c0f800b001071b401206029110004512802103080042540d00c1d480d03078095200f40d4081050300d03103403104000e08140c8248207248039038501014420070342400411078245079560140483c0aa9420348452044541c030b5024040460007001004003140c1e00c07110f15416102c540e1503a6905100641c0115071070300145600600700700e54440c004000c41d028440003613800000901055000c1c1e15044989001c4c203a0300031046001e41028240310841c0b806019800c42280b081c0f814aa002c0c1c41c5031a0808940501001c1703209e561f40900c0601d06685440d400c40780903020f00d4027282d650b800e000c02800000d110311a4654180c1c505880248041881a190b2060264050b560390401c1e856540f02c00000b9840f07030040200d0303441400300c6d0324000344d02440914001c000c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 29269196 1250 29267946 29267969
    0x30304031d120109060501050f01051c0612080703031404020904150b030a14101103070309030c1e02030606030d0f030209060c070e010e06040606051b070509150a0f0609050d061104 79
    0x42417900c20b080d244183c214500c24500f030b00c1400f84603640301c030684180c544001c1d90021280038002c1aa80182400d40000c1030706405c0340d6441091000d000e0081008503c0b9a46c100705140f4518a00c16402605941c004e43c0842001c010030081074800c0c0d11078007040c48140700000d04145450020b0703d800c147c10011102d00e040ca225908895005000c01c081882100c3c205100a0b2040d55000000c0d100044c40d860515585030385c00401d062060201444690f4441110200c8041e841003002240d202c1c058124428072543c40003130b20034140401e0440d150380f501e440d05450300c80c581d4001d401039000703003100e40d4100c0802c0c0140e0b80c60040410400c03009002034101600254100001109202ca0041c03c1034080c0303040850401080d9440000c940d1840e844140342100881c8003d0000d092166650140c4d0340112850248841407101121704c0703051b0355003200e110300069940c00300e2041c1b40001d403044502281141c8130811035400e0200d8940e070814401c0d1b200083d401101410450681c00540201c40540c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 29270446 1250 29269196 29269211
    0x8190b210106180e0c090403020109060213051309110f240a1b020a0b09010c0501090b0a0b030106030c0b030414030a0e040c051c0e0709050408070c0f0305030304031d1201 75
    0x401c00142c010000c85906004c0c040300c0000e6072407a9892001c1d40d0303140e009682402c00141418800c1d4010080700358055800e554661032024000c030005254001e8620411041d0415465580f00388103010300c95074070081281d00c00000904102000c40702e140d000360044440034410170590100b55401d600e25080508483e02c5002e100c800604554110340070304900e1000645440269803804c1c07080e0704492030101c1e04c50395481c180c00122041e0070140401802036080055a03420030031000305607403054a41c901d080010352001c038209400c3e41c1c0c0920010b042403584103018411032200710000e561141c05942a21402c0c69042c900c1031856021605a0300000c0c26008110720610301030245440640c5d807803820906041e8250030110000c107142034100c0c555955040b203481c1030340b0103010316402050090000c00c034629003428000e00f04d910280c0c003180c00313294031700b004601c80d0409440f6900741c0341c005d00114215a10b82d0303002d4402c5404400b90230030010810261481c4c0b5034845050b2030b03001d05204001b2901c0d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 29271696 1250 29270446 29270459
    0x304050a03090509011a0306010509190306050a09021806030c060d0507090b04061d030f0708010f0f0507021203090106050a1202040c050f070206090d0506040305040e01050108190b210106 82
    0x42d142c54101e18441e900321001008950003030494118080c8103001202ea4a40355500143e406210f0f150f5002d400a004122500c11041d104000108507405041c040c400faa440341c40c4003003181c41081c0001c0d40320b81610766041a200300e4208a583c0008003074115aa062101000641c031a00400c952842c1c154960301000041c580c480c00c1c034801407541850b000e081500300040584100030911100303c09440d2180c91300900d54042041201d41205841900e03812629004c3c0240a0418400081c850500302541c1d011000718a204252040749550301078030300c0014801c000d0840d1b0344050a0120039648441b00032940303039256007085004140701e03084944004c40f0b91052005032130606c482c08091160074042404000550b60440d101c1030b5040703d196554684010019400c04400c40000d0000e02c82e40d02084101500400104184c0345d261010500d180c1e078401c0116441001121b4210000181c0101200c000c8980c1d0085075a800c0001c241e40400c00004240e1500400080510354650303440701d1041240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 29272946 1250 29271696 29271707
    0x50703031106040b07030905070f08030c25050d080d0c080910060e06060904060305030c01060614040503030a0806030a051b01200d0c03051201090207020a05100e040509070503030304050a03 83
    0x1c911801078a0240390680342e400c048034008040c403083c941c440c0300701c4080240510105000c0d2162801040d02240c503040000c0d9260000d064100c014443e00c081d0000c42d000c82c00a40c10502d00c81240803698504020a01180807400e1100300c44640b014002e01c07005d00254003500c5540c41603595146814540b0340c003070b1450250b41c0312002a9240c5004070a200107043d504c07100341d0210081e1490740e511035000b008a40100400e51001e0601c0c000402d112245440c10b4100200700c0307800d6582c0c1c5600400064070407550b48510b128841e41584204426070b500e07401141c1d8980c0c4000002d082c1c0e01000041e4690504180c0c503044150244610042d88404d59a00000c441d6100c8460125130f100155541e2669983c1c0c005181d615014482121903000400d072041c001c41c1c004110107440d8090559403250003001a40011030100d22903140342c10045000e0403c84820144231100f961502c07001c0000750140b200815003e44034840394081c840001c60305071420402140500e1056005004003141c03030800502 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 29274196 1250 29272946 29272967
    0xf0221130e040203060105090910050103050606090601050c1b01030b0303071211030403050a0b060301180b0402030d03140a090201090807031b0e09030a031517030a0801060201020309120706020702060705070303 92
    0x161003600041c80b0260b1030000d5010306541050700c0b00041a01e80c0c0a240b464002207101c00c0c540c0e03600740030011042143c00f0800c18080e48044d20703002c0d49506c0f16401501c8602403c985850964001b459060741c6d03c16100c8114043c4606040004109040101081c1194003411080e2080c0009a8040400c3c0d41d10540081d41c0c01d000300003035402d0500b50350350b0396281d00d00d140014026075140d6010070800e9600f9031080c001603565101d0794000c2c02c8603241c1828a40000c407802c3e4840e004405d01c030504503000b030103038944402420006a5403940c0c1d40070004024550290140e040084680d00070401306010000a0003542c01001120003280c0765682ca003082100b290410303042040764005000240d0000030940d2101c0b120741c2000314245001900c40006001c00e980440040c1400c01c445051811001c0003c0c82010f891ba640d0392403903a00c441050382030744000e440404050f8444210b111001a180d0082e1000502c550405868541c4130707000502140c00104c000d803055080540100101504100c00c2c44 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 29275446 1250 29274196 29274209
    0xc090f011407030e04020d02120702060705031003030804240204050307050a050a0605030a0902061603080a050f07140c07090c0f0c020d02120309040920010215070f022113 75
    0x340e90301c0d603000010707000307008030903008091150b02c0020041070790b5241c0503035400c0303a40c4031070441d00c0f100703110040400d06c0b10aa07240d0025014030004503501e81e1182c0e048034410310200210114080c0741d6901220035220040041d00c00304101506202c4110b2003540a0440641280b4050380751400d003000c050038854207a125070322440b084c0908121540b00c60150fa4116062810300f540c90b41d80701161180648041c50000354822000a50302c03e10120141c502500c46010380d64444035595654494800c881085d122884803800d40400a060700740f0071547c58041903000c08202d424041141c8c4410300e41500c2c0d420600100f0788a0b207418841750761200d107040c1544400c0c5855110310754940c0203c0c94071a08404041d0203801d480b0600190141c04004482a0403c00352080011074a5400e0183c03400b6132050f080d840040e41400c3d0f1080307a40c800150003241c2c100600301085140c8842c282034440400643d105c000f9405100940d01140581c2248080250540e408507960f4500c054103940b00704a0541040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 29276696 1250 29275446 29275457
    0x80d0f020a0615140103021804020309150a02250c03080c0f0115080609060c030406110405090a06030501050a0911040911090403021f02210703110408010b03010f020f0a14040306050c090f01 83
    0xe800c208c445440360444100955006990740c40b00400c1a04066042c002c140b24510810f0602c010450b095004007114001402c2459a119080d11139811030151160040e016041c241420700100b08880000c0050013015002c07544141c0300c803010075003510741711000d083c061601400c00304580502403041c0c0d03503c1061a00a41042d103860804c019003030001030400340c5503039900c5507104007522100d02190040d01c40244a401d0524044071224054000b60008565650800001c076030066100d001d0780340c03110383c0300106500c070b4080ca0381840000e1010f250300360740d16404492801410707115514100d000350301031b03400b03429601d803410001d400b10500b0010506c1e05600c100050102c03090005003070419041901e10036000e0b030b100e501044014013443d4215016001c03001900080710381056000124002c1c080d4020b0140007034400c5032070100d02802604407265a010841c026a0902c0350010980900010300c0311403c040d100d8407003108551084910216402c00001c104040e407902c40b404804100c3c003403801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 29277946 1250 29276696 29276707
    0x606060a08040b070306170105180106060c0609020a03061e2a0305040c080d030e100605010e060d0e01020a0f0e120304090c11030a02030a090b04080d0f020a061514010302 75
    0x40541030001d0020f40344800c20004100340b40d01c03e40003000107100032038600c03042d009118010741c020182960740448801500b110748800c1d4106001d203101304c4010b42c54101c180030041d00e903000a4890014100e80c0b01d424184044000b40c101d20900802524111f00da09409003414040411035241030803813503500070034200702c201e074049050040141c480a858040b5a5442d640f411452010207a080001280103207180314641c0b690544c003015118030b0a80c11100d107a801c000744e6500f214031600030180007030700300311400c1c003d410804001d01c0000883d1200048010030002c80c1822a00a511003100081601440c915180d512192000c0c01910031500b40780c2c00014100f0082e500c2c407661240d01c503030075290001315030641e0056803444120300034017041d26a25558908003e44a5011480d90004a1b101d9400822220640025203094500420040281800c8410160f0f144030741c140c041c0f411071280105420001d0442d000b00c45503038000544a402c1e00f4100f4166400f982884a20223041500c144032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 29279196 1250 29277946 29277967
    0x6150803070c1a090904080c100506060a0f09080601090501170303090a02040e0a0f0b1e0c0d020d0f0f0e07080f0a110109050d030203120c04060f0e0402040906120203060606 76
    0x85404481c1ea400d284040d00919003403e01c018040d00080c9030380480c0c0a4204000e01c812240100040030101040c2e9046404088000382140c4042e03640c40c0e00a80144095881130f070041103c10420b82d0a81449182180d44000052510b4001d81281c1e082a44540c01080180411084140340c0702c00c2401960841c80c0040d0322a66982a440c8082e2040303491f8044c4030308513082407000340d88454004460740380700105820844481c41c03054a81d50090003081c075100800740840314800707004812172803101d80790102007821034010350800b18030900315070303510002a036240455205103c2c01c0c2502c0000030500040d0306400c43d0034141c0c164401d030740542240389000100f40c070204140d800c05074080030b00340c003513144500102e40b007d05a4200315041a95601c20303500b815000000360043c021a0085c0041691340c502280c40d040c0594460b40e004940480956075030103000d99400a05454054401410290781d11203680c10b89405a0214560126209401082d42024401c290b401001030f500e803450681d9402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 29280446 1250 29279196 29279213
    0x6050403020f090c0904020703080609010e07050304080c120403060f0506040c050702040f0902030d020303010e060619080a0b1c0c050a030b180102091009150908190206040e040615080307 82
    0x4600c01d100c1d480e083c000607910384c0740d40d05882c103054000d1300464450440785406011400107a944038401c4e034510700005441c8030302c1c002c40d501c11200c0781d03100382c2103449583c0d034420a034103c000c01d050103024028000110b120503c028000079402180c02007801602504c0d81011204040d0500b801941007401021070150400c0440705902d906480c00102d12011100f040000e1640040c02903041c0250440c207260990f00002841c141d030281d02c11241c5544403030382041501e104011800c00b145142131440c44949009141c55030f800340001801007a140d414200207035040d03840385022051500000d44440a205800000802070403003038504440003411621a18071042009045401d002c2003481c828040460030340640e80c6a140190030480c589010440140c08140b0702e004900390701000540e02c0b200b051040e4800e000715843c40b0003400c240340c880750408410a204510980c0c021030200400a8401c000c030030380c14407940c050007001612140d4581d407801b90901c1130b40408980e170310a004400100e048103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 29281696 1250 29280446 29280469
    0x1b030515030c010c0501060308030c03060307060e130209300f0a0503041e0b040305031801030510091a150406031d070e06010c020d0501091218120f0b09030a090605040302 75
    0x2401c201d040380c1301c40c0c5803150142400b80c1008140c0d04010041c0110511070a01075070249200701c0c1903d00c403d40340c150484040d02c0100e84c0a90003e04000c040403001030560051540381405880207100750840c01141500d00c5042c030a4206c651998540c03100400700c1800941940c0e02c0d240050180044e5949035141d0741c0c0a1030103454229040400d0010380e80e182d101c00100249001d19502c3d841c0d41d520f0415a40b03031b030810108200f06140e0805c0054242d1300c01e1181e80d01c12074a05180000450501994100800c21203c9070a11140e10140490b01c590ba010360707491040ca20700c0d21310b50f0354600306603005040c0c5440041034a000d416029142942d104041038a9003070302d48003030a40000d6178032280101c030383c82e035180d0020f500811810f400c54140001900400031032030140320120003400600d8012070b21207100c40b00904168002034800d0005108000c030348000580204d40c001c202e4486611001520302e4141c0b1a880309502c001950000c1c06c0c0c0001c10000103007054180303582400d2441e00800c1030500c41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 29282946 1250 29281696 29281699
    0x60903060e010b0306131104140f0601030b150301030c050a0609060806060d0e03070606050108060a03020108041a09240f06010503040f05010606050703030509010203040302120c03040305011b030515030c 89
    0x1901c0203010350040962004040781c0d0000c0403111681460442e40c0e84070241088155040241801c0040352400d25001715204040c500c0c2103007041c2d96420b01c4c0d04c9001000502241e04041c0c688484082550718003130100040707200f960120365694590b20313000d0341c880d20075800680280c03103044080200340c0c1c104402a085403031500700842c407030f0f8440c2c0010b6044e219490185150030302d03088130700004002c00000b070903844c0e20400b020445180c49800540348a0400c49109078811441c1000340b0055101d940302c01d400a120744012850842014100c0642a400311160480d0f6480440300040d1050f1590710126400080e08075858071341440840440f9815000f000141441000404682042144500c040760705402a000704540740d00c401000301190300c582c90940c0001c1c240f40104043d84010710841e4010303a496001842010455403090181d5009601ca840040c0828800040410428043c81a00c400c8501e14283d01200090010341250005005081500408184118142ca0020b1403240c829030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 29284196 1250 29282946 29282951
    0x110f0c191109181002040602190206040611010b0409050a0c0905060d060515030a06060f080c0904030c1403030c030a050a050402010e010e030307150c020c0303030405070b090f03010203090a060605030706090306 92
    0xd030040c9500c0030f2420b940301d80c203031842030161070b1440880c2c80e030242040d02c600f982580c0c81c40b0100248403100c04410000650b12400070001000064000c900f00b0300d540294800103c0c1c041001c03000a811180706110555264000c82500020007000030302c080c0c06031102c442c2c104003d0810001150040e0800c45004000c43d603500701041151f04501034154000c8401800c41d20410204e103041401341034203100e10b1244a47d140e90200740c4a034046461026031102030a0f04480d030342e59440c210f94040500308107880f032242030088855a510306200940c843e612401c00a5078a081c4580000200d030b0303009140310310407441c0c10203110050f80c2c00f48045040c4602440c1403200c41001c080028254425248010300b02014010b1035002e2200c640c0011610740055001e8940003204501815120720003100e005040d5000500d044c8500d044100c06003209050240c03990b0340244096000c242268002d480c590400e900080e0b00408115480c011741c00904015405000c01515107100503002a000340401494a40c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 29285446 1250 29284196 29284201
    0x10b07020d050f01060801110c060a110f0406090302030c011103091011161d040c0605030a06030c120b060f01020c04020304060e07260c01080118110f0c191109 70
    0x50318107415540581c2c011080d03c4005002d115418001c01d0705100e1603041d5403c001c2c888101440c1d25094555969102c405840310380d070340600010041c9610310030100c071050180107205120324600098070180150b40c9603148e095003103004242ca480f02d0314001e22304110080c01080c1024001000760360003c2401d0b01c844048540f108802c2d20192581c01180d004d5215034100c0c14a503031503004000301200c0300c0801e40b110507840da804543c8000c00440740076213a0b140c0c1c80700c2000101d1166004641c45603031210000303400341d02c0340e41b10398002091303074401c4070010123403c840010f2281d0040c8868000100b100c008054020820020f501d80411100541c400d03035010000500344901c54200c1d03c88044010180c40656450307045100034540000203c0c00c9030000760558402d00040040c0c1805c003440c0503141c0b8000c580c80c140e51a805510301101030103031641c840c000d410f010302503e80030300141880c181100c0e803101101030540d86007902403150310a8650200304000085030703103400c8101046000395903070141035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 29286696 1250 29285446 29285449
    0x2010603060f020406200303040b07020307050601030b010503010c030c0905060d0608060f01061e02070302130e060f070f08040c120206070f030509011b0209010608100b040b07020114070308010b0702 87
    0x401640e80060301c440e0070001a607102841c00c1c1c0c000c0c000e0740d00b10b848415440e616018500c000d44080300082400740c0c000c00108000c141c602d407a056010900b441100d1404a90756a0b29017803100070382c002c40e1004100d60060200c1d24082c0941d0032620218a0300700006051004010f00e40c002d10300c9814090840010540b446020f160049400381108404884981c24912114844190300344541c1c400030303512480c211507406c0c00c51804e841c00305280e8000d05016081d5002c02c4081c0090b104c26440d140d0f521941ca00d0701e640d09114892241000300a888000c0c07905c150f01800042c2c0d5215104108421386040100269203102c12101703a034400382d00f12100d8401880480c00c0d1b4880e01c1000f8000c02c40c1000e402c020154040000c1107950020f80c0d4402c8200d20039104240c01220040d4000d47c05403602006100b82c40c40341a003107511072524032003510500e5403040174001075402604110704200300000c1040540d44c208c0d00303a41c070745c03640c0c01c5c002c0745003001d6910000d00740e08060048500344400002c5803420b5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 29287946 1250 29286696 29286701
    0xb090901141908030a08060111070504050a0902090a0b01020706020a1a0403020c03070e0601031404031d0102031608030402090108060108030415090302090a02030f01050901050121110a020f10020403020604090b010201 95
    0x1550b1a4040404516150900541e80390010010f0700000f40781000000d015502c1100c100f14490f84940c014200300c2c7c140300801000e800001c02401ca030307661b02c011301409a85c3c0d903100a0301070450f8880c0002d038000004002810200b46403c65400d55110311402d00005100000c2d4a165001400002c00c00d900c692408078200304c0074140081d454418982d001c10300001404600740180001d807070410151500011619500c60200c4010700800d540c0e030815041115800d04160a41c3d50510682c0c0c6460402076140400c0700c000042580d003180048208000c505200c903071280904402c00040601d50701d03151025030340e4130840c016050700704010000409140d020b00d51440c06154005c0100b4041d01d4614540300094004440f0541d000c200400005040d040404249069400c113a40e841040c1255183c40d1050403400006031071070b80d82d940307120000880d03044007a1020300519406070040d04032000b01d0034640700381d5500c808200f42c8100000c100580c1e5020403a070868684610110700c0401140040c2d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 29289196 1250 29287946 29287969
    0x903020118090603080307110a0305040509040f0c09020903120301030b0705220b0a030b0a0302010509060903100c030b030d1706090c0c010501091506030b0a12080d150509010b09090114 81
    0x82d85400c010021040040a102075441001c0507501d102d07940d80c015a045540382039045c070250224604000503c10380c10900d1495600601800e42c00d800000103565040000940754403a03001c556002c40d003028a03260038014601d001004079851810765065403911f13100c84c00081d2451060081c0007940e070140800e9211400821050005105400350361040580040d030305c0b40000300c00003464200e04440380c0ca4604000d0707040d2a010780d101c5040c01424418040e2652000c40844e5152040259141c24034015000e82c84118459540100c0c07548030a000f81072406148213000b0090141100002d2007010695407800d41c004422202c070016500c43c4c50b101407151043e81a010941d50800001290441040c0c00820001c400301032111802c656400c811811036001ca00340b16844100070301c04024034246141e440c030600b40a40165842c102030300d0500b10403151814400e50a449450404101e645400c2110500501c41c4bc443c8500c1c2103051400541c0103181400380c20700200d072006d4a50003d0312214039410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 29290446 1250 29289196 29289209
    0x30c110a03090311040509280602030a140c0408030a030b0103090b040506041709010c080a0201060b040905060a0b0306010f0305090c0a030f05010506030304032112020d05040201080906070903020118 87
    0x14240d00160a004101c403045000c00c1c1d44440500d0018409800c003071092501c24026400681820b1800242d0b0300413060140f130340d4515402400b0506408203503a44011400f5075291600045c0c5016203c0f6015102040180311504855041c8002c010443c0080122841c900141c07030300250b401c07545001070300200614900070f0300c400e054a00f0481041000a1007601950148000c910b0014484021341047d11400003a107000400100b0305400280c0100084c1c030010210b4000032540a45420408150f60015440003411076241c1c0140125818a8040000984410406c0c2071a5140030000a000251251b14800030540c2c3c0c0c03130008900c203400f8041481c110000801c1e1011a0780c0d00e0502014a100040c000d0395294a09004109185000804c031800c680c5d020744149008584049607040c030001600724042030010345190420108104d10080c586c004005900096034203043c00014140200105580d0302c6511400521500982005448041302d0342441d0900803440700107086045160140d1004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 29291696 1250 29290446 29290453
    0x3020d080f16030302091503090712020307090507020307060b1509220606050a09080f0d050c030f030c04140405040201120c020304030506151005030402060315030a0c0803031e09030307030c11 84
    0x21070803d40e068008181104080361402d4400b081100707074030b10a00c415240641c241d4011101007081544c1c500d0359400150000b0b041d03d11644d0f5a0a260069510484520006800c0045d2000800025101c0c03407056103010345007001e4000d00c2c82d00d000c600e4411611010700c00e45403010301d80c0324591111040d0140c0d1000310428444140e036100003400541007513103400c012500c880c6001c5914100007480042c0408004001e00564600e140c0990300c4e9401a50312004500040090412201c11800118050119130030010350720b1740742c0401c41c0045203003840400d10441c207181c180400350b80d01180156524410140008130b88449802c20303440e521440e0b00003480d901072a4100603219003a5a4075011250702a03032161901d2040300c000f124188001c840c0258025810700c0418424450b05c2181107200e84064101e40c0c0e80c08080d156140f556515502c44800ca070320002c20081030380c442ca500038074103860b565000d0400e41021f404054030390000900030400c00d2755640b90100c01034401d202c01240e420320324096 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 29292946 1250 29291696 29291737
    0x209030106062114040209090307051609050a0e06010b0c030c070e0612030301062703080c160801060609090f06120609120e030c04050711010608070f050a03020d080f 73
    0x1a0404200841022a0038207043c8403205611440c01044480c158480e05109690f60307540c20480b1906c009000d405980c0300034800240051010040b9041c4141d0b1962203291061900c403c4d4829220002c094000c0241840680c5050640020702603040d110340040c11510344100300e414902d10700810b040840140f01d00c880002d1902041076880b0300840c01541d01080d0254101400c03039aa00c02031113590001420480ca01c0704012200140070852417104621184856998481c21190b40045c40851005d4010940300c2c0004480c41c030020006050307620007800b680e440e290000d0301006581c4541c82d4138a4542130800c3e109c0c11a03030b010902403c1c640d0060710082c80e05040c20001001c040f001104d080c0e89030313425081d41c180100b400e504401710040081a038606038030188030103800040c00310f60a10803e03034030520b40c4050a0117400003402082c002805201c0ca85600d003040b103040d543c080b500076004410241b015855441180400036002a01c440c1d4400801c6800461889542c03c1d24200e03172000d030403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 29294196 1250 29292946 29292959
    0x1020604241e1b0c0b0402030a06020307050309160b040b0c01020c010e160b12010b13050616060b06030601020703080f04030206070b04032c010309080903010207031106130507090506040209030106 86
    0x10109500440450401800000160a40d0076088081181001c42d03110704c00c0d4000501600c0415070300504c045c0079226104d00301d86d20303442a608151b41c250702080021007002851a02042011240c1461030300e40381c810743c51f041201c807081c450342c0038030344a00c5400201100d000400750102c40500c1800802081000d01000e52613840341c403c1e603080ca10f0603981c0340000401007809403c1c4d46114010b0a00c0c5007807a40307001a842c480e584240a4290b20f401302002c0020103564600191038024044803030074240b041c151034104101c030600c0010038412401071042c82039699000a211003500d83c01682c076581d680c10710b001a035160140303030310080d40030fa000188042003100c0f0020403030181f0300c203031220900c1455420000c054500140c440803040e441c0c91030040c0840d8403a80100c1200d0b405520500d16101503070006c03c2c2640d200d014280e01060761409000c1071041c0c1000069800713208201b00c051078000e01c0e604c4a48840c1c0300d1203a440c3c503a4882012070415512a4105d906280300100200120f558858 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 29295446 1250 29294196 29294231
    0x50f0304050907030509030a0f020c0a03030302090415140607020a2106050901020c0c0f01051b0c030c01020a080405010f12020304031106060a061407060b120604120e0102060424 78
    0x71507025408410200f030895000340620350040114030051800c041c02c1d184119036418865072100e0861062000c03101194403030588240180d802960003580e900c03540e00c1840103884c10041c00a00c0032240410030041a4410207c0d44034103181101c0990380d6103903500004000c40c3c0f094000c00109c1141142c04a486010100746e00001480b40740280415a80c1c1100b0500300c4c0a00030100909410a0403042c4c001d02d014000d50340e420805060460401d240f0fa4100c1d2202c00140121025a605c1003902500034a070410043e00b43d11801d10040c80104c800d682d80f1070050055202d040d040c00018405c402c1c2e00381c01002240400c1c01c03185800c54881c074243c100105005054400f00813140a0480850b1711420002c0d0031700103942450b12224841404541102c0241d8010350061f240c059613604a54070a076a03500e400707480805040d0040203141094103180003602c80300c405441c1030041200305c0c00300f142d0700400c2c02640302e900103a2101101c01c0c241100100110300c640041c46c81480c0403003d1260a4000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 29296696 1250 29295446 29295449
    0x100f11041806060e030c01110f0a080c01050a0b060f0a1b05010903090501021212060f0a06090305060c0403020901060c060f02030a060e010f0e06090a021e070b090111030a02070204020403050f0304 86
    0x10000b40005640c8200030794a9103071040000360960000c0d1460800ca50007a40000c4481c00502c040340e40d4078030401c0d81d15092004518049592100c00104200d410009000d600d0b080110078204210350502c40700014a0303072182030110100d500e00890304010250040c102148000100010b05641030910300e4014001d200404c012004116216404207142d4400a03078200c090b83d082e5086442c140d200c005a60024070000d0100d036000045840c036000f140c4944071110024192620381200640c10342c5009402c02100511400c0e412806210070005a6a051207041c110341e03484c01c1c012003525041c100030010304102c10f4501d80e994000401e0111b0804076500c24021038100c05a0300c00307035980b51150f9480c0c00031b4031710443c0d01030080c0002141061400e0f440c001d07002010b80000626048500b514140c010052080191001d90f004c6002c00a100c803203180c40780d10a03855002000644804a5241c00602001c3d115824056001c10303540b04640700c40c0c0c1220702568210703040f5080004c1c9038a0081d43c82e03005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 29297946 1250 29296696 29296739
    0x70203190c0f0b06190506090607020307050604080102030f01060206090c04090602120f0106020705040915050603030c01050702010c030e0d0f0e060408030403050a02010318050a020d0204020d0203070e0102010c0c05100f1104 98
    0x86040d50642038205d200d0b05015284002c00c2071f4a4079054404004480d00526000da90600900200007050743d11a00140020305082e0000f50b200e1500300c00100c000e43d4161b001900f55005002000301054011490018000003100c0c0014050340500700000240074082d021f6500c0c40460040c0b25029070b10f480c0c07050403100e05908540c9280d4070740040c44240c0341401402400c840126007800607000c03403508540d074001c0000e021213041500b002030b05820b5603030680d00031026075550114030190940c517009420381c010342c0d00010480c500107140020f002c4400d0301405000c0100c100d80344805603a030801102c0051410504894940d03841c4c1c00c2468641da00030100301e0109181480e00c0c0684d605010310000c0301074000c1c2c054243e80748e03e6001e00a1000a074601241d015600b04041200190a0302c05103005484907075591600b100000700290844100030b29501c02c0c030605040c140b001a6000410f102400b419540105400342e900800c00090401c80720078010341c0c2008640440c904000d058001d08441d007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 29299196 1250 29297946 29297959
    0x20c01060f06030903050909060f060a08090d09080a150f140603010c09080a080a0e06040608090d0518040902060408030c10060902090a0b0313050d0e031203070203190c0f0b06 77
    0x2d450105030101c4d585610f00402144080c02580600e01e02164400c0c0e000130098210031414400c0400102e0302c0e40002c4c042e4020526200622280d1401003008078540c00c2c0030305050b54171780d040240c03460383c1c0e000c032980c011320b40301149604101e001c000707811401c09410030342c00030b0005164540c401a1208401c880c440d001c2d41c07800f4810340c421407103032460400b21074004000d400102d805031140400f030b41c0101b0300d04040c80024901b1407100e413680070040c80103050780c2e9506021401e0140c150750920f45200c0c8013030200078051050045100b882c030071450b800d07201160005018440ca20200709140510340c4540c016010100b4900c404541c0400c051050039001c1c82c0030802d0700e44a011030022802030801031900000800c80c103115031981d58004541001140d00113a4030704034282e03a810300c0d0017001e600e2400080c442001804180c1010402d10110440380d0303601c01c0c01e42c0b5003280000c1d0b49019080302403401001ca8178203c8000c90060b07006815281d0818483e0311505058208511501c0c82681c50342d00030308 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 29300446 1250 29299196 29299199
    0x18090a1e060f02040302011e05040e1303110a03021009050a02060a03021b010606051602060c0d020705040c0c1a0408040f060816020c03070501080604021c0c030605010c0510020319020c01060f 84
    0x380f842224152603050b1202c0c01b6070080d00c1a00b9004080800c261424440d04110105007080c40e4200248603462480e42ca0301c881c02e071454024500348680003043d0050303103e084000d000907008034001e52281107510001801a41906207a85130a1001c580a500180d00040c110b4445615030020000c149030494000154a4440c200900320380f0280300d82d400045091280500503680b00c80d50000c01d0380014045400c216100c48418281807081403014096849454100400e0800b401600c44904140c100b9480c1140d06840710720203400e1303000d10010b00c0c48080340082c00308045141542d0240007203401c07519025840e5007024000341c01c141c031030603403074000712400c06241ea01c00101003041490140c00303042028500401500c402501400320348c2e06c03640a1000b40c4007840c442c20071221003007500c44040b500f041c0b00c00e00070f400c0300c04c0f64000c0c504003c1d00003200800300e030300003480350040c10000c10016900d94a010060a40710301d600e2030040007900004080c0781c01130301500154140c0700d914040100d9039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 29301696 1250 29300446 29300471
    0x90f0a0302060a0f020409020d1506030905030304060b150c06040b0c0c1c03020f0a0206060909011103011a070605010b070510022b02090a1d06010e18090a1e06 70
    0x144401880200141e200d50002803807040b0941040b000f91803402d40260a042d02c030140c54041c0c0c1c1100d0032200e1080c1d034403040d03880c2e0b5108800070540100842d003000c01405081d038544a4580c40024806400c19481704070028450702d07034a0390444940384031300e0525203c0904410b403070b4888405440a407601140f4a001c59002c83e8203204a0b41d2200710000200300d02d1100030000c00b40c80d401402030380140341d400c0c411500725644000c000d00748080194090b01c400d150507020000c0000340500386e014281c0c94252946514540c640803a41500c00c04004203c15a11106094126100b8120700030503e50070000009000d00c2c1a42c050304009200364156210102d612082c0c2040340107000c085454001d02010107901490405103280e00003032006009441c0000020210380302000c0b9500022441d10072140b03076102c200d0403031105600030200b40792105110080c03100068210070484a40518a40581e01088840350b0030050540026400183c42842e011946000e480141f12040705a03401c605061400145 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 29302946 1250 29301696 29301703
    0xc0106050f01170702070e090f10060303020a0305030a06051915080405120901050d05100f060504050f011d03060f06010905150301030f080f040f0306060902090a0512190b090f 77
    0x2184043e9074028003a0f0081154105010010b403104095008006010500e1240f03040494840c440c0c074002464400c40c8000890b07e0000b07074841e1589814504081800040d5001c110a81e00d242c26192044c0c41e1b46412001000505056020360b91000c040c0c211088801905c1d08820200c560092000d0101601c0c58410740b800300301102c4c000e01c02e0308400c01000000d08080c000e0241c1c601306140017400d15480e0b500c60812560160344c00d082e10311481b0010080b1100901e8810090402e074034001f82040d1625000c544c41e07032141c8015906002d0080c9500f200255000059611030310020101c540b40d00f80311006244140d001d494080c0010000d0b203000c03c150030b002c0c290b15010410301d00d0f418034681c40c5448540400e04885800c841030041080305c1165505105c0240003d0619500c1300900d29182d4a00101110741d80c0c1c0c07010542c0f034014442d030342d115a500300c620011200140c484500c805540c01e003c505080d44450101d1114101801040600104800d0103101d80c50f00412200241005082c20f5075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 29304196 1250 29302946 29302969
    0x12121b0f03050309010209040203010f050f010c0309060e01030b090a0906051005010e06160b040b060405010905060f01030b0102070f0b0403050c0123070c0e040803070e040c09030b06030a0209010305030c010605 92
    0xe255040031030a80020310803001558004003072000141040000300000301640d02c213a03c00c0c1d029030000c01080c4a2460044139440d0049800d00700340011040c10381e40500200c141d440341d0701c1442070105050300564041d030040804030300020310200d002c1c07038403039080ca0040407549020303640d2519120015038000b40100c400015039030140c54003100900e00d4010491703540e04c81c801c0d451403500300701d0215002070110840140214401c0507a2400c0b480c0050030b00c000c40303c05a112031007141c10078040c0179898540d041c0300c0040c00f0080c0380c08100400d2403030040c1c0ca010090f900040109980ca0030000e903560310103001e0006d072880351082d03031181c003086801102c20480c14000e1981e071080e9010440c40d0740c11444020a032803403040e820780e0511640c0300e0b038209004104440c203886404001040100280c1e120b001c6543d0071800300c804000001034188000d1801140340001041d00700c001c4040b60003a507040000074907250303004100e40c40c00d40c0c50b4035240d0344942021129103415820b029011039107140c02c070503180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 29305446 1250 29304196 29304203
    0x403030e010e0c0a0e1003050f07080609010b100e0a08060109020706060504020906030c13080d03020d0c08040503090114040503010f0204081207111314090102130e0f0711030412121b 80
    0x60307468100041445c01c004d001d419903110702c065920000000d1000c0c40030307440000301000a00005e5203010301207820070a004020001c241d25005c50990b20f9500e0324003444803100c3c0c0d45411202c440343c80000c580c0700308154122910b00d104820000a0350380e80d54000b440b0581c41590f007440389650ba1418041a8003540351126402081440000c1c0e0501869000e070a00c43d074612034a850466894111700e0810070b60b0b5280310002a00069103d4551080d4010405444080c0c54031050790715250325a0307034a902511440c24100865145a010b03000c542009a42c06044c0c000d0080001c0a812810000207510a210710750050007150240200036020701c054525298004450705001c1e004e4400b00109840411680f0500d1903a41221003107208040e04002d1185019500051b03440da2414402c4410280540c800403651580104000b0840d43c0400f40540103003032400c0c500840703080300c21032078250b00494010032650f0280d100740341300f40800c1488507809000c0c42d45a40d01e814442c8407040c55130610740300e40078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 29306696 1250 29305446 29305459
    0x3150901030c080d110c040b0a030b04050102070623010303080a06170601050a0f0803041e08030d050f0a02040501021b030a0506042103022506061715010605070f0b0c04030b0403030e010e0c 83
    0x1b0314a070070b254200340720224005114180e62601c2c0c0e41e0395010200e003a0343c1541d080c0e40c04543c3c0810802c41d8884d02c104000820b503000208a0340d0f480d1401c80042c1400300404003e005404035005505541000c8040e00c404007144684011429003070742e40d96070911a40b4451181c8500004590f14251622410382d00070308003030b515050404204008415905a194003079481c4101c000641c84810700c05824150701290300801c0c0d03410404641d880080016003141070540c13040204000d16a00080c40d01003408141203015041299200001d003410900780c006000d0303014850410040117075000e0380d00c0c2d0b40750b20010807180d8925081000c904a014036106c440a545455003084000c40140d40d0708074a85200350f13030100310180c894400705851103440140d4031075a80200c00580c00b0301d03a0003d240340904154a48642481e1864030f42c81d640b0480b62002814020411001c1000c04004400325005940c10449846440c20145030080042080302c50348030082d403034034260a10326440841e80c200b1084004100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 29307946 1250 29306696 29306713
    0xf06010c0327060305040309050402130512030f0a08040c060201050606160c050a0f08010506030a020d1707020904030c020913080f090607050106060503040b070503190203150901030c080d11 83
    0x1a107440000d00c00980805020b0440b82c40e0030034003144100b014002c103950218550409141c098512821078106500c111b005000c06c01c49809850101812a0400c44064805000301b00115013144510b00780300e81c43d00e00c002a0510000e400c00e1180380100e110340e007400004d03640d50304d08a00720b070f00c203444481c2c1c041e070100007600160702c5c070004611a440c0141d5111200c0d60f920303400a000c480b40d59102004034050044c00b0000c543c828071807240d000000340c1c0501266000c42e40011001c1700380610040100b4407141d16803004402503403d031510154003405071041030400e420060005059010b0491060390984002640f254036403412114030307a809580e0b0b9003081c036100514141504807940307064202031b01344480307000309409008103002041240c4130b00303a680c1130505200e91070280c010180814040104240b101e016101c190341182141c1260380140c9035141c0d03981015445107035061072544403901744004020f000d200c036100ca040711602070445410710101182503c20161100c5030020940003d0384 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 29309196 1250 29307946 29307953
    0x31002070204140709091a0a051c060207032a020306040b0a0e03040b13050102030403030e01031a220b0411070b060d080703030209090109060302060702010c0212031804050f06010c 79
    0x240803164802400454031560800e4a210740400803500a000201000350421007100c0b2845591003100751503c42d01c0309000e000c00441c95400191107014080c2000010191400807034581e542c4020368081000d543e1040320b824024004061071590720040300c800594840210b4000f00c1e0000c0b03103039028000d080701ea51151103007640780c2c2004085a0001da00e40c10b076a0341c115000e04c01080a40007030340d4564ac0b80d4414896040350510070340c00c164155030003080300b8070200341c201d01421440386092902140d1100201840864030841d4440150888038480c100d0481803100441d40d2040b44a650b007c001c46418501000306a913207100d82c1e0b4160480801454003c0340138204030a234020f4002e003504040c00c0c00c40e40c4000083d8403402081d800a0344c00311b001581490502c3c0542d00514818005005223411500050610300c68960000d0500800009110840d2161610540d01d6552a029a502d0b04401a642c3d40c1140419000d10302c503034681800210600c208000b018012034041c0c5d13840c0d80320301c41940c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 29310446 1250 29309196 29309201
    0x705060c060a090c050a03050604110411070807051509010902040c030c0909180819090e0106120509010b060f0c06010e090d0809010e0102040303210903050a05090d080d0b0a0b04050310 81
    0x4d8401036200440814a51511180e0b5002036202d01c0c01003000d4946420700301300440c1081c10071486103060289142c0c40074100d0040e101c0564015101580d20540c9141c884e2409090201110303c845c05030040082003a030640c481441940240c07401d0060610183c412170440305500a100042100c0e03807400d00004001c0e41c801400c8004031007a0315031a8645483d04a140e802c6030100103204083c448620b081242c0c04542d07000200307029034486060b54141400a04101d9500300060607265880300015440da00c00d4001804400001d80140e5903807405210030925944142c0c03ea0550b441400300002d2004d02d05802580310346016400360800b5400710302d045035002d030083c1640a40e50749a1401c0048802d0a10007000110702c031303480d403101c3d800c030b1481c4040084142032900800d0900d007401042c007084d008002c8038088515803a0003a5a80c00320300000705010100030000d0000e60000c1356401f180c1c899a440b9a250b40d40807102500380c95aa90450140ca226501882c1c0e010b030485180180095034a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 29311696 1250 29310446 29310461
    0x315080303010b0a02160b04050307080102040503060f0405151f17030f0a05070602030c07060c051914120c09030c030304030309030204020f12070c14030405010905190f0f080705060c060a 82
    0x30310603500e0000740800072040d85e940c40d4001401401000230204403074901040080002e00303851000b5401c043c546000251540c500408814801b0900d01c00a0200203003403102000c0400146a080468100980d075100c1600c80640d08485280c003802010850741950400c1001d444400d4000713510b806002c550011680e001212000c0034880b0502110780021228005548030f0b50042d040e240d1601e0703035400e10740261b030447d181ca50240103040201c0c0b40040c1000408c0907904240c2d00702401200720490060046101d40d0503030194182100c001c0c04540000c2c1401001e0f100000c804aa1091092100705614ac0c41a071100038003045030b50f4001c00042c2407a8002d8083c82c119881c10f54149401c0701110480a0b004950001c0080c04500d118001c02c86420030540d079149403c0015070415040c4000607204607a6402035503c60048001c003c0380103c48140b205018221014070345292036542e45500007140c04600401a050051880c08102030418000b5102c0210b02e6a0040c0115100c0808280040540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 29312946 1250 29311696 29311717
    0x718090e1218030a05011401060c0218060109090908040503010b030708100f060510050918160318050307050d171005040e0f060c0703090503030c060412120c08070315080303010b 78
    0x4902503032400e983c00d10071808124010360000c0346107584040c200140c13000580203013045c800408110005a00d5552510103100784500038a6610f444180050b51a1a0300e0b9000d82c04543c1410030f101c08008840d0094011200158001d102400c0384074109901c8042038014019540c0c00f51021461a0809400400e034805003142d0008409481d00040381c101c1c0d0040c501c00c1c001c80c400041e00070b16802d041080902c04035008a00746560300744400d074041e00c2c40310401000c0070903403616403441d02c03115a24845a0b606a20804583e070310420307032800f20384410030b406d91400812076607040c0240543c2d1901005101e40704040690040b07d007041d04100003404030003e120300c80c1c810b02d1101d0244e528100328950107100d8a1694913101c0750340d883c0091809441d0340019000742c0052044c076000c100e0015119410582c04a442e1114908440003280c881e0004030701c071481036081c150140603c0b07403c40c003c14094041903030705004184040208181c3c000b15840349024079401080100724803094940501040d089 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 29314196 1250 29312946 29312977
    0x120803040c080307080c190507060f120501120b07020105060607021513030c050f030a0f030f120c050909090607080403050901020a0602040f0f0e04030914060c060718090e12 76
    0xc941c00201c0c61a0003c070f2017100c4c25a80060320004101c41000017401c9420381ca545140c90f0842941c60a8940011748160414030056010041030036015504042924513109020070841d07a545440300624544004142c3e810115200400c29a0380b060082e43d200341000307461545419080e50130b0244550380103205c03001174041405050343c0c1c0348184082c1d100850190112021041c146070030010704e046140318152081d884511042c002030040c10101350019014141003581c105846c40542d021b401c81c4044210492170041c40c104000e070004054106110252a00700886e80c0fa951308640e00c1e9001c2c0c841101080c403d1000600292190004044040041c41903414540726035569005903081508070320050030340e9541c10f1204101546209004240c024443e00960030a0389005c1c0072030364076000c2d0300d01404200d01c0c0c41303681c2d445400455400300000e008482c0340d4030b0306e000000e1a00305940c1c5c1d5a000040c64020004002c562405801d800d01e281401a0494000e20404140d480d4864402d8030320420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 29315446 1250 29314196 29314199
    0x5011407021306030b0a050405190203150606160f0302101415031207051506040504170c0a080315040506031c0c1401050103080406080c03250309050601090e070e01120803040c 77
    0x2502d41c003a1038002d0711b490102050f11705152800b01d040c00240391880c4c40c0c10f00d03030152000140c0c0e4001905101554400c40c204901d44516010070b03610320503001c044405410b600c2d80d034010000c0000d8000e04581c000e6003502c0d034034803a1241d02070603203030b4600801c41e00c48540404140180c0b240381d068051b0700002412502150300d03000400c8aa40c000320010b032100c3e08801446071401c2c0480d0011903104604480421041c6025035940000c05242c00240e01c1c14078002c0390b001e103003400030022030350a5900900e44a88a01d420705031400241c4032410524003031810f08001c0340441c1000a80388481c1440d4504192420203106001c4880000c44201030b50a80d4140c100801c603c0703000c2c4a49806540501d04135551141040800b4040d44006004132072400010010040701d21501ca0b14168803107801070b02070020b200c240074124080c0c85149400351940c09180000204910340e0382c8503121400080c8140e03084c1e242c1d0360010040e80242482054005055501d440001030310000007550700c43c3c030070740d60251401e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 29316552 1106 29315446 29315453
    0x108090c0916020a0c090b010210090213020a180306050402030f0f060c0c011508031305120303040f170c01090c0e06012708060903040303090501140702130603 70
    0x400b5500c81d80e02c0180d10a00044054a80004586442c10745511000004201c00a039440c0540f0901105082d410350500034240103039002044c142c450108860781c03902030f40c800d00419081140140b01d05016222060341c0e18040d600444000546184c00d04c14186000810741e0400d50702d60108450b0b0410400008409501424104040707844451800500d8050204002e203864074a44060012440d850b001001d004111903900883d2065940d4409000c41d4450581c80f070040c64000700300040101d103180c01c0400402e44950301040c0b182c0e00001500881d40c010034015000c03030f515241c2c4c86050000065015001d840b1044088880d4208600007070240148040d150311418a540c03420450500c0e003000e044c1c001c2500c4002d481103841e100c0582c940b698003d010490106280d100f0224965202e00300b103000212030044000c1c5080c1a030740800c0012201d40f000d000c9200d44907100400003 = true := by decide +kernel

theorem cover : BRFrame.Cov 29136696 29316552 := by
  have h0 := BRFrame.cov_init 29136696
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29136696 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 29136696 ≤ n) (h2 : n < 29316552) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
