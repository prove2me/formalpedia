-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4859
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:58:02.492487+00:00
-- url     : https://prove2.me/submissions/d9b50dbd-30c2-456f-a8e1-3b7eb4198400

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 873741007 ≤ n < 873920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 873742257 1250 873741007 873741017
    0x9020102010b09011e0509072102070204020f27131d01110702090a0b1f0512040819030c120c03090813150f0905040509012c0c0306060607060b01 64
    0x1882460f1074610806018002400304a400b0301e6412540481d082569403000c1d21030321122080c014215006405050108442102006124000300241001e4411080000d410900c002094103101965001900c840b804001c103080045240c0780c080300c00d40b00a42a0035501049081804106401c00e81c00030f00d54012000028050326a003400140c211001041407000d0700d01c00249003004c501d80702040340d0f400b101d00c400c05c001c913000d000045660201c00000d06001c220000c080e401d5118041c1e8103541c405078040303074802c2d8035160a15103039086401001c0070103002d90ba4444004c031198060301402050080b9960389100e54007549011002030294002c5a805150365074091201040b05800101004003c80310a01d034a28a090f94140c0b48450540600c420010307251211880075074040740000440703104480c045107648490780c0b00750040402c0508401742152240284c2d0120075201c10035501c0020041c150303200d001405007410b40741c00b8100d0301240c1c080c80400620380000d04076440403135511810301d45 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 873743507 1250 873742257 873742271
    0x1d0a15051306050703020a0f02010e060c130e070203040f090e0c0103021303021807091706070f090e040f03020106060c0804120f0510020c16150809010e07060c0515040210030902010201 81
    0x902c021607005880c00d03400a500002c02082154001039004444c2c04648020030070300e81d44500150300d03590050070304054072400150203221300003055180780207020001d8081c000380c100a0300181d0b41e41d1040c8110b002821b02da8400041c0d51015114000c62920b85901901800c1c10701401103000b50b00600001c412001458404400340e11034842c044d6503848201002c0141d07050911019208850541c8465507030f44c001821903e020788081205a00003007141403040c005c40c054034064501c00426080842d107060014108003e0100100000660341e000e42c008000c03180e201d0a0454800000000281c00300303404000410103c0b0b02d101c64040118041d5400300402c02c19aa520703800c0000080601c074895401241100007450240035001c600030150786414035032440c14695840203400325080c0300600883c84000341c5081005c3d080040032040b08800da8501684503240545840b91034402600c2c58070031401031003056061010514002c40c3c00608903680c4184040003113000e0481054128115521151 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 873744757 1250 873743507 873743513
    0x15150409090f020a150c12030216030e0a080304050d0807060e1501080615091302030a02150a020f12040308032a09011214070c02180405011d0a150513 66
    0x2041070402480341c102c0c00c0340c00c040c50041142100d041c1d0055880c0044074415400e525401c40c0a05015076440391200340c0b2410203000a400900070702509020b0304226452410030144e0010040003105801c890180345c10f512042d0b2160349001310b0042640020042041c0f20200b45100050549a48a48400b0502016402a00c4c2c14911504824420054544014040c80c0000e100c035030b40c000001c202040314010300d44e00040e0361040117048150640e588d1108181551414061f00344040c1d0080c01509000700c450424030969032040740d907440180100e20310466100d00200d9021402c080700858181814216180c840080e8009010101c40c808044c0e03140004518681c1c01c5d01d010780b2004c2c0075944480e1800300141110b105803010f80b0106107044c0c007400c0d41041e030400d50798108005d80b911369908000c0d4404112009044802c40d01b69661070310802c410032405400ca07500c21044500720425a40040306400e43ea140c0c1c44800800207a10340880e1200e590044d07000310340c40019448440151440c43d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 873746007 1250 873744757 873744761
    0x3030e1b030606011b0618030909050f0601260f06040605040902150f0c0627010c080f060109080a0b0604060f121203020712090806181c1709010b011715150409 70
    0x82801c6207d41c900c4d21701000c1c5a0481182d000070042c0c600148200d107001e54614900c80c0c0002c0496041c00498041e00c0b440c250450310742c2500e810342000300d035654207028962861407441102c40e20b1040c3e05041000c952070906004e18100c3c954081c2441703280e00700c00c0640d9038854000b06407100d2242000d00c001b42580d041000594090141c4200c91151982d02510145801c0c40c40341850007607a0405607114821036104900d950b1000824128441c561a101c004943e150004e40c0f04030304038414440007909026220f0407a90007104101c03001c03c102a0741d640c3c4684501910320030000e01d032900d01204000301d007012246106803485881d0061400145990300f00a8003500c281e0080007805188042c0030b00142000059041600c9a0003001034018541200369100083c00a000012031000315002c2240d01585180c3e203083c9291241c50b0756032501c1300c4014000e04804ca0001d0016403c07407903000c5400d40700b801e5140280e100c09260600c02c441340c0d0621070307403683c0320300c42913088a800c20001070300c02254 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 873747257 1250 873746007 873746021
    0x30c1504061407050c0d0e03030a12020c1e1603021003090606050607050105100b03090a14030d05010b03090d1d120f011a01020c0a05030c100507050a03030e1b030606011b06 76
    0x213611044d86828020505620b0701203050580e405004a0000160103560000103440c0000841c1c07800c0140d1851040c040130280c05074000c1000d1900c107425480e1030a0b100d100b951209180a00203d8444d41901100e01d2442091307440040d410501b400d005204051081d005100400d0190401049140d80c07000410000c1d840710030141c07079995445060000c0f1003a113492090090400600345411030400414058840202c000d0040022a41046607004288140706681502c500161b0410641d13a442c0c100030100d82c01102c4540c1e803405603030001c1c0703201401078074000100c8040800e20704642003035009110f038850400d07030302c190715110750241100c13507581c01d00521120204d4141400070789103e20002a02d00780e2034401d000c0c0300e0024807409001d15240000c01c036034000d1b400c440940b682c8100907800d80c0e161141000250036401000c01d81c4040c90f0705508241031603020601110101d4014030314103422608859803035a41a04071802162096100d441c2c2e03440d00c040c4800881da80320a440d52118121462 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 873748507 1250 873747257 873747271
    0x8030301120501142e0b031f06020d120b010e0405040302031809041a180703050d170f010e09030d180201020705060a05040e190e06010e09030c15040614 67
    0x41502107404010707081c000c040c0c0c00c841c01c003140d511a081000072820244010940130740d1160141103e01c006100c01a840c2c40200030343c000c0741d81e40f41800c1c0ca019191f100700721080d003160351480c540050103501c0003419981c4c07000c0c140c0d00e2b0a5152603046110000d008a007903101d0404c51011016005942c0302d21600380158480d400542d500c2407482d24031a000362a01b0140d501c6004a0000c00012500401c18095844508034a102d1150f80f444460107070b0000e242c140004500c5503550100803c00700180040d1244120303212000030904454558082d22000c88605408a00000042240e902d1001406402062290070343e030414012902a10071210613003507001100030f0340b401d07240075941c0500c517800c013a1500380c813024640310ba0b41a0143c828425071142e0301d184c0c1100c2d000101c0307130412460780d001a045902000e00c080010034601719502c090a000324070200c0c50180110780922400000c0b00d0782e40d01014040d20a884d20202610b4000100600030780e0b4142e155130402003401d004000151045103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 873749757 1250 873748507 873748529
    0x150902030a09060f020c15040f0b070f030b1c02040902150f1207050c0714060702090a0f06050a0501091e03081b010f1829070203091f0804150608030301 67
    0x3003400d0100541d05a1120400d04c60b20410102c4850000441c0380d400e0402d0f405510315042e200ca00c3d040d0b00c820400400908501c00c14000d00684075401100c1000000c0d159400b40305250700c4404214982c5001c003087e00300082280351b243e00500303181d001249010300007071881300440f0410304030103041d03840040300c402c009400181c118a800140c0e1565500101c0c9490300c681009404050345554580d24042d404410710030300403014040d40d40004540a10f44c0c0039105c4845030402c00f0b940d00140c20035040a100d55070900c4400300322800c003400075500300c1d001692043c01641c501340c0c00c410500079400505103880300e41040407000c030307210b80c00802804c03c903c0e540524420442d0481802c4624095000905a080c042c3e000010510701011400380c0c1c1d04107210b034800d481c03030810320000d5091034100000401d520404014a040d0080050051280240c4808410000c1e1a0310021481000c01d4500040396204020902084058401c030022032a44000044c02030b49800005107143c0007680801a165 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 873751007 1250 873749757 873749771
    0x90702070e090c0d0803131205030603063301050705070303080f01120c0302060d09020a0825031e1e151a0a0e060307030b04080d110f040504150902030a 67
    0x1912140165034415100c0740079081c843d081c2d000081e002030f20201d001d010304601001203a0900c1c40b164500e600030b0f5011000090303080b20034801a0854000311030040c031a001c0c0400150176006240c44120704c9400365130030305603501000341c202c0b0540b5807800c030360350304114050004200054041004e4009540a901e40c10828502110340740c0040c4416001810040c3c503840e017101c0000c90402d2460b060302d60459500703464501c1902503e000341a01c1c20082d51007020561700048448000c00c0841081c640c660904902070720444010461074094480186454101c0300309503210f00382c0e4081440b400d84100d00419034680080d03003000c85400114001c2c1c808644400c8090708440c424401c201408443560b0b81d092140b420000006c1c076001062080f541e2800e08000010001e0f9000d1002038055a0302c43c00070a2a8141428054642e4020310f9240c12040e01d00800c2000c0000c0030b05c1030ba0384040d01c1c21407461078242801c0a0101a1414884591900c030402c1404100381215001a40c418140039000082f81 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 873752257 1250 873751007 873751019
    0x10b0414030d02030d0207030e1e040e0114040b06010513060504080622060b0402130f14030705100f02010219020c0a150c0b04230d17010b030f090c09070207 69
    0x155034100d0520311a034401000c0000642d0040242c0f58014211600143c07140201e05050781d40d100c80f41c55165010461009040004220a08440d0403401c1940c0c2000f005101408240c02c0700c0c90703e00103048036003914000a0014000e4030800da8031200601d810383c01c055080c8010001e0411a81210b40480d802150510003281c3c20441180d20580e03d0207071131912204d40008a584420510018010300e0700c43c1c140c25115250713078045640c00c1c0d031502016800300b5502c9a904450044c01e01070580d940410200361201854005101016a807000705100250b01c20000140c031404c1c08070903108155502444910203110a00c640703600e5044803074000d05a840012810001c0111aa03088203101e8051046415801075000120f402c89507030052910781607840d141000d0b2a003405c02d02c61a03004d80203594420a00f004081003940381080d5588405008a02c00580102d13891001d01072040b00450031710024001c01e10424049030402c800005441000c501b4038042040784404440b01000f40c0d211003420449 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 873753507 1250 873752257 873752279
    0x2a0c0712151404020105030115110f070503011103040c0b25030e010e18360a1407030f02040b130e0304181104060c0212011a1519030c031103010b04 65
    0x1c5182c80124580c00e80c5010350018010740018054458405400309086202e140224a01080c01070200100c4d10b8141208d403070182c0d100b9090242c18003035400c04880e100d40304415015280120f50020242050500703001003e191608040d1209505104c12080c40d1000821210400d800c28000d984514906001d000050f002494600b03189024940b14100c1e406c240240c04100c9800140c01a41c1c6411182500c0c41c1c90725007801181039421719039036200700640d600000107d0803151351050340003415545890441903103820840c40003801440d0b0551510f001860564404096200010803402a0503140c102e00011a02d07200005d600c140e0001505120445008099800c2e400c8585010b0015400048503188075004900c1420107004120020380119a5015040d8000305005402000b2107603030380c4c403040300340400402d1250180b205940400496400041260004880b1541c03c0344241020300d41100280b503080c0f602000c050b912000044d0030300e4000700640c000c0c1261042070b52200e00341f640d0200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 873754757 1250 873753507 873753521
    0x8030a0e0a03020a02011d09010e0105150a050f0d061e03060b0415031202070e0a09110d030221040f06030e1b090127050405152a0c071215 61
    0x1420754806410400001d40c0003880715030403542841c121280310104c206104000401d9108140e200904d1703c004649032460b024024100d600458040320030984001d840d42c01c0303210b02d80660001030010010041d0309050032008002d44001c07200c0006a0301d40d948051344005403002c41040301d0812407042003051060a0041d44120301c0211410005002c2e805460b1828012078440100743c900d0702403507070168034004d002c80c0004082198076502c081c0341c004c03248402850500011200d11601d02c600944608040c0c80450015506070001c10380b0b141500400442c03081c080210702d204460400c4081501d550b80080813000745000c1e00c02041c0c0d0450300440600703052142c2d6540004150304c010180e22a544c2e1468241120250b22109854104080c0c445040c0c00c403200c6140501802d04051004201c0b0028005003003441c41001201c00d5120311004100b02802c007241d1980386040f09215450441002c0000c101014119044030449596a44030011040d162001650308245403d854030003400f0a0080003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 873756007 1250 873754757 873754781
    0x41d07090b090f0405130203190b1f09020928090f27030507120f0305240118210515010302100813050609030d0f09080915070c0308030a 60
    0x15090401100101c0c28200a80c4400c622468031417020400221500080000591f0041c0a48410410301c0420304c6046405031070849000a1910020b500340240468484401101880041d4003a00d8105158083e40002c8400b0b076119000700340b83c0380045034640001000d02070080048a15a242088900449000e42c860080072414240440c01045c00d020881c0206903c103036031140402490309045a42d80900742c00141403032200183c03050219000b0003400340b80c40140e50240a1952406824080b500a403090309803400c1c460031314000c0940c0944010000e1008036a101036202d545d40c100301035a03889403110120340f4a101c2d003d0f02d007400b805000c840c95070500d422010001c0d5166a000c038071600054101c80b01000105000305802e00d1503d000c0c102202c3c0c21000725946070414500041d01e90b401080d002016610344503611980c164140503807200140c00c9900603040c03113400030a01c00c0b038048903494240d4016042011500090191011001544c000d07212503403246800a05802100c07070910743c0f4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 873757257 1250 873756007 873756029
    0x100212060108130c180b01020a0b04120c0501020f040305070b0414061b0307050f010c020f190c0f0803070c060e0603060f061c090b010501170a0c0203041d0709 70
    0x800204444540380c000348203103410300341982d034034400410b05000f0000c0200b0042040c800000c80c030803180c24000500c071407454200012120800160fa6601500b0f074010480582d110000d40883c8c1c0c18042c418143c420350074100c0082d0a150303102403c81c4e0003005010880400810280180a03041050750040d040030766041d0f10340342c2840149444010300d0b401044c8501000154400f40c0d400300c00d811481d441610003182c0c2c617115985801c50705d410203078403643c245603e00005004800d10026044441e98070f074401800030951010039105105480e04c81c26039400c01c00f4500090000003c0039110010520071010351780f1441c0301c1c6051800300e541d40d8084020003444d00d001e020b596450303004580d0804411198454001c0e16000840d1650203120700d12803000b0904005181451201d80059031003501c180040035050703886200650340503480c80404038083c244a80092a034928039840498401614011139007800e0b5594101500451070209480c9646c9140007806030540d000801d040c06003d02401c0303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 873758507 1250 873757257 873757267
    0x15060c1b06090e0c07020a0303020a0614070509010806030a0b090607031a0a0902130306050c0913022113050d170604060506190507060212010f060f0813030e211002 72
    0x4002c1802805010b00e440f050240004590440410011079026590107000d0000da40d87c0c03070601a4076442c00010554035982016000c001c0c51440b2600607104042588910341480001c200444076050014181c0d80c01d0b00c00e02924401044c2500180340c815110354004000920301514000e040d03a00401c40a4451044008141103c1d55507201c0b0809449400c000140c482c0100318851911544036070016100500d07050074001034070310610040850030320a03101600340e10866003004049110313031500208a50f0846405031801014840d00c0b6420001d0b82445070202074040d15200c2c100304c6d10070307514004521010a80e85000c40360307485055000c001242c00700304c0b407494907020640340d110390580d0210500040880103506070041c0140c0702d40e0740e004075086482d09a02da1070480105000e0080c204448007089002520a00c0b801b0300030521a6680d40d19042e50302d4488075030794002250070003181480820700d00746010740c460015100c020a15501c09034a4180344000541c20000d01e100d2003c50f041c01004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 873759757 1250 873758507 873758519
    0x20c0f1c0c020108060402120c0409060e1e060315070e09090c09070f02031b01060305371104020a08072a08090a0f030609060507110d1215060c1b 64
    0x3212038080c00c0400145e80d4050000b00240b02d510822410f801c804428011f10945000250080e45c500c48400c02081c0d8658014840f651b004840180900710079502101031703600090b0100e0b4100310050101c1d0141000c1840302c03c0400002c44092002400d2000e1005c0b503460719000b2941c00c00d2400001d096096880c00200e28401001040d130800d201600a205501610070001c8400001d91410f4880c90548c0401d0317128081c140724441501c0505c1450100311a501a491004101e4902c45da0720204403480b1280c0811b024180c4e500c1512518114400c0c8501034031a0300081807a0400da6030380030762616261601a041d04400c008080c1c0c084c0c2c0c0301921104001520400c0705006403c41d4007581c03241404000605404a5500203441d05a0008000000c112aa400c01d203c146d1182c81c0900c20340d40c1e20032080b611001408100c0010394045030800c401c55000796104210210b00c003a0200310b1034a441032103140c455555001c4d20016480700700400c03e0026820122005580b165501c85d200c40c5011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 873761007 1250 873759757 873759767
    0x30f06050d050d030b0a3605010509070c0303060509010b070203060a021606020904271e020a05060a030b060c0309010e040c230403021807030e0a0c090f02040801020c0f1c 75
    0x241104141644c80d0f4407805d0694415084400030440c10390070810071070030a02141640c50383c074900301d4155084208160750210301350195038184c800c06812110325a0310307050129003442c500355080e01410340c0c50501288030340317555080368081c1c5010f01d18a9929800391040c14036181c0024001c601080c41840a81c1101d03080115074090581c103c800541c80310411030001c4c0040c440c0c2851000043c0074070822984070b5052260300d4003100c0c00303039480300134210f068681c082c000d45084e880291300c03142c101d906000700c1c079200000e0401d00f0b01524001900c3d501141c04074041d40d0145100051a500c0401c589180f980d0203100c00001a0f01a90f00f84201c00c03038000050640a030254003410000e48442070910005030800a0b200107580040110000d0700820502c1b03490840c041d02d1002c0003e090400e4002d0f003072000250340704050340c003104007440c0a00c1c00030000014420780c0700184070a0780030040000c040009001070460700c0410005803640c1284a90410718028200003c0409034030203450040d0400d401c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 873762257 1250 873761007 873761023
    0xc0e03161202031501061106090606090609040615240504140904022707030b0f090c0309030714070501081e0438060306010504090c0b0703020a12030f06050d05 70
    0x18110740c2400d01c04034030000303041244c80072070300075000030010000a159602c51440015141660262031a0361103240761140c8501c01100c0e69072b04070307280c6004a203c80c1401072042e580325000e060700050304059034012a0001581d980480000e801c401d07214001e00c035090301416509845401c1c040d291624042058120918082c0030b03030b1140b0848030019082d911030111500c8900300b001c0351304450f00704d421f46810b0400700039100c0c100001d203400e007000803c0c01c0045104054040c01001340300d0603a6130140c0d1002d59440186424540e001c1072040350001241070213042048964640034142241c20800010106000200002c1400041b50700c0303298005114602c50380c119030000c540000d40d802c200351000e41c000f41580e001e0721403a00c0405140041c2c0000c11210700a1208805980051741e8440c10002a11013001000d09a02040c4204010845240e03004103850b521038010b03100030798003903240e40012008100218000c26120b164a507000c00c218801d90011303000481d5402d0003990281c959039640c500c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 873763507 1250 873762257 873762269
    0x18120906032f0f03100e0c03040302062a1605010c030b13051005150c01050a0e0d0c1e050f010f15050108060a0e0106050706050907050f2206090c0e0316 67
    0x840b0202100d141a108110350030b21460780c0c115030313580c1020f207500c044542e11841841e071819054404101094400c000300c0740140d415074000c00103500e4100c26020411030b0032001080b2034140c54400740c50308020301d0113490204440064000c1c0300800742001c5080d6144081240c00b098908a8090016502d00f40c0920451140c0c170000140381d540d01c0b40007442d145058001961245000d0300c040d000500842c01810348403040d10081c0000c0c0c4070a81c48100b980d441e01d9200040d90040010091090722401c003080d40075010300310000e0003d03c040307410b0501039600f41091b952500042030041200305c09007d407041c0400243c0b070421500d40a089908042c11450154504002241020030582d030784e5103055502a1103120079450b25540c2d266006041c961200302e048a0f260b05003000121744110108162040700d5014000300c0e8180c070342000300417003086410301022400c41490190380c1c8480f4244110b10203401e551100140700e40030660040c0c940880101ea0612030383c40041807021007402124a2421210 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 873764757 1250 873763507 873763571
    0x212210c0c061305180f160c0f08120f0112110d02040614010e060f040b030601052107091203120c0207050d080301170613151812090603 60
    0x218805590409103290700d51944500c000c07a14012241c1c0c401c902c00203c41d0210b6014865500d04241e01c2503448044518045401149000030225803001d070444245462602d0801e0581c5003a50300c1d048289001c14059131a5400070032107480304180d1a00d0f042d0003c40790403903d801e6600d0b101c40d0b850144071880e03000380708188119034149143c0355141c07100840365009000b804055114800785440d6081c06080c503000070300700100e02442c0d0400ca82201c40fa00c0c003c007001803800d82011003000440d440500341354108041004408600c40b50000c907040314200540c003580060a0404004107000e007150803601029000d0382d10b2800194010804452940481c0c4001c941e01c130052138203908100d031951107540c02214032241f1400300510040214180d91042e010000c03044034100718035070b071013030116400000c0c0b180ca51040300102d1000c2a443d40340115401010400f4802041c0d00780141c40384000031038100340481001c214198100001502a2001d1700c0e04020102c4580b100050b0325140700e080341d020003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 873766007 1250 873764757 873764767
    0x6040b092407030f09060f12051308070501020903012304030e0a090903020705120316061e2a0203091008100312050a090f0608012d080a021221 63
    0x14040005100e4a0201140041e4940d52541000b0b0203510390600b2580000f417419001250315030180c130340c0d440f0030451542d0b01d50300d000210b807a4400416010b8481c00300500e040c2800c1c000130b006030340101880ca11501c000360312101e01005142c00c3d6400102001c11414021242e01c002c1e46414006540c015010b14200880602e1400891120100c0b5003005949505000e6060241a0000f48140440e04240c81031034098120201f04c070703102d020f01000301c80324224a0141c1d00101d441a041900c10200c02d80821000032020760804007200c044100707011203030101c1e40a072682100c612002d401041c500c0d0000d90b14202d4244001010031031038511020071702101d9030104520b20316004c110009190f0200e013100010340d1101d000b4000740c03c00e00130703900003940140d4081500d018030b040400403603d280d1507405c15642046c01c40d607036030701591401c0c81c8056494941145448030180c0102d00401980300540b811041c203005006224010009010301d91b40184a01c0f40c050800c4540c55a82c0c05030031307180d41d44503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 873767257 1250 873766007 873766039
    0x1b0c0a030c06090b040b120417030915010b0702060f0a0201060b1216090503060a091e0309032312071412040f0807180203220b061f0e0f0604030506010f0e0606040b09 73
    0x5200078a509c41d05d18038000c400c00480940000d4900000c64045c0d402041d240c0c1d849918060500c95039500a41205040c0310160105e5071410207820942c240f400003007a09616001c90310308581008481300064440e843c14840300850114610600025a181001d255410100031a40e240300c098841301c0750b550baa044103014410503555403800030046805084112045080003020114980401d4075a000201a00e4070070780400d03601a50f0446110001c0d144404050502c210f1641000c40c2c00e40d52603d005500030043c1406104055207007140c0002030392602d0074400446914001c80c0c0042c2000e078001c080070b01220b07240c200030b0001003107182c101590341c0e030340c035045690100045140500c115182c0d00383c0300100481c82c1c0d64584101e40503160200403201701211000c00c0f0f00d0041048011440d9291042514241390381444400c2101400341c40c5015542d5480d14a00300c026403081d4002e98850700f05202030340c84d10303010640002c41200c1c41401d041c100011400c6500c1262003051207017240410310812 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 873768507 1250 873767257 873767273
    0x1209180f01140105070c0e0c1e030603190c121502121b120a09020409020a080609101b0c240213060c150b0409020d062f1b0c0a030c06090b040b1204 65
    0x28503003890344415a950f272400c04940c458009650b17140c4a806447c0510f0200070907404800c0b4000e40180c00519502d140003400d030180424400140d501c00e099607032000f04107040d4001069101c40703105468103140b4000304040c0070541c1c11002c0000c81181040142d0061408207203c90300105440e600141040880c40010003c0440e039000a40020150344001185500070840d01e2058035114256044e06003540700ca0811225402588060041c0810b98000003900c20890040c00c50302c50240701c03c2502110200100382d01c02c3c15160300c050794000400300340410715058984e00030705240c100400c120800d590759130b0200905009458055a0b607440d61416a80d031034002070011070300079082012244aa040003c0500324001e03003643d0507515030710000b0001104983e0b459038681500c40e5281448600c01001900c4515800018264800d8050360301e00e50780c5820000b0029807003010541c170b080c1c0c507240b03000d8541440c40e8000c2000d00d40c18041000103500b41c00450300040c07151120415503698520f08061 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 873769757 1250 873768507 873768517
    0xf0307061805030d0815010c020a0306051e010807031403040e0c0a020a32070f0510020304030501061d090105091914011a0f030f1209180f01140105070c0e0c 69
    0x15252203031400b058051500402c5d402d01a01240d820300b1240f400c1180103403901241c3d02c1001350840c1034510b0030004200903600841d00720f442200b0f602a001001e0010b03a10020080e00325005641002c60700b00104440c45031100b0b54044510003450415242001102100c98014102142c4500011351826800d01c00c0c007010142c507505c10b10200d06007480e0101c0c0c109900b443c148500c2e000501e09040542c04200041440131240d0300100304040b1800c200c2842102c007008a82c02095110a21001c000500d0078003c0c1c0000c5d00781d440c00c0c071072880760106650520703800c0588040302507490401481000d10020030704000f00e88500008083c02400c42c03504180d1034075040c9504c03019500e06154901040c0100c14082c50080301101d01004880402c1d08142d103d1200354080740060340100780d25005140704401420800c00010301104500c0070109900c8814441252030003811039900005100d44170100b805114500c03400e1a1081c100152682c5200058149025044e0350040841c006600c1200c16000c5071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 873771007 1250 873769757 873769759
    0x501110709050708010918110f06091507060b1002060115050f131e05031e01060513050601350c040902070c0801050f2205010204052d0f0307061805 65
    0x1245140c06040100300240170f005071180d2071f09000440502c006d0002a070441650442480d01da4104410304100303c0c12148401a41c201303d042c80032400903618403140c89641a40c804500d50344048c0c505e031001c02c0f185940c1070340d80300300015150344480f29400511b560550b40b0704003448011854500b002e039a0350149800850341248001408401a004c48900101302c4400c5440d100c40700783c0c15030118501c402e2500802d50164402c00c00904641c3d8000b203117085023507900c00000f901a4550b00403c034184e0758160700303103c0d050319101445255603010b40c5442040c80764080148902504030504140305c120700342c03c421090003034404281c40194404c100c1c1c00a0032080003c40d0354503224600700c20036803914802c046d0345502e8036000842220b64903641c544250341042d2051102d0b4a024414084001c0400c0e0507140c1c2d650038000400c1c1d03925030b00d8440400321551400030360320302c0300c413000741c00c01225140341140201c0199089042680700081c510042c0ca103181442000014003180385015409241c1c002c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 873772257 1250 873771007 873771011
    0x3090a0605150916050a030f0f0501260604020a030b09010f0e070f0f08070b0f0c161701110a110f0a0812070212040504050406090212060a0605030c0a0501110709 71
    0x210000e00051040e00310701900a40307140f80c2990f034001503200d5010000d0914070100b50b00300000e1898501c641d22080c204c4001d01400103056000c0900300040b50002d030043c1c5580e41010051424007211102c0e00711110710080001c0c0f4851515a000c41c08440e006e12005008103110070100f0b80b040e0b400c0d00000e0980101071003c01401300c1d261603165171544540715114181802c4e000209801c80c01d89500f10a84100c0801041d02c9443c00c3c40c0440c1d00d504c110f8450a18000034003045000c14020b01c20712100c6441c14a0803182241012a4808810381003480f13214541c2c5402c904000754030242081c0c85c0daa08050500258401da070078070903414450140001c05180c00b40c01082c0d010060080302910079110200c10b0281c0c2581d45540c10783e0354440700c855603030640001740400c00140c50075400c81a40030384035040104070f9842ea135011484001c00c3d010302488542003101000b43d0051240309100042208400800d09066098041003000c0b4403405098104103442604c544203540802c24040102815541 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 873773507 1250 873772257 873772261
    0x50d02070b04210320070516061206060201020a0e040b03070b0f0307080106090f03061d0a3903170405030307050609060606190e0109090f0207020310140a0203090a0605 74
    0x488000c00d443d040c014600c00b1240404075030350300c01c0c031440340340d09800d250200d509010000c1d0403035580c00c004802c40f0540316100b43d400482003d402d20b00c001344560f4589000b80c421801004094411603007050045a03c1030054a106581c80140a10702d00e005031400200270603400003190510505400041f13814100140340350079400d5600045104030708507a40c13441140d89512044070a1481440307034031024078078a40280040342c010b520130541c7c4407420440c08540212104c0ca41d0510071900020b40c1c2d062203003056521050200420300c1c0309907598000300b41f4076500100c050744e1280890300000e030894005111340c0d00041040012100a41001011070352070701c4092030042d50340c0d181180c0c4120240500707008585c0d6410601e0607a2110000c0d10301540c20b40c0c1040d0300c01c81b200244803400314100040e641001900160911401c00c004400f24405039a1b01c126005161424004201e8004030524101040c5003014001442e02c0c1c00048181004d61380b80c0721841c60034036200e542e9101030706661800301 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 873774757 1250 873773507 873773513
    0x1a1506040824010305031b030d05010b120c03010501050f0f07050a30080604020d14010b0403061b0c140c061201032f1c17120a0b10050d02070b04 64
    0x50080280800706002403242c280c040b0300440d03205400c0c0f10040c542c3c2c0c001c1c000400329440300c0055900e85030034041141d080002d2102c0d4a02503690a03031285203d48800034a0030300018445441e140c0c481e01010545140d54074180000707101c2e02c100200c00d0486c000104241c5002460385080b240525009030480d00110560704200c04c40a4414512407400c40714030b01c50468907a01000305102c00c400710384800c00c0d035543d00c0045c00042c0d03000741c02ca01e42903a981e100317504240c504107031228040c0c8508240c05464a0540c500603045513194400010001c8580704460b10490740041001c030901e0b40075440300e00408085405a203440d50001d04598000004281030940301014030440d8100d07800b07181000540840780440019500c3e40520302c02e10114000d168850608003003001c030921400410030340381091415101d250b59550175511010884000080562400300061440c03500600c00719020080500d00100007108061320410030f00903c6404038040e206100f1b41e90590341e4842c0c00400c2e060329850245 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 873776007 1250 873774757 873774763
    0x503071202010c12060b0a0e0d02120c0a05040b10141323010e0f1e0d0c03060b06040b190e1306050301050c0f03060607060b030d020a020a121a15060408 67
    0x20708400000ea29151450380748500317402501d04803000f100c1010f10b811406942203034500caa80d00490341051001407403100607101c000c1402c40214082c03019000000d404400c01000c0d07122503208030301c25410a02c0342c40595454039016030b110649800c050600e0401007004140318000c0c10b003514861096203400082440620402c0c0d10b0035944080711034941d8002c040190781a140121003960410100c94050045041c200c2d84000c1842920144800c040c418400103030343c00308141000c40c0e0b48981220108104080760080c2004201d0031541d441c2080e081c41480c80705e900411a290604088000901c1d00c41d0340142c610014454000d001404a06010702003000134100364815a8001e41ca4070001440e20980007080da0502c0000401c11071854480300108035054000c100300f03540550390303008050310707035a010404000d0003103094010b03224448031401004025142640300c6440c0d4111002c80f4030011f41403e004031071007032035140812800d4991680215000194500d4540c02000004004c51400800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 873777257 1250 873776007 873776021
    0xa0302150f130609020111031b0106170a080a09030c0e180111040b0d330503030703080105370905010f0e070507080903030f0301061b1e050307120201 66
    0xc0c06405a007a1150103907010059401c988110490800910800c00245281c008001c400d00516000c040f141c00701c580141558040840c603400762886d0180304840d03010a000307100c01403254a0f869a404a54001070b00d4945c1c50303413003004040100001b400c0c1c4500e0301404011340a140c0010304218915110f13100903550400607078415a45ca150a80400c3c001c85050169031080300c0600700140c2010725103101c0003440c2c1c03c0900001d0b65191203a80c0b00800161144413001200b20445000c071074038080805140191501f600081d0190b0000c00c40b49011a4000d021103045410a6504079282d0803606c0c8502d111000f4406401800d91001c4410f00080703500c000c810040e5641d40c0740400c41039a0311762031014031041034803e003442544014000f444187c020b5000e0826240511b03c4035180592210019007035502050703012140040100040c0f18441c1c0c0b0130300380800744151075035548402031a42c46401241c2e060352401f0046504e600b4008080180910542e980e05900003034984651002e8a4064007a02c10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 873778507 1250 873777257 873777283
    0x180b0a030905060a0b1f0915020c1f090e13020315070f0905370305011b1b14010f05161b0c140a080a0c0f09060305060a09140a0302 58
    0x90385004c0344058405101d041400707032008080102644808024003450075001c0d1844083c8809183c0020303003018100780051a186030b69010303104620312031042181e840120080070043e401e00d05074041100c0d8110005c0d03820b0f202d03485d00c2000d0a9442500701c1700c03141200d1300000d4250041c07402c82c00d0075100203e14903025166030340310402002c03091030003255601010300c2a103510000070411500c50010388101d1413a40282c03001d0080519007500d40d06004146030781d000322105d030365800340c030701329a074404d500080504114941031009009030031030b20300410a419000b90029041c00b4a41e10b541c4800d5000074091b0340079940070300803481e0641c100c100c40b00b8000742a00105d640c000300184080f060803151608503038818503601e10396044c4500c940211034a0a4802e03000140240b010861401c10019005403a101340c4e11185200e0408032031112401e05503000c40300e010300707001c0d05100148020403a0380d40034044890000d501d0100703003469201c030b0f0070b039408007400741c00b0350070030700041c1030b030101d0703070b0300c01000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 873779757 1250 873778507 873778513
    0x92202210a06151208030604091a0c0a0807080603030a030b0f041104030b070f0206011707171f0e1b060d060b0c0c090402090c0904090c1e0b0304050303010501180b0a030905 76
    0x141d40c2003c07a0145900d44c40040010a04100013402440c0660081000b58021002c504d480308003100110448002074a140c50f20081c00328100c10740c039522101c00da910455501d444095803e044012941c0d900403003d40c0e01c18551a410b102505031206e44144d105010000c00901000301e0312000c02c003155201340000c0c2c40d02e805450000e01d510f80121030030014004103600414550b807030012108038050f02d03024844100d0065040019280d4250f010f800701ca1142200540025984c0d04040700703000002880c410b5000d41025480e0720420000320b101d180000c42c80c10021004507012002131494880c1c18a0506505c1c03803c68080f4202d080304e80500740159155048841c088042c20820110900440b002980480340100103241008440080d0190307880c007a0020821043c160b4803c0000080c640220744503946040c0c02c1500c4942c248481d40050480000007441c40c10300340c59690301c0c2d01c414003e56040c010800044010b81c0c46906180d4010145400d0160f19942c811030010068483c1002c141d800384 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 873781007 1250 873779757 873779759
    0x6030a09141204031410020d0b0906030f1b010207050616230c15120f091203150103110d0e030d05060f030d0833092202210a0615 57
    0x82000541c074902c09000801040c101842c45da5081d40e8440c83d00c1c101102030180c070404804a65850003d007060b45c41600020a841c1540320603c41200001041c0d50702c654022046000c00c180d02151004020503099025004102600d005074a806410b5119940081000607140c0104098416207000980b04003d180613010480b012800d12000002100d0700036048095640038030b00e000700c0380c860362841d03480d0300c0707070401c81100806003094208917400c03101c0c0240c2030704018a00104ac410009015058400c450660a020458002c14540102814181903540441d00150100c0c401078414200d050102072040001c10350b40700f0303165080010818026418000841c84601d0704045403500460080c009090801c0b60071000c840c4804013810701c1901140e08240d01b04011101c0202e80c4605600b21024031201e40c0001c24030022450040161020400c90b4840554100c039880641c614141c044a202c15074883d00444203980e420782243d100c0701481f45011038000c1000e6500000748d41c807200402c103c00740e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 873782257 1250 873781007 873781043
    0x10c0305090d14030a06090518010501060c0b0f1b0d020d1104060219030905040c0c1203050402010f0503040602121f080303090705061605030c0f0609010902010f030c0e06030a09 78
    0x41c807804204240407510082e0a0b480d2680e900d8044c581c0114400301c00300e0302c2656012040101d580603200d0702d84602c00400c41e040c4004e42405070341d0050a480ca40500241996100c00d00e11403809042d00d20100300c46004110711100d180c200086200d0018030f2942c0d41c4d64011f0056000b580000c000d010071506040c0010070300214103080c0c0e400c0314401d030050000041241614440c6000b800421000c0c800b4051004c1515204e51242d440c500c642515620b0b0700c42d0044c180440161801000641010300742010800140d034444242c01da903201908100d910b90310f40f441d208000c0d00980300d00c102d10800343c10401c40d01200d11102e0440c50314200f0031801401e0b890310f5203e5100d2008844446007031340300d520104a0780c20804010581c0c40f01e914902041a41030341d842909550040c80040820f501c010587c040c0c089040c4030058124003080d008010742c58480c2d00182144a80000302c6041c9691403c2d6000000d0003400d1615481c000101920780d00e240185070100200400282918464240f268085039 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 873783507 1250 873782257 873782263
    0x8030405060406111c0f03050c18100c0203100b09071403060d0c03060e0303041401090302060601030c02033f01080a120909090c03150b2d03030c010c030509 69
    0x2603a002604441c901803c000c8291801c44c0c1da00203d203000e1058850f105d1007205105603d90081005645040c3d420001d56030050076110054a04075020104000740101748001440826081d082030b80d2040c1c0603c00800d0517106000b100070080d400d0700a148001d0032100042e400032403a02d00456001d850b9485038042240c02e10280019207031201e000b000490b9a0380790100124002034882d5044442c606c0d1250b03544030031b6035402c120f0b0b00c0e020361021052008000500480744d007003106c2c00008004e827440e540c170005d42e10310001d046036042c15035501c00d100c41d071071092080700c0000c0030800d6800c40c60454200a240306e1012403a0000b900d1150070401c1c805090040d400e01d0403109040002c0c0885480e07a01c50000d07200310581c3c400c0c10720062440c001965446070250202c0707030f8000d4819142303d52940c20030020502200c0e0000b82d45c10300d0a144003049955808001c515440c0100c18600d51030f034078241e110901c12501e0300b0207616200c0411214410101504203940030680381e581840643c86816145075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 873784757 1250 873783507 873783509
    0x6180203060f151608030105010323060910051c0314040501200a150c0210230c0c01060909020a08060c070615180209010806010207050a26010c020a0606080304 70
    0x40e00031801d804440d030525240c05850000043d802d0210300e0066000ba82c6288600406822a800040440100314540e05071084007908030300031500d040546100105170b80b411400a0050f40702d030111401156103c54480301c80006000003420664041c2a05c10324401c01d4010a10100c0c001520410540aa1991030007668200c1c1c00603101c12170011918100441c10b25044080003031580328101e0303190081441160000e0344075643c0440010803407a0710000a0074051000c0b44155114240038803c40c201008480a8042c03c1906031000d0080d00d4803c03440e41a8400c0c24900f010a608020000c94111b20590251100ca80b00b1210688013581d1545441e4640404903202d41004009016880100d4000e070400034640d889142c2c084102c035241c0210701c104245540c00c103c5217543c040303024038295070443d00707880c0c00c040240001c085491610340011100f2515002c1d0404000700d0542411364404c92480100c0303141d907404002d0100014200d40255160868481a2622410104000790f100c40c0070040364 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 873786007 1250 873784757 873784759
    0x50c0f0a030609020415060810080d20070314010c0306050a08070e04060603050a030e01020d1107180b040204290316030b011b0804060e1504171f0618020306 69
    0x25110380d01d581c46541c010a0307981c10a81e00f140c0c480d0001c1042070305245045000e00b001d0344580503603062180c11b01c1c0701c01400d038204050300c3d8040c400c15419640c11080802c46840c80034407440e055401c5641280c104401ca901c01403010f035982c070b0840b28001c410342094580c104140c0c2c080014035940d004100c00c40c20b940c441c501440d007000c403040c001a0781410400f44c1c41802a10040380e003c1c0c2d01d549083c509841008141c002071446500300180c0d607814440343c0c1c01c6841750324001c00b020912251030380e2942c1491092520b142e00c008240506440309400140c0d198000600441d280d80d82c640310003800d01100003942420098540381c12001120040c1030302c0c025004039800f250200c01d000c00c1500240708420b90141849140003d10500d041141e140b10b40c2103100d9156541c88a25051003d80000c085001c0c01d071088480301e09983c010400c000c140c0b01114195041c0d2005d0408062449050003010400c0200a0300f00e118640d080c00b0645d04540202d48036024801d60701c403034140e011400ca000c1950301c0c2d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 873787257 1250 873786007 873786019
    0x203072606150c030a08063c150d0603050f06090604020607020f100f03050610020a2a060302090f010518240a090e0708040804060f030f020c0307050c0f 67
    0x1c81d2841c280b1000c800c1c0b071240c2d0b403001a450310b00807601c0c0500d50b820100c0048001112003013004041d060403209844061a201c01043c40d00215440f070001c0543c400244400c1600c14070000307200303540c40d1380c10300030510080360050707581b07002d41c80300f00e00505a513001c151058440e000c205c0300c909800086403813190010001034581502d465003000055480072005982c8481a400083d03000e41d140c1e8200c50000989441d0220100441800901500c0000707018501ca20140c008000c901c1d900440e1080700564080803100c4da001c054146012805103a00001d454401d161502107403858041e07000386504e44049401403600303100c9000455551080c2c082101c80d2170444540300c00b050404ca00320144c0e4401008180414840040740010503812040e429000034400200402ca403034061003050303401c030740c903451321042c0f0f40740c02c2e15880074078851481084200180b9210305141144642d201d0001c09108280665641d0710740080c85503290040d61090ba8180107168415055151103081d94410f01c00c01380603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 873788507 1250 873787257 873787261
    0x102030c06070507150c0f11060c0703140d050903030f150f010509010905090a0f0b0307050607030c0c0b040f080607020607020d050903010b04050c0712030510050904030e090a02030726 81
    0x400c41d01900000300031500c261602c4003042d4040d80e1802642031b010389a0ba6a000d01098904008007003076454012015a5045601807080007001070040740c0e4010f805060900d81440450080e01d1302d07100300080032000514000a015021101000035030040c3c25075a4030000c1c03a291754189a200171603071100683e001620b0f1408500075401000035004c2404141440d080082c2d451002c1202c00034200c580003d8959a040e80c40240a414443da000700c81003a001003a401d41803c0120383c1034403078030102600748034904d080001041910701050010304910514962a15a83d403107010703000d04240120b2185016050020b41e156100007441482042c4603401409014501c0030180c0b102d0f4007070480e903501035484940300302c6030743c8580c09014061340c41444c0a59490159003045c882c08800306159008140c104801c1c0000d0001c1030318010300343c507400c0311002641c2c0c0300d1346800e8408007451031000b90080d010404003c01d107166a030295100741980d440b40510303954540c41d120b440062000c0540c0c202c03607034000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 873789757 1250 873788507 873788521
    0x2040501120c0e130e012f03010302030601210f1505070c0218070318110a0b0310090c03020c150103060e0d021c0c0c120203010f06030b060111100e011a0102030c06 72
    0x2011213240070070070f10005000c0503950100e821340712803906800c506d43d482e017004052100e145800700326400219440c18190350455000948032a01031107402035000f1a012103421000701d8052103940aa0700032a1201200114038000704442107103202052014507000024200b10b02034002030418550003002d80480d94080700340c005060070081c0011080655545150712410194507510558500410b405401c2d90394039030070080166103503041000340d10810300501402074480cbd1111815a00011404a0040c4e0720071021030081c0181412140035108240c000f010a2070b5a180c1c45058074040c410074410321003c0240d00b40c0e603440d0a6040b800580c030042c0c09091111041c120410303131040501c0c04820301c01103606c0c1d6030fa80c00500d801c1125030100c400b60140451900340304d24403c4800c1400240802c1c0d1640d243c1c2c59144070000c1ca42c41c14040d54011791610f1032801d1084462007810f003801002550140c00402c1c3c02401c1d4448101d400440b5102d00310308660000054420b2180410000c20955440d04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 873791007 1250 873789757 873789769
    0x4020f0108190e1606090501021b1503010603050414010c05070206030a060302060705070e0f0103031e0c02041811090f0402150403060f0e06070e1e2202040501120c0e 73
    0x109030540030100e0319401c2c501a1502d0054568900c200401800c0591300e90400032100081039014030103000d40d481e000c000030790b00031030043c1c23004040c4104c084000c2c8114000c90355513080700f10b88040003d8001f0000c10300300e815a101c180520700403001303801c01040ca030380000e00302e5a4884201010910a00051006180000040d54042c15044000c0750b01556903001c07410540201800300c0300ea8118801c00d125462111080c1a4030066030800800c2135490354401901b50048103d108103a04804005e07a0304c00b60151802510742503015208011100203181050741d4840003d4040710341d6100c00c3c4158060b40303454144d031405400d2030004410161141c2e401c21040e001c0c00461400b40351400e100000103e540c0d80300d114250400740b40e0105d103103000c880c170007801e101c8024034050034011059541d000c1901c031000c1c4800600c00448000b0441c0380050300048480390900722504044401e640403004010064010300b04030385081c0c98070941054000300c8a0180c3c2c111894017400588100c0c0c60307807040e15100c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 873792257 1250 873791007 873791011
    0xe0714130b04020c010b100921031e180803030f06120a060905070e130b0f060409060603050d080c280c080d15080a05120703090803030f0703050f04020f0108 69
    0x51030001070001200c102080580c0c01042c40e0203003030307550b9641111003030810b00b060509801882c030b0407007441828041d0365000e41d1100882603003241c0c5004c1c004030805004800d4a401c4000a96180d080c0142c100401800030782848006800311a0b80100001c55440000a5900400000d2414010383d84c4100c14003642685203140610588103000f100c84c0842c201d440354020050040c13014100c0d143c10540c1c000d2240101421b00c0110300b030881e02110116800c0701240ea085003000041902c0c42d250f07600000e02810a520003d0705092a000000081110000e2101c000c56515142c85d115aa581e8000252a0040e40c80e4803500601d80c1d03400d140003180201002080c1d001a0401140c510015100c00846400407651411159030381c1c4940001e001e8020f4209005002102c01480c501c150f0755034164440c089000031a40c0d00c000401d208041601850304800545005070841e900c9141030108200195410340e00800440d01c0c0c0700200f030000350b00300243c0e44210740140c001c420341c0d482035004440380080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 873793507 1250 873792257 873792289
    0x260c0c010908160c061d040914150f0a0221090313030605180303270a0210052502011d0103060e130218060f010c03050c061008010e0714 60
    0x1840301d04400042400014040c0c0c400b624801015000d16071818142c9804c0f107800c04400c0c0702e200c05175200500245080f19488400688000c00c207650949000000303518544011720560003a03007000e501001a10980354444c040b509603040e01511480f49a070308078071034040b4101141c41c01c907402c1c02c100d101035035100340c00825a01c100c903c3d044024245980c10802d54004035805911032060101109440740c1000c036000a20700514510304054100c60750b8541c1c21320544101d110140340480e600d140034050300940540140c0400150104000000d10540c000e48840b6400b841081002c1d994000d0716842030500c0780c1c183c541e800d00044c0c014806144d4108074441300c0c10103890700d02c08140c0540c2413034041d0244101c0346050b80300180318410440b40e4496041301d03440c2422890704012083d80d078a440c100c010303082070a000b01c0d001040e0800700c4480c0301d1400c07a40803520841d01402403100421201400719003041000f04111507144240507201d6046100c1e4240540d44072007203101030316144101200341030b9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 873794757 1250 873793507 873793511
    0x1020d140d05040602090103200405100e090f040b100f0603020903010219091406190509031c09030c050303070c050f1801030b0421090e04020a030f0f0201260c0c01 72
    0x81c1c440031200c290751080794211103064000c1840b82d00d950b0180918940c0850b41032040480f2102074481283c10b0155100f01441140c032136001e0802180900d241020841c130140904d00d051400030201c2c228141e06a4084803259100740000d80d0402c900d040301402d54940e0445500080c0c50300200f10040d4002154290703055500304603400388001140e0a1507507500c0b80c0e8550403180f44c5060085400c008450150034014401000496480c4580500e03c1d00448507509109403141180400b080c507028806403040c0d200d250280040207103d4110160740101c901c2400030300c02164445040c1604ca0050680c01050a01c85900a00c8146000206070b01c00c444042e0041100c25504005441d001900380e206546030100c0da42403009002d000d5030300c2210000d049820303402d042e410b00401401c12003d031241062048903400807d086640340c0a41a00440d000f02c04648502d02c2c1c1d041511030f04104100032408a48401d0400c4103028403583d400c030102e0442d1508000f1940c40c0032082407194003c00354001155 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 873796007 1250 873794757 873794767
    0x303070c06180b07080108030406051605120403050c09150102191407090e06060a050307063b040506041b0c05011416090608010b0304060e0109080409141501020d14 72
    0x41e00740c1c1c4001001c1c40c002c52890020f400d141358041d0003500180c00000180d0800c102c1030140540080c2100e02d8080150407008130a031450402c0ea0612518a1828000d240000303000000d00c10700140d5103581a01c109c40c400d0491300c0d00b10380c1019014800c41d28030b0150300090103030520300d10000314040400c2d0207580400c0a0400d103803c0d150815078540c028481d0076030341c0c0c10354007c809020082264841c8040d5901070310f581c100300000c3d0f5030321010f00c80c00c8100902d0300381020000202c50000b940d0307240c040d81e844000c8400345081c2c82d00c3d0a00716401c01d01903407030032000602924250188001c0b03100e480e50482085456460201e842d6184a40c003a1a01e40d00c4502e56a10440c40d41030031442030041c0307022501e2000500c42e000300503c0a650140d000c03c01190018094211210101c1e0340140c0c4c400c800080c0c840300f202c28907002d003545440240c0b030500003040002d01c0e0f41c002c1e000010400791168a03076800c3d82d0349010000700313a401c2030051801a80103000039002d007030113a40310030700c88035194090600308 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 873797257 1250 873796007 873796031
    0x10e07030c0905091c090f1202090118180803070807091a1e0a020c0a0b0301060518130507080106110a1208060a03120c02120c0d170f031f080706020303070c06 70
    0x42c5c0b03c40074003000140c5000d1082141c00c000a0f140b101616265620302c1c2c12141c20b40008030004010b024403202260895a0484600503ea00030444241d82040004151950b424200941e2b00101c0b03100d004504c004000800c098840c40040701611030030040e41120103a18103244c410b542010000e40c0094111448569160074000003806c400a010340c007c1641d140c0b0482440311841042e404518410b209200522109401400352210300c110b140608010604000003c4d00302c55907110314402d164501014058580c1d405002541a90b01a0700c0b5030982454859200350345481d8001c026102c0040386401002c40780c070880049800c050300a210318199030b00c0c0c1c2c6642c035001120408a02c04074580240140460500240c0b078802035034050003400400e800c000203d8115a0a140010018804005a01d1301e1091000580d00002c140f02221500c4e4508401080d04c504110810130b10400210f1000003544030b00001c134803064590644c06035003035445540066480f00010308044444a072240741c10218 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 873798507 1250 873797257 873797293
    0x9010203131418090a0b19020d06140d15020708040b0a050d1d0c1513060302030415050c0406031e020c0d030606080c2b1d010e07030c090509 62
    0xa07000380c03503108000c1c00010040020021043d03440c41045003400040200f800b001040c1d407800f0340d801542c020b6444d41c440c010b901c641c84004110340c1220740702050301007070084a0f138441c2003502c81143e5442041c07800041048862105c903500103218000d00c10700c0f1144028181c0241000c14400d158071070425880b80c5c82008603400004018000550100d1582c1c20078015011300d0950840100081d0301c188980340c040790300c80c200d00b640c8500442552080050609104044038880000d030400d09540b19182c00e8010013030752094a00307499407110b4000313940d58140c02d440386074014044070094a1500e0311b030030f009501402c1c0c0d80d010112004100409840b4030300d268001898800b5608010300100301040340d0203070446450790481c400708603401c030400440040c00b004407803e8020318101c0340300800d40001c660800014002c542c0380040d08182c20458403104010b046135240399028001c7c0b00b058140b24200b980c5010302c0c40003420844400c07508000d401e1150b0301c840d80242449003690100e5901e4540b20340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 873799757 1250 873798507 873798509
    0x1a1c0605100513090204050a060305040f201801060f0804030309020414040b0901110901032a0503010f1e1a120f0105030106050306090307020f3601170a080901020313 73
    0x10101d040000e025211802400950b0f0151a80c07480843c206070600b00800c0320700d151b5008090a0503503400c0410140900341c2e01c401c0b40355a100102c01003040f0381d0040c12094802d10070b10540202c10200d011000030008c61580ca050718015605e076054015110300844032030748050400d4007410395034070800015896500841108842c004980e0910741810f2a00300341034900200180030036403404400c18034403804401150303890b10091901044d1140b0041c0e9050000c118032070640084441e9605c80620260001e000c0e6040751800004076180c1396a4150240b5045a2900c2c40c1e480c61402440074400c601440044031200b600c8034041e9420880b02c00884241140190f8010745a007580b00010031044c03800340602c50251000754044c00c9541440ca0a082c1d590064030b00083c0b083c0203a0b454a403007616001e0320341c0d000204407695001c1c0d407441d0207040ea03038416007100600d14400000c0c00200303100218415001031624900000c060405e04ca84507000c198119050140c114002046611441c0519001581c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 873801007 1250 873799757 873799789
    0x1e09060b0108222a14010225060f050c1524010c06051509040303050a05010905070e12010e011109030d020a0b0c030a1b08060a1a1c0605 60
    0x1000a039520000d01542001440410901181c085400c885119204142403035684924810044510003850a03403e000e1045040503211070080c1c0090140c4989a482104400c20703000d903240c00010030000e071013503102e00300b030918404010b00b010441c49101b281c030090412050b141407814510740b5461036050a1098001944603440c400900c40051010309031240e0b01c40d0a800011788004000001074803100c5a208003030101513032440041c0f03805844078403004520700003d215001c68980791401900600f02a10010802450080089401c504520038180a02c14507158210201865002c1040510703a44124142c0343d52100d0521504510900500c51410644c2d5180790701d503025102458036014400c4518002c6611540700d40d008140c2941c0915000075076003940994030380c0d0b0010010080c4c0380301d04042c40c0b8403ea107035101201c6a4000352041c0611000c640c0c4192a65903800c044c09400300f0800342d4a40d03980204020011214081200180300004000108213241da800005a81c0c01d5206507031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 873802257 1250 873801007 873801011
    0x3020f150a3915060f0902210108070906050609061207020a0512091201051006110106180501080c0a03120c0318120506090d0e0d050309040e1608031c1e0906 69
    0xc2d0003040b01c9180501c400c43c0501108101080c601003c403020152544a200c942540c00038845010444000d042003245400c210041d8140d40e541c9820740d51002c0c1480741c8480709240c200d000c150b902c0d29408403100114000c1030241800c0121219846a07107018110405522411711140000b440c20b204403a200741e8042c400300c1c1ca440d0b07074000707005a4020681d81c10100d64500002c11150200202c0d4101c2610a6450716074414455404518010091a045030b803501440328240700a00401780c100340d042c0c0d403800702543d41c3c0c0030841043c0012002c0d40e0100a0000f4040700020101c140302c2d100d800d4856010745017040c03151003149601001c1060542080440007050307002102480820040c0e40c0d00701d5100c01c010244000c42d80350080040030350100f2140302ea0781c540c0d04182071100420685009400c001d208228100504924581c0c552500c00c54422035110181c001488601c080240c41c0c0342e20124000500700000c0980303180c000d1000d0b15401041448a00c00600c12412074400ca404280c0301d9000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 873803507 1250 873802257 873802367
    0xc030302011b09290c070803090130020d1d0f070608040807230f07060e01020a02060706020a050f030a0203070801051c150e0307080403020f150a 64
    0x600c910040080b000340c01802540a82081130b60070b0410191411402d029107a01001e400d01c00c28400d601c01c41922004601c00c245001c228000080000d00281000f40c131b4121040c0c040a0071051f24030380386032109500008010f00c2e0213080140d6001070182e5030b803420700040c800368244004603070308100a0350200d00740e01101020f41c890b202081510050102401c10180d41c2c60655501c036014411014010110412100c0f840350000010a80880440c448020760f0300c00348450f0b22442c1e03100702c5071151800003040138250b1105540003003940c42480e038006d00007501c2c004d910b85414010b13600c01080394081240400c46c8114040041000d5401030445140161b641d0074419001410781c4410780103030b8400d071018130a2211604040144400e0709a004440301c28010800805500904560246424a00000919500700700d401402001560310844803800d044803103905000c1d40c0e044030301d800c00d04180b0422640c1c180c20b00070340c1078004404409206c06c1c4402403103038003444902201042501d0196082e01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 873804757 1250 873803507 873803531
    0x606300f0a06060315020f19090e0411240711061e0301030b072105060d05122203022b23100c05180d0204050c1e0a05030c0d090c03030201 61
    0x2c4c0c038001d600d4217a4056040c14050761545507140300d007105034009120703040c401d441c0b185d0080c2040001465880d00403402c0d4601410410401140f0452091103a506c02074455403015403c44000140740d10389040c2400d0043d1541d40302c00070280b2071001c82d07024506014502c203403143c03031400d001d0f4a43d40b40502c0b503d030f51442c9041450810060400c1051202c90682c4503141112303098249050110702001045039110b42000c82c01100c2c0100c0e01508900550301c050100c42103030001000b81c0281c1801e0341c403108107125124030141c841030000039440300c0c840c821440317201c60003580601c2682252411700b100e610141d58020a0003a5880150540c000421949003460014003c0d0400803640c04014040319108510042052007070000100c104c5810220240d80d54072031490000340c856010304200400d09004075480c4c1d030350b0441030341c3e10024010075000b28198040e980542d4580c05041c0c40f21070450301c0d800d844219071341000c050b20800c80da807903030214089038210074600000c40c0a0b400001d502da0620f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 873806007 1250 873804757 873804773
    0x1b150d06150207120201080a0b090408190201060e011223071d0f0604020a020f0a080c06060307181109100801051c02180403020c030706030b030606300f0a060603 71
    0xc01d6140c2503400401d002c104801c1d2009452034441c3d07091070b01c4202035464400d2200184100c40c6500e400c44605000c1008004084008200c015020350a082d01c002d881d4400701e003039481d180175001e040c00c096401004140c850002c076005052060700c0c50b9098a80410310421004809a42c0ca04241e1000c0b03000c00251001d504c0c1c40d100b612200310007180600e0f160030100405078000d00307000d000d264001a10090fa41c42030098080034a80d010590300b25420358142050a50012070b070003407080c012500450924034000812104440b6002924070041e008800c0c1400200443c204211410304100f140c9009683c5207104004000c6807601c0349141c1e03504040920144601d2075032000c2c51032404450420160791260384405d0a8504e40d0a005400d81d00c030314003241030513110052140c0501c640c04010658517016000041c80d04400d904071502c581d44c4408002d150100c00320b4210061041448580705413208202c2818555040300485084050054000b0f1405e10110b000f6240c490307883c1000d0041280038 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 873807257 1250 873806007 873806039
    0xb2d0609010f12030c030e0a03030c020906031524100f0e12030d090f0605040b1815070c0c05031618020a050a0f0c050d03050a0b0307081b150d06 64
    0x82000c01c41e11a051540700f111210a001c1e0140c140520702036000101482a102c00105c0040640000d03001d540d030f072034050414000c80800300e10a60403100081d070b00742000200c00c0c0c8200300072400c14035942c507550360500e004582d9403290003600b8640700c00004640c4810030740550f0401c4559610f07d0b214402c01009010900c810802c91180f140324030070099045001095035110000000005130000151038850384c6414482030007000700342014104001e00000d18550b911640810001040210041c1e00c0b4944580b00c8468001c841184800402c00300c6e032091040703886240c4900421100d4685502c0002e14290290310050b10045083c1c0041c0071708043d804512060269026042d410000102c10140050241007a500200003141c419480918821440001103680200c00d466601c2d0741010000c001c2c08080710303011405130805004805500300000d00100321071403000540b0084000304001c441c202c0b4603c6071154420b508051b2a5200102c032801403242e00d070f01c800d0028002d80341c140d140340b0070026 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 873808507 1250 873807257 873807269
    0xc040b060a12060807090902010f080f010b1b0a05010c0e03030702090127060b0304030905011e03050711060a0902010e1f031503051b13090503070b2d060901 69
    0x6225400026884040c261090400242055044481c54007040e8006100c540d00880c0b2074481c1c10400248130302d050780801016030003a170310440312040e00201910202d2090720302c02d9150b690340d00108408843c2c04080c0c0740340c1c007a02090140c42480303030080d50700d44425907409513030316552081d080b000d09400484410043c00d05801840c1020207c0c4c000a203a0710052040404140586601d4400143e41420f8401012050002006055144d00d101c810701e41003294110081a05400007003407540c020340c0c00803c498400e28680240d000046000c4020f4140900940248041c110080c030b14602c3c207200141c410410000002070b4441f090000414407108480140c0c003410071700040c03000010030086848000003181c01d0200d0758100200c0c0340ea10000890f0300150150013110640040e04c0c900d9014051b0613101103681c141c10310a4407040b541241c16810004115a108100b50000102845401039111400d00201711100a032440c2c84445001a401c1400000c41c118042289078580403ea050151407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 873809757 1250 873808507 873808511
    0x51011152406191e090e13020d0f060204170a02041406011b05031605060901110a020a020120070e192919090e0111090108011215060e0402030c04 64
    0x4141e0010420b584500220309001510003607400d00500c1c0180d070f92a00100744500000269038500c01d008040103400c1c050340b555080400301103424880040105020700350000c00c1d071940e42c0784698503990800000207045480903020302001604410b41c6640d042e6080894025104011040c4104400c4822682840c8070f021982418030640d6680101d002ca43d0f988030f501418621607041c00c0282c514029212414107000b00061158200000420041e001d154003c00a000d940c010f40740190311409148204401a4000300340b2001544c81400030301c1c2010411220380408051a40d007041c1001c0641e0070200a5903225014415031380071901450b010041100307401c119040e26890000444e070f03031906100e04010f00c5c034446041c10f0745e6103642c2c9200c1c0f04940e00f50450101c0d5135a8501000e0038000140c070007035519206942280300360210884420401c165983d0145a00b006040013100c400030009842541c00c0c1c0040c40c4a6003458400c160140900b441181858030f014410107180c40f080b0310010b40030314 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 873811007 1250 873809757 873809821
    0x60a02130b040b0909090102040315240510180906030f12080c0415030b030d030518060408040902030702030c0f07031403120a110d050f0115020f0705101115 69
    0x190200144c0d81001c03030441e443d0030142c641c4071119001e80995040a0100c00386540c101500081c0381e070140f00c060f11500000d82d0b03805150340c0c160701894828820380c1c3e081901c1b810f8000380f8504c5202c3c0300c1c1c545c008060400b40c034981c40701e51a5048418030b820413120604682454400c0c0301400c0d101c0d403082c0800c0c0c036000c0315500d40900024a10701451141c000080340480350203520303501a401003c291200a021982040707400d45005020301400da4142003001c070041140080f4070000705400e4031464104100354603042c900000c1c2c000a500052995045001c14401d8400b441001e1020403880d005000c000c10b481c60450400350582529050304204070b9204201e000c3d203c401070741d02c2c15809032801c02c0000300e80d442d05258544503c101740f840c90105140404104080540300c40b407506840c420440340d58803045070542030765141d4600343c00d04c2d0740da0300140e0200300700d00c0c0882c10440041441d161124941d601c502c03007903151401c2140d13821041c000c480c0030051008514038010540b0f10240052900345 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 873812257 1250 873811007 873811019
    0x10606140a0f0509010e040905010f060503030f030f04020102211c0612032106080307051014150613060c0201020d05160b09010905060103030c11010206040804060818060a02130b04 79
    0x8142110b4064091001c0800c203050b4a07805820800701d0801e0240c0103010b40d05192416500801c4800c0b9007440d81d5280c401d0203d0107050000948143c4800e0404091030754480d4480751041031001003040b0b045101d08035031010001c02100d10b28103018100c11049444041c01e039010154650b103500250440c80c541042004110741200440c64156054200f20400c0d1022498151040000c00c50746100701d412312030700142302074000000b040254001e00c01c1d12401e11020030320b80c0c1510f082540c4403403805c1c0c1e1807001c10900ca55194074a100c08600511541c0780016203d200c01200c0e8096011030701081d0010076140c15542c050218035a40d000318984203140c5582102d1000015401100191040945400042200d002540a281e65542200485406682d6450018240725030000101e811901c40f01c0304881c59400024002d00407580300d02014241402c01c00100c0711150001c000325400f05050032a10340700442800b03440e000e0710701003c0c0035a6505821901105103203d5501c1001082c07020842001381c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 873813507 1250 873812257 873812267
    0x204141b13031425030507140906130b0d12020d020f060a0c03020d050a06240203030103031407020d03180b1e071a0705091305090a110a1205010606140a 67
    0xa5030391008000032000c02c40301902e450300078280004030302900c0c11080043c00e282c40c42c204e1004c403803040c001c8400581e1544095411070048208a42d048180500444c03441e107408418254034100000f0000340b46c103d8000000c42ca051101ba00f0364466407030f41084c0308459410f1103407010007515130004081410009140540d603401c020420003246a07140101c44641d40b00e80c040350142d45680c0000c0c032031418000c54400c000d109034411507216078890866103106190840c41e0303100858458000d54210380c61518141c62000c909020915561010004180140ea40219100000d4025526003003d01c602110302e86100076940c120004803481030000700c20715000240640049091810346a460f81c0d6079180c0302d640411840165050035500f10104512280d00c800035040c80f031801c503000e00440c44e104a41004860007590300a0440e04000220030104403c41d0105024010203844610b466a44240c00701070608602e504844913512003404008a40e40003024102840300307094071a191150724100a81 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 873814757 1250 873813507 873813509
    0x11040902031b030309060d05151807080c070b1e0702030408070314160e0601020114151e0402040602011b080601020304090917040b07030908030301060c060b030a0204141b13 76
    0x1c88482002e41500345031018401e43d00400b10242100d92901c0c80d51030300102a201c01c41b0001050f120043c55142c040c5846803840b00c0801040c025010130761a421011030b0f054400a1441c45050002c00800c000500340d05941d0303116000c581841c020102c007402c10306018800280000c0c08540c02484180284035022402204499004036802d030003500d604034807420101c85c40c0c0c8184c00c0c03606180000502ca142031120901ca05401d034020840000c0b038840010644005031074901c40042c0c00000c400c45410900321001d900b0078403100300700d007444811001806903030294000c000180d44031001e801c040301940c03141c000e40c00041e0a14044600d00100006e40d240118410a070040351502c2d6050244011021000c03070b25400d016a441d40c4503180c0142d0350a50380052011000264840717030004410b00c01101380e80c1a9041a95541e640320a00d4903024068154658426418010b20f42058010307591380c414041400500242d02c0214681500001103440f0819034002004030f0030031030b908003d01001c0f2150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 873816007 1250 873814757 873814783
    0x110a080402120a14060906270c090a0204050901080d1710210b0717070c0201020f10050f0703060317031f030c0f0b040b09090601050706110301031104090203 69
    0x20045603128000164240300d000b00701c0b015800f80400c0841403010b5084002001c181c1102251079584554102a50740c110413144082004070003903a281600d00c0e03510b03907904d101008204079000b105024000441032a0280c803600107203540080d041000c0e0070700130040d40c01019800042c10862204140141c8001261203841040d0710503500040c882c1e00d20a01c041d805096402d43d1141c042e4071a0850010140e4103240c103940021060000030140d611820644010410880185401e5255080c0c00e440d4100d002d0300481c1540140c46610789165020072640d402e5281002d004200c604240011030f00724030010742114205401c151007803000c80e44080c11400901400c4541d17030750369580d100300c14008104a50b4a40103420602d0030020500021003072400603910a42e5607110790315624402e1414a110b144940003225806001c0301c102c42c501205e00b2540020b06041540ca4268240c1e580d074202d841d100c60741d03600c02c08084012700034400e07864025056402c0590741000040d065400195598541034400d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 873817257 1250 873816007 873816017
    0xa08030c1213080a080d24140607060f06060e03160e1905041101031d0a1502090303070f1a060108040b04022b1e1211030405180601080a110a 62
    0x905006060300c0c1e02c0e9801040e9210943e41c215541d4070300300d141ca922a10032110300741d080500c00c040d40301c4920288443c5150380080180014a00502c0c100c0d43e443c14040310341d020200b801440c02240040c024031181c043c0c3c00c17000007800d6041007006004c003070f1400b81c514003d0703100c0503c0c681040003414424003640c0d0745100b0a0071541e9400c1d54600c0e040380e4000302c602140d0030802071100300300d5560212801050709890502c80345007503440c00382790410108040d1145c0d6010340c410001041c1203000300c0801280110025181240d02c1000c21703d99070004000300d0351074070300d11094001d0100c460700300034800650040126843c104900001c0c0350680242004c1c20300424400461b00f195178003a8101114641040511419100b0b0003c40740044030580054074190310115044c3d010041060207000711640c810b410b2400c05808900440d010440c2806413000340c0301c1008085074036960343c0f81440e45003299a00c001c1e01450194001040344070702501e080c0e1414180800d89641d10840e80698850191501d84 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 873818507 1250 873817257 873817267
    0x301060e1309050105040c1a07030302090a080a0f06050a0b060403151e060801061a0729180c01111002070201090306110c120a050a080408070512090a08030c12 70
    0x4004041c0c410702007040034600440c0204110701900803e12550044003c0580e2990f2000044110028118201c224200c10486400028000c0d0702402d03c1c000302030160901c881c0c84102e228500940080b054130000942c110b4002001400c1c060590b1001c0e2162052000980013004207101c2d000307134000207103100d007001044441024151f2101c03009800c406980084080411254001451107000b410f0071f0f5400c10340d012484d000480040760b281c01300015403d1030410031303807203200b02a20b083d070754030049500d501c040c0c81c0c4030100780030501d028003c440070700a001030a260100e494000310f800c3d01414080310541507483c4200210710300c40d00301039180025039684030302d2004031040c4900360801802c15184c1f0340b4203442034496101030403003030f10907001b124101d02c4200350300c01c001c0c020100c0080000b1410806602101d115419040c0c00a1290714841d040c003401d6512a4140140101e8445c2094008a80d02c03a0620701000f10f04010300200028515121491150580326400720310401400540055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 873819757 1250 873818507 873818509
    0x308040b1e07260c09120a05030d02130b0a02150603061009050c1c0b0406050a0e010b0d02041502010b0a210803060109030507090c030b0f0607030c020619090512010e030301060e 78
    0xd02c6048004410b510483c54902445a0318840e00320a20050241c02013244070b100c00c900014000301e005800000541c108850109200c003c3e601420030001c0350445032800050900382c000160010701c0d050b8025160341da101c850203000b084001070042d0303c00c4c0d000500b4814940404414002601c544041c04240c5a0344c0360002c000d01d10802583c0c1c407a0b00c0011170f041c0c42c104400d9003c0c50321524101e03410300007103a075a0f04110b60240c45004501c080f61380500100844006240202520b20341d100000d82440d603180102d02d071148942c1900c00140c0d440d5030204c04d051501d500f01201910200c85154640012403404810b440d52030030009002020000209100385c1c06075038544010340e03001c4119083c40d506c0d155080c001c1c1c400843c0c010301007420001202c016141441d00c1222111014000703500700382d69a1022030388005501012ba0304a2010402c503c1d00b0461031080001c504c41d1a294403a40e14540024805005034004007581e15034544000741c044d1841c0401140d04494451400c41c050380000b81c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 873821007 1250 873819757 873819797
    0x907030c0306120317070207050303031f0e011d0c030c0d0914060108030a12090206070609060b09090d08010819200a0f08010b182d040308040b1e07 65
    0x5044909078400f41010f0307000300355100c2e049102ca090381402e10764207522554005ea90b02c5010b070044551682051001450060302d140d001d0600ea05110501e03501c49070749440025041c507007070700002507006450100003410400a034000390441c0c1e020740c02902c0c41c60503d80100007405a441091340d41e0740c0b01c030155024041c0e492841848c160401d0140c0c7c00d9941e54207a034075620740c03180c001440440e1080c44107115424180c401c1c0400c468001d483c291600c00d559448500402c6002c00464100b03644e51343c02900c03a02d41c140c2d001d125680e03c2c0014400e001007203401400b10f0703005070300640b07a6138055844044101c00c980d044289080c3c1c010007401000d02070352044c142c004030001d2201e412000b000000107901d5400d40070a811100500000c010030f4070b00700148859a809020208407040d8018045403288001e032403501074031071500f101190201301c0b07240c0c51400810143d50650000e03d8107400c6c0710030f000d58249515044408a11700140d09000c42d00b08040e4160010f14450600400c1601d14900710826 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 873822257 1250 873821007 873821009
    0x30e010207080c0d020613020109091d07260606060403080a020f1207060c0e0307142403060a0b19051605011b0906140910090b07080a1404050907030c0306 68
    0x49100c1c0e440e800300c2003020faa82d43c8041c0040340148255030228803c0e144840d00480c0343e07a0107940b51000ad505020303841e00502190001405883c801100801000c9424042c2c1c4c00602101490b2f8402940400c0d20505c4070701c005019901280c102c002440740c3c0c3d0756504212422203900a24070b507251000d08c90142d00b8020780c2c441d010201c0c0a88450182c0c8840914020b0403042c2c842c450420040794080d0045980445007800c80c1c2e016801088140505d05040c10ac0820500380201200c02602140d50f107903800345158895001000c07008814842c803031506460000280488000d071a08154150940131561880034504509110000980c4048618051104586160000000d1112030550300d210301e405c491103032078130b00012042040812024403c0f18003500010542c0341c214280310f0440c04101c8103161940c9803005002d881000007030b2190381036000d408110701500a0b2500c603e00200c0140c82c02c03018110110391448200000c0c4003075964240007641041240c81c001540e071180c0c140550060a203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 873823507 1250 873822257 873822263
    0x609080301090b090a0507020d11121c0f020f0d020c011503210e0f120c0a0e012414030a0b13090201021005090601030f081c0603021e0a06030e010207 66
    0x4004008900403025401118642030199600c4140f1780d03079041044210340003a2120001a04080d07000d05034540710b07070b140c0d5280c0c00000c0d0aa95900000c000104150b40c814098450300c203003003206a10024415118246240d10b000e0829407401c210407401e490103100d4001d02909195020803d41c0384003100f54003282c40f00d06501c215400b003076100e0400641002d44d90350f440111144004810488500c95202c100410390040d0044400c440a80c04004614180e40a203020760f03c01d1070f00070b0480381e031940c0086004041c81c01c0d125000b5410b01140070301c031710307400401c0a501c03e43d811401c550069010a000b040000d500c6226070b240d407680c04200000d00070b1401c90075440041c0c41ca4800d1180400c0d03002d0140a4130036000c072a1a001d03400102c2e01036031000c0b50396102c15001800100b0204649040e1030126510030072400703107804040360080440507402440c40803e1560341ea024000c43c00c00800070303070103e50410506141081d40130002031140041b40585c6042503165400100c80b81e401f5019100c03010381c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 873824757 1250 873823507 873823523
    0x308030c1e04080c0f010503131110080601021507050d02030c09130b01120902030601120215040e01030c060c0b061011150417030114090c0903010513020a060e0a030f0609 75
    0x6880200041d840d006806501e005018a40c5050080d1400c0d0707283c3c40f07010006854042c2140d07501088649034400c00300e070a451051102c2e60b5400c0694440d5950b00100140f501e03600118100351000a140507483d6840c0c05001c443c00e000d00000c250031038291603030601c9200c000b6980b940c4900d403200c0c85000e640d942c560004070341d0203858100580e60304100300c014000c0c0c1c1d031090840041c2a030201030301c0a00364069019000800144503281c40301c4101001c0d07c0c006412442410150700c4806a1075105030b0000380314180f01c1005004200d040c254047c010b002030326080d0003900e01912a1805002d025000c2446624000d4000e90042d000c4d50a2185c0c004000050310380002e0410100f0445a0044504640d401c100801c0310344c800440101381d9040e54580080c0d54082d0041d14140309652002420048103584288411034055900740500d52082d014030084040502d4207105000e001ca0312a00800e040c02244101e091560315a01070a40c2180e400069103c80c04c0da5a040c000b00402c0c0c0a10b0141a400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 873826007 1250 873824757 873824797
    0x2060a1e08162313120c03021519111f06150c0c06030b040f0207080702031b010212161205040810050115050904060503060a0903090e0108070308030c 66
    0xd40041c0030074811072440080c80d075640d581c0c4008403203040310702141c02c14a5000708143e41d545481040504020042c400008040d6a151048404041c184c0c400488402032030a405004504007580c80c180e0329030119030ba00781031050400d00006001401840d0300c00700100f03d8100c075850399040181c0c1074204a4a00e1041419100c500594068121801030580401c041c0302203540d12441011070a041a4000882a100c02d0800c6011405460300382071407540a51551550141000644003d01c0a5807090350b041f6030310a542d1041c03600b09a0b07c50341e203064040400d07040e40300ba03980102c1c108030f41030410795035035980780304458007181d5400000f08081c1800802a64041145801c08024020b540d004811a040f0018020b00d580648209024003541c00742c00c018202e2a850240c0702030200c0503070042002c9101600d03a400729181482c1250b00780d10040d29090b80c501419007051000e009800d40030303ca4140c139810203070309591f20704840c4401814400004001205d01882c007054030211240481070701000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 873827257 1250 873826007 873826067
    0xb040f0c021e03030f04030f05070203070608070201050703110a0e01180f03020a08062202040f0510320609011206030b100816051201020702030703141e03030402060a 73
    0x2040035801d0b801c10480c405111400c811400001d803885645051002216503580d40d504450306111022101c051050174058100181e40900c4840c1c0a006150b4031101c82e854140300003030035a003010b0101018103180c5030210340e02e0500001110100515400c0c601e0482d4220b600403502086c03c0c20134803002d040d08140c0442c034003041d00fa114003140d008990341c0848585620792140c4902d81610810030f21440c07044002c564001c4025450b640300e000130b000044002d40350008009860089982403c41c0c44005020b000c214034803294060740e028103003112070300740d125511040d100030113110380244640c0011500c440d05078031911600a402c00100c0c010701555076a45072011074500140c4405020a8182c030010403180000900380c166075084e12400c2040901d080d040c0b080d083c111a01749515950200050005a1820030510380158070840c500c80144410b00740369410214403148612551349540c0d075054541500000b600d0308250100c030701c20390307459000005481c892101c03020f5000c4412284584036032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 873828507 1250 873827257 873827263
    0x90303040605010815010e040f05030a080709090c080c030a0b03030705030705010f09120c06020c070b031602010219120b0a060203070b0a060f0303031d06180705060405130b040f0c02 80
    0x140d200d07000902c51a41c032240100d03203900e40020a1464266100f00401002c4615007901c0d41141c0075403d80d4003000007a889103819940140e030b1680109800c030007403200c0a603000f540e180080080c404200f000c0050050003c0050001415200e0240c2d40400802c9000381181e00942c101103000301125503403441850030729140d400104c070542c0e180d407801d03541140800403030040401c0e4a0340314140022458003e241500d4008651405440c40390f0b00b0f0240703121091042240401400d02914140d4880c60b101e0f920f02c4070010000c450300110390040c0501d8850101102d48407031070310301e1403e040b41c9281115070b0b400004c100c0e00c01300a501403218076001401d02d801000802206020b45151129a0307581005a02625900d208202c180f0040c0101003020030b00c244e01000f08060311284e100080c83c13850040c58a030113001d0f0b0b01c1e044200705800c82c0840020341003090100514080d10390070b003800d2401d00000d030f80308002588110500e4803290307a0b00d919176940e846030003218140703201040491004400255 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 873829757 1250 873828507 873828511
    0x109091d03072006160308090a0b070e031903020c15070f0305121003030509040b06070501062402070501080105060a0e04060611120408031602030a0f0515222603090303 74
    0x607090f4180c20021614101070003211050240034078240d82107456540e0840b10040c0081603120385001c1c20b08800c0c000b036813074510940a491aa51803019181c000010141800e84041c0c08030001c50760040d8490010b42c010540340c03209002140d204404681999050a0910035210b005041c0102e0f500c0823410940c0000190507a07149125080c0a00d0380d40d005500342d1003a0602000c3c01242c0c091107180c80d1480c01d0b0b0803007200b0300406441c0714100495680c9607030945804d50440304180c5448090a01c40e14420749200d00f45e059644018a4010f2400700040d00300032042c01080d00803100024030f101c1e01c600406140d002c407140540308100040da80c600040c5903000b203800f0080d03640a0100d0190031900750307806640a0ba1031401c007851806115102d100c1d640210a441281c041c01500b081c11701003200b2540c00c55440e80604040d10751b18117113a042d40140700b80148003001042c00507249203c048220f03003542d0507040c1e00903020035044500130748218100035580c1d8240032076440003040000030a8044042d40c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 873831007 1250 873829757 873829793
    0x7080106030506030307020306040b06010e0301020d0c080702150705030709240912030503130f1e02030d0804030221040b2a0c090f19050a0e1b0109091d0307 69
    0x103443e0710003091344138481c2c6140170390305520031008200400c48808587d5000b4805050100c6510300c0440402d099802113092400703042e0303440903c40c03140b580060080b5840400c600c094035001056600c60540c5100c060320350800c1240100020301c0c00c44c020340b4204081e00c07112611000c55048014000a44174051440c6000104403050000b158000080d5100708541c0c5074036103505503500c18000701c034407843d4124162003058120b2420400b0800d5200c04000e1a40803428040d014035503401450f01c0c220381080f0700402c1003042c0c0204004a6070100d1050380300c0752911002820800f40d140000c04500840c1c104250080c000a01d641105411034003005a0700c554030401c0542c0c03903002c06510344a2000e000c48507007102000000a0425038030101c0d41e40d10400c01000e510000403040044001ca4400300d891100c0390350348035035001030540d0070000c103102c04840f0740302500074800c158002031040d42c0900c00c042c0c000e0303110130400ca61201e04c0341e005400400850b003169102d200301d04103081c0f0305810f20020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 873832257 1250 873831007 873831011
    0x15040927060b190f050f04150e04171201090c0905030706020a060f060b0306060f0c16080f0a0201020c0607020f130204060807050f302401080411091b030708010603 72
    0x40f403806031425040c1220303d0800148041c5244c8020301100c01c0c0f100c010b16500ca90380e0b4928044100c040030650020f00087c0601e1091b6250900c3d00100f01944100451001007007401010205a0f403414030b5070542e900b42001042881140340700380c4141d141c0d0b4101c42e6050050074000302c0c0d0035500040e410000f0340118014002e0ba51240680300444201380901190080c017000004c2950409400030062800001851490010a510b9160401c440c81511940002107883d00300031107101040368440c200b824070058041d0b004542d0010b5035598041400ca03001d000c010a1a0096690300c95409400c0c2002504803120100c001c1c000030000d40c8280181004075080e10041800700e03108406483d040145242d07010b24086100074982e02e4900044044515904007011a01d0418003001c03149000b150b0240b40380304101030a51f03c00196250607402e03241046044001c100226070103a0640340c0d104019285003c1507200c0c02600d2024a5a428115403606000801e110f0800d9220b14131504858041d030341 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 873833507 1250 873832257 873832279
    0x30b03100231030b100306020f07060e011404060b0303090a1412071503111c0902030606100507080f120f1e04030c030e060c100b0405010515040927060b 67
    0x121058000020b40700c07400d4400701440610000d2404c05015420466078141c01c651943c1c0d0b0b0742c0700c00c00c1c0c0e480403207030309000d82d0b01054600800c0300e94000d501d000360040f8002e001080c0740812404220034002c0014185a45400c04007005440520455132005009020704010030344804040d416441e040003040d00a2203038448082c0100303800301ea00000e170381190b407030000f14401601003100a070038032540c98062000c00304500b5212500c001603010b9224000c00c400300d090300443c01054240a8020250f0340251105205400015401011100340e540d00010f507603201c800d040f11000c100d000380400445029151800d11401c4880414028420143e000d019800e541c1c280d60040c4a6080c1074400402103800038000c1d82c002801804181d0b0500f101420305420042540d0a1071318082a02200441750380d40c0f914000c620742060701440e8050102a9862550a60380144141c254400d1f4412011800c2e0341d82401d500407802c61844544501c1d211009400200d182c3c00c00e08002c11300d10301401e01c00c00d07001c0f05c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 873834757 1250 873833507 873833557
    0x12130504060303021902010509090702100e01020c0d0c0609170711040219050a030b03240f06060702010513031a07020c010c0c05010e0a09060605040501020d0e0a03030e01030b031002 80
    0xa4006a0383d00d6030241032114001e0b01c2c0400e001d030907a42d00f00d05105003480528800c0c4c6801c1c00300791142c00d1640c010409a8965280501129908014265180d00410134400d0b030316030025519214902c140740a403015000f50034a10000c1840b4100102103091600c1d00341c80f4407400300e010345010390242090444460783c65040004a228084040c00d044144800b20000b07140108064021f01d00381d0709011903520f010300300107802c00ca0b0030440c10404182e442c070051002d12680d100b1325070203503a10460950500300b00000030924004e0710300007810410005000b4070900c07801d22010300215440b101c01d0b6181001d5048a4210f03c50441c1d848005118952030040103602c10200c07039803c181c02030a101c0031310341080011580004521a0340390002c8009000082114251146000604456454941f1142484002410445200c0c4500b003000f060b64030008080c0d580c40b00250440303605040c945021a40c190050b0003a1070031b0100d56926000d2a4280303031004e51250014034440c41e421480b0451818402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 873836007 1250 873834757 873834761
    0x6030c190e0a050405100b1806060c010603120f090b12040c080a06140903090901211704140105030903030f07110d0906080c120f0403020f0a1217010320010306050312130504 76
    0x1c0c103d41c2d03121748e45c00c1481c8110b0800b0017a2540101c03014120b2490a0843c609090075120194021100c10180036081001241e003c0c0c0111441e09062404007181e91800201d001a4002d500f90450284030250220b42000708001e00c001c01081808241c032190b0201c1d0410500801d00990008207103001c40e0001694410040704580e01000c008107400d2541e400d0070111240c900160f840040e020001440d0300010031a0040d020800e041a2842141c1d16030421a060110305164a045414000c0038801e102e1028404070540f03520507501460340449540b01c00c1c00703c58110703903000c0c9504280150b20061904592040e046c0301030704c080341c4400007641c5884200b03011621805902c41e454140e02400302c0c0c1c82c60100078034650007070b000e0301c12181404000c680203030816000c1d900c1110381d030070069445041c50740c05c1000103e4082d140030800b074040d80b40d520783c20010080e18440c0e070300380008210440c200d41e000b640640040c01001e012100b040d4004a2106a1640080128424103409040c0013030103103018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 873837257 1250 873836007 873836021
    0x908010c0512190e0307061a2209170d0e0106051002100b060717030405011404030804060905150709050f0f0315131217090606030c190e0a05040510 65
    0xa1482d01101d96242800307004440c0e1050039440300070762219141402c141e8200050140103004050000340401610800d00c51803000c841c18130302070b00591604804c4441c0c000c00c400070712401e203000800d00034010b103081c88c0108460081d400401601003083d014802569020695032204407000300061501d03a0100845a2000c01e0000c00503405034110042c1400103400c0121000b4016020a09000e03150b03441c0003088403070007030f20050005d002c01000f0520000340035491150b541d1105284041c20242c4006020a90084c0302501701a20f03140e507602001810001d00d40b00d520b10103100b40c020305040d0360007800301095111321032042d2801007003400c00d40f5111a0480140303c00400402d64041c403004024080400140001581040c403428078002c07400c04080000e80c0c0d4840d6440d10140703148a0350340029604060003240c895030121041103640c0c6c4000880012914080302e006d0b06401d40a45101c040003160f03000324401000500a004840d201343d0440e90040c1d1094007030302c1010203002081002c68510b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 873838507 1250 873837257 873837277
    0x30712140105010507060e07091509181220010606030b06090904120207090f09061d070611010b030f010903090506030f0705090414041b0504020a020c0603250908010c05 74
    0xe04004000c42d6004000402d1000e200c2d910104811500c482000d04100c0168846099a61a180d2800c1e4481c0e034204c152025254481c02000104001c400000c3c040451283c0240028066072100700000c3c0288502010690401c2d00d0f010801b1104003203a019061a00c50480403030304081d120701581c6084c205440010601600496050340c443c0ca4040b09070701d0190302003095008000b0041440001c0c0d0040c40c800d46000c000210301c2c0e80381c0e0325008084034000620b8102000d0058110801000f021841d0b9045510b80e241101d04643d03031044075401441d41c610169407612540744c6910805006404c0008294082d40b6420100c41c0e88405020341031104540c0b502c5c50594990006249500560103441c0b5075002410000f001c90310f98642100d030210940e030945980b001c0300d848000003d805540200941800e44095090221408004e95140d415800d01441101c0210000e01c81c2c0300f184050340154200080080c140e014008805842f103c2c40d40285e101c1542030078080502240070b0002c8a0944078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 873839757 1250 873838507 873838541
    0x50709140a0c14070507030c050607020f040e070b0403050f011404020d32011b050906070f060b0306040b041718060a030921120c05120411040f02030712 67
    0x929030890328010401180440c2c00d01041c5019440c161000c1e102801d070040c03241d00140450b50031410800c403602c2480e031010b440b0305010480c190043c1c842591144611405490105000340c2082c1c0c454240070064000c20000d040c00b0500005015000482c489210004002006050003404040c0880c0d603007264065041921280424001140c40301d04401d00e00f0b1000018190420f401d2006034541300880440c0d020346c2d1a034140a0406a00d41c0d00c40720701e81003904100e4a814240030204540c1d0145003405041e004207404400d051201d80d811608031380310001c0a903550f900c0d01d482c22080d131542c2a5025136040641d05051800490348008807104000e091541c1203080c907428040003269800170b039042003019100c0f403071000051040040f248001d0510458401c011224241c01084040c00f40340b62801c60741440074080019401200301e920405400400302080d03a22401c04445005494004a400c945020400340d02210344d0303800740d07024042d10313500c03241c1240c00e100c02182694907040807075849030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 873841007 1250 873839757 873839761
    0x30d09050613090f1b0c170a020307080406020303010f0e0402090c0c0c180105030d050f0904180b01030503040e091c0e030106091406150c0705130f05070c05070914 72
    0x45810700250075000d90100414000e591503d040806603021400b00c0303d2003588499065004203e0242c650030110f15500d03001000c1c458a07120007040d00140107000703001600c0005d071411503500c2031003100c5002c2c0e04454159590303907646030002d68940c00bd2260080000310300d080403482c0440e08030707414007958008100310020344440800c040641e0001c9040b0b05103216120000c1e20540f08e2203001c001411400c182d90031150300d05824542080c0c14405a00c1c1000701c204028201c0f414140207a4002c0760081c1c0c0c2c002200844c41c0c00c1000714048101d0050301401e40003000008014000004109944141350305403070702c0d01c54a00c01682d911661050f41da840c003412454008507442007413003080c4207400030000b00740c150b81c0c0c505080c1100c0c0310708030203050384c0014020484507040040034028a224824107691601d185c030014a5250724040c040c6510403000f5030503518528030541c000c8107441d5102802040345003000c420241108900540c11a0a80541000019110645c0c03042d1550320a0440c42e1f4940c503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 873842257 1250 873841007 873841009
    0x8010305030a03180609111c050601150c051c0216060203180112020a030501080c011e0c0c210c05090603120318061608091605090714130e06030d0905 66
    0x3616000640b0504100c0304c00e2001d000c9000360140000341401342d207200350340b03210200500a60307030640f201e1113042134980700340040003507000540241122411594800c50706c0ca203180c02c440510381e81138054403920541020341c200458003507066003081d8845d0201c4000070314010301340b44e0701c1080d40310300b00142c1c00c20b0140c000c51089144141c0c12140e814035281d01d8600aa1411400301c0c0c202c2c00c4200e00003aa510010b006a91b400c03c01a084400d003420180301c103a03031500071030344183d444140c4040bc0005032036004081044c3c0071a210003601c03901141c031100b15100c2084e940c9102041c0070907280010210000101428409070050046c000680034260013148910503110560000d00419282101c00c141074075045018046103000d046688110451003125810062601d04041d004900d560008001d50076510000d194000848800b40c3c1c4403200d55845040a8a6543c070055080031101000500b1194030f02032504580c065a001d4014807289840e04c000749640c480d003041c1e2a5000c038a21510074072076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 873843507 1250 873842257 873842261
    0x180c030c010c33060509060f031c030b0d1a1003050d03151502061f0b07031d1203030a14090303040611190c12050c06191508061608010305030a03 64
    0xa1190360310b00c0183d44020841103050303551000102040d90b940c810f03050103540380c01080d103600460101d901220600d00c8500090702d942030f1030f41a01c9500b011a200712a0180650841e03810000000d20b130071a00c0842d81005000c0c1200c81e1102e41c2c603001c88000180040202c052220150398006004002c6800201010340042242200c0c08090640000002030181d40240702c049428003603501508a03030415074026401c0311034a00690b210300e22000004e200034110142501d15032605072914a02618201e0100c508401c01c250b006500660300e48508828441c00100a600800440c80f01304924607100010503800903040e682c203060350700204042800b01e596a08600c0406c000b0640440c6461140003003030b0100d020710304d4030401042c14000d000040c031901c65941c040300391140c20403915140500c11070f40c0d00c0341d60007450a0ba161803d400c0001d0200310a030b229101f01c3c141d030301400d22156292402c80307a594204039410700d91a26a810312000842c07041403144d0489510200860a00d241f8100c01c0d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 873844757 1250 873843507 873843533
    0x207051b0a05030313050f2b06020903010c0206041202030a020c0d061d0607031a010527130209040f0e030301090207110907030b030d0f0e0409020303070209180c030c010c 75
    0x40d001c030140c9400300710b540d000e00040c82c401c50b0400c14130f000702e4a00700a00034200350031282a031082004c2c01c084140d070280340e40d0b1440c88000709501200b4062135464408024010800382c150990310f41450310204070f40000e00135008500900106a00e050007080823a903910030784c048240182c02c649150016420320000d190750180c070801e008101d13504c2148200d64110040b001240107640140c09002c5116014031400c840c0000d0030f00e04101004540f800600a4850041c40ca16604062000c42e080d119802d0002448024020120300078000001240c1010b50000b003c0c6034442c071b00e000251910640d03207108a00c0c5840f82c0d40050350440e807130701301c0e000300941080100307598100798002003100603581c000d2031500c180c1080d180068410254400e15162118023039010040c0450820744081190300310000035030643c0103c80104038004688003103411801550002034001c03007a00144140014164820090090000101d5080b20012410942c1c0c07400100c001c10f021801c07205810010501d07010040b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 873846007 1250 873844757 873844759
    0x61905010f060c05030d0504050a0b06010f081f270b040203070c02060d0b030d0c0b070e1f02250305060c090618190303110c01090528030803040b010302130207051b 72
    0x2411b00400c0d400300d60680747c040f0f03000c59180d00103d4200c02003040e00d0804a400500a207031203507e403003d64901405048010b00705040782802200720803914841c44d9a08070107084031100c0b01c2d82071000c1e40e0320102604007103480c000c0311074200904039480342414401d59215a800d951204011000d540034484030344e01151401520685070302411546440400125500c60803903919085016814182a200f20344d01034502c104100030900c100629988252140402e00c207000c020742115041203a00364540100c0e034180c074522040356001c03020703200d4003000c68000304d90181090300d125035615a00701c0300c42d2284120495210700e040c404211812001c404002241d1400b41950f202e0003903c10100c0c003541c05a071300440005003e01c2c02019040014040030594020a0030102d11090800000030002c2c260703080c074550760a600c034031002c0394006000d15030f100039038124502c0c0f50f403400c1ca800c144040700003d0000341c1c000c401103540100d0913030072071085580d155000320181c11240c1d07800d040b112114007181449 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 873847257 1250 873846007 873846013
    0xb0a2c0d0f050f03012c1614131503060317090a0e01124e212307050a02070f030308060d03020f0d170105031f020f0d0905061905010f060c05 62
    0x129040c00244000d004040c07030030045502e402005401001054008e03000c0242c00801d000c41e6880b8050700ca90301c0300b42c4060817003010810400603400c03402050740d64400b4140d070300c044803212030100800b0f008000f580170944140000c90344411148905003400e00c10742e80c41c0b0030300c91805004242c000e001c1510200d40c084030f641460a103c0c209950a00020714000102a003e094502a00c00c000c600800d4203681c908001c1011040c941c0b2900703c0704440c1c2c00d1180015242c0341103200c0842e07410142041c07181c4440c06000d5038145400000e000d500008410005445410717400301c2c03032440c1079078160304aa5269841042d20b641d1007062201c07044000d002101503100c1e039030f0502c48103102440f0030340341c195032990b0307215400d034107da40382c0344196060340300030701a0f040030084581120981d81742c681ca204480b00c0160740d8400254084010703100e6118840ca01e28030385149581080004942140030b890300981d6034001d409114030040860701d0070b2056030280740800404012140c00341c106004614052030039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 873848507 1250 873847257 873847319
    0x12924071b06020c010e04200d02070b0408030a0609150b0a0908011a0f0d0b070507140604030804030e0a210302070504060e06011b0b0a2c0d0f050f0301 67
    0x40c1a1410032980245001d6040005280d045583c0f00e00004081b22045805002c45210011002c9222054880e040044a00000e50007103a180540413100001e0303120240d20030790b01c0c160611040c0c2e500143e41e4141c0c2d080c103141c00010705c94940d000310040c501c40c020042010f189003803400401b65008903040003e1024994000603000d0080c840c04159014210180f0105100f6900f0080b146918040b000c1c4900d0391140d1507404a40b592040d113510a1941c107144e607440303420707060041076000580c014180b24441e10382000b08050344206858040c1344241c4039000e0801c45501082101704072409854403131b42d0541d0720f1460781407009541c401207500900640d40c0c016201c0300807400766040da030440b460080f0003905201c401c0d41e0201461001420fa590700e606400c0c06c907078584a80c1c80018003113004154603241103c0e00c845d2048540d800600e820520094801d4400c807a140d1103211014100307004c25084112401a1405881113600305004a06035510310703070a1940700d02a1200c0c002e905e5051044e1494 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 873849757 1250 873848507 873848543
    0x9071409060409060606020d0201060902040f27180201090611210c01020f0a09120f06020915130602062d1b0a0302040f0605090310050403020f01292407 67
    0x845c413030240010364041c0c0702c00c1031106406400c1d144a42d0122044500c1044200702c0540c0303001c821300907035a0540009a41c05480c503c9600c0038440c200540d0348480c034000341b2005030304035248003001d018402e0b01c070303020466030391401500e100c4035162100071941c00407a15815422095006400d041d00c11002c2c0a08107035403427044500720f800901c404d403501c0d40009003110030f80340c0010900f0001c05080c14600364103586030b910340040c5c900d444402003803682c010481000c50340d9070b0124a059051103171821a01c464603000140d03505038031889a40090300550b404169080e1560204a0602c07a040c10740107050800310070b0250340800f0040005000c0c2156482200920030030700700030300381c280c5941d8015032a0348c109100303039488005c6a07002500344481084003e900d6100030468030804c0300010400107083c1d8450500742d0400d50351140c1c0001e41d5207850350000081d80741c003100583d1b105203002c242120351202c00500125400e000c07410201c010034600030600e01700e6408020990141714451254021003801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 873851007 1250 873849757 873849761
    0x8070b04050f07080f010e0f0d0e0f1503040629010810150f0206060405070e010f030609021b0c0907170702030d090c0503060a060e0c1605030c01140907140906040906 73
    0x500070012a420001707040700082001d001c0e003010301c0050713009003d000c40031614095960340f06010050500945075240c0006075210011a12511000ba22081b450100702c12802e4182e441107404550f21440d29075a0044011100c100801c1e0303040c020440030106000d0401510300b00b80052104800d2542c60901203a4103a01203500c1c1510055a10340713621405800304085e003403540040c0705500851815003004000c070b90160003082c4003a42800e00d0042d0441d9094124060a12904001c0c00c160000402002c01202c91942d001c0b807004413015924804c80c0351040040c011760641d211000204001c84000300088a1101f4a07041a0640100d81c50103009078405004d8400c10002501c0700415000e04000c03500301403002d40c1d403108c06140700300403240c02c3c180c2002c030380d5401520b64500b102012800841c00c0181d031080c4901160071608513030300c0d4940420101e028146d0507900c4035001d10b803180840c01c0c1e20000103c420075580c6445603088070b001010140131640800922242c1c2c440d46402d52940420214 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 873852257 1250 873851007 873851009
    0x915090619021b0d0f110904050706260a0e1c03020a17040f060203152d1e040b040b090709080609030423010c05300708070b04050f07 59
    0x14107400d503107103500c0c5000b90800100d4018041c2c05404150912200d43da0007a12548a075802215038500e4402c50401e101c8001c84c00010b2074108000c034047c4000d01c4400944074003160050b6035000d9645940e550a42d010805070341180020007654400710b10381052030740010403040d00392002c441464521007aa00012040307000c4d10b0001c039034006290210564824585c04c1140c22080d400191814030350f852006442c0c0c20722014100d240d010000c15010380c90880d000300c140320002e03c0208800483c0c1c1c2820700c80100f000221100c0301c488800f191043c10030040444c0014640b400c0c000c0703048071250a00014103660b1045ca58400e0361045095040d076103100754240155401d60351182c4450514503124a0520301038003418040c1e0043c841005507511803030014102442404000c50045046001610746440444000b0214003c50302e860003905d140414502c04802012a113400c01885c80707145001e5031084000141c19810100400300105000103161608140b0070000c0340c00600900100c2c40c106005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 873853507 1250 873852257 873852277
    0xd11150d05040203060f07020a0609020111070b190f17150607120f022a180f07080106030b15070f0206030112030e04020327030f0f0a030f1109150906 66
    0x10700e50030701003907044c2041426480241c4400259060404483c0a03507680c0003420018012915680d0b1241164892010098050100300c11a003610f519692910322070b41140803402e2412003800c120021140c455603032a40c6801c200e0700c4550b1041801003400b038038401d009100020003442c0b80c12295a503100c070380081c8904e500980301d080c10742503e008004c00340c5c4820784080742198007054520607500094030400c2c4105d014080711070031031643d00e00803071030f44940900d101851002ca5420401210403025000c0d00c1103d00ea81c0340c5015030380766501501118030996440b0f800481c10b501c0fa900402c504c0000300324031401826882c001070304943c00514143d2098011520740070b00d403410301c0201600902040c9002600312015821490010844c0020405440c403007031201500440c81d0039442c006008841c0030411005542d80d403201d607150120030341d41c02100d030000081d1508041e032000c456240700d44910b80201d10340703c51601401804101441c07048640c0d2400c550820807000380141d80d04001400040e203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 873854757 1250 873853507 873853511
    0x1c0507080906130618032307091a0102060f01030804030308090c100201151211040c1202030a0506091f0504050a1d0120030708010501031a090f160e0d11150d 69
    0x1c24600c0040c81041702144a41c8500d0701050203000241002482c21075044400c48200d210070ba080c5106841c14683d5070115a506140215815564500030f2004440c81002e8084641548030601c005100e0389003440f010348103800c1448240f0000344a005402d40005080040300c0001e010702d00000e080015111103113015039544c0411044140c2601c4035940113204000842110b0391381d544905040d0802484110f10031548c074203501c00c80034014452500e40b003024040840d2646082c01c140d01c010801928001d00c9403803401c00147c1c0b440c26103442d46200c86480101c030307000309143c001804090180034010f200c5041d1030325141744064104159464030b5135030580010608844580030706050300d01c0c270306954442440c200100604a500400064111754007883c00080035000c0300503104c036803901c000741c4641c400c090405108446554081031800f40810100c3d52555001d80f41043da842d04000d80040d4020740200c5840d030120b054001e204280b40d4000d00403185003840b9603e610394950200625040d80c035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 873856007 1250 873854757 873854759
    0x2120a05070501050f04141804051006140627100201060e01080f37110411090d140f06012405120f18120703111c050708090613 56
    0x4a801c02062004003820b003022407800a8104400a1074455030281a402c1c91214003400385c140c44000382c90404070f4042c40408038a041924155403150701d40303281e0b41c00150070110042840c0c00404200b10740309100501c6141b4080c444040251400c0f075044041350f0000440e0740003011030301d425110901031001d96000103659410b1880c101440c542c1a0800040d9502a80000f41e01400006080c02242044060000b201803015a4622654808410701b1314900105611760200b05101a010a004504842c01e000001da034102d91003c601038542c0c8540c1c4604800c4184001c20310794111030141c1ca007400b0680d100c4c43d041c00c607011b18081c001e90100b032407130900120b03c1103803c2251203150032600d80c0b45000c514110408442e0001c988010341658503042540000c140c081c44104a05650f4144541c10354201001c00a4481c060382c1007014181e01050602500c80380e40c14001c60a904003441e030b800340e070250100c0b00c5011500b640000004469a1004001d294802da031110040d01e801402001e081c04c460b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 873857257 1250 873856007 873856013
    0x150b04092a050c070b0406080c030a060504020f1c051005060a031b09080d030e0303180316030807110703020d1101090f03080301030c0e06090a230f0a060609060509010e01090302120a 80
    0x316120764000a6003401c11b000034046594084d525541004103041065201d881d0711142030003c024a42c040c90b8441e100185c0b500b800750b40c500240001c90300d6a07d424402c03883c0c4c1140003040c1c5000310780044001503140414400c0d441d0039009000c3c3c2244030310700024400f204643c01050b860111803558040b03200000c04201004081203882d40c08003140c901800111000c1034165170b81c1c040a00311501e03115400304e0340c940b100300400550321900d8807040301004001300346c02c0143c0171004c103442c0607001038000c240b846000000060000210f940c040d12051280903591110405280110082030400981c800009500181e098414010354040d8000e00d035039502d9807401610450f8560300820074001000b080060a40d24050f100364014081c2c0c1000c904103148040d01310380302c800f11101c0e0340c2800c1407405000040841c0c402e0740744240010313202000038680760401540c5c8103810748140400036000700f02c021015445284081d4440106051540609d5103e50000c0e1803032100680c1891607920400300c22040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 873858507 1250 873857257 873857263
    0x806041e150e150108210a05041214010c12060b13090213030b070e090a0b211c021c02030f030c0f040b030903090f0f0102151008010e10150b04092a050c 67
    0x1031310140203082c03407400395591f2014215000c2c620502d00a40101c8001801340301381c444028126100400080114520f42e03103000d055602544400c02840745021404550880c500f0120b4a807010b0075892008014030303228202002e98802c0c4d82d0304c00c40500074503000000490031110f01d4001c0320141c0b0340604c000d103444180800300038010074054805003418443c1c9030685030300501d01c0054040351500002810350f21502407034071041c42956154050410204054658080303064040e4885811140344041c4c0800301c100e0381c1e4045d5144c400c02c280b400b08040780c0f00343c8e4000020941140c00406c0b1604160f40d0310000c05441e001194480901d810000c1da00b0010303c2c00d8038006180300404c50303c2203c48048040001c3d80e80204c04030342c03c1c00c0c0039480045840445400c1c40c3c00300928546009020295403100300c15207900e030b00e40089124500340803030030355040c2c0740703241f01c40c1510801c43c0700d9820b0524102c00900a01b0390103120780c079071141040321010415074000366445140d6664803200e98551007450300740e107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 873859757 1250 873858507 873858553
    0x60c05010c030504020f0f01030905061810020f1b07030203062706010f0909020105090d0c05090a18020105070305091504151b0f0c0803040806041e150e150108 70
    0x1c2054504010800160f0300c00707a19030030150055500400d85000394005900074103c012024103030344502c10402000b51128501c0b55505062101501c56140524440c1f00a0b40601c030010420a18280940c0000310203000346181c00560200444041c20350700d4001c603040c10307000c0c2c070300902080810100300540c0c01c0798082d0f80d070020040c5009000ca0740c94880d408600c140d4901030445030340e489200e140103680c800c1042c2c441505008240a154000720725040c007400316a03209442c094034021000441d0940c035440354070312500301e0b0b640d011500f02c401d034011945a808160128103000c000c0c0100c8002e519002d00c2888143c1d03800b0002ca5645080a401010020a040c1207008020791018030034030004000032402c0c0d54551000d1420582205c61070080240b0009802500a510000c80c1c00610410700286880c02a4001c507180f000c40d1071041107580e042c106203000504804024140d00030301c111658054502001c0ca10155480302106981a24480c10282d0010080703900014803415440e40c1c20b62004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 873861007 1250 873859757 873859781
    0x70b1222030249030509030a090605160b070e0406270f06050607030c020f09040302060615160f060e0102091c020406030209272122060c0501 62
    0x2460414040e94000c3d030300c0b0b00c441c50300807441ca40081c0c0914101880c2a00f918616101280710081d541d5103c0d02d510410010010b2400190070100803505c13120340030080300c594100d80c0d41c0740d11030603081140030364440d800a100b0741c20000b07801000d4408a4007492101d40120601d9031164524240d400070031040c1d0700141c20515032040c00340d0406400440b81c50301c070700d800b5151560206d50408540e1111005020941c4425085440081e500c810903170f10001800000b0710803201240540c151801b40318806070200d80017000b6a21030030105249242040d00b089a04240e407140f0352805038034044031144044180360440e2884a1003440004024842c05404a03c441202c004c42c2000010000580c3d000031a481c4560320b40e00313a02003030080d52101e4004801075900a000342e902d40c00c02120040c0f0440d801e82410f04404481000e5042c0e048021072650a030f41c2910b2602c00d01c0400d04190340d0800c3d84400180a162100206414051540740140c50000c0003203464860704180b060421a0070346821082030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 873862257 1250 873861007 873861061
    0x3050105040c0501050a200114090a060f09030804020d060e0d020706090b030c030105100903060c090302030c09060f01360602120a09060302030a18050c180405060a090302070b12 78
    0x1103003035258070214180f01031610b0524200d1a2018009040c011310b079100c042c9d603012410a00f0030a04180004080b4040d42c0b10f084200b046d911f07000014401c4401c844c0d4001c000444243c0460050328040c0b01c804403180c05032000041c058810108245814010880e02026800003071080110a822100620052480e500307803516525054081e060684014000c05200d017107120710350844280300764405000f55034000030030854603400d110003402c2d4024600c003c83c070078030070491030b00440c1c04c000122a00881016110080581ca000015078030612070402025801c0c100000c1c0c1903140c4100401d448502c41000c0742c0195080c18a80000d0a010716040c0407074015004110b0713244980d070301c0801d40049584034a001a12501c40044a2001c4c0c01c1d61640c050009005041600038414046a00a0f201300101c4014488040082900020f24012a00035140350412000120304a4a5800c40016944248107450702c440e1030340e802941e01d0300441e04a0510b10310113810001c029110035510010300408890b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 873863507 1250 873862257 873862267
    0xa050d11070807031e06111e16060f20191b06020708162316030f0f02120a060b010c210201060504090303090528171303050105040c050105 61
    0x3041e0b569819844001c084074200000071010f101c85002c00c403400355004600b03100d08a4540140b0381290000c400a02c18423041c01c0c0848851000c20041300c0541386400c0d100e511031600d984520000380300320a00d1a006548480b805120700c451040c01950080a0b10000b81c0c1f9070000b690070a0441c1070002055040c0060070034071640700450103c00c07003e0181d2005001d44d403103015140a00460150091420803410140c8420081100700215980030f007100b03241031000f0034184440c1e0f640c1c4609002030208200c000c1d050a002280303a1440b40851240922031200312404242e01081002d0000f81034214150800f2820741d08201260280c0d24044909207080300b220545070f00c4d60312048000042c04000851112000d400890003900810000c00c0010020048603c1c81d05006d4050b1a44d01c50403655800f5000325101850f940c00d805d040c40010051541002e6000307030f83c030b4841c42140d5040c40f07040e511042c00940211407010607e40d024520036000454141818504024461200d8000768144001440 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 873864757 1250 873863507 873863519
    0x21305030d0503150d0c0305150a0506100c051c050d6323031c060e040602040602240601180509010b19030903051801030e0a050d1107 59
    0x703581c0c0104440743c4001310504c902001a41100c1202c8008011181101b000418043c02080003001c228022174992000e40c0c1308507121085031011942207500407071414060a00758480c03020b61118078894001c440126841c5459003404910b107201001c0020000500b24201441034002e46502c409441500412241004580a01803c5101422071940a442201c4190481440c0b951f04415480c000301d40c030003900300314010030300301c000c00c4145c5580b003d0b0881406003000002040308603441070070155082c103104241c9801d40d03481c00c1210f2680d080d2501c40c0801c1403480e10904c14002c5100b054016991840c14034080c3c1040d01480b5061500111244286000300e03031100d40076840b002c00d10b800102440f4000545401b2903041c1c01c1160080c10900010406d155000d0092102c08403500c0840f881100b160011020740e0700321701d0001c000410503c40307a010105581261000090b050502180107406080d100c0d00d802030000c0c0a654591040d40130010a503000014038444100074030142448500f411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 873866007 1250 873864757 873864767
    0x16080610050f120a1505091308030403050d020c071d1902030709170c03010506090c0a0302030c041e05100e090f060619021b180a0e011806021305030d 66
    0x1035860401d00400180c880d2080ca240c0d002c4441c40d040c401d5000900c2d040800c1502c0c018030083c01c0066003001140c1022070f8501d002a080c42c4a105d00d4070400301d03a0710080c1e0b56404c6a40014004400348001170007a8103044500d40040c0c0b990b20480300007000100c0c94245068030720140071b102c00d459111840d081c4407505080421030000f42510030350240c2d0f00e0300d50072000c58132805503502071110030302500d80140c803920020848040e00340f0120000c1c4015140c00080106012041d1492540c00c8000c00c01c0b4200d13107001e90007856101800c10f440d00c0c200766a488222081440003014900b1020407003130144102d207404818141110b46a01d003021020030f280012030a00358024105900c0c80440a00207003140d0344400841e50f88051105030303106001544e20010b542e90507291610180c20040008108450410343c04c0009a4281c009109001e6142c039002003000781441140e2000954035032002c40c031180d16400500764451310450005941da88400200c81011410340c10080c4290401c07040300e0041179000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 873867257 1250 873866007 873866029
    0x312010f050f1203160804050f010504150f0c240c0207050a0e040507030206120a0b0114070308040f060516090812030f070302040e180f01090507060509040f14160806 73
    0x182c6007080c2c3c59400d07a111a00e540076aa80c2403401e03000f4048028100150b60024104440c0300b554130303180040c0060010368080c0102d0140b40c1601c031414900601d200e100b17103d480040341550814045103c01c64441c5107103a6002480c48088204c0002c01c5115a0024802c6949404d82c500c0602212810503001070310200c1e0505c950951441382030007041c1880030601a1400842e4010021989c0780543d801c000b41d00c15040760010880b0307141c0740f03800c0d14650181d9515920440903502440c94186195016604200b02400940b1100407000681000404501c5514015005407008492544920f24000e1840c059900302d40c80c3c6401c00c07030100001000b10001c1c0da40000000c0031450081d80c030054104c00070700850384078901400307984d030500456007110882501c401503008103541745212050115400d0b00d10708000101542e01803142001480e1240c80035064500c0700400109805172915907800c15503e1008440260180310f4060004502104001541030041030078001020300d41100020300503a10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 873868507 1250 873867257 873867259
    0x1d060d0c230910030204181508010911150d140123062a0106031203110702210a14010507090e010303051219021207090504330806090312010f050f 64
    0x42140c3c40d100e14001d80684007c0d041070b90500280d0108245107034040d02490814008145605030b02080304403040c0592581c6d1038000c440612364050b17071010300490748005507c2415100c4140700740c00031a907548c0114079a151800c0c02001c0d032075041c0301c0c044180090712250032442b1009502c482074140c98410643c0d000780740314417a113120044151f680141c00700307070310000e9801c6500c6c0500100030803907804110542e260080d58104100c1c43c44000b861590300c100075000e544090843d01101c5d151443c80c0c040d032007030303641c1105a90190225554030f40c50304052442152031651100c007046402a17201d0033100090202145003007065140d614003034041e1044000c0264007440b1038000908030104e80003d42038400d038000c400c640e036a240c80049100024142c840c1c2c000968180d03400641840e107030245210000000010090005030034003032000048035030310807081c00581c40c3d1001444039001e1000c10304c00d2840b00b001d1030340c44203099220003403190140c20100c3d1500384d407402405681c948034035128034954 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 873869757 1250 873868507 873868519
    0x5090a15050916060f0f03020901020a14120d050925140105160803090610210c0504140a050603030711010f210b120604121d060d0c2309 60
    0x81c0c80a40e0b504018051a8810308101d0780107001613034035405500704054031120364650000300101101141a40300e005da005005a009084550228188a2048030707030404c1401140e0007429501c1d80d0a81d1504011002c00c01c90b5a40c40070014812030074040720510000001c0c0c14914041d00140703004c840c1c00f0078003401d00341d114a141030b2583c90340190201c584500301c0305004c3c1440d840d1480c0c08456640101d400781c246014060110700d03106048006401610f555103005c2184100a90f001e40d140210035205039450081603800140a40f501c3c4154600c0c040f481d00445200d00d03002e018a800e5850141919001c0d920801140c03012554006410080f51000d107010312102a0803a8101c03034400c40c00c000c10100502d5001060ba01c4c0317000e94031141d04440700365040c0b004501030b07111035074841d80c080340d000d0200d107041c202034008280b00d0a50780402906003c220364100144102080381a04000c14074031855a40d0b01d028007415030072a544406c17480e200210405061a81c40300f80c4400d024444845010b42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 873871007 1250 873869757 873869761
    0x110109081209070803030c0903160312030f02044a0408070203010b210c1e01230c0619050411010e01050706150e07020601062f0607030f05090a1505 65
    0x30b00d0a100e860000e100e440d0850707440381855074620003550701c80441c41d4407a225003800600d06000040c56041120f41212443c1c0c0c081c481c62000f603010744150003909034000d90801020440da9001032100503007141e1200c0815106c521001a209800502046c0060700000041c000802d003a81010301c60f0710945c40040f054491000e4070100340908405210984d000105040100314400c581c0c2c52503418002c02d9040b249010b40c001e0034441d191003050704450307482503481d80d0000554025880b1010040300d07481488074011008401a040f0b0300140321100e2507400c407100b0b20801111102c4150908109298104803909281d582d00c4040391450210034107001c5482e040710740682c05030082d2008107800503800d1008101e04c081580c448003c1d070003030407441e0304a04003050600b880000c1c1e99060b60315544590403850000003005a10304242c03689046100094488a0300301242405194011103035900d02007001c103090020700c01962002854842154483e005020115403000341101080024180014183d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 873872257 1250 873871007 873871021
    0x703020f030c0a0312020f0c1006060f1718031201050a05041e09081b0303090d050915070813080606180903070f0c03020603130506010f050f281202011101090812 71
    0x19024812401490003004240c92000340c80100b00e2720208481040100072050b1078042c00e4500326894200c034000282c8440c0004007840c4d5040c601c9810042c0008280e5a0000034460549107521801c83c220155005600401240c01c200041d6006058212000d000100a64102e2a03081d240606282100e585402d05882484040340c100c5003018001f0815400d86e51007200c40ca95280d1042d2031081192241140306250644a0801d03103c038500001d0281e403402c14165072514064120010690311180204521600101152411001401204080c10385460101c0030007009203440c2c40c8810801891408120101c040482216078007540250304480c0741c900780c24802c2d100e4856400083d04400c0004c20f00008508180c4203c6030548a0002c503050f580e00d8410b03e802d40c0c0a20f10940350000000001e82070329103843c89002ca41001038240ca91504a01c03545142104c0d02507510a9910709840800c92040d960300102041122800c070380240481d802c20398030880e0307912034440c04108041010b0045221 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 873873507 1250 873872257 873872261
    0xb030705031003021905270c030c0d05040b0403020c010801081c020c181f03050705100c0204060609092a030903213602042c030703020f030c0a0312 65
    0x2d140c024282c1c1040707030001c41d02c02d02a00300c21b02a41d84241070815071862030f1500c0b0341507614507031b40c08008010325441d103583c121030940020300701007404001030040014850030351240301e11507802070b40f001007142000c3c20041c0c2010b1901c1000d6041146600041c030803443e00080407440b050744000381890020350302c0000c80c10004001c4180b60311590744d44040074801100e00410340501d51810000c4041110300e21221400060751000038000d400c00c0e04200090314000004080c6001e5905002c444164141c0c001812990703075800c107002141040c0810700c410203243c81080c0840b14108400c40200c01041c00c54942c012032484400f08051700c42d0704400c101880340c4200b9402686500504500740300d80d0b0f00c1c880c0980030364116404900c4801008503145480e0710064125845220a4050100c140d6002e0001a00786240301c3c4d40403905a0343c03091041d107001142c0d03000c54803591010b5900d80120b441c00a04005010074503030019030090103e504a8040810950201549420000c2d0400407442d10340340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 873874757 1250 873873507 873873509
    0x120f0612030408010e07120302100203040807020415080f0304031e141506040c0507230c0a18050603010b0102030301090e1c110c0108010f05060d020d050702030a03150b0307050310 79
    0xd14007020500181e01003054006800114446081c0c0d0015a15424800d04002501d1405401070b8405800079040c14444c0d4002e54205000b004010700e441060b801040540748041c5c018944540b92480c1004002e20501800c407066036007070051440c1600c0c40e15102c0461300040580c40c004046040e6400401c41c1200d40140c420b21004c054034614960300f00003219082c800c40300c850040d404e00441184480c41340003142d02a552005110716500e050b100c81c1c2c1e211740004100314683d889489403003551507a908400b20001c040d44182840c2e0030b0164002c1109403130303001d0101802a03051800010891ba008001e0301e0541709001c6000070141c0d00c088015250402040c0c01038403c0c0c44411380e428074190b0160900400341c04074011034901d4428200111107a4009200d4000c10000000c00ad110501d4410000e1035000345210001d42055904031042c4100c0e1000d84440001da0700024070890301d43d8060045080356654813114210301460500e444044d44802040d000401c500000040c81c07026092180c08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 873876007 1250 873874757 873874789
    0xa03030b120105240411161109010b180d020108190f060f050910060504050d060207051603020307060804050309011215080607170903070f0f2a0902120f06 68
    0x80401e0504e02410640d4811401d04000221516080039280342414002c1c0000a24113841280c9440da054131061103a64045008a40e41c0101030070482480e07640c03010040c06000161502981c480e01c402c0240740c84204c4480d0b041c0221101c40e08400940e8218103417030360101d4020f41d070740021580320100d130005203032070711a407008140b62450108504414021000076100d042c0c07480503454681d00d080c0212810580729000005804000600981c10031600401d10329203d190050305000f0b003a40d0300d81c101025219400f682621010b404c1040d49020030010008003039a013042503c0d400c1507107505440e4420120b05070705001c10072450b509103008a501c0500000d09040090900540390141150ac0300826103000000a0300081083d00395070a81070602d01880004004515000c41d55a0310b000d040d0f05031000b0b40b007512041110001040d21005000e00302c22840030034a40312040c2d0310b0030f462030011a8005c1b200651040c020403030f20200007940c1540015140824140560702c14001401c00c2c0c880c80c81035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 873877257 1250 873876007 873876011
    0x309020d0f120e061201171219200613020d050109151a0604151103040801020406170621120c1005150a03080f0403060903020d080c0c0a03030b1201 65
    0x20203002e0001c0c1c080070502180ea035000b82000003d000c020b01d900815076420b0740c080410004022a24100c01d40e040302c11102c10a45d0000b0b8034024004006820034000e021089516103020541c49a21962501c22195103850b41c1c0184040d0301e100301c1c0c0da0390b001495010700803503481600080d07540780c04581420315440b2000b0b200324401d5261524200002c16401c1203030b603007024100c03c15040c00c00101c807a800310180c002410185807003903020380c0070380344030a42c1c0c1409508140d1400d03644091000307101038040540056a40c52078190012b0000951054220080d00c41000340544e5540d07001000d41c8604180441418621408580504000924040e074501c3c100000c3c100036052008a08410124812401080b00e0b5556100081031410019041c5a0240151005000007194000030341020750300000c4e0f0500b402d071a07039558030454602d0a0700b980564400d10340507000316801040d4590241e581f1140a080c9010000015641e025101d0005c041c0340d10340c1c0410301542c03907104984c000b40d401003000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 873878507 1250 873877257 873877283
    0x60a0f06020109020f101413030f0305040f0902030105150c1018140c03061306060b0301031a060f01020d11210a0f020d0e010804140607050a02010f0e0703030309020d 73
    0x3001c2c0c002e021801049024108003540d550b014500410708440c030388225203d078000b10740c0a9109012650284400da441155000f41c044041a04000c0e00082d80d482a1259076407582080301404c2406110b50090041d5801000107006c00d40390940c1c20300e25200304031046a114420480e002e82025103072070105c2c2e100c13480c1c00c0501d01c51541c03592041d80320600480811200303c0c0150480c41c0c42d03d44400f5040c3d0158014400720380c00c1024036059080d030703038060140010310503154405c1400c5e6030720030b03803003680c45244419840d840700740480d61964100710103c400c0200b0b500c1c40000071f520745540640e00344c14004189000e443c0f402c0144664402c080040c5145e83c00d2819504012a403600001403170400200c0ba121403070051800003ea805081002c3d890742e000100903203004584119008004603120340c1039140c078000000c010001c0c1341c0a514261104c0392140400e8034001d085524003e604a400c0d418859502a07150300811110300baa9010f20340817424110a001007000105244801002b002d00c4840c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 873879757 1250 873878507 873878519
    0x140a02072001120c0210060812040b070203030409090303022701080105090a022a0715082a0307080609092d0c13050411090421030e070807051323060a0f 67
    0x104c0c4c16011b401c0c2c60082003143c0e01c58400607512419400360f800d000030208404d01103e49544040c29a0754802011a4600f42d20343c81075000341c1f640140c044020903000308074509011400d164003c9030100000007403407030401020008100301c1c13040c8691400b61841700c01107014855250102c800f48104410360600b440c0700c00c045128542c581c104540d081d4011481c0100d43c071002d007155060030844640c0c85190a440b00d01c0c135005101030480b00600100c0d120101081d07440b200700090f510032400d030380343d02c212031600078203018141900400842c8560044041c2044030480c0d19040e4240000300150b60060303c4025107550726140785259004e84c48030010050314007040c016004180310ba031080040d2818002078505102420b4001d0710700030305d41012004185400390500b034007615010400c1c0fa0101e01c42191012180c2420303101d411141c0d03d034008410078881400c2001c44040328592020041002e07070840d203a0040d0003101c4440345c004040419003c103441d5903602c00458040c106007035000a146549070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 873881007 1250 873879757 873879763
    0x605090f161d0f0408090d0b07030e010c0801060c0303021605030c160503030a05040303050d111303030215162303070f030e1605040209120709140a02072001120c02 72
    0x4440c1007030381d02415440400444002e4802c602030070062101007055260303a030b40c81916030450802c003138025a150100501107900c004406025082a450005071005414492802c0d03d02a844803003d022107000104212540452a018250740601c0d005031100c190b1000c10452a000000242543c800403500011440b40402d044100e495500400701c10f40b5504e00500d5228001c088020700800e40500003080880c3c080d10051803a841030f980005403803460014007081c29000b0141c9603003c1c8145560034400c058041020007420f03640042d22040f14a41036101c200d8035564860080e0411624400d44030365600041c640c20002403621341d01300e807240b03440080180305112803c0d181000904102c4c6d647c0d4100c1e004550343d0b0340c504003800d242c4011030030101880f02035841409c0c1103402500d00800c0c41c0142d101404400050201400003040f08080c130441c0a400380b102a0120255a01c100304040004007580c2e40b1101c00f0b5a0000030110000101006903101e81c103001c80520700702e040000405c8025808 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 873882257 1250 873881007 873881009
    0x405060a1e03110a210603060f0e06060f0d02011106240105120711100905060105030d0504240c060e160f03032102040f081f02030903070605090f16 65
    0x4401c1d01803040d078645104905540032040203240a442c1007000b0407041c0e100b000d0028810000070300e0295a0507031a11302c0c40885a69500544070325503110082918003140d4012500d00110356402420f040c00d14400184d000829520350303074420740189000001f10f9000b282005400780264041d42c3ca03900d400300c1c400c0401d03101c092071080501540d0165070034640c01541554092103400400101554404030140c9400480c240b078001c062260200d44041d003442800b810b0f404500c0b90000d0b042652408e000d141c40c090b00c1c0c0025005110b010300040c00444691170303078102d40c0b520140d0100d074144000a030954000d1195500030702600e00b000030031903603942c0000b403007070034114a064407074161644d48511610712102e03800000e0014180344000c104900c0083d04a40e00d850100e07500510707056a0b400b07000c1003505039503c0528960041001079207080701102e4901a4449603010551841c03510400c0240c50348914140204410b9503000455040c03103040046c00070802100c41244c80c02c0308421401c089030551 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 873883507 1250 873882257 873882287
    0x3070305062d040b0f0d0305040306050a0603050a030e06071709090708091e070e01030c080d231c021b0c03010c0f0c080f030f04051e0d140405060a 65
    0x4035860601e00c0e4a5800a0300070051030b0001c0c0c0300800c0000004000181c1682040580e0050b41001103040307594030b90040c3d030101842500d880d80c1d180c0c51445e00b6000c1d03c1e00202403480180c90600100702050000c0742e5520aa0303810b01c1c4c0448031107201030000300d40340548100500110705100080107003a217200000c161241080718610170aa81d40031080740c0c4020120380c0c4c194103800a40250703250b04820403004100c0700f074102c103030340d060303511000d8403401490241c0c402c1e684031107128801c100c13400c418405413500f00168030301185a62101d4080d1200c00030704154811509000140d000240303000b00360524000d030126002550303611448200001a06a01840f0441303a004103c1c1d6030609280c1482041122251910340102428441c4020ba8102c0b91644081e02c1030382c0c081201100885c1624020b5220304440703582032007d400c050400600c2c00304006490000c002c5503880c0140d41001c0005c001d82c480d212454140e0280c3c000c00c001c84428022030b07100b242c002c4c80c003107100610181c000d5500c10b18094 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 873884757 1250 873883507 873883519
    0x20d06140c0c0c2b0503070f050a020109240509121204050103060905100603240e010e0c12060906010309050109120e0618040b01170405060402041b14090102120307030506 75
    0x140000c0203e80903d691000c420304119a400c0413101e00c016000c41c0340180103900792414000140c480e9001011040700803990394008450420031036030008000c901810403486a405440200e80f00311a075480781d00030503c00c1c08404030320040d56540742ea10700d52054000900f40c414044003603c0c808403d401a005041c0070a05254022651106600c0b40c98031031a0130800401520b85090340941c0104850610548000e601c1070b030b01c2d0881d01c0801d44100040904d00210f401030341c5403182c2c002e890031010f005602414030811210041064104c1040d030045006c40d410001911007600580c02010100001800e65080c016150140a82541394005504040e02da10b5025840c0d001002003d03c142c4003074088140c06484035810500740740c0d000300c03030a100c10b04103580344d0419041d40603284042240c0442d940c4c0e00c044100411410240540c5200005410b03088669815815024120083310f01c009038120101242070724041c1c0c82004110391104032122055941d0400d5000140035200c2150a1030181d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 873886007 1250 873884757 873884773
    0x1031505130f0c1505070c03080f121e0c03091b19141203040f030b0703090204020c0616050316050319060e010f080a0201050304020d0c1a0a120501030c03020d06140c0c 74
    0x85c0603100303c40400746d101442d030100c1425030b0344013100c80d040555600d601083c18084640302c4031040300c880380902c4000c0130b090101660103038610034007000140301441200d001d1060242c80c00d00010308000c50102e146110180210b0440884c1d8203245100101e1218100b4901c001192030003d010703201204400d540e002c85a2484070b07410b980d2841284070381c0c0e1a20b20703001410030100c0d401c07185058101c0301c949400f00301071110390000b4050b600203803002041a000308060003400d0005042d640500442c90400a0031071400c03000c484019001c402c0c0306014810001300040480c001c61503c0805882d07195010040e550301c45940c0507601d070302401040c08601c04050080b07840500001d04404441e0705a60345483c580e959401c0c02242a6008401c40d0021180880030801d50241d02c80500844101c201054071a283e12100400c1010104042819545040010f00220b9840c1c3e001901340c98055607260110351440c902800205114484450305200c1a000d0008200c080001441c0814035801152049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 873887257 1250 873886007 873886049
    0x9050d020f060a18050616240f05070305060904020f04090f080a080601260105010309050307020a061220030a020c150709061e0206150402300f01031505130f0c 70
    0x28410640d00010000f03818900c240080c840f24106200d0201040040e40c00706c40e140e00523000d40b01504000840c5075181e00030440c05652620074507500071422520a6494180f640120b40000c0c84034040501030744d01c2e400a1700502c41003194120038a680603074007e47d9401c0d0f804009107518002e4510600142d58400d452140343c81d40d6002102820107001480000d902e0b08005600520b0196401c4440340414802d06025940d001c54110043c081a2550b40c48100000926400c50746601c2105104040318040e01c120b41c881402900d52001000070300598a59241d41480c4c070f00103014000c40c035020310600800c0001c0e50300c00120304c126403032900c4481c4054040f6000001c4458401004401079104000181c00c83c541d072005201901000f030001442c02d480006034405103c1e0058019602480c129413000ca000c00c0c6c024a40d51006100e6061145035042d59140c042e0703294103440401803107031240041450050075131506030481d94410704080c0502c4591410750f000b00328600c610509924120111011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 873888507 1250 873887257 873887269
    0x3041409070207050f120f010c030b102f0604061b0c050a020d170412020a1d0f100f080a050609011b0305180102130305060a060609050d020f060a1805 66
    0xd40c80758000e00000d40c02c00090082d40340085480075030065004401e154180d8080c00704121000c1100000b0800011701c00c00030f0700b0f592800004500545941c1c289001c2181c0c8120f502c15400480703030094a0040c20383c0301c0c1220200d0007803c0350a042c0070340c0303062100308810342d800400300d014501004101c0c1e9034041d801707840060550402038040d400581015005180c01c8441c410980e100e00d054509101c141d00f99102160440d0b0414030f00740c450141140194500a036400000740009944840c001d0255581c4210b03000000e842402841d0410000c07610814100c1410000342c000c2c88003002c00c441d41c898800390785801031001950580111408074042c075106008040100000c0a100302c4000d524220440081900400c0e600d0030114110101c40c40344020b00040000408420303822000c90f065050041c10941c000c7d01c0d04400300e1030180b0420847d5008042c8000704c82d000c82c1c1207403000d009030001c1240050400e213400e82c00380e00003840016054002a00100c3c81c60b10840ca4036502d920b90080c840c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 873889757 1250 873888507 873888511
    0x11125020604180e01060603090213050c040605130305162102012f1212010602030319110d0c1d01170a0216171e0304020d1b0e0903041409 61
    0x1400220402c0140b00b25500d0725628040c00300090000180710700c0400c14a42110381c10741221000a4503014600c0a41c58003c011140b8540b00701c03410040c0d400c043c8064105482640300d400d091003c082f0382020340785c0041c83d401c0c0056410009a424606800e144402181003600500300c0080304123070f180d04100c1d802038006d030201c1d41c1138440124042900d503a4480caa07112071300d580000c040034940f544040100f40003620380e41341d10000741a11340c54083d6602400c500160441c0c0c08560051082202d1000c200c0301d0380842c821003c0380011807848030007100d5214490710166503025800c1040b4000714940c068500c56090f16405807041d5420050801140c070310b07500e400740204503103166002c1860310380c0c143e00502031101e80c00690000c0041542d100703900c1c0810b810888007805004100514114600038010001c1c40c0c940b404149589003941c0010500e24001401400b0381542c0240900e9813609000001d000c1e1542d66040103680ca844200300e680c95116007e6404117480c0380030042030300d0519100c428 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 873891007 1250 873889757 873889759
    0x606031a011403150a0e0304031103011404050c1005072109050a0303050d0e0c0a080c030610150f12090f14070b0711180403030506010806100c0303110c01112502 71
    0x44401001a4100402d040c0d0280c652019140d51b034000110081041000780000e5206800c113030038410a45041500711941d048540b100442007404003c00500701040c02800c1c8481190b0f4040c01ca00d0410084034907000305840103012004c40c840601c01c20303003042215060740d50a9a68511003a4885043c03081d400c0c0c0c64070009011a10601c1526000f07511074000c011040610b4049611405030312001441a02c80c0d03600c251016000755031610ba541c00c00344000ca5103d212070030328442c07003450030a8659012030700202c210300b001346e00c201001c03003180f081e204946007056102e42404681801c2c01d05c0e2200181001040700c401b44810001c078140000070850200326144035500c5400d014494a07404c400e290041c00302940101e0980560101c0940d02c0fa00d180641c0c001d950005151a200d03001404080000d0812842388008481c0348400c45d500c81c415034031444d858900410182a60306803440c0c140a00e1014220550802c0c1d00b407c61203c2c16400340401c00d02d0469140850550580c441d1004000301c2c07400f17 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 873892257 1250 873891007 873891013
    0xb0a0f15120b28051806130303150b03040615080f1615020304150c050604140105070e090604020a0207080f0109200d080309031201030c09110313120c0606031a011403 73
    0x3c1c807242000c990010303a100c0c401e80900c0d0401d8110100090404074110b9401142203841030720b0006065040c403403c218101031840b02006281820300d0340c2c3c25800700910040c4207688561003c8003003944180b040c03004241113411986081c01d41c1c02c41e6030302c450f0b840f83c1410071981c0355540010100500111507401000c01d4025501d003e007464a0441480000544c4c00c00b880301a030b100780000b86080115620403070098003404242c034000590039007500e001030400c0e401c1000080010311035588aa001c44e4216a0449005980b011214020b81c1400300340d03400b45050780211682c00300540419085541c500b03100d401c40d140c80d400c2402210460b40f000780d48094021003a007442c90009a5842c0085411101c2c00302140e00b00060040030380c04403c0241c1049409142d405c404009040b500d0042101501550a25905502d8001d40d002d880c5400450050503c81c0b034601104049809244845485a000641071200c942c0340e050405000313024540280b1004610000010040e00c001c01c0b05010040003005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 873893507 1250 873892257 873892321
    0x601030e2a030f03120105010909050618100b040b0909060a03030207050415050619080903040614160f0f0c0e0c0d111c06031e0b0a0f15120b 62
    0x620780c032070749401015018852a0504000c021040002e440030240303404504100358180800104140301030751020203114180018484da81d52140b204503140d803c580c0747e08a040d41d650b1300c04c0214101c1644029004800005c012901c40058002001801c4041c1c0f462101d40c0c442000740060128140300c00703401a086801c0034049841c054019400e00701140540b0841580c47d90001043c5d0740c4060300c5040103a04054000091640100300a503120300860083c1d8281381c50040d0140c00d09541e40c081c0c2c2c00d421000a850021040050700c0080e401d608010032003d54181481c0012103044007130400c4d9080c5040281c00120b840b90708131468407840d82500e0150030200c00c0b84200c400741c0402c0145d102215414000714200c1103a102043c90301c8001d40802003607003851810400c1621100859a100c1c4090782130244010414992285130881480400007a2074800c1c9048040101034034100c0e06418030100c03000052150441e4806030045000341c07641d1a007511042c0d1001e00e6409508600062030040d110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 873894757 1250 873893507 873893563
    0x3040b010e06030309040624030c050d090c0905240307030f080307020f03031e090a0f1205090d15050a1a0d03020312010806071b08042309040503030601030e 69
    0x801d150041d10140c2103904000c0b06000050a0f98450b0300170407600c8d600c3d04403548503d00310207000c000240032400c040202e0304105500808501c83d2000942c0e0301d946804480040103c2410480000d01c172101c1b0402090500d0000e0880303100320388038111803151002000700c88514001c105c54003200e5010b10507164174441503843c0c143c9500002c0c821800d5000c1c803520311648140510045101e0500600e0300e0f41701d0094103802102e11007000d85142c41680c4034412501c0020000280c0b1703080d15030004034140461505039000c80303407403050070300030b6030812040f1004a0030810351021410b40444180010b00496480b86105d1080302c0c00043c00f01d490300c24141050a040c100a581c84089038040c0c819a4500f440d001052448410f003239014409a500200420040303170740c000c2ca80101118500706070070401c03c0c15110341c40940039a0041000300354800c1100406951180c3c4003821101000e081c2040a180070b0400c0c5840760000c031900e50100c0e007002103541019001107280703c08042015407003000001401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 873896007 1250 873894757 873894779
    0xa020c010c060b0a181a030d140c2b3e15011410020303012102100207030b0105040603020a091107020303070501090201090501050a2001110c101103040b01 68
    0x103181501d8541ea50a0f50b01c6032038641180c40406051921442258845281040c008035a240a51001c00c004c0d42c046e8000c0f5a9400f00785080031252078501003000c2c100c150111107980c410a0306014061007206084400c1d46c0e2085580001418003414195a00c4071110043d0340c511142ea400c015411644504a40c580d00501c500032461215030844140180e1682621032402240928842600c9105001005000e81d10038000c03041d8101541e40c600550020034010355280410b001c1c602064850701c0d501d20001200c140110013481c1c0003000426078141880000c1e48a04550200382c452040060020039203081c2030003543c0071298007a0000c84098034120b4090010620114602603e600400910300543d40c200302504149014000014565610b0b100240100b02d00741d202905000003070000424664211141c020202c40520940c00c0440302c805406005085840340ca001018001c5892040c1c0b100c002070300f10f802280e218080207603040107880d00e1400c1c0421030f0000c2c526900c01c1d0050114455013 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 873897257 1250 873896007 873896027
    0x9030318070f0b070b0106020a1502031f0306021b0106050d030309060902220c0c1a1b030702070602071211011d0405010603020c060a151509080303070801030212030a020c01 76
    0x244081c1d44405450b5200d0601c0400c266200355200e00000c2140402d104100048034010301c04c500003040d1503611640d0704c104c12814040c0750010107a0120015100a00441e100704c00c4802c1c0e0f1460a1210317440b442c2210003500800402c00070341e0345c2010500086441403003480b098401c020f10400c444800396404078050034007560304885081d210420315005840d6114107449d210004d034000381c1416803800d5240222890501c00004001d0b04146c46000300b08601840910b00460041c081e020340e4855034058440010485101000704002040102c160380c04625101030340c0996081c0c0320720b207944814081210303800400140c40100d500a0b1025650301400c0c0a00303c14200c2c048020900c3c007404005070890b0401da22220200750009144c040c4030078240001c5522850746141017000d0691090b01d900c14500741c1c0245c080103070704085c01d0510030307001f03c072420003d01503002106c0c0d4a00e00042c0c0204405ca0a00c4201c0c003902c0786608140b014880402994000381d0310ba4000c4c0424900c0e200112202029 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 873898507 1250 873897257 873897301
    0x6190c021615080f07230903251212051c14271b01020109080301030507060e060307050d02030a02070f0b01050f0604080705090711061518090303 64
    0x381c04401034036421031450080205102d0184200b420103000015040400003000b18000c0c0c03072030000f0000f50a4004080102880001d400a42002c0154404940c84d1203081d084503814440d000200ca500c2c030580e40f0019a1100303140d45005041c1d600c801c2028140c04140c8010031400c2c1c80c90091101c03505c41c10242c010081061648d19801c0c4a002c2c0032401c6078801c1c90b108215045a0b4104140c0c00e003c100d10445000042c420351591280852040d0707110403024005400c0340c031581c1081d21850b0300c00d411018601d42c01c00308aa580b07594070f19159a5462046c810000410340f1380440c002d4500c0e020382507a128085c19252980780c00312418500000358002032002c003180ba42805940c01144c1c856692481c1c1d18071400200704e441d418202041001110b0680241c85040c04200600c40040d010810404485058030060803a860303000c41512400304401c0e0101040c40360700e0403c0644e513200810b00b00c807628181c86041c1c81800c0500c41c505030500c01c94948007640d108101041520307a5009242880c10300c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 873899757 1250 873898507 873898513
    0x120414060307031409010c1e050901180b0c031c0504020112110d0204031505060301110a1b050607090627150c0506072a1205070c030b010603020705010c0206190c02 72
    0x5520040120301a5040d5942c5d21141e65500105002c1a0800b4900ca001c00700080aa400c2041d040340080152141c80c01c00303810400d04c1010002d02c1c8401300f11a0010f0840340d40e03141d0300e801da2039000c103a581c0c00480e0540c02c00c02d200e404c4030300c40203254800c59010b25010303514081c000c2c151481d0b441c043c1540c0b002e09400d6034001c01c001e014680a920260010314840c0c0d018000a8a00ea20310300143c2e007001e0089031003a450451f0b003000070180d02049030b00100050510300308180c04400e030078991800c20030000c0c20303502842c010131544a6001000d04140d92480d03c400d1800b000c04004204944c80e411468072071800854810310940162140c21071b02e008407442c010400582e40c0d55818100b4030305a0340b00e004035001c0340c80c144a900d000d142912148105030049500d10350f094441417090040c01d0b0f1080e045c00300001c0c0c010b003030240000300e24000d50b801001540f015652210014000e6200f0202520907510b014040c1400a00c041034075401040132114002d980e032010000c0100401c2c0750007040041d84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 873901007 1250 873899757 873899771
    0x16030c050a030f0807300906021306080709030206030106050c1f1d0109120e03150903180d0b040303020d0b04060b04051503090a0f11090a090512041406030703 70
    0x12010841040024401d944802802c481d070840a01003c2c0c02400d007130113104031906540089445110940203004510400703256001b4007101501c000d020800b4041c1c90720b800020740311900003103581c814003188c00300c2e81c855076265586c250849541071103000c020b61040041004002c0302d0305c030b40e000d48003290104096490752a0308446c841c90b50030811065907001e545a030000201d42d0034901500d0300d0f08000c2c000a1155419a95a811522403c4280303c024003580c0201d402040c0c0302041691809200001c00d81024102034030343d90b1752038004c00c5001c240740489200441c1c0e242803480060300500d600a4200fa525110f5a400350b01940091041c002d0256548060250300c0ea1580203600090160341034413983c032403c1c030061003d082604c92140c841860104103002d521480081c420f48401d4005038000405140c9150007030301c1440040000d540031494405000c03e80201380c0c02034800c10302c40e8013151030404285c40c0640181c0071b58483e0a010090010040000741055402941e00842d90301c0d001030302c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 873902257 1250 873901007 873901013
    0x7020906041410080601060f05190207120302010506030d052104150603150e2a010201020f04240801050a0302010e120a080703020c0a03080a030c020f1b040f02030c16030c 75
    0x1c20803915030416880740d80080081c4c03a400d12800c0d0140415241050950380d0b001c030081c11910078511078200500301c413a84400054400c0c45010044c0407008800781c241c04440c100240608403c1d29554481e000b18010300315403a0080301250300541c500781620b00503e1480c4864a003880000f00b080d04d011207044c00d07400d00c2c13807054890170340910310840704c05000100c5604070340112901411710420640c03003680000c2d0504c10795103020800c035024030f8070f440700b020740140107d019000e0321803e550b20300380106010403114940322a0800c460607801410b0440b08402c0340c125051903003881341c0c90700f1008100041c405035108002041c003a41c80a440c0c13240c40011825800e2500c860006c080d00e52110201d901020182d044c0304600c1c2a410441d82174403105d045403104030ba01c0c450f0f60f008005241c1c0d2404004021760080c0101420120070b1820340e42d80c0402c001181201034281d110880c81239280c0078104903410031034820b40c7e01442e5600102401c00c4080845051940b96540064051040c82a1001c0c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 873903507 1250 873902257 873902291
    0x1014040b030d11073006141017070b040924030503070201110f0607030203370f020c0601120f1b140906010e0910050d12080601140702090604 62
    0x18003a01c950343c40c01d400c0060041d039401c1107210b805c040507102c002c0794244c044541e107140c01d540801d60b441d004a100c1091b40740020003480c80d03c1a1072085007040007001107011220700c0c1700d001c8404190324500305a40703800543d611807446026480541e030040c4800e1282d5049035220310001d448101140e468200804568081d616059008490b9175200040d401c0440d40d110b5034100e01003140c000103009142800d0509078540e0401418182055400b10001764a01c2c0f420900036028042605405004050104c0003024415500040940d190910a03840e0b60050980f007194070209505005d4000c6900f070200f110f60408000b401502c01c0715000303030481b000c503e0550b00ca4001c2210580380700c0303019140643c40c19a00d100c04d03c480740b0611010040040c140d801c411160742c804005c503038260031a5103440260810052640205070000712114407142004006d290b8022000a02d4854010607074032030004440d0500c0d008000c0c000503500340180d90060a100c8452600290300602c045190301c100c03002460303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 873904757 1250 873903507 873903523
    0x1021306082d06040c050a1b032015060f031e01060f06050a02010605100c0b0a0204090c020604140708150c04050402030c12100617060607060c1e081014040b03 70
    0x38005842c10f0040514041c0300705100074030b00d820114240740100300c0107000c3d03482452041000482c5c1050000130144254481c040880010b0750340100b0044c80401182d0324507078458809801d001407000b0801d6032a10000d0005402c0005004143c0008800720300c11b20403070541d80c407919564848030003141290160a01c04080d0469607039164036907040f81c2c8001d09560007980228050001820071605d0180e0142c8802a52034000f80c040d289512800c0346840203110340d43c4021441c614250781c0503c900c0c0c0c0070036868090381c0036558042c1c1e07180008001c1c949a00c4030b0300c10421168440304941d0000301c10951095440501c003c25141459a035030040707410790b801150561032070800003511081c60354000b491580c00481c076000b91340038141440005803440010040b52510010340380c0005890390b0755141110486e90b0b1004090050548621002c2c0000c1810a6610648414a0b4800010314890a03c2901c60422042001d85481ca842540d921030465404003a40207a1910704002a82d00c0c00c02c0055 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 873906007 1250 873904757 873904831
    0x30c0a0b1504090b01060302031519030b0907152d09051011030307032f040509010b030402030c010f021507050c160f03060507051b06180102130608 65
    0x1490300d010000200401507140c00580710354600f40ea2080801c032080305040c103450142c10f005a498880140032110340782034000c001e600c1840c2d040c078000007003901c0640304201c9104003d503801c6030325908070213034881c900c81c0281462a03082101c1c8810305889211018400220590041d070b45030880d002c20300c0d200d84840701050200b40388a03010089810400920075104285146c0040030742c02408200c0d4030780c44080e04500805403560488041c2003124600b8500c4160790203100f245580305150b05403140e80191081911914000000065121259044034440c030f07802030281000001403801540c802070b168203c801103103c0e08038680780f01070803640014000d903200e48032070341c88a042940951405525900154400750115820003445c442058204d05803544440041016600e8075412651402409810800840e50f142450034848000c40c815004c1c81d60854000182d02514118a00741d21403042c1070300b4114645081003003024401d1802941040d0500c2400c1c1010309103652560921023120686 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 873907257 1250 873906007 873906023
    0x206040e04050715050a1e020f011b0f020601062a02030a24060305070504020309250303090e010e0402191d100806010e0414031b011a120a0311030c0a 66
    0x140101c09007200d1444130b800041c42c01c075242076140e26000b80250607403080c130314001c198001300d41d1002d4028022030308004004402080442c0454501003040e90740f55030360034003240d80c16108008203880850076a0694450b5161070400104901010346620481400c0e907544401d50800b5400580e424480e80101600490020b0700c2802510000e518200c1e040114040e058942041040003800128846048075012600140c07170751b4840b0601814610903580e0001c41146072003040d01c80305d0380390311105c041d80d00903600c40340c0850304c07404c00800344c4030b00307008103034031049114005001482c00000c2c00c1c0c1316101a40e0b000307408a60707851101000d60310261494110019980810008070007000341c550041510200074209945000709010030480c01900c0600302d164850040e1796024003c10842c2c4000303030320243c00b480c407004c0720001c58000d040c49030400100080c030700c94044051801c02c2c0d181d4400914200942201c1c003280c0d5090740c24200e210069010381c0424040c1203a03a00341404080c000350300030034070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 873908507 1250 873907257 873907259
    0x9160b0d050108010524040204080d090e0a113109092001210b060409020301090b0307080309102c0a0602060f040f02030a060c021f0e06060d0206040e040507 69
    0x10394819200c058005070b84036031400041005140c0b82c0180000800f001d017251900500d07090000c600030344121740084445100b03041c410340005910000c2c800440340200d480004a840e001801c03010b0b02d0200190382c102c02d909000c1801b40f25120380c1d090b10b0300c140d000d00e1071490034003c1c500219080e130254072504580b035840904209100d0b0038200c41d040e1001003030042c80300e2108a800648110000344240891244035483c000800c501540b11030304044002300b60945460b07540d00014041e41c400d0240d140302e41e04000120a20b0309001442c401510302c01405581089500c02c01d01000d41400352040d41080300341c4000702c1d0107080d0000c0404800401440081c1440550700c00d001d02511150b0007002154042001c0016203696a50290b400c554051045080c011890001078a061a08030000e80810319001008981d103400040801400002c240c606140d004480100300482c0e401414441841c0c0004000880a00c8d1980707803900040d00c02040582065180c281001c00c1000440c0d044503a40d02c5204 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 873909757 1250 873908507 873908527
    0x3071208100605071a09031b0109020406051804080310051905010e0105040b160311031303060c0c0213020c010207050304090c02011107020d02090403050903010c27030506070809160b 80
    0x420038064001400c086107040138075510600c80d401d0800080c00482507450100e40c40340e8052045541230782607002e0b26410750b031040c01414028442e8a104078802c078503040e00020700e814032001c4800d400c8100b0441c2c0401d5912901c3d1080d150340700804003c0c0d0100150000f041560303855214034108440016550a001d003020000f41c441f800c40c1c09080d05000741400100007241e600d108481803018000f00c034075141d640318541503d000031548010003181c000407802c6940e2805a22000301120300034682400480034002d0152882c1120300e10103500a9051032510b006c40015400078138840001d44001490f014454460605540003034000c5140a61200c88099560303509004540441d4881e841152828900e40e0000f035503c440080b00078000c80e4032600040c28140a18181d84610741d000d40203105032600c4c0d4400800c4800b480d8003503010b103a1446000c4181c88840a00b56003501e0f0f01c00000c10072610b072031800703854900d40109180e05500c0f8024048241660711501c140040603010303401074a540d04c000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 873911007 1250 873909757 873909781
    0x30c050c180a150b030403260f0a0c0320071407170f01061d0424020a02070e040302030a0c081e0315030a0203030d0b0406090e0d17040309050f010203071208 69
    0x610000382d00781020306120501d41c204c00c880e001540741c1407044103102100440803659140a519034001d400110400852404c01b0070080c0c410039030481d00300400380f5040d80c04c2d0b04035404803806012000c0c038030003010280c1c58000c00030035016004803482807020341d4045e00d05207070003000e801100007808020720900301007800b0000d406091151200034040f290620034031448c2d0b502c445120b9560181d100d00400d0610022202ca040f075411400288074000e58144041d0020b907210703201503c010b205010b0300081c000c0039180018002c56040e4007651911824950448070441150320075a01110104440e511a0400b20003045040450080142e128a000c0407a030303900e07260903546203020350409011707107005036008412035a141d4001100000c030440b00502107001040903400c0603280341c1c40c2c40b843d8402c840e00064005850620f650b1540d85403506141202060201901c2c000c0100300c06107000d000622380402c0b506141401841281d05085254650444102c1c040e1050300100d9010400d20030894900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 873912257 1250 873911007 873911021
    0x20301032915010305180703080c190b06060901050c010f050f0129180a120215040b030103020108060411120103030f0203070b0f090109120306060810050d030c050c180a 74
    0x151403a034407858900602c1581e12285002241010703640c9001a480d01c401d08681414018140103d40300e8a80780e00e403030489584004004151445503468038a650028a41c0c02902c043e030024240b48680c495a0034000180c1201080c181070040c1071240198400091084105006104030702007040d05003070403291408030041c0c020101c2d91902c04460300c4122074070f400d4900342a60b1b0030002a500d580104048025450100503907501030b0401e880000d01030411305408130800c2c022662400e58030002c0480391428801c07840349001d03941c0c041c00100302540c02017801340d82c0810007400201b00c5d0711428610141a600c4031500803100703500b020040c418181e01c54090041e044440c0012361a20f1030507105c4140036003000300360709680340142d070018400400c29001f41a41540c030040d0800d400000550107800b03808140103640004e81c090740040d615980b81145001290360140000694207101d850407101c0d404800d1342941c1c54414030301544200d0325034409e05007030704000c0442d403511420700550860a813021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 873913507 1250 873912257 873912323
    0xc0906090618130b0f0603061f020708030a0203180402071509050102040b0c030d060618030204050402060c16081006050a0b07030e0a06090320030d2007170c030f03160204020d02030103 81
    0x4181704110f40b98075182c402c0d49e54480101c03805021056141d804900e0480c40b5000b4800b03074000810420041d80e000405410f500c40050303801900c0f840780000780401ca008040c00a04003010b5116064409115588103800c0787c1d00450026241c0341d00d4003c40d60305540b02c805040300769800040c2200b00c06d8070a101d220081d1100e0319060750030b0851100d414000725400c3c04040d00c210307510f2004c1011541e41b20200d03021460500c05995500c03081c1c0c080307002c02c485503100d41e000380c1c01440c0002541803114410402030381c0b0700600c0410b15501b8101070081e59002400c04406001d820742440328940c2d84c50344003500a00c116602e40d4103c81c15071500c814151070070354400c081100848010440c985d80843c100141d5490f51070001c0c0a08504210486034080705285400c3e80e01410b030340842e480c8529180340c03189466442c1200d01d403652030400c0c96a2203121212241141c1c0082c000d09076421801e0026072200d6000400250600c551310f400f10040b80d0007a40112041042a003001c50803180c40c0d002100340e450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 873914757 1250 873913507 873913519
    0x80c0f0a090e0f27030909070c1a06010512061903140d03020423031c0c12080415180b090109060b09190c09030b090709050c0906090618130b0f 63
    0x206049001003204030b04075052290340000c0c900f03046914040058038421b10005108000303506028001924208821200751050310381080b00008043c51a2000c0e402210f040e0341e0a0301d441030019400e00384a80241100340d001071000294404a071007042d6440103140030f2246040740c00142000545490b02d1941d02905160052204005900c144020046611071540390b068013a68240f00281c01c11454883e9020700c00720079140f85072100c1c4d102c40e660f0f4a55203c4c0c260038070741024041c0c041c2c0700d11a0444005104002c1500315251002042d0410041109070804042004c184c1d640c81009604c0c08484640c6035039950603e00341804024041e0414007041580c0510315818034000a017030800c200c5408014554842e901c580101d4400d5010b24021a08103031511083ccc2000f000d03031602e48203c3d2140c2c409040c00c00020640e800c0c88801150480b045c006c21586c40d1080000500405030010313010340d0320b003101c003d80000071a25102d4070318180c01130254002601c144410104110000e0b030b079a2a41c0982d07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 873916007 1250 873914757 873914761
    0x70306060203040b0706061703030105101e0c0305090414100b07080703050f0d02040312020c01050c0c0d080403050105090a1b0b040e040f060614040612030f080c0f0a090e0f 76
    0x94001c402c071010f40c0e007404c0425940c0d0005080c40c2003d0440c96100d100002c400344480c5000c1c901c003001840c180c4078102e507001480c080c0b030041140e0900171000300c1c07a14500c60242c160700960152040352019440f80c240316003081c09c5280010100c0320015100c0e0a42002c050810803000000d15018014040b00c6210394140f41003600c3d418120b0140d0a0000c0610400181845016010341d09851035042c64010544d47ca50702e03490182560144910f04402502c26a082031507075600800a030b466489031071006000d084c01c480100031940054000640c1d004408000120124900b070142c00d109288210003091755104511b8016400d94440402506c0224030000074071a5841180c101d50895909281c0c0e8001610b480c00d2990042001c0c4c0c0c4c0003030485203010400030341c12103c10600c5400000441e010420701e60b881070102000a00d80e00010009201c2900d2211040c0c0500c501d9500074600d40c000720305111003500d8201581e03000e00414070204801c0d41d802c000790384400d0080c036801603040410b072582d8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 873917257 1250 873916007 873916019
    0x201060506040617070c08130509060414060f0d02062208030712030b03010b1f0e0609030a03030e160f0905010801020a08010b0a1704060509070b0708221203080906070306 75
    0x70f154035461513910400c403000c100c0851103045030035822500b00d41c41580d50103050300909121881407040c039020700f030002c00164251a142c4990002c0700140c00962032155144000c001c0d54030301c0c5400050303005142840c0703440940c8400c2d024140c82d26444d10f1260500c4208202c0000005032a40002602c3c2d104000c80310024051404a00303281646013030124400640c900000e000d00210501e8540214926202c16510011032804208003111030305d4211468130000241f101038450b600c5134907015400a003483d030000e44071b980124000110342c801d90318540e40d0140c02241e00200b81d440344014410007a030501200100d441054010b1000c00021803402d208884042c209000501c1442400107000c205000800e002c0c40020660344950b1707003945030134982841c000c07009120131380d04c8051071301c81d10002148008000c0d085800260300040403d0400e4411030321400128020019440700f445603020010f1484500e07000001094403a496000e03452400400c098a4000000c00390741c20541449410010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 873918507 1250 873917257 873917267
    0x302030601120521120a0c090842041103100b0d14070807180c02071a030402180f040506060a0605040b130f030302030d060f0f0b030703060b130602010605060406 71
    0x41c00d01c142c000001009402600c4c141d01d0054031000d00e101341d940c0301000390040a81d84188070007000740d22581840f0341c039000b215584030304125865681c11b8a0022050001300c01501c011843c61010351520310b00700b02c4501d1103040590903075003124101e1401546001c1c40c03409000c0c8202d2a040e07908200900a401d100068400c01c5041e8098501800e510480282e10340130701090000e00b0100f4101c070481595080404074420301c1e07031816824141342483d0160307001c0c4017155500031610503140d43c080140c80b100f0042c01c560300c00703002264403100c80c40c0c1c3d9440c01c0006e803a20901c1980a003045042c50310341824410b041c0030005004510610001405008240d004400d440940d04941150354403040141c04d0341300c92040030740202c60744840a0100004145d4000000c02c101e4411580610120b90303900b9489140a130540541180c035074010b0000c0c00300c010050061940a40c25181c0403039159641da906138102c1c0c0c0702c243c030380a440c2c1007420284181902401100003c00007a2412403802c2e07d80380c40208 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 873919757 1250 873918507 873918523
    0xc0806151906120f1b0806040504171b101d150a0207020303073518010c060b0d110f060403050606120a050601060309060b01020604150e07030b010b030103020306011205 74
    0x803c1c06038024441084091075408803500b42d4482c80204034150403690040c030071031800b010101c001a800e0300015024145801420300480e44084240c3c1c65880308000000705403c4001c03001042c0325441051520322004100703811802c9001107000584100e42817568800e000c00c08050303403155000b18040c0da40310005030300440d8000d210000041e1180c0e200d1000034210b104544024002d0745042590070540c0301c07044299181c100d05040300314200c040600a000113030091012111310301c1c1810002c201154001c00c40c01c0126072080c84005201030702040003908840044006552003040b810140d050380c10244e00d85064400c00b1210203050510b140c0e0340030f5072404000c044502540144103400c0c150703181008031410455001c03040e910590b8640c0001801048080000d039401402c080003940710354008642035005a4010860b002e48540300200c0c0e9018006480d004d15640c413400d00008007080488046a01a00b25540300e556203514500405151a5040c0c00c090009a55030382098005000010390300c0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 873920863 1106 873919757 873919769
    0x1518140609011503030e0120190311030705070317040b0a05070b0f01050303070201210c030902102a0611070809040e0c15090a030c08061519 62
    0x660b0f403000610000c1e000c00d2854400c00465407080f8000d0845440f8001c040e000581c40c0c4962500d042e00c030a40c082501c0d12410100002c25038440e07090b02e0032030492401582001d240703485d481d80301c4000344401814000802003c0e040c03401403200ba54010071109500c00e494485107100035146900604003110f18245550000301680c06503a00c03e416648080d005504040066005655480d050150f00103101c8004060010040041c0200954441113980114581c20b10348140814090585120414048000002100c10401603030540c10103004a070203e40c4410141484001420070459142c0041000101d8005000403a030052084203015202040f4001c0c0a90003141c131403155906155004500c3e10300e40c00d909104401070004150010403029250b80e0769900c0c0d2014038007c0c0c3c82481e05421610400c84074803141721001e0342004054030b902c00011440c256098030081c1c80c1c0a07017 = true := by decide +kernel

theorem cover : BRFrame.Cov 873741007 873920863 := by
  have h0 := BRFrame.cov_init 873741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 873741007 ≤ n) (h2 : n < 873920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
