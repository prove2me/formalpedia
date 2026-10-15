-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5348
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:34:21.735267+00:00
-- url     : https://prove2.me/submissions/8044b085-04cb-4fee-8524-0b1e7e4eccbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 961690647 ≤ n < 961870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 961691897 1250 961690647 961690679
    0x3030b12060a0b120a0312020a0306050d080d0e2a01110604030c0c14130b040e0307110a12020607110f0d050109170a020703060905070f030609020315150d0507 70
    0x142e80000b01c0c0d44542007031010803a00a01020b03115030040160a0119811070030701d010080010300050396030703034075000c048015100950101d41c201c1200341d40034080004000150030500346c2c1c4a410050a0046562259a0800340300c4440d0101700c04201030401444580c00140000f0f0706040841200d245080f1861500c0802c650a030002250b201c4404108000020360000502d170b034000c1004403140d80c400041807415003030081444540c1e1100040e00c19202c0e40c104030b902c1c8040300f095039140e1105003000d07584000c00000684c8035954140000c00c41d4008150040601a00945401c0c2042c01300e9546107110000b01c1c20096011480f80360748061641e500b000000d1170361261001181030300b02071038171004894260002d00031002003030003c8500d403a4000360003000c0700e40040002c280740c5d0719400c2203802d103089a003080711000300b545d20110a00903e0f4100784c000c00e100b94100c0e203d0390705006001940000541e080c1c011055404240c071450324045d04c004000c140900199822a42d81e003e03420410004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 961693147 1250 961691897 961691911
    0x15040b0d0908130314100b03071e08030406081608150120071d01080105040201020d200303070f0806180a09060b061602030d020a050307060507120c0302130f0e0403030b1206 76
    0x40d000401108050a000003400074264140510104030447d00080d229070321030180d010344a101c102511280943c00c2e01c4400101818000e907035441d80c40722001440f5003401c6810360401c0c9091f00d1040001c1e4440c462641c440c6503928001aa0301501d0320044608540c2c22103200b82908030680202c15007901444220001c100120002102d140000d00380302c01810168080e55059251408000240c0d070046581502040d1600d8031850380c00c0810050841c400c0d1800c0304080320705c07010042000c5c0b00d4100501d5601d416080d211181c1c1d9035240400c00c0406507541c904020140c0c4030307001003050440b2642000e02d03818400c1801048591000001ca0180c0c1c00c002018585812480442010f60a00740800000c207800ea00c05000c52510f591552540e0340718446005105603a41d000003503d0b07600c20181e081a550aa01e028842c0b03880402c0000d001e900218113040c5c41001e100720005583c2c0703020b01190100d4035568810116561281c40903070061801424036504103200c44105454040140004d034415a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 961694397 1250 961693147 961693163
    0x60c053f041a070b0f040c03060c02150a02161214070c150206010321030b060a090f0f0311040e0a080c01060603321909080915040b0d09081303 63
    0x3140082205140c503000050b00d14141003040060302144c0c5554000b40d000d601d501c401c0e100c0e030325585000c0070218081d03072001d800c09207440c0602000c1503000c14001c0b100807600d08020095292006403504a03c102c2c0c142100007400411010300003081e540e100d1011a41c1030802c0c800f158043d117100c90032940810b908a445068420301800203040400100400b940184001e141a6044d95103900405040300a40c80c1c2c80d141d07131584000c4503071082e0004011000060700d200d440d12003000001d4012425030048050b0026010404500d400241c0304545c104c170b40051030411845880002e200c01412081210000c6006605249010440c4800104043d010040c00050341c0781c54150001e00b01c0d15140039408613081c0041450301c030044c80455003031040b5007000d0b5072203c546482000c07482849103555281581421300d0803c03402d0004120140c0040c400035a44480e080158074606184c511841c000c18206003024007031307201d018019900c41c10312503216000403850508081d40310740f14103034140d00442e03000c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 961695647 1250 961694397 961694399
    0x6060312111b01110f030c070b0a2106050628021204170c06031006020f010b0d0b150910030b09070503060103200d080403060b090408031b09190609060c053f04 70
    0x203007040100d18020195109c20b64200003180c680103141c680d004062001003074000c4c400c0e202c00d00b0160300c00801044002c0c152036440d401c101008007100a00d2605014031a0354907554400350f8000b00d5040a00041e6a40381c034031741410a481604141180041c898030f511505669015645a07080214000d030352060510382c245240a01c001e01d090303155127003482164100640003034141c0b00c903202c987c0c003982d03c1064480c1a0340c40c540405100400412036607400440744042c0f00114040d0040300095034040c0340003801039510b0030203007941d80e01c191003200d8059000c400100041080418800001e1500704406400101c15000240060701c00e0300e000e0301c1c1028002802c00c1088130324400c2c030100344820380b007029091516444100b0b05004c0142180943c0c02c5451448006002d2941200c07405034000342019400c02c0b070300c2601129054203000d0032010071058003001c2100350003005414200c55015004160854203018054602035050104a0758030f85400d1001ca5141001d880b086501106c0440140d211 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 961696897 1250 961695647 961695667
    0x180a14090c0c071a091e040b0f150c070f0b04090b030c030a02040e010209060426032503090b0a0809060709030201020a020d0212030706060312111b01110f03 69
    0x19400c0a4004412040100811812907101040d102d048031101c3d05448040110a00c850b48240704044c02103610035912212845040d00d0201002030400d420b441c100300c0100101c050120480c011241d15038440110310f481042452810000e00c1ca80084a00791010a80c0d6108541500d1015401c140e00300d803004641030240000c188141c4410079411001041c4804840c03010135140d4080c00d4010b4041d544920058999203025011100441e002901c540e5850ba602c4c0704502e07800030300b0122300d00b101e60400d1000d00c01c801c0000564072032496080c0d082c11046840c01508803265102e1400320103000703070f485000991008000140020800c40c2e15514414548040b0840c05d00c1c0c4001e240700180f042c192401c2c400741c1da000499404a95054400aa40080c28000038101440600c03503200c071480005803e60801c070082d00020116480388504291424602d081981d114120311508410365101c207440d0b0071807100211410484a1060425a8020700b0f02c1d44002c0c10a840311000c480d00d6403002480200c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 961698147 1250 961696897 961696909
    0x61d03070305150916060e010311090d030e0f0a0b250204050f040507171b06040306060b0c2803050702040e01050703060e010909032312040c090e160b180a14 69
    0x60216401c0c807481d4611b060140240102c004001c1d058105039640d0000c0f01c9903000d1000329050400c0041444120005500e0300504e2031a442c854207000d002003500c801500d0401c0340749003007030700d003110209400e11412407110b00700100038080552121180c1c5d02c0707190142c1c13a1845401c0c0215401031604c00d00b442d02e820b003e49800100d50100048030b0400c1c1034601c03080c001040070b044212400c003a40002850000024000d8003c42e00081c0a41c1e19000c400282219448024418480030000f500c10000703005042d40b83c03900041d40c00c8003081e0040d40b454400203100d6801450a184028030002d00c1408020003603003122003c6a01e00080790361907900384050801000b03224010014550b05015412082e0780080006600a444070350264444c080c003404c40c1c4001e0282c4035646911852445075107420b0a007220304101c94442ca101c0117152104c0800210b401050b89142001040302450700741d407800300300d4000c0d40e0100c01c085c240714040e1410410541c1d952647e4800401c4150500c91083d5044000c010b2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 961699397 1250 961698147 961698163
    0x1203110a0213020c15150d2a032a060807051b1b0d08070b070c05100b01080c090d03050d06170601030303050f01060e010c08120a0e16061d030703051509 67
    0x1c9204209040101080c07401240095881b0240e40441c0d030b860041c501140d0418a8080341d9034500c0c00f03034846201c4410a00b641008a0b4050010302d4103a43d0001400c02401024440043c0c40d40e50303c0409100c030314021190990401d40603d0b00c03a00d440303402c0b00600e444088a0212140c06d8010041c0344c461990340040103100b41c0000c80b03907140c0724501543c0d44805440b41c00c00c01800d1039003401c0041d039001c2c040d201c480c00064200d402c0c0c40080c3d04030b011040007002244101800319100e400480c85150344041507030301c001d00140520040c0e9900c0e84090b07030700d0381006c00780041070b640760000414070390a040c0e500000d241c440d500030150341d411480e0107805c3d110000c1642c003074441642c0041140e941d000442c0b100c003038400e0038a0801d410140c01d000d2090701c11810131103010060300060040c1c0307603a00c2e800f40d03002c2d501000940f0444036510401000c2542e01c0e10034000018a441200150a8809806d0806403c0020708032615180d030703680d9840c00c025900340742c400c4107000740081001d50341051002d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 961700647 1250 961699397 961699423
    0x10030c0801151e09030212030304031701050d060b0604121b050108250c02061204050706030606051c0f1b180308030a02070212011b02161203110a0213020c 68
    0x59010940040010b00c91241070a901c0c3c0340400301a458402c00c1c2c002c0543c080a150040c1800482c42c202c25202943c030740c02550205c001030140348204c002c030019200c0d05816500d00400e0f15481c102240c64140c0a0050b04050380d84c424002c01000980c203a4446e040508140300c0c90528100d00701207400050501900c1e48100c0c1448041401c1000150f01020502210a00c46048980401070000304a400882114000350480c20001f100b6006060000c011441603100d0300c22074002c582c441c5402c4007078881500c5418080f9005000350700344140c48088094404041040010300e5140c841c42e00420703502c0c401085040c410030000700e880303601c0c0c1c4181d8480840010f40c01810f16140785907101c0390584802426815000e5000c90a6030842d90f038075840150040000300207004203444031056514050f44009200d01520a001000181c060b02c1403000c41181c03540ca2608400d4001a10240d419052a507060215406540c08907801680d901128403200180c1e804010307200c0c40000700d03071480c02010705044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 961701897 1250 961700647 961700669
    0x110601060c152319020d140610020c01030e10050721020f0403020607020d02092e08122a1b09042d021305060f0a0806012310030c0801 59
    0x601d59058580d90782041c3c1c2c4981442e001c01d560740d00340c01502500d5100c9400d0058900016810034006d4aa802c41040700b00f007107041081d02d0b220f81c0f04000f0710211507000b14002d6041449d50390210740c0642c0c402d080491a00d030556034069000e4030341d6030840340704454079004501000e00c4c0022118400380221001884400c0031032170400c0c1010311308010702440c40000e04c1440d00003000021516400075807885981c0c0540104c000d82030040900d89180c00b402850542003020b100c440040c403c401c403c99049960007005040e150b49110802085079002c10440311650440d0030360384e0103048079613111480c4186c441c00506008a82e8182d040360320046e2240342d41c4140791107020700c004900c290846100145168040440f00c040c60b5039805001d100011001c2d511a14040440d8010902500031030b1140c04116040001981d0080800040a56901078045030b540500e0043c880350f40d0150303000001c8200b04605184210700c41e00020144030701c103003201300080c0c1c880700c503246c0e0b40b0b81040706180586404022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 961703147 1250 961701897 961701911
    0x20c0706091d13060207110f0d0b0402060a140307211416020c1206010e160f0c080d0903180b160201270b1801020606010f0f110601060c15 61
    0x200c070181030b00411003642c2c0d107241d1001092001c032140c0190042107501690564a405403800d00e088402c8411030150b0192044445185c2c4618107503070104249940400c0410080d101c036001c1c44000c3e041040b00000b030100c4140d004640c21060005075203d1040d0755a40052641d41c41040c81c0130b03050b80654425580e0501c1980880d80500020942d8080c40700390302c1030103410601d0400c80c035224903800599040800e0034200180c0c45004030b165816207040c411480714584a4070b070040200d40e098070b002c000041c40303604a5810f0901c00c8101015150203130210070f0410703000b12400021101c5420303044004c5801b101700c0c101d64042410f21407008000700385e4898102a1038610304a1507542001b4000d04001da10700d41c0c920120144982174084011501c9170900b82501e500e460030700c40c0d00c00e10411000300c1001c2d5181001e580f0018103d0307ca442c1c10f948030b050f0500144019100d840f4494118014400d8452030340e8121101005482c0c0201241d07911105154402d00301842c00e400c00021090a41d400c201c0c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 961704397 1250 961703147 961703159
    0x902030c0901030b030c0a060f02120a05030402011b020a12140106080c0f012601030311030a050412060b1e1801030f03180b071209091a060c030c10020c070609 70
    0x820380301d52503002c0c00c01040710096240064204006100441d9000c1040207011440a9024010001030b40954003103a10841d1034000f030308850b00441f81c40d0400501d08000040041d4070600d060b0308040718500703100515040e241d0000b028000c03113802445100c2040c0c1c1050007440302040894040300c501c50f000708451800d001c80181c9480e4841c03007440c041e01220074070740800d91140d03084c1407540c00c81154032003007058224034420b0b40e28070a02c801c1d030006201ca100d50117001c5000c41207410340c032801d440301490146400d0814804d0384ca000c4040d07031550b0355180e000d5282d0b00d4a8030b80c1c1400b0b1100f8007003006208201e10400030300d00040f00d600514050400d0041c000103d0510b404007515800d402c000414003c5005540c038100101c0c3c11481c0f64035004101c040030441e032020080c03034081007911051003503030700e4003411000c58440110301440d604002000050a0910600601581c0c1b00748090301e00d049060b010462900e2033100504442c503600007000da0052100f80007500103014145000b0210380d251403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 961705647 1250 961704397 961704421
    0x708061903030f12020c0c0f03030a0806090a0906020d0f05011505030f0c2703011a0906040e030405100905030105070207050904080c2b110606030d0503060a0f1e090203 74
    0x102000b420f2081e41804240e4090141e403c02007503030380b400002e556030b00b1364071169619212000d82950144c400400d00e90354918003c41a035a040b4000e41d65101e095079a03c0c100900380388080c02c2c44d003480d555134002001048190000b48084181141c0124065020310358100480700141d00003003020845030a8988000c0d0b120040f85e80122810b15400c0c01d070f45444044c0300349881880c130400c00242003000e02d980c0303005544d804900030360300443c001c00c000707000103003045990303a8980c00c81540000000c0000d0041e00d00b40c1c1c840645880300c141124106525500807500f600100100c02003c5007288004000a1800740100b651143c0644081c0042528000201d0328100003e08001c0800da40807901c48802c1c501040003080d0b54482511607529440c200100604e00c042c0301c5050340000d0034181706d0a121040010701540035000150041180403038200007112990009403200d5032205540304005403908619400c40050107122544007a03620400344c1442103041300e03901052503980140b08003c82e1000403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 961706897 1250 961705647 961705649
    0x24040e03030619140d1b172515031118030c030f150a0f050414010507080f0112060e030d1413020f0f010c050105151503011203050f0c0a05010507080619 67
    0x11703103044900301603a01d0802d04005440d482d503a42ca001c2404d00190015031071210801540d2110142d8041095281c60055003000255080340b122244403001c100401041c10303c3c850071040d40c500051741c2c2034155000404c0c1d41c4080a013801d0308071100880c140500d800d0080068900f030031001081c001d08020503050700d5200324017200c449003403402e00041c4000300e2038000b2940701d009541d0070000b91a040c41e1100b0f0640e46003884d094598a810300084c03000340200401c0340034002000c0308550740c0c1c1c64038420b8042c0d21400c8030103c403810b8541107411214101000a400c1004501e1740100341d02d0f00381b0b490000c40043c002c00310019400c001060002580316440340301904803056840608043c00303076006842400700304c6401441903203010100151f050003181004c004c410129082044c1012141d89001c0900080c007410303100d505e80c1c02d00c00001a0040d0003d00d19440401030316400d00c10b41c5400a402c1a221200c180c0f401e0b5110740c1006109507211841c25485030044411803481d0842c5a010410040030b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 961708147 1250 961706897 961706899
    0x5070f020f12030c21040c0e04020d06150e010806010504390306051003271a07030605060c0109030e150a08150607080d05070c050624040e0303061914 66
    0x1001010641c1603d040080314170802e8a0074203602c8460302501030020002013250182c4036192108004110003031000385840c040c64000b040c01000003000d40322a80103007040441c4e82c041d14406800040d106d0801003181e8000d0010b00090151585001c0510060307690081103001c20468801e480603941c41e000c1004068810041c0110018040240080d00102103a800803580714001d002c0000321598150020b4041a10310a140008241c0480300020301081024004040c00c0100da24600c1d0f2103d195030306940a000c07898041001c41d40c4001207546580900030b1f444180c1d4641d090f96062507006800313840701030030581d00283c14034000701c0485554000d11002000704409a40030071b41c0c0300c2e03014190034220800105547e56461540c60040455489070f41d440d5045410100003899080c01070074260307920350f04400a414650303140c0c00b0035040300b29001c041110840901d04000c030191207910074131049480d041e00035a907a0030300004100c1c24010524429040714040302050102ca803078102c41c1002200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 961709397 1250 961708147 961708183
    0xd08090d0e01120f090c0e070e040f0207060e06090f060103020d14010f1d060a06030b0c0a0504030b160314010f1e1503140109060b04050609010512010905070f020f 72
    0x601140100c5071040d60350040d089490404481510071002c660280c405c19104603480711075940d94140282204000300c070702c88041054400715180b913040582051540b81d698840044c41c0c80d010356100710441d201d40036000501c3c0e210b0746c1041040702c4100701c450410b05082d00103201d00d44c03556000990012150340010040c0700b071407403401d40c01642500118034500c15a10240044160740d841c00e4010400f0812095a521030b11010544040e024032071001038039006280000d03155101b0340002c8081d4095039020301000320800002002c140030b08007503070044412003141c1211084420300103040e030301800451100d00a102c00100440d4500261271001c4600d43c002000c541c5154012030000c21206910070b100388114285c012140c0f030ba040d4000c1b01010a010385200c126601c6410490494440780180051a4810407013032100d840c012000c0c1a03440e40502d003e0380782010380d0a0410004400782c3c09520744c552030b0814071805a070840c00000d000042e17840205107803c040c103149540c6080d10810f03280c002c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 961710647 1250 961709397 961709417
    0x7170c15070203010b0909061006090e071107030812040b090129041404050304030606060c080706020928081e060103060504140a05060a061d04110f0a060305090d08090d 74
    0x3d1000c1d00400303010322009140204a1400144241d200c803c221440d44114803604008282c0d1400359040b04c00340d40c1c0d50000008aa5107418094510b02d10f02d02610000d4851040e00000141000008101c21420941c40f410641003510780303c81c180304080c10200190341443c60518040d00321348043c1000da405405c1c40500c10310300101080082400501806606408400304000d00c10001700800460340725a8040003040d5540c44121541001071342c0082080c1c80070425100841c6e030540140611410040040c1c01c0540c1c18480300a140714440301c001d107043e00110041101c07800038064030441050b04050b02850003000c80c040794840005000041080d40d032213021500340a00b00c110360540c0d0595808a03118014982006540c86908031005c1d079610f4103011010420038510b540c0030300b15020b0200004519180c590307444840003030310304101d40c0046076404d1401c1c1550350041c6440080015403000242810401009410050181040c6d0140205070007072082103e00085c000300280000e240000c601 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 961711897 1250 961710647 961710649
    0xc0a0201121d0109021201090201090e090c0d05010b0a05040c05070221060405070f0f0302060a110c041a0f31020f301006031a060c07170c150702 64
    0x1008600b075046804800d150b64140c80400541c0030750001c6000702c500c0f40707031044486c00860030b9400284000b40040c119140030072058103107001054102d40400203a662403d0080040b85100e105d40743c2c1500e544e03441c2c540682d81c9052411380300002d09003e4400348041940040003500d544202c940090283e5406282030903000c25012042100540c0001521401d0070b1905020340d50f070038180218440c0781d280070000034080384014400b00407a0303409011507042a800c0e100503a114800205412014010224240041c0d544d038070a140c0003202074213050380ca28913000c080c055045281501d0600901da000c0d59100000c0d40110300300785800252422442404008496002074000c41817582c1041da0040707084a460040d080d00041c008182e003170081720400100008003e03008081e80c80912800300c800044c081a40702e9080580102d00000034580044801070104d45580d02071030f10341d080c0340c0105100784884c04003218040201030f6120010480c40601d0342c0050a0030012048508041400003085021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 961713147 1250 961711897 961711901
    0x12070606090212010512240603011d0f0f0a150209030a0f0b0711150a1a06040308030106080c190f0e1207080d0302070506010b0f040b04080a030201060b0c0a020112 72
    0x50200d1940940d11201076584078400303883c083c0612441505901050400040001000c00c1d03100c408144120030303140000800109104090f140c90703099503c50505100320581c0c0d070117809406118500030103414030144580b5080545004400034903400090265010030000b00d00340d0f40342101d0040041e40c42140900083c41c12950700c0d001007006084074809030500c0156003e491003841d040d02c03244500700100c0100764580720005440c80103028081c010408103103a80d80705c0b414480c06002c1400c48160003000041c030315089a4801c90343c4031800001070001d143d100c0c2c001a0003110100d0700703605204890181d203400b10041480303c0c00f003018100707041c00080c0c8070310000d10110102500d4a0b6241a540402c591201003d0048515500c02e0700c0c03000844034484c1c0b003190585a080783c00b400340d90f420105400202d50002c0c2e0007044604043c000803966030000340080008000e24801400d02140615001e4291651603221001c40c41082c004541000030104816130415824640036203000a24032103400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 961714397 1250 961713147 961713149
    0x7051303030c15050f0414070819020a0f0305030714010617100c0801140906060906030708010e0601092d031709120c0102030a050d140403090302180912070606 70
    0x15280200000241600400d00e008024040c0b6003d03060341050441034002d440c070590701000a18000c50004001c42e5601060355001c01c1040c05841709195110011480c0c42d201002d040303481415400c80d0000c610b07000c00b03940008e000405440d11300f1f62540d162183c69000d2410080c0419400d1140504070035003c1d84035001402086032420200d80c1160700d407e58644030000070030b00b298038200403200d40038003480016041350782c0b404007020840c0d992020f100840350064612500105c090121800c10b03501e0f140174601c40e0306181d590303044561614040075441c0d0b50280c81c440c14000711020511040c0c0313891003c41d4800380c0c0300c403044150400300020b080900c01c180d44040d1400101981113008612290300070311421200300d0303400b0326007040810303a03c5c0c43e02d102604071070140e4402c016140480b4085e801425001a17001e0000494880f01420072030391344400c45044002480000003881189005282124800c0f40c2840e06280c919144801d155101d210542d003c10030040414410100901604000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 961715647 1250 961714397 961714417
    0x30c03040c051327021509030a06020c010506130e07050103110702041a0f040608070e19060906051002011a09090f030d020304120804150f090b270a1a0705 68
    0x1402c84a0184030f072800902c41044400440080e8805000360300013080d0442e4000c540040c02d01c1c2640341c180280c0318213030380311144c85505401000d03c11404900c803440608454900e5200220755840c005040240303100f1000c000c5c07110343c6e00e003445c001845c190018806050328000c0c200007a003e00e8401e9041103c1c000c101c4001c0d401030070000b074000d071352105485401c1625800c3d00c5480c074100b420400c102c181c484a0040302c01039400303075a080240761200040c054000400074404034144d40b62845807003d031491138005c25a0755403113010030030031420908619400446544004c103c2001e006442400e05200c502c102c6200d06540c0e008201049020300200c104d40035203808503a030302e9100302ca444019420480e010b84202440c1d50800d4082801806018810340e40b2074100c1c2e43c0543d02c800c068008042118060b03c8513981c424408001441400320301c1e0080c10344c1d1201d448080340381c041c11000070b00e441e03016442c076030020580000006d02400c805103031901e402d11005883e41d29903d048072140249030b500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 961716897 1250 961715647 961715659
    0x903080c010c0806010509300a1113020c0a060b1203120103020f09011503022803090b1f030818030a0c0801110f04050415050406090b040b030c06030c03040c05 70
    0x1950400e1055006601640d1240c4807801d03030390f5813280151480d008142501d600400e40c000f410301e489245061941441ca200c0c4081004603200703800140c6000d0070a04100c455110030813100031075180c2819500c03e0041c3c854000e51504142c13080c1581c88554075800100f240703441f9600c00803a0303039402461010300035106040b41e45440f807415100d40d440c5400e1106a0044161281004d03403410026400d60580304803103103807101c2c0316030786108800940c008010030040100300f0380c84610010240c550ba03110100c042e6808641c9409506194004902c00b5143e810905001c05070031808000b4480d4090859820020071a00c0f507055828448803074650707052003503040c024140000100300007160720809940c1c00d50001c0203c200b107100d19800d14840c0d8540213003420300621081100e8a000c0d000b41b10031101e6000c85d015043e590b5401b203002da6649402441d0070359102c81c4c1030111400d00c0c0c411001c0c079a20460062500300380c0c10010030030700d00c00504000c201180010004017403041080d0020000c1401400c6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 961718147 1250 961716897 961716907
    0x3120e12030403060f020703200a0506070806120f0d14040806160f0206070c0230250e0f06030f060702030d06050f091602070f0b0405031203011a0901090308 69
    0x1503031039501a000482c4d40528010700e40400d041140701b92030103030358507490700c404003007590401c81d00400707032030600c20b61610683c90000c002480910103680030751450348400c03101d8140041000815100c000604400d40d004000d07414811100050182c1c080c0041e080159503034003815080440e40c800c41d007100405105802c280040c03c075001101c40c40c845d54170b40d40c5c2400c25030030040490700c49c1070940300000003450b260030303610240c54032410100c000c2003a007a03c007903c807030440c04072900f4100390b040114041c0c1001c4404941d061404543e86c101500710540c804109040580f00f0081c1d110140c26010300b03110030300005110303880c100a4044a00141d81c2124918540050b000303580350320000482e400300d824000000780f541860381070048035050003050004282e84401e010a00c0354400078000c011442075810020300f50302c072500f507072018222030025282c0e6030303003407605040c03400100c410f606c40d001e02c1c1000108682442d01e6400600701d540d80720050358650202004a501c0344190304054124240003036 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 961719397 1250 961718147 961718179
    0x120c0c1703102315030c0a080a090f0609031b200d08040905010620031b03090d050a0b0c19030e210306030115080c1201062103080606070c03120e 64
    0x4a0fa81c082011182402110200714221000b40000c2e00e0500724000140300c603a41590052581070380c4003680400001e070041c82900c0755080d01d807180da015100a5910b000709420b141d0720001b10b091140c40304810780f0800a00360b4a1018094204c4640602e143c8405192006a80c52542c5d0140680c1c1181103a9102d60325402c000c0c000300000c1c4203400100b507130184501440c10000c503490b00014280d1000c0c50134224a800c1c01024074528200000043c00304100c0801035580d00080c1e50485070083c802002150b0141c90b20005407400a058005111000d2005007002c203c0207040c1480b140b0189008512845003280d454138101280c0d603100c138660500511094200d01c14405544038000440007030000c201c054501d410305a40900601c00355030007443d05d00b1105e042c91052488221120000000c1c265907400310658240300c602071040204540740021030903d81c0c0f00c01102c2c2c0100040b81c00528080983c2c0d540520092a40300003060a2043c26410044500030a11852810740140c25401c0c03002201f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 961720647 1250 961719397 961719449
    0x3180b060f09011509050109150c0201200d0206221202030c01020301061119080f071e120206092b1106090f010e031e070203030712120c0c170310 64
    0xd0404d00000f9051400042c842d8481c0b82c0300001c4030510303d0010090b041e18102215400c10741071050741403024460205488078051414194400c044001410400114820003401e02401805400c03281001c401c01c00580790508c0150651f113030344000500e80340768840000347d0960064140391000783d440400000f071241c0d040012144028010380a0b41c014170f913014054200055140307000b40418030140401200c80c00c2c4400184078103400f42008464030740441883c25014000308904031103010382100240900ca8042110503003156075000900040000b140c0003054a059140151200000c491540d503000d84c040e0410120100c0443c05981462500c1c541855a032000c4107808000c2d58038014455044510100a940c020300b90401880400b0a681c1e1540001d50460107040e80d05000410600707002412455100d09059460f4554403240301e1240720307180071a05050640414080c8101c82d07440000c40801d8906d01d0150303550b003015141d480d400c001034860251078200310054a80740005560301c6081c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 961721897 1250 961720647 961720679
    0x10c080a030915020703270506131a0301062309030a110111120904020a0e031005150603070c0312061508010e0108031303060e120708030604060603180b060f0901 71
    0x401a40824440ca80f00300d078100e114503800900012491042c000301c080d10000200c0d440c113071180080304050745560002700a58010031000312109444001006608001140100541c0204030190f0a40d0b24000c409465070318058500e481c1c0d4404804002404a5206c0070341d00000c83c00b4040b01d07038500041c9402d01c21135000e00101c82c040703040c018030b07180711000c00108840051041c401d040e0600c1d00f002c0030700c4080e401c60828a02400b040c008401c4141e1410001ca41d41d0601c140c10202d00c0d420044401d0401c41f450100017401403500b0400c20280c00d410036049008030394546840c0302c1844282011100409203600300609a00e10010007040c92588954040d05072001e0b801c1c3c40380240da03280002540c0303100d410203840d00355100840800104070550700c090710701e1070082c01f0703508101a0701d090460300360320020045800d41404030a02c29070703041a10450000c2c1caa03508040215922207144059407040203500141180b07071140002d800d03500ca5001483c2100c001a09030b03403440d6142d03141c44001400d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 961723147 1250 961721897 961721903
    0x6020712020f030c0a030c02121203070f0206010e01050108090a0c08160906080d080c04090c0c14010506011e020a060921081003080a05091005040503070b0301050a14010c080a0309 79
    0x2d10348440400400403049640482e2400c00a142c000c1050390143ca00540ca06810b80c0d1010b6004060441240184014000381e00d60b92905a078910b4507843c05001303074010240c140e0855210400602200c81c40200d114103403030302420300c00110307a0351150b1140782c40c1c00305000400b0f5444030100040c082200145800e0318030445c06c1c8850605490b0b1041e881224810b1142900300d500103a04000114000d0380d086801415100034589060b071181801c006480b901e0005500240705440880103115000c09210207035640c05000384198104000000d004490401c0d50065401d05001300800d000d0003040385600032544081d061101551a042c92020307425038031407800341c060402c4585040d01d4400d01020f84902e051413561210b0f03500319111014550080e940c20000d0180401c42d00c000c9540302c490207002e0391a00d90340d4030780e101d0a00c41072604088042c1d11141c032444040c03005100765a01c240d80001503c44d0443e83d0241c6002000040351482c002ca0409020b4000020310a8140340e410f80002000c140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 961724397 1250 961723147 961723153
    0x50a12030204061d0603070f12090f021f1e0e190e0c0a0f03050703141f09020a0e0d050c1206061005090112200c2b090306090f0602071202 61
    0x86804d0380010401c1003a25041d600003420070014800e18015400b4009505c21490301440d01c6c2081320b8203c00315400400207441c2048a602204210300e001c00314031761403a49914550090b110712030009003d280b55100000c40000501d100c006c1d06500c5403411111b004401020448030940740c42c180d040041442c01600d0030082c10000180c4840d60000c11900070b07a043e60350340c050013270000d4011001000091b000ea0205621234040c0c4400c00d2003450300500911407540b284c6a072203980c28240d802c0f14420b038022964103005021040c25035070440801410318005403040d11a10320359140071410b0480ba406c1036580901501640c40303060000044183c8034074015691101d40d801c1010050f655400342c884003500144200071a85420b003866040f1141e2000035503044100131560302420040e0390007580103410745621081c46690002c03e1981220740d00c40c51030b031010b4141c1e80250002443c4541c1c1d400060040c80c1c84004910410654036200010349401007021502e4840d5450300c44107082c02c0c1404000144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 961725647 1250 961724397 961724417
    0x110d050a0c140a0507020d0c090507030617070e0414120706060b0909010b16060c020d020c2e051c1a1207120f0204020a111c080a0504050a1203020406 66
    0x40c01900703a140d4900288200d01d0500b030f001001200d25900c0440c0c1242c02170040c1c1074040c001540550454003030044c0c2100840c80d0f141c8124001c084506640c00700c1404045000a180300c10004500303003080d074103910381d5070351150b0711410034407070131844092044541d2050544001a040d1540080c007801e9100e07040074403500703944034801c00d02c86c007400e04c3c02e0364400003410040268500000c0100040b1148003100b0049402a440b90b60450303c441442c400541c01041200a90b00e5050010803800030302100c5148070240c025400d401709600c64011032a522510315a0000d0540c000d40945031528000c0c590039a0103504540400007426119000329240510045052090314005001a010384c030300a000b07002c0c40b8980706d900035904100a0007aa07049810715010b40140c0c480740001c0a80d417400d9120189100291a5907915013003940351f640ea6401d40e80f00600c1c43e09a40000016000341010300c0224042d1030f1750030301906004450784001d2440c403c40d200e5001c000d400d13402800c1221074a4403002111 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 961726897 1250 961725647 961725671
    0xc0a0807021305010e010b0c1603060e1905251a0a0809010c1715060f03070206010653011e06121107020901030606140607110d0303110d050a 62
    0x3895080c0181d03800b505c00800184030b54580803000d8000c50b40b044045419071600c03d030051019121030340064850b01c0d00c50306c40310116442081454031071b4408098403040590703075440f0540c4408107250005400c071800006484c0302d03d15440c0d00f801900b074035003000c0c3c00c0042d14400c40e40d00d81d1203480b22502080d400000a250b080043c425007407014489d4440c1f1140d41305540000503800c00091030003800d81d80e041022106e0381c48101c0904403002220a2607641c2c0d081c1003501a06c2d010b4143e10007820400f0600062240400c64001c090703402c000402101104400503d00400e0a5030000c65450040003104030300c070030303030228991280c122000c41d05d080c503586605254961032103059014100124100070f05540b144901c55020400000380310404e1030a0008590000e11007120aa00a40d07132592034000905c0015003004c00f201d41000704884aa140c50078686e11440b070184030251140c07089812405803010f05000340c2216040d06500b061859843c00801c03060300c01420260341c1c519809203010340350450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 961728147 1250 961726897 961726901
    0x21605010e01080601180801090305040f0e130b0a0f0203041208010b09060a110106120f051209151803010513031101050126010204510c0302030c0a08070213 69
    0x141c0040e520101c2c02e5a6200040d04c64040c42c2e0481548508403d00c0004c1c1e9420a115030500c69200f43d035541e0b680ca00d005240762000c001d541240c101082d010080c0f0251440c086113400c000c90307000300c040c111640c03020014001811584121b50015000204003c208000c071014015241e00715101d07106266200c0e4010704003409500c0d5200d07003155040200c2c130042401404681c0c500310f065400428000d40f55030f82c404048012280444421002400344420000d040c061402e00a85507110907040c10305039400101e00030718070b10702e8000742c0b8070028060504c101810079086078000050000d2040d828510b92200c0302c10708a01c400d400080c01e04246e03e50182e0107025950481301080c203001b5100242882107182d461038807040b01100d42d03007000300080c40710000100000300000000700300a90304050183c05082140410404907a030100003c0c1280b84804446640360b200803413401c401100254a404e901d140300b01d00781483c1600c0398424850030042c04078010f0a403644285c0740c0441c0b4a403000f8810007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 961729397 1250 961728147 961728167
    0x13050108191103030c030c1009050d05070f0b01080c010f021204050f0d060e100b030a150f060e0f1b04030317190e07032307050402070602091002160501 67
    0x31540000c01240d07501c103510903003108194010341c4040500990030000034074652150544000b15000400e541485030414007520000ba4110340c002d102d000961b681d400d403a640c035042032109112000c907041d01441100c00d024280103901c02c2c0f891095585900704c40340c2d50511155013600003035212199503d028400b040c01c4440750075118189040a04040230000c06105d0001c3c2d0307942011900c200300010400c0c500813041d86448001c040d1031680d08012001c4240ca111500d2140264045408400001c5443c00e0600300130040c490001001584110f0700c3c4085c002e5903014009c1740c120481031120900902165600483d00a43c100252005903c4601001e0065101c040d0118442d60484055403030604440c95216410345441c0791407204e0a4141c0048070351808250400b0750250b0814010054041301168411500001090009980107040d41d510001406144d00840e0045000001c016464050f00c04909000340401ca0000340450300a540c3e0f8a9481e04450146880100003015401611080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 961730647 1250 961729397 961729409
    0x290a060924020c090a05010303030b09190515120f011808030c0a0513030501243002040203310c031e0b090a0c080f031b0c03060a0b130501 61
    0x104080200015105441c10721501d1501903000349503095200307075104c4480070b01c2003040f0307580040c2e9941141001001c60f03a252942ea4090100b40c810b1202c9199523110b155a00c401d030490104190b90303490000031840584030b5650f5004030721080079885003240400c210640044600c008c01c15000b511080341c01c024a140c3c0060040d11040000c6983e9144034070040492302487e00f003040c940071004080c200d03580c55a500070368a40c2d5441f0758851035103200041a41c40103103801c0f9480c0c0114101450728580c2810b02e004010b20702c2040003400070010b5641554001035400500c110340364070348002c0c0180f0350801d01c500d5a42003e03400088400d460007440c80741e03d80719000325401c0c9240b81180e0f940c1103014646c22040c800620848140c2c000200c201c2c1d061845510f681001d084290003504d405605070307901d5000b21455400c00c80000c00f002c1310020503a10300f0f1500c126032488091145c0300503800c01510030f80c40d40c2c00d4090700e01000240c2015800103d00d8220903500d0702d001d038000024032421508280506 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 961731897 1250 961730647 961730669
    0x6270303110a0b010e09061b2a0f0c011101020f0405040902190906060f030e1207021f0306150503040c050f030f0303040f140609120706290a0609 64
    0x1800880e201e640700c070120a884008541c40d821443d01c940200c24001da00441000c45204108140b4400c00c1c044250004401182d215190301c0c805c0c03082c45540039403000019000000c000b024801408004510003140c0d50900f580c90044d40c800c1016240c0004000b00c07804600d07244891080302c0b4051003103404084028003030780e0805060800b080041c01c50a042070768083c0d40d20006c005501c90001d90300e8010140000001805460040c0c05000b00c5a01c0310a1018107240103510306203c0000300310101c03c000b022651b90303900d140340d1000400403040000c104d0214481044940c1c04160940e01034015200d080080703131100c151130b440880d0b47e031200301c1d002005017010250811050a00440701c0054500040546403000441c030700e40c600d19082101c042c1c98010551861900340440202290007031f00306000035040302e10b040c0c0700080c0c2d0b4500d8000140d224031000180c100502001e940210310300103c4160702c1c0c0e0400340594281c031083c00000d0b00f6500c11002c0702c80004025000300c048004641d14a151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 961733147 1250 961731897 961731899
    0xb0301030b0703091a010e0604090c1401210506012c120f010f0b090604020915030c070609140f0d0909150906060c05060109051b0304030311130627 65
    0x7859090748018102d581815100c202c5040090010181c3c0c1c003014441502c0712409615011400d10f9244000e0410f90042d481c00d101c000101e68400501001e0715004000d041c5000307a510012601180c0d95004404a4a5501d00d44c40919100f600014015134090344c0d244640943e504050649035150240039404c40311805800199007445520400841050320644000e414500e000c0c41c20f503040000a8502580e9991240c0e61a01d41216040d40042e8140c40840c1841e202c24003040c400070b140401c200900c0c1c3e010000a8004800c0c60840f15050341c01041402040b06ca40342c04066035081000c0d46c0c01500600c0004040c5100000c0c040315a0715030307a603506020038907008810000b0302e007400703100f0300e484811640811070317905500854004041507941c440450965080c20741c02c058041c1c018200b40c03400c000030312509001c0102115400d495802c605583c07903c0b9403070151700824140f2007406c40600041922095003d00d8620030341262031a44680f0085007445905d8813007a007240395111400002c0c00c0b4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 961734397 1250 961733147 961733153
    0x60901030506180702010b010206100e0105060f090303040b09130c140a02030d020a02210313020103110c1e010b010c050601060810091b1e0e0f0a12050c09100b030103 73
    0x40140c200b203010741424890300381c0c1c80b0906a202d8044603441c026039100e41c1c0203405944d040041030b600490000c0501d03411750404021a401038010300c182807042c180803803005420b01d0b003403086403c0c0700d00007821203944503540c204c0c0c84180d40015426074032941504a041442e100319000d005e000c1c02e07003651802c00b0720b00c2c1069044810740001c05d440003103200c140152072084000c3e00c0101103c076050b8005041911a5141480440407030560416103030740c003030051104107524070b024081c00c40e509007000b05480c5d51440101445000b411041151703842805810141610102c804040824400e4001e03c01d0034080c1005460703440a451004019502800040108138450310105d43c2000c120f818001e22550b686040c44151405001c0c0009006482c00c8031280290300101020304086203688480da9a480c1448007400d040308115000c0e0055181c4030100d03c0c0b5543e8080014003401e170811403002c00c1c0980b1304140c0d54500304d2803030150003214807002140c5007600d5200c500d4129400c4014151441e800c0d80c2e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 961735647 1250 961734397 961734401
    0x406060c170a020309040f090b060a0f09021b011524020304093305010215090c010f02031c020d0b0319150b06161104020f0a0c021818061506090103 65
    0x111a04003140003d0200c1d00240d5524040e19030b03002e82c0740001003802c55003030801c40c5c9c18240c06054a8411010300400300b1206888030020700c1151030740c2c030780140c440400d0024001e03582e52060b009209d95103401c010074941480004a030050700c214204070714241020751114840e4544d82036454016a01c10311007004a501c59801c00318110b210050382141c1d03c000b0140003042c000102c1c071400078040503c0300c24062540e0402c214a8003000d5203801d002c603814a90036954481c90104030031410000c0c800725400490340200100d8204c00d10185200c40c004002c142c9600080d080008051441828211106001d240c0000d503002c0403d498409407043d40401e83e208818070703401c0101d032921703e6101c04a103095541c0740400386c030000380d800083c42c540c8542494040f030829081e0854030b20540c03040c062050f00d105a40103603041075030181007880310f4a0640c00084d03842c01000c0c00d052081c452017070800034003030010f0410b65001c9605004840c1c95868018440320049105c060042d00000140f1284410b907200c1c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 961736897 1250 961735647 961735657
    0x3020a020a0b1003050f0d0806041808161509150c05040605032208030a051e060d060e0a0302010207020909010c0c060b1c060e0d050403080a181e050406060c17 70
    0x7002d0703000080c84e5642d6a072820554400101c0340b403031304202c0800088981040d03410358004001c8400b00200510b0301d1020910481a24011740340302030101c1c0070855803162040c1908920b4001d04850b0100410300001009425408022118002007000551420307121b806004140710366030315620308003400c180c1c0445454200030171001100c1110080c000040d0342d01c90380600c4450281460326500d2400f400042d083d980e02604401d100c0c07040b00340c100c1c8095924118035400240448102d0f40111550070420f02820300700a14001d2070140000c09020140c0550040c1481fa102780e6903485d983d0347d00542d1500322a00f031001d580c007040281d04004005040c6078450250010003e06c06590101002442684a00d9001e82212569a43d4400c102d20020401c0709003108551841d1441c9003074219078440e05540180300203201030110814017080324200400241c405000f4400e817980320742115a1f802c02a0950900c0380c0da000b00d151010104600b40300340481d15a150300102041d03e40c4a00d00d41000c581e504c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 961738147 1250 961736897 961736911
    0x807020a0c090209090c09010c030305191a0415060f03020f0c06101a0702061218030d02040609050423070905180103050c040c0807030b0d0602030405030a0e0103020a020a0b 76
    0x40e5404000000e9031079050034024000d00040140c4641d090802d00c5220344014102c0081e40006120300e8005a80c0b00c1d80920345180e0605d80855035890343c0c0c6044001c40500740d4000c0300d4605004480b01c03040c00401c411a1281c104440074440d040b1458080e030030961903401004002405002004003c40c040d400421101c6544400340c0d19054620342c809007401e105850009a10303119030b0b000c00c4a200321040d0b00300080e403402e0540d8031340600c960000381c0d644903903400200e0000c603c100052a2002c45001c01c000d0740401426241c0e0b4400701a0020000e50113801481c02288e0842404500b900b081d101d414241a0100c2040325000704040003160901c0d8001c0c007110810620032000315658030341021108091300301d0641c0e0074580d419807400e9070501c1a6420303c1401189003400c40000e10382e00c40800307504400c1d9410005603007055580810040000308402a1000d8000010300c8100000040101340c0d03c00c45a44e8103811054402c011010313442184042c40059120200c01000701e038004070b2103600008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 961739397 1250 961738147 961738153
    0x60405150f1602031e0a020708071809050102070606030510061203050901120e010e0d110a0c2913210c0902090f041d070f0503030304110d0c080c010207050103020c03030106080702 79
    0x10501d00031180c42c0785401c140c80e039140750125050740f0745a01045900e028011070b9012b8100242052410304508490100f0316810319100c0d03c009090100030360480d003c0940095050120a80b6814410f030307140c030301c401600301d202e280810019524014180207450107906a03229881e2080c0d850044810b07000c4020490079003540c92a1009400000748104c6043c61008009404050550710018084000b54410668180c02c451543c00c005a5400041c03415111044c01c1080c000c0b8010070740078143da859440030001400001422b02c950002d030344809044030400d45554441442d620803030240c0b2588040000d1068a40301c0081c00a02c2642d00540106000136000320000000040050b003659004a1441d08600c0d141214104440081c8081c5002d0805034511300b132040e00d0130012a42ea440005c002821b400e44283e1741040f165a01020f0705055a0411640301140d41c8070001181c46072001c0d821503001d0b2107414000656540623000784c803422240000558116803034002c0943e0303403000090401c01140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 961740647 1250 961739397 961739407
    0x702060114031527072409080601031109062d010e060d230405070303030b01030f1d190b010302090601021914070501031413030e12060405150f160203 66
    0xf60028510511400c2440c0324950601800302c80c408458124286200058011403c10305c242d55001c54050141180c02c0200c17a190f034241030080b94808045d800581a40c01040300010a0089607807560712240000c13100414507466420400180c440c010030001146040c4404c0c00880c48052071207403402c1003047c10504a00a54a800150303941e011040303144a1581e102d199105280d008008070400e803006481220f100d04090f254950f4800c05440028105a02e60003490b003a6442900420b1009180d03c04c140080b44400482c2d051182d29010300c5030141c81803844009051021341e1612004680050000c92a03909540034014203c6004100320305600c20142002e038440000c81c6003480c141d01a6a2021500e44c0703462801342840300c580c0c03040381058140420301c00c070090b60040380c5c3d8110101c10740101c0c10f0241850240c9002c8000400d10b64015030526103d0524940032650500c181c0c818010f8070010110b0700340c1260b00b00380a491a03150010310b9400034012044018031400c030000240100c0e4100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 961741897 1250 961740647 961740673
    0x1706030c0d0f050d11070b070c0e0a090b070e0112020d18030206090c0307050108010e060d17130b25051002070f02090a050714070807020a06030506090c03070206011403 74
    0xc44024030441d4020364640140c400d0100600c80350901c0c0802d4174207000900040d003c010f540740c0c0303140101501c0c030400003406002c00c4054114030008121605010030945401198000109541304064070040d0001002031040c42c03042030000710b840d0050711380c0c440034034115031800000d4002c418030604aa03501c044c1102044842c200303103039105200e50300901c522318212115604107613060420707902990141d001442240c7c2c00c407031400d0540300040d44c00c42c41503503070800058500541c04400b80c80c4a01c001503048903c00840c00800c5850350480101807130b266940d041e01113521888000f100a500d9901c0035031808413040c1074040d089800f84044950401c0d00f4014107040f68000031003200c0410726040e00c0011810901403043d0b000b803407007030100003e03d84844060000c0903c00e07400c00600d02c1c001b404104205000c81a101142d401070300e40e800340342e1030700000350040406903400b600c030f02e600c4030000720211401403c880c8034806070740c003404517646081801044030401001c40b039494024051950341e4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 961743147 1250 961741897 961741909
    0x308090f060c2d0c0f0703030f08040303090209070206160903021f0903080309150114100e01020708031309061a0a030b0414070c06110403050717010e06071e0305071706030c 76
    0x1800452225607103d071040700840c40c1c117140c111304c50310680203d1803c0020a800909407105620b25040460311030b6294070b400c5005000404009500213140c005014404c0ea00007000c6110f81c00d111040820710004203401e40d440708007844025848000c0b0207000b142e103a912403228040254a0800e05911512903881c050160001c071400103082c0e1024507030480340c10380b9001c5a80140b0a402d203030f00c811142c6501146030b1144a251260500058000400c86a4270800011000380384000540381c48100c035249000400c000d6101e00d0f08003e0030001d000c202c00103074403031183d03082c034001c003859160141d030201c00d5002d4104405010740c041d81e140c0740b075540412403440c2e0500c192507030303a55507080340250b242c01340444100700742e12800140288014800a600040c1c408203882e50500c500c8800784010a01a014001c600c2d880c8001340650810702240030740100500001c1c103050300141d00c2c0c80d00400c5049048520440d400000901c03051ba12444002c42d0000d83c60b0011030142c00e881c0c10304400804111 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 961744397 1250 961743147 961743217
    0x4080607020a0203061b18060d0f0e0f0c010f0f051614060f060604030605040503070c030c150f052502030106060e150a08060907020109020306070c0308090f060c 71
    0x3580150a480c81180f0b414009260300405406c00002c0313248071280003280318041c0240100010343c401e5198515907850304c050315204803081c501406064681c84000d070141c2404916500360784100740e2100030f0f126010a030880c1e401010382d228003076840565021a51740440291540c00e0000400c0341c00c11400b192200301c504140901d02c424101290004418079000005000c08a284041400d001080c1d403104100c0f0200d07a0803100c0030880ea2280d00303101d41140300302180107011040e5081d00004000700d178040d0350226444141c2d90010100700bd44151501400d0800031070001e4000c0140000000c2d00c000143c4062504148101a002d220b9021074212a00d5800c100041284c1060300c102525010000c5822080500c414504204201c0000b810401010f8107076441800101c00098201c0d200b584050403054000701141c89905114002400030400d02500b030b40010001c00002d6034045e40002e801150a0b1600000c24080d920159807900680040701140b071715085241c07103014a0320140301c00c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 961745647 1250 961744397 961744411
    0xd030e0307032102160b091503040b010303021209100f021903051305040b060901081f060c020f0f0a3b151c0305070c0306021b01050912031803040806 66
    0x40210740001d41a010544410000001154070086031502101d80d451004d0046030f0f00c801c1c20700e4803070347c141d40003854159108041680d8200080100814800640010750499000343c0075650400300c104210b050910a030403060f5001201c1c582400303103680c4250301d0849118410310644010703a95818011000003107051060f030004130040780e211200704504400c0c03002071100b241c0c108115000316020881034082e04c01400c2c14000904c00042000001d8080302c09800c0c2007142e4150341c152110070141c9500000d0f41c0076400740c01455243e52880c10048040440c1d590b00801d004605071804003249802174290542c11207918540481d40440041c06050007070078140401d90224514005c0c0a044490140e00503180c4141c08480340940c00940c20a41740c0001c1c0c2c0c0501c4c1c0f80d50b0318403441c2402c0440740400d07403001b0700080c4001500d85807400f11104c1540c1059000c0c0090115031101d4001540e1907a1090419650780e400f00080340000c0101138204c00480038103425681071559500c615414000700311110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 961746897 1250 961745647 961745663
    0xb04060e190b060a050d060c050903070801150e3303070f050907030603081905121612150b0c0a05061015080c0702041d06070e0411040509060d030e030703 68
    0x110800820b440d81541c000003e481d031208007441c0400142106040210180c1a6a1340b01c54a0303d41c02e101e581155001140502103400507a91901d145000340150700503ea007951181d030300829516041139074240249040e42076100042c0c4206441d1080084540c1c0c8200003d42203000342020380c90070302144000f400843c85900040e880d2209102e110388000b080241054641101030002854079800ea410a980d115208228508036440554142c4290402d10941589180800c007540c00c10320000c01c54060241d03556800c5100501e01c15080e03035550045411503c1600c1811322000740280050a0b00c60b14800417136040c8010345e22100d04258041e2090000412074144c203000000f601c0040c00d079850058030708202545000641030819000c0e4802c028407030740e190f0b5120428400705100c51a80409480700b51201800d007800081c0507441220310080c0078134100700702462403440c550191360480d40301505811882d9a038400b0000e4a569551080702480b5449416240c5501e0820410740a5803051a031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 961748147 1250 961746897 961746943
    0x9090f02071a070504060804031809050612070303080c0906040504141f0f0e060102030d1a0102100908090409050f150421020a06020309030f0f090405070512040b04060e 74
    0x4910400c003100c42121000903110428400f403079910004441c1150b595160201c00c50f129480e00301d80906c01456000707400303010300e200414006255800180140f204a03030818901411071a03503920707803003c0d11010707001c101108001004244110004e1020200007445189460744a00010b0100c07250040076042c1c0740389080030005a00c40496205d80302142e100d1240908525243c0050640d1030036000700100d00e0b0a14000c5807084c1d008100303903124245091400c2c41901541222081c0d0601c4c020342c0380c1d0051199208e40111070300395208522105400c03442880c94000f4250910021b00b40340c08049544c0d110300d10307003004000b00521080e440892038000003c07003402c15007405094005400c64184613601d201c00d14190560300041d80c10702455111801580300d43d6504d900c1070550041d2803840482c540d00003103081d00818903070020304203200c0c01c603010006600c510781d00302c1d00e070300070003441c04a2a070030040810b02081b01903240d154818071a54000c20200d4641111760309000c0c40c1c0ca0080b42d43c0b4424a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 961749397 1250 961748147 961748153
    0xa120f1b0503180909030307050714030a030b030d05120a020306060c03070f0309090203071d040b04090b01081605030706050d0b10030212091f18020901031a160903060b0109090f0207 80
    0x800801c0710001184d504450f0305020755103584070321001c0c0c101c0b4144800000c4c0041082840356804400003032078001d40381c844803101809406840c1514003640b181c000c0348000040c0c60700807001e403030490041ca6445042030381c460101c0f000a60000d000b541e441102130001d07200c144402c1000705102441303480d0100114440e0b1078060281c1056806c104c4a0034010b00c00c000c45154405e031103446601421020004d0002c03500003007001407504503a0a6005414804840188950400f195040390941d208a50300d64031488030301b4031000d0340c5000e180d030b03d60060001046468401e102514000d250000001280c1d04c040000132641805000c03c80c02282d00854449000f00090032080d40c00b070b0003600a0031268081c00c3c080302c1c405680c4140204803a40d55061001c0d810007000f680311b034141c1e0107440100c0710358490400410305c81d9040018050543c00e040003444d003000b01401019084050344810110034196030b950405130888510f09810800030810000d08006140500c04c0c6414591000603624a2142 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 961750647 1250 961749397 961749427
    0x15061e18051504080d0221160602040b071a071704240b040b040603050c060d1d0a020a21080f22051206131403040312020615030a120f1b0503 62
    0x88600080d90002131003052201001c512103207c43c0d071040c10041d40c40210002c40b5100031340610025207030510200d000f007207a040b20402005118058021038159155542d0340a5030b0942c120388013400900c07003001518100688180903500302c2d2190781d038014813080240c514034005150a004e08501915000840140c0c01c0ca4030070180f070140142c4080c405141142c641c03a6895107400c118a0140c8400030340286100519440b40080c05801286210741c070721b9906c1043d903140340c40b0106902c14030007504001810b003508010305070450f998520281030200d1039100c508040c1c1102c0ca100c0005141001715076100803400c0d164803520b507610a02d15101030309100502100b500f8040540805501040a010051064090100c42c1d41d43c8041e01f180c161f500708d4042030443c05a84e0000704000c0ea4032082200942d004644180f00e00b000d540fa44203410f813a802059aa10340801c40546882c82e0300e0305400149120301c8905444030304600380900300000d08142002210a503039000c0d2196000800c040320840414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 961751897 1250 961750647 961750663
    0x3206031b03041b0803030f07081306090b041e1a0618040f0b150d080f040f091b03020711010806041107030518041506210e0115061e1805150408 63
    0x182000358214640300c1d41ca40715245001d0150300500040500041401a2b41d074206141264003010034441c94489240c1240080d009450484002c5802d1941102122020800889079070308111103a0320000303510020450300c000641110b030000a0310368441c6580002c01a514041e520801a00c0e0481a072810840148040900040403030320054842c00003a075694501002000d8100082e9aa1900154400c15079445a540b04041401c40749000245242c12a403060284e0061204100300f284a4644104c08038030170b0101c01040c0c8220b550540402d54450014603501c118003820008079064501c0d40310545800107a01140015000101c0600c414541a400da410380401c4e02e05101c601400301504600c0c1c111405210200030304400a0b05010800a00c03075005104103210800c02c00c001d544040d80a020f64140020709a00184d50024507640300341c40c03c407010042c403036004415091000c0c048400b030040303181c0d501c16865081d50105540c0d441800d2103014282c414280350744c8a24108005040640d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 961753147 1250 961751897 961751909
    0xe0609060c0c07030b2e03050d050328110d0e0c03070e070507030e21011b081f210201090803030106090311130c093206031b03041b 58
    0x205002a080c0d8000003e081c40a9a40c8000c4848050340c40c0381008040030b0440c0440c0200300ba44038511400d14080001c0a81034a006405555002e01e0101058031603200560b220790480c444160301800c28012008038200d2000032003c00b01e01060380030103003e65900700843c01080070f41c0d10014040301010400100000b41d00a4011344080c62034260801c440c0c00d00244204140440020304104152045030508103117880104130b2841c45101a10003400350004507607810f80c1d98030f8103044003640015088a451103801075511481c03180d40780d07040c800a07400c2201c030340c03030203511100c20210301c4528801c41c4100c02524101040819142c60000400c4c20003a98412078103504104014014294807211000699400103c0110515103540110300c902d160443c1216400e450101c4803022140d018400e54111000c000030035400d40030000c0c4075141040d11441c100b0505600c200b981c03441f410800d002d543d006510200b6080040c00741010b08681c0d500440303044034200503580c2580607640101c4158400745c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 961754397 1250 961753147 961753171
    0x90a0c0e0114040603020f042a020606100305160e0f0402030103060209030601152f0f06010311011d1009030f12021203061c05161e05060a2a02040e060906 68
    0x32441d004036641100b8404441c1c000c27510b9000209010401c100000c40d120a14824841000c4003000020f450b010b0581e0098031850380310401c01c001901c2401051b004142030505032401c10010b504c1a0b80c40e00c0c51003071454110800800402842d91207101071b500950143c00e0169989002c074007094141041608503021040c00520085515a80001a4012100340391801007032503500c1200440c0b07624200e00305003070900c1028010692540d0100c0e01e5412139210740400d254902d540780054407a495114001205071050b45030b04035643c03801e902500c143ca442030500907401c1c2d4480c1c40c3d5204c8224042400d40d0b807041003400e030455507507040250224010015008500b54104100040c011072800034500744068141c00340c5005109061240b4071043c3d180c1c000310120590f40d440c3c40daa400415240048424a181c0d100156a00b081800c03100311100540d158000c4500038002c0030052150030741d052545281450031ba00042c0c549100e02c1281000c07030f2006102503e0f2084c4d54900e020170060081030030300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 961755647 1250 961754397 961754399
    0x90d181a0702040c180b030604020d0c0302090f042f0c0a0804032109120c150e030c0a0501201f09150b0604090f090c060309032312090a0c0e01140406 66
    0x40f0171300495000b035074400c540003952a2510400a00a402904441e0003007d240880d054039054055006190b080e4003902d1100748a80403900300000c58245491464000e440703809070515070005044410074140000091354180580e40d001c02345010580329003144d044c10006018003d001c1c600d8035a4045807400f8000d00501141280010026002d610881c0e581003698080c09041183c80c3c041e103030190440001501c8920702444c40108012440480c050081c018544d602c011400c1c05034500d000e440040c0c59040d000048a954400f80c10038001d003002c46409a00c0e03258a8201080041045000b081d680c080785501040c1800d00107600320841c9442101e02d4402000f000d03860781070a5400710340f04080c0014102c0107a1012070003034035074600003e200b06400e400c04104103402d03920101d00c050003651403644c006000e02034503000e0142c10404502c40481030148021000c00000115072240c0284161110b40e644d59841030351000b1709420100f0a5407040006024441225a00140c1d80e03c0c01c55007440f140d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 961756897 1250 961755647 961755677
    0x703150c0c1106091003061d0f06121203040606170c03280b090a030816050d090c0b0c07050f040b0603131e1118090d181a0702040c 58
    0x181e6081031004240e054200800140340c0c1c0d41c00142c82d940328000d005500e80a203812001402001d480c09507045080011190144001c0c03d4072480c1d115808031141080c090b00ca1808018592a4410703420016125040454041d11442c40203180981d100c2c101c00300d505803e10032040000444807922805660002210300d629603000103d0500506022040d0444002484000d594000c0c1398032020381400c3d80c0c1c84c144980084001501d091450107980c0360603031038560b0799402c03040400c1027010303500150007801500c03825007181d4050710407a4840c845000c1455a90f5084d00c2c0203800c0030b43d80c00c0b0682c00150307080003e1b00b05a19207401c82e80c812541000000100c1300014014000030300101c54071101c0705400d43c10882500e0304103c8590010b6000c00d20042185003a00b900201c07507035894010b0003811300c054400030303400038480d0045ca411405420014515207085070924441404102051614540013601410b41589101c400150b104d01e150385403854010701056403c00002c480401c12220071130006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 961758147 1250 961756897 961756907
    0x90906060d0309080d0e041413240f0b1203130314011503080c0706090b030a050a0b040501060f1707020601121712060f0409080a030b0109080604050703150c 69
    0x404202120301c000c18050906040b02e1040f802c1c1c204062500c950b03203111400c2e540015a5030f080c010116070034401540303007200d060b011180c00d48e200c0d00020200b0170390303100041002c1e100b400210100e01c40c61b10541448604c6800b56031070213003100c030155503a02031414a414480501e8010442d030400540c9040d13001201c0c850392600300e01c40681840810f0807860485182900310034100046c99280c0390249403a41002d8040344e020400340c204601c140540050003074022194a812112001d0a050442c0c0d0741c0b0242d41e02902d40100b0440e05182d44901280c00c650700d900c00d150203460180d85108900300c8184014050714a50040004a00304103810424815070024450303055510302d1400300d55000d030501d4000d03841025899454540b4a001c1040154040c000036800d1180100301c43d101000142c00c0180001c50300690303400307421440200b05418006000343c214400e0143c1c10b16140705015601e4001c80d007800810ba4040310144c1280310300300144070b02c1103000d02c843c92a010040000d04404c94020304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 961759397 1250 961758147 961758151
    0x10e070b0d0f06080a0606080f0f1e15010b04050f18131e0312060618061d1201020a0806030f071202040f0e0d03060f05031203061f051305090906 64
    0x340300c03515101907402c210603e4100c6002010707010100d44004040f0316040019007070901494543c2d10032000d2680507090700103902c040d0342c800031005d00300c4010b0480e01c912401381100380b5880f82c3d00c074214411610308900c0720020300030f00d041c4040a45950030312040201c10703204685100e200e40340719800321a650542c00b40c5c842d001050740300440d1640180385000e441c2e000c0d0400c04001c40200c8681608113250700110f088001c0d003286401006403d4680e403043d075a0084500c5446c000120b601e201b8064a03002e0007040501031002081e0f4203506890b140022070b01c20070004000308594003c9030244005821030400ca4000f1800c80c0a02200d040c4006060340c2c41c4c5181c4145030000c0c51840401003952117507070022082c2501a001400700c03100768922a075645140e0017a050009140c00400a4201604002034085e00c000070013900c5034020a90303040641d034001038480c03907004128482d040005500003510000c00d01a83d201d8686602880100d03c6072941b02d0350005c0e00507071452041116011001ca81d0503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 961760647 1250 961759397 961759417
    0x105040302130f091506050f0616030311130f080709020f03152b020102150c040504050604020405060a02240105090106180f17070803090913030c060903080405010e070b 74
    0x350783c01c0f01024400a0001d0300400b4041011038075002c0210b40c842e410150035180c00741e401d0b620780701c0300302d003840150b1190341c8295107440707100d040c82800248613801504615000e11489410420300220390320050581c2d40c003400003000000c40812515105110000003800406011410b000c46580000d002c1d22000704480c12119003070911890503520078414a03403400084090160f294a000c41030a00303109080d40c241c1c0503100340941c1c1d14840c154256094401c403c0c10816a06180c5031006200c080c041c0980040d9009400b40300124460321124043c05160386964024a8042041000c4030a100e0210102d102d10111400042c000c40d11810801411101c03503142985080f41e51001d605180d1000d42c000d2040d074621a6000200c10790004403c2101c00011030a4a4203150ba07402e801c0e82e030344504003a468000c103180e000a01c60b40340c001c845454031406400c218080090075035808040300d904503070840100d500c0500740030512800340b088510360f0500304000d0203542c3c140181680d083c0a42400d40f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 961761897 1250 961760647 961760651
    0x102122505030903041809110d0206340b0f0106050705190305070f0302010605040c02010203270a0503030f070e0108040302150a02040305010203040f1b1d070905062205010504030213 80
    0x3c00d8a00703408008840040c07034514000442d10811090310301c007070100d8041c00c0d502c140d41c1c141000c180f490003030b08280c02c056000340064a414402400707075000c40c45070003030240c1c1e01d10070340e004200e51043c0148203c00280700d03141040e61407030440c43c402651001a044081005002d0203040006075002644000519419260030b452040d10b02d4119101d20038094010000c5c452000010109601500110181c8078102e40c1407142e02c20b100c030100d080f0f0004554020701c0010145e0406182c1c2e05869011240020000a0b10888d14070303600e44600d1540180c4084444034000410055841c4c1d0200d18480c6098003403a01240d03a0070300d078500030359030300d1031405c8144817202000c0460304e014540c1d81280c00075a8844000d540380e05d064140018007540c07641c41610442e00d4040a01c2c42c1c0c0d8407554440c0c06640c040300352500c0105504071200342500c401044441885402d40001c02c556542401038081c8001400d21071207500c00c101008d2440c403681d58046814000280010f000607035800c10301ca0007020000d000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 961763147 1250 961761897 961761901
    0x80a0b04080d09120e0108010b0c1504050c03150601090506030f0f1f0b071703011508040c051f23180a15081806040305032e08010212250503 62
    0x200070018000320310300411a11304418140f5485810000707551089800341c07a40c100983c1c0c4e0f03071021440c61040742000d6140707403c90480302446001c40c61182c0c1e0818001c00c115118048040d01103450003515880300e000f4101c81804102c0b16607484003150300078000945000e81581428680820b014a0150007060f0300e03110603002808611342c07000e880c0b03003030001d080c4903840103560b07010351441f203034001d1000b6100c2c94a0700543c1c5051000030340840b41240c012806010001130400800c40781e401c00600121007240b441000015250359180f000c0300c4800051100403d8020a03030b8000d09803038115098013043d05c0c40c0c43c080d80c1c03c041135881036900c100143e82d00c01404050f07840000d100e80d10150440e951801040c1340200307600c0c0d07220040c0c5200c1c0840b00c8078174100403002010700c2e0360380d01c040350b009000a40c04c0000412040c681001c03407640c00e090802c800c444400f02c0e084403111003080c1c1c010305084d07940480c3e161080d01521041d150070084002c40025000c07031942142c1001d20503501e0b180140040040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 961764397 1250 961763147 961763167
    0x9280e0c04170c0a2705100602010509150402010507030306120803071b02100f140c0f150906012304050c09010e1f050c03040f272307030603050f0c0109080a0b0408 72
    0x80c0e00403070801c041e01c0c03c00c941e01e89108031900010050151030010740c4bc080000d811180700055404940c8000180b9a981ea652503004550542c0000c00c218100364807080d0004074030f0a0200742810040c42510344d551a454078600040406040640083d6484520030101001d41c490a2541000030340c1c901d80f1480e860b586103821398131200e03480f020012160000884d1110300d04041007000c80e140303074802524041390104d0083e03582c58109903500c403e90f800560042203648522003050300d0100000303c011105194140000701182d004950404403035100250302e007465a8041107441541c01d08440000c140f05902c22072484c009a03182c01481030060014085000000402c243c8000740041d2a090b4170f410b46400401d00318550705140102c042c1d072a04070080160351940907a0010000c0392840081804256200c0242184050480024955113000c0031011a5040c4500243e1807401001401c0e06d800e10300006111803007550140a454228007000344c00a402c0c800d159170000e07006140c840c4c079001004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 961765647 1250 961764397 961764449
    0x50f011d01080a23160203040e150d050f06041103070807050d0525030209010b04080613150624020129010e0a0306050f0c09280e0c04170c0a 62
    0x1140c03034800144c81440c2000c00141265401d442504130b041690a2050b00c0c6000380d80d40c1c003540c000c8103164404800000d40c9207040030b200948201d401070405d03013260015100e0b00d0828481c060050840d800c08010803040c00198000c2c400c1d00c170700640c010034049103000380d02611803a00b4020700f031060303011070321442c2440010040011844c07051550b00310540d0301244144078821180c4005c81c0100302c0c8a0000480725a40c10076076044801c150702a0072160340740021700c0b40032441c042c8111050101160038400c0412103100c0c1c3c10282c4141011074003c40020b0031403004110f40059001c0441e070500302800e9000302e2088000402040894000b035036441040300507100c841e54282042d4200d90b03524000018041150401e0340540d46080e0341510036110004068094842c0011440c2c00031040d049810f80101c481c600154501154904a071701651101c0603050704030400d079021546a00089800d101e02c40500383c00b82244d00b000001800014000008a0481d254038810000502551184000558406 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 961766897 1250 961765647 961765661
    0x60b0c0d03051305060f1b03161101090c0909020109090932010c08150a050f01120b130c02190b06060702040b03010c120c020304030503040e0702031902010501050f011d01080a 77
    0x1c2402c0c0d03409481e05103040088140102c0360281a1100d1601840145000c4802c49000749070440c50580311a00c0109c060300e40c00c040341080c02c5150340c0c52180740d0200d0f4150241c18090b0200080218411002d400010003051141d04a80155071400b540d40e00055922020142180030790a1900ca00310304040c404080c08071201003264044d420030f0401085c0c150300c4403580d44542040e10704442d0303402a80d000e0000649982c081c858000303409403c3c4020960040e00409075134064440c0100e140760403100401c80781140c1d880d15865054031480c607100d44540501c01c280c0128101145001e03629100c2d1100700e00504054071060059800082d440305640701c42c1c00c02029810094000c0c00351445400008140d140660318107441c1c1440c1c2240748041602c080b080724100ca80020003541440d0907c024110203003000381c40002544400c0010180141e112682c205204100c2d400018a543c074007424031a031080e00301c80c11410455100c03002500c400b1900b415198802c1d0a1070b06031110b0f80d6000c00310004000e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 961768147 1250 961766897 961766903
    0x80616140304080304060e0a020a05060f070501090510060608090d14090612150301020f030a1d0d0c061419380a05040e0d03090c030c08010f060b0c0d030513 69
    0x10010400043c440d80b0b02c0214000d5105a104020504003030710801d4407403140280096000c602d6410402c550b1528002038026024a03218052412200755606401c4403c00d45040f00d21343c201100242e8501c403d031050100404080c03d1450180c075103889a640c440c0d070710640003400c1c000075012601c00b00e6200b40c107880300084044d2aa03580d81924450045510000b101e0000c09224559010341c030505041c020b40b9011401d4221590454032180c0703d00b40079044549500c7e61040e0b101c8044d402c2004204241802211203444c1d900b183ca80c05c0c1401ca06480441d40d509200301d20550911050b4024500e1056001400780000542000ca450b40040c1ca840d44200f40c9058220403207445003201c1ea034080e006011801212100780c0340350f031401230100b5182c1c201400c41003504003020104035240690814070601b40304504443d181a00c995806051401682080040707030341d54120000d161090b44290401351540c210110b0a200d03881c004107070f44110681c8001308250711040441e0381103041c51014a0050784c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 961769397 1250 961768147 961768187
    0x6151e05031f060e03011505010507021c0204020304030c0c06090308030a0e16260736020a0801080606010e10030c05190e090a0203010807060c020d0c0905060f040501080616 76
    0x20b60381c43d00404000000300020320079440d040130307800e018140c2c500ca0002c83d01d06850702414134845400700181000440c064683e41d08480c0c0704a1f0042c1c1e10b03031005510580c403c1d1a941e6003ca21401c01070761511071504080d062115900c01400403d4140050343d034400c00d4441c02142808104c0304e8942810190080440800402207001c50307420b01c00707080d589091100011004400c03e11802c5190785060900c5040308a08501045c0503c100707182c2648450030300c0c2220b5085c0b0091100340341e40200e070f21403040c40001400303140060109036000c0c0040c6800507400d1030038800c80042c40703000402c00750003003503402c0c141581d03140c038485043c5c02017055030645d54010b142450410709034203025100c0e04843c00324901c1200c40d14001480e044003842681d068414030001081d8440c01d0590582d03e405201c9426039001c8520b00d00100010151501007002d4030000c0000301c0c090920700c06100481c100d011000d4492803c00c0d005216001c000030301e80e61710405403d501c107401e40441200361906400c0d86440c0360005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 961770647 1250 961769397 961769399
    0x10050c0c0a2306060d03050903122101090b031209010309150203070306080a08070818060c0703140a020f0915131e110a0315170106151e05031f 63
    0x40201c403901001286034884000d80000400c6a0341c3c0c03107400850f8080d5000d188003000501091240b0003420742204041c00f1648061900358245405401065803c03034058184a40645016210f01c0c402e4010b00782c070b00b0b09001100c18440002c2e11070242120420b83c004001c43c5911484e0710942140100070b400409042d02211000d0358940a03500480b51000424200030700014038003000202c5400094204d0800c500784502c550f10b091140d40b02400c0381140369014082810303160340d542e00030128136034180000c01d8914554a014404401650703650340341da410100100025850320070507441c803000b0494071241266a007a41c1d1105545001d101c841e000065401a0307944035401c0d500030040310860005946070241e0000d00c1c6e500342c030904550170308062800c0c00401300d8107000c2d401c503500301c2c2c2c0c01e6118000d400d611001400d4101d1108141da204c169180da20801c900b801c1100e000d20402000e280000c00040c0c0c100100e405203240106000c10020000b0002e003046001c401d00506540403072105200032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 961771897 1250 961770647 961770653
    0x191203020115060905031218121020120a0f0c02060405120415030506030a0615030314130501050d0f0f1d0f07061b06050703051906030510050c0c0a 65
    0xc0c02100358020031a0242c10021803c0e5016080100444200400403c503066070395200c00c3c050307000f041640c0b41715444c220506201390303191240c0000f001e18400003088096241d600c0b2005942c1c010b100ad811411101c0c20440011130b001c03045842864614650341c6454807181030510040c8209180f1080d0b95141c01000403940368082001409075000308202c40398100646129005441148110500e00c0610720072051400d029800895200038003c090b5100c40c02d00e40c071102d09a4244180c2c4060b0665115411300c10980c020004820480c401006c4070300300b400d0205460486200c1d400b44038140300c8040340104a40a20b604001004281c6100502c01020600005000303015810421240420440d04200c03a400c800aa00043c090f1044024420a8608181501e113002d81b50310f04102c000c220301850010640034040e140c011031643d0b4000403103207802c400b140700601d4000340e0a413103a07040050400c040781c000600010402804400090306403103514600c1a5403241100c502c1c007a0040c1d480384014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 961773147 1250 961771897 961771901
    0x30a020c0c100503100e09031b19150c0905030c280306060609050402090307170a051501140a0e010608190509070e0a06120f050102040e0a0c0f0509010e1912030201 72
    0x20f0341740b0500d900380c20340e01e8904c802c4d40c0000440c2d084400394020701c02004240e03000041d0040d08440d007010b843d00c542c11110003100d0181400d40640720b800144003100203200907482140004515072030441103144c10500040e4442030580681032081c42a2101049400c03015100002c40d0401d07214075800c166900e05d880d80c05803040c2c0c8507890104072040070005807800c0ca8000c940c0316006c020701900d4500e06065601184001032036014029218920a0307030f00169081000207070078211b00a5464030f5624041030036180d0508505680c0c080c46220a0410841207070403c024151015400d18841656810120742070181c0028400710209081c001404481e240125480c030558200a0249500750f482d41c8540050b038202d40316043d01441c0c1686050040b0305220001c02516200f00000b61506a0f0349800884021007619094041540c13100c600c45003d8004a200f81010040d041c06400d040301280080c0929034160b82c4140100c180103003c400d4042c2581402c0050681c0d030900d642402000d04000740 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 961774397 1250 961773147 961773151
    0x908070f030e061303030822140316061b020d1d03010207080720060c0705360f0a3e0307020106090b0f0307030f140a030c0318050105030a020c0c100503 67
    0x204a800008c1801800d130f250400500c040d00c03507035210307404005940d40010390310a200400c0039404180800e2680c03400c21246040300500074900407801c1c2c0076a031040807100303800060510942d80032800891701142c1018101710425210154610f82461080210340a031040503070080c541c64000400340e007040329240640c10311100400307030340781072801e440103103d013a00c98100c1e060401d03441a402002903180215401c040c800f19510f030352040c0105030881514050016000d8840140d0100801c2803072410802141d0340442120703801e100390020074007203907020f854010120300a01900d10100d038184031003900c50b80c004051188007079a2450302d00f900a00800d00c82c00380140260401219501c140307004003501110b514020041e0910500e1a55051704c10445004100d946402024413071012010510044091034001d403256441d21500e494014144201d0442407003515012000a01c03003640c0c0710041ea94021141c100050341e03190340d001f00500d01140003140641c410000304044103079903070100c0a14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 961775647 1250 961774397 961774403
    0x31403040803090607020a0305091e040614130903050405150c0d020303061203091c0c09091a0f070806130e070f15090e0c0708090619020d030908070f030e061303 71
    0x680720707211401700701c2c0c0340e90000d44040c000905c00d015500c0d9501e88040d505100300c425800341c2c003d905903000850300b80e03000d03640201c0e05070650701d9103a0010b08103004501040740c11100100500e84481e41c01a00c603001d01e005460240b11150381404c4080b07000030445601810079801c44c2ca82c60300c1000000d589601c1100c005019a11100160f0301c1064000203a0307615500041200c150380030415003010300c4078000c00d42501d491a000500091010300c1e4404c00355110b00a55a4a90300c0b078920303c040f60550005401d02120b11101020404500d0b80203100d540c01c800120b4068036042c20401c0c042010304098203003c84030f40200381c0002100e00d5590310303074000c45140505080751500c811505482c032428070303c0382c8120a0860000140003401d4880284541885404124101001103000c5561038102540080108030207084200125804002481c3c1190341d40c5410f20001a160350f4000050058a078028074900b441c0035941c0405004a04d1880c14900140266071104041c44680052250503c425 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 961776897 1250 961775647 961775653
    0xf060c0b270c1f051804150b0903070b04150c030e1314060a030b01120206120703020904060801110a1101020c01140f25051c020f12011d1303140304080309 68
    0x2c0081100460702545003d04540c403200d0070303c000080000d20486400076455030141e95004255456503210750000060001502ca03183c0b6880e20109041c90119240c01c42c0c501c01c1418030081001504410348200d002c5d055103040c03200385040b841c05440e6480e5283d5101e07070100705c1c1c0040c4d1aa5a00d030360301080c06603880c0a080b418030b4540c0010322205804600000c0c10041c0c0c00e40050040d0811094509415480602020701e080001d8000500001080e52000300181d000100070000c1c0c5428020280988610f2008001e81d04500c07414016512403501c04005101444806084c1201c00390306689104100e04000d01a010030050380c0345400000311002000280c10b9400700c0c0044500106040d010749042c9850420170042c2d80082e581c0d6040341e1500b402070b55142a0b007000a42c164000b9146042e01000002c0e10b50350600c0448840e01c0050300a801c1e404500032200941c110750003060703604040c0e24203018200110900301194079080c0b540003440c2c50b20300041800f040180180045104200038000c2e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 961778147 1250 961776897 961776919
    0x2f0105010b1204032015061011030d0f06030501020c0f0f03033d18060b071104050c0d050708061807140a030f0e010b0306010f060c0b270c 61
    0x640e06403400342014040c81d15041200207800030b070260340300c03559500005500d217103d4010344042c18a003c403540c0711401e03006142014030081c0c2c100070790582000c401a0821002c400c03203001c0415543d0182000a03101d5075214152480306248035800440075582060003590b4825288441300d0395029480b030522040e1241c01c541541c07140c0f0120549010300c0b5402c0c5001240c0846020041d46070b5488840200b81034822022420307420b04514540d00107009114604200c02c2d0100a01000c5450310340c80603521107410810312000882c18000c2c03d12101c3c040354001001d86030b145001540b40207004110f100f06241c00e00b03120080d034124011901ca0241116881d00108221006e0040c400c0c0030703a015004030301442070b200c0c1c013945c051000d0002c805662500091032210f0030004405c0e6038400b802d84081e40d540e4038043e1000c0c00c05100803405492108144012240703891001001052015005031400d29101c1c04039010b2580a03e40d1010501641140352402001038605504d80303d696075000d104484c900d078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 961779397 1250 961778147 961778159
    0xd080c1b0f150c070803310308164d100b060a080604050601031803050d06080606030d0c060b1e03060912090d0501090c150f2a02012f010501 62
    0x304135402d1580c070104490550b01c13050b00320a0911440d0228001d4504a840c8102e07001c080303c0d1800400b82d0080d0f481c03070b00314103042d418841ea08610400071b00820000e0204512001034030010b80c2c03410145440c60000c004210465070241c005d00036030350048800480d5104211042c0060f0189000d0075044003003001d50000c0d4100021840788242060125600701d000507168902603104950008041c1404900c109107660002c07180f890084041b00030070004100703c1c20480d21441504040c140c54002000a400c01200281d59910003400b084104a1f18820b450b080240e260031810712102c01801000000452b0803424243d50500c10401d4007a2013000001102400002007500303440000f20702d164a001e04950a10441c0404408195840d41d290018000084c007850340800042070701c07083c05d8151606902c0014416083d803490300d81000001102124031607043c2d4003034a216285940c440740d800303600d8030069a54240e00039020300c84018500b04072148000340c60042100300205030080000e82e172520 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 961780647 1250 961779397 961779421
    0x30703020109060807120606050c1603170703091a03011d1005011121030402130c050a210504050c01111209060f04121101110d080c1b0f15 61
    0x480040e002400c9500e08011036405408480e030003c0032440c2c404002d121a031000010780e00079621020019100154080f4040d90902040201400c1c5036090010340346903458942400c4130802c610041b88030001821010103000702c412200511070b0400161079900c0b80250360325190024840c025111850a028059a11108007118485e4640b0b100311101c0c0c0303050a004684503000a40e0304852031141c044418807081c0d10b11400003035024200016039036071038103105101c41484030003086500203081103d000c02054102058500041103440c208414184000300d800c1d14540c0c0584050105240038203010a0201c003180b1104095400e8807a141d02d00c08052039603554010101c0c8a451a040c1032004a1942c584503000704140e0144a065600f41610349000106c15261050100c8000400101c03600e0156000b400c00040058140301501c19080103110152000c20018090b000c19140010040c807a094864481d41d440703014072040310004808c1c40300081d62040c3c0300d4412900b114010300040d41c0c82c8440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 961781897 1250 961780647 961780649
    0x1080105100915180f0b1002060105090703062411191103010902090c0c0c0103050108061303020708030703081b070507090207060212160e060a05071106040f03050601140307 76
    0x3540420158500603508006010f512a00180e00591000000d080c1200c44141c408403000746034000b0707599181c145110101c0707841c0c844241c00307a004418042001500443d2581c112102070340c18041030b40d0340180440003400c039600050710301c1605100441d0300c014140d510842020490f240c225202800c3d0100950704c1c420f14405d440c1a4894004410001e03102c2064440702d41000360021031000720b26800140c03201000c88031850140c80100b5000e020340c0717080007000c1402000f800c00700299410600350b15180d0310300414074540c07460038000c0c3c601014400c001d04d10080c03043d8002d036510b4100300e02d00140f0404050f45d00c00004902e8520100305001c8190440d001a94014010404039161a2680002e9007000e0015518aa42400403e501e4111070310070610842164010303506c818800c1d1800350401c03003000003c80c040c003000e104980340c4030b40140072500c007a5000038414180f10b5100d4000364403441550000841044081c07400010003400054060580e51620103070030700a031b03d10081c55a100c101d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 961783147 1250 961781897 961781911
    0x9030606040501050d0201141317212502030f01022107021f0b030304090b0316050604120c0302030114010303091508070503150a080d0e15090603070c140a0b01080105 73
    0x413401032500150701072400c001004060901107410b091a910001400b00384583c00300718034a003242414070200000740030307880141c5070803c0e184140c030f9042c00034019135003302c10500e50880c20a01980501c041160321f003004080d8024103c4100e8588064007602030340240164a10626402e500c00c020700074072020341c5103ea0b0a03a8003c1030990714404040c0707000b0a550b0060541d0650300d10b00000251000d00c0100003078000c4103004944000030b03505244c0b0344451410145108000350703000780030350360b9250125411221054007040b800401801d10303102c00141030703000960540c03030030320380038019003204000e0350482c2e010703841c2c00c801e20350f541f44500159a48000d01000107521440040d0005001d000a903811000c60005c844101110383c0120700300d80e805400014183d4040c2c40c0c0c1d4003c081d80402c101e81d008400b0790340212280010b044040d018011aa915407040601000040a1501c02c41c0100c3c0c0140c0c03c1905038408681403010030b07480301c070000c406889180080c0d00219020005000700327070243c45 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 961784397 1250 961783147 961783159
    0xa09050606120c04080708030406140c0d050c03210a110f030402130e0f010e0d050c031803280629090606130e0f09070506030103080f0d050c0903060604050105 70
    0x20079128140c1c01600082841000c00820311005c681c0140c10460724015225120055a0301e50501402a25410144065411001c0208003100348208089800c142c031426508010b80c41c1e0101c4500141180181e40c000c1e4001c082c0a60307c51201032581c4407950080307003481c5040283c211484540003440c411058403d4101d1000c00204005042250081c0200001002c0000d00c0032101c01a5a00300352400240724066134560f10318072048402030007108400702e481d04205150001d051050bc0e01d90146485c0c040100c0400c08a210082d2424086d055103030528858081c607651408101ca48041200c0c0d10a13540d140c40c116466a00007d016080070352104030010b503041300d4515000b084510ba800606494003c075046c00f010305e410402807040d00203441da0504070503407450300110781d01040f0401484000644d100f16800c000c0c039222001128152500034085607960a02040380c88260301c00c0c043c076524400d1034142001503100081001d00403244c42202a00c43c0c540f200300401040c0c0b070081c007882c1c1d4004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 961785647 1250 961784397 961784407
    0x1e01050f04081e0403080a0e0108070210021806041512060f090c0309020910081506151b0d09030209060406081c020a08041508090307030e04050408070b0c090a09050606 74
    0x34054001a040310814101060000341940d40c0d400410340195200302c035441c2c0041f03514080070b80c124004500080007031820540380d20b44284021342c0c0e088100b0300498016400510031114440044084680d40d07400f524070360f9074981da01d14843c550204100141e0006401150094146641d4000c01017101c2e10761440450440c107101c00076000740a428902d1007403640d1882640016100c100c0308611030b00d5044401c2194611304104942070401488040e09010401001c110f039541cac40501d0f0a10000e8035000c075540360b1440f0310210300c5c400841600c1114600c60040042e90055021400200341c910a44242000303840e02e40038041a00c00c54010000700707801190760310f0240c500d10211680b8040e21481150015881a10742c1740310380d4040c0c0c000d1034a07001490354a08906420202c41504074030103100842c600103c54800801c0418020300c0d1074802c0c1d4444000c2010302200e00309890003075800003e00107160402071414040e660213545081d00404203c000018281420f20610384100b4026188a04e04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 961786897 1250 961785647 961785653
    0x30609070605030636160306051003201204061404150c050708040801060f120b0708250f0807091a07080f030405060a1a240c030a021e01050f04 63
    0x880415003030303942018142000074405c2045190f4150000342c0e07503240d0a0602c0000c62001010416003a01890300f011010031003070320380c8443c2c01c500c4000b80c6000541c003400001e0002a0b0915100001c21110020521101e00c46c20803260314041c92103503070100405a84d940d04880085001c460103003060105008290034060340e40c00010070b1a0591810f0b070b160038403035603612a90b90003039084440c0581d547d04007400680c00c02c0d0218800391a00c0307650700a0040c0c02e581c820b000000001d014104200002c408070b40210701403918403088104141c23698200c5c4100707050003080034104c1150180010b68030000f007030225000d44410070a171402c0712040c10020024017018682070b4480d540481b00d0340410030405064001c500040c42c0910301c1840070b0300307907800d0445103403064407030054200461400c00701c506005a41c40000d00700d020001e07203101c10414091921034034150b0150981400700c1e40030000e030a588207540410060b03c0103500c2034040300e561500012080c00ca5900711458840702190302e0108004c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 961788147 1250 961786897 961786909
    0x30307020127090b0f010804080f07080906180405010609060c080f0d0207050303100923090f1e12072a05030a0b01051309030518130c05090306090706050306 69
    0xb481d900300345108809608206403550304200c41d40031428036544c502c20040145881c1c454211852424601706c5036908068683c1001ca1151405d07014000000046110421407400c06481c28500001c2070315466007078090746024000058000580716911b00400491b0b01303030049458030141e4090750750740940d15030300381e44000990381f004822040540301801001d05802c424001400054410000355031242820400704074848000d070070513810300e410b00c40c14456040d2840c85c0c1c6400f8050b1001c80b504203441d1501c0050402d55040710803900d030f000310b04141911280c44960058900c012104031220301e180700c0e0f00000e150040d071000804980d410171442c140409a540c0c9009440c0940c04c610b1030340d945d00c0e030001e8078008550000b1107a8144050040009141011011104e844010028400803015941c01466842011904040301e40303510348003540350b01c905501c614030485504041001e524003000181c255005034000074070a11495000411051000c00d6810850700d0648519055844031400c000d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 961789397 1250 961788147 961788167
    0x606060c010e0604030504030c0e06030c100309150b2701060c2a091113030b0c070602130e0c07050601061b12030c02100b1302132301020601050d020303070201 70
    0x200d992a980700030032881d828040b55000d58429203c8039980c91543c81d003c130440b00658800340ca2610380e03d00304222500c020a0041c0f42090403102c10080f10703d9458280c000748044c10001d0500c13008980b002100b8941c99010380708031501240d004000100411b00d001d030981d840001d041c0700b80c82e0407004102c202d0040340c00921182c0300380075295000d00c0486518841d000c40d0a100200014103440030800016144140c880b8614080310745443d01740c0c14124038500070305a2100400d80400e000c0002c000300e09010a4a00140e0f100500f0f55840340c04001288000c1d4507401307000080c0d0030440c0883d056100c0c0c0070440701d003641c0c88009001e1756840c141c0706490008840d54656100b13110300c000d400c00242c0e00c03840b1070100c41c0140c138001007002c9070110003480c260b40c1c0b528565109245c44909140d55558008001c040c800707022000d82ea803140900c0d5840f400131140d10450280c584441c6c006e070740d172210710200440f01c0c20a90894040d43e90721010004903412410019416070000c01c0003402551142400764 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 961790647 1250 961789397 961789417
    0x305451503040f15050610090506071407090606020601051e0d03030b01141b070b0307300606051209190305130324050a0c08010506070f0204020f1b0708060606 70
    0xd160501d01d074442e01d034080c90460040c11842d40d030f001001440c1c0f9003003c0d9144501f0f45840d1a1000740c2c2050045034181c41502c2d4081c0c0300d0903030030400c01d401c22000c0007044040d20034804103008550390f441c0060351ba4a030a0044900c104642d04201c80d043c0050f081400044800914068680302c0e02d481c10360082c844120100c1c10815200c00241403ca943c0303000300411603030b88284206019000307403205c2c10040540c01c42407452608006100b809907100c9003014080c0490031050560202c11685081d07800281501550140d00b410f00000700b1342c1d001006448510300381020040280c0d00d800030a910707a041c001100ca40000f031103120601080c8500080c010b1a08001050803842d0344030784402d2007660416004020083c4102500f035a00c08690080700d81210303060100344144808a42d01400c14881400f40318040c2c00089103039070510100e10303c0c04190320b4010300210340c2c610300280c01f00c040794869011804040301d19901040341c040001214411100c0c8100a440300341c945404005683e4080c031810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 961791897 1250 961790647 961790663
    0x3f010e0c010f1b02061c0c3b09010f050901090e070b0f0c060903031e010311060a1709060402010e0303070320010e07090f05071706010309030545150304 67
    0x202c0f006849000041510b110140007881aa544002040301603034425901c44080003054111080505050202c41da24601009110907520900151003020081485516a4828201000040c0c00b051805d0b0303030b1060350f80c140c41403005a83c036036140c00b0507110700425284807079229210401800440c071380070380700c80070400074410b103044444000c040c5041000c0d01c4581c442d4000106022460644400290301c107408854030350304035899500d9032074030b04441da00100d004410004126001c9842400480340b510007020b4000c2460610509003951a9811202203000c603541c0032202c0e01c2e502d0000b098a501079419a070302c3c0c403002e050046401d01c0079031503005800c4543d00d03a010f03541c1400d401d100344d6026012101000403d003004101901c141d820180a0200388200c11052404010515007101d500c04020300f00490000383c0751030200c61340e01c1030501744c10004101114520540907030101360960100050710402c3d81040c1441c441880c100c0040e00d031988030000b1a504980e100c0e48030b020b148d000d03002e81c00c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 961793147 1250 961791897 961791947
    0x6081906030807050729040506161a090c0d050c040b0102010e1b0414040209010311030703171314060a0309020d0f03080a0608030f093f010e0c010f 65
    0x4200031a004074004944ca9082040d06103e848030780400081d9451036007411050f40d4008140f4248640b0590240b01e00600001643c007035110358600860314030a031f0080c070070400e203004141c15840c8104251095591030007a030740094440c3c540841d10b00070305038024014025480c0510104002041d102078520305554031407146d012040f4061000b14280f480000070310604240c8102003008489403c20182049070000d400d02001d0b845566500381900d03800b1103020119800300f0002813400c070341584010081224009105d1058442c030700a4400c49440300b030041c0e0515103035442400c4025540c001180c110906004403000e142c4603070420521103001904881e80c14400d42caa0010400c0c00741d4050380455a90401d005c14002180f16142c002d1200f0400745040444581c18115644182038110303100c0c0d1142c1d00034000c05d2002c54400242c1c940300b50003032198407a4010080181d07158000b4035080c01d518101e055070000c100445c808105010503582e022104400c242c043d42c0030303e00e0141c624041c605001c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 961794397 1250 961793147 961793153
    0x12070b0118231323100e0d0513030b0c04050418050c1003020705030d0603051005100603020c030c0a050f0c011403070503040c0e0106030f0e0c0904020f011101140a0b01090608190603 80
    0x1155540004c0c020084030404880c84840e00d20301a450f070140c802d613604d05004240200c9001c5000c8007a02900d18101d44c1d15940301c610508519100c0d00040d120712400380510106200d0036008004645040d2014013000031444481c1c1c2d0603644014015060b42c200e00300110280c90200000c01d4000341c207085c014104900e5859041c0f954110b480701c8581103640d5202801032200811082000d03005010742840300d40740603413000c4d111969070311910062507004200c0b52010039081c001d5500d20100740041f100510034505010340c0c0c44079a01030002490169601090055204007508075864002d024850b16645801c0780846580d40020802d41c0c420350052004602d014034900118024401540d011130056034404d420022182c84c202c2c0c2100ca54461140041c0c1519210318190f031103034044520000c0402e501c8010b03900162010b080341c45a500e0f05209443e00c19007411124024841c0401c01c00604824038010b44101c00305025440110340d0010004082c425402c806c6140c100c800480440d00c15500d44d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 961795647 1250 961794397 961794413
    0x120e06070803090106030209100807060c031106090d080603010b01050f03040c03020d0c0302210c0f1903140105090a150e0a12080f0a020301050109030f0512070b01182313 75
    0x40c1e1203c02503511860200103502e05810981c0c1c2045034800034801c00b6140c00c0070355580c0c0d000d502c40c0506014405154000741030044d002d05150580d070704140c1d000d501c0c0035050941c95205d8403080d00b02103084900443c90130300341403250b950410811707120341c0d103821410110308109800060040b02c280003021300210050310380c81e14103550f640c4a881c104003401d0461040005401c00400e20090307841c150034a01e0b003c0c02d000144040300d00e6040d582c411075540b0920210b000c039201441f0740032050320b001e00c0c00400c001d0620b00d07070b144810001c00200240d40f03e094845498a04d150006003400d61084103200d1208440d41c06800c081000001302c2e14a1040c60b41c9048124a070498004003007403c4504002180b4103d230100d6a21100700c0500b1860f56040000180c2010440d000180022109071081400c001d4200f010300d80303140c07a185550fa1240b00600e8440b00c200300074028843d5980090b444d005103c100c0380a4140c100d10700c40c071000685100418007a8100c1c2c0e00809540c490121440d207080811145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 961796897 1250 961795647 961795651
    0x80a090c0b030f0601030b09010e04060906110a0210022110091814060c03270709020a0921020607210809070e090307060c050705031321120e06070803 66
    0x400c84460b140e1400c0c0800e000c080c0c60003021303641494148103910741190345120256065030b51440c403180b03068845040c414024410030300300900462610b4101801e41701c120014001c01a079a40c215608658042403c000343d0140c459142d5107041c1c1d848a44101c9803460b001c242d40058100f24406803aaa074a0700c060a84500c804e015645817002607503e01844080c2074000e620800d242c005202c00d040c0050503007142d1100400c5405242072460307584044000c0c03402010300e0031031103000f210307259038031404d14000a43c4803281c0d1101043c02458005080929a01c2c00101d100d40e4250510340e0722601d4080c03020a602503d002c1718640d2103070a60858841120f007048104103150381d9a0981c503d4031003400c514000d5560010001d080d0008100070760540700108681d80a0f0b445031000c04d00c4002c540c1300790707000d0080b0140100305010208504c1a0002802d582c030003128550404081c4101c0c192003004a010b100700320143c4403003003c0d192207851500801c40e0416107200640b42624204c265169101c65801c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 961798147 1250 961796897 961796909
    0x70c0611040905160c1403160c080f06100902090a050402031504051e0c0d09080d09030f0816030b0f0406030b010305120f0a180509070e0103060b0408030a080a090c 72
    0x8003003400d101860742c62003010380c401c1c805088000d40142440000d09a80308000c00100021401c01800c84065411310039200e06503514a00c046d51404103280024030425540070301710092040e060922003007140080c40c035000e000c166004114417810001100081e50112440c15007140d43d00f24001883d40302c03440154450041c814000009210035410070080da40090302da154000315200780a1890742511551540202142211903614072120580d60060820404064505c200c00304048410408a07000502014404c0d0365403a1582d15281e400e40c1c101105440c2c0d901e070000b40b0076004a4403800b80e07200c880b400000614a01c05c403544500000d080e2507442c1c0045a15240c14030041041110070000e049040340046601e509200f6a5100d07000940030f210070440800010451095890500300281c2d0003a0002422040d0b40e13251044000c0c220440786000640024502403001500c0d21180064800f900c0030b1ba00514540b180e01b850448282c4800f400c010010b0784e58001ca074001640da10f03010001800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 961799397 1250 961798147 961798181
    0x1807030b040609051e09150106020f07091401030b0a0b1309030e030309010c0f03050d050a09140c10050a03180506061c0c0e0a0207020909010515150f03070c06 70
    0x211005100a4548542c490b1242504040a00117001800409202d010081c440300940560303d0010362031422403130342e0b8503001030036099002159055000c03171162419030103071084481c000d40e250081d00071a200c0094032055002c1d040014000100c2910402c3d400c840e26100101c0e00c021908001082519000342e41900300e59100403030420982c05c4410081101ea044001c0e50400664000207040a43d030003100070240c403501030201041500950a5900c0081c480e10100014500621580c00901d44013000340d07907118107410b10342c5a4000010710714041d60705c040d16000b600d00e448a41610717286c1044003444280368840760740c40c10b030b82c140411642d04540a140200300508040041c08400090a0811414620800b510b0404581661480c03011a000d05080b00e00513990403c48500031700924500030741c002011010b0042d40703041500401d0140c80e070000480b205180010401c6543c107040041c20303880c4603050049800941c14070018652144c0d081c1441511075202c1d54400084805c080d1602040314 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 961800647 1250 961799397 961799411
    0x3010b0903100c0905040c020610030305090d200a080a031d010e131a06130510120203100510020f0c040c090f08060a06271d1f0e010227180703 63
    0x11416007d0601600c926001820050405400080090300c00e408003074180a400101c941403034980f030717a04d0802d240e004103c440d0142e40c2c1c0740d600480103012100c0144110b0036204027040c103a00208a0039103550340754413021007658080c80c03200802e10310b1841d20f0f414011181c2000603680c461224488000100080c0000c0020800c41e441c0055a554a8035500942090021600071505003090f0801c0c0e071002c443c1801c10010820b81103d500da00b0301840d40c501800030041c440030740e00e81c281000960302c1c1141d86002e07013400090102d0b0f450307100c0403042115500100a4403500c0c01c1c10381c0060f096095916115580300d440307200c0d1020a03102a40308902c0740e070090302000340780581403056002070100d40c0060f09504055981004210301a100300041d01ca0b40d6000c1200c0c01c241c60a642070000b2602c0c0c1c1901d244041c00700e10034141a0324003101000c514205141c6056429040c8211500a00f00c403c210507a014a00081c410059400601d60341188003505140005600114820310403d27013654085000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 961801897 1250 961800647 961800649
    0xc17090402180420120a020d021603020c01020d05040e040515041505060a1203030b04061806060311090916030f0213051305010e010b0705150405060f13020603010b0903100c0905 78
    0x3d42601c0c13507803002c0d03101030344060240070070b50310450ba41e02d03a0f0258440301c00e40328086604002e210740094500228070015010001c000326851351103689000707402790740c01c007511040160f07200c07280701240380b0000b0300410062040102c1e1120480d006070080d012583d840c2c8070080d4410320071206640642d081118400b00901d040e85c94050280d2280741500c0c645845850300165103102102054000c050540701c552016064843ea80120010248007082d1044a920101040300402007801880002800c094401110b19000000ca0b14801d038054440541b0b55510b44070212156026081e90701010745420b80d0204218290025021901c8001341c840441da1801081001c4c4032402601d1702415801e11004208030030000340300ca411943d02c03061250303852100c2c0c0342003400c2803031410802c1a000b01d004240400e1100004100384114441801c8081e80d4070b50030036800c401d94290b03034000d51044040005110714903202004c0c10030304001400b01c604c03007032400c0340301400e4a16290342d11001a00d015002c01003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 961803147 1250 961801897 961801901
    0x902030f0f0c0702060901121b110708190308060325050103050121170f0403060e240103110a0b1206130c1403071809091a01060c170904021804 63
    0x3040000b00001e250201071380c081540da0046001040c140010800c2d5101e007100a90448140945000f081011400c0c0b00140900720754004190f84140e84219000030501c1140000c051052800381e0302004205203003541c040350788040003441d4641500442d1821a10f10082030141980300b03400b805110310781c0741014001411964164448024501046a03030013184100b1706101408540220344404204d84001d500d09642c400e40703480220f40305c0002800400c2c015694001103404c500c00017074540c0300041c291200464031032806030441c0310380007100400020b40c41d0540300e114440c028040320301982c4e48402188098002101c031a1100c6a04410003050307203800b40d14a000008249010000c1c02002c0710000d00403020b8010042d060400040030509903070040d44c1030f000c07881d0014042c00016481d600e580c000307403c00a80840c0d1411611130399183d51112240d119041e900107640c0c41000c500380b070f01d8001c12070402941071040fa0f00c081040d006035440c0c90000342501c2a02080100c0003000c40024401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 961804397 1250 961803147 961803151
    0xe090118140d0f12050c21060405090f1c020c0a0b0c0d03151a090316060210022b2a09080c010806060a090e0412110c06030c0a090902030f0f 62
    0x200700c50180c69443c010742003910308014440c801e10000d25541c840f41108114880c980d5140702d10007080745480e191420101c0f007240316407800c1c4d030f0500c1913450f401a940e9582044240401c203e40000411030307204403018140c00d0207440342d44102d0ba40da50f8240c0108000420541201600b0300c00026000202d140c10000d048201c4030529040015148009030220b44840c3d50050940c014002e40b6410792215910094840ca40300040030b691200311180d245910140d0a842504094080e00c1e50101900e8220b109492004d20f100e940b0038841607040d480000f0741d0420501100c2000d9950032021000c009240c483c2c1c9108070340048110bc1000160009071800c070b20b079444028a64450101c43c846668462002e81d000703501a19201e86400308110140c0320402190802c025000e00d413400c00040c00004184121a0b414588a00000380d031004000303034480124030411600700c5c0c801c0001c6401c10710324800510070400c1c2c3c3d140c00e480311500d0340840000d0364010b445080f03452a80106001c0b51a050100c000d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 961805647 1250 961804397 961804423
    0x24501180b07121706131107060f020a09120b0609180f01060f1e33030603030305070503060102120d0f0501140a05010f0806090a02040b070b220b010e09011814 70
    0x401315181c0540043c0d44110000c4440c40195120031014141604c040160388149510980a01c40d0f03c0e88030701a0002504145005000910f004900240b2248580320032140542c1188480145a0701c001c10300039101c07009482110702c82e0400913034190940040c8081107a00fa0950b0000c82c85c18030745400d0100c4802d03503401100e80814103000144007c820303c0706603400c444020b451840400c04100850701c42a090317103d01042c220b405241d100b1000c0e8564040d000740c910a8404011680310500b00f00c4150000700c4005015a100910b040d070500200341c0903200c00320303040d88049828060804044c1c141c2d60281d200c0011012401100c1c10245000440c54020340801c0c45e08003146541c0b00c200410303191001c0d0400d03020b50241804212010410340499000e0b00410104075603d03041403902d030710541c10440d0885600342d000c43c090760300640b182e030945901680041840c20b0743d0b400c1140c03109003518054001c0303070f1940d40c1d0311841512b94052550310b44014058249114102100d008003030511395060030b21 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 961806897 1250 961805647 961805687
    0x70e0c0a02070311010c0203190314040e04030c1e1a0c0f0a050906070b1509061c030311190f08070513141201024501180b0712 56
    0x1140d0903900242c0b80c01102c0c2c001840d401850359400040c1c0748507407101006501405001141c11114010f5400024101e100c0d544136108901050b0114080b401075010707142e11a250320021502103031040d030301301c0d19081c0600c1c1008800141800c10040b0303c818400100c0d080441e8440d080500036035030051a41c0035074400200c82c42c1c20202d4416541d240b02e80e500c00800d01402040594558440e20709a440155200626038420305202d400b8040c940d1100303940c02d11602d01080068034905109081000c40c0d039a620920403a48201c0d03030198007510034010021b04040c024002000f21030b50180816000000e50746500024002d00d90000b480c3c803600a00c0c00e01409402c22440d5039502514104408a03030301d4024010303c0c03165040000307040700b40300c4000070f19545c0003180381017040c07660007815101d450485d450114181e0b5503000010680c0010b100540c181480c0722184245540a0181000030080c40e02c00080040c3d250b4281c02c3c1d05d500101c000b5202c4c0604050b00f056150780000c0b42140c2c5082c28104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 961808147 1250 961806897 961806907
    0x5040e07021f150509130f030210050103080405030d0f0806130e1e0d020304031e020301140c0c0c0a0e010e0408120112020a140f130e03041502150c2712070e0c 70
    0x34150313030f106c20340e0030003020b66054418031400e240c4240500b02c2003c4069601348441d5940c0e0800020b1b070b0b00680141d0780700703002d080d541c018140e00405403da80502c460b180c0040b43d59a1404019204140300b0ba807144c400d49462181c4407032002071120400302042100d103c502640c80314000d51034070b091a49518150b5008202c24000b00c1c42c10038901100bc0040c0310303840d03031050b041e20204e8050700590b403125413015401001d02141c19500e40180001c1c000314021182544035000070040801228812844034002810043c00940e184481059005024801d001c2c40d0042d51025200300500991100b8401010545c071041140f80c01c0d20000300800480d8151300b03500441c2c10000d40c1002180e40054800c04600f900404041465049100801004c04c15a0b40700d0390b0b100382c0400000340c641c01900041c042c14100c4809030340411622405843c0b481078141c00c008480081009400c407884401c4001e800b10900741e161a0340350021101f010100030003416071a031601c0d41c0844d1401c4080c03e0b104100c0c8007401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 961809397 1250 961808147 961808161
    0x2a010b0a08030d050402010e0301020703030506010212180906010e0d0308011409010b0d050403032c010c11190507051e100f17041b0e0108061605040e07021f150509 72
    0x10503940183d41030040000c140d10349100585400541002450309540081051814150942c0c880c1d4403500d02038080d654900c0000010800c24482e01d14400100e0240e5112482e40d4104120f80c00e03488041070601520340c0c100500080c4401c3c22000b0200c0008510100600c0b0381401350146125080c01901c15003020350524581e16402d004020040a01c039a54800290600d44250410540c1200c09014005c00e2001500307500709001602170b03410655070030030340401102c40c45400d45810840001c00503000456041ea010100c401107030509441a104090010841d6035915141c141071005d0501100d41c848202c005020013914910584414000d0060044091940040f40c64041081c40b59128010755944e2030002c00000e0000000c2079801d4511074081a4040c000901700d044c0c961030300440341283e80b2600401e042d81802c138081000502c06100410000c42c01e001003580002650060700d030b08011030010f8000343c01191042a101c66250000316145808080b0604003a000070b407250720ac1c91406038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 961810647 1250 961809397 961809403
    0x21030b040c0c030c0f020a0b04090e0319230a0507120e060307140409050a020c060906040c3510063503120403020a03030c020c010801090b03032a010b0a08 68
    0x140e40a030134400d45086480820800c0c0380b4000e0040d0303009218012581c0c480d2035030751107a00031b030280c10001d0b0b1a280b0128006c44001050b543c02c000305c0206642400b04e500c204440c0090500100031040e42903080c03511280b030360f420190019100304d5580d20b4030380707800d403c048031250052903d101c01e0082032655031056072a0b440490740e02900609204181c4a41301400c079005204d907030b114410701341c03814090003020540c0390000c0079150348240407504181c9901c0030144d20b540c4261001446000b244401700880011030352289015413418400301202c061091580c150403904140c244815001840412101d010354070403040900585000440320300701042543d0881e010a14600307a00c0901e079800003000d0315003042100c038150801c0b40340d0740321f41c209403034003a50b107500100c1e0850100b428040c1812110340700054085903010141d48403046646400103010042c02c1c82d00e50b464160004000203006080703034648540404c02201c05441c1d80c5030100300d20030708456040211a108000140302002224000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 961811897 1250 961810647 961810667
    0x12130b1612020f040e0114090f01060c0204050403050903150a1b1b0c03050a06051911190201230411040e1209040b120d0f08090d08090a21030b040c 65
    0xa680c00582d64110f42800a00901403540100d11698000b00003007031001c18803155403116101030340d451406403a0703801c4541e081c05003402150001440b00d00000301514040d04102c1e0024000c0c101075203089041c001190520084040301c8030001050002c2c40901d41c82807094042800340e8510060180d0340e404402850418140404090303110020203402c240140405200015030344201216003516003884c10300302038182150103400304100d554003d0f0044220b03000b09001040382001c09850b154451410000d590903910712031381199a00c01c0503840b4040801c1e002900841403100d010720602d8503113850348540c8e14071000315014500b400c45030300340070f00001195104034107442d400d02c1d258803030f000100c0d0040a00780c00c490b40c840300003c1e401c0c40c2c40001047d203070800500c2d81d031000e5685590351400ea0b001c0b5004d4491040c0d950046150070030035481030401079000742d14201035800c0000207850301d035880c003089400f1661550102100509454140c840c582c00700500366024464002800d034060041030072 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 961813147 1250 961811897 961811927
    0x506030d0e0a0b120a0b010c021507061116140c010e1e061306080a06061409031f150611060420040603030207210b01030f050312130b16 60
    0xc0d07403040005598500182e031015203c1c0c40b02180d110b005010102c40d010b041138881a02091401c101c200065125088030600e041e0050519020410703501c03400344065000c40d8007600d44554408881d041d201d0668000d121a49100140c08001c2159007016203030408046101c841c19803144110f0300b22030b60041c00801d202d4004583c603041c2e510344060f10245c8840a6242182c0c000c0c0d00052070fa1100000310305010a0b035605544040942d5501d20890040b9845800748001183e41009041c150090b46001000b140c1e1028003910a60079108024101812455034070000c165101c0c0e50300d1303000c2d0454020681c01000d0380d140000384070b00400d00154403240c0241000e000803103d840d10107d11000c00c004501a2070f0003a000304045962404c0080d1240c055008a440070045005203d6244120715601c901260704641c600040b0b0f440d44c0d45200002c0c52070141180c50307000510002c1207211903031800611a507018103034400c42102c02c0c5405050000000d1002e8640b0903001c0000307962590184400521a117 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 961814397 1250 961813147 961813157
    0x40e01060c05070e07052a120f0d05151008070c0f1415150d020117070309081801020c06070b06091005190f2c150d030f120506030d 58
    0x51642803081c14503032180c02c288000f04211301805410342c0d00c03400402001c07000521020312075201e80002d6150710103407030b404070495001940c6003001e20341c203c00900360011000c00300d03840c0600b01039414099850454103417040440c0364001c0141402c00408415100348245054211803401000241403a606c482e0040c06006c02a02c50508104a119032004440502012140000c01040c000131300210101c84170031400e0079030790030b07440740b0f00308010320600c0c00c0d60585801071045091703081907604d803c008000d0410503489140460209507420004c049070742048550320f030640d940300c001a24103201340b00418002c840801c11f03240850381403903044e500f10008980c100180e807110003034507a8240480d0032490b4001d2040c15960164a410358a20084a02440340d04c055140d864543d1a800c00c0903400102e80030115101d414071050421103029800304d00400702c51541c000d0381010501e11336560404a02040c480050010101c0c1c024081c010502c44130101880355240501c0865259a921854001444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 961815647 1250 961814397 961814417
    0x50d02030a090311060706020c0a020102010f1a090c040e0103120906020c010507111206070507020a0e1e0c0c100b090f0c2b09120801080d08160c050a0b0601110102040e0106 76
    0x9aa03034006c41e0505d0341c00030429074031107035190807590b00c603078030510101d016610b0300e0821071448500b80243c0c0840c1c0440e84646412940c400d00340304180704000e003030940e103501c108004210f00d110440024013940c082e2090f401d83c003d4100000e040300040e80c200c2000d551080d460901140e0f0b000c1c1c22500101d038000b40b002a0b15035a02c01003402e000381040d034510b540c0541420800c4a41c0d000c0058000c950080b2180c1c0042951a00c0c0032102d050140c8003617111004030650408031165916a42c3c1d0004400c000151410301040b41480c104603000c81c1c1130301b1907500d80307010943c0c500d40078034401d402900d0503001a22a0500d03822030b4129205844c1340d20203804d09480340e90105100147c05c03804079406060280030f0f00d465807078003044d0790501084603c003141c11000041209880020728a02690340e58849564035151441c0c41f10000319017681c8901003200030384500000a41c02d1202e101c40c140b00c1d010b211000d0510000251001c861070f546004160704c180030400200081e00d1510341100c4050400758928 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 961816897 1250 961815647 961815649
    0xd0207080c0a0b1006080606030612070308040f1403160e150a030b01030201020601120506040609110409110307092a030b0a0b0304060506010302120f100819050d02030a090311 77
    0x203000309038480c0e026000b168070b46000c1c4070000741002e00c00d5201000b07080e00b0a8031038606172000344040d240c1642000050002882c241802415100344200724000c98401640da543c2c0c0d884141d10541001c01910403600b0100042245507440400b0404114094840058407640c03807024042c00d0711030524100c0700c00012a0030130751030011518003980d001d0807548145840c2d06000c412084c00303100803030051040e2000001c0e4814000400184190322401800366911240c440102420310742205480301d0004580036a03d0355114030580c0c805d584500c0150110140e40020181091032a612070426141007148040c040c0090307091010b1030170710400c0a00c0c5c11404026081b40200250000c1a400404001c408107a0703000c4a07010b18031692140700d060115689020045060b8015525050401c402480100742400e4150b440d583d0b01085003502e03a010307580e89259662400c04401e58003c0d001a00e410100207000c2c1c18804c484c0550620700081d0f19003495144002e010039070354031016090307c060300c0d400802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 961818147 1250 961816897 961816913
    0x315060314040b07052a1212160302040504051510020607020a0303020f09061c05150d020f030109050303070903050606061801110106030501020711040e0f070501030e100e0706091403030d0207 84
    0x40720b59240303240700e41003014100890407006403441c030400511801004034425554201180e8031503454213440d101548a0031030b0340d01e02c02549c8a200091680074003010841d0780baa031240c14420101c41c0b012920380030484080c80340c03caa40d100380d241107400020400960940000f0100c00b110317414680141d40743d60000c0c2c4c904c1540140d506ca2940903200295006079094103104108902d04101e40c200655100d03400300708444040101c14a0f00400d4801460f005450325030352011100b1005000440c2000301a0b880c0c500b07581c011101701d404103000c44000d005114040150f1503100304107843d0f40d403402050420350201010780c13070340d15810402410720849401400390410300066500000075500c481c00c0780f03401c00f24110b403034051a0285280c070341001c3c800c20001880880d0141e1020140c03075190704010045001c1d20010042c2502c81c8100c0d10b81e913880c0c040c4d40c03080001c3e48413990094480d290801c2c90040040e080c951090304561f19144040106980100850708a91140400141d582c0518901003803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 961819397 1250 961818147 961818157
    0x60a210201110604050a14070302100c0501090b04060c1b0f0215070501052503090c03151404050622050c0d0c150305060423220203030301060315060314040b0705 71
    0x100380c001d040c1800104040003980643d014400d105803140e40c0c2107c45583c0d5a030840d440065070180e038510307540c031080c0d016000800401d40510000314014540c2d071034030094048162022900c269542100881c00b980c408480301d4260144c24180b00b1a1400780c0340d14200c1580b10170083e00c600e91103121880704500c100c04613010594050003d000030300e0013151012090744041040d42ca8280300c460444400c030f11034400d8001481d404180408228155102d003001c80030284d01480c1d64580d40c502030f190390710070400301521a910880080042c0d24003055840c820488901c0000400804c4110344e41c001000490750342083c1509440b110f0b00d0300b8581c10141c7e6001a642d00205898510a01e20210180d03d40c0003e40301d10f0042e9021300c01c032030307a00c85600c4071942c10311068510469200040f4100c99502c0da050590584400c81c00301e140e0b409600024110b40c420780c418004030740c0d1820718201c40c07080008564002d119904080100724854800290710100050004050085900c0040c1c0f4190181c800e0350 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 961820647 1250 961819397 961819427
    0x2070b04050d081b0a14060c03330a030f120509030303040816020607320c040f0212010f030b0c0915160605070c06050a1a10030204030f0c0e060a210201 67
    0x74194010b6070402581c0e40e034521806d090030380035290014444044e010f08890042d54880c0ca050700041040c54104003820303000001c070b000441000f01e04102a030340c2488000242d80250100c494030b07129481c1010072110081100020302c4802d000003211075070040b003643c0e23003d50024412a550038000218940d180d2464500951140000c111a0240620712260300342e005030302c0c0e400d40b0700000150820080003e00701c0094500e603101404240301410325410068016050303e0300941020700c070040107444094241c12040c64604541001c0080c02030000310580c1140c5c10b07120311454240e8042c00b01b1503c040408003100f6040001551012195219160703141c4244c10000c104100d0406181c010141c1400d1041951124180302c046500400c081c400c0d0400459007807196100108804184244d000000c00c01c0d0742856403d0100001154030741520b003030070500c20941c580b10705042881c900d00181014111500440c3c0440040c0000b10034080c0c2c01c01e405202424201691407184012925400415195 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 961821897 1250 961820647 961820653
    0x303050309070e0f16030504020619120501031412280c0203010c09080c090f0615040e010f0510030212061e15070302010501122117040302070602070b04050d081b 71
    0x440200900d04e40c6004100d000224646600365140c04c42c190380b03041e01d029501060401100400002c1aa16150440f02c40d041041c891051110b40e901140d500b41c5c401c0e00c1060981000d451062424448002c0306000f40c8101418030500015400c1da125170f461440208103403d420088800303010307000c02c4403000c0d1f00400a220720014210001c00c1c60f400c0e44a401c602d4032903100300307440d6450b0600f42184909101010a1042c2c4d0780c1c0b03410010481800c1044c030035090020800407524044020440b8081c200c0d1400000610340ba010500c0071040f1291000d03000c0510500c042450304030003020031a003180042303036800c1e2680d04101444d079034188455807032035216005040b043ca082d43d081d07000c2c0c0340301c4d406a0020051a83c0c1c0e0101c16800300406100241603280520407842400840c03020b22403108240d2428110198640020040002041c0d030160b0240e880f0b03100030800b09504020703003006000790340c20040c10300c0d181c07802094a82030750310802040d1000c04650b0000105c45100300b010112004421 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 961823147 1250 961821897 961821901
    0x120305180d1103160305120f09030706020109110a0602060a09060b040c020a06110c060f0a060e0903070203101b050d0f140f10050d0b1512070920040303050309070e 72
    0x3058807900c02d0044220f0107400349401070b003140f01c20060388000304c0e500308004d0010028041280200343e070000c6d810b40c0c4035203800d1003024000d48081001700c02901054000260482d141d00b030804180c0c1d0046409403045460460a101c001c1e404a00e032034106084000114000c041c43c41c240b0003404800d44101d811514180c8503010750b0340c0c00600841c4090164400b00503c6061082040380e42c841c440818030300360f0000c03010070480c40c030a50845500000d0014002080358460f05074103400c039006d0300e248c2250b500c0882c0141c194a014040c3d21800b0b02e00e42010000300c0100d842442d02c00800b040c6140500001040d030408012440c0c108800c1e81c07492400811078002c0d04038803081d03010300640c1c070040c1e00782d0b01e603000500d0303204062949025034000030720100150740070b41c0d291452014010300f4480426401d51240c1c086031240b04405000020f064054581582810001c000310303206401c159502c10b80c241c4880f01e03034001c0c00f400c130340039650113140069495540aa0180c9003500c950f0101d0b40b2501c41c441 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 961824397 1250 961823147 961823153
    0x171504150b0f04052b0807110402030103080a0206150a0b090402040806010e090f010b01080f130c060f1215031205041205010603060c02030a08060f040f0504060e060f01120305180d 79
    0x1c0100141c0300d04880400703185a180c484030355441c007008103008038a05c1821922004c181c00c0c6010300308091040740f0316000c480071400890b050740c2003a0300c111011040843c01075035098040c021198868844201088024203503000181e580340c080c402c0d61260030303000034070800c2074071103804840c003502d58403044801c0e9594a01c00d0040c0400102ca40310098010b01006010161043c0291200b03a46d050755000182c0d150703036003078207441480a054000c2d21307030911f040200029040042ca800800c050340b80c0d2561806603440203070004202e4003170040e141c1d240016034a0301004003e4080256508444500100308244506441e24810794018a0070031848009090410405403c03150580303100710400c4c403130542400c0050f40d60b170107140e0268000c10a00c40019a5504019000352550040144040707810701045183c002100c1056401f0b5407600d4448150640050042204c01d03084180007501454039072511003940030003a030780203005003004000900020000c04411801c2c10740d4100501003840300c0701c286 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 961825647 1250 961824397 961824427
    0x90e03090415060807050a020c010f12290303042d121506090203074811121024080607030c0503010501020c06070204090c0e07171504150b 61
    0x203c141c2c00002c3c0c0032800500da26110300300b56601c6056a0b0000d10f0091000001902d100c0d03028403d900400c9039000b115a00e031050390041d0241d62002d4012a1000c01490747c1c506030400032010103e00070303403040208105010f14400d00c1020025104904200d074031030b464007421400b0306944000ca4640c00000903000703005440710b02000503006d600040006960742c0c0109001da000444401d40418a00320800188448401040e0080c0f48108081d60a0552001c682d580c40d03040041e90301207845c0014040c00c01c21204100e100350004c821a1034810308040c110760140e070707001c2104100643d00d403954044906c0c07190b203012080c421030160603810611a10340d25041c4d81d07464101d4000000a040c01030320300340c0c01e000b041100c2c180c07031040e4040e24001400c83d051209580c01094101d81169650700c481000c2480d120f00c5c903020386822080880c850501010081c0010125158544100e080c4405d0081140908514058800c415180030980c1101500040c2c0700d5a0280e2044206007000100242500160 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 961826897 1250 961825647 961825649
    0xe010c140307050d12090b0103020f040e0d050901030e061308130509240d08030106111005010603020c0d0215040210020a1506080f1c1b06020c15070c020307090e03090415 75
    0x1c2e505d21491482d4041c680003038030314641010b412003080c04010710240c180043e07a9083c0c01800380c004100300d4a0904900d03d80124500e03400006100410501221341e0705001d03a0300ca01c2501802400c560600d40156201c000c04d02e18020268100045c0400c44601c401a51400504000309002d0103031801d80b0300b806028805c0b100c090054044550810140c0c40c09070303800490b00f03401003183e500b141e0825000ba109000c441b000e4500c1c62040c1c450180f0218854000e8a02078505560b015880301e402242d07142c41c01200314081e40c213640000e440a200a5024a812681700360110307900440d40c101400241e04113190410040c000600201c442c2c07100c5071082c1c000104482a5a08540c02c0c41400f000d8142c9841c1d003c40040c5100b8074034042c0c0c8113034a2041d0314001003440180c80c035103030340f00c020340d29001242d200e2800325510790005100f040d0118038200c0042d6020708542005503034800b45900080d150f182c54042c240d24180c3e9218491080360042050320310240c0064010003450215500b0300a032000c40d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 961828147 1250 961826897 961826923
    0xb0106090e0619060f02010b120a232a040f09020901090e060a0e0111030f071b03050a18120b3c040302030d060e090609030a0e010c14030705 62
    0x20391002c12841c1c00d00108078203441c1c2850182480c41802c00748200c880c24600c8241404541d25490070741c0f0070303980700c00c2083e03100380b40d5030001c05040c00705240150350440c0b8030281144031100410117649030140440c814003d410b80c041c8004100c01076001a2110400b0a009540c0161801d080c11001d0001d81d40300d4010180201c50040103a03036509409411703200da41101402c607401500200b51107030125007006a040c2031140002c80c0704038110314900c06a410407100c4010142696041c840020f0700001804a00c140c0d038944104112401d850103001440750345522000c2001a11340b10380f000a280d100c0c08007814010490001460380c034144010528010b0b10b01c0d81c4004582d0551810342030800310b502d440103981907046c03015070b58448032201e21108005c0003681580010411000301000521402002c0c0086454014103404c0401c003252405400501e20255a4401c0281d12001364024250a07107180d401d1030000b000081c145056a0740082d1203901d902644008901501000008614440b002c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 961829397 1250 961828147 961828169
    0x3050a1506020c040207020a0e0705031609060819060503100906060902030f28020f07030e0a030b1f120b090d170601120905100b1819090c030b010609 66
    0x38245200d5803080403030300c40c1d140540c0c044104240903040c9034000c0c0074030f01c2c00103181c2006c0566030020496118030807114140001d000008010020350a05034242c2e00d400b01d4038183d0401c6060510240c8a00c1002c0c0c6480d0030895450b0b48400700c00841c0c0c008101901e00030b41a161400b001a51040c054100c0c0841212505c2c01e022010035015400e1003903a10600b0b414090290a49400919640900025040c42e80e001000c00c00c408000007240010407200002c0803196035144518103004040d00b0401400c3c52140d800700c601000412050340515030001062002c2c01d14504545e07a0301100444107131720036004e400000c0070b850140002405001e2080c1c07005030560700301d40003408044800c0c400200c0720880607291000861650b5101c0d042c840350f10032501c2000203d0078031a45a1074034040303071004161100c40c0c0b04d02c201c100c6414103101540c10700400300005201424041c2a004072885440c40441c0000c2c3d03240070310410310030700461280045070008d081c40340d9540c607804000e10b4400e2038000e51541380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 961830647 1250 961829397 961829411
    0xc1b0e0703060e09071a0c030f04180504170a020123040302010507020d12021c1802040b01020a050c090402030705090103030305090c0109050f15040f230118151e03050a 74
    0x81c0d4a6603a03d8030880482001e05280d60030f246031032180710030f480031014181c0c0c014030400791802000c1008241003101441c0864482e840c103444100d50351140300031305d0011402d040038040007132592240c0c840b4500200c0e0195484000f0048200e00400d05d02084003010200c504000254048014203640102c0c080d90090295664000b0705a0fa40e0380b0401c2c0036000584041529202100540d0241151200c6004d01e1103160b680d0410000555080040360080c1140f001000c0e411460144502e04c101a420b001a0429500c2d5403101600e840e03444102c94004d1040314005011550140101030281400501000455869040040080004840c4480544100d407001c002560103110000203e0704000c0c8003182081c0c064040c890f400403401401c5610441c00e0201066400746001120042e04030410301002d820b00583d07030241c05085240c0c0700c40c1070000040e0710203401140031202e542507910704207c0003110340c0d104008894090360704101340560050080380d69039090703060b00001d015900c01101406a0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 961831897 1250 961830647 961830659
    0x706090c0602010513030302211f08011e05100902030c040303080903070b07270612050604150620031306020c03010c210608010213061803120c1b0e070306 68
    0x13260183c0d10942c2d400c02c008203c0b40007034172940042145501005607603101c90b03540d5403845101e050903a6900350314000900103928501c11004090003e0400300000c3c00307807400312194003284100610724095555210000601540700c1086a00300500710004110741e00e150420071304580b500140422400105480b003ca1561140082a00e010301d400625845450b02c0307000050340e5040c03030800421401034620b03414281020000344140010010342d10380105080036510078401705d50005100398403452812900e01d0005c0a01011034050700d02c24141800c0c034080420250750124000b0603c00c200d8031001036030007264102d00c4039030700440c0d0f4030340c003203541440c1000105800c1e91032541b03607840042e1a02100c080990400c44202952a441110009a058603484036609a038094103245400c141c03114001c105a40e800126880c0c8455802c3d1840c41090442d5107800d0003a454081b03101c2081816071740882406480c201c0528604101c50500d205241d98030200011b1040484284010a140c80d40020305 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 961833147 1250 961831897 961831901
    0x44070315020306032a01030203070e1201150b190c230c010801090506032503052401080a031707112a01030e0616020f030c0c03070b0906070213110706090c060201 71
    0x1851440c040d81740042d40d50303000110000d402c0240840c040100d140031756440c58450241024480e0809400070030762207284401c441901c030803a400500c0442e02002402410b9600f100d032041e01002e81c0ca842140070110303042c4145111311692005039a42e800a000c84180000000c011301501c0080c2c82d41710361a0307030f50300c98802200c404884036030b0150003500c2d01c40c60721a0b002c0c5200551017106090398106988035240e9a10301400c450702d000c002003031142040d41d040c8032490454010881d51009114024196a0051a01200c14010417080d003880b408503500c00e002d10b4a4147c07d156a004980160740038a049050040d8040704030507000380d920640300d5042d4801d01a0b0403800000b900240070b42d0300c80c41e146480681036419a036086004001190762016000d00080140d030204000801c5c504001804040c10702e15194804c00c0707010020495004191500400e81d0300041e01240d0710321b4440003504034440a0465420201c0000074005102d0082000c1c1c0d078481040345e4000d8840c065001c3c1c480c07006900b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 961834397 1250 961833147 961833193
    0x40b0d020f040c020111311206020307020c0402070b041716020f0d121d030123070207210b1f0e091005040c4407031502030603 56
    0x90007005821181c401802d16401c500c0c5400c1c0c8030303c000a090100041c9040858000180788407030b1241c40c0313007400191022203083c039410352090491800740c64030302081507060030700d90440181642d40101c0001c8209001b071120380d0280ea000b910070b40d59006245003800d03201d5030032a02101c05102c200740000200c80d4201c2501c00c0003540c000c0700d180e10962a000c003c103201c50b00683d1a8400e01b51141035001403e400d010f41560f900545a032080a04070184000d44a690b120159000b80c1c03410310441c44070f918201000c01d100366004560340b0141c407070400403400d043d9030b500064982c0040c1d629201380c56000f01d454185d62400707001844081e0312030f0120703004603a040020400c801c14116409100411520701144c1d0441c1e1100121a400c0041910007001d0f500704440c1942e001403d8801003256094070301c00e041c0001c0f14140388bd00c01d19000082d003000c0c03a5240300c1e00048007400003a00d0070707564810040c80010755003200501d840219003201d1480039502c2180c800d030080c02801c071052001d40c11040a11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 961835647 1250 961834397 961834399
    0x50a0606050a0c29040b15062b0507080709050a181104030b0703020301050108060111061504020f040b220b120c1b0109060e0f0a062f0702040b0d02 65
    0x94640091504100d414100f200010381e00a0030b405601912810030b4010303600103002c103000301c0300f0b540b074142040c0c804094014140714036055009840c080c40e40c2c2c0c007800c031079290b81c9044c1d440e0701112210018035048401c3c030041d00d91951a01c4184600340d50007031203061117042c040c0d41c2e00719095141d00504c00449094441c040700c02d90382800740c0658100c00e400000206003001d14943c01e10790342c0e031109000840195042c0011070707030000050100d03584c81000160300c6403003824003803032400c03031036843e9641c0b408018800815508801c0c003440d016511501140c9440c891491010349440d202d441410556120340c0211840071a4962400d104d0055800350200303d441402c0a9410041050b20898000c4002402c480d1886010400c0a0002c989460300b405150700072400000c01c10300d1440c00c8812a45140100d00040c3d10607a4809000180000c000d404158880804689042d8000842244022806601440b5085100f21040708001c01c40640740c0c49008071005c1c8081990b003000d0020b40140f030200a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 961836897 1250 961835647 961835657
    0x70b04120e090c0f28081308070209040302030f0c010b0310050124120f141005060711030c0d0f03021501050609040c0e09180c060309030909040f0b04120201050a0606 73
    0x2039030f40c0c50241e0242000007040943d045c9000080800856214180c0003529420310f618091030802981c018101c1d64000002030011a9140494507001c1103400388490080c1700b0104040041d04043c42071003a0b034090010781c6c00440c1c480249030440d50192004207412030080c45031804405042c5a6401464121413512102e0015100e00b07110400d00250b42403e04c506100b0040e088030554541031103241441004440700060b000c008103155803440f140903000c1500b807500f248041c000d6949400485281c0e41c2c0c4170042e03801c0558114040f0341825807a14503039501000000c44141171010ba6042e81c00c009101e0390a842003070440c0001c0070420002030181c20b07000344040c40b0403842e82c01d00d90301480081030b50307092102a50820600284050b002100c4441e21b42d40100070340303049200e00704442c660b0008201c65850030f524007611203c0d660300840310340c184103140e001e0125051000d144515112140c00c480c604440385040e0138401081241c0b40f400c800190710705030000340b100b10785200b0001654566655 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 961838147 1250 961836897 961836901
    0x160e07031d1020070f0809150901180602033a1b020601080706080c43080304061e3209070605030c04083414040f11070b04120e09 57
    0x100402000000001c1b64125030401156105a0700c2400342d040c090304180e00d10341d6070302c00f001c00180840f0042e9031000c44001d00c441c3c1031200700c0d00803090304e441701000780c4549000c0c122001080e80f07c009010303800140d2080401d400c0c40c801c0003a0404948203019a4028468100799002242d6980f400d1041855982001000340102482a0320041e00700781c00455590401340000c0001088070b40ba5098035804051844040b00c2c442c28454210700c8000c49800b8400303000c3c1d40c0b501c0702030480c400180300806a07982c5a12480402500450b01c0d1342c2e03141405000c011428100000507007841c01c00c2e180490404405031a1000410b90710710103846440d0030000380160600d46034080d5444c3d00060083c0600e20707800c1c400420540010809428641d0550030038050031f11400070454100b0b0391092140300010400d8205104a5074024100d8111500595001901010070940d00b4010111003018405885e400500c203c02d0100c011280c41c007503070050030021000b401c0ba01080e1812155000c01941189072100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 961839397 1250 961838147 961838153
    0x30e15030703054303020703080a0207020a0b070506190207030e010309060e0d020a060e0106060519031803030b0906010e031522030908060702160e07031d102007 71
    0x1180c0d4100705044d25000c00a440801031600110000107415540c40110010f08034981c01481c2100c2c08040d03a0600f14075200740c40d20004c140c19401070a5005441d000165030045460703515001004240c8003401ca5140c415034076000ba1507510950386802c8140c22001d007a244444140308852640d135068441c800c0c4107802c10010b5001e40f041c03a9003910b41d40e94510211079203903010301001074540029030290141da6403600d4001d04039004046a0045a0325016040c800a41c01a00301d5a801c0c00e044551642d0740da40310800c801400880c80040440d0405803200000c25030036412859050700200c4049100307a455400445450300c1405030280d240e807003900792a0441410038456500f164102c8041c0d484106c011102800700444c0031011400184821410810548244002504180f242c405404818180f45402c01d40c90701e24058201c1c0c0446041c0455035080c081c0e80911490401c0003950064800034092041d1100b6080200d5600c580c2060203d22100c1046071600130142e40480c282c41c1002c107030362 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 961840647 1250 961839397 961839401
    0x30a12231201210623150d02150c151e09031b03130303020a0c0906080624100203040f12081207110a0b0a2414010302040f030f030e15030703 62
    0x14040c40f152401c0483d11501007510381c01141d40944564910149040d010300900340c0501000b8001d01c01c1214005030301009a407005451170002d6011159a0361228060030000014400d11101200c144212004102d9080443d4809849800031003c1c513029a280002501c3e0083c03421034201d01c1310780041195580b10070401416000c810004011282028040b04441110b51800e0f001980560300807200c0200b00001604440050b00d4071741400e100d10307854587c0d100d544810207801281c41d0811b808003014820501d02901da40000700401c4844200d4039800080c0d00c95226005e2100170380001c03140400c2050740080c803091017503031004141e031900c09008a82855140c0180200e130400c0f2110b0506004580b0800c0610b0400b030003506507203c2401c0a1100404455903240700c41c0c10b01c1003620f000600d40a000036100c040324481c19000400c0402440100c000744101c0d04440d00c0c1405210303011081c400384a80c8403a2152094a81c15242d084403001c0002d9a181500500140001000000e115520136 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 961841897 1250 961840647 961840679
    0x5120f1507030e061003140d0e0906010c0b040c060f02010605030307110103020408100515090403080a1a120a060b030319030207060902040e030a09270506030a12231201 74
    0x203440c0000f42e104200c0707a41800d0600c1038500c80c000d034040720001d00602c503030f0000d5002c403200500004c0102254080001e45004200641e4504c81c01c4070400043d0103901030728020f01449d074001c1500302186010b15040c90904a2800342e4400035030301503245141540148030b175a0907550300400031420003829913503d40003900f8040384030b07042640a000010b42c079002003040a103450a96030001c5218601625602d0908115110300340c03003a081c9506100c04260800c00c0141c001580d00000315030600c916190340b4284541e4040303280c0205056410700020f400118000c500603105110a00c001c076508010103581e07004182e40d04107808081e80703a0101541c000d034002d00115100704030110306030900c0d40015040f82c2500c00741b1681500000384940c40b140d440000600640800102c0e60000c00343c140c1c90301e4800c030118107040720941c0e072035003c070341c3ca0b507410400305102541c040441d5581d804450402042040d43c800044410704419a28542103004201522040c11a00482c2c0c1400c0c0e2809480d91624011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 961843147 1250 961841897 961841911
    0xe040f0602030709080f030f120a0b0603090a0b24130b0301050c07020405100b09040e0102390703050a030e040207050f0c190305030a05211005120f15 66
    0x20400080068154005144035100b50b8407100c001602e402c075498200800c2c0c103d0140c081d00104207615400088100380c460401d10403011204668a07a082d0300c00401d4130525443d84203001000b04200c90741c0c00a5048055446106c40c4560f544842c031502c0c150183c64495000c201070580c000041904080781510441086c11901050021042d80402d007181c0054490b262481030001344230044d42054003540d9086030752418154115443e1a080c2c058074060825014400c0f900c0e0f0364550890320094040d6090041e01d00058192200f044004520600310186030960381c0c449002e00c1c6110000105241088940010243c080e42c5032503078044580e2008030640300d034030550900225011540800000800000c07040007048403201403410040000e0300b0f40610744036400d019a050000401c04001c0d0f40011640d402d2541d1038030441a00100c8003481c003400d8100d40c81c00041000003100c40c3e070141c0d004540007604e40c6103904c0f83c09201c150315400c1083e0340041d0750380105e29285002450482c06544410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 961844397 1250 961843147 961843163
    0xb13090f030e0102070918061d06152206080f0a080f0d14040302060108060105030a020a0e0a0207080304080d18020102030307110c030709020301050a0b040f12020a030605131202070f0e04 82
    0x5155546c06048540f140003901901c2828042d813400c100d190711484980e100441500c01c05600c06400ca07598900c001820090f03804102103210295480d03c000443d40030702186a8030018606084102c2c0081c1824850404035110340d000c500384010020413a5170549410014840c070b0014007021071041c0e81d00c880e0744251059036814511031004a4290024011271003031380500042d5150851040c605403060300404d200f500000701010060340c0743c000000c04c4601e408115101c1380d5403031714004001e0180b03a50242c8910800402c00040100c12001045243c10030841008188081244015408500000240940d0080021880c8540209041c2c094502018111070303548041d44c0101c1d00f0125180c4c46210815004001403099141c81c103443c001a020003c42d103400c040c0340c80240c2140e07500501c188140040b1a03044442503461301d10a100103103401c000c05001c541000c98100f03d540b10070304802d480b280c000c40b0081c21a248007140360000c0390000b0700b00c100304505105800c4900900030b40111440c80e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 961845647 1250 961844397 961844399
    0x307060e062506020a0341041407032303070209130203070b0a030207030e0910060503090c1905100c050726060f0708090d090909020409020a090b13090f030e010207 72
    0x203503d03030000b07003840140c5a030007203031100e10282c0c03040c1701c0740e928820f4000300041039050a82090084242c044d54070560501c0b0a015200c9007403034201a0340840da00552400b9030500401880f03514030070035804101440c14000d26003504841145c59000f9034000944c07181c01c00c00403441040311640c080ea5242e000138141e4502982e04d100c050002e6000580c00d50119801240010515800400710714400d04203071441c04951421620744150079000e8001d400601c0380100100381490740c1008039582401c0e003d880002030300307010b009103644e01d44640300d00307445030500081d2284003d220344541e074440d03648000108100d90800f0403104032100030314201034807117801d02d100c50b46100e0f040000d5802040082c8210401d4140700b00700414061000b091140307603900c8041d14800c21584403445108480d00300b000024803101610005d0064062000040e5000c59150700c0440c1100c103950207002d1400c404c81d121182081018883c0d02511107442002d000703461502d03018004640619480780d514003051058035060707 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 961846897 1250 961845647 961845653
    0x60123040c110f03122e030c03060c0c11040509031303080a170405250b0d140112051b040207020a091a01170712060902180307060e0625 60
    0x3100304000440010303001190041001400f440903c254007000c0000e1031900d000340502500b05400548050b1000d1900090850300c515a00e0440c0d01c843c2c00901d010000556a00b80004032a4007400107807102454200d180f80118003c296401865130b00140d90091405590100802400020042541c60004104903c6462500c94407100a54860240e40d5220855050000c001d5071502110740b45820301c650502000c40c00016408110030100d10412001c501540308148108440e42d1007440504804a40005c0340d408540002c4240e0304e2000c2c040640c3d030b0740c511f4820002400484007400310342040141d0915003c40161214200307002a01c050b00e400140d5011822490050380140e42056442214104540c52240d80e007010007403d284c0100c1c01c88009480c0c0020401c00303490032060040c540c1001c8069600c6411035401845d18880031515240b413541d0030f01400055402c42442030258020100707030340b40100201d20301140040c240d642000f010019102c00940703451a46240788072041010000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 961848147 1250 961846897 961846901
    0x708160909020703030222180e1f0203070f05031e0c160506011a0f04050f042901091a0301361406090f150a1d160203090306012304 58
    0x3075241300355001a030b640040480e22076410800b01078901302c245007000410607540c1050004205e030603030000c00101c00c0c41c0c1c0000546481444440b250001040c400d401110200c5503000d10301c0703119203840e213141c0d86040341c004440d02d110440d0b41401d0102e00041c3d05909a400458040e8423003401c40e403481c80c0c81c10f920f01c0010850703038010044400e54800340060000e0065250501540d420327140308541400d50304400d041c914000c0d40500da001d168030f1000e030b210554481d0003094015000b2400d00b03c1705058040c401108000480d041804549a440f0020f142400a20380d4800005240c0c441400d603401c140e046100d000c2d2410450354071443c100103d038440c0c200111b040e80752501c002000103044400b4048545146001031034a44156048020014403103040309006034003070204a00a00b4103c00e20001500314400d50704565034002c0014038000010032000a954015804406c00450b030001e0001c1c104d9891058034003064054105000400078106948888030b503c40071881001100d48848001c201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 961849397 1250 961848147 961848157
    0xc02120c0d09060e03030405060906070b0a15050603060901030318030b0f0a0b06071a220b0a0e0d09050904020109090c030507030606051213050109120c031205070816090902 76
    0x44a40150001d018050381259030540101114280011201e81c4180007940324001c0f441418000e0b0700002d4401410342d15042252042a8002c40001141c14802003c400402c0032000000502e24400c0300411185040403e036882044010405900baa0079a0780c1101c1c105021041059402ca00a0002c0005115030f00518030551601d00304400c01d181c551103000035100160001c0d80039480070400840440d8444040c0f1984c640a8950600316071035282c5903002c1200341580094803081101505020007041006003130084840c6901030008605104100e0303214410f004441010440c40311081115041400d011644240141824488143d0b65841d00341624a8000c200000a948500300078106800d03100b00e034080c7c030300c52a00b00d04001c41408002441c01e400313480381401d41c0045014504004094000c44d4a00b07500600d8010740c070048140140000c842d0b03820482c042000e85040030711554040c459a403142c0d40c10f90b900702c8a0348444040c550044070726400c01040002c6402c010074400c000d400101 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 961850647 1250 961849397 961849417
    0x41d01050a14070c1b08150f010b0c15040305090a080c030f010c02030f07050106170d03060b0304030e0f040902090126010b060703110309030d0801080d020105010602030a030c0212 79
    0x2261510781030500d40708403440b4002d003414420090080c42034280d40165080451a071180b05407540c07041c40710100c001307100c0c00d41c0a0f4089118900002d2062014840014051440751200c01c9540c0d8071026001143d011b5000259200d030710040c0151000310300c01136100d13085400790518625055462000c2101c00303000350402d1982e0360003400c0c1210390b8282004000b103c250614000c028245118100940300d1040d014000c40c0c582010a0b031200b406020743c040c030020810250300d681d451000701c02950301d5010040901c004607190032030010344070107402c040f2440790307505903035950540640000300908580202c09864105603a41b1030080141c031001300107070190030428040c000804000c041d59071040c1241c20019881d90400451401c10b4582000707481904d0307803501300700c0411300c0d94021385d52441c01501c04195140c45802121164280c104c14064142d80643c0c003980e04003001030300180e00380c03682842a000103902c10000e15007494420303409200c0350440c902c1074031040c0f188091b103800c058011020f00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 961851897 1250 961850647 961850651
    0x14060a14130b06190206060315070f090f06020c030706030606051e070203010603050c03010e0705030d111f0209040f0c12051003080403051b190b1b010203040f0605060d08030105040b041d01 83
    0x6030902a01000587d81c05001140100756800c1900a00c06954001801c10401e0014140120840d1401045c58a0217045000055030031599182c02c000d544a103080842c074080d01881c0350200329944a40207070707000d81d0010f849a51503c11501107203140540001054200000c00740005001070382d083c003807140198007500c001e00c0c50b240c24008042c2190910101e17221140d0000e68100540c0cac0303001c646c079a40c51226003007000301d002142c981c1c1800d2160544500c80c4801d10582c240d030103600b890b80503158240c0d00340c0d8100000c0098458a00881c0c0c1403a4214011402140800400280b6500701641c00100700018202c0d0961325580c0501c0d40c4c20a030401c456513000107030810f6101600410120344c0040481c1c0441900c4c00700e400900a00b0700381d01034600c1e0f0041c0011100181402c480c01c0207603803982c0c02d0003151340e403515040c8511507441541c0100c030920304110100c1d00e985441200f070b8a01c41d8215810918503441c0034208001041c002e0041900140c070381550700c0050001d04650342c0b800c1018400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 961853147 1250 961851897 961851937
    0x40605181011121809060d0b071106010902071e1509050312090c0901150306030c06020c010206070810051e06040308073521010914060a14130b06 64
    0x50740e0074800384942e9000c82440601c41390350328100c48198204601c0b4140c43c0304286441e068041a105c00e04c0c0d0f1000f0705001010307401d0204d4198403019100c251000b90080d121223980703404500d01a8030840c0e0000d807498031182c02c03000c00d101110352443c0d8200c3c8958098140681c403a2511402e44e03132250415038064001042124504045400032984070740204080c007074882c003600000702040c0b0b0601442c05480038501505c4290342c025800320002c6e68001050310040390f034410000756902d0380000030500601032200072038000c2e0700800150303005290181440c045541414248259039400e00040f002c04010200ca5100d15100d0b10003d0010714044d100295846c0c01c14284025804206014200103400d5000f540382e0581d0ba030f1711325581c4521140c0501d50760300902c03110780785c0315120141c00307100341d10080c00005041107050b80628410080c20020a510b55540400c1099170381e801e1103025280030010304034904a01d1700340d446822080d060500001d540d408c8601050240e0030510710030482511603030b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 961854397 1250 961853147 961853177
    0x1c030204051504030203030a050f0706050a0209120f4207170106090e041505010806221101180803030115110a020f040c0e0d080712020703080406051810 67
    0x142c802000c042005442d141c61940400e50300e02c1a04024030420501044d45003114001304126a003140e0016014850b82c20400d91190095208500003803144c2002c2038560401100403d6000e100718100018082c403d47d0103035403100b1500c0c502c803880e060b11100005c844281c005c0040303900c200b1a14a90000041c50056030182184440013150456a84e108004000d41176004d501903080d40d00c1801180b101e81c0f240c2c03030710140002411038078420241c28072001044c3c0d40c5001404a109156615011803200ea2401c0c020000a040283c0078080100405110b02070f07501600c0440074100c410503d694420317a4402081d0305582082c1c0180c4010b1034101184003c2da940112104458003a00300a040f06040a42c00101d0302d21840d41b6040c016615180b207600744a02441000c0383c2c00a02800b403014006076854180c0091344026000c1300d50006181c1031015148c0f0000d00e0310256517000c0c000e189410f08001c0156a140c004400740392517a54009001c8045441c1c94400a40000a50f2a008600d140e024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 961855647 1250 961854397 961854409
    0x30b030105041a010608010e0703090221160f030c09020a0c02100e03011b0c0212070f0f0305061506121b0703050a021002090d0b0606120c03040b06011d121c03020405 73
    0x17a2020007084417172030050141d21203001100d900f02c8180d090005107500148003046183e4000140d0344052045450304410340013010514403540c07000300d0742c803942c22515000548001400e601000d84000203648060200070300c998014943c540203030801c0854051254005816801c20442400000e21000319038803190401b40a451014428200548032824400300001c20180c00c5170006407089442c02c1c002e901c2000c00f8031120024110320080c02044545824500c08011100d12080702c0a100309400aa8413005003c00e2081c6264000c21642c07804101d40034503640c0c81005480c07004420070415480d25030342001002400150711a40310152500d809900c06814842480d9248170400e00401682a20380c0d68034050f48170150340f00c2844c3c0d049450700804078419006001c441c0d0310008000003800316400c82a40550722403480f40341050410b0f542e040044035402003e80f18158000da000005900900e8882c81880440c41c01008440c1c800f841030301030005c00800070000c1d01c04658005010b00c4581060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 961856897 1250 961855647 961855649
    0x120c0d0204090212070e0c12160309080c24040b0609040c0b3103050d0309060e160e01150c0609020d050a1b1409070e13020703050a033207030b030105041a01 69
    0x4500513048c03081001100d0100540180450308039841e400010300040e001c0e5011080c1c03e41c0000030a0380741c0c642c0e04000d0fa80e503220031842100b940c140c880720383c0c40624900856807103a40d00002c0700095886000c1801180d00001c0c204896200f600e50005c01c100a0683c00340018504414003a03e10210a450300307030341d40200e0001010b07541c001c9401800403404c001503240c103101807443c0008000b0114100749001301001210300312103000d13141c0d400f0003030124081d00c0b500f920a200710700c480590381c1d61480c29080350b42c0480000401c0091082c440030809a03849845854005403140c100182c440c0d4501e81850100c032001c486032090320381b400303181c0d80f80550741720050800044d840300072084204c000f0b80b880c0c0c4010416070401c844c14884400d242c640007502d900005c4220025510780100c2d11b00171700a82c00c00382849000a26044020026481e519240c001c001e401b40b29221070180700034000b51003150b0007482d5070281034548a0580c40e41d10242714942c46540280d054048020940c8409a118141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 961858147 1250 961856897 961856911
    0x723070b060924010509120a06140f0402010f0306080607031b02010603170d1812080a050118150f08071502030c030a0305070e0a080d0e120c0d0204090212070e 70
    0x40007024035000d505442c040c03e2000e08040c0c00000c020048a40b4800c0d002071a81003000003a80000c49440020326200451103400180034501c49014404031a4504503203000c240000400414050350043c0c400c803030030414500d0b0100d01151240085480c15030203950742e400003559a0030300c800c0d1041078000018034920a2009004080c5141c03201e00b00791400c102038488090300000c40c003c1c04000360380442c15401c10341d2031450800381c043c2004030f4000850422a030104080c030001032034500e26807042605070760000b048412032025604c4440c0060064000e0840740e80074000e408105810001c000500910300c8000800c1502d080000c218080c0e0509110141994824010310700b0080000c4203070f40b0078a040d440c0010303065880040c111865407a075050030b60420401b50b004140410b010400106402e015102c0c580340001003011700615281d0070b00d4540e059008140442801c0c40c01010000c0d1950004001140d4051150002103840000c15141c004d90760011300100845064188215030002d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 961859397 1250 961858147 961858159
    0x260414011206062c04050903070614060918010e03040b07030909050403050403170910030b030f30070606060806130203090307030822031805041e050723070b06 70
    0x215202000d4a65046203000c04400c513080313080502c0030000d800580c2e007203543c001c05c14042c2e4101045010380f20791060000380c130041c4c00c000060605030340342c1e040075010f02400703001015540d41d828851350102c8040030b8903182554880610940f0902c0804c050400713012081c84250782d444580c80d0241c10204645e10448100d4140700802010981040a607400c603504400d0f00c5600c41e401120f011110300c941c483e010b5210080e5691454510b51561203440c0300b0800b42c08071120600e4120380159241d8002120408101d48550038445c050748100078860750408019040341000b44541d140015145603401c84000956074804004031072030700c5070030540c621000700c0302185035080034a0000d849229115000d418070190802181c10b403450b1464203e000c9098910b20300310320341c0c9440c0c000c000b60800d0624400c200c58640340030610b0700e0144039041503070340780c4085105040b0603101c2d030360040c01c1c0c018604002d0001d60004280c5a15601c030010300b0b08940010000da40ba0502c0c03030400203075503020f01140d0040c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 961860647 1250 961859397 961859399
    0x6090f080c010c4e0f060b16140a0c0b07121107120f08030a0b040b0312040302151207020c15090607030e0f060a090e07080403020a260414011206 64
    0x15074261003074180d02a08041d401e5001d8000300d001340b0b1603100748075124004101c4800f1000c560701d50b03119600d410303803034881807022030380c1e90042010f64010704408554818511801710000ba41d01c0c030700e58641c0400d0009440e2054501d8031001221401a4800310741d0b083e0005400f000c10a0301c034a030081c00d81150801c6045000b100c42d28541c0c440e107500510005001508401042c82004041c0b090070315407005c480c0c0c0c0c0d20324044022901400d5074a180d02e0003030381000c00e00b4641d8540422071040c206840e6895606240c60f580800106101105404020500c104280a02c01c40da0f142d00301d20810b1113070014141081c075103091082d641d907182600c0360850010f1100d10440d58403141190030594140c035009045840c1800060180c1c1c0701489a203921000c0010790410443d0800c0d100f41c11a8607111828400750b503043d205075080d0204480040058010558500000d04080319040c2c0c54240d40e84030505c400c40401103009039903c41d400c803005224401036078100710b41e0300018441c41007440c20000e000c91 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 961861897 1250 961860647 961860677
    0x6061a0318070b030703140105010e0d020f040605090f011d010308030103060c0e04060f0e10030804031e1a0411031b130902060304060b190b120406090f080c010c 71
    0x5400080d0010992958105900884800420070702e009400031080740c6682e400c080c4000f034000d000c00303090108804d044e40c00014a66014110f011040c0d000a05a8103440d007641e803c10160540e150845540b195a074580810705448118100340302c1e1098101b408040e50501001c020900d42c10410740311800e601100500008500d542940d045941c01203020401c004049016200320100512903a0040d00d04000002c00006408641045941c1c038590f041030707502e03014600c44403c4a17034000544081810442000025800d404a0b5810b000743d081026903000da550300d003003960301d14148c0d109071480908107000a0240710030503400c0d0344101b20020100300304040103c03a007071061540541d120325460075042c9400c4d2100e402401186900401c601e42d00d03c3c10349001d00040161a0798140500d103000146c900900700401030030142c610303428801d0b0900c0c80d1055524416403004208035031103a01c8401c00800140380780282c50250340b191007070307a0b1110003110802c0d00312045400501c0801800840e00100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 961863147 1250 961861897 961861949
    0x30709020a0c0b06010c050d091508010f06051309090609020406270b011205270304060806100c020d050d020c0a0e0c0318060709140108040203101505040e0a0606 71
    0xb6698404902890b80c0ea4400040c1c0d561402e030140078040d800341048103514242e01402120a0320b00600500c81c0c03020303e0000499035201d00b40940140209140d2302449103500074805080200074040610142c103031605050b00c1520301c0c449045a0481c0c40c1c0e0860411031034980109405008000110300028904090301c40c214500c489150940c40d43c1d0340d400c0030441c1d129040322400b1182c001ca0912240c00d00d012138400c0f0302c0401666004244980c1100618000c2c04400c8a0031590140d80320506911880c0401401203030040c4030754184442000504010b13221221a88511402240905a84480500c000e03003400a600c02c080c0c81100c0c041c0c014020040301c00011500000c0b50b41180d504da0b80d98502242c01d0500e124a2401984685410861420b41c00003203041680c50f40800e1b802e185000300c0040d0381e9408103440096243c1c00085080200d04125807001100e04210800c0166140c1d42d0804503048804001c8601c83ca82c2245185005005a6002e0b0400070102e008200350b480240003d0b41c2c0d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 961864397 1250 961863147 961863167
    0x10b01080f0f1801020f040305010e0706080a05060105040906120c05040e0304030f020612010f140103050f010909020a18063002090a060504060f150908062205070311030709020a 78
    0xc0809040490000b400828030243c02a4001c0000c40d0340d0104060030314031503003143c8021104c03582042e030884920300000c101001101d0031900c03003449a0721620011005410010209810407505000000c0c06c0402801a00c006140c1100318180c5411903082034101a90982c0109000d9410501101c10300e80380041102c00f2a074120a00901154061000a4042c41103015900840e5520000841c03d0001500703850308642e8002c08000c03440032180d0040d429603104548d010541100c8034010060260b8503000030001038401454481d4883d100c01501811071901211060065944c100030701100d8a220700340c00f2400c1410b807805c1e480c055a2626009030710107465000340a031000704041208038081e90032800181038018418010039031140f0140000c000c152144103150b40003004114012402540d000040c1d0384010098200380d542c0c038030010801d500200856004c051441c40f0351010134000d10584020f507115410052a00c5e01500816290101941200c000a44100200c402c05500214811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 961865647 1250 961864397 961864411
    0x306070e040e1f0b01121e0e030714010c0f090509010b1e120a0c0813121431060807080604090f0308060108070306030807261b010b01080f 61
    0x11803416407890308541000c5022a0030f802c0512980c401840c41000350f002040ca81000780d0300c0001c09500815464160352094100e101c40d85141850500001e1203508110312118582e01100d207131022581c0c900e5002640c0900c0101680d42d10405a00800e500901c00c0c04c070411a4904030700c509040400050000305c043c810760100e80000100c24101030400e12001c4108145664000e03204c11684d4000c003482d100c12206840c8452500d60380c4503c2901909072280545089402421400d00319548c8040c480d189d0f0041c0c0b414032200c0c003041100300078407400400125003000c00c1c203c01c01052030414042440000005110303c015044c0c2801015030280c4125441071052519050507120030001c030700140310800f40542500c1105601c9070501d80c005c0e6880c0d010340f40a0741e580c1d48541d00c0078000c90407035070580001032104004000203000b0904601d006108030803c240c4c203900340422104aa0425840b070310306044406490380c5a19428070b42131040d1500c8600c02c0c20044078601e040c204000081c0c00c024104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 961866897 1250 961865647 961865651
    0x30d080f0907050d1a0601051c05070e0a1d0c0c0d1419030b2818020c06091501090c120e010b0604140906150a080924090c0306070e04 59
    0x92501e2010403200004020240440340d054444e03041003c1c00558801d0f102c1900c116420108481e94418800c0324200314070070052040e48a451800031380a844054488810000e00c1c1c0c040008550303034900272200501c050384a10b000300c0d150032402c00d00c41c00001d210a1103102c0500156403d142c002c03500c4201155170f80381030042d80f1030b0403405078203500a030810f80c10f0391014504c0e05201c1c60b40550110300144011512403a489008441911070030790340c00311038038000300f42560401c2086070300710411010710351a44015007031100f14211a86050411149080f43d540040401c0b50b910030f01181e540e014000024091150050b00e4a0152400b86c506110030340080e40e41d02e04c206041c030217501c07200702c4003401094150340c0c50703a401040b0340108041964601c98080c0001059403450000306040c048183e4407503003820900108001c2c0d41a0800500c0305095002c1c0403a242a40e05100031200c1030a174040403142914100400c3c928505080212594002c0d4010801c2c4081030740c0000d45201211811140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 961868147 1250 961866897 961866901
    0x3070f0804090203190e0c0a090207030302040e0408040515070b0408072a150e1e030a050105091b010f0215090709050411010e030303010e0c0f0909070c02030c030d080f 74
    0x8440d003144101c0c1d0007071084900c04000e1007200074902050500d05060038900740700440f07200f4075080d21240c4408800354410001e4204200c0e4a065030094120f9600a040042c14907039110201107a1410840e4102d4900000103424041460700c0185001044803084080342400c1e46551003074007000c40540081e0a904012800604102c60103210f04402c04d400300000008888501840280c55040c0c090500401c0c0704210801020384601100550084001d1044005003010800400841505100d054050040344805400708209008403401419020018903a03280e0600480291600c01d1440504114010350480d0782140c0c00101003e01020316200d602d810745841103142d24040c01980003560280c1440104000e03c01c51600b08420104c080c0c840907413211240040503220b02c024094600700054420100302c20300f190501900361100f246100501c1d143d1b03403070005500c80c24115011030000d070714034480b1021400c040c0064045600250010107072101040000303011700000600c100740198074240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 961869397 1250 961868147 961868153
    0x19032109151407060e0109050f03070c0b03100f060206060a0b090303121815092b0c0302070f0b1314010c02090406200a020607020303041212200705060a020c03070f 72
    0xb04684155500000402000c1380e40c4079158081c0c07410f08010b4515018840f2101c600f08804000c540486a0110020306658185404480310742c0000d40b10800ba030f0b1220802041851040d60950060301c42900100b0b40d618104c01007000b260042d402c0311040c0fa00611903100036450000542c0c0c000c64890ba2280050340e07920343c0342645e048407403900340240c0c8100741d014150207205c04802030050140c48251100740f200400f0700201161201000003000003145003005010388900f4103420071500c02c0c815500f807030760380b42c0309249415416000040b44400c000f4403441e0b0564440304610092050941c0340c0c3da24003541001800d41c400026020340103080e000006801c1103030030341c8204695072001308040e801d0b0091100401141c1c000c0d4286401503c101c1e40400c0d006800007040d644940d52100c944146440e01781c2c0110340e16500d200050800c29101c01200200c5507010b040b0449004034180c0e0b85032102803038180180b030000702412400702c2c1481042050f5649002008403440242c10135103101c0d625540740703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 961870503 1106 961869397 961869437
    0x50609040803070c0503131d2707050301060b09030609010902130c1205070e0312130b07170d15080d1d1903210915 51
    0x290014001500820086a00a030640703064004078036155a0300b440c58004105124410030314003000d11551499200300f03001192400b03018020f906107010440080d21407200c0390359080c2c4419540101c0010100400c0004050181c000c04c074181c4e80350800111340e00140b5425100380101c50204007030000c14040c281d02540c0007070070b011294138803020020081c89503140500501001314007001e495030380c40c405c50741b2828590312419040c03041102090700300010140740b07100c1e005c018050071060002c28019401521443c200c95a80ca85031400c020f002c0541c0c0c00c102c007403400000200c41c90502d04541100101d4903900b644955107540718a000c03500c8500c040600b030002150b8810400c01a504051074a030725510152611079847e9070040c0004964015400a031507100d122500c42c003003180c50700910343c08a00149440c00c3c00500348003001011b030803414210010890500840d4040048071 = true := by decide +kernel

theorem cover : BRFrame.Cov 961690647 961870503 := by
  have h0 := BRFrame.cov_init 961690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 961690647 ≤ n) (h2 : n < 961870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
