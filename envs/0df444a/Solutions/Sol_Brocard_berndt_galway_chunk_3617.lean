-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3617
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:23.003023+00:00
-- url     : https://prove2.me/submissions/dcb57b0e-52d3-4ba3-9821-1e88a701b07a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 650359712 ≤ n < 650539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 650360962 1250 650359712 650359729
    0x7020d0206030912040f0f14210c040c030209042016060b0402030103050102090a271d03070c17030403080d0218041a150c031605150708090c03012703050f07060209 72
    0x590300e05235103149115514041401403041041c0102c1d1000940342624a141481c03001c0f080c2e030002e14100405441c2603040d0002e01d80d104042d6401e03c4100e191001d06040c10b210b0f110168028001440070b20340014540040203031040c000c84002c540410841d00040032a44203a001300c8440c1e60008401684e4200a180e00e401046030b41c2911000800702c94865607212420340984810703680e1000300307103440b034214010031150003450030403680c40e4503080c5005200c0d2034080c001e0806215500403500540f080020403a000c5c1d9602582c0750381040340c0310072058041e400000089000b1050340081c542c454646106140e080d03440c0361600c0302901e5065040c4007001040440c42071495004001e10f0303112600020807a06240019180c9510b10004c50802500300044200c0c2d0740c0380546000d00b1f01c0a1907500c4030240740251040403e940c18481403000301400c8820603130301c40b00c0d0b51030003444a002414060280d5504a0301070b00b00280b074280c1145003d800e41d88078080c00c4034810340c0866011001d0400984 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 650362212 1250 650360962 650360969
    0xa060804031206050f1005040b041e0e071202071a0a0f0c030b032e090605060906010e0d060b0d21020d110a0210030603141c0507020d0206030912040f0f 67
    0x20000f1908001c041000c421301c0182e0207000342c030507440b1088101d210728103c1b401070a0b50702030152160389581b2008075030785855018000340c400401012a9207052000c5980c00341106407a105010b000800c800c0f0040d411500c0d0a0325440350800401c69a0b07a48181c041c2c0c451b806084001130f07184c030a082000f04640780f10880008051505440c4070160710005000d4130000c105024040320301100040030901900c4c00c003201e00e0b60905101c0d0003170411001d0741283d4080d6008607261185a5a004011680c038003550b07800660090540c03103014081501070f484144000c201a041b010882c4003034503000c1082103010362400c07901c01800329107208542d040c0046030103d0803074507107194000510090a40c1d42c044841c4040d1107000f803a0000e20506000e075020070006c3d680028018100c2c107842081075103a000125a04002000e00301203461568401c90417a40c400380e0060882641e51483d409100c003a8000501c403e045101c0d0302150030707a0b00d1242024000508540c412014031074102043c0a1859555a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 650363462 1250 650362212 650362247
    0xa03030612030507140127200f041d0307050304030611040e0c0f071a0403030b010e0612040203030d02040f0f080d051b10060b0d05060901030c030b0c090a06080403 72
    0xd51070380001d910104603035404d60007902c0b64101070550f5007401c2c010483c3c40a103035441e9048000200d011200ca00c0361700d0380240908000002842d80e10b92207200480e11018007644442a1030003901d10b0b140561001e4014020030001d143c0302c50440031842c4c80d541c0101c0d0151032942c4041000c0082100d107001e5440c4210034441454182850682110500300000e00306401907013001c103245c00c1c100c1c141410f440316103030490303e428540850101d0002075a5003d9400b0b0380080c0c100425000554041c4105a0f01401c010307008624100d001d0000810f185000f40049031f15000030088001a808d150010348041c008400d001d0341d13003074034000e008107130b0300311035480110f490308100c119401264108080e90311500581240603d202c0440b0450ba080020700c60b08002d4080c41d00c035011030000803203005080c1551141400b00502c0d182c02c000c20002d040300b40300051075140d4401e010f00c0010b0700c1d1610070740c010b2400800142481482c1c800070b40982c100d504400e00080300107040109041c1d02c5030280d05038010302c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 650364712 1250 650363462 650363489
    0x120a090803061011060133050a0c1104050114010906080c0409050c07050a05030a0315080c1c0506040b0403030c050a1706012105010303140c2a060c0a030306 69
    0x195144821400000e100314407030300c00140700c0ba8905004070945608284028145d9000d585c441c0f41c11100300480c0340b0300d0038220781b00103000c506000002c4004d44070041390b80c030b41c2400d05d10701010486280048000464a03c40910b8801105850383c1c001d141c0030f0540307000c4500c1c0041100c2c00050050021350301100800c01d44809000d01d802495007143d05603101c00c0d81c0451140e583d03c50300221803003001c6005220f031094100c044244180480541400c0c986603030213000c034642c10314002c2d00a03501d07800340c5030750b641000d400c9049603e0090306405840500000039241e00710745807102d5040201c215000e03035502801e10204000c040c2e0510920300070603442d0500604180c844640149103080100d4a45e00d00aa41c0003c074405a00640c0e030841808440c0c1c0d54000301010060304500641400e02c021804a01800d0010003000e20090039515211285001060503403010103246a01120302000e070b00940c402c844a510b11910380c00010450105050000c0c013082056150050444110358005060b40840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 650365962 1250 650364712 650364731
    0x708190b0103020904170a020c0102010e0d051209190b1e01080c010e011b03020703050c03030c03031911040605091905180903190c1401060b0a030903020f12120a 71
    0x240d02900c1c15241c0640381e00c8103994903481c0c1002c0c40c1c0c0304003a15030703401d00300850540c42d060760001c0ca8258001080e4020700190410043c0302d0b68910486401d40301050007841500c0c04210112007079030b4006100000c41c0d5a0310040703800d000c414140c119003940c0e070084500411038540c000b11180d00851803d41013500c10756140600c40368442c001c4001003410030404a52800040e84110018100e200d01c2c5035541d01020461302d000780d9910390602c000c880c40d015800c01c1c914030b40f9001c4191048290321201440c0f40d40e03240d03000700300d41002041c2090069581e07603a44480da0780b01e6a000d4009400e85896061761980407004214030905e140810001c0700410800c00d0010b5142c0010028000b80440c2c034400031074844001c407500354001c600c40113800c287d0304804060503e5110b0140034200340600400c1e040040380c0d140729404d981150003900324a6004001d0840317080e1190b07024000c002c1c0280705a03907440c0c2c1a945030318101100c000b5880845180420686ca040c002520f02540040310000104071a051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 650367212 1250 650365962 650365973
    0x908031e072f1e0102180301020c0304051212030703050114030f100902010e060a0507120206071d0414010f050f0303090a0b13240f0e0d120e12070819 66
    0x32105011501490031458070510340e84104101c000320b140f640c4000140c1851104810f00035003046582034001c00c40103000c600c1904043c42201e07000d1a404001e1458141440709001540c1030303105a014031440f550590054903179a0802031409000c3c11394011500b03501d4000c1c009269004081040c2c420740110880d11102d040005150700656180c0d00d0108041c3c21500042e200c000b010b101c007c0e0024070002e12680c115611500401d0000c0c81000000300340440e15904a03541d0f41c1c12a801d102040441150943c2e00b14002c500201d40c00300100089030200222904003000c0741e013070748941c0405000c8074081c00145400b60801c40c00c10400c2c0c0065040546400000361824010f20030244281400140520031070f907a01d40034005005400c1030180722400100801c1300e0340b9001050480080c020013001408544180da18010b45070004040040440d81c640321070344040030070400d500510882c5194400c0c00d8992945130041111448064910355240c200224140007119640182c0c18040f01c00000000c0c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 650368462 1250 650367212 650367257
    0x1206061d060d030810050a0311041805030f1629070f0203040b0702040b1507030305100b0913060801060f030c290f0d020417010c0801060f030e010908031e07 69
    0x181c042c648650b0a49801000d0003820301c45d80c10581c1c20045840000c81404030030802e181042d54103071030811120751407080c0480000d419010080c0b55030000c2006400d4203002c3e2003e000d00c0d101050b11101c03241180c9e0340719102102c441608100b48813004600034000500000000d50003c41402c09404a07009944000d4a80c403a60040c8072004c98082042025034450782c0c000c076510580500340301b4074013418014009003038102d0b04088000030304107070004011410720303000c103000c5030312000707015040000c1d40d8200170082003c00c40304000c19035600030009031584240950001440c200b24540006811401c04019112250700a4119030032010180c564222047c1746480141100075611900c4a0980310b5403200d910443d05403841c0c4600100d0b0203b22641d00d00c4108485d032003240000c00c40400c0003007087d682d042d000d1080d480462903413034265034101c2c000d0b008500440d08040c00094225940e0340c1b81c02c400c0e003040d1007414081c40300030034041c9a04d507021000b0f500464a8208072909414030920068100d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 650369712 1250 650368462 650368489
    0x50108060f19091e050c18240a05071b0302090c07050f030f0903010b01020d09090b0315010b09180402032e0c180b090904110102071206061d06 63
    0x41144103940c0010b0030464411a0103004001c00510150b600c0715440d0ba01d07014540800c0200030300d003401150071002e18604a500e035503040068081e1080007241088010f9100711880c15050358459132004801000d04010040d8403000d80316103444405500b050844450072031a00100d0440703408040c0301595894400315400510420103590f1040186031441c204003201c450005140300c0861012110444c2030054040040103400030480d11441c100120307038039284401c64002040e110f000500480ca415007040415030b40240c03c5500291074903404410070542648210840c000102d14081e003813420340d801c02c9211282c6e8441c00c4042c10250002921030380d034030114081c90002600382da0810300c0c00b6114041481e40050041003440040d0350050000c0e10b60b1107544240b881c01400218039100c1100580d100460041c020420030f680c2d0740c0c0d5010848030f2202c1400e0551051800005607080800d480d0a400c9120784c40101c1c42d0740c503000c203003400c1c1d030381120006001d40d4a4500300718090715000140b1068 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 650370962 1250 650369712 650369719
    0x515030402130608010507081e06150f030109051e0907060f030605120609010e0304181107150b19120609110a0f0305060f040201050406050c12040e040c050108060f 72
    0x9a845a1000800c00c0010700241d80d00705040507000281c200040d4401441094280c44450303041d511850045105440ca011005000c00c1000201da11410070080c2500315640800c1031514258044400e5030007a0001d0f80054030f19078903031040040310381143c407200715000c050884040702070404803500f40e01c445490040c2420032180c0c00000300c00611940140d00105800f80c41703400048080c41348161a6039003158400c5180d070900380213404244001045800300d8440c07800030403100200b46410000b400f450802c00000c21014403408010a171690030100490581e050005203400b11171051082e1a421101c4581d811503200c68100084080346980d11800d540c080400a600070003071502c034060700b60103040681c21581003400480d0f04c40764010340c441500d000701c0803120142c1e603241c4101c003404030849000340010006e0100300480f602503000b402c00810b007841a114081000c8080007120b41103a400862010b80d20010700003405002c4481c10b015000c2841c0054807854038101040309038082c94502c501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 650372212 1250 650370962 650370967
    0x1a0a030b0a1b0906030b060d060806090f0705240c010c08160302040506030f090a060c2f03090904240902040e07030803130201030b03010c020c010f0801030c0e07110d0906030f02040515 81
    0x6455603004201c42340c0c015401d01c10004280c60380394060303458408441d00c1c10140320341e115419070610009410000c8071f5004003140c103000340c0d48404031507136204040c01d011028000d000400340c1540a00500c4501d220079aa0743d003482c5040f80707c0c900d2810b030744000c220074148100020720158490004070b0341d11418407172501449864401c045890b1010301d81c00038061364070303100560040310343c800000030f1180390003401c0654241c42c2c441c0f1040078001004124200da401003210416904044403640c1e03115008034110b4003007940294488050a01030003080c1e1074103684282140461911380b10b000c1424180d030004094050455441240c50310016044043d903600286003e030031684203410000340504058000e00144211690103907481d02c0012205010880250304140100e20515001d0b04a9400044041d40b413450411401c0003c84081e10b45030405c150003101d607220300410030008602d00041c0d40ca10750180d1400c60020304491800c2204922940104003c020603074402c0c3c0d40c000d9544c040031906a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 650373462 1250 650372212 650372231
    0xe18061008100608061c030906030b04051312051e03011a0313150902041a090c070b0a09030c050a050607030605030118021504050a090209010e010302070f03031a0a030b0a1b090603 79
    0x100000c3c0b0346c01505ca0203208418800c0d080550204840301252080e40302441030b21074880c1044140d41c822142e203840c0030900380f5200c010880d2206070b4443c013440c41c1070092402006002d0810085881da01b40405444000010030001100078003070751040c0c408050150442c1010880341c810704501d51005841d205140e000c254031031011b640500001ca5005004200e8118180c0150000702a01040c0718841c00d844400100107054031012114110f6111070101000e40e00c02c0d890f480102014030040e010040c03034800100c00900c0c208150300169000b61300405141c80c0c01032009080c6c40294200d14042e905010f181054038007031072021007019604072400018010749420303048581c005ca601603541308100407000030b4580d4207680144036140c406c1c0da49580910041c0015800e80c071070745400802c6412000c04107004a0300c240e001d01528100d910826500e81b08920000b40c02d603000e074106443c0840c0c40d5046c00030284071881540c1c0100d00303005c100340003030711070090181c80407403584500e000385500c135105039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 650374712 1250 650373462 650373469
    0x5030f042c18010f0e0c03010e0102030103121805060c0c090912070201110f0d090603050705070f0b131b0e060906090106140906070809180c16030e1806100810060806 73
    0xa50801e800e4041c1041185c036030b05c0d1950394400311400e05c41d029501c1c24210404114042c002ca0703040e83c0e040408070401e01c20300101201d548402415640300704900b2440407078640e5401004002c41740310303c0d000b80040e10350f40e000c100a448000d865454580e10040d1b4600c41d09066006440d141034090074101e1048105002c081d003400c0209954014900413104000c903410f41140101080c0d90352a03400b00251b60700c00c10155000e12400001030103045000341e103d0f000447d42e074420341d40080440704403002071165554043c261561644040b240c100720503001d01540240001056004408490403c84c2c2d061940105a88500600540b41006078150500c41918070f1b020848101c603c000d010980c0d0340d14641000d000fa03402112501d481482400350320302d1944808009540201caa00c030503103103460b86003031481240102c1144c048090294550f85850b40da680c000d000c0d55012400c40210301c862409804028885124491070400c0c40002000c0c48482025440707080c0a072006400c1980c03060711508000b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 650375962 1250 650374712 650374721
    0xf060708120702031902011824090605090c0301110f0c120c10060501260714030903041d041109070e1e0a05010e031005040204060305030f042c1801 65
    0x100120014180103200a00f503000006200d0070f0840c046101d09076200040480c2602c000c4051941e0040c01c0070807034004189100e861183c1c802c0c45010745448001d04080c0603095a10500c801c0da0182d544608000d48984180903007018008100d0081014490900d2516a10b014000076107100c03c901041ca000b64986c10415268200b00c403003509034941d648482d01d10b0f520241126401784980c103101001030254021950401c50b20608100c020784848863310710240200000c00840c100400b4408100700010303000e0040d40a00ca06602855503141042ca036200302d000c07031070101c01d0454030030820003001c02c5005500340c01e03080007150401000d465020044a8200c000e410315603000c0000036490244640081020198940c140c4104581c1075581d001502e0445001003810f80581001128072100c0e4082d90100d68014401000021f40f19166114280740d60840b40b03c00d070f0800f400240c00e100301c0d012114500007150070340e00c0c420706032010310083d66184100603000d40f50900da901c03040c80c02460207400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 650377212 1250 650375962 650375977
    0x60203090f030414030c040c1b061b0903060b061c02031510030203180c0a090e16060503010602010501050609060d180210030b27010605070c0806010311040e07050f060708 75
    0x2c0303a03103694550707030f40500001c104001e141c13082c8501c540200c59414a80201d502c010229140e443c0110710a02066520b00c0042504540050761101040007285076440000c0d1000031656810030420300b07601c0c0c490202c640c60308000e80300d00741c00c0c00a07003018580f0b040f80703c1c98014041800360716603c41901c1007155251000790300d6444250b290030881401d505134045c62241591040c001240301d0301e0081e103612414000f240540084800c41c003848403080b182c001c6824100e10808484044903201a004000d2802d6004840010f5002004020982e424002e2a01500003103c819191004007000105c0034490840c0c0c07000c03000d450342c1d422910030340703181e00e60210650060f26080810141c01e50080c0140703000c103040c600c145c0040701c00200c00300d0203040c0e030024540f5041d50700095074240703403064649800441048640c44c04800010441c1041802001d0003144503403d4841f002c040348040005032802c2d0200c039420350b8002102000680e4402c00300b6030000c0e5007075498a9550320f1505008040348525803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 650378462 1250 650377212 650377243
    0x11d062103030a0e011508100c020f240708061e030c04110322050c010309020307030501020408101b020a1b0e13110a0e010b0f0403050d020a020406080c0d06020309 72
    0x410400d4003003c54212039601c460b000d00801a41d07049400c1c1d00e01145c414095407480380e0043c1380c2d000300c1c0da4035580721081d8020300b4011101410081c6445514100c040414207044000b07a078092080100c035603c0960b0080c3e068100200070f454174401040210404103050700d400c201c0008620b00c99103040c40607440e4508058818000c0003c0900c511407280d006403420050303204512844006800340c50b40c084000d5901001070140e07004060300440141054000c01e2b0f81c540545880040010024402400185010806481d0550203940d01d407003201d960f051000307000c00c4c1c03115408401d15800319490408a1788106c0300c0b00a686a1b104040451840d0b070070182d00080b04806000003005101c042000c0c851083d08007040700041c5009003c07c0050601c03c0c091701400c41001480840c03904400707440d0540468030601d050945c0e0341c5410703103010105c518120158011280040c01d60a280c000c0101604905005182c24102000850a0307880d06690150011f64044080740002c2d9050145128040c0781d071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 650379712 1250 650378462 650378467
    0xf04060c0509040f0c08060105040302130506030309120c040b060a082a0c16090603020904150213061805240906040b0309030a1812110a150e09011d062103 68
    0x101c1e4003400428184041708007140360040003600e1980b18404a40603654040c0441d200c00340c10304d40100183c0006801c003076050106001c4085943c446903c1444602c4419006280001304002030004440c0001502401001e0802000403134a070883c0040760040e545d403605200d42c070520459402001c0c941d56509000001c001180144010f0018121090403240c01c41b000c0000d5941200000715006403000035080154940044c022803484281c0724601440180b01510702110203007108075182e40743c0c0100000c210f81004002100b84510500409410291240e111f9081c0c4911a400d03400341b010041c3c0e02c100c0000420f2031041c1c58100546004082a100d2192241030050b82035407241c0080034100c00203064990504040c022040381c140c101d6052440c00000700a8580310742c04e2203e06500c20542040c4800c000003400c3c049812461b00c1c001d865980d040b011001d050404c00c00e19410780c00540035400b81956102c05014041c140794002d0400c4840380c1114000790b000070461410350040000c04d0101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 650380962 1250 650379712 650379731
    0x141e0703150b040f0f151b0c030b0103060b0d20120a08030712090c0e0c090907020607030c02211605070905060a2c0604020714010903030606080f04060c050904 70
    0xc2d0014109403540e001c20300340810340f2540500e050900920403210340c40014400c5e04540c60140300501c02c104410b031510410407055841d0484425a0369004941c0703000d0140042092081b80c1c881c402c2c410004030360804c2084015141c04d04c5900300c1160340760b2000d140d10045061035640640e00090340380c1d070340e05a403035841032814401026003040726510089840720540c040b680c000c6114003000c85502880c20ba680342d0070910048034a0200411801400000b08942c008035510782e045144110316590050956180c0602e0040949915404d880e00350350041d220607030a40d680081040c0707040c034180410750301c52060781c17800c814100d2000d0010300307540164000800c0460b03403500810300c40c1c0c0e0309403020160169161028801e0a0020208005e60044020b110041c0342d25a446c0317030f410a400800242c10164962603400b1841c1e1150451160b5a5540100f0010590180600d41c003c007a05e082030001458520303203000340700348010001454035a4a265050b0602c0c0103209039013083c0c41c040d108016030301d074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 650382212 1250 650380962 650380979
    0x509040b04060e030301030314090409150f1a1f021510080c1206070e03120c030d0f0b030d03180c06050720030318150a080a141e070315 60
    0x20a0341c064407001d0405603030b00110000001140c4c103e0b545682c3c0c003200c5006c40c2c1d01340c512035001058823039803254031051840b02107100248910b0b60100d4420001400440b106c0584007140c03c80c24401103c1c51400800310b03810f0b035800030071000720062416020308154101078101e040a98440f40010100002d0042c49100c420200038041a40d840300304490340c89420301e007000507814580302a8045580b203400040d550a1050074400310f100c002508840407001d00400c81e0065810142c034500b510352000c1202c2c80000c01c02d015141e00501078140401501284a000c01d4450030711800c0c00301850f840c0d15403451440341c0082041101c07038020b04403003202916801c000740903038048072043c2d030700c04c50304801c140301142004a0b440410358001d00451920001900e21603048040f9481c09074803000880300401100c100c4002004800c0c25035075089014a401c004140441700628641808000780508000283c00710040403050b02c810f54034011401c2c0d64802c1c088010b880d007411054007000b10284002400c41 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 650383462 1250 650382212 650382233
    0x130206160302070902030c03071b06060b0a0305060a082a0a03030504030b0604062702040905070c020a0f03030206071d0d03110706030905070b0703020f0307030216091a06090406050904 81
    0x40c4294241c40c281c3d80c0e981c0743d15013039000c2521003000701c0d0001c10215030b0341c078042d0005810303052007951030400c903070701c1a00d402d4100c46003640403c104110000360a80301a51610545034026400c942a10400381003d8010356100700c10402500c5c104048114942170490801d0280b494103001000c82d02500c0d100d223030003882500180f000f22130621380740010610900e000d00545040c1d070321101d009840e0300c0044855005100c4c1d040440318031140c0c00c01c408101010703a40075081c072402c03407038231200c001c03000318410700400021030f03801201c004c104030a0a10019a0105516401c42e455260003400b20f2500200101b001d68041c3c031540c0e0241c0c8128200301016044407030201182984020703100d405a03100350640544906500003041e94105100c1441100f00c90409446028002e104613280118003025140c80c541c000c0b4070a50141e841803442c002c03603204802036400908040c1a003440499242e10a9400390103500c400503204450100d0602c01980382c550201004240080034a1a24141030901a407a079 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 650384712 1250 650383462 650383507
    0xe120d0903350f090301060f0e090303070207090203040305041d070305011202010206010905130c1221020d03090201120911100c0b0a0b0114040b1b0106060504030209130206 76
    0x403580d80742c600740c60440381c0840c9242e1400740c070800c006600340001c00b1405580802510910a0742c20f11000790180c900344031b850301800c849502c240c0001e091108003501148018640b15065004101300034101d9804203459007182c915440168594a40e031800342c46602554121551444000407851420540c240030b0078007500072034030100010f1340ca40405220a01c4904800390141c2e0144004001d010119030019501091079035a101030300b0b4090b0385600f04000705500401e440d03048100c4805c2030250304614807142040048510143c981030301da01a403924140360001c4241507175040100e0559003d41c0c54603100300288107041100e0025481c141003a003444c2c272021401198115079500703659002d55440c0c0081a0862044242e940c0d4208916015001c2d0440003410085440c07030322010040722401500185c03140a43e083e03141c4241c0700c003070125007440d10801c1c030040e0705000b0100300a40e0800200c800b600d8058480e1400399423410ba5035088010f0303d010003500041c0c0020300c40c00b40110016100c115 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 650385962 1250 650384712 650384723
    0x40905011401170a0f0c030606030b1504060509150a030b16260105130e010908071101030c08190b060c0d080114012a0b0f100506070c060e120d0903 65
    0x12641c83d0390703402140341450308110420f60b000c1d09590300070640546480014510440ca112601a1255110016200664012158070014a090005514400c14510031544059404010742858000020700d80380028200070f603c03a0007001c107501141c8844102d10007175500712000c411b09061400802c080940c1d07140c101000540300e140070180769085007480c03088071215820303000541e90a1508008040f030304c54008041059403034501c2111280203024017801e15009004007504e0344403030304003521b4032244002140c0c1018034050589610036000000550000280000760034070035161000000100007041d4195445540030444980d810400600000d0030442c99490310841d0b6030300d1102e98015904100401d02040c03602c2807a84908020020203098100c290b030031100008803e071940062034400341d980c640300c3d400c002d0411200349002c1d48650010720080d1103c601d0807041d91100e0040e10000d024090812103072000300956130340c40780306d08103040d02448196010b03c00c003810302410b0b111091008650 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 650387212 1250 650385962 650386001
    0xc080c062701110f0a05130602030d0e0f0604060c0c020301110304140615060f070602070c030204050714030606031b0406081f060c03231204051b032a04090501 70
    0xd20725041c082c080c5500f144014030b60500c0e0f800300c03034140c4a4005100740b0007041814070a40410341c5800b50300a0041c5100e4000d103940d901008030890030756404a451140e10b900485001158240005020707901c142c0180c0c00056403921564112144030706220043c3d8075600f4809802a0515084000c50107280b140c106803402e4080c20007019107400c0e04469110301072980180351002c034141a0b004100104200c1c540c64038001c960340e203040c120380101400343c460000221090045082c18480d0680028ad2800c1556620042101c0c5204511006103182e01808000c004201c0131301501c000007500030080c4a4080d107864440c04000c200d9030b821200c41ca00500d4681045041d402d801a030101a1100d42e0744144e03003180191804c0d1956441802d5465141d00078401070061a1005d0010380745585c0b40481044d40c50425080041c80c0a8503c0d01003103002404e03200445281e500040c220a4040300d10601000c01d0480b03951401c4c403400022515600036040c45000000c0180650150340e410000c0c801420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 650388462 1250 650387212 650387281
    0x3117071d040308150a03140a14010501140f0a090e030a020c180a0c090e07020c01030506092503020705010c0302070b070f210b0a0807030218160c080c06 67
    0x340085000e44014010503680f601144190240c1e14400440f0036002c1c006511141d42c96880d40c030340580034400714034260041034445042184c1c01c201c00c01d0300080f0034001c1c421035042030300fa1b40d0110409440ca074071490380391400d4400341d04e44451640040c0060f0300200019100c00d403442c0d45a40c4100703400001400390101c141180c0c0307810320010f03001c20f035504481d000700e5039800d501c2001014800030000a01c126618000341c003044281e101c40c03040003036034003800d55048a86d00140603100007400c0648501101010000c40e0291214400040300c40c40440c4c500181100800390000e119042c1d0251540d401c11088880c03d80d0140c005000003803064040c00d0072641e41c41001c03180500c407800c0c044000386207001030b600105413104101c403270000014800102d15001c01c0c0040c00504c8198045807454100560800651030b1003a000a0008000d48001c0b07554a00848018000d118030100350062190400c150300c00c1c040c90030140c80c2c0010f21041221000d0610307004c5684841030f44c500c001c44d61441380c0000c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 650389712 1250 650388462 650388509
    0x605100905010e010302061b0609030a090b030609070c1b0321020312040206030a060f08011a0607051f06030f300c062019080c311707 59
    0x15040b2140d83c502403116900359400c120303490b805a0150000303d003110800d0b042007142030042e503004240758801160b44580c0800c001d40301c00132582c0b010700540c9003402009503545902407044d0303111280d40b41000c0440601d140540302a8480080d880c5c16044580c4040104400d541041340d0355803038040c80b1190702140700022641c900c5030040c88400a031203a00403500506040001d16001881e0110101d1a0350b04d80051a00b8441c06600184290303450301c584c90f101c03420740c91071640e80403025508180b40015540302c19644504842241d008001c80700d03e640b0141c030b103652154000e90340c440e02c2e194071b030006400d0104201c4100745000740c1244030041c141d40f401001407000102c0c41003070384070b09125601545840c0007c02c2e805240705910750000402c01e4000c60100c0c018021490148003042c2d54804100c0c0c001d10f2140001c0c07803142903d000300801725001c0c8200219550150040c2c00000c03084041200c902e01e103981c10303408400c8180490288003803024000c100d503030660748000c960b203100e04034071082c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 650390962 1250 650389712 650389721
    0x90e070509060f090604020f0f090a0f0e0c0703050d0e0a020909010c1407050c030a03020703111903060203090703060204180b0d120807111c020c0d110d110a0306051009 74
    0x42da603000211544100c440c0c1022007040e98091001000142800d901c41003008503a480006180d007002c1000440713860614080c0310f100040c2002c0c4185d50300342802d1041211030f0301c3c0003820130707200014041812010184507004035400385401d2401805484030452440d541c405076550100d1043c5000d00007e0828070051007021204507255542c000a0f81c00c0c1d9480030950f40c4040401e035810701a40041c0c0c0c42c6501e040105040c02c40c445c0e8000d03c2c10074070350304015198180034588a8403501041351601d40d000145821102038980000c40140d0300c1c0c6030240c20b645003914a40c40100040d00100d800242075071100007a10000c1ca000c0c00500055003034804100310800a8a80101000c40c0103182502d01c030302c80d802d1070758010b9490512002e4411250840c0d40f030401c40380c899444d1540c1344008420201d41c1030000007460001911820061a5569100101c004111300024003d1242460480a004031f0111009110034003900b01040d2544a00b03004010300390490314034104003050b08001078400a01d114 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 650392212 1250 650390962 650390971
    0xa05070503010506090622031202030a1d010e0d0803090106060e100c1505100303140309151026010b180f13050115030311030403030e06070318090e070509 68
    0x68003071942c0c0c20801009107941007124883e80002c4c00f8403000c80f81c00d800740f1064070b10040c01007502c107507180b03135142034000880d004980408540003070003204030b9940c0001400d00e0070541d012102c0c22020329040100c6500103604811903101c1e5040a014050021039001140140071240c02841090744883c7d095903c403080c40c0b8503580100c00c4030a400a2903100d0b02c909d00c03034141f09083e90b41d01c2203005410681070701c20a54440c8080302131300f20100304264120040082d24941d1141680c01d501d00800d6803515022240d028110719141c0000203140900d01c0e05a00d0042d00c8011454000070f83c5901040001d00c820464088880d0300c0e109402d610303413a02110550f21700301148a2800d95a58450310038044820107000101c000355a0b2064400288082c06200c0030000c10440c0d1043d001d1650030014804142000c81c000560402c11041c40820741c00b20940d464071005584050351640c00f40b40841e480000d442400b803100c010901c010904c56104c0e0040324a100c04001200c080a0303c4d00100300329030368140c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 650393462 1250 650392212 650392217
    0xa050411030f07020f030f190e0f0d051908030109050708061e0a09060e07030b010e151c140910060608010603090c0e0108070513050405030a080c040302030a0b060103050a0507 77
    0x40040c0d01c2c80030246606034060428815039a000700e2288a882c9540c115413455040d08070003080b0603807810b0b0030a174400081e041c2860080880788032103021403030000d40c1c080382d1030180c051440100c00340f10042150500076500d0101403d040c40e464180216250001e0080d4a205070800d808592071320310800d00e9a028440c001c104800c440d5280880341c2d80820707104441c40c1c2007240ca1400041e10451441441c0040ca003035884d4188519100500070115404465407a05020042c0d54101881e25285d1290300303095020030419658540400f1080e07490f001c41c00e0008515810411550608034621840d10f0141a4060803120078042001400080d0740072800340c40002600d400c0100316051090304165900c5000b004003a2001d80c135040583c0701100260000205507109800810071810202900c02c100c807a010410005418295543e6445c1d206080d80801000980c0001c030740000c0c10701048600640e80141101d44010903850841605082141c1040c0441e141c40e00090134501e0398001d0501c54200795 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 650394712 1250 650393462 650393467
    0xf0c0a05070302071229090c011214090f1c2a0c0f080d020a0b040f0317010e180d0e09090709061e0f0b0a0e040f1a0a050411 55
    0x450100d44030742000e0020307401c6100d02000007808210340d92100308251300600512600349810900f200400e02042d04040360103604508204100c42e0110340301c0440d007002d2030801185862071401a000e0f00025412581d505150402e0203010389001031080110f170241400c0c1c40301100181d401e0010142c009070744002041c075415107406180c200710b8400c00c082110040594044003180c564683c01442500064400151001c09100c00101004001034000700c920090081c4e030400d0351140e10505000d48020110361940312034004140c011400001e00f0358003400303905810341e502d403a0042208001c0c6c480070f840080752042e2420403e00402c403030b1505110394942d80042404a0188581a00010900e40440c043d45d400810102a18043c80e0300910042c000c504c03450040d07027074014120313205174007180500500180404c00d02c10200d080c4c1e8440c01c62403c01840c912004070114001d01440c10b1f45480b0300e403500b101403000c6400b80520002500c0705580002000d501c40041c40f045406280818840e820b06 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 650395962 1250 650394712 650394727
    0x908030717070201050409090f11030706050f0a09150804151109010c05030f0c0a110108040506070c11041b03050117031c06030c0e010617061c0c05090a020c01050f0c 73
    0x10700101029031040c0f511038a82999200440101e440d40358044494260345222802070080b04000c02c0c04007035084004e490800c1c6080740190903442086030409400d1804100c00503014014800c42c401001c0c0902284280f0801711001810380e50215812101c00c8002007825075043d90310700c181082e41c0c01c0b054401d442e2491450042d43c540346d0000040300c1510040015070b001c00b4101e009060740c0e114550003410707200524038010f6600c00ca001c10360b40c104640c950030040030070800070701a41c00500504049003d11410300f45500102c40200e0300f17a802c18244807007910b480c1840420406c100d04503903020403441e601d0f10030b00b41c1580a01c54000980b1351050000c5d2041503000c40c000c0440000b41800011050303581d607074800e00c109030b99000650320080395004014403a04090074164200f299908101d030383c60514000741420340c65523140d030b0901c170f0814507030b50401410070604405454010481c0c0445e05d08200640069403108484030311a508010214a11000004140e4000c40a40c110070b03040064 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 650397212 1250 650395962 650396003
    0x405100b0f1c15060806150307030b07020307050303040305250c0b160b0103121707021c1808011a09090c042706020d0c02061009020a02012007020109080307 69
    0x284018411110031001000000084920000601c0c000700c1490225109117040e1006050090080c106000740e56107000c0852a030745e01103900401c0d00d0b80015541919215040100c2c910f00071044003d20340d10001007880103158100d4090446410013809040400502e6030070802c13114003c0314001c0011803104010310034a02041e01415420061100c0b035424062140ca40840405003030b40103580b4039895242c9008681d034858929000508406485036141c18022030081d5a50781c074080c1c01040351186121012458414000f0300fa030341c0e074a0071003011602d403030300903550081c5410305460307541d01d8560180113000d0400c84080d910a030b80c0a00501404140c2809000140000c103803a1145003850441050780d0703044d940b6034011f00d240100c00040c0c0f0b031440601a00c00312040083d140d0103641c071000c00c1000e030394099585001503038140c20000da00c508015100764050b100f080320603402c440301e8120b11038441107884090040346000740d0b548041140d40e007003860340f02e00c11020701034010080c00d0305ea00c24811 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 650398462 1250 650397212 650397229
    0x41805070e06030307081314060c0d031d030703020705270c0d090c030503120c120615210603120c0a060932120922060314060405100b0f 60
    0x8040c003500d10700513561b83c1d000e203194050030003d481ca1080080034000c03407015101100c0101e0f0f0a5640c185401d00801c0c005598a810800d00b070201520307052000807040d406840320410001400480b61180d40034034000c0d450f8802405450b0203646084000c44501102ca140403118800782c40690480d92660141042c46500882001e0503a40d11101c1000c0090310f0085100000c5009074003a540380c01c0a40c82c000c0e00d002d03019001240014051101104080c120b149568101e941101c000c9400000d8800500c3d05020722407149100c1202486860030041c150b07247c2c240b144100701c059a51706200c6e150861f603030780100300c80c0080700c5e40480c5500c00050000e900410302a0b016002c000c0c03003a10301001c11900c11751510b21100d40d40400600c405102e00c010800310180320720702c1114504003658000413407554244005000c285150415202c05182520760006000c0c40d04080950108a00340610666030031065400b1986072258492002420070540310312080103500038900042000c00c40100440366 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 650399712 1250 650398462 650398471
    0x1090905100f150e0f01080c180406120b06030a0f14010f060603061701050c090114040e070f02100e03090d231605010e06030c0a0918050402041805070e 67
    0x140c03101c400209020341495000002001110022220783d100d0880080180c5442a142402500350a00d030682581c3c01041555001042038801d80c0c07924401c19810300e41915031410650494036080002c41c40740d4155102c804070328040c02000d56030fa100c640600d591260016400707000c00d061050706400041800c0c400071000c0c5480000441e040c04c0b199154030403030300558040c1020941d078500802000c061000d1031444041e82000801c034529101d11010441c0c031a0092640c10801d1040754411800e0b0240e040c4c40240800d15107200c003902c0c0501028209821342820701c000b5124110300c20300f4400003806448080001507000c9e40c00c0c184410144440320803a442d04507206a4006860071441c3e041c0303100302040b11410401030810032201820f8010080b810780003141041070210031300030140caa007001c40b604180d480c2141e070b0f81d80505240444610010b9040f0300c07000b88031410340c24042211504294040c40c02101d0400003114501045c00784e103040f041c03004186820443c0100b1010807040701c050303400f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 650400962 1250 650399712 650399731
    0x6050a140c1e0a0b160801060201090309060305130f061d0609190c05090403120f181e0b010b04081e0c011218150b06040b0d0c090504110a021b01090905 67
    0x1005496520b9001c808402c8035001d003003205c5030112440d071613400107180340100500e000811000140d03803802440c84401c0e00036001811b44070f0300414074071202d511100028580100e8999a43c3d1444d1900d24068281903840503000c83c00c0300200e1000e00b002182d6103024282ca47c004118141d046401c0201401d4070340016120040c103048006050b1321240400351107607110303503510902420103004404c101c6284209030240107150034240c00c202004200c0e8024015000000407086c10b00d94140c20006188141006003d51100000060603812910141c0183d49411080d51501c1d440407a4030030060010304040342d115805160307081c21a5016405840680c403a0307000205070b0715142d1301c40d0300411500344021030b41c0d810b101d03042c09024003940c8114042090f00f1076500c0e01d01172625021038041d0040300e400800c0d4590b82c14801f11150300850655000381406401400f160200c10035040070394005c0c440010160103428246900070300c0115000c002c4030381c143c55030030080f428400420300a05008040050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 650402212 1250 650400962 650400973
    0x512060409020a0e0a0509030313030c150c09090b030d050d0905010e0303090f0c09011a03150d060903020c0901210309120f0516030309030b0c0d0606050a140c1e 71
    0x258640080400c090720200d11680c5450410035075017412200d00505001858005000703101d8202c94807100080d500350941740c0f000030305503d8140046088420101d105040d450000d8403446250007071900001c07200078402c20014100100c05268031108211144400604200201e0403540e00c141d020b0a03044d80518000182000021581869940b0540d0f00c0f03c215400012090034403941013150300210841981d5010b541d51400d00101c00701e151100f6000541200070000a610f000071288020b014503004180c042011518100303800100003560042d001405013040301c200e81e080c102d1680d030490b04d80002d01c9403040c0605d1146906100124030840400600c0303c1c0004050b141030f403d44507082c0c01a0204580c00806180007071a00401d4211075580e80c204250405c0803e801040e050100c1e41c01c280d44d07040903a21582c41d0003091040024030344071985003800104a40f0b90050151000260345e80f18055500846401305d01e10b40140c0307082040c560b0140c6000b41c640e4800206480c101030a8004070307407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 650403462 1250 650402212 650402231
    0x60702010c0203120c1c150f05090a0e0a170d0501080607020d1103071a01050f0315060f010905061210060201060803070f030311030f06041d0a110120011a1005120604 73
    0x460000c42c074007042e41a87c60381c1a203040b815950450b80b008041c1d81c028418a9031401c004034001b8807004001c0705846a865401e0056102c0c18080122029403181d20b02d0b08501510380030391620341101d40300c801d80c0e0346024004140001c000448600032040c5800904080291640032a1600a00710f158441030100340b0400700021035041e050380d052000001c0c1d00045605010034403200c2d00744103a880340b080d400000700c144101342102449400c14001d68944150700c000760016910842941d02c1250081400140d402420002c03240340c90203034500350101e92825903203200803404d94100f4082c0c03503c180c104001b41d00000300c40d09007042d040382c03180c01c0220f0298149800310741e2a800032101c1005900301c8404210140c9054401d641003840206c8500e18515500b1700c116944880340c1000625102e000104c060090713018031100701d01160b218140703001910b80d540c00b00c0e004c1d198441014242c2e101000c4c0200301d0f440d1400502102203d640c0d41d070790401d10a82c1c200000050051300321134101d0368035949107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 650404712 1250 650403462 650403487
    0xf080c0d0203030406150b04171507020f01060801200d060e07050a020d170114030a0b1009150501140d09120e01021005060a1211120f060702010c0203120c 68
    0x80ea00005150041c60702c0c0c4c505400c151007640c010b150a070031840640c80c000d200e140c401506a40c1650242085410b045d80142ca0192414040d64413010b03015059070104110f0301c0e40080c112800840c504001d02145545940c0c140c01c0c1c802c6200c0011204044100b9248440d00c400007500b603080603420041006551180580030710502600c60354001000010074070442501005070400c000e40c10300d0001d11203102e00d80341a40816040c083d1702c0d0041d0b90f80c03040c45425682000301200700c6401c030f41c04000c00e04081d03107402521241031160040040c00c040c000703a13540781e003c43d4a10072250103850705e45494000c81101307038182d0702c2640e40ba05402d9a8024602c00702c1e0304010400c4025455844080d190f0758a10000b900e4110084044120349003410100040342e11202e0104044507101c0480902c0e61003945000640c040603100020b81100c241c003c202c000440c001881c1c0c1c080081ca0702039641e5920385000480c01d0b01c0c4810304040c007681c42080103c0a1a04403100d10768841c00d4a032659052102c3c04881 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 650405962 1250 650404712 650404723
    0x1115011406120106020d020f030a02030708090402090a0e150102060f04080a0207080a0305030a05150102070302060a021921080708340e040b03011e1a0a0e091006120f080c 75
    0x100180c2c030202446d04901d8040003841890400e141c0114200490828001e540e40325082e00140300d1503010840010300c2e01d40d0f40589515450051080741c4054640d0034041c5821821204a003400011f038030910362039400820781500500340c00d0034085c000c1d0b4841d1140c1c0e00503804280c2c1c80c0304520030200001000c1c20180301c5140e0340c44c48bd58030940d403030800b10910b01c1500d1000c0c00840b8020303030f05c400c955220ba13000a082d208a0764103a91154817840c51000c10ba0034031a07850065214000080ba60344200050115000308030a01c0c0a001c9516980c00f00003161000011190000865609000325401302804940c80040b80701c20980946580c4807001091642c4564810810200d0b0288103540d85a103428014000f201c4000d0b0002c03c0081030314140681c0070840c0382895450359030340d41c01c00c0352080c00c900d4503803907a41406000412059580c0c0040d180c0b400c81210808000e014152400385c2520f540e002d05021035126500914805151352078420b0050045441220240401c0268401801040c0113 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 650407212 1250 650405962 650405969
    0x207260a060b0405010f05061e0405062206030b0603011e051c02120c100e0d0807210c0c050105090409020a0906262d06040f020111150114061201 64
    0x110b44001214140025940183c210f216524451107052116840d1841550f014036020014005803c1482d00030460744c1c496a005507400c1400000c0c0103c85101c241140900c1c1d00040e81a514003a542d140101c00f242d046081d019440b5000b0401007010020480c4e41c2e8640019070b212038402a607680340061004407920003504060061100c6100a40c504848600c8060410802400c080001c502c0042c50882e40c44c0001000d20800d0407490302242c4400300c08080903540012129038880c8641018a413074451101da2000c906170700b0300c102101622680842000c3d0741d1003000300a4003800c150044d01d46810039100150810383c3c1e20301a6015958034082d500060041035000507001c0d00300041e8540c1e51a00c2003040ba40d00c800d40d12100d1022400240740c134210340d503030401081010380c4c1c0c2c41c204490b02001c3c1c02035500391148038140000d000f08600101c880c0c9200741c844050b8000140001903c91490300c0c40f20900c074031002d00410040b0440c481c8540d018030000e04403440d0098029444010a0080c1c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 650408462 1250 650407212 650407223
    0x303120b1314071706010c0c0503060103060203010e07020d09090509030d05100515270303040305101406010c030c061d03040b04030b070503131112011b1b030207260a 73
    0x7501921038000840b42c0790010b50a103050000301c4544440328082e210040c010380e04200e20050107800380040803c061002c3c0030001c0907200d8650792814550040d4200380500070148600c0808111158000a018140742e84607441b640c0303096181a10040041600804480c0c10b07010401140aa800c2a4807500e4451288803040051441c107210030300042020313040032445002030030444410f1100c0e050104c00c0079407520500c2015041e038504007003404c5020390340c0700030460f100714061609044c415412841e014080207131450070310b61b503200044408865102c2d0250100e4a0395402a02042e1603401c0f6890320502d14003c800b941c0e00348402c0302c0c42d5501a43c031990f01000003140910411282c00280c81e0040c5036841c11074150308003c03001c20380d21480d01300d0040410384240d82c0d142090f1102c0a50144501d203003c001c10130501091403003000741c20180080d400145410411100c2c80b400700c0741d1118a1600340c0d0080142c0e03418060700b01c51400300f410006000e8400070510549000c03003041007d0071184182c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 650409712 1250 650408462 650408471
    0xe030303040f260702041d16032d030e150403030827060a05060409020402040611101e091b0f0317210402010e10020a051006050a0303120b13 62
    0x504041c3c01c0002c1441040c41d080c00c2024424455041042c1920a881e40440f00000d61140c001491018072080101d07001060203420f10b428602c070000600d50b02102c3c010700007405000c02c0b003103881d003a201e805410313452051a5a403040c00807034410012a282e2460140a5403800348901d1450111500144d2084001035054020010a402c903400c01110050344503d000b100390f0303c0303004140e0705c40c3c100400313104a25a5440003e0f0f22a81d440e0402c210094000e4421580d071912004010a40860414850000d201e0014103901f1104103101d00801610b0b000d201079200700c0980310341c0014219000007a0b41d0720407100700c40c0c03440b001840340c4907004102003903140710400d00d945003181c3c091034010302c2120f07045014480c40c1408410785803050032072849000802c149603694401078a8251100030702d50b0700041040800b0301c0051300014800c1841d402a170858102160364074540c41915943c1c0034098000c0122401040000d014101c0c0c001d0300c004104000c1464465180840c10241503c9081c3d056103854 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 650410962 1250 650409712 650409743
    0x203190c230a030f2a09030c0909060b010e1309211806090e0609040f0b010b1c0b030a0305300411010315060e0607050303091005070906090608070e03030304 69
    0x10300c50021982c440c0030052000198030b036116403c180300e4404214000c100c4c075606480240c810a611006190300c240d201c03508c10b4550b030320000100000320080b102c0c189402e41142003507014004605502100a280d00f00f5000700c110740002801400204039400c901004d032480100380c141810701d120440c50750b5103004080c44405030311800316103981b101c03007800081c5405210344100100c2d0f540d4081c1e01a10003201c20384036454030030025600c024018010310310400c00030a0280010b002000e0390041c0400c2510541480131801c001c60b05840e810503815840400c030f110001340143d0190102d030b0703010050b8901c40e118180480e030307c0c0010710b544101c400c00c13140200000c00203154020b44c1550b40c01c0ca0104040030310a0202600d050381c600a0384180a240c0320740c414030b607541c401165101ea80c000e054a4481c10a401d0690303441c14568162580c1c0350414000070980e6104140881c2107408a940360304820b031900400380d4070058040d10100401465941e40404c5440030401140a103215042858002d80d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 650412212 1250 650410962 650410967
    0x13020d1d03120f04030f0f0c0204091a06120709271a071e11070f06090509060303070201020703110a0e1609080c0105040314030c0a0309090f0203190c230a 68
    0x28003d2803035100d100b00c10309010101c0e81c13001081540400310b09010340343c1401d440068481d1034010700000d610030f0030308407200c08000c03031010140c0402c01c000f04180c071651208010024030540e8200d0141c5142e11400c803c000780242500816805601c030f019405c116000703004418003001d0312400a8070a801466901d00c8203c0d003011556920400134500845031452600944d144002d1b094104420042c50440c40d126001c424003021008141240d00040b034140d03682c03009014074038035100300c5204406c0c800003c0c240e82008004c07148400e034160702038060a800d41e078501489294513080580c010451020100f0382e1001d07a29280d000c0c1d0444100c0c2083d061500368018507031203168104048135082030302c0014150741c1160640c0e0641b035002404100c0344000c0f1030500d185014001c03800b190ba11500884509260300507180c10241c85c4021414800c00b100b039810042a4841642c00c2440c901c90004528004005035004010313040381482c1541c0030001c8290300c0003044040b00c0300b04100e2040010704401d20394 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 650413462 1250 650412212 650412247
    0x6050c0a09120b1f090213060207080a020d2d030512160f0e030a0503120601020f06090303010b16020901090c031401050d0210020331080a0213020d1d03 67
    0x2c584120450088820380d2215028000900b4400401131082d00045407120b2404020010f0804603401b191a010141044803940006100d1400940214000801d0070b035408a080c140c895006441c60026002d203984d00000d82400c1c8050380001e501006031740c00c9100201906800300c42c000c4c1e0f1101c0c2c40710151a00d80003034100240107240d0141108503a0343c500c0f9002521140e00c2009030a00302d00b40d10101020900b01488880014594000018440001c16545002c2400f58200303a084804a4040c090010b5a802e429110070001d6402880104500d12524000701110402c00200c00549032807540070a000c41d00a0304a008040c2e1501203140c040d90745481b456100e40c0680280742c0711540b4103800324020340c0300c00714041e00500c40001c01d2082680204100c61104022045000c0e4044060342d110b0b070301c8801d1039034207001d942e01450000307196603000921b51003c0d60000c0c1012030465002c40d009000303511101c0800c400c251a800c52030322409805501000c0e502c20b49000c1d5945140b00e10700208400c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 650414712 1250 650413462 650413469
    0xd03180b0d0218041407080622050f01060503010f0b0d09051f0b06040f0311211f0203151e10090e0622022203050a0c08010e0a03031806050c0a09 64
    0x9a00d055440700312081c441124075001b10740c82c24a040c03243c4940c800329000d601c0c0342c0c2110003030004001072100e000e001540241c0c0b198042031405d140590b05c80d0f00484240c813080c460b04e560f039008803100b17000c40b4543c50f00402c0c03684014800001c0d840000d51300d041c00e0402148032148913074503807403800d4091441d50158011a0808841036450b250504a444d05803034024040036180da00d54101d1255a0340354003d000748068034040c10408520704d07007001c4a0b62044100e00200007200412400003401c3c0190003030300d000701070000020000440751401c0c00400100a16014052859201d80301e425450300b52a1120810240e991000440e0070070705c8000d10a0f4002e0900c900800210450310721031100000c24040c48440c0800269440c60548803400143e03804195206083d9000200002009400107000440d00d100300324614a650741d40444a088a40c401164042500070003403210009103e9800150042011801d03d02c030007081d602c550f4120742044603c0140300000003203d18030690000c1c80c50005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 650415962 1250 650414712 650414719
    0x71b080309011505181305070e0910180201050306041b0203250f08130e181603050601050d1b0303090302150f09040f020c160510020601050d03180b0d0218 68
    0x34940f8060110391056907071038400d60317034030030b6880490014070a414030980d13415003120031980e00c2500d84036083c0c9000001c2c2e82d07030440c502c100c2d100841c1c1c0c240c0300c0c0940c03000300028022001a401a81d00192000d920040203590300aa8134205901d05640000c4002d09003c8140d000b0b5443d5503c0307003c90b0b08a00440d800d16089051104e455200003548918540003140e80040529116003105c080d243c0d04501d250425031182031003408102c480001c0d140f400c03400e92415000c40f060000109003400c24005c59020180c41134001c00014455410464403800b50544544074050b41c4061003035201b00c100007217030002c90000d24182410825450650300c4103054800c1c0c84102803401d404001c0c00841481540070490080b9110400d40a141d0880c3c0d068075512800c41c82960300c408007415100c0394201c5280502845001d4000c045c1c10004c0c40050074070305803131024040040c1881c1719101590203c80d510300c48000d186046101261044502029140b004080302025890b500c81c0c0d000740e406425000c0e0fa00e0702 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 650417212 1250 650415962 650416001
    0x1020c060f071b0c0b0f04030c090c03051e01090506061608030601030617030406231602040608010c1407060605100f020105060402070809010e0105040504090b0901060905070215071b08030901 84
    0x124501c03020704030484440d045c1241d0303034091040c07803080309004591018220420340b8100148070701d25a00b242005141c140d03010442b0755070700005581540740310b883e07100304500c501006001710f10480e84031a0308001e004000c5824503481c0c0716440c1a01c0c10740e90044854120100c02e0148650305401060f028100d00c80e80e81c1c1c028600e04a1080d543d009034804c1c01e003004400d4000e42c51860010180d0190320032862100c40d43c803c103c1c0802c00505410322000c07405917240c80000070b480349040c45403900003009903492580c0500c04000702070711604138060a03104c7d160341c1c80c1d002030140d0b612080f0200d0081180c03540d000d100d0003082c0103421254028031060146004006610001c7d0b80c0d1811500c04d000f00f420105490f84030301c1c004a4040c096234210780d421614105c070010500520504851042c401000240a61a19480d0707107400d460040d40c0c58005a800082000b50b0011900c42482e4000c0036890720100340380c04800ccd042c002c11100b00c4259088400001070056110082c01070240000c0c0c081090344 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 650418462 1250 650417212 650417267
    0xf0426060906040b040602040e09010e2a130608150712090308040f03090e010909260717070602120403020c01020d020303010b13090905162403090501020c060f07 71
    0x16202d4070018001049102c403900050204611340d41942c01400612100e10131500d040030316a8028203c03844070217118824108000f4040a480000c081a0100b4044082e580e41c0405e0a0085080e080d4900d65440381d100c49012130740e010308114030700a400581c1c3c2d111086007001d2030050284040c50600c2d01c5507a00300342c3c146000c207421140083e005540598101c3c10207415003402c86d00c00b20150081d4000c20801800000c4030708064100203103a6018148400c048515081900c0c80c07105400a041000c520921100004c64103100c40c4200c10b02d8440c00941c500340582c0e6270307501240e12492000700052640b100380024141e042100141485080c00104400100c140000e55240014418050740c03480c00640f488080e0f4502201038028158002c1c10300080b03515282c0292034036881da05201d818100e502c00082c1a506e45200700c1034041940c01c00c3e5900d139544004c11805032140000076100c039074003081141c41c0d9010800c0300d20b01c901c00516841030a8200450010700c00a004480d0a2002c2800c074020b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 650419712 1250 650418462 650418481
    0xc270a0308030702010b0405070905030f030903070515070501150e0109090f110d0c0e01091103070906050304030912050615030c0612061f0305010e06041109150f042606 74
    0x58094a82101050740c5036030f98010124003402c070860503241c0280c1014203024131150009401c00550318210195518600d0803440c0503501d0042904071076240e03002c88410449400d050b8001c0c038000540c1d0020520b80031062722220309655070b031514081003e0070303460204043c039080d961883c05001d01c1d00d41404141c08503258009034480c3c900f4054003207011084401b491707a03107030725100b00e0081d40410340301c41c40f9946440c8030456000034810201103509000458400040c45804c5a12684079078658001280c1046401c0f5069040100700300c003480a08200460200c42000078042198410001859507182021100c5045c0c860348a002d130095000015510855803040b003958108103007052402020354070900020301c070000c0b10300080c80c0c800550301c541c109a54180c100f18140c5030036600f00c044584600c4140800c861441ca41c01c3d001180510a010181c40c0c09410014a4070284600505107178110000c0c1450717074000d134030010203003580c8030f550604004003145070400040c401d0007520003850b10443e01c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 650420962 1250 650419712 650419729
    0xc0309010201270212160915170a14120d0f0e01020f1c14090607020d0c02060703051c060f180216030f0c0c170f0109050c010c02030102120c27 63
    0x9209410105800f0003000c01080340703000c3c22810b034175008441550382041c940102100c80c81d00b14220101d00c80413848400810300e889d003220601c1d000f8031440c0e806d5100c0c0c83c0c019841c0ea041c0360b1903003c1c25400030704000f03005025100500d01c0c01c070002003e0000c00c0d1030108682d41c01c094204c090340148000b210305001c0805a5041841c80c00748090301c0744241d5002c600801600429000300074003502400b011074000100d003446240715808544090081c0341d82030303440122600c00298030110812141d400079100b80c0180c0300d88540303d14020700c242c03c04070302e19058810ba030700000d02d083c0c5502d901700030409145e44c00348010040701f0390031460045680d4600782a4020100d001e41884003c4040030325440c40381907001700a607002241c56010350b803103940b015425100302414075028400e04940382c2d141101031155016241e0301c44000c092842503030b00151001d500d956401c0c1ea041d5424482c03080d0304000e41075014810f50941c030300e142d41c50340c20490070145031030000207000100c2c0c4100861120758446220 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 650422212 1250 650420962 650421041
    0x605030c1003020403050601030b0624250c0b130b09030304091e050408031819032f0c09180a020f04180b01030210050a170c040b0c0309010201 63
    0x180d6114198801c00150041e10541d0301c01095032003210300005c14844001030450090748101c0d4000c2180c0b51049401035000c00780c80c0e00c40724034101004040c2507100c031305a0740340103a0b051040402c0ea000300b6407611482c911281d441400001d00c00150400c04400407a19440501041c0702060704000c01031011983c1c034001c0b40900c0054075980c1925440e01d030074100e0841c02542d9020070500c1645001e182a1041d608143c41c40074007000408091020281d01081c42a050550200704030b040c40c0040e14101c1e00001040117410014025070501028030ba25600e9170000411301c00c004108480080c81801000c2c88010029009100c0004002c80c018601040300f452054040b03808180303203200000051300500b990f1444680403a01d4080e040100407440044504980c02141c5441380030640340c2d0195094400c007100d202c009030402c80d072030048a01343c0f1031094020b1403800315141090b403243d200800c00d0b804a041d0080035400441c00e5400ca41e424002e0503a0a80c0c8410104041d2804d1440752217001800f11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 650423462 1250 650422212 650422219
    0xa03111011070215130b07020f0901050f1005091504051c020120031603030b090f15010c0819090f0f0b0306040c02100606030207170a05161505070e040c030605030c 72
    0x5070140c048904040550341410030000689140e9592583c0a504692120102328060341c440c805d4070000e0300c1e00700c42c0c040c100d4001070070240900883c1e40400042c005442107600c14450103120011a0751200005183e54120b00d501c3e103075945051204200381003042900340022070307205905400040c2d0384046240c40b00c0401c2a403401e80e520015107010700311300034001c8601107501e002103010280b5a264006003880760003644e8403225600d4400c10103030703c508100c035010300e0002072003034039150740d48500120b001c0c40340542c00c03050030941c140c01d0003040c0b40a510b03609400542d007110700740040003540080c0401810a10000c041c881e00d00b010201003030100a05051040c7d5558203803405141c002e224940b00002440c40c10012240c4079030001c0d00079044010166240e4010003400c02c03520307954004490384542152a01410041c6400f079100c00305107140b404840448801c03140160000b0140510740c080c41c456103440c042007080e9820300c4100c2d030a00310f6000826003020b4041040341c40104100302c2480040c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 650424712 1250 650423462 650423479
    0xb10030611190f0c02060703080a0b04061422022107050a020607030911031c12020c030d15031509031412060906030f060a020702040b031203010b13080a031110110702 73
    0x4094071302c541e075030202070742084000400b0020540d000011500c1317540c0200041180e80d0307861040c88221010340c000c1d0681c10718040301143d280d10340654624280310940c014552032260140f0200c0c00d0340c02030110450090420300705d9001405103400c00a601444030b280c81410000030f48c5c07000350380c0c4101601e0700c0249036462000609200072600d0a8218940282c1140c80e02810043c0c8652030740b18000c01da800045003400c00508020150085841102c0c3c031500031410004002e2900c2d00404c80030003060603900444d0740000004214081c84032110071003280006030820141005403580c1c0060703500c00c1c1101002c2010710041c01c11045800e4200c81c003a01c009840340e480801207850400240c0c12007119100d079408000072484190000e042180c8240c0301407003110240c20625581d180d04405c2c0d0803a10a0a200500440d808038000d88050103500b550340011999900e10a820700038040000c2d00020125041448203003010001d0355180d410b10401003108a120060400079401580002407084000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 650425962 1250 650424712 650424737
    0x3071502090d0f0c090c090302030304030b070219060204030201121b030b040b030312010302150a02120703021c0210110301060507081b0d20032803090b1003061119 72
    0x25010b8020582d54007000140a030152801e098a86003100d00c92407460714100401c01e82020312945181d82140d9002d00150300342420341da200b852041f00180352008500c00c8101c2e0023030b070307440c00ca1108800c24000d00c40103a030b690650000400c1d1801c0c00141c10394581c10842c1a01a0a43c1e000c000c010110310361500045900c264000500035000b0680300340e078144808100c99540d9150024064122031003210481d16400101e9442c803014000d1804100c09030300807a0100b40c95950600003400d48a20920642d140c4000b4540c2d4a107031040f0042070400180c0c010501580c0e5407400c0d01c91000c0240103070178560704540c50084000d000e441507100081c82d0710070120b02d0204002c0115101340002214906407032404000250041c024110079080503807043d81d10000b00090380c4d010003250005501c140380d090840c6144a22030000c0341051680104040da9012074001154100b50124040c00031114860f82c2d1510314102003058544100310240104010000340c1034010b0740b291480c9030305583c4e0404210b288007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 650427212 1250 650425962 650425969
    0x42004060e27040f1b210c050d170409050612070311010e04110c2b0804020105070f0c060801050a1d15060c0d0210050f090c092806090b030307150209 66
    0x28407200203043c400e50081028030300c0c290340c1c400404d0343d00d0300410141541b03110003840c4041081c40000b80c900d15401006202a0908005985920340945180b90500d00d0600c0c11100c6648030f603209480d559560401d100441c0b0303101031403150217204000100702480c10364446040360404454901c1c1400b9041c2140b50850b101d82d0091300841c0f0804d20220740b50601441301584138007500e030180c1c5108012454501d24000240d500d10340ca10001e0380c0d0611241d58990041d151a0711403d802c1d2241001c812052002540003905400a4072490f5184d0005501d17000500c000e00b511500588034108003030b1040daa2110a8814090380712540300b0403050302d1510710012421510420100e820341d0b0054072445000550001642c0c62074482c01841040f441e99031000052481c2016964544d5079041040c032410343c3d14010b40c2141c2c20034003000e1504014090f100111842000104c81402150345810b003c001c02d02451003040d1000e4020740c0510b192048941d81c00070f1180e42c3c50111245294042082601902c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 650428462 1250 650427212 650427233
    0x114040b04021210060810050103020d0b040218130204081009030905030f03130b12190b03010606080f0c12130c150e031612020d02042004060e2704 65
    0x50060821503560030f078840075103000e8104454451200ca903415000807040d100e01001c510604000c4002c1003039906000045000e948101005001030352142140b880960312480184844070030142413255580e0b1440034000c3e000400b1030151905841800104002c0101040d5001d80052480001403519003500d000d80d07804485820464041c8100d008501410780c00000410610140361006801d041c0d4540c20303030b10b5904c140c4141032403420b0000e000c2041120240c00c0c14804840c03007038012840701004c0000c28219000c1e03510000020b4440740502c54481400c88211340c204d9806860076260040c035410504e07036030342d0182c0501c1030984034203c60420b008014030003a02420300c40e00400000149000c00826007100164074078400c1c024091410310780c2c142d0516103021a0341805099141501c2502000718103292014180c0c0c20584840000c103860320400510b842082d040c1352421740342c80c2001c4000300701d0585034652a00400a80000b810031041139148210411103d00c801d2800e95503500d00084400d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 650429712 1250 650428462 650428481
    0x403140a0c0f080c15012904030609170d021c060f050603190c0905190e060d05120403032703020f040e01180303021e040e1302030a05060a0b01091508011404 69
    0xe001700d6200301101512054414104c0300303401c001d0250444400411416102c0003000d61095442c1040100005039803500002c180ca8051501c0c45000c400c100184031003941300e0b02850000b9a80015161120240328080460541422100f000058185407a50301c8862070b07401241d00c00d05011000819071030481c03041d07507070001c0011000e0010380c0c184007001d00389260b5405001e101d8805010058002c849441c038100c22103202d0f410340207250f00d40c0d4041c000d010300e80c0c0c1004d440c0380c080d402120a200c9500401040118440c2d501c00702c5014030401c03c9007280210124107841c140003402c0400250307490b01941020007604a50019401c1550382d0242c0c0141100b84800c038400390f000b50b4020070700d50503901408603002002c40120000c0d22100c5440d01c28403c03800303040420b56100340440c001d5a038000000703040314805000c03990500c00a448042c94450122469502107030ac0e107a50150300c0d64010a07640c0242070108241c041c240c2100d0001d491400305004140b08400a4090740c08195120f40000d00d64 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 650430962 1250 650429712 650429737
    0xe030f0c100503090a02211b10050c340e0105040b031506040c03060321080a061a0d0e0a0803040606050f030c09070e190e0906011a0c031e030403140a0c0f08 69
    0x2192031115248071542600780b1232500c58842c01018610980c020b50895403200c9008029007002812644c90040341182034031043c04508010102d03401d00c600600100010f00315140700c02c0115071400040000b9a40b41500c858080d0b04010038003031884200202c03542d0032100485020880790500c0c18120000c20241d4009454458860025416092414542e0743c0400700c0c1d5641c03040355070304e1540344820b0f00e0082c0304554903000041c0c80344010100c41c802070003e0214480c00480d030030300d03950301072072410307250300790030741e1b02c00000804c2c00300300005031140d40300030b0034103540290015844500103031321105c0891155000ea40c002c0002960984150503084d4046001085000c4001d00700700b010842c200c0c076019142224035040040b90094a00140b00f034100c45226400050041161000c20a03d80141c40456494407050000030202d504080e10b001100e0506001c80f6228980f6007030003000341d902c41103440344a030010004a60440e0784245412031058002c28501c44c3c03e6942d01c0c0614940c418030f804c0148 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 650432212 1250 650430962 650430973
    0xf0203010b0304060f0203010f0e040f0b01150e0f090609040c170d2307170c01020720100504210605090319110304060f0e030f0c100503090a0221 64
    0x5940030807101441c060b50044804001142e8007400348004c80c442130107190a604d01307503541000b007444e0350440164054850321002451011642e00d10051800a810038440742507400103003441c0503840003040ea404001220901e00c441784100c08605102000740046015900c2000058240540c201c440401803003011150300040c11341c1d4020350384810720480040001614941c00301c24000c1d949000700b60aa88581c9124030740540741c0c1d200c03462801000054000c040301445115a42002071001e07007400f42c010004481003120040c5c06000031030080034224400c504007503191010a601c42c0a88003511450280b055840f1001039112035669151785000700388505140400030403480c0840681307038001080b000e0300340510b01c068080e5017802509040c40c00c1940300344403c11019124043c192080c0071281020601c400341103021900342710009103120041d0740204078425907801c1c1240c40800c4030545150060850a01098040e120b0070007540207442201d0100c8000d6502e110b40c28100f079017080034800c858 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 650433462 1250 650432212 650432219
    0x51c0f0803151915020f01151a0c061b090d080d050610081504110d0c02070503070303090306090302150112171204060c09091508060916030b0a0f020301 67
    0x1002075104440418100180509807190b90501c10807000e0004080c14560312101c0c01c00c07440550190380348001008600c14085d003001c0e0340d0020b1041441c1410f118401040c4035041c2030860002016046401c1c090170010441000c07000e101090450700510007a0354a1b0180c003084100c4000c40c040d20700c0325035010356600078407810041080c00804d40112044000e100750758807074040011850900c0c6503103010a0b9044001260941c603040f45c003408680041000621060410302d00ca11600702135441c29446035a440049102c80d01002044001e01e42200100955404d680e40107201810a200040545450f40100b0301010b0080c4141c074191002d020200c000c1d580d440c07008010b403040321902514514403e40f802e404020f074010443d000100130080224994540b43c0d0382900422400400070200041d214010070fa104850050007021780c00b50400030003c6090000311402c203040901600307040d80c01130360b4039441c105c02c40c1d041c40700700c90704150004102d07681d070310700c9002501d042c41400030440d10000020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 650434712 1250 650433462 650433473
    0xb0d02090f030105160c0c1212020105160207030b0c120415050601030c0c140a020603101a040303170903091c0303140910020d0b040504060914060f01051c0f 69
    0x610100a0846854808414400501d404c03260191805006000b90515030941280640090201c59114031a0084210b6075000494134031010003500b20743c09000014005c00c86036090050130f0700804840781034207104a0188020b50f03602200e01c40141070095450010310120440c50544500d0340400061100f185007614100c00982c1c8054000c0009529010100b0722039446481424240091922a000f41401d0350700d4000d01c0521030750030302e1058810070040100503299040030358000c01061034540101800e00ba03100c1c2c10050900c0c03a810440b40140702c01c001090744404031001c0d80e20b102c007050741a9110141d4040c21441001d10310f0740c204031804400c042c00982c6070b076000d0780d01e8003c0d90100002d40c4d01c0315401c1c500c4038041d40c1c1c02e03146a21120700071140b24039a5000702407003040d032940003d0349c41c001000b08094500131902600d034169a40f1b003940038805004186407070a403029016021301e1501030305c00b000201040c0101c5000e031020034002c01e0100348480e030100386903800030f500d000403003001c1c03800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 650435962 1250 650434712 650434717
    0x12020a0504060f0602070603020406090521011d0c041e05040c0e040b0114010e10050c07090509030406020c1005030a05070e060304120e0303070c0308070c030206040f0317040305250b0d02 82
    0x1301c40061003010000203003644a4420341d030964080f2380c1d42030000e900d420208900c146000d81007000d24030585030091401d000900c42c410f0b0500c1400352402800b2043c6103058246540510700501903810200380b160b414100d01160014000d40b002c00041d035494a0405c002042200e13040301008e030040300c0031312040c4040854400c0c12030307581860984403006841d004441400313044503c2c6400c004031a0309410081d020340c02509044451404903452181d60304c01003000d45100340e070151583e4000180502401d039043c051a04503510584000d040c848404000401600c002040818526940e00201d608035200721004402e08500401003a101c0c02c241c02d05440e0000441005004070b041a8003444040c140481941d00c1d00c3e400094000c1c03110f10316112131aaa80c00000c0458035045c4690300400180e8a0074040d101600c4110000c0f82200d055140098000500010f8691644024032007000042c03800074003880c3d43d40e01d071110b03a08040d402441c030005098040e005030310314030300115400312090099801f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 650437212 1250 650435962 650435969
    0x9050114070c061a010806040e010f0c180506070c2304050c0901020c0307440304080105010b040506090402220801090302071d0705030c0403060f0203010315110412020a0504060f 78
    0x800c001c0d11131013041c11103a48113a607142501250750b00340000d170940790903441440c001080800102d400c0d28803c0004c001c640542010801140a4886220f084030442e02c0e440081c110a46170b1514014503900c40d260400201e1107040181000b8070701c0102040c0100d03840e4074003940c01a00620071400c3c81b00d41d8407465089400074600500c21450141c65519000500d0380c100ca070088908a861008441454000000aa8165407c1e4290780c402d03050038260f0040d880103465050051a20b03a802c3c80c207800e09454042c1d002c210070040074001030042e0360b00c0800b00d400140d422200141c0d2034220f0b4011000c001d103813408042099640003c00290b0b00300642008100341e20a42c25610155113941d24038044408007100c1500480c0c000e00001c1e0b0702c500a5000316004461002040d0500d03660745c0e0303410250780d000c484440c0c6054008c4010420003100400ac0408112040400c0c458008040305480032800717184038100e00e04801d40d03110300c02c0d0344030082008098030000d08180300d026111141005029280d20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 650438462 1250 650437212 650437223
    0x204150c140d1d030a1407031208060303040501110c04090507080d0201231e10060905030309010e010e0a0e0c0406021c170709150e031e0601030609050114070c 70
    0x7100410000d60100e009040004180c407075184404202440002c50712551441d540c0610030644080081411800c680071142404001810101d0440c80c110802c1c3c00386003412400c0c0301c810b02c00c0c081c00399000b105682c00c0d14020b103480706107443d09021491400380d000401c0c0c0d400510b455419001c2c404041800c0003500c44000407144050b4801e5400c03403c03280d10072004034460302185801c08070f61104a80c02504082e03900082800401c200d41001250101600c51400321940c46030100a500e800c02c1c1c03480010282240950300749841c0b40c2c00a07100b03600c2c140281d4104031580d8003200c400d82d2000070290240c0780b612400f03c1903291902d040c0e0303003541c024001c28000d481502031080c20100c0f810712100c202c140135aa04504a00032807164814030314090030744002c2c80300b0f98501040380c40c1103c6200711050115902c00880043d550181420100446003074086031307a048110040750400060540e044903480200015640824100707640107090004c2141d511602020070305c020300e070f400b4900c0c00e507560081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 650439712 1250 650438462 650438483
    0x50a02100f0503150a0503060c121608070e150c03130b1c2c01200c0c01050d02090d03050a032304080901030e070f0e1b0f0c010204150c 60
    0x14090314407000c0702031074600180301080054014001905016008080a0482020140c0340e000080c2402c20031291107c0380c106c00304840e61003001945a0982100841032061000d80494100814840c0d00410180038040700300c5059410303803543c2050386061000102071f246ca1b24080d5041d11740b00d0b880b4154404031038040005c0429803c048004864003d4080c88555400d0030b80030b02c1400c080c1c0081950b000c0501100249000c641d0380583c22800e0781d0b04640000900c4483c10071280c03a0424030103982661400051000d4020000c00140c0c0c080e4011003400c0964032101c0c401d24601c0607215403020641c0144c01001c00e4404c258100e4060404403240e03880602c10030700c0031078118100c0c1180400088800e81b9060118010441c0030004144040701890b000c140c48030704016007031800d0300329031003103605400202040041500c2c0d2010190001c87e0b502d0603107003041711001d00c10010f005400e4007045400b00051010140503003541200c0c024505120010b0030500101006011414080c00541e02d16400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 650440962 1250 650439712 650439739
    0xc060a050d2a260109050103060509060f131b0f08060109022d090406060206160e0a0e1003150207060606021609050606041a0a0e01020a051203190504050a02 69
    0xc0000e101c2c0200168122880220a108022684403260a06410404040e000d0081c400400d809440c1e02828050002261030b51444c41d2000440304002c2c000302c01c540006090140c070700d0300203206c190800364040005180061701d00b801c204801c10805000403001c144000010041043d041078400c0324015400d603402e40c1c1c0c1e504588405d034810284060880a00840c00c0346101c1440c900041410190185c0036003000c900e800400d085a80076001000943c3c8020100640001c0a60940708160018030303040b40320b48443d8011452040031070040350f048541d4100054a21030321455424000c40c0c00c4030000106a600c1001e9100950100b0b4060b1069810321002088032070000604010340002018000c4c441c40ca001d08500080401400c0a64400d1003000006500400116a080000059042655280354601015000d6424400742d1410f542140154402140001c51500840201e0604065480d9100040402c1f0382810880d26000311f890031080c4424080300241c14002d2034402d5544c00008501c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 650442212 1250 650440962 650440991
    0x140705060f070f0507031d030d0908120c061303020a0b0a061406030f060d08040506040605040513050613020d09021206070909050c0a030b04090c120614071d030c060a050d 75
    0xf008106840859010040300f40000e1040c0352807030010b51515a44107183d488100001c2c03d0006034900c580c0091b014280900140d5028004824071f807180a01c2c5070701c2c25508414080d114000100b1700b42d01d601d5404285e0341410300071301070704109650000e2540d00f50306d00031482c88010701141c000c0c20790300981a6041905400c1000031240580c1520341e00c4015640c85804016508040c450105c484000038800002c2c1b6494004c0074101410300340d00ca0585443c00d01c814004c0c1032800c000814201030a10007800080e40b113120032a0003c291400001d640c1e2908507041c0009007240110080d0848a4045100c120060115100f800303004540c4d10742001a60b10703110101034600650700c140714080b0801035000c600f4020f42c4500702c410300242c004182c1050300c3e210707000a04220340c40358050001007202001006568440c81840c1c5007280641d05d5181000c1c50002d180700e551100b0030701c5108140311903110311781d01040a4414203000408155550414001c01001d540140a4402c101030419103110580130 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 650443462 1250 650442212 650442227
    0x90b0d060e0c0a0e22150b0d0f1b050304170705070905180d0e12150a020702011202040f09050c0910021e0f030d20040605090a050102150f07140705060f07 68
    0x1290209480545c40d05403260001020205036080e016401c02400040004419000e042031800c4018001501000a00800240c945c1d401118420700800128140c0c4603400500790fa03006a08040307032103103045140068078101e20035031001408a1059201c0051524031907082548240301a40d01070264420400b005603551010003110340c0821038440ea07010503414003680b180114600c050032500c10142010085848031070545550215a40004007002036581042090391002c030249400c40c03515203011254011503405d8011034909075110b001107000c007041c10050301c0c521403000f0446c00d050301b100c84000c0d595510a1940d12840304084c1c1032041c1c101408599031448104101c055441c02ea00e00c44000010104c001200c132150b034402c81000d04042c1e034203000e08041c0030207071151640c4500d00400c001c1c0c041141d5000d030f411580041c400f4400010210b103400e42110241c9020700d52a200c0c1e03007066481c207500c03d20043c076080010072110213210703000581e030b030207809806001c0d0a26124400c0454000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 650444712 1250 650443462 650443489
    0x161e061d070e060f120c09010503060411060706020c03031f05040207110d02010329011206082a19180c08130c0e01081b10090b0d060e0c0a0e 62
    0x103801c001000c0140100c101c1009034030000007010681201311200016880217101c145441990b0301c5459001c031541403952071603015000850040610345456612584503221a5890703e0140c03202041c5d1404009550301555000e05c2c1035000d40c0d41303a251030310350fa4003000d5410a403180c4004060764002030a007402d100300c802c0c15030403001e403684c9005400c003803003c11031204504a040503502c5903a007405480071071030000a04245856911100424400141510000010f510240f440c1640401603c4c1e0005130441540d007a4035209030f81344542c0d00c802c4126010006405030400100c00c09082e09401d001e4404050b107100200d0003650104c07003c13400040320000140100442c44840c00b081008100300c51440780c840c496000d0020407516041d03c0c600c101c0003a0700440c0b2580c024140025004030320141c01c2102181a50004c43c01460480001c1c54103625104542c10707118005600d13075000d4110380228001d00340f0034040d0100f900b800503c0e416940e0000200703100080d807071400100d01d0700d00010b000000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 650445962 1250 650444712 650444771
    0x15020c010e01110a0b1803030c070308070203090a1202030109050d180e0c09090a0e0318100311030112030512090705090a0605010c0b070309150f0c0e0d08161e06 71
    0x80c91160340d17a4810030340000d03080000d82c03500b2030600c18400a040004620070f40780c01d107030141c45003201e2401500034800a4502070a5410512018203a521071081c0d0303c04540d004044014500000e001080c010241c8010203000b9000702c4800d40081e68200c401c4144a003071841001e40003e80ea244244131540054a040001810411040110b0718103180746540104202400203240c428400c01245076038400c03a881c6101500c81c0e008006c807441c0001007501740604900f82800780b69110300500c800380c07005000d11071070000826402e5041c588508282c96840380c66906640103400d24480d405e41c0e50381c0c2441043cac82151684001100210b460140c0e004650068540040b0040c00da40c41c00c0000c43e0041c05201019510800c45021032540301004a00341a42c0c0000a54950005129025281100d400c0824080403565000b51030b115150400f000680200d010f0343c0703c0501c001200030313681c0e0101000c3c0013650500c4020160903070840c41040820300c00c0c0000c0208009071001e22a4120b0700002e400035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 650447212 1250 650445962 650445973
    0x19030b010e120d0327051b090601020d0503070207032003061b0d020912160e07020109020117040303060b030f10050d031b0c0f030f20131515020c010e0111 68
    0x64060017908000000484880000c070801d45031040b02c10560f6010000340c420b0703804640300c2c0c1494842d01040d110641002e580c188228a80480003035990503030b80d8440020010008005808980b09108000240d030f800740707801d286035803d005516501d00d20264007d00c02e000d90000b0810809a04156620003004240720070b00745900b8012000c001c0d0801012903070810302c400c40c03441c6c45160500500303280b00c854040e9400454100b81c078013102400001e0000040d60324080c250f80c00360b070f00522422030002d00c0c005c2d0080d0686c1c42c0d00d42140541107d5008500814001c828000c540f011203607210310a44409101c0051165910100b10025030741d1000036002c40c9410151103a05612261030805a602550902c0c0400303030307151049403443c0c265910035101309240c115200c1c02c00042084c1240140c0d5400c43e0500c0034a06500000c3c01842c0402c400307401d50703650b09101d0404000c0c0b90720050003011000c103c4481095000406900c07101c80310100c50010f920f100420105601540540c070081f80324400500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 650448462 1250 650447212 650447233
    0x105040510090f11032b0905040e07030803040c05040915050f190906110d0605010908031201050d050a15090201170123060903010e0a02010f08010803090d0819030b010e12 75
    0x2580f610101d001d40e011300480c0f000034a0120084003018031101301b105c0c6480a04da4102004100540a400180c0310700e05022000ea21f8000000b2100b040da034010000d40d46c2d03a00d40345443c1054103416402940c01a003409aaa001e07c0062507008102c4005c0a005120a40e50403640081c1e000303044984846880e400364503004503641542c4852500c0d4800c41d00040c699400804103207150f086400d40250140d1a88001d1129592050a8000900c1448000d50030924142e04c41c0c07a8412050240300e0090843d0a480d00500208000c0100d40d08e070043c0000712105518040c50f005003a40c910180c5c0851150200d02400b2411a0b044034100c0e01c0d02c05035590703c2001c80034002d6600c4482d60a05c1c2d03206509125540803a5420b00c190700710010094001c011820b200d100142c020422106040c2c1840a40c03401008072040220841c1e4451004030350003440c0c110303245060a034600039800d801110032044103d00c0340da250980d0042c007001200b602e501044507800010410100f00c190080c01503500182d8100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 650449712 1250 650448462 650448473
    0x3080708040302190506101a0708070f060515100c02130c030e07080604140d020a0f06020418050603060a180b0714070c06090f0b07030f0905060703020105040510090f 73
    0x9030064428410b80d60080d40074081c0002c80501c44030159a9031b0005401d0240c62181012808000c060403415220301a4035007a80503010700514502414000002881904000b4410180803905a01c070f0340403c5582031945002e18282e20000309203024528084080068034018884154042d60003403100c44854044880c1002402c5420b818006050711203040c45a10b40040c003030300000d052000001c00f51031405082652000d40e02c084070704400c3d04410768090b000d5501160303005400b0341205441c078411690b0b180c480001e103c0c81d40b10444105030001c100c46001001e402c41405480202c044418503180c40d4a110100ea5050314001da60701d1003046408005900309480c254000050b05144404002c44545c038001a40a1041160045501802489069007180041c40503003003002981110508050500c9201d115685002c0e050040d040c0e1101c580034400c08803007011300806000d050302c0e04018500a40a004259401c5600c0d01030781181c1c25044460344100c50704aa04114241e4038512581c0301e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 650450962 1250 650449712 650449727
    0xa020d05160902070c0501090b04030b091501091b0206070c0609050705060a0503040c0b0a050a05181012061202030c09130f12201b0d0b0103030906090f03030807 71
    0x112528021031024420700c030060311007040100424400965160150314000e41480100d81003241072144200040c001400041d042e182503030741c0300c0b4a02d00c0e00c0d104d0b129020b203401000301103040d150403030b0400480d074825203401a001c1d081c604241c000001103101810381c0ca0380811600540040c3c0c1954940c00490711725048440041d01030070554640c6525400419440c7c2e0005000e9004030300000300348402c2145848400c001003040140742420700440e940d00034090b11514181c4c6c1c04110001c40c81c0d2044240010402840d0000244440c0d40c0c0d00c90910301400d030b01070303030b880e04601d4500d4903000103003550925505200c003541c001e0150101c02219820002c54150142059443d181501c05850000e840d41c0500d0300064017031900014040c21000f4000d103541200c180c0c01d6002607011112020841000844040c41103c00016000300707040705010484880140002604800e181e200000c141904070f02d0203415941c46954038000191205848415400e45200003000076000c0c82c001010948070310304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 650452212 1250 650450962 650450989
    0x5070f140f030406091208070203030a0f2c010e0f100c0504120506040c08030703080103230303010f0512070f050105070819030b040c020d0e0d21080114060403050a02 73
    0xc61401c008401d2016112074200320303400c0740e900c2d95071503500d400c0c000c040103803080c28952454840c2852a00180c025224040a07244010766030b26496403a20600e0241c010000303440c1140341616400c4c2c103d030481a14010407812008240d4070b0009000350501c000314403125030031690030007490300030708240b4900020311524010801704003080c00003003110300e04007041d100d0b10b90160f4010302c030b41c1c1028101025420b010b42d00044680d4410046480042d0300081002e0460360844000480340d0048054038000c506010700c0d210301400000300100342019100c9986059450a45101d0101c4400401e050780c1c1b0f0300d060051007010680c0103010007296220b13000070310800c1d1242419505000e500e121440c43e40c072a0f600028003007074488400003a1402d141c400c000b0840306510090158184000c0040c065641d010104c0b400f036550f811216050001502800c2054102e01c42e0311020717010581c50091040d0350a0144c8110481910200082d51404d107069405aa4011313024000024090342000031803161600d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 650453462 1250 650452212 650452247
    0x20607031d070509100b0706020403061406010e1212070c03050705010e090c0306041e0506041413020409050111031305070803040e132a03031202030c220807032405070f 74
    0x500458031b481648041c0449511819016031100e01b1031030206c09484d10306c3c4071824801c10300810080542e921440c41000510141d561510309040010400d080c208065140710032820700003551001c22200e04072800c1100d0181007031345c1c001ea495100443d8410444810242d0116181d40070408082c030702001940c001c0c400070000100c40c0b444586110203042c4407080460455502d4080210604050048a1842c01440002c4005280c01240340702c01c5030032884c0c06030007103988402020400900754071502240d602072140980300c0ca400c403034001c0c0b00c101c40c1c00122418025100e0000b80000c00200b40c0701070ba100c40c22401d00035a100c2c0c4ca41042001d0043c07042d20011504001c80355804d5940300e070074850300e03d84240c64503005d003141400340060611203042d546813481081004071025089094480e1303480035003503510088219600000050f20281c0080c0300c0740c019518000101300c00c0c0d00041000910314034524a00300318110540c000c56400300d0301c0c040843e060103c145462441040e0070040da54a05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 650454712 1250 650453462 650453491
    0x30c030901080702150f07030b0a051518130c12090f020913060609065301021309110a080f0717011701140c0406050d0b10020607031d070509 62
    0x8801081700900c20b65000703c100d00072100388403c8035803501070304018140544001012624010110700c4520910201290003c0040364184600c882520003c402c060010825450520650350010051055420940109001d0004421411042e004280c0b400c3e400c00441030141c4415000d105050740020618610724074010340a2001a004e0301c00d031409000208400280b242c10580f402c828000e44c0c1c6a42144120f8450082d141001105c3d4500d40c0103030700b40a01005d041c03000b107442d4801c0814600841e115400444c0d80d243d406204401402140c424900500c800342d01a0104146442a4840040000c0d0510006102c41d002185565003240d0285040403081410203544030540c10280c220f00100c6011084800c0910307024001c100f239450b0031031031100203030811000c410401d1003103105600621038042844002101c01e58040d601c2c40b44041c01001d14050310200080d00c072181112000082403401101c40703020b0304010200c001d1044a0b80042044508000070403071441030040508102980300d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 650455962 1250 650454712 650454733
    0xc09140609120f01090506090c0a0b0d0207020a180c08060d060921030e15010b16080f0307020c01270302010804020f04090f15020f0901050a0201060b0a0903050f030c030901080702 79
    0xf0805400385152010001407014001c1c40c1c520f04000000c1d110100c0e9900140d240790042d9110903400d42140c603070403011640d8282c1d0082035000ba02402c2c138042d50180414034001581110802c4200007400c802c0401c0104003616a010340f6803040c00d4503495084483c0b200c2d03d50000f04d8951050880901601c00d5004620020024100c4007401d02d0b0601c6c000303078a0301d60003c079070b10040001d00001d00e048042340c5402d40c1002c241c45000d021712501000c902c0001d400c4e510030700c080700341150724404080380f010f60b980c03030003c001a50310805803a129002031004141012402000302d00c80b6001001602160071135855030300116040000070b08242c2e801004002441d41594907442980e81040c89909504142041400d01010346200381404410303080c0100001c1c1c1646540c80c0480d2201042403e1298542030345250482c010300341038110100740080000c01d1840c0ea43c0005801c0120381c40f40080781c50400120a40030307101d0103000d118602c688d10a11403610598014203030203034031650703520464014240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 650457212 1250 650455962 650455999
    0xd15051605090d05211b010218090709030210030e1c230d02120421080c0a1101060801290303040501030b030f030a1713020f04051806040c050102010c09140609 70
    0x2528000c005d0751410005a030040485c1da26901800200b42100031401d00d0500c541640341c10031064460f91280060b500003802850260101d24099900070f09200204041048041c00400c075210014006116000c8024540c615070141100000792a9490503003110100101402d03040c0b000b8424840040c00384441802111070344003601c61200240b80c4a0840e003042d0070107011391103c2c03040400b600401f240f400c038605600000c20070303004a24080f401d42e80328200c820448080106258020041d42404000511914150040d044103280c035162002c403002c1003c02c40c501c5052100c042d41e01034000781f00801007980070381e10400340500041e050310508058042c65a041d03622a000384004141c0d03452004415908540240f07502c0400e010b40300100102540010351000c180000051060f9107480c0090f50011390308043e40c1c600030850040b01c00f42e09003407030948581000c0e801001d0040d840e0201e2040e0b03807440340703460f20101e4030007039201030300c02c13036240207000d140c0e170043c1c000907080b540c00c1184140c03804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 650458462 1250 650457212 650457253
    0x13170a0201020913051b030c0414060702030a1a131502030c13090c081305060a0b0102070807030b01080f1c113a0807021f06050d15051605090d05 64
    0x800030302c0001990b01d01442010180308406c660341c01451420300400c404840403500b11020381ba010303100c401d13400501e81c0004180f0f1081d10301c02501401800c100104121184041414486820080170910780e103182002055198030b800c05480c0203403040403071040000981c000d5811002d0610428038140996800a0000d071007a030080070115540d40d10703002c020707034425440d503000b00550380f131040e1b28007490b1a0903a8640001d80408485170f03403800b10744016802000340300000c214820941e5000c0d50360b410001c0e8015424402c40602d8000d0f40400c1c0e50858002c11070031001074032601c0d4003c1044100d5030031036004040301042956441820004040b1000c210090883d98003400441c0c3e072000514140c2600c1c40174007181d82424007420300d0500048940100d400c0a0210200351443c480c06a07261034140075004d507a0240b0f0f00034003d582c1d00801d1100240c00e8014522465205000d00c2e00d032082441d07030301d16a012007140042d01c144200b036100c0c034092176030080d002d015004032402a00400040003118 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 650459712 1250 650458462 650458489
    0x90504051c120b01170103120c050607021f051317040f0f05030c030109020102101802090c090916020309010c03180b0c0c030c15090607060e0604030813170a02010209 73
    0x2840382c26089002c82c030394020030603182c8081c604100201e0744503880700000312060200505c1c070092244e2070f1409510500300091441d4100e000c591482c20600e00c069125418020750402030851029000401c44032806101c0c0203010022a00303a0030746850b22500c0c1280c46084980c250001c0400001407260800c00d00d11000d0070510020010040c0340001701031030408004c21203400380c0d040008010150b80c0102d021034455608010106500166200b540c8881c0c2c00310340001d620080b01424482d03040100000740c0080175003910301048580340c505070300020b2000c030408600168800c000040c180e500c51603142843c20701c2410000a8010801d02051510805d5000f201d0071036004500e1902210003008664148241500501250103a810208841080c2c0e4800314031003180014070203082c1d469410407940c03000d8000b01d007000007200c0c1e405c0d40e80c4ca6a0095405800140709000403c001c22440c0081014030303a4080503140d9030f08a40818041c05802c40c2c21585c0565509202010040e00d8070004030110 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 650460962 1250 650459712 650459717
    0x13060e070501090603051b0d111602040b060c070311130513020316210c050d08030a0c03051e1012061b0302090a0614090406080303090c0415090504051c 67
    0x40d41e00344000102800c020743d102e10101030426062100b0041d1600e040042d00303110301d07501943d0703c100340118806010107107030003450485c001401910700c070324800242c18114422034050110032449020459140240414400290400801040003803540058201d18000181042d580e00c1c0d181d0141d54212a4120b6100c3c00b85c0a241d0036000031441d042c090510090b80c050380068890341004100c2c01c80c11101c0094103080e00d1070b00c014005020326000400b008002c000d144002040c0d140c80d14104a0300240c0b500051542800006c402041c0640109071003040c42072244803076583c1c3c0014604c403500c40604140040140600046490605101d40d000841d000c2c00c004140c0360b80340c5000110f0343c20702000003c200741c41440400c2042c0e80c3c2c1d0080c6400c0301c82e00d14107500c00d900310740c40664191040b01416a40546082c0300000e0050011020318800e00141c802d4515900c281d03414041a140c81c1c290b82001c1000749403090080442a9220700e0304140240201c80b80d0441c100f1101c2c00420303404058102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 650462212 1250 650460962 650460973
    0x9011701060507110a2d0f0f03050f03040303050a05070c09051e090c0306040305030c090607150c02011103160908060a0501030507150206070806040213033203030604020313060e 78
    0xd0001c4d010030904d540c4810b4a0b01001c25142c030745c0c0c0d081d0016081901d405643d56010745800e00380c50400d41c3c00d01512191010f001e81d00c1d40c1c0c0c5480910041a8401152580100b0482d400801c9020055800310307a00f507240c1c81d03c0c050116008403241d602c1070700300726040f0355000804503d0060354402d252099480e40101c01c42c08000801409440400610741d185d258009910f04070035440104036250071545c503080150300d0b0b07111203062540d28000d00c0e86d82c0fa00f00c44045000401d010000d200c400c1c1d84680260100304e2010a041c040b82660100940c0306040c06c41080401c860380f03004107040300f0090305403030701c42c0d5025159070350282848004d41e040400540c83d50018000d0003001c1c0801c00041c400c8103c130302c80440e1012000394a8100007004d080a22500500058460301e494044a0540440c007e180b4461780d142e1030400c52104d003082208151110310b0148480e031101c1201d030000c14a949400a40c02c3d41d89030b03003c010180d80028030b022040c00f00084110b00140e400d004114802c8038180c042c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 650463462 1250 650462212 650462227
    0x90206120c0310050d080403060b03030712020a03090b091011010906050c0d0b180708040f02060d0f0b060c03070204050705040e0a0f05070f1704020120010e060105010f080705090117010605 83
    0x441e0a01d013504128401c0070002d25010000758124211400c49078072080125590344105c0c0081d0070350103405400741c950010100e4000380f242e0301280c0701c50014480c0d1504400b19071900807010450007400c14054200c00e02d05e044131401c500405007102042c1c08580045825a01680c88809643c8103543e0600ca482001c1040308502515004040842c4003e40b08040b000c1c86c400d144041421018202d02c0c14480141e0108040c803502c40c01c20a03a00d038001c0e281d0381e0ba0329583c100000c01480d1060b49844641d162a0240e00075142602c00c580c18541000001c505100890302000024036000d0700301000d0120030000080e4404000061a10503048010000340d011b065014040690304010009402c01c1810f407607161025800100c0308802c46a844172203031740744d620740c80180c80001080c5640b1080c0c0f081a00c0743c9d540b401301500701c1100c81d680042903400c5030b641da50056419600103801140452110340c0002d01d07551143d07014109401052400000c2c04c036100c140403160f0a000e80107000043d13800900304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 650464712 1250 650463462 650463481
    0x8010c0e101403040b040c09020703080f0f0603031c0605100f0e04020a0804060b0a050301020309010c0908070506190c061a1c081602030a0b090109150204060909090206120c03 77
    0x1d200340300160030907104400004092a07030701d01c401007000702000d88100c086414050402410070113008000801c5603515030500703002e007801d0030441e00804104080c1c1c00180025198040e420300405016008500704114002d1001c212042c5000d0b611059981c2c80340041c140d80c1e0014015034807601501d4611168203491001008403140c01c49660085c0c0c010045043c5190b80401400e80c041d0300602d0004a1b2001107000410707500d45640216072560010060200414040d4045e010700303281b903250340c4d000da55688030380b80c3ca03090188a101e038841000d01404002405600d0600400c4465243c880e80c00d00c9130b55a540101c8030b000c43c00040c44030815075020141c2c106404003612030900c00804040360031071039031041d2071446100001821030b101807401c0011034808122130003000340c2c800c92410151804a403854002c02540030180c460780c0350500c03804044005842101c0a40ea0160303109030701a8100103405001c1c0003810000ca030800c10403c60342e680000e00001c15402443c1c410741d210350703a00b080080d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 650465962 1250 650464712 650464729
    0xc010b1804051615030b030f01060303050414030a0b040209060111030c06011805090a021c020d11010206060d26070812012402060a110708040b0a1701031e06020408010c0e 75
    0x31032040014405050000c00030b00c2c44040203513101442d002c2204c0c000c402c082400c0c1100c1e12242011507081500c04010103405c40b0290042d03400c2e8000d0b810548551000701640e41b4601071002d401d200c03904d0086405414492110b550060381810207074030140c2611107581c0303154049a0100e42030b4000100510174502080440b0001800c1941e0a1150382000c0300c5442c1c81e00f480317410091141c0c12800742c8140c4080413028030b14041d40c000304519006907050402030100c40700b00039124014001c1000080e12450100781003040c032500244e40c01524481800d24417060140c1000c40001800c09002c10b500040e0203c0007014082008403038951254980200324100c0900030451142052440c030280c07030103c0c0d0004c0c02c01d0b03004052800203e11041090b8821105102d19000070b03103020300004000c1000040b540007000620810303954013864a500c5141440201d1080c00000c00c60b229065840601346d0000e0b201845480c0038500051400342d54140300341c01c6036140800030300451580f90000211f4a0a03500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 650467212 1250 650465962 650465983
    0x11061c0b0d0503190221040906080123100b03150306010f27060b0c030408160e15010e1003060302010908030a0206060d0503070f03171501140c010b180405 68
    0x300c818a0709a5651070503124002e000407160f10004041450030050300c2000250103503420050280001c0796000440b14040d403083c02129845410106d00140c4800c05100e07840074102c800303000014110251307440110b07188014040c2c8812007180e43c1d000c20000c240034015801341401800d04186490028103060500320164440340c0281d054807801c2102058100d8001a503d0251030307000798284070a4916002400c00d508840358501e404542c3e20240701c00000100b041c0c46130007045500b01071000704000b41c125070501503120b1440c1f81b2400301e800e14850030034240c0011014142002042c0c110004910780c012820040d10001e501e4100800541d608100c0c25030251004002451138009110406903454001602c500e0240c2d050040c010b0600c001402030395144c1e0340c41407242529171824240289000602e001020401c00914082860a0240b01c150120980180c4404900d500c69003071001d8541c20842c5034a2180d5200c1d0f1400002e552102c2e0500b030f000301500010b00181c00d03e81002c0b841c0400c4404d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 650468462 1250 650467212 650467219
    0x609030b0f070e04020702011812050622020d06021606020d060902030c0304030c031b060506040e010c021213050301090b041406010608010b03250e1302040302061611061c0b 76
    0x10301941030752201044500b00c0c1e05580246e5140714074030048a8031204400028200d003d01500800eaa0240c269441c8080e8061421a98030781c44000041180f49100c0441c107102000383c44c4a8801030a240594891083c021680141090326410089650f204c4080b000c0b00c41c15800550000940814812200541041c5d0011070440c5444009500a44809803028042c0b12011030301404040c8181c01c0c0f520031200102c864030410390140b4010026000070394015100314100702c0c1200c4004814441d000c07800c480307a4001e0181540c03008004070b442e0300101d1a00020b46942602080c203407424014000d0705d0b40305190070081380c0303403d04040b80c0d140f01c3c0c4407010030180c02c100010440c0940c01094141581e14541e07410b50750703803039907001110714102844080141a1000c00403488030b940060484541c0710303041d203890074041e130b0f10750001e402c034451404020346c80f002c01d10000c2c0411224841c0c2d0401d56108040b400c8800310240006010390704003150b042e00d11403580103410089040d03801111000d00d03059 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 650469712 1250 650468462 650468491
    0x60c0516121b11060d06180501030c0605030f04060f0e030703050903070509060928140702063108070c03150b0d03090b1305091303140405010206070f180609030b 71
    0x20395698142e2503e00218038843e8038007142c012449096a0b002e98010099694110030190440d102c41014113424030003520340c41400040010381030f0150f0122171041400b640300b01070369911542d03090010320000f00c500302465941c20b4407401c0007000704010000b09019481d203a03110060380c81018609030f142e030080c030302881c6004203011140d11080005500030214240d20981e0441860180900f0a0601030110102d400c0460044d80945005040781c0078008982c241c03074050ba01c0342d80858440c920b2010118540018000c0c0800c20741144910305030061040781c50624201c02c5460b00000d41c2569081641d69070049030b00c4000c900050321520086c420f050701c07404a509910380303006d0030300121407196080e0044000342c124400195086504060301009001c0001410041585240c05518000407404900240720001040c3c100e00c00b610103c42050740141161380d54031908540f00c2c03010321102e00620418443e901c400390002c55584c005086030759a030b21005891802d110b14200d502504506100707848 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 650470962 1250 650469712 650469767
    0x70c1502090114030a0b0a120308060d0c1a0702030d080f0915040201080a020d0e01050a0c02010603050c06070c0f060c0606060519080c04080f011a01020d0c060c051612 74
    0x403040d4000760a103d2103943c0d88940c0d8040d4400080c20684040c0d40d8419601039000c10b020407401300309124940030341d844c9000c0b80d443c1c0062001c0d407c8001e001910f0032004480801c9a030a52030714042e501a6042c00d840e0510300c2507030109180040f08441d00011428090410012012000c0747ca0341c03000c0c00f074001b02089035040e51082a55080608040d041040c8a400604c810b2400d40481d0000517102404005e540c900c460150b000341020f0780c40b1491941402180c140c08c0e4814019901500c0d0410060300440c05c07600c04018440d4400b0720300700c07403041c2c0c4510000741c82200d550b88540106110b880d031410310b44c40e61420008446194101c0c00030301c1018041d008107850000c02840c02810700c0d013000d110039140d8120005803401680d103c140c8a20541141c0340e00c010301904185640340101040d0076032404200b0059031102440d04500740058130702c000700c102194040d0040140ca00ea242421454000b000302004014007440f141500d07154401050f81308199402814850342c15038001200040050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 650472212 1250 650470962 650470967
    0x90b04110c0a0623010b0906040312080f07180e181e10090305310623031b03060f12030712020c01022a09190c02011406010c050a0209070c15020901 65
    0x41801006c03110745020620030310741d480d02e0040b680070b5078010722071040c1400010001001800103c0314a0300302c91200c40401c0400780221102000c210320700381e40e200341c41c0c1800d814500c001d100410614907804401665a070302c0070280100c01c6482078501c0e0262022803010056864080071544401c1c810703203842000404294070400b500c038501502c01103101075013804e0a0100c1405021400d04c1c00c041031a250010341d8641242001d100d9001c915802c045410714001000f185000460340314414a001540380782d4080b6a2000850380050010140b1803000a40b00c08a140e00c038110349210200d902c0000d1810600507482da1401e001925403000346103890b00280001d4840d207444031907078440e480c43c05042c000d030000a040c40841d904050003041641c94602d041c04480c0d100f08a506142c20300e884000700040e881806903180010491880e5030107910b98100448180348213030015a0b0b28022031901030010390b10356110700c0c041c600341c0da0395083c82c08460400036400c2170700000048515204120721101643c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 650473462 1250 650472212 650472281
    0x14030f040201112506030b040e0c01080a18200a06091203030f0e0c120307021c050c13020903150f010b07030216270213090b04110c0a06 60
    0x15070a1a110029403440c0042a241503540072240343c408484007440b00c0b55401030f50f10841240c80e9a1750034428007400600f84000ca480041030250309801400707075041154040c880c0d164120306000b00004144900320740028003d480b080c411941c0503690210400e484003d0f0180003c7c0d4441100c400280c0c92410300080c02c1c2e200c0741e204040d415155030040f001171600035030140c014400328140612210550b1000030761200d008400c4103204000359140d0400c0e1210000c1a10186940502040c6039a08405020340703012014040444591241c0100c8505035100c00000b10b455800b0480d016850f09207246c20141007180b8000c0c00c1040003000810000300c015000902411100349010380350381c9000e00d00b4203d090240081c02180040c2d0f80002c0061492100000060b4044160150796111200d09800d4405c1e88682070424650b003117112400d000d401c42030740c00b45042c00340041c80010700d154901c21039162a00407420000f02900030303034144000e01800b07005007101c144d45866606580e130591001d541001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 650474712 1250 650473462 650473471
    0x509060a0c0507050f0705180f061e0d06060e0c0f0403020d0f0b070503011a03010b07030f052a060a05010509070807230a021b010903060209040204032114030f 70
    0x1951104401c01d0703914003a0045030344250b000f000750307811030045407000f0341d8a008502c215401060007a145050322880c020010740501006000b449254840000704048480811170260b101d100c1008000c1c0356640e000544600140325a601040c0326180c51020100361030b00070a84000c0c003004220000800c2c0d0048102c8081e0781c1d04803405044400036041140407039031441e4008080210002c141f180b01c070b4002d4041e604032110f0340385085d00d10180c0102511540402c1c461800800028000c0070000b03030048801a5003c0c3c07092902d18140004040500100001c017111441c03c1a10809002d0018800b84102e030f0b4080d0290b58140f0003549440040345212800803d9a0208000d0102040c400c61040e6005284000d8098414011030a501103846503640305455103405449192000041c80850402e1911001d1050311204074407444d644405010703510095034158050341c00c000110000340170800c890007202000428034140450311601030001048003140c03142c01c000c103204200b114401c1194a83c1d01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 650475962 1250 650474712 650474731
    0x7050a0509041109041a07021501050906180106030e100606170907120311060709030305030109020705010b0310020901020607020606090411010e040935040b0f0714060109060504050906 81
    0x307a541d68200741005000f15800250702094150501c0284011010380818100080c1c1c080c4080342c0310b0303403426030b03a810b50861030781c0c11504010010080c0b0701d40007503c181e101e840980a0300b010b01810b012006252000d0b00402d002c66902c40f24030041000c00c00280015840700d980400101d801c0101c090040429405205812020800066000c52050010030000c002c0c00e05825000b089502c0c0c054100400e100d504030a5200b140c0010741d100380305244100c02c0340d030580c49182c516405c0080140c041d6000c428251103642d21a803080c000c5840030000c014185c2c042038030040c0ca0f100aa0b000a007056000341501045602c0001480800d80d03407001034070341050340104020000310401005a0300c40440380c81b0203a0042c40e0402260a1080c007101042040d4009803080c8140c2c3e8108034840e01454038007820520720b2006000a0241400c00c000820340303106520500d038188ac25a5644600d03405609144150907000707600100302c000c8460040b10082d00e401c4505001c1490244000340d82c41c080201003101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 650477212 1250 650475962 650475979
    0x8101e0b164814030f1b01080603011406060a05070c0e07020106060f021c11061905010f06140a020c090c0408010f0b06161106040806090c0402030f240a060305071107050a05 76
    0x340c1d601080301c1c45114481400752880d000c6c1440311341040004031869036001ca8942d10005030b4a01e0107104101e45200c0340c04460302c40d81c80e0401484016003120010300c040c010100482c00c0802d2880d900280107007421020048140b1300480000d0944215500c00000e029258400f0202940c000c100031045040515030300340108102501203914610f559400c4020340500c0e014801450071410800320002c0a6840034449a6a40c12905d01142901c1c4036a00c0081c40380da62100041c0399001c001c1c840702c40d039481115400007941001400268040d144135103124030010741000242801e0003404001480344904000444040c8089003040c40307412902c0320000169030304007007008080000814100e0024140e65141c1d032b1507100455407090241c44500a034851a118030201c0d1070140201e07882a145007060b106652503110301d0812071030107000010494550f40301005042c0e202c07001c00e080200a40d42c1c01140600b0030000c054011180d0b12030004258100c00002c0c800354855043c0e20302103e0060303c4514 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 650478462 1250 650477212 650477249
    0xd030902030a0f02060f040b0c010c08090706270b1207020106050d23070f030b09010507050415090515030103030806030a051b0a090c08101e0b1648 65
    0x41e894480c850945000007804075002c48c22004803000303011804502d1000b0841c0d442100c00c251000d4204070748604690340050000d02400e48248850607001c04c1c428440000e0901c0c960f400078804981d50003103c5462400b1956540003055903004ca41c02011a000810843d810907001c2084900b074501d0141450b80d2071040111222a41164400c0e03404810381600c1615485420380c490301c030b03104c0c407040c2c40b403010840c00700790200b00c10300c038050040c05513032100740c0b42c2071034103040707110200160b40320340148210a280014242c80e03d2400e15210036007001e00640d42d40c1545005403c800020f001e017802544041c00c81c400240d0000303421480c422240c9002d5101c0d1101500241841d04940c0060186604200610241070740090b0124058013040340d40e08141c036150b00c0713144201104d20910718500300000c0802c00c17203140c0d920000c00c080700c940440c0d07101c107401648441c8407011801c0300100c10504440e0048a00000011084000c440100e2100450240e0046901005c0005005100040e09a0317655a03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 650479712 1250 650478462 650478469
    0x1f0614070f060608061b0301050a031103030f0424022125080705070e091f1107110906010509030a2907090f090207020d030f180e06030d030902030a0f02 67
    0x74404a6441802406440d407224481a00e030102501c038003d03604003e82c032840035810014141e9040c0d0300c000c1c249200d142c0c610340b00c914582404803000b40d05800f04001c25008072501000030400707407500c40107058004910704000c3e0104518015410219005620404a003290440401940c940d40160030f54a03040075190040108261411300d5502c01c491180c500d080003200c001600001c0d01660507524207907034444820750009002c480f8a03142d0381094140f212141032840242210126040c00041d09412407102d00b03149510411040d14020401e5100c501780745413010086620940a01c0e0035402c2861020100742d030342c0390a0100420b0720080340001d4950f14495184000150081201c454681c10b0030807010b044038030340303004400304482200f20110b80003000d4022030b0710060380903150010740c0041e07881c207e403503d840245040c10050a0b40e010b180c0c4030800f0350000084c0c00000c104000505001c01058985031110141409160501c00b000e4050307072300070507034004841d000f510180c00f404c200d1000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 650480962 1250 650479712 650479733
    0x30102040807080c0a090501060206160203250b0c0a120203061f0503010602070f0609260709060504061d01060518041506080901050408040510120f051f061407 70
    0x2151940b10301000051002d03400030300c2c5441084141e5100286907140c009040036103070309000d4203001d80d20031f001140c1481d03800060018040d0719481500e042c03040012a4100c01c00b11030309201e020b000303154500c41c1440700101c1c0481e000710a40c0303c0180703050303418500601400d1003014040307510360b4080009040c5403145029020002001454890131590114000c0c1c5240c1003030042c04010f106440022600405418205054488980350b030484a41381c81e03050030582d80f0920020b218026441c109185081c0100203220141c8401c10022414508040c140700803602c0c0365000d0035000c00304190555070a181000820b040d04d91501d0b05c1da680e01e5035401848d01c0802e0100c03d054009103444281b481989042841074180d0b00680d994880584034040014282d440035507003d0030511003000104010b06c0c00c0e00161215021a080101c1c03410790113604a03084034030716500010070701d46603000c111100304c0385c02404407078600500c640031f145401c018004199000c02e00c0d400300351180000e80f0001340800081d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 650482212 1250 650480962 650480969
    0x80f161d10030509060f060d0204050a14090607020f07240203130e04170a0206070305061201020f04051f08072003030a0c0f0c03082703030f0108072c0603010204 71
    0x3400301d9000054010020700c0100d075008074074010400402c64445c0b004800b140a000d0040420140300581c0d000c0000034132001d4850b40752196954045000046054206440340340440b000d40b415190820b006801c0c1009000030301840d030405101440f8200e28644580603403044c8181c40012410001d2040c0c0c40c0d4411020881e00b20f518851002031181e402c0207806106600c140501c10b460042910303092002e00070000050090380000c400244403901c00c0e4051070b800ba1004004820400e61000c0060880c0e0000402c0f000841d00040d007803041c1c0c180740382080046090505034003200304883b440241202e0700680281d0030800c1440b01c442401880e01c09a01c1200798803420f5a51300e0401001010040405c035400d000403990104c42000c070640914240c2500e05d030551568811030743c5082c1d05005004650f600d0a209881c07100e100c072034a40080000e580306215001800c0915418102c0342c0c1d18000e06030703100c0032140c0c481d5103e218005101f04e00700302c031000701d0301c04009003619140b00080c00781c00ba580 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 650483462 1250 650482212 650482219
    0xb0307030b130c020c04020a1b230c0f010c0506151906050310050a1401200604050a0309091104090b0102010618150504050108060f04080909040803010501080f161d 72
    0x1002d0315103a940310340c400d030207044054007211019018242400280e0054500d00d40103d00b10100800d949001103c0c80c1d802c5c00d200b03030f000c0c0031005c14051117034002d07070340c54084182a0313408600712802c5400c118501000c0a042401d0180d0301405907640e95541e50002020020b2041860f00c0800d0f05d41c4031000782d80166400201580a01a00c0b20300007049034008071100740c60780d50300f650002801c0c117000d2180420b5941000440300e504045000640c1c070103c00f9622035540030841400e500804000340038880c0941c1c0708030040c15030f141c20340c100104180351a8002120040c90300c140f101040c8820300488044030002900428803050081c0140e0040005500c440d20a5507260300c01e4010302c00590000310060600d0030101403070742d247d20a10003100c509000701002ca0f8800000b04e8036200420f0744141d40148180705107440c104280011928500c42a80e04a400c4000813005010541c0c2000c1160350100480070031f5500780c03900d03030700440c00e81010301540c20900c614100745050862010303952420b400c2000c2d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 650484712 1250 650483462 650483479
    0x219080115080106090b1c050c130e0607090315020f1e0406080a050601020303180f060708010611030c0c011809020d05160309110f04021b030405150703080105040b041805010e010b190b0307030b 85
    0x5002903010f000c410742f404607140500780004404030700840d000000e681e0410904070700ca42000301d0403802917004030381210000e4400d105d061441030201030711409904500c042c0303a03101ca10f80100508410700c003408090314641000c04020499900209495000c13100030702810005010600d0f1350b0034010722a40000319409818100104160800c1c3d0260484a280d5104c0d5940c0001c091200e03142d01401034441240c0e00b05064810840d1b02c282c08007000000d108620500983c0e59820300d0f001c90384241706a20240780c4400410030325403404c0141490424550809008804944da100d5580007000b110740380c0b00e103050304c50150f401e40361b90781030340c084a400c56024400c0303070501c3c40442c1c1c0d650050b00c1142e2051104000c0c3d10035941c415000d0710045640350f1104119a4204000c100141a65040842d00903665150003900c0401c08103800154034040c46c000110800e150584d14203640d145881c3c180541018000a403c80c01d804114400301c80d034100003540c880c5c032001c0084018280d03000c41c03941d00c4000e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 650485962 1250 650484712 650484739
    0x3070302010b030f07050108011401022d060f0402030a0b0a02091008062707050c011404080304171c0f0e061f080c0a030219080115080106090b1c050c 66
    0x560000c1c1d42c00404070202c80c08651100440c95440450f400382d035001404e0000104a5120f011000d0101003205005803502050301c41007841c010320003400b20b6039103860780ea8421343c01784e81d042c00203541040c000080c0301a00c0c5000d1b00469500c42100e0801005038044100040e0407540d107038103503011003c0051070303581c10200350180102138000070b40e007640c49003000648408450900d0900c916185601c12180c44241e0b0ba2907d040e40c05420201910a00d0354071001c0e00000b100c2808141c511803441100703140e489040608100300140f042c01c11040e0044002c00007000015510400007492012144021a0100742c2c0308045000e0502a1302c0914180f22380414056460100750200a01740905d800807440f0a03070719010190b48004034a142500305404110a0016041c0642c1401c16a100c00c0d00c010192075039000300a0849290654241595400e2141030201e054203000e140b0040080c8c10041c0100351101c00060801e40600313000e45503030100f83c00e100c02040418091500c0c100d0b0300400e0351a90402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 650487212 1250 650485962 650485967
    0x10507050c04020c0f120a09050907050702181515270d050109030215040b0114041e0e100603050c04021c060308070b0a0e0d051c051515180603070302040305030703 72
    0x1e83d0051701131030301a40003800e00524101080c0d50740040c5541c3d562104170b00d031074180034901c00041d042208001081000c1d00241e2192030f014a440018641c601c42d45241041b84440403a01d100800761141d1400d0b00807404030030b460320a803030b00c840e8070100780b280306201614402c480280c400e40300303a0444010441e100078010103500c00c0c88028003039003d40307500d8001920002500001101d0082074041018018000000030b04a81105500060000541240003c0c000c401061b42e8005c401da0503600e440c40e216011005002d501c04406269605102c030383d045554564030388400104041c010381c3e0114403005541c8080d858640283c501030801c0044d251a82081d0b912980305d02c00036a80c9900000c04242222294421f003450782c0040b20240510f68044501107070190f002c0000c543c5110603074810f00801a0042c41194010b194882000344143c25080510100b8201440d8600301c1d2032092000c1043c0d10158001d00001e011300b00c884558070b541c0c4000c10780c0280560740010740350b0300c0045040c804140c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 650488462 1250 650487212 650487223
    0x5120105040b060a0e04380417120c13030209090129180c0408190c06110607030f290a050f060a0809120c06041403090a0302010507050c04020c 63
    0xb4041e144601c0680d07102020310180449600c9070341c0d45040b003c0b0020300403a4001c00000b00c0e18074150b480700c1c0300c203c40100036152010340000713074060b80e44494103210800011201003403000341c40701c440600748440880f9419158100070850f62503500002a00b140380f020070303d01403000c3d650041c0805880d081404405008014001d080490511000e4801161142c400300180ba4120024440b404006900c10741c1c1c503038400090014500640140004540c8180502285070401499001c100d00041d5030708000480581e540e201c84140090303102c602c01c1c0c0080101d05540c0c0312280b420b0100f080d0b0055049a030081502c4800001c41c544040c040d1101e03103000c01c01c803240d401811030300c100d0466110400c000200303040001c03c0e980624204030102c002c0b4012050b0541c0500014140c0d150300f484000d5010507540144250506900240100002c10183c041c10000010310350f4004c0d403c084113040841d115144602000e41030100201c0d0180030041d01704800401030901800c00d5480360000344480e40d503030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 650489712 1250 650488462 650488471
    0x3120903130506041809030e04020f0d0f020c0606010f12021204050c0a06080a0b13020a110709050103050309060c0102090406030c0801060503061b03060117130201030b0102060f04030e0a05120105 86
    0x420a10000080b82e00e407110586080d01c0c0e02e0a9034520300004880700b800105054807040f0144056000200d100d90303920302c05040004a070040c21607890b00e2545100d400c1752070b20f60300350b90307018810b00144014040000304194003540c00e080c4074030a041c1800c010b558800c1c040401d41e0040340000345070300240307000e1000d944c0101d100344112480340c5500c000304818000c042c01030200080300e840005102c042181c110615080000d8004c5801c10040c808400699018640c1000860251805813100306420080c3c10000c0c20100000c20107075045594807500ca1060701050780c440c14003c10303c001d21440c294111181c0b000002e00410480342c2c1d0f854900c2502c01c05124120080d460003100113418200441c0840c0310b02c0c1c0e410407030102000314040003401500007030540c50410141640c454a41c3c008114014010021850301c0c40c0c0340101440014280e86a84031910b0441d0480e10600038080c0907502c0d055003080d81418010407000c0c000010440c044040d50041c1d9114440c0c8807002c04106042d8000c0d03004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 650490962 1250 650489712 650489737
    0x16120b0708040510021806031e0108031204021525020a08070602030912160e0402040b040c05090904061e1a03010903021e070b070b190c090e0903120903 67
    0x1680d45009058900c118200d5000d00b841c0c201981c1c1902003903040d8001c0c010b07403035181d80c98000d00301c03604085600c0340c008031114a10450300d000d11266500003042e1090040c4085030013140352160030110110030000103400240904001141e28686c80e91203020f664024540d4a020700c0402201c60700100c00800d05242640070710111500802d009101062881c152140c0f500103518007441c01051110042c040b1080c0643c60044c6e51402499806244c2007200415030405221018100743c0100403c50b000b0503032051043e460504420034080d00001501d42020084410040541c0d80d0704194014181c400c8a4450051182c1890120503080ea4060350035036021260301c00801080c18245422a84405c07030240140e03200e0004058480008000d01a8890401d130a540c9010750315215074500da08040340480b20489a1001c0100c01c40c02c061212101c1151204140202da9040c4806800c414030390090ba140844890000341d103030441041140d0414408812251407441c207048a10b1310f036040903692014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 650492212 1250 650490962 650490983
    0x30c0314091b010206070f140d020a0801030c06090e06130905240105040e150c0409061518210512030906073e1f1e0218040c021612 58
    0x81a504c00240c05100b40d00d9901d03000081d990300c3d0020380e05401c502d5420104400200912100a03045001400758805d80341c0b940280b41d415444c0c010b00c417a54a41043c4100708001404108540c91440d50503000842a2010403180345a0100d11f4042c2c1a951405803c91085407401c641c1254014420f00e8040554004200c2a90301e034810001526101c860310341d0719601c101c080311701415840080d1608400c0c01118180303042c2e40c880d0301c80103440320395206201c03140c1804801001e041e04405003065059495000301d15890802c208410b106c1d42d0081d8020000c266100b0210821004000040000e001c1401c0e0316160301d441c40040e6a2800119040c800264455047c2d00c207141d01d10b81e02c5504c42003100050761523462032140b0361100520341241201d20f03110303004041e00a00c00c81175044c010042c5141e4003140e80c1e503132151442c0d010610681c1181100c1d00c1044501c1c02148007641c080c90003032003202c0c00302d840d03170784440101c3c58854000742030007018410010020712400055000da030002d01c12aa54903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 650493462 1250 650492212 650492263
    0x40302030901180e07031515020c090c030f011a0409021c0606020304030f02090411060a0f090b0a0e040f0b130b01091a0a080705190203040e0c0903030703030c031409 73
    0x80341c800c03d9110710400f410414020031404c1d4029001544000000f100c20000c0c0c07650381440c0c83c603588041c4400005030308011801420303820040707903d50380030900a04040c614203105201820340f031414481c41540c110710303500080120010710100c500400e9101c030199250071006150415a811112061a5107843e146c40000c0d40b41c000b000340c3c0e00b201d800c071010100c0040c86400b4441218801001107942203404542030f40e0a42c0c822010b0040b025103659401050948210068800000d82e00404094035051203079444030f592140515409500681c3c001c165024809100760151000d0110f85a12402c80c0c82e41000e00303141750b8080181020b0982e1255010f0b65154081d010710b81018110092445c2d040280c001b000c2e01480704590010178500e003040c50030000390040180901000030600060304009010010701c0c1d003a00615801015411150340b8204030100040c2d528420381c1e0005007455103030701010505030700980c0071120104042141842500c0d00386403080c0c594102c1d42e810440b400380c07140a003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 650494712 1250 650493462 650493497
    0xf1e03021b0a021302030604060f0603090b22032f0a1b0b12060d021903050f06012d0801180b0a0509060105060c0a0609050634030c0c0b040302030901 66
    0x40516000b4001340030b0310100c1c40300300300a5403004000720f070000d489041c00500201c10f0030102008007080c0c0c0c0c0c006011031043c680203000c218090300603043c241650b048271117403950840c1d24602e003030751504003501000c50080300101d51000200420305c80c100088000040b00c680410f0980b02c051096403414050521490f402c0e079402168007480115420034410906c1c9032201703200391034200748006d00442c01e55516900081c000d4407440800c044a40c130308070b07082040000800c14101d5408044024080720340c180725032002d19410a203000d01c41605003003042c0041d881910325990151440c14002d114050480c6000d84d495a0340003070031a511600840014004178042c81024011100d02010340341c640d103400100710300740d0000300d400c01c040d0040c3c040c2000000c06c0b51141c83c820501c03a4000e4840c1c2e00d0400c3e0210403158180d80d4681555580308490b00039010351012101c4503028a05000804140494040328241200c41004101d1b41c0c000c4144018540c0002c0549103025090384e915030044d0004409 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 650495962 1250 650494712 650494723
    0x60115090605090409020f09010f181415240703080708040c060f030618270b010905040812041b0504021c1a090a090b0708070f0f1e03021b 61
    0x800300002c01c1030026911901d016040f40700524002080e0581820744c00340051001c180070307480290100700b1100100304040b982c1d5540d40150101a00801600c0707120b08070361251050003065002c05840c8108050364903520308006082480c007020744400008a4104026007544c064142900031416a40008915074070a4100c24415a40806641d61403450084103071380a00d11f041c540824561a2000442d420080c081c05000145142d44042191244000e64030b000c0c0b15003508841a21100c080e002e80403a0003001910b0450301800d0002850b036982d4100f0503240e0103510300b80c0e0303052160501440280f00c59400d0203080706c1e42501001401302d6541c01040101d101d004090180b8080c525010000c2a01c954007265a4403281000400102503620014100714811500303034502651710003403403062100e480d0744079a100019041c510528181044050110300176030000304100b10090720304084541c440c12460030104004441c0a0126699100140103034001495410342820155a0b00b4143c2600240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 650497212 1250 650495962 650495969
    0x32c01050702010f030e01020a02070f0906050a030f0c0902070303020903010b0906030a060b1203070309080d090e010b0307140c0d020c2b080906040b0307030e0c10120b090906011509 80
    0x103603146030014079070042d616034000500d9013051607550588034802c990300b80001c00c42448140d002e80389450a1041640c410701258000c0d2a00c2c07464100c0920994503002d00368030950b900301e05003500e420401d1800c1c440c417903050707080340034514004900d410825415801802c0040c5040b4004e00022200e1000c0c4144140101d940c01c2d4168404003100c40414803d50041d4900c10018020381784c00341c071405801b8a9a0b1000c80210001051034900300441d860a1042928406c51442c0005d2140c1c81d2079503906104030180500f030800304000020414541c001c00b0786001daa80140d0ba0305403651200e02d881512010342c0e02401025000b990702c511344600d0400351052045074a1020707003401700c0740440004a0b101000e1001c664400080180107440e55900c000b90005041d4440110754900c0c24110060980e4101021103185500c0942c0740c02a59a400c0340c0e060394001c5500d00320460208a80b051000b40440318441d540000707403070052244c00c400114149043e03400800c91030505400094085600c02c0d80c520 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 650498462 1250 650497212 650497217
    0x1f06031a04051507081815040b01080607050c0705101205090f0c120d1b1406060f04020703210908040e09060702071401200d03050103020312130b03091504032c01 71
    0x300098058485003145801c138039003907089070a04100c2d1f03841002e001c0300c02c2c1c400780c03800b4220100412076081f04001240e801210f502c0c2c100e05040300c500c005941c40400b40202ca02c207842c0700342c3e9603405074421030100d80c002254000501090600484903500d0f500c04114401280c00380300d64000d00c03401c240081c0755000400314001c207040101c0c483c00f00c40e00e015002c0802142c1c20a030701203c1c045101c01d40680e000800c0b0340041d040b14181401040b550ba00005c21145c025801403243e000401d400465440e0f041401d10124170109045030450310041c125000c00602c05003011901003440d18040304858442d060241c11200b15482e0418140e0342c0b1046c502c90102210781444082005500c5a04924a075040710400f8002a0489000060800440d10340a000083d604c400400540c0740c20406c1c190b42ca60035400d01c9240640e40c0351001c0c8204214001c113a5070140000c08180144010001c00c0c000b602003507585045030030103242c000c1c00b40310044800c40d006c00c02c8450380750404a0b5005074200c202d4058 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 650499712 1250 650498462 650498477
    0x50109051002010905060705091912140c030109050102030103020f0406030c2705070c030806060f090909030909070f03060506030f070c0c050306090c090c03091f06031a04051507 78
    0x8800c21a80c1c1140a40450455495070090303c0040d13001c20085002e8080c07521250b0710307200c03010180038000f4010703480c0c0040201c42a00c20040700d041c00300100303042c80d0020340c0080e882c446900134500d0b00400500b1a9015071a008112050100650142d8141d900c01c81701008640c4504007000709403410703070001504000c0f2101c07040040b880164503070f12102265007030390045006011214401c495044401c0c001003010705a1010030568485003903079100d0022075102e0b040507050880c600190051a001500942140d00840c10241c42002910381f0785000078100e00052901c100c00038407041201c40c1040109003450804100c2d0726101040d07900c601c7d1040314040d241ea640c14000c0710010543c480a40d400d101e01d503030200d00c43e02d082c4682c0348181024801043c203030b12600284040c0c2007000300b035118000804d005001c04100003041c1001403440c4129058a0030700446401e000512581d80002d08422900030102c0c080140e0180140c03180c1d01640030f0342c00001009140d08400e03c000c6825000140b0703103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 650500962 1250 650499712 650499719
    0x1e0302250801050a0b0a2102130209010305091b15070f080421020102060f060d060e07080c040501050d080703020f01020c06180c330d0207020a150203030c180303070f0c0f050109 78
    0x44203035a2810784443c034100c2d18050707030607004075101134092705141031941d80000b514106560940262608006130800800140c0d2100690000c10b00140c118a4131442d030400604881d407042030180c030701c015004507111041440070b1404001c0b9902501c1f50340f6000b0100b40544440740d00c0311198003040394068014000326038a035084038101850060070030351711241d605600c20201d600c43c4100c4c80c00c3e01001004100c00c80c10001d002d4500400d01240501c22410840140b0a076120035000000059211586607200c070264601a0b0800c1c0c0389900c421410741c404035074100b030084001101c90048150800b08054580030f0801c250300d402e140c41d1038940008010aaa1502c05100401a0311407415002e241440b8904a181c5c11101d500504040c100d8580105190b029441e02120483c0204420383d2030b08944521070b40042c0d100e002c0104104c40c1000c2c0811070611042c0c40c035500d40350501c0010150707681c0e13011510b08002c00c0900d000c030580f011880f100c404925003400d2030b501d005540c0141c461401c110729 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 650502212 1250 650500962 650500979
    0xa060e070807020d1209140709060b1c0b03030f12041b0308160206130320030a0b07050a05090913050f010605012007031208040506070c1e0302250801050a0b0a 70
    0x1170302e00b07180885907541c007105e00850300c103803002c00b040304041d07019086552510510009a82c1107410030f1443c03036420003128005612040e0b04e1825550b041c5004200309201000185c01c6000d40d0789110100780c800103548040c01c0162194a201c4c620450081c01d035080300d00203401119645020040506038100480410190b5070140c10340e2252000b81014504002c100070b000c180c00c0b142d4412207105c031030100201c0490b2901c285c1c286654105800400c06507603a5207641920580c0a800070090082c001031840c034803849103003241c4030340401901300c0c0c0703441c04d1041d03507000d0401c3c1207a001c1d9494043d41203031648101e0306008940446405944041d8004041c1c1c0a08040020303400c02c0e1440781c4034103640040061140341201030340e050242c84081091600341011030070400018036000c100921210200c00041d02580d89200f6007421820a0014459a140680c5410215800403030070096414109501007500d0010a041d04c0854000b401680c807541094007c0e8be0300c014042c2c0c2c5c40b051011041c4401603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 650503462 1250 650502212 650502227
    0x21819090b0402091005030f0d12090302030406051b120408010b010206010e06211005100f0b030406020d02130b0d0c09081015350a02130509010b06030a060e070807020d 74
    0x210140e0741301a4207503880c6c0c0004c0c0b402e12200011415134001c641455001c0350003c101348030007100d0b0340d010b200301c6919950080d100d105074018101400004900300f41c0c03480000343c104e0500e524280c100c8025001003000c00c2100e40040c03040b14000e608020740b0b4a5a5440460303201e040300c03a19840034415864080412102c2841068400d00051460380d0007028248200030303042881500c1b800025107401c1c01410003400940980280912410b906020820460b603001141d5100e42c10078401612114101040701c0a4450b401002c035a402c034082c0b011900181d6000180b2029846410420450100300d8054850040340c0c410040c940d040407400781c080500380c2d0030204000b051000314a4800d6183d03043d80d1360704003008410400344241c00009890846041480110151403903004250a05070303036000800340d8000b1280040a10345034404a55100000d42000741c20749002440162a440c00c409900b000300305512524003400c130601c000c100c2d02801004014056800c03a4050070303407209045c0040d00e041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 650504712 1250 650503462 650503471
    0x10302060912150f06060708031f1502070501030b030f03040504020d0e150709170303060f120d0c020a091413030c080f0a0f11150a09021819090b040209 67
    0xc46040d400d800ca050202c3e0304843c055592000c1d0504107004652100c1c00010306170740c00f4090400c0700780c0100710b5440691f0392002075000d014050151105801c414010250300c040d042c0740d01c81c60140c81ca43d8000c5001c0d401d84100703981c02c01c00c090080081550b54040c2c00340342040ca401c1000140308a040c84d400030300c4401980d00b030110304d00300543c606030b10740155004150a041044d006000070320354441403050052410a1340380964103000b00b1100d8aa10001d0700c0d841c8290030003507910500d5280e01011030345000300b1a06684503604e0814010341805d40032581288280c0301c0b07600c045036010140c800c2d40100070031341c0045111075a0300d11030100480a03203e03066041c0700107124410b00040843d8004c1074030780114200d881e1500b00c1d42030302806d521440f03074820080c03243da0f10300940e0040b8000740e07412010070301c103003118a0b0b40c8840e50000014802c8507000394100d0941c0c10490a14061034151502447c2103407441f5550756200140301d01142eaa00340b000b40507006c5040410b01603d020000725801 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 650505962 1250 650504712 650504719
    0x40f050123070c030b090105070f0c0c08060106110c1005040303050c0115061d100e0d060b041b0f1b0209072f0c0306010b040e0702101a09010b0705060103020609 71
    0x1034111040000d11600b0076801240c040101071014800c10450000c5180c209090307070b00a00c03450800d00d1001e86030790a2030810004020180b002c0c5000c5c0320000044000600c03103402516071558413000010041caa007200700d00c40038812041070140340d0034983c0070044003160070340e260381c00c1900310303941103890b07078800c270b201007403541d21038096040034400c030000c0100034034098582401d200b02d0078030020709162000c03501c40c1c40b50150811407402c5640055036000c1005017104d4181d1900003514002d00102503080800d5000b503d801c082c44040c400d0901d141e02800140d4580c01156070103550111560390414818003406299103180100500f003002c5a81d802280b0342c10240c00407410901140a80c0e41908001d10b17048280c0d003800d000b5084d06214003602800305401819642d0b05190b1515440d100340d201d0050303640c129000003a039035803003030103003c0652a100100b403040c001e69042c8554488250803800740700740052400021402645e20803101d80d554004040d103142c0e80307103400300640d98115086c810342 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 650507212 1250 650505962 650506007
    0x9170303060105071a070c20090a0f021201030b1b0301080d0f050403050a0b150f09040b06031509061005100c0f03031508030d0f02070302031b070902030708150303040f0501 76
    0xc240c1d0010705d03031a124403103580e1042072280301030814242d00c0d000c95441410318001c25010024644650350700992040b0302501c0860007107956a48480244514039248440041c1c41c000482000314203e030340c6020302101e4081d03543c5403c07031000480d001c1c482803040c00780303035480320805c040070a012301203441c81e007c050700701503050035500e0f03d078982050f03460030044414200001c10000d10320300d00152180392060030354900c002656070001042002d2000340026002d8034003507000030701c01d540811800d102419001580302e031600700b00a84135a07540b0203a44121000118500204107130a2103505002001607a644807503940d41d150302d4400401c24412019410992203030714980c810030714880440010900b0200542c0e494083e03050034130440b502d044500403c60700401c600b0300400d6000041c1c40240003090b0340301c0e42442c80c1141c180e107469505e43c007940c0c0341070021003000050380d00f00142d148102403210754941c02101140425031644918000c0c501c003031100101c01d000651107901110740d004054001004c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 650508462 1250 650507212 650507243
    0x1081b1f0504211a070f0509031612030e04090f0201121d0a0b01140603010b03190f02070b070c0503030115091d040c060c0b180a0c080705010917030306010507 70
    0x100860350740b0180c0d03480300303e12048010031010003015030140f00700f041c1151007820104001040c1001c816500c0040000108480d8507030b42d014040c0d610314121062042102c1660364000443c003c016040c2a00401c4d1a24000760803030400340140c0068a921280800328624168019207940090044454074156655600505260034448100304140d1140042000300d2491030084100c0c03405030003075852007488500d49051903d602e000d490644090b0700d100e40e03c3e030b0360f4901c0c0c80a401c190400c1c40040a8201107900d004100aa801400d40a004900784440c0f40d5039200d050f640310000400040c19503004100400c413844880c0039644045006150039540d0036078035041050b03405400070442030024207210070310040000d00030400c0000d041500b001103c54030380792a0f01c10800001042540078525840c3e2600741444e05024881503150301a9101007243e4884800f6907690199010303081c04151522404074004007810880100807007a00f006510b195102401104d03140c01c00d15044989075511000c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 650509712 1250 650508462 650508479
    0x30b1b090d0503042c0601260c1905090306041104061701050901060509190b150310061112070f1e0605090714031c140a03020301081b1f0504 62
    0x20701e00903000304000c640f80c0e4206441c0024125410342281c220050040b402000d003001d40521030350200c001d09000b6000d120268030f040f890068a2851000300c403010081000300f070301010151900d0700c40603221200e4400307140c00a643c14498288e049606030f01c0174000400142184402074040c00b0050030124259a03100340c2848000b9441e0f007280000e0351524100701032030000f481410000d01d0704540703c40c041c1c01d02900b44a4030003d0341072058015a05c41e0728000080e15241c202250800f0103100040e501d1030302d4480344015070814094000042c600f079030815403880d40080c00b0011400411819460016140d490380c1160242e80000c5448000d04060780d059141c209604402c01400303028007055a20780680344504003d07283c1c00c1902c5030340001e10810500e4800090901c060428500414040c422045054481c074104656801c00d1070300000302000b0243d0b01d03030040c40c1210308000072514403001080032040d2603645800e00c0c1c1d030065881d5400301038070101150f03000400440340c10060b00d0304d5143d07181c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 650510962 1250 650509712 650509729
    0xa0611090a03050105160f090b0a0e06040801090c0801053114100e3403080a0203180904050a0305030703180b010e0a15150921140601030b1b09 63
    0x141d419941d2201040070443d000302d1000d030700a01d01d291904000c1c0c3d68147c00b61540d6024015601109004036010fa42540512041c0d041e14000400c400e417200c0d59450054081c06140c0d400b107504c0405580700080341c1105000d064000c41c0d8010a00c41031818a240780c2240120241d0002c00005280c0391580224008200603403581e54411301070f120107034140e06c8013070a07200e414000e4900c603800f40005484a0442182c0311030b08400e10640480c408102e501540100680c61300081c14072030f0000b446412054000000301b00c1c4001e40e05041c1140300c9800c04102c4411400c60340903040d50003003080480045d02c204000c3d641f201c824103000400c16805d0038000680b405400086506c00f4083c0014800c119403e03c42c1a8000c3c80c0300401d00c9800c95091040540b6100752040030380c04003152003e040d80358015284079029120400707030f07170345c102c161110040c9403c0c655001c203032a94060011020345054010038524140e176081914451180c448520b20f003030b041d51620460544000c00c2c400f81c0829502c0150 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 650512212 1250 650510962 650510969
    0x1b09050f0609090f011a030c0f1812030406030e01021c05060a120501020703081303020d1d12161a030105060f1b060f160c0f2a1d0403020a0611090a 65
    0x40e0786956050031040200b070805446c0c505039120b01802048030109000c0c0407594246030485616455100d0ba0440e02e07041c40c1c41e81e8019501103d0b1941915250340c001006d8011641c013950f0a200810300700000500703d201e6280031420721560032041000704e1b10503400c03164010313030041e1050401035030fa6480c0d001e0004e41240704680b66500001d03924181940700d400560040303400c2d6800040303520740c1ea0b00030313560780c0020b840001485825100107200c044502c1000b425120040d140700000341100908648901100e408a6074540c2081c0340850503021041d400c4039500410020545181d00301020001d140d00400601205440c0420401c0100814003900820080d1104001c0600b8104800540300c4610018400c408580340d06418010984d48140c0100115030000801841c601080c10b0040521010151410140604200b610500c2c144400050211a1032030310f40354204050f4102020501c10948000e40181c2c040024130340828005e91012024000382241c1924100303802c2c000c102841601d60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 650513462 1250 650512212 650512231
    0x20705120c0a03020120071b051003200702060d050a06120813050111150619080d080906071d04060305011b08010b0403020d08031801060f03020102011b09050f060909 73
    0xb03031400b01034090190f0031000480420143e4440c80071440f40c525409640406400b65000c02c1a4040000c0c2c13208540300641006040c0f41c0300d4050170003001d4040e040c00500e204c0c0010340b0ce101d501030009410140c80c0300960050a4516044a400645003c1d180292100e51165514100004e400100000840c1d0765842804c141d40ca41481800301084480c0d140c1c000350510014103e0411081d00100344903a0303600c0301e803000703d0241d182d81000c61910710014441d180b06a10700c400c0441c24010000316a00950070781e0b51820550b555880c40240c0b20007050b14100049007002d01c8000c401c0d0001400702d04601000340000542d40c1d40c90b01d406080d00c1031082481c2c1d51003008040c03841d130b181e030040c4e4143c05040e62001680c45c06245501260062140d8440642003801c0400420002d401041490201050401c028840039844409401d8840303441e200c12030141d8079016103031010215007885071500540d0741c0c940c1b044036403030502402400c40c0d607500c0f070702e03400394080128a08980d25503c10500440004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 650514712 1250 650513462 650513473
    0x3041103060708091501080309150f030901020910110d0c03020c0a15030b030102070822030c091e1a0603090f031801020d1d0d060e010905010507031a03060a020705120c 74
    0x407201c1c2c90030060b2403140c26200e102617000600080e4000400c0380d044602c16035181c80030b00002c0a074840d05010719450345151450020074809400c4054020744180c0d42d0854150b00003860300981516200100891207400340c00c4a1104103540f40140d03803e80b030b054008d0064440c5680c04400050940704c03585c21086059600c00c0707c0b40c195070380c1403040e85030b404000e400031894100139403540c0030305000320004100040301c42c00e65418a0510462142c00441d4800400426503454002c83d0015002e0301e0000d13004038650310000c1d1f030b810640703004814422101c81c1d08088003822030018031206070720040c082e0750603220313101d94192000001c200804c44000d6188040c140040d0391800241000a183d40c0a02004481514440700700c0b0094410050f4140c1100c040d00c201c10300d8507080b40a4586090110102d51030200f808040c0501904038510820040d54100451071034180f1801c0740e070381d40720245a01640420f0010395044426801000040d010308100e07245c00030b00001d0b50305280c1c42505d105406070800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 650515962 1250 650514712 650514721
    0x40e0a0b07020304030b0103120c0f080d0510050906010e010e0d030e0306060a06120506011b0b0402120708121305040641042307090e1b090603041103060708 69
    0x1448503941d0481014400703945010302d561620b04100341e0600000e4a0f101c1b01c030340711855203070081c0d080344502d5030301c4800f0404200f01400c00140d550400e080c1c14050a080500144982c0700901101d4280c480c01801e8003200c0d100d2000445031846040100d40c1441080d10200c8001d6403845808004a4483c0e50380702c4001d58000c0c181420b0980140102e8090300000400f401180d070046009003001414510002c0c0c80d076030358001255039240c000d02c0c101c03080301010224414401c0900c9514440e500a41e580500e10b14150483c0d0b54074080e911601219810110b050102813540c0780062441c0ca100c49195400c1030303200d200040072504264003640015180c1d805000310f00402c022245620300c450089680b00d80f00c1e21082040c100c00210300f05210756034420300070784070482581c43d000703d00b9500f168840d01480c0000c0c0280c01c0084500400000b54041d038000307178000d1017070000c0c2c4600c0d8250b002c44034100002c0d0400d1245541024004842d01501c0c00400b6603d43c4082018603c681869500d00545041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 650517212 1250 650515962 650515973
    0x61206010c0213150504020304020d02270117011a010905040903031b020309150c0a141f0e010b060306060a1b0f030309210905010f0e0301020d0b01080c211005040e0a 73
    0xe80741d01c106e01590041c41000301607541c80c66401009601900c2c0801100b008214040d041039508001c466408040400072440502c000c5126030300302c180784002c00a499050110000c440d100d18010360010304604030901c61820300d600540c0c9003030700c03e00f00400d41205503160b01d02d150351010894001640007060111492a18016210b007035001d8800b507a14001150720b90513202c82d80f0704c03005810302ca40890040308044080100703c1a0080c103200182c8805038003410f010240c0340840d03000d0019802c0144034102e51a015080703e01614000b411945802c00320203040d1502c0310094030040085090305020b0300800d541859407100680b20b0360300090450342901e8a601c16101200c0078040968008043c607003041e0300521a001074510909242900444841c0f0895608201e41140d0382c0550010801103141651030704202c104250076201c1500e03550361002099843d0090f00d0a0312100c040104840903c266059501340e0408020000308112075210800b1505962101400f802594043c8064205004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 650518462 1250 650517212 650517251
    0xb1321020a0b0f281b1208040201140d09020f190e060418110910060f08180106080c040c0f0c0f030513060c1101050a02030a030e0c0a260606061206010c0213 69
    0x5e00107044071144020700d460340c0041700860704202e01032102c0000418190380c084d034060402a00116122603441a950346008040d217040c0c50124090701180044680600c0c010700000c0070490880c03800803502d480d24004130030348880030b059241c11541e2105401d43c203102078582d00144c507000d00d200c4125103210f803080c8904500c0007414801280090303a0f051060641c0f200014403651010315215445440d02080569242120200c0041a40c41c001c000038050b140801d0030901d603442200c0c100070366412103405580ca04524203a140008281c0b0000c0c500044000c4052202c590282c54048d040c02d2008007495045803980d00080e010868403101d0004100c0401070002c1124000e00e0040e00340320946001a58034050340d1188024140c40f030712248c00c00c0304104105074104070001e11618860b070f03031441410750407000c8120030100203800301e034044030f41c150004140340a0580545203918102100580d110300e03190203001281040007402488000d40d460841d903c0f50003050703000019038138215010074803800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 650519712 1250 650518462 650518487
    0x7110106060e0402091906020a1707030e130f0501060c150b09060402090402070f080703020709090503031816090b131e050903040b1321020a0b0f28 65
    0x5a04042050101503070000d111980d0b01016a00943c9500b104d6001030494500f0560f41d800c001034140f0001400e070740c0003d07801d0703038140207400403200b42c0d41030801941c40b4420000040c02240304501c08510b0b03400d28810054510a121100050f0700a030382000c0415200203901410008540c03200907000c2c0241068000c0b02010310040070407400c0c0040020400c10305004294601c5558003140840d143d0316182c04507440164426242c0c80d80c0b107030a2034038048a4104450a40040c840e00c0404a840c10452148611480d0010011030440d654882040346900758903010b0ba80500882c00d2075041d0400b41e242c980081d01c00c145001c504052801d00f840030120b1030300b01003012603041103031210240c04120300b150510085500301003903580d0b50200092851080b6403080642d0400000c45100c0d03200c1c041c03200401e035a07403a40c1b0003008861100500c600b42801003030280d44002210400c01c8076241c0c20300188a228201004c513030a0036000c60045042c094910060120380d458035400c144100d62106400001d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 650520962 1250 650519712 650519747
    0x20705060609070f02060c13030203161a07151112100608073207020312090f09010308160c08030a050408010606050f0f0d09080304050c09010e071b0f0c0e07 69
    0x1194038090001b0f588982c09003600140f80d0001900c0100e00d16484030400c0950b80140481d2180c1c0c03901040171140400c1031155000060800300d05800b0980d01c001158004c85c1c0101a094450703030880d00c1c42c00107204660221403540b0b020404800c0d0000d0200000c0d02c15481c01d40038000035841d040004c1c001d0341d80100024100000252030304a0034030000320f001c8090105240e00c0d0503291003401c80c50203074400c03c00060f505104031203004c01490f2151001b441010300036203101c850800d17288140a114002030000134410801440310300106100c03080090b41a0b40218120000b003a902c845890460340000c1c000c50006900007410700c4814400d0040034028a040d00e040c2d0b01e0030080c414920098041c0c0f034850780d001400011002c0b45094650000b9185a401440e40c69a0b030a1030301c0d14031354804c02c580f030b11030180000e80e000040700c6600e256814483c4105444203106032030703000b80c0c107000d41814840481d01402145900c5010400a144500c00fa10030303d40c40c2030352400c010760094503030900007100d10750 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 650522212 1250 650520962 650520977
    0x1080702010e15270307110a03020d0201110c130e06060f1f0509060f0a0f020a022101112a0309030a060c11151501090305031b1002070506060907 64
    0x2c07400001421100035409210801d400e0b480b44401c40c41c031481003402c01103400404c00e001520b2510b000c4003e080f214130074110704414441c500240680340300c0911019510110b2440d030400554028005d040c01d006440081c5d5120303610700310000380856400c02510305032a5480399201e90340d232820840701c0d42010084a4a40c90744044400083c0380c41c002c0715907203000c0c511508429849602070000e0343d415250003000e0302e49985141c10000065003040f0342050011745c541003024a541e00200308980810f03005022504107012903035940e094204081000103a540d80d07000c1c88a11603025401500e51240e2203502d900d005000000b01440102c2c2d481c01c00c0715650010003d0b60515940050850500c0360b004001240d01c00d445070741aa5030f20003030f4081031401d01072aa0b0104a0980c0400228450032075810f00b040e41410b01001103030b203046103010080582d4002c22152841c50b402d0b91a41650603c8035088404200604142205a81046a0440f02c03903002e202800388500e0f0240c071181c0e00145a250001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 650523462 1250 650522212 650522231
    0x50a060801090807142a011e02120f0903060a0605040506031b1014160303050a09170c01020f0c010203010806010512030a1805043605060a1503020d030c020108070201 73
    0xb0124130507032800400c00c410990003400502d00610107050000d850f0702c5115100400210000c1d080405d0003626800528140e014010702c6100008004011000b0317401424910810341d043ea9984c1c3c0503403030209690400784548440c581d0304200c541d1155400a00c0856040c1c580401d0206031100500b0302803207900920800701030354074824800151203c0468081a01c03000201056980d24507070564152021000903640c3e0303515100000c9428104c0c400d41d0200050b41e03640e40d40c0b8007103c0c1d40300d000074102001e000c459400f501c0b03100054141c401c90b080005241601d95616500b0755881400020140d0350040010040b508051029070300402041e600258440100d984183d10b030710501c2130b50400d01c280750034009079044840d01c850002e0200075100b0041800c13400395038441081e540016080c080003000b5402c03492003500300d0502d4140d610000a081c5902c40a10b0000a0401443c035000d11642841000000da0b48903032030200e40c42d000391100518010603000040ca201c50040c103071815a81071a0100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 650524712 1250 650523462 650523473
    0x3090201120f02120f06010f08071b050304120c17010c0903081803010c050408010617072105030708040302031510060c080904020c0f160b0d0506180a050a06080109 72
    0x8030100e007580020b601e07012158484001e0061a8486450501d003804200c00d503d81601ca030380c00b58000340c0baa000308460340d03c000c1300d001c10100c0700100080c2500c1c200c0c41d2217080c0418500e030968031520583c2d003019201d5220f220130240c4d8810644e003808912904005c100620b41c3c0d48494103030300340c000340590011110003420103907462100604400d40007a030300b4407402c4038010b0a080448028000c0c0004042e50300b00500b80c9d0803a005144141d403800c100012124210680017000c03200c0c22000d070980030b00c0c0c89a128503041c2003401c604800b91500d0844800104288028102c4e107118140303c948590440c01414681410304261100c0d0003081070501010340508030b1440211007940c5800c0c2c4180c21145448110b6000e04050280c0003400801c9d10408481c0214503100d4a620304011070781d11410500e82c2d5154a403140c03007040c03030048007005048803a09194106503800f0002619250016242d014220f0340c404003202c03042c20036645ca0041c440d003801c103030103600300a022210090080d40d009484e074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 650525962 1250 650524712 650524727
    0x21009290603280b0f1501050c0a11180408130e151e0405010e04170a0806190e041406101d04030908030f0702030c0105070b150103061502011b03090201 67
    0x6003000204074048003260b40b954048803d02081c0e212002d00401e0600503120480312000351030300340c680d03401c03815403070060351141068138021a030000041840050300d80f20090812000001d0a40002c802c5241054041510102c40c0c0035038818000e180e1794485002c0d09090318001c036003010320098000e030103000e0b0401c0711075440d16521800b1038000382c5440522100034850704841d454540c0080c10000000368800301490980d2240f4092a01500300b0200c00008083e5807007028804c1012a13641d40c04900c071070074182d007408840c2000c841026032a0f52650702c8900d000c0d400316000c0f0ba0700880c0c10380008901400303020041d0499444013640400a04003070b9542c0c2c4c9981c3d160798001c1e803e0803130030014081c14480c545170801441d10780242d03036030b41400d040410120360103440181c0c080d00c0b94124150308d9501c5101202da0f6260015000040c50319003815040b4450850240715040544898002c41d105200760345202203254160000280c811091341900c0c1003000b207140ca501810301e41044034000d81d03084040b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 650527212 1250 650525962 650525983
    0xf03050f04151503050a110405060a030f0519120f020c0604031401020f040f0303020d1d041a130b0f0406062a0c090204030605060301060f0510021009290603 69
    0xc06034100101c240500c0c0050682030035444035840b40f54000400c0c00001305501c12024000c1b415031002c0c890f11020310007901d03030507030390a601f00c90090010400b080319000040c025500c10b000782c0c0c4441c101510500c4e143c450420059a4010a1328a10f1420b15000480506c5640460000c0e01a005454001070218000c4e440050301d15a65031240d2440002d00b13604444041041c0d4801d291100c1d140c00c11080d04001500046000d4498040401100da004000ca5440e007050042201450001e44041c4009030150710100346841d0070008044009079201d2040a041084942c0c0010350220380710104014804069809400307280f901c1802e000503503100c402400c3e2074a030035842128020a502558940d181c520030f0140c01c0f607090800114007030710300740c000b0000c5900500c410302007a20307110304060803598240f16120298050705010049400c2005040560f140b00d030058807000e503080b0300103c054400a0904503007550403075000418000d0f980485d00d801440000e802c3c2100c1c80c1c0312012940d02c0e0045076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 650528462 1250 650527212 650527223
    0xe03100c0816090b0a02060106141e0705032a100504020f04090c0305100f06060f020c151b2b08071b05010c020606030d0201020f030a09052b0f03050f04 67
    0x412249628003c4001400030010454070983c0c4042082c402920f5841c01e001e404001f483d150340701100e01d001741007503c00324a8500c2c5d000302071800102d41140309900140003210103010074445240312030000e8035030000c01803000140c502c60000c448121400c0418452401100c0385c82d106c2030002588030351300000d0100c1c1007510002070580c02c50403c400d00740303090b900003000b40c404d17059001f90002c4150070018003150340d40c80a00c003a1351031b24020340e200c40901030600010790080c0704a814514200001580708085c065145251082e80040244401140344000c441c40d03000159080b203001c00841c003054201d01c0e1142406080e03800510041030350030b0141c1104104601800400c0c1920302d111020641d96600070001c0243d00d00c0d01038080e4503458111029480b03802901345103030026006008403903145881c0d5600c14519912040c07550000c08808109840921414041d4140c520700300c1c4001e40c0145c482c2c01003000540458000400c401e101c5911581090b0400b01446030542d0b45184032904180d009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 650529712 1250 650528462 650528491
    0xe010312020a0506070f0e090f040b0c0d1109030c0109120602091c110f010311040b03130503030c12011208070f21090e090304080a1e06020a0e03100c08 67
    0x8640c100d00d00512a6009040d5001c0e40c01446152a0024118008003100d0b850b50075001380c0070020481e038202c080784d1a8072000c1d4084009000240392030101640403606072003903403d010038015054100c8000381d1f010605032000041c500850700e400c0010601c0c0840074640410f20500308600a160864101e40081c0b02c2030f008104004959903149040203081c2071a20307651504001418880008040d4000260040b0921a48100194485d02078160f4603242201800d10b403528100250312158002040d0100d030b1458100c0020001d08180002c60003061040a5603442d072403502c0080440301d5043e40b0180211524a085100180d99030054038280d9400641c101d110708840e08220381c000c41032400d0b064513015001403541c9900d4010552100391000c40c0385038179890740c03015182d80d6244910700504c0c0140d4002024940010030304461001c55002c40303c00703c10510540e0352200280d800c5001c4400c0410001d0580785500d090800048020319441074050101c00f051420290000380080c0c8043c0d101002c0703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 650530962 1250 650529712 650529743
    0x30207082b1205150907030b100f0e0a080624030601030210032c1b0d080903100f0203040201030b0913020f0f030304090905010501120c050907030e010f0605100203040e0103 76
    0x203040c11080030040650140320354900742c1103034484d240c1d2001c0b05500c5503001d0804501074600c030b80304040c0819006031003491001c291210684801c6c2e01b085542c0300b04a40040c061b199612050740305d90050039800c005203100d0611300240b4417609032501203200810007541340d90300319560001b14a411650140c0d00c0c0450302d000c03007008401500c40c44601408411344202004518032801c504149026040820389020a6001031411481c2503444401c1d6400704140c091180410f40a01c020440010014103d54001c2025030540d420703154200e00c600300c4698044104810743d6054010042c00000031a13080390070389081c1e64030300401c802d01c000c0070340200070600000c00152900022826803002c01421a0340361941d548d07425000d00154101150355508010000405609a001d000082a80501e0740300d2120b0900d003d021041c84014081410551200d480002808082c81260540c84d200302c402701c1c0345d900304814015241c5d100c000100c1158006c010402500c800f044100c1c0c15241e120025401c040354 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 650532212 1250 650530962 650530967
    0x405012706121b0c02030c0402070809040b1903060501030203120c0d0309060e19170702060f09061312060515060405120304050301020f0403140102090f040e07031202010603030207082b 81
    0x45500011660a54000c0301010701c0d8000141341070301031007241181e4010300b04005001c1039006404005003241002c0c85242250310305030b000365440c500040c00340b0140080050340800700303009961003510b01559400051041d03080034040040e145901000721890321304c1003c070300e0381e480c1c2d4a50791304001c0581c0c3d0011a82004125042450a20b0503401250001c00034554583c41e03a0030440012103158185480780c25100324050140c4800e40e4005150f242001d00c04039110001e50b000c0415076070b00100c2001400c02d4017100c00f000c0307400740c0f80301c207007802614807203103851030899030064040c8000c0413a01000341c074903945440458050b600c00741c0b4041e12800c01c5c3d5010303d15500a94001070342c59400403a00880100d00100500201d034001d404106084e402040391a080b4030851248681054092081505504040c1c00130000c2801d030008444240d592601d84184c890841825400140d455035020018180d04112460261400c007016100a182413211545464802448069004e0061005810050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 650533462 1250 650532212 650532221
    0x5030112030e0402190306080106060915090e0c0403150522210c051c0e0405270f070806060d060507091a120a0c0c080309120f040501270612 62
    0x41000c1c105540ba00801e0910008185c0301c20508030029281140018580f04140205822618643c0301c083d000e506001d03645e0669100d80c1620000d005001c1c00001d1406590b20109105282c1e0b21100d603110790035464482d540d0141201c2c00082d850074003042c000154407000c0c03d000107221000000c0125513051822802c40d4601d06c41100304a4420300400c8095504031038092074840c0301350180d0380000f1644003040403c560340c000000004040310720032616420981c0c4000e421544103400d01c5c556124000c1c2615169080300012040b941003440070032110f4030304101c140040d101c00c40203007100d8034240021a95a100c129006809551500f0101d000c00b0300509488002d059201520344014610040c291207070f5209404144e41c4e01d21560000e0340c42e58041c480c1803102800b6607504400f140321611809516040504448698020603200036002108c000007056503040300144103807524607160001d8644100160440d5141108150068880071200314040654800d07060801d10402c2002881c0000e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 650534712 1250 650533462 650533487
    0x5161809050717101716050907050d0f060504060f0e04080d091a070801090e1c1b060b0306010803030103020d03030c031b1e2604172a0303070503011203 67
    0x50106018050b00ca4910784400c010b40e0f441c0f181c6a01d071400800c2c5001da4401040c6c0c1e0b071000700c8039840c40610043c80c1c2034440301c0e08081203292140c288110841780400321000c1c480c8200059070b40c0e8008000d503041600810004220300103a080040b0302d00100c00040d6803000700010418500095000d480011551002610f2600401e10444410704405181d440000542c2d0110200300310400010303034125107000c0c00c03881c1c03014034025240181c120700c100c252030b0f002210b540c0144041258086054540c020b20501424001d00d40420000030f0034081c18101401a0030070041c80c0c00400042c00961030b1248040c81c1c99605160010700707030f0500c0d64101c0050014660740c54820002418007105140d10001b41402d01d903103000c1380c0303044030500c0b5020b80c0d04101010520444d516101c5c0d8012000c030000d041141e010707005031382c2144012402551060b49601400100745e0080505212105010141040f441040b83d10340085145092030000074241f800140f08543c146e0a1181e80042091b10444402441 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 650535962 1250 650534712 650534747
    0x90d080f0403052b090b030702010f050957030613050c010305010e01090f15033e04180203100c23031b07050f01051618090507 56
    0x54039203d181c5140ca4400309040e2220040c800c8280e00009544c05003a948040142d032035001103240b42506100c19500000e02d80000d55507906d40051000840e406114480c0078103401402c402224000300302400b541e084000c000c80d03400b1560041002c80400003012100002c90925400c3e0401c00c4981d80480811060b400e406019440500800000f1040c003c075455202d070090b00c145002c100e004408032002481000813805e107a5004002c1040c40d44d001c1c440860020b2404180008404683c01c014401c942c07003110013200b00d4900c1c4a08000000c44010300d0f40c68100c6600c0040d1424400c540c07491603121030705200e640c1d5090350401d007680c0414040416075001d4250b03040c4958481000c03004244a038005800310f80010880b0040c0c18480380000d048400c25113a130303811610fa075000c03480311200d00821084a424200040d001082c0108031031b404030f440040c0080340b64a000400075211280120012050008003036902913a10721040300e039410b070b954085000030385641d0b004045401001c901d0140d0310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 650537212 1250 650535962 650535967
    0x109080301030606091505040c032a0206010b030c04090c1116080d0c03120e0705060403210905031005331c05030d23090c0f100203090d080f 62
    0x208560900a181228050042000100c0d5240081800e540500c3c2c3e081e1020402400e0501061030994419080d105aa260010341540d44802c00c3c1442141d600e5a00e0141803040d0124241da41d04001d2140034018414902c0e080d1b042162003280720340594000c7c42c0d966a2901d080c418110b1242d4800e0300703151050000c9030b1901c1c40c83c0746095940c1c1240e0245440c50b00805041d40c3c08180191322400310664190340b040c0728400806042c400900280000010302d01581e400001c45944a101400195018015402451350070040c0341c119190055111402d00607024030401c0f160b43c011400400b0a0540000800e6030360724000c021442e0101c1420b40351403400444018086442c0b000309160450784203030350229601c4984c180050b49820a154014910391041052815000e11504081d0741500121f51300350010640c40859a118032044505401c0781e8050700c030360445841c3c281c840d00080501542d14100e81e4000290085d140e20852070b0142c0500301c807003410010007035100d00f1030725964a1f004141d40c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 650538462 1250 650537212 650537231
    0x10030207052e0c03020a0905010908030d050604060b0f0a0e0409350a0509040501050306250c0f110f010c0203120c030d090303020c151504050a0e0f0715091404091401 73
    0x134000e4108404000c000b42d014600850a035024418032010385020300000e60420760780d00c1318400a840b00900d0700c0d4009454500024035035182202034590745020000044d142c0c6039030b01004240341c1a550203c0d00c0389081801a00c007080c502c2108400c4000300103403169426400321008000704081c2d020100e60880c2c001001c80903564040090541603c04440500059990717800705603075018207490a40c41d40b05170301c0f220f250111b164602d6042030704240c14011801c40860300c84041c4c208011701c0c00c1c1c90701e8001d000e00b40354a180c00705003450800d00900348105504400e80100c1c4c2d403102d8000103829154800a00350b54403200803c26944441e040640c1800350049515004010350024449035000e03104110181510050b580032007881821002c150a2a01c545081004090310f0b0260044507508c0c0c3d104203034214210103000b00308520301310000070305400340307418800320b881c16003002020204032040409108103c0c6013075400090310001c40d80440c60038181d08000c40100d0040c24203500f95031130180c0310b9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 650539568 1106 650538462 650538467
    0xe09060d0f0c0303080f1e06060a022112010503030c030708030a060909060c020d02030a050d0c11070f0609090b03060610051b03040510030207052e0c 66
    0x41c010807442d1110201001550000e50004245000300000c2100803e00d00c0d4100d150101c01070b8000303407102420030300000080c24661046000040161f805482001640000c6481d4820710f031403041501e42e00e41703072a8007414900d8110303443ca20001586107004000d491490042c0380c0130b1490404166219041da60006014251032a915940401e1010162103443c1c60644a0b4400240400200078080c0c5001e400d10301c420300315801041a840407951110689540200c0b800740840d41806c00c81094502a00c00d0301a080c20380b140200c0007402040d02d12400044851503151302c056240c44103041c0081e10344c0001c1254056000002054450420440c260580e0069190050824411105a960710800703050502035a5002090600040c941342004007119902c40c20b046103000c00683d682c94a0310480f41c41d040c450750f5003a00b421f000e42c0d100040381000781016001085a028a450003 = true := by decide +kernel

theorem cover : BRFrame.Cov 650359712 650539568 := by
  have h0 := BRFrame.cov_init 650359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 650359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 650359712 ≤ n) (h2 : n < 650539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
