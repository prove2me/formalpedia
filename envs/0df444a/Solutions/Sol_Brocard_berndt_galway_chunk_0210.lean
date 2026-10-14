-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0210
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:29:00.954973+00:00
-- url     : https://prove2.me/submissions/d3608096-b59c-411f-ace9-a5d39e71e71b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 37589933 ≤ n < 37769789 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 37591183 1250 37589933 37589939
    0x105070203030c0a030515120c130902010e060f07051203160e030c01120608030c070f08061509060402090a0305010e07060206010803040605031f0306060302040621060c0302042112020d0504 83
    0x20090200601f55001c115001460100f4030344500e00c07400b40e1494038400038070f903282c840010311441000026940300a21710f008060401030303901c54032105240c0d1049880c640c9031401c14840807007038480d5040040803071007020804141c0d092000c016600c108036010300018507983d0440c003511a600c0240c80b0302e6258028034403990b1298050040c4600d9106020000a022038a0f0b03c030003455548003c815036001e0b808284100011082d0b510707a8009405240b0180c04142408092144a803a0694170346209039801c8000401917203841d415a482050000c2c00f10b07490076913a0400300d000b404020010321640c081d0302c00c00719005000151090494403040001c500d005e140600484440e00082e222040b0441c540c092416100f4685500a02440c090040060707410b01d10310400045503042d1f03000c4010800c50304500c98074251040a104100c1d500726034089100458200101c00038416504640482c90000ca07030b202540d64501c00a00400784100840400388101c200141d83e11560081c4500008500300f1080c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 37592433 1250 37591183 37591187
    0x60522030f020a050f150c12030109153008070210090e0a02040e0a050403020a0b0c04060f1d010e0406120305070203010605030a02091302041103010b0a020c010e0a0605030c040b030907080105070203030c0a 90
    0x81010022880507101c12240161042c400742e07000fa4060000306d600c40c480764001ccc955002c01c000c01032943d81c2030040720302d0b10000100100007559160448100701c0034400c40a200c1d140341201e0240da4000c04c5a8402008034401401620040c00741d8101400f0307180028226100038800c445c191341e05420f0f08600c80d501ea000c080c3c00340100500450450145a45140000b0031034a82a40500990050191503905142c00101501059072101080241400507402d03c0038400079620700c0724200b1729142c0707900c6011501107409001d19600000d50414641c0d42e05c01410340c80000f800070b1500c00c0300240250342d550010569591940c07840a03600507602070103d4902010390041c078500600c040d00116200d41240f02e1003400350026481100c140b8400034070042500e07070510084d8010b61090902d00400c402313103004103c003c00540a000140f20340000403c0d00c11455070260390040140d0542c031607813860000d903103c0d21484644541c240035070034403010640990003c005d076442140900003450410a400600f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 37593683 1250 37592433 37592437
    0xa020a020904060b030307030c0302011104150c06060b0a0c021905010801061112040608151e060a030f09060605120102040e0c09060705060a020301080c0a030c060522030f020a050f15 80
    0x10440c3c0342c0f070740c407a00784a054a05101400c2c980b406a200c800c031084490030080c2c00c2d554005400108514200424007404208122070800c00d170b0949860401c0c20120300c0c02a0080c00150005506d000c0045100000d00740e00040c5070b4403280c130030b888815150400b03035101c201c030351598000c0e140071070490001400201d225000c0919140c0316002101d203010000b800d2000c0355401a0460f40014101a00300483c005c18000f40611024080d114404241c0303881c0580520140ca22a1903885008001501c041451086e04084c4000000e86000c0003401800c1c9008001003007284030300c0d0301812492407800382001c010720076101101c0e00c40030b846805555501000f40c03c1c1d40708040b125130100061007141c010440400045110721128580103a80b54182664940f030701c2403a503001407240030008014800548180c81200480c1c48038100981c541e43d0341c0e202c03040d2002c101540ca4200403e004030010901194104e0f0300c0540b40203485918169403290107000541c12803852a9400064004640c7d000813030303080c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 37594933 1250 37593683 37593691
    0x6010b030709121a010803092b0203070b03100608010602030a030b010c06050a060807090903021f0e030a090e0601030e0a1103011107150c030b030a140304050d030201050a050105060a020a0209 84
    0x503104046588480fa062640d4540840c25100100c800c400251000e0304402c906000d0034603600203600740706407000010000c803050840c0d4170030105000a186d000820140307110092650081c2503030502512091003621170b401c01c480d9144045011840042c815006031459410707600241c0c055850301102c00e6094001e00b0071601c49604101136050343c030340070400b00d1140c00e0046030040d80200700d180ca8851064a0b004851300322460300c134070381051000001c0d00081c5d40161000c0380c1402d18010f00c04080309500400100204070b01d20b02002811280c1d4a42c0301d400300c410380381c08070808012031b254440110101c1d4082d0740f41c0345140d886115210042030b01038030411842a030080000c02d8103061007407090842c0d0440302084609500b06904085140160b02821031410054501040b8540390000044d50b68000c8141c054078102200c868031482403014401c48014100c0070f00100011a0b0910340240245004c86900001d075251a0020071031380380c101d0460b0322010a40c0e0042c41d11040039001c10044040181c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 37596183 1250 37594933 37594937
    0xa11030601020d05090d0614060a080c01020304030b0901060e1609120305040501030207060e010f0f05060d0c12050c10090501020d020c0604060e030a050a12140306031504060b090907150c0506010b0307 88
    0x140d02a40014090b010743c280c28120b6a08c503400f58102907040c0400e4801310317084a41c07a0341154440244590340041980d00301c0f50817121081d01d5840e110000d078010038468001c030707007a03401e41020400c0340c80f440d21b030a9a101c0740c540c0d54070384015552111405610b0b050900140081c00410080180d0341c80780e0042c00d1601e004070f100144d0401c100c454079003110321502c0300941c29515900c0006c10031070548940343d4440802c0e00c2c501011107482d0340340740510245005149616a02e144d602080c0201041100da0900e03029090907202500400b0261168900c0d200305c81c014800d44400c0c070300d054404241000800030180c001403c02e81482c009503907010816040c0f0b6090701c10009541e0100b6001c00200e000d90b4001c00361003056800240d80241446d459191082040c08104244980c81e1070008480220060b00c1007540d01c26121403030450301410459009980c401c400400344a2817910100307030340d400c844944103047da95100c0000f0035124148203050140c4550040401003114170409401160303c12068 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 37597433 1250 37596183 37596199
    0x30b04020f0d0b0106020106140f060c0312151e010c080c240a06080304080a030807030209040f0b01080105030a03050301090c091a03010501090b0f0a03090312140a11030601020d0509 80
    0x40340031481c0c2e002c45680590705024540010011180c0a1007040301078040580081003503041440440c2e100c0500d9001c417030082030002400c1100d14070501c00c0d1600a107920074910686e040402e4220081ca04142150744515488002d481c411a0764501109c500c0300180c44003990242c4030b4544920381d030000c584240c943d020b0f401d03504484480c4102e120305011810103901645047c446800c20448855070011080755004110602260f0400076400b6a003507414981100c03039941e102030403030180c0a460038084e000747c00c1080c80106c184158012070020755081c0c3e126800c0baa82c62080503502d00b2032040c0500404d1040006000031030050b0003d2500d40e540b410910700d943c0c0d6a18403091020250310700040900004401800b040da401170441000b001418102c074248948140c1d40406442040d8806080c140c0c2c400204c0b00b0180181c2c1ca01c840d0030b0a100040000c0302e4031104c9001144c604850b1105201e240121455010307000d401600d0045030185d000b440046032043c0c080c0c906078420710200b6848040c0f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 37598683 1250 37597433 37597459
    0x1050f0f1207080a140a08030f040302030405100c060b0a0b070b0a0204030b0c030a05090c10030b030a02040216030314090c1e0301051e070207031e0804030203010204062303010f030b0402 82
    0x81049840c0052082c0c000510b840d944c141006030003440741e14422000c642101514601092084d0309483d0840c0030300c003141d42d031b945a924040c0d10391b1060303500c041c0d000b0201d42c4145d8a00c0303401c035149410380c034002d6009110714070800d01042135403041402136002c0d0a0003400b10002181654840c0c55000d00340d9a001440d2980302d44640100c802c0c110b0700c1200000c03002081103034804c41d070301803550009000f0004100745100207000403a00903843e82c0d0782080650710012020107a030208040c000c01a0050000c55448100146052070302503019802e401003070900225010450381c0c08079440c41514204080d000885035207080025007908a044201109240503090f00711f660f0078410680945000b0440303554112004185410701c0400900810035904000c00410206401e0890101d801011242a04d0140301514128000d0300550f04042d4166201040101348940c00c00b80100013040c3d2540070316128041000421a244405d01940309240c03c074400070000a403148001c036401500c000c1c0009800c00d6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 37599933 1250 37598683 37598719
    0x30705071401140115050406020309040f140a05070e030304051f0c0c0905060901051008070e0d0f080c010b06040305071809050d02060604050a0e06010b03040f050304060509030d0801050f0f 83
    0x1a200550460300c0f00740344010440241d0881100d0103d4902d814aa414030340342040180d16806148031a82c0250f807211416107006c0c105900c204c0c1200455180c41d02c00c0c0c2090580702006000448407a008901c080070704411516001040e603040391402400381c25007140e03021040d0490601e1401460900c04103500c80400285403000f40c00141543c2c007c002260b01d0680308204000f041170348603d014920b2040f076144a02d40c030000b0160b0050141c103298100d0480100821701d8151054009081c01300350f483c0c1641003100c1c410080000e400010b0003441014107181c204405845280b00081083d4042d020401509000303001134007100403804c400040481c0e190f10340c3d5003041000b0b2150001038022100f0080586840d11480781c01810506041029001194501e942c81106000d8505080d00c0071001404220442000984082d4030805480d11141e5444000e8403c3d0452140c0350301c80c3c029030701c10034003c6103e50311050495900401e03840713803110020107010021640030440d41d00644608401000c2c61 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 37601183 1250 37599933 37599941
    0x903110f0c03060601030501061704140a14011a181306020a050306030d050408030f1c15081212190b0604060e0103050901110702100e0406170120030705071401 70
    0x80c5044000c0d1030a40d203450100350410b1070060031981414603060043c1725180d4440156050b0020700800784006880c0d03800c141504400c06070b454808c0b8810034641e50100000d003a04800e6042d4008002c0c044e12500c0c0d20007241d010302c1c2c1d143e01d94102c4191010b51240c09000c501540c0c0186c0300700b20355443c0c0724843d22b541c07041ea400321001a0105a0001c1801000d041c00c00c6401100405450650304083c10302441e546c503403181c01040d085001e0301140c501c219038a502c48244160308a05400c1025405154886032603180c94401c440d01800740c3c0000801d01690301c3c084a0007403805404800c07255540075400301c02c100c000300c804680185c1c0d60010554944880c4003c10250003561100800410040001000d0380c13402040405c05904142c4810a460b0340c200666004030340c1190301803481810150304440c1451140074556005040c0f4400140d500041558031812612900081c0b00300300c030041d980d0390070342a80a950040084100001215184100003605003580b00352410550511060119401d507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 37602433 1250 37601183 37601203
    0xe090703020a0e0d03091a09040212040c0902030601051215040504030206060f010c02030604030318080d090b06030f0a1103070b12010807080d1205190e010e06010f0806010306090311 80
    0x401d900060742502c0b640c1201c4400a02e00040b1070700d19001316140c1d00101030a48910900403022402400907098510203415200c03022806402151210440c480c4409139020584080e102c3c1e503940c070030128502c40300e402181e01ca2130040c0c6426181294400d06000302c650000c200311801c01181602c260203903039078040e80d4000c6001e5070003401e0b2420060200051085055041ca05126440410800588001c00c0845d445505810002201c04202019520840d00c070a8000d040c03620004070007d42e038420364040c070300207400380d0000116913480a042c550340d1426003200c145c06500c18400f94000445140c40142030a80c09019034000741d90328040b0180c01d4002010000040780174100501146804125840007400d400c001888580c40444003c0c02c00d014505d4587c04060316800040d01103098040e00e040039102040040104e021008213660007001030720b040030818002c3d4000014010b140701c030700c02e058818000190109034a10b640d03c00007440446011010700000500022007207400b0b2181c0400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 37603683 1250 37602433 37602437
    0x714100504032004060510140f070f0614060402040b0306040b150d1d032b11030a0209011e050a1206030b01080304030510020f0405060703030e03030c04080f010513080a0e0907 77
    0x103ca0710030070401080c0c40840e045280540c00480c658143d0560000c02c41d100d0502c001c90503035a070038901c41c0440c082e1240e4500508000e8a8001507002c000d540e42c44412001e8600304420007907121801080b0036446144a86800035406102244051419038003109204600034000e08503c414040d0600b2582c201c076601c0c1644a540703040c83ca00d40f01115400214444240c03028526290203003801c04030050400b11102c0380d20001202d0000c0310700b01039100705565a1590450b544034903080c080400603510600140d40003c650444566403c1410041c0740300000141c0c0f0340500301094402e08517206008c540c1107201840e280c01000010995601f4000d010b00a68400341d070f0351303038218103000b483e280001043c61903840c41007004031001c0034004199400d1705d20440d6543d543d040340e0708044010b041c0c80210800580000424003119583c40c1008204603600d8106031105103005143c01e03400c88900f02c81540c2d801c511142080c00240b080c100070f041c0b02c6c905043c0130802003c000082001c141c4102c41c9000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 37604933 1250 37603683 37603733
    0xc0207051906020c06070c030f030e0904240b01050a0c02011403010602010b1e0a0b0903010f05070908070905090d0302090a08070602030310080604020a09020c030c0f0a14071410050403 81
    0x6256410b20040320072050a80f00e1501d1b20110380d0f00c648480b9011f20014024542082c1d01c0720804d84240f90290803008020184407460415082043c1c01d0012042c0c1620501e40c0100030702c42103050781c01400c400303c005850701400c000d60f030403060307030700c500b0122040341003290710190000c0742004403010303502074000b50b800020038410100511140b040241c0b0b081c40591380c842542e044d143d41c0c1c0d81c284030503a110440b04d00d844002d50800700f4050302202405002c141d0070541005615680311044100300d0b01c3c0b082c00ca4403841d541d071980304210b41040e9201c00d1250440d280202920340070390000e00c103a840161081d40401e42da04205400d200d482e40120b8010b070000002d1080d441c0c0c0d401c560340301070202080903043d5410a03900013000c108143c80360717410140e00801c0714940c801c0c1c10300c20b4841c1c0c0d0f1229000e94810b2003180d001103440d405507100443d15100d0038504e14183e100d000030883c0075180070201c0e164229141e20100010078010f48034800401c40d0400003c00003540c01e4000c01c901c4032032004012 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 37606183 1250 37604933 37604939
    0x151a0d0f120c0609050f120f0910120e0a03020d0302070503120c041a0703090f0e180102040503010c020f0f0d0804030518040f02070b01060509011407050a050f060106030501060914040c02070519 85
    0x2c0d0605084400c2d1f00e048031410b00c540b81000402000301c0f401903408840048000c0544582607420311800b02d44141c555103001d80d9140c180c0b0010071401c1070a4031a600b07450f00583d040c003096040780242d06006e04075a0040c84030307214041c02e4203013043e00480501d00703c0b0f080960b60b080031421070302c0082131181d40d0080400c240341050780101c0408050140010341d03084480c10402c1f40000b00100074120600f190401c400200d222600303504803406484060028040d500001402940d203101c0c000301c0300d0951007120140680c3e50300c04154071928040740e035600143d0f51607946007200c0e80d802c92890002e08400800903e07001e40d03294490b55915290301500580c8038600b90908078007410050307121409201003041410074580e03114400d0b841d0840c145a0302d644904030b03424080d2400514a500911501c43c80c0e00310318001e4000683d02d030407110242c1d4148090303030704c83c4400c48480049106003420a107422480d1001490b1a0308104055035580c811a07071903550302c100003910080448541700c90030304110018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 37607433 1250 37606183 37606213
    0xd05011502060604020403030509010507061b0309030206090708060601140c0d0806011b08041809021816030b0609010f022d0f01060b030f070507151a0d0f120c060905 73
    0x10b58460b100301c1341142401e1131134402030030720312810740c83d82e04001d8005003080c200720069111064002410744521000340741602e01130018000c061081c0c0144c413441c00001d0742c0000c00035500701550315404c05030200392903200040d00c1c15282d4a04141044105100c8004c0ca02c1081241ca66542c0c1544d0b00c1c45078030f080c510000741c0a1442182910044d0300c8021031880420801d50858049072560a40b031048482080d051400600d0b10000c001d521041a49160820314016079a40e8051026025080d01d481c5503c10107074121910104165004041800248899809001c5400590102e40140c4101c1c000d80b03000c10117200e600300f80ca076404205032001034060703000405c030348202450306030001c101090810340c0c1c1c00c0f1240070050082d84610180800100010312400548561a070700001804401f40000091005001f13140e4599603030040303500700601103281c00016094803503040945e00014a58903166540c080d480c004403a41070002050030980041c1c00e074403800720341d18062800f0b845800f20403411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 37608683 1250 37607433 37607443
    0x3120a050415022d040e0405070504061205070513020c010e070e0c0a02071509030206070c080118020d02010315081e1608070e0a0b1507030801062a05030d05011502 72
    0x600101c1032051150101c21542200e0070480b0a40d408010845600b1000d0031807100d114503080b0300d41b8508904107000800c9000100035042e04d0007103600348402621a00030562000003600c1c05052a80302d0601006941014401e540080b82c021350058a000c8a0041150949505901e80c85456200010402c45080d030001959004026454041e02d00441900025a510250b0140c103e400181486180400d4010001203006540c043c04064540b0b4040c2450340741104a0311590312903500b07100300c65080400d003c039459600c41e402007000301c81405a80044005000c0200d0001600d040003001281007002000320100843d68003010003a120100e4183d5403c1211400130442c0b071030a074440501c4101804155982a18a01084090540c0d00c0a2000c0d001d010141210754202d406542c00201d16503600008102d220300076201c0d0442c60f43d03900c0040f6107950260420f01030107170001c01e8414200100c0440701d450f29010300304690908041859013000c95a083c2d00044540b11000c3c1c034910415010700c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 37609933 1250 37608683 37608713
    0x412060507030501050f01050c010609060803030108070e0610050904090b1303020708071413110d0603030e0a03150906020d11041502070e0a0e3909010f030807020303120a0504 77
    0x9420f100a515080c085009991401a0f0a052220112300582020025031008000f03150b00d01c07007072102d00c0d030768401c07692070350700038056803465002d00d12021908076200810107008241c05130104030940c0c100ca01c1110705801c26440981d000e610b460340395001c90f03840b148090181c40c0d80002035145110629020b498042252300441440e0040d54041024540b00c03d85d0101d1900c0941300e0200038070720300100f0340040809941d424034070000815201c0d144031280d4068410b891113030300c5000792140700c0010481141294400101640701d21f03009030440013a0340d0050403019129a00160400000440b4a410350704074610841b030075080400d0401140c50f10b0380ca504041003007800904000c0f4144261309160180007488002c40988801c141c00f1108000c10009440820a0b0000e01c8071440981201c0d07907410301f607401c00440c00c2589440038424642588001c2c101c40390301209040300c500d0f40e500c0070180d40014100b030780d150000703129004007402c094000307920605501e6000581842c092a2150340c84070600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 37611183 1250 37609933 37609937
    0x6080c09010905090307050d0c06050c03060d0303020a0201020c071403061b0a03090f0209090a030f03180605040206070c0915061d010806120a080c0705030c031b04090204020412060507 81
    0x9460819240c580500050540e80c480340082200d54851010031302d103100d0010010002c2c402c807074a0b50005680182c82140e10391040c241030041e6251000c2d00301d0140019140c1075803001801d5080030020b8082e500030003800c0014000542010321b800101070414980390320070910000410718000e014a014003131654081d0002c03e400602c2c450ba203076801140d0040300d0499040c19070b103401901c00c0c00207445d880f18005500408a604502c4c10580c1309499580c120400c502242000b122040d0341402405907081c000300f0368620b615100550307142e21020700703805002030783c10081c10440603000ca21030340282c10140020720380105400c5a400808003a00d201c0d80c0c04002004101602c2245003801c0009040c9400002d1801d0750316601c900002072000031000700061414814500180100522400501142060b40301910813451703a0b9024503031100000280550325801c043d000c1a01c0c0341483c203105410030b0020b800080c80d068180e000c44c040360700a0300081181908801d0040070007d0900a2980c0a8024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 37612433 1250 37611183 37611193
    0x106090f090b0103030e0604150c05060609090c0103050a0e010516140f04030803040201030b090a0b03070503030f0301060f05090a0306050f1b0d020a021204060801080717100915090501020d0608 85
    0x60b114a01c01c12018040203003003000c9040c18040c90fa85240989010344605c0300f13582c860112040c40a0094000480200c6050054000140580c5465081c0920816120001d004001200300c01180100401094051040e0b80d620030165044401d01c07540784a2040c094001141d410740d003070050102506906403182c024010451519844201420358084075407000c0e15548a840380d02c0141c3c0a4081d000d101c0e034014004c0c030b00f0080303c40d40d503400040d00701c07800383c0940300311980303400605459200303080426000d0b0b0010001080084c2c802d041e40c0100340b0701850542d041c03448400010344070824580c4155084c644072828441110720f0b030f0342d05541254405a10000541c400380d0340740d907103001d100d143d910079640c0401c0d070900642c024410500545840110341d41e445464800241c11500b00b801241d00c0d510806d0000304090104207401070610800d01e0090840c40104441000640304800c4225403d00365a103210744011440d020300425640f29000150f03c0700a8103041c1812039003e90302481ca650300c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 37613683 1250 37612433 37612451
    0x30810080c150d0f06180509150601020f060403020105010603050a021306050319020304050d080108031201150c050f010501090b010306030213020304060902030d0e040c111c1101020c0106090f 84
    0x400181000c5644081c2e6040100c000001815129030254140703120149060400790703548100554895425241800310f070b107000c08078141c141b2080780c1c0b044641015542c030840346e00302040b6003d40ca07503030f01980510403142d0b0b07980700c00d03038050901134241c50840250391508010f114040d054003689601c001c2e8080114189035a0708103010480c03496204140510800101240c1ca5800c1c0d0781c80b481c20078122140a55503400c0501c0c0c4980d079504c88112034400102410008200d9181c040700311002204503488600c480d9081c8131200d8010001406a0818810000b4001d800903c09020000c940c8035035000010b000e6150001941c15648050034050406240120600050395070000280621682d1400181c481d503407231400e00018040b02c07102079494865508603c10499001000c03018540c0260307410300000600c1c800c10307035806102801030000c0340c00800395003183c0018a042d0040c40704451405c1401c80c11445e581c0c03422607000543c07000140e5128101480700c0b44540c01040c00c0200344031004c21411407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 37614933 1250 37613683 37613699
    0x703090e060d06150b0412020307080c0901030b0712050f0f0129090303070602070803010f0905040b0708070e0406080c0906030a05150a06050a180b0a06050405040b040213080307030810 81
    0x2d4400008141d03a40d65240140e0512103038111101a1074001301c0d0941e80c58449140f020866501c8a04901c40c0c4074640010800c2d003030104800000800240c6009070990840c1e941d4980c1c000c00400e80003c01008003010610306907940555070141a1004040120b428015080c2480c1d860581202c0d0300801070201440d41c944140c0b407165181032103680c0898558110500003420752103040702c003400745800070407080300740b01d800320085048031a0a0000786880b40d5400a040c2601e104407405000a0081c2e80094145406004d429504c82c1180c0341a08264a031a00020110351440c1c200f08c2c1c0b2640060194080c03420b10410080e00b11004400401c00c45100c0e41d42c0564411071003030b9070101444010003142400c1c185401a00241c24010148840c081d01d8564101a0003502c0d4500c1c84107604049003003405091003401c40041c0c402940d030b41072500f401c201c1888090807041da50746030415420814481d1004070f000700366014222560145a650006003802440040e000d88a410b03015030121040202003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 37616183 1250 37614933 37614949
    0x903060906040203030a0e040902060c06010f080f070302040c0c0b010f06020706050711040e07090e1501061701091508010e010204030201020c0a12110406030803190c0512060d020f060706020703090e06 88
    0x1c000c7c42e00c2002d0390300c0d071800300e0302402030140001c6d000f2102003600803240f1004510f5078161041c600380403801598828600c0c0d070741c0311203056002a60300114010300150800350008840400740e410440f445503000d44c4e81d800850002da01c00e25901282d00d00912000754140102401461280341441c108461a1549043d101d92030b01d030f4034070455490205121210301070059a008100086041140c02d048040898440d4411044c151500007210004120b0502a9900c3c0550034110143c92002e03a0074440010010800004045002c40000000041c185000d02407045461f480900143c0c5462642c40007914104030301002070300c1102118014081c504203041d200314110340081c68402036802d82c0012030700804403600060806900007080021032581070903210710307c0d04070207400c009140d07c01d1001c990744e0280080d40d00b0160201401300700d561410401035412640002d10200c08182a00e00054040d44841d000f161802d402050722024540c11685d0700005041e4058119014601480054460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 37617433 1250 37616183 37616197
    0x109050603160c05030f04050a05010906020a0605060604080d0507020301050604020f070b04230105090d0f090e100509240603040f08130302030d0e040f0204050105030c0c010b060708090306090604020303 89
    0x1c0c210340e038000c2c48684101c0d041d410302c03500a804c0d01d6a401550541460541c40b5006060144203640c10000d0035510400f20301e004ca0703595034064111520380366035207405000c0203400c81d94445018000441c00840074490301d49000902e482d01a6182d60600c107050a4a40042c8207602c01c92060240e6041c0c407101c003007142c6010740e0241d4601e115035224504680c0c2d603241d880c55800c042801c0200c1d5070503284151b2091340540d1084d0125500c8407007050f8100e54510119060b040002d1000c241000b1816605040039000602a540b4400f800e0312140460354043c3c0c00c54200c4909020720641185000700d400303039503140c50820750b00d0303a29500d02078036240c005251001c0001c142c15000139030725440c00c80c160302441c05191b0080c00e488074402c09450041081300e0002c450345c4a9807801500d0144008180f00300c4041382d00685410f41590303100304104071607801003c100b1900f5500c0301c11b840f0690390307044001d02c41c883c0304085150303c0e910344601703052800303000518881c4284d00000502c40560740010546a80e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 37618683 1250 37617433 37617451
    0x60310031502040e010e0103051009020f0d05030405060307030b10020f06070807030b0d240b0f01050a05040305070e0403030e0a15020f07050709090b0709060c080f040e0414010b0109050603 83
    0x140d074141c0800000384101d5005481220881002281000340800301714107c0b030040b42190300e4584501d2500c0103d81e4485002940f0070107030b201000c21403c1009800010500403020b0700c0c00c0c56541c00206a407548200c038403100003942c03600310698a01e4485400140f601c01d5200401180c0500403402c0c0c0e80701d1000d0070360428428a0300014883c54441c1e000740c03071040805405642c401a1600c0c0542d4400400d620503510740d05145443d2050001c24804c0e000312000c01465034030801402401900c160b80008020320401100704004030104500b003001400400d080c0882081c42c2c50320b8100182184c4084480c1140c1d504007000402c04541854a41c01c2030320320340b5000580ea42c3d0b4010000c926445241c0c2c0042450003003200000b1007265507880640d0f031602401c106015942c0d4100100c0740480c05004500100c2c860310000342c08035007918080e1000741d10a030800781c40c09480d6185842d00740001c072000c0720444c9030080040c080705000e0145c0c405100080c24000c902604000020341030780001018095 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 37619933 1250 37618683 37618703
    0x80a0515060c0705040c0e060904050402010512090a0308010b0403030f0f020705040c0306170a0201020a0f020402070f050c01020f2e150f090e06010513020c0c210c06031003 76
    0xc91400c0c4586000c00600005045941c2c400d5070310304103078480c165840f44500c200d1504031043c05042c0075039418444104010840d0b80b5009820b0100802000050300a90421000b0311030064000d52401c942405001600001c291044191500805942d41608800744150007030000b000043c1d0407842210480b03c41e81484040d002c47d6130310480c90401c2960182d41d01c80d04110b6000081600f591145c0269040004c11201030f11103007034503942d01c05050400900503400401c16001144072022540450740c0300800161500300c03146c6074102d00380800325055034150052400c007480d0f9038040240c6070b85126144040c1540707058001d042d041140200d00301c070b80321088005119903402000c2d404101025001c0d00841c038083d4880e0a4410b6401031030140074030030f901d0654001c50aa2000270000e04a0344010044045440c00780407003c00394001c007480d01c03542e00c03c0c0220f084003a9510110000b0301d00b5401c035414450000501070034900f26038454803902405040080c0240c0008459445090305d4005031518 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 37621183 1250 37619933 37619941
    0x10e030a080a050a08060a0501050304080318150f0709030c05130e06070905030709020c1b120111032a0f0c10090501023402040c050d02030a06030203010c02030a080a05 74
    0x2414020366080040115900180318a029900a00a4050a00c46039900c080c69550070080c801309510354041c10b4041101400040d0001c1c0395400250780c081d41d41c145502c42085402c00700d03881c0050700392903641e031101e01d541085030708a04d070402a503004500d85020303c041c5240d40c0b19414003603100e0040d01e004400d100c6090556a02980212001180480c100c1300249030080f00200304902c9806028803038045c10600080c0000e540c020748a844a916019040d218880c21030244883d400014240d0889400c03603c08000010a10440b000f80c0103400185550b4070389080c80b00c000405215001000f00040107404262180450a4400002620410a40c1c1d41c4000039164070308280c07141000409070401c2d0000003000019006000d02e07500002090780401c900c4040c40c04407542c40007401c0d0840da455602a00980385c65003080c11100c8103814010301d8400d130b040c0402c0a070fa104031013a00229840ea9010011401c5c02d01c10542403c031107101650500340d000c20002c103680400340180d001b40e601c500100f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 37622433 1250 37621183 37621189
    0x80717070e0414090601060801050105030906010605070309080a06050a0f1802060903030c0d020a1704080a111201060b040326070803060f0d0b19110a0315050910080d030b010c02010e 80
    0x1034006800b0f0250b08040030b242c208035a0365078031001d0083c0c000180c0d250b4000181940a0004c0d00d0140b2208006082130382e0812300d0407540f036041840160200038048a0000d0381030400d00004041c9801440d003c155440d0601114050302c4c20075080c00300e900d1034611424a051001c034100d05016604840c6990b98519050000c2c0c658042d201c00140107000e220003440b0345076000501c0c60342c030034070806860440703540b4800082918001c0f4841e0154a030881c40340400061180050125020760003080b1815922040402900712481e580004045580002c2c06006000c01809600200e100100040b60850540e5194154602a138907004050940c0400800c0c460341d0749805228034400c026001e072981e8151800c0c103141512040c0c0e040c002c5c072200c0702c1062000c0111406829004524585014a80043e2040440060840c002d40104444450101243da40d903080a514096550484000c3c02d0300c0c10041c4080c1080c03402403c603400d041c078181075034105980240d45000d050340c090800e484015005408 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 37623683 1250 37622433 37622441
    0xc030507050f040e040f050706081503070303080609040c090203010b0406020c030c030d0815030625140a1101020904020c0307120f08040f030507021302030a0b0913080c100c0906080717070e04 84
    0xb01f11380110403010031082e9019810354800c2e1b00c5080300c040c690384682d007411380f1516180005030000341c80d0000501035040c81c60748c044d04140302d400f001e44035994400c030010480e0401c0e0410410309078001420402564104003401c61014114040c0988814003400642e80303c0084032007070184071244d07000500c00d03000000f608042101c007034240c405038680749000b060013000404811250b004a030507448440c501c0780086402101c0310850322440d0071620242512203500240d4582d640b91340822000c0701a4482c0c0c00038244a614180055803981103a1900c8980c1213001da4a07039081005007007d8040d01c6a0001c0a170781c0060700949039003021803040c1402c42e05072280c00000703504010308a42c980c601060590045105041e0b12804000d051050010040080c8003941c654041c0104d00300481e012889490003040d08403843c1048a884910845c445001c1d50301440821010071043c0c2000c004098020b050385604c8007840ca81042080c1c1520801044c8610152030502008481e0041c105562182c1d80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 37624933 1250 37623683 37623713
    0x92c09100906050105130213060e0d0c030b07021e0703030e0a0b070f1b05062713090506060603041509110409050102090301110a02060103030e030a02040509010c030507050f040e04 79
    0x3051000d54a02d080000141c0001e00c0b509001e01c600c000000301c0385a26100356a03800340e40c1d54200c09414034103401142c2d11080001e01c03a034000f00e0540c3d40000103203075601c400021481900e01c031540d07189c4001c000c3e050a0041c2d000381007110420120707500c0500049090b40689616003080800103554a010440001c4140c101d60740281c8005542d40c14071201c0b28092443c14443e00807010700d59001100d000c03000c0c1c1030707214040d0059018800f16220202290500d21990392102482d0680c12804000500420b0b50040c45034000390351b0400e130000c2c8034080c40b00e6944075401780e480c0ea182d82080e07903e141c1c258915064040714603070303640d070000c1c00c100c4840601981d00c0c2009200740104459420810b00035408011550311942c81c0c00c509103c0315617140c0c02d6505540c03081e0041d1400e41c1c65a1010380380c020712003c86035414000c00c542c0800503a124495180240c10301d50001a000c0a1481e002d01103810140c0001c042c80400e010340c94065085404540507202d4040c03010006444a18104200c0d0b020b502c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 37626183 1250 37624933 37624963
    0x21816080c0f0a0c0203070906080a0b090307080a0c051009030c0204020a110303011503050f100b03040c1e0501020114010503120d090203030c010e101404060207051c020c01092c09 79
    0x1080c0c802d0741e03400415420118000c1b001c1e289400d0341c90701550304903140c62140740c03955008241b0280100385807a015a41c0540c006041c0c9251400c00d45c1c136004190701c58824180441c3c2c0380b6114505102c41003010746901011024108100780c81518041c10b02c09407080c00078807403500000d261200700d2042d00650024003001040381c0c2c482d61102404031045040c40560070000f8500380009004168019100740101c8001c08008201801d06502240e07991006000b0798554510100c0020324510130000b4400780003024a41078401d41c1010002425101d070007070f1242d45400100300601060f60042401c0c10340c403410740d460070755440e065500c010184c00c0880001e0341c5400041034240c0002419000304a0706550030f400d5034004080d2a0070a0111001d00c50000e165000940009000800b1136004040c102c0c01001118001c1021021072406502c0d4010750200580005250310b0465800502500140c8045881d0b4640d1480e0340148110000081c2440c0d0030140780c030008107201035028407488050302d44c42 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 37627433 1250 37626183 37626187
    0x35060111062701060f120c0305070b090a1d0601110a0804080d091a0d0207030509090901060f05030f0c10050c0d0503070f090302010816210504021816080c0f 69
    0x50140140001002e4610419403541c0880c45510300018482c1401744c44841948910042c10311142d000306107032080f400c4420700000d000c0031001c9030701042140c00038803564400907550400360042c4000222140c0c0301c00090090300300d07041901140504001c0d8007040c2842c0020451121010142c5050200040074040d40350005010915000c046808107182c85aa241d40c0c1000d42d542114280b92955298201c685580500408040707241d9600104641030181c9083d60420f0110400960b0a03503040e26002c029a6440300104241c1c0702290f9071200801e8203c020b08010f54401b220603031210101c4011a03caa02c4184050f5200c40c001d509807101d29080d002100d0980c0c452406c050200e1b4010345d02203021070348900c041d01240f441000e189040e0707036042e03640240907218210111042a14000124103002008100100780440b8004000120a000b2800b003110305050042c4404e240d00d190092180f84802820031407005452907000ba400005454016516560164000664040c0d100b0303400d018600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 37628683 1250 37627433 37627441
    0x40b0a08040b01060c0c061110050a0e0606091314011b09091a010f050307030f0218011206030209040f03020307021903050d0c0b01050f0102010612050d3506011106 72
    0x4480e154500c1680b2034002440240d032903103020368404801c0c0800500005002800b4020f0520605035005840c0c1d02c0c2c403c540e0406007000d4110300303468003299280003450351080e207000182c0d000c0003880c4e0440c2084e12550380608101c54406404412040058180c8030514560040458250705c440300214181c0010380404100c0070b4014074a9826100e40f0702400d080c00d02a08408900100c0044840340c16100c2c04000003054038203603480e810041c840014540c0d5a0340c3c00d038641c5071724001080300076600c10303980b030a22051000140c40e0071101d08648400529150341440142c8491000350341240d0064180118500140f4080b072440c890404004d401114152052211400307003601441a07e10501c1503644a90440c08101d8481c500074201902044010004000302e081c10b003060b1403065010700c00031841c0ca03220f424024903004504030840da6580000404482e09500c03010741c1400d51140b4600c008a081007444840911741001c045408800d4481c0215155a02545941d240404180162a65494 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 37629933 1250 37628683 37628687
    0x14091806030d020609030a0c03210c030e03040b070f08041206050a1112010e07020a06090b0702060c04030503040302090a141e150312030a11130504060509060108060d020303040b0a 79
    0x90360110701911440780e20071000c9001050300f92244083c14000e500340003210384200d404042e9040141c0501c900ba00560200e00340c000301c8449403440307000001c10080c064102c01000c40c3c10f00c114140681d08103200500024010a00f15103915403c403041c600044500d081070b080e06c0c8599400505510b0720222950304000c90707500410700c15034144c481040031120b8542c15170554401e5424120905050f100140a0306020100c0950001170510481d0390300440c079503d035000c4907028807094400304001e004005c14658104900c65000c0c01c4074441d60706051460340c0c3c16649003e6400028820b001c82d00004118030201c0d07100407040c100a4507810b82c241454101a80c5a034961090f400314100c43c02e00198034061081041550b901000c1c1c005c10001345a0544d4075020b03000980354079200c0f510b4035400a1950002005000b0035012410a012002e2410702003008840d66035020501412045003048801c1e0b8001449562101090721440c804603c41d100083c1144916080180c10480102d0307668070080e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 37631183 1250 37629933 37629979
    0x60a0608190c0e04060c0306090603080304021012020f130b0403020307090c03020702180402190b0f07060209040c020f0708010501031110030b06041404060504021204120c050d120c03110405011409 86
    0x11b00d034808000060700c403e407500c10b89855000c0501002c0080002c1401130400240780d00d43c2007518905000310388c18070001035050764400b0501d806180d1010440300180100301120340d0091049d030601d5880c1c02d1030750340400d440e400035101c0d40390403551341d0f07119070001802a01250704403940185040b0020900520440c080b0b40c0030380b405c1c2d01403000701b880d0140806188041c1400c0c0d1740021481804e1401070401c0641d1603016407401c454440e001e101c50710030707612940500d03044200c158001e00005508500014070b131410682c0303c2c89a9a04000040012804600500e003008030141c0b21341d003403580080707025405800140142d6402460020b0005121003051301c5e00e903d9090121801d01a0302d68400802c401c1c1d0240c0303c411134104480c01c0c00b00340081c1050443da81c4984a60400401a08940c0c4500d401c113141e1100340800704103010f030200040c240601c18503008030b41d141810060b00c1ca09401c0d814682c0100d0240382d0500003444e0744407131540c05800585102d6030009004145103000e00b40c06c4e10440d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 37632433 1250 37631183 37631201
    0x403060c0e030c010e0d030216030809100201020a0e0904030e0315061306030b01050420030c1207020d0206070f020a05100218010903080703180b0d050603060a0608190c0e0406 77
    0xc5100766400001d00d030114002084550503942c134501100d52404000110040040c11001e51181160325240c01c00075000440c01140074814035915500c00704188100030b10040030040843e4410062400e489400255a00c9400700035500f0510b070b40e480741f03000d17550b07681d9500d841a4188203030041c0c0b51426191141c0c80c3d206100555071070f8284542409003006592481c000103048058404c01882a4202648194505d01042c0702c2140414446a070411a039401039440c2c007600039000034424951200e90101d642c00100c035200130400754024040081d1031b10000781c0041c082061040311061450310800041c1c06041d00401519040e0039083d0b0031074025071000307140d6041044140c002281540c010301801d000c40780c1110b601071400304541c0c1c0444820709640d5107542c50108144c030109500b036605000d0210403650580c0000c0c80e0034064205441d000d4024040b04045092282c24040311001007003c0300400e0440c01030000d182c0c0c1c83d150a40b04007416422025007000c90300100414048990000801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 37633683 1250 37632433 37632437
    0x11403090714030c01170901020f280509030c01030e0f010f0e060601050f03010e060303070b090604020109090b030304030206030c2107030e1603080c07051c0501050903030106020a0b040302120403060c 88
    0x3200800b54107140e10390340140307207241c007141d00140221050069650055400344c042c0000500e0020b002c149510260400c031403005c01c40c24003c2c0e40300c0c0da4613021400f8102d09210b60038100e0400c042c110023340c0d611004c2d00714904142c2c581e0300c00e541401c804c0029405904050f03000380f0480d4280c01d2801d00500f0808490741d040e124240c04100c2550040d0304450742c003003e0030841c1d4070f56070070120300d50000b0801508542e0984400c00400c1c010036580100c860040714040c010b0529810540001000407601c6c2d00401c1d4414a0309211002d80d0740d0020841d81180d03411f54100da280d40e07580c1216a0305014813205240040c0c4044846501a0410819980705080513101000710313204ca01011f0383d0b40e003841400c1441c8036424800c144040380001029000f41c8206000701c44901d034403440458803c2040d0300c44040d6801c00710303941a0800c402805000e910058045c000d60956151590007552a4040c00c4098003002865002c40e05240c030a1140e5002c1c45000256166a15642d04d064401490542c070001c1c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 37634933 1250 37633683 37633709
    0xe0c180406182f1e0307020303060913050a0305040603150b0301120f0212010905060a0b090c07230706020c01051306050309030c150402100806030a06020a0207090609060e09030310140114030907 85
    0x900055100b0317240140e101e0350003903080d0341d100e00c244218000043c1102490900030380e8000d000030403c00c6118503240c440e030340760741e04d0741d15040d8058141c0d41400c0003400f4004184d40e09200c50020b10301500d046500e50000021070b111a801c01d9030940c060303100c029400c60354020401c15510015000440414810000c42d5125038030311103140708031600b50075907641c00014000824034440c2688060f01c2c0c6103003e40000e05020101011000200078008a0b01c1280d03000801d08000b89501402000f08002080c06c0c024540450240c54030504801c44c0a0a8280900800850117080381003055400340c0140c882103450f8800303482c2c0c000308000740c00c9904a124021051581040c1ea100d003c2c1c480c0602c0011340201001c808603600e88000c2d41040c180d40701180704e1030038002406441405600300400c282c0b4000507640d4100a018594510000c9c000e0301b13640d104000f40100c0300c0700044418120348e800103100001c545007400403155400000e03052044110003000f88a01c84402041441c112100290400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 37636183 1250 37634933 37634977
    0x9060b0a05010c120c06020d0903020106031b0605040e0c04030507120b0c04030b0a05071e05030402031002040605070609170403141605010c06150e0c180406182f 71
    0x1107110184401c0103181c41001c241c0004245c0c0600b510007a41441340f1409414200c0610301d403412501580c1c426001030391540005c1040c1724461141c502c20100c0302c2411041a4203204c0c01800500c950700c10106082e4070f00340041c0c0c1810000f030a48000e154041e050b18030042e9600c1d6403003500c41d00c20030142c51081600c40410520f102d010102e80442c0d0340039240d000c3c0d50341c81c2a2404010080148248148441c0300c0060305240250040303544149102e0300c601e0748a080500525241820702180c00c0c100314410030040c00403d401c40203403107200e5880280420110001d2400308840318540b000c4141019003c60301000f081050000000852409000c4450412001060700018086842070b20301003801c00059401088043c0c1103580307c16031101107946c020f6604d240034140c0710011562003258103004186090300782d034681c02040044104031424041e0606200180034445100280d440c4d02980c1c401541da403c2604000c03001c03051200c1c0c1061074400c41030050240182d0b0245a07001c025809404070700d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 37637433 1250 37636183 37636187
    0x10b031b090907030207020f151806040e0f040305190c05150105092205030a030c02160e0106050a030b0d031107050405040b04060c0c08070309060305060906010c150b0409060b0a0501 80
    0xe078420450007031004046841c2c9407000e41c025031082c0001d0b6000724900880089940340e0010090352406208540c0382d441e6240000d00b5a50f05185d04e0349441940c041004214801964450703d401c42c101012094050700c50b0320b002e58091084401c0c00780e0b264801d03400d41420342e400a1180840d079002d10151040c1c03425120300c41c14904000d005241e80041d11101060000c02e05a098072091038070210050384a12032600d565185030420320441000a072a90104510340381c0c1070051205801211110340e00280c20228540200b03041401513800300100815040f2200340300e030308480440000584250031040c12410020034908104056030101d200b4030100260031f0915114039480b440e008102c140704d9031175581d242070291070040d02590421007407025403030200d40d40f040102000340c0300307481d04800d4078500742019081c0d6900900151240c0c0d8038800f0441c05981000041da02542e111100240190084c02c1034401007200c1000c0c5a00180380682d900108141381c3d1050600d0441141c401114564403001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 37638683 1250 37637433 37637437
    0x8070305091e010605060309010204090b09070e0d081902060108060c0a0206041209030c0909050601060504081b2101091103070501050d020703090509190c020c030a0b0408070803010b031b 82
    0x190248a601030008000e1100140c5101c200003060b1000124626940d900041d040d5042030307503001a2079600050820804016114203103000000741d030000007d28082030302070010045242c40c0d0340200000c440010400c0f6640d011159040d5000403140c00540f80d150b8001e545178000d02032051140318000200306907107100d0040e107089101c51303402809107555a0f80c401c80d440a04480030b01c1440203000010001410789040400a0842c1c0c0800140c80c61aa04040b480d10406a10180034801c00300018084c0b4080401c0400b003a000048498003811400000300d01c0c4111940c6940c1c841d4000100c0e90030902e0419044022071f140260242c090390003016080541313940b454820344c0d0224404100816100d0080c1d0050b02e503190188c01c2c0100c02c0d566441c00f140c40e507101103440c0d04000000030308090b6a40d40910451003d4186440102a91045480401c1d507420b0340e0345000e081d00d904035000404001c01c11040b100f1066202900c0754880d44e449070b4080d0740b0703002aa4800310250400070070380005c000d5401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 37639933 1250 37638683 37638691
    0x140f060f01050c0f060906040c0501050415051602040c05090405010806010b04180e0304030812091204051c0203010e01090b0906040506071218080405040c03090503090105030919030e0108070305 85
    0x5120a6500401982c243c1d1000c80510420f001c2d030400c804030034105010051003161000e001d09241e02d840d1906d81c51941c91600181e0600005000600c40306100482d010b8840c12682401c603681c85100003c0e6810582102c0005d50150030860600207895210000d004004420b460a0202da41c0f80e03149107848030800d0040a910345001c0c44104858143c07000b40701110413801d000019008801000d06086070b0258005070360440000400303a0392003e01c0415564000081401707410828404503c03060b00303100f13620a443c800d45903c44414942c4626085e43c40e911139000700200403105009001c14080c1c0310612090342c07041f411710006100003102145240c825603000c00900240c0d0f9a14030151070b04403c100c1c1e09101c050f6210400304a03061203449540c0b0307030b50164031995281d40c40c102c00c20080d139041041078401c1609064059000600000a41c0c0c2812000d01b0b20079100d80e2043c20991401408a520854440750841d50f01c09050308140c1035a4609000e0380c0341c0e11540c0d1680c03019000e941040c1d07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 37641183 1250 37639933 37639939
    0x405041a0303030609060105040807080a030908010203240a1e14060a17040f02031923030d020906070b100e0f07080a240e010806070e030d0f03020904020706140f06 72
    0x25045161005c6180d90003003050412505160711491468541665030b08031036801e51001c08400c0915811890501c02094404000e514500d0210203c2d0728030120b40d0a408008410159448040c0d41c1d400302850292803d804d40b40401241c090f044500741e0154499001e04c0028002c01210608051040f165968403070345910014a542c0a512020044020019504400098000001685d05001424400036400c490b000010207905003444060146441c0d2003840d91060500c9840c9200401958818031091100503102c50444021170031901c16044000c000210042c1000061400780c43d2000555610018040c0b503695182d0401203001415146640468640e0000800800c20f40e0050303403244488054004c9400705498001e02c0b0328034183c01100e491100d2800500c40c0100c00c0000a40c003039042d241c860b0362510002d0110341c071503c0c1428000100f0030b1141f401e05ea414061340403140c0c980ca025004550b904140c0c203181000700011207081c54614050008610340d01061180140a80002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 37642433 1250 37641183 37641187
    0x110405040b041b0503060414040602030609010f0f0b07061104030302071d01030213020c070302031c02010e0c06030103080c01092102061807090b0111010203090105010303020f120901030906090b040302030405041a0303 95
    0x90f05644980004081d036038060346030b003420905e1a9200d0748c01030281d8810711000d83c0b6414404200405100d050704a0150b00500d85020004c8149107200f030b400b1078032400c0348640c0e5001d950909201a11018031604c2c040040000d00004050740004c00d10219118010001c04d54520000100b01403a82840302131b60190001c4040e0052648a60007402e03030601500c00c0310680c40c0daa601090800c005081c4043e001007182041210441c1c080c0582400b2900070000783c8071219001c1c000078540e00041c003020300005000701700c8450070b5109622030707034485d500488e0011400c007868440e60081301c1d04428000040c019400803032078030360803a04004d0012191074003824085003400ca0080007003c20407011410400051440741c0386043c03c0c8002d502446180b07001045660443c240607240c189002320701c0010781c0c0310181c08148000340c0c6050728140042480c010071260b07480d0030704801505644801405646c012401d0008258001008004540c01a0342c2400401c1140d88060000791410503031980507001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 37643683 1250 37642433 37642481
    0x70603140703020a030902030d0513050406120b0603070e0c1b030a09060302030903123103050306041e0c02061009060303090b0f070c080318040203090a0308040501020d110405040b04 80
    0x2e8000e013800003042e140006164820b900042c0c903100740b03108100c0203e500014068807419009102c1d002820064a080c0302c0e032460148076041419003980090112031160011030b0f502c1c2c1c0c0500854004050800ea020b03082d080c0004041c403254488040c1c0350701403800248aaa00040202c192045101c0a881780300c6050300c3c0c000305030080c0d0b000400303805c2c044c013040040040440440141c0b0340900a200401c0da042202c481d01c10020151401003401340003440c000403400250301c081140e071701c4502030f0307000305450721161002540c1c44a40300e0076501060801c0c4100f58003d0b03002806901c030340c0d4604104c201c2c02d81d039220554102d83c80c40c0400b0300021400c610a004040d13800008015910750200441d15101c07982e00d444903030b40900d41003403025400005101000c200c0d00d80c564003407100100d40442c1b440c20314042d030b566070b0b010070f080003400e00100c040001d040c00800c0d41a550fa105100c4018003054440c10420486680301c0d0245078403a51500b01041c200d41010f200b0302c6482141c480c3e5a40001c01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 37644933 1250 37643683 37643687
    0x509040509030c03071b081518100504080a090f05060d0209030307050f15010518011202210718020f0307052b0b0414060102030d0207030e0a0f0302030706031407 71
    0x40081035071586100c01c100720301d160f000c204018080580643d40e0440216040000e1840680c555413000e00c007588003084801034841c00b0b640c4141c218948030901400e11080d03000d61400c0c2134110010303203001841e1204200c10700c00130200400d1080555a2000c01d041e0b164822022002541e015054124405102c1c015008c0000d50007031182c10f0004081301c2c00c06600c0c1d55043d01d0316056008460b2141c10140c106503150810b101c0c0c0358050034048a090f40caa25103208c00c410310120510900444129004a100a40d10f07404580d44400344243d94490740f20744100d00c19503a4420511a10447c549000244240000f91b44242d13101001109851465500c070468222095040402080b4440310b46030100180010800002010b801c4001804500c5050303000420003220076448850f1400ca0074101046040d07030f400f200301c503000e40d4070300780050700da9080d42401c41c2d890103a07103034503a040184a4400306c0e69411814001084034422070072601c0003611030b0002c40581e43c1440a950400b04400c0c00f00f19158 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 37646183 1250 37644933 37644941
    0x20607050904090f06060f091a090c1209010501050112090b060d08040e0108060a060506120a0507050c0a050303011a1201030b3301030c05040302010203031306060f08030306010207060c03050904 85
    0x10100400c0803c00d4242c64407401d9480b040b13494201da407180c3e07520003000781c4010200311070020854548104605015101c00e03212440155149034482c5490100040502030704106880c18080114a004a64500842c001740249021b00030356000c500d80500003a8171014a00a181d000c0d0360201e0716036544d403160030a000401c10010002ca80b0749030140404541c40c8058200180200640030051200c0d091007583c6100715001e98001c42d020350300c104007010480724205075144d0041e0998400081e50707915908200d0b00ca009800a00021b4000c00c500c01080c094004040c5043c0c451454401e400c0c042c800e02c00c100c241c41009210702d4201050401000031501e100b80c2c1c541c1c091210b01300241800030b1007400322101d85040050106440d1150114850303540e0521414400500724248645000c2c01c1d500083e580c0d000c0204204400b880040ca00800c02030560002801044000820103280303440d003000c0c94407a0001c0f0b4803680140b0a074140020228441c0150701c144903051748030240380840c2c030350600000d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 37647433 1250 37646183 37646197
    0xf090902030a08030907140f0306070e0604051306050414061c060f09030315231c0b01031211010207020607030f03060f06090e0a05011401050c0a060501060e030c04090302060705 78
    0x50302a00380c5902c04240c03900000d5210351106000783c800313903060440149541070003814007400f42c010080e00b20b210341c40003d00b040e04680c4078140900f2031040000051070b41d1045c0d800150304900c03100f209000d0404190442d4080c0e5001f1942032018071440d040b1010242000c036000c0da4801c00c40d207060300380c0065180148070305901507440403840f000c0000c142c4003a120654002c0700000d40e19080c1e42e0800d40b81588140281480000c170303040c0c4120fa16a401000744250048030311540c00c0045917407a8080e581040005240c1c4113a03011040e6030340e428240003140c500102c000205104a400341400007040c800c40d50300315802810b840c142246501c00300d0f92000e03480040828076a6400001c51240b0901c16640001e01d02943c484041c1814604c1c00210160050800d03045035082600500280c5088481040b80f40070030b18001d511540341d094a10b28000112402a100074542000482c2c000d9124119641d80d0030b003541290440c2d4801d2091000715106600e025005800040c00b25100d688200018450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 37648683 1250 37647433 37647439
    0x6030c1e0a030807150519180b070503060102070b070302060714120408090f04020c06010312090b030a0606201b061209030309010b12060c07030302120403020109060509070f090902 79
    0x55458040200d071024240340c00039201c03504003007004400c00c04c80302c04440d901580403100b40814146940b8004d54030b800f004040c40c41d9603e4007a008509582c01880c00340854101c0058051800d219001500c43c0d441a40c1960060103030000119004003e5000c0703406082c0d241d80140f901c0d40e00e00e001141c0c090703c010b02c501d074010300400c010f6100030416034841d8004d501078003105d80d50300207240401c00d01d8200c150105000303e005102c5400481808220541104d1700421058410f61040008031181110398110003805000841404a1142c080d400b001c25101c0c1d130344586900400769050a040720b000c28203d184154000c280003003110803901f0728480150b00203040e00c0d0514409080710b9002c180700303c0700145694004020409151024000c085507001c094a2080b618040700301304c103480c1d0500034480411280000362036820548213074121051000c0c000d4800d1441e040c41e1a000b8083c140404080c1d4485040c403010070045280410b01404450100b103501c0d003483d19000d01c40c40a003441e84001c3c0d034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 37649933 1250 37648683 37648729
    0x60e0604031406060907090803040e0c0708030703050702060c19030c020304151d04060e0109090507090e0f070605030601050a030b030f03130e0c0405010e1915020f010605060306030c 80
    0x800140c00c600720040b08001000a0455480c00d6428003158160040586040050300041000300300000b01c2118140c0300d244407181e0703440d41d44008002ca64800c42c0402404030100004002d00c1310350690029018030710a50030341e106a12001d031007100a0040015a801246101e00c20b81c5415000340c6c0016843d007068010307070703040942c0c40c400300e5036440700314a415000c1075800d040d110100034901d407607a2484900f21010484542440c49603140310005026640e00181e403000c988007030210400c140801800d2941013070225100000005445138050007050320140304915002c2862030240c01600e12a041c180d44082c104940840f049004d03081e81c0a1881e0180104080e2800400e410300040100740c07201c0302c160310303214500880342d66403801c010400549084213000510030b5a034009a5043d0084045603410040e907241040081c0b003556650150240c80d0404000c5c1914a80111702022070302600ca0081281e03564039024015030384001c90701d05030706801c8203460007500c0ca03200304c000b50347d00712109580d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 37651183 1250 37649933 37649939
    0x10060309020a0b0309010b010305010510050403030f0309050a0f03030c0c2d050d0302031605040305030706021810031b02150630100e0a030e0f01050915090405090601030c060e0604 79
    0x1080f40c0c3d105070b81c00d5101d0307510344219040340d50701806410b00420003926484d540c50040c0310020105d0085000080803c015001002d0845200303401c078521040e0880266000c1c15850328103510030131880202140800d0501140d02c00e030714050540f00c0002a003103c00c10940d0b241071074040141a821030039442700b8180e041511004204100003030221031440740c400503a01c0c208200d2125005080302420410010104030900001d04007205554086501040140c2c8940600307940c0c1d0b00b1401030400c01030300603000546d0303118410340c1a00002e601c00c00304408038210380d803004000c03a26010060080092003008801041c41d60401880d00a00c4450301d0004906d04010b444055407240040140c40c4001c0d403144402c01c00d420820300c600354101001000078080710203281d070090070030140c0e04a480e11070f403424444500b40d64090001c8440101d00244507141744121001084415041200040d0081746400c2c0024880c8000054184c1600d400401900342d403481c20f441102c400d120780d070910f038001c04140000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 37652433 1250 37651183 37651199
    0xb0310020a030506090c090306010e130b150f09091c03060905131401020901052a0f0a02030d0801060e120c06040902030115020d0203160507030209131101140409090f02120303070f02010510060309020a 88
    0x50081c8004442c10310415000740030080510a60f223f01882001039a0910903210700c00590f01c62a0311065039001c0b1581c455581c00d070003c00031580450302483c2454104141481008000d01c0c10b603114141c040d851002c5020568202d01403115414003041c0d0421024070032105465070f50354058200c0a80005c1001c140101d141409081100812158042c051040452900b03101039417044e052b030f01e0000c4003580760050041190407040380c014028a4101d558100c03941c000e0140342d075034540c06485030b40d80d55503402c0c1c1e840c029882441017100c0d6a4810103509812440400d180242c440198010f50410945403960044000440c44c120f40b14841c0440000040e281c003100300744225002501d0b1205180541484094060611449810000080c0c0d43c0030094030940151000d070b80c0c460800245013151882c10302d8000c940d4150183d4040020b00101d01c4200b00040210721600c215a2280c0111003044416400e0350700039140080b504428400c140a103900c650700c003c0805000425822003a5601c940d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 37653683 1250 37652433 37652453
    0xa0c0303320d180606080d081f0e0601200709140106050909250c0201030c09030c18060e0c070210020c0105090603040201020c1306080c061303060b0310020a030506090c090306010e13 80
    0x811b80c1e0f06e0700a6040001259003003c00c40c0c2d8010602c1c544218204003460074075629500a0054006000c01d20010880c56449560824045115201084008001c824410b43e4a2000f442800c03059420082c18018212600b8890fa040fa15291503030703410324621004008080b80000c044149412840b0040c08003805102e112400501702d5468104c183c44c0700c0d0000409490081d1010340c140000c2060400005006102c0c1c8022111488600c0c0d541c0101488464050000e07030340150b0341d1803220420f0040c1e503690740c1c0003804118400c45004000507510700c4180d864000c0010024040b40c018060100c45041540046502c1481417044c1e500280d410070000d1a1080c0080700d0b0079489965032002d00a01d0320030403c004040c038044816505241394040040604422800b001300350540360190100c2c01d40f0108210759410701c040400755111031741005c0c0140140000c035641881140360102150116402200f1501c0c81100034001d88071580c00c04001e02001c040c050072445048100010b50310100380201c1c3c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 37654933 1250 37653683 37653689
    0xc08030a020405151201030201050c010b090c040e011d04030c020103060803030a05090c1206040f0f020907052805070209040503090604090f05280c020a0c0303320d180606 75
    0xc00140c8503400e040a01c0000100c1010302840c49100308881104d45900c000240d04503507091904666505000084d9405805480c8419400a805030240000200c0c40b40c00790045e03e90828403d8410380e0b0b550b15032100800c00c84448c1d560059500c02080100f4803803a44515803d0040c100070031a03640c0c0b100041d14690084a4072840c0d1a914000c0c011a00818800c8030b8030342c1c10031039600303000610441c2c50039220f11025100a000c00311402500c020060004030761207281750000c00100380c0d031400c0c5d440075101c0c1d48500c1d5038030161040c03825020030341c0314080a01c171040209507803442e0610341c0da0360a0107224079001e40292503501c8144005019540c8800041001c1c010207880030403901c2c0081802c070306aa2028000c1c103001108081704980601c20020191941c10b0420000b01d40c51414100c20390424403450405000021075420100525800c900001c070034090038829403420007507002d651202840c99a414041d03610040010f00200d40c55500b082085004125450301288641d55030182154081d41c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 37656183 1250 37654933 37654951
    0xa1404060e040615270509040f0b0901110f0a11030f04080c061e030a060806070e0306061f05090f18011a0903030706020c0a0b071d0411090f010c0803 66
    0x203141040c07504141c0280300050401c000c00c0c030488802008041c00d000400c0c00d40c40c40c1c00f54024174111241c0d1000c070b500402401c001d031a507040d0781080c0c00c00000809041c0e5003914403103010760118104050521407610640049014603003010003030604038204d40d020904134810441e10303210b8450700c00000d000a200070000720700169901c03803604406038101803016080d280702d548103024001021108180d8041c001c0e4804c000c0b82ea0300d41c0c4810b448401084581c000f1110b52081c0070812803c6a0000e030000382800003203084540941e2103004001c1801540146140e9000854107921405402040546511000240758000c10b0340c40101144450400001c0083e03d01c024400400141c7c071340d00103004a007030512042c1d518001c42000441da59204d1107000811a590005007204200320920030301c0d0055500c07a4003080c407400e080380010008000f0548074080c0440382e10f880060792403e486442c1000000403111402d02161400708205038802034801414080e600700e03c7c100082410000b184640110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 37657433 1250 37656183 37656197
    0x1030b090a0f0803060d0221210306010e0307080a03032003090a030813050a0b040303110f0403201305060102060903070506060f0102031606151203051204020609060d02070b0f060a06050a140406 85
    0x451411868180c400e00c5581c0004c03180b09c801d42d181901c0000b100c4d031100003801d1000000e595500440d25108044e8040803190090400301c80426606802038510110700e461501841005911030240c0340c03100f66a2000b4030f6110b0740f0024002402000041e078807202744010503941d5001c5480310313820403550340c00481d00e130302486080008048e01441010004198640124240320004030490300a20407400003030446204080c04a041500a40f80104d22a202401b01c2c82032046403c030310b0019010070384442d409406040001202d0003400400e590080ba0044020007081c2c0310082031140000903000500d0450004110100d400c074a903170240c542061043c0d04c0041c840000049841c41400103400c120400d01c050361106000c40c1e4080c1c2503070301d052452007480e0802c0e1900d100095442c07050f407030650380010300440c1e000e21520380c90b806006614041d190400785940c0d00b40c0002d03100ba00440b0901c0e88060403160a0080c81e00c503201812810469040003401c00356141804079250700558080c500041c15 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 37658683 1250 37657433 37657489
    0x501021b0a050105070c0b04030c11120d020d1d090604020409150915060503040b1807090603170c0a1709090f06030d0c050d0e060910050301030b090a0f0803060d02 72
    0x2d20540e64417124030b01e07010085408958a003561a08042c1c809400c005204111000348445158505c649403401003402c50411001a410782d100e541030045c04016001c3c0d100704110260107501c0c8031300a000c10500c041c0388140e005042114100300504402c1d00207a00744404900010340303201d8036020052a100d4142590700e4600c019080e120004540340d00906030740d6082146940150950350084c1e807124000c0d43c40c0d038603000c45441c400c03010790fa000743e02d01c11581d002461110340e0703000005590080d28880d929402c40c9080e60120f1081d00c0d035401c007541c8050f200c200411491040d0b070344410116003855140c0349a104c002480c6a005a545100d0a110031042c4850361034200201d203120402c600704801000c00507201d054442030480182c206204040714040070a503503541c11503540203c01003084155245003c0000e000c1c2c5c0007408104e4100100c080812603000c00041c00d100c04583c025000d071406d0032540d551920540028004e2600507156290302d1005036955a4014407940c0c001904000000c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 37659933 1250 37658683 37658693
    0x70b07170c09010206040b040f0b01032303090f010e01200615010804030905091b070b10050d05030406050d02040b0a020c040c0c020319140609030301030c0603050603030a03090501021b0a 82
    0x382841020741420850003402d43d80206141d0751050b01320341c1c466080c0c0d59a0900c0790030404486e074014015006600040704110641c80c015240d41380d07480110080d200d2090a041c1e5074416884c00320f0b0300c001240f5120089601c04c014811f0550018904101040023194500080d02c40d00e5014076401d0300a03008001180400c03040c00c1c51811400d01c0c10be941ca0515880c00740030190795000b080e002c2d1200d0800203407120000350003070034004040d1407016902c0030700342001e240120341694003005040341c0000000b041d00c0d05c03070110690782e600714010350300d0140360400039100c55201c200c602c844150203110004406d1026009444203144903006013056290351400c0104441c10b0201c030340140140c0074500301c05a20001880741700038190b68070005142e8a1428942070624248122150b81d1040c0000c00003200e40100246040740e105240f1182c81c5500c501c001d4040d580300f215001c0d007503401404103064407442500300e181400e00940c001460102d9902914195807111202e100e01a4811807900c82041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 37661183 1250 37659933 37659977
    0xa0e0102013204020114070804050f0303070b0f0907030f050d0909020301081509030d0504140c01050f0f031302040609060611010902060405061c05130b090105250302070b07 76
    0x900c0c10010404455000080d0003940c10700b1250b40ea5203a1000000581164050f500d0030300d124258a031500d454010030300e403d040a9106c0d00030b1600408a480b00a019818000250748446501002d140c2c0141d689021080a004008011042e90310502d00004003141304d0301d40c1b01c0319041c0150050080c00c4025078001d01120519400507103020700c10001044216004910b00842001000340c0c3d60041d141c015045155005212003c40c00600e0030003031004000f524851219480e05003019104861501c40040d150360041e000c2c60080c01c10108252800052010001d507444149070903200a54007603900410122415078100e01651551803805101d038541027000d8900c1084030074028040d110ba10b40c003048090089114a5028100204000742c0d03500d03c812110300e010b001c0890070451841c00c1240c0b588010b201420985050480101041202c0810b01540c0d2180551440004042020b215103c0303a4440d200d008070304259081c84900005012074640038003d000654036001d40481511b1003141c94 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 37662433 1250 37661183 37661201
    0x150c0d05090703050d030c0e0603180d030504030e01080603030705010504030801080c040605030703060b0604090504030306031a0906010e06010203070804080f0c10020a030309020a030204021911072403060503030a0e010201 97
    0x107034800d480400000c2d5001619076030030700382451b0204110342a010143c8031003981c0e401e1039500c40404010801400e41d87c005002c581c903410811660300b02d0310300d07006508890080d40d000d000921840b201e0402540101041900b1500c082c045030b24141e607076102c2c0d0782150000c0c0c0d011030015100d81c00402000d4810880451042d0007100c00700800b43c40c207400640c0c0c640321444018002a1118640791895031920180c50080401da40288120b103003034070b0010010555400100c5040c504134848038021300d21000b041d8880d040b0400140304031f074240202d80480e0f07800144113904602c802c01494000030807140c0a0001000500e004000c4d00041251300c0c0d080c0030b1103901301070041d0b00e103034070f1000300b0742d030010309402e40c0380e09030800040c0072116001290030581e01d0b400182d0000c0c00000c007840c4c9104200148484015156510107100184551071625119548900c003544104880c0715008944102c240d500c45000b9402d001489070350700e2021a00f180c014403284004501651244071840d602800b48000ca = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 37663683 1250 37662433 37662451
    0x705060405070501181404060f0b07021801120204050901020c01060905011a0304050706050702032107060605040b220f0c080115050306130f090b010f0305120708030403050705150c0d05 81
    0x100c08000d00c007405c2020b0144185410017404064000d0346032500d41c071020141010500d6160b40b19214500e42086a002000490103295a0202c034004610184401811788014141665003070007650200300141030080e1008000395400c20042c41e00810910564008018111000c00c02c1d40c540004030701c281c43d4642e10700d0f0305080200300b00000076202280030f90544049003230240d01d0368418004a0700e8800100165640f000b69034100d0810b60100d040a0b05129109084c24000d0310b8030360b0140700a5410001c843c0ba0401401e0031004d10015100095155050100d2000545501d0140688059408010107800400c0746280180240e240301c111007070f90055142400c42c650300303102c1c001c03c2c01000381580282c0c00311765481c4155a1461544c00c40c81c152034000f9a40381c0d003561100ca0300814041700c0d01c41150540b0800041c546030602c3c0d0419a88140e80049016040d40e0391918196825888030500f26194080c1c8401d04400c4103901b4010707800748010300541c0782c03603003404141441140c9000d012054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 37664933 1250 37663683 37663697
    0x6150412050105090625090504020a0302031807060206010b070305090405160206150108010e0402031f02030a060e010f030206090a09060b09210a020103021c020313020102010615080a110409020705060405070501 92
    0x86c0203c102d03186894540c1c5160228040000c4100f8200d0f110303c244d8002560050001840c4030f043d580c1034000d94080c000f00802840c4405a1040d001d41d221060306c135400241e000240104810040c05018164440c0a4200140f0b00404000002d0458200f00c070140701414000480c14071156040040c964000804041140000c029800284c2001c50500c1045070f4850108001411910180120b021318651101e103031081c003403506483c030080d400496500c58500d25000d400250f05940c14a00c80c101c0b00036130b100203816030440d001d0120540c0300d0381049820520b140e1002400444a11813a0014000c044240745c8902c8440200000a4001c80c0c4251512003514805141c440010800301070040d82400d00690b00d0004902500f641942044400812440881080108400b02100e616010701c00d900030082c20303441d804494090301c04028041d000849507400a05482c04691201c8641041c8113010b03400c0682e01e0007000c069034080e94081f141d80e0031020070b01c81003060400023140035002c00d007020380c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 37666183 1250 37664933 37664941
    0x60503040f0b0a02071a06090604062403021c05040b060906010e0f040b0409030206090706020708070b0c0a0209010605090a050909031c060503060f0108060105040c0e010503061504120501050906 85
    0xc00341c0c1510310003400904410010458420751a8111080142c0c0200c400340d02140b405c820300740041c0300301c0b24140600d00e2000011050b181510130b4a00b0f5030443c440b121030425940440d88244440340b003240f424541e08115840e20a0780e42404850803040c0365001080e0392404d40351980e0306407000b4142d2400303a0300384014000560f800031075401c01c15905035008001a843c03240003034042d001c510111900603280000200034580c0c0030600303e119540f0f5001b01d070041c6a4070182240e5030002e0741b183c42c55a8100c240140400c0008500810000400e40308403540c0c044550002504804280e1248010a400043e080101c3c00c00d10300c0b07100200411511341e9180d160021640c0d88a100300501c01d00400c04c4094102c0500c0e40750f138090009414060200c1d1241d2810a1284401c14001c0c01201d031284104400001d00346414001c1480482d000e03075403c4d41d240103000c019196504044d005542c407410a080c81021035040304090401404070f07a009074041e03203490030300f142160009015401c003604140204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 37667433 1250 37666183 37666193
    0x3030804020402031e01060309020102060f01060903140709050c0403021905030712140604050c01080f090a23120d06080304050904020d14010509030301140111061f0504060b1306050304 81
    0x11030303205805440c0903999940f50042912050440d080c02e401071010300001003060399041c1c6c0290355a500c01e800312941c80c2c40d81405840403440034450701340003850b105d2092000071000c002400e070055400341140e00b580c0c0c40ba4410f0040c0d800440c0e040201c410b0100d020425490724045207500041c00c01c051051043c20718020070784800060140c0c1ca0300d0001051000100420f541c450121603c240c025501075003032a292442d01d90410550b0745000941d5400030a0145a01c0c0f6a000e0040803900020900fa1009a0300c440c00200e1100031208000d4a0203005400ca1005020350b4400c40d161181180da9009608201c0d8101ca08540100090f64401d100602a1b41c132043c0700150041d030100ca42c00c885100c18038016860110100d80e404c415400d200c00c6c400c0d51080000a10b044e500060107503031507a900803004503054944154a000154010400b10b044440007210034003210344900740d0f00360625190030100d02580d0b825480750002c1440003441d85459049010b0850280449250a034035504050300d927 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 37668683 1250 37667433 37667447
    0x30c0c060e0a0e0403080601030509071a0301030311070602031614010911010201111804020d0b0a0b070b010902071a040606080307080301030501140405030a03020c030d05090607021b03070e0907120b09160303 91
    0x41141899032b1080411046107080040600410030440b000500c00d6055010b1001c540082c80101c010035401602078015000c045071184c19107600394011810649044040085200924800d8403e5000b92162211000c401c1c02203400042c01142c0c00090310000c44002402c640d42c18407085004101800a030700d03c940c444075049400c4408680258823074031507a84500003010240c21007135201201140005030403e1410107461500c2c09281d15450903039803032a2810591042010090101e209200042008802103140642190241000040c81e07500d4421a03883c65100507410741300c02c04040b0040040160900403500d07130000b01d98400c8503a0403d5034903180e40740100c0130f9a10626801040c908a03808041040c1d4864903c812800e022038180070754040d03183c80c0152614801406400d0102102d508404c9104118042c0903004001c1213150402d81400040080d11002e01400b40240028a10420a140c06c1e0424014044c4240c28107006070300610b80304040050503c481030188003040400e0700141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 37669933 1250 37668683 37668691
    0x90609030e0f03073b01080a1205030105060d02031302040f0207060e072103020f010615020c030105010f150e120d0207060804080304060b120703050d020d090b0d09030c0c060e0a0e040308 82
    0x10b508406007400c0036442d0700745246041d0740300c901c00c405c1c00040c4140000039941340b05802500211079103030b4620300c2201c0070b01c0240506c68012404100c603c4038154030341e004552002d9420558007007a0180c1e40081c0a842c1c1e5a4044002260003203140c406004040c8135100c003140030724008121039881e201d040c00302103195880300403030201d041c0c202d682414000e2040e480310402110007003045684074807240001c0b240e1414000018441d02d6081051130a05214042c162080762447d01c800d03516200003120a203244170407480030050050b481c00220346840042c0600040c600000e069806095035000386840c22580c4080100030300344091201055100c0100d981003034000d440418a01c10b2400400c460705501101244a840380300d100000b40300c2e0100f212000480c050703090360400c4d6a06941120940349a0040c03e1900200300001074103580140d001141c4103200e404c2500c042032907500e5030b2540ea40d9a501601c04071352076086540b1149048048100a4129440d041425048c5514001c1040034020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 37671183 1250 37669933 37669979
    0x30604120309080d090503070b010602030903100e1609020910080f0403030c0c02060a080103051e1207050106240219050319020c210705010c080304080904090609030e0f0307 76
    0x3030000c50038451924222a49035131400414401038006240950303496100c4002510000021000480c449101004070758183c03400400600c443d514007102c0100030219114006980e101d03d0700c01c8400d0080c03d02481000f016081d500580b540b661000303103d596003e01039490f08008203841002005019000c800e60040d030540340011300074801c4c0340305176002c0140a0300a9032003040860703050005988170350064142ca128006655902d0640d03041030042400c0261104120740280b82c0c500304d5010b44402502e092801403001207100c50f40d4000d80e00c41000100000390004203085070240c031142d010080c2c4010801c400100000450694650f40e860703000b60110f0f81c510b82901900c081040340700700181c415042004065040404524101d201161000440ea0a044c0600361001807258000d480c4031030025004111140386076111b503202c40b642d03400350501603031145d900d0101d000404d607a4804c2280c09031094407109039038040c0c1001c01c8a01241c0f901598400d5018102c18480a101602e200004060388 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 37672433 1250 37671183 37671191
    0x80105010909181a070e03010e071e120f0303060605030c0403020904060b0301020c03040603050c0c0703170708040909030305100b0901050702031c02150703020703050a0e061b0c0f0306041203 84
    0xc000e415207003c038000701804c082102c0300743c12800940407a00318040c1005448180700e0101c0300040c1802c1e43c0c4550200342145c1c1202204122003040161048080c0e00309410213541c0300c2d142d1501100c0301e6040c14040e156195000088020190548903a00180c2114246141181307050b1400188505c02c0d40002405041d80b0380103c1d08029154000d002c020200a001b0b54640c0000d4044554903000703440344000082c1000c0100b0645800c000c1103a1a8107482805045154196215030020800c6403030b601846140c01c1040802294441d0f000d0b001400030a00f003c690016982001000e42d0320280460110036800101000003240420880385200c030282055900e0398120700000f82082090440c50024108000101080a40c04200381e0300c0e0000e1080c82000640303520301d0881c00ca01401200801040c03003000302c45820350281000141c0175000800c22454096a5170380c0c414400c1c0808044076581c0e0064045a2081c40c1c6849199000c01090b40200300500e0240c4400b81040003540c914824140e032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 37673683 1250 37672433 37672451
    0x5090118020c0d18050d050c0103050907030b01031b05040507020c010e03011404060f0513050304060309080408030a08090705010201090f0b0c0403140c01080c1204020f01020106080706030912080105010909 90
    0xd15019200074040742015150100100c0780007070024180b40344080b807884001580455a4548035000300f001c9a0400010108a000c1c0c0005500a00d4003401c0203a86104206000000498840005001c0c40c07050880421a03026010f0110103031f000364000da40314504000801c820651300060f2040002400d01e0460317586156500801d0041225103030001101892900700001e00889070000c40d182e5001c1701d0100000d40d9043d080341b000d5030b4040b0f801090b60300100401c0080034840c1e000918554041e103c40c43c586035458403100d103140c3c094550309000c10503103010400c10403414000b0500070700e000e0009105107005030342c903011100592840200713480308080210b81e00c400d44806841c060340d0300400ca098011a4851b005a0f9903200d0040da600240c041c0300010003050503001694041921200d04080c640c6540d801c02c282e0072a000c64650440d0341e50350340040c1e03140c02000628020074003618001000c0c1305908004455240b9000403a0500024100408c030f13690784104020126a00c2940001d00d440c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 37674933 1250 37673683 37673729
    0xf0c12050c01090503180405010303080a020706020405060c01050601093501090c08030711220c03240e0105060304080906070312022a01050405030f0c0a020306010e0906070801050901 80
    0x100d4040041035031070040f01c4020004004018414013400396040c500f600300240801040d224240001000a840320020680c0300300c0c1034015000f001e04c500fa0160616481d100458099004941c24100c3d03a9160340a00c0210750300069880d018011007519494031040005481c529488106c40804140c0d0010f58410601c180030740c000c500490740050100802d0381e071040c01c0740ea00d03001600f05075118400c1c12000310a5207040300485c0c0328082c80d1001c4160640c034910301d4000800320a0b4840d814191208180501c81c0320303007418006407004440714a40d00c6414000ac0785000c040580041d402110f0820501021031100303001e680d5211800c0312540d6480b140c0d03103400c80d104504005030110150001c540080e04145262089043d0384244107841448030500d9440c0307007030314070a950140c940d807c108840c4807182c030703058000c1c0146c014001c211030340a000d96010a02e40340303090b8806e404544150003031005440c0c091090300d40041321480c14143c03070750600e00001c0d000709040c4104107940c01c40d806401d102d00c1c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 37676183 1250 37674933 37674937
    0x2a0a0f0905030a051f0203060d0f081c0c170c03040b04020105040801230703090c06080c09090f040203010506100e1c120804020f0406120f110a080d0f0f0c1205 70
    0x300140c2501d050340c03e90700d801d03170750b900d40b205441050b0802d80c1e9180b400386000d4402e03a071240000a0144200e11555121b030030100d00e4215055031401c0c010060440d03408100041400c00380004100025003103481e41c0010400741c0c0c54800f4171b01050740c8109109695521000782e0f908690000588182d0307845920040c0c0d018030642e40b040703006d5400c20031010f4170b0400c40b9501000c41807001000160599800c0c0044085914000008015411104d403c1c03110a200d05041c9601c03044d00040b191900c81d0100c0042c030910070071200307901c2d443d004104110442c1000c0c05095000729003520400d0511844000c09800303005494002c5000700400e0ba50b403003240e01200000045550005021980c8188140c00108611300c00c59069000d1581c1002c20551800c0a00c684d5045420b200e4030220209055070310b104654490000984500b150702a4240d01540c1d101c100d44001c180b010300500b0072500c6418042e107070225081c1e0705000c0c00700300d03000e00308001d8124100d09551540003641f1207403045044010349540c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 37677433 1250 37676183 37676189
    0x4060509040503091011060a0b0a12050102031005040902130903020a0b0114010e01080702100b130e0d03050609100512010e1603060509030405010c140304030510052a0a0f09 76
    0x140d6800180018008040000c0c092642e090745c4170042c00940c034400ba621140c2501d00320100c0c3c0c5c0b11a001440000345944080e0f00740030014646008207940c6c40c1100e4408074500030035201a5400402e0081c0d0034100300b5060300038901a07605001000c00c1c0e03000142075144010400039480d450b17004d00d40030140300b03101600f0f88542c0042a0303002561030f141c1c1139050501010390507011840448040340258010f035006841020300740c1c0180800c04880704800060180130000b80c2d000a60180c4028010506003e54081b00f5000341c001c00d030258040d00c0041c00e642014110740e0003240345500788142c1c060740d4445141541c90555507aa52034651910b283e0041c105501c4045440c0102c2025040c81e0080543e00b6040f01d029070300611440d101d0b0f01d01c0325103e1142d48100e5011464218020f0005000c2a145141c01d80c11001540c0c10265251107882c14040345100f0070643d950745104000041a035031003005020750801822054401c10106040320307d2150b0014403042c010300b600c0a5164520840806000d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 37678683 1250 37677433 37677439
    0x101a0a050f0409020703020f0f032208060f060108070e010c060b13060305010c2a12050714010b100f0c03080a0f060314061806010909032d080108030403020a0b09040605 74
    0x1540f41d442c02500001e4000b075000b14010702074814451180e000004001d1a00c41703441010b503290040f0301c42550000c80c200c902c0302034500014203001402100501c0310502c581c400c5460100c462402500041031404028692400d0241c41c408400c00b59900c84180c402031688000005041040c520001f41c003503104660400042d030404802108002064104c900c424010742c64048007000350512000000d41164070620074540250003100100e80d07004100c2c0490301039424028034020f1030f038640c0f250921000e90002000c0e0b440303c0003107000d814030000003a1840b41e02e02d4548107140444400420319603c1107400345c100a204008901c1d00011540701005084080d503042090f641d5034540a01d07085514a105505401103200241d1107064400e40d9950f03050824000c2d1046070300700421000100b840031410740811407100301c04540d01c071a04552050341840f02048034140f0504400051948405811064017500140802c00041e19100503007401d4444464219803204003110104008010507840154 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 37679933 1250 37678683 37678687
    0x30507050612010e1801090c06031112162001060609050103020c0607030f0213030b1b070314030a1b08090f01060f0302010c1103030f04030c0b07020f010e030c090a0c08101a0a050f 79
    0x8c200445c441c2c02c088130b030b090b00c0500420895852b50740a5000321015805201848000100c1d070740c8051203150410744a0b1300784002007040c070031700502503691803800c002e5613070307541c6c1c0405c1c000740e90000350007401040246420b62a1480c001c0070f5603281c1001801030810715455402c101c5a50820740c05403228904456981c000b007698a041c803100800064500c03128101c1a4100c0c04000c800c200100c600d041c2c0c041d1115501c100c03129805035071707603030005208410896450706520301c11480300700b000d08014415a03441c0500d082440403282003a2208000803d203038901070003000240b820155440c112602401d0144445041c0d050980310390f012401c10740d038107000001d0252401c0640101601c1600d001e18480780040d505e0b020740c01c0007031007a10006507220003003060b1150150f12441c4400c01200703001d41600d1030303120f452003c6a261013045d2182e019043d1030b070001c416071590120b01d1540c40901c1401c0d00850501d014112205000c0d0042c000c103d0900004880d210640140111404c1d283d10300000382e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 37681183 1250 37679933 37679951
    0x5060307051509010915090521030708070204050708010305120f040308130f0602010207030206010b03090f0d1d040603080a031113150801120b0c090a0e0f01030507050612010e1801 79
    0x250342eaa11800b90540450001900410390904446412040001c01d4441000d09400d007401c000001043d950404180a0300201c003105000081c07010704082c1c0d1181001035241d039064410041500c00003000c210400c0401401080410b00c0003848e41c01d85c4421005a0707590b90a014103059261169800103011640001000c0710464900c94000089403080303a04580c07240d480d040300328281d1048c0c400c09030042c1c0c080c070010700030440c00000841d00b202c01c03c0101d40088880d940b11038100504004c17500c010541c40c0f08050504c0e2001e2803006440e00c0121002c01050341107a0b030307180c0705005075a04241013540c1c61500141500d8510304648103402c00c5c0c0c0c05107a00981c2d54600302042c09030140d07080e00052000000240700305188550000255024800030400d035105070000095400c5058015840540804006600c4031315600042c0944c90f00c5c06220785035070650900c07503c0d040b200c2c5d1215001c0e076410007031518500540c3d14810b054500400c2052416107911007800c1509001c5400c45c0d2480d46005041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 37682433 1250 37681183 37681219
    0x7030f051003020901054c09030c08070f12030908070e061306060e0118050409060509160e0f0603161d010503060114040e10140a060e060604090506030705 68
    0x45088900c00c40f2850f003280c0c2c0390f0b030500900c1c50076044120715003454001c000090506014403d2000710444d0340e6511400415500070041c4542c807c0000f01059a4440500601c03508044c060094400f440003881880d00d4401601d125602521880c180f0400f504018404c15116285060041680104a0b9211904d503401a03000c0e003425074089110350800103840002c031080b4041c10003115060b48a486982081100558001c100c818046080008141c00402c030b075034a5101d1032051900451001600749050714219180422800104900038944101080010380c90f224030355103c111a0301840144d22031002180c0352105400901014680c1c074034012071041103080c00303c0f010100303c0030030190b0351f40c3c3d0b401410b8580c1d00a0103181c28105c1e00307003070600c00b0b0300b410740040f160607000404039044a4034440a0b40304403048001c1c0f918080d028001440607074140d81c0600380c0900961211444507040090025051348218420140e80e40e4941c400246165001d104080c01840040c1a4090801003200b107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 37683683 1250 37682433 37682461
    0x20f041d060a0c02010b0a0e130b070203070309050a0b1b01021e07050c0906090a020c07050603011706070e090109050603030c0a12031802031e0708030f0a1d030706030507030f05 78
    0x401c2a1040c0f4100168110034414016507100c00801380c0105130160400e160942035010040101e01c1200c5a09201c80004016940451040ea00c65025503203401c2e85160040943d0000d60119100d00040803080c0305420aa0341262030303050a4488810254031059802c87c064010b100384514051400e0a2070f0313001d40054001402c2c074500c80c00907501da4541c18010000600c80950f9500d8110081c00e001910320380090b0700404024180c007084482d265907940c0010b900d40c1c42600150321810b02c0d1849620390220420003141c0100d094100441480f0b800c40204204020510442640325283c501180b030648041c001c80d49440c1d091410744800718010304010600c003140700050000079103490542d1008200c0703140c0c0c451440b540200030f0620000a40001007400f411801c00c0c500a004412001030501020001401c0143c0e2a8880544de540100d5000e0900042c1c450f195105080814444c04076690100700c175410388241e8103002600d500c0e00c00003100200303226078200300c11920301014404540c400c00c2c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 37684933 1250 37683683 37683691
    0x510020702130c020c0906100c060506060403020a1d07020d020d0f140d05151c0b060a08030a030501061404050105220f0803030402040f021c090215030103080a0f09080a020f041d06 79
    0xa950072494460b80180314031280d03035848c0240041d2a080c0c031403000544a8204a410090003408941096180e80000d25140000d038442c402074120700c3c03a402d0140c0640c05886074800d105001030402002144030194903800300f252100308100b1302c00b01c081c1d10316000d0058100301054940d241030700d0702c080f1b032010002000243da000940032480701000c4018981f09800303400c54818510009142003d90340e4076a81030b8030180000b540300009213000704240c3d100704042e00701c00e5401e0f0785c00708080d4905039014000009806110804110411060050780d0f001380407119240b007521000f192280106182c1d1b0f01501c81d60700108076284076004001041c42000001d50301503030003100c0c00c129140b06100c01324224400c00300707080460640440c41502088260f40001c0c1842c2c0003508003400c01d1200400400298000d0b003040b100040c0c00f0942e215010f034440c42081803008642000c1c01820b040c104890354402c1d0102000b881464069040c0209850303503040f400d40c0e8540e4046180140800503402922260704032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 37686183 1250 37684933 37684939
    0xa020702010e0616110d080c061905040c0501050a09090c02070305010b04020a0804020904030c02031f0b1203041701180b07020d030209060901030f181202190510020702130c020c 78
    0x2003995541d442c1030b00c00c440c1510000d24162000352090745e20b400182c04031003000c59000140c1542c0201180c9620000d00030801c5031005400140341002490218200c0d8440801e222031600e020003001550281e5a001aa40c2c00d091154440d00b039200100c81ca8059a0807907a846414004508006500080d0f0300c401e480c8542c0090100748168402c2c88103c0c09280c00c090005904035001c038001d42004c401e40f6800500070710740a00582865008245411a0000c500300320051002440ca100c007014424440701c848111044100d841450030020b0b07403405980101518800c480c418001403e800758041100c01280c0844600c510b0380b5402e080400314800c55020700503000362090b81401a100340b00302ca002c940000e08050410351600b004500820718103007202015a030761107490611228103c03000303207014881c1a6025242c0f0048000a050450020000908154a40c12100003980109403030800c0700445100507190340c0c5500005903405079506442007098949158449481d40c0462154145101070b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 37687433 1250 37686183 37686197
    0x60f0409060905060601170c0d0c0909110318031606050604060513090c0509010305030a0309060f0e010f0b06091f020c0907020f01180b19061806050306061f050a05120a02070201 78
    0x143c003007444c456401c0b40c0902e00050204270a51800a550784640300a000915003441c441c4e440e04d8424040310421501181c07103660110402141c01c49050080502c228032101942c2490b400e41e03940300d4407452000740207141580b40c0300090200d1719290b000030006d01009005e250001c925106440c01895801415240a0003020010915080c034404e140e049950041c0214500b29200070110f0080040c41012111240c80304000c900340c48a5010b09943c901840000166028050860350111030f64002614042c00c002d0048814542d03070a041d10f00c1020070b4002c110499058100b04908009414100c15130040004080c00754040d0b000403100054480200200030300e9512260131000b21031900c100030210041440040d010780840100e08017400d00c1c00e500442c81c80c0d190030803401d011100d005d08400c410380d504800c1200749400c114080d004801540c041c4401d5031056444e02e4126a60030200c0306000c0001003900e4800d20030011a500c4003c0c8082c512500d080124401c4040c1d4892541030740002c0304 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 37688683 1250 37687433 37687457
    0x503090715080406020c03040f060302090a05330409020c07170304030206071203110a0203070302070b1602060f070602040f0302130c0503130615030b07180e060f0409060905060601 79
    0x101007005086606494400c920341c0c682d078403038001e5404814880381d1030205102c00140c2d08160441c00d40a48450b490150321629406c1c14072146075420f078800f500c80c00760740d80f00201941c50495600700107109000821940120960700a82c0d601c00d035403014412a20000b40700c0c6a2450214a04041d64038482d00b2800c203684800b0400c0ea28025800040e6014504024540004001e00c4510510440c80c6c01c0100341c0e0889036207000095080b580704400540c00008115040503418030240d00a08201c02c0d18509004810544039241440d0b454001c0c0030b0100021007400d400820b90507560100e62007041550b50f13940700c3c940f801040c00706100480c0245100e48208000205c540541c0b4803108481e55101d046582c4c0d0782100880400320741040c2c070320070b40c1d42c808040c004250904c0e0038050341c010080041c0d5810310070002011000040960360550040c4401030010412031130005800c400125100d806030382a21000400034180414010100c81c6403082840402a02281152060b4000d8a40a40d0580 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 37689933 1250 37688683 37688699
    0x3070c0b0f0108120a030b030d080a1103040c0603020f0d0501030f0b010509040201080a0c09080a14070501020f061611060403020d030c0f021e01090c06020a02030c04020a0818030d0c05030907 84
    0x107800e014440c801d030055081200380d15070b55005413928505920700802c0451001c07020909003040c080320440041c0d01c40e401c01c01d00007c01d01035201e01040f10201c4502d14600fa403203814019aa5010310010182c00240002c0c03420071400030b541c41301c006204100155652840c000e40e00d200404000c6a055181b4000050b01e4500509228411038041e1192560359861059031001441c0700003018081c40580746000c660440100440b940300303440780660f40841046040f15070300e000340d25401f003030455001241c140780d81500803ca60780c000c0e1410107070042d65840352409a584882c00c140030340300b607c100c50402080c10341c0001c00784092007417610304102c800070f5000e0440d50480c580303034501d02590180141c4585003048904420309000d10900020743c101c515a11640151245d81c400c2005901040d4014103518042c080d01c0844030382164110b1404658840143c1a000001c100b01724992080c29140d581d00400e10880d8105d00c03500c60204503160100201400d00c2c0c0041c0c802003a284645074000c50400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 37691183 1250 37689933 37689961
    0x9060103050402060711040e0102070510050c0c070303110c040e010507080f010f050108090a0209160801080105040c0909050703050303071d040506011b03090f0e09010f1104060c030507050303070c0b 87
    0x81d00038081c40d140c20b4254846c06000342c003480c1d50307136006a52501740b050f0740602803005d0080c092140b03014010344d110318840c00e425100060828581c8910801c036160b80000d00044100490f985400d1229440c9030644240d800c103890b003000c0310780050a2001800c2c00b500c0643c080391180100b81c8a14481d5100d1030105024404240542003145540402c140210342c0030f0301d03205a008245000b280c4900b201c6502050380410180d41680381c070500a403440c0d071a65080362615001d4512400204041d140c1601c461400554900c1352002c800d5446010030305201081c0460000380d0740280849680b41820200113107c42804404450002600c02d04592145454010540030382e44c16940d03990440041c00300a480685486c908405103e00350900044c1c40d4000014100141000c0c5109142449c00d00c8245081d02e10380900311107510326000c040c411038a5150141ca0603144280b0304000c0c03142c001c0c80c00350340301d2103034000244c41403202004001380ba59201104c074000600c640d82444064079154103441d051303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 37692433 1250 37691183 37691191
    0x8070b09010905030f090a0306020c07030209010e0601080a1a090403050d06050f0604060305130f050705040c030b010c1203090b0a0902030d02070617040807120e0109060c02150703050c0712020906010305 89
    0x213030001c1041c090204a00c001401c05944002c060000640c0d8030f5440b00c04903805000d07140c00d5504101c004005524024002600420104000403070902d0720100003441c0090081000c8111703503031a8803008a40201206070420490090840c5c045407c15060181503500701d04081216141004004983c81c1441c9401d4032442e080680901d0070542045002d402800c4014014514200c101623400b000c02d00340041017440c40c0c001d90251100908010078807040d074410324240030900d820a280104142d0780b000300751000c117800480345180c0104c15101100540700400020b448001042c041c840307015000c0d403212846078405c800300e801400e898002682c8540c2540b2500d408942c00603400f902d0168903421a80c0d2203441f4044032440c00e00c9a41d50406e80ba400070400d01e0004140c00d040070040d503081608000509054103003025042002d60008103001002002c104583c0404603c0d4801c0600600a0708e1b40e0341c0301c90081d034000c29200d940e0304482c5400003800741d105500d014003158095000b8030130b25000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 37693683 1250 37692433 37692443
    0xc01080c0c01021e03010305060708041101030902150403030201050603160f06081506070303050f0f13030509041d0a0506070302030708040f0f05070f0801050a02120403121808070b090109 82
    0x1940d45460440308280c00c5294040c0055408200c404c45040440c000210010300d040d050716120350643c1040c074030b003a070020803040c03d10000e00300f800f000c201c40180744600e261003481d003c83d401c0c1d1a480481d00c403400d85400004101d0012030f01108041d0107401a0f40b1480007542140c4007060750070000306d400d450342e2261a440c0c1c44014010301896224484080d80548262001d524a0340300134080b82c10366000079000c0c0c001941d110140614001c3c0f4100142d0400005108901181452050141c02208001005050020004100c0025102c903080f119012586621424440c0d414803040c945414034407800321142d025190000d02814061710a0300d00031800c5584409140d80c45680314600104000d40c01d5450401c3c810251001807410000c0c4005050380541200a8a151035001400e441c8080c1055503814018001c80b10068401101141c2c4181c1528044864030341c042d041d40000c1c0011134820041c41600e102c00c00034401d0791401030031524840d14061100d59110303202c2600f02d442498000304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 37694933 1250 37693683 37693697
    0xa150e0d080307080c0909010308030a0c021209011b0804030f03080c0301140f031c0201020c07090513110604030b040b0f0603060411130e01091a0705040b0f0f090310090b06030c01 79
    0x100b0f25124a51180c1e0181a40c583d142c0f402c0410400140780d4582684101d03581d800000400132180c105018405c1129441c0c0014008050f910003070030601d000b182805410450600c40041c070900b410a81d0380d021030340101c0113981e2540c603030401c140702e50520300b0154080b400000104072698519011241210741414500704400340c801c0400004421443d11a94107220f00b07031500c1c0c1100d003070362081c0c0410b0305107400059070342401040c854200480366120607a0136150108000e0100031408901300140d0f8800305c080000e18202d00018824059900064500460501040104221580307400c0c0070b4610f034000410250307030b8030040584d04d40045030001c0c4913180c03010b486092401c1c0750031417218543c4031510128261508680ac41c0c00c4071302ca40703400d80d03c0d80800b10f02c1540803180c0c405502d03040040c0b813800d240703004d092001c6003a03540725801030030f00341410000701100720030340150136a40d2141000b000d41e120300300320305070840c00b504003c9415242030503c207002c60058034001138001000324060311144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 37696183 1250 37694933 37694941
    0x3051e0c01050702040f0203180717030d0b0105040e0106032702030d030509030c0f0a06060f05010203031b0706060e1009022b0603020d0503070302060f04150203060a050a150e0d0803 80
    0x160b9641100344101d8029803500304404064182d4005035204502d00704080b00040510302101c5d01c0e01103103600c922182c1c1000d1807c030545090100456001044120011036111000c4004072142d101d01c2d4050070b4894180f5002044a6a2542000243e44807801a080b520b2551110320086810050310096245e800800b124616038060b41281d40d2041200c020380781001c01200d4854108103401200d02100d4101d00d015004004072842060081c0400d0340c03000c03a9640c10800007035130700d01c0b002e02040d00c151503024104540207004400c8555817a40320b5014070100741c0d52254001544811382d1050469092140041042460341c4251500b110400c0c8040541015011003041c40d808030311032071b101c596214800403001d6100d05501c40d400c98842c00c000c541d0340310b940c14000e050407009410003800741d1300101440041030700582448030110034144016a20349035000060b011281740d60040b500300c8428800040c0f400800041c50000703c05a4480814184001003005130b40e440307001d0001c1103010144042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 37697433 1250 37696183 37696187
    0xf041403070b07120905030607030f0f02030702060606070609061109210d030906020f0301030b060a1d1618090204051203090a09050403210b01090e0714030705041208030103051e0c01 80
    0x4035001c110136003801c202c1e10307480c3e50200b0304000c0c080f0b41c1800400e03100c900c00301c101d800e076219411090f032038a14114190b0529a0b00252600c03006090b041c480c5002085400c00d1056591050420b568414820000400c1040315034043da008602002d108152071000c0c8001081d07038014644410303900f40003a0990f4011090164010480701405840c3c850b0300740030051901102070011806940204141c1d251403402c03500f0020382c00304035008042d404071002005035440e40002d602c0ca8100601c8041c00240340d00425085804141103045200881080500003d020310150f0007070060714801e0301c510520441f0740c4800e641c0ca200304020150407100c1080100603405241d072000c3c0e0050300c00e02e058110350740034542031054840d00e51500b40082d9900d10a080056070803111020042c507000c40301d21040d240903500900b5500040c030101c0100b07080000016401481001210049d0080d495018400788003400c005900c0e4009000071190b6109000300d20f0031841d04403c03150081e00041008140b6040f0040c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 37698683 1250 37697433 37697453
    0x615080601020115230a0306050103020a121a0c0c25170a1509081206040f050103030516020103060b0d0f1503020618010e130b030d0503060a050f150f041403070b07 72
    0x21260303617040c500c064140c0c3c1c4d4550381c0c242c000f540500b001042c1c139415401048100416540581207d003d2a101c0340005041280c0c0c02c110110616143e000305c0d072340d4401c0110b02d031250301a4420540503400c0d17031aa800d40c1c0700d40012101803081c41040505501d45007100d028500f800c105c020720307a1010403481c001440034400803280c203c41840c0400c0000d43c0d65a1050142c110080d0310064410281c10004142454810f003d04840010700c103010355403658401810030310818202c42d03030034035081c44400203690094020308014a0f1024940d69540142200140100103091444c0c81c20350801203100c42181507905894241d0380c004007140c1c50000c012049031140e41040343c02c18107100c014035a0810036034941c00000b084a040701400300c0c07201c0700d207000c05081c010214014014046c2c01d00520006440301c84000055400a4880c042d210305150f0008001103081800310445c1c0b503000400c82c044803488805803085544070128038020000603400c00d6240c110301e0084000c1c040040c0182d01c0402d01001d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 37699933 1250 37698683 37698719
    0x1202012403170c0706020d02010f0204050d0209090703140c010908010b010e0105031906090b011106040c090905030c0a0305040509010609080d0e060c101e060806060f130615080601020115 82
    0x2501031500ca0309204460a049165102402607000030701491f00e1240c081c0514032092034625021464a4106030000740f0f10042c005001e40140c03c520300080340c0380d204000500140d81c000c11681c00e03a055142e1180d40c1d0341040c081640c0000c100c80d50000e4141014040c80c1c61850b816114801c0013a541c1004456540000b03051011004203070740390403190102c41c07044001400d54040c0104015014038005841900c51481d0001194411820030000c601d6901c584400e45042d00b20200300c00045040c071518601a080103040c0b07601540c0c40003070030076401000500c101c031026900918280c0c0d95007800e4500390401d103d8850542c1011003108843c0e4400c2d100c502080200400c0c5d14202170700007034000e2034200c0050b40302040c1d03075584802d4003900b07049065441c50f00700070082c24050b940c10000b001d51100e0004c0c041034000e0350741a101340115603400d070844d801c03a288420100045076940807048a03e40c401d166103804151101c01045465106008141a2044039100000c160b45043c6064100e800004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 37701183 1250 37699933 37699973
    0x30909161b0302070609060f02100e070f0e040c0b030403051206150a030c0e0a1d0a0605150703031a091b0903030d0e070902070c09020901030f091202012403 69
    0x1424151540c510740d022921400e020f0b500501c1d0190400f000501400410342144003401240d0405407009640002d082c0d0b0040d01c11000880c0341101214020300d010344580007405a0481e9450100314045c18045203031145004103605801181e940310400024481a03401500090041146042d01580c1c0602d164000d14041c0056500c15460001059a07821a40345200040d89580642c0c07000ca0380a6070002c1c00f0700c41210010042841d1101c20301102e0f00f1050010078109100b0009002c9040c00d501c00001050080c0c201a5980d22000f1919100c0c0c1c00303004205d0110345841c000c80107440c01c100203c021420081c200194544a11602850b2200c000d004101d100004015211050324144058040c03a001c2c084027054403240340300c1050618805412100000e4030512100010840300c0d10100112821240c0059030b41a4803801200609640c07005050424101840c00c42082910b6180c40ca243c0410fa001b00900700409158041c2c4040c551603620000d50141420b0010900f0003462061340c40b80e41e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 37702433 1250 37701183 37701197
    0x6050c011416180312020604030e09090c1306090507020307050d020d210b060a020304031709010f18030503070b06040c090b1b0c0a080106060206160906030e0a05100605040b0303090916 81
    0x1d41d55245c0d100e0780b908000e0010782000c4103000c105600451961020707001150340302c8071072502032070707260780c3d850300004040c894021800d11001c12450b0303034000b501a0080b00000d020514000c4006507407588403c204440501c42e20200c40c0640b403010841c441c20000550b10f0380030b010003064058416842e1094241101d594601401510796521001070030800069000b850711039195050000c00070301c8402c05562a000d040000c00200da82c40000c0c049074507090700305912000f6601481c00702e8032840350401003207803000081c50810f0218282225101c0e840441d1305102d15003581c0c4003110110854810075044480910503880d00b0701c050b40c840403a40e482001260300e030710500380002e201e041c2c0030307409202d85941d80c00d0700344042641442140ea0101c03106680041070342d40c0301c10041c910710b458400ca004042e5100c4242072032110500850900c06d810a0031512001c00c1700d54101d0080c1014410340384154a001c24902c07441c1004800d0300c070100c1d0001d000d10307a1a03440801c0541d610f074014108c0000c0200e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 37703683 1250 37702433 37702439
    0x60403030f02010b040f06080115180c09080f01021b0102070309060809010f05041406010501050a020a03140d0e010623010203030a0b0607020607030801090b010309050a022806050c01141618 83
    0x9948076805115008884c0800c89900d8048d8070f40c00c4808401c911b1131560010241032102241480e5041514015803c0c0015440c480c0340302252206042d4104407540d001d00880c1c0c520002054014018029020191079a1561540100780c00c03441030340001404180b490404100c0a4080c1c0a001d501911500001c41c18001a0080d0822900210360855408404502600726048100300340c502420080c24920b2078041c0c1550003a6480d94003040c020100403482c1c135005002075000b0251030076520620350030305c43c031200418484e010308254007840e00d5924210014181e020090b140b090105d0344d041c1c002d5890b40e100c1e0303002c80c0043c1034108407298000004100f11380058a48030010040c65000c0e569040c182d504160040d0f0950f40e03403242c524101420101c618003c86c00100c0da01c1151a41200c0c5416040000d4a03041e1038031803a003845039030400c000b201c001001a0003400038569203d244008200c0014003c42768048c0000540d072000003020990314080030a0b0003058560840d41145082105aa0f6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 37704933 1250 37703683 37703689
    0x10f02010e160f0506070209010905100306090503120702030306130b0607050a200d0b0c07050a020316050906060304050309130b03030706020406110604030f050a030e06041101021605060403030f02010b 88
    0x391550b584511100c90607010400b1051800c600c6002e040c1c03c45001e85007840940009a5003401030080036820707696880422010b45000000354000c0d540840c0901c0007503010f0a00540ba50800d0414151051408000540152000c401c8a228810041080901104040e13140b4020191001d840da0402c0c0304221f0740c80072a0f02088918141c40c401c284c1c40d4850400d00700010703c152507a40c040742c0a140c1c100e801e9000a85908c00103940900485511501d40000c2e00b882803a120000001075010b0040c50002c803222104c07041070406440e0f003500e070102e85407924410311081d44000c0343c0240c0035401c10700c200b2601e450101d000384040038180d0404292648000000b90031580309980840b0500d5000404002003504111002000b100d4100506001d1a007a14040c0248010300952010444001070105106000341c0c414140c420400c3c4c1112054a450314000e10800004d60000d4094030a41c000420070007080000074082d0358005d41414141840c44d50207407214002c4014600642d5201c2115071801d031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 37706183 1250 37704933 37704943
    0x201050315182802070507031514090f0f1207060b060706020c010b120309030d12090b010e01080115031e0206070b10050a15020304031b031406040605060906010c02010f02010e 77
    0x70411250303074400300840600030412410f51460080c40940140702560108101042a00c1120b400046640d8031100e60b20031080100300c0c0081d180c0c103400c1140d0078403e20f000d0004181810a0402040310400e00c8010fa810f41d0340e48600e8404940d42c0410000e80d0700242c3c50ba00180d406010140555041c40540e03591741c4103a8201503420740441e907480080111601c0c2c031a030142c00b0010124065840c000390000480e403181ca08202041c14001400700003500001e45511a114082c0c100ca0f050901e96121081c1c014034034030a105c2d2903195805c0900b40d006c10301d0844c00301400c0344e502c8a00c0020f40803000f41400e51400140101303a034080070500494001c1000c1d8032005102e503040044411210342001c1c01c002c466641508000c061030000031416062540000440e800e50740c1146084000361441406096280c0103900300030b08c441540c59040c481d00354002000c0c1d009511a8030b0501903503139405d09014508208a84050018880d48002c1000d5402410290301010b6a071001255200115842c140b5003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 37707433 1250 37706183 37706191
    0xd0503060406050603040210030c02030d11182d130c020a030f030e100f1107031206090c0f050c070e0c040815090303010303110a02031506030613020105031518 70
    0x4544008104085460988281800b4180840e2000d086085c250003141c908912036940c0c0060560312050080020b0080069803440c1d4480a0180481c0300350181c40078150300488800460b4060603900f190319813a01c26004405020f042048000c0f040f01d1140c010040d003940350000d42c001016560890342d00c0e81c00c3c001c6c45640c074441c0d0010888a54a0300e402001c030380c1c02c001c48508151418000d0950104007141082804681d94408100314a04030040b00c01010442c10500e190240040c00f03400f01500b0043c0c0f000c400b072154801704401982c03168104243c1c2ca0800c2c140740020070541c0003a000303e00a0000d080841c000c00201d580d90340d02c59680c00c556034001d41c1c2d04945d040011404000c000e4007001030710f14644038640030003694242082c2507a501c1c04103000080c1846842800383c00c1c0c002040000c11007403030f0001d0403070306010110850500100e40039141e0301d0080c0250b00c000b0344841c1e140d002c1e04a40560603519030303195944000796401d0030a00019516404a030250200c0c0c1c2501303200303661030b0103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 37708683 1250 37707433 37707437
    0xc1507080d0e06091501050114040b031006020f01061208031801060b04081015030f0302030c0303190605030109050a11060705010603110a0f06120515030a0606050906011d040c0c050d 80
    0x1e01d01802ca4401e160040007000ca50107680003010708181d141a03501c41c1030450f242070070101401000c40031032002034051074000c081140310100070031401c0290308080704100d40300c40d000d40310b240010703001c1d03c0c4c00c1c1c0752507010780488051403548810004214100669119442114400d4072041400c0d17460300b91407040d440070b540200041b9040c86400424070880c4445003e00ca410000c1d06205440f07626045c00e0751201a00150481041038149402442101c0c40010880240d82d5240380c034040c0d00340741e079002081a031b54151900a0106240c14140309040300c9070b411000030120104260340c0e204407218022005504000d043c04104000f5809009020242d132196030380d80d04c4003a202c82030014100c2e040d48030316000e81e100c2c44100155a08280c446070310040050300072843d5522440b580e030b540031580c2e00250b01071003510300360005e12125600c02019100e080751070f1603584d00c94400442d000700e4407003d2600303483d0906003010014581640840503180450802101240d6540c130f501d4140314040703240e44c1c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 37709933 1250 37708683 37708691
    0x6061b01050f06010306120b06010e06030106021507090b030609040309080f03030406051e310807030207080c030705060705070305030313060506100503040206030603070305061906080d020c1507080d 87
    0x403501501c000b66030f80400300386000c0100c0c921b019001c040d403542c0d10b031000d8480703107100c000716001741d01c10788100c0c82481e8042d20940d5070356525480207540d841e00d1900507082c2c010141c082404184503e160808452000200c1c1e0700f141c80c2d640400c0390401c805401181441210031000450354005d028071000d00f1945406107440b4982810600151346004100941480607a240ba0131032040e40907070142c2007115401d50310400d45055000b01c90030300d4682c0301d520303100b0441600c000400c00000010061a8400e40c02d545102d230f602c0310403075511f410a803946507041d0032844c1d003807003281440805840c3c0036000302e044030400c0342d0baa00d43e00d0460b803040e120303011070645001c104024031040d0300074103400043c142d903031100440386030744010640c1c000988024421400000418001e90741044113101468000040e1449801c02241030071500c607410360f60309022414030000040340d040c00315020007441381070b402903c6130f842c006007008601c02002c08000c10041041c0600c0d00820140c1c8058029403001e00350000d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 37711183 1250 37709933 37709941
    0x90906080106051f080112110a030f02130c08060d0206070c0602010b010f0f050f03040f0212010c030f0608100e030f0301060e040b0301091a0702010f0203040b01031a010807060806061b0105 83
    0x80084240d00c40c1079141c030113003490b08440350b200c1500c504440c11240002d0040ea034601e003544c01c120440c9005030340504030700340100c06d004c02ca580c0e8000c040d00c200c036003000d589180004001510704038695200480c0c6040006540c605000c1d41c015056480201602c0c0ba00f0015034400300c2000c900e030800e90050f075541031480802d58000f039820740c49a07003a0820030340c5c200424000030075602c01da040a43d225000071011804002c01c8258401d015035000702040911604081c40500070503142d45540c002909012220030000070078800d01c0d050b80c0b88a1b0261140103050006103010f09180204d001c01c1c4c3c070042094101d1440988050740c041d160941d500d0300c010442070200030a0701c542c100701c07501c80d900d4209207000060004402e4540b0b03075015101136009980342c042c1640101501071146074128000801c000800202c1c2c002d5038140d078492000d10151034060101c1c0745050740300b40a8075206900c2400305004403801501070503440a40240498a0840c2034504054501801d0f240015269100c0040c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 37712433 1250 37711183 37711189
    0x906090f03090618150e1c0606090209030712021804030809060121020103090602040b040b0d0c02030f1c0b0d120305011a1206030c04140901050c1303021009090608010605 75
    0x20000c2c00343d0310b08100c0350300002c036003c5480103240c403580c03942c1080305140c0088180500940d034000c0100820903ca610034140d0b0340c01782e045a80c40c00b1140b05140940100d4105641d00c03d9030484c008c003600512001d410078050101034510014180ea1021920420102441059410a2003148240d48200345800d050001e45e140c1001a0005503484054190342440e080318640d049508940910b404987c80b07038075003020002886a6040441c1e00c0800107400300385064550014000b80c03601c801c0402441d1030002080340c49008505214a94040070007031622140c0e07201c0072020070310072400000610502c0040000714071a8a05030b041f0340200c107030701580034203036014410b8500510105005560403035a6003e940c40c1449608100c1248071000404210035480810480703207020000350080003092035085911110840803144030305250f08040000380217012040030b031007030440f1420a0065290840e0b08000b1403000c001402d20403c59080d6000500001e64002c0b04010070103000000344685c2400b040c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 37713683 1250 37712433 37712447
    0x20703110409030f050702150a0306080c0f0108071101060503150a15060509100207080105090a05060106050a12111612140405060f0a05070501060602060a050109050f0703050a0906090f03 82
    0x4480c481c5251001c80d001280d000b1401a02c80c050f40d1610ba6501c3d00c0070310006090500e02c0303092a0038040c01041c1210041e4059001a003542e8810007140c100100f00402c114514a148114a0006e050040031801b854020103c002d00d100c403c200210303023a9281c0c8046460200509d40050f05500c000c0c050100e08001c501c648012506907542e0300340c4050510501404511520400b03a000308111400d90300d560303200b03100440181011900921803420124020307070340c500713011005071142d0248000000c1c2041c066000c84419048603214001408007116404000700422800100800c02c10841d001c101030a0191124545100d050410104000141d00403c20a1600d079141a8800204400e216540d64402540c521240c5030003801c0c2d907000071403000c89541c024180020702c00d60a105000c511b080d00070030340a100c1c107c400801c0015070380c0c801704201034440646d155445000700d0804030740d0b100c0c0302e50001d40d07100700031007008a030f10340503a62602c045070706a14060b9100156214043d00705540442 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 37714933 1250 37713683 37713713
    0x60303090816031101121a3d050f0d06080f120f0d240303020d0801030f020d0c050a08010506100201020f16051006030303050f100605090402030a060902030106020703 73
    0x7008110302c2d1103000408038101040d00020740004000c1d4682d00c1c1c282e104540d06082640401c0040c42098903d002d0300d403482c602d0000142c804c0840c03544550303200110200510030400141c215032910f40c100010074419103052800881001401c000a0044010400051807119208100011018542401341e400c2c4010040e14180a800180110f29600c2c10242551142120003801070b41e40d40b02c0c1780440c801080c1c030600b54464444015011004e56814038800400c82e4000d070290f4484046805041354004801d000042c164860070f40981d015007000b0f40d200d002c051080b04c5000c4141c0e1a4800906481040c0c0d00695441e9100c000700700c0d00c0d0900d07602c100f8280000307000a500706402041691581c0c014442030f06280111444044103119042100c8100303031b01110010441107449041c010f000c0c1c48201c860070003046511010030321a0049003903480480d9031607a1100d041c102908104800395102800b404480740e2103003c041020801c500c01140248030a80041501c645146000700710707404011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 37716183 1250 37714933 37714949
    0x120c02010e030706050702040e070f1508060f0a2304060803070c090b060306150904090c0306050603120417072c07030204050a03030e04090b15150f0a030509030706020d06030309 78
    0x40f00c2000350980020540b00d80c258120307004034140103540b06082c0f80881c00d922500f02c4911203000011110245900a001303036410b039990400039039a0406224004940701a0746420940440301004100311480f40381403141401101c0a00d805001d00c0003505071000340d001040c464100040c01002c0064401000000b00419001440031a80400010380103000003018940644048036884158078085070840e03081c600300030006c01041c18941000100780314503010488600b840c1c10042400d43ca00042d40a809051681c8081d2030705080503070705140f405ca001100c02c2036200e0302d80c0118144041e074071551411007442d48411400300c150310b01c1c0c0150b008043c01c13003000d240c0704001c14822900c0348007002c02603d4060a015072030301d11400c0440c00034071000c1d6001c0d00e108551018081151f203a022340300710546086450b400350700410f403100b01c00352103011008520300394100b10005d4000c1c02030f00a182d10030000c50989080400079141c00040e41c2c03250004801055072002c0c00c0c81016040244440504481 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 37717433 1250 37716183 37716193
    0x10602060a062114030f0d060311010206090a12020a171809010803090d030504030b040c05040606020c010516030c020607060506011d090a0504060e030403030e1201020c0715050403120c02010e03 85
    0x8051020003100c3c0c42034080c200c20010613184203405801c20480e01c40401014a690b80c0e40301045084004148074001107130780e4524103240480035032000481324000c2c4081006000d20394100d0361540c40000c0b050340c0e03440540c0900c0c1243e0001c68041c0d01c081c4000038414805030307036407201e03d5102c030304c4410029286803194171010014809001c001040d0f58079103a05a90703030590320f4075a0030155464025a40000c2800700c0d40d60401007002443c802034000c03150207036428070010b52105800d03030300c0d0303800e26084030f000440600090810108111400c65131740c0c003a0600e2800080d01d50082b501503131001d10250f0304241c58105110042d64401032002c110130328030200d110910091400543d0402020b03081c14403540e20b60000c01d061180550107010003110f0a4116030740c841e030b60300d0050500c80d480c980d21031240000925100103100107000301d422a25010015050f42800c0c0700260044642c005075010400006120100025141038001d868040380790310344000a9107244001845090720101e050b0181e045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 37718683 1250 37717433 37717469
    0xb100215060103180f03050f0406030e0705010305060f0f04111201030506010807050d0605090c06160506010b130501080408070f03080115020109030e120c030a0606051504030b0406051509010602060a06 88
    0x429500f640c0040c0e17102003051407105560604071651700407035071030300480d40d80040c00040154255110344000028003054640c00740d5120010340c1150b00884d102078104152101c5511140341c00030040d01c0c6098010b0000840c20b1030641c0740740d0a81c1000300120400ca050038018814058100310f40d50051402400a050303140c280004901d603047c40440c000d2107280c8076030200d00300365800e2103e0004d200010b0314154480401c2342c1c0b00c4450241035441611180a20b00000c140fa000800448246c0030800d0301c1a841d5918000045070780d9113005006403000d40d010f1190030005894425803950180c025030b42d81490394100180042c941d6000100c54040da890300a001001036005031100c1c020440448400035112080b0304814148080302400b1360341801a060110200b003c035902810070b40b00140c60b0340460010049a22426101d980005080c46850f40c00080002384280c00a56000580c8600741e586510304d017001c20715800b001e8100b40d0142e0050700402115081c184103080c001d182c00e9041100c1910 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 37719933 1250 37718683 37718711
    0x302040f0b0702010e04020a0c020d05030301091404120c0c0911030a0e01020c06070e0310110a03150b07110d02090906161706121e010605030705040b060a080405010b100215060103 79
    0x180172400340c1c0541e80224036110000e01a40c000000ca540140040100303608520700191613920034060152400d1800c03110543d10308200815078440c950103e208114440c480000355000a071901c8210b44405946101094554140c00780701040006205101d49030708111980f04255061b022400f40541c2c03041c041005140e20024040341c001840d03090080b03031021500007207401d0000c1d000816032a1070910040742c80c41c500640c0203200305d034466502004502d9402d0102d141c000c1481c4248041c541c0107111010100c0c419016103408050014400b03946c0c0401d503804076800c1e860481e1540744c00d030084420400d80402d0914401c1000700b0034900b460b80210403802484070043d0142580340101d41e04400d5901a41d000c0280c4401800701c10810500400c0e0750100302d002c1d0040c1d0065602070701031960000b5050505014006801500030b02c0ea40c1855001d0000b2200f41c000200140d40944d214624068652122003030610704503203a034013a02900e03850050088112038040d0100d410140303030581c0d01407801e03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 37721183 1250 37719933 37719947
    0x2040b09060d060902031c0509040507090b03010306020a090906081b220f0b0a2c19020901030906060f210f0b04030207030b0c030403110607090b0706060909030302040f0b070201 78
    0x142d000d40f000642c1841c1e400480d00c0c0210340c00582c1d03248804220940503158001c0c01820507060121001d10142d07985240032a04481c03d48075844241409200620016180c1c1e0090a14440c0a11700101d07501d5903180300500740d03041c2d0703400508603401c14003809418140c0306030500040b010aa03803074581c180011100301400c2c00808000e0320713850368580101c1e034104181d42107840d03055001040e25844640315a041c0ca48003100301702d60741100c5504110840e058405c010390510415901ca1111102d042810b4050060f42c80107841d14101640c403100800000d4040c41110b010b05038888221001c075080009800c4d88200d0f416110800d003001c2c4118500040010448044c0d00383d0103035000c111501c903440c00340d02e8050700c0e0700300a103280d40d0841081030400d5040302461245001e691680e070a9219007000300e07141d03002a948000040d6452074103102e186030b0300b00107202c1719100344800070f01c042c0e482000c40221020810110002500018200403015850140f1000303000700c40c3c481440c040300c550001e400c0c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 37722433 1250 37721183 37721209
    0xe010e0d030b032407021506030d030b010e0a0e0601020d021b010507020612010b0702090606090d020105030c0d140711060c0a0c02060405060a020d030c0f09030b0c040f08070302040b0906 82
    0x551200320030482a24140881d4010078613a094005070052081c0c0a4004407108582050041c4202c1c01c00300e59154580f9046030240202801400f41d5103c4042c040f00a03050300d0301114140101015644e00e2034803001d082e400106a200c44400c22810110002810001039165000c00c541c04004035642c69640c4004c002440031003400c0030340d0358111505c0452158001c5c00c0309020258074801c00020072007003503802031400c2c0d4800c4405908540d161020490640200c000490f08012154041001940035000450300801e0510305281170200a0140350305640c40320341d007003007503411107801e00000c41e8020700c0c00101007225002405940c54202469001c0f0b00841549204010114404030295240c0d83c0483d0054040504855030750796080c040690307240c0c14444044002840c3c4000400d08610408d2280039003911542c4450365a45952102c4140c220064a11400c80104110026806241c070045100234a421805030020340e14500422045454001c41c59020740c09600820940d46d9990240600b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 37723683 1250 37722433 37722437
    0x614090a0c0309020a080f010b0a030b07140903071d0c0406080c0a0302090604080102070209150a0501050d0204080d2601150309060b090709091a06030c031509040311010e010e0d 78
    0x7000c40100e00c22400b40a41510103500500000008200c040012440448010107400207001901105c0b050240f8058144000b802100c15080461102032281802002003031011280b0b0303003003540c0c020001c1e042000c00d42c0400e508694411703043c00080c01540c04142d203d2854615a0700341898110043d100ae8002401c500f107400b00020b00600b060f0080d4192076030403038042d110310748540e2100c8505000754070000c0181d108807514800583c003071213000e1a43c0c40380500030f04045c248507e0140190340ca5000000d480190f2034003800040740c85481042001c11700c03c200e85e14107032821811003402c0d0344d41d241601101d090381d80341d80041c0b20305000035407110040b0149140000c0c601e420741c201b0310700512200400d16800303420b03402404140b9500c40e088606441015000b04500783d402c00d0001000245041c3e980d0304004107200142002130b81d0b801441d800348020b640303070010f0810384000402d43c01c0103c408401061030071180d024503010911600020f030403048001c0011144a600e4550340d030b50490b000c181 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 37724933 1250 37723683 37723691
    0x90c03060121090c05090604110409180204090501020324010c020108070c170913050112030e0a080703030203070b011203020a020622080715020d0507080304020406050d0308060102010614090a 84
    0xd40c0d0780c00b8000c000400254400c102690407481d016400c080ea81c81210300c60310706640030940d2440d06200d4030540310340c0f019106107001e15050f903140243c19950305068900c90b0034a85100585c03154003900031801e10035000107035640350240d80c101c40002c1111055206c03200303c0f940b1038001e0740c100320110001e81d024200741c0411750b5109000c84d0031411240e0020000070f1440c1241c0c1445d101c20014000888013114040a0075040d01c1c600800c441d400d02c5000f400380f141c2103104010a000d03008500340a40c7c0600700c80d1005485441c03103031900c0c001c1d50044005030300c00610301092004684070039015041c0b03030070103202c0c11603181c034020741d54250300300041c0c80b0314000600c0100d4041e0203003c101e0040c1d608041e04462655410f004e98550320180b1400c2c01c50415800c15000c001c0c8041001c962464181d01d0345820082c19846002d480e4000030030890700b01e80d4484011416039101982511300901ca60703940140c0c2c3c50b00c1c2d03000a0a50700c1319030213a0141440b030064000d09607588228140e01c0468004001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 37726183 1250 37724933 37724957
    0x80103170306060d0903021b04020c061503010204050a060c17070807020111190b0405010c02010621110411070c05060c0c010809011104030b0709050f0a03020105030621011a090c030601 81
    0xe4002d1241c60005074800e45801c5c0c04034201a00426401c000c503050303190440094180c4030500003039219880c00c0c90590340148001850788030304644400c00b2501d01800040c28252180041605801c407900058040f4041455280410000c11502a03090300c0f8600b840d810900d0350790315030016000e80140217050010301d8403512190002000195460540406c3c6100241c415003401c528004081c1c5050740e540d401e146102c0303181401401100d0443d40c0103907410701440040c80a00c00091202c0c1d0701120b00c00c0c1c1141c040546503455026803101c5060144441d65116614946407062041e99408140510307000c1c45841141c1c080803a404407580005c0c20401c42d01e550f1040c5090050904040c1c900c2c2210740880c004c0306100078500294400e030602d8964100d1540c40b18108247e6089951200740e02c542d19000601c0154440e401950300704d0b4002d454440241541030164002c903005000105450303550700f4861007640011242c99296032030a40d2120298104039412031b04030b120081c00d903818005007580701 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 37727433 1250 37726183 37726189
    0x150504050906040b040609020903010b0607020f090c070b07030c0f0305060f0409060609060b12010e090c04090602090a03120f0305010b09060a020a080c030a200604110102010b030f0105010e07080103170306 90
    0x13014503a60041c0204502c035202e0350303408001e4001f09452800307580f80070b52010a90409008458880380c0040075040780b094400f04102c5066001070032101d03441d8052144200107400013940300c0c054051500c1c00b007081556200000d090444000004c2e003018240000e101c599200d140e8143c56034042590007251b41002070170074401902042d0b100c1401746213881000a40c000004016004c48411044042120799890710124000001620440781c9600606003c0001c1d180c591b00c0312245512400001d400c20b24000009544102036504c1514408040d00c4a407461942c490b184a80245860408000719410400d4103a01c03070040d00303042406100000345481003507008200d117481b442d5200d88020b5a5101000e45c460310383d0412104140402c50f41c40144050385942016008a00f030382c14010b1202d6602c2d40c5881c26a01074010b601410740d5030b1203c40200c4c0351000d12a80d4000c8020a0010609500d000810b5035040070003010f510420090034010705c00202403094121440c00e10300c2c9100d80385e44910b400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 37728683 1250 37727433 37727441
    0xc07050d080a0801150806221d011b05180316060c1b080a03230409050906010501020c030312040303061805040506010b031302010305090309040504081315050405090604 74
    0x155008035844203510800001000504203105140d0340c007150781e42c5c0c44182c02ea03030101081c29400842c03800b03000620503041814000d0415200020780341c40c00c0381c5822828089034004403103002c507403540d40d01800c1c42140900591610496995542c00441d680001c01070031070051110142002c4445040424950340402c00100d1500003400c04070013459907604040d040d1010090b08686180358a00605148800723040058219402203000d4601c240b00d50790225080001510000c8901c0480701340900308641c0d01c80580082c0544500c0001d5505140c41039501d0604142e00590465000c0d840d03111881e240403003a2030307900a800c0440e01c219121880c0c01c0e8050005900706108a03006510742030182da00c95084180a517002e482500c4290740c85100c028014441115808035244569032144015482507001d1130340310300d1201c203503818600d4800c00a4141d4000362400c1d2821400070501c841d41404e03a42c6800c2c0140604083c04400e440541030140050141d403185510418000c000a8816152900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 37729933 1250 37728683 37728689
    0x201080a090501021b01110f0702011115150f030d05070b070e0303030709090e0a2103020c0109060603020a0f2301020f010c020d0306050d0b0a090f06020301060c0b0f040b0c0c07 78
    0x1000b13544034801c26000807455142544444080d6083c02000080219180c1c12100c0d0035030511101840c150302600151900080940300540c1445a4034400c10700324094483e8500510f2003046200d642c0411070100320744241c0a0b00c200303102c0e070000c0003000041034010007101d0000303038407850a08143c1c1d41c0201c02d807401c0390207440645e0540400004c02444503403003031680c0c0907248000360420000f03412810709587d440c801e4200400300500030b010010b050314040c12252104280f450054a48030301300740110f0940701a000200c071b03115202c90741802140781c92002800078100202c1003143c48c9140c0448606040d80d09150a04070091802400307189902c00e100e41000000101d000384001103022500070f40d54038410340d1040003c0d2410303002160f2803600c501450b01058100d01911000e403545030441d070041c240316008a03484100390b007401c03000500b1030001d9802070102d6141d090304d00d241c81c2010618a10000c00e0380d20b098642404000c001180440c1b030580150300810110b8961001000103031400001350 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 37731183 1250 37729933 37729943
    0xe01050d0603050d09060201021806091302160203060601080702060609070e0910030c08011a04020c0705150901120504020303070b09070b040e011701200a090906080102030a05061009030201080a09 86
    0x201c08014010000386010a01c00b00740e0700d1507455940c0f03d030100e0807405140b10301006500c501c40840790078074110002d06900d090080544091680c101c40300d074101c0e402060602d4504078881c081d1b009629042c0100ca0388a042820204c10301d1900c0500252146401855540301c0d00e00e640c046003120341f00700c4020000b1103002e0040da00f603040c2024070000305c80461000b11034140131104081042501070180c0c0c0701200701075001c9031200b030743c04080001a400007240d070041889041c800107856507414804e440c4402464083c00e0766800c212000501240303000d901c610500f41010f082c0300058800004036000190025000c644035102e41181d1030401a541d1312140d0f55041c0450040340d01150790340c50a0407a01c6c0d140d2200144401c2d10707256800d131492100c20212120b18000d03d1041207000000401110382945042c1d047c068480c4540390440b4001e41008000381e502000300701c01012944145034012008540980d6411000d14004020100a0100904014034003000c141c55000640003907003200c4e07100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 37732433 1250 37731183 37731191
    0x6221d0417031f060503100510050f0304140703120305090106030b130201020c030d020c0306060d03020a1502090a06030509061005030606040209040e07032a0602030906030411092805060d030e01050d 87
    0x5944000d0031600187c84540090034425800142d52070020460704d8418215141c00d410109064100411508010010b07102c9030210f03d10003040d0141480301e88040c0d80302d6405942c20f500601401012074200401070b208507890b042c0140082000351411540c4400e0b06401e0344901141d910040341014400400c070f80e0544280140c5596050b00440c03014001c0c44160b003180c42e03907580c2034200280440d00c050042d0240c0c2049041c2d50104643c080c600a2203869800c002d460411020040b0340d40ba010b0b640044006070350b60781400179075030082c440242c10110f26820181a0b50401d4006502d4540140041e4482c640c0020407030055280e41d00301c020307549001030a0310350059907030801c00002c0001c01000f004200000f40311440c00000b1102000581c0e109900a50401c2000401e104451384050400d1f5107203045071510000640e108405244290781c505442291500085100410020b110480c54022030400c02041005d0321b650b950b8941c50780d052714199a08103980b0005890794442c111400d50b905082c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 37733683 1250 37732433 37732439
    0x60e010b041503061a090f370b0307031508030a0201022109070b0a090b03010b041410020312071103030a06050102100b0d020402070303111902100501030203190206221d0417031f 78
    0x2010f43c1f82e00a90010b045903000e0840301e03910340d04003500c2300c0c0a840c1c844213007800440d00041c031a501c04c0c00d480050510750120b00d40c681c1c1c01a0714580002e5507460042c2c0d00019030f0080800140d50b80360f0042c1b078203480b50031681032110354107495405901a40c1c41482e400301d14202900c0c0309601e44001820350040156695845c0e19003000b03154000e0090b8040706a540a800072281003820003501c04234032980c003030f50401d0031401301c003002d0220160042c010844000d10000d02ca50f002d00085001d0000900300081603031a100019091404804000c0c5030340e86040c08030f89503611820030807803040d80d0469006a03518180d1806a006001c3cac4410705080240c041401031100c03d2554200041050700e8080320040c00755803009e40207403202400000e400d030704107202841c0329600c1c5110384001c05100410031070404442c0005085807003281c4002605000807120b04209aa00c1d0086610500e100c00c410046d492900791035042605041200d20b1002070000000900190307601148408001a0182c650900b155 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 37734933 1250 37733683 37733719
    0x30c0d080904060f030c05060f04030f020103020904050a0c030507020304080703150e030a080702010f060302060d0b0d050d0c030905031c1107030206040b0403030e0a0806130303060e010b041503061a090f 89
    0x81c1c5c002201c2039400344501246c140341c074000707540100520f825800d2a090460380d5400c650005400c0032814940c003801001015550f40c05968032406079800e0010740118180c60007801d4503800b50020f03056410400062203902d001081e00016280c200040558040c80181c420004107550001102d103404040b906004066008208500490644e4000e00201010307a506904980c880d210003903004d40f0801c0802c0c0b5221181c0c124a1044200814031660b0802c251117090500d000303290107a0014407540d40c144201600703c1071902c05010b06400903d02058004600020f00154038503010501c0381505402030b034401c0c20803035407003e5a409008151544c0d510060711005ea04030740030845c0441c04180491400d810b0181d500011103101400400b115260003400b0000c401d141c460039420191140d402041a01800840900034106003140940c2d503407400f48481c2e20546030b03a00d120105420305000f0820000c00c00d4082d8101140f0404c01691030000e0300000b00c80401e01c001140c5c2140e03031641d00d0540b050f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 37736183 1250 37734933 37734959
    0x4080d0f060510031d1203090f060105011b0221070515070f0609020d0f0303021e0a08060402030c0702041409160f0506090d1515051804080c03070b0c0a0f0c02030c0d08090406 77
    0x3c180304031441006030008a2b61a103000340200c0e400100b00272404c0801140700c5d03010040d10f41c0042c250b007800e00d10904451603100b11800030401c0c0c1e90700c400002c016500300300e00402c0701146050b07403040c00d288442da0348510019800901419039030b1594000401d550718202007c00e030039440349190000504034035000d006900108a400444420b800c90034584009540072a08400542d070f45110382952048108002900f01130517030100104181710440c01615584684105500c501d000e03000c1d076240881d0450314180840d52841c41c81d10701708404000407803640c203150301541d400301c4140e501c9003015070204166400e0b8140141c503501c00c142100b007002c2001d030701c0004040310b4800d21035210798859040c40380120181644082c5400002c0004001c81c2c1004058110003111409607490101300d42c5660110f108180c650220044000850070035007a0003103c41040d0240074181486000c0303441d00001d0300c482ca142452070045440300114410000c0650850706d48480003030003005800d4031440c0004000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 37737433 1250 37736183 37736191
    0x1806030901090b070504060c0311011506030516030e1c0c020d0303050411010306150309060207061b08060906061209070f0f080105150a06050c01021204080d0f060510031d1203 77
    0x40b102e001c161414414000c40d42038076003039100c0d82c00b41c050fa49d6084503c480100079050455684044c3c0c4501041c101c10b03002c000340200d07540403969003810f0403810035a03100303100944203040c40c0c518198200320000c2b84180a407240c0542018401a0702c21065811040f01c25000b54006004071001c020180c02d80c0c03100d40035a004405144070352901c4801034081710344030300802c007020300b0011400f000c45200f03422103031201e8400e071805800c00d0000c4d5950000c0d01e100d0f011003144c02007400c0c0c0d8038000690002d40d6640c0300300d08841603003103400c00c800825914850f00c15806110801c010000f0100541009020014200d0240d18000b00703a4035455003032003030b9981c00780340130035420308011070944c004440c0b001803199401010203030043e00d85501516141c0c003035100c04956540a0100a88107101003008034822400380074000d540e01502400003084a24803e0074200227450302d1010700403500d44c8805640030032440e080c0000d1824259007551070b080300e4211210114454070301113a207403000040c00f139401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 37738683 1250 37737433 37737443
    0x10c0b0921031909030e040c1106070905090a09020906010503060d15020a12050405060622060801150603020c0705060d0b0303070807050705010207081c14210a110f180603090109 78
    0x50f020002c01c41d80e080e2804c0c1c03074000d4001034203041e886c02c492405502c072100520060900d000c150182d03081540c203001c0e00f201d80360b0109003807103020800ca081c180b02541d0303c00c96400c0d080010030a00d6000441840f4040d11182c10010003200041c91520b4002425181a8009081440c8851180114400b030b501800c500d0000410081d001e8024010600444c1d00481c0d00c040504081d0782d44805200349102c40c000b4000c8070340c0800c1101c02c2ca08001d88220005440b022002141c0001e80349283c040d41c9000e40c1c004400c16204000ba40380355140410711a0958008503292a52100502d1194002e84079990750700b50316002c00034070344d8204420000200070340740c411425500324594840059858100d9403190300322613045142d05481c000c0307450007002041c83d200d01303113003440340c11001e140d05064000351240c2d880000300c00300b4000e03e01c580400440e8440da10f04028010309000c1ca101414601854080d030a8042c1c0c00300c0c4810b2601030403a0b00103149032020302825120314200c403103503002e84030400042e96 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 37739933 1250 37738683 37738711
    0xc140706060911070213091a0103060c0207060f17091e010f050a02070308010b0a090911070203070b03070509040b0616080301030b0601030507050f0d140907140609010c0b092103 78
    0x41c0388200805465004d41c00134081c072206070b05190050051701845600302c1d0302601e9010400c140c5d15070408014044c6010721000180b4410b0074001070310304401038000006001c010b210f00c0300c2c1c090303100c225440300100221001c80f25450f00c0700c0c8140350010701c400c6100c0c10740000e004400000415400840500c6000c0300c00e2000392108040740c1c040b4170540c0d030050001802c480050020450b0400104003a0046181c1741d41e1240e070b03641880703044074124030b0700780003907240011000b040d46401c1041c14094030706044040e15508200d90050a588a0008503900545c2c43e154010704554510301511014581b03800d050401c1002c0c0c0c90103101c1503109010488050a000c0003042e2035520a110b070a102e04659102c42d46480c000321004127050300241e180b084250f8139900e01d0341803810204501405044010000c040b101d080c035501c92000d00d40c0954a80c01800b0a000394400d5a80c081e4030300002035009080141d80d030300d0705800c15080c0818a00d4183c2c0341d5171070040b900400e149060055109800401d0400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 37741183 1250 37739933 37739951
    0x30c010f0e0a0209040c1806050103050609010e1303031b0504060f0e06030f040203030c0d050c010b0f030a0f03090e040f061b1e0c0b13020109170703060c1407060609 73
    0xc452560310303a03040341c0d80210640001404e201030910341180c040c1d50301c01091035172140c0d1090090480100c1d441e071552166820030241d42c160081d10f80001c811662407600398181400705500140c000d01074038444042d40c00420a0501981c041031b02c3c103010704099112603c0c03d0502600c01e6002e071183c02e0000e03500040e191401c40c031a4082440400c001454186180c0f90010035940c461b8026000f030303a140c0001c000c1403103581820400b40c425001181c9070380303484100c2c02d9289421182c1c144080e5004044c8580e41c3e002658010903402c21050f8028980144507050742001c40714903a681e00904a0303126950240b01c24080c8408640314018411281070002e052158510308442801845d880b000c00c0d01f805005080ba2041007142c0c00c0c1e010185000405c1801d03588803560910340035185110804580c0d0b0400080d96031141000c030141c036410090100c0410304104c0f01c0d40e90340c22444041c164507038421050520a10400e200310084a01061054580090b818803100615491160555184c9006080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 37742433 1250 37741183 37741211
    0x150a021b07150203070b0105040c030e01020a08180a110d0507120506040203010531030302090a0902031009020304120503090106050604060f0305091204050607150516030c0c11010309030c060e030c01 87
    0x41d482168403a1b0801410307480c0509000190403c6003414040c15180c241500c4a4907091002d844401416500d107012410070340d09514104140166108582d04284891404102141d0f040c0c0c500350380c1581d05050540d014206036040102c039401122039448a52400e0051100004a20f0300940c0210003c10a41d00d84040c501b00200b4120310048402502084803814040c00c0304100c8043c502034100940307001e81000005410f846640c0241c044c29902005110b0500d1a120141019240802d011465401c290700c42c5080c01d09488248402c01100000090809070700390006801050054001c6840340e44486000d0009480c080c64440042d00c1d010002d0400c1c10002030034a22031040f07095007880c0505000610109603c001801e840950340d246020100403a54490700d480744d50240100c0b19081070203032004040d81d02d0810480c0c01c1103808034582000c034610103900f400f000d2090074001403c0000c2d290540b5101950a805040b051800b0220b042115000c4004c200e000f106000800660b03200d1400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 37743683 1250 37742433 37742437
    0x203071d0c0a0c0209060102100612030306050a1421010501030308091b09060409031107030501020901170c1c09020d110102070509190e03070c090209040c030b03150a021b07150203 79
    0x4110001900882c0840140c2004c1176a41c3d04084184141c0756001c61180921042d1a1558080740820f030317040c51106c06240d07041c0304840c05804102c1c0c0384010f1500c0c080034000d0703070040007450a00c200c040c01c8450703504504507000e04141c0c0c4901c07002400b4a42e9a03040141602c1e10485041c000b50182c100503105400a40d511565900401400002c0d0381d01c1304400c0c0030040c03000381400c8080c8580807580782040719003044140c00846c4074000150752100d010f00018244082c4030700c8a051021000e01b4040020502015968102d0f501e549081da1078100941040252825280203904032340300d40064020700c0001c21919100540a808580010b5520130034029902001c840484507052103001c904408011900b24400d10340701001268240700d603949401d085584a54080c0921aa00159416050a10f03002c0c110102e001d80c107081101100c0702c800320303031a11034580d03151141c80070560008402506036070545101002d110207501d00c800d800b0300b081e51b40d1030300b5000300c0602d0211000c0384240350b40b000003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 37744933 1250 37743683 37743697
    0x2240402010f08070302160f050f0601060503040f0305041d010e06060c060604090c0305031309050604060612090c09021303020405090a0f060c051603021c050a09030b0606070203071d0c 81
    0x580e551562100030740440d89030b0f82c00341c120740070150204182d064001c51132003155a018010340401505901ca8030308645024594041c0502c6500300f4001041403d4100050f25800760300a40d05403200540c40c40c00302c400d0300c9182c1011251140084aa110b40705008041d141602c00000100390980c480400f0000d40e801740d0400400c6691080002606a0400d904040325036449820104c1160341c0366603810303003582c0004004540c501081c0d5402c101203400c500030700e03400c44816181044142c3c140080200703050700745210b009000d600c8003090410080c09412503002412200b60440d190782a0050001c803260442c13006034403603801d0034080303400001c000c21030340c0a00e03500101d452862071403079407000d000d840c034080c0007028400d061000c80026012480240b0180b40f10780e029080d00c03018070030116550281556007004000e400c3c4640c0801e06e03004010001500c1e00105001e0301070382c5801c0040d00a100b1101c5c029014003803c400051180e04489107800c400e2050141500142d960101410b05d5001e0a1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 37746183 1250 37744933 37744937
    0x4140105090a0204021303020a06080403030b0a0e270f0a020307080c0117070212030a06031a04030504061d030706030203010e070507050303010b0702030f0109030f0906090e0609250224040201 84
    0x140082c01407500b903006200420b080380034007000599980008034100a55407100000c01c03100401c02003096030510032483c0303510301100d05d41909828400104000c550052600c24204040b80180a920061600d0841c00100703200072502e0f5081001d85d400d440e0506140704a0003031045400c0440c9034040410345190010040c2c0d00e03d1980c0c3c244400820300080b0250014080d4014814014200710400004600c9040503070b0011030258610320b0240008000909990b9401322080b06020000c1d9100301100e04035903452600280c955149085040f1b0780c07620301c0c441580751003424000110b032900740c2c0103541210240501490307180d80d03404003902d5a216034100181650000c10052081e41300000240c5003050001d01240c003902120f04041342150b0311040260081104000040e03141e591200f640d10103400c0500e800010a0b24120b200042c140e400741a03280700e044000c000038409947c05510340340c19905450600460245500d0181d100c3e1702c40c1e20400b07003101012001084141c804040c16000e80d0381a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 37747433 1250 37746183 37746193
    0xf0b040e070c030504030f111002010504030c02010305060109081005010305061012080f04050409110a0b070308041e080304030e040605041a0103090c050303071103010e01050f1303020a12080414010509 88
    0x101400c0303501200c0742e2011414440140808404201641d0401c0941e921030b80d0000c0d0414650707810000c0c68540c0c555001c045a04010812000aa0020801005580c203090118a58995500513a42c40031039401400d440d02c18100c06c0c1e10388000c0ca80005040706d0080027601c3c1e964039441d404845044190080c000e44410f20825030000810010042101c00042410607080c1900e845c005000d940b00d10b83c09841c0ca003591143d42a45140c0584250020812407040c1403400b00d040c0c5e0042c0589000030800303015284e41c1c109402841180d2070398102c155500c201d0f650358a141518014001401041c00a070040d85044404580340c1070900c00d01e8000d50f842110448600643c00045024144440701180d807039901e0349001900d51010405050a13500c03500910b50070000d004181801c40700548100290f82c0e0600c000d00261411146289400c0740c240000c0d403031070303c181c0c1c24141d10349400c20000170710000b151002c0d000300541c8500440d00075807081b00e00f600d072804081e08048c00d841094528080e41d0300f01c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 37748683 1250 37747433 37747441
    0x180f0616020d0207030f060b0d051f150504020c0705040207030c0501050601020705060d020a0c1b03030e09010515071407060c1505090d0c06090503030901050612030c0601060c02060909010f0f0b040e 87
    0x460422184003440340c803010548c5440000401c40c000e58015080380c00c1ea024031003040c074600c0c0708044640c00c4080c155040000800400803103c0d05402c5116072030081e60f0002e0b080c48002405e101150281c2070140003950344060902e0028446106c016044d507030b95282c640440c600d584040348000031920020010350400b1400c241020003944558001802d002030070f6003240001e40300c5504c2c0b038640013064123250050303490b60401410601c034101d0318a102e010780500500c0301c1d0307403402e20240014a01e11a02034a48082d454601c0e0701629071144011140703d401c60024905034020260080c184c4603640340c03101e035070b400c2d0880000c4e503005450700c030f0042d001103940c000c65920507038220603134034003602000c21044015120142558000c0d921801240d441d80e04200c243d04005412149400385580154a45101220b00daa103844040c040c2d1010001c1a000200035581c5030f03c10340d0001e42d00180070a07555613440c3c0001c041442c2034440d2803070614201c0030001e0102003070025103080311a810700c900c40544d2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 37749933 1250 37748683 37748693
    0xa0807031109071b030207180b060406080c0706140a0b04090f060b1305040b09070512060408070c03080c0105091612020f1206090708100207020d0209180f0616020d020703 75
    0x8004100f082000244501c8605618100d5401800540a074001e007004500b0180d0b144a007801060258001c0e41c140144034005880d8101101c00b100e1040c908400d541d25031114501c1c040c0705070a0040c3c90241004151208a00c05508440c09640d4821080040c00720741818030084d603901d95009401d070600c0600900c007244890304070341784a0a00030840080014480078480440350156416100c01440204001c0011410409a4003074081120b0340541071140701b50346580d522005100030055030010903010108146401c1c1034019592000d11036031074482c00c1d51441e000340b00c1201c0c5130030785100d07a603580d5480c0125030803502c040c2d801c80002c40e044a4404c0e0217000c061201c0c0d0310481c0e044a000d0010840301a01882113500621500e0060410140703004000c61a02001c6c003040307200c130f52041096600617034070380003103035403195056500120750341e6000010692000e0540700000b40340603590105c401800302082580c86654960055002c0218614040f691000c8894078040964071140050011038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 37751183 1250 37749933 37749949
    0x31116020a08011107020906060408030a0e041b020a1a060a120203030c030a0c11042304051e0c0414011a030a0f11070501140606090d030302160b060a08070311 70
    0x5030014110210352603451204600b11000c08801000041e40450350504600e081c408103504007500310f503020304080c1030140039034813486410202c50912540c140e9007020b54880742c03c003002c081e109495070b42a41d00c100a000c2c0d00ca0200503030441e40380e500d095403541d221b01044201d0740281009080c50419905051000f805805004801e0b649031009001c6441446400c00050188104c5961500f0294840d840e11440e261603100e1018811820306070383c0c403c4041c1e00d030714855035296410007400850f140c504180703080c5100d602c80d03950426840c1040190030b03a00007400000784070007500c0070080041500d90740c141031502802041001e0780c444a07000c4824400402454110350441c04c00540d000d610102c0d8421141038a100f020301a001148540c1404420320502003250008180d0150038901100000c0d00380c401c220000d40f00c1c80c141c0e072400d0140340c429030556104445c40316402c2105184e03800c216450810482e0040d1088500d55404160b040303020070014202e035482404c9003000c00d90b842c1000500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 37752433 1250 37751183 37751227
    0x206100b0705070315020c070614070b07050c07090606090f0b0a050f040b180906010f0804020105030c070602030c1e0a0203030601030209060706020d09050705030a080409050405011d010b010f0311 86
    0x81c1c0f2800001001241640d904043c0184103030b00c0060ba203540007031702e4034148039103648000141305003c0300b14050484030702c046502c101d07400407020303c0d140c1c1d80180c1940c030f600078007020344607d204440700882c8202c4e9641c04101520495112021119600c0b25000c00304542070061151082007440b06040403401000030b492010584074013142001d03114101e408254002c40c0d06401c0603107021548484a0818a0410313400c00d00a08e001d01505404c07a40181162201406c028108140007001400120101007a1050b04d5402001550347c1d0505006487c10782d00410345040c0321441000031800d10f000c0820032038140d0607107600070f18215560200150000e400040c18603401000070004d0a00123812031006088491408500140000403070400c1c61400d100d94005034000d60000c0c0200011071820810b940407516588804600703603441e0318042d80901002046440c95038100c4107001565601900314454151003070f81e41c1110343c4031000b0210242d9004203441c14042c0c40802002000002c0c8040f2001c036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 37753683 1250 37752433 37752443
    0xa09020a0c1209050405130b16050c15010311180a05060a050402040603020318010605030304030b18010c0206010828020402070501270219050105120a0603020315090105070206100b07 80
    0x6000080d0b2900c0c1c0c034501d94550010006081c00209020614042c0306654002040c11103001d16000c407566081e0700303020080c003100104907942c500c042c01d05104104491040d1a5541030341c2810b496101c01740e02644003030000b140d030846210701681ea641030a14612404010ba900c0b24007d079101c656200b401444040c009503000413038041c0106964459000500043c5003960380140e80740751091003044d00c60000e5100c250b081c0d0400504104039540041a6000e81ea0000a29907140d2541714040c2c100800f282c103946055420807010a082e10340104485d03048071003100550301e5107207202101c40d09074952560300d103501140080e500005410180d000c0d100d910300c02c400024400d00c840481d000c000e00250188020310210650030740450030f100510031010410540f60030361541c02c0000103400390290409100c1d5a080c1900003401d9000c40750412030040da006429225100032a14007040b03841400c0390074490303c1d0308207000324600340d00c0000c0030780c8150541031182c1d02c81c9050014000c01c070b034040481510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 37754933 1250 37753683 37753697
    0x308061525080f0d1d0706120b0a141503060a0b0a020f1e070b030606040603020702130203010b030601030b030a030e010f030605120102040302090105010207120816080a02070503011a0a09020a 84
    0x410036801001c01c4400001c0315501c40251074201e0058a9004c5d61500204107280d0341c80481800c00a294801c0d103c06007082c00c2000344224041004290b4104569409510104c0004210703d138020080c2d0441e4040da203101003140f840a17402c09500c000e4074083d4222400341c604120b15a0180c2c06024600e1991042d11801190104258030f043c1d0125611a591100d954894945031410401c001c020040c22450304d04600c1c01c03200141c07050080748204010300d03400040040456850701045000500c1a00301151256150644801541c108840b96400301c5c0c5000680070340303442c0001e003c501555044e030300d010021810000444185940f40e56280916031245004125595030160140011a401c00016200c41c03035401086a81201a40031034155082100140010707140b0400181e0810f4002c0d031032a40c0c0c0c41d0741b034010505469040304042e003200c01c0819082c0d00b40c2e0f404200501160ad04800034404985401800c3c03001040c4885141e1b0702004401041050240b9500078041c401503130b050080c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 37756183 1250 37754933 37755007
    0x4060e062101180603051207020f0a0b120a0203040f020d0303060f0806041a070203030a02160c0e0f07020d27050901030f030f0e0109090e0a1e03080615 67
    0xc0141401089203031845810000180f0001c4052400054007007039005051150600e0750700caa035219000c00c800340000360b00007d07160095440e08a000060920302600014140c0d07075a490b18000391b040890f2940d8440c46080100f40a600d0034000d89001c0c3d50400201598001f01da03007003010602a03060110240740e200c0500048800460303496000400d41800500303a20302d480d1515140c503411075000b012a03882d0220600c0b2001d5400410760307070301103131540c070040c4d4404009a00314810440d03820002c00c0c00e032401c1c002040480005100c1c501414200c0b2550320240c64401c1c0980c1c81e90300f0546000300003200a44001d5205401819050b4010b409002004807551078402045802d9403d8000360382c8984683d421904240d8000508681c0b1001c80ca010607580541e10002001c103469407040280729034861400c05100341040c850446400d5100e809003961101400a84110680300c0e901500407440c800002503241c10041c01078070201010281062519181d09002c5d40c10162240d91480c98075800d110766 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 37757433 1250 37756183 37756207
    0x30e0106080f0624010f0306030c09060503100630060903111504080306091e070e0103060605120a0e030c03070819020c010f11010b0a030f06060b0f04060e06 69
    0x101414981c0c01070514074000c030601920f0900c000e41556104119001d0010110701c841c0c2046045490034600202c100d03004490480c081c28407600042c00d240009000022440c1c0d950b403046044032030503025110451402503820089a40034410200c0704181c44e0f410508100e01c26020b0810342c01c01d000c105000d00920b03212002260303c640021800705030355101082464000704030403000d00c4040c2c00c100c0301d03510b46a590002c05000252890307004803502408642c0618041001100b4441384070401d00b064a880a402000707162070624260101c2d20740780022a2541c0704000f107076070011011502500c51b8071445107600041000020103c4d46000c203103c0400700100a000620049001d10b41450300c4102800c007204602c21215043c005540c45001100110390b00610301162a08450030701c21011002c4c01c04480c003500100d401a5440441c80d8070102c10001d103450f980e4400307030083d45c04010b03072612900004594030654140d066142c2041c041003050034802c800b94220400050409810031120240c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 37758683 1250 37757433 37757441
    0xb071103120108100b0312040513060324050c0c03030103170705070b070b1005090a0c0e060a020109060507030c051603050405060301090e0105090102402405120115030e01 75
    0x114160b811156400c01010485d000f0034403160001c40141c2465411408501154403071441070b64003d81c00124940d04500d15a8880d50055801074032980681660411225550f244611482030301450300b0081411017444400792001c0e5080d880055103140d00319144d00d55501c03c07007100112401000c0101000080c8280003000c0200f030100d40345034903103110345452889041c0041c540003030340c01101c804009503510214034a80004542d980022241d01c1110100e41c1608800621600300400156800f2055030550141070a0f9019000030440340e00c1d500c20840a075042ca15840000030001d0000103008400708017a03040091080c1041ea25095641c0b0105a450b00b09a00c0f00160565a03468101d0051081c020f0607404120700008624200440fa181c842100300030700a00c10600420500030b00c01d540b40c01100f0300d0001245400031100c1c5d46e5001031860003440c100d403051508000003070000494041c20a560030585100f590a05076802c00e0742071608424001e07612001c05444022460801c80d003881 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 37759933 1250 37758683 37758689
    0x40b0901051302210f07090c170601082511060901050f070810080105040609110411180103090204090602091804080409051f0b0310060905030a03050c030c060a23040b0711031201 78
    0x10701b01c2903240400308811100401c103210140701c00a01551282c10141800d59400300c07007402c0c0310a16071540403102540c51041c01c0a600402d1030740c2c12100c81d0b0b9400c07400c008490000704046800c2c580c0c54a2006098802c10781d403580321011503501140c111401078031420703800304029071807002480d81c07904400e00b501e01c1544c1c103440f1181d45245600c18006008200c800d014010788081c0009002001300300441c0c401c180b8803184901c142016501c50b68440d070000011690014800d109116050824800035401040107521541e280c2c05131007241c082e0b80c0c03025881a90014100c609080c504914400a4603008111b4510388003c1c4400c6045441c548142d4030142c25a500b20a45914011800c0c880e040c030540c02c94010f01c03195400c20040c595000034071802c06a8103141c85501c61003020b00040c80c5005526120719980907460401000c92499840f01c0d40414451004a528818200329113610380300607240644840318040014200f50f01031290903280303004c40011203181036000184c80300d4208003a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 37761183 1250 37759933 37759963
    0x180d08180f15092b091409010504021804050406020c06010e0103030f08040c08030a021606140702040b01051b010203091902030d030510050411040e16080103060b060d090308040b090105130221 84
    0x1d084e116446501c0034440f005020501450f05550008200080545105208541c03046070000781e40366110710030f81184408084050018031042c2000d00d4054065004180c588a007446550b0001400008a0307440d14101c03a05500c030607682041c2284100c0f86108018000d5031110381c41d100004980d80e08200500d0b5900c8558040c008000d5042c039200c13004507140d4041810810f124940101d00401c2c001185c4600f036048400040000070080180da80d0300951501042c0031441201101d400d14042d0015032180340154244c0307590840e444444011030580b840c011350154001c81d9120200350203680101c2e0081140d1100204643d034a000240a4610700c0942585070140417408203c41c4d014090201c1c0c025001c0c0c4007040c6000d80e4400f004200103030521000d0b01141d1a40c0c00c0f1013003515030104070340205c070000000340122140b40c24080c02c488002c4d0350480c3c0302c1d4005c80014014086c18800c06000303080d5220b003101103900b10b4080004c0c00e42541e6a48811921400080c05403500400c44128009214 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 37762433 1250 37761183 37761253
    0xc0306050604060501080c04090213051903030909050f0a0e01271106041212030207050a031e090510030b03010b060307020c010f080702060f180d08180f1509 69
    0x119042c8010b03603609070300ca9810702100c0c0052244089448007641d090304c44103d4016144d011030344074031100c030001e607000b5508a80110811640d0002d00403040c01034034041d4642d05401669a02200d04850b42191885004102c0002145c1c804606400c00c42c00e0705003030310000c01d1961200c814060f0041401e54041c115880078102d0740104030705100c4622a142c0100d0303141d811309252804181785002c00010081464441c03d0280300103d02960550722001d0b0400e040307901c04003061401900c2c20800c0c2c1d203c0e00c1c40202c803080d4195440d20814280c8159280505980b030740e404a0304040e8050703c40b02180036410f5407500c1a22189441d0301d405940b02d4605640100000c3c007c00c0700240a568080e00110104032040040050007500007500c075401051182e4951820780d80c0c072042704142510b03a424140c0c940075460207440c015038000a62405491100300040712400e90020380da9551003d41c940300003a8100203400250040888a5203512038a00c60994071109170803400540403001c00403d4405405d02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 37763683 1250 37762433 37762441
    0x709020405180603150403020f030f030f181506030705040e0309090c0f090d030903080d0b0f030a03080109020904090206040303020714040204030b2701021c0e06040305160f0c030605 80
    0x44039885448198005540303203050800211703464113195401e446034002c0810110301054801c1182070101c03401e21055035103500b00b0ba6843d41440d0310550b500c00c0080c14032004181440642213060120040780380c000c2c262507e40c20482c1224002c01480d89a1500984c075000846407150b01035511900c160002640d40c410050301000200000038040b600501d00038041c0c1030b07a18003242d0440c1c074021011241c1b2410442c0a280856411840760001040d00c080800c0001c8003a082c1c3e084580206022602006540240002d0680c0c400084034090009001540104a0404c01d0b07801454a001e0140c0301003070b04040c42c1c022500750390145d031040b00107a020704010000030b010440700c04001c00d801c540542c50b291450715004841840607003414000e1450450607000045d4000e041030140103003100031364490714042c401c1480081c0190403144035904021070560121070200d0744030311540c0d045d00c030b00d4201072000c0e00c0000007645095046510344800556000030418003070348100214403400c000b280da458 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 37764933 1250 37763683 37763689
    0x409060e120715020f120405030d0903020c030c0907140309010b04021c050a050609040818040c03090302070909081b070807090b0f0a030c090b0a05040e0304050109060e10030b01050c0709020405 85
    0x103c03800c01d0094207205200202d01a001001102c120700d010450a46c0b42d6111070074032074110b2003240d503404c1e2030074034064038241056004a0251303201c1030220185c42c228000d010a02ca062a4115a00c1c0c0005501c458400c00c441c00c0d05014541100d2104000980100c4800100b01240e001c08014148040320070b02e01c010040c81805460380c41030245034140503034188400490544140648018071502004c95500c40300e040c004005d01d16400010b2040c0454104000060f00070400d220013034005000d469000700c3c401680b80035a44005030700c0310041d40b03410511190301c800324400884105050054400000da1800104000400713801c1e541c4002882d4141e000801c83e6401204018600603034040100f04082055044510202c90401001242c060042d10000b10ba804050f04031030340c49031800041c013109007800400f0b80151042030300c2e400d0b9500c2d104d01c0155007214041c21a640d001c15a04241d182180c880d8000303030322800045c10300f1410507070b69003015410000e040d0450480c155000c40d08102c0c0c0c1c6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 37766183 1250 37764933 37764953
    0xb15030906091912030b090c130503060405070512031308010218030c0a03030e010c0b040b0105030105060901030c050d0609080313061d0303010e1005060406080a060515090409060e1207 81
    0x1c03821401891031001101120f401c030003260001529841d4290300b9405180c1c02074004000454005020702c4003491f1004002605030810101c64140144401c2d000c141c41c1000903c05010300d03040001420468074040402c219500d41401504060100348090148600f0218081019102000015840d41d440c80380e071701080038084084622a603c4094100d0702521281044405c0c0d0b0f4041c0740198410100b50016a00800034500c01071207214508100000e1000c200f00c480d0580713078104c000b4001c2d80c0301e0204110500900f07000c083d0018190b2a010013103480e01d0100f0903005881842d01203148070082d150b00d2602c0d0412901c1584402c2d003607076000100a4280700d0b040401e0800c00a10110440018a5a80d83d0005004041854212401080d644c0401c110110014a40248600d6070380380c031074900806100080d2200b01d590b5040c80800700d41858544813283e284401000c066041c5452802000040d10015a050714030580c0d5440260883e00c1c18000020165a4800f18039640c26661500440c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 37767433 1250 37766183 37766191
    0x30b1614040302060307030506010908070801020918010e0c03040303111602030d08070207060302091315061403010b181f0e12010b01020309190503192609040c02010b15030906 77
    0x610401c8103000584d03691003500d821054600d0000786556602005a41c01c4065810191462007120000a07103020150010920308000740c1d240d070078807081614220340d400028054200300500b202c1c0010200d651010146522a00a2802141c4008082c10342812603201f485440c0c00301c24840411415401c00b00301040d845d101c10318113a1107510b01804000e450f0080c6010b280304264000540c564145c0e40d9a030707507244045440c0d00401506400e2202c12441c1c11080c800c80001c144070b08001c2d0544040081664100c440240205141c011080c5440204902010003581d02040901a5012030601b40448001401c0f075901d40d10100b40a10003089001c0c000c28040104580c1085003000060344e010007a1814003406594150700c000b0301840e4900513a44c02e411003a0035100351100030040810304031142904500420900081e01c004070000404511165555880340c9000c0103419a1030915a0040700c01c40e40500c000540503541c0000900820540d500c105107004010042c41002e1805100303150704 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 37768683 1250 37767433 37767467
    0x2040c02060f0604110712050901080901021603320309010b030304030f0807030203070b070203040603140402090114030f01090501090302010506010843090608090a0201050d05040507030b16 83
    0x20728a04541d01d2180c1000081545004a44803514008944d4030712095034201513100500c0c0000b0394010000615580214003000c0c001643c00002c40d100180c10310846054524420f4a05400203050724162111081100e240c82d00c01060a80440c00a0200415a2980c07a0580c025952400c2201501303094030f519600c050f100e50803c010400029551074803541c0040e03130048245031100c20070f003000d03802c5015000015200714905404c001c1d4495000c40240281c60a50302c007084111885000c4800684040380c001b0b4200700c2000c0107200108480d0580208a60000c0c03c030345510a030010714500790740c10340c0000c0328140e44907266441015021301840303622107000c0c41c260314140741c080d02880f10700c083c1201040020a4541c104140c00b941803041203426056840e00000b180c484120050040315031384105000120000c01107015004082a07100846405072345d000d0820601007586402450040c2c011500761007207400002c0014110981c00d4495075005a41208011600a0140c101d080302006100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 37769789 1106 37768683 37768693
    0x21090c0a170d03060305030d0b0307090f0911040b0102100b0a03060c0c0302120306030a200d14010c020601150e030106080f03041d010f0b131e0302040c02 68
    0x1081d4800e6908541e102a8004811003c0701c006000050254000f0410f00c3e46240b0280c00180311050024183c551003990340c41880121414901c443c0d0b4526100e0084205203c02c0c04907852100009507010b002490810340003c1d20352110401d20503145984045121070745d241c0c409200c2c05180e009508128002400344d001d0f10817000300d14118010320510602c2a12034541105590040d040503000f81417071001c83c0d841c0c006120316900560103504200c0d89003986962070040c1209454082d10305131440240441c826825181502e000c8000d640c8200010010300080c0c0f9100d0001c60b0880c07509000c0b041803000042d000d0407a80c0d0092f001c600c148440d014040c00040018021103031030080807c40ca4100711040000000244140280c2904120b020030a12251800404181103040c0040707200f562149040341082298a0040c64041092907084c4114107081c4542000c00b1030070300040c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 37589933 37769789 := by
  have h0 := BRFrame.cov_init 37589933
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 37589933 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 37589933 ≤ n) (h2 : n < 37769789) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
