-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2847
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:55:15.886987+00:00
-- url     : https://prove2.me/submissions/c728e45f-f009-493e-a4fc-4165490b4701

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 511870503 ≤ n < 512050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 511871753 1250 511870503 511870529
    0x414090613050c030d050d0509010504201c080306120d090302040b0609040504050624010503010b16120509010e030105040c050907050706050c030115030603080f1608030403020102070b1b04 83
    0x68a00140f0301420b0109aa03414011940c28526040d444400340c80081405001406140c4072400042d00b2070b042500c4c003800030036002e02c002081d498480700045021802034010181c17441c5410510010a52284040714000750000a02030745140c84401c50504103c00406040494200c5c0d0010b0021549480001d00594036404042c02e940c0d80d25040d140141000b4005200a24142c5000b50302d0390740848644480088000c2c03811202c6c05403444050a595043e100d8605e10303400d2440c945000c0d08809090100b00308881040e0340001e0b160400c0040c031070085e803100341e260b40ea100c0000d8030700700410400c1070190380741c5010400440c6008000304100c072402e0750107441e580c80d4800100c0e100d114100380a81003d00700f8040c081d800c14090010340c104ca140c1485100c22500d11441201524024407000e0700451050200c0c0004803c0d110062451010702c24180281d21425135400710346400490b000d501603580481c040061102c6000103075406071506003082d170703c05032003034454686000e103020b074002c49540 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 511873003 1250 511871753 511871791
    0x50409050a0203011404031706010c060b0d0f080301150305040b06010f140c060f0a15090e0c15130b03040b0f130b04120201060f0608010909020609061804140906 71
    0x20520140e440ca070740103802400a0142685e0100da0003205880c03c8000038111140c4500581c0c044030b04900801c4145d42d01e00002170b25071200340103040694422030b40241d02d020701d00e00103041c0e62000819144241c0d00280c41e580345c05a84121116066030550506003400c08100009034a642c2c1c4940c440705c2400d0030308512075002821168210742201c4121100380000303407205042800988540710700300800081d04140d44641981e001d54640000c2c0214030032501e54240040f21403500136200c01011034084480d048111340006001904500540034551000941902c41601841d000d0703010b46025002d02d07145007400d54071035107d2000200b40203410711342840440c64050b000c50704090401e410110720402d506103804c100810500405100d8050340c64181c0001d540c04600804604640c62034039a243d00f60302c0c249555000c2d250043c42280e00c0039041140c0303c41503469034003908564811056a4820100c60014001180d0711800803000127000305081080309200051a582c0c00042c103503600b240046 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 511874253 1250 511873003 511873013
    0x909050a02090a080601080c1c0303050721020c060603121e0d0c0201050609060103051003020f0a0906170d0207052805030f0d0e0a0302060316120c120e060709050409 73
    0x94041159201c206481c0c0004d01040025a4a05031103542c8191040d0a0714082045400003001401e4602c1c94450078031000400c1c0698841d60f4803281074184090f090945801c40000d0391444480400c5607540032440c4044080b00700161540700106400405812409800b070b060280207001000c48004000040032041300c9119060710085601c600081c0102120084064080c080448000b0300900910000a40e558802e008507805183d900c020620794a0840c1c00f401090102544e805400806101000030710100d240314600007082d040380860781c225000c4200d0307030034020905208400c42d07101d00c200f4030003a134441250310264059030036100e407043c4001424260102c1164015036260007403184800e86907001191280700c1da503440e034603102061856002c101d4401100d006c040e4001030148000784540740540d00c03603c4051000c1c10030743c4404600607928801d4910024224000800e4001510702d00e41c0d050155902c00f40c80c1c140075040525000c01c00030607135911840b030a8460394a03111481f040c40703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 511875503 1250 511874253 511874257
    0x5030c0f04080d0c020117040809010c0203030708030103240207171c050a20070f0201030b030f0f0706111c180506130503070501050301150c1406090601031b060909050a02 75
    0x589050743c3c0454803851010b480e56075680c1083c0d000c101441c0b04401c040c00091603c61155a00200407818005902d00448009900c5e0f48120380602c4100604808103590700b020b0b42c000c41c81050240d03403880da4540c0c00b05c0705c0d0141c004d0b504803403401400400001400c80c01e8007800c8580201c44642c80e01d0130808451710181010410b80c926605d008c060164003045074021041000440306e140072051031303ea08150051044403c081d05914100440b40019882500403981c3c1040040464000c5000084401e041280c0ba500324000e6901003101001030b640c214056a0703001d607054000d840690840c00c01c0131012400b40c400401004902101c0e20030b0845004802c5000c0c24015103103035220340403003060b40482e445d1402003034441d10900000048a43c41002124180c500054154800241c000f200f42e81c00b08201d101200d074001c8992560800510030004076100d8441d14000304040d500d14107000d144544007407164144000b03a5241444059081000e03c4225080140c00042035a80d4000b000000c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 511876753 1250 511875503 511875509
    0xd050402130203070f02010b01090b0306090a1b0801030201120606080f06130f021b0601030309120611210612190c0e0903040806060901030f0f0c051201020a090e0705030c0f04 77
    0x40d07032000c8113000c0307441d6001170740130100d5145800800c00d801400c0019506542e9910030310390801c0c0d0800001d9002c1c00c1c140d9400d074110f03c0c0b10102081203440001000e01c800c0c00c454086001a800c00010401d543e0300034000442114003200400c811410f2580c01400c062000b40400c180c074400c600071420940750040c6005403040002000c03c0800d40d40408440a5030000c1d02c070520b041a142c801200c1d0786400708180e4102c07641a15070b02d00c2607140216960000c3c840103400e0f901103a42d0114920200d0024004004880140603803084d80c04082d960702817480c80140c4080d008030404200a00401000a0b0178a140004604418003135000c2c0e1500c3c00d8200b0984e0800300005510105000071144000301800580303040a003594480e031307140c40c24000591400d11000d0301d8040340b550040301041c01a1000a8064012442d0b08800394448c00442c0b02d0401ca0fa44004542e940020841c4c40507901000c100080c3c0800e0311080007500300054000c0c0780b4000030f0008020381c400011081d4100400350700311001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 511878003 1250 511876753 511876789
    0xa061a070311100e1c17130605040305120a141b0415051306020c030a20040c1116080d0806011701060503180a230c04020c06040203070510050d050402 66
    0x1403040884018003620102c80c00301040d2080c0e5504212609034036010410f28210340d0384100d88000c6d901c02440014802070a07000b00904810380343c0300440d0709401900d2085001e07403140f0750345441040310341d940f00c04003c00703c40c0740c18644610300001c02c06040d00103030001007a0f000f00d68008910700c000d00300791003039902215107590080310303c81c10150000040d000140342d190701000c0740d0380c0c0e8040a90b21016216001c42d850b8021745105400079a00020041203141d000c1d16000e1010606c1c3c01080c101c0325681c03c04408102040d071030384000d220402c001d0402000140c0a0381410349031400b200d523543c19110a11040c8000c002c00a50f060b4458048500000c81015008049503920fa070b01509560080e1802d29410030528100506800c00050342062b0543c81914202e079042590190034090300813000714051401580c1d8882402e40e039a0000c2c004420185002c1e140a00302441018500711035980854042c16400e4442000550014181c480d00d000b07502004ca0240d84610009901d10b41880304488 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 511879253 1250 511878003 511878013
    0xc03060a080115172b03060e0a09050714090f040f02100305060a0501030c020c1201020c030a110106060903020109090c021005040609030905030304151d1f0201050a061a070311 77
    0x109504400090b000700d6004d00c1c44182c1030360002c030740c0700d8507800c0d41c1010b091a45a401d030b0030040c40d000c141d90400d480c0c1c0f0500e0001465625590025992201501d41c0c0e10500c7e03c8408400a01005001c642c009041d0074150f01141031500d400700c1d181e071400a21f08451000040000f90500220071411903500790f0050421581000c0c04502030010311040d01c407607014940750540400e2039406417150501d5a80383e40c009015041c03002c4100f148482088200707600c195024007290703c2900c0200043c02c2c60b000e19495100208035622205400c545031548460f04000d86000c0800250341c000407404150b0740185000b00e8141c4000394244e19044c1d0551281581a03e0a0108021700000742d201c445003501c06e5079428016a5640c04040c0c1da40514000e25841c0040005109425805030311082c04071200030000c0c10b2442240300c00148440d9004e40d0041c8080c05105021038202d40c20b110b1035038084000c031020002181451280202c4104922004509100028401d0189030117003680c1d510f06285041122 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 511880503 1250 511879253 511879271
    0x2150a060b19080c040605090405060d050115060329011b08040b03061e062203020a0e07091509060c03030b040f0c020706020109020904110a170c12150c03060a0801 72
    0x903581034a071610002c0002c9215000c078074290030a5044404845035603891a0508907107208200080c0405401c076544800c40030b0b2440f000600a0007400c2e070f890f00130411958014a088405001e03921444030000708015135424500011040d031903c540741c03000a00e06014500704004100545944122029003280f801140003e0f45211107001140304541c1034802b001070602403143c6910500311160303150342c4170b4000d102c0c902d02003400000c5c840c80c0c0c11040e1640540e107690381e0042641102280c21a10b0f203010117030100201c00d03810549000090665461900001e1520600101075494900031a001c1110300b507000418141300340c10010f0740f80720060040101c4030140101c8001009010310150150054030400686c00d401841544c01c40d40e0054844141d9580e15660202c6c000c0c655500e040d800140000042119003400100a050038501002440a9a42d0100b00b04881c07440f0790023120f03998480a00c4808108014810703540042400c010b0907120344070500019907141607504000d100790f281111403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 511881753 1250 511880503 511880527
    0x200d0c080a030e120d050f070b04060219020616120209090a0f0507020d08061903050607030204060e100f030b040e030703051e09030a0b0a0902101e050a02150a060b 72
    0x2020a0a02c00e445100c00c8489400a00c215045135000d428900d801c22443c1e900d145000e80010210083c0c05e031a0140381204a03950780c6078054044d58241c6d5407584c081200406408021004840e0052600040c103292031702d0301140d40c400d510141e417101044801c031141c04ca00c0c0b00c281c05a8000c030100500c01415403230b02806a100400150300d850b1401402d00b00840c000500210b000301d401c45459907004003664a032814080307418105910299032214141c00000801d20a114450040d456540d01580d0b840c07800fa4000d20001c1928689445a92803014426141d60445100000001c0d1070034042110204000017600610407500240580c4c0800603d1008140c0d0080040c4441e8850014580c0700303c0d2142050703292801034101c0d03181c0540c4019882d0000c5a00a0503c0b51f00500745000400d610140380d000c9103071060303c4520030011508107041c0c0400c46c42000b04a11200760303103281103800c00121000081d6101140892580300301202000310316103481a030843d6000e03080021080b56030320205411 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 511883003 1250 511881753 511881763
    0x5061807120f021008060d030c050312041410060b03070c0c0b041706011a090d2604060e01020d050d0e0f060c040806180706080718080102030601030f0603200d0c08 72
    0x2c22071090400030b540c0c014160040c02e01900654010b00301d0101148180d07010b8694654281069801d44402d0060401c04004525454410342c80380054041c0c0700c3d80e50803128a400d00a811009030306042101c20b0001c56880d100381ca50181940c81c1c45030300100f1342d00b842100380126400204980c40b0015003c81c5a0040500c48100718407998116055a82c1e80c40850701c01e66801e185002400c0d204011411051410082c441c4c4942c5c02000d807005c030040428a00885005480036458404002140411040c0e17004119140381200a0015092000c01580024002d2160665090310590750312525090042c0810000440144440c229052400c1c2250242c9a5804c030b84a50052441943d0000f000803071100301441c80c0d0b8004034014001e45090070340a80d850640140107000300300c22181c5544021501160000040c464080010381c1e03820709100040a070f514194103600100c0c102042000060390800254031440420070042c074203001c80b078000030316008150401800f203402c0c462020a001c000403038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 511884253 1250 511883003 511883033
    0x3080306030f06100608071e0c0209060303070b0a2318010e0a0302060a020a031b090810090f0204020906090303030906160f0206060d060f06091a04090506180712 71
    0x40b01c9180c920b404046546480440b40500d48100301d040420003280508141c03074001c01c49081c400c0000280781040d100300c8003111500d0b400510510345030400c0d4145409019000781003980a0351a0281503250f040701560083c080502c141d6032000d9000b1620750842081450300001b1001200508040164010b10a0105e500540e2035180c01d5000b480084002403190f1030b20b604d40c0103090b240c1e03900b0075440003d40201c0e440e9018140c4034800e8004621900607800e8444001c4e85074400d407903041600040c50041c1003201c006d00c0310300e0282c042d004101880e000071010740d81103c000d0703aa500310b1004a0003e0080350b64050b05440702100344404200040f4906d8400e00404900032034400200b9011150156080600c4016070011008101641080b0701d100b0241405440f010410500800310038045550755441461225569100c14883c1c44401103419480c1c10700715014000c202d075076119683c4404003d0180c0e22080c1c0b014405944051060208500500b02003c101c00e8001d2103080c80112009046 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 511885503 1250 511884253 511884259
    0x13030803061305040f060b190801050403030b01020601060c020d021315090c1403060103052701021c0c021f0906050a02031603061a0703030f2a080106022e0603080306 73
    0x500d000700c80c2d2074030440b4071594001022090300000e540b2040000d00b007001403140c00c10b1074100201c040f140c02141d040e00600a00d000007031740d0710b0300d030030028100d03011404140d0464000200400c102c83d80401c01e400c9141c0c045404c1c0a541c20640b000456080302c821080074458180b0400403108589041034004541120000707200c2d4113100802110380d0140c2e40340c034603041003040c4007003a1f180d480ba9004a0744014051050b15010420342894404e15130110b0820390b440e0f400040c100d0002c1c03103030301d561001c940c14540c040c4803c10200e60060344030300c080311028078200024424107910f0b01590b081840841d030040000c01135810719081e200080c2d07108507040f03003000901c1c440c0f840e11103110344943c8040381e559501d41d10440003107244e404450340c40010180d0806860b200700440f280078038404c0b41d91400840b02c413411481c0d400d541c1c1c2203540c00d02e00029810302200100412041d5008103503402c030340c0d42410150b406190316004d8550003500c1034510301000c6151181c044100310b8400019070080b9412 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 511886753 1250 511885503 511885519
    0x1030e06101502010b12030429030f06030c030109060c1805030730060609060b16060203070c0506090106080609060c0412080c1605011d0609060d02041a040519080a030c081303080306 80
    0x1103009c1c0100b0508034260f941800070800020300c0006205503990f400400040607170318040e0f031040000e800c0d030b08983c03c00e941440c5d840c1100c8003182d0300030f04e8412581240000c480303001c520b414001b944840145c0718985c00340081010a800c0440101c42348203204000c800c1500580c0b03407170306104000340481d000303044c00c142c13501c2c8011036018400b0b800e0b034003900301d001e040142c05540e0b6907500307029400103001003061007010320818000840500c540c9120300366030400004d220380307000348079850054042d00440c4150070420138440150303200310488060796003076912684040c40703c1c030b0a029507110720805c1034998060700c6c1030512610000400c0e1021500309980d0300f4000f000c2411807242c2141410641a4041c40410400c121401d028002e88014080000700508140ea6400003102c1404802007402481c1c82c00079041c00145484070314150a00c2c1c160b00030354041810980416540e600ba2075002c4d050244142d160410403c0d801d040710f4182c1200081812407a81e039250216154105580c81c900c0341c00302d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 511888003 1250 511886753 511886789
    0x1c020f0a080d05060a03120309050c0406031518020105070f0516060f03050a0b0d02040504020d2310060e0106081f1818030e0d050a0204140601030e06101502010b120304 74
    0x4481d0102d800e80e60007120741fa05124158070103500420704c0c200115028000c0465000956491381300c0c038401103004595006102c1031200319a0100c50349014048001d402c010010710150342d01c43c09482e4041e620080360441412142055403510890080d8009406070304900824084d40c0300c5105804083d254405110075221500340006031028000c01c030343c100c2d064520749c00240c685038204c560880e001030641d80f244400381d107401040034401803403202d411040d10316411690b4000c00038840c0d5501004000c0106130305140512070340e180d062103544200190700010645646c8081c58882403401d400070045c0360706a449000c3c01c2c0001d40d0010400a08d807400c0b404110804881c2d44070b00e40e550b4075540303101e071201e4840c040008030301810310241c43e03074800d40700103000585603840b9a074100725051148503110303d010380004082d10400c00c055495074100405100340e050160480c0030503250b144004810101c2d8082089004203202402c055002e03401c000e91744009080030000700150780d02000c502c94a084c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 511889253 1250 511888003 511888009
    0xb030f07080d0311070f141603020a0603020304230c100203040b030604090c0801050c1c0c08040303050c160f0b0c1206060d090f0308091e1c020f0a080d0506 69
    0x5038841c0c0352040e004140030991892096221a00388007070048000c0c1003200946070349408080307040d01252240c2914801030094034040100003e20328110812142031419a07002c1080080c09214403001c1c0f40e008004030f0100917a0503082800164111010040c14042c185100d07555030341c0c9a0f4690250304141c04420300148003008450550744400d8a50346142c860741c0038800144849902910303a20049900072812100a006403801042d81d464078985807120740340c041c007030f291810321071240d131500d807908410300304c1c1d00003800a6205425080000316540c400d802842507224910360344101d2040702c044201084040002032005a002e0643c0032010740c0c03001084021482554105010300342001c00042c0d00e031605a0050098405118012405140c42d540351258580b09040850200300e0300c00420403a51000c110700902c102d0048900003028030340c03c510a40340d000046c004080c505001c1d849249041c0200038054829010204940d4480920300341103004c0c1d005141915092820003000c00c00c103207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 511890503 1250 511889253 511889263
    0xf03123304110703230c120418020712180503030c0109060b180c0304050304090606120b010f1709071212020705010201050403050a080406061815050301111e16060b030f 74
    0x80c0d85a2100b041035900007071170019808040c4d8203165141410004c0380c1001c04213008a8241d840b84014503030301c440c14074465024541340d840581c1c50341071040c0211404107010884404014000c1c0c02c140c550038400341c4000904414507000260588000a00c00108d00015800380c070700300b809034000700300c04402c00c4104040070240c03800c6406a00e5800d0046003000015000854204d445802102d1800c0c1d40d91000700c007901d250303a000790003050714444920b2850001c1c0c064404440800d180500e5428001c0a01400c04052400e0510409110703d0005001410401115002d010064603410301d42070940ba0602034000d03031070003000050150080c0024a54014040c06000d00e80c952a06418540c0108040b0f680c008000c0054401d04c0e107074880000c4640804070307032060008000d00302161104444000c14801c6406038401c4e4000d030f00d401050a00e201012040d00c5c10689502029000d10100e8800351080313000b00040442c80b43c00070b484c40401c100c1990720011320440b0039000c2e40c400208a03041030b9210 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 511891753 1250 511890503 511890517
    0x30c19020904080c010b103c0e060c0703080a09090504020312160c031202011d1009020112110d0b010203031e070314090d020f0f0312330411 62
    0x71100d00109001621500151899011800000594840344070002d011407995200d1800850081e10845101c0100c0c0410400c2c03044c1c000300d070028040d80360602c014461940521f00b404002041c415942c41d5500d0900b2525441c0105048814482cac40b42440301055103c03a82400101e6420800001c491149020f0280308036002000381000e45500301010f04070b60f002c200c5980004071311150142c000341801c176030030020303600828410f20308514010010742106c1c20490599481074644030840c00704000024540c0400c401084007180101c070134401a501e4103100c445250401741445080c201c008007a0f00542042c1e100c0c0c02080c0700780301001005903103900c0150741a000e40702856083c213405d01604d8804e56008032051070005000e40c200c0c0d03c40c28807044244c1c0c145440340c000c51b0004c0741c11641003010035650704580d80038021403848642219580d200c1c40804480c0d1040280000d0b0541c4041070002e504040420000c0305103041c0c10151100a6075010030b000d1080e458811041c03822001d031002d855107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 511893003 1250 511891753 511891759
    0x1a16020f1507030b09070207030318051516121107091e2c03070501050a05090a0f2f01080f0106090909300219020607080c0717030c1902 60
    0xd003100c0745440700c4a880140850145911012032030080e481d202c3c02d583c843e01c030340c2d80500341c65810741c90024009894103640e2810704002160074080f9035512072410358900f91010166540794080405a903203114007201c0640700c2800340c200780380e0031608144a9200303003072102c00382e99886898030a500300701c42d901000851071307020405824800c130249501076203001c501c0c40200c2000c5058507800d17030341e00d10b000c81c86001d103504041000c0080005c2409510b0300300341c0d2a8000c0c0000d1600c090300590391480300c540605000100401c60040c020178000000241034006050940401051068501c86000141d02400142880c00040d01401c00b4964241030704c403207503030700b1001507e8018841c2c0545078411042d2842e00300c4081c209503401846d0000e1500c407034221801e003510b0351904400313070400300141020706003005010348a00050392407030304591440e940101b059031503a040a241c5e501c0c0041c0394110710001c00e88100c4854424000102401d00a07030f51600311202011503902495584000460081d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 511894253 1250 511893003 511893013
    0xc0f0806070f050d0e0610031e02060a180e1326160204140709034d0d0c1701060b0d02030c0f1303021002010207020307090b01020a1a16020f 62
    0x180b00c6100d40001c0855542c00440400c2280100c841d031810008150b070b0b24100c3c0410614100108079035078402400c0c0341c100f601980c1520000d50045542c2d0303c50609200200003451029028540c40d015051000d13111a1f4811607151074065205061070380451000d5403e1041c7c41d09519034440c0d01140d09804220038540141018240d0b0311007001030305030b008101c1e4010f4540282c044060380c90012288240307000d68600d14010301c2e40c101503051303102c0440f01c00b0700741c03160320b080b00c0701c4131070100580d060441040d0050711800c500b42c4c404000220080140ca5214402e40c04031024044a40b1569003540d21041c00d001d1554110041c02c1c1c2202c90501c05c409000c00700340602c03180180558040e40d800140341c01554a0144c001a40c3d442d154030400c080788540301c10342424402e6043c100001d69201845000071450000f4030b80009a82c0d803d0f038401c03c0c1c039076611071003d1009a40b081c011408102c1d403240b40301400040d05100c10480b240115650b0402000c02c3d115090280c2c8000391441c030301010100601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 511895503 1250 511894253 511894277
    0x3010209030c0f0d080c01060f06090807180207020402030f04020f0d02090a021803121c021213020f1203030402030c01140f09150a050a030c05042105190c0f080607 72
    0x4070150440311003c0354440000126500840e99440090440401755400050414109000900819550b8110404210080000780504080050007500703864241c50410300107451511a680648208400290400d00100602c0b00ca010ba282006024a20844101d01503841c0c0400380455142d00d0103001e584412032001155124582d9401040b14a60521864240030070b0480443d04e007030001401e03084044800170700f14140414012240e03140c1502002c0951900381078140e4080d0280016100d10000c8c01707008641c0c411542c0d40c461480c00000003910b1059600003024009840e41c00c01c9074264040d006000081c4090762103040c0b40001c1e084103840f00d030f0070b018944038691010780041b08005d4000420070340300400241c50740301401c03681055549003540c3c2c2400840040940c0e0440c0601030a002051000b44080800318005a0054002c0d00c401807c1d2042400c0152501d901144900c3c9080c0300e20308a0018002482c90b01020707110020b044030041c070b603111f0019035565030440300000010340c1c045644c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 511896753 1250 511895503 511895509
    0x41d06130b180405010f0c11010f05060a03020105220b0c060f1b180d2d021302070507030c0e07080711070905040201051e0406030e030405131e0204140f03010209030c 73
    0x15080f60150000040c65001c150b92041200d00d01100040880c0310400f060f03443c443e0074082d02e986580210000c0c801420000f000c0343d105a8280002414418040303503904401480110b8540c280035411407180185595041002c03450b03004001c0044140940b800007440413903500d0550380180f1a2441c206401e20301000317109225080000c0002e225044000182c120382d8070344040c56078403405034034410b8428000d6251103900558410403184400e419400c14000f40e500d02211124070f01082d4005684c1d16541c2c83c0507410071202c0c0d003000704800c01304d41c5c0110301440c414400c140b01e080b8030340f12144180c880304400d031445000300c0b0900d15a544004810f0001c2c2c0c2c902d4004542192040c1049800e00d40030071408010391980300131015201502107010001c8682c1f41c0a070300c2c03200180300701461900d400e010100e151004403110415103662610040030981180b8000e0b420160301a100c11525591a480030303048511528404030f105040c2e044200040d841d043c1700321140c202c0c2c010018144100e00b0b60078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 511898003 1250 511896753 511896799
    0x3021308120f2d0a030e010504110103020d0213030507060929090a0504240f0501050421051006150503010b0307110f0a05010e061b0307030908041d06130b 68
    0x1195202e288140c0640a442510b0f0035120701a142c1d212629543c1c0940024100c4224a448a4560b07040c6001c7c0700204d075044550501407072080c0f8000d41da0b03c1000740c0000207445011544003803094103050001c00d010011603140305440c3c81c0d83e5240c1d0001d98511101c0c884540c0d0803c4890300800e00c078418909100c440c0010070400310302404004c80d00c3d035500001000c40308148082082c0b8800c130245401c1008081940801030018208100d01c84d5040c074000030298002d902138500e072907120391501d000088a10300f04040d890b40c0300d000c880680c845140b808010700400d219612889080000ea40742150080007070364161104608080d055075611031085a039006019451003190003030350300725a1900c805210403520203001d40300104040c400b44246503d0070000070b2041c0304446418400c454469030a0044a40141007450086030a051a05021900e803065030721800c100504004a1002400d00d911418416141203030403440b800701c620903480c290b8503299070b07456004402c80c60411010ba60561 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 511899253 1250 511898003 511898017
    0x20901090b090a030f110901051e010806041508030a0e1f0807030917040e0c0906041e0e0a0c020f0a080a0c14030a0806090c1206100c0c0603021308120f 67
    0x700d9102e00036681c0e142c17154080408002600c60b0301da4145418410300f800e0403214010402514628007085d286aa480e02c40c50305604010b04201104001c80d420317030707169040341607041017140816552640c2d03840000d41d280d200035010008507008400000151070000302920000c4c854104050100084c1e8404841d51003006246100f031641c3c4040800210301180603a03031400d64910308035581c0720300340504c01c80c6030a0002c041d00c0c1c130107104100322101904d410003a1004c0792542d00550303810121149045d01c00d95180e40126005c0c0070840108158529107800c0006800700d01e4090300d0a0300b4401d43e0450701c800c4400005401058100080c2952a1080c00c52207201030086814500c50055080c040f82980d10003215240001d00c00400d025880c500900c4003508141c2041da00b620f000e01c0302c0045205910b00030b01c0b6910810584140103280d40c0980e00f0310300c0c104c0c0d000812001468079100060029041039a8102042c1038a110110f4400350001c3c1070001000b00740e0358039081c0b245010101406a100720 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 511900503 1250 511899253 511899259
    0x12030406020c07031b0b030c09063016050a020a1212110315010c0c120f0f0c060908121819030609170703080a050c09100c060f020901090b09 62
    0x200700030b48204240100c1024621030040c2c40105c03084000c6480c4000c0c80782d0403a10b0342d50000c00c00c3c800780e214180308a400d03c0f0400d07a4481d0b03c542228840b6142c3c8402c51246020034207800031000503120809400c248a4242c116414031314490325407044640b40581d2980c0405a4407080c0a1004103107141301c200e603981400d1503c2d0b6000304204c60341d502a00c180a66464051502009100c980c01e180c1d034511010300020318100b06003c45985440b4807066070303441840103500c40750f18004240044500c04480b010303000324100c0c50298851500c460055100d01c280e100140030000c4c00b1802c0c1070042000d004c940c80e00380800c0c0c100131810192100702c1d0404910380d41d11001d00600c0c11205074442180c0c0c00194010345d0005203000c03080c14442640388610444400401e030030040c4000003500840303040c1c2c1003100d03c40006615554448442d206100305801a6440040a21722100c203da101102c00c0300c140c4141801e21440340e103d0044020707406100c1c2c501d4003180090405001d03441d9188081c000c883c1e001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 511901753 1250 511900503 511900507
    0x3181606121a0d06050a0605031612060b06070b090606330408010501030b0f0a02070b0c070303140c070519030f0c0c090203070f170f06040b03101a0307171203040602 73
    0x4200010094066114126507490321740080204408240c4164801040c0643c00340422301000400d40070000c8060081200c0301c411440c1c19010301c481039000000c00780000d40802d582c0c079000c0c2086800c80f401140c03040f6240c072a039400941c480c18402c001d9000401e20700d0804100c00c060a0451071100c00c200304052a0303401c180000134015070700340681802035002c0d01c1840703c181045507c09640c000004c01b0300c84202d00421420000501001429620031120320038a525030459103804c401400c0b5003144150440307100810300070300032810030003412802d20810449842c0c44071885080c10541c400d88000e8040340e4010018051503014400400740c0d40e2054041c003400b5922803400b60100d0704241e0381c410001c1c0d00d01c2000041c6581000484c403102a501440c4086440c080040c0c00305014000c20250069403601d4142c045520104448030304c943c0751480c10300001101480005a441c20003459a102e032140d4030001500b0007140c9001c0f128940090098a04040c1561080b011075001600c1100c40c0399007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 511903003 1250 511901753 511901801
    0x40903050d1404020306100b030a0e0309150a120b0906010e0303070f0501060f0801140105041109030304090b150c1002030c0702090702060702071e2105030318160612 73
    0x9445950441c41c240c2d6000c04607414140181440d2040003014440c140320100814081041c522054035408845481c000c10000701d0002800d045028820040740c101e000302c161518003800c484080e01c2100302a566844110000310b02e20025513003070030324858100107400041520b031751140c80d180e20441005822a4039040c0c160b0b41d05080d001c0d54440035501d80e5502e401c144195140721b8002001010032800074000101e40c2240300c49420350602c40d01e0b20480c2d85241d4041041000d10585010a20040a40b5102c0c0c0c0c1e00c1c0c29140141c0405800184100841100520f154010302d0075940c1c640d1611008003103040494a06000a620207410f0f9030b442c00e81070107040c0042c1c0d20040d030740b4410103555002d030610b4103110344080d1810002c2c0d00091800da841012800803101c011007602c007101c20102c202c4213040c103026408840440341c00c40142c01030100004008501028082c0e100150400200304c900070704111254890707890540c040c50001403441c080030903150100b60061000303007030400722501441003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 511904253 1250 511903003 511903027
    0x4050f010e190e07051c050601090b041706010b0a0804080306011701060309020102010b040e120d0f0c0f0e030319050306210a02040509060106050304080c0c04060314010506011d04090305 82
    0x2c2000c81c9052039507002c40280f06201c00d43c1d0721140c0142c000c2c14401d09115610306034400040105003082d03101d5a6070000502c0300da208451490007032150101280c0c0e01c5441d0010701b00d000c080885560028850940005818031002c2d003110544880c1e0380e90b00d100d580f95556400c060b617001a00590400480b1100c0c850000035008455008000c1a1000140100548006401d613460204241e12803440e0002c14652290702182d840c0141000220541c1d44003050b202020080c0b100000b0401594584000701201580154181027140c501d500e4807111500c106040640e0ba1003242c0d071030852030003038840b50b00e1082c2c007402c0a10341015000f040b10010090f90b21820920030b60030340c480c59240c1d002101c3e40003981040e205d526041503185014042540c1080b0b0003911904c4064402400340c98005580144d81506006a01100c0f10007041131250964034144401098a0001001d44a52a000106820f58000d45c24401200d41c00180e02a0f8006407004200062440100c00d40c2807010410001c20140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 511905503 1250 511904253 511904269
    0xd0603050106090b040b0103090c05060a050c0a0b1f1d0403020a020d120e060c0a0318120b0406060605030f011403070b030f0f131e030c080c060702011a0604050f010e 73
    0x110f4281c80c0011040810001c000c151410509054145845d004002c00880d443c03c04140030b640f0190b400580d0341000340c0048079036100c1e80044800b14001c0007000400c1240485120b4012150b00401044203003550b0081404071040d440350803800c540a46000c0c03940c402c0c90f084e103540305010380165111240940c0119101c4001d04104603010320b00341907500b10f40e54004642100c0390300103031440360031b1000d12544180e0300d82010f03d0103020b01c495045280007410320191240040c080d80c1032118094600c0d8500300499400c15101201d1082c1007910100340c0078070410590348280010001e01c0c0c1e590b4030304903180c14000c80c1c0401c5190035000d0014040360242a04006501030f8181103480c112601e0903039000354601801030403550180e171041103000041901d124014070410034103511402c0d0b0707074203500e0140e0f03950b1120f880c000d0010034003050b05041071f030300800c0142c0b25405070340091042420041141c4000400c00c403d15910002c1403200348902e0a000342d4001c0c400390181016451408046c000503000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 511906753 1250 511905503 511905509
    0xe03010207030801060206010b040e150a150201020c06070503070e0f190e04020411041d0a14040515010618090e030f4e060d061a0a0f06050406050d0603050106 70
    0x3c0740507840100a02a41042810300502d45500400c3c1030604141d0345000062010340704880b200c40851000c00b9030768501c440800208440c3d013031042040814400030b8081e400924015089005003400140c060740140101d900ca011907584178102c06048008006404480c0000305400c02d0022003241c03101304442c0c880d6005003282e59020750741da284c01e04c1000199524010031602148050004005134213455000401d00c0e8040c4041d0305456651488041c0100701c01c0c0c8400c022001d0b841c0602060200214001042500002011050383c0e00e43d230094800c510525804150800c2a0100b0032030602a548404a01c1d40c1c5007040d64139180706001c1e90b81903500812400e1048000b6500b00c81d4007054041c0341682190b9400494811820f004030700d2003030121410580d5143c001071400080c2c02556418001141c0030b5101208024081865008860042150303c0540c00fa000c00300b000300c2c4c04003c0900c04030403501d0390380e01d07949003c0c107242c0212250380044103035008aa45554000c000118280540d10103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 511908003 1250 511906753 511906757
    0x50123030a06081e070b03090f06101d0702030f0c0c091501081b0403030c0312060618080f120a020f0604080a030c1110050910060902120105030303150f010e0301020703 74
    0x7800d4107166140d800c00c8003c0c04084d500c45500300101d43c1c110b10100b00801112819000d0648035541e9030506030808000c407038119210301030b200810103800f0a200c9000195800750120f02c511030380d400502035880340242d0f4800090303071040c0701d8410280c0441d40203202c00081c0d40203441d031281540012514041c01135811070f10a01c5840c844110551b8482c100d15845001094002007688625144007050320550001a00308541c040c4504140340c00303001e200c040c02c602d0590420a45c3e03518603004000044e046c503481d5000f02c00c05070014440d100041c11406030584d41000d0245d410000c04000e204e60700180d0f4800075801094101000808140f0616204074000e540156650f807821600400322a14505d0401c1032005041d80281e00180028040b03081441404c0c0014031500c40070300342440c0100d1440458640e60818070041080340309078029020b050340740030b8843c0301c690b210020103860303002c103c82454a000450021021501e0400305d207a20100060506d40d2602404d200800d0036a0710040041e40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 511909253 1250 511908003 511908011
    0x20f07060501080f1902092d070e0a0b0301140d0c1e0e09030d2a0207030209010e0f0406020a0309060203090307020a050a180f0605041e0b090103020a050123030a 71
    0x40100e090152884241e643d034040d040303d241c01005001720b00a10320000e0f000e140307081c002800b64141007183c805501c0f1b130103140409410707404604544c42d15080b00e02c0c400040740900c17407a5890a250b400c0b1801d4171100c900060440e804c00c00c24007520810b90011a82c000600309004011039000d8480001070135644401814000094411b90000c1c00558442d1907045125820000b800801000355881c05096030070100b0750b54500c841c404010306c2808040c03400e6a84404407014901d400181e0101113134420340b41c40215a0303803050329030482c0310304546211041400400260010700380f64000c5c49054400d050000e1145e4541d12104200d8100b00c0f4108413960000811a041d0701c2d191000340c0c02403d049a200140600302840342c504100c0039204400c13800d403204848000c40d49207410050151034080c00400c405c001c5149410302540e22403200100c5146041484070442c00c00500f81030590350050f111800041c17501004480100000300c6003c00c01443d0406060100d000b100110300518a02d0b102103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 511910503 1250 511909253 511909259
    0x140607050a0822051008040b060118060e0a08030301140d03050c07030b06041503230c10080709120314030c070c0305030a0f0314010e040c03050f011b1d060d020f07060501 75
    0x20340002250403051045c4102000810300951148030150f0040c2d0101c20200a40c840d0001031f03400d4081e01e0300101058007120008030302c595201d440c081ca401d4044440401580da54078075a070703c070b100a000e0004411000c0c0703202c49103801c00c40c1d590002280700b8503090f0300d0800802c8060b418040c0d10f410464a0304044d4050152a2500e40a000c50101403d1024400c59207150b0300c0b01c0210400700011103078441c0200750060480c03030134042d18411000107020031400c2402050020481b40e0101c90510220303000100c086100b5424030352100c000d40d8903440c1c11500807800c071090f24030703a0401010011000020840f1714001070103824150010742c4684025178441a460201911500141103030b8010185004400403250902ca44000d0459000d02c5540409840350f05007000040c0f056000980a840303070900b42e840c0494158841e812807080a1421100c1c0c103480035040380d2908400407600f0a584071034800b4141c40c5480390040ca0324084564005140c050300101d070591035040007000742e6000356984010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 511911753 1250 511910503 511910557
    0x703170705010e010c120b030c011409060d1d0f030301061817010e0105090102130902030901091a010501080c0f030a0f1b18050f0a14040b0a2303030301140607050a08 73
    0x2e80e501b00740240061041c0c25007140426641c50610b41c0d441e04000700284058a0141440c044442c903400242615940e8800509050b001d801c0742245004180000e00129072003c902180000810b0b02e010082c40c40c0d64a080c070700729a080400c66000084810302d0400045503078401c041c071000c01302800000704183d0702e954940713421100004c10103801d60b40100031810410550603420415505030000050312a1141d20110380101042d4038000c0601c0b50b00301f0342c910041420032080f41260001da035034920991382e41c403404c031060141d00122050080184080750f9003214a40040380c00b1549005e002818072842407041e01c1d042c0034807081002180510940c0c1214410034145180500020740710000b410900c1400f203504a201d81c031482c5085110880c500340503030780d01d400084082500030030420440d034844085202d002081045000c402c00390062540d43c42c1408001e1324103c44040d042445850030030000e200440e8009001150913010f040d0f06480001d10407800b40c05841000d00100340129402c09003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 511913003 1250 511911753 511911767
    0x2090d0312060e090a0f110a0303052709060907031419050109050705040b070812040b16210c020705030d09150903021c030e1509011d030703170705010e010c 69
    0x2c000d43c103040d01e000700b081590b40007500604403a840210301c1c102103500d040007c003444014002ca94050740c0028000b092582c0100540000c40340c0c04c0d80035a40b443c100817011400d48030030741c00a03001408080000c15a161030240282c0c00f13041c030b08011035820308824034002800d200700e0f402e03441100081d100f94223100143c42050f0240440356801c001d18207080030060454040c0d8811540c2d03500e80054040100640e40c8141c400c0184a0390003840c0074107040c0b505170340d41502240c004145402c00d101e62282244a05141121b01d103801c201000d0030851104010003400c9000c90140c1507104084c000905503c0403c0b00d4400000556100754085041c0443c89004042810f242000c00c10b207003070140050b0784c1d41158440303107009007110027041c1500c900d01590700f01100107141c2c1c1d001900c2d81d07040c03100702084001481c00070400d0ba211200c2222603201950042e0409405c3c54259001500510001e981c3d0b02040e04000401c0300d0342c90609002d0768a49003034600c480d43e2030010780d450741d0b00c1d80b11860b00054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 511914253 1250 511913003 511913009
    0x40905061e0105150304141006061209020a0308031023181608060f0d120e0d0507050d0501090f30210e07060c0b06030a02130c020102090d031206 64
    0x507034070156515080c00980d50b403051600e4802444400404641080b034601032501d034071805103040d505083e60008060005060a2080801060840d07030000031048961082c46403580d40184134031016400c503103c1d1400c0e42c1004011690740b80c12950046a4021100c80070b2880324080c1d0030300c0e0b0803035110000b0710100d942803425400e60301c400700060201c003403983c4e1604074081c54a07140c1207140da034841000a000c2c0020022440e044005803400300306105048540400d2644a5202e003c0740d481c12905100f080c400202c0b015003907805c4114103020706d29100e625114514041c0d0000b042d00701550701d4011348420200c0382111005008140e040c0540e4603500d0510080742001c1004d210380301026000b0f403100c0180d9010a00600031018050341c0c0da00aa807012400d084403804465481e41c8075a0064401c40400c0300075182441c500c0000b4145140001d5400c800513405468290841007018075040640748034215501555000d120440045c3c440d042039019640c06039440816008a00309080202c1d10260 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 511915503 1250 511914253 511914301
    0x41206060b030603060712060f08060405060903030c0a140702191419050d03020a20030111090d0f032705090906040c12020402040e161701030c06030e030904090506 72
    0x4000c2003e20ba402040300b40c0c1c003050a050080c20320940c840708200911480e046002d14120031f2034041024440050f045e40300b240700348226007003500e421607001d6036030104560345000c800d810407220400601c0f0701000407044158045060621000d43c2c001200c0f10340040d040e0b0407c046c4840304000c0691140c070509180201942e19201503441800d0503040ca107418003e0ba402080400c400004251003003201611050700154580359070302e4481300b440d00718056504890b00c00c6d800d180b2030400f02917900c4120b982e442001044812a4072980e40e50f50000304801405034148140344508501c000000a10800d2b0f048140719112406418502041062b4901600560701c0760b00142c10000064901d5000206658110f101ca680e01507a070720000d8068450b64001482101e140b0040c001052070790350500b0320300103075034036012003d031504803c10345c42d44802d100207410b82d0080842004518000d5100360707141401842580c0c6403041c910b001c9410768101000444986e44400c041003402c4000965680f9120f0400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 511916753 1250 511915503 511915507
    0x14090a260f0307020f0a26040503060708101505310e061314100b180405060a08010911040b030c0108010b030c090a03141b030a060c0201060b041206060b 67
    0x280c82a614000c0380008011450000302040e9030030300820900501d824a20100c0e03180b203ea81ca010f004202a55017990340381c00407801c0d2100140518800e48081d200040c0c0104a0340d5a600012203e03144058048888036a9000c00032130700700c4002d0864140c144040c1c403400d03070360241c074051550780616903c5240410414650400040b03100940014112140305031400320a441d040001100e12031030030340301056140303000745204c0e042502880e500e1188240007e06040d00307130380b2a0075031120f10900101c40d02d0104542d0019402d894103a0005802002c00392a040c42161034030602401c55060110503608620f9002396901c2a00e4a03009020500c03d054018086c038000c07510010740810410302901c40c55010101c00962002c21000a03106001001040b40804a69070304141080401c0c000780b62020340640344d089c04140f52415481d820803039000c0c0c0181210001900ea0100819981034840c0465480740d800060140445010b030015002d82c5141e003040800300c1ca40031040700c0065014402e80e0340d007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 511918003 1250 511916753 511916813
    0x1030b010f0f031a152e0f080703050415110c061b0a050d020708070c03051219051b1c02010b0a030206030708040602130e220210030e0114090a 63
    0x50b041c5030480e13405019013054120386038861038403141030100c85480d820540c4e08404038242c0c4c4ca40d045910700c0c0c000302c0005c000c400c02e0392042200d04a080a500301c0224582d400072030140c501c26031041e540301c0d00560b1078002100c43c8202c49000d6604521251169100c00b181c2a26288002d1000c42d800125210280c40380c40004000740c0303505e00030707008680248000850300344980c8142e80c044400c03c6511403440f55840915161491100810b03010548080c480c0c9582d451031003400e20308817000100020b2110b4807442041800f04c840b036000c6c01001400140301f031405030200c030341004501d035502e9240c454410074a6141c0c07402802c56640c100098454119040708201603260070003141e421901c2458100380e0740d0f40c0e0382091800380c49140c054a2400d103800700000380880640c4034032401001c1008030b50213107159981c6003101c464103c020107540b000c200815940414002d9010404c4521070800110301b0b05880e00c42010100000c51b2071701c125401c030b8928903040100583d913140d88851203101942050403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 511919253 1250 511918003 511918013
    0xe070312051b1c090b09030309040911181506040b120c04170a0b0f0609071b0501091514090a170f030a1512030503040204020d090b01030b010f0f03 65
    0x44100d100744840024003070b1548112140700c060b504150421244001010340c208264464070311162000101400c2d4080341d060040011a100c40600800031810520284100030041401050032904003c4549800d121a21200d41c1c0d0ba0555103104c601640b03d2820358a04405011701c407540030b206680800c070500001210b04140d0b015200b820bc020100c541d64205942400c1c41150400c4400e102501d6401001c5200003a0f5800c40750703c40d038030192180c3c580c41611007400f401950095442a80036000410141c89010103440780082c070512040c0d00a426180c3e01c1c01c4a8007500185c0365511400c161582920031030103104c1101d034105203480401d00e4100360941d03e890100d1002001c140311407005601e001740d0038059800314201650555628108008103000074038207801240d6001240040008014180180240c00d20350541c441510356500c136400c0000950003941d65088180da10400440803461030002c0364060b5120300b9501c0181c2d410103080006000050b0f00495040184000501c0051 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 511920503 1250 511919253 511919273
    0xc020703060b030f03070c05010e010f0518131e0b190605070303141510020d050f03041502030103030809070905040807060f0b04020d02090a05040209060f0a03090f0f0302010e0703 79
    0x280d0070640005508642d00c0001c0d0604040d0481a01036120100c1c55006115044c1c4412003160317000d80791641c5d404000f8005652800c0241c44150100f14148240e846010a065402c0e90000000302620740c9000c41d0a20a0102d07a8061900121741d440c61040e00a40c43c40c0744560800100211150781c0003144d41501e580c4904154010b200800c4008216101014040c2d0001d5003500169085600c0503d0081002c0340c551b6070881800c0d00c10b00d60f00c96aa03002074004100a02c441595644803450f05000ca510007400b644040d008482142c44107041583c040314030710180d13004c1c41c4660307124881c0742464400c07030340741110980004034464074007024080000d14200232280d00ca6400800800c0c0e800098001900030700300416095000350000446480d1000341e0350080040c40002c8030410601c03912002444100d000310724405400010800520004221190141503481c00600c0c0100301c2c01140c0d910124499000d013400c03207840341c00602d04800c154080c050410001007041c01000e800d440e5407100c240003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 511921753 1250 511920503 511920509
    0x5040f020607030309060204061d2407110301050106021501080f071703090306090607020f01050f1b1912050f0906040204051f0b03011401110d0815210c040c0207 71
    0x1e4600019003104250098110343c03111508020f085480740d9403900040c01c0b141200440d000690b0f444c01842401d4a03144002c09011a10a0310040c200c3c044410500c2d20340d8001041920490383c42804d0340e00544c0c0034022203000c2c1130b281e030103040b26005d0104c203402e40c0e50042e00002c01603000307074510b006840c2c0e00050850032200400000c0d0402c5440e844441e0031449141e000c2d507007502a01081140b1039000140c00c1d03001c0c00c0560b0840b8815806400400c0c00c0320010345124583d19004004518a80c443d85048601c8414242e110f61a20901450000180d14520131100104056100030210343c1c809118040c0c5c0500131215070141032504400c65900c07030100400082c0b240c1c0e036400101d048080e080741c030f005400b11840024428181c403040c2c821040e030000d1045601d40e50b00446000c441c0e500c600e000f1001113500c1d50040520300322600042e01d0a01008141103a540c1802c0c407002504d581d440032598000500405c0b0250012401c10301d24100303c480700c22980101d00349440c08a440364006103030412 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 511923003 1250 511921753 511921759
    0x403030e100309020916021b181b0d0504021c111e0a0b0c06011212081504050408070c090203010b0702190e04050f060f190506030a080a1101050a05040f02 68
    0x101c1000890030340c020312625030081d421010600170040310540040404030804225022504c042c000e5000745030307039200481000340d0801a42803038841541c0c04078501d65001306074041c0d51003891009001c6a8000d4000c0c00f180c13104e0319182c00520080d030610130300403e06003184509551026909490302c2050400c000c450500650046129000c0441d0044842907440d000034220741c00b80e40c0c1c0d226415a650001100600c0f42d00501000049149107514212051544903005207003030100c007541900c00320402861084081004207102c9a02d42e51403080c2403042d031080c00400d0b1607042e0790030110300c0f0b45056080504628410001444044800303416102040d604491800ba800d800081c4603020380c00380e61109410041c080c06010802c6808590311b200f0101c81422514280d9601003100c4440a0585800e12501d4003142e0025021409805c0310358040400307421558406440d94070038446610007201c950000b8203000091034807070002c0c0506a001710b92544203114604007078a5070707000700104a100030701c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 511924253 1250 511923003 511923019
    0x311011d0f0301060f0807090e0c03060c220f15031e0213030c0b071a06060a032301030803100e04020f01052d09040f090f02091302040905100b0102030403030e 70
    0x4040d079000d4121a0150a991040311181d543e83c0da4170a079101014021508d10504045420610680001e60000341802c0200203051940b18290748000c03992003151640750104480130640741c0c40300c901c2880c034000c10148841c0084289081c50f040707213940c9038480a008140c200203c540100300ba9050800d42c000213140b0069440e0003c00039110341a10b00d90005080d90441d09000a08503540005402002d004800c44241429608e48440d6001800c0f1000e50b4071120910090740728501c258041d50742c2001003039007245100d40b02c100d5494106800d0740100c1c0c40c0e180010401a0300030a90340a9001080c45000c9220241441c0e40019040803102c1032190400c02c0100705c144805010b40d01d642c02d070010403004940a03120104040a06600003104140030742e09041091224060b9403080107250303500b102c40340c0140d0141c1d5003008591840034000500d590f44441807080961381750f1050070b0304a403041c0020856142481500000c0e10980c0500324150b410034842080441c0d080b003c0324483c0c0c901210488 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 511925503 1250 511924253 511924279
    0x90a120203070519110316090f0603061e0c020109080f030702071505071a0103020108130201020319050c010b03060106090b0c100f02070501050a020c0304030803040f14070311011d 79
    0x1d10394011003070080c280c0e2240010b10f6941010300c60090b0880d83c01500f840c00744c2c2042c80c050680d6201c014000356010300c1c1c0f18004100304200d550041d10b50310076040c000f0440e00e40c0c03a12141c0c15554001c22080c031401207150042141c0e8421301c01e08800c0d40c0b103400240305020013900c4030750080c000c0b401c188005a40006c0060200e41c42884050054002801403c000300311064005115807c01c11f4100c403420340004016010385003c148143c1202d41c141e40c1c5003125a00c41640d10414032040720124194401030140c0059015003d86c5103c40c401d05a4603280c49148441c50f04d820344032802c00d080e009400800060084940c00702d100400d450b48450550384d00d0201c9076000c3c4c03400f8038400ca045c001c00d241040c814030883d142e400401d58280144024005619540e84031000c9100d102015407507a801000200b0018880320051644103003d595403500c00692078407904000e502038980c01c207036904007440910404c0303510600280d00c2c000c2840c100b42c0c02500c914403100b0701d4a0440209102d6000c210050b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 511926753 1250 511925503 511925507
    0xa03120815130b0a1502060103030215190f1401290901020a120e0303070b0a0b041104060309081b01051b03090d110307020415050a091a2404030809090a0203090a12 72
    0x4030300a0500035484448400c51200c007c1d102c01c030a000480c0103004404002c45490114072545001d4400c0340802e603c000c1d800c03d8454000c0414034000c21034103880b644510416001d8400b001e00070300039001841c0320b8220030190084003800d5289102c50714081400007101d00d03680043c2d002071031944886c1c00049045048826508050702101d010342c90701c400a000820000f1002c0441e000b01000d500c2844140c9640040206542c001c9a40c003285100070300040080f28403a400200c001070181c00c0c00c41c90100c000300d010300000000054003482c7c2c1e4550f820301032503031000342200c2000b20400c18114211308190106c69207407080b0a5844082149034074894048e40420303c11201c04c182d00800400001d00c1040a02102c07541c00e00c40d8901c512101c080002d03490749036009921a400e1070340380940d002501c2204102d000c28030628001c1000d80301402d0f281544074118003e0010318000c4080c1038880c0d107420100294414010b240c4040d481c01030080c40300000c800110613803031b590b004082c0301518000040c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 511928003 1250 511926753 511926769
    0x607030e0f011a010e0108040308040620130e090d05030c091305090610150206190603080d0b030d05160f06110d0608060a02070c180603020a03120815130b 68
    0x401d0709079502e411019000780150070f0b6010088042038950110110003440152102001102c0240108500c500082c001850b95031003100400304106054440c40c0031221100384039000400c01103a1070b0201002440205030000203554400481001003442070200d030760003002408050101070360341401007191004d40e030f01d1814942486030304400400040c03a04c01718099855609840ea10587c030020a804a220089945c440312292503580040c01a905e5007103010346181480750454014550783d100200003d01041d0042c076800182400c00304410040d08109401c10786080608d5080c40010000441010400c18419100075004050821302000300e08101001d0080e030a40880e05000005c1d51004480c01940a00156203803a01101c00c90382d2540c501c10128450442d001e8010201c10500300484602e20840010354010580086161562a80401c00f40c14190308201d82e18880b0b10011410154402c0c01b042d40640d546840c00002010344000c213800401c50b80e0040300c00758980c040001144c0710000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 511929253 1250 511928003 511928023
    0x30414010905100c0b07020106061d0a0308070b150d1e03030f02041203021002210709050402070305090925030216050601030c0810020702090606092205060a05060c0607030e 76
    0x210003d03030f074528000c0042e48500400c03070b4011081d0700822000c1d0300c14824402600c01c2500c81500320009500d0420380410f91030412a40068203190201c0000d080c0d1000e03000907442002000d81038200300000300c0d000641200702074000e1074400c1d08080802e481c80c47d00969030001d5100304410340d1030350a0450140541e441030180d121300010f00018810070f540c5100489501980c243c684120000510074180d00c280f6014414650154104200c0c6072288078002d03410074040c5c00c0c0750310311640d90380c0401c02740d801a0720180c02151000c40c0b55111410003c00c07003a8030000b5002c004da4500b00c5802a001c014480002500802d94041022410000c2401c6001c4038aa0010111403031903039a032a007a84044010f000700310b00c40c0036180c00c40c8035490440c02601d05655000303100c000c0c1d0303130743c2d42003400000d0b00040c9032241d01c00c074100e403c2800702e141800347c10540380000c03001103000d28142c0c3c240b000c480e11582c00b00e40a03c170b0420924000c83e1001ca280f9820900600c0e002c80d403111940c01c17091805014403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 511930503 1250 511929253 511929259
    0xd05011407050910020615100516050307060b0306040b011707031e03090f180203060112050f060f0d081c020702120d09120506070f050d0e03071a09030414010905 71
    0x8240510190050040c11090314200c903904c640001c00d000483e21020265020030940e80c480300050041e00d040840340c8040500b41c50860308081c4510240d88030800140030a5499800005125050010b5405030901c1490250010842810a0343d100315800005101d20300e4100010ba88403405070f41e09100403001103400280040038550084104089d15a80703401c224080340300c84000007200d012030001c040c00c4030101241c0340d802c0c0914020841c06540024001410030401c80b04070228000d0034481d2038004c8244004280c4246441010b01c1901664580103038406c420b00003101c0300140340c0302c0855003100c031900031140f20541c040003510081e0081280083d4081d544801c01d0790090400101000c0509243da6028000b69548600d840ea41382040c00150054100c4000034010340d00824602e1741220ba240b400d00c0c540700001000f08212850740c51064100c0c1c10024030030041c4032842440340110750380340f02c19417546c2c248a516a0750380c3c8150b103e1100c0d80c84410102c10310740e80c010003168004040c05 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 511931753 1250 511930503 511930541
    0x60d031d030a03020f48211b030703031d040618060b040501050906130f090209031c080112030207081002030910050f01170307050709020307021c020304050d0501 71
    0xb501c2c3c06500c1d00c1c8001c0408902c6d208000e0f00307115007000300c4080500b40c1c099030390181d0307541c1c0340400244075844040c4004404141e9045410b8060b105d0100480b058040402003040042041d0200c03030900d0300601c0030044468a9042004481d540031841d041101d5140c1004110310541002c80811280c0c1d080d901c60344107140c4000091040f042c00c04080e2440c0c5030b11420010b254894580f000d481c00b45010725800150244019102c4c3e090070700c000c004181d050b00c803603401c9a64648071200c07214103e421103100c1c1600400c0a10881c10200010150b000e0f440c10a01c603039a5882c500240f83c00c2c070510a211040c804820800300740345c003c0c0b00c1680a06460301c155808005c5580c40c0308040e500540301c040f414071404040511044051080b54068058401c0840c03072079180078054190203c1c00b15844945000410801d8002034003044a00c4c01000f40c2c3d080583c8034600400c010342407403980b2424000c0d600b8414100182d07142e01000300d60541c2c10407201d02c08030700b4050500f2401070035a038121104c03005903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 511933003 1250 511931753 511931773
    0x609050a050423060103060c2c0f040b100c030c050312060f040c09050123070c06270905070e1008060306010609080a0f05340905060d031d03 62
    0x2140d00000c1c460b034000c2c001c400c0382e0035641031001d0404081c0c18124050744c1022006000252841d0030140c06800709180042c841e40610740a882d81c0000c1001c4d44400d50f085c0d414a103084c0c1070681e0320355401d480880e4100300d0510540041141c114007405880700b0046400c0d44c1c141014040c68220241c40d030030604694a070100442d1180141c1803d8849034410207112500001610b098020b00c88102015030b12614035901c1d00c001074400e0010000700481c02c00e6003d100030300e01c810207005001500d00515511030140d1415901400d01021100c107016804a48080f02040d00400c0c0c01d4003007229a038420000c0c482c0c1c0e80000840f4030712003200c0101e42c044110740f01480354582c0080818082c00d4111305503005641e03500d40665070403a5038411b505180d0810760486022600800703c00116a0103103003502d41244100210240034410722014400d15282031010000300c0c065118581c010304401b036030400035420510009444845c000c10024200281410100041d032544980ca020350400507013150110b0300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 511934253 1250 511933003 511933021
    0x8011d0307060f0227040609020306010203270d031e0203270d080a0f1e0f08130c060203070c05010203040e15030f1906180807200604090f0f0506090105040b04060905 73
    0x10444005d58461400c0c481c012a645405100b2a400f604050b0015840d1001090964511000c041c8400d80c003035500144543c05512491250060140f10307030b0b241104580d103084080b05108041d44a402150300900411422030130300740e4802400740401c0d00c500b443d2104600014403608030305400411000c0c010071040c072220740208050b0040311254031511031a40700c10700701030030b2603075041c00702070004078804a110882401000856008642c0d4400d91310040d41c1522031300e9242c600d07030b805a401603000040150070f001f007e400700c9020304400d1001d10302d05450070212705e202c80000342641d0103008441e10350320314990b0100b040400c080e60920075260b080341a0b000301e00c14440c003040190348007401d001700419108088030001c3c103400d6102d181581806503588840105441d50210160001d006400300c400a030342d8840540024042c02e040490742c0311744a203003c02503540d8486091b41a60801051102655031240f001d415110140d50006801040d60000380181c055644030b0601070785854240034203a4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 511935503 1250 511934253 511934317
    0x150d260f040602010f090c30140706090803031b0c010e032703060705030c04120b0601111c030b0109030f080705070f060c0305030a091b08011d0307060f02 68
    0x84541d0001c02c104900c0e0000b110648500d1b820040c51180341c0c010910035041e4403001440c00d072642410140303041d04420424480800440c2d03054440c0c0440c50100b590303098081020300060000c030b01c2c0c800041e40c41c000d4030030740d20700000d01200402040084604c0b00700302c1a03c142c036009031144009110788240906000e44a40c454020004040400c040d41001800c00180b00d021601c0050028002540c9146044606070006040c0c0d01112070100000140c00101d00711607802180035041110f020304041001410300420050074640940111039031000e42c002c6822003003900412803d010a410742c00c0d1004803460b006540006008603604220380307080c04069409003804512480440b0390440d202c040448070b2502505c140d5000a40e010440c070000391151012799000748603441d01040f03000c040d6480380080d800d40852030b80042003039102040840d00034000c01c0241d000306404110054101098180c40e4403e559010700010780380d0400c462240040d81c112403440842d14000c5240c101202180117040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 511936753 1250 511935503 511935509
    0x120313061107240311030703051e060f0d0c0807060c0c0807050a030f0f080d0b030106090b180405070b0307050706050c030c0d090510020d06030b150d260f04 69
    0x40e10881c1101801c00d000100b40043d900d00c55200700750f410580580c58140c410b0900b11a08054456203010354000503030000d076015010580300414586032401d00c4a0031000408034501424544c030080c8a45500d035400022403410050380c3c14010313800181814240e00740341c0e61094005106006001403807550210708820f1191240401d12001641d950280350346060034020945e000819100400020b42d007030402c02500f40c4200c1c0e40e44005080c030345411200350804513003040929100c07442c10321140303020701c01c24002c1c0c680080f08001080c02c401c0441d2580001171100705101a00a012409001c0c08005040c01031a5030740540359607150a110007050740d00880d108903006420070010541121581056038414060026001c1c2064118004030001e45203058017542c6601484151003c4007115000414483c849241e02040052440c503060b01c1904000300f1900344400514003c00da9036469099140c0b403580c2040c0b003a6003807420010455012030303144205030140400000c0040440c14004094811 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 511938003 1250 511936753 511936757
    0x60b06130509060409080405061c1e18080306120c0a080c120706021207060b090f10051e061b0a0f0b06062a03040905010308040e0702030f04050f12031306 68
    0x26440f00c20074402958119400208001402c1c40140110700700a00917140d031001c8903003915984880d030301c0c0c1c13001160190b88080c2100c00422002c6c0c1080040d0340034500628002c07519081440603192103100450001410b01032007119428405005400c3c10030058080c1b2100400103541c1030359900070701d0740c0c510039008030a0050350328801c82c4001070000302d40b05080300c03200d402400c1d20383e50340c5c060b2494a41c01001d007111040e41e20f060800080d200ca0114038400c85120380c001125087c0200c10203803005040d070019200304000c1500a980b41c240e40c010010f0407905540c510344500c2d03800d02c1c081158011444014041c03003512001d105003c111110540c10034050308148020b501c81c00300b0710841e4071944c1c0b6840701c907007000c00d400f0500307c104420244110307003a4016a42059100d80003c01611707002c0e17009551560001c1428000c4815114900b078000b0301c8c3e030000b11b00e0032000346190394490181d03104d0365100e0300031914031010344e88520280040812424050301d0703886681a407a4124003d6074010080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 511939253 1250 511938003 511938019
    0x30c0c060709080703150227030106081612020d1e0204050a09080a11030d1a090f040c0b03100b03090109141204031104090501020a0c0b0f0f010501050304060b061305 73
    0x200590003504110b090352040c0d0701402840b41991510340b00c5411380890043c0303090742044207c00803540c0304a8510703500c5001c010010928208400c0509446164010903200c1e000307110801c3d020741c40340280008480410b44800c441746100c0c00012290200ea036006001e80c9420703401e0028580c0c018079030700505403003100e041205480c0d02d14000c003240c95002d0001e0014008200000d0817600500c0c24a40420000007180c0ca000150382602c03094609540600301e2900108420a13402c1c582604203c0e1302a0381104400d03114a0b041d290140b140500741704501d14507038000b02003245074550408100251420214456480c240307015414000c000118090382d02c0301c0300120400886201081c4000c2c1c003030180c040a810681152581c24400702d00f001500c0e8001d9840c050500000d0007800a01186000c0b612500a840c0c01401c00b5030000d54000c00102080d5120300401482040b4003549a065034800e00e4207e4680d0741720b181c014014094003010701e13800000403a602c4494000300142d2025180c2c01c0d10681 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 511940503 1250 511939253 511939261
    0x30e0c0303162d030c15150306050c090a1205010905010c09180e060c0a020c03060403032a0c0b07050909010905090111070c171005010b120105030a050c040218030102030c0c06 77
    0x30800c0c94128009030b06090f6811441c040b921448000c3d2070f10303000d110100c41c00c1a0301c10162044805a40c01180041400340080081c461544980c41e4441e100280d400d150a0b500341c0018000c03002d50103034900c54603550b660070042c44025407040d00c156038050003c21800a5600d0301601c83e610621030004600403000303800780d010b201800390680f0011250000c2495486410313410040340c21260300c0300210b1090400303400d06070b0340c10040580110f00903100002c402c40c03d0a0640100f819911442a12005250207803000c04d620a10b280380d000c2e00400c0d4010103841b40c4204607198412a07104903032103504c03080046803046481d0b01c00703409249050b008000c615a032021116440c05088405082e104c0703106420412050b180202c91207180c00703501558800340320304050600310b440030781242c40c9006011604100074036011810368050a411801080c18512035614242e88040da03c11080c052a00070950807110b005540e4100c198a10080003552207240202c68223060303130000b420304521841250081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 511941753 1250 511940503 511940543
    0x90612140a0b060906040b090f061008070c030f120509250f0b03060a030206280809061f0503030408030c150f070f0c0b090d0909110a030e0c030316 65
    0x385032400d030300490b0303801160f0755030342088000d5100070641c94001d5100c0c0e5405d000c43c2d0f00c550086228a9503408000b0075070030900b041c00580c00c07200c0990340a22200f02e050124107908148420903990340351424400b0040c52050803500c0320440404600414200000e00001c0c81011a186040c2010b50740c1548102082c0c584030b1481401500c01d44074228101c0b24188080c40b462002540c1c4100041c10a44440d590f07540820a0780d03100c0000c500c01e0b0f65541c4c041e8803081841c02c542158611003460020841c0c00c10b5490b1076118000034154641c15035040c00c9075018522500d100a00500d0700600b640c3d2950340d82c064564882c7e00550400a141c0540305100703600b690684040380c0664204003400c210f60740c0708072058541154130811038042c8494180c0c604002034554101900c41c0030048058100a0462403001d004400181c00c241d03000c5081401b0620f98604000c280c03240200b69207004103010945182c20f40c184405441a2600341c0000a0366810f600c01000e00c0b1110780c0d11510210445403204908 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 511943003 1250 511941753 511941763
    0x30a092103110f0d090c12030c05150714160b0c0711040908090613051c0308060909190206090904032706050301050402031e04033c0f0909061214 64
    0x10101000c58103000c0c105000405510020f4911b200300c060714400b68558149a0300c00f83d0001044001450303040b00081000000c0c0120880344030301c807440c1051410401d10280803510500c42d07901c0803050101d501c201ea00141040340302d0090300702180454500b008580d000380e03030b8041c4000342d50598008071010081d040900c01c0c031301c40641020126081c05216420840c2c81c2c1e115604100900580010200c5e0303564030200d88020415911501407a620700e503240c050010800200382602c90a602c10400c18051800320303907480402c01d0400044070f220701e54800540030380130b200400d41c1c00800da00c04100070150414075241a881440b050304801075402002c3d03400d030301524001d2100050052004102e141481d40107507800120600300c9060380b480c00c4400c00002c5070112415400659540c1003070f550940884541e4825038140c2001c01500401c01c500714081d4007030000d00e8800c000100c410010120300ca4138054025050540051204556412140f03c900d81c4c1d0388410b80300d406122040072001400026 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 511944253 1250 511943003 511943017
    0x102010b0d0b060613240311030f010302060a0203040e18010b0316030b1504020d05060112090203060112020f19050307150f0c030e030d03050429010b030a09210311 72
    0x500b07400d05035109024484039801c4003444241c5c44560040105603101120024a0b007010746c01c5600da003000c00b140b030003030a0b81e48640808040d03080c20800e101100d1802c002d1241941d40580d007413555a41800d004030320b103100d6030740300d4182990b1440074002d280e10350458500341c44c5540f50007481380c3c440b6542010f40740c81400007013900100c0510001c0001a045500181c2d00c5032401c030a02148004400115050781e00c10800c10061656503400c001256820a41c22091410804020031800000350302082d502e00c03060080240040440914104640d10241070200041b00603001002d1010215080c1002040601070f452203801003010204000782c800500f83d5000240341e5454400700c1c140403040d03490f0b0b0445c2c0c105404103c8000700740202600c041040010604170355900007070070725290400c4040f0f1000b40000e0f10300b18000301003800c514001d0215080c1954640703064280d03240c65403244e2000034501c10b140140028142070b0f4003480e0748815542d90036000e034291030030300c440c00d07403103606c0074581c0b05001b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 511945503 1250 511944253 511944263
    0x60b03010e010f0b071203200c0609060105010203040b0c03130e040521030f0615040612110403020607082104060b03010b0109080613020406081b01020d05070c090207050312070e0102010b0d 83
    0x4010315000c1b8004000310310f8000c41c9400e0005045d50102e08101d00d00c041481029054031000401e0300d44007800b003088070307444940c000c0a42415410000000d440740300d644100102c06002044424a81c40c05000712a440306681d220380c0714082e070320514080e12610072202600c3c2c50251290034500c01300c03015109000220005039051455031118181128144080c02c010b42221814440340e031030b0384407607000380301a0031076031030700f61112038083c6814003078503004601c1800e0b0038070a20040006840326425a00f0143d03111024585031290300181d100c4031140c103c0d5800c40c02c41d201c0c00344414018a54400c005800c800d900901c2140d2200005445081c558411004c140d031010001880700c0f400c814140452071310062010036066074601d582c92070800414403400a001585000207003d60301000703001c0700a2050b0038000d00b0801c0303a0b250340d82d520902c0e1240300030194001030a401046070030310840d40b113221868407607411030130300d02001801d485e020003406015601e8522414001d141140c40500d0381c0740c0c04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 511946753 1250 511945503 511945507
    0x9090b012106050f0105120c0a3003050406080117070504050a020f0c0c0108280903030e032109030c0316030c02221512020121060b03010e010f0b 64
    0x24064920078880340755941400354060326100025855009003802460604501c007050750401d010024141000180d054642e8040d940e8981580c460071440340c2103c0310f280078104807501e440d00f66650b075903000c101000d203810442500c02c205a0888060300594520b595050101c0c0e0302d45c4a2124503001c810352283e91540802003c0110389425004181c0c003450410003d03061030003140441001c1d421021007216190070501d60300081e540e1085096a000c04210181c260303103010400c2040d40b040090001809103500d44107aa424107000c1d40119101400e10000c032a0780d00d11400da2140856030007003a00f9200c42a62000c070b102c00c080002a03030100341030a00075514215100607100b1009842c44001c80c284035400000e540503a0b11008a21142844018182200400b91428900301e0302495040a00354210031411b02c5102110782000c951564207080042070742c5075484008120040c208501d10b44a82001000304004c0b001401940c100c1c4c00540f40070400e0398988074810300503e80c502030031503103c4003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 511948003 1250 511946753 511946759
    0xa1a120706030605120c1003020f1c140f040f020312030103120e1f031a040c0207080f0d0f0f0c0b0c0901030e010501050f09040c05090115020606040c09170304050d03110709090b01 79
    0x80481c0711140c4600d24180144ad24900d500050700360f804c41c480c003aa0030a40e50301b02290140d4280a032140703030314018240082e1340c036080d41c1d450007200001d4006400d0308942c1100404544082141c2c2509550280b0881c0e200e6950746015200000d00c240e4036070015401c00010b84090500b030a44002041d2001b040390000c404400c2e0481c01420355011400040c070454469500c0c0351903622440d80c0c4a10954042c00e200c07400c1c169860f15000344c10704401c40607800701100002140d80907840c042c030241e4a16058840401c495001c030390f1200140c4010b0240c47d911018040c112a000c0c004100060703007a00e0600c50070b0346d0b5680e19801c0710000d1145a0b084034001401078103d1030201d00082d40035104480108600b40c6a4000c90f40301e0809800103c03c0c12808025440c0c03e9404002c90b55100f00308440a002145844400901d1a99248245120b00e42c0218960b15a1402401554050040540300094003601424000c00c8686640303050f68660188140c0030841c007034180a011041900080c42c080540d103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 511949253 1250 511948003 511948009
    0x2030d020f0706020c0604050d05180609060706150623180102120a02010906060e10050906030705031606090e0c070f0c030503030f0a0609020a080a1a120706030605120c 74
    0x4001078611605030300c01c025010005103944041d00e50450148014280b51a06203001850a000c00300848140300f4148554107008440c0c00c1d0310340400d002600e42a0f168199040419030324020700740020070107820801c0380c248151106440d0001c6072555682e2800185600840d07600b005840803100c02d205c801040b9405000c3c4080b098284044018811295141780c1c05460240310703040039100d000141d4540703400105100c9540148006403046968034611802e02d0004109400018887c0d01e000311042c80018201d5074060040700d0080c0405002e0b20010b41034080c040121881324081d60021481c14000030861300c1d102044076100311414883e241c64105036071641c1b03554201d181e0f8122072003004050044001101030000e14042e6800d9042030100d810300395a020140d4503aa0003242683d8030500c001230080d5030042c1032a400c20003c810004d00601646200d00414980c1d440b81030300840b508a00c09503041c80001c4400458200780d6040210036111800c01403266030200e91411030745d000e14840e00d5140307 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 511950503 1250 511949253 511949257
    0x2110050606160507060f030b0102060403080a0b040609053c040615062c0a17030c070617090c0607030809010605040f06060224040f1a0a0603120e0102030d02 69
    0x4100768100711a02c080100111519402100ea903001140c08000035034110700d898060071803d0606120340403004000039580c40c1c00401c00b404001e2240040350f2800080ea0101c1401c401c081e1080c0002c6442c0e903581c101920b02950a11548040081c0c0502c1882d01211040d402c006102d020050003030000c0d02c00c003c0b58a020704183c0707800e66144466501b024541101800401030380e1200c01c078100d0b4407180b400220180b888040c02c00d0021030f214103284e589a00c81706c4145d503280384ac43c9440a062929440c65406507400c0c441d00c0b03108a95020609940000c00d14100c408100a4600c4030ba5820240603101c200384442a90080402e203c0040064040c00080354800341c0e05000080b0250340d200050262800300c3c91800095035180814000e4a5041c01940101c103222100d052a01172204014042c440b0010405040b20304010341c0035007003040711088842d040d100034164800c0d031f0401c0030202c4010491032200710703030311103c601074122800e0044000c6008000c05801540c104070081c00b541020b5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 511951753 1250 511950503 511950511
    0x1f05120a0905340e0613090503341b290703030f09120f050c0607030c11100f0f090302100c0207080604120201050c190c06020d0911211005 61
    0x448443c04181d0350f04420260308800401c00031501d06000d09040d010701140082d90501d03030306e000b804d090350180406e10000840e101458214054000120080c0e1060070b0072080c0f84242c2d4501590030007182c14032130300c0500518003401480c841c02c08140d070b82808486a0030841c41c00b0042410745010510540c2044d005810090300909010500c12000100d00045401d128012212101c4950025100741c1d8020760f8561614030304c0c2015450116161849680e07000010440030406454081c0003040364800c04d01c403001100341c0e50840e5210488101c048001e040c0c80e52903209c1d0381d480c0c01101e200600c8135000301e041c0d0507010b401604c1d03070311190720089015100711000d81d000d40c4201140000d13800c070308000d101e110340e000380d07800f18041e0203040000f400d46002030496210400f0510071191222540b83c3e901e0305c990f00b28200000c0b04540f62500b0006030180e010840d0500d46088003000a000d1f401d01d4031059403030115001152900f40c0e05101c14820700c1e80240c0c0010740c2c1306102c10000301d40298070031a00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 511953003 1250 511951753 511951813
    0x7050702030d0903030e10080105060d1e02030118020f03040b0a110c011a01030b060d0207170a050702040c03020a09050904140307080c010c020712111f05120a0905 72
    0x6428016004640b03054070118418001403140c2204106140c0e21414080440b0001c4841c1882c042c0d500200400b00c0006018061268900041003070404280754000301d015905000b2002c0c80b1102000f108000307410900c9100078a203a000c8a02005190f40d10071035404404189846003141c5440e00c980701c140704001d211241080e5117a076000b0385440948045c140050350400040703031817040d808800c22005100c4054a041c1810480010499990841035540e070301c1307600e10010303114640c030700300010850580004200210800a460b28016500c84010850b40e070080d90240f04142100350120300300d2180c84e0400001441d6010b09108900d80f07040ca04d0b4001d8010300010020116403500f25007035a1203907004032500ca41c0001e02c0041c140080c080c00d060b0718842e0004d0902c86181921600c031201c80074100400081da400440d050703990743e068400285542a402ca10b10610100102034081d510840c0c403c0101d640c85400140004014000c10010640c45005400c4080041450140d08031401014101c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 511954253 1250 511953003 511953007
    0x9010b120712050a201201121a070c06050f0919030309080f091c020d060e1c030c03060b070f03080c120f010e0a0b101803020a030c08061303020606090705 68
    0x40c074501c0d14000e49015099481380007a2200012404485001000c043d103210980144466400c07481580348441c11500c3c20b41c01e4002c0010240340194035502c2c44c10500e4450b480c10014424226400010030318054400c0c04100030307940300e02c4444481d002c0100d504080680c0103c031001d06102c818005000b0f050f10909002c18030001540c0c40d62204e030010000c04148502c007203144081f51521f0040701030710318404400c013140c038191a00400c1e90b4541d014009800c554440000100d80301080101d049604841500b01d01da00941e002c0050143c2500407025000a0034010041040a003550458107000d9100d400ba0090380160341d800d55040e072000b41900d20181080c007950910040c55400244100741c40041e4000542c1030017000e030004100078114014151a0801503c89900d500104414212103800d2021203100c080308402c5552078030b0b4000075040300485100004001801a071102a229010260781c0142d680d600312801240782c10708040c1c0140d0218003c10f00030300304050450b800400525140b4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 511955503 1250 511954253 511954277
    0x18050c03100b130f181116110a08032a0705061204050708030309030a12061430030d06080d050703050a02030906040803130f08100f0e010c020a030e09010b1207 70
    0x11003021342c0e94405618543c0315400e85c4015070552042c1d40c481030860004a040840031040400d00f207500c0d4000410b49418140c054113182e9481c5034920080641c07400b2a56280a42640d41403884c5c110b81c07513504031351085c0603001d00d0a500847c00c40c1c140d4202400c02030030010300c440c29040000c00507109584901072081c01090780300c0c0910040d80309112060045582c0c41c4011001040b0401e0300031003c00f028540101482203900100c404c4400030004c032071030003401e81070600301c034030300d5800361903016041d00c1c04d41e07071a0f4010b240480034001410301c0000400003990b8403c80c0d1900d0341021210b503070000d402040701030300080c060300251645c0011841100d083c20300440206005500603004030700c50740c0c0080355611050034200a40006014000101c2c0700851401c400f060b521400c1102d0b6681560711182c800c00d201c5100c0e40035180e0552600300038003d0b0101e8503800380d00c41861500c00e800203503e0400c0a610760030005180c50498503002056440c1c00440040014903c0015100c01e0801c04c114010f5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 511956753 1250 511955503 511955519
    0x702060903010c0503161706210d0c0204050a06030201052203080406050c01180213020a0210090b07021506010e1507020d030305090705010c0f0803040201140418050c03100b13 77
    0x41d0f1080162140c0e0790360704121807420040040c0300c00c190208821241e0315400d17030402d02010303a000b004c19120340d210650039004030540c4c0501008031500c0c6208050707a000e0420391106c9207600f220300a581c10080c42e102d14070240309036074103400081d003c68000c00680060b600c5444044084c0b100c110144500c05442e9601c4c18035940c000c0c0d200c00700140c2c02007038032140100c0a00c680380d0f50014151210202c507546902003010028181d148000d055408124004154000c2c84207a5101e40002ca08019520140c82c000d91041e00a440e18401407050180e0007090f001c4a050703103800b03818140c685816050205080080e005480e400c0349401c150309104070740068407202081880c03c0c2c031075203004c0351500d0100c910f1031604591781d001504022244090101040130714420f08882030704040400da803640c66000685404a1600ca03075460f620000a0000703481045445100841244c030384140703c170ba124174075071000d0360009403244121261422805c00800444200605041c1e1200090b450041c2d607a03208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 511958003 1250 511956753 511956761
    0x190804110904141b280312110303160306050307060c1719090602060c0a05190e031501090c05030603030a032004030c03020909031e03041e051b0307060c0602070206090301 75
    0xc1300038010707059400b0b103158a030114404900640d00441c11143d000781d02e084400c1c032001480043c10301101c0c0580301824a10507421121030000681c2126901d08210502c01044c1640803c610000b0703142c5200804c02d40703804682e10003100c0250b82e607075041295503166130301000e190f0280c11504075810810041102c4260b0b80304a25000984c844400c150324190340a401d0020003000d103c0038400401c464100b0582000a6039000250f4070080c00d44041c0c10401901c803d80000d06055152041c4c412003c4010340300401d06041e1941d044082c80788481c151800d503028017040d100e5941c0358201744001c03080301d442644003241681064441d80002505240c00322100d5109400541e00d441c4d00c0607003070040d400c100004075004600c940003145028040405c54402204424007042040400000700d028000c001e410410f000d43c1032155180c4500032450b2041d41d5112402d00304519142c3da240c69201c030314020510200711150380d103580c441151231340c0d5180029407000c40304981c040c200307200d1040c180d2802d220b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 511959253 1250 511958003 511958023
    0x3030f0f0c11010c03020a0c0311070b0403080c0d030603030e130b0405090a050f0309061207020c03030a0e0306060a06020c061b0f010902150304020109061209060c02010219080411090414 82
    0xb0340094020166499900b514003a44500d000e040c01080095142030780321080c0d8980d1605864034110b4800103200f01810300d030345a4001e2420000100c0c001c810f2000314402042780005044c00c4503946000108154242c2e0886e11000c0c01042e0000300c2d4032200d0074000180c800c9602a0301e00054007148550004007200c409440341101544070000c0c0c80c0800c101003010725040c0f80740d50001d40c1010303214070000320303188550700780070b80c00708884004103120074000c0015000d10800102925124442141c0080007408812074041c42803160001003105810064408819980380380d0142c0505c00b51001031141c1030344065100000e4020000760040004800d01c044040712103c10001711b010280742c010032064a8140c0034400c0385100c10414000141c1c0c000c20907000b1507420342420340c0000d03640098440141400c0d5405441d4a00f400d2103905125410341c014000388403240b000c2014114006012900d00b542218006c0004004240c010541d181c43c0006980c0107105212448901030300700b115030b0030510a05 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 511960503 1250 511959253 511959257
    0x60105210f1b06090a0b0f0f160c050d0312111c020307020c01170604051306051e0c120c03060a0f09090b060906010e01030e0304080a0309090c0f02060403030f0f0c 72
    0x940b0209407280d020500803040c041110742508003121140068000d00d402d12601040c010300160300003100a01d00b09031072510410407085d42e1240340c80c0900d825004490801102d00200c009c501255915040d401040d4140d05562246006005541401d0041500c0303802804d4050050100207100009a401042c01403920000542c5038102a54042d20f440341034080c2c50705001d80d018040f40320184000c03075250b11a10440300498203840d110000c01c004410584003402c528140000c01070030301000100080c1010503074460b441c1a50300c0d07605280c840d000701e01c04408444a00b20100d034030480c02c070b80a1908172100405c054105070782ca03600e001c02400c266000140e803d031148649028407040d43c100c0b9a102c0d8094905d19010f00d04180002c144120032102c584c141030381c40446c1c644003141001500d015100e280300f01c40030700d10380d42130103086041d151084802040c204800b5884441c071800c9060120382003034000b8440c1d901e40390340c00e030080c28070401640001680e6811141d52401c2c140640c240c00300e07280e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 511961753 1250 511960503 511960513
    0x2212110715050705070e010605072402030a050906010e15090606191805030715080711061023010c0201050309030d0c05030421050f09031e0c011808060105210f 70
    0x16284c5642041c6155005240c00c0d4441d1004001c4541c1100865900550102c002105010100b61300b04d814107040c216400d40d10303c040108205510035900860142c2036803822600c0c144e80c1c1e00014100c010045402e004000d10550824856042c0011070381c0d08404010300301414a580c1e08a841e56681d5200d10010004409620640a900100784410050601034025204050a200d000c07411840981200300c200902e040020301c10030303c1405580f41128000041c4c3d04a42420ba10310a900300301790081c202c038204c1a03c05902d0341d00e003044c0c0884284c6410f8441d000202000e400544c0c803134000a0003541680400c003c1c0d4043c88880d807003503081000ca03c3c0c0340c00b912030070700d4102408656042010038413640340001e0b01a60094000040e00c021001c2449042c0d6030f400c080001c68242055002e0020004551110194143d000422a2003450000380c0c0d403151404c17403c00100d035174220180b02e17110140c0c00c208014070081c1041202c00140d0b00b4941c0c0500b07100c0c0480d001d50b510302510f054504445800c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 511963003 1250 511961753 511961767
    0x1d0d0614010f0b0406051e0c0f03030a0c080f07050a0c0501230702031e0d0b090a020403020f06030415052508040204060602011a04091a0c03221211071505 68
    0xc120b685402402c441080c880c00c0c41d003003d07400742c41886800181060064030303861501403251048100d500c4070a842090b5441c1e61140c4981a0741d94006642120000d410a0a02c0000c0340c0304541c0a44542000188040c0d952904903041d030f196401212540108000b0b10440d0300132610900450459030840740881594803582c0210a001d0031010701070308115042080f12040b80601d1100071803258001502203552101d45c400c8100c0207007000a102070700800700b0020000c0e4505594042c101303c1c0c0c0261130001c4400075010170020300703100c00c582c01044008801d440a586955951216a00c9040320314124504815155803c807c01c0e41c2d04840b10025480e1001c010440c10030340203000003080140000e000c0750406d040b8081919006076421809030fa41d0344844030900481c001e1540c96100260f040d54007900740010110140d40c42150103d203460140320100010b825040315640c03a068018000c040c85502e101c004950b042c0013800d036902507105001c0003082070882016078004400c01d40d190140d440712 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 511964253 1250 511963003 511963019
    0x2090105090402030a171b0f0606061e0702060403062c06011d131e060b0d020105160c050901090b0f0d020a1a0c070303030902011805011d0d061401 65
    0x4140c00140c000c0200e10705010050b1400070b68036440710346c05450440c001ca246181000300d03000f20000403e400400400001005d5070206030251061a00710a49400d56511001c0c007016128440c0108028100702d156412652882c80c00341200910003020039141c69030740d03260002906c0c440c5075803c0c420526280d1103080d140b184170b1800011008440544032543c5030481e0790984003117420714403080081100004000301e030a030300d040542d80c2c0d1000106020000140281828a0034520210742d19131802101c402ca0f071500b41045c27240154140d5410b440e01c0b101d00381545d411802c181d421250f0808081002c40c05903240ca51480c06004003c070006209100c001c10002007500c0e03050481c2c0210600c04406006d86c495000010aa460010300908044000c0b04440b026100c0c00102001d18020b0740800f008240d455040b09084074000da81c0d41a405140403031003c602c02462086602240001002550030700745030060034419500101801807008864468105503603084104444994500d001400210 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 511965503 1250 511964253 511964269
    0xd0204031104050f04050325020a060207031203110901030e0102090904031d0a0f05010309080705060c0703031a10110f0307060605150a08041e020303120f0c16060903090e090a02 78
    0x8074000c1044a8a4217054581c0707a180d110781c50500d07014400da880100c040300c41403450a02c0203071340a4414046207a075608020344070002030004403480900f4040041d41d4a01c60300500c3e800b1720081d10401c3c580038130440190300402001c0d1817400700c0d540912400010781e94845842d4800e41c000d80310084804400003030000400081074486228a4103014140940104032480350141e8074207007000038282055081030411400780b5000180140700c0e0000b00050700c0d4482000d004400d103c0d49041c003c2030b622a55105040e1290b4246641020141c01d00180140c400d04000340ca031040d00c1d041d240005120600c16041d80c1c8402410f03500c294840108001d18180902001c405585034200c141c24607402c104020203082001d803000e03000a00f0486911515080c4c0070008034140e88c010b007200c1d503030900714034289902d880840b83c00c10505008070005420381c0540c02251882400c4a102040c0038000b5914000100b5a0391400c1d07003003103030041001c10008901d118040c000d0400070010032640c495413040000a0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 511966753 1250 511965503 511965511
    0x3c0f07170109050c0c03030103050124140f040609063305041403011103010e15040e0a0f080f030702030414011d06030a09050111040602010e0a05210d020403110405 72
    0x4100424030800c689508401030544402200c04030342600c840c0035502c603d000d2561038000038000040000200481503000d070b0380007203945a0b41401c0703a40d9002e8202145480d031103180f114107060013800301d6510b850311680301488802400090300c2901c0f1000c003000c880b13076904000004204044c00030720701e88688220354034104045030b440e034403e03048101c01070180c0034501c5202d030410800701c040c100e150b400f0b4003d9041510001c0846803a5a503a0303050030403900007038403060000c3c5100802003503681098040d03178080c0342c286070040c03820400c1e550f114644c0c50310794402612002002c0c0082c40d0350314000070046000c2d0b5420740c011500c5a0600703c1709208002c0a1740308a05000e0640607040c0e0740400c401c85100d41e0301c400c0f9812502c0b5641e041e44080a81b41340300c1d00616075440c100345001031140e094090710690b01c8a9000300030f1000c07035103034980da41c0030994005130542d84400958a01400c0910001e06074010741e0750612708000c4000d070007070305903005900f0880d80401e040d03a411440c0c0c1000e2069a501c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 511968003 1250 511966753 511966757
    0x9080714060c030c03070309091401060f0f020f01110705060901060608041713030b010f081b06070c030b0702061909030f0e0d14010501030309150203033c0f07 70
    0x16440c1140c240040e081904400c1d01a075004120802650010320079204500c0ca144242c036510714640c5801000c03c041030042140a078940050f000b8440c94900146044c2d8100d0744802c0d85184c1c10040070b880444000540c4070441c41920100003405c0005c1c0100c40da60b40300c10b4040e903214480c0b4940310b4140040107140e11b60680c5803440c01c00c495540061100d800640040c038070b00d090416252440014880c41c080c610380d80f007a0240000030001000d80050480b440580d0903041c2d56110480c65484001c3c40494144801281d402089607140000081510380e10504101a50355529a2801c103280021602c20004d600304000b0052074003811b405c0745080701d40d02e013020405804c0360b990150402c8070b0b580c9000100b03c804160030446440d40001d003030400b034005544006200d100f2088601a0000b40400ca0002e518540d0029030b00031140c00c40c0b035000c00190080c40c21a070f00c140c3d030b00c1c8604203070f0318517418459100804640502c4c02041d204504002e039000102d12450840d4041a10080107096901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 511969253 1250 511968003 511968013
    0xb030a05132409050615010e01020c030604150618020c01060e04030f0804080c0a0f11012307020103061505181504030311011d0a0303051b04030b190204090b010908 72
    0x1203100302c00c0c440075680340408a52181034445080020012001c005000e40310b5081070007900808071414002c1031000b640d03180c6c1d06c0400100120385410405410b15015400b480c04100000c584002c00e1030300099180340060700c2030b6540351122450039010051900658005600e80302c180081c050440079001d100030030a0942855a0b004281107420509401048003038070100e801c10041c1c0302151103400d900011500404034a080c14420300c101e079002100d00d02890413500c8010350003480700f0400704c420009081d071001c460910803501da91002c98101d0405a070b41d00c0100d50a1100080503408503059a6095210f010401c61000c03103100c0525050310072b03e03c032742d803040c0782c074542804940a6907418900802c4400041444601401c501e03881480e060002030089003086000003003e20455009603800d11403030307d50b07a02000003803070307410340c8410039560410043c008a5880c400f07180d04445601c080118010307018103c0000c0760415000704003140c1c1c441d802804950707030080319070340030382a180702402c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 511970503 1250 511969253 511969291
    0x18040b0a0231080106060f091403030304030f0c0503070b04021903080904020a02011b0f080c0705070e0601121d1b0603040f080d0504030503010504060602030703080c130504060b030a05 81
    0x105030420b030400b02220702101d03041c40702e021000706107104010b1900d40e0080c441d82d0348501020741810002441d01001444050300011400d803211030301c004448001d07003c0c2d4a0b5846076141150094035100140090180501a00d00041c00801c01440164041d0091000c42e040a104215800103040103460140c0341801050020546000c102c03040410b0482e0010b82d02d00b40c043d8160702400300041021001c800d80781e04841c01e25005404c4c4c401051403a680c840d8182c0d20501c2425040c0280743d8082d0059100d41028030800d940030081a81004050601c0101c00b80b6407160711058450198184214038090884103c0b0082e00f08072805000442e59101d076842c207546070218520340401017000c0c01c9120382c40191400d0282c0c020466600315408441408107292506024007168000c1c480c0364042c522340000040c10394808419940710a13855540ca03104e0740c4681402c0456900009009d1112101400e4005602e6480e44a60710003807140140b00c68482ca82194980c04462006006012503a0310f07219003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 511971753 1250 511970503 511970527
    0x7020306010e060a0b030103080726070f1502030702070302040c05090f040b060909040305070209010b0307051b3a0c080a08070e0a06030902030d0306140f0d0218040b0a02 75
    0x60640d40c0040c0d2042050b0343e214001586090150b00c807440c0640700000220520034528004e081d0a40202c0d801c192488201a200030046607889000000c0784007808824005503014540e4134080d1301801880c1102890210518104c3e070042d2505005030380062400c00850806d03015060301010241801c03400d292084001c600100343c00701c492031149036600e8448489079581415114200400761408181d40b40a14025055605c060070036881020782c4000010a20035200450f071103400103a0f6240d080041032001d00710316903084004040b05004494030043d488528008032400c41481480b03042880e800510a142c5000c01c401704441040494240c100c00706100070200c511601c0ca0b072078164000d43e140c0b0401c4a24100c03034004a640100003650000e4001c0c0d06401060119000301d00f940c1407070081c601d00741d049881c148155540108158404032080c9001100644142009442c4040c011310583c0050442280710400c0010402d40409100610100d036203655401214504118601100d40e00e01c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 511973003 1250 511971753 511971763
    0x50304181506200714132004032f0105030406110d1a101b030e06030c072901120807060207050d0807020109050a020f0103200903010b0415030803180712031202070203 73
    0xd554060703176400504842c000030b20b6020f4280442051540514200c5014407021f0f164072030703c030594454140b489400c4105628238401c22107607003c80102d2882d0f2201000654203a040180b050b941c940c5d0341c424450103448000000c1c00d920789800340005019602807444000c111080802c903000311300b200c41300d00c0c50784d0704642684101e030700012108004000700d1500322000c0f1000500d65070403401c0441484450108040500303009031150614080101d9820070b009070344500c01c5900070314001d5400040110580040c1c030500b5050107022150325102d400c0c1c850006076440b1400c2121140c2c030000404006503804654250040d209100910112602c0d8031155650081864007900c112002040d05803030342c4c001d0b408011940040d401c03090a0781c80c00d081c8500c01c1c0c1c1240170341600039424419900c0c0c0c245441e2040c102d001091400708160300c0d0841d251010250002000c6030039062100a15080140041204400030b00b8601407424000c451454010508088040100d5040340140040c03c0140c0c0c000c18 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 511974253 1250 511973003 511973039
    0x206010302092a04030305090108090309010806090c040308130303020601121a13021801030b06040b0d0807051e0c151207180b0c01050a14040503041815062007 70
    0xc18000700c40d02c020401d802d000081e01e4002d01c03d14001400020503030880058083e298090f03c400086070b80d400101d80c0c40e881400c0e8110f0005403060000741080c600b12130000c0d0004044281d1504080e00c9640389005540309500070740c980071752003900300100369040280c14090801d060190001704030710760305c030844d429505550908120190000a00031070741a031950304910b8001300b1041303801c52814044c0345280e00038007040e03d5000403000000c4880c14203002d50000300e24003070204014260b0a84031140b43c0e4004d80f004441900540c1c4a000003c1c1707a441c81e4000400f891406005000c210f1020000c1803c004480810320007001e001515002c0031401825500c0151400c100400c1705400c20484580e0b0165040000d1154001c80d44044101056104a2065804d59000c05c480c1049000c5d01c0c40c0b480c4111401000b83d0300c1000706215008840d065880386580310314011422041c000c00200c5104895000b680020309110001c02c0032040c0f1424005035600b649001c1e001141c20200702c4086560501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 511975503 1250 511974253 511974271
    0x3062c070e181303080a051003030e04021216030614130b01090b0c010c140403240219111b01080105010c0c09060e0105031005010b0301060c21020d0f020601030209 72
    0x7004011540342c200356500141540600c0031100d142002010420b00340310003080d4001000d101c0042e2000b042842014040c9100081000d140c1d80f9584c0c0440b40301d00382e0742c3c1301c0e50415000c0c090441c52000b00da24080c01821001603000b055254010018121421a4481c1881d16055249107240d9120068030b078295a004181c00301e000405a80181c0d142c0d01c0c50707400f00c075075464002642201c001e01135011300e0040505c7d585000340c6d50040402c0300040d024070300018001540850180c40740e01071b0200d007030f5202030340c04501500b820f100c00c95001ca500c4d1780f408000007043e00c5050f800c541c01d1080c89002224820341c0085d400c4864100e000030840c1740c05028460610202460038070601210340103480007414480c10500c000d6403100301560071241e0a10451303000b4807603a9400b13500c26a084c0101341c1030319440c5070b0b150b04580c0303440781c116240e4407441404e950604280085200791513200c0482942c03c16250014040d50400500c001d10402c1c40c0820502103401c03c0d801400141d0765044801d130801541 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 511976753 1250 511975503 511975517
    0x3010b0d050403030e120a0f0203030c030a05072006160503040506070302090301140420010f230d02120121030207050f28030611040819050c1003062c07 67
    0x60f14058004140810740c0c040b144c4240140703a03d011000ca8020241e82200c1e40d1410302c0c405601c507090ba581e00041d038810303401e400140002035000c82c0981c016a408600352800000b0320301d035003901110036214400410b090f90020300410451401042c0800c103203100c240340552541c5090f40f5000d8035008d0107071480c81056000944051079a900b50809007444050190414507400d062411000b40c0145c40b07501e080c2c0011000000a00d5170081c540c3d110410100e8032a03108106c2c0e11031082c0c8646400460506c007086040c80403055444c103034400f070f110000c0d0704087c144084d4101007030340b00c516028148511b0882502901080042d43c0818800b0072200b040e80c08800c10500d050000d1a424007406d403480b495014842d084050380140c3c5111404c41c2d00402d03041005000418a085440c82a03001d402046d612021410707071402a0000c4040c030403070103001580d051344000800145820300030414400001e0303c50f0380c103110300c0a01c110000503181601210350903421061255a20380c2e040103014030306000c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 511978003 1250 511976753 511976761
    0xc0307062a0c082b0b0d0203102c0c01020f0c011d06040314060f090d0c02011b050f0106050a0b03151207050a0306050a0507080601052205090109020a0206090303010b0d05 75
    0x26000c00c1d03a801080b40300d41c2400c8030015034248815003412681c403000480c20100180c01c5c80c1080344009600e6500600074090400f1801103140161a60040444a5201d80200c01c9100e0040d038500f2081c110700704002c0c11a54900100082c07402c101d00c066440c1c59000749441e03d040d680c210195280c1c426050290111500681c000549103000395400a003100f243c06110f21100000803550921502c1401030040c2a52128024181c1d00ca44d140c0804000c130b03141c24010f00c09580075841940d03408043c2011140c002072107a48903030506d07800018091540e07450700000d101c0ba150000a140c040c0c01511400703811031800e40d180e281c64a13502c400d4503015440c000c0000d00507000600408000d0f08001c0c0c08000196920f01d403044c028001268009003003440c2c403000c510303a544030380c0e1183e0107488141c1d119420401d01001004120529a201c2e521031642508009a036031a56000c241c000c2522079001078032441104000f074105140101900140d4200700010701400032a2401d880c500c6200d0070002403284d81e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 511979253 1250 511978003 511978013
    0xe012c04020912030405031b0612060f03100b0a0618060302030c040e04120801050d120806030106090e0f0d0819090627060b420c0307062a0c 62
    0x100b00c002080d0410007041d0381d0301401c040000200b0460700290112401d41100c00024130075201c00c416100e90006d0200b1a1103861410340390181e403c500010550300455107404002450401e9148191140d142c0713031060109186041c440d03180c010141801d10141102e400326180280500384d000320342c00e042e404004030f01d8a4101ea003c0c1c034080d22401c20700f1b80090405042c1180841081403007100000d140742e00220b094202aa800c0c0c001903844800010301c0c80c0d02c01c00070b88000100401d01a0107660b55180010001a1030003800d91401403000505115910164200d041101e00c0181105000602d41030040c030402c00603005095000450000484141500e0020043c2c49800c0c05840c842c0d120b86d8159000c08100c280260345d46220304410080c5c0d140714000e000300380203001c0c00c001800c00c0040d841820b403c0100d05142c41803550040c904c0114405007900324454003c00e05402260784041440c00800941c0e100b1840401c0000c4803840045182d0002d0b10444488496400f0400c14041c0800302080707 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 511980503 1250 511979253 511979257
    0x1009080d0302130506040308310308180f01080f0901061a0c070e01050d021c0602030408031509010b1902152838031207030e012c0402 59
    0x2219905442800c060480d004019420010701c0c00503c40b104500015540f404800f2a01100c6d400041c04d030410b4180341d404440150840314248080c0000c055880380c41c2e41707200101c40994801d249407034848034a030040300480c0340e014110038080d84d24018050110381e004204503510110090582c2d1080c1d807122030150150050341d1000e422850100c0d4507250744001c0c04c0117851b00c8090041210b1056640c0c14a02160b14000c0c42030703e0300400a01d55040260070182d01c54002101e0440c000d002c028a581d498008a80c0300312410f40d100003001c800c1c00700c1c3c0c100140c2c8030108a14200d552041c0f030750500c6010983d5200d9980901c0d5454545030300091083d00034440003403d400e6400109403685400c00051082082c4a0721400174459404c400d5001c40700684a4440b0b0082100e544442510482303000e603801100c10b0812100c8103000010400c0740e66410000141d141000c207000c0b80d1200036925010703248030138400344070341445018603000020784038a581da110400851090301a1012440e000b0400034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 511981753 1250 511980503 511980509
    0x4110607030e0a121401060b0f0f09090a02030414030301061704050115060203041829060d0c200c030c0103050a09230c0901060c030c030912060605032104051009 71
    0x1000c080034001070030480800104e0b080c07500a1040c80e031078158041d0203608130b070744a000d03807000c2640501048010020680c0600740c01ca0101d0380e00c91a00348c1c00000074410010484040044e190000204070400c454034150040c191400b000035815941851406003054180020317007021099000700184c1070210035046482031411845031440c901c0c1d100d40d4002d403203502a010f0f200280c0d10b800040c0e41d16001612400c00c514a50340d0407010520740e10247c4480ca4552800b83d40d5005070240800500d04015100e40d500310309003034491242c3c820b003d030401c0041842e0696400b22035008001004100d0311302040d00e9400d50024130b000200c80d40c6030607002e8014215640e0240000d6150980249503040a813505d51070201c8040c121107e00d500c0804000140d1024010140000c119001f0b080000e400748002d01d400354440d0030041e8000340c88017190358060003005c105503101a00d074041040642400c1c8801d07452030100c6292a451075a500f0707401c0e90548120720a16008403040032480030114850f030034031005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 511983003 1250 511981753 511981759
    0x90b030406060501030b0d020306011403010207050d0c060605100f0831110f01120e031c1b0516020904080d110d11160303180c0602100b040504110607030e 68
    0x2a400c150078590000c04842c05654046464001440400d140005801c45070941c010b00804560703007440d070f0300e440c03510070900c025030150b400b4460100020000d0100d8803040c1c070306a552140021103400d103034003a1021b590101e40281103540c5002e07601e5034012541da01005417030030030a00c1600c4000781034401000302043d4040954400030f10101420104581d400d00c14060103140500e52180d1007000b980f08158650785011404244d4018241442c2d0340007900030f584050152130078410910520001c00e0758110001da100b50380c1d1628280c615142c0e2040082d004600d1800e5818001d9410408181000e504070191142c481403001078100401d040455a00c0603100390709211160302a40110482d030480e0700c85400150403c4644030690700402d09640c204103400208d05101c0e913507a00c040d0000c0c02651520305004d00c0110550020a400d5240300b402412103034010001c042621098a08031010005a5442035040c003090101196540e081e10700c0c1a00100c40d020f5441400d80340030756016410a461a030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 511984253 1250 511983003 511983007
    0x1206090603071e051801060512251709010605090c090f0a030b0610030e03030a02031f03030809120412060e031209010203070f0c031e0e06030925061e090b 68
    0x40d5540140d44144120361054401903a10170081841c1c0c520719134240581c6000074400e112003c1000351801034a50040c0c51140483d80180842106c1800400d8008070304c0045138106640c6942c0303445900c82c080c1e01c845408000c102c000d01305400540010005460078101c040041244d55007540d80d0440000410001004150150355034648444440004c031840340c0325404090801d19220700130300071110400c0d45d510185203940c0c0c4400d072a000a400150100c0407a0030704840320303000010301c924020701860103600c1d481e000e0300e080003230341c1c1c40c00b2039940ca400f0022000740020840c3c01d165281e01d00455074840404200b400b041c088041c0355015060f8120b108600e20000d01c0544031041d8000c3d03000b1122986c81c007280091102c2c00351160041190700800080c210f83c0c401c0e1081e80020351000c182d15503031800c440c440400c0c00010b0f61640050300e58480b2500603d00211500d4146201000b13001908a110103403140b51000203011901c10020415144c06240c044440d51849500b203c405090b031616415 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 511985503 1250 511984253 511984289
    0xf03090109020f1504030f0c05030d03090c050409050c092e0905070c030e090402150703050d0e0d050d0c021009030f020d030e1902180f0405070b120609060307 70
    0xe001c0c0c0304805007a402200da03042e51103c1c0e400d003800c0da410b0140c020761000e481c09295686040007243c030440c0030798280083e901d0101c1c2c07a0340c0034802c00240c500c4694000c00c051580303003011000c05420381d111034803403031618030500c000441c08201c07e02004811180e0b50696a80c0c82c0744590b04004800c000c40da4107110f031150f9001ca00c404144803054900c000f4040006603034000055801c10b403490009004145203102d0000603240c8405969401440903014070070484501c003656140d5000358000b100880c202083c0341420703200c40d11030007030449101f500801341401c009030050224841e02c541c034844d0b29151016001140d0003000340942012241c0c004000060560038018440300059520a005010302d1144d0401c2e248640100805c0d0134400028181618110360740100f8881004822070300510408241c0d070226480c0c4c84510f2080700c52904546141c6040c0c034020b230400c01150002e10a030307142031145c4003032440065a03103070f80300c0b100b520703104016100d010010f850000a540200e4050502c01e15030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 511986753 1250 511985503 511985521
    0xc080909010b0a12051015020c03101d120304031d0303190807020c01020d030c17090a02010906020d0203030105011d1f0e0604080a020609060408060c030103290402060a050f03 77
    0x7040480000c1e510a24504494210001504d101b40c03419404401d44000c1070109061408942450b49400d0048070602c004400100e030030000381070243c4460903502c0209419003682c568902058498a9003d4140c81c0c141e20b000e1041404003520103001c10a80e5189003403032a10a174501029014010100c0c1d031650000701c41c00b003515480c0c4901c00c0c001501d020110300740301c0c000100d03424207070300c140c001c2c1400d910181d004800030010301c60084108042c0700b660a00e01500418918001d40714440900400007507800050700803240c590049086610a8a13210350890303010042e07d043d00e109182c400644c07000c02600b801960f202d070b18040c0d0701c218900c55200c9010462810344a10144a03100c8002c0d60301e070641001154082e5208102298100d00d5140005140c100b00801c0c00380c3c402040d050420761070303800a5282881c211060040d0110010040c4244404d501c2a00400c80f12200040341601c40e1440040351070002400003070142c00d020407902d40c090b0080041d01e804c08140042c0c1034507803a080000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 511988003 1250 511986753 511986757
    0x1f0503071106134206090902091b040504061d07050f03010e100e0703090506060a0602030403060f0608030a080a060b0705031905090402220b120f070309020a08010b19050307060c080909010b 83
    0x103405021746032100000325012180120b0315100c2c0c00516212242e50781213a9502c0003184104a090217000402005c1042e80d01c51040c0405041c90f8a40308008a0840c0303400790560301c0143c00001801414449940c150005104890641c6c18505105106031580d010040c42c00440780c014400104440c010011145c2c0d05a10503000c8030b0151003142d41640312201401000c4045000714030068004202c180081905500400001c4403070000000e81250384005107400d5410415a000c00901600300380541d9030554080e1202500030304109600c0c01403140da41c1ca41d01d00c02c0032190307525082d216419507845400b440036200f41e080040c10a5540d00306005110585844600c5102d41c210180400405c0100c0318000390745254225000b004955103c01000b041c0464004015000b0035455014403401038440d0b4103060000d0080c00004100710300c440c000c00038400c0340c0c04600c1c4862060468104981c0d0350000b0043c003290f0340790400000c11022030a01e45803078411003181c0d0b600801580c000092240c10040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 511989253 1250 511988003 511988123
    0x4090b06031b0d140c0303161506061205060a0906090c080108030304050705010804050708011e1b02030307052511100f0806010e1f050307110613 64
    0x580c0d00030b401600421a00c009005080e07a0001001e2594000003a080000d6062041040d81128980f000b000b00007441c540c804480508000d4560000c2c0c001c120840800104490104005101181c14108000c041d849071211f55441c0c0c54490313000c229543c4540c06c50a018140c04401031101e1902c0c1e590070320142c003d0100360000103054800001e1220000700580340a694003001410005141000440d003080010340300342c40703038004d15a0002e11100c1c244141301c8620a9405042809a0004018000c43e0043d41241ca040e0741d03821525104c0503800320440ea40410740d41405a215050180303c24181c0cac401c0c0403010f6801c1641e10b080c4062140082c8220308020040360031503803c441c044001c4402030304662140e0040382c0081c0205e822580540351501681001801d0514480740c2041100c1d18459800140300106600005000100e41e000c09a680140c0484004110382e0600070341c502d0240c41008405040041c580052100e0680c0840c20078103a41158481c5c07100010310b20f8070710304510350400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 511990503 1250 511989253 511989259
    0x613020c06091f090c030204090510050709060801060509031f0f09080315061204030525120207080708100507020703152a021b060415080916120f060b04090b06 70
    0x24001c920100d10394002c070403c5550006540808500c6c41e424000075002e514400c0b1036901902142448080c1c0900c2074500c107005039640c840d04d0f203250032405031250b02c040c0c200c541000030802c1030b00b540c1e4500092140003240d04801441e03602c40d01c60b01540041169020590045041680701814450050013440c000d180d500405031042d480a0200142445005e0f01d207100e1107000800500464002e401410100d0000c140601c070200c0b4005a4600170f20a8003011124a0b00801e0b0178002d0903410440e0300040d28410b0001d00700c0d1402c01c02c8090b5903d0003e10340c225000d80700c1c000030710b55600c00d12004009590082d4041d05080343c6114000c0540700301d0001d03041c1e9403900e50300c2c200818054042c0388000a0700341c02804540d079800c07048d03103424580342d062940c0080c000c00c0000341c180f003890040d1800c3c000c00e80e1074049500348040c5840c01c1c501160304448114030810310a210340c039114808034168a601140d003090001e035074075000000d40441010145e10521301170944040c030800c000003038410b510407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 511991753 1250 511990503 511990543
    0xd02070c050307060f0507020117010905040b0f060307140a0f0602060f130b060d110a062001020703020c06072901030302010f06030309090e010605101e03140613020c0609 75
    0x50402e050b501e070140d00c0b03401c00150540002010040c080c00c001c0070140d00625141440c1c2100401000e4503c07000e900070000650b56404200030720404030781890300007540802034034a40c140240000e035200341d0f6000d44624481107412085555a0741021540204030016500f034503aa0750f95000303500c4d690100d41d941c85440d54080024142c880700154903419551011500016441e42800c1c04811044408102c03803008150f4204c81c001c1c0e8800580600400c0c1981d25514140201c49545210500d40058100142c2c0107202010000b41c01041c03c0c4040c0e01d090310965110360090405020404c00a450711041a65071658005841c0701d5508040c10b0700e000e60002e0001c518507011640450303006201c0500002c1803001d09104406007608414290302c4401c0011410546540000d10040c0c81400000701150009c840703c84d00c415940c001d6070b40b5810600301086070740c803030380400010800001c1503144544800700140c1100b000b03940c1a80c55140008084070f10070f25186000303070364450340420b5401c103880c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 511993003 1250 511991753 511991759
    0x2130b0315012303210a0201140f2d070305010f08031224120a0b0c1602091306090b09010e19140a080708041a0c1c03110d02070c 57
    0x8502201c41c1281c815180f1808500a0200198504080c20008560500030300013641401c608100c038504004c0c800c054000c1d5079504200000e0708550160380c10110040740102004440302550710315a61060788201c40c513086580000c05150501203140542c01c141c22910709000703100f6810392000f07058817181501c0c580b1494a400351142d9900540310030240c101e0100c0001a00080f80e01c4400407041c3c03064503031020703d03100c41000410a0803a4800c40311503511104c00901030202e1100c0303145c2c010192034407540c5024600c211000b42d22482181c0680900c00c1080407481001421180546040d00540b04018078100e5180040714501d080d904084250308140002c4420840420181e0b10310100300c0060300e042480d03589121441c0c2810568107110b019451074940405d45100040c01f245207d04a0150f03624100b80010780441d4401120414484041c803151506030000586064551003005004084000b00e0500300c000d0003000084658030b00300890f584260501640140044a1040605042a0762 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 511994253 1250 511993003 511993033
    0x30a02060106170402040c0210110d0b0414072d050309100203090c010c02040f0507020f010608071206090606090c0201150905070801030308040501060e2d070e120a02130b03 76
    0x4101101c07250f008003070b20041070051030310358000d03031258000303005460401d411038030071071300301c46d0001c918440c82d100025200f511214584030300d01c003000d0100c0b0b0030003078008189210b044160005000c0410311000c54274004e60360303507038003c8190007010b000b4000307210100c0c04000070650703001540c4c40c40a6205408012400142034006e0b0703071180c0c958400400002c55403c3c01105c2c54030491109a805c07541d503034810b0980b44007a000302486003131103800030b11710481394070101400c66000b13502545454220880611008500c66540c40c2c4040e004103011401103a6801c0590041c403d03644143c410b0b0385495040380c030003901034100c1062245c020034215030b03890b61442480141c540454420300003a40d070200510001e4001e680d00391f0410b014800029003d82c0b100000d044c140c0054500c01006000c01031a24039041109a28020307039031640c000803083c0d090001020b002c010450085900c13403180c0345402203100768204016010787d070700100094149000c810100300182800380c82a03010b030080b0700b100c00c3e49003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 511995503 1250 511994253 511994267
    0x100e13090b0613180f030207080f1c0e03100b0a0e01050303030103020114131410030b0a150201180b0f070507030c120311031f171504051e030a02060106 67
    0x150040703403058440e40c5180c1000054030000c3c08007949983d50f040000c4003a80c014401420b003503c10350490405410604000e890100b4030740c00100c05610014641c41500004507039401030700069903450315002a6004255040641c440d500c0d901031065601c081c10008580e08841110902590889030040c0c481c4846030140009015841e00741e8010801000154890034800c0c02c4216242003403070602c3c0c4000c03a210400f444a60022179406a40e1040c0011840c2c04280b01c40d40c8074250800700000000705000c55134841c82071040c03440d12010601915402c0d0700030b420007050180c03541c5180c003981c580361424010f00700c07040c2ca00403c4e01c600c41c000101d600d07000300111555945c01d0b8646030241c5005640c0d004042842007081010542c480ca281d030300b101d07000f4010313500503520451540380313405640980c0d00d10401f00fa40583c41c0084200c804041d50307000464911041c03512100444080c0e5642c1c10914a020800c046101c0b009009548a05c0d0480011001d04120b11182e400d484259907074202c200c490b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 511996753 1250 511995503 511995521
    0x30c15040f1406240306041704030c060815120c0d020a0b0c071505120a050c0f19021b06040306050a1803120506041a0f0d060513050c0303040e0f0c0702100e13 70
    0x140c3c0044003083c08140f0394408040e80c00341056825160540300cbd99020b8980e0500e80c010004155084107002d803200b040740401e144030f0000d40f0740d412801580400c6541d240005130019000b84903031004002513403113101181003d058448116940c81d980d50203040d650303001d984602c0603008000c54005c500d0a21940880b0003503c0c141050001e580c540710440b0000b000d000d0f04400103488104050081c0c00070050182100b000c050714200442c49299030080d04182e4490440c610500744020410559991203090b241901d801c14000a8607035150100c0700300418a0300810100b5030440741050080650000b00780861400c607100610407500e070803040c80b081d1554410903560071030f4201e036090b0080c10091084828144010201c180c54441600d03001c3c00c1715000c0e100d402d40f2036406d2400e4424001c00308045198840143d004610302031901c0300701407074180c010300746104850b02000403500d001801000d640816400519450003c5014035016103104c3d14464910b01800f1064072101003c3e0582c8200740c0d413 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 511998003 1250 511996753 511996759
    0x9010305060c130f2c06060d090f060e060117010b010507082206030e07081203070e0111151006081513060b04030606090e030c15040f140624 62
    0x1a112000b8540c1250002d168092401001010000f182e182c4501614018451408205030503d0088546890030102c1c4880c400744082903010f202841d200c10003200c076400048000029034013500d1800c00010341202c000505214180891f22008100104419040b10a0044514511b10014000e5400d882001248502003602030140401040d4040c0040c0300c0d03c00072402c0038214031180c01000b4058180d81e0071410000307a4510009a05080800886000e42110001084018142521042e01d0703c4000d01c00700400040c0340c0010517036401259521241d22a2030140c0e01d550005140c600e403000705c00c8a141d1180c0c00840b10009025015003d11801025640411140343e4502c0d01841520340b0000d4200c03494a40c2c41034002013200811000d4400340d446404041407051400300c544054441b216801605038104000c081d64503140010707049010f541900380c40b40f80e0390716420300701c1f01c07244c2c800c4000c1d207410803000c404000200041101413040c20060010030080041c1d00d90a030000b040b42202c1d6070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 511999253 1250 511998003 511998013
    0x70224010e04170a0f0f03090804031104090803040803040203060a0e0c10020c0409050f01050a020405010801030b0702120307112b11070302030316030e010302030c030103230313050a0509010305 85
    0x20011441c0546900501449074002d181d484034803031414607840070079a000041e0808010202e6968045408090326400f13103824072910341151a8044140314600c802820001c00c400c01641e1502e03180c001c0d2120310f1704502416120302d89030809400ba6031045404a100f401640f00003040c4500c80d1042440380f16214008001504100c2d0901c400040a40304400a601c00e03918480301d01da84078020303041030501c650040d10500e46100346250070b44002900c400d65540c014001480540d80c4808140d045a8011034020000d4848403000d82c14800501c0009144c29000020080400d400c940d1410040310107400722000c1040119528030412556982c03000c3c030b540302c407200d045501e110f44d4610559054100a40310760b0703030b6640c0c00240341d50320010514100848101b000000d1540154a104450400b13003001d45c44c0d03160003c4422030a22050000825004941075902110600d14607409400d204002c1125951084140c00f100d51150b14401d05104902c01840880d550801c1c5003014101c943c850300800d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 512000503 1250 511999253 511999259
    0x1109010f060c030e1f090b0f07030507080d05100e060102120f070303150f080f0a03020a020108070509090f2e12031b0809012d140909040b07022401 65
    0x44164400305420750070080462032150103a95154504420a144a500c412980401c20f4010b0060180380c0c2c0a447c80030018440c0102c054104402c0703030026580f40c07800c5035407181585020b4046028808101781c0f210328020411880501c15500d0800750707000704a52001c59590000126a0341c04c003541072042180e420b0001d00104002140600a01d5120381804180007041e01288080c0101e143e0040704d0458081c1c1c42085038600c20b20241c500860f90320098134401c5200d0b10082c3d9600c0000c44028100840c8034002001640310300166003502000609100c00d40c1400c0d00c00000c907036000d441500261940c811110f490300260700059070000c004400c2101c8540c038040f8030460180c42c1900c2502803180c0501010480110920340c840320f42e10414019844a82510005050a600508072a188a0042da01c180c035000d692024400040162074600c800c503070f071021903140703e0046d284519084a60303071051000300885164541d12600070f940c21608020405540341800358000c2884c139044020740c3e8018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 512001753 1250 512000503 512000507
    0x3020711090613051008011803091a0a050331060e0a110d1106070b1005010801030201020307120504080d0801030b0703050f04030e011e030c0e0a150305040c030501060807031109010f06 81
    0x52031740941c440305080b80013035039026002c4c25568800d800c80c030101c621020b24000c0541080301d21014202030007910b003158040500110052107580856028400c0110000d1818166090803072400c0b0580103050303000c447d801c1d0b40d044040350140c904540e01800c1107203000e4980302c00a12550125007119401410903171100a0015000070400180c940e07034520844102903844100050400d144192662601460320410340500d43d1003541040d8100503101c8010000350f03034000141d45541da00154440c50035502010160307410301c559400503c84e80290078603020440c1d0452103c504890044503200c2c0e40d42d0b50044100c00329441107400e8100d121a5a0205021038415880201e2200042c10f0040010000d0032407100d041c60019555000a80c07030f0711036501e845901103142014501c05071501003a103800c011640082c040b6401211003019a83c00c0010b080c0440d800c620700003550090020007055403201860f54a4400500081d141942d43c035a43c000c8504142c40716904803291000d03078840f0b02e0b00380076003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 512003003 1250 512001753 512001761
    0x80a0314091e0304080a0c08061e0c210c07030318030903030f022a0f0108150d0206070c0602030408071706070e010507021905130b280b040603020711090613 69
    0x10030b0b1a100034440801c00103410400ca03203055004e00f000034405440c0c4940c071441c0280003804400710200daa01c4404210f00e0705c0c011103412004040009864000038516900a1080002e200100d444007006000c03080034070307030000e09003075000c0d40c0c0500450140a160144d485a41180180012004ca03c1000071038820249403a00c0d030700c1481030350400540a00003c620151102c490301c01d1250b140070700c08141c9400700c0854590442800c18807040d01e03054280d59041040c1503226405602d40410810442d13581e00704031000e031540a0801d00403961601c50007076498004d805442090f10625902203141d1003aa04040400302051004112559452504540800a508885c6d0600005100500040c1c0d80e20030325104e540c1004250b000c0c001d01e404104a01c9001e0f0b03821400106141c114040042c1c0c450503030880c001080303080c0b020000304202d014100e101c03490368010202e0f00300c0410007013403880d4590002e05031a400390100c0c0742044520010030103121400d42381b640d0300400c3c0302c42a060109941d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 512004253 1250 512003003 512003053
    0x717010503190302030c160501091e0306020c031b0105070306082b0e03100f0528092a030c0e0108061506160506040606080109020a0e0a06030f080a031409 68
    0x7040d28105804a1000f500c2d00424001c0d14a009201f80c00c00e00c0035517480404e050007094803440c002607800f031003030302c1c1c2e515804640006800f590700020300c111040d80030811a0890401c04a000c0c501000102802d0f0003418241d8480c00040e052400005601d0700002d05140030a940c140f1034455511b49400389803080c0304206522040c0301c0e01003002c2c140c036601805400900529400d000c9400c60b081c410b0242120b41c01040700ea089a00b0310300034802c0e910900300103070040e500844001000c1c0c89038180314080107101080c03540c961440c050f0242401701480d90040440e03201c0e03d0441c82850300c23001800b104203024011514164017641c00513903421100c10443c880201c000c2c00c4e5915008192038054101c84407080c040c2c0e4513502410070300c410810140308103402084181c0080082d9070f56940002d2860420b8407075130f0603d60310540400e081e45040d601030001954040316405110b11a8504441c0640080d403002c800b19191030900d000e5401406074075803041c00280301400c50304540710441c18150504803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 512005503 1250 512004253 512004257
    0xb2205090d090b121b190f08100e040c0b0c071406181009090c09170c030a03120204050d0b1f05090c1c020a050717090d02091905040b07170105031903 66
    0x814517004144c9800080c2a07614540c160018003805403040a006000d01d5805941000300010410a01011058205040d50290080e03140140c0321030600c61400b020742d402510a010340003460541c1e070100090064115626a00c00c241180e1120007003001c103000b40407051034440c2405c2c580d20020719100c0c2c00d1100503105400c0c1401c00c0342d25211a0011503640351201d102003400e0030310901c0302c0c031145100107004900b04030003000c010f4a03010119495020703003000101817004007944840b14181d0741d0142d030080c14002d4445040030030241400090b80c0001d5600d20003c1080c1a541d041002c0408a050180d800203051000035440d121303520711841c1e1001d41c2d0003451510304103082903201c5041c0024100c030280d507600c194494109042003408402d81c2e20030211014030030403c9a0345a02d450034001c010640480e1001c640795240005800e420343c0c02044040305900c0c183c200000c11a85031701a50080c4190340c1c0300400e0349401c0c0c1c011440400d00b8010103030305074440c035050200406401c039200d02c664480c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 512006753 1250 512005503 512005531
    0x70311130f1103090f1603121211031b0316050c010b0d05070609080304060e0f040e10060609050f01050301120602040312080916050607060b2205090d090b12 69
    0x41024100326240000016500040082804041c041c1080003103401c1417620701a05658806440c4003245101c2840018071546140008222080c050f18a08407112641d600138090300c40e07030300400d07040c0e80d0088070f03503100003128002c0500d80c85104030290b0b8800c000c40540c070181e002c2d9000c410b6603e50082c984400c455920341e109190540c41700b00c6001003551203100103018090800d1406041071102c1d8002c08101c0d8014001000843d900c1400c54110742d90540d0a002208413400c0820098120f03680039030014410480c0c41c48035400c4c1c641c04003007100c9491b92000031540d140c00820050300720f02d45000740083e0040c00148000d80050520303602051040500514051303591383c861108190004c140008200c00b02d007040030210b004e00c8000703507100304100c1200c50b060400002503254024000c015002030f83ea90f4403075203140c0315001402c402528000c103461825880400c0c00000d442c040340d040400340181c0c0346169615000f00164001c0c2c9040f000114140864190740d40300152009003060b05015030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 512008003 1250 512006753 512006771
    0x4031b050712050102190806130e030f07081c060b0406031104080712050615090106050705070801180201020f010207020109060507080f0f0a031b120e0f0102030a060f0807031113 78
    0x2000c82c814018602c90000961241995407907000d40401c40f224040a008001c0c0c1000740300e46e40c034050050400c01204000402010141c1c0d00c5107980120f8110002c420030014469003445030b004041d0030540400780701350f51034a01880f03400003031b03e15510490300c080d07000f031100344545030080d0020300506c030350790800500781550313040141e00d003030900d601070201c1d451411843c5041c060248031990344901c600c0c0011084065142c040351010105100303120801c28042288420003005022060041038401c00034040c08420034110700c400802024203d02500ca9071220444404c0180241c03a88141c0584981c0070f910314100c0300f641c40703611250040707070950005c000303124008042c1405400080000e80d8400d40b541545040901102e0740e180203003500c00d0094a007401115403041d807440300c49886a1010035505082c615642c40c2450314400c3e92513079400481002070703016103a404101220105203c00070040d65900107a602c6084500000d07205481c120044042400c0000108440b0f8146420000f22215 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 512009253 1250 512008003 512008019
    0xa0c090b1e21061507020303040e060102010b0307230103140105100c0b07090906050f0a091505040e0c100801060e010c03121503061a030c130e06070c0303050c0304031b0507 76
    0x1030900010801030308410240034030303411310011104000840d08505860a40d80f80c0000380d482c01244212084140e030b1800141c5203034802c4d001460702c01405000c45034210340341c1c40f00c1810350801c1446502c200c450324200c0c6413558828090160500f04210044586900f09400c1c001131954642401341031017400e41c0000700041000d40442e101c2c0c0765540d21800c050342030601d2322045e0382087e48524860084da8181d95050358510f030307400045501c0c0c00700004060a036400303c0114940e01d1f030711059009140402101c1c0110012442c178005039001c07600b429046080c4a0b040c2c070030007020b0184000040110583e400294007a981121704a4001e04001e11012048000102070710f250801b0a450281908020420481c480c02414040108204105041030441002c81d54510304501d01c18490756004101c40c40400243d88120000d282610a03980186800704010b445003208d003004600003454040043c0e80002800c065a00550f071603502d103260b104074190b2a0f51500070442c000c0d0b680b401604c4000132152 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 512010503 1250 512009253 512009287
    0xd121808010605030606040c0503070e1201020403030e040c020604052817071109010b0f070f02060313050f1207060509010e0304060c1505331005030a0c090b1e 70
    0x480c1200001c10802d06003024141014030241c00701d0b00072803c22980c501403a410030309a80d4803240614011150000c80c0340024039039101c3c0081440603501c0020080149503201e05008180c3c20309032014483d45245810882c2e0f50b01c001c0b14040c190f6000040700c042d50744072440030301c903421518546210a0200075215a00c00001100c5001c40c2d0040001b030038002c00080364101750309013404a66124040d0b240c140b0041152145210000342c02c80d001503035100300030111101450b2280c001d042c80e600d17441e021141030320410043c0c40075505881014010740c0c1d00c03c0c000800b00766a815900c1c0782400c1c000e4a0752542c0203081c01401d6940b00c3e5407100005049803400300082d200a001c6c550b948001e42c4842d00f8a241700720030082980d04800e05240800c2281122030302203030300f6400540a40b010075240518001c21003890080a0b80d8002d0001c0d0382e9038a641d03441405540030b262900c00402c40c510344200b06a588900c0c1c0c0c450221140c4052088903846032008000501192408031050326000006030203c40c28 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 512011753 1250 512010503 512010509
    0x20301060f12060305031b0703050d020309130e0a03050a030f05150103111201121a040317010605090d02040f0902090f07080702070617270c010305090a020d1218 71
    0x40c1060349444a210b0b403042600e280c00d10050341c00c20a0300d040d5195541c603481036044038500304104044c202c1705030f0780802000c0015500a803d44065000c0c140c00251251300c6001030707034440d48144c0720007109550640300340300301c2901d0a8010007102c4150340c1c06407200d40100c200c580038965510b4505518003914090107204200c07080b82c162220100c100091b08403000100d428a8550b000c3c0210802c00c2c01c0458500c0c152501014205007580003854032005240f0100c00783c14100c1d100b14280810160050030184485a8200d0a500c0c02c0c0e80781c0304100c1d80c42c02002000d03075002d120070070381c0e00c05818154014850300b40d00030710120f00c1c4141178010540401040d620454280c1d4406c0c00c03c04840d6000042c603401501a04c0500a05440c3c040001c068003804105554090200404940045050050070138901a504480842071058461884d2500101102035001c6420b25000070360789036010414a070303180c0e4000c1a02c00080b0030380d1101c0302ca2b00040420b903424841c1ba40001303070401d14082d1442c001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 512013003 1250 512011753 512011757
    0x6040603060e061b09030c060310170601080d080c070312150b0306030f060c030a2d0b031209210f0a2307030305030c130b0c010b0a0f24110102030106 66
    0x3403c0964000010458122040c00130f80d1041c031840c1803a035400715106c0e0143c8401c541558036915150300310141010145d1182d15502302403521a0508240400d01d94100d8030b140c01611854522804159091101250750f000703041020020100068011a40d040e121002100000703201c05290210580049098107c149440307000f00c10051546020010016104048c0010f4030250820400001c0d1500001e440c403040140c0b140340440d4028507824418110280103810b41d5140905044004020811005103d0090158245500066042c170b070445c0d6040c1d90142c01c01c0244158041e902c401e098801c8550444c0b80035491100c1098981007241146c164041c450b50090309515130280400286000501c0301c46030070540d41040843c2d00402603e0307105960280d01c5550f0310031800801c00d1759195410404100c0c60100e00282c07014030550052055050580f40b241e141521101c25421307a60091003442d44055a0580b035490f6078892202c0e240f2094100c3c100401c02e00e04160640c3e0aa800136008100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 512014253 1250 512013003 512013013
    0x5120f10021e040e060907021014060111070b0406110c0303040b0910090b090d0f230d02060405030a030207020a0e011404180f0b07140f12011e030b06040603060e 71
    0x2100d81040c041c00a5442115076140c1c0f40c503180c1070381c00158983c000c14140c4030b00503810002e028030b4000c0c44140d1041c15042c004120501c61107082c24600c1d14203484143c0041e8448001c01030111000641c40c2c00e946038030420509007071600f001100c1c6052181e440c5032203400b80c038021a00a44040025101415100140d107844940c1e610602444c03041c440302c900100000201c0800c040340d1010111030304404250b440000752a6a41441800c064042400600f201c81d0f404045087d20000e20005140c0d464001c15201000c0b5055422030761030f142074a0291041d042000700d112018060750003050b0161001c4e00050055907100c080c0369450307000342d010301c030b01021540e080e007132030302d8140700341d080a072660b03d80302100c12116103401503c01c41204006003401c034040c3c0400c0509008011070070303080c101309441c103544e000c40e15009491b54020070501c860181756074002255042d1202020414220b055070b224210b140785443c1c15900d481d010701240c1e04203075504804004220980200030703c0b2982540181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 512015503 1250 512014253 512014267
    0xf0b04031103060403090311041b0c0b09010c1205070e0303130501020d03290a08010f020c0c120607030216020a120201270603050402120a1202070f0b0405120f1002 72
    0x510701c540d0100c1c506100303400c50701c10040002c0d04012044152900055120307104072a0304045401802002c41c55142c0902000020609540c00100060f0030342c41442020340ca5110f03901100c1c00d0325007004034907011910180e240304401e092a030040d90f01422a143c440d8408012102190035540310b980707900320315445240709004550b01041006402c10003407804001c55842d00c0000c12000c40400385040f0181c0e40002d0000c0903544003111080600540d000030000c1e20210300c0041c1c02503000e110034116601031040b0f84e6480c4d2400c40c0d801e10041c0e0304040603100c1075030b4901c011130007944030081e00d030102e41035940c540015848600320740c07020b0118840c008002a82c07500000d00300c0e13220070404401e10b5400c4c0004204440b422002c102c125410703400d0101d0203032a603200090b4040c43ca15070120710340c8901c2460b0380c18862a0760309102c08014540903584029180c8017068070318846801140c1c120703202040100700c80c1c00c0051310800c0b00c05410048d5203400e4401986a07042840302040a04c489401080c1c074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 512016753 1250 512015503 512015513
    0x1502030c0610060e0607051006060e040f14040b040c120b0106030f0e03040510020712080910050f07020906010c0c030303020406020c010315051009080718050a0b0904080a0203040f0b0403 82
    0xc0e9040300480a08080751450b18200526840021541038005e540109040301000006c00c06024035040c1d409007406482d032110340050521075001c000354070460500b040c0408855851103509a00e0f80ca007119840c0039601c9884010b03154002810880e441800e958001072070992510f080f5002500c10040782c5a40e5241c490002c06881072030003c402158980144521600c02c00802c80e030449009844200c88074146800990800b07880d580301b2021403d0220440040250500091010200440c0d080c0d2030b103485201d08503a80d000b6100c0d020700c0333680200021000741c42d0031602203602c9103052605501d80038555640c01900070305540114086030300400d0606c09683c0501416001d0002031a0400c040d104034020000d00241c00e2050a0051103516886001036200300b071143e01800c1141e040743c00c41a65440d0703a280300d071240209070304050701d40804075125242c5401039407050f0000500c1c04249813a2501c030300704035a0017408420150722003080002058072000380c03c603008211007c0483c0c1c403a843c600700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 512018003 1250 512016753 512016763
    0x3030f050f06010f030c0201060503030705031e03010f090f1b0207090b030c240f0a0926030306101808071d0408120c13080d1e0221041502030c 63
    0x1184903240e031000c0401000c0d0341d0220300012182070074500800c04130151b4000340e00601c400d41146405010004044c81405800001000040d005412610006031600c41601c1c042c042800b805d51341b1007003680100100b02052304240b0094800302d0000a402040000c06a1a40030ac02100c0000d40c201000c1003245515a100320381ca035010a030b002c0d0403982c0d00300f400103041c0d003103420041da804811060040503480400c3e007502c4080b244000701507502c440b007000c090070b00ca02c02e03c42c1038840808501500142e05134486544000000da00045046840b072004020550701860115410015462001c954403011031030414010101c0401030702200c0e06020380c00712648032a900d11028264554140000164894115081c104004058003e40e4032001800c0f000751040110024000c40849404a61060049a0110005416111a0b09054407024140c0f514450700c0d5101015800c204030f105492500c0b2030500b10b0980721003010610b0607442c3c60012481075426032911005030f102141c46031001e001044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 512019253 1250 512018003 512018011
    0x2070602040b070321020901120203130209010e011a090d080702040b04050c070b13080a0c0309181a220b0f09040501231317120702011b1d0121020703030f05 69
    0x403096203440341c0000041c9c1442c104c940c1d2605c0d060ba0000014150283c03445080404603802400061103594584036840050020b0041d246503004010b41142c00b500c00e00112184044058501c400c03c0e070040c2c54644064200e110166041500c3d907000301001c0c1d0f11071085900c1001130344085601e6807103078201700c480e00a0041506564145903041c000110382128140c41514880786080d4441a41c00c0c5070449810005501c203d81c4000001c601600321605134110f000041c60041d185901100510704100c117500b050745d01e0300c00103802d819200450707811641080b141d00318060524a40e9583c1c41c0085100084200c2c0e00380c403242d64940d4013695541030403654590103400070320998490306100c02c0f0940c1140024500910721600c14082d1546070b206e007001d5a400301c03a001401056468285001707030180103410300043c018402c0440c1091054040ca14007c2003142c076819054030060000019100c419049051442c02011220080c0e40c0b104240001d00340c9500c29600890340004010b518015190064 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 512020503 1250 512019253 512019317
    0x191b030e10020f04030605060d06020307020606010e0f1f090305070e04020a050a030803060f1309061506030606140a0c020303031315050105011b0201090f060801080f06071202070602040b0703 84
    0xd500e0f4030607540c1e025030301580c1e00502c00250540f10000013680d004207170b07075004105038000b0040100c529004601984648020303221500031641340010454048210704030b1075071042003030713500d8000c9020084100313207201d295007090803a498403900d43d10300c1c4c0515588a203003a0b00310b034810041181008a2802c008000a0754218000c5095580c0c280072800000d00d02c0d80100d0003010721180c41ea41d1140d03000440241c604041199030361900b05000608030f00798800b6030b81100d5000c0010440d20a04c01e65088615641d554800c3e09254459449245d0080800004000301000035001694092008601800c9200140c44014003180f800c407002d1010041801038080c03600300104610303608544030611561002070101c84603030b00c510050307500c1c0f0b1180e08441c15036181c803000821072942202c0001e043e5800002102d5408205000140ea0341d0000ca50320340006148048020a0140e030b40c0141480503c940000750030f00d034940c50b420b4181d1700000340950008611822196481c4010190740384501014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 512021753 1250 512020503 512020507
    0x50d0b0109060515040e060414190e0d0e010c150c080906130b0601200303270615120703050165090103080c16050108191b030e1002 58
    0x401c11360040c0507070700c134a44100d42d001c40022402c0e500c0f544400d031212040c03e507020750344c10a08520030040349100380404c9520320708503a00c0880f94002070b0170b88a42311070b1323030fa1100d000c0c1c280f40c011a000034441070215281300301c2c100400e400d11458016420035207007550300c0051a00c7e020301043e1401e04c014114200c59450307500c914001c5241c10b505554080400e007002c0d0407180c504107000380c001a603103002e10603500010003070168010344004601c10300b4500c912000300107100340c01c4042d150202030b542d076015240d98440d4440c150504011003210940d4140580b00d01c543c0d00c0d241c080c04d43c0c100d50805800602c042c81c00c0002030030495a580c45124200141c4080c0803d0050340d02c0307a80d44005051080100604030000c90b805100310046402a0080e01404065a403450010f991b030700506000310b60f43c0202010501d1401030842c0d030500b01c80c8169511140e9032141d20b0003064003140072101380041070701d44441c40142c5030f01c104595044070259500144880010f032006040000ca00c0203c0c0d086801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 512023003 1250 512021753 512021779
    0xf0e012307050a050a1b0b0901060f0b03060d15060e07120c0917100204090501140d151e0504050a06060602011103010302040f0b1309060c0e03100e07050d0b01090605 73
    0xc00320940c0c680031044e003821556401115010703501078010203072410040683c1003034241003022400500b400742620704024000e854403182d030b41100d4046400b43c2c0d444514140006a6186800301d40f1040e41030168035a58212000400100c0580e200c0f42c100381160b0031414280f2500c0d03039007c1c61141510005640c1000020402c100081820341644162100d900901104c1441100706118003513170451440400c5596503500c05400014140901c600800404012500000d50408007400d03035000394040b0603c03518401154804004101407140d41c1501c44c034050311225807444520a182c060340c00341004000b01201464002c0c10b54005400c07403403c590400c00349000b10704aa80959054a604940100d1160711b01e413000001808005403e40e40101030031076651903c1101c8d40118080ba0003800706000004848134182c3d442c48000c0006901544510400201e03a06507a11032100c400da07131016a0115959000010090310074250160b4001101d03400410900e06188940030041a01351210401801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 512024253 1250 512023003 512023007
    0x6060306011b0804151701051804080d020409020c1e0d0e221103011a0304030c06050402030a02060d140112050d0f0210182f0d03030f0e012307 63
    0x420b06204041030790144903410100201d85080d58040e101c0001e000340016482c0d240140441600070b402c91a51880100108880c200803403680488000c04407044607513100e0b40c0c2c49411030b40c0442c9143c07503480e03030030b100200c0e00e90f900307000604a29038241e00a01410269121810038008100403c0c1d103030782d21103281c074010303283c0240310711f111698112000a001c3d401ca5083c0381c40d50a503156440c00d000d10b00414078420441070400b03141610560b803201540ca1042e0300c030342e090510040e180540405c070025001c0001a030300b43c01450748144043e09550100d2099804180d85800c01c0042c44c076851b813501045c82c407210841c1c11181c01800199410b880ca00303203c0d01c8664035035040300060003c02520b0070044100c54000c11642d01e45940c070714010805039812840301015900c0b4243d08540e4100d031449607101a5800c0200e94030070846404015035100d03182c1041011032500703044101c0905840700e40d50340c0480c44604c15000e229011a001062185130010320302c030f0009008900e40010f10000c0c1c1480300280d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 512025503 1250 512024253 512024267
    0x2130303020c180a18020d050d080703020a0206011403010e010c0e120313030201110f062a120621060a0203040606050303040b0304020603060d1b15050a0c080a1704080306090606030601 81
    0x8106441c0c00505051801c2c2500040d0005c800702a40012054072500d0400000141c000d442c201d0715514000a81c541d101f08405034031035a447c07240164040e030010300480900c441c0750749000c800280001004060000c8450950306881c505c580443c04040008010703051001500308081d0040c0d001d5480c0c0700f00c0020654600318140030181c10000e0144820703403408010410481c101d6903d01c1241c14501c1c000454541804000c803c50000600302c9a0721000c0d0414441a68440c00911990754019aa141309000008440c0074215000d6030385104d44070000c0394140b140c503001c1e540d0300101607500e103424248001034810f13690040d802580100300812508091300203882e0099411a403451b500d454403000601d07444001d41015103d4100403190b042c40b02c0d484000c031011943c1c120580003210348101c4094034540141a052004500000c10100000b1100802041c410b01e182c14110581c11504078140180802124103c405510010a0080615000c014254030001c100c40f440d00d18900310300000d201c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 512026753 1250 512025503 512025511
    0x1b23041803050f070804030b0a02030403020115061709120f07020315090d030506060d0e0c0406060305010819150e07060e040903090905091e07060908060c0a1d0402130303020c18 78
    0x51a002c0b40f503074108203484081b02c00550b04190146001e08001e0000b500075841510118050b610300750341c0070800591440004211400c0d41c8440746140e0300c0d1854203c203020010501401401400b040b200e5140124015116810300c2102c0700f5100c00c0079105040c5054100c003405285030300200c04005580b000028100491040f52030702089a48694001c40c000340510801c81790543c0c14540e01001d0300308002040700d09210100c6060182e02c1e42c83c03000340d04a90082c010083c003a00704010403080c41500f18044211980709680a48015000d02101412684640c80c803800e075070041d020421032158068001030410008031800c02200e41c080d50041c0c5400f00303d1159030902d603160b074005031081c001070104d0840c002e0240c102024902500301c580b600e81119024200c0800c8080002241443d40010031510800000f000e041c07520070505800d94504040c8200895a60f855040900d141e44460000d880d05500080030b0b0414075041d0326000c3e040c012001800c50141da07509500d1107225844010140d08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 512028003 1250 512026753 512026777
    0x2011407170f09180703140f0705130e1510020d2a0f0303051008010b100513120b0f060105070c05061617090406120f1b2304180305 58
    0x92074207214034000e007900602c20481d034000c600c1356aa40c046a031020405118180c2c0b540c08100d141c00000501060070804d995048140844c6000100160f01440081c046083d0941c20461860795074941d9146040b0100d80c0c110314000000c1c02c08005041008625502d0422400a0304c002c0c250300c18002c1c000c3c6800c9882c1d201240c10001000c022007542030312b0160003038228229140c050b602d400c1c06009400240e80c08510007000c0781c400956900184107100c1110402801c1000781030f5410001c80b440c2e00000034207e111000c52900040d00c0000303000040500348034180e02d184501d4444410350340c020000b000e00c0e040c00000c10000c4009010303030341d2210954200312003042d1500c0d824000c01e4044140003034014146120400c1c05c49030101200e0203403c1c4030f8000c40d424065140c9581c041d170b2022501031001408806034040d04000036100c2c2d020800302a40744031840d00120fa4901841c10800c0350720b1a40650039050300740412640c10a4090350050590680002d100070780c09035001065407050441c4441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 512029253 1250 512028003 512028007
    0xa0e0c031015020703021005040602120f040503030705060603060a0e0606040e0712060204090506060901050f0a0e1e01030e0c1509030a0f0803011e05090402090727030201140717 78
    0x10107960301c22003103009003200340c2448454400b0308a02075603e07940e600003070b441080c2e200361480f10140700304221000e881a41d400741001d4080d024221034560040e403841d010400041c4000b18440d10104040e01046010b98010f0005081150515040c040042d1032007941c1c50030701c40d03007100004000442540100007690001a00c01142202c6803d04d000c581050baa5090b200c8240c0c0c0900582741c000e40213072400c0b08420401e1341c6440c402c204c0d252042041d59808a181480184003402071400500341c1d408242c01c0164904200c800041d0709000c1007a80160000704015050000b560700d403158400300310001c001840d080312410300091510007119418101840009007040f5142c0f4140401c1600650050440004c0c2000d45000600b541090040d040600c04824400100341d410701044011141c1c068007a0314a91546c3d02480501c030b1004040c03134103000f440300c01048446650360b00440f00c000c07400c010307800031400d602c0014512103586061548040052000201050401e401c940505c1e9250400716 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 512030503 1250 512029253 512029261
    0x20312090714130e330f04020d0618060207110d0222090c03030206010e0a110d020d0212040b01061407050c0d05150a0507110d0f080a0204050d110f0a0e0c03 69
    0x15004e0b00705440d49840c1d0303004009800d801a49802a01c03084500360b0311180100c000751200e80c1102141c200c9502c5c0c00349503002c002c50090701f08100070003000c0e4020b02c030100c0c2c0b06101c6074040130340781c5a480046a416500040003401d2144c00c42501001c9142100c12900265503500000c46110205d43c04021080d0740d6821120f0b1141c0d01d512074518550301000008500c0c5e940c2c107010392101c000f417151115829841740000e103204028401c0710f005c0202d40e080c450a2480d5504441c1c029001111040b00c107a030f0030071400c94001101502c40e0310540c880e80a50141d51304240008240c60000c1c0d0410340c6a407814080c1100013103010407458581c00017601c2500020300b9a0030903514101c1d4080d0441c0206090f107081c40040242908541c1c8598020303207462038500c07005d1a1581d81c948035104404006031550f01020001ca200d8040141c1102c0103040c094100340d00c400000c3c400542d0103104a503002d5842c100c4083ca4100a080c00100300001c40d00c04c1e44451900701c042403800070080400c820000b0000000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 512031753 1250 512030503 512030539
    0x10306151a09180108030d051005040f0903030b0d0f0809040b060a020304030201090b0c06070e0a180e06011a070b0c0714010902090604021804050c19020312090714 72
    0x4400400e01c0820152114511100d40078a5500c0380520314040d28000c0305030350741400011111812a003016000790728082040b60214000e04001c2c050075200700e08084001240d50301e60081340c144808032080040c0c47d888601c1d0180c00c4801c1e55518500075041c0c292040b01083c003180286071480d03044121242c6d24416500018010109461a10b40c03010011541c07988043d800000f6000b1340e4401e0320713017205040d105d8070204194001c0505d00d01440e4410400600700b80d1251186d0808058040d298201d0f0729114042506105c142c3d2050f8288580d54141c542e8040034104080c40c0108946884e08a21a260001c40c10b144c1c410b4240141201c003c17400481c201001c107800701c450981d004455192850001d80282c0c1c060030500f2026880b0313a00000200c7d200c0d04d05442107640c1c2c0f21000c0c602e940140050010b200240c48010050301c50028281325403030001c00f13640620500e40c1c1c0b0726030246551303140900003111112000b40c040086948030003801c0c010300101444000800c0c03801c454000410362a1018 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 512033003 1250 512031753 512031791
    0x702033712022517040b180307050307230603061018050d060c120c0f0c0c05040507030b130905031206040e07030b070e0904020d120c1a011805040209010306 69
    0x6009103441100780802d42a0f18003090480c0d184c8140f000e401e20304c1c000000402c00f4010340c094040c1c613004c10020000c80b4031039880c03280490798000d81515001a0790f040000d0800c0c3c102d40c0710500000c840280104500c001300510f910605c41121280d041d420400042010712800d1100306043c04206003560365820a03180415006110081642a6100552400601800a10381080c0110b41644c503125100f440307034064203116801940d5645207640350110211807110940d4810365030b80040c0080070846444500402c1d1082c1c04503107011440014810070b10141148040d48109160300e0517141e0000510040200d03403075020818004002521420000390003010030080a4080340305001d0004204002c0302e000c1807103222240c4840343c14044181c140a400042114001e502c5030000c0c803000b00250850340140c009070307280e2406004000650f03a0300b4495120455070381501041e0703403004000b5003500e02c40301030a808401c2424020342c14540d002c5619043c040c080206426255503558690b500e0380300c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 512034253 1250 512033003 512033017
    0x5010e1906081207081e0406080906240103140405010504020901052e110d0c03090605041d04051e0f0712031d04020d02041409010b070f0f0206090405070203371202 72
    0x71000000c01b00003c40f14030640c414820a40810b5480002440c01000030611900c41d02c10160740c030314040c040c0b0010b90445480141c080d07041c140e450302041e01c4c4203c002e110901c1148200000036141c1024010403100100580c0814483d1444103181c40030300c840d544066203041840303180044030303050708181603450214000c50044548110b00e441074070b50346c0c00700da5132028030b0107030f00c4042d1440d49400007103506116501649581c4241c4c2d480030782d075130182160790076400f0340200c00341c3d10340b8000c1e0340700c0301c0d09012404100002a4482800203420b801c060004000400c1074460728600401142da0103064044400407203009203081c40c000300c12a84407034045511207030000008541c1e4603141e1200c41e030310050018099000d43c001c1b800202c0d292011004459805401501c20400f103822070781d40c411b400c84145800c9801c40b10502c0100c1c4a51110f0180600650aa40140d62100510040000c08003450248178035290143c2840d105107049094405c2d030321507568600708094001c18101c0401911401d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 512035503 1250 512034253 512034277
    0x3020102120a021c0203030a0609060f061107050406120501060b0a0f0804031106011716141504090204090f0f1a06090a080709021c0b0a0909051005010e190608120708 73
    0x4e060184801c3d804001944640d80c1c050b010044103850f520356408698072030080c46600000301206004050182c000d031041d00300306004543c08540ca880c007040c103440d6541c0c01001c200102c00d43d0101000300a0040d01c0162007426040c90400d40e0f808001400310320030000d82d406011851022a007810b01c2420051440c0305110308807000c40d40d503220b01d4640f108050701500c1301d5002c0c0d81c0c1090503c0d5800034008080340c500b0361070030313221190040c20000070402210241401c1d041c100400039881c4514000380005001d44840059048211782180701528034050b541c0d200d55140000c000ea65000047c0da40a0707141c0250b8255403a4021400421000d00240d081f41c0388601c20f600c0000f4565010341c00420000300800750080d510990299004180e0b802450507039400124060244003000700740c2d00a0281c0350140c0300f228807401c2e410310802e0032a0001c0c1c201785420b18a04041100c00450880003061030120b140080203410724104000c3c0e1507051318804404e426800050000078002c281007559500d200038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 512036753 1250 512035503 512035543
    0xc24210a1812050909090d0917070e070c0f050c0f0105033108030411330306040603080c06010f12020a0b131e0501120b010c021210060909050111030103020102120a02 73
    0x75035001f40d035801441202000103000380404103140286501e0b0151b68a03c4500404c20903003000c40d0172020250040940003001102c0c0c20601c003042c80c02c503800040c1401607026201a580c10000d00184050744255541030180810600845c42141c3e00b251000401030745902c141c25005480d00104640b50402c040c004c020007005220604c011030b41c0c60707060543e049802c1071041c1140d103000c11209a1b24074444248d403031071000c0048a803106034015648140000e000045250f202d5640039080d0704068600009a401a0014010030360300c002510042c207030244407650450516800180103469500a0a001c2000492120344030303d0441081005064200f2103400324400c0e05442c02d0415845100d101d00040307920107409212001407044030036806041c2c4d10a9210074458090150807206604d40c0302c443d00c2991001c0d04000060b110b21070150140900c041080d82d100d082c01803d481c3c000048000c0c20008100400050782c001801d0b0401c4c0d415050b03501d845440c1140e080e0300b0321502a41e448200040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 512038003 1250 512036753 512036761
    0x1401030e030d060e19090b01030314040f06030b040e0f07140a030203030c100f05040b0610170c0705240615120106170708090c24210a1812050909 64
    0x14000c1c0c0d00d48a25a074540021500e09480317042030594075800c8024010803813a00040c07010034410030816031102070110106140659a444601402200e030b80b0070400030f60390714545031481c5401d0281c40c140c0d54a820052541c8000c440300c2540780c403c103114081d01030318101020200f07a29040303801b10003190001c007500d8403010455482902e0701684013104e01382c00e240481c1a0ba001f407041c403d5074051a0000b0003040c8958404e4281b007800301000d5102410302280c000c22501d020f09120007180304070b00c068801500c9a4070f80c81c0541c6010721205c40034507a1aa9114441015140415a10f90001c0c08541c1007024144030180d0751070510820303031101c45280d00c050010448980107075100c40d55610070b1400c2ca4160f42c42c0181110410704c1510086241d40004d0404605858900310100c0342c928403852103100c200805a03195041d62081341480704103121410300c0501c0c011240042944010115000d2000c8085031400010310484c0c9100203010480841d2507080d82881407055444c0c1c204c000d0140801400c2c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 512039253 1250 512038003 512038019
    0x1d100c020f030f0301060f110a0803040f050d0f18030803060103020307050d0f020301030b181b0f0d0b0f090303070e060f0d0c08100807080a021215040609050607091401030e030d06 79
    0x100074000c08000c0341e000d204141f80148521140c0401880e88070240480803d940e0b20f580c4140e0020704259a1030041c821540701080b028080b80d08001017540320950410300208014061040104014001e80c10012040011a2028045990040c024070f00181d403541c3e514400c2d90b05020700001008800d18103c415482030b81281c0c0218140c1e4000c01082c1e1483d654015407a5413606886220540b42d00015116907905c2030501081070785000040c6141c0d41c02c01c66402284002440500507140001c01c14140000c81c1032a9008581000408024500d5490310079406864411000364050080300d0000c2e012034220803440c00da4030001000c000c18020f400306680014522038050b44c80d007003051845800024880c00008a02040b11200409008508910703000c1001d04440700900c4004e5001d55001510100c0d181303052144260b21580c0b0000d80007880d4100149086c0300240741d4401e002c40400103106034683d10b41002d126210928010501c04000e03e08681940101c04043c40a141040c2c404101d42e4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 512040503 1250 512039253 512039257
    0x1207020a0b040b0a0f020405030a060b04060b0f0d110a171b1605012706090503070c03030224060108010306020711031603050c24180d030c061d100c020f030f 69
    0x1c050380284401002214108207d00c03c0b4400d244d032551200d080c0200065060b0003a5071184001400090507a0343c503004c0741f0035030748000b0340c0501c2c0c28800160300740d040d00c0a210345605905030100041c14840104070240c042d92038110803904002560000072422003041180400d0600c0300041d550700c94400c6c191114040201030000c032481e500b4008a4202210741d201d09220300160403030610f40c10700d0390b03440320001003207503040980d40d5010400042d8041941803800d000158400d900810700c40355010004401061440410500d880383c10050006685e885011385041d290402e00050b070b1083c46190070160340095460f03098050241681c048400321600240300c04a034010402c0c0c8090b040c225040151740300046408206200100549510308400040074041682c1e00c01c2222800f0700c000d800103502c0c0000c44004400040314650702004000300d40c0150000301000d46113030741c60104040d5003680c4880001011b2011700d41d4541001c800c562080080e03111070000601520b50303581c40011155265 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 512041753 1250 512040503 512040511
    0x70c030614180303060607050c06030718091b052a1f0e0a1124180102010903021c0e060301030b01060f090b04060c03171008120c031207020a0b040b 65
    0x1180c52107000940c1e0045101c480c2d440034000e100030b18034640c2c80104000b520b41200c1004c1e210762064148207071a035291180258001c000c2030300d400c040e4a5945903a0040302c0496040000900d0034030081040101000104040b0038480d401e0068072071000c0741003890103030200e5052680b4200070404078001280040317a0508180500d958124001e421b801c40c690030794000304034100e80759008060303410200389030854448031104020a04c005031651034041c034000d521004c00f02c0302131003c00101074003440c95605080c80406003c1c0002d0080384900c1d2406500c1c0c000d8440c40c54444000307088006800c81c0715002d54030140500414694580d610ba080051a40d6000d00030311003c5502000160300d00d6000d00c0501084540243c513041c5043e081038021141c4000da01801c801f801000d0030111400d04403482a94803e404280700302082e42c0ca0032010038074042d043d450960035240d040064540c07440d0040101c0361aa1511005101c0e544c542e000101d10f0801980310103000d400003c81481308100943c000c040c09 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 512043003 1250 512041753 512041781
    0x2090f01080d09080a02121e030a02012909040501020c07030b0604200a0c060b1201150b1e090d02150a030516050d18200103060f030203060714070c0306 67
    0x31101038003030140d400e43e105000d9103403968403e20043d0010300d05148041c00e42901c0c141555004a164401c102c0d4003e460120849950000b140310311003241e0900c82c2e0040601c00c3d0001e42c0080140001810054240c803501078040c01c100390008060080940464901024803000c454016590b410010759585040c4c420b280314500b00040807484580071015909020304180d9480c4c54800c0022090b0b4500103200d0080f690b064840380808020750390405141b031140882c4002041160b0783e050590080b0080760408140c1d1501884940c80129400b42da40c41000c40d000022135a0740b5281c80000e14400e83d0800007507001400c041600c0d124040d250290910400e030b500c0c248000d484504507c12107050850000340000d5003030103074109203d403d4000d6410b800117180d42080c0e00b0000d4503160b003c44125145d00c0c800400c0c8800942070b03940c2c144103000041082c034a40014640c216070000b81c0303c5070043c16039010840141004010740c0d0816040390710782903021810041e12503903490200301402b0351480d1200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 512044253 1250 512043003 512043013
    0x3090504020708190903050a08120703050c2703030d0e0f0601150f031e020c120304020a060810090204080c0406080f0a120e060309010e010c02030703090302040902010c02090f0108 79
    0x41905050080d6803603107038801e40f07003410b00394130120250850300701c1121542040f11440001000c01c03414030003240f0240c001c5080307694a8044618100c6202c00c040d02400c20580350030704002980740d01006a44900701b540302c0709aa200c060603294000c90001c0e018065041c013001802d1400d01400f82d100b0b189801046050f0744000d16a80401c0f0349585003440b42e1f00010410342074900426114101c640c0b104031941c200090400099032242c0c641030381a0740140c00c0f11768006041c1c07002e01010000e01c80030640c03103030100d4a94580742e8045100c40c0520701c030710403c0c0003054021610351683e103282c0342c001d086c1510f03045440d260f40c2c4282951700c00741e008466002e1807421501040782d460224061650150751801022800041e40d5444421111200c0003001c000d0754000c189029075400e030041d40a00b000c440007050307480ca90040e25086803140e070702800945d40304119140007c4c0d0019003404c1100d40454000407450b04600050300c0402143d10001d6010040c6001c10800241042c94035060355856800ca031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 512045503 1250 512044253 512044259
    0x210306041103181c0203030a15030803090c010e03070305150709050303070f06050a0603080913021b10051305150a180303020c0628020d0b06040321080106090512010b03060c070309 79
    0x2c002804e814080c0d8005030402c1000500e1441103070400b805038282c2e8280b10000d039545e80c460741401d40003600c01007810b8000f011300000c10342c0d00c4040a00034420490140042c0f51541c0c1d0340030b50700e400c4042c809031120541000a0f04090251005200801740a810341e03a40b03107406d140480c5526550072044410701c4c9000c02088800d02c80b4816a403d03240d11090803803405611404000045c43c4140d14030780100d800b00a040001c0b04124284046158038100410110402c1d244840c00c0e250300800c401e103a51205a00305000c1180015401c9400000144030020b9494407440003001e08182894202c80c0004480f4070000c01d6032544c003d02481040d44165040d545924003215101e80402c0300c040d500b072195074501c01d00c0b080b25600030310701c031002c11900051060420002c00d1079a0040ea0080c0e171003991440700c40c0c60408103d0243c0c4c802d12150310b031481c1a0b605000c400380c070f03800b0140960f5004503100810082464025030140d00f0303907c0020103e9131140f90402240400303510600044000580c180d40c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 512046753 1250 512045503 512045533
    0x1806060512010b161e1403031303050c0c03061006170106350c040617061e010c02030709050106030b0a030807020108101806031421030604110318 64
    0x24a250a0030100544116440c209000301640c0254501c441340e5620501c2d072070001a040360303200624115054040e0850215418407140b4900020030982c0d850f00100b0410000c04d141c1c9042d403003195450304065444440c10b02031507151241180d11300c0c3d094410707201800706c00103c0000100869142c1d580b808660403640741c1d2407031290703404c5c40b801d40814418618603210b04400c0d080301c4c09054032028002c8190130a18072510f9070003c103440d0445e49040006050100d198040d144040300b00c0d81c1141305c3d180e07040142c0800c1c0440205508103100d040102501e100aa10526400200395001000c07070345442c1c0c07144402d100620b000c2c070402012a10306120700d400d0303003400310851003200c0e0001407450800c03030300350019144001d0084c90700c0f0141c106020b010403001c00c1c802c610000040315800c0080d143e070840c984075078412042c8405001d10b51052900b01c1807004100400041d140c0c956036050707165140c03400864081c00ca0144003030011940407013040700e50644590001d014200c41c1d03044034100c488240003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 512048003 1250 512046753 512046757
    0x5150a090b182d190c080c030a0b03031309050106092d12060f0501050d0b01090c2106091103010b19050d0212060306010b0c030d0908040e0103030c0606080d0207030b0c090a18060605 80
    0x26201041e450000034260788451f03400380da840001144042034600513a0006401d55001b913007000300313101403c034091099524520445002d007240d418450403c83c00d090920707522000d8490681360a98540490205807440f00715010300820b0840c4010400f2001ba2918002400b1071070b414508003850070300005a18500600131070040b90b00a0108092039007030200950140c1580c0000b14140400583c00380100700610034035442800d9000c03070000e429418000e0302410b27110501c07000d400250043c001806514030f010304480c07001d00020010103403203400381c20507a0b440c018100c81c200ea440c4081682c052403101c0140c00e5108410460684a090f07072500411010350103203a101c94803035801403198070b030051a60b40c814400c01e030142d15540d09195841c1c007007000600c000d0b00201c0001d41a4000390303040000b5400f0b03c0015040e01d001425082a40c1080203548003428840580500690000300390b20038000c0c0c0840700069406028200e034151075440440c0344005d048010b1403445e00c0c181000404500c1981 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 512049253 1250 512048003 512048021
    0xb0c0c1002160b0603120a02100513020105090f04090c0f05010210090302030a18030c060314060f031009020607201806030d2105150a090b182d19 64
    0x240030b0501c516a91121420000b00900d402d41510402022044000c00440582001101170f80282550544982c3c07130300079984054602c2d01058049240c200c0140e8005090b20028034040e1003002e545008000024058096010040c0035841010760200b0328003007001200b401d6800a8007180c17880305010800f042210011000600141c2081c80600900b51107900207002407040310152010180d2291600400700c20180d00000100c1e0799400b00440904c40381441c0c6511000444034045029030b81d001080c0c44060800254515642e284411411550780300152101140c0045900301e41148a0f01202e21014150f41038a00c1501d50202030100d003640d840b0064440d00340540030b4461000d0b00001034400c00c00c1e01c0e00b041c855a10101d10080406020b11580744a24a11111002404c8101e410300c2803c41243d0007080400d030605000416a485045006070051412040105643e403041c5c408141c1c0a4801c94440300a5130501401c0401079401c240706000d400180c0300382d00c011a1190504044444005d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 512050359 1106 512049253 512049277
    0x1407030b06010521090f0a14070b0301120b0c09030141061003180b041e0f060b0120060108160b0f0c0a0b0c0c1002 51
    0x100e81d4010600f0f080413407030460007803a8401100c00401a400b5108401e0021400b01102041030514140c1c403c0c0c2070300c03594881464540501c400e030703145ea0b0000e4400e0450214018603440101e81c100c030203204c82c925503000a0303901d4201c0369900410321a89200300340095941c0391420f000e044404448100c0040c03030b1001040c204404003085200404003825020700240d09581083c1c4081e4000740212081c102c000c0700500220080d140c4c90040c9120140820140f8041261070150b0038000d0784982c1168020701c0e221540b4100c030782038010014050704e0141e000503001c92070fa030348909284c481c1071624131511041d0030b29107610311103034054070f01850307008a00401805506200d50b0f00380030b0301d00e00c1041a0900e4080010128080d04040d46048071000070128041c4008000020000d94000f099141070700d04000d0000e02c54102c80c069035060f00070740c0031580b030300720661003141c0c4070050312 = true := by decide +kernel

theorem cover : BRFrame.Cov 511870503 512050359 := by
  have h0 := BRFrame.cov_init 511870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 511870503 ≤ n) (h2 : n < 512050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
