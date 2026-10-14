-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2704
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:45.703793+00:00
-- url     : https://prove2.me/submissions/b17c09d4-ee39-46ae-83b3-17300f845cb6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 486151079 ≤ n < 486330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 486152329 1250 486151079 486151097
    0x30a0f05010c030b04061503200d0b030c09060d060c12021b10020a0507030c02060d02030408030118091a0a3b0601060503041518030f11010b101110050106 68
    0x6405205280f070010060317800780040d034030f401402c140c1000b0104180c42455141e80d01c8082c2800e00d5030b102c042509440c1c0c038076516100381109036401017440481081c040e10811040714180d20700f003c14107119100c0205244081d8405640325800341015070802d4003400380c480b54140c1c04000d50b0002d06800680c80d04c030060010604200710745000e40c001100080349204014070703260158020100e41c3d4164060404800d00100d901c0400c00d00d200309014000d16910100500c8200311309403008504039505040350924040035813030908106c4001c442d00a1412540210310102c000c0300824060784081c01e880d00240b010241d11007074007000d1003440e00303400180a08040039060041c41c00c8003251410740d1710040c0380075030500401078034600c40500060071a40f51051010785200c000c0c1c000104c4100820021134115580340b40142000042c0240c03040494041480c00000e480148140100000000d2100e00d0a01e071085040d41c4144549101507014081c10440c04141c0c40310380142d50081c08196103403800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 486153579 1250 486152329 486152351
    0x1141b09130e010c0e0105040603020a0504031a0108120313031d0301090506090d05130e041b0303020c040b030a1a0c0c010905030405010311040f0b09010e100c15090302100b030a0f0501 81
    0x3140c00d1604d1450510203000d000603075690b800010790b015200355040059481c8009001900d4500175580014112400d02c061142c8400e24041b049048490200c01c07961842d1480748444031343d0004640c021131100000050002003481145421800307170f501111400a038820300042400d665501e1819035841e8010014007800c0b01c0304003d8924010380a2504505200a5150118454145210b406c10300700a40b0081814004184030183c000d85a560704d02c3c0e5456a6494081c3d00c0b00707110700d1030787d1040f440c02c50ba42019080c0480c050840703d40c810307040d012034100c511011038908409480003144203c113008221107514240724001c2e299016800943c0c03150310388400101524070030f03061420754803824001002071407a106c10303220560702c80001158950444100407624558904030003a405641c48801d00c89940e002690605117500030488583d484421000740c01c107541c03104c02c00074016803100b80c0c0603012901660004426280c0107080e550b825226484540d90460303118010b443d2650344030341d0700715 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 486154829 1250 486153579 486153581
    0x3040507031101020c01080a0c05041d01080c0d05250b040f0513091e0f1203021e030c1b0a0f0b090c010201110906030703110c0109021201141b09130e01 67
    0x2c405003440100244419000024201a00a0061003d240d100c90810003124056020b680c00f5240e442c035145d0280c000c24180c02c078403c20a21405e001030140c400d40040504065421128058110004244a0880e1040720004000d012110808a0070056021031407841d214010f1001f040010b40701d80800b800c01081121000c00500126911403401c1180c074001511a250b180c00044452100083d00015050002c0c2003c03091100404003118420300710002034240d4041d01202c16030140250340c58041b2410341c24140310542c0c1c0010b4008052051130003a040d5010300e03080c19504041681c601450565078041401080d99045031050b103070100b0071075843c00800171000524400d200910109119102003407039031161610150040400000240d5018020b80148803000401090282d84514034074803e070007090300f51400c0303100d02c1600c4991241c2002c14052210307030004580134892961a1380201e000c07000394184000a5151007845185141d40d90015821105180b103000800c1c003090481c040b074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 486156079 1250 486154829 486154853
    0xc0302010513021005070f0b010e073e031b010204051f08060f060903071404060603020f16020315010617130b06300d1b03020a02130b04020304050703 66
    0x3169018500040701e0140ea64002e058100c42481d003416941d510301e07810080a103507d012806440703007220400001d61040590700e030502c50141070340c40b0121103c903403d0301c102c0e0101015180342c000840000610742000400c2000040c0c02c160f80450749081e8280d00b0380d90900d11400c90901150b58007080401c103034140306545880184402a079140151718415015110087c09082c40340035080c1c00101800f00d8a90f5403c0703d5081c10010308031b0301150340d1580310104140c980e40307407640920b08101c80010342901900940d143c90b00764240d00c0c0e040c00f04100c807903c00c0c015082416a410301c00e0b40c806622238070740c0145150191801d603554240020142c08091040e50018020b501c40d1824030301c424012030006d0071000c0e008642112142e2090801001e50040c81c2201ca4181400104403425090f0140000640300240029900c50f85010010603200400c1c5603c2c401c1c010303000d030304001f07002c00c01858000d800d04d0f9644240580055040c51490124041fa00b085400300c542d540001070034420f20045207640c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 486157329 1250 486156079 486156091
    0x4090c0203120708040c1e15030b1c03032408073002060c070e100602060103020a1a1218010605040c0c0f170a02060f010b03010b0f0901020c03010c0c03020105 70
    0x7186428984a111111000028840340420000c10040340030000d0404104000305010001c0c1c0d550205051940a00c1c3c101600c12030805541503200c200481e4040c0c0101d2a00160040840101c044603d401c00c010b103c904008508241e0740701401030f010303e10002c1101841900b004520031040c1030040041c9400c1c007640015000380d12541c07207000801d040d540c0150b1103902c42c202d9901e40129a00c0403c10030b0003040c00c1702c0309034040d42c3d0011440c10100810948210107000304160b50702d584640030f030b807145400e0201940000350b0440a10060800b00c0440f092001d600c900c4a00d0700c0c41c07410010003d818165207011700442061520540580240140340140004a0301040706401000020b0020101c1d120003d10b0403084c90980400d00154514110f040c2d640400c01d5076560420150080d1146400c445084412980c02c3c0082583d000c1e480649050b03515500c003142c0303400032250790000f090b00b0440e5001c0c1107100f800c241140c152404c0c000c030007900b0312540303075080070140c0d030b00c1c01a09452008000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 486158579 1250 486157329 486157333
    0x131b09050a21080403200d240603080a03020d1a01080601140d150e24270c1210080a140c1207090b04090519030203040e0f0703061212030509030c070b04090c02 70
    0x207204041058004041c17102c0f0f141c0108c1c003e071221000c4000c0080e00c0590720250030544d010070300c54035894150b002001c56405d015405c009001c9082d02150f01803e1a03400613000680c1071001030b00d65405000000044094030003040e0034159580558426241c000010840d842c01c025801c00114011a162a400c4212040615108401c101000601012110321144111071041008503001d01d5a2240c0c10b8400013107030120698a01100c0040c1c048d80000c010071104070300b00c0f0000d20003440341201d84060712100c0e03020f0200d61541d9114104071386003900d400300041c0600e112803031855440100c5506a081c0050280000b07a140c03007111030489480711402805a070400f042180042d60219021401d4003c41e42a5000d802103420b04030319501a030340021050340300b48001d0085168800303840758401c100130b0b5424070105031141c0b000c000c0d044004034000d00c0907182d04441c400507400382d00002da0000b2944100c1e41003580d03084056103410ba980d4440c012100e00060240001c5815006461188040d400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 486159829 1250 486158579 486158599
    0x14010609050a1812200309100f050409110d0c0807120902061902030c0d02010b0901060e06120a11070804080111070f20131b09050a2108040320 63
    0x103640400106400004003519085140302d1361032400307000920000541c605c1e11040300013a41c0344540e500d42c403541003184582491004514800e100f256407101503066562906d0503e403a00703aa0402602e80e09026040140303007849030005030815803180c03000900207030740c9004960a11800c044e240301b880b5401c00e50701c2402c001c580030150312024119504101d18128200110071000401c9003140601c0421016034001d1601515034945d0541000307000010854140e5200d990350003095480d03400320041e05812200c144882d9241220b060311182d400900d206001c241d4110701102a80f481e84807030011150620085014404081d0074858440144120000c05107071018070b0f1104c801045810600a048060350109140403081c141082d02e92900084c001c501400e811016980143c006c540001741107000690203203101c6846001102c08075280030b41aa81c0040c103000d06442040e50302e1545507201c4d25981d6240000a1103e00280019801018144168001c1d080c0220341c00e80200c800e2840746080d10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 486161079 1250 486159829 486159851
    0x20408032203141b31060905130302011b080406020d090507290c0c0d03020a08040909060b03010501030309090c050f030901020a020f031c1a030f06010f051e01080601090314010609050a 81
    0x400030a42c5e0007640301d03c007034000302c0c01c0d10058041d042c5a0849080030341030405010220344001561b500140c480c0e002400301101728482050301350343e080310000001e0380c0ca402003404200030303500500080b86106c40109240c01c840e100d05152580744c0e400820006d0b44190100d200c0045403440a005003209402c0901d81540000400d41e6a00c010721a41d1150703a80e10080000c050082251060841e88a00f03600d480340da45811210040c0302c1004180e41a90034034020158518040c8070f614103032a8152900040a41806060380042c05015120300c1844010000015440c0c2c00d607015501c00e0071440c0c00036030b032171402c03400c002e0401c4116420206e565006010301c0907420304030519046402c184184c001500707903068002c446000d2000c0c881e82c0d0103011362031000e9032032440460002d043e0f9852030f46040040c1c0c1c1d10024824074545200d12040e5200c4880201d201a40c864605290081c10526140719a40d071252581d030000155480701140700d84d96080f04004513203030350182a034000b5011404107c0880d1031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 486162329 1250 486161079 486161119
    0x9010c03061a090d0b01094b02040506070501230c19030209120d11070506030f0702070b043b06040905010e01020a0804110301020408032203141b 64
    0x1802c25070710050000301d400c074866240c0c04095004182c0091074002d05581d251044801440840e80760141080c038060300f50088200d00101012004904c0d44481c8000d840710888108a5480c01140d00389039000c02c00003407242d4940011f080918007403000051100c1505078a04160040420f004a03001140020030025842d4102521940d25040e070b41503100d0000c8290440081c40340040322035000e18090040b080c1404001032100b0003000a4440400c3e11881c40e01059560460b481016800441000042c0c41840d83c607001d1504084c00e801141c1e4a503458070340150700c1e500660030600340f1818400e40001c0302c64910346044002200d5841058080d40c90b1285048840802040540900e40302c4280b8003c000095102c8139084c03804074021504d900e481c60300100315800c2600c01f80c1e103d044171000e4030b0180c42c040c800c407411549480c00440ca44420003d0000c500700a001140b0502c004e24440003000c18a080009007c00d02d120015005d041e20000c0c5102d809946400198044c280341722031131012803c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 486163579 1250 486162329 486162359
    0x150d05030433030b0a050a06050306040e0712020402070c081507022b05160c08010c080109020c061b0c0d0305062707232b0203060f010516050601080609010c0306 71
    0x3480e01013000701e402c002141d26040154400c50704408404400211580d00401a50050108880c180301c141c1401500da5038580907401521400c50390f0700a0b041c010310b8164010608144500280c1e10302d156a50851800d02c942074507624034151108040010403981030007580c1c80d4417158607034280b004005103218403084441c140c19000303001d030024540d10791100c0b11000360382c2c0561088044885c40c1d202c90085001e040e241000314007145213107001007220384041c000d40745c03d0110360f001014103030382c0e400d040c414002c501c1003002c08040341000789501454092010107802c4860381c402042a05204040c08207070f03100c05d00080b01c2d0000350000994014403075048603801041c6454408000a072514010b0400040102d252016050001d02d8140350421002071500a4429165542000244902d82c85c2071b40b10417039140c4d0380005001c10b420340e1580100054900f0003c00c0c8099141c21810f940e601e480e04000b13802041440c2e00080400a09403001d000341c0200810301d00d0140240c030701d00b14a144840c80303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 486164829 1250 486163579 486163679
    0x615080f0c1207031b03020c0d03060e040206071703130c150807080702160f0302010e0d050a170c0303040f0c06051804020a0e03030403030309031b021305150d050304 73
    0x200d64400f255400c1d11a421884100480002041c1300b10b0040102400070f5005182034015401140072001066000384109421500082c0c50000d9075519a8200040c540c41000200c824081b1101c035101002c9035000514850441c96031084e0008409041c07800303646039540d1210000b013802c1e4121a482d103511186441d0404203d050104003034889a40503401c1c0440d02c841c0303002408880000160103c05403034040210b0f4001c2e2114400c3d850108248604001d000c1c0c0c001d003041d408125000c0c0000c4011000500013060544001d042010701c0400707900355401500c09a44082402219209010340003505c84010030f402c0c10700528000380d1500000b803010b030740242207100e0380d8046810b000040c06880342039030020004042e6a6030b282c803032901030001d010016050780003944590090704011042d9500b80441c5070002c003a2a280c0300c0e8500c40902030324000340305240b64401c888902c4244d8581c2aa81e01010f84114081c5480c1c5003000302850100d212882085440d00a080c0401811511070b1004280d0310 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 486166079 1250 486164829 486164857
    0x503040b060a030f0b0703060b0a090e0a05040c06050a02010f1415040b0102071e1d01080123060d060b0a14041b0f052b09021c050c0402070606090615080f0c 69
    0x6d03403108400e400800042e400003102d00c40009913060358130380c07120241080d214034441c02d4110303480d21004081218000c4400030312840c4038110030b202d003a00039005015945520b10000c985504498441c6007540d030040e405c030b1130075401d03c401d200c82550300240c56000400196803c21041c00d155000030b55450680c030611440b2000380110780315501c04903400070040c1c01d94005580c0c00d551425103c03201005c0912620019510f000e42c441d10361800314814019682a0040e804482d444107000c0040400700508204d50f22a030750142c0c0e0223032752640c1200400070410f0090b00012808680d05000541d443c0c144000c020b4540d003441c41007041e0300085050078000c0d040c500251952a2141890b11805111401120000d55000f1452030380c0b40e01d8000b00c0d981442650400c0e42850301c1e5600c0c00000a034841c00401a4020340b6850038503040c81d038003401181e4021a004901c26564640b020f04541d400e400ca00040e4420381143d43d88590400c1d07946402c11110580700e002803030020141e0115008840d40300c1040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 486167329 1250 486166079 486166081
    0x8091c2a12051e0a02180105060a110a020d03030e0d0801030515060118080106050f03010903020706110111030f0a0605031506151917010603141f0f03030503040b060a030f0b 76
    0x202408100c3c65040f00256540d0b481000d50001c507482e134650040c80d00728030944c00c0200c01006845074803440790490320081d0041d030402101e19010345070060500d403212040d210300b00a100c00f507903038460301d001130500136100007426010746901c840c203202a01c801403050014110040000820010fa070250312600300c0300300001c58894400489640e8000040c0005c0109407510100d11400e0640c003c8044a004581c041d00c2894a2420b040c00d8541e07140e006005038100358003c00c00ea500800c070141c03400c84070701d00000341034060b000c00c01220340040d60040c2c80882c0010810181ca5400e00c20140a04012801044281c08000e648001c040d4001d002c640103070849003108040034800402d40d802c070607440321604051a1031050041030601030f2150044098040400010401d000e8402c002580010345800ea401d03590f003004003000c0c20040c460301e00005250031350000f10b0380d010b80c070200040c620942e6455982d04103800c1c2480c044c07101606117032041e90521000c100082c000e404c0b04441580c44034148120b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 486168579 1250 486167329 486167333
    0xc020d020103060b031e010501080f040303051504020703090f2918090405030903060a05100e06180702060702070603050709060e0d050616110d050a080408091c2a12 72
    0x1c3c0086901c00b144029011081c0902c060f00e201e012800c1c48082c100d0700015a036600011904a8000e4030480c01c0b07400c0345c001040c0405c0c4030b07401c10740d8003002d25200304001d00c1c140004a0304a0344110010380014501132020300908a001032440c0042140784003088000445510909480b1074541c2024040c0d4800244d0390001d11451104000502e40180083c0d25440c0c030782802074a03030f072143c501640b0074012100014901052071141710b00492102110040319800c2421030304120401a142592001c01d079401c0c980611003501141d4400e4056a01410176820418006407030300d80190440c1d401c1c181040c04000e6815405007580c011518580f92480000211030003281141c06082c00241550064500300072110211084c5145d03000b225030303210b00b02e06001c001526110055442c07401c000031020003108034028491404590414014080140b600e820407001841204403008501011120040900140611030100030b0340383c1062921401c8500e054441031144040c1c902501405801000030441 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 486169829 1250 486168579 486168581
    0x1816050310080a0f050606120c01050d0212070f0f0507051f0b04110912010608061f090c020c130209010e01030c021204140a081b0418020622090b010c020d020103 71
    0x1400b0150999000402c0c80c24002c030824040d060580f15889010041001420004103039180805160f0240075181080c4004595543c80307001606101c580a1004002d03840e4095006c5020308515182d00342c0503010020040d0129200f000c821f000e0107001c1c414900855004a4210035640003030a02d90000310704c8403035840041c0210300c04190060701e404881525581380c10002e140501c0c04640305c0710407035803c1a0b502c1c00da84d11030240d018a5000003011641c2c501c121501076002030209121888901d40b00e940305022588030b074003440010703803105d8500c0704a4200005803180c5030510707034002d40c5411aa6000606290003440300203040603503804c40a06468428090010400040c06e18250380c0ea583d40500701082000280e010f101c0c000c81900010076040c0090580c180d0541c8809841c29118003c04000091020800c1410829100552040180e1b90340d0001c05052044040f02014540f40e50140d08400c54140c100300c2c881407500c0101020baa812054074002c05034121a82c1852201e1440124 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 486171079 1250 486169829 486169861
    0x23130515123d1d07050109030204050403030b12010504060b100c0308090304081207050c06070c061d0a2411031b01020f0318010b01020102040b040e0703140c040518160503 75
    0x2100c2c03020154846070881d40290460707031454095104280004030700b59403101c0e1640308540c04241c000c0c00410050070107802c01ca60150007810300103403050340c85d004070f01d00e0640c0b000c4044099540c0c0d403c00c010880c00744a84021190f040e80c001e40710445009000d40250081840030701448005000150304800800499001e03221072403c1c0d42c9008480b88659055030404801240c0301c5c0110808910282890401e4a821640007049034a26626214050320b0724258042d06204a20300d9451545641c1c0340c0b10060380c0140b02d0648040101841e86504448400c500208070081189600c030004401c400041642c0c0b81c1001080303408094000348511600900c140199008000d01c04020007407044081c000c1299008103d038000d101c4030030f262004900b01d10440c029920300c0707401030109008a0806c1d604076a440441c2d42000143c0f501840c1d140480464112440600030390000340500c103505020200105002900801140324244454002c844070318080610040100101c00609c0c542c007460f4401c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 486172329 1250 486171079 486171163
    0x170c190503090a0519140a0c06050d0e01020406050301181514012303271b0f040510150905090c070f0f03020d0e0105132313051512 58
    0x702e003070140741603904118000b03112007074a8018101494881b849008603039036410341d80c4600e1106502d41040c4058940e60000600d6041881d51940e20143e100f0091000300040c180c00d894483e1039616000d0540034400d250b40e000c000d281e00b0100300840e07031030981c241700c01950052141e044280c610070004851a034404a100c0319010b650781400e44040281e04000c1d80078111012804070842d161040f1a50100340000000081d81d1080610a0411043d803441c0480301c20000e001004030341400b000141071314004e8803199850f01156404101e00c2511030600f03c464075507810240070880c40c000002e6102c1400a140003134070f1100041d0074040040201039848502e6100c011200d40c1c200508000b59a100a410140041007130100c1034a0f0303543c0568140d0b0b19242607114a2402c8500b018030001c04030800700042c4000004d501ca981c0c0040c0d039001c43c00c0171146d18942c030011b80c0e454025402c407400d48610712461302400015a150324a4000801c1a1040740c100c09951200c42000010440b41ca081c64640 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 486173579 1250 486172329 486172333
    0xb0105150d05130b0f100e18011d0705040c0504030f02041404030513120b04150e2e0c1409130c02160e06210c04020703170c190503090a05 61
    0x1c001035140d9103e4441d407410700808002406948058004006403401d6601a0810800c01000c004002011201c02d41c4407201040c01c08842c00500241c900351846849071208401203c2c180c264460800c1046600030a0704a13410701185060ba840581725115030302014100099500442043d5100e5422022200c0740050041d10300340381a04004000c1d402c061600d1000070001880082d46a24507041e9016a82c0c00c070442a000d43c03196500c10121181222004078926220b192500343c6890501000c000d103d0340300145c210303000000c619070a00020590341c0c2c0f0800f6250100260000d5800303607200701d4110501e040c4541c0c83d0070390340c0000c500b00011140d007500c0364200031414400b1640401c6040c0c22072a945410000c440c1c403102043c0c0d88032401c56a1942004400141c0c0700c211984200c0d03042c600c0032401c1940c6903149401e01240990b40600e8041e400305180a054140c0b54003400060343d40150482c49460910108104280b4403032500c002e400c04002002c0302007a6980c1050119140c0390f039110003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 486174829 1250 486173579 486173581
    0x20306010e040b01140109120c0512070602060133120203070504140a05090c070201090b0c0708070902030408070f0213140610051602040e0a0b0901060513090b0105150d05 75
    0xe42000100d070485040351040765010000405c0758407000c442c62403500585810000a082000d500403005400e4800e85080d06560000121511018a0b07080741034803500150401d00c0c18084041c0c0391100603401480b080140c022a80116500015903101c2034a5500301d01c07c00c80c0c49802c003111046260705500038214400414020003a402100900403640120100030a0399008410864419168412aa0040303226000a2144c203100c1000340115032050400c100c0c81030300c440c8007010507002442548519800a0f03c28002203404110030402401c4280c0700b0345c51442c055513054214041c8101c003c02690104c000c801c00c55440f4205200c0d400c490803c204102078144040306032030325055425a001e074034809003c88030240f2540c1142c0303160412038286080020503a003404020311000040d61014001c040d8014005a506500385000e460b909002040c0181004100000c04a82c140d4034651145440071290005080d0024203045a801300d86400001e03241d400c014040b44582d0f4509820340b8980700c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 486176079 1250 486174829 486174839
    0xc1006060507060b01020604020d1e060501330903080a141306030e070e0f090c031002030702013206030705101107060e061602030102090d06090209060102010c1b02060702030601 78
    0xa400b03041640d000c2c090901c01d8080240c010780c2c8407101a00c0c040d4005440c03401140c04035036801240c1c0c4030b4a6121000d0f408104050321504101c0e13001380c2100d20340005e607171035050401190158410017250340302a286034041140781d000d8218840340c8402810000081a45400c1c64003402030b4504000c44844943c1d038404240100d0400c039521405400d002c00d1030181510800c040000e110303420b035016060840441d80703c010a018035150010100c01151150800c002d405482c281b05c4c0c08010518000050703103d080c40440039080d1402c00401e82d801920181c80c19008612410007010001b03100e80b8603c01c0c6840b100003290030100c1580000e0b410804183c6104007280c0d211042c101400944425a5100c0d42c6030a0708403520a61195000c0e4860810310240707100000074850010110310040006140407003c00102d42d5451442d4010307502c103030365040c0200075401e0200031190f10240910080024031030307103a0003402d00b04610601140c81d42c81000074000b152551000c0f43c003410380040456007250703924 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 486177329 1250 486176079 486176087
    0x30b01080a0203010e070f06050d0f152909090403170c070c170c060a02030427050702060906011205070e010e0711120706050c130b0301380c100606 65
    0x1c40c07049010398604040c4a180c2c0c000400c1d0070f02501c00c12000b0003203c1e483c02104443c0c0d03070070a6441c0b6428a942d44c90751070b4840f9042c411924452406402c6146081c40c0001d0007045030313502d5401101c00d943d94151401001d0008080b0b130420101110301d01020307211410122018641405403800c080d5103841405000f02d00503000c4d014061080500c45581911100f000e030300e072080b41300301412036031083d5002d509528011014103210100c81c4100d03801c16941e981000c000040950780c40c00300c1302400020752044442030044a600251500040c0103604000c0540366880c0d40510480664851091800080010501206c00240b13a001808a00ca5840d84c0c1c0ca180350b014151010004281a24072810300d859012030002c2100000e900814145034440c3c036554043c2000401c8584111000c006d00800c4407030b81c0140d0000b03030540004490722581004842070b04d0840c10030218000d00c80c40601c0000c6000e03d40070038075448148240300c1c0e0b154000614118a0302c42410703101e01400f0700303144000c2202640 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 486178579 1250 486177329 486177343
    0x91d03120c030a02090a180f0b1f1218030f0e0d1506050909010c02070e04210e03031c0b0a03110f040902030d031b030e0d0f211a030312040b040c030b0108 68
    0x82135400c01001c080700c8c0e0b9800071160041c62890300701c01d0020601406014614004110a0f15402c00c014080303003401c1300604803078420005004c003070640c041d0441859444a9905000307a020b041c000400b41c00074000484c0c100401134010300040003030700700000c4000e11385c00c40f5004000192640309142006c00c01e1034042c1c10200207250042c4984503000891103a0030486600854010402d004d80e0000c14003541038036002c0d0f00c06031023803051255000c1415201000101080b50354070345409002d004400c1104140c41d001c8018a01c140c099080a00c045072035400e080e2001181218504050191304002c10064010004041d5042c0181008041310540641140c224801800c0e840b0b951100d42200035001c5400c1c4c0c103082003040e032000c43d502c3c1280e4002c1040b50740303111240c1404407111401d132019801501c1d00c2d19500305550f07256094041c094800c01c14140030314000b02c01a6050400480109250780402400a4081d0785e0140116042c0b010040c1c003180a9a00a04113908a41c3c641d9016035072045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 486179829 1250 486178579 486178619
    0xb01050d090c120c15020604031e2a031d030c04050405161e0b070c050d020a03082106031b010c080c03132d050f1207091d03120c030a02090a 62
    0x1801d0550013062413007c94898880c0c0d60641301c403000b140191495641422000802006101070030921240038851101402c80301c04d45030441c840756210510f0000d0000b200121544200c7c0c510f14801d81d86a6408500f074180311b0016140066180e0701e0741401854120903071074111400309492004500c40350002d402c1a00e080c546901801c6603542c4040c105454071890781e02030300314038000c4424042407405d50074095003140000d1480d0040c540b01c3e143c1a01941c0300326136280c2e0011250910280c3d01d00b1443b5604c1d880310003100500455001e0005449003616401581e604001c402949042000340110070f4500440038603044903202d9560480741d1003218014002c8006401ca0401400e00b80c5061501c141c0c0070501c00c51410040394030740018006c070304002600042e40320810b5071100c83c90482c200f0000780104102c94000c81d420040d1384103e90342072035030440c20345030b60002c2100b28620b28407081c04a811170140c8803001c0c2d51703940715034000000b8043c801c13115500050820300014290340040740440f5081c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 486181079 1250 486179829 486179849
    0xe0d031e0507030e040203040f060c0203030a1508060a02090102071503020a0e0405040c0e060f13060509010b270a03050102120f10030308011202240310090b01050d090c120c 76
    0xc918440155920b00503804001c3c00101491054101820039801941d00705100c1e480800305500300f42d4540b015a034000001c0001a4400b0080003203596450003109081c1920184201420381401c10280d2203600040c4409189600064444842e2f442004400010030700b892086400d003a140c07038010040e500100c00100003840138540307c509454144911801690301c0300000e1b03d80d51400b1040388a001c0300616290b406500074400c0c0285071101d070a06200504040800200a82080c0070449620700c1038218072021141030281d07495000340400e010000001d00071260000d00070140006a00401940005000b54000300d040003980c00c94072034190281006c20085d00440d40c6c1c0b6108041c090711544000340c0050a00001000081202c1100341f07034090001d0040c2c440e92203040000c244a01483c0a0502d07011000010080c00220500b041006014900e100340030074422040024030501842070303645001551104041f0402182c4945840103000403034102c882c00c001c1e41820b141d102014400e15040d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 486182329 1250 486181079 486181127
    0x30616020a21080105100f08060316080106030b0a050705160203070b1b060601021b01050904060b0703021b0d020d030806030f0708010f060f0509011701090f24050c0301090c0e0d03 79
    0x52a0603590b01ba030507540743e6214241e6595030f04040b1000354010302400d406009200716082c1601c2143c8210f009001d617200049a204c1c07440c5000000d04600808e40b0303180924100074090001d40c414111001400791100b0490360120500000e810045c850780101000c000005200324000102d0141c0382502d010141901e0703e40c1d0b56003006a0702c078000ca03420170440c0740b401d6001c3d0b019036014601a180c000000f401c002070340c680342c0c003610b90580d0241c042980542d1103020b00026800c2848800c1001c0709040d140f148550381c05501041941016403801003c1c07110726400241152030410065248075005412241c21650b0303111218001c0045407c0d40d40203d0400e200482c0c242c510039440070403508050014035840c4e290000f100e184d03010139012030619540701d28401c80466102050000400d010b84001c0840070240036620300361385103542101240605020420080c40c0003102500d044400c40540803400d8659914201c2d004003018403100c1e4080015861101031691001103082c4403480b580000380c0e6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 486183579 1250 486182329 486182339
    0x6080a0b0906090f031e0d0603030509101701090c05070606030c080c0102120a110a0b0411010813020904060e01020d050112030305010b03010803090103110c060f0402040b010c02030616020a210801 86
    0x48030080c240704541e40d841007001b01c03a4486410083c082c034410401160303052580a035034071401d803030340b0764020750025601060481840c40d015404200349a603501f0200500c0c4252450031280c1c0d901489030401e201d95802064040368056411900c1300e6500c200b0402407540c407032a01e60500c010a0040c0342e441e120f82810b500c3c03a940001111a000300e49103808600740110500102c6240c84070301c0440520b405518403290014140800450241d0300c600790200d00c004800c000101881d000a0803208c41d41407184c140c80158039500001c0e50045d0b002480414842040d80d003c9029100b03901c51113896174900340000550b10301348480c4910440c482d81c1c0034000e07070340d80e2070b04000070380801c0c080c2c80c040d50030800000c1c4030380d03000742d1005244480069004e07003045d04480c1c10b80e0800c4400c55000e9103c82c5100100011450b2030710030549140d600342084699100c05e80c011a41d0b60000800005040442c1044071004900800082d84181c0e0301c221248814400e003000d034000b41c4032450307006010908400c00850 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 486184829 1250 486183579 486183583
    0x1c1506030b061215030a020a0f06020606011e08220b0103060507050406091401090e011502070e160507080f0c030d051e041211030a0e03070f030308010b03070306080a0b090609 77
    0x40743c0daa21003410300c004e03281c06080218165a200003964107200321441c40006844400c40c00c801860364038a103a040c28541900a4100140144460304002e1218600c07113007566180b520102c2d00044e4500200190b8540e21040d0200c41d40f00d1440d00f86000540d40d240400540c080b15a061300c0c0b06180521050325405002c0c0d81c1e9014500450000c04c0c450031040c05049901150a0b0b41e100d01491300828190f83d8403144048130b1020381001500c2e0511000985001da01000440e006100c4c0c6c1d201d9841c079240800d0740b80c210010100b66402040700c0019910306100e01a03042d12910b80c8111200f507174030740320400495540c0d07209070412031289082c680003030901048800c42440c2d918017500b110609507260340c0c0d40d101c040d5003c0c0c1451300748070401281888540302007000c0c001c10b152a03182c850704103180c81d0400d483c1401992042c43c032204482d405000182c2c3c40b460329030441d2807a03408562641c032a804190017400040d0403000c1c040c801d000c0c41c5818000c680709554001d441544c01d54890344c032142c0d1415 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 486186079 1250 486184829 486184837
    0x4080c040204142403100e070206070f050a050405030d021e0109030e010806031903200304050f0f01140a090f0e06090f09010b0d080d050f07090b1c1506030b06 70
    0x3408103219200c041001c1c14501366510a04031465050104000b04d084030b02e84a03001640d680301d208840780010301480001407000d50304500140010441480c0041c0c0c01449000640403110411070041803145d9420700410640d400341a005098902001c50068002e40c2d511424591001c04500c0950480c11814180305481d4006d403d0ba4420241940c01801504c941e1009884e440d010321983c80d98802d1007a11180c0800058400e6482d180e10030f902c24800c3c2d40700311240c00f21141a80041004005595400700c03440f01c0d11000b6911025000300210041e26140321040d146100c010f40015818086944985014185c52030741d10b9190340300b929035201440200040f03403055000819000414502024502080d500c8080240046107038035450001c580000741c140130445000314007165502c0c2d03041c102d0040d154010f5200c8180b68003485e1a090085c00b8a029105134662003500107002a003503590001c00c80146a20040c1c00e0180c4034070010b1045007002d2034814500002d14000b0000d1440c030b003100c100c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 486187329 1250 486186079 486186089
    0x7050307030819140f0a090e0702010b0112020414240c0f01230a09152306040513080307051b1005010803090d14010905060c0d0c02060412120b1504080c040204 70
    0x2e1708001400500072400c2c1d0100001c07005012078002c001954600c0d0868140c400d0480340c0c00808e06041020000d00700e5001c10030700e050250700500080c080c604201c203030250a8403003210718858000801c203c220040c1e210a4494400050008504154941c001100749441c4200d01c0200103055101101800a0b064418112100c03084d40000c21110316454000301020b502491076603812001d040034200446022981c1690b181c020b40102686c4901c1640c03241d41d000c40b06840921292810f424100034003490810018000c0304041f01090f951882801540d0311105a615000541c1149240c003642e04c1e4110740d20b040e0304030300300800410004004000d071a4422000303000220142d10541d240000601a440c00450079907a5030540004680d0400040b0f00600d041c10110b17587d4001c42007031400b600d00141b010400d651000084c0400201c04000e400011100c925003609800303c2742821801912024144036841542980c50841e0b80e40c2d000c0007001140d030380000711120b0041d0300080c002640150700c12 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 486188579 1250 486187329 486187367
    0x607121701060e040914101e0c0503160c0209010324061a071104230106020d0c02010302091c0302060106110109020a05010c020a030c09090b011706150307050307030819 74
    0xc248401d084c81d4200c45041131150070105e41c64490a07403130324902006c0d140c10011560f154503c003141003003110141c05071100c1104080c0b00d007102d610000303451071001a20301d1030031071001c10444080510410840c81c040340d004240e11200d580d42d0410034501ca803c29a0001c0d2804800c1d4001381030601c512a800460340f6403a034515414102e0b01c010400ca0700f20010507079048250541c44803a07582e07a489442c05000d489400c42c000391256800c41c0f0035030a41600b1841c159844480c0344202c2030382001e10b1036482a42480c0141e514214240804c01c080102503200749500f0300302d001c4404254020550718142c1d5190f6541c0380f00c040b02d80b000d683c03e070b460301c2d1f0000e50048900326081c4480d522404629080034000b0706030303d4a031643d80d03807420765410303141c1d00a5100c9036544061801300300005e43d01e1401001e0006c43c000e020044c00020948071013020701944460ba6407000b50b440036480900246000b0030f17008054800b510fa60b82070a4406034000311000341c090b00c4e408002845d440c0110325800b0032282c1200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 486189829 1250 486188579 486188597
    0x601090608270a111815062506150e01030f0503121f0905060915040f020a03020309010605060f0415090f12020301151a0304020f060712170106 63
    0x40644101c04050925882103121100c10009119410395002a890380040141005021401d041ca034103489202c900d0301c1612540d101ca403c00341c00300c0e9403941101c007281c0c10300108402c010003d1107a20030128140241040c2540d0202d1000c50300c030345211064002c00d018003c0460750b032100912025280510400d4521820060000c100c030304401d20443c500c0b8070f040701d281800e4034031b01e0841d0b00c10484100c0029640c03e816040079901c0e50b101c2c800240200b81040c040c900b4031200055401000a10049003411046c1254a640e940d50b0400240c0d0410300f84119500c18908400a0195008070750b0f065556007800000206410600112842d0300e00309000d060505081880c41c1150001c1c170402007003040f80201c0c0c081940070850a80c1801415188d10341c2d940718040d4410701d4252061554100340d0003030342038000c000040811044284c2c0c0c04014049a65a540c0c52000a6032001d6450f8100c2e000740c400704840d0100101c11514100509054035902520400a081000d403100c09014080008001003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 486191079 1250 486189829 486189839
    0x501060504060e060403140d021506010c121202040603020909060a06140318070e070e1e04090f1a060109080c011d0102100f0510061701051507140715020303060109 72
    0x22003d6000340c01490305141a43e240c40c3d1031900040c59203d00d030303140c0150020714070346074040011a0f03004021154510381c619010001030041c0078071000103001003860380310b6601824030480c244402502010002c5484985a0704020300a400c0410701c00e00803c1150089802450180c641100300c640564605021403803000411090707400242c04d11402044039130450000c04000e2102902401030400145030b185403c400060450000030f0010307000722701800c0000030107080400301c68010312040da00841c02d407180345411f0446c1501e944e405007600c1c0711399054003802c3c4030000c0c85501481c82643d80c00c0c9001d0322020140d0711142c07292035841c00f0444000d5070209514208002221a2074140151a5041e010702d00f114140e414107050809840c0c0d59408005d031076110500b860014000510b0a88012107503020040b44840060040500c03030628a00040d03520001d8804855542d03602c19022041c1c0c0d510541a00e03500d418900039030100300401007800c4041803000040c2d074030a05050f03582c80c0c8581c1c642 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 486192329 1250 486191079 486191087
    0xf03031204031b0609050c0f090f0a1a0a030c1508070507020409080d050f01051f12020906070206070506192d0e010e06060901080a03050307030b0316081f050106050406 74
    0xf407107500080c03071403890040c08070f0340030302c9444010350140d406401c1f9a00080d04000c0f00205d019401c0744170301c2da00000e01006856421545a000c10705c040005600200b4a000350a01c0c28541d0103254440350341700002c003c220112040360b0460b44c90041512003400f40c3d54066403005000c8a810000a070180806800340c50242c1004424900840d0007d103000d100040c00016180100d8403a420006400c0041003075040400b000c81f6001107282c241c00d2940c402c450300402260304141840b04403a000b1641001d96550f940450300203c0d8018502950344c03240d03141c00c6403185400c4807607520800003480900d2085000780030382e5419103003151105c180c421b41c1e6444407028460b840241030b06140c2d91202d10310300074424805d045001a40100821051502d203040115542c0c05802980094100ca003114002a410105503034101d5114207022401c01031101c0402e2a01c50344690001e44107801d103100080c00030000c01c51b00d2048982c03014403404180c0209a03d010740d9028440c0c500019000c010410403c1c3c85 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 486193579 1250 486192329 486192347
    0x61d2e0605032e0204060305151c030c0c150906090509100e070c0602030c071523042111060702010e07090209011b080919050f0907030f0c0e0f0303120403 68
    0x10f407070390101a654440d4108102c2e0860b0700b0000100e0313920802c0c410400d0013244200d5a0440840e00840c1c001042201c5007555900305800805111103c803c00301001446200c0d00050084070420055042c00c1d00001000c14403544100c00c0410f10700c020214841c1812003103a886001080002c415007441c2029450486c480201181c2c20003400115880c0011681e0000354050016030300d0304c548820071401c02d8038410b05885101d407012460314121800f000000c0300c004ca0030b104e076581c804036940d9a83c2040704000310074403109481055034041c04414180c10410003041e040b144c40840340c07960755000d01a400c0310b1b43c02c890040d0a900c00001048943c0e215001000015010b141c080e0b203250b04100201e01080300c03281c0c200c8a442c804109900203040c0000002e0442c2601d0f0200c940301450300001c100c0c80310469400601400c40103001403002406a0081d0115481002c0c08003c80d480040c1c0c01020065800c80d007910894103010301101c40d142c00803d4507401040c1400b8000740f0744842c5e5080c4c80c1661 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 486194829 1250 486193579 486193633
    0x6130219030206070f051011180d110603130f0303020301170303130809030c06040803030703051b070213180303051008010e06011707050909030301050a0e070c061d2e060503 76
    0x2003040001600542c45008020240d0030309540c803a01d90709c5051000c1c0380e0981540b41e03035006407103c0c465032000c01d0b040204200c1503a02a51015502c0d19000c0400c1300f007040314503010b405040740c2e040c2e550806502d54000d50485980b5803049098000c40000141c90303200030341d4080c000303011291200c40130034410b60080901c4c2200408507220220904086030f403581103680708600c02d82000c0104440b55070540902503003c2d85040008500158034004040c0c01d020b0301c1c00290282101d8606154a94829400512001b0840d161071180810a1a0040140400315040300031182c40003000200762105000e40c0c49895a1500504001ea09004800314021160b25541c582d42c0f040c60f400054076100c1c003160314003520351030b809075581c3d60402c8103002c40e12215901182c0941c006404105030950311007098400c05600035000b0036a10849407184040000e051a601d02c2409080c80240c407140e1242800d48104603071742c00301031500c0d100c0701246044030b4371f610805070103801203591003420902505a124440c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 486196079 1250 486194829 486194833
    0x316030c0207050d031d0904051504060f0f0e0f0d0518031009080a080705070b0c180405010b0a140703080403050c01060b03010605090f041a0f060c06130219030206070f05 75
    0x2e0b40d2040098424500381c0c40560115070350f04401e4512442c140f6182480c02402d8800c20f6081c2460b585142c0d039541d54001d10784010102c0740100c0c0411a103a00210391041004009114004048150a0043c4030303910080489100f001d01080f20a0408a400440741d41113072100b500f4148000d118a038030385000e0700722540c035014014075001c6003141032143c07101c3c90740075240c00e58542c03070703009401f4051070710241414060110a00481e4001681c04010340d60290184071056110b0400b600c1c081c0c40c503003071006680d51260800c0c0012030008480c030058541c00e202c070b6944020300e04504510701420311038408041e00250f49500068003181c000e05c0149a52000c031070000074500d9403003d445a0070703002038014000241c00020410b031246040c05101c050446e08480410246040181c20580c0003804d00700329001e40d08400b40b400b0030342d650000381d42c404101601981d4162408407250320030b55007080012446070070124802100901440c4230f0400752540a4095403070008a61585075140224001c200c03458 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 486197329 1250 486196079 486196093
    0x150b0a030201120c09091a1002070803030106050d0914060901060b0304080a141b07050907050315190305010f0f0e1908070c120309030b090f07090b0105070503030415050109020316030c02 82
    0x2d2150340c81f64007051081090550014050001045681c0801240c102e0455102030b00502640d6004070449046a1030340c105207030ba0f061681100d1014014003140a0a201c69101c4004d070301002c04202c040c8102e20070002044650745507200304e0540d01041d00d018101c02c405000c500741d040c2c01180708805210b8098032490038810b00044c13282c1e0500990754008030300e0700b01503010070150400d4140c06400043c0c6040080c258540448907052017070851481a10454000c4072022100200b0365202025540100c028080c9803401040311018148814161019624001c0f20441100c00403070424010805005030842d01000f42d21145001d402c00c4101f0748901800c090000380117542d120100020b12311944407200344900d5403c0004480c040200008841e030030043c02d9131404400801c0c900184d0362240c10009200403d00d0040f11940103c000040062100105000c2440306c8840c403290150040d0700e052101c0d03a01c82c003140c4107030300082d5011403001c403803001e035503001c14044d03040100302c902c0c86d204403045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 486198579 1250 486197329 486197339
    0x4061205070203070c14030c0103050c0702091504060605120a061211151902010c08090a0b101505270d021315090e210405060d0e0109150b0a030201120c09 68
    0x18407001703031740a80c0c1e000306980e0700341804d4102400380c0f003100d40003420200058030b004003890130b083c480d01c0030081c400d01801e40050311180940f0224080c00f1800f503c1088900c2c1c035068040d116030302c54400044c20074901d50000d696075403540583d0040da00300b00c0c031908900b901030b134900d003940a6000c221640284100b1040c224404d10b035001e41084584850b80441000069030060f0848603400014000c0101c81e0041080c041d00000d218980c1c1c1394001d544a440c1d9585100700034048149070070a20309030104413040113005a00c40058803040802e140101c07900000131880c84c90b0299804906078101440b44214005442d2420840c10640d00194000c11610352820020305803880c940c0000480ca940d60300004800082000840c010309080039000d145583c0381c020410042c0134074806c5500c1104001484400c920b015000b00e604201150020b012680980c500464200303003d200040e00245015400c0c1100e10381820010212038040c0c480c0c1a1659001d402a0094424031003603800b402030084000403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 486199829 1250 486198579 486198593
    0x1d07260d030606030c030b06040512030f0d0504020a080d0221090306091b040513060504021c05030415170406020918130b060102150601030b04090f12090b0406120507020307 76
    0xc025005640c0010100d081c014050102c07200c0d07000c54010180303000074182240d105e444c211400d540049402c0b46440c650200807030310710711540404030043d00e004034141510340815000700340580e108965629205803079004803130ba1545454000e4006a001da1b444195841070341035103e5064481a454918001049012034900b6a098032809180c0e80b2010488008070094a103a60020030101c8081c005420410310914102c000340401030502a17481000ca8215070355150292841059118404041003150500c01c0c4c40350014400d182c0d008850305200c64031144100440236000e146068421225107803901c41030000d401100807150000401506007030310300c05880710030784259084030300001c1d104401e280c81c00164002925460555124a0300b0306c0651081d201201d6200d0002c1c64005a807002000002d409070a0818000d001d1506c1c2c02c44d68070a120983c04042c04080c0152a1000d0242da6240d899a161003148900303c009245505460801074003604180d411180c2403044904050081c2c490340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 486201079 1250 486199829 486199843
    0x181e04150609171510031a011a030103030206040f0204020f040f14030f06040318031703060118080d032003070c05010f05010e040f02011403070905041d0726 69
    0x209a100020100700441544503904001806501c039011101001182815550304c40c405501a003d2403041c0c00154a1a4030007500002550000520380d101c0400d1490b000c90084203026010303405000c072901d051041130040440e8101c0354141c1c005c040350b6803151521003800803609000c83c4d000b5000c0143c524903000000250004d4a090440d20641616111181c2c014000460700d440c000c1d0454540c003103a2072400b103509644142c00d410001c0869800545246414a041d00020000601481d41c1613031031008501a40c807584080c0c071744d200071109500c80000700140e544100c0096620100001c69054429040108602c8003908030400e400482ca00e503115a400440d00000010b110080000921800340160603a1284003102000154103020503482d541e2402000070340b81541210881045911840c80c45000c003040504d5103460b424034500092030b40c4981e1003000c3c483d03400d150b407108051031000c0c01202c1c051000b074020b08035680352242d121001c280f003030550101e001014487d2560400240404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 486202329 1250 486201079 486201101
    0x2100906030b091b0c0a0c150801121a070318080a0e030111090607020a030b07110d030b102d09090e030306060316211407020606240d060801050403030c05181e04 71
    0x10070302230018403c00404806d81640031501900f0624881d0740450b9000058401c84440c2514002156660f0b800a9010741a0034070447c41c000c407280e4600e0207004520020f4118081c665542c4250807000c00304040c06da410b0007800103020407081061402900d8240028080a440500400c0720543d407616010940d6a00f02d075000c01107810310303a2404400c24148a09102111181410041e4581850108080740d5290150005001031821416862000300ca0b01004580055601d14900c50902000400710200c501c1030081d40fa0030a40d2221a4800110550b07100d804081c6c0b24a003103581d0105003040e0001811001001c0c01014912203ca50406400d50700c2c1003130800001062090180c1054602400028440c0701117410074014010580c0c1c036407800d080c821810420080c2c0c100200d02d08032102d8490702c0218000e4a151102c005074802d01900030502c10380c0651001c1000181020041c2c516110b40d40b61a00706d404264410783c4e0340d1031b140d12405004030070380406078450028000440c04854404804c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 486203579 1250 486202329 486202349
    0xb07050a03080928030302120a0b030d020304031104050a02040f12110a030210110f070609080715080f0406021e12011e061b02100906030b091b0c0a0c 66
    0x480d0038541c105032020340141950008114840c150b030800340031501d50118403d01c4680000300c04050500c43c0c3c044ea0b2804041c4001b401180c20007990107001802c810007c14040c1c01080850010140040141c5080301c1c4c020a07400c294440c0141080000c1c00024100344c2c100385d0034040030038040465007181019050750009075003c20043e0a017000440b0081503240c0c440c1100101c00e00060300c03800a4250000d596043c81c41c1e80207444495642411031401031002284941c900c00240150300074840c000301e981c4032040e070f0700082d00c4100c15444241078062540208440301d01281400c1c8120403919030240c0510303801428a030020303d041d07000c040400502018941e0214a0040c8024020011401801252011140c1041e01400f80304800103500c14182401000348896141c000d5511024100503030041c0703410802444a0307030160009101d4001c0714000f91420741c00900505182c0f4505015070103070002840164900100390300c0580c44400b0724031040c0504110000040c005d14150009882c0c40c8107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 486204829 1250 486203579 486203593
    0x111506040e0f06011404111b010615090501110105220606180519062103020c0a08160e010b0403022b11010e0402070c050103090c08070306020a0908031207180b0705 72
    0x40c09817442c00c1c0a01020300c0707940340020030085034025508490305c014040a1180188014285641c01880c496000480d40740c1c002d41c6591107241e100c84c0c2082034410980719050188150440c4a089500844600e2145020013100080405450b440700c1d00140c460304003c65403a4aa50350351801c14504468264010785680610035510307203014010031f882030030142c104078403480c0c20b1001c02c90351400181c001c41d9001c0007071041d040c140700f03014442102c4001b074160f07100256a0880103650340292402520b5000321108042550000056541e04039003840d81e803242041e0071602080068545e110b030f1842180707401d110058403058900d489070a40380c054442c15455004010014210380d81e05080e00e80300d140704001d0329000920b14a15202501c20a18000490420074540107038851403c0d000380940784540d800020800029070010700140300c0c50741d81c2d841880c0c1c3e03841525990340500011040302c03803d8800080c0500e4400c4508500320680c0140781d84940d50707203208d04007559203c42c070161960b8202403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 486206079 1250 486204829 486204839
    0xb0424050106030b10090b09030a06020705100b011110110c01050702070305102903030f0d0624020d03050712020403050303060a0e060d110d02060a020f0c01111506040e0f0601 77
    0x110071249404d40507681c9006490640d14001c3c01600030303020701070012201003411101034404010351001964821402c568800e50303030178496507400d4003210b03488040c0c0c1050314507181075220b621445c8114442c04024200c0307540240404025184980c141888403205000d0400c860400340282405030381c031900600201d50075401c1284c10200c9141850204c00d040c500d00341c007140100f4a048050306401c0c20601e14000100000908510982a642503049404918a51440d40e20703070124041b680381d080514900c40c3c210400032501d0840f102c0142c0583c2019038000002e50194114590010310340c9025902a0b988050400403a00150003d5a8590021003004201e0030003a40100103041602083c0c007092a02d50002040310003100e01c001d00140015a201006448650800b248294000d118030789600b910b1000940d0754805492000481c070641020034a55402100204416401e2001a2011015600b100040c007000545401e800c180d548000401243c1c052200c04000c10084001d0301181d4944 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 486207329 1250 486206079 486206081
    0x601030f06121419170403080406110f010b06070212160b040f0b0f1e0d050c030406050711060604200a030c0809120409052a0d0c03090f0b042405010603 67
    0x40d03200c1020720303800800c8013136080400c800381c4e1000c2513100d05a80f0103d80d40e4100c40002c0d004a034002045444003040105200e40c2181c07410546030f88402c22075554891480d600c2d800e8403030032071000c0d4000c001042080e01600307111717040c0907000300b4a82c200e8040e407110010900601445a0002000c4180403906210342c8507000503110040c00d1030486582008c00403201981688150000d10b02000c21744200412080c2594040c4d5440b0f0040001c00c02207443c2054800c001076008503004c44182c1c3c900b0b40019425030060142c0140030000d00028103a42e96080d0a1000804003a5070f21613081b519403544e01340e40703089003000b007840c00c2890780d01088105400c80054a03082e80580801500e41120300d07021080740700041510b0403207003e52400b14a584803c1f0380c0030040005c3c41c0c6a8011040340009000306294004000d0072240001e134410400c4031040301040301180c0d404680145000c00c3c1c50382c41d00c0403401c00c0c511142c000740100e030707408907401182c07032000d1584030305100481c951a100d6004022403505 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 486208579 1250 486207329 486207353
    0x20105060a050a030209010e040c0b03280c090902031519030201090803040b0a050a1101020d06150e091b09060a080106090f080312040c17010203040c0b040b030c030601030f0612 78
    0xd83e80e0a40c040d0031540040c030f50402c140200001d4600e00d200003000d02003684c003100d004001406003941d982c201400071808540000d0000021b1402a421003009040c10b4811600c8040c2d0661700c0c0c6c0c8500342802c4082d0044d45c4046e003040c403092005200300c07849558460050001100c0760038415030640ca50710001d00f00b8007040e801140290401d000400c0880c115204031001d1500074980f0542c1d40448000641d0b10034054900b68a03190301c00305402c41021550b0f809442903c80060844505110031001180c408a00f201800e81061080b40402c04041c180000e044c5450740340801c080c207000c3e0b81404105150091003088001944000c010000c41c0c1d0425030490142400b01200030815040442c4a13039039100303400c0c500400c3e04209001405200410549c0d002030710700444101000e40c3c1d41034510b80070b500140d9042d5210008601c0000320020150215003c68209403421822341c0c0c0c4040503142c00d40c000a04141c1416182d04a82200060a106000142a07503446000106400d41003030410a06 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 486209829 1250 486208579 486208589
    0x9050a020c100e1509060f0c0406050406030b0a0506070c0306050714091002070305100614030705030a020d030e030102030403090305190201091215060e07020d0c030804020904020d12020105060a 85
    0x320400c5640030100000c50780d10b40c114000400800c0740ba110000b1240380ca9410641c40442040300c20902c0b03651800810194090345001c802d44890340c86101c0c41070080d100e24410440030513000c10007004003d0080d0403401c0071b50802003400804650b15400704806034460380085400d100107903402c0c810080980b0405401603568607080c4046105011040d030284140341c603051007040403d62501d9140d100300f120070040c50f480810f403889140b00302080000380c001130082e28600072000c410302a041c18001040300440300014000c20400344c41b6000c1c803803500359440d0241d04200d6144502c800f5074809000560040b4807075a02c405615207541000c505208444900550a2426543d0380c80980c0c0d0144951040d80e0404940e10030a00d403d00c0d0058030075110752012407100e4284203000684022090380c4501c110f8094082e281d0cc0440810100c07100401d500b070046c0490054004034000d81440b04100751301620140562a41e040c50b91642001281e01d90540d2006039117401c200400d50401c0041d0b080105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 486211079 1250 486209829 486209831
    0x40f0e0d08010e011701021c0b1503132a030f020a170d08090c0307092f040603050a060b0d0b1c0b240a0311180708061003020c0d0909050a 61
    0x150520300500080181071107052014003008030198001d000030b42c103c402c0212080141c625200030506014040c00003000d845200791404d02c00040350711a074802f02e034410030044482e2908485181c0c0c5072030400d05c1825500080e100e580c81d80c45e0380d841e404c10240b405180295060840480c05104200c0300aa40e5003200c0842690b10070808400303400062401203005160511101a582d54400b191410410040e180d516204a0400084280e03c07a88022174020b0410000800c001c44403509105403022100c11481c41c9034104000c10846100358070864000018150100d0b815076140001859500021450440c059850303180d0170f40e0b8541901e00c190041501205c0c441413040c00d840360654044000c0501101c02000d0b00306508101000c0c889040e2000010019001c964480c00c0007413224004403002c40c040c0702075120041031900300d501c52038071a81190742d03133002e10340e5200705000035503085007a0681419003d109070f02500c4070a02084880740b0044e541ca4501d145484080020f5034006000708040e5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 486212329 1250 486211079 486211081
    0x120314180d0e030c18040b010503010c0503041113050c1306020c03210705010213090c020a120c0512221e0501050c0307020a06080f0a06150f030209040f0e0d08 70
    0xd5101044041c121861801d0090030711504101003401c00780140d0300d00b98071003800b90741a0075982814000d14011070084140b00301aa1f2075005140c01c031400b810f04207001c1503084c0f00040c001240810604e0001d00c000e03095800313501ca01d8030004103880c0143c52040c811003000c00d80741a001d1044800c44e00a14142c0700402c02404440d001c40c4d1118580c4d0364a1284010301114400d42d07600d020112124550302c040210b541c5c90280540b0b5000102d00c0c052001c01500300030409080d64070000c2c6180300c00d500000201c185123200001966501c00d00c200480d41c0340074100d18200807252020180500c4140d078180d43c2410b030040440c000a0182a410080c044000054a51840e880710341070305050324005e0a08a80d20606801d0240c5103000b452802540f0480e5284086205035008144900903150446440d0300703900c80c8046281520000d0144c150300c0502d00c110099600d1003a208584110340c1c1c1d0078014074001010000c1415a40760300c040c1a800c907102c150903040c041c81041034001689261800c902c80f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 486213579 1250 486212329 486212371
    0xc030c01050d150512060f0705040f17101b0e0411030a050402031515130e0a02060f070c08061017030702060d110a03050a050c09031c0903120314 64
    0x118040c600d42c001900359141c4042001e245042c22007405060004e1141041c201c810607140d60341c48003100e00c01014140c020100f4199030081003520f0646070f8002000030003605060b0400c209040744110924a40b0038001003101401161007030702080d81c19030450181d260514607000d010710210b8840d05006603d020340e19445040c142d4280c80d0040e10204000c04caa440d9400040e2804030500300c0d1030104402103061041380d2111018440d0224001c3d188500c41400e00da80d050120f6800200d01740c2e890f003010100000600e00b0100900f40c51514502407801c24203076448500000c172441e0000151a4081400d010043e109030007110010300100c0211440d00c000441226101d004100e002401540040f44010a5240719040030584040c0214074035180ca4020000401500c801d9a086c5001ca00c1e2901040f0424031000444205890180042c210f8980102d5811041070000410404221690f00044005440e10380103011072811598086100d840541c6150700b19000074051300ca41070318828510807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 486214829 1250 486213579 486213587
    0x80c01020a050a111f0909060f0312140c0d120509012d061d0601030f0c020c09060d12110601060206071e12050a02130b16021e0d0c06020c030c01 64
    0x140361613210304110443c01558010a80d01000c240740001010786080d0f6000182c2c2c0d2040641301101d02c00401800310641e66100b038500005240000b42c450000d40c0070f0300441500030f0b02c03e00102c04a50351541c0ca000b565412940c00d1030243d0403544001f500c03141d5200803249072805403e410200c180e000300030f410310001040061034800c5180090031941820700d80e035850071583c0071500410160150903014002c40c004030000010482d01c2c0c0d408030b8600809285e1200561007001d4442c80aa0010100185420200002003100a00150740301a211885800190000c003005547c903103940c0300d2280340e004041d800c900f400b0050700100c4c00c6501c103c0401500e260b1000f0100c03954105403103404600c5480410468480382c0414100c2d070168200000d2010111890703005100e07540700f02095550f0261205400d0002e445580da401400650340600c0402624045103121040380c99400e541c0c01d144101000b2408113000b4120a40740206004000c01c880d580520148645003003c41c003806c8120040400a4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 486216079 1250 486214829 486214843
    0x30c1c021003020903070312081b0405010509040b03070305010c260105061b01090c0911120c0a0512131403120403030b01110a12140301180902060702040e07080c01020a05 75
    0xe03224100d80c121000040740a581101c12019019003640c030741c9516424583d6503460030005100c00102007030005504111400d00c0d079145000300300f08003481c261500e001160b190b000400002d5205554200d841300aa80420842c1c0c02188100b0011030386c040d00760000b5003c0350b10341d411200c14120007a101d45140c400048c060303055400c11549030303865035252204000c4501002c00f44900c01d62034480070205000006c0c4420003207400d1f000040c0f280c2222801d03602d100d0f0040c07082e070300e15003040b071000700c3c04611030f0344e028080d00c541500c2c00e40e0400186c006520720840081e02c50250003609440702c502401070b40c40d04581e2505c1020001c0d4508461100002417680d00180003a04240d60748462491a070b02c00c01101c8004040c500454030300012600300700000c0000848440f02240340c440c2c980c0741d600b015a05030b90403a4601001002000b030386440c490094072000000b00e90110b020024000180d5940c4030300341c245214000184661403c3c105e04030319005061501d2810341d0b01c00c528403030000301c000841c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 486217329 1250 486216079 486216083
    0xc0e060604060c030f11030309071719020f01032009030c06030702030307080405030c011409010b0109060c0b150607050115050a050d061d0a0f120806150306010e04020c0a02030c1c 79
    0x1c800e0b0f04409240450310501b90714a41140790100005020358503000040c03c0094a00c100c04006508150503042651800c1180000b041f407804c0c80e00e0140545008180c09614240605010880300a910300046555060305c503810170561000c1401034040c10200300d46082c044c01558a5891402d000718080d58074000140020b0801c080500010100503051007a1008071149800034400c200446070f501e482e1540841ea15034966280c0048117000350300c02c10070601264181c1d120341e52a0b000d02e071070f000d0001100038221501000c426425612588400f8010300080f40034500014120b0b80b141c0d00b059404803c2c1e8440f0b0b100d20080300c01880181c2e00c01d025090096440200010407080c0040c2d03076030700d07050b0242c80c40a01d8010701c0000b0041c440c41400d00040ae902c240501040c0f0441c200c1e041e6182c030303c02c1d01d01c1a0444407141c180c5050f10b44900040d41c110030141002604107508000007000d0342d108042490240c3c1201d030000c03007141003c0043c9601e000d07084643c1044d4940d880032120940b80038040c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 486218579 1250 486217329 486217337
    0xb19020403210c0b0903040e150607030c080c0d050406121407030e150c12010603020c030a12090b01230603040210180b12010608070203070f140312040c0e060604060c03 74
    0x20700080c600a04400103c1c0364002c803000014909000c28039200d0b00503120303404081c410400010126115a1000c4400020041c4143c1c00c1a9154508903800c450044007101c080307404001e08011400204003041c3c030740c84140d541d02c1d9540d0408200030030f80104018848005414000d09646032541032600320342c072000e02c0c64006400000e6a81c5e03246820000d41a400c0180c0308202448110003c040081c42229002140e001c0c80d1390340e4980441c100d1213001c20f100c4581c0c10500c400780c80341d48105030058020a08a0002c100c0101a4840844200c000c2e0300c410364807401c2801100c3c40d000a4100485c400c2800c072103050444c6481d401003400114003001001c104066119010a54210006004060403600c6a05a2240c6080090352800c280a000d81c001248000d800209c9252002089501c050f50045000c41c0d40c0a65030784800049600c0d4450016900085c0180180e101402c01c203540f089005051340c50f2124a001a40f45866501900c04d500031a001c1000b804010b400080c55503506ea454a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 486219829 1250 486218579 486218633
    0x1505060f040314010902030d08040506011211090f160c03050f030a200705150606070f03120f0218030f071a0403060606020a050706050903100b120a0b19020403 70
    0x1000e01880c45503401c024103103140030250036007030101540301300031079032080d0704a0389003510340b000644800304125801001030703210b000180712034811521021421403141003034403591903059000500ca9401110004440d00403802040005204030580704030100007401c01c60402009a10018254400c0203c1c2c000003c0000000c100c00400c82d602420b4505100200b0014138128005500d003140e01141050f211482040e019400110640c51518001c0c807005180c0c510305200b0baa40c0805403482440154207003c085880c0c00342c0710226028844c140341d0300110060f07441400e000d60b0082c0b01000c0300d08500941c400585040c490400151580c00da0740c1d031a18810b4180ea43d000d1030821803056410080080d0300f0580001141c9800250700c282c05031184040d0341e07280d034880304225014018021038030b40c141d0000203441040d11242d0700c0203030a9500502880100900c2521061900703410081c2103070040e0780f500400815180790a107800f50740300390130415450030389592941d040c070b401c01000e1400c01c542142 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 486221079 1250 486219829 486219847
    0x207061a0d0204090c0518040c0e070c03120f021308160506070f0c0b1b0c0909120a0c06050f010315020310060e2d150f040303210f05060f0103150506 66
    0x300700000510004010407540d0b0003202e0030b440614800d40b021249c0e0b5442e010042258003031904014482c18082e42c540d9141690b94404451503c4601d094440311503541004c0f0400c140c607800244414032403000520341c01d03803510305140c0c0780408400e00d0803501e51500c02d052003141e0300c0c807048400c0e65801c54001c1140b20001e00b04810301034095806600120400640c0c5c1001031126414000b18448000c10b46841c0f00c0880e080c041c415004a0b010701464100e4041e150300e41c507010016100f207080e10f00c1c00704803000103903584400711501502c203030440e00c00900c0100200f246403801214010544d030310541c00c5007030080500c84c40c010745008280038003110a524645580700c800400072903080360900c0a10015000f41c2c0d603030b04d181910000354012540628042c1040c0003074421215110400c00d80c2c545400e03d182c070129403060650101d01c08280c06401c424495a03018052707401814003c0300001410309010080004c0c600c00c20081c0c2d41810b00b4455203c03100200920048103d9400f42d410542d82c9200c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 486222329 1250 486221079 486221093
    0x209100e0a090219030b01020105090a060e1f0e060105060f03061e030d08010e0105060708041703070807031d1507060b060c0d0305150d05060c0903010b040606030207061a0d020409 79
    0x82d004800828800f0070b2518101200d0200c510350010603440070808864858012800c2e103070100c03010021540030b074014a00091940c0d00030800403070b02600741c03a1100b00d8002841044810144034845a40e142d8801343c481320000d1200500410301264414074060004045010703a000080405104490500041031022800c00010503800750082c180c4a01d4140d10402074505007007070103000c1c420301c42000042a14207010049074111071700507601c581410301d000c4d08100181d01c0020a11501c0c00107000c130000096406003c0c107180c0f44a6100c0341090400c484c00c0940c0a6041d01d41d1502c1a45040ca00c080312074102030441d4000d43d00100c0200e124106d02001c18000c0c45111090710503889141411020b160707156219034082c510b91010403000c2030302c5e0000c11109003075a0344080c0c11500300740041200c5070003c03401000101c502a0000c614503041d40d00040444003294450004242c000500d40e00b00529803003074003106031261080f0140c64460801051000c3c51802000303009a0340d41583c48184103038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 486223579 1250 486222329 486222349
    0xd0509060403081204050607030c0e0603130209040b090c04050c0406030c2f0609030f03310303021206102313090b0114070201140a050c0f030910030209100e 69
    0xc60215912000c4103a24180b41c90700701c4043d2211f000340c82c00b040c01d042c800e0240b440030340e080b42e980009401c081000c01032140c2c8094048480040300c03142180041e191200321920a60143d00c0081103803510030074450429059a20f130328030980c600340400140008880a0324141c447c2071400040c0c02094080a540501c03280480142c8050111400f0907003900d0748500d69905d15254080d1001c980750588815941d0044894441c1f0501040c0001200440408925002e0000c560200c44108100304ea00c031222603242c40041c2c00003030f00001c1c55084002409a2603810440076110b9955201140c1d030010309501d0302d500e101343c000903c1440110201030742d00642d41000100803d010607190303985000002400800e4040e804030f40e040381c80c03240b1402c102c804c0e01c034400d8040e120302300011107400c0e04410303941c880320f03071507084c050280820070b0300000030800700c0d140340d440c000119642c0c8000c0040003e1407181100407410140100210f12a03611501c04e9a01101500d04288150205c80c80018402c812 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 486224829 1250 486223579 486223583
    0x3050604032606360c040602010c030b1c0804090f0204052b03110c15131a0d11070515040209090703110402070c0e0403170604110703120f0603320d0509060403 70
    0x140c294180849605c0a20050080340e2041d0002c01802c031180708241c040d10061706020394001018481c01c0400c044560841c6076451040080c40d10f0140c40d0071803141120102c4260b4a4055804a81440507081c54081c1300e44c4405000240c10141d1009080042081d21200c0d0090401030301c00c0c0101c401071390030060900e02c03540084c04829507403040c4428103d10b4000421001d50f03491640c80014019500d1010190408420707411a450031541c1c2d00b0002c09014002045000668100070034000300c3d03000d00c107156800c156544600d00500307090040251210029002d03105a80042c5c904100040388803000b0b05850906440141c0c40703000604054a1100c1d5541c8038442c210000401c0100305944003089880c42d190580c03001c0e44c1a00c40106020460b4900d00018108540c2040403001017402484899854142e81b0300c00b040310f20b100105030003940d5195000b10345600a4a10407120b800c2000b008440d200782417565143e04101c1046e1141d924442c060200d01480400905154261561411280555 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 486226079 1250 486224829 486224929
    0x90e0f010302031e06061003110a1d1c0311070e150f041505010e180f2509030201080a0f0e03120c0306150a02030708032502010b1e030703050604032606 67
    0xb50ac2600003500e602125083c4580c02c520300d51408046241401162210000d080d1070072146582a5505540407034007203021415600c240000080d03402784030034807203210b4460441c051a03002ca884040c02158810050b505101d681410301d1440c12032000c3d2121800c0b90000d03e001c0035410304a40201d4121400c0e945c144492812882c00c11420b4060b100c0705600440f5401c4a44840311003e02103180d0800c00e85d41141c00140340c07001c00700090b40c40307884425005414508005426076011030640205d0703815298050b125000030541c02601c21070603214560200c00d40034600d2031440c10320001250030b0300e5070300312001d40138001c1183e0841a10800559006070752000d10235903a81050364083e80c0302a100c3d001a00d10710640b50100e10304a01c10b0085000200000e03000b0303e01c525138150035000701500a040590140b0600a0000100d0780c00c0009a00882c040e40b1001c07960103503c24014558240c103190444090310702803d00c0050344450f20220283c0c620891110158040780d80c108440c501c003150100c28403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 486227329 1250 486226079 486226087
    0x7350d1d1f050a1103070b0f06010315030302162102042c01060e011707270609150b030405030405060711030d021c11030415090e0f010302031e0606100311 68
    0x840e0000c2c000d0241040c0ea8035500751458407070042070350340d10994100500742c98144c0e01003903c1c40744224000d900034005044c00300e25141c001002041d4061580d0003900140e11442044000101042460000e8040035411380165070002a9280401e101044003c2c001ca5540302c000c10305807142001084003100704d10032180003a0f120300c1502d000e049180640200031504400001d100d913091075081c08418101006012003034581201c440300c05028a151164000034800a014550054405c000160550b00c0b0002000104440c1e607490034200e83e004a50241010400d000103c6c2c4000f06903400c4070f40445049a48060030302d01170180c0036803d481c254162103214945d09145801260711b8203138120710000456440755007042280c03440c0a00c6a000c0098001704400e0082804201c1c038010300e03440034245906043c2c3d03261810011102d0840750302d10300c030260600603c110b103001e00c00c5641454640310702c1402c41c0800246542c032003070054000b40c42a40c0c3d40480c2c80d00c281c029040454070704610703500180c0b6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 486228579 1250 486227329 486227389
    0xc010204030c0311040615020d031508011e0b010c05030412020f10020102030f060604050f0d1b08100b0904020121090203010c02010b240304020d0507350d1d 69
    0x109000d540c1c095101d1741c1400d0022410801a41c2d10b44640403166009160010110074150700610007040b0401c1c0c03510b070700b40e00452404024018002041229100000b03402c1464089108070b58244410303904002806001e039001c038000005940c20b8800c43c1401c07040603010351000a400c0c4042002c050340040c036040780345001c1d94041d40a14410011401c2065050351408100f0200d4440c40c00b641d9400040c4e4600c4c0d01072410030b044150b000c54440e100b0754000b1842c0c9085008034088552001255600c040202512a08039029000070f580702524100c1c90b90425a001901c190f0100300e08c14118400109114000711340e94011b0100940c01800810005151100090107080d4152806004a010150382c02546170b07914080c01d20503c50308141c1c2c1c256280ca0b403c0110307200aa92082c0c4a5106000b4042058122442518241c01d00c007400c04d01001401c0224200e503001014924445401421203900c0d00381e00002a4010b50101103c0030203004d007548001403121800001e070020042c42c401d25412 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 486229829 1250 486228579 486228593
    0x60518010810051026010204031113060324090f0b0a060506040312051303120801061101140411031002030f060315090d0c14030a020a0b090705060f0c010204030c03 72
    0x810780310000251181c101e09210707004140d0308207940003e40716034140010410250003502003100d40041c00300242003602182030140c02d98000d50410345540c14009065019480d001900c081d860042c0001885283c1c6945c03a860003000004148030580c079401042804c1c126201d600101046c1ea00800b15a240c5078142048840c9080c11640900c200f4980503002c04c481c0780c9242aa02260351144005642e4038006500b12110f40041082a400d00c032030700c8000c40051003000304518207201c1582c0303034990744d807400030010034800031440924a1a450b00301c89000c02c072401c03028240d100d604a543c0e80403041c4500007080c076007416514004140d0744040b0a016034140c0004007a4001c00084041754040c80406031020107210007078808600359070000790201c91040c058040603c104d4041c0007113920a0003a0b40e0300d242541e120002e4413005070004040d203400c1100c0d11182d59080201407000740310302804c3c400802e5040c818108860090307140418100c2044001750102c4003d0740d800b030440c0d00c100b562440c02035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 486231079 1250 486229829 486229831
    0x1009090905010b1203090618040b100c06110a0e1002030d021305180606121513090221030f03040c090204080706020106080a021e0d021f031413080d060518 68
    0x140700e152107418a0450b010004156200c6c160b0041c4846c0c03800741d440d01010b4441000c1740d00e240d003054680003000c0580c3d81d50401d290009410761105403644066140190442d006007144224070007040c02070100c22075219410031200c00054480384003103c0c40c1a002c0c0e1940c0a90040440340500010b0750401e0481100506401c03500c05544020080c0c03209424119850f4084900c00d0300210103204404d620841d51141f142c124400f680a02030000004001c52803041c4612a4440300980300c0c55600114101b418060280c82401d81d807140007001025800ca4591092190b21800c039040840490280100d0103144001080c26a504558a6503100711040c1c030340e003442c03107000c01551800c00c002507020f20100703141407030950051419121004508003c090b96038090502e1350041600420340006840da0025034440e40510000c0000d54409a4070007800c2d21a803d408030496540001400700310b0a0420702c0882c190b81c84864551240e03010650b00c030003048554002c5600425100b4956200c1604040303207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 486232329 1250 486231079 486231101
    0x4060306050117090d0507031704060c08090609030f07030e041a09090d020304060522030809100512060108091204030c2d05100c170a02011415100909090501 69
    0x868002c850500f200f1182c1201103900d80b41e2604008842c9161a03c60030080144902c2130800c000326070320501d10624182e404460454180390340e01070503030b40143c118082e0741c0e0140c0b000c40100a28a4104180754807400360303000039500361a010030100101800380410400200001e001000b0082c01080024540003618031020b000300b0820021450320400851008185201a00294070709443c126045030164440d115003807104038107401c295100341f1408040c000035405138101c1034403a2508807c2150b5000c0080c591030034000208004640e05000300c070307020f620402c00d080c407031010303a1017040240c1442d0005003003c0c00100002004030030842d80b2460242900c00103d100c95400121142c5c28580030101c4201c0c2c0382201282e0310030030052403d2040070b007407001c417031030084101030f19503031507140c2c001031110701403011070001c903144604680c2403084000c40312050b0151034280c00c1001101245400d00301ea03642c01030782c55004c928659405002d20070000e01401d030b0b04010080381418614000c128903424 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 486233579 1250 486232329 486232337
    0xa0608011a0f03031e030402060d0c030603050106120203370803160801050303190306170307171303060e03070b070f020607211a030a0503130608040b010302010302180402040603060501 81
    0x4900320ba003400019a4814409030038160f03140d0803e0030f1074680ba50001403049038060703410480540050794034000c5408000194401203402411450031500351030607600500f4034030030b088a408001d40d60001e2541081c510351903a1030403207e080c0d194001c4140c121000071240b0740c94001c0b0a41005030320401107128030300c2e1000a5008480d03c8004544d215800c2c884d40b80d142e40144594100e6141030a280e0007916403a050004580b66902d0f400d1261340941a640c08140e08007180c0c50041c80441e0b00c00e01c41170243c0d01007a9107800048140c091205040c0c4c0000382481d0790b5205d02d44516007003081159000d40e00009031055524000c2c6000f00890039403092440140100350100e14030600035201016599890340c0725554081c3c2d03154a08005121001050320109495071303036140c4c10b03101840b407081c42038000e802442d5519841c07001d01348905a0740d4460420810309508000110b040604158156682440c0c00740c0e460384c10100d0340b00440040c035000307a4090300c0050f00080d026055484801100e8083e22 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 486234829 1250 486233579 486233599
    0x3010c0c0c1d0609060f0405090a0611030c04030807050c31060323070b040b0316020703080708070203100f021918031106160b1902210a0608011a 64
    0x1c02014042c2c20340d90000040740704020541900c1e003051500c1c0c3c022805171515240080000001d41969003d490004040d0440611107041c02720600034480301c0d41044000c7c40c65400c009000760307150b10551001909101021031060104401030162180401005004060350050001d46d01c409054a81d08911050154000700748058070381d01400d01166040340202d4058520000d110b100300d1042c940c074007800d010b5910046020451000a08040d1031507600c1c654403490800186855803100d04600070540d400000c08000141c0641c0413a50340c50b40c004080ca8503090307140b0101e4a00040a440c40440394103000340c0d90220800da601620408940c003903d03c940042c3c07030b035080d00e0a8207421000c4041c040c1282080c40819416402c55440c020702818191420300b181c2c81c41001005406000c68403030f912601031180316565542454050151010110705c0c1030541c0e1603103150640444001200144a0710010300440c003e0b80c044001001ca0400a000c4003800f04407503180c1c060180b180c2c5200e0007800b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 486236079 1250 486234829 486234839
    0x3240b040e060705090a080a06090221061308161412090117040302031c0f0605010f021b01030b030a06200415050915070f0309050303031501031a03010c0c0c 69
    0x409448000507418001d003100b5101c2c024110303110b900c0b01c2c00042e000100c426000480560401003406420b004010019943c8101c1c030401088034100245422540d0000d00010346d107030b2000c01c00b035800481040040307403d80700c249420501c50154560b001c402910321101c1d0f030103111046661040c41c0c8822001c1d940030980c1090080c90174018451603600160350f003041e00c1ca0442c2d000020b640c10030b0081c0100d90800d0a60401c000071000440001030b01c2a407202031032407046490b4050307480604400d00301040600060300c8001d55400405204100da00300f04e62040c1c001c0d0340a41d1240030048409402d41c2d82c05c142d181040c4001c0c10010404007880e4031510701b598030b0005403506403001e440c01c021859401c0000510105c0c3c2640054036001e5000205080078030301c1c508010001d000f0340c0d204000f032045444050502800012807039100301c1c003d4000f0001c12018200d100480304558100f400d0018500c4110600030211205c2c07000d6140c0c0540c68402c010742070b950050341440f1468414420800e01075254 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 486237329 1250 486236079 486236081
    0x8060d06110a0801061d0f040908040b13140d0602070309051306030317010b120714032401020c060d09051221090706080c0f0d060e011401020f061f03240b04 69
    0x510401170412040005286e06850400d0360340443c80c13401080440c0000140e120000303d40e005078031000380c1c204001600c18003400304142c04d60040c91400111082004040701055201080c0c4000a1031168005030f06000c05000700d4036080034080c081c1c001503440400e400603000a050502081c0c0104d280701c50842c00d072140c038242c060b042e548080c600074140340042c0f8401005150284c0040c0501441c0b00c440402299400c0146101c0c06100c800c03202c448442030446440801103982450454010800866003511036904650094800c41c4000450000c1418118240029059107801d0b12100007541134915600401080c2c200f003010718044025142c80e601c01c2d80e103409610580300070a11000010b008030301200c0240840a46a1810502d4402e54544410480310180c0142081800b0a40140a00b4030788440301d4414081c20300040010096400d8030a56440d0002e100750004500310180b01d0070140d410061800075948011580c620040391501c0701851400d07500e044c07000c5032134403c0b1220341e464a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 486238579 1250 486237329 486237347
    0x1b0d0e0d0206040302150412060f060b070b1605071509060e15040b0c041503060f17070b0d02070b090a111e0909070f06030f14010b040608060d06110a080106 69
    0x3005002ca86850310359030170700030800c2c6030050940500303105110010b0701601c6090380341c0c0300c54480c1c400000c0304441d56004004480f4207820030480600c041c8a1900018801a080c54201510300d0364003030240780300801107405104140e402010388481842c030400c005099007200c044907100d90010b0040e490215201591110038807440001d81c600440030401080341400e03030b130f80c000740d5504070580707456100e40810358440911100c0000103a901c00e410424004400f1002020b0700c8400c00320318080c6405001d0039501c64035400303116144000003803103001d01400d0368101d800c111751001c0c14403418a050312240b5240c4980c51420340d00e4081f5658034000a140101c107500103990b0207000022000201024844100e40c000c0400c00140f2803028081401c030226121030008010903500428240c0300c02d040d4000ba20b0400121140c10072a140060028044040554040e560b85180c034116503564500040c2c42e020300c41201624651411b595507605003810f04c0217004420264440c2100d40c0d90742c01003112005a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 486239829 1250 486238579 486238583
    0x63706051e0304210306030b160206100f03022209050703030e0f0616050c130c09051503040210140304030504030b090a05071e08010204080f1212070806061b0d0e0d 72
    0xe0b00040d0384100a00c200c0c10000004e00e580b40005a280d101d03616002114801c0d2403107602c2d601e0100c20321280e5030303040020503401b012511140d2541442c1c84032034070052540740002071046440044485040f00c01c112508010314603240706104111450400c45d03118146404141c5c0003560561a4187e035040c9190300c0c418010001d441180350940850003000039400c001002c43c1d070790042c40130b21031304c0380c1c0d58542c0c559081c000c0b03c10003e80d0314048000544500d049510150050b1030505c2d030b880401c0e0350703001500e51243e010380e807011303010741440360460304401d50340b0b542086060040240b005065020002d84280c030321801c4a140f140c2c960102c20b550b901b04610000302154001607050110400c0180c42e41c6030341e0345040039418040e44480406007aa00641c2008085a005000b028040181005240300780c3c843d50000710301d0650840c00c80070404c60024000d60902441d00082a00380e120f0401300c4595042e0012112000350059071036644540c03c102c14400021079107004d00020389046c1d00716210144d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 486241079 1250 486239829 486239843
    0xf0210030203100320030d18062303060126040b0c0702091501121a010e0d0308070c0f08070c0302011101060806042a0e0105090c03063706051e0304 65
    0x740c5940c1d600301d40303000120070898540e956550b5801170341c3c900300201c0d4031150f40c0380c07a2150140038a0070300c043d031048103910040401003111241100010b01d103055040c000741d0002850340d0b07541ea0500590300c8100070035200202940241131443c406c044994440c0c01a0f2007000399801d80c1c0c0340d0000c00c1d0b07454060b48030080d5000e203002c0e01107045122101144030a024040c10f1800000821101c5a001c5419a02c0100309240001c50040030b99a03101c1310002c50b03188104d81580d800400c5032002030480c80c0050968083c0820701c2c12110600900d003c1c0f0001d180d0748581201d41d80c030118584011085241e02c030172030105000f000e0075000e841060090b5805d03208002d00800456546495403295000045040300503108541d2107031040910b410030841c040d024032024241654540014402c00550061a0898400080c403c6c0541aa074460703403211381e001c1034203680b410003080c0410a40d8198040c80324151220203420000b91041d0010043d000c00f65140c06c00e0301600b602c114420300d0900c01214020111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 486242329 1250 486241079 486241111
    0x316200603040c08190203152a03061201140703180c03050309030f010c27050a1d0601030b0d020f13020406030c03150303020d18030614090c0a08031c0b0604030f0210030203 76
    0x190302000300700b07601a2001554408802c000903424151809d1000c074104012000000c200f05414540304480b581000140200702401d00c4062031603400102405800030182c0751600080300c003840030f0721400100e411a10009920703075a4903107a91381e41e1050740d14600902510325418015030040c450b2844100c600e443d10301d5040d00890400702c00300b04011088000485210340407510b6140c45a03898017074000150303c0600c40808400012140c074005259031704040c100320204c0c2e00c1c0d407500d402c0201c041d941030f5003c4882e044803c00044110b102c00002801d07051000c01d0006103107505070020300500c002c1d03480c200800d4009143c014140602800050b026902a41c8011700303242c8501e0400441c1c114164015400584a54569059030080f1034018000d0b115003042c4401c0240c1404a074840c2c0100f1200360b28628645000e5035103e020300003120388007903441084030700b040e2800d4001c00002c61700249000c0d515a1607140030b9600c2183c404040c1d02514044c15407400351070182c402c0302d005100c603880131012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 486243579 1250 486242329 486242353
    0x60909193305131d010f020703090f03080d0e03070b0f060a060302041a030403050d06060f0806060c0d0806030c0307031401061a03061014031312020316200603040c08190203 76
    0x191404d030859000064800c0010903480c0400e01c15010000c1104c5005039a40245040040000904e50001880091b0301d036020000100d0320000c4502948282402007210f00366400d5003419801104c0001e0300d1890102c0800404000307801c0814400c0304100c40800210b5107420342141207000f0b50081d20012142e40323001203011350003040a964440c0c030138540503142400249000041c0c91040c1d004502048011804408064010460a50055081d58018101210340400740c2d030b2081014021801e00c014000810142c8c0c8090000300c403008409000c80c0e480325074130b181c1801c00c1003824031800499440c0c014041540e81642140c40e03611400080b00c14196150301e4101300c289600030550300280400c6c0c0304505200071405010754400c640303111184440720381d81d00b000e04601e014203043d401190010040415100e1007240745004050300004107411800300003030740d8203481441d00752807076000c503010040000b0080c88014601c10b44070b018007645c2032885414080c0782407202c2500000d506070800e00140711 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 486244829 1250 486243579 486243581
    0x60f020304030611040b0c0708010c0507031d06040816090509060f0411010314070503090d05090310050c0417030310090b1c17030108030705010e030906090919330513 73
    0x502c4d800003241e64a4240e9900b01c0071000e5220035065260307900b1040d400c22886d0b0007032265034030b01403c03820203034a0141c10340d0300101070241810400d14400c07651f00b0303540110f4a5000039a40501400000c940e03104c024203001c1e01420710079209903007005003031000080001d074020503428043c0032404003c1c4210b44960395040025003c480d05241019940d080da840c8100700044198066440c64807159900e0801007081801c10000c0e40c1c284003480340400042141c2d4500242500410f91985800906a1280b9003888030760300c01c941c00141c0703490000701c0c07600d000d5601100035030158442c0402e80051a6a503907000050b150007000442d80b02506ca0b00071002ca00340c00e00310a0181c0d10031048080220035034100c80100d0f4100ba001072031580e001184100400c08240b05800d4405010401076080030b20500010324a07100c2c0c2421940034100610202d801e40e1a1610710039000c0e1074043c130030302c50780e00d560014801004030300c0750b50002042049000da145821815454060701d80c0030b411910a81c0d912200b6030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 486246079 1250 486244829 486244841
    0x110a05030c1e04090c03021c030206010b0c011b03050f010e060609040b042a031410090b0a08070b030a050f04110f1816020f03040b18210d0207060f0203040306 70
    0x102c01507010049034035a030b42c40c45282202e03481460480e0445043d03005002460403c03e445440c242840008140805d4000400f81d0449004e518001c2d0b9540300841f0240c0903046003003160b42040c00703007484a0441d6406821241c46119041c03200d9507940c2e070391402009201c0c81510f1140c1c20002c1000b500107942000d803c00b46411002400c01306000741c00002644584001c80e06080d040600b421a003c0655818056010b02c4550a10320201c242004035030900700400741e1203101d0744166224034000080c1c0b00e460109004100c4123094400d8503560780511201d07079204030b544000e180e00e0000003500d82c0418504042c095504180c00792801d001c80d83c2848244101c1601c4145e02c11500c1c1c004800030340b0301d568403c0c410150b84a0055100c2aa040040e2800d119000b01d0b00c515001448213000941110050394480d040d600383d0b042c900814400481e00908070b400504103240c03954801141c140400280e001000c84203030342210740b103540d40c91040710346a505006450043c0c108000410200703580390401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 486247329 1250 486246079 486246109
    0x20304082511010207050108160207030c0602011a0d0f020108040222090516080d08041e050115090b0d06021305100906030b03030f040b0313020604060903110a05030c 73
    0xc0c0d480c00d044800212000c0300080028140d0700000c1c0900010886255010503000000780000c103401170030000060000b0000802d04449801c5290f5860005842000920002e640010031055515101c0500a02070144c0030591109007401410b801010300300469468040341d0402e2030304100086560046440460152007a41e109031400307140c410344a00842d00408200403070b400010101042c0c40c000e0b09066100e01c260b010382d5601c2404010101011950030700c103a0462521802a03600c03407034120900b00031600f140f0a0340500907404c0c020400d0543c0078a601109541240415030b41d14407120054400c21200603402220702c0c41c0500000d501a00030f070014460216843c51120303140c401051034081d00013000300020b000700d1010404190140b1402201c040f00781e014514015015960500500c15840341c100801400000100c0c2c0d400c0c1909150503a42d4000e010550307455852100420030f80240c0010340350200c82245281e124646142c141048401c0a0046d000100b5100200710728400e2004513 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 486248579 1250 486247329 486247343
    0x303050d1814011508060402091303050d0915050a050c180f030303040627210e09010e0a0b041a1041120609150405010f0503240703020304 61
    0x458000118465900b40b941c400e03010001a203210728091004048486a02c41e50058020009000158a61001a070f62041c1905076201c02d0440d5468201d9161041341c8000403541d2070600190100220355000d108001d5984406200644400e44824210f80003075402c8204858104500304418603a00075589403140c0041004c03124408002c0440d040d9881141c0441d05a540c8000e010030000703c008107040341c5c418a281c00702d8818500e6a03003000c000b07a00c00368075000fc42d121000301800ea1107481c880045902c080c0c82d0600700c1d40e40d400407080348882980e00e103c1940c02c1c1804050b070b90901c0d12601c500c1544000140b0764500b4518180b201e8005024030309010000c210a04170070b81148003001c250260030042200002c100440c50304c0040340d0540c0c00c0c00c0d006003010070901d60340258821650350412011580455507440e801c1d000c540300700c5080b0740103070090705041c00092448007804802c001c8440903800e41d103e074000d51150b00c10390030031510003200e40c048040208a01e035219601030355200d486084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 486249829 1250 486248579 486248621
    0x20f150c07080310150f02030403080f041206050a0b10080103020d080c0f03040801110a1709010b030f010516022109030717010f1a18060301150806010e060a0303050d 73
    0x390503000f0781c011113082c9000c00d071450040103080d103003107003807003403041549052070040c101e00300d00941f02d10840c4005802d01e50041500200a000130342118000c00c2d1072881d104140e00e9524040d00507010880d0110a40c925102c1108403a0404c000b8940307140c9140e0380d6130a060b0782035a007044070400700e002301030b14600801d105841c5006420171100640c803003008002d5458511f060740309401e492824400909085044c4102462035420800c0c2640e071000c2a2030701035044d907a20200e1401000040b0b04d441d498465858200d4901c036040d03002600442c40d5401c40050048084801c3e81e40f20350740c3c010061900d0030384240350720141c0001c0140144c0d05004054400b800e0303850000880d40592400c4c120180d9640f545081318200d203178440d0303454540700101156101551900092500c007400d2003690b1704540e01400144059a082d440002003404200100c85541e07290b00c2c0c19075a4403c24028045400741240c081602890201003280481c0d80c140c1d2564070385021240d02e0809081d480c1008007280d030980e8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 486251079 1250 486249829 486249833
    0x6050a061107090c020609061006050307030f0b0402180f0303030408071217010906061b2d2918030406110307050619061409130f0f0506041101020f150c07 68
    0x1010b200b1340702c96190700809a0b070400c000024100b54000c0c1c01c103040341490b078101f007044e1030300801030303d51004a03800e00040c03c1c0c1041c0c07001d20217801c80c4005140d0041c400900403000304c07079914110300507410560304010302c0780700704042c1a600d11003070b240034203a00000d020017000903005168640c2420200d2900d91402030000d50403c208440a03013086105940364041840040e80c043d00c6030320b176824200411b012203070b0551103d0345508150070400c046c80310325881010300c82d450400d40162056001a6210305000300c00303a1084042001c1820781d22500301071003c5050020b181340e00e420298801c0001c0d61402e841c00400b03540510380c4041d001744a0100744000342c017140c000d1140c541325040043e04c41c141c040e030280c240b008540d02504042c21519460551840e5611080102c1c0e03481012242001905850740c01c0c002e141278520700d8000c0580c02c4600c11002001404124076010390310400c0102c1032110341d4001039803500c01210903075181d0350100307000341180103584100d1504480007802d1640307092820717 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 486252329 1250 486251079 486251081
    0xb0109180605071e0215010e1008160f0f0b0301180605060c1507050705070e0601051306030e010513050307020907110703050f0d0c03020601121a0a1e06050a06110709 73
    0x101ca010001c00c100c00749810038610310340a40d0106520700c5c03025068031081d2110410000c1018080c050b0700340c00207800500142180003120014080800c11642c10040c0d8140b140b4480445020f0b5502c142644a0f00161520b02c100700581a1081602d107241941e00304400d40c07840d228550030042c00c0301e80f00d403400201511410000c000c404030742409403000701201480e100300b00c1f07000b414440400c5000c21100022a8002c620441030f1800c0c0c060300500754071181c0040303569025071000c002d40050708000000b40b03950140c0c0300c014000403100007481155100341b90340040e0148a40b0282c225001045007a00520304130341b610346e02c0b10076807c010405c84810a101481c002c819001203950350300084102c0110754080000d420501134070b10740300c8445095560000e46891042c800d041000360400280410003441c40305401d00800b41c001038000c980380c1075001c080942002c40320355500c450304100002c140358590056800b540d6014000400c5240380940c226070070400002c1441c09070141010200300b40c015 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 486253579 1250 486252329 486252331
    0x9030133061e090b0d0b030d0e010c0602071407120c210b09101503030207150f1b08070b19060308041a0f04060206040b0a02130308030603100e100b01030204030b0109180605 76
    0x40305c5800a894500d55042c50f140107a40f8040e0802e01107460401000c1d6a0700a4050801d20b911403005611120941340c440e080142070180145e080c083e1100204101d09a01c1c50004118000c0e2094007204e0703500c0c2003454001c0c82c0e91161144904070392966201041e40b251103d50080c2d080c40840c0e2a20030320051000444070201c0302d101e550000000c0402c2407560421150018000f49802020400c4c0b0303030384c8042c110860508004003444404960307001d0350510500a4045160031200c3c4da980e420651415001100d0700b261148000107a805041441848600c00c2d2400d4a500443e0b00349001e01b814285540580d00c5040060700d800f0802c5108510500100540020907071600207000a044c0b40c81c048a0000e00100007198191050080445403400080180201c0b07820110599480d1034800c0070908200d0b01001d59800035043c071081c0b140120340050140c40b54000380e4020000c5a012000440c245d2046d440003904a4216900600c802d140c242c0c4900d0600c006807001d1401c18035103649003025120 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 486254829 1250 486253579 486253597
    0x9270304090b030c061614060c09010f02060f181e100605011e030902040209030d0f092c0604090b0f2a070b0a0209030133061e090b 58
    0x11404100000681c0202e006494084010744416201040816628011526806a20307185044040d00340034240c49040c0281040d2400d5400f50b01d040c0801c0406075108515042c000350302c000d180041c00d480410818043c101d00c21241005458010740141d062070468a00b500d2401240000045003003002c3d41a115444040080c0619040721580d410843d1400d6005c43d0510107160700032520825a00c4203071031501c0603410300092408031703400460001d000f100e05842d0035200c0c4d4100c813141030350400300c926a500021f41e5042d442c5c54032620082c02205039050400d50304500300441d5140d110707840c0f0841d80d112038090000100c49031251070300200d680d400c0d02c041003445540c2c4240282002400306c0100303250b062100c098100c04d00d141c1d11800030b10855001821000001020409007100c0350101d820b8460000c000f03200c2e03640c0300e598001012802038000085502c00340c05c003051b03202c10000040c085504507100c140344120714428420014244602c05030421140a07804118588400080d0610701 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 486256079 1250 486254829 486254833
    0xd09050c0d03031d0d020a0609050c0603010e09060117070e0c0f130602070609180b010c0c08030903240106110a0506010608180703080f1c020a05070b0a15050927 71
    0x11151403d11280c0c4d910301d22484540d8101d0701c200b641e1503030000b40e04901070790b018400080456041c1010f038100a454814035510a00010001400c00031441941703029001c81010340c0c100341d03038503403002009a01f581d407a611542c201400400c100001222460341c400310044003c0d00e0000b0000d2404050303400f184100942c841342601c140200c0768104904809400303d0b00382540c1650078984a03142c82a0410408071046840d41003548a5074400c01c50251216840754101c0103d0340c44090681e03c0b41c00c16292940a403240350301b00310346000340c1c1c07940000030440e0708841c0c0000d034240700742201d81c020b200400701d01501c1000031480010b9001c001d914000c020075a1100300604103ca00f502d1400c0321032035545119406440180042101c840031100c0031501c6802c0d499803a8034a001c1c1000320042140e0b0401d81da803000c5803071304145070001d00800d641f41c0700b4408141607590b10507a410888003990034001000800e404248041d0401c07201e0150048032441b9582403000482580c19501c207100300d000e00241d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 486257329 1250 486256079 486256091
    0x30703020a0b1807090b011b05010c03361a0f150402030412031d160603110301270209040c0905040f18020d03050405060a0e0306010504020309030d09050c0d0303 71
    0x807014614601d60840302188100f42c40f4003069407001e0352000c140c000c18161a035a00613210f03a580c0100d404a0070b1440d2000c0b40e01000c6210309246000341200e910000109007400424405a030601c260b01c91088580c0e10394000e413842d1100b820060b540720340300884044480030110703c951180c1c0301c0d6440c494036482100301650f10b04900e0b0380240385800c4180501070744c0180144000115201640c2e0b02c1c12502c3d29001a2150750f10507840b4810140c3c000d510f41d2401201359050b42c1103801d074001801d541c62502c0602000766200f100c406284405d1003800500d01402207400d008400e125014507690041c0000076041219002c0040c0446412140ea000821248a0700304a03030f09141c014031002c1ca108680400c440880b540c600807005a00c298000e200b4030054883c40c0c1058000d805440141c0800b0308165142e80e88018003410002008503500d00c240304100c000903841c6441d008591051a40001440c1007910701070a95014090a140c01c50382d9005540080d070300c50710755007400130358a030003694080b0316 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 486258579 1250 486257329 486257333
    0x30715230304031b030e1e0604060e03120c0616050f1c0b030105090a03120f240504020a0507020f13020307020a21020319021c09080c01091a1b030703020a 68
    0x18144030320000c4800c526442946000c079400040c0310600314400e1f62405810009a6490b0100702c541e40c4400390301500c04100031441c2da40c450208008614250102c8442e0108400307000802d00803c5140581c0764800f03070014041803820581c0400c1c103000e905000c0d0030a040310303e00d01003a802c811070400d07000c0c0499001249810143c003608002000c2500200082d051900035152913140000d4040c0c00e00c112840d81c003100003c154800801c0b40d0b11203c04001006600c545040c1c060b02850306a07013517552100d0045041d1416200703c80345000c464881c24900000d40c0c0c01d205200c041c8042c40f0354000e400117001c00b48020540002c0d4410712480c0d0284c021900b552030203143e250700c1d2101c01e0a40d0b02a4407c100a010380000c11a000880d2032100d0010706800c043d0100e04e80710b04000c01ea44c0141c1c0c580006901d80350447e4501003135400704000d41d01c41c0d40c101c1004407034860b450300c10003400c4991030008000c05a15038008045020f40c405510301d07080311845040e032440c0d118040440040e80440b0401c42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 486259829 1250 486258579 486258587
    0x140c030420130c021014070509010c02030f0f0d08010e0f0606070c141e060901030b0a0330020129010908060c0301030203070614071104060e040309060201050a0b03071523030403 78
    0x11741c5618001c0100130b825000410702c441510014469001c0c468002241c0e101e40c0c2c00f502d49120407a03030080c2103803c1203d0000d4503548410305411701c2901441202c414185480c0105410740c140c03501109400901d40d550074010680d0300001c0d0009820445c10400440400c070760101001c0903184000070002214008402e100b00c4415040a00c030b400252603021071032954400c021130b00790200900c1e001c2280d0384204001090b0a00681c0004d10380420507640640000b080c140c0d140c0b5000049803c60000b1035880400d0303003603894000e00d005900d1100704594030300207100302d01ca0790700b0001850100c14580e202c528452800c641915401e04090000c001007085180c03c00a500191860741361050514400c01c00c14006401031040041206a005096650360b46482d070007100104802118030004e0b08003806d000e0b00140f41350261800550810340000c05130b0105003d290b4000001a005064042c501000302d182c04101b0340c065402c02146090354048005841284000e000c400c2e0103030741d928107003450003034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 486261079 1250 486259829 486259843
    0x3011e0f052202090c12152d040c1b050d14031e04290a0609200915120610030510061116170601060f090e070e030607020c0301140c030420130c02 64
    0x48082019510401c11221404210890800054a01080e582007038a0181c4525812f503004540c01c034050350313040e01070090024860b01c078614a5292070005000c103840c107600070f203c100c03110b82140003c1c5c1d244242e05540080c2d1258003030301903600d23040c1c4100900014505032b10360402c4800148405000d0009071040c52041000519035280704005c030003400d100c0303031070039003100d0886a030207000c04070310714107551501c4249150030140758404a5070790b00004407104111308203031402802002d40040c1050454064414180202d5055680000a5261402c00c48140c40d000703000d90208e0044c0a0310840340717124541c1c41d4007e804800383c450100e44001100d24a05001684000c0030800039030712911105170441c0e280002c1d41d058001e09501c5a544880550308039440c85120750b050f100304003c105e0510760106903003d140c90114001e0140c810b0300b04040c40c003c0425101281d07090310400110300020800000781c401a0401041e0313400698a850002d19424030104040e000e150b00d031101c3e141c64030303414040d03a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 486262329 1250 486261079 486261109
    0xd120501030c06050705010b060d0f0e0c01021902010c0c0303050c1002132c0c03060a0501021f050601021608102409020903011e0f052202090c1215 65
    0x20415036255494070a0004150b1180c00280040020540b062120a4100541c6080090007c0d683e6882c6100e85000500c01c290040520614100803450404c00205121049010590082a00400c00e5100c000e000e00303c54012030500186404210008a03120071200085019444031900c900c0c100b078085003008442d050514403944104500d2059403030210a50707055038183d01491801c2a030f0f0030346038608120800000c51a180090307042240452036500203510031002903030b607420301690325001640d9481c1c0d020440c84500301903000f8000b03201c14640c0615031140c1c05104a6868580a0000117182003064020404903002100c5002c034443c081c0c01250702c941c01d403c48001031120081030040c0e014541c0d020b0024079580001c3c01041a070340075048441d2501e070b1400c0b0344c3e101c0801ca20388440244600f105d0101350314245000904041800518000002005d140040001089508200d03c004009003515030321407007440000c07213100c00002c1c40392051406500c0700c402107020700f0800440501207050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 486263579 1250 486262329 486262331
    0x12010e071403040c06050a0c0812041502040605040b16170d14060603041410020c07031e02061e161109092d0a020402070503031509100605030a1401080d12 68
    0x240000660303580c114400b11249071030956150440850111207040d00f030703000609080c034081202c03030100144ac2c2489000c1d6220300c01035068990307080300382c1c010790240348035260205105210030449850700324002c3c416958a1258083e10003055130324212a4803251070310500948011400304065000c40c451141801c400300242c104500c0c3c241d0014031030f4800100020301c3c3c0f601c60300e42800708601c10400310850365014030066449152400d4441e40e40c0b4903038841950103025100d510318016501e05028169103030060a210725000100d145024544100c0c10016448a030070000c49410f84c01d0120380300007a510a80356060322081a0f01000355003034014105030b265802144140d400784410201c24501c1d0390aa003900d2001c0c2c0d50902e0000e05221142d10041d40260000807007204004011000314030501102c2400c1104c42d07201c0080c00b840c40c1086a01d0011649201c205000207805100910b62040c01344c200490203144030034017002904400e0f4010700c1d440d8442a5880f01442d0040b038403d14550100384 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 486264829 1250 486263579 486263581
    0x709120b0117070306230a05251202041706090f06130204060506070c03230703080f1e0d2405041d01091203050601020309030606041112010e071403 65
    0x4803006051818419420b0282200c240559a210148080d07402036030844020440904c2140388080c80c00310a16046801307030b04440000b00c0041061103200d00800c0c1004448149942134902c0d491888210b030300d080203001008210070a124107a000501c044c1a101074042ca15499117508107140580141000c0d1460708210003c4100301b000203090f5a00842c1c04001400c02c1190703001060082140d038212036000700c000a4817070180100b216940703080f20721440d090b0502e00e4607100d90310907188081c049907089070072600c2c0420202d89010040d00010041002540ca070116482040c0b620f40f20500c00a24180c0002c03d800441180d94403520400910712848840c15506c030002c0d0308800160b0b4012144140e50360b646d0800142d6207403000850310f42c0355000030085c0311400e0400801800406800c480041e06180c0065900e504c00b000b075071040036003e0001c5c420394440100b040050481c031039108003043d03020b1100c160044c207400c0300e050007405203000729002130070040c40040c00d003040d030300701c509500740100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 486266079 1250 486264829 486264833
    0xc06030e0d050f0702040e030c0708060103050330280c050702040218030d0905041503080d110c01141501080103120804030203090d0b1f1404021b030a0503070912 71
    0x115103072400c000c0920300b45a40b105403a6140c6224000d076071001c1d4000345401100c10800c6800001030401003100402c45441559070484507507500030901004055820030320514a8400155040740c580072104041c0302200c10308041e4403100310208540410060050300b00f05001790300314418800d41c001381c00c141407000b100302c0d01c400f815921071800020b000303650001d40b403e40c241d40344550f0035880b4001800e8642c45411080010540301d120b005181c1b01e50300c2c000c1510300b180c00c142c0140084a074091b8529080203480c3d03510b0001040c01e00c1c211502e40d40b080001500d2044203200741070f03101c0f0126007580f43d030b405d140e44e600c400d401c00c84001754144440d2400500100310009003001c0d0161040c5000e4026543d2440d04a00754020640f0260f0888402c3d030341c2d00100000e81079228030409208401c800c0d8241c60865042c0501058815913031a0034009803c1c03000780c1015002850610503060f403000d8090b02040c66146983d03c840900800514080301f84880c06600402c480004c028180e1410790200d411707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 486267329 1250 486266079 486266083
    0x5040e0d0f18060e0f090117010506031b010c03030e1212010b04030515220606050102061b0a03091a040302060105100c020906010f1106090f0f060f0c07020a0915030c06030e 76
    0x2d401040d060111281c1281c885684454810f8000040070780b001110307582d41d002e01c41032820050703031240c80355091800081d900e0a0000c2d03034480c140300e400e8082d02240c0300b0000540e500a0720360300a4080503102c00010b00c0952080002c40c040b0002c0b41d807500e513510b02e4043c41100b1401c060700060403420040200300003103500000c82000042c456a1058940c3c0c440c1c4054a06c0041c0c08030f82904c06452a0070b10030240a0039134415003c680c000c0e001d5401c540d40d03a565802d840f0700e4800004040007001d0101641d481c0c403c0d030001c81418400c00d1550021031240c8a04504c00c1404c560031401a800b9000512860410144118030110a0b04000ca84000c0507030005c0c4d0200300040000e8104200e41c81a0003503688180036280c00d480e8100c054030040d04140c9049074442012401400c21b0b441501040c0240d0b0780c000680c248144c01040070f0f4001ca80b05c90a40300b05070381c0700f0f41c8141c0c1d1011452001098075000f074403900c248000c0f89034a20382c059155190480180840d03a0185052615247c40312200e00c1380 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 486268579 1250 486267329 486267377
    0xe0a050303010306020c210d0c050901120e0c030303150f010507080d0b0604050423011403030409090201140d0c08013804090c050403141219050405040e0d0f 69
    0x400303503005d40c4441c04601b2031460203841805030900d50b02108810511104101300400d078440036110144007400c41300100b074030507100d103030102400038103e4080040d1152080c2c2c0451420028a0107841441c4203210001c1e20f150070680d041c0280d03828004040031585404074980e0120442803e0860030500251643d6159010b0040210039042d01c1c0c104003081a9603403c11035001e070900401c20014403004014048a6040c408106600304a036600089100103000b130b0904941c400c01002140741508114950020b0306003900c0490511200046040e40b01c0414806410a010140c00005608a1082e0000c00070032041c0c1c400701100740014104898408030301d4120010444031444542c1c2115000c0002c0300d2840b4a51103150b140d4a0455030603aaa0b41c008010030881e4060402442c2d691701da01d2000d9100c480c4030146000405080105503480d42005001c05411249800d00500300b03031782c0d80003080a0300c440703403101001600007038054200c040d007220b011244044107144c81030352056000c00072901118 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 486269829 1250 486268579 486268583
    0x220e0108011b0e180702010203040615051e04090f051014041a071701090c030e0d0503011512180203010c020d090501120603060c0801080712050c09091603080307030e0a0503030103 79
    0x458490a0341c0d8a8864008031403500c002c1110036402445c12000c005e000750030680d0115000d50416508c1443d007403d0b42c00520a981005124039000c105414048845081c00c2540e141c00c03546460794400400d11003d04002c000340620b000c3c081054240110b0300c215581c00000103c03907480c4030180404141c8c20314100744051444038800100da16150020388510100e14603103141e4400d10310001c80c0c80387c00341d08116561030b02d40d202401050800490a81c50310000000d040c005402840108000c81c0300041d1002d01200070304001502030321400d25a401d4901d48510b09414146c404103d00071824240b0850070001c0711480900080101080700800c03150380e0384526810486502d5103060a402d41d540724500465000004116602c081040a040020248a020881d0141500005000c0c1140d084290701540c00400b0303118406150041020024014103868140d1258100d440d103e01c621442e018040c502a0306265100d14200a0050950301d0440c0040341e00d40205902c0c4001407000000d80e41507035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 486271079 1250 486269829 486269837
    0x301140f031905070f0803071703062107051305040f14250e1303053f040204050c040b0d050a0b1504051905060d0b010203220e0108011b 60
    0x6051140000e19051000e0201d100c601d04203590a0100700c00082d41c4d000715021301e040a42c9141c1e83d26070756502ca0068001c050502c0101d501c11031603002c0924021544000000c008501e084110705c00714526207801c035a002140d41c030002084c0050300d000c00140c120400030326410320180ca030070360360030801000404000b0001c211440d01004451400e00800c400c141d40c810b0342c50744000c2000c80010142c0164460f00001940c00004589181203411681c00700c03035055110f1600c0d00500130100042044043c40c100303c6400c0e0a881d09020390000703002000005140c00951810381090b0041104451014000c6214050108401c1141180d103500755032011788565800601c0d580c030402d01402505d504149582d001080807201346092114030050001c1e14800c2d10000340701d10180d402408a0720040c0500d540c89241800131081d0700c15943c000ea0040001031043d42d05100c0c0c18014024000c2c030780481c5000f10000310b2024403003410748a10140c010401d80001303000206041e100d004107414840e07011030403c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 486272329 1250 486271079 486271099
    0x516030b010e060f0717190c0309090f0e1b0139080a02010c0503040215030a06080f010605040f021306120b0904060b030606040b010915030b0405010308120705030114 73
    0x160700071400000451405407500f5581c2c1c442100004d019805082d00f05d0300010707248640020454444143c07100144002020328145a0a80f01546d2000070103404600304482030a012807086400d004001480002441c0800d26007821544541031078500b403403440c0b1228210400c2c0040f070ba40541900e002c000312020000c42401000160369290141301844901035510b05069001c00c101d500042800031080e9000304110794581e5030444d201c0c03006823800b17540058140d2146200d02da0060007507030000d040a030005112076990f0f5590741015140004403507242d64038a010001c40c2460b016240d001c04403100114684034042904048413102c81c0a9842048a03074460390030100400d61024840e00f00083c0700d28503614162521a02601c0000da42c28024000c140c00315090781018000e2100b882c6050b10303a5040c403403d181001c0d03070b12020310b00404205901e8481500e02510b40c0c3c484c4901070350003104a50381e61014204c0e48a03243c0c1001e005082004020401007008074200c440800840c8421aa20082 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 486273579 1250 486272329 486272351
    0x1e03030a120e03040f030b0708010305030403080c1903031b081b03100e04060c0908061506091c050609011506051903140718050609090c0d1b080a0f051603 68
    0x100419440a003080c0f00024021440c05507a50715036007140d00c1404c0040041d035491604440b00b050a1000800e2903005000c180001506900500070141c0030354221440c002d5065030b400303194181c4d081d0035804203680d0081c405500f000ca210380b054101540c14500b41a040805001c00a44102c50380b0341c017031423000300100701d00c5003643c81580000d240404001d03a0b68101030508100800c410181c000104280b500005007250f4045000c40c070171005000c864440084103c10701103140c0c45013403020350000d10200b022001c0201c1000c1c0320412400340c0010306180c40c00000090844000ca501c46841080c008820001c0a9024044485480496115802c01140b0781010360140104c003241c00d22407030740c920810030201e500c202c050300012007a00e4503503a400e5a62050003254403818100c0c0760000280700000381908c010200801c41c4021b4548006500500f101800280141c4001c0e8400006c425900703004649040703014001e80c07440390b44000c000c41c0c1040000306546400790790b00034050644070720303c001c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 486274829 1250 486273579 486273581
    0x6180f060717040510030605181b040902123714010602030705101e05040206040305010606050d05160e191a0702040f05040b04020d0507180b1e03030a12 67
    0x505030712049540810301809030603900c50f0050f00406010310011002c0031800d510a0042e10101c0f00041d00801c000013420400150b40c05000b8000361a80300e980d01d010000b0941c00c801000101012900140c8400110400311050800a04460300d84174070400c03003507840c880c2c4580131640e1811a00100d80344001c80c0c5800000f8110181102d54542c540c07200019503da00480204091485201074030020b0100300d0750401112400210b40c14450155071807070b42040803a5024580050000b404542000d6503035880c142911900d401120020b50007041e10f1000d01c509000300381c0c00001c040b0071403c0c4454110001000c108242d0001407040c2d00460160700301101d0082d081e4050900740228210b184003110a4a0b02c542c09100d040780154980300c503000c0c12a203140310703460255030f008000401d9500c0d60b408109020460041c10b40700c600410301d000510850100100040e00c5003003402042282c0c1001c100712845403440e084041d200031095910125650100454414121034200200c111001180f144 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 486276079 1250 486274829 486274837
    0x2070c0b1b03040f03021c11010c060b19030209010b0a0c12120606050a1101050108030d091a0f060a05030a110603130212031e1608031b031e010506180f06 68
    0x840c10b800006008240c50f02009101c0d0140c90090310100c081010001400f1540d0142d032402810b10040c144010a140d8070500007813080500450020820407034020015681040d501c0031024800100b5804108504044500d140100400c0c100c0d5401d0410480002d000783c01440401004012072034020031109000d020201da01c5441c60030104413440d202c20014003e0341c0301d01c6d00440840c1e64100c00c056031003c14015241170f601000061424808a140c001e009420003c43c12211480e00032180420000d1500125214900ba00910721540c2040800e1104a8100b070b00541e00a0b000001e0003400701d5980f40d241c5800382810740345207076660b07604007080b241160060700080d4850603049401201000c00009070610950b03104041d4065408501c560442e4401d0f2090020516031805084000c1503c8a01940c1e2010030411801122100c088907507145600c03c54540c40700680a50b50213910064075010346025200030f8400c1851314480c4042140480c1001d803110303200700f0042030464800e0326800300355 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 486277329 1250 486276079 486276127
    0x1d06090d050403032f101a010c020f0a080f1c0e0102061f090c020c1c0308070f12020703170f060a030b13060c021506060301030314090a08120c010f02070c0b 69
    0x82e0910000c2c545a140c84170861400785001a040a02200c5c4191b009a51301043c440161100d681d418064ad0070702885540b1450b91030343c00328085d1400205841c00b41300d00145106a030780501507256544030354036480c070700708020700c0100010308414003213503600011565001140d107400584c02d001500f0a07450508440d0700114016414003a402006031340011f803600407006c00300c583c1e81c840015402041030b0141d14110140c00140102c001c1114907008150102d586460b5107082414045003004040681e88181c00480010341c1c0026001c1007080100b0002c2c1d0130018541018805003805000204200c60300c0c007002d4554803051000c03c3e140c280e10304003030a00d60f0740003200307104191298902946990386040400500c6222a00044072450070b581124180c030740c10f845095030356560b03403214012900140e60795608074465550100340d8a1040184a8008200d00070559580c4030340308609094580702e028001c1e1f01401400003c1c00940c06107a418240c1c5c01c1c100005440d08140c02c90203813894011259 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 486278579 1250 486277329 486277397
    0x9090212071508060415060c0c030b1305060a06050a17070510050424080f130b0f15090103080f09030a1a060405090d0c020f060d1d06090d05040303 65
    0x40011100303080b401c0820441c072503840e03c0d4140d40d1450240000d82c0c034019420038940136695804c2c00f46c0d0b40140041d030403190140d51426842034072543d80801c07003107080c0c80310396005d298200c405082000400c03115a20094904040c4000d03450031020507182d000500540000200c0001d080e1104003003000140010300c0010401d0040c00ca0707812001d4425071042c05481c4585a6011500807001d018a03002244030351142d450490139a5601d685182310040500000c0c82401d41440300000300791184881405080101a0360b161400c010b20359068000d015108a80a410360307070010800b140a400648409885407041c480e40c50301c0550000341441d980d4500105440c4501e803061407402c00340d82c643c0e442064161802c001540f52004a9651207880d0103240e8001401c1c40000e00060a040741041c00c0242d015203914200345107040d1000a83d00c10850601d000d18811420100e510700402029070080220006406501e030700ca01d004242d44224040641404940c86600071800301b4207426a50800790020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 486279829 1250 486278579 486278593
    0x3061b0d1103060a08030a0e010309080909040b0712060b1b010608060415060f05090a0905031c050f010b0a0f110703172101050a1202030a0c061106090d0909090212 72
    0x80d41c00d04541095030102e005070002c59010400c0e9000208035000c2080548030980030440603001100940700d50002202c101105110410702c60711941100d5000b54401c0c5025502494204001050720540c40c034103c1040f41421400c10403660b45004641488603484200c001c100d6600d00c0c414017611b00c0303a01c580e44034416041000300f4003648034a459080e42410310117222841e503503040240850614042da56000e840c0d1004190400503d07845441c0e098451026281000180c11008440c008280c2c0d000920544503010091600407071200346002d03000c1c5411440c10f01c4003014008190102c444203002c00e101a400840c103446204000d00313001140d011811410300481442003400e55002940c080700360340d404202c85222914010417440c144d45000e801203002c1464102e907a01644c1d6007000603609806500e2894002ca0b820b40c0010024090a46030300249560743d03a1600d1821000519004442d0071507614003100c035a116900004880c104400070403000030b1400000c502a103409501e01252184c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 486281079 1250 486279829 486279851
    0x40207050a0b0103030f030f050c09060706090204230a021905033c060108070e130603020406031a01090207020904110f030105010e100f08030703051605030313020f03010b03061b0d 79
    0x2203009040d402941da018048c00b10540700303c5058900641d2641c1c0c10310400d000424090034414040c100850144c8404a03031400c160700410210348040001c65a08103000d00c070500e0742140c0d48200394000346041400c520b421000005d0341a0316114020b942e04005001020a52401d0301c01a111000d41040c020160449010000c15049004800584040941000c006055980590000d91003040c0703a8855412083c035042c100821b0000c002200c0c001c0395558000031016880340e1003084090740c842e016003150784d03400410b44440d01030160b11804c0b40900411080300144c445d882890b42050740686040d41c919603400009208410303200754640c066180c10000101241407000c4c0901030740401409028142c0c0310320300e03c07901548600804145070300030410840040d12450003030603c0b000c1c00100403d041e02c16a202130071640281d4080b00810208000d0900f5480d000d00c0003540110704070020400c108074040881c2d241c000003456003207402c0c841800341140e00c1c222000c4501e09070304010308112606002c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 486282329 1250 486281079 486281087
    0x609100f06020a060605091015031508070302010e0319020405150d030e040b12071a0903030f0d060b03040203150703020f0a030608060a05010321031805010c1e0c02040207050a0b010303 81
    0x3c208255403076401d0640c00110707030900301946405480846014503800e41008060b0700716288024810017015950707850140c00c24415030080c0080c0c03030f00a01415811303185000040c02242104095482500007402d28200c04442d8841010700c80d5041d18046059596602031855001140c0750040c4c00c0b9125010b0304013090703401000c1e004c200208640c20460208a40f013406038803220403482c645283e11003101400381c1000c0070b00e065000e9410000b5140340884c1c0c0750200f03042d504403401c0c0c0300d0065000714280e00360030814080d603400f40820300e59050035440c00b42c0000307680301041380342800086500e2012800040c420780403601503141e1011280c0d81d614100000400403e0684180340c10f1380100c4022901c440c0e01c0340101c2c0e0407203030003500510802d1850501001c07144002d0b03840b00c0c20705603205004046c44040c05140548207000300000200c400991760302170410518003080d407140024214540d1000f580005402e4021070701641c00584480d142c1c98258a03101032400d0107005000c3c0980000105540 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 486283579 1250 486282329 486282343
    0x60a060c02041b0c1a0606161103032a0307020105041e09061202030606040b010c031422061b0201092931050a031e060e011a0303030f0609100f0602 65
    0x45882e000745c40e00c2d03182c140241d070000e0544140354481d50800c4030a400001200718201c001d4040d15014511140d0744001a00c0c55104e05640c806840042e09d414008107103800c860342100d001360002d1481c0500b50750000300382d071180e805440d103a45002540c4100e24900510404003500100e0010802d00d038450058407201c00c1c02c070508038400e11a000000e400c90404d4040c1824510041e114410100400c0c1d0341910b01e80c03000101c00115400601145001c1101400326500010041700c00076030803818104010880c50124800c042c80740c01031160440143da003c4407a01c11100342001c0f0340003d01048d03402200d140d0b100c0454180380707400810003683c040f02e10825040e59100404000e0303a903420540054440c91898807900380c1c40143d01c1000c10106209208580316102d00c0e00707601d20581810750714181290a0b00d002800c0980d912210038190f4580e078103420040c01802c500850a610700343c105004d40c4c9400034441c3d80240d609002141124030303c00b01031f9000d400100c034481c180b02d84806000b5a0790007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 486284829 1250 486283579 486283583
    0x1050609311b0506070809122a091305060a0f0902150a09060903050703020f1c0c0311013608100906050a0c0507030c0809100210060e060a060c02041b0c 67
    0x1c180c00010710780380a038212010b081d03105c115641003047c044100a188c07807a000282c1c00a0050851030766100715841c10040c0034110100007404801d1910081c016003401c001c1140c0502801401d140f000300f24002165680409104004a824441c8000c2340002c0c01e030640d4000d40111410710035540e808540d50160548100e650354980105079201d008540700c43c07140c4000b91894110540c10320250500c40da198804080241c500755644000e450703040006c3d25042401c0d105412400d2040c4104000c10b507614030b01c98000d21b00003140ac2e094062910500004d00b621001400302000904649440c1140c880010b014401c20f075410701b0130804020010304964001203401c107150000183c80509544100600c00c80d0580e40c00d814a046c5035000d40d08481d24000075142a002800401c1c0595501121514a4101ea030b0150803080c00001c0b00704299603d80c0c010f060010503560402032151036500a02e401c032981441c1049045045001250080c00904002c003c0c80b2002e80510a400317411840307010b0583c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 486286079 1250 486284829 486284873
    0x1c0201270315050103020619090b0d0207020f0909190c03020604030b090c01050a05040302060d11030a060e060306091f020f03010609170a0c050402180405090610080105060931 77
    0x101c00700e402c01c0c1120003d000c001d50000080c48490302d851502e00b0080c1c489030781801e1480e84c554403a4081d600507040261001d02c0c003a0005100c0c801c50038400f0040b10b01c14025038409a00c1d003070003010580c8400031000b0814244000c800540300f03001074010f11744001c44e00504015900da8803801d120b04501e204031203070b0b00c46100c0d051908039a9480f4200f1550342002981e42d5078102400c40d030070070200b0341c455001c180c6c085484500d8848a64000c20045009255080b0b00103086460b01c81101400300000704881d00c070307030031040400a0b248004102d4685040910100c0180ba03220201014024020500382d283c1404020001040040d0410360010503140c0d6030403203801000c0c480c20700e1a511558040020700e0440009020411030403c2c0d00039040c1c2c505903040401c0d80c000704c4070210307040f43c4088880b07403180c0d40043c0030320a103100580310420280559400074802440c1140100d62100e0001c1c0c1205400d11301d032090031083d410b443d02c541c170081c84912045150243d26080490b04590303a0500c001d245 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 486287329 1250 486286079 486286103
    0xd030302120408130803090a1809020301141f12110d14060613020717030a0209030102030408070204060f080606011b0b1f08010c02070306090309030c0905190b1c02012703 75
    0x800c00000380c031f80c40d0000426042500b0b0405251010542e03201031540d490944400ca4500141e900313004880860300b101070012420b1400711b844080b88015000901449c090f400010311014143c00501c03075070790380c000c0200000a082080440da418214400260104036800c4800c10140004180103004140c11aa030141c8081300e544520124491010002d211191002140000d030652034040c0d80e100314890710040c10300c01800007181c2a40c4c4111001c840211002451500b1071402c1d00c5006c0250030a5441550041c0c1403a031a01c1c0e94003405080281400711102d00c0440c01454400c14504040d071000c1d100b0f001e41024000102807005e9102510b484c4140d804010800410500c10b02081d42035540c000c11504c3e1540c6c40342c000a00190707200303a08118003a03001101050324016124010040103030001041d29200c007413130765040030800000b0340700c42c10300c0312030074465485008900300728240e0a0407603481684e030302c01070714540d40c0c400424000402ca50b6040180400c0340b000d410842c4e000ba00b9003d15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 486288579 1250 486287329 486287339
    0xf040e120c07090516050316111002030f0709060f141c020c0f0f0d11150c030702010605100e04021b070b120612060f0408130f0503100b0109050d03030212040813 71
    0x40fa13140d643c05d000094801d100188400c480c4450502c02c0c907480d0300b0040c40d48621100c0e81814a1032210101481540010500461916040c50194008054640b1041c0141007100040881700c041d00d048003004031400c0c283c20212055405c5940100340c17030851844404005e41c201d0b000c4e41040c80d44076042d0007507452040300e000c800700c0c144200d41302c0a00a0895403194a00556072110043c40081ca24401c100c12501c00c988100c80650003020359085060b12854a00380090a5409603008580500341c0d44440041c6e05810210040c40e0800890300540c13140f890003032428420402c55040401449803420005000e42614002c2003681803400f03994801d9070381c0b5000e1100038401110344585540c840400110300c140d41e2645143c1003071081d00210303e403100c601303c0d81080401542080d003d02042d58020030183c03601308881884020744500500c20580c0d2900040c0501c07901d482558010040d14002da410540700b9812110340510442d000c031028146800d000080c0c0d0403207074003070505480045005c01c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 486289829 1250 486288579 486288601
    0x60e15010804110d06020c0a06091719030e0f0604110117061e180717010e0609180a050304030b0a0605090c07030e121c0801050d020f040e120c070905 66
    0x1c030a90b002210400c1e8007030b108080c404132000c19641074070b01e00d41c00c0c015a0411082030010742c0403540121408111644541810130044240048105c5011803c1101905548100788482140d126900340000c01f003d1144aa5081c94150002c44540340110403c000c1040703c440c1c1ca9180e40392080e603a8210585070001c0600340c0f100142c4009611001003880c422250903002808a08181d002c0c0804001c280a001201c01c080815107084000c03c000402c14941c0d0090641464011708007508a581c04c0d0400da404a00c0c01c04004d8610b840012900c0c41130140c94008002da24903c640c401d08880e941d595034105a4a040c4c1d003991030b04860b40c02c2c104000b0b11894994081d50003005404441890b0a880d603906032100d0213004c2c46140c100c0b45591004040c0e0400740010715014100da1070712000302c0070400e001031541c2016001244110106128013001da04d4401c000483d151003900d0001e103007040ca842d400e00c1c2c007100921003000303140c0004179488070703000c0444d50b04215420800c0500183e00c0382140e0b20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 486291079 1250 486289829 486289831
    0x5010e120a0e040f1b050405180f1f08030c03071103010606090905040215030103030e1f0f110309280e1905060114131e0302101809060e150108 63
    0x200050141c00420945140c5a4003020445000240001c0d10003c5c900421200e03410345c841d05e42c007180010404100505102c40714940003080c00030302240134a0401d05484807904d014240e007001c5c80d803440d04250324041c0e9000400c09055142d0840b51075014008505981c0c1d400a074044402c0700b1942e581a2031824140035881c20b5585030344407845124281000314000707280c020700c1664032100040c0103c1d0300c0340c0c0c41c0d0f00a60107540241c0d40c03031100d41079540c02e006442c1d8801601d40c3c0ca0542c50002000e03001d5200b2840041e030000c034a49104c002841d200c80078514092514840d502401494030035014045011040004030301c5154a4004150380c1c02c040741c103407001241c2001044036510044450038010741c0c086a402441410451121045d156035000e60342c1003841843c9219658030024481030480b40c01d00f680080e4075101e030074580f80c190b5000c11400c254840e401410f120060003480441420034020b64090001600d08102c041e5032042102d840f088103541440b500e6081a10859640d44640405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 486292329 1250 486291079 486291097
    0x7022a0a08031e070f150207061a13020a2c010206011706010306022508090f040218012d030c0f0309020d08160803040809100f170408040503010905010e12 68
    0x3400d01403a900c80d008a84c0485001c45803802c58810483c0065450855405407010780b84005807200c0702868200201d50415903c8555822007180440030f80da0f440447d00074281007503801503144c0e42c1e06c0d08296400000030354509000c6901c01d1094501118100702443c03154426400c441c01d44e40c1c0d07017594000001a0040c41c48107030300120010700c080340a40d00108403805c0402d900141c0c400c0012014040c00d00b0700c1c0030846699400194840b0070349840c01c8020003c02c2c04403011864004010b8001c204600d91130b2445051061034140391a1202404021034041401050305d0351706c001c8810401001403000c1420301001c68000e511103411a031292183c000f0007a4082c00080601510303444004464029148102044070400c9900001480b00c1010f1400340d441981040c4c1c0b500d0583d0208035803410460014020000e03400b80e8068005ea00140481c1c9402d11803400641c9900c1d5030628040500c12504210703059801e04a100082120540c0550490110070080d074040e6818141075504c0c0e0710903d101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 486293579 1250 486292329 486292357
    0xd0213140c0c0c1908010e010507031d060a15080a030210050f221b08010204090b010201051e070207030816020a06230f0d1103070e010309081207022a0a0803 69
    0x42c0c0380f418100341200b902000561200030341143e130b40300b20309820342c4c114910402150351180103011140d038140c000c064440700c03082034805d5550610110f4550741c12005029454040c2c44001c2c19400c0c860f84611040580040f20590b18074806504006c0d5981e4454902040141c2c901030002d004902c0068040740915285020426004e800c3c1c080c0440107800707154292122a504551281c2041a6411510040c80f0b5540056251484e0047d0007013119000030f481415a4101300400014007001d12081425081e122001c00f003a85522a040340342458640008000703090026107040b4007400c00d5100c44440d8400c8504200c036544407042258640301d8001c00701d0004c0406440201000d40c0c3e14040c04095480100340360401c009025000184c03240010740360000c0e4400002d100d0b0180c7c0c00708512139040001e00f01441101080c2d070716074030749108201d001c2d0301358000e1001060300d4900c02d01c0a980d02551000d200028001003132040e103808401109928440c41c40c041000500d40710100540350f45038000c2c0c01e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 486294829 1250 486293579 486293593
    0x60601080a020c010608010e0a0611030c030612010b090705030610020706020606060c1f0c090902070f02040b0420030105120a0b1f0b030f0106200a110d0213140c0c 72
    0x600d11010f90003000041e4055525a07401041003142445610b4031030360518010240e4070b00a040050495010440303c140758041003080007010010740b0103c1e6040328090f6071642190145560140c010078200c107425901c410208140045954407501840c0034182c12518400c20b4154800243da4803d11171040002581140700062080c1c0b4102c40030b00f541e0411001942c0d0000720f40c504240c4140045201e800481ea581c00d1100c001030b030300c234070300e88c024115640e011454090103444070000300e150ba0030024481c40c2c6030055103103552540d4100342c0400d034200d5040c03506000d150340c070402d10350024059140140080c4240e03200c807130b000081c00300142e60000c86100c1d00e501c6080902c1a050300441d0030741016140100006427442410700250300c200a035241901203075060203030003804d40981c16181d1681120142c0e8540b202a800b203480ca01c100e43c03124091103642c08040200c0e2103031099642c0654003800c54821080c49021940040f00150200c100b1f80783da40c1c0c7c0e0412103280d180141c0079007508540c0140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 486296079 1250 486294829 486294841
    0x705030a08010311040216081803060a0c0201050105030a0b01091a0301021303051c080a0c030608122203030f0e0109050a17010b0a150503220609050c030706050f16060207081b06060108 81
    0x44010070505200b503427421015075441d40441e01c2e0503825224002d1082e035421180b140b140d828481c0c5409080d08802402d0601c0803a1100c10000f80f0600661402c0b6654a07a012071207c3c070b051004090a1000e0001d40d202c2840c0032500503802403510041d55940142c00b22441e52410708812042da91200c0d841d08006500d40ca80b440d0f00402009a0300004d1650320a03021440ca40204408040f010024580b19500c10240b064044001c541c0e0b4983c1520811504081c0300098000904400800140c41c01c4845020301c01c0c012a1801c0b0164050758005a507103201044041c510080c50356003c11040080c0212041202440f61550462082c48940e01d80e00110200703003072045000303540151081400c2000560403104003c04903185441c11900d140c2c1e82c04606041180a01c01000000012001b8100240c0740020103011842003904000f0b05980003e025401081c551b0742e0580555007140c81152501c1662509600990101e400340d401c0e0700c0c103a80c03104004180001c1c0c16214003410ba503010700c01d131110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 486297329 1250 486296079 486296093
    0x901031101031d420a0c020c0f010f0e0a08010204090e0c0f0111010f1b0e0d021c0213020307050408071a1602040e0a050d03140402090403140705030a08010311040216 73
    0x521120501000029542000318401c81102010082d00b444d590b10141000201030088402c9142040199005006a644155640d028039042e1034800e08092440005410080320303199155076000c1c0d8400da40c040e021031701400550182081c1c510701d8208001d0440c140c032001c0e13918040e80d00d61580c000c500d120700380c1c080e52180140058052481c4000704450a04050b02c00685031143c60000ba840020764030021007560000000030311210660700e181600c0b200b0b4001c100c3c191404045c001a0806c0746201c0d20031511b0f120304402c0c0d40504d06004648a0405000081a90380984620311803481881001b08501c24500c2c549003041c1e202c40100380c904400c248020082c032241030b6003a60b20030796420a40240c400c0511004401901c03640140c0390708610342700b0140c00c54008400d803e800c22111405c00006031218103005402c26094140103800c1035410622407510b11a22100810900001c038410007016000b60456058034402c1d2400401a0140b1061004138080c4000503808400405080707804282d074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 486298579 1250 486297329 486297373
    0x10150501110f0d0f0e091504021608030a05060a060801081c26090d03060b16170d0e0d05031e0402060d0603030c02040b030105041a0907050901031101031d 68
    0x21003419688190100902142049407510110340455070049040c8001c80d030200c118840d0807000c803001c2d10031f4144100848595102d40200318026540090220b0204012000d0154010350001c411a40d82c41c0c4800600040c1900b929032030300031442c2d0400416036500503544181030390307416402000340380100c0b043c00404561b4600100140100b241c0380350b951001c003114088458407001107200700c506003142418a80070410000808140c0307004030030321410f00300104658440c3d1a00342410301c01002070509004a50031040007245c01e01e40041d0801400c03109400c0640101a12002c4c0d80400b10021002c1c0d5440c4022240716140c41c00007605241881d40500b0313501c1e046030024007450304100701c42d040310b8100d4040c7d070000e07004a11481c0d618421454180100c0a66140540003440182080c1d6a041c640c00309040c10b40040941c0000013461580c410442c0000828004048203110359481c24900380c0801076200d02400641040b080c011103603125090880e00000e110000e020000c0c1980c07442c044461 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 486299829 1250 486298579 486298607
    0x8060a0b1e040b06040e150105131406040b030f040302011109010c200901090b0901090606050f1c06060314060103140718080f060115020a03050a030902030a140c010210150501 77
    0x180c0c0348400d40703c1d40c442c8406480034000059040a090400501070f56201d032176070f0407442c1000f8040102c00f0b828500d10040c10100c600003a0507201c0c820001001442900503600b00600091010003045104d80c0ea41403039901590190300204031004154000b59507510412440d5404140d403016400c4c001408407490b25184200701034041d04400e0f88400140c83c030031081e444944256203903400c900513460300801150040c4100314042100b685400070240481c0240400c2440d51800401c00029942010020f030001c10140c41c02044426214480900100b80c0c04034520b044118a0000a2442d4064883d038040c1110301480201c0580d92408202d0391280e0b0300d00308103500840103100040c1c5410402c00d00300d42d01425801307408a0341c103050801c0e0809188804210455104c040642c011903040821100400320510340440c0441840c00440d02e440d104641c000c00130802408003404041c00401c807403264031001da0031303280d415407400040d0084e5003100401400c2c1c0100550200503035800303203d00506100f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 486301079 1250 486299829 486299831
    0x90b07051905060924160c080c0715030207050709020a0315081506030a0809040b0402072f120717070f030c051908030a0c14100608060a0b1e04 63
    0x5074480d4080003044000d21001c41d5194024400d11111290910410240403500c05581d80003400c90801201c0340e22000e0042d01041e9054040700403c0e0f481507840d603170050781210a1039a101000301c211a035036549446400300380c1c86002080e4080500c0f03030007200c0400340c01c0b8004002c1c00d03041051010082d0b019060f090189035a231800076104110720a004002080d1244c0507142e99100c0e140c804110300740c000e00880c4a1b41111044100107034007581641d4004034183c03000681030400c04c0c0130600034880e9010240980c010003444600b682d0a03241d0280e44140640c1030490584a1042400b0a0511200d00d43d600c54105c51004c3c4410011181e9141003140420111601c8039962070211b5907040c00d40e0070076210440300c82c0d002c0c03106e400c140d51412142420050310711700303551429070700b10b480303000e894448410046140175160a11120105c0f201e10280d0340c0094405c18107403108141d00402c8188601403260080c100060410469885051421301026140c80300b003064140c0c10203e41d00301e6800b01070f849 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 486302329 1250 486301079 486301093
    0x120c05030a3b090a110322170a0e0102011109010311040906030309080c0621090a081b010e010204030210110712030807030e06010605041206020408030d021e0a090b0705 74
    0x30188003555003400b0b1003644020314002d415401880710350100200411841424030720210110400002140c1e402826284c00c20300c01d03a00078503a81b9000000b45c801910190754010012080344c000c200414001d0190340782c0551000745036006a090b25041000394085002c00e201040055001c0d40051290550782101d0303500e07042e1110303101c500720b5903260025400074800020a0002d000100326400c01c0c070344100d410070306000c84920382c250490784035240f0381511040b40002c0f448480c030801c500a14039901000640c2c85030030047c0281c03101d03070030849c40440c00d41c00e02100d84200d0406100300c80030703650090420302160320100ca06583c454101079000c051441000800500e00c54203140b06040c0c14407956900805050869006083e180d040000101c1e42d0401d2004000700d0390050100e074210b4400c00301d140905421420680020301660f1300031162400001521101d03100e06500400da810410441c45948524201107601a409203c6803140880d01856051200c40540005002d080d03102c1c004681030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 486303579 1250 486302329 486302387
    0x1501060e0616050a0c17030a05070203030c01050a050610030603111005040f080102090f091003060c2d08090706080604090f0f030c0b07111b0315090703120c05030a 72
    0xc44401c03810a0790320b6040349070346004100522139400020084a03001c80c03524806c5caaa0941c49100300400c0e0418407e0001d684030454409005540d02000544c2c000c00052a11070110b80c0545400c0b120b40e0703c0389007100241480d42d4040d215a0b0141c98002c0089030505d0080018482c1d2500b42c0c25200c3d042c41170601000484800c4010407130044d00c40301c000580c440c0c900100f4061007191440d2000d125400d50820000710806c4501544200d9812100200d4500105d45040e98040071510300c0d0007040c0d04011100302030401c076501e0081081c00d65580c0d00507c2c1e4420300701c9502c0b4402c1d0b000e10f2001420b46404902c4906e069000342a9043c05034100c01284055955122a800320014044020412019002c000d20458040e400da116900f81030880c004aa41c01101e91100b00851401c0c00b5501d11030f4102d0119241004101a180300e015400d010078103202c8211aa070b600148001c50740506e0380500707940c1c1d542c40703188040c040c42d074480025810a003221000b03448600307140c801002c01d4032034805620340b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 486304829 1250 486303579 486303607
    0x504031b080a09330323041401060302030a080a020327010e01050a09051306080d050706150f12050c0616020f0d23010f0203070509010201050601021501060e06 70
    0x8040c0d8801c0e070110340e0750030a0480140501e41030b40c0c07006428400054110307241e64541410f04003404120803030480300d1018820264020018a195501c004484441c80d804d110092465680554060b1200c091405c2c011a50a07090f0b0303409000080d010b4201100900c000345190300035040d10040c0c1c3c01900d0900d0003c4002d4109005034204499030f401411072141140e507001207844503070355401c0c6000c5240c04040b01d8081d1481ca0300f8425540200304405540d140e61480f980510007070103107a4103940301170444203c01081c90300082019a038441c42c1002e0b01c08100c0c9200081c000f00c07004100681043c40c07411400c0b9502c55108042552117000d0100d007980315030340c0c520050561124a0715900e9040f4407900500c00c0502c0e0803110503004803000304051000c00c83c3d0b690380080100c1702250451040f180b40100c90f01411140c00150350050001c001d00c807002d44c104010b4070300008203034001c00c001c1d60303484012a91782004440200c0204203280050044901c14007840d100709401406503458105070000d101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 486306079 1250 486304829 486304877
    0xc0e070509033705060712020f070c05090108010c090e09030d0c050c0706110a1113151409070f0806030703021f080708100b03100e0a0b1f020a06050403 67
    0x3c10040942c11a41088002041c040d480d075205042020420803c40d80d00d0b9135841c0d0001d0725003c103020789005101d42c0840315404581a00d03041c42e003e107448605c1c5141c00c0035095141d00550b03120f10035040000c10050814801e2483e00403581c0d403640c4199103810128001268040c0001c8030300c0c0810000252003070070782d00519030039203c02d40c0d40c00c1d9541e08404000c0e04007800c3d03400200400600078003541080760000344503640540c00c49a54280b40380ea210018445505440b1310040e1a030605222448500100c04034504588076070304962074800241d4208410034008072070700e00100b803401119690040c401d61203164403442c0601210440b945a030001103c82c1710040400390394003840342c901030307040d50b2000c0c0140c0c1005480c00c0a641d14200401d4690560640340142113a00300080006035404020052280c014071181c2121007003810243d0412016140d2010103034010040300c1c0d1801f845c1d245070010f00580382c6c0107074094499000c0640c0e800000d0800a00300368104400150205500035001a0078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 486307329 1250 486306079 486306103
    0x60c030c070501080a0204053f010506040b0906100c11031e0705090c07031103190c0201020708071211030a0b1314030405010807081017030c01060e01030c0e07050903 73
    0x3070094030b2500000400d03008008001d00303203040c018401000f030f544802c80031440d28403100648000000c0c1100c010b070f0500035041e0350700030f0340d0312174811892a1840c103500c1180144d106480c140301c40c200e50402c0c0300158006a4080c0d40040039400344491503803040b15580c00151241070b8036000041d4220000e840c0416005142501c00c40c00c28043c0c0074601d0803c0a4001468196414400c1e0b00d0b041ca5041c80a00441c2c2c00030301402880e40310314002d204240115035000300d415000040c11412002c00425104490101301c0c05445040004142400c4c0040d40c4001c03105005101c01d9243e010340c0da161031540d800084180c0501c20080c0c03520005101b0325441d4407030306a0312001d1001d1916401d2129003002240540055504100001d1040c0d0b40d000b42d0300399000760710b400c1c40700c115101d004d100059000507900c60444402120a0380280d040003200802e000d0042c24000e00143d40c81d219488850002880005c1070307098800c10811008040c4003e071603000402c1e00784542880036140200303080140c45200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 486308579 1250 486307329 486307333
    0xb0408030a0e150306090a06050d031e030b09130305040f03080309150606030a0b030a02090f01062c12150c0d14060a05041505030a0c0f06050c0706030506060c030c 72
    0x641d0580030303030041d1a09403001084900c420010400c0e03451090510010f0400360165411130006205100c7c00c1d0010b03001001d0141450f62001e24504000b481a02d80706443c0505401c915540c055041c031901909221850040c0020016111080c0c0360f101401b403200100e0030b00200b44000640e40c490b146140000314041d280c2c8640d070740740c880003039802c0c05d10f0580881c2403420010140441070b240e075402e980d440702c8400c00c000380d5924403200107882e00f810b400b0003e42c02402e010811107102c0d40444017034101c96407034407203c42c0415409900c40c01c0e0b000e60380014a03030640b40704042d1210710301041c1c6000c01500710070583c5c0768296102d884250360002100c426422400c0004d1141c000b885174071a0202c0604000300707824a504000e03001032030070a144d2040902c034689442c03030745000341061001440185001411a00c0c5070352b1501d800d807440c4120303218401e80030200e00400601c4602520485000c00d40c0034025100d80341c14524140d00800001c0c0040e5001a414040084469000c10040240c2d02c01400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 486309829 1250 486308579 486308587
    0x120717031b061006050f0c0a050a02131e150b0412020f010f080609070908010e0109050f06040507060302220801020304053c190311070603020a08060d020a0b040803 72
    0x70000c5100d440354801081168003400030003040072207600c0b9100988250346400e0369a44256500b4603124040c40030341403040e0096403010401c1050000e00024028401e65440354050b02034590101161420f1a246003089485032074004180240d500c8404401c0c0915145007190751128100702130ba81190b00042900004032001c04151325050301c0c100025002480d2042c00e0110001c00248034a102802c0a8003d00048010620030350003100944090048c440c000c03c180540c480d50702d03028101c510820388040c00350a580d204c19000c003003072a0740b00e103401100400c601d40c54400f046000b5480410700000d000109040140f4043c504200b040040c91404000b40e242e040030304041c0d00780030b854411401c924900a00300601e60351075082400040802c07048800403603050201c09030070844003242030b036a10001310400c6010540c0040c81c0004111540f0b00301c948481d2200016401c83c802c3c6100c0d4000305a4590004030245054110881220b101518409d1116503600c0c0340e20864000c4c1d0001042c03500081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 486311079 1250 486309829 486309847
    0x10e030c060a02090d030c0c05092a1603050705150403031b02061918020904060212070507080405151309020306010e0303040509160c0c06170604051512071703 70
    0x10001c0d4200704080000c5291a4181001417048080f4401c01018011880c48000601540c08002001440054200d0740140781104140d28164041d88814412a138101c41c00d00003094440295040060072103010710840c2001d4900f0346094010880490b5903104440c8103880101e09980d40a009500c039890200c0c0d0b41040034907900981e80d060740361004662040d0308000c02c0d0784136001c08807800c14030710000040080300d500c0401549500c0600c040d40140740c0e18280420848181d000b01040490845c20889545400780d045402d803282c40c8026080c407a042c002403106180c06407602d00100b00140102d45020060001240020328541c441440c480e4040100007041d6003100031200d0352141100914507190822000034039150380070b42480ca417224043c0458042d03600070174180c14525000152400080e60300c0c04010708103007203201c86003129010f107004101141007a008290250b0702a94030b80b00c2c003e2840381401919154007002c81400d102ea99030001346002814240000400000301035541c881d4a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 486312329 1250 486311079 486311083
    0x2310090303232e050a120201180f09020310030212010f1508120d020f190306090509030901030b27012d060e0a09050f071421090a05010e030c 62
    0x8418041c9a03901010401040d02181011014a43e0b8100e02c01048551611902608031156801280c0c005900d800045120b041c0580c1c5070181502c00da0751411082441c040c946002c0b001442003c140900303401003840840903580255501c180420402401c00340e403900060481c802c43c20640d40907940d0f90300c901d2101245406000c0c406010198488c541c1031804480780e41e11300050415001c043c41c0810142c022801903011034a0b1b0f4a014000e40d03440f00840c0109441e25807030300c480b0700082441c16030006686903040c01004e00c2540110040c5041428030f00054000e0001384102030b61003c000c081014841e602c1c003000f59008440c0b100705400d9503060411380940700da1b84d0813442e54540040d60142d41c2c0b100c01d00403038505031071031031030440402418480841d11120f0150840d41401d0f080c00e041090344400c205501e4800c010954031140a4a0b00c4101050144030311200c403512600c85240c080007100104a00c5034218181a0403540b00b0115078030b41c41c1c01c40d600c02031002d4a13030300001900e011860003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 486313579 1250 486312329 486312371
    0xf03180b0f0109020913021b030a090806060a031a15190e06120703030c050a0611190f020304060f0908190524011203050d1505100c2310090303 63
    0x1d01c4200310701e06170b880701c00581c0d400020307181e0818482c0c0004101c20a4060316007030440040100c01100d4a0b00741c103080140c000f05050040c44554465171000030120b18019a85404513608903031900900c2c010702c000011260001800c0380720848404000d01000d490b070f40604030500180d40e800c2c1e50810300f0942c0800c0b20030405442c06e8801c04002031000d076a40c2000c5040d404580d41410105824030fa5840c0040c10030314084c070003500c5c5502c0c1000070202280460006c1442c441c0c0313400490070001a00f03d09889154258549200607401032005221017400b4841c0032410180c642404502d055031081d459103048d00c0400e27541541a440c003902020000208a400440a0301810744c02411100c00001840d05005100f910501c690320202d10703080c540100c00b11201c0214000d0188802c3d04400c0c603c44040119104d0207004582e4030360004042442080501201640071600da04006041d5100580c5040e03801441c2205014001c0c00d00b1007541c0301d1145080862284c0c6004c548000350185003030718065 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 486314829 1250 486313579 486313589
    0x90b062106160207050a18051003060f0911090f0109050702010216050309090f090307030f030902120d0e0301020705071404060807060903110a030f0f06020d060b0306040c090807060f03180b0f01 85
    0x4264244404080042447c0002518003c0015503a0f00d048802e4183d258030790001c0d0404e49000e00700000740d0b0180d001085124010451581c1c0251a041030010000c8101d44040c000c600d03010052006a125411142d040190741c400541071285501c0315125a054900c0c04440799880018a504503080c41e09487e5070054482852846514041d08299164850f000c802010040d56026415109002e41c0c805a411500030780404100101055020781c0c5103000e450070b002180184480100d149014000c0780c41030b980c07240107003001526100d261080703091603c8040380e106845820201d900354007008032034000d00781a610540c030790749503003440c1315882005102d0a008040e0550b003400401c000d000e50758401c0d9400341d80404201c066080520090103032131001207400d800c6c00c80000314946001c01a5000f014100d43c2000b0301d00850000355032401451150b00900c1d00400810030455000300080c000014480c100441c040512607000b04400c0c801c16802ca904e020724070180800032405082d00f0303014003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 486316079 1250 486314829 486314839
    0x270f140603070f03020708070b0f070201060e151207122102010c0e0f0f0405011412060f01051203040f0e040311120f070f140a0b0a090b06210616020705 67
    0x4100103070010400352194182d401413503000031349441084000030031541c20300c0d0000002046c0741000351890303882c1c0d003058440c81e00560074650301094511100c4113260150a1a402149002c403000090040d446404981c00300103000d465070000e00c07040039800170086984109981403804400c00220354900045e0b4544404680c540400f0911464002d00340500ca10310454048244010420028104050200ca00c0d40c001d800c14000180800406d03c510800400850755840c58074411143e42d60364000440c5c01040f0283d9120041149003040c3d00c00512a0283c04142c0745013075100e02d000c0c4034a50b03141d40111000c4405000300402c0c0740e41300c4240514010410041d14422401c0d0f20300c000240070350309039420503410000d0604104402c4041c0c03001f103035620203400c04011107415078042d01d995840c0e8059030b8441c20080014103032013107885034008107a0300030a0100c1c1611420140041812034040d0021403040702d0700d000403095001c00201d031003085a244503204a8280340f1000b4200500340e80018061 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 486317329 1250 486316079 486316081
    0x20312130b15090c0c160303050d0b06070b0703090203030c0304060206070e06120105010f090e040506010e160801030803060d0618020310020f0910031806060807050f0f01270f140603 80
    0x60740d03c644003d40c0085070300d09441d445aa0542d25517007001010404040d41e0a029a80041003517004030103041500c000c610104280e03800b01c01485241e03c650200244150705400c00503d540e80641d00c450305030341c0007800300da090040c1c001c40e00e0700d95031050700070001503848074042004003035011040082c000c0c4207035105800c20204c901ca8a00000301030042078140701002e80c02c030b00300f6441502c1a2008005040c000005410b241c141141c0701d020a000784606001071000244600c0c036040f603003950443c5540e803182c072160700c1e6403940302d10340c0c0014054991040300403c154010800031b000c0c802c40c61182c500590800c0310030344100351a2000700300800c5405401442140c1c4105419400d60345c489109658040409241c08009c80040809107800114400c0c0c4040c0c4005105848d0700610560341403004a4452580799401c000d01030404401c1190711501204103050254460b029601403404099000c0e41c010280e01c680246c0030f0203580100394910700341e2500308104900c40e5118549401c1c2501c3c035500d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 486318579 1250 486317329 486317371
    0x40509071407022e03021b010c0210110906030c0306121c0507060e030415022103070c2d02011e02151f0f170c01091401020312130b 58
    0x85010301d0348068419003201c14020030243c070158913114a05100300d6820007182100d140a0000e400211000c80300c450080450040c9440502c22440400100d4004043ca1462141c241028080404c0d50107040072003402190040e8079420080c60007004d802110075201d250030030900c0491b02c4800502038403588409a460b82c200c4c40814940411819480d04c076548900c6410100d0241c5078201807800d29210001e00002c003101c3c6034100846000c090390175100d0780d8500d1702c41d0290f10381740c0e040441d40624003040482c0742103006010400d04503100b6203942a03100058904c03c40212100d404401109424a52400444da4454181100c40d01d0f240f01c400080c0c1015030307000350384900010b440544114244c004c5419020311500500d42d840006c18040300f919198070030326400624511a420003103071883c1030301400480100d0440d240e0315040e900c59104030301d130242c030b81c0710805410300c05415400200826484006d004400d50301c04c0440d51401402423603549070021040c0c0d4000c00c920454030016040c966 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 486319829 1250 486318579 486318617
    0x1e040317041805010308160302031303210c08090603070e03070e0601140f03040b0403021005040f0210020f06060f060702090a090507060504150c031419080c04061211160804050907 79
    0x200081c0391f02c0703020104111500e02a440d610903801c12144039020106c5c00000c1100501070900301078040e01004400039a03e04003540c0c0b43c1c204003801007002c0000c0c4264200c80c00d200015503404030b6285044072000b214000400d042c540150003180e200c5200104100c0c1ea03507002041b4603400c00074000645d2902c4080381c1182c540f400050301c01441401d00001140174544200030601c41010306003400c028030f08062600e10108091400c080380070721210f00c0d04102c401d0021464443c0151584044c0140e03603076030010032a0480c2c4556041d9800b440610001d00582c4403210030750310030034540d1000140c2041d14204039292803160752103001002810041802420710002601d0000b00090500b060700c03094a20b01960f102c050640145021400440c07010040208000c0c0058200c1064640a16549601c814100180b107070340035800103e0900e05880c80317107040301e52000e0030545d0f04c0c0c8040d03400c103204034680d0707003c2e501c079040c0070342d20450049014081c40c42c0540c005604002241010800b80400081c124 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 486321079 1250 486319829 486319837
    0x70b011401210c05120c0301060e0603070804020907231e070213020c010225031106150607260d0b040b13090f0821011202061e040317041805010308 65
    0x1240903440744102d0f101240603100340c852100c00b00000c81110700d0b20f40c1091a50f40c000344294000907014a0300d074100f0703080480c21603004a14640ea452003e13502c1c1d400380304008001070151010409500003220020004d400d28210144240411564400001c00030b50000100e000480900c00382c20041040181c0e210702075110756172114a40941c40302c802c842c2c1a40207000b0a1300c0901105295881e0990102c0946c540c1d0300c58030b11984442002103c0c903000c0d0381e03840c0c03400c170380ca101e2048211510200c20b00e0000050710b03000788110140380d040944e80350b2004181c1e095210700441450042540c400b0701c800b5000c0d590307180340107880030041d602901c400282c0c0fa00e81c681412000b903030384101c83c009000c1e40401e200d002a03044038201e50b441000000149001101902e0410000035103030000c02c8101711710342c00c003050741c1e0011710880c10264030340d5482c00c0180c1c002c07089000490003040008002048840301c0008060303140070880e1180c1c03a240211642134008003195440b0b525110040c000540800155 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 486322329 1250 486321079 486321137
    0x3040806070f05070b011d0a0902060901030e01020d0606110d0806010206070e011b2303031b090a0f06120c11100b01030222030512030403050304030e011202070b011401 74
    0x700c2e0802c4000e00041d42c2e03522070002d02a02d04e110817030001c180900c10301c3c0d8080440352107502a0b02280e0315161140c0440b40856402540140104681142c640c42900b007091030b20300e55400107103040c01c2d2820303080c00c4814551003040884e6100341496082074090056010301101400c03c504107140c9840000c2d114a00100201c082c403050700d1041803940d104896400c0103241581c881c00c2c0a01880c00c1c40400b100810310707800715210341810350101c6544040180c2e40141600c41c0166103580841c00f03651a5900600e0b40143c0044291000040040c43c200c005002000344d600c9114220703030049e03240d03130940301c01d00d900303005212031111418419040064031242500c454000004c5042d4103500482c040e02c1002d401e01032090050401300172081d1a400a03008481c424001c8800b095130518107c1510300086a000d00460020f000103030101c0e025103601d80040361305151210141030403194a0003283c210b03800984800300c0c000018003d01030091151400d251742428454240801c61003100c010708081703558 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 486323579 1250 486322329 486322337
    0xb09121206091308121915030f050307080409020306040507090302030309090a0b10031401090908030c0306030a020907020c011736031605070e1e07110d020c0901080304080607 77
    0xd814921042c604000b007035800005903650b4240c0c00a0100d55800030386d01541105d0720300401018080b802d20401c410000e1102d880a0401d146440d1400d030403074881030981e4240030411680300021112001800a0400b1130001a10303800d08200340412500000c0601041c86894042840940c1c0c000080d104014001c03a0078520383c7e540d10040d50054200b6000c80f5400414950344801d0702c0e901038000c1154480d2400180d0781503070740c0e6065207040d50311b03480001e40038403020404078540503522802590711047c007030200d508a01103079004c10720b8903000329080c0700160001c5500c49502e681c021100031401850404003502c50a20640343c410a18803007100780032100c03060200201d010300c00d59001002003e080c007540c0e283c4581885141c14586580001c5074180600c0700041500f018084400e4019004446224001c003100400c003010741c0c00142c88031003444203a08144444890800480140308555800340a40c40180000d001c00120103800c41c0b40b90750014003040c0046e010004803280e00001e90b00d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 486324829 1250 486323579 486323581
    0x10140301020f0904021c1503060f0b010e10170c180a1406070204181a0f130f051009080c0d08040506160909110315040b150d0b0d0b0912120609 63
    0x1440c0307103d49005118406d5840c03c0c50701a4900d000158003550840c0e0240d10306000240c0700e0110081200ca01724041d07408568408148a0a03040090b84007010700c506050a105400e8262449152500d08070f5180108810000d03145141101d65200c88075900001e40d80780360140d00b40051101c032075654000c000e00810001c102d2409560b180e4004c48204107001c034800c1d501a01c182000420810054984140d4400b20800b260718010109055407084110780381e10728140c092560b03401ca8040220a0654840c45010b1805410469520900a0841c880c2190f41e0761942082051402d00341810780020a210024041202045003c181c2c507510646250718083c44851202042d40c440354580c00400070a40380940c0601524101c6c8011400398542c1014120b084035204d0801003a10402c02c1039a402401d8241c103010000114000380c200c41d4a44600400c20f69040000f181300e94174910000c0c0d9019a09905102c0110414000103400c00440c280c601e25103801381e0080b10031001e000c0e1a03680220f000700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 486326079 1250 486324829 486324847
    0x18060112060e090604031b03080402040f060b0c011409071a130312030e06100302030a030f03061d0a05070503011a070f060204120c060809120702040603020910140301020f090402 78
    0x680060040c20304450340c0070310b50401c1c514580e035860044800703d0105500d400d9405a010b594241e0405240e41580d40440c0740d0b440342e0a10000e0008808400d10b03590316440045450f10101024012001c4203000000c0c07100982d4200d00084070002c1c00074200c1d5000b40d08140070031440e220b01c00d24950702010180c1c0e640c1043c00c4548504040079440a404165600c0c91545d038103505410000e0444801c808450031a03d07000c0d1503c01c0b01e819448000d5055008400b0400000d00034220580d00c01140d081c00642544d0f00c000301300d411111807078400383c011034600030807404145611070560050300340c3c6010760031981400401050058512030f149901c01002c2901d00800030548d4035007030403550007581991529030f00d19403041c0d40c0300d0038030741200c0010003007002007030080c410000e031446155606c005011140303020002e41441c2d481010107a8205031503800200140e102d52160310b009401c42600411410324200812100c020840d0310107110341d0040001c04400c0a08000307986801200f190700503558034a030313 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 486327329 1250 486326079 486326081
    0xa0b03070b0c031e041505120a0c030912020a050624150904090b01080606100801091e0203090309030d020f0d0e011803060f110301050a0317040305120901090518060112 74
    0x11800c1c04d4000414403070382c096001e6404081d00c200c1d1282e00948030000007400003070300c0c0f90007040318051a682d12000010002c454540000c5400c0c415414000340b03542e0300c0e4480c2d480071003803101c050000d03a000c00600300c20000100450303075001d80c80d01c00040b81150071891820101000e070300c0e102d2040300401c42404408600b141120303d401001003040002d040c25140c0303004049824070405d100e6014000004815052000c0b10b02c901104a54400c441a030170180303030400074021a41600300180799041d5844100340c3ca48025401550700d41c5c001c5d51600d136603038205498403880302403841c00c54019107606400d440d400100140c003803145090404100c04d040004854102e031215120601c0161614004180585640103202d95000304500340300310466641107203070320b100030702c65942c22080d114020008070340d5030346002c20340101c0300b24510f01e001da41c2d40340c0038039045d4694506e810070440003512040355078001d028540202405c1d142e100c1d80e1030341c0810009442c2401000703a4180b0201a030700c50940101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 486328579 1250 486327329 486327337
    0x403080a18080a0c0806060a17010902030a0b010503010e0a03090b030a020c0307030f09120510020a0c0210031e0614010311040b0a0201020715090b15190b0901080a0b03070b0c03 78
    0x41c1003140358109a8a011250f500da4140d103080d510313820707003403c04905400e01083d0305100d40009000b81112a21b0101b14900001766500208142d540e030304110001070398140541c0722074601885818640394144800c0500b1902c01c190b42d90040c0d4071810201000a82105040c0200c0d0303042c044803a125a84c0d554220085d00c5101051481400001620810107820008070000342144d40c1c1d800900d0741d04c80004c03900d01c00300d010010306540d0240c44d04000711513142c4c00a01c00748041c0d1610f188006500e42c08284e08920365507071800402e440b070031040d0620032175445420503180022028002075142c160400300c815401e0b100300f0b04154070350f00c002e00701ea24424101d0b070003000e031004001d40c3c0d0003049000034000c0d00a080d040b0f0396110640a00c1c0e51040d25802484a1282c0140030f408080c4c0f0b50000030250050182d6566030001c40e50341c154400304001010640c01056031400c3e103a40c68802d8000107040300700007800203c189181601d40045501c0000d091350036a40e8504450303a6032100221040d00e1406 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 486329829 1250 486328579 486328607
    0x10020a1b050616120f02030906070804120f0614160320180906041401060c030c0501060e090613033216030f3915020a0f0e060403080a 59
    0x50003d01010211855907144070710500500300d030162440720389002c440060745031420400590041c0482c0c42c252811a00400c016882441c60038a065078502007948445c01843d4103903640d2911010b50424004a400384520300c1160074200030592510010002a0100012512041560b100d208806022103403110b00c090f0411052141c0c1c4803261801048400841c81511310701844600000c901541403500540b00c45250b00c2003040c4882e801c06108580031070b142d900640810039400c4002020030403e105244c01742c55102100b04503407508100311850242c1c007601c0e00e1840d106088485002c42d0388440c28200741c40b000c0002c0140100100001c880c0c1c40c1e03100103900349149001070320303407006c2e40c01a0b4940c050610a0325131400262150304242d490a071130005980c2a14040b81e00c0c1c801860300042c011007600e41c80400701080d29040e49910a40400c040000d40744c4e90780c00183c01d06100c4d017009841003a44e0040c5822903003811408040b0b402801903200080030400c000ca452010b09009100c0401170307503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 486330935 1106 486329829 486329839
    0x180d0b040605091911090c0702030c090618010f030b070215070e0111030a020109060501051203370504050a171f0f0f05060301060510020a1b05 63
    0x80001044030b8441d0098509480c403200b14a00c0443c211402900048105e21210050150311080940405401281032004100607600001c8558038103038291035200c0781b6110507001c40c82a440100e0441617038001c038400032a1200d010301f4944d088030301850740301c50b854441d01003d0340c0b1141c1540d1441c800314088000682c2c603500440c14008112810302d03295242521184030b150440c1c01500c62000180d4644542c01d0511145000302400750034102c0380d154852100ea194544d070b0b0304c10b00074500342030103048500c220b0640189246c00c03801c00c5070b00031801412804402c014400d910ae4000c561040c0f0726030340301251481210140780b4020040000034640300218100401e40d21988071500d0380815154040c40700d40c00540e00880121403c4500046040d05000c8100f5003034401c00e401c04c038098500c0c03a02c1510a43d41c0080d1014409800443c0d620b1034407500c510381c44031310b501508225048 = true := by decide +kernel

theorem cover : BRFrame.Cov 486151079 486330935 := by
  have h0 := BRFrame.cov_init 486151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 486151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 486151079 ≤ n) (h2 : n < 486330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
