-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4052
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:26:02.843411+00:00
-- url     : https://prove2.me/submissions/19df323c-07b1-46f2-b50c-9fe871113909

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 728597122 ≤ n < 728776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 728598372 1250 728597122 728597141
    0x31b032306180a060f111309050a110703080705040b070b100e1005040e070e0103030203030a1b05090415090c021f0203071e0323041208090709091e030201 68
    0x1140c0c100d486484569003040d54600e11108240c3c010192400025030607007000341c000d148000c00082c1515060a0703045c15501c900003090a03052103003c01c0c00f03211898030600d508050b0310b080c10001c0c0908030004c013103144140c1c40041c09204007800040c0038140b20301c2c11600584032050700d464440c2c440b0b1030080d035804025140e4018800d580030001c100640f80b0004103218080d886081340b50107181c0018000200300e609a2a0018041c0b076202140e00c031100d588141c003d510aa00441d56450b28240709011900d0151000200c02d46032009040311507400403d44400100c111800542c00e14074a2440b00c61f40c4032079105085e140d0070100c42c005d0b40d94000c41c1d040c2c801d404e500b03000451044206240c1c01288811141e440c003113440c529210140350700c0e1940f40900620305040c0081e11500701700700343c0c0e100700020040c0710905a48804000800a030000095450b07003150502d00241d040000c3da540e01c0f0f000901030000d54a81e0340445200b809071a949900f40300020815410f854207803414001d000c1d0200d8103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 728599622 1250 728598372 728598443
    0xa180807150f0e1005060120030c1b031e0604140c0a1e0608060604030b07020f0703050d0905030604050c1302070c0e0f012c0403200601060908070b04031b03 69
    0x26104c2034030541405481e1060005035100015290150500c91050003010f180c00014030041c02045281c90040141c00661407040504031400d00c049820540f030302c86046102415800041c0b041040e030200000e51070342244c0d0010f4240d03694059160518640301c4440c20490307100960b80000150800301070303840350880b0b18201c0280032071502c411064031409070035100d103030304030030100001c00100e203039a448290090b0083c070503181142200e046172490310303185800584007a00f000742e0804a081e0021603442c01804160301411083c51302d62510390f1940203003603506000d00601200004825200e604407103440340d01004035034420307444825940351140115541d80940c0240000460401e07410f44c0000a20340d20250105685203c3d54060022210058011000d0100c1031402160190303607078101c0c51101c1301c620010702c15985000310081445c02c0d04d070300034400b5800020092000705481c000304c500380e075002410041000410194941440c1f1203501c054040081191000c2c100d10081706151600401403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 728600872 1250 728599622 728599633
    0x70b04150e100f0501060201020c120f07020603040b06031b030d110c060a200111030c0904060f090912030507020d05091513090b030c30100b01080a180807150f0e 71
    0x101c4047c4e00705e00c2000303c0d0265580c015411580d0661601006201481d0000303c510b08000241d0f0100b211504142c40403100340300180d041042e2801c0400080703410705a9040c0340e40d408110398000c40e40f030703243d400403000030411840c00c2c03044000010040f00c0c00c441800703000150303160000000204000d40c002602d00592106210405104205008141c1c85d2441c40d80c055145403142c1c8204149a406041910b410544071500003903c0c0c00c440f802d0100401c049030000c250b09819240414680144551080a051501301801030242e40000c502a01040300c3c10b00301d607106034103800a0342c200d4807a100c0b01c09001c80016103420f5500d41845000490f40600c600344002040481010784a0f18044000c039004001c407070140300c450030141c90302003000c60a81c82d08030400c000c100d01d403410140011515100603450f00082c0882d540e0004040381d00c50000d02d030420000c0c0071006190080303802854050000c0d000450743c1014000c8171a203203407a80e42842d400708404290358a160010701904200340360503000c1c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 728602122 1250 728600872 728600879
    0x3150b01080f01060503070815040908120601080903031909141606020102191b1401051504060b040b13090c020a0204050a0c020a081804021b12070b04150e100f0501 72
    0x401e21024169001502c5c0c0d0f80c00e45c2e80e85003040707a00060042000240d07404100703082c0c25944951060b108882d0140035211340e030701c6e4010034440c10030101401460402084804102401c400130040c1c9410483e201d8140f94207a0b004856072000e41418540907169141c1414008000d51000540a143d1807601c035600e0f032010303580d160983c02c030f0284007009071006c2c407001c0c002204284a00d11102c2d00c0c00c40403444162042060301d5001d6465016181d20016a5403a003d03c080e407862110880210701040b070302840050304010074101380d17000740c0c0724950460602103202c65185448c0805180508407040c4208400031200200030341e00c040c4104140d0080e0b10304004201e02086d14000c10f083d54080b50024110350302240d940c050316621904241200209072980500f00d0b50b40c0b800102000121440a240c5c00103105400c181031081c400803c00300c08408101500c00030300030b041440da000b0b420103030b080c0200c040e108449025203d80c003502d1020307001d50a00185501c0541c2c1c0000011540c90404000036a00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 728603372 1250 728602122 728602141
    0x1020d050708121305030d060504150f1e05030a0f0b060f0d170c0304090e0714150304020616050d181406030c0c191a06130b01020703150b0108 63
    0x160080501494010000100951540403045070032103135805407001981501e0700c400703046802104025032090b40b0340b2410491868a4003c102142a0600c5002c401d0380c42c00d03205010350b8400788203205040f0041c10b43e000108100109100003401c015080ea018038402d407920180ca10b00d280b01c101e84400e00030004c12140e0a25003407407102d40d6002307800810003410548a41d80510004805c0f0700b40c03440104082d0b03080c207005001801c000c02e82003001003103041f5008c2d000c0c0c1c00c100058003c0e00c5100a045400d061030750351003070b0125106070054011a0340f41c449002084451081c41445080100c0400101c01003190000b01043d24110942d02c280e030b1a90101c146e1703040b60f0468400d924916070b03c0c60840900780341c0f00004540002c030000c00545000f4288029034104107940c106110964074140c01181800101041c0c0c1040084080f00e0a40b685082c40c00070315090050b0283c080410341e1070210b10b60ba03034002c0002001454100344040300030310007a0451005040410751490005610740082500e411 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 728604622 1250 728603372 728603377
    0x30809060c030f2a0c160e10121106040b030a14010f15090305070e0906160203030a0e2122050f01050c0a0b0708010f0506130e09010902130b01020d05 66
    0x414880700961542c84500d80032008030000213000d000050704c03151909101c20000024460356019001070900038454080c0d00c0001c80096010040340002c0100300030051088021076005d807203176210124546800da0a1549c01c0040c40c100003030701320000150100d24100c00e0800f540c030030303030b5505410b100b0003d0049031003008880a00c5424100030000c00180451541c01c1c107120544580b501c0c03c1441c0356940d440d05844c1c940d65a2108100c011848140f08914000344030580e0b000d0060300529800d03681c0c031700c802541d80c07000403c001d0703410356606480313448284180325241c000c1548804841c0b00c2107d0302d40351b2903203900901a030341d0542155600c00301c45081c019100400c461700100b1010700e0030010801564513a0002818103824014079900e03400095008225501402081c3d603807003819810002e00131f0505001d42c000912a80c0140000344011048507074800560720700d03154250454885010450140002e454002d40c056151551018401a540c5c000300440f5000d0742150090070140f401500e092 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 728605872 1250 728604622 728604631
    0x602070b0f16090303032f0702010e011b123c11060415060b0c0a050d09350a03110d0e010804120c1205030906060603070203070b0c07020409030809060c03 68
    0x5803494000c02c0806d019911180c1d440c04524200290700c84103440042c6406400e5020900c5254082251801d65900002502028201382041d02142c0900702044090744a1080001d040c0c40c0040c440700030003485259803d02da418244040f194048020444150f050056505001d034003045d40c600c01070080c071400c1d012041015003005043c0d03e842d1921a198808003052504032069201e040c00503040403210006c00010300000081d01468025207080380c140802042ca0404018458405201c20380d584608841190150044100c0075480205140010404c4108800141c000e18107580141904407800d0700c8141903041c07d54a81040c80c010075103107070710310403183c50014148000040c0058003031946511032940314141081980090791f40c2104108558440d000001c00200500ca0b110004100c1c0e142c01c4801115414214900240001d540f4000e0003c0a844640c000e408988900a000101e81351140c000d4014812071106003005402c040d42030700c0e01d07401c921600340007405803007800b070590b03015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 728607122 1250 728605872 728605877
    0x230f070e0418080a1701050a0e0a020306030c0a0609050405090601080a1b0519242708060a05010e070906121a090a0615050315090705070602070b0f16 66
    0xa00400e41804001c00d501012801c040c1e82c194480c10101d00400d02604400c007444e40e96060203049108809400345040e40100d001343d5100d24244001d10008000303c0e4800f00d0349000584a54803840041d18100d441c51032960040e074a04004220150b00c030403c182624400e0364144284d0f00c07000460340c2d8078030f4240308500700e5400c208085400a100401440b2000c44582565280a40c4990000d400b0b0450894482a800c03007140b000c0080c6d0500c0f80c1c43c80045010801c0d1400c0b81060448042c04415518038003140c2110945200700d55624001c9032032018100403170480300c05103030a0580d5401840c00303003d03000d1148010070010f107005105920b240b058034603e40c0c4040d8465080e03d00b402c05003456500a4044280c0144260196120030080a2003280010408121249805840c04003c0384a8101c0020040100200b101c000c18040d450381c024401a40e04071140e03901c0c91021030341d9004540c1c009001500002e004024801c01c2501c0500918103a140c03e40780f0341361100c54081c1060a14060b101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 728608372 1250 728607122 728607137
    0xd0e090402012615011d0d260d020703091a1917070f0e0301090c0b0a0912210c120e040e031c050a05060904110112230f07 54
    0x65200d804070802c59a4546414030075003483d002d0050103101c00300c50030b1020a89070300c101c4555682c41b00030030510391281132641840381e86440115a4071541c41c94094141042602c030b1f04103d45030b10b140d0341e10b86075022100c6030310791110030700e01c02c003a40c001d04042c0c0004024890100e41c0c0071045c4154441d20642104941c6041c069003010b25071900d036080b2410601c048640708420045941140340e11410090b507400d1403500780c1c44800b502044511078514000da143c1400c0b000082d9421182c40c0c1528911446252203a8003801c1c222400d01694110f5440900368110500401646c56000d80990465039103002480c416040d040791a108004805040da90106078040280c80c007540310702c602000094808607410720b030003075080d01d594840c004600209544514101c4040310a1050030380085541c801402079003400710008001031005071000d4500403024110710301580c040c0641c0100e001c02010309102c2540c0d5444007a21030700382174000f50a40354100002400032400e990f003d501c140d0aa844182 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 728609622 1250 728608372 728608381
    0xb040218010f0611010f1a0118051003090f050102070c030b01080102031e0405070317041d01120201080a0f1409010e0a020a060f260613060f06051c05040b06030d0e09 73
    0x15403085405584c200195a10310070610701c04200d0240351400b80014455240102d582c000041c03900d0a204040b504100302d0410502080e5603a0300f5144007030700c0d039103800720b01055581480a01d200280e41c0c02001903100150000801a0500380407048a029140c03a806680c0ea40705883c0c280d100840340c18100542c803100103040720458000e491741041c02002100c2d007241e06c82e511922140303034003007020a5920000c503041042802c91041c0d405049001c1c3e00c05000c2c3d501d040d14040e1a0084544000d050040c4200010012000c0354031a2440103880c800a12440c0012607002d40400e0701514407040c59420179804000c20440010030741d2940d64090404070760305140290440b40400346100c41d00130030030644070309442e5048078500da0382c240004d003140d80c1d1075040040411100280c1d407010045400e08000e820040d28611014150890740d090400310f80d10160000340b001d4266400c41c03046c401501d080305200501282c1030410344503501c194100d440406240b107043d15520700d200441c0758450400310000e03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 728610872 1250 728609622 728609627
    0x3040512010207050706350414030d150512011404080d02040b180306070212040b1818071b08070618050a060507080105060c1c0e06070b040218010f06 66
    0x100e12010869000508140c07240c1e56050404e500340e0301080c00140c2c3c0c401e030502003440d501c2102c0442e416003c1141c09040c13200c400c00402c42ca006002a1000c40d1000710000d00d15420f20458820740c400e0300003001941706142001c100c54190740541c41c0140d1804080c55800b010511a120700340a28048039241a51942d40d164020b601c00c550540358260284030010b030300c1c800c13040900302c510700603030b408103c0031050003d15140c007200405490456101c0c201480610a04004036020b032110444195503a044a10a03915030780c2e00c0d20840b40e0084100252500c40c4040480c071207015194a44e01d940044000003403085144140d03200c05803100c2001c00190380000c409500040d4160b10300994454403200a072221428210103140a4861640758020413001d590300a42c2c10380905000c441e85418507509100b10f940ea4030303601da0303840d9003010490b05024140e805081d0382540c21000500c2c8035950484d40c540f090848100703803170880c09081c070b105480110541c1c2191013130580d01c155628100d05440d01c0000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 728612122 1250 728610872 728610889
    0x31208070e03100906110f041505090105031f151215210c0b1b07050103050717040f02030706270803090913050106030c170109021027260a05030405 65
    0xb05d61a95070340d614a010700400202914811880030001d5441d5480c2a120b150306580141c1007008015013006201450b80e0481c0560760490320b024548403011100780c54400b801540754004404414990007140700c070950146483e803034480d402c031092001c21004006808125800d0240d81c1c1e40812410101188c0821000c0541c800d502961080c0344041d0380740f00b0031855070300180f6000881059041c2401d21120704004107401000f0a00c1d00300f01502e0181c000801c0c400c42003000d00328014414020400b8014030300703078003141070350001c05031000e03a503481102504c1d0703a800c5c1d040c0780d018444a040d248c1460445c25010b1040320007510155203820b00031003c02250380d05c010240702c001c0d91820030540201d0424030032400510300c5490552102400c0041040700c4105043c0710546076818242454016150b4a005d03001c1d400950401a40c0b4420340c0f4002d500c50300100214039002d040b01d000000c1c074894645090440041006c0c0207030103844241034015244e01c5006005429940200070400903424502c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 728613372 1250 728612122 728612141
    0x6110a020c0f0102330408120f06130f020705160504060b03060a03110102071a0901083306070506040b04030e09040b07050702270103030e060703080103080f040e01031208070e0310 79
    0x2046a560b505140c5c80b046003510664040d0342c1c2517004034a03800818525290740e43c001c1454501c3d9145441c0c020b0008502c80740704040c41c8055500e80c0090f200846da10307010b5036221548641a02c00460768010601c40d854041d00c6603130300c11800e0000c001428030700c001c1100c0c000c02001c2c210a00076400c2d500d400300d2081104c41700d981144107035040081c168038407121000302c0900003200386559203c1c0800040000c44041c00c0ca40000808074036070700b00c01c3e200d4a00c0a1100704080c800c0c00f28400e080000482e240980100075205020380e10401c410050b10183c414400e520035294642c035120315800b400000300044a001301043c6c8450040f039520760107034000d0318000c2c0c0700030700404d0001e075070004039028074021400b441d400408038001801007540000e044010a1000c0d280316090585949000f081c0304810311019201440001d288015040d210040710040c14007030f80351a01c03559607803400c02800c9d1242c4008034009a12070001c103002510580600f11455001001040100c6403020f100c1c001b40718440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 728614622 1250 728613372 728613433
    0x11403040320011a040203161d0a080703050d0e101d04022a011b030f060302040606050a0206060a15050a03141314030f071b0306110a020c0f0102 64
    0x2000400011911026102c0010b4040b001060300b000c1c51035100e24803080740c034070741d4407860040c4100004d060703071040c02400512561406550704d0000560024981d54900304142d0018405140400c040d440011940c003241d00c1034046907841c41819104a07100703141c2610b8290710a45000d0201c0040b44940d61480007990242c50300310b580d4040c80002800c0380e000c00b00041070038040c0c00c500e84048030203010780c943c6141645c0c000c1c443c0c481281780c004070080429030703204207043e955908210b814003e9485240a0b5071b001c0d104014003501c0303841c05059034206416100052141d000012045d00389290050f0458641010f0340840f00517402081d5a04d400c4a081e41080680d01c043c969204480d4010391801211075640c03c52004100382400b034245900020b1607600f60380108440c81000780102c046504654000c58400c0e65a545a46c01141c0621702c0e40c00601514109260440c1100341c000082c070303e1000c2602240e0f00c0b05a1300e000c2c0070030600c0c14000701d800341e000714030240c840c0c5e203561416800301c90780e19 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 728615872 1250 728614622 728614637
    0x812040e0702030d0c030b10021f021605030a050301080706050403050705060c0a0506010306060f06180e04030c0507030516120215030a0204030b040f05010e061006031104092d09020114030403 84
    0x1c511803405c4444038102600000e45842c64000b660030f21100f800c2a4100300d02c041c00300105000c80b9a03024030090710b5084400c0d2785c0050440251000c810342e2081f072680c080c055070b5403608070140003003498200f8083c10240380100b02c00000c40d60700840841b011a0390003000f0b4202540b40404010a42d001a5860741081c050008a5000a00180301a034065403158000040301c5042c42178040d007000c0300d0f420000500c10740a869800c11500c03000558216803525040d45800d41e140e242c1240c0601c0c04c850014134501c03036600f01004015011490810f00e0061074544a4465035510f001840300001d5003010f50000f81d641c0d044015107841400031541320008100152400313640c1c4e500d1310f4640c202110150381c080110b030790500401c4000c7c001c0c0400e414541000300018184101016120291481a08249585c810440f61150f040340c003590014114035004001344180c1c000c6401c806c0d051482c1400e40882c40528080d0740c0b000d03d200e41c42c0400d8040e9603003201c503000590a400c06a0002e001036040c00002c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 728617122 1250 728615872 728615887
    0x2100903062405030129360606091c021908010e190c060c03180806061201290a080f0a031706010c0f11040f0b01090812040e070203 58
    0x5400b0b22240000a003494030074001030401c000c162a01c164000c0351180c2d04004064580020074260b000307080541d41d07500c8501800f05800500c95152070b02c05110038549648243c8040e206960310500c03068500743c0403541e203507501000c02109100345280c07264007041c0c0c1d01e10010b6a04089042e0700c40144060300116070504590740b20039040c40181d10242c6aa03464419450304020207124000750010074015000112100f950348001281e030500482c001c00240114285c14144100702d4a00d003031105a5001c11102c0e00c13124145d8403421304540c40b0340542d03080d0100d003c645605104142100d0804294510702c551024000649200c85200300d42e4060f01e180c2000c03400100a2080180c030000520041c100d0000519000e4070415104400004a00d50f00c1c00f0081d00366007003492420316a03801500a0141c811502e4208042102c06040d55041032911207800784420080e84141e0b007401c400d07214610070a0f9200352807540c07040100e0031104500f0042c0801c2201d502c020b03d47c3c94000c080ea0069a0a1404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 728618372 1250 728617122 728617133
    0xb0712060b0412060f02030108120a0e0d0b0114010f050316020c04020c0123220303090611130e090319021009061e0e0a111c0506070801060804050a02100903 69
    0x800e400440c00343c8514122082008805d10880084030074050040d8107542c500700440e9140c0400c000d1205403580c000441d250300d00d02ca03e143e4602000010030300c0d03980441c1803c00220002c07007402810b4206e600e10b10807280303540c0656100b0001c250295607480c0707165500340c1701090010444201e00207500ca04280c2d41920313941d90018040c428428000014501088081c03d085004110b41c5140604507040611840c1d8440b940001070219101c2d28022112100307190032801846003200c09003202c0d00e401d1548848000c420002c00c02c0b0076035409e10340b020686a104040e00d2803000d55000072598010881840580740b44204a5160070f241d00541c0d0841d80f4403184001501d401c1c0301c003200d04680d11640390749107010715603154031800081c200800050710034660302c40c1c0c2c44001c80b8000e030408510346003214140da601102c4450200780300711103c1c41c004a40c903016541d90740035150000814040d40010420a00c5170301039a1250b0b401200404001c10039400703010b2024000f0f04004101300d00e055000c000700c0c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 728619622 1250 728618372 728618377
    0x8090118170f0705010506190602070e311119050d060905060114040c0801060503061212040305060a0c03110403081c020a0c0c080d1202130302120303010f120b0712060b 74
    0x207000d01c00129047c64002c0c1000a071545a040c01c104d80c0610680601c9174a50001781c07401542c1102074141034648448040540300c408100d111a0700c2040c5004403035501c0c400459407111540308059001120100408203e881889560511000080a2009c000625100400c0421940a1080041c084070162145824101c0981100150f2000d0204044c01030806224190b528651442c1c03420195050a500900c603100181a5038458021010b007a040b04105110101100c0001d240f2103540c0c1e6901d280050700c0f41d004881c60058149049001030000e4007138003c40448041c088416031030320b8190394031842c080d0001e960710250417007950107580307a0758510310040100042c1c6458082d400182868155181c1100703800c4020f03190015000c580d0065003049000720403840c540c102580310180c03441070700480071890380b000e9480824901e5440e2480c402100560581c0ea0059448a1094030340c03421207075003510510010b003001540000226130700c0c850170603038000000444c0041103099451543c1da0b0681c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 728620872 1250 728619622 728619637
    0x90114100c290f0601140307030218030118020406080a030e15091c0605090c150d0b090c0912030304020f090901090c0803040f0602011a010305040203070f1508090118170f 75
    0xb540414060105505159664405024a40507125071182200c0001601029148400349600820840c0040300f030801005002ca44c090f0003003048518910080c05140710050341039001c1e51802c1d9001c5403140c40402e248000e541c15441d0682d0301a065024001d000354558076409078140d050100f00d6056849440c0c000c003001c0794a11806882d800340c1849002c8441c0a00040700603881654000c0032500d030500c12045401000e64880d460340d600001040107070030564042680501c2c18010001c039011300401500c0190030981e0381081c0001000c900303594902c0260743c00ba61050410b8041c52091401241546d80030115000100341071a8659611180501c107411010468101184c28054141e101440100900c0390f84002d1120742e002e48203045082485000c00e60406482d940098155102085210020065001c0120f11175685004d0100301d010411480400100080e0126810a905010b580540c4464640c00c408134081560b480c80c07a084641000007102a0510401079000b180c9070161408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 728622122 1250 728620872 728620943
    0x9050a210b010602100c020303040b07080a060305070b13080a030c060b2b140c060712030b1f1b02220e010e0307020f0306280612030e090114100c 64
    0x20981c4d0b15900009a6400e44d120b06e0441d40140100300110f425400b407a41c000e106401d04a4850301d07410f4007000540714942010341140b0465600064054204001302060002c105102214a031038024072070706c40b6020a0050b0000e179400003d00702040356a401103003400c01c0100492105d421000c501c0c00424002c02030802d402c0341d0b483c080340502052a601d0008803c03000050300c8000308080c0000c540b402400720103419840f0313500f803510b9030a00903485284910b034001c14849080b21105007926010903400038110014803020041480940043c3e0056501c50b4000c1004111090300902e12181443c82c888002c02e981c0c480d04103800405080c0f244d0b07042c81080340d002c3c50344d90480340103014208145010490007540903000300001400d00c40d0017100c420b5a10462800541c0340c610502c00030b00f005070044d00080204500780400c240c4c110205c03005810044c1c80500c0e160780d0301c00c0c14401130b45a50b010660001460016090203078850790510300681e1140c9015200c066403c0c1510314900400c42d0103806 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 728623372 1250 728622122 728622133
    0x50c0c0a1202150901050d0b061201031203060b04050901030201260a020702030f0703170c0c090f04051608300c03040f080d0c0b0402030c1002100c09050a210b010602 73
    0x2d500b4504510034a645040e05030524000341280006c2c0b00c3e12030b01140b18022039032540e00c504580d881008035000d0054042d68844a56104e0608414000412070002c01081c0b5000b0000754040300042a203040364002000c80d1314581c40c540054030036400c4894810803c800e2600c1070780d10701c00d0701280980a0002c00c0c000689408051050515280040c80c040000f60b100c004100005020030380100c460303041c000c0c080341d22100300381c40341d40c50450b01424855000e0344d90b03410040140901e45806206070b01410464558203130321408a040070409014115840e0010240d000480d0710703801c100310240000303000c815182c40141c40341100b5600801c0c00704800d0341000400300240f0035480303000b5000d001e20802070565134055401c09400c003003032501c1c0109908440000101075580c103100b290024000034200392518400700340300035165101c101f000c2080f14074041004103100d20508000c02902c0c03010f420b0700c40b0542000605040a14209606450002c100e00840300040c06c45201900903c226001400c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 728624622 1250 728623372 728623409
    0x512070905010e03010501051c02060f040e04031b03020c15091903020916052209021c0c0f120f0209180403030b091509040302100c0206040b07030903050307050c0c0a 73
    0x10b119000443c0c0720b501c00e0b0305044c0140141e554119000b040700c02c400c89404210745041c8041442070241100040540f103000ca40054002c820400142c480c910aa85c0c107410041741c00ca00c4908001d25a40241c01a8840d1940c0c020909040c4c0c480c01520f2440c403030080c28902c6010000d0780d00f0710704100c2a04000c012140c100b04600b007190b00d15810034840e41106011040c01d1000501c140540e14001d80c054101e1005004e88400c0502000041c240c4101d00303560b034015100c0d010443c5841d13440041c400c10302c0c0c403011b08091072050f075000568452958070b941c40300081220b070b0405000c0030310390000450750810000e1136682d20708040c034103017903030355400c07049549050304010702280c0203900b81c0c90281d00b0000030042a0368017000354a42001003141c42140c941c995080407407601601030600b5000e00d24008510b2a22900090810b01c540e100b0420740101d583d0f1900100d00b61440410014080b1b9024030110760202e001d0809403401000c0501290311410070b440c0040c048c898154001344540c1791004515 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 728625872 1250 728624622 728624627
    0x30f0a0b1c060c0f1b060603080d020304020307050f150714161406090f06031f0b040e1b160f08040f0e06120705040b1305151201060312050a051207090501 68
    0x42d40110303060810711001a007050003e02810000c40340c4544103800c0001c06020001b0703650250000e580c2240d000c988070a040031822000794000d540507403291054170800103052800034440c4945110142205628080c154862142600074180c220748101014800c0b403102242040420340160032441e111317034072614001c0d440005541c800c0086005510030491901c2d03d46038840d0505103502d051f21a0340c1c0d00d6550308402d07000c940800a6a05444204440010b01c40c0d0002018000381e902d00403a000e41b80d200d40411000d005043d090050142c6d00c2444014060840c0f4015107000601545072030074903449640e41d951840d44181c00c0900c88614035101030108001c0404101d902c03050940d4502d26445202c00c1c000d5481d99903120f0144503d8991264010513110729449501110081005101c6030401802111124910383d4440d801544210301c1017604590500404e42100d0b0480e8881d800c291920b44c003110154040b810322001c1c0501000f1035002c58401540301072084600d5942c002c81f650401000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 728627122 1250 728625872 728625881
    0x1507020d0b0402210d0f05120702010c0e18011413050c13080d02100f0227091b0301230d0501060e0601090321030e0a06060911040b030f0a0b1c06 64
    0x2c0a1010108095048132644000307080321030308501c0d041a941295040d18203c5d1648101a07400344024100c0040c0b0403e01d405405c00180c900c100e440c0c10340c90364443d00034000750075400c004105003083c440004000c0c80a0741075100c0d1319004060183d5151041c0351f1040c41c250780080d14140c0d2004000502180080300c40041e4002500d6128003400c1c0075018139600941e145541c0c00c03540c058980c3e0310b13054610710f40d895048403400204a9265075084440e0302c0c40d820440031031030400d0300414075140003421103200f01018803015120044072a00310b900f0300754100044c060080780f200007501141039102c155a40d54458240b403a10480c004903855051182c543d0292001070312050600080d4a42440001d415400c00c289401d21190500e41c1c195803400100c0150104114010042c016040c0180c18070005810031429031b001c182040c8031140070204000f4032846148218641c54200b0300100d115400421034450b0030004142d030114062040d0000030f2210316014116a00c5444041006010003845000303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 728628372 1250 728627122 728627149
    0x908190513050d11010806120d0c060c11030706050a090b0424020a0905010e030c100f0e030a0f080304020f0402030702030406020f070509041403120c180a050a051507020d0b0402 78
    0x30f41c8441000240d4642c0b144103a280040d6040c4001c4400085098540007580080304011504845480741c914002078910401907100342e82160070000e01c10000c60085114064041c00d00000710714043c281e0f20307031300c008210141031060381075152905240826810f440c00b40c05107000d00c00c00c0d40f81086034400c14810944180386003102c0c50060080c1c000441e080001482160000e09081e801c902111000906003a11240801d40c8801e03102c002800c00340d48010b8a40c210340003612112058604241095550b48901d6030003000d0000219032400010026009543c001c0e1003e00101291030102000805a0f0411990000141c0c000b1401f000309036410069540b00141213006449414145003b00f0701c1400002c00141410301032601030454803600300101c402c6184803a6609c072603801c00a104d1030322139000204000c40100146a000d1652030107030780440450300014480c128151400052021303e07140c3c0001c0c022000400d020050258680c500d05005070b600c201040c0c103091806104010b0289001003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 728629622 1250 728628372 728628379
    0x18012417120301260f0105070906170411011107060807030605010e09010e130524061e09100506030114040e0a0512090a080f0a0303061403060604090819051305 70
    0x85040001ca40d40400c880c151000450314440080302030000300790b180d556241101c1c1905c9910080d00c20b2400c1944180d0140c070b02552460580d0390303911011240044184910002c801c80c6030042000103440581c40e030591301e018100078500e0b0030a440000d05260300d60b407200d0b01290307070101045100d541c1841042c0141400342407404415619502003900410140903201014036a0804075049406c0381d0b10007403201d0b90080440710300990040d60300c2c0f40b91004405400c00b4440c1d41c40410410b28084020041502d04903080c100401080c4040256480b8040c102d201032076801e00011510b0344540c002140031388040690302416090581c20b12040310361000e590802500401c4c01d1070005403007c921f101480400003500390300c91012100103803484025a1014410348070780c0124000d106404600081e000780240c0302000115662804d0400607010811280c0d855045040059441d1916501c60343c009800360019a0030125101080705264071500c0e5410003150000c90200344074000301d65080050310054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 728630872 1250 728629622 728629633
    0xa03060315060b04050d0807020a0915090e03030703051510080906090304030503030f1f03060f0b01232a0601031209030210050304060b0a0b2101030b18012417 70
    0x110550782c80c0505d0042034460160000c1c0007092003400015685242d80052100c41002c1da1501c2d984001c0c90640050007a2107401600001d04100502c188582004030307801443c55a5103604c412002010010504424a001c0c0c10313601500c2e0700e6601c4245041300198544141034104642c1e0585071400041c651071903079004100038400244003000303403a00240c043c201c2d0615511986581d0201e020394407911389466203004030020074401d4581011004079a1400100501d5011400459403001c00004041c6040800c06078440e220800c42e00400c900c0001c5450b109180b008c07400c01d640c9002c80449e896415500042c01403003408169009200c00c06424108040c02501d141c0c00704985c01207904901c0c0912002100080078000c00340c00000507510010116126651601c6113041daa402c104031403ca01e07044c42c04801d0780700c01c42d01c440c03506803600308000390304a594105a035401c170892410412841d5403034140c010310640360494840c0082e0750101c012095142003404400c00d00d03d00787d41404060b44074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 728632122 1250 728630872 728630879
    0x3180609061101020706020711010e0f2407020306091c030507120203060f09040606060e09040b010905040510091a090c131109190302100f120c0c080a0306031506 71
    0x10544200c2101d100d41015540c0040704458a4024000e000c000b0300464000203454007000503501d0058235181c4241c8800400300511818401e080740010700458001c01c88c0c03039000c50340c4007444141d082c081d550140442d1815001d54040303801c2140c20b0f200700c3c003250b02c64114041103800261840c04964503c3c40c04002d01d04e000b5800038003558644800f04c203c20f5001000c1031158840c1d0507180500400645055054103180c0b8000b00244218400c000000d00340401c030040c0f44c0340a40307000d801290031081800e600d90034100720700c1c001c02020303104071010b01c106050010003142c140244450180a01c82c60b01c40c10010200903035a50b03030700420400d4260884480d6500c25a1803280251852046000c0003590300350a01c0c0f0142a40700c0c4d810803035440108181000c110403260510402640e10aa84003540104510004d4402c0c040c40c516040100340c1c00e410b07031a240001c0d03034170210005c0036910f081e101c100140c0e1681c808640c0f040048000194a52505000744440f1804100304c80494401c20003200b441d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 728633372 1250 728632122 728632127
    0x70203040911160c0503100603210315090e0607050306091306110d02040f050414070c08070605090604050708070b0901051309050108030d0c1404181d0a031806 70
    0x3450044000e410350300d0098060607107090b4141c6a07107000300c220f01c8101d501282024200091a489521302c44e200e018082801e1242a0145104680d84049282ea000c050940d41506d400217801d0341c1410559109032490901d006619003000130910781000164400360b0b0744c2064140b4500910f6281400310400038020b40e500d8011005500c1550041c0074291400d5a161032806040c02e07250620920340d01056080e400d40f810781c01841101d002e0740003c0c5000f6583c3c8180070a80d0b85004103004480e80000024850900505000c051184640c103002d00c2e00f1600d5607040b0480b44191840740352544000e0401007084001c20100018102d485c0007000e8092801d9000700040c807420604030304010000c07a0310001d501c81010703460040c1c40e6030036081c0101e607141e0401c15600d800c90003503011241d0602e150013191a0269001d80d203032000c012005441c150034111a11a1290783ca200c8480c11a0346403240d010190031510720032031080b200006001501c13508e040c01003c42012400701500543c0c04001000200d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 728634622 1250 728633372 728633377
    0x30d1107141507030c0804090b01180317130302191403210a09090617062206020c0c222306101707021c021c05032d0603060f070203 58
    0x19000e15000f0765a410078542200c110300c0420340201401c0d408a4046000300e0140c00c01c0604039002e994070040400f21811084a0711803501c00507100d80c00903901d480e07002512800900c41c0000711205400c00700c1d50fa5021a004507500b00d003102c01c5540018041c0405402d100107200e42000c00c80080240f85001e11119024420800c102901c00c480010600d240a00618001d402000001410042103aa400046800518904c5840414000d0900190385200384007000814030805813100700c40e040050391003500a50180070040c25034812210850020b9903100180059040d8544240092000c400741407000c1c0c40c120700140710f0000d030200c01c0c0701581d10380d142907035403011f012280e4800000c0781f204199010301d802c0c8110b2030741c1142c2d10100100c081d00045d02c0d451198601c881030158a0110070202c1c0c603582c113039084010a91000301c20040303407885100a5600800114030001021825490703a151a48560030101b81900b0385c00100925403070248580c40e4802d810304400a210724003060002e4491 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 728635872 1250 728634622 728634649
    0x3010e061905130b03060f040605160c150e0d0e01140405090c07140a03050712080c0a0c0302031c06170321070207050d1b0f0803070b06040209030d110714 68
    0x61509000c6250b010f059038103c0900c010018095034660306008020042c0000121800d9803035504007008602c03080d040d103d901010702160b83d141e10300f02d01d207640c80c01803000c1c02024890b1503644901d0708800d9010b050124240c0704c801500d40000b13014110780050000c03100d02d8456040c0c800c0502040100d600c44c00b24581d03100c00400503041c0e030340d48145440d8110704000300c140030280c410100e045c000c041e0803100900c2181d003c0c001c2000f101d000d10004403a00720f0200c0d40744548880138000301804500814100112a109005403410000304079140c00c1500c41d0400040d101c2d5413503003002c01c15404807082211003500400065440c010a149070121000141d444030b001e001018000141070074428441b002c0070707140080150095180c607003401d1384150b051101a40055075101c1d0005512071800d04910202c401c03a1014500b04002d9881d1000e210390700030001d41c0c11513001c100c441110b5500744003400000400f51103d007610f00091070302510780090b51b00154004041034030b021500751b43e40852080c2c05d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 728637122 1250 728635872 728635879
    0xb0a061409060a0305070e0a050a0506010e040207020d02090705120901020307050307110a0602030109090209161209020a15020307030f02060709090f020d2f18010c05030c0f0303010e061905 83
    0x40c0c2c50710408100610f5880d407020388680664203000c16070042c450368030360007154482c40c02c1c411529600c211204641090b10020b0205079000500700342410030760043c2025a000900ba080c0da03001d6a0089015080120360b104001a400611100821741e0802ca09420081001c02141940340c40100a00148030203031519042c455400c030304031500c00302000b680380307269841202035441e56581c0c0c2040001d0304c41144128406c60141c8009a414200d100505140e00107554a207003200800c60400e0b030007006417440c281d80142c054840499030745480105070b6003a101035402107a071254203040c0200541e9071101c0c80c00440d004442400b8070740c0d5201d68017a041d1202c02078002041c080020450009101d46500603440500b408000d4022009506090946100c2d0b40c0343e070700e4101c2c0800710204070342c4a4048004a03203002244244ea095101d44244929540729401312440e007828600d07407510300500e0090410391988000f006120b042880d41d08030f0f42141c0c090301c980d03c0003413240e0b089400c2c2c0f01013401110300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 728638372 1250 728637122 728637139
    0x30c1e120b0903040f0609090b090601020a02060c190f0501180b06010f121508060105030703150903050c160623070b0a1d0304090605060c071701090b0f040b0a0614 72
    0x1014140300700c8004100e260720402581b503032410054a800481d20540f9009881e0554105203400d04015151040300c05034042c00140900740e007002100d41001c50201e00a221b0841c004420341400040d80d49040d0140140c022a60b2840c07034101d00b9070318880412144103d02804000020b40090121a0024030074208185030001440f81221000da0f98681c0c0c580540c1012245400d0000000aa0381904c440c20181c50740c50380c80784203043c1e07290407900c40104030250401d540c161042007940401086407082c5046490207949102280c41e0000340b101380d1000c030118400c1000301503001302d000410700c1500a2982e060a203040c0803a40b41d8043c0c0c682c06490110920005845c40ca21a0b1083c00c3c615820032080214020560b050740c1c0c0c940140c01508030b083e1906e980801d4a1512105840c09034242c400185041070070b1142c0d06481b800c2034002542c2a41d201c280b1400061001901d0314828406030485a545d4981814401c01070384000d01407041035442c203039090003091510002000000e0058900c100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 728639622 1250 728638372 728638381
    0x6030403050a020331060801051005090420040815071b0f0212010606120e0a030518090a0c0e180109110918010e01090e03092701030c1e120b 62
    0xb4111700c901c080c602400111110b006540c881c5103000007520031043e0319041c0050703446440540b070b1440203008155014414002c010ba00c1841000140340b400c4004c0d001180d02c3e24580001d420b9180345264011800c24040783c02d10451504006640c001407a03d0800041c0c0d061040f80601703180c014a98180311091450140000d01c00d103400c02020f42ca40c0039002e82410804450040d000b400b0300e0088400081511248220107900e40c05200c00d402203217405418440c4459500f80c1c0c035039001050a405820359034140b0b02155851000040c41801c914001180418040000418060740400740500c42c1d844003440c00308905a88102c6810342ea807450b40060312140a61024556020380c1811a602c0b503e0042200011201d16071643c0c12a1034503000010666200c0d507114041e00e1076107080c2c81d510381c41403100144034a00a5031540d104218070700604405076140d804034441a00c01d03041070310461044d100c2041521071024440305d0310302818940d440c0346e5081041d0281c01418849002c2d040050600125 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 728640872 1250 728639622 728639627
    0x10e0c0c06070815090105100804170c07050f0d0b0a23041101021e0604031206090c020a120c05030d0207081c0515060f0901080c0c010c0c150b06030403050a 69
    0x1100c119880d88101c030703564035100800801c84201240d41c044c951440f031081880c00c0c00c000f04c600d0f060352030040c409807001e203154400b210000d000400a50390035400314001c1c400311618900910314908500041c200040c00d10b8207001c440401e6102da039000d9480b0010b10300104102d048243c2c0c10011840c0080748070340550114101010580c001480e4904005080c0800c00844a42184100ca0207070262078603200034a0003d000c10345140384c49800b50304084000390001e0720a2841642c85401440f0005605440d0f084110407a6a410703912001360f40059407000502901c1c5040f100e0a04640c9081d000000c1d5030340c0c4031a22401505003044000c0d4001c910801000744090599042d0180d01842100090314040604003601c0b081e1401848000030405810301820300408540c1e42c0b0360b01d401840d2030081c402004640d01440141405002d20b0140000071018800703002d044206003007a03480307030000300c06420001c441580524071480c2c99450020a0546511790005580c3e00c0360305420543d40791076071103109 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 728642122 1250 728640872 728640877
    0x2d03183615060e150c120901170703050403030b0609100509061b0303010303030e2d07150e04150303020604030f0c300201090c171002040b09011e08010e0c 68
    0x15004460300980c00401c29a9004003c440c400700704a40c2e1840408124004290354800d20340301442c06c2d000111000700200d0240c1c01000c00b4030061400c414610318600034180304110035949000000d031140140405d0541c140210541c07050100c4440f4500340d000000200030245501091003808800310b4965000d9480805840200c801010101103100d015081191650300901044020a2030040c404e0024500028100c62000c0c00015401039244a2a007111041c40e400c0c1c0c240c40c40f40301c4d1100100b040e4082800d071780c039405925107030123014039251002c000c01d079000c020303114480485000c81040400c3e0300056007900940c0500b440e54003400c420004039010000a0310203010968000340045601b00801d05200c110b008901403100010103e1004030b080c1c54421102400801c0e2a102c24800c00c81c8062400107149281070464243d0301004c88454143d0300705070301c2307440c5446000c6030b4450356503000009000e083c242a00d04101d00200d20794090400c0d6410301032603001104110002c2c00d0b80303902104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 728643372 1250 728642122 728642141
    0x25021f06090e0309090702010204030f02040b060912060106170402150c030c031c180c0905090a0204050f010509060a0b0a1d041503030306051c2d031836 67
    0x1800d1240c0c50aa15074560f81342c0c8041d801d0343c011112000021704651043c42510280c9610074440c00c03144160703400f04006085039451441d486002044007400660302c101c0c9030040c8100078809001c40d036140540240241440300446158242c0701800c000040e0b952114840642131811402030301d4840701024a4034600035840315081a1000080010240c90050b9a1180c1025003090500010826a58045510faa1030350000d001d100d17645414000c9210940110f80c0c4420030104955030521180c00140c165681501c01001820a41006115509043e90865401302c4e080c0c86c40940b80c3e1030124002658825060540304100701031100d0141c0720b249040003c0c1d950801001031014500d0302c14038510f03070303d15840110040f9281103400541420140d03141c045c0800224001e00c52a440380e10b83c1408800250710741c0c0201c2464900340701e2003410302180c40070703507074000d64404400441c501c0008903c1000c58000751148002d4201d14010341c000580b0400101c1c3c030081c50868021040c005001c00743c41d0811 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 728644622 1250 728643372 728643389
    0xa0506041b0b0a080f010902070f06270f2102190f0b0702100507090807090506061605030c0f01020415051b19020f090c0301260a080325021f06 63
    0x81440602da4010f507442d0140a1701288820583d90f902400002c910541a0080c540f2600e80c0c01d40010440a0f4092150020f000c000580e108440c80300c403001114001c0300448110305995003031814403401c846140350203504e4480c01c21040490410207961122210292841e0201c003025131010828200341c2243d5865010010203640c0c03c108401039107070f80307801c0c0c1019220780c0f81c0b0000429135480f0382c552000303d07910f000290081c142842d1940001e044010010780c2c1010b8100320a4500e4000c01c008030000501032406103403a43c1c0d510603803604005a0814043c2c03268010301052010028881030142d40103542c0c103000350340380700300b10010008044c0c5207900180e5004175142e10401c0500300108070011842251040c3d20140c2c03240400c040200c0940d07550407505030500042c88506000d190118290b855209036801316101080176034500000c241040b104010080280a100c62083d008010041a5006c2d00340e6101c0c4050030095440c0c0b10004600c2c198080c0070841000c0001b10742c0110702800c0c1c1c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 728645872 1250 728644622 728644627
    0x7030c0209040309030b0f040206030c0c0c030a0602030132040902041b02010c0e060c150603030705010501080313050f010c02100302071b0807060206071409010905030615040e0a0506041b0b 83
    0x1d0030044d100f49018032003510f94064a40000f0821450800c6043c402ca074000e242e14156110380e80180201d8201d1991603440b8490200245080c1d90104201c16000f4410305026035250f0600c0112201e401102c440e1545091800d440e62401c0c0301c510b400d03030f8040304c015030780003031046610700018000c5d00640b41c21180c40e400c0e00d2100c815065040d04030028180345500c800042160050900c4650b200d103945815042d086004580b02c880d03442c2c0c02443c0c103c6001011203040044645405007101c400307900c004400d81c000591350b0701c581801d1881d04002c142c225034040d551f00504001074241007030a84001e01c19003840b80d0100003a4001c0c3d0540b980749030800e1034143c4e81c84011209400b0409103010703400071032182d5100003420300c1c40002c415124000c80d6035610720300d42196083d010030707401c41040755060107036244002c07925403400c2184034403440d90501d8006c062010340042c0000c854020b64001c21940240d89007e01143d800215150016444104420740c244c40960154048110b40c10152041500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 728647122 1250 728645872 728645881
    0xa140a0b24010912061808030f04030915090510020705060a050409060504090816061509020301030614240a03062c1b011202041d1e01031203020c0c060a090311040b01090b07030c0209 80
    0x24000c60074030440c88ce48504145503120440100e00c4d800c22000c10000401c0c9000034000340c1442c91009110070000d0044a0340c00e0b4070b80c4009000d0740c01c544000030004e03001140c00c2010390003a002d140002c20b0251410041100309848040c0c082c8170394941085003210b01c0e020071003080359503400000106881e201d00381c142c0c0c0e1520512000f035442848107455180c100700064503200e60211465000d007440d030f00d103424260100d08152003114803a506042d4040728142000022401d54000d41d1070740e81005001d2200311080400c404000f2040d82c01503a100e40c80100203a290300501103a00e58048800d0800e031500000401c00d07000a44550341000300710702c0b0010300b540107526001d42c0d081c0c014441104100d01c842e401c0c0c0141300c034624003444013030009240403210119103400b9a005180740c2040c2c0c0252440b09810300040707500740d0b112114080001c0c1c00b0402c20420f00541c42100e8608540c01c03101484600107010000300565514003d13048440f6002440004060042e84050710841d4083c22425071440e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 728648372 1250 728647122 728647141
    0xa1e0302040501020c33090d03080f0709080619020409090b010e090a020f060903010905070b1e03012d0e011e0602030901020a140a0b2401091206180803 67
    0x500c901405481798220402c2ca92030403a04050000c130302c1095012440c016a90f00d4110301d01d407540a0910701c2c10412291400ea128003c83e410518005c2e25130000904000103010760060000349480200320b8142c00a210b140804584540c000741c0c407604503c240a4081c030050000d00c1b55502168a0a182c1800482040b0a8044a5040f209081d10018550350340c0082162910642c1200951148007282ca1800038034000300606548600a00006035a8103e9981c1e245410440c5e0403901c03200f030000c219001c0d01c0e0b01c0b0107411680c840d031700881c80d81554504102011000f04010307010106d00e0180c0110fa101207036580707504008000c0f4000190b82565900070807806d000c800e9181c45018510103e020885034000000c40d5003100060780108418402c944410320039101450319824140603150040001c0741d400d016041c00341c0b002c501d140c9194000040c900740c81d600d2140500303041c0100d8400130801d20800c1d580d508003040c0c1002c0c0c040381060031204052140400c1c0c0c00010101d060101c10b0000102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 728649622 1250 728648372 728648377
    0x2090907230406081504030503040c1d1b1e030403230325021906020417060f01080609120c0102130308090f030105191a150309010b060a140a1e0302 65
    0x1e4041e501000001c0c2c0340c0c1090364450b402001a4844d43c0115004070300040d11450095501500503000c01e10000c1c0c48032964058501d180c51503001c8902c0d010144004142c400b84064060854246494070b00340420400f000c200e40402c01048101c8000300014081c50b000b49040c413103000c42c2020903000c0351900d180490b50b542040d40e03051040400700b41c06030140720600000200e00c18468006040000c3d086540d00c011200c179040813a4215000d1000240a2007003101c4c0c03c00488009015003c140b42c411416190b14105a2003500f5a9102d101400410700c00480e00b980140e0403401c00c150f0700c14803500220f01a10070910b02e003d02c8281e540e40001441103000240c21841c8d021103c1c80d404100950401d03080e980c040d40c8031026101e0300c1c1c100f264000c6050344069490b0158204444180080100041113a0465401440111720000c10850300d61001e2140065104d4116465400c0280f505e0008194150380311102c0c200701c60020f1001e1005003e00c01d04140d041d01c007409984103410f4050028003a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 728650872 1250 728649622 728649689
    0x111305060d0e0d021e01060b03010e07031b02030a12090b0708041b0b1b06160c0302010f060b12010603020703020a02060c16090606020f0102070503120c1204060203010e010806040f02090907 83
    0x11460782070394805e04038043c0200350417a0b20b446011070540e420301401000d0344002034405000d0560721241800503501c01041c40b0180c944035005591144000200a4580b18800e0b1aa0038418940000400000c2d415001241c00c0a0585400e1b201d964440ca0001080000c00c110b092030300e10003110004010b07a10000405606204005912907003580e95203080e56208103690840c4051700200c0e26132850780c0300c0d1180d4a07450740248004500401400d24a4003100c1251304032400c141000204028140c910202a41c0102418902140b8006e4182c070b0080d00e50400d440007e2203104005040c4d10100010051090164000c4960301e1003190358448440042c15240f1604000d401810b10201d20000c0610030b40784880c0e00070700518908660300815126240c001003807a030780d4100500c000d200e07411815206a200c2e034818040180d580d41011036488920205034059001540308004000000310509030f00030040e941510980ca0380d4480c0c14051f410711000340c0100a040d4001401d840d03000c0440240d0581c403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 728652122 1250 728650872 728650903
    0x2120115050705060117160f091508061f051002011a15041503020c0604030c02031504081210150909060b03101512091104111305060d0e0d02 62
    0x9030114107442500a524001d4102e80012004001281044100c681140354440030b6900c400400c1d1081c410080345a0403e0315486034054050054201c41d06c0360081007045281d001d01514941002a42d0f603020082c0704580390302c003518080007252645521607001e840b004255100300c0341c43c1b190080c02800d204002400c2c01d25409038544407400c0075142c100c1c2820181e20305928080c01e00402d60f00307600c0000345000400d0b42c00c101c100400c000600155010b103100c1d540b01c0044040c00d00401d491300c040e0300102c49240c070324102880000b0301c0c1c00c0121581b00c0705005840007582c0d28401462001580b40e48208200708501c4014a8843c2d40002c44c0c00c10707101d8094041040707503154200b203000f600007168641d141f40d88044080c854406101102540d1b1000f41ca00348510310340410044090b60a260402c0b2900761824824800354a014012650100d20f10300a0508140354003600050000701132043c04d0050741d0000701b003100d1041e15080754a000c0402802c490004078100c00003951080651100c1d1f06 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 728653372 1250 728652122 728652149
    0xb040e2d0c0306240409020304141608011a060327160906090e19050708150a0509010b010f050702011209050706090b03071e0e040509030c0111120a1e021201 69
    0xc0d11150740c010745913421100719400c01d402c01500ba0020350001d4020b542e0b170125400d032407a07402c00411221202030380244604021505d003084039401d49803039481d0500c540d510b20440d00000e4030360f05c042d40d620800000803281d030340c8007266001140d442d0001c510034160140c0706170b480c008154014008200c418660042011564488445080742d82c0001400f00640004e007140203070021448080d00450701a00c256140c05070380e981094a80841e142074050710711061010400390824911420383d2103d0070000a02104640c270000800e5542707aa090705080c1700c0041070100035640301c0c007410381185080d024200410380e454105103580c0e0100e2b1041c500040e004210216041c00101c0642e805265682c076400340c1c2518541902c52180c00c0c42512104001828009112a58032402024001e0450314040c41c0d85108017080c582c2510540b074518548031074104060810360504003042035000003e00000644800030004212400300c0c04521240c0150001c64080c0100510411090403940150201038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 728654622 1250 728653372 728653399
    0x180709062606190b12161106041b0e0408070c1505040905070309050312070e010e090411030f030d0f230a1a1002010e070b040e2d0c0306 60
    0x1c440407103591102018070000c402040c0a820650041c200d000d0070341881d210160f48540c0410b00c2034018611a141c0170803101d040c81038448601ea01035000031620320b03140030704040030810780d41d0354040075200034601482407102a2845464405510152591080540c2071742064108a11250015070702600c001740c502c140000c041044541a181c0c0180c65141c840c1020316040c0c09000509000300600b06043c0c4034501c02d000104248002c01414901328140c2d4080e0500f980300500c1a081c102159061100e440340c101410b503918030307032543c1c40f5500030004039071101b0a0000c00c0c10710922001c00300491202254124801d01d0542041c80405041c0384100018604080e40c8107603940412000301905032040f000c41d80c070030f0b61034102070309400380c0c41c0a0350582c00f1210080f600c844039200031000140d5642c2c0c1c54003030301402446413000600004654500f42414541d4a0020000191509038007900c0c040d480c1764040103210b0b502001206200001800c1d00e800000b00c031181e8402c86000c0d20aa2103280c0e0301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 728655872 1250 728654622 728654657
    0x11110110c06100513020903160e0a0b01090605070605090a0f0f0525050402030430020105132316140909010e0c190b07050307021e1e18070906 63
    0xe400300e80005002c010071781d8040c440c0314029400349035156018065169032526030400903104100074400e00385c0c5e10384c45180c8481603008690703008a0190400004600402195a104041d00c80254010000042c2c3e529041c22a82c0303025584034000340900c00440010041c84000080c61003502e0140f01034401c01c52960310061204070795402c04841c0492000790512440c10141e01540d48241720351010261280403009500c10300c3c0e4004460201c1101941a410110b54280505508080c92000020300d07450344c0c0e520301002c0e465031005412000c1840c1501845602d0400050498214049803580420340303680c0c40c0558041250031140c0078014600100385103600522894507140c0e045800f426401032468104104222a80c1c1c00103900b00d90780d0f0300480c40301c03485801000b00360b10501c0103503540c08891051088455107950000b00001b0025000881a200e10601e0b0080c0040385010403075401c8400001500d0640022008180c01d518504001c48180c000ca64401914082d8035184016131a04544 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 728657122 1250 728655872 728655901
    0x207090b180c0c0a0606060212070218040503070611041a1204230f102f07080d0507030914011505040b0f030331030203060402011110110c06 62
    0x42a821070148007811000c0304481c0c00a54000c03482668607440c11032801c001614200c1101001d403010f0366500380401610782c041100c6400c1d00b40c250803003401c10f09540c0001d615003881d40902104817201c140000e0030400c00f40704554070306d41d120720200700e203000c02c00048a040d00b060089802c0040722101d180f080c0e1000e8016181c1e4850344c48425907056071180e0340d420b00c3c1e6860009815003008001c010318040c160038031440c18801001030080142d5034480441109890074000311240f00b030400e1902000000c4040781581c03c42c2d085100540c1d540345245049045486074040d400c900900d400280b14050b0360541000c100c01d401403a14200c40d55a10070441d00301c600056550001d1100c4900420803400c043d002400c085000030509001004200c0c042400e543c003803030040b03400781003a50742c100300514035000340e0300f00350381e20000074203110b0559012039511000600701a05000d0207541e0110024420000c2810040065000f07000313803ca91303040346002d500a501c4401150141d000040c0c2640c814090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 728658372 1250 728657122 728657141
    0x60108091e01150b0c0106060c02030a0b190204080a030e01082211041104060f140913060302060c0717030a020a1b0803030c04090f06080d030221090607020709 70
    0x5031004041c92424088052409405034200c0e5490780e180d9401c020011211600802d00e41400325900c0c01420351a90855000f600100148021001c001c80541c900180000078654450f0545505031215020f0f86130840c0032408410041e0700008010440da400454440011846901d03146180400f4034015507034403030211a0074084550301c0b804480900d00185403c00b41c24043c07402d861590301e0600125080d40e51050601102090001781001140e90050180290311424600880360004a41d80d04556120f400903e52050451004600b03400307a0b03a80c0040019640181129036850341c98007c503459103442e200d202d07001d540320703220f44103426004000c4404043c1140e01605140049644045054440404441e207032202c440000c6010042080118041d00e10314994603161442c1c80c03410020b88072110800d44070141402000c001c2c40358005121428050303103041c090384962074281d0095080c24000a4041c9001c60001440405100422524025003061b800e6900050721841d2040554a0645 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 728659622 1250 728658372 728658391
    0x12060902010329040914010507030902010914010807030e010e0a1202070e0c04060c05330901140a0e0a0213060e01051206060402090d1a090601082d1c030212060108 72
    0x410b6441131400b079200282d140e1080803000b452440426200d030131244215501c2c00460380d00e00c2d0f40d0040d580c03c2420f06c002014148015001e20001c100000c0141c58041e0102050540390385414001c03103030070341003030480c8842102140c2c10205e00b8140004000c1d1001d50100240c020b0020124056180700d170484d1040500b100c102e442c1600c0e152040302c41c80242c3c0c00990741c0f03008408100200d440c140510030301041c0c1c904c03404040f03009500e920340300d140c00280410210703a01d40702c20300d001c100040d503c40d81d02a803000f000151500c001d404250801030f404900a5000d0301812500102d001c071360388100c00703845040b050a07101d0780e00c48050181d240e03013006810400d82e20100c0040c0551820b50001e00b0202d4001e02800140d448566500403280d0320000c400d10080d101008101002000300071083c0107055900080c040f00031200030b02605a0800051071481d1004002002c2000a01b041101c0045446040d0101030160701200113000b500010044901e40d20200041011903115011703080c01880c010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 728660872 1250 728659622 728659691
    0x6060908030405031b01020a0b0a02030a0501140d0f020312220803040f030f0c090c05190516170f030f180109030e0913051e070812091306120609020103 67
    0xe076485032a204002685c50444c80380c14035000000d8100c6031181d000d004002c1d070260300e0b0306200300040250386050300702203043c850740d1b100d00205030748810a40e42c165402500c4070708252080e0000c44e08044010f00e45840580b000a10702c1a180c1d03004444a418002c0400c02540040d12031000e1600c0384114031030210300403148038051021400d8a401c86030a907100f84024074002d6038a00c2d028054894804490010500c041043c2481e410960035503c00c08005183c05840d00141501c5000c1c000b102c8034001d060584030951040d41c0704d044d00c2c00c8480006d076001d9800e4480c07030241d44422000390211007007000c01808806051421805006a00c0b50701d516481c0c45151458172020700000e8480184614a03610003003c0e4440030401c20300003000281000302c0000310700c9030b40902c442d24000c07980c0d200c0c40d01503000b0f40d1180440e00041041e119895401c4036590f40361b40010310b200025040641082c00102c1000340c0380f40411031141c0c80314420f58401e803018441681c08040c1000400310203100000210080c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 728662122 1250 728660872 728660893
    0x40203030f18040617060a110d02070203030f07050d0f180b0a021e030a35070c170307120c082a040e1005060f09041503080d0606090803040503 63
    0x140090402d500344441a00c01006010780003a0603140c4982c000900040d800c1752410095000384110341e445480c005040c04000c85041c01e5141c2441800c00c0010920313400b0a824046650038021030303500b0006d03401601c0d120f1406040194640e20211080c0d03011500002c80680218014601400c5204219842d0303005c051600411803181d5200c05d400b0b20460240381030317407624035821181380110b50745010000e41d21030b5081c040140c07546003000c18440c404d40074a820707100340d90210ba844c580c4000d45001c40f114991160342043d251050860300041c00030300900d4081301420ba114010350300c03401c2039640f1301800f059070300c400c44102c610030445d0304000f4000600180c59202001440c0d40c1ba9000001c10b440d024800ca5402c0d0059001500302041246034030080c4085200704500206c0034200803512103103803a0310030444d01071605c140c000503405240c4940f88103401700e12100d03603400115001500c07255140c0b140100000108064001c1401040344600c0100309140700000344c03005e4401c0074006010f032652 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 728663372 1250 728662122 728662147
    0x9010e0909073507050301060b070b0105131404030201090b0c1612090b0406080612060f040f08070204050f0405010f06060c0609060f06030807032c06090a0e091e0604020303 76
    0x40c0c0030a100008000e00e40740615418103200703210740d103d0a4001d00382c1c82e800d10701010300f0f65003507600444000f5420f1100c4808600c55028040c1103807421525510410022a05000548006140f1401c000311645c100003d0640640080b00b80038480d0f20305040559442d8070b070104a01171200b0340c010300c100e0300b10100c000543c1d80d00442c1001082d030030000d48c03560303940000c2403040e4060b4100c10002000c0304140102e5080c0104180c0150009801601440c903001d40600030604000300082e1101540706e80724000d10104d074046844058014005001502c1c0c040c2800f076644d2802d440440e9190301c0d201548814501c2481028181c850a5592840100031612000050001060149c940c0c0b40e54060301940848203100302030055101e990303101c1d01e54042c0d09010b001040e0602007801c854144c007050100d00306c44104000154401190320a456580c007030301003000d060306504024101c10400040c4828048005241e0804900c460740c40086d40498503071258030360303809480082d0903510030701c101c056580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 728664622 1250 728663372 728663399
    0x90e0411030f03270301052203030204050402031303080a0c050a1d1c0c080304050d081606051801060503030c060f06010c29010806040c0608060d1709010e090907 71
    0x108001c04550800c840090780c0341c01d590290315a140c00050100c01a01034400e00301903c0000f03c402c8000300040d18000c800c0884084100710416030244006d200031040500a5061fa030290101410031074036807421b4004100e02c20a8998141e001c9085000041c03402031440c020070440c21925540c00e403c1c10032100301035034107048030400310000000303011031015551900138032074401400c00d00003c5000d00b8681499501e100301a080400386820401062005488201c1341001d0300f54000032503039071046a4040060070b4035901c103004200310305180c14810b07606000c0c0080c9250b109584001c00002c1e41d07840c20103035284900c8080340165004000043c0002000c80e03a059848113060518460005540da0f81107501c103d41154861501240d8203504150f14424907441c0c05402c0140082119050603114148000da41d0f120302c0041007007a40008085480d504c48030025254840100710707000da00e9402c011901d800103604d460004520b5100c050311441c0040300716001c0c14440020780381681c2040310210341d81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 728665872 1250 728664622 728664653
    0x50106090e012009240a180602060103020907120e010506100306050d0f0c1a0a0f030501080a151d0309040b0103021204060b01030b220c0906120509190f1101090e04 72
    0x517100f081002c030780000101c200c0142442d000e00300d40d550b80c12034000750042c1c03c21007450710340d55a10781040c00380e181c00103005030641e41c0440311702d80c03942c1c0c0b40c9800b03c2d030340f0820415045100e0305242081c069030505400c15801800100c079094504140c0e03050450807070f0306a00c03401c0d9010700c04480c090046541d40000c00c81da14000c100c0d40c0906600c0c0c250110054084e0104442e802c0000254807814a60107400107007481618076040c03100d94505414650b0b02e481d9100090414112018110b44030101944140301c0740688100405001c0080c07c3d0040d102d0300032400b00740c021400c1ca032954506620a208956090301911407849664a1b55165980240340041040d414035603581d03250b0000307036500c00e201020048490014680ea03030030350030b2130416101806040340a04c1002401071000f60b80151107440040070054002030190340382607a1034540410300f000f0032001190794540e0411304c0b00f543c1c8490403281c040c0203c01040360543c0c00444064074280300d0010300c01440000b04002840411106c00032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 728667122 1250 728665872 728665879
    0xd020318060708041e080703021f03060806010605091516030f0203070c0b0c150402090a090c050a0303090806010f14090702030909190c140a03150f03050106090e012009 74
    0x400b00a55078100c40b5622a40152030700582803103541503180160f02c0356001501c14a405013449a285d030b404107420680d0b038402d4050081400e4080001c0d54425403103a030017070803040101c0d0500e507528032010703007558030241d4840d0140d103050806030180b101e400304442e280200b5010088003030f02903840031250348080300d0040045000c1004400d000c150101140c03409454010342c5140d0f03403030082c12800e1402594010340010410404200030260780d550106c9680000030703d1020441104501c1c040442e07142c644c10441c2e000c00b0128000c402c0c15031040802050702c645404131404d07030f621043c03114402500c610511000e0480100000c605080c14881c0300e401209500441e410581c00c0d20006003200000c48900502e4640f1107403000005041d402021410441414181c5141c0080d41500721a0300c01c42c0d007404181500c0d02d80d400c030b40b19070081c0d810380100800814104965200d1900c50f003e861248240c20102e400c0c181821000b21041c440d40c2c0864140c1130741c03003142d00c010b5000f1406a0300303d50001ca60 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 728668372 1250 728667122 728667127
    0x140604182612070810050f10030b0a050603010e0402190b030103060f0f020c0a050c0402090108060d0c05090c070501052503050601050d0f02070c0608090a03080c1c0c08090d02031806 80
    0x407100d0b00250414060700c07035520b442c206850280c08000c000c91059000764802c1100c80c601410326102c000300c40c060390303002c0c0c0f4000c52040504030200d906c4000341c2d80802c0d007152001000003090044815050300441c400c50b6a05d40210720105940401c0b01c0301c0c041d50301c2c104c208000401c0014000e6020416194201c0d00200e4445100c4190104076000405241100c1d0801040c0408104083c403c00d000e50500711070850411b461100000c00d4040f0040600340100c402486c400184504416504001d010040061010746000c4e40700101c0c1c0d07040180f04035520360904000c00c3c22a9201c3d0544045084402030062500c070045134200c000d003101906450511004106224201341540510391001940310390160347c9022502e0400450740c0c181e0300110401100c8401c0c0404c5820115940030155058600071815072a04400c501140c0b00ba44240401101c020a40c0c144140301500b24603030740c40c542d4445400a0307440303041281d02c40307040a9540005030400c02c40d08100e54001d44800c10600c102a14a50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 728669622 1250 728668372 728668387
    0x120d02012418270b070f1107090216052b0c110d020d05060106110601050402090d150b13050a1812180305010903081807030b0123041406041826 63
    0x100c0f003009400c0a580725030880080100443d0459945c42000f0f4403480e124002240c8645038546400090141084c030365000214101010000500c03d256603811106a42070449480500800c0341c01a400b13440ea40c84251002c402d0582c01101030000c0c00e60400000000040d42808009080b41318000891b8803c8400c020714021410421040e4081c1200d80c448840c48000ca001e028a0f001c41680168820390040000d0b4103181c650f45140d01c449070f402141b882502811003092400740850000d610b8101c80740341d4035511500300320f800050041c10141020890000b07681c2c40450044284031016014524210150004a1140701424012030b4140f1103031868680320b62305c4038203407001d40d0021343c0011040e40900c180000810074002103220843e004042d8030b0325550701d580300030350b052142c141581c160405030b0451034400401c480d0a068000c00400c040c43c84100c008145207403da03411801107241132658000b5820010003810072641054581d010b904152000c11081441d00040d00f01c9514203018070f5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 728670872 1250 728669622 728669681
    0x10314011d0c1c080d020c0f03130302040c26070504170f0d0810060e010509040e0a0c211707020310230103031706120d02012418 57
    0x44000005103000d450446080302c1040f0151518034404401a00b0340300e0b0701e50020300e0007000c50b50398000a43d00941c070f8111043c0300900b000880440400517000c0080d4090b2012012040107091300d00c220350130000c11564600031508107030b1101c10088841d00c1c030400662503116040d1890b82c0320380f061405905d000c0e12050001d0100c0020516002c80e54841d8021581000060154034003022031407401c2801841c000403070741d004000718890042800814030305a6441c1c0d1060040307481a040c040c0060250079610201a640d03011b4052095403da1003201001c01c2610407130100c000c040c0082d0f24040d6000c4265103800c6129040070b60031442d080703000c1001c0720050300c00380000800c00401d188002410500075a0000f0200d00e00d443d2000041c40b084c00500010b038101460510307954201344440180d030358a10209450b055515010000c920030306100001056054000c030401596582210310011018451406d03a0100c0340070b9410059250a10340241d42050f5000d20700d2451910f2858000b0140001d50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 728672122 1250 728670872 728670911
    0x4020d0204090204050a140127120503030a050604020f09040b040b090c03070f0305060904030c0c05090a15080d080112060b040f0608010c1106070c020d051002040303110705030601031401 82
    0xc2c10301034010408015a24004e010440140a40d0500170150944440003e151902c110440a100c601c0c980c505407008504501c80d00203000b0172900405010180d00f403030b43e80da403c11120321f50428103103800904541803d00070390f114025140c020b1400c0244440070800580b03108543c10b600941d03107411071022591290f0082e40609407900d039a541c0c0e401d25074001088407410002c0700041c0741c20102030051984407174407003c0c3c0c440e40516005034125514503084c9491292644100e0b4042c2c03203481448000001580851003101121f0320615184c0da40e90865600c483d41c4000401c0400c0c0080c0c010840c90011141918085118501c00104040741d0300003c0c0c225075044800070742c41a030326902840121400d1040203910700103400c0c55100f0302c840320b0f900707680e0f50750042c40300003003022140080045440340c000c0004055404004c1e202d441c0c50000a01009402a1205070000740b054001c2c02d100440110b0aa020b485015002e484140e0035034840c80c031140d00d460032a138219075031441c1e0000d0301c1046401c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 728673372 1250 728672122 728672129
    0x20301150f17281b0f090b061209030306040b010c081911010908030f010608090a110114030103110a0f15051809160801090c0c02100215091011090f0f04020d0204 71
    0x400b00c0b00e0f42076041280540011145804801d002014203000c081021101003049400d403150100c1c0780c01c1040007142d40c5001d44541c405021a412040c090074a00100285109001c1510100301c800120030045031642d0f007000c0081c104810802c00301840e000d0401c1e028030304007102c4c00c055000454448000b402c641e00500c06a50000021052000c08456078070310720f00400151034118141d003400aa0305899a01041c001007003000404240b012903400b81881940c0c582158401c1034980d07a486c10314498550407945080c0c411460b800021a235501d4040000c410f5a035110017915084040c0d490a0300c840e440b001c00307040d030804100c40c200f05595030700306164031403c0300899146c140c0000c040042c18440c0180c11100d142420b05020810884d03025031800c0c000ca40496015940c101c20400c143d04001c440369444140401e91001c01002d240e000802d4800d41074400401c200d02803450444000c80e0140c0652194032a00180c444045441c02c0903c6506201000304014901040880000c0032603025a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 728674622 1250 728673372 728673433
    0x1709030702150a031413200117060406180906050a020309070e070507061d0601050406051305060a08010501120b0603030307080601080a0f051003030e150f0f0405030703030507020301150f17 83
    0x201300410050382c5c0c100c184080d81038140c080812926100043c00d00c9d03400310182c464800501c000262117549130342000c002412411020407040c030507014041d002c0c00c501d14068503554142004514001e10078802c90b4811090720001e8001c860070404030444802c0090b1100041000c10700c18407020620780d02c904080c031060112042c00120301c08944a0400c00143d102c0e500c2036180820801c500c7d03c9101c03500d44000211100084d040c1e807100300194141d0381c140c0140045601e0000040b80646440210350080c90055501280c5940e5160405641e44401ca40f060001640240415842e501415915800c424514030201c0c3c880905003902040320802c079200ba1a00380075000800c149900114950b100790404ea0b0300c40c075030012031070400045110320008003064000000c1c0c41602140807a042e100540402801c0d00c1e03605035681001026500812001d030311039481c14450b0701500c01112078000855895031080c03075046241c005402d501030b42d01561244140140c600203200d007600c02c2c118046e1901d0b0413 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 728675872 1250 728674622 728674651
    0x304061b030e06120a05130203030f0d06030f06230402060906030a18050c1008010812070f0803040615050306060901031e0606080d0311040f031b0503030a1709030702150a0314 77
    0x1a6017058400251220742419807400f848805030320701000b03c40103030b0285202c07150f0300c400f22142140200890b900103800200d03803044200c2044816007081c2c0700000f00715841046a404c415000b03d100400703031802940142c1c00c12040b259070800c40050b6901c1030290200141d0700321249944020401d00715000c480e150080004640c0f20f107443d12071400080e09529102c101917041a21096850300300d03003a000e050b007a01040354010070803032800040d090ba9010310007548a00b09454018068400b451061903840607100d0003261a04001a0452140200804c160810f91854480c000c040d0304040c42495080001c20461000c6085405000020103940004200c0700e071401c80b00500b21140c102d142e0310760600030001044020401c000b19000c0e285c002c00d281d441c250300f040410308044c10700ea02c040d0f01800023145a0001a800c1103c1e0f90420402d0407422059a03182c5004035200d21940e1030081d0b01c1501d20042cad070740b5006c14001520342441e050600082e008a842009003440c04100c407a4101030100303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 728677122 1250 728675872 728675881
    0xc12090c050108090d0516140d0305061c030806090c09100c050d181406120126010e0a060b042c0d030504020901180b0406090b0306090304061b030e0612 67
    0xc00c44590041340c88000c4c01c100d56280c1c00007001481101401650b00040035022002c0c843c00d0030054450f14062402c035000034503180c8004e0050002160040e20a042544009240d60f000c2a501240c0341c0c0d1646e100703000b5a0f1076400300052200d0142c40088004800d0003212a59215240d885451101c10388a19130340030700074905079160541d1840c2c84000c00240240003013030782d4500d20008050f11080c48801140070380140104a0b9400f03030100e08105800b100c400041c03d020f8003020256402d00001001108602ea810010b003601c0450000b00601d6100c000f1300004110b880c2d028091141000b480440c10040900c403d222804141903080c109528038400001040c0007003041031050300c1181818080b6141580000d5100740e014801d140d24a2282040c2130b04441181d40f00c0038104100070b01c100040c2d17407a06035071402480031071110780c001c1c07080304042668400000180c504444e09070380c607800d04c0307104001c00383c40703e01d003410b03080b01806031484549049a8800b402b42048202d6155140d113035142c0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 728678372 1250 728677122 728677127
    0xb040b19020a0201090b010b120103230102030403210e030a050c0f0a06060513050f0403110309030a29010b0f0703050409050a050a1b0804030e0111030d02071a0c09040c12090c0501 79
    0x4181d000d122356540c100220458200083c1c2407504407900041d00050410361007181c15201c0f50400288001c55200000308410103070056202481040b2b0b61405014020341443c1510403a0200040c00c40198018812200c0a42c81480140b10f100c03800016a00050b41041940d4640035850800310749003a26107000740b1007410540303039174a24a0840081400f00303090500002c201288040c04c090100001c0c608407000c000c02c2003040703401c4440044d04a0303040032081d06128043c060500034064002940d040d503086a017043d5a80c81d410b8900001c201441e12140301503c048903880072004030306122087c0800a004c030691700c956031284000b04008607582ca44209400200c0c2c2807003003948000c0c1c400500704000c5560100c5046e50080d810300b444d125a50154005954440700b02444043c20b03c00080c607048418010f40140051b42c4c400c00104410b1800e00c1e4402d41d40650840707800351740e4032042c00807000600c0c0036002100301d8641410240241c01c400c44010003a982210003d80b0101e410319810086075a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 728679622 1250 728678372 728678393
    0xc07030501020d05100e0f04110d03080f06030a0302060105130908030109150509010b030a0e190317090105090a15020405130209010801050a270209041b0206130b040b19020a020109 79
    0x10481a40780031800c1c11b07014020b030b0034007916500394001c03600000380400c0f403000441c680302c5400030010781e40340c451032800a00c100c0b0200c628440c100c02c5a030115203d410000356100e4190350540280869a0800050000f420a4040d000c00340784d40b0b032400400454141d40040d406808114000305e070b070070442d207a4141592101d134803150003011298010000200c1c0324040d0380c1c200803800d50105400ca8140406490028401d903e038803d41c40041e004ea0826811807810b01030a20499800121943c902401600b00d44040302d00c1c65298100f0100100042c4001304510b072444441c84d801410b090300c40c1c01080d41c51036542c1c00f03440c403d640000c0309900343d0b03081102180100412120561914104803c0000c110043e40001c003000450f5032660015010135010360300132040c040c1080104a040c2540b03c0d218458401500003d8044c03100032651554216101d0005140c2000c0c0c2c1c80116140c41e528500500c2c0c008003075183d446035011081c1880d40d850700007048c0ca10f50b1a8004542604d6504140b041c15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 728680872 1250 728679622 728679631
    0x6080d080c13120302070306020a0c38041a040b0405010e070501050a03150e0a090b010b0c580e0d03031806020309030304110d03020717030c07030501020d05 69
    0xd00140620b0628916151038501a02c0d412a0410503140c2d00d460281d10340b1030140c000a00b094004201100d289074032280709501a40910f0303884002405042500142c103030b00c82c0041201021b07200c003076100c000c0241c1015420500ca44011034019048035806841c00000740c070100c0740d5100403024442030100034001c12040140490240c000c5500e0304001803e5413040845440c00d064a4081042c0005800c1050030014041c9001e040b0705450550143c1000f01045401102e002c100d6400208114080105650500e000300000384010006940d0160345030003424440c0c0242c25000c41d81d40050341403001c00c80d01c954010307999013208030f1603444032043d45840d0b241305008000011000022541e60342c001141c02640504000840041400001d1000310341071101600b090b00000c1403150042c4000025449540a50105101d5051080c1046158500f6260290041e4454070062003c1c507151400c001c1460300560840749446040031240e42459500e0303005880e240d40c049280b4508a0300da0040320b900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 728682122 1250 728680872 728680891
    0xc03050607091a090d0b1801020d09050f06010b0409020d060b0a0f1d1f20070f0506270a0510080103060c08060a1401180b090301060618051e0406080d08 67
    0x300840c0502045e03c1d02010007010b440c00104101240c40741d502d014a10882c0c404800c0255680c0e414a503840015100041084800703200b01200400d4401d000314206050b1220040030a142030b16007100900690089142c20070040da4685000403940c01107401491403009a45502c81c05008000c0c010f8050008014a0001100c450141829541c3d840c01c81400e00b417145040100440c1c2200021180704410500310985030009400451141c50002038010455105040b6080301d40e41f544280b04079170048090064207005060105141003240303c0480b0201c1c8000b40449101030354600024064070000c2c40703c040407410b90001801803008070b00501910003102e0401041c1410020702207461000d0f2480350300d0003070313071520f41400e02a031044151f131041c14000f840c0b0340031044c4c49211981e4a40e0098039054880c1d880d080b400541c0d58019150760011001d00c4d0f00701d021007880e01c0c052049900f51540c00720245040c0c4407500245540710310a640180c000480100304483c1c1480c805044220098800e509 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 728683372 1250 728682122 728682127
    0xb0105121302090f1306050408090a08030d061505031603090818090903040302030a0221070b031e1006050a03060f0b04030218060f1516110406051507030c0c03050607091a 75
    0xb000701d4940350174146a9402100001e01d0382c1d550414070801c1c0561000981c0c0000300d50340000320001d0000140100003a803038070400c074940e503a943d201c15020f000b09001c80401e1061000035665551108281c045048a00700895200c1199031060015403003089840d15107080f16540e58480c2c2800c01f130055105a004004620301421500001d589080c00e4500078480c0d105c00154080041d80061508822084002200e0a807510742500c41d2503a0401c6440e224800b08002041040e03010602c5c5581c014242582e0403102c450510100f00c2c1c80342d01a070580350903d5104c01000800c940c0c01d40c58080100800d40900c1c1c2c4650175441045442031201442e241404a8081405103954079000d810300000012560700350312103943c0c0003111880c01220302c06090740801a12035003c0c420311402604640004846c01c000c01031b2114104440321100501c80c40c85000c0610403c1c001a0058860020003030245c003034120380d10381d25954985414811a595400a00440c408002c0d41e142000745088600b0022916030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 728684622 1250 728683372 728683381
    0x7020622170c060f010f06050913110c030c01020711032d0304081b0319170714010905010b01030e0d050714160b1305041e050601051b16090903080a0b0105121302090f 73
    0x6a041d400051000b0b4203a80da403200c0e404043e205030413a50cc20341c900d000d6940b201040d980f480e000313402c0700b2000d4440d4010750034403400394600850015a84001c403002d59170801610202c642004003040440c07c0588410040811850400c02c45030341d044510310140300d01c00214105141c14240b00000954541e144070442030001401c034070030301d069007401c0c7d240561664154103190041e8090a415007429520341a9000140310040d00907540c40300c82030b2000e100b4903800c03081050340d40d01e5a050500010380c00380003507000180300e0210362410503121003c440c1501440241e0500805096200203154840060019070207052401d0075401000c0803602040300451601d84190740c0c082d40411840c1c00703a500c0c1e0001c4d915070300810030713244220495403161000d90584100107030380ba281c00b90910f21003100360b00e00250a4106004461485a15542c2d61426071111400c0c40084e0402490190502130144408a02d4421741481e041c4540e0408109103d0982103005005102e80081c2c03100e01551154800c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 728685872 1250 728684622 728684629
    0x50303070312090c06120c0905031b0a0819062004140301060e0c0702010201060b0306010203040e1b031501080a111804090507090507020622170c060f010f060509 71
    0x198030503500360030882502001080c400d4000c252000c0b0080038020f4006010640c40d03840720a80007001101c5008200a4032120401c1d81e441915201e075560660041300c40340ca520103080300310100c031032020740f60000e11a140c2e0211401c1c4a00904085440a034840903c0c05101c03850049034000070420300c000480000c196000d1b50b8a102c0ca0041c48030020b034050440c0400d0320250302190040001c2101c201d09803c000074419242d510400060740198240f000110f81c903900c3e80202d078050392050300118a03061400300c90404040004003000c000a02410002c1440d14051000b181328040c82c41d40102a03071408000540380d940040d1400000c80c1c075010681101aa90000b110f03594040c110744e80205044003800500a00301918004183e4003510400082a5045400185c000c0c01e6a400b9a0070a1342c0715402c0d01610710800070f118040380910110039000c950345000c035001d288590050301b4504448021240d1410754192402441d008c0c0c0d05004000c19005030341e45c3c0000c0c1014bc60f20074501003030940003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 728687122 1250 728685872 728685877
    0xd03140601080408090907031a090606070f0503070b070201020d0e0f060f27060720030304080a0e090708190204030b011a130303020a02180618090c0d0b0103060f06050303 75
    0xa140c140280c0c00e0125007400700000035501800001400c1b00c44500d41440f0040140c82d094001c521110707000c1400d85001d18061450910074180507201071f0030901540c64049032840440c00c00d0340c40380820408030380440c0350b044034684134950540001d43d4a09400d01d0752009c940c0e4042030001280c1018840c0300950302c020810603006103900c2034604d8241c48225901c0e80e00524064648030440003101c1c103400441e408148a485a400b54441c2460500c05148036002c1c001901404142c603001000001c000420f0100036001c1d0401c1841c1c80505590f030500462504c40d03040e07030700001007004102040403c6a050b51020342152002500350b080c14a990384841e45003006010b1680b04c500c204e00d43c40d0f0040032481c10307103a00c060b181140c07050761a6603050203521011000401e130301651304042e10700d07e800a000c8816019240180000c603944102c52003891044d5000740c13018850303004255825000d1382e5500007201442d4040c00e0122002c0d403442c903011007104c1d0b4201a04807100e0038000e04000c166404800d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 728688372 1250 728687122 728687131
    0xc0402030103200f030d090806150102120a0309080c06040605010902092407080f18040911010f11011e150e060105031918150911240316020d0314 64
    0x8003108100e03000010b0700602e4013011307858142c42142a8091401d92118400041700c40050940b0026190f01d1a00e0b29030903100481c46000d40d00c000070341c10001400d54020400070080f40740000707201e80075030f40d482699031002d221645950700c40010700040c890036100310f0703004044180c7c0841c5000700d000045040301c113296200400b5405111102c4040c20721400840b00300c55802081c0f2507503481240900c10b02c0380c202642c0051041c005588030207107410f00c0d109103410745820450802140d0f4540004480c3c9200d440700322810080305071811b41e108002401080301c2ea80a181d03540380c03460072201c41d01d0200c44001c203141c0c200d03c1c600082046001e4004001d150050020b180071aa05d503641d000b207107010b03040d08004101d01840c0079a0f0000e0ba81149092008240c4600d240190180c90155400140ea01003103014080004104000c219850302001c11429400c50050000c181e240000d020513082d041254a0001c10010b100c0d203201059040c07080924104040c201000002e608202000740080c0060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 728689622 1250 728688372 728688413
    0x21020a02130903020c0d06020703090605090a140d060e030d1a09070e0312030f010f1707050405060109030807050102130807180209040b190801050702120304060b010c020a030809030c0402030103 85
    0x810b0481854401d00140d03010035030241c0445281125440c000000f54040141540011102200482c030a4407410880c0c085650091400740030720704103e18801e080c4202c03401268003411aa078544c0000d0414041d9424242121001c6d6840c0c07400c402042080d04e41c0100300c0c01c0c01d110700e250580301681e503902281e42c100249107844180c844a01002c41e20f003141c3c203281d071800030002200300a01041d541c20401d050720761603001c0d032241a0b91060001d4442007580240011340e080080148528140b590003107622100514010704076694030740300c000c0c5580c011007042d1800e9400191010b07108911210050080200f9401410414035149184807880c90b030281400d50540c00058000195996401c24801000c1c0200058441c903101c44610781d6034009481649103550038540000c440900100c0c2032040d5a200c4c03800145150707280d40e1b400d1b0081c0215a2420306001004910b40f01513143c010b0070303501442c840c4020503607805000d810103103004542c1209a10603401000140009102003541c0c0e0a9120000b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 728690872 1250 728689622 728689631
    0xf08010c020a1419050c01090e091515040f060e060a0503030a050d0f050703020c2b0e04060b1606060e070926030a21060e010506030406060803030421020a0213 70
    0x141c2d8424140404103044111004c460240042031040100e255265620240c03500c0d4141d0b82d070f038014a4600d100880340c2092540081c1c484040920324580c203660700000d400790059102d4400b10001d02100e03000c030200862969608807e2064030f102d042d103075401540484502a9551038280043c1c5e0f82c1c40b42c020008200070001c503000c0d41240c41e5800200011394029402d002c54904000000c000307404c4465410005d00c140324aa40941012990031b02203d500c2c04c80d6101c0002d01e220013a1100c3d00c0c0c084a40d508a6568800000c802c449000a0680800c0d00d03031144420200905103c420340b42950407007001640d129050000198112401c281124441e195008550740024425080da8101c130101d13460500001602d4105c00342d2050030039003000c15180140c04070a5501d9043e0b0205c0f840c074000e501d90b9510700001848a0320b4124055540a84104000f00b01180c07101d0045046400c2941c0c00c40b00d0f800400000b4510b85103030f0051080080d01c0348010304c81030460390001129260800e4001c4907003580d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 728692122 1250 728690872 728690903
    0x20307140d030f2a120305091b01050d02040905040309170601060e18091f02030402060403080c0a0c030503040e0a0c020607030b060904090809150315011d1206010f08010c020a 77
    0x9504041030041c0c4d03070030342201c0c181d454602100e144d10000c401280c02d0401a1425101a4000d21415004094200003070145c07070740a0740d00b00244075001c00780e80d05110082c8603001c4480e015000502c0544002c89001c00c1390308007490050030400b074035004401c01042600c0b503410081c400182003411039140d842c0480314404540042820001c02038030520354514920108400d01d200040d001c0c4807210070400c8807a0351500700400c5004c0f03000c2039030000e506c507800300000c1002c0350202020305025190ba000756806101c8503a1019114107255104a0700c50300089020008501402e04495106807400c10910004052010003501c0f402c0007404a01890350f0f44006160300d0303c5030410b80e01209800303041082400201e0601d01c010340c000c080d440d882010340e2010500e00959020035640030300c91802c07440304a403a61100641b51150000100b0800400c0032403100c0d02e50f0307503442c2550301c0c0c2c0c50020b0180010f9410001e84245010080d000040b40343c0c10300f041c102805a0000c1c4080034550002c246013400400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 728693372 1250 728692122 728692127
    0x30606050a021c1704121803020d0b0703110c0c01081003230304151d01020c0d0b06030a020d0305030f01081f0914060412090806010b0403080702010201110c0a020307140d030f 77
    0x1002044544c05a080310100000c108401c243e10310340d65940e803650001d281c02c8405c2c00300000da45000003500500c0754107109000a015043c3c0581140050401054410102004c0601a00011002076080d400385528500550b00305440d1317a0001032102d4409903890840d103404640c40c04000c1c80602c0900340c0c02084444074002e209840203000e0120702440801720b10380b402042c0704410400219421141d41c0c0c0f0b550150300029143c0d210030b0000e448501c003030b2075070780b1000d4554500800d843d801d4000d8090503001680c2e58415480f1941c86911900e881e420302c440150140581604a4500c9601ca070304400d544030b03200d050f4120904015080400e00110504e0040850520f150300e07507100d40301d494140000c000c1c120480009210180d0b9520600710340c1d40d25180d6465070280320f5411030078010001400400e80d180002d100d403500600001c14507900c00b0328004510b0780008425406a003001c040c0d13000310300e014004400102405980112040c01d0b000000380e680c04600c1000301809402403205080d01d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 728694622 1250 728693372 728693387
    0x20108041a0a09021221030703091704060e040501060212070804080708060f1f030303020c0102120a0b04360c030b090303040606170703060519021603030606050a021c 73
    0x82140d00c036001c40d800d1210682c0c0c0504110700d000c9200e00850075004080d06400208641882d5107001c401d1103004001c0601d10380c580c0041c00760020152079030200d0011401c19032515128480500c040796507103151500042c50b45812101503481503003480010401c12358000741030103403584207003000380d0b0300c030b407031b071801004a02c0703144d1041040340622100041e5100c004540d45100d00303500c94010b10306079104c9081c0d00d500307071101302d0400d4a102910303004d00229201c3d41c094403100e11480001440c0060003041c050400104403407892515440d21201403241c2054080c040d03c060304990f0b803002a0351190306c980c0f000241a0001c01441f080e001002044c4541200d00100840e00701501c0b90300360034000011626a407046a050300c201d403d0090010303016110050081900030054060720400b0304642d1448054940030b07100c07000e200343c0d00da0b1305444d110b4144001e0070010b0b01c0411000601103a0700c2d000e07040e03421562148043c40414090581016004603030701c1007030402040d44486078900c03000c01380e1b80320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 728695872 1250 728694622 728694653
    0x100f0507050703060f0e1c05090109270606030c0516060204050d0f02010f0e0310050910020c0106170a0803011202010320031b2110170304060e010c080702010804 71
    0x902c0781c0d84000007440381683c4903004102ca5154280040030b1281070042d610074940354801226000385003c030b0b51481c40748000d00401801403503c038145d2a90340b8802c000d0854090703004d528111006680c0804642c041c46101e0003000c01c3c1c1020b11410302c3d0100050441d0090086500c5170618501c00c40c41044a2581201c001d41002801040d503800c1504110310340950148089010440030b0440104460040501c1e0643c050020018080380449004030000b500000c0c00d50b10302841080a501e108100900240191030391101c00061010724041d80e944800401101e510b00d55080909014003042c1080d0480781075411a400c0c44100030b41c00d10040b0014075001000361800c040041d007090440d003140008601494590a07070781c119000b81d110103891032164035443c100d203410070a0032805001d0a40ca1240c0d210307450074144488141d440c5809065552140c1110840fa04002014401503403c98408814900207280c110209011907a814a06205820000e17060104000029041001408203010316 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 728697122 1250 728695872 728695883
    0x10030c210603080705031c02030609061002070f170105010e22050a0507030602030f07030c02062a030f2203052715030114030114010302101209110a0b09100f0507 71
    0xb10411405d0041d1241c1200d0304e180c0d2195039025401131751151600030f40e405150010004c1150303854160420541d82080d80c1c03498198003544100103400c50b20171951000411881c1d080c00b18081e140308205007140e405801c0141c0e508008400d001c64402032550000c3c0340217825110f1380e02c5446070b00b03100c6c8c80e00e0703420200140b01344214807000c81000b040790040c5024290000d84424207440b10314054042d80c4060700c611005030f106c5800503100524990038217a03c0071042c0420580e8003003641401c0460343c001c0b910307010440074000920441a00b000c0c0041d405c6a07202a1041c000d0f10103940080c014411511400f00d004040036105000c01031b004070719881d0003c001c0c078218031065480e0100d0010f410906c01e58401d90841c1d004203500741018065595070323070305c1b0091400319a0300315401c105810940f0024101007103014003010324bc00001c1c2c840c1ca582c9078040c0c559000041c16600c10008409529003002100b0f0f981401342e403130240c842480e4402c0ba0042030400150070301462004603014014040050311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 728698372 1250 728697122 728697127
    0x28020112062304020a0f120f020301170f0d09050405420301091e0501110c1c051c0b0613291306081905070201050610030c21060308 58
    0x1030100d4011110518291403100c180b80c003a10007070410089014241c0c0d07030004101881225503150740f240302d88031505c0b804480b0004000410800b0300b022078009801801d0814501d2101c00080c030010000c6a0708501d0310002401201c00c00c1100601449a0b03101d01402551507001261844000d003501810720041e4941c1054030070030b800c007400c031542012016040c200c0e4500080e22150b003018080e4850464000740b802c4040031109080700c00d01d01d42c2100554040d56a020081d1810b035180001b0600c1042e440e00808101e100c00115000e0010621180e1041c4101040071100c1580d081080c10a00380c4422070010304001c40c032010441c603110303041d40720119020002c4007161340f00305c030b4170150b03021a602e9250a00c12900c20400d14041d202e4085450181d00c11580c0c2040010310400f03601d94404c01120007000da0001c4000b140b02901c1003640c3c8032001d03035140d00411595080081411074450402d240501203101c500901500d40055440e400805001d202e510b00d440b044a6045900110780c04840d030795 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 728699622 1250 728698372 728698379
    0x90604030209040317090303070f1b0c061e0c23070e0c071707020d0f0812040602070201260106030e0309100503190207120503061201060b0a02010b032802011206 71
    0x504401c08030303600c1c8103002e17910808105211800400d6078400d16032501c0b1400c0200120b001500c5c100c0c4880881207401e8900000d080010b40c001035144000c2a2540b00d156540108559000e0b80b460703660300f90300403c50301e0441e03500450220700c4400f071502e0b8104400e000e01d001d03400e81c031801e00300c458000c00404170110052240b114803080051044038042c60459601900014041416105403c00654450340c82c41da0030011404103620420043c1c4610705113840c106422661200080041328259010307640410002e055507002240008844d40f10031409160310000c1c0d001a1380d071070060250004255485000700501181080ac40d421054014040807000442440003030055000712019180d134450b2560800d100b001c0c90007910b01c1c5a42c07000343c1e2000b094101c0300c111101c2c4c10082246500562000b0710309c1c2c0f01e80083c860700d0080c00d404030f5026a103100ea0580070382502c60208010380690311964540d4a4501c0710f07160410941c03110480b0b03403000d1400340012650200c2183c80740f1842c601c0c2c01c4000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 728700872 1250 728699622 728699627
    0x2030301351006090e062706041b2c09031e0a031407051e1b1506180a0b060c060a050739020111010f1505190b0906040302090403 57
    0x1518012040c1030000c0c0b61220b5040f01501c524a8017600755034092808110074100741d6000444d030308510300c48406072207054510249040010388090704c03810b01c09903841008044000c40d4901038001c0b19880156402d15201100b80e600d0300111039040c08042c0d10224078400d0041c01100c3c181840070303c01c1903152600d1200c10510b940080966008640740c02804c1442d00752301040544144200d488160a00901e80c941040d00400452444207554040000e22401401502948110100400101298007000d03190b03070b40d298001741880388648683c082405070030200360100c65026010b4000841c590300c2040114507140503030740405100340a13035030810151002d2a44012b20906440d940e03150103d605180c0d000908042c140704082c0362030680741080d0000d140b13010f54081e2902c1803401111038418003440900f12801c001c540410a6212180d1000000c1002c2c14075000d041d086840c104810a440c8490710420002d2080000488000c910b8403c140e80d0001500c0c01141c000c0e101c13a03454649071400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 728702122 1250 728700872 728700883
    0xa0b030603070905040807060203061c0b0f0a02271503010806040308070e06190908030c0714030f0616110105070801051801062a0624090207030203030135 68
    0x880c0d00034402e119001403909043d000302d82c000d0380c20100c80344c5440d01d541c071548081c0d8401811300390403a1311074a1300c078080030361160301d205014015036070811a41410301c40311403060700241c0710003803a0340144403107030741390300403101c41b01c032031109000e0302002c0c260030202054401c52007107011012144044000511020040f920300e1007140302e940e410209a50340308042e078800104004107134110205222221b0442c000078a400005611030508440440d40d46018524582c08000c071146103405c01e55040008041500000800d04011401352a0300398020001d65aa184000d02c0e03811800c0d0780080e042e1410b4000c041d0b081110301400006d002d503203400c04014090134028480c02e801801520342801180500840480c1a64002e541d05c00c141031108060808410760f0044140700003c0440f007410000e0200c0c481c141d82d046000740200c3c003100b2140c0d00c14010428a5004040940c0104503401c006a0301000303c038150b4980300721250030030114513000314200d0090003803030200b50003030b81070007a11980c00600d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 728703372 1250 728702122 728702131
    0xf031407020703021318020d06021e13051c060c05070c0e0f010605070c0b0a0e06220b07080901180504050f06091501020c0402030717010f1d07050714010b0a0b03 71
    0xd1a400c40780d5002e58034000c803000d903d035a0b1041c0001b416008010319160130003440c01070050b00f0260030040384a80c0c2c8868202605c0115076034850000340d640c1c21f0b238480d0310f004005040840751804503410f420000b40c6c942000c0107004010a81e208201109640114195003426030466450110261030301c0c0b400020030815035075032014112100002403c01d10490844848544c05a6007052852030718800391850b410550300d41090098075048019241c485030050b220503050071000d91480d400307680d0b03807110300720158104003030b5002e04103e001d01064180c012102041c20a107814000c1100c0041c14004048042e004942e01504000501000b500d00318000d602411b000c6402c185c05807292680901c107030307140010741c0d805a08150504104e61038036034090365003c5814107003189090001314510020000c00d81103419101d28402d02440031100b03e0507025030401c80100c01c000d0908000e58040d055028801008040d21808042849c0100081d044000d603981c003e4854880d4640340e81d01009550030848 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 728704622 1250 728703372 728703379
    0x1603080408190f12120906020d0f02121315020d0e100c0e150408030703020d020d080f04110301110315040b1509010c080c1014060f0604060f03140702070302 69
    0x1070003284030b8400300c4807440482e44501524039070a9240e8440b003030140e0101550041c04000c1c0c03140361004400b4001c10030201d102d410016980c031000704148046070340414150b80c1403441401391484590620403003640007117083c5110900c2c000030380741c8030058104c8191403882c07490000c80c40042080c1950861840c60b81e420b0260f406158290385424201c802c401d1078500003034040c01c4200c0003800c2084c000f258802c900007880340341984803405245194000c100803001644040c0c007040e5410340c14400e201c8655814030b8011044d080100081100000161000e0061840307400c000f80b240c0d4003507208040d4080c0241203540c807480d041c4c802414001456001a00030b50400c80c84100c3ca20f460445801c614903d080402e0074070425000460310400c290030102d5400301c08000008021030b0400038281945c85c4840045280071182d41a40c0c00318501409060107110030140244540c0e603010103503020780d0840c1c90000c0174407103102400c41c050451800d00340c031641c00f1402400705c000e501181c481e041e6802075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 728705872 1250 728704622 728704633
    0xc0a031e0204020d050a0e0a080d0c03060506040e070813080a080c0702090a0b0f090108030a0302070c0b0c0a0312020913050603011508060609010609060e0d020f040f0e06010b160b06031603080408 86
    0x8019840e2194031604005040c00e608002c540e580c0003507948400028082493300140c1c0c940c4860104005038007135000a0181400030007001003081d440840141c0c002c041940d04007481c2a00d40c1c0c0c00d062801649032800c14080200c00043c0445040350598154a4000340898002d003084409440200079801c041800b61640752181411410003154141c12544490700071490002100411130094000080845880c0d00760100020803049070303c0079018400d0204085e02d007050052030060186610014440c480754018040c0005d1a940e903840d000d038020844c0130203d4107644480011340105000c601030300e440b0103108004140583c0c0050381d9131007a4019a4190f9159807111026144140207114040014007544400078140c00c000304c408518034400b81182c43d8910041001a041c0d40c58070592041050760342c1c054102e81300c402c2050f01e005014200741546410350b156017034038110400540241c0000e0641c000309520b070303c04000390a25084582212403906440f494038000741d61041c402d070400361048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 728707122 1250 728705872 728705891
    0x15160b0c070b01050405060621010e061806040507030b0607050f06090606150c03041d0915130204111204032d05040e09070f080313080c0a031e0204020d050a 69
    0x4104403501c0380d030040d881840a80c0f920040202610001340900d803c144180600e8030208070840c00340380b403151080580001d03903051800307010f0307181401800c2a102c0c840c01c10400d42d1142800c40c002d90400c0c001c1d81c0c007082e01c0d52520390a4000d4918100c03801d13040740d0001451070034003802181d42c2411544003401d9130655100c4592090382d9201c20780369154812a815080c0035900090f000800982c2413500580b401d0680d6159a00e41940301501e292000106d9001006117070213080c0030130b1182d0740c0008807003603040c180034244542098034544002e0243c1d5480c04805031100d40329060780c900140002002107185814680180b1050410814008038800010041407036032100380d8400d00c003615a40e48030304003454440c800d11204001360039280c07140102c4001141d018411030703488020f042224020750742c8140c424404070380e00b404d44e401403095410038115480d103641c40c22003100440ea044407609000b001035000d07090000400c1000294458400680081400c1064100c0e620814212004100c0fa20340d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 728708372 1250 728707122 728707141
    0x1e02010911310b0301050a0b010f0201140c090d05010906021c0c05030406020a050c0105091c180504020f0c01180204050c07121b0206160c06020d02100b15160b 70
    0x128211038a81c090a00090300c64800c082c0715210444481803440442d6040a18021a00f154810f99240c41703041d484081844695030000031030404a10588000c100544541889040800019001e003800180020704a01c82d65601d1045a2606401c18000c02804850b464060000e611030150050781c440c0b139078100071140142d84210711b001600e540323403585176969655030b0700700960000b8800c00501c8010721880c140c03d08240f01d92840b81c21442c0050442003032404a038544010044031050820845045141c2c2c12000030f450f603001c64009072409600e4100101c001d156501902c0c07880d0740c0c50341c03801420650360004a0240891180242c07410401904c031744895000f0392103464400f40140f10801602c80b0001d01c10803e960342e08110b0360907003440c01c60a0b400a00d09906c40080c5841813034504005000b031000c6040c0301c0005040c0d600060003450704201d0301945880b821103214103069510601820703540c94030400c0c894112100c811240e51600030742c101c129401c0da07a8a05861803ca031400082c0d1900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 728709622 1250 728708372 728708389
    0x903011508070803070b060d060207201f0e4c050301120f0507170303041505071b11130c020f0102090d06020d02041221090e161e02010911 61
    0x703402106e41c07055030307075800300303000c541620740c00201d601560030000c21000c03903050045001102e80e131784002c8024400c078004106201c408075004034000700e01d5503a103080d06500315000d240108400d8814000410070300010b4038024121000c40500d00045800d50b109510403040b400104a000c030448960b0849500e03401c807041d000034014602800f1440d08207902244114518038101c81c03107082150a070079243e94544400022500300b16040e540040107000030850036191844070b001094200300240d103052038004004a207031402e2003c3c0300a034852100b081c4118580c4543e07800401401e211001d060350815040100140103005005024070341c140c14015406008413070040c08000c00c5400039a08a88890b4020750024054a00541e8204000115040300f14040790b0090702880b6080c1a03111841c00b1002c0394244032040d4810468036601c18802405058540380d0001d1b41560200103544040e01d00341c640d9400c20079008c01c02d6600c5481d151095505402001c1120710405031441901104410f00c401617 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 728710872 1250 728709622 728709637
    0x7090909030813050703020303130f05040e06040f050f0607080601030c031415040f05010b071b0b12040303232406040b0c03040f1214030309070303030509030903011508070803 77
    0x710402c02045506a48090800b00315010f8800d640c2c01c0703075603035000030300e117600c90031983c0718132100d40d2010820900c0c0008010004c10054509001450080c4059170303c8400090005001c400010398000034003504000c0f01c0c0e00e0103120f00499507241081c00c4080d040d0102280c860380001d04040140e2225031103401080c2c42c010b6103c001164688441000c1080310551031040b03900b00d640c880d84220707461001e0048500030003054640c1035640f405800c1c04000401902d018544488030300000f0841f203910542240c000100c0c0c10720314251a101d920b0110050685004160800c80c0a503c9080203035080781040e600649034186141c05504180c200c4400c880401c4000aa00c80700c144802c0080007810030083c02d074961044140e82c50140c0b100700c980044a20fa0b00003452216000c405d41c420001026850305440030311800641c11454140c81243d6624454040142055200c0000c54001e141c03c000380d652401c2c0c0100213204990f90b00054408640191045180d00c1c4130b00c00740014080008022224503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 728712122 1250 728710872 728710877
    0x61d0a0c0501050906120a020927010e0406021612030c020106031109151002010209010e0604050f10050f0703020105150607020102280204020a02030a0206010f14010e03010e01060e0709090903 84
    0x40d185008010344654102950712500480c3c20001c0306100d48400031510301c1a07204950042c2c4900389501408004580c88071042a000d00c0324000e2912009030f1511581110300e501c1c03401445955070304d42140039000b2140064072410440001904001c07862000b82402c460701c1e60104208a0300d5541282a610903100c081c0050036008458082400c2c69041c940d48001c80c680f980c00340ca5100c1000c50b44a1200b403030420300507540840d8813042983e010413001c1c07410300c04071281d42c01c143c10700000841401c4085011485017580c83c07844507416000d80c05582481070131103120f584404840c00d02038061701040359034001032452a1b80c0c0c41142c5ca40b201c160b40256070181e0052000c0c2e5500024030307030800010b074506100c030301003110701100680e207500041c030101e009139025607221010084003038038114040c0c200c0d0f80080e09a04091000144541c104194144246009000803905601081c010120500400025402c0110110b00d4040c02d9840e03600a0400e43c0c1c0d02c003941070342c4201803000c80d200101c00400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 728713372 1250 728712122 728712143
    0xb0306150f04060e07050d11030f011202010c050d050c010e030333210d1d01031a0406090b0111030304052a09090105060f0418170d050103061d0a 64
    0x840c0d0401e0805041d0040000d440011269210250316109400440384100068030001c0e4224014100b4003a5489130000014454103504041c052600c00c02014018001c1030780c842c2d112802560b12404682c0956600036094502040d0307240002802c42c1d2110020301c09540c02c1009031148070350004200c91050351900340904602d888200c00300501d0542d10b05981e50014003102014485e560103d00c00c0e80d1f000c03400000315007080420540d9080028a540f198241300030b24208244280404070f68a0710310038240703800644400000d07000011800301040b00c0703800600d800b2022500b0181d60384100405e1900b40c030741c3e0035903078000044035a40c0d10045900616682052401c005152410500102c0e2940705410100380314100101144075190221f400b0302180e91507405101090420240c800080c3d2402e5400380711004103c10090060704162000408100c1081825003400b10243c007030720309000980e403040c0300d1542c5d68101500038181c962752034105c6041c00316104040010000e1104070a9901c0542c50300d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 728714622 1250 728713372 728713411
    0x5060703030b060d0e01020d0e0d0c020111011409011a19260102030f1008070b12060604050d1101030b0418060506010e12010603110d0510090309090f0f0b0306 70
    0x300a09030049000e5040b943c28000000ca07644903000300340304940d10800058a40c80e0310000b078015110000d0102c3c0c050340081006540c0164050045003d10b030302030801600c04889690010300420f000c49580c015401d018003481051003043d08000c0e0354004020344040c2c2d900758030003009650960300d40c480c1103020610700e040046054075000f981b107200c020f01034a801e4003080310342c040c2a80d0040b180d0f04084e142900810180f000705c8000203001c1c0c00c1c40320041642c142440c2c4440c801e440340340c55001e9900195000200b80c0c0d44da1800316809810042c040583d140443c1c58581d10210100b40f100740400e080614941307403801c280c440e014140d0420268001101001e8440714001c1ca805040607041020442103240252903101d80d440041540f0301c00024490320318101003074444010b2010300d01c222280d014200100394001268841c4040440000030700d0603917072500350307403400301130744010815030801c607410780401096800720800c20001001400140d190508064660300100d51f024102c000d00c01081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 728715872 1250 728714622 728714627
    0xc090c0206010603240e040c08011b1d0a0602060415050408090f030a020a08070e0112020307170a021e0102190209012309010b030103030f020307111c1b0f080705060703 74
    0x180c4404a0017240445500c20242000210303803a1a0031040354001c00c98148802c21080b00c00c0c0800809402000b0460380d40c07c1207080341c1100404c40c2c00d0007004110b5001c2c8242c559520450004207400070031800209a50300000b03500d03040204c5041c3d40c6160b00c800e6149801c8441d00400b4072441d4882c544518060341d2008004081848210641c0c061042d801c0a50040c1c64040300080980708100080a02d01c1c0340c4840d80a10703c00503001b18a40096540c140720068400142c60010746134220110f8009000b00c9021601c2c0000c602e001170351040701301445501050704251002d03c5910b0a80c2500c00781c000304240380c0c2c24849941d0000b5040441c1c030004020406120401081a414500c400540f20b500c0c00009140c01900303800c41412002c000004108154125640d030354401143e0014504203150f03070312803030307040740345239130f20300d015285000b0680d4080388405450091030740e110004001203405040340012086043c040d41803091804040800c1554001031918110b803c002c18880c170306a582d6404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 728717122 1250 728715872 728715881
    0x304030c050312040c0828020919140f010611060f0903160602030a0b182419030312090503042c04030c060f0e0a0632040c090c0206010603 61
    0x151454001072021461080700140c1d00d40c090717401502c040102600300b07030107a402d01b40800d1800d802c03400d140340003d0110b850034030020138658044640e441c496442000c940c450215a0800052103450401824a1800d5105141e80601c8104809207043e030307255030003600c1e144005010540d881d801a8000b4400c01c00c89000d40d513014000000341e9040c42c45d40b0192019104007c042100c80d01d401108002005140340f00e0350b04045070031108520b2901d4285403006125034040d28800905003000e00c43e8492001c00c14805400080103403a00f006901e410032800800701217804202c001408112600d00d003042580038a00015800c40081c621344ac1c5000c10803942c6405d0202103044000360818103a1001c10342c0d035040c9106500903100c0344081e0020340b92840440e00c00d0342c6160300261902400c1000c00b6400103610b280c007a8400c0d800240c81442d0201000c0344404007008084003d40581e0300d155100032841142c0c000e52041411001c07460301c40001c0d4003502c0508200c4801644242c004000040c86a0003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 728718372 1250 728717122 728717147
    0x2130f03030203030a0f0b1011010b0604031e0305160602130b030c0a030b032401080f010218010c11040f0623030a020904060906020d1a040605011209061d01141b030403 74
    0x100001c0c1140e4280108041100236141d22022404d245075070a59408207018804040204950540c58182554ae802000c240040d07100584104403010803070070180075030216581e140c1040464003c0400b2440d01c50302035808041d50f005404144040040e07007141c0c200540e070098074100e00320303814005541c004078014605007031280e6140c403c102d0804103200d0142c8003030100e41d401c40c00d210344540c1480308081ca414111803141034180c0c41000900094000c402081032200b000b41307800d8040d049142025080c01080a03039072a8040c0c0b03403198411840b180c41d400741080f9108c1010340121984080b0240d0080c0952000803505038210880703001c014030b000c0714516032045c421880040c1102d0309881d10030880c1c103d10030703d00c184d558560100700300b1a14900302c42c03010401154240131960900300001c15a8030310421200714640c9951607607080045507080381e0749214140c000100d01c441041103003400307007401e480607101c20704c1450081001c1e01105407010900191103c040e91850700c907542c0450b150408400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 728719622 1250 728718372 728718401
    0xf06030b150307090906020c1b0109060e24130608010e040b04022b0c09020304050709050601020a0b1e130f0821040f02030111042103051c02130f03030203030a 70
    0x404d642d480340c4116030b84a030040748010385034802040c3c1a80b07000000a4800030031200c2d490710900e140c1c0d1000c4081f09641807403401c2d008012038034002c10311060003e01c0e20141000708442c1001d00501c0c06020b0584010344520038114250749a00649640d0b5081c0540d1402408800000340441d0901c030710607800c94405040301d01c00922810301d982c0110090801d02c00300304051107900c0144030b1408041800340000d0f010840c55800c00d641c0303999481080748a80440d0a880e03500103420f6130b0091008591041d08113141c20604d10704044540a0301113910303150b14414807180c000c201d81c2a8100a043c0c5d685900c40760281d6540c15a0310307a041582c2091719910011200c7c030b146185020921a00d00340100d115455101702843c4030f09c1010300b5520f1010301007440306014041088451103400207000941c0c0203a40c407001a10107424115640d1041c0ca2841004481070140d13250072200c036078010701000500340260104c0d00e840c3c695810217924540300240050b441400815a14400b99110340c10710051003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 728720872 1250 728719622 728719633
    0x1503051e16120b060d080c0709060902090f01110c060403240915091712040b061c080f0f030c0d0f11070201030b0415080109140f031e0d090f060f06030b1503 69
    0x1070303560002035408142d401f000d0fa001384904101405980c00780300040c000361030081d4101030018000c07400c044503000c00581007028122544107906030601c01040120b801800207981d49840c4d041800a00c070001d0310b8105039001c9550740c20302805075031140300403140d4401640c01311250a82c00210140000f104282c0f0302c0c03040404483d030644c161074000e048800d100803601003640b41c20b04207064144002001903000e4040e1b0b540341028dc407060510765448a5004200b261078242c005540450380c016441c00c085400d00000901c41040e1546000c0c002411071700809000040c103082c5000c00392086514907016940b414020100158003d4002c0c5240c4a005080020b0806010481204e001c5061340700d14166591007280c582400b41c4c2c610600300043c4504000c001c0300a400c10300c156030f0702c1500140940c074401c0b50b0810150343c1400b41199200c00006a080c0300d000c0c1c840c2001180780021110031074099140080004001c8198081c010480b80c11210b0f200280c1c2d1007401001811003009921903150092 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 728722122 1250 728720872 728720899
    0x60103170405060a030501031b15050d0e06090c130c080c0a110a06020a030612020a030f0c03140624010807180806040b090c090408030a1503051e16120b06 68
    0x1043e02408035600c50741e80100c0d6030f501d103007410580c480503c9121180064406002d000710703610f441180c2d4030a150780c230b041940c0340d04941030300b8000c0440c0907034141c07240901c1061003003a0300700082c802420103044491002d01412100d10008945500d5002004502402c0018100c0e41034607019202030002030600142004408110905107c52510200d82c5140d010904440c01a490b21440d0050f00250b440c14044100360707000144204040e00c001040300c5c0103400398504002e110342e50400110f9000340c4c254103000007039001741c2d00e803a0f089804545240404445851f802421020b08018880c11f03150040a500d480000302c41c94003d16000b001c00c1d403000c01002500360000c202c0581b0942c014140c800041c1071100d08d09080c0490200943c1c860000b1724103000c042021082200c1d00b204860400203110380407440b5074521260998405480b130301400f46000403417104514190607a91b140000e94200c100c411450280075646c0d40224075030196120000d20007d04040e20031500148000d260941c46100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 728723372 1250 728722122 728722129
    0x1003060506210f1209150915030106020d0e060703080412050f040f1805040302330a0f050714070201031509060b0c190206220b0c0d0e030708060103170405 68
    0x4000c1c040c88283e071140705061041c84050025400c00500381c80210319080c0e289002400000c900d00900366501000125044260b4501d050341c08142690900c03240c42e5a0b4854029444541c0b00ca26000400c0c1400c95480391840e041e0111500c0c0e40d13150711030320017076159034540703030312152202c480e030300c103202c810085c47c180c0300815006071005200b43d4121802a41c240f2040c4580c1350b940c81682e00d602800c0c0781c24440002d802190f5045d0180d440d5045003110000d2400b05450f03869050f5814580c07070070603030502240b1940c0b900300e1109120300640078007541e10340c80c0c02200d1000d03510300001040da00c284000c0d00150b100ea0840c0d642c80b090840c0500c3c1c080e4444610764100c42d41c503440034141d580000341111400405001071007400b8030209076021454610740103e103c1e07100e075201501a64030400744803848000d920410740082d19146030380b1500e0305400c640d46d59890755003860b0300d804152400d002c400f00d07250008400e81a95845030180c650340c0d185036985c0c287c003200c1b441c02d030900c0300091101044544 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 728724622 1250 728723372 728723419
    0xb090a020918130311010501240c020603040c0501030e0a030504050f04021213021002030a020304090c11060403080a0e0a051e2b082a0f0405040e150c031003060506 72
    0x3018110040d80c0d42284c40c001d03101003484060540c1ca641410010014951032a8400c0174542601a01d0990740001e8042110b640c100740d00000d42c4210701000340010b02c0b441c8041182944c0c401e807810481c203144285001e03030341d092044006000510402082c003003420a10b243c50540c80c000350002d82031440044003d06508000c403a0181064254a0508198540b00810105a207040d0018500d06041c89100a40300d01c0750b800380b6000c4a444072005510188106c21080356050a081174400c58182480c0c02006034106541d1003c1c014101741203004e24040203d2100c0c0140d501c0270003000781400c1c07541c400042000e076228603043e0740030703640c00a170101005100828020b882c0b15060307200d6080c000405002e0620291402c03c2c0300281c030b60a88800d403d5492103c0325081100720301915030501d00706a142c207104540049402034201903104010800014215085021080f90141d0701e135036160101e201400b04440707191a8000240040002c2002540620b4104501401e1041c400e000345c0c0801c0401d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 728725872 1250 728724622 728724631
    0x1507171803010f09110901030b010330020f0c01090e060d06020910052a060f151507060b01030b0108010317121e150121020c010905030c0705040b090a020918 69
    0x1c2c4e2581e1104042168000542100300000c4035805815411074560414000d4140001000740284802400c00b007280d4045170044003540d00c4041c06d20701140300000b92261130071403411a052103440c402442560140240c941030b10090010310195903070716010060b010509100986400741d0800818403c1d46900c2102500e07654640c171800d590b25910400ba00d100c140803410240c0b5400c1800c130041c142c0b0400302e10716800c407681d050480780903100e03403824000c0b120910805d580c2c0b1403004d1215000040108000d400a9405449d04220400501005406413003207614401d002414010040c0000b44003940d450b401c1c0c40104403407500f006034101f1014040e03042500c00e0706141a03041020021b02500b42c41c0ca540c070007140c2da0501142d41217000060308e200700181500103101ca480c0c0d0300709413100c0d56074190303030030341700090001d00c0101c009081c46503c0c0e0b13128500f40310386400fa6010104d5641801d004054840754041d10400f00c80d6140d998140081d0041112154490700d08545c1484890555014038000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 728727122 1250 728725872 728725901
    0x6040e15131d1005070e06033c1f06080718120212011a060f07080f0414040b0303090f190906060f0c030f0f03180605090106092c07080a060b150717180301 68
    0x21501d4140d6034003109e00002d2000500d4410700e02004000c001030034001e4119145414240107544404000f9202000c12040c0024000e008602c00610b10445480300002e40e07000b5074400c002091400c0798a400d8410341001c00c0d100c00511143c00c0c5207401e20000600001ca0076183c190305100042c3c0d100e841c07036409501621080d01c004a4140b20030011004c8054240303108803010800c0b5001da80109072240a8040550b01c1401c52000d40e8005403101c03070314080c0b000900c02500041c2519140500020301d0301e4040c02002a1070f1030051002c090044442c040160b40584404e0003000090008481204103000d02508064a504280510f140004140e91601d0b101c4e220204451402044150841e8219448140343d1800d2000c0380d400341403811802140b810100304030085c07a444500b46a46007a407d50300c01e482510503803040308140642540300d050300180807600213414003100b05040c00c2da03004a0307030064640c00440800c4000d0403965002400e00c0e2408400d502e181100140000b421141008e181544 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 728728372 1250 728727122 728727211
    0x1021c030b01030608010905071e08190c4406040309050103110906032a0d060302010e011e1101150602011a06040e15131d1005070e0603 60
    0x4072903805004400290031020020040140365440b55562134107944119184c4515048030500c07100f41c140048030180104900719840a40c0311552040c506c1d103501002c1e13441c1e0f00d03101d8021131b440281e80c49002072001000030540719461410320258007807056100701605000e598040270340300c100504c0704510a9000380c07941d40c1e000b49404005403d036030f00444505038410080041c0c40da150b440400762034001500d8592021400e100012401044007403240c51024003102084806046500d500508207491007070307039818441e8030000c00540751641d04252000310f40c400031003200d03030491140c101000c0769003500002040203c500302c00f04444141e19000500140d4480000c0e252940c031581c02c0d281348910948071140f0300392070070320700e5a1300d40006000540042004406204107503540c0400000d202403061040100a03040e01610200300d244144080c2c0d2801070720341c0c0c0d00c0c0d4414288160342c8074881984036840c594011034200440c1d0b41c00140300050502da0000c0300c1030402d482c3da407400c4003010104918407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 728729622 1250 728728372 728728391
    0x30b0405060f10060903030509030a2307090209010503040210090b0309011a101b08040b130503010b03060603030915040f080d0917071a07051501062007060e01021c03 73
    0x2040002e0080111403140c00346001085003945c8404600700304c98240c43c20702d84032010310300041c1c20428007801c083c240340c1d040101c02c40d48a01c940403150b0700400010803220100e64400e401d20685c01442440c502160051000074090b0911401c0f03070344c0b096403c4c60720700b40344c41e04c0707402404030b903001541e0104040e0355449205030b090b424444420f400c104201c48400480c040400c0007080c005180b50400b81c2220070b01942800c10003048203841c058064803400588600d014980c81c0303500346180c070400d4400c2d801d02d00c0e40001403d01180150065101402031407803c911001403152008200004d0304040030104030009490300b241d10500e010b82440e001400741a50031500007002c3d0b0b07510b0f40103043c00c803511f0078079070303c00c070a00149980440b4404138400c541c400c810042e289080c026288040e00b54090b0181400c40501c2c07011603e8140c07691512105210000801c990b111584510030421080e80006410321616004813010041103a05104076a0301d184039a40144041c00012101004a40c4640044 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 728730872 1250 728729622 728729641
    0x91b0e010e042307020d1116031719030903080609041a1005040f05010509071103180a050d03020619150302242b092325030b060a08030301030803090304030b040506 72
    0x1f05c00c3e41c45494024904003044181003100840d5034400140100c200038101140301515030250740c0d001d4010b07905c500d000e065414015010b05102d140407000107004034000340413032600b100114091900691400c40380c00541d4034400c08034001034900303d102542e4130310005440d0b03a10f010f09502e1600e810004503107545000c00b031041000b4090242c1080c0032191001c098900400000d035040310040401403440e20b516203011840c48007154001d81d0308100c4240f200018135400203006400b074410b0b5104000319000710808002116460086030704654120b490420143c50000403040c0b60343c85041c64400021005046e0340c4040d480059140d60005010f000100e1140403140045104101144140700c68100c0d80e0343c25540c00d182042c032440711a4403a12031140d00d501045111601840140e81011440360301e484900c3d41d00d81c44c070040302d00f64481e100040090425150600c03c9030495030081d030950b429907454052030303040107100141c58482400300002052241034054016406000034004030308100960 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 728732122 1250 728730872 728730887
    0xc0501020604050303390703020f06090a060209040605040204030515090c060301060f0c02030615030609010c08061e10030506030c040b010f121104091b0e010e042307020d 75
    0x54155000403080201052001c41101d82c0101100c0c15400402d00a43e50881004000e4210310b1140c5c07074111642c4164507100c802481e05c98005d400b15840b1542500301c0960301c1f0421180b030002d5400407140300300082c55a80160020540090011031280d440e100890101c0e00079a00c150307001e80c440300011040000a0a03155042a0031030041c00e440c10480000c82c01c50312062080800308000101980e80c03603442140310346030059004084c1c40107401c1595201c0079500c903071b8580f64800d000301e00100d6500d0805100e4040380e10000e071501c0440350b40781403c002e8a40900c61500010003807008102089584492100e4868006a00c0020340c6051201c24585091800b41040703004514200228180c2d80e000340e01414044607a00c0c2c43c0103e44200c8510310060000c5010403882d406002c10040f622803034981011000820754001012546240401181c000d410414540c0c0400d03802134050110341840d4002640d0070710348075075504004600140310500200220350721401a0043c04400041c1c65006a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 728733372 1250 728732122 728732129
    0x30c220204170c19060903020d050f01090b0703180515070c05030a0507110906031c030207050a2303120f0a062d050312031807120503030708010b0a021e07080106120c 73
    0x2c40c1d8105410180007600000044c003010b48240c03030003a03105007013000820042f04a8031616000340200f47d442d207001881108280c034654040b0741490009810049004c04208800750802c008000303c60302c800c00300c0d00f0306001074225410814000e482601141c01000201010116545c03a1641c45d102800c03c04d155034003089170745119510900500249680000711041241001540d48229290140054000344165075004110307001d003c4515052115108034900c003d02358948843c003003002e40d00a140c0724840c0104080d5911a04408070360503020b54520340364450032000f000505c094907800d641c40f0b050f08405c04004c11501d01d80c029009111a0201580100b00a800800000e00380c0d0280084034000100f50040708001061403802c0c07418100b00c0c0e000180b800c1c5403c5402d0f0ba4a0341010b81d00c03644110780420124444100005d50100d00404880318854142d0151610f42c50411340d000104061340c1440c031a91143c1c08010800306000c2c410381000300b083e0032056185003200d2414010a0781c2e55071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 728734622 1250 728733372 728733409
    0xa17010305150603031c020417010c05160c030c14010f050406050708070c090c120c08040201170a060e0a0e1b0102060711070e160e030c220204170c 65
    0x1001000014800507402c0126142202618070703941e50071002c6440c1d409020424401d110740321150818500380c550040c4141c41118031034841142d003091401c1d00f61102c00b1141400900100f0070304c41503000c5940f41c080180e2180918000031541d94455034102c8081e0740041d800d0302c40f100e1600c00305680000f51000700600d030b0b042c0b142c1010310b0644003404c140076254001c0c182450001c2c9450030040400f0144010f010905010807940020000082c9025500c0c0807192101d440c00c11000f400314041c901c403d10a071350507928000c20003a1582c1801303209401500034100f140d2a00ca0214040310300c04021071090f82001d0000410f0400407204074984490701102c0c030170043c6c420032480c5450360302040080d4003803250304080c001007448001c403504e4204103510500c01d200090045c0702c156514940e40440101440d514980c85072150410541c64528000381c5a41c411581001c1e2010314111501c0c04010034449a0010300780369030703040c0e860389403100d003407404449400c0740840c8411841c08142c4941c10400c030340c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 728735872 1250 728734622 728734667
    0x5161b0f06111908060303031f030515041b050303031b0c010903020606100903170304020a030f030507020108160807080606070f1407150914060d140612120d021305030604080a 77
    0x81c0481d0312882301900e1118202d040700e400503001d0504411807401568046d007156642c11010350465203990341075504031082503121149254002c01c0c2c0550b041601d8009001e90714684802e45820070241181140a01c594018043e1003d000301c28420079046502a0300904082d203444410400040020748612085c090030040c20301c04031b0111150301e85900c2206600b980da03600c43e0b000050342c0315480d40c00141a4400300d0154130415a00001034403001c2e200380c851509507158501440984030f0310b0038403031000811407400105428440e8010716004400548075500e085402c1e00c0c0c04065100032002a15108103034a180100301d00701300821001081d513000072180d002d6a640d8010710043c1701b80f248415101404109481d80e556000849152003601542005201c003084214402180101c5030644107103612541407111581c085480035000a41c4014149045070001d8140d00a40001482c82000e07000f900300451030f40c408100032070186014070303401900c4070340020300141500070003c0ca0f0b900d2100706 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 728737122 1250 728735872 728735881
    0xc03091e0203240610020a0c08031201050d020904020f01030f020f1b03070b070e0310050106030b010e0406080a0b0c09090405030c010b0f090601050c0f010213060305161b0f06111908 80
    0xf640f501c00d070060400c0701c85420604940608900d005040c240103056800480d000055090f40080282907014012001001607a0b89000f00554000c0c5500c02a4100c003007000060014070784102d0b0705d6101d800506001410408071440d1000700d810441c0c649040c158002165000d4a00020010212503d494011490700125a4039031102001c083e000ea01484484081415203540522100380c0000352050b041102d981c2d1800001c011701307040e20f5000d010030340f001084611810140110b00540b000f500081065103101d41d80c0d500c0040004081510500302440f1b41e0709940d03108414180218000c074010364440d906030301106d00715510400c895100d0113840e101d603d80c4d40c59425049a11080909110391242005084a03090149d09611a521035100144400710482c130755455900f9100196410400d650720328550710072001c950b403c0d00d40400c00800601480130101d02018284078805d90f02d204402106985640669803c01034a034281c20002c10b04c1482500610740040316203c40b860000c909041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 728738372 1250 728737122 728737183
    0x150b0420090a09180f11040f0506090f0f0c07020312070308011706010303210906090b16020f211606050a050601021f0b1503190e0d0f030c03091e0203 66
    0xc104c802440c5512919860061141108101e4902c1c8000742060203a0180300542e200141001c6038110700c181e8120000c201809000040340788075645a0a04c3e60954946084000c0c680d00a9802243d040c410140901c0b02c080949000c0e02096110351114000b550403c1c0c41e00600070b102d1005003845900100040003ca54080720040e0031000108980712841405070054005c0d2850000c003400407070030483e0f11410400304121140c03144c1e211005c00070800450b10000ca85940030711843c949950301544200a841080b0342064011614207103d15250640d074079140300c2402140001a03407042c0d03440d0200950340d41070b07008071903000341c00344080c007240c25980400071107a9040400f804030803175561004201c1038030764802d42140391841c09401034903032504481449a80010040c10031078142450750403551000d0000740c0c0c00f041c6c022929044010002004110f00802007140e001081540301c4030ba69010074074a06200c0094924190102c00703140040c014580340400e0040410321600c1190004c010024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 728739622 1250 728738372 728738411
    0x1060f0f02060c0d020c011b0e010906140a11100207030f1e03050921070c060e0607120203120c0d06050108010f1701020403020612090601050607150b0420090a09 71
    0x2444003016884414a5070710b88020b000b146c422080f40d40ca096902c6c00070302070410a980090f065544c61010900e580001110ba65565100340400b181004425110140c0124090b2003070b40c40e80c0c60020080300e4422103840c503011a900e0003081056001541105255101c0d4000c0501e4000781421030344031903408454101c514030401c0e21000c1668520210f009000c06001c0945408441c503100f05541c090000b005800b60f000c480e00321442c42d98400005803250203102c00314964400186558100010343e146c203808003180d040724a04600003008074180b4940c41811041c000e28078480c81503260139090000700107e510a400503410b100340e05004100a00d100c084d0311003580c03c04c0c0211075202800c868100d01a01403500000e6000f080820707550101d04c00c50405510603204801218030690340d4005001061090f000c0c090000e56519181ea50404595001040c003040d014000144043d40d1344500350240c03000c0c0001003003000c0000340c05090743c5084038070380007d0700009808201500d0306020741030a20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 728740872 1250 728739622 728739631
    0x120a09141509040b040608031917040309060c110a03030801180b031b06090d08120c040302060304032a150f02030c160206040e090304030c140f040e03130e01060f0f0206 74
    0x365201c00c030083d44c43c1c45a411820040020700e040700c0e150f0703c100e080b00203040c2c4140080c40004000144a01c2a025141005401103405440d0844075070b00385030049841140009040d40d005681d10882c881a480350002c0100641c0170341e98074030041d410710080b513041c51161254100001d0500c007014201d60b502046483d40d0407941801070f000e100744000415001d004007d107141d44648050201c0d418000900c00403c40707588841c0410602c0e40d0340369042102d50065000207504400c003400000c0000e0b0188884182d00c51454940191044141c2d006490301406400212881c90ba41000b018075a02c80c0c3c043d40c800b003e16400c09504500d801646101d82e4065038428280258220810f407085d03403551421580648841c107081d410528150054507a01e90291000f100d2140c0c10300030000343c08440031115548480d0082c581709880003c0803c002c084c2283c6072410101340420086e00c2e91040c0410096801440364140c4005250b2418001415200018503400103000c032890500080c00d601040c0e02d03521 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 728742122 1250 728740872 728740879
    0x7030b0708070905220203010b0c190c030605190914010b0d0f0f0303200c0613080d050a0b0d03021b060c0a06021305100c120e06040b030603120a09141509 68
    0x600b594460511191217220b888104640c8004004a0302002640042c42d004240ca4102d418820741d182c80c80600c0380c650359020748000c045150900016440e90040381d001a10b20641184082c1140b0784401250701c4014101d0f0002104030301040e08920a02030348564800031142d841142c2c1154558610a565504c40100412102c64200c02014041d074081c2c0880c0342201d124000701012080d034020180c1c04103401c96014810b0300300041100e040021180c02280d489008036080c2411030315804041c1c18060300c10302071540c907040380c0021510380050036128a8069801004015071041c40f421080f41e10680300c80c060710040010540c90315002803021b003640d03400303d001692102030240c011070006481d0083c07230b4080001164030001a520010303410035140100205039400114060035901c1c01d0800705003c0d0010300600080142c44c1d205005154001005400c3e5014200403814164650b4001170b44900442c0750884c06004040d000100341c2680042620b1010511500020b461218005c19481a10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 728743372 1250 728742122 728742139
    0x9161806140c0f0a0f1b06050d1508160e010e07051c11030a0603060f050103022d12150a050603100504050a050d02331f030803070207030b0708070905 66
    0x60980b010080c070140048460141d81a400141ca01034020180c880c1013619041032002e904071180300b4507450b0341d0481d0003580324a031401c460b0010400190410018200c0a402c40643c000746483e814409403015401241984181900b0710500724480c000c180c00003504041080d040180454000341210b480d0034401a1400d0ba04202100c004041d00c95607020740400080807043c4504168140c002c0c0b401d0728464403040c0a43e25072800100101c03070091001940c40200c24000102440c00a14001000c2d0f0100c40b0080e101e900c0f81c400724805501240410307105910828013030558452403142d494020400a20a220b5402d000c1e00003951120751034a41c0c0009642c1e0702c08a0308001c0100030400d0b40541c0081941d2011045220194686441c6d404000c64030380f00d8041046509501c03913030f211030780ca80c0b82d0740b40c0c0081c6c40c1d10390b001e14014009815500c100102d614044003083e461005140b05003596401005000d0661900c1c80b280d02e00500500d061050740414444800c0c1c0180080f4140d13601a540c400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 728744622 1250 728743372 728743387
    0x527060d05030d02220602010b010c080a1b080c0c0d0b0c0a050d0c08010f0b13090c03150803091815090a150905040c0503070e150109050916180614 65
    0x6040d03200f03030700200e4140d074800100d2080c4003070003d5801401515a114441007207580740000d900340c1e80845035007070015041034441300005400901402c1440703a00c0c5025490310390118041031021030304440540b02e007500800e00216044042101c070003841002e4400e8090703010290f0b582c05091002800d4100030710004581d880140d4801c10549840340b071260b2060007805014a0b0180c8440420b002e0406001c101100c04140b039107403842210f4000e41d11200d0120340500e0241160020200c80c0100700801d070300c9044070004a5903d080800140c0540b4000e159514001003c00c0041c00c00b4035100600c122200b4100a640821003d4100c880d4501351030b290159610b2460100003000b5804031110030502e1010003240509540d4062407140e80b04404c00c001e520745940425645089904c902c242c20045c100c006040c00504c01400f00110750181030128505803101c2c00100721f0719048030705000605400408100c81070b03012000054000c0c0d004090102e01b0f041090040040110001d901c5c007002000031400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 728745872 1250 728744622 728744633
    0x515090a0b090612360c13141608060109050607020f0a0e0c0d0e0c090610170c0c010b0d03080727060c0203160e04171306030203010527060d 62
    0x43c0c4e00d000504000101e82d00c0d26400002001a50f0121040302207036900c09240703081c00d01d80c4d00341c0404c4110310042c840d40c4104000c00026240024030001000d803544103206581800604081c002c00144a04941050400380001d006500081070641040311f000000c2015880c0d1000312590660150342c0232a4200f224004204910950340c0075480c50103015040014180d0002d000d44107141500c4000d020010071120762079901d0603c80c880e00d51151018020502928040320701c3c0d01840d9107402c02c1c01400d2033160103107550f00e00403207502071014000130713580e001001d0030b100e02c07002c03440126280b40c0500c0081c1c80040ca103880080642c000e1150014540d501d8040300018540e414810120038500f460301c07400c004102260b0032404901070f00c41c2c0d0584000100d8010408010f55421001a00b06070340d070781d20b5890901e640d04494102101040240b004e0000b030b00030040020313103010f860141e50395140c0024000303a21180e6903450300000b07a80711040c9401e890109510f40048040310300c10781e0325130541003c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 728747122 1250 728745872 728745877
    0x5040c2907111c0305070845010206010b090919020711010314070c1205090d0c031a0112020f0409080a080114010215150f1f030b1e1002010e01150515090a0b0906 71
    0x400c5e11a980300d010623000014580180a0420004120001010782c5400585c1c4e80e000a0181407e001020b004c038819078100700849a0340a408442c1c074a0a4044e04e041c50812030b848504141c07000d6810420340e2070196054020b010350201400c6403008c0700d1500307090040a00c540d4000081414100e803d03044e6850b0b10840545602800c001d01030828407265241c1890307001500d00c1304440310398885150000300751410100ca4100c0b85000700300703081e5080c65400c1010034900c10351080e504c9660340785000042028500900341c50f00300d9440398005541400741c0007813800d01c000c880e1411903004405c3d0100060714401d2458210f001502c00030307100580000000d2025280d62030361500011450111710010612050703146e803410b9951410042d03215050b0901c403040800d01c1c81070b203003580d44a0590103141440c80d01000c4ca00c40503c00080c100c0240d61100d403c1d5400040c90004203404000c3c03e1006203018518002250031a161080c0703082c44001c041000030400b8402c00041441c080741daa40607807141c004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 728748372 1250 728747122 728747167
    0x20a1d04030e01110f07031709010203041403120d151a0a03051825140108070e040b03120702040f2c0f060708070f0305040c2907111c03050708 63
    0x142c1c1d200e031108080d61744e0b072500e940c0300a990b414921a10b076201c0401040c1100d00315501a80954035060800509901c0d00381c01001e1940c03d440f540c5103021104610f400548a40740728980302003803045181c41107a8030b29950382c0061803001180903011014203104008c441000da200d00703021a140e41e8480002010b03c1c681d080181c06400b5000d10b54000150074404a943c015030460040481d649501c0d66001c0d41d060102d0003401300782c404011800c210b02442d90024440c40041020460401401c0400c0c240304254409030b258000201ea888214949402100d80d81e01031900d00700009402542c0f840450300e1444040311158411301c561502c0301070306108100b84000031604841b0340e03080036000103000d002d084030660000780d250300c1c4c40c0c0302040c400d005050145800cda800480c0030b092500b150412035403000d1b01c103082004840f1010540380713003001034120703e401020ba94a01303a05032b03400e001490040340c403c0483c0f02d501803103840010350844240c41c0001c0e008611940c075000303e41900843d038401c801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 728749622 1250 728748372 728748407
    0x1002030405040c05041508010b1b0a0f05010c090e06030a080c1c08070909330e13020f180c0901052701030e0c09130602040b16020a1d04030e01 63
    0x101d41c07400640c04c907004204641d110080c0807500d4804510844a001084c021070550301001c100c0360803940780700c0c0d440403e00c0c41034005660511030306640300c00c14903000c03180403683c0c0e9460b041c0f1181d02a4010030740900900400b8422411841e0500c002510340f1403d4a005008010100304902200e1040004801409210707440c0030401190000c042c062181c101c4070180020080c001c00705d2040c01038043d145008a02c00012065014241420f50804990510700840700c3e1044000065949003005403038000d0b91784100c0c0302400c4100d030061000ca1101800403502440410004001403240d07200d14652040008061988400d0301b0300040b5024031a00404d243c85001c84907001441281e8010000e08108003601c08008038101581241d40b0780010302e140c0c69111038050001a03001c56502034820b1101d2042c00d0061a02c2c3e210682c1072456004541e1445517003d01c201d0481c11401c060341110701419082da852810402e40c00742c10b010241004100604121405a944009900403e1040d00785140d07007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 728750872 1250 728749622 728749631
    0x9020a170a1515091406091b120610170109090c09021803011d19052811091b07060603021018050d030c03260a092a05100203040504 58
    0x40b2100c050030000c1c1c029114150301d10000030321020a4030401d941d41c408124102c0c105e6480504110004400805a500951503442203021003ca10700091255100402c3c0f84d094500708242442445c441c140d441e0b90520400c5a08030115507c1c1114080c11150352040c04030319007025103802d032600707089544041d41d1540086000003c009071b90b04009001481034008000006c100c2c80c45845520788280c0400c003941041d6a066003040e0146203100d0b00d00d0080048507140301c18890312301494041d0340350f00416841e5407120380b03040010141146241c0d0300200d41191035414209880500c41c00c00b01e401c5121f001d00002e81d4810054141c12942c021074000b40b160484c9071031036001070000c4045040880310003168101c0421b0914000d04100d0405405558080c840e000d240d4044c0c03059010300754407940010b600c112100003801078044803482003183c81d0021484081c5458061848405248075251109140f000090f00300f0311504400e00300c550444000e07140e030b440e81c6c1050781141b01d5608015086803d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 728752122 1250 728750872 728750903
    0x402070309031a0f0604090317010305072d0512150103200604080709050915130308150d080a03020f0706020c06010e0f040206130e04150c0309020a170a 67
    0x3007020381240d0082000f1600d24003520009112603c085540d00c0d001c1c1800804518039081a80c04001d1403032180c00c0640342c003415071000d00b944c144268000c5400354002c0c2410b20000c8107640c9440c0071000c081c0315104102c0100003520f00d1071890342c09010f00554030700380010f00140702044482491554030820051030750b16414080c41d06400d1178008047c101852003003e0b400c0c1015030072501100d03c01405001c21a08003e400c5001d000c019009206501c81d04011a28151240c5441030060010f06100c80502c00e961038040d040703401c01000c1d01e0744010f014520000e140c40d0150401000c41d4030081c2283e07540b150000980007801140340d850210300b4081111010401c41d540180084400340c021200560f80e40c80d1070411004c011a640c0c84541c1c218004a0018103202000c2d200c042020104004050345555644c0303201982120241c2e100c0000388804404120b01d0720828a150000345401d0018001d25004582070b4a81e03840b528200b40f1075102c0349482c0c4a17080c0019444568001c900b40c01c00b014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 728753372 1250 728752122 728752127
    0x9020d050601031a06030c0703230d15050d030807113a170a0603021003050a0c0228050712030504140105120c07050a05010c030905010e0a0b160e04020703 68
    0x2021a00700d4042440c004400f44a250080070440311450020400c80c80d540e00d1080380b0009400c0500101d0a0040701e928012080b80100401016484100c040907140d094402a04083c1e82001500c00c0100b05140001d00803925088045c01106400d402c0618450300d9070081210040507199103501d20f4043c14681c42c28012172029548403200074051501074107801c07062160707164054000c0722004120003440440c031001e000d1840300c0e406440084002940341d92500407030442044101c0601c0020b039070b4004c00c480c20200c0e201740344005226200400c44412031101e5500f01e1038103107010040e40d0180e5010b07081080310030880d20307000c1c0140200c2c0e41441c60346450042d0164005d40618544429510b50300c40040d4421000e55101d55011b84030040c06440f030118000e0240d01a0805403258020840300c2008147d090040c0c2150f51460354001809a0a90500f00c0c21a0b170095058203054101041d80004a020b000d00c0725000b00140e051200c89101c440010b039002900c0c80c00c011b40150011811806064 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 728754622 1250 728753372 728753381
    0x60314040f1703072319110a0507090507170c09130204030f030e12060c0f0a120501270e0a03030e0f0601120b070e0102100e030d0e0303090d020303070203090d080409020d 75
    0xf44c0301c1e117040341c00c125000288201809516172400f9903c004444609441e440345080c14805a44042550f0b04150310341c80da03500304684c03600407142140c0c03a1414001203030307884081c3d10001900300182ca031190030000154545449060f24061286030349518034120f1070780f154100c4000f0340c1e01c44070540380c0d42c03564a0050705624401ea41e90f8405e01c0502c0004000d54400700e5100e100e603903406a02032804203c90910026608425050b008200a40e04011a91440d9200c2d140c01b0b4114002610034081c81007000700521100c00e001c45010b14180b09030303121000030000b2003a0701c2d90351504022415071094650103207090b00c2c18400c0441071103900000070f0b1020500c01c442880c140a40c3c1100701503641d4107000d40e101d0003004151070050f440700c45101c210020540c0a04416181d11007178a00d82800e404040c8251003102008501f075030400001d00100c00d00c2000100312821050024504620b080b01c00039480340a50602140120200b800c1c01c405c21070a581140c010b003000d05001c40d2200315041e000070080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 728755872 1250 728754622 728754647
    0x90f030a0c051804030c02101110051006050c0312090f0709020d0b0108040209040212010609090503040509160914040204120302160e100303030b0d05030f0d06060314040f170307 78
    0x101e5500071200030482c0d0f80e41e01c2903c519015180ca42040c1d00b241e00f44040075021446000270842c0c1c154003c039601205200944608a8400d0046514240341c000354040d611540d1200c800c0c09401c000c05240d8120120136a0814403a094210440d40c0e91880310b80c1c00c0c00034610766141d541c0100344010450700d031160b01074210300820740700c01c0109102480042d40c0202080e07401075400314201b0006401482e000101e2420f0b2040000086642540c81d4440815200c03002c0003296140c001040501960a00780c03d00c903400b2a044411071050800078801074405001e034040c001c4d81c40e07005071980c1115110b9404403402001032060211021001c0d0400945420044411811f804041e000016034511601c45460289000402d0310305200d2540e50194000c108000c40036401c201811045c80214405201920b041c032426100140d60f00b1002e02e143c1c040b5090b60700040f0905107080e8042c0409003140c00d5003503015501c000103019150a50400c2281a04515440e20840c40d000003000701d01903003d140f4422a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 728757122 1250 728755872 728755879
    0xa05031618180b0601110609030406080906060f1c020a0f050907032703140706091505040c0b0c0a0f202b0212070303170105060a0f05090f030a0c05 65
    0x70061040070403401c0c2c518400940d101c1525500c801c01c0461005074069030850814105400f0382000301901c24106a012030320300304a50404078081084940040704075602070641c90241105103082c0c1c0000e5038080d14000e0040c0151041c0070070054208200c0d2200210340c1c0c0081204281e942d840c581046120103a0182c02c0c003506401021030302c070602a00030420690301100004140c0a10101c89081d0405803030000d4040003800213491280681180060040b14060100800c8030807050600404442c444001810528604010800464040c2032a541901d4142440550b540c08024a40d484c19008590160169841c181c164007000000300303034240c031008140b0b1002c4000780d000c0200805003075032000f00b21040d2128031246c80f039941144d54880256100500001d6044008402c00b4580130054208601003034500600803841d0724030900180c01007004681842c0f40226242000b040341d60034655080c00d0110100f070040c401d6940100c0014421000b0b0100c0b81d8006090070a4084c0c41c43c0b03403007030501 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 728758372 1250 728757122 728757149
    0x6090515091b0c03040b070b09011d03070f0c0b0a11010f092a080303040308070219081905041a0711010c080f030a0b12010b1003021c09020a050316 65
    0x3581044641c1610944500701600090b59009481282a601081d05409140001c00002c030740542d41c000a4015140209101040c40c80e140720365a0845400440140c49a840000304586802000046441850780701c10300c00d00300c125500c0d200c500394816410101141501041458180754084406881940410020b0264503550444142140c0c1902c030701031b05d0030790750f45000c808455142d1220b80c050082d15008075985030b5150149030075904180c0e0100c00040107001444000c3c0d50411544541c000341c005c440d02e07000c1196607120007138415100102121302c2089900515580602c056034001c1c2040b50024a06040c90404c001c0c4a5011100403500710a08011711280c03944910798641925901c1307401949040d8401d08440742d01c4d0002480d501c40507856002c0d41c078094032045000b000c88001c081c00402c1c41200b000400182421800d840010584107010b418001141d0190050310b558460400185404144c004222107048a410450b00344c42559020102103801000c0307801200d00c0341180d0107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 728759622 1250 728758372 728758411
    0x290a091221230f09100c06052409040c150f02060903040b071b051f030f1a12031201030b0711210d140c0316021606050c10060905 57
    0x5801da006a000d1103400c0d0581c0086420b2007964500500d081e11851080500386411000003807602c403400d90300c20740025100d01e185010441c107070154640003444489241d4890710b8880031a0700d1441110081c034801c0c280100803070300784540300e451580908600c00064010705a070101c00b0740309810804043d00141f00d0100081c0c0900c402200743c03402d03144524100c03458104251101e01c1008030a1128800043c503c1c040015240d8544070503000200e034a030103100d1501c407080d601500712905c500341c0c1d0f0f6006040003003240c20011048112460840100e82040325550700b159194514040c0300c10034000748006000101c20b00004403074040c0314120390303130700c190b000d00004503100c1c0c0380d49030904200790340710484800c3c115420708607019001d04400e141002620300301d4005085174a442c2698428480403000082c002d10002e1111030611803565030004085400f010501d00300c0c1c0c1089807248008000b004289644900e50030f000c4d0088400c0303000d40601541c0e490b80c1040008003004e41ea0031000c10304d0a103000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 728760872 1250 728759622 728759627
    0xe15060a0608010305030306040c02030c0138090609070302220302210604120c080d06380a031e1407031116140d051201290a091221 58
    0x3e040c0e0381d0100c0914290385500701030101030a000d03005e41055001c1032110804000e400d02ca400c1c0800a0700000c0c8a003641d14803404000c00404181c1165401010900521540ca8040c49260010015900d04140d07a481c40350843c02800352010481c4070004180285070000448070b0604283da00848500140c1c0c44c070f8071a004035030700c106003010041d90000e0000602180d0b104045428041031030a040140c0000344d580d00072141c2c0817030040d1041d15074810051150342e41c00e5600000760b0039000741450561000c00c040302d03100f900ca00394117a0501c1001031040d00b11032107034100c2c0441c0024110f0f030100390f41c2562880006043e51060a4405038000703c0001c1d290ba00c00d000369182c0703c029221040c03808100c00c60b540c100d81031600c010f035101d00b00114041c0e5040b41c1040307440030038201d40d5205604c0c1e0004a005400070b407010390020b070000750000d088500320103010607030300a0410800b104030382c0d030f0484100c180c414610b02d502680c40125020b1026040c403400e40104441c10801c096002c240d020809000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 728762122 1250 728760872 728760887
    0x9030d08070c0305030a0b1003020d0506190306020c01090c1805070206070e0f030f060106120b030a08040e0a0e010908031501030c08061009030b1302030715020a03030f0e15060a06 79
    0x8000000c2c03035141421002c070380900011074005920300004601c440c4c41001243c81e5003840e50300300c0c0010b940007070300c845e8010703082c8503941d08036074226020301c262200300510b0342c007240a901010344202d50001e08807044500c04d5101c42803466000f5046590556540320341e01c00c4090380000841e10500b4000000c1e00e8520204410b842498161603007610204802c0a11031007040f0314400b650544100880403a00d41c0080020500030500d076030300c1c0402c02c1d6103822910142c0d00540c01e03442c000c1e031141c11000005810801501c042d07840c01c40c1802c01035070b1154541c1001e40368480b036400b5103519015042c2c0c1807014140081d40719079880d03028058011450001141110741c030904100014910a002c6070640c98081d403001580c0405141c480036064503074448030b40c02e0206861146040c0d440020300c40c2142001c1c0410001000c04d5900704080408554000e0344403d1080d100a082665800002d50b4182182d886402c3d010010402c484c0300100085002c2c164081c02d86a80c0c0c07107590082000540d00380b00701d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 728763372 1250 728762122 728762131
    0x70c0209340e040504050d021506031513080c0d17040b07030f090818280603051e07030603060b061e030603030724050703060b0316120f0209030d08 65
    0x1520702890045001e41c0c03904440024012040140101e030040340c80d6100e006550107980604064844008007400c082d103011035100f0a0300c2e401d0b02c01420004280d502180d14100c20204065814082da00c10351012161000708100034500c140100301d600c040c0d00c002888190240d16034440d12900306204c854201c1010040701c004100003003000008400e544240c1103105680703181000401c4400310366a03602040c0e0413145d440c1e840d0f000914036030700051034000d99414140c1e522654194060b00b000d03c500e801d40405010392000e041e00d41000c00c3c13201811a0300c044075040c00d00c014200605081c03000070301600d8a848140d0b0494202401814145011030850f5030b0000c5400340002190307041d0450800a40009001d1030349400284810004101c9911807a01442ea07111100600d980c0043d1181e8201d50025210204241c03800505120174907405003100d03001400d030f07025103001c0104401c00f02c801072142e40c502414141480f246618040d5075070050444400d085050701d4069044040c02c4424250407907 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 728764622 1250 728763372 728763421
    0x9060903021e030c041406151201090c09032108011406040909080f0708040801240501050912030a02070602011a06250c031a070e0102060601030213080105070c0209 72
    0x400c1140c0040b4840c00c0c003088400040c1c01c0d95000c41c2c0000015080ba90265903d4902107200800c200341e40c5008107142e0503410740d100500d0309000620001c400e948505014080003103a0b0b075000c1c0100c00d0300415000f00210752015407855104040c5a210700d44204c409010f40c00304007141c0021901c451581c1940b03510182c00340c42030b41820310303000d001d502410134910141c521046c100100341c0300c008280d0050510310302960240c1c1e42c80d0714210405084031440ea407002e00360b0311882e01c2601001c85011140040320f9007441c01d01e40b920a5100068455044800e40d56214440021a00d080c540c0101320401114140d4008220761402602484180b5007018005a03005d002040030b100e443c2c0c40e085020b00511410b459001c428104c66840881c2d0950b00e40080d916600002612078a2140f10505a64448010319280d1101501c6000203543c0b40d10141290f8103054001c10000c001d2811040307480000e21041e00244a141400d4101904c050043c4009034040c4400c1c4c4009a09501d030981e42241010084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 728765872 1250 728764622 728764639
    0x120b011e0e010302041d0105010f031a040506060c25050a2411120d1128020c03150f1006020705040c1e09140409082703030a050a0906090302 62
    0x4011110214041c1a03141810790a01010a4015441d2455a08880c101c20520034650620b00050702c0c0c2c071542003104040604103124500c1650b5054810116000c080e58003281c60386440700015070601540d00d82054920640c600440412865500d02c3c414040050350700f541103449600b40400030500d0701658213003070f1020442600482e01c07100420f5200c6030618001103108458000030f41044203c207005e640103d0082241c042010303062050307000d07a01001c0d020b07074130380726000c005034901d40707642100c070b09511004581d09000c3d28000d1290044482c001400d456145a007404002031042003620b400d200d0580c05000504c40a030102001c50070b444280e0014501185014204005010648090002c2020210700c2406444180c02001410490343d252005880d00f01340e100040085461660740c17003075050440f8003001c0f500c0202120898500b2010580c04094204400da04034400007600640500c000900703144980e81c002c000d040b80640c2640c1e44050f05a0383d68044a9030340081c00041d6200e03490 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 728767122 1250 728765872 728765927
    0xf01051507021e0a03020303030a060509011202030c090c0d0e24010303081305030708040611010b041a010503040203120c100c023405040f02041805010f05091e0403120b01 75
    0x190f90281d00c944000802103160703542c4907808242036030800d8460341d031100e440b20b6080c4954945254010b0250800c42e5480c0013480381c540000b6516002c00540a0217000b028000c40e80e40311090041b04d1400b410b07600144160125480c2d1555039980040d102850380b422000c0c0c080400c840e1004c0d040c100c0f034150351074588039112400403902315480d24004a68600c010845070700003a110401510041c00c940d141d100d0001c107880d09503804c1d10072040c0a244210b00c0c10040496441c031a50050700f65103000e28020340c40c0d988030b1001c01c0c86c019550170b0402011030301240c04102045d00144c803124414003081c0622038460009001e980c2c1e143da692270400c98061405031015110145940340c2e00080c0400301980f082031792200858112018a25403030060b5070000f400340842c2c2c40304d10b81d009480d0840074003004550715103000780c480d4503010301500303215000031404240e41c8925410b02c440c0110b44140d0442e0241882d01d000f51802d003c00102c0c0b1511414024014a15030040344105085586c800703500c05c4807542d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 728768372 1250 728767122 728767159
    0x60b070206190e190512070b031503010f060b07171215042c07060e0d060c02033601030905150603150405011406190308030604020f030f0105150702 65
    0x1400c0c0e258404200b11485a020075075144d01c1001032002580305400b061034109014003890750356009100c01703550300483c42009241c0181382103076404440c0c412000d40d40084200028054460340d02001085810100c010071000d94890040c045c0320704c55403000508190321000340320280a4111203100840415001401c20078120714100441030004000191180c40500b042c0d0703503803140401c40c840d00010705a007110003480c20040e040c041c0c14241840401c072144000098044948144000d08098030303080b4000c6518020801d5852020000706090b05280c6190301c0f03002010120210902054000b80041d01c0c00d50091043c030314019000800340c1490141c52141d0801c044015182d15054412030780a03c03001c0d02503500c4540928407960000c00c075800c0c09042e0b080e1030b66004c2c0500d4071a840c10310b591254405804a07107821660320408071600c95445400140083c02a403540c502854800020005800740203503c0d541a544103c0b81c0a0001c100700d48450924010b620009400044145a0403a03075070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 728769622 1250 728768372 728768407
    0x5180f0327090406050103050c030316110103021b0c10090e06010809070801091109010504050112030c080f1b060a0b0a0b07060b04020a080f010e04020a182c01060b070206 75
    0x5404012698101c00c1200400c072520401c8605494a40e0740b20010b004004050081114a0307608500075400d100d65a0240d03001d00383c4000c8021724540706048120b1031039010360107960041c0005402e414107042da004800340c640e100b100359548640e4000580c40c08043c05002d8030800d9425104c0515001e40c0c0705401560388032405030004010f80700f21080001e94080c240a02c1107002e1150384280c1000c42d000e81842551503060304102c0c4110b04000060118281403810b0610550f010310b415204101030b814003200f103204090004003894000569600c88482044000e0b451151640450f81c00b981da181d140021200c4000d24507a200b6400b400c204903056506005d40010790040000081e440308040026003241e02551468022a4800c0e0410946042441c1418010440990b80580614081d40040c069a030b00e4000e507041c2c4841c100c003442c01e60065038414500b490807405080c2002c0d940789c04660072110481043c5504e90300302900810301c05050020348103195400750a01d8200150b0f01c0301d0710003e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 728770872 1250 728769622 728769667
    0xe0102011104171c030f060b09010c031805151b070b0901030f020f0310030c080c030c04091a0f0a060b34061401141009090e070302040e0105180f03 65
    0x18030130007071508030001c0c00c0401410140381e02d840004144854035648000c0d6100d03a400201c1c034644c1840481d8942e40c00c078040c1901250b0500d065481c03220729280301241d0340301d10340100e50081250180b2042c1c1c1842003005202d220740c0705100c5400854400c070a25580d03100f42c0103102c401c0e03000344140c0109500940190600810310381000d81851410240032003507400c21a10050410044c2801f003043c801d040310100003034070f402e10180502d620390401003075a0300b0403900018000c0c3c3d61502c000782400303011584411031040c01c0459a00310301b0517000ca0417003105c041d600c0c41041c601d040c60005416003110119403000f21f8915010700c0641070620482c10305450980d15924400300030034580001003452041d900c40d030582046c04211941081600242c0c1c041401402d40103800b03030745103502040d07009141401220b140300008540c20003180d43c594101282c5910007900581400645410b41030190403041c07250400c00042030700c8070240a92103543d000e06502d50040e980080120310301c078556004509540d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 728772122 1250 728770872 728770919
    0x903080a111515030f030a05070c0806070807030507110c040531030915080a09080c1005180d050a08060307030f0609110105030c0a0305090c030d0c030e0102011104 72
    0x440007040080340c18518500000d1a0281039901005040001480c140398401800d4004041e5450700b41980c6542c3d201300d812000c00d008021030700c60200030204007554060404036090340c0c01c034100f1800103043c020007960703102d0101341851b00050b6150f02c2401c64802e0417000800500b0310345a601e0a00005003009010703101c0e821814115030100000100e62004914000e1417485507285890600070400915a00200a100750900e010a00d0ba64003144464119910b07000c0001d2000842c64000000d124107858001a4000c060300650010256808507107da44568404010391620380b281c241c441e009541300780d003c01c82c24400000001e11881803d0362003000a03080322081a103a4803081c40c4451f00440845030162100020410006c1000300150030a000307081080c01d5040884584145000f000b40420416980b80700148a2a40070030041d020380e040503054803207512900e00c2c020100841e07100168081101d554921131254414800c1c00022025000480d04003800c081e9221003c01e9100d103030707040c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 728773372 1250 728772122 728772137
    0xc2104080c01052e052818060503101107080a0306120804080f0a02030304050409030903020d05280c050d081e0c0706030b152109010b09090d0903080a 66
    0x5072800709104a5018010b000894008140140b041100c400312114030480300200303c98042100707485160030382d400c2210f2040944544103011301e000311403e04d05d5111401c0c058000344180c0940041340e01c02e1060b0f941c1a0143c0d00b14031641c0002c1c400b42d548820461403503180c2044030303002140440d0094810321a5925002c10350b559285004a2482c22025064810190020b0108440f20381000140c0d14840100003034071118043e074001075203038000d520859004903240c2800401b01481004254051070703008000c50840c408a04101e50f0310b1381d16400d10384881051101c0000a1040c961440308013980c04456500f031030b800e1105004502d41210801c43d1520000d2100720400058900c001041300840038600740c03941d02602c0721034a00161a80f1410500d480c3c41030b1600c42c0d40783c6030107400d40f59200d41c80c11603441c00032400036101e0503580807141807460701039000d206419006400209000d881242c92044035190480b034203494401c0f4200c42c07804130b00c2031002000000e0000b00507020307450480c00c0068 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 728774622 1250 728773372 728773387
    0x220f05070303030b0907080f0f1005060301081b1c0f0602070f0b04021c03090b0306010203090604060c020f0a1d09161214030a08130f0210050a080c210408 68
    0x618000d040d07001140841e4540040c1540e50404c1c2d582d0f168010040c0c40c29180c242455400d0202c90308002e00340060010101300007034498400d030100003000b400c000c0c08407550782d0707941c4507100d4803044c05080034802d04a04107803258203441d0500030b00d001007060400c3c0c0140003a40d80d8900d00f040c1c1c030703205044031565024082c10000c5107030b0303416081813140202404003084c0fa0510400c0340b00165202c0300c3c0002100754140c10082544606403c0070341d070027580099034076200d001c0180d14500601c0c551070341c804800600407440c2da80c443e800f00e8495100f030340c0e070744c601c0c071805420084024464003481505d0391005050404507108041020303001410300050340d000c40c05c4095951285850358001c0c0219115848801c0100011200b800c2009250403018606100d5040320082c00220050f040585984501c01000309200c0d540c0d5040340140c0d03006003041901e1200d040c025201d41c12011484002c00d5501c00012180c9080208640c1019200584480c11503044204401a108041e000b80c1d0102c1c1d0511184 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 728775872 1250 728774622 728774633
    0x60c0c090507031d061306021b0313030312020f0f07061d1f0504020603130804080106150f02121e070206030a02070506070c0c170f060a02030105041103220f 69
    0x100c1c040c07102c5640210300c84107415101203480034a404003840e103070311030000c204001c25005001001e072940070901623681c0143c5d0f0a040a03120810144903082d000000321080700c018210004411a442612841900300740425100224068400e03030020300501004201114000c0000520314035208130400240403001c0401c0d101403407800301c90b0041681c466039240c40c41044e14102074040d8490b80c0310501061400b68081000c2d07020280000100325051640041001f0114054501900d6007200030452240e441d604051000c4507065038101080414281d80451031000c2600d61903803c040c0369040c5020314404c000510100044002606840140000c000580d580e030001c50084560000158440c042401c0c1141046c001030206401e20a00401da01c0006481031178442c1144d00d404040304a0005517941ea505000d10b10141e41c840d070043c1d90810450182c01d80c05541030f1181942d0030050b00b00c242003580322030f10060b6217039081c4480c2107040c1101c0c010040f02c5c4400062245c0e41030a074000c078a5403103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 728776978 1106 728775872 728775881
    0x3060909170306031e0604021806031216020d05010b040506010518090c1620040905070902091807050717070b060409060b0d030e0307060305090601060c0c09 69
    0x43d041d0364180b02d20094034124400e0100041c0c4403220b881d40f00d19044808130700c500d240008034020050015119841688060018a02d41c00c480000d268142c1002441907001c4003500b4500c00143c56007903101c082d041c810b5001003150700801c1c080009a8400034a090304210701071040100d80078200c0d100240b4201c0684040c0b8040c0c803940300c400454410302000c00e0701e01c000d04214100700210003c01602105000110140c01c0c0004010401500c0045101500c1903000746000d1041401359030003800024401040700b0985080b28050205446c002c8982c2004500045144800d0022403105070000c2451642400d1405066942d507404003640588418042e81d620f4141004000b010b501600d038015005200411070b11403031400920710090b60410a0081c05030100014034140240111030103160014003501d1a60f0070440c003102d9440051780152400e6100d400002003540d018402e = true := by decide +kernel

theorem cover : BRFrame.Cov 728597122 728776978 := by
  have h0 := BRFrame.cov_init 728597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 728597122 ≤ n) (h2 : n < 728776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
