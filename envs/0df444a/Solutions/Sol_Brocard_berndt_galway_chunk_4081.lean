-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4081
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:30:51.257734+00:00
-- url     : https://prove2.me/submissions/58d3de53-8b96-41df-b947-9e5aeb4c797d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 733812949 ≤ n < 733992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 733814199 1250 733812949 733812967
    0x1b030e10020a2c27060103060501051608040b270102190204021315201f020d0b041d060109090b070507050a05100618050412050d0e030307082703040905060105 70
    0x360891003000240c124804c65594000e400201800081e111a040608040c4100305aa90050613254103880e5142400740d007408901c0d040e805480340d68400c070040e80010400f030104102201c5010300101e00d425504450303000d200012030311004002280c4428440c004000d80c05410642c2c041c05100c60200c0c21048000d84940954440060408002c400160019141c03080042d20041c0d00260250140c0148008a65059004241c0c0c4003d0408684141e0214611760500b01e1034012541c0b00c1d20140c400c00064950f0850060030a002502401292003140000503030014244503480305150440c0c4042102e0311540d50449856218904c21313609482205c0703002002c11010301c400c3c00d1441440900284040c60003200450fa500369000b0a00441e24003810000030071120b9403002c13050007140c60099520446421031170b0041c0010150000c4074400803003000401504494a58000e140802200c00e001e40c44140f0100b4103a428080700c086500148070800400e100340c0c101c180c1022050600c942010025 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 733815449 1250 733814199 733814209
    0xa150803030a0e0d020c03030f03071707020f15100b030405151005101d190909050606040e0a030f0516050f06040213020406080f0603011b030e10020a2c 67
    0x2e81c2c01c0941155920a50f0752510003c001d0440c16590500207001c40c48000390020f610307405000c031041c0c0b08900010000741118810380c0845044c0c030b44502290090b00304541c0003961600008040c01036031141194184c95290403c022510a803003511501c0030359820030400000c1a00b014004441510800203100e00c408010900c1078800e20041b0003600322280f03000100030800645c581c2e2202130200d0200801000600444841c014060079651f0f4207000ea01018883c180000652252490501c1c00e01640c0412002082c114010007040f6410302c05261403103079860300c810711180e00501045815281e8001d80303014101410280d0303108031440395004410b440e6941025400c0c400c84507150003c004110441c540089200c81c03044c0500d50445c2014101480030300040c1020b408840c6005c2c1d158006803081d82c0035006000c01000403400100c0b0f000b05414058054111340000308401d014010801070007450034400d9403201e240543d144002c000915160303100c50340c034500c91645200c0388119840d42e15154 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 733816699 1250 733815449 733815451
    0x2823210405010b0406050406120b0402012303062419020313060c06060e060d06020313061b080a02180d0f06020f070c0e100e1005030636060a15080303 66
    0x508004036421100604100840b01070381c114a07c1213241ca6010700090524101980d840e40d8440030030300b2140c1b514001a200380305c00c002c11041c0d04241d2005013030480786c0c5101035400740c0026200b2105400d0f5400f03494040c82020300c029201c9030303014402034a44080c03603c1d0f46012401940145e0340351041100304c060100082d600040003103020000882e081007201c0c42502d001b48803980084505007000c000061403458200c2d03000c1c01040e00803000c5041d10104001802d90182d10150030005506440c0c030034280c09030b048201030041620701c400200308200b24000c0310058003222503d80c0c0d03000c503400d0030044d590b83d0110b01923900d2580d090014002600c1031004207800e150442040e6100c4200f8a44224801c01c1500403111806561050054122000c161001682d1561000345815035030311200c0c00c0c15415560000307030b03d0300c155000d00c2680040308412140710718012482891130407201c0c00c1007070805030100e02c11070b0036406a0009000400642c1c4030041807881c000341941e1040c1d0718580c0d80d00c0d50304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 733817949 1250 733816699 733816703
    0x70903080f0403030f03050910090203160f030201170f1b0d050406020408010c020109050706051b01060608010e0a0c090e06010203040b0c060108011d07030206031003020628232104 79
    0x200020244281600321540b246222420714042c047d52500e001529101c035044020b0b028050b495540032411980c01344143c0d05000854510100d00d07995070000400b800d95207101c2070b40410300a880385102e03894450b2142d445007440403905402a2074014085c1c183c0744841d0501c0d90b01880034891020300514a00442d400741e40a1400541c955003010206400c4401548941082d60b15020701d040000d40f010a55004580c0b040c00c2c12030701c079007160b0300401504200c099070002c82c0d40b9101d40402d00a41000031241030300e00303804014030944c1d02c1c40b8140b4211164a01c0d118007164260404110208840203250350001061042c0c905199490a81518a81141d10052840d820a00042c020102d09201d502d02460b0303840d4124003c81c186214003520388108d404080d001f00800030016820705456000e000003160b0180800c0d07030324030030900740841c9480300390000307800300e08a011030b850800e10030305d0b60311003040044c000919101c0446405c3d1019a10022856088481c00103180102c000030400306403143d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 733819199 1250 733817949 733817977
    0x2a06040309080601080c130216050a060207151e0b041820010c0b0a02160c0e04020a1a0406110106080a08120c031504180818040f060b03040201050307090308 69
    0x142046056410500d0580042c022076108140c221b0859403030101070840c1c039907000d000503030318600c00c103000310004400300015016209900c502d100f040308070f5006268141c02042c84501c0300c500705c0084429a4081450317a055090028403980d0860460b6004006010b8000d1000490601170301c58101304038107100d0182c41e140740341c640d14500c0e00b05030700d80169908803d18000009501599420320f40100c00380c0b0410600358082000e40c1e110f1948820000ca00313400901800e0080e0b0749100b1100d07103910407102240a6075500300c000a05002001c180c04182020304544c40c1047d00b4500110303080d00c403031041c00c1100e40d00c035070300001c103603c003409411083c60141c07000030303031340c4d07052410060074800058941001204100200a411520b0350641c584000049501140f074a0503060821110a1619005801c1500001347d035105213140c1c0d09452081c9600366000e004d0903200c800107070f08442040c400c03264041820070000f801503100307000840e40007000e824014112500c90b1100c03852500316100c6108a1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 733820449 1250 733819199 733819217
    0x130204090f0209061605100603120e030115120f06020d0204150f1e110d080117030f0d1e0626011a19052d152a060403 52
    0x14049074007500403072010152056107440b0008002c5403241c031904a44420030600c80050394100a0103100c826541c401c000b0040c01245d446c0c1c01c01c901003640c1300c0320240208182c6609c0003001e0030f043c010030082840e410010260319244c003060b0307000c140e80030390111156604445544002001e501c05060741c07040036000107171224188100302c9902c4042d00310200601c0b0032801c048011a5004c2c0d04818814034040703d0103c0300341d044005481c440810321700d05c7c4040c0078141540f8a07050f40a040f04d4100c0d00d4003260f111410300d0524420344c40b0b10604070480380040c020081d041300c020641d04210700f18005000105080072880300c043c41122465000340465041030b4000c0d4400048420451520301c681c03500800c01e202103800040704440c81100c000c0d0040281d8200a0102324141400e60010318000d02894080380c000b04400c054107000d0b800408030305952044454860608213008000355142000d000d15040712007401d416013041d1601514220720030150100c030b4440051000c1c034041c51181d1165802 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 733821699 1250 733820449 733820459
    0xd0f0e1006050d081c0b04090506190c0215130c0303020c130b0607030e03011b080603010c02010b06031819030512070206090c0f15070302160f060c030e0f130204 71
    0x3038541c140d00041c8a00240c0e44200d010840440840c0d150311310a801d121000b8001035a041c01820144050319800761528810300c06102c0d0104529104142e14410300c0d140d56080610f100c2101d08507801e02c4010381c004039a054149401000703440c2c1142000300030704000d4100d656444021005d41e001140103801003c8889042e0818080c00c8540303181498081c003608c4250300101ea820701604001408000e0104000e0203203890079070045032885041100c603c0d20f020b000030042c1c51040c0070341e0003038020f40c605180c41c60b6446c8180300c0d001c06400010310301e074595202c041c2c003070b1401e900d10b808480c058016808030b189039010014454001d140f01c2d0711140e482e0308035000700c00c00f8400c0c001c000c0307002c0d50410020804d6031240413900c8080d8480844103604e01c000c04e030001c9200746894112400200e0b0000841d0300c02e15800080c0300104001c4040d0140e681c0d030f1500e4500c424a211445144046440d9442c0c420001c0d005000e10164220040d10803001e03c208100050b0380a07251003011062550b000a003881 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 733822949 1250 733821699 733821701
    0x51005011d090c0a0207080c061213021e0f040204291c0e0c0306070f030207050c03071707090c0206061002010e101b020c0f0904080f070803010e06030c0a0b0d0f0e10 73
    0x3001f4a480000b805c000d4480c0004900c7d5445080c14070784e0051480b8002495010361424888038858000d000094007034445258403003040c2d422141c0600c681840d40182c0b98a1409008a50030b413610b10b040c1c076850300c189180e2a0003d00100e400e0b059007420900210702d080208508018002403948804500210b54504c0039040031320701600d49000350800001c001841d60030400c40d10110001c1e1034010780d01e5400d07080141c10041808041a03042c001c40d0f03400605100486040c8000c01110380580320060b55440c850b1040b50402200c40004da08503e0000f001c0d4a0300d140c42001d049890300010a00355003919019040170200d042d0f100e04103503108045e011900d8242c9011400c10b54074002005000c2d601170000b10b02c141102c880c1441481440c0c00641000a88003d403a05d08018604c1c0035155001898881a0b5810900500c00c1c007a4001001400034500015611081d1001074407403180c580c201401002164080201560010f071210b288040e0300e41c540c0700d51001c03c04101d029100c42c1c3d00440c13800c1c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 733824199 1250 733822949 733822963
    0x37230c070f171e070810050f09150411010c1a0708100f150504030b01170111091018080304060c050d02030309100203150a2601051005011d090c0a02 65
    0x640e651014001d000044006580b08075a003842c4040c0283c44401d1140070b1505480d500890185c1c02034000500821030f00e40c204c4e90240580403101440c50b40d59004150340e0b1005404030740b41000540d404100416201900c02406071418902913109403401d4480102c001c03050019806410b60603400c0182c8150700800240e000a01001c6501c001c2d40786c40700c0d004125606004103007444003081e072000c15003400740e81118011944880c40d80855a034a401540c0c480c8000d4100c040c495003841042c00f29050714608031501d40d84000c0c18080c0d540c010200449260350104070345588200400d40100b0403000400150005000b207640e00380c0810700d00c0c5004c43c1000104841141950303c20300c00d2011040f004141101000084100181c4984ea034440000195110006058100342c01c203201041655980d80500c03411701111300e0003003180c42000c13141402c841003100c1e0300500306000c0c83c060184d50301ca9601a2218070341516003802044112001442000054440d1100b904001411189840d010f100503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 733825449 1250 733824199 733824209
    0x3140f0f16020714030a060510030606050906010f120b03030409091109040302060103030c030e1504150215010506070c05041103010f0605191119050337230c070f 71
    0x159074221981c1c00a995411180510003110410002c0111941c03020409050003d4015606000da81801d82003040040c0300c0d400103584c85400c02c540882c0c1800c10349025409104180c9d20f041405101000455441e03142d00c8000b14400e484041d1741c200c46d5020405000a8260b413200020224158034022520985154503540282c41c800c0030000841d4000c19038504480e0181800e0301240c41d14541103800b064120300d01a404020051940da001c44640040c0045d10050020001c0e040024441649c0d50031200404c01e01403155140140103a00f4104090504140b18a030020041398440f0005010f403141c1c24140c0941c1500803004010068420380d201e0010549070a24500e000600186c40351200c1c0c1c441010b40a10107440860810041c0402c006512b000450021400008030f9260080c1c980d40b103000d0320307131070701c035110042c1c40c036101442642e1100140c41410342100d2001c50a030030703a1050b40040409a20054080c60395800403000c1d80140f283c0520100074141413418800100d1040030103400ca = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 733826699 1250 733825449 733825471
    0x60e0109063806161a041505102903041109070c050309100c050d0c03032706150f0f09050a050411120f010221130305070602090103140f0f 61
    0x320b014003000307409682040c440b040d280c0c25581c1c4002021010700302140310000b40202100303200400032450201d2414000c51003210400c24899406c80c02c1c0c82a40c41c19924142031451848d410411108611507610b00344003018142c0700342080071080490b00780c204a5080d51103c03061101021035260104103103034004171a04001d6000d40d0261550340d42c0340600346109000d4107030851086c090034003a1140c4a0900c0c2e2000840d03201c0b4203202c80007800a0011401180403900706403042c1007040c1049150038481c0d042c038142140c0900745440380c00c00b81c400480f00c0c04805044240114859038000e0304803001e402031a0390782c0f04203464101098110785004002d00d21051130541888009400d0784807800c24a0400c84103440401840780600d4248ce50290300b403182c0b9072001a541428501b0b1000521080034a25400c41190740d54031450311075011150001000260100b081c1d00028080d40d0240c00019018540013071100c03000e003103d01c00e25030182d907031804000380d520030094619840094581d00c0055420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 733827949 1250 733826699 733826771
    0x18050612070305101e0f0f1b020a03031a03010e0706170f010311040b0301180501050c070506010b0f190c02032103010b0a020f0a1103060a020408030d09060e010906 72
    0x103c0d1500c0d0b8440a03c0e101c149600c0c0c0c003020042c4401e40c0b011200ea10100b50b420049125004803000080441d042100b00003800c04810903104012003000a14035190f98000d0041d0356044e9500f00c0c000c00d01668001c0c000403803041c0780201c82e02c003441070300303825610900144042401c2c12000b03007056802900c1a141c82965004100304c6c00030304503803141100d41c044a100041035140b0001009031000581694144d0b203800e5030408000c1030352050000355030043c4000c01c00741e1141003c060b036511801d480031b40694403c1c00100078900c1d01d00010683c95a90944660074242c001110039400040313803503180b00103441003031081c0070b6140a11840d00c03c0c80c40000704041c0d42d40b20002c00c3d06a404144036200c180e0300c0105040040d43e009009460b4145c4462054400c030301aa460304070070036581010b40501a1080100003201c000040c030848064401d40b100940c2000c401c1020000646000700c03040300c0c026100d00c205940c28209010f900b40292064502292000303c8458202d4203c0750000109201c15044c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 733829199 1250 733827949 733827953
    0xc0b03010f0b1e0c01140703050a14010311010804020d050a0308100e04030e04020a0201090204060e04050f0f030d18050a03020c150f030a1112010b1c0b011710180506120703 76
    0x1002d0100041d0038102a1074444c258191000e00414600c00700040c1103100c0d00c10040502d6059002c80e20940044c4400c1000000c03038131018090b44401d00008001d1a2044644c1301c0030741c00383c42d1081d4000e200420200c21075000da601c83e41080320000046000c603d002003400000c109050381d07040034080201c0c005800b40307819100100702460810400740210f60020f01a02c0341e6100b9041815210b1b000b034001d00071a965041d512501710000c40e01a20310b8010800740400050300460f296080050210042d814060030516450041c0101c444904840a040d0900c0c00080d001f4880c0340b4126003c0e4025080c0c003070f240130a001c210100740788895200340d01042604248100241600e81100c18aa0009808400078601508510981160640300e114880c000a58011040020400d103e0048910110012a03c3c414001d58607054140f1f40407131442c0890f5a40301691240c242da001c0c030b280010740900c5994604001c4040e2680f80190f84207502d5208100d01800e0800ca441000c40c44c1d140200441e901d96 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 733830449 1250 733829199 733829227
    0x105090a150e0412030c020a03140c010e070e0a02070b180a0209070c060c020705180a0207081209070b030606031503150a0603030216080303070503100f141f1b06090c0b03010f0b 78
    0x105008080c00030001010589502060594806148241c000c0103a482c80c02c4002d50760b0041f60fc1800c040f01c0d41980010500803050007a280302c5580f11694540355151030000c810224403440e84850f140c0300d981e2010000d07955008589000c1d039a503480e159400702141c00e1250a0b503004550b16415548031220810180c1c450951000310746d840701606a0650322a01204c41c007034841c40c64040d20280e40030032000610010900a140559a8002200d03c03290307890710b0100440c001154110742c0a581071000502c100080d140d148859500203007650501880643c00c1e9400003025a601d01e4001e03900e4005004240d010003154046c80030252290f0482e600c2d00c0403c81d03513480000c2000d0200800400886c20300c40b00414164003604a12103440d810548400c03d0302c610103000f2202601c11410302e0200e2030b921314200705000d0714a90039901c0e01590060007102d000c0720700061703508807503595544020310301180c000c1c84a60041d0032141180c82c0da80d4982402e11225080503004070007010702c01c00402d8440d00d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 733831699 1250 733830449 733830463
    0x9021812030d020901020703080c01050106080f04030c030c02041508010f0b0103090803070309140106080d030c03181e020a030b090c030d0e1504032a0f05090105090a150e0412030c02 80
    0x610b03000582e684201d840102c4c1000070326403009003040c1d4007007805030800c80190080c9050710b0310340d601c0703441d56603443d81c0401c2d640d2000d07900034011840c04609a80480d10602c0f40b4030316180003030400b281c506074084201c2d0005030070390b1010003240d540f0702d20034496500074051092140b41c2443d013030007444003c1e100c608003880098020014165aa00460208921b1003a001184403810000308241d540d5001c0e2a41c6603400c0300401e000180c40c2062030880e0900034411030324541312041007604240d141d0323528034054a601032040c000d001e00d80c0d000c0f00c00517951608010082c40c411803000c0c0d400d0609640a9292075034056036244a40c0000c8c03500351401e684030b10405203c8004660780d1801c2d1200d0a182c032414810381d0000b40800c04503c4d4800c0e00e091a0540c0c01069000040c0001c203000d9480301c1850802009000701c59001b07500d900100914a80700c001c03560401c0e00a48002030741440c4060000844915500100666610204110900c481407800c00d0018440341010700422801c00c000039101c1c18 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 733832949 1250 733831699 733831717
    0x1a13031407020301061d0a05010f180515060a021606050c1519020a08040506010506030c04090e24011a13090c0207050433050d02060c03130902181203 66
    0x10000c074659080d950f003500004000c00c00059500d00c1108440b011070742140c42200c044146a007000700002d17000c2d8800c80140211200400c01d54540f640724078890b03000d8500504103c0180f618000c00265550b1031174000d0100c12290340050070b1041724010b0642412200d40d0102c001d100091245007034424021510304080c80b12100410141e9a030303820f02d03e601c0602c3c1149002d000784049070390000c8541264286000b01c0c021400c1700c5150f03030b8590070041c8502c02201c010030070038401e200421500300c4035003200c2d8170040700200ba00c0c2e10b2400004980c84081100c06507004080303500b8010030001c2081040c1e5400780c42d10b079042c10302c1c1030001c0860768041c8501d481003481d01c582d507540410740c2070310a02090001c0c0600500038401a00040c401c94466a10040850401e8400d02c604640040e1540313142c2040300c0c0c029000d40d03041c1c1010340030808240c124000701c2119003c20001000c4580c4084100c001802003058016200e818410240000c071110301412030040203600c00c0314a02c94400800d88000d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 733834199 1250 733832949 733832987
    0x20f070b0c071203030207080708090f090402010519020f060c040e0c12040f08091f17090a1202120307081b21090c130902042a030510121a1303 63
    0x202c05131030201e001340304000010301403102c0801c00d48200074100c1c0080440c03103000c58165030209414070400600000c1500e00a0105404200510104802c0202e0800d6200107006030303061404070b40c201c281080811140c5414403d0001000e00076800c684c6d60142d004202c203422241021002c80740003142440140010300b4100d0380640d00c1040002c210120780b40044050812501100d4040c40d24060054011102e0003181b0700000440c0f9120f25090214482c003009402000403101946806d4101c041131880c0c00c045008035428110a0980759004500860740e590780e2904501d0803c5200703105454031180000c2c1c090042268201016025802042d04440140b020304552501e103100e500d81080d61291541000d10041d200c10407054580c4000308880c02514180000c004054240001d0302507556121111382c0c0d03401e0744540e058800d61007070b0750203101c0003160104581c0b211103880140310002030407661119242200c4001803220041184c020121001e01d0018400ca0340c0c0c050503000700002850b04203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 733835449 1250 733834199 733834229
    0xd140f1507141b0604050c01030911060901031503030809150103030f03050a1d06060a09020a050a0302030910110306030f010b0a0b1e070812010f03111905030706020f070b0c07 77
    0x5071901d00308407000524921030240f51406664140c5466407001c403415601c030b0013441080b1b5659400f900a45c9400b59004805a2030002c2c44070402401d80c008941941c100750b80c80e20302c1001c1e00b1040740c0c1c0e0703009580641c40782505860501038080c5400103880c09040114001401007000035009401c00c40005914180800d10340d0b9488050f20080c910b507880c01c43d1089940040d150b20100c0480c441e8001c0718107845c540f60b02501e0f448818144d02c00d15022034000b40040200c3c6a00620907030195400c18101c0c019200807425010240041c1d9074030b10324141031000d0000c140f04107131500b0800443c060b805100207001c403102c2d0740c001902c4040d45110f40c07042c3c000001515200c40544222484034850158515a110f40c07280c200b1800700d410030403000c14071400d40c1d8000b080c00501c07141150101e03603010018a005100c00c605100c10307494200c918090000928030086001d80d014000e980140200d54010302c82c2c051040c01c4a0b24004280d0721500442d2400c11240b03142c820013146040039a600c0320cc0b8181c00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 733836699 1250 733835449 733835477
    0x2105041103070f090b0f03060c0307090b0d05010e06011e05210c0403022803110319061a0a120b0c0c0111090405070f080a0b0f0d140f1507 61
    0x35840d40001401d6142c019040d000c940800051030503000c0c3c0d01103540c20421070514001303200d030a03401c21710b110f1351542c0300e42d00040c88912044000e5510280c28034080e842241e4030b040b241240d401c900b10000d44030b62298014080800c0240c40c00b58450024a0100d10700d000c01d42044481030f0203506000d081000018084224050700e858096144244603030590040c90640410135843d007040c08124403440407000151041081e817590b82c5696608004840c03c0d00d451555120003a40d044400c641d054026070350001c01540c902088006c070316003c0c14000c60014406810790000841c0210130b10700c00c500112080c00940f610030040e805803503003c14840d20310745400010f9486800380f01c012008030340c285a80d1030b42201500740503050002003a18103201d1a00c0e6000d05940c401c6140c1603010000358918002054030318943c110349003005006e403644161810140c041110014801c0c03050b1405e03104082500e1410608002038030740b800f13207003024040140541200c40e0a2140140400d004c0101d10b52500d11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 733837949 1250 733836699 733836713
    0x1171005062a01051501080c040603051305030a080105122103150d051c0327030306050a060512070c02010f0f14030403020d02100e2a0603010b0c010c210504 69
    0x5408882c21000307000201201c0780c1c0d14042d080c12a401d07a42c008070046103240650040381d00798020f407a0200d8480c00c19007040c0d02100200f0000b48a03a00300390842c1d1403800890b6060000b04031850302552503030302a60501080c021007136a1502c80c40940c0c1d21807001080009814a00c00f80c40e814864551070f03594a50015130441c080c50f45600b181d205092100c032a04002d0002050031300884849280341c105481000b00303404507044080d000144005909140600400e2426454122407281c18005901a01c44005c5062508103810081c04640c00183c100c02c2003500d18107281e400f00481ca00f0141540300f03a40000d00601740f81810805002400d204110020b01540d8140c492006200403140c99203018180255a80100d0010380027500454001c42c0140d82c0c140204084800460010308000c0008280e02810718140802141c004015000103e8255960780086000300014810740e521a032400103103d08640b402001c54050250b10407445581d10701c810b501d500d9007012080b000440342d81d0b40c1041c0c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 733839199 1250 733837949 733837987
    0x101104080601180f02030402092802030c090301150614160b0421140a0f050f04060c050613030c02040e011803050d110309060115111005060117100506 66
    0x12014060314001083d204200e0080f40d501411804091044203840c515000881c030050760060341100c00300d070010f0301144c49a81a407141c1503192a4081030720881e80c00d08002c0380c00c19101020441000a0001f035649000d00130410b0f60820883c0e5003076554079041000e4500307901242480d09021000c81c00385c1c01039483c010540e0146401c411104030529051400780d003c00780c030400145188808208807600340e0b1081e03256102d12711100c48a10303e0412128829500c0511f10b040043c204542002a004040c58a0700038000911141e1034448030f0b00316074503141c0d0914400418203040a0700d00745c81c0c03601095210005911302c41d01902e0000d056001040820701600d01502a822440641d806e04c0e000c16920030000d256103520100304010498403203120001c188400d131000082940710708014080c10800c000005541d052074202449102c500411007414400300c02d900c3c05605949000304030f45941c1010b4020f60011035407000781c90514200000b0454440503010361805810301003180080104079460300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 733840449 1250 733839199 733839209
    0x1305091e09070501031b08042a0e061f0c0f02060903010c09051504080a11040b0d080406030b010e1c032705040e0303040309171903020114010611101104 67
    0x6804103140c0744044503994032480c0b207098000381c0b9003001e880165807440f1000012400b55614600e5a8071217447d000e00058150825104400e203480056040b2030001d6800310040110060341e000901d040c000304403900c0d03500702e014030b41084030314400350701d0543c0701c1d29640c1001e5100102010300e100c00d0010924601890b402203401d90318114120303011603040710381348003299811070740882071005003406007003140182e01c41c107003580d4001c01652000030441094002c1c06840504000740c250b06410000b0211032100200b43e070380c124001000d01005516001d0b0000000003801c080460b04140400b0548501050720010003041c2c0c41c00d031103001c1511446c80951402c0304262500014488030386521180c058921034544103501d48040b00c0700760075002c01aa441142c140c2c8549078075a00e032a04008014400403d200406e001d07000d6140d150308000d031032441441c0c1c001ea00014400d085416a4212850183c02400900c03001d0541c1c810300c51030000d480994400c4090000c1440c0840c0c0c03000e070b043e034042d41e000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 733841699 1250 733840449 733840501
    0x703121809050907080c13020708190f020f120f0a180f0918080f03130609060b0f03060108060106050d150602010c0206070503010f060f020c030f0d090605130509 71
    0x14160049400c8140034041c00c40642c1c20b44d40d55503243c1640e42c1d00304001c00b034009901908a1810052580c042c000f51400307501a6031600944d03440c1c4460300204101d51001107140d120b40200c005504004084118021100078580810a8103060449008804d111b8650f880d00241e19030480380b03c2d8040c11803441008400103441d0380c403803501caa102c10550140341c00c200d01d0703d11940060310800140b044800e0300071502601d4014070091101040d4402040400b00d02c2e210300c3d107040003c07800d2040d19000f50043d03000240320710b1024200702d1030b0000d44c203c943c82a803226005011464000c525170341151000e0070981c0c1d6980951080b10082c00c3c0c11044007081c0300c1055800038426030190405400740f07205038283c500d240d03100d800950303141c0002e000c4d50224484600c03051001d6030203581004296800381c012030b81c000000c800024038002004104200c2600000301641682e508201007002806243c01e20034206840d00541301401c0801d8415140300e0300700103020542420000405500c50580c84030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 733842949 1250 733841699 733841747
    0x50a03020d060f060e0703150f120212060c071208041716170705210901031107061b09080c13110c0706020c090a060302100c081b0609190203070312 65
    0x20b2030031720030400b10303036a0300424284406581e60305851030b01c0009031200400070380d601038200603107241c04110b10360040780c01600051304015200c80400080c2d105514070b40c046652180c5d14903100c54020b0740461186c0c180601c2c1070034000000c01e588110214614040c2040c1c1d154140c010b80b031700500c4201030f809000017103d00078680c880350021008241450103a0220b170310b0200c0c03030122054401c000314140382040f01c0c140150358440d8443e400c0800d030811300c55585030a01142d51140c030200c3d032420380385a010801c0395000d0003219400a845500800d512130107440030300c030058003141c0c603640303100202068a6568a1080b4a081c0c03000196602e907000201110781d1582c86401c065038a818005d106031003421214002a58510306024500c280c035805840303090341e15200c01c0203642807850100c1c111400b10060041400320000f4000c1c01c0811a42c05004003c036080c90284c181c20941d4099506c6200e8a40d002100050785000440008036035110704100c07032002c00c00c501207554695022114429a008074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 733844199 1250 733842949 733842959
    0xe030d110309060f0108120a230c0d02060601090b03060409050d0c03080121030302160818190302101409040504030801152a030c020306070203040608010f050a03020d060f06 76
    0xd03502c0b0b0b010503000c44040d0313103544416503035000e800d00c5078210b264442a14407014008010150040100070308080c0c8617030b10702252407404807012050803e01481c01203500c510000701003000382401070310390001c1c2c559814490300007056400603000341c4000840010104078503844650046500d20740002c1030b24091080b800e002444401909021340c0021042000403501c403240c0c5001000c0000d54a629032030042c41a9016400ba4110103207201c203082d0032030005400709031510010410a20002e02110b0382a00501c20014107002c0c20680203080c6043c0241840140c41d01c0054400c000c0c045e00341040c401c0b540094100d4075124511420f600941030100740002c143d04040303843d0580b1b80e400302c4041e0f04500140100c681050b034a0300b1040100c1c184048181b443e00e03039611784003064060314040c8907041d8940c010030b160190686100005a00001c0c00700021984165224050208441e201c200e0f00c1c0b5202c00121810715501000c2c1c401c100000d0b0510070022194000302000c6202501840030941d29 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 733845449 1250 733844199 733844231
    0x303040f060315061d120c2110111206061606050406110a02060a051b030103050319050f071704120605070f051204080a03060810050405010c08060105030601030e030d 73
    0x854450301d05052084004201c2c4c0f409550600c040c03200c0d5100c4511103100b2081084021500300070040b0f4140105400d0103100c0c1c69040b4600a5100440c2844040d410420300d014513021540c5940b6801da40b5002007000b090140000302d4109005c20320701d41c07500303032200000180103100c3c6283c4103001d0065000440304220160b04098840c50240342d0411120002c80584140b911411030f10b0001078202c20002580313400319901c82c03074005c0b0340300d1411010b000c400070044402c1c0d8402c0c0c101b03441d203074408101041403106114084032034101c6840d00c282030407aa00c42260003030064001c014114802e012403024013074800c40c10307100282000107031444140d0080c144000284816103010002800c1d5520aa158a01913022220881c035134082a101950700c1c2c1e01ca030201e41d08003400364410192034010000c0d542504014030324101800b1349002503036080c0741c5449400c449003200f0b1802444900b80800ca5aa81c001080e00e80c410020300b0301113415003403190b40030300314441e041b140500d480c5850105400c40c554 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 733846699 1250 733845449 733845461
    0xc0b1305190311070e010608061201061d060f010903050d05160c14130510090e03091f0f14030f13080f1c0908090d03050903190209330303040f0603 65
    0x30f0701d010b0311681900c41080c200e048109014030f00108030740b50f0104881e8142802041e40c0314000c40c0001510740d441e42c010200500a4032941c070380d4001c841d000d000300c525059500b0003000200b401d0408100d8a980c0d180c40e01c60900c02051402d100700401c0c0e18490020664040c28180d5002d11516402916060840a010041800f41d030003041c0c0303902c00d880207500920401d4003400c11510100320403403912050f400a00842004500d4070300050042c40d0458a51307659641e8142ca4100303000d644000801e20090082130000c1107541000000000140340b5107000c2d0031039030401d11011600046035502c07804500713010004800200b24400c0010341000024550740036020900304202c4180e00b40440390f02503000e0311000c1202074a11881001885030a2500c800d100c0089403082c18240d0070050f412000a042840d5251446415606100341d81c0462400c07a01c000c4e4440307200c80d40d02031346c0c05030184a330941c101041204045c004034213a4000582d03508006480c0200713400a104014652903200060107010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 733847949 1250 733846699 733846727
    0x70f06030507110c0f03070e0c04050102100506100f180305031c1b030207020a08030a0806010f081014012c0a0e07020a1b0e090c100c0b13051903 64
    0x441c1c400402c036030034071480b40c01c5801c034281401001030300e89a504001d490320014a4555040c0300d10a0000303050420403600501c10000d4100c3d50b500c0303910b440006800c12114040348000240340004115180d6a031980841024025240c504d6000d084c0038801d41c0c20840d00e440404603120090000810070600000910110a4401d003200b02404c05c03140c00429542c1d41803421000c44810340c00c919201d482907000d09080c500092024000d41c1d81c810906046a010084400000b14854100002b5503042500945443e40a00e000c0a10f803a209000d00c02105150180d905510640d140703190650703211f86443c2c80812001c0d107030b0214403120740800b4007a80c5000789009004110880700014241d0710000758a02c50392260b00902010000390740d400107007901503024900c0044400401092907a803030402c40e803060007000d0040031810414003c0120b590100f800c184100302c0302c0c00320b041c00100100c0b1680c0d004516842060400c1c4183c0c6021420009140740c000d010080b00d01840003495032040e03410807010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 733849199 1250 733847949 733847951
    0xc01090615060905032512050f01050c0414090403020f10241a0d14090a03030605090121140604080406030c0e010f0c020111060c07020f0402070308190e070f0603 71
    0x20b95182000d46040c0028030820790f15400c0559082c0e0003082d030001450080001c3c07034850304101d468908403c074031701d00c40350151080d5003c17004545440400f44103060300152460145030419152401501c0824000c64141d809023170144007140405008020070741c00b0183c010181c070b80200300f00c01403100410320302d0b45031500001c0384004020f45240004032002900c280220081080d4404140303140d4551014110b0170a41e036a650b017013900106004246c2d8000c10100c4050310184040d400d009081c2e40ba10b400c1980309207140c0004206511000d50110707c00c001000d02001c82011a0030300310b50a05034200c10035580c0c000c10007004100301640c0000c0c01551900d80742000f0241141c10211000d58081c0750346030104040703e03c2381040c4c500590307071035410f284140f40c0303511800901130641d401c02e54140e07400c503a800004a065021458201120b4908200c00d440c11420320319161801012401c01502c070100082d0a10003010002c002a00244140c1b0364a0040b91411079a17106c0001c0c2c1c0720502d1040c0c00c006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 733850449 1250 733849199 733849241
    0xd150f0b12240108090a02060a09180c1b020103150e040b10080c1203190e040e030702060409021c020c06040b060d150c090f0906050a080a08030c0f0c010906 69
    0x8200c000810015541c41c1484602d00020600042d00c0582002d051005030380716810744400140d691100810a60200f9544e8211103883e012807081007454110b840140d11b41061103142040d5484081c00441c0300340c08402d04900044d07400180d000b4a030743e00c5c031003012242075000402c030341e0421400340b03028520540b02c440c0d03240c0d1007007030b17003000600700f03005134403554000311101c0d03e4510b00700407401034140004003507900d812455440e02c0d0303034224075140b4a800305180980030030451401d44503d04122582c807000d0351600d84981c4c0010558030907801a401140c0d80450180072030a170303e0034850810000041c046690f841d82c141c5a541c4d4410440b01200c036945454001180f031300705140011074059000c0441d00200325101000c101400300000c010003001640500090341800e08286640180307010140041c07d10300b0141800010801034000a80130b5008804540000704000c040780c0d8807a002085e00350712500f040c40410060b1203032a100b00b406600b0300000f501800800d500c8508809143d61143c055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 733851699 1250 733850449 733850461
    0x7061a01080c0403031d040203100806011a0417010b06030a021c11030703051f1413141302060f121501032007020d051203100503120d150f0b12 63
    0x800c141c101c48010000d032007444104002070240c1381d0314150400346c2601e60b100b0881000824100d030030881ea141c01044000104220404040c0300b6240500280d0401481e00c910560b0184024401c0703100d10040014032803035400c84404294000b049149004003210b9690501c808640040d4002c280b002101d0070b80074203c00a011907a216211490070008180c909640d5580d00a4008200051115414864801c41c410912000d0f03021100901034030300f601d5071005034420601000d125941150800d581c81c10176400180c4410b0000d5a91007280044480c0c0d0040304c52000c1100d9001304c05804440c210b0224030820342e01080d83e9620320440c041039064603502245d000440640322002c803075840000da01c203001c0385101c0b04007006000c1140050700c0b20840315080d9035281c0c035180d48e00d07441105030100841070204410601070218010b0008070000c15807140404801e4109200b00d07121f000302241d50341c001c0500e01417105800f900510340c64805c0c40c4416502c0d81007206651049000b460f03150b13000000220 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 733852949 1250 733851699 733851707
    0x207080c0a06120b1305011d0c030402030a080a0c0b010e0603010c020705011407020a120614011e1203030e0d05190212040e0c04150203040501090509090d2307061a01 73
    0x101e91030b6a85400c000011000264014103130080c1854024030003000542c1404c03414000c690007060340d0460038980d01c0d01e03a04020020760015080d089041400c04c02e00000d42d0700024100e00160f04034022a44e00d0307945a01c1901d03154243d101c01031017a140d40000045480c0030001482c81600160000e10180303070400360403602e0f82141d00625000c0f9001500c0c200441e0700b400e016024050ac06030503400180d8031102400484401004102d8400d61102e50f000e002c07201c8000035500514004c503429800344da20105d00d0b15012200c1c003030260078111514031207062621942040c00a1078541064900b200f0300c801c4001c060b45d1058000c02c034500d8240c3c0e080100325200040880c9030301030801e41181018200605d0084a250260aa0380b980300c00b40700220702060750144106420080f900110394692030400058910f004940c00704d07110310410410001c907200301041c18202402c07a0300c1c0c00550700c0c40c60554414028245081200031a101065400402c20b050b400410124800a0800d10408541c40112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 733854199 1250 733852949 733852969
    0x105030d1706060913020307140703020a080d2403020111160506090f2214040f02011817060912130e0408070602160605011e030b100906060207080c 65
    0x140080c050204045400030040000d0b42c1220005104603d0680480009650401010220b42c4c41030b03400024411043d400c1100744000d40c048545560501080d918041e4984e04e0511300030b003046400240c95040d040c800d601c40480e5603044801041d402400d42a9843d0340c0d06ca90200302d01060105510b64dc440400041001d510700c08190b2408140d82800c00303001181d00b00c50900340e00040b00c1c41600049036030324032443e220b03180d0001c4580b1060b441e00502800f6283c034035407144821118001030001180c1100209001507030203017080213459a05880ca084060303443e5015098a1011200e22240c544000c1983d5000d031904e8012212000118000d81700303a440350900e04e03c60320344981c0c0e00704242c08450380c00b00e600a0080d1120350a1640913117992041e640071070403074030f40d003018082d000080009a02c20940913103050440134101140340402e50100560b103010140c10340c9003a200060b071284c2c00407060406401c0003101400f20940d80c402c044d65455160086e00d885009590150101e400e0ad07080c06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 733855449 1250 733854199 733854223
    0x4020a0807110c031f1119090506031003031b080a050703081b090114040e041a0702070311120a062406051e0a02030c0d02061501140405040506130609060509010503 72
    0x1500c1c200301c0303607100300014162100401c0716003600c6d100120089070740d1202030800c0586454200c42610300b0803c00a00d0070701c1c6504858820041481485035441d0b030b8180e401d05496060601c2c141404800c203d0140c5040c2c1c5200c01002c4c030b0000108160000d0740309024242e494800e465440b0951035286115000c090510440e54080000340012000782d8410700110801042c0b1340546442d242c1c41d0021420981400c4034151118044102d01a505000c075070452a80201c0e24030203482d12500b556109584000c002d07201d54418020762420410a103400c0c050342d40c50f01d510000801129840c1034400760640c881c220b040e00c50450042c030000d0038030f01a03421036280c5d002c1c0c0039003e000e41c06180e14040b1a600141411b00861005200494056004101081c4050380360f400400311440c0001150021280080c400303410070001303030845d111203454201502d0649034200c030080b81c04c2e9034074000304074944c22550800703030303d80c0c20560000346000b803a50091046d40e4055402a04586c0c8803018141d444840d4402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 733856699 1250 733855449 733855453
    0xc030605030c0d020402090607060e0705102123040f060b2b063909030503070b060d0213020a1418040519090605060a170613030e04020a0807110c03 65
    0x3c01c0185040d6009060002c0c1c0200020704103851515403804560100c41e0026480c2d201301c8040c030091801004140c1c0020b400c1ca4400c00c8090000700341c0384004848004400c85c1b985445881820780001c00107000340558800740d901561826040201c05e0881010007500d100c0d01d0400316903500c1c20f010205150049110384091407008101c4514820105114404d4800300d5031045c005440c554001c05170180c5969400384100c2da07440c0d04042018001150a000c401e200e1205d408000140d00441030b50b1540742c0001d031032134580d5030b031302d01042c034142448030000c1d07011030f064005854000c25613002c1d14038419195240100d0f10141240101c840c40383c401d500c6030200c004000c803581440d00e40c000701e070f1242c01e560304003e01a0203101154155041c0503002c43e5090340780c1042005d50f0400000c18030044c0946a04403032400c40c002225511036201030441c0506c014902819018103015011840800c14003410855403601429801412608281e030941f00140c214441c140c086103002a01040414000b00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 733857949 1250 733856699 733856719
    0x203060603010b0708190807111603020d05160f0905070801050904060c0c080a0504140d080406080c070f03110129220510031e1a280c030605030c 64
    0x8212203944d00000003c50700b0640c10400c4411500301c03045003107403000c0ea6032204401401c101030064040700141030940e10f41c0e8002c0c1d40000f641200881103104698041d00c40c1c3c04840650700b40302d070410140d1403400313450030b8445d50001800036207444903404440714050100071039280e4a80444080c0000e10070b19034456608000320300030a4095200036187e8035142018584002540d0743c25525030070000b08440403c101080030020510358503184000d101d812900004002140d03551a0201e0083d402a07008000e4024009000140c3d00000c8030f4103640c00c2416201141103a01c1e00420503198511008415420318120341e01401150081c1000b05440740d1401280203002800e00c459022580c50b0203c50740110202e80022025500c03c036401120340301c600074191803c508181c2c040132091071114a1004120309203901003a820711381c002241074110415883e40d122089800c1e08814121407000f503010060104c09000019a440307907402004e0b60b01c00740401036072401056204e8076900702443c0c105250761 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 733859199 1250 733857949 733857959
    0x20a030e0118150c2a02030106060908070b070b0708060102150a0912020c030d0e06040e010e04060b010c030801150e0915010207120503040315110403080a1e020a11011e09150201020306060301 84
    0x401a000c00c141c000c2d0026294401741c0e000030782034604a50200340800c08007041802510410700114001c0c200d0600c00394a04174950b42e4034a86e0400051124081000c0c840c04110325a10a0108400e189424010301307034a420200224401060500c500301e0708402504180e503101d40c0046030751000160b006020b0000c04000400558180c1d84000100d0f60120080202040708540018064040c2000444030b2807103181c076150400494480314505070510092203141c1c0d00103540b0413880c074103540100704c85101c02c499006040e525070a8041c441d541c0000e5400401c00c07140c1100c2080c80c00c8000036400c6035445656880c82d01d0b81000f80c0d1b08007428070341042009001103092a103c200603104006c400007500d4540c440c00303000d15001500200e4005a00051812842d544a1110848284c80b1030004101c0c1e29016000f80d0b03940c200703003001808140e240355a151568019404200180c5005a03400100c41c082100140703601d01034090440c070b2040002c3e070350f480c480c414829248641c402611442c9184d00f06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 733860449 1250 733859199 733859237
    0x50c030a0509190302010608071202130e03070b0c0a020721080309030c0f070807060306152318031005270f01060902070b090c090109020a030e0118150c 67
    0x14400296840742045801c00f4090f410104030b051400381c0d00014080e800e01d1045070170180c00358822180d00814010520159842c40300c4010042d500344000100110448a044d041d80a8a000a40342c040350000b00071840c80244002e0290200980c26105290340701c24030503005d54901c62072581c10200c10518480021090300003190480400011641800801c1524503e0112140b403c0007060704090b0080116420421842e070244c021410188039160031b00d02c110b80c0e00702105c0b44a1041007143d40030780e003170034285110640d00d4000c0d10050750b940f000685503400b07090b62402e10003400381c810342d031075104880030512940c0d004070f07240d0000d10000f4448182c644240c070315155210307095008401c0881c1e1288024402d0030010060b0600145e29000745044c081c0c15054020404a01c0703802c585621401540c031001002c0c15141c5145006071211410b00d001c40007040c00b40100c1d07003d5841c0c03c01e9070300340007031071000030004620608009145d824042302c0035058401c04c404420200d800310521841e0100c030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 733861699 1250 733860449 733860451
    0x60d1d2a0d0212151302130c0509040908090102280b100902070506012102030a0803150d050106091b0f0806060f221203120207020a030f0302030a0f03050c030a05 71
    0x300500c1d44180000a800081c42c0342c1e00182c0300c501e1a80449214003200c40007104141c0d00a181c01031040800d06640c0100700c031b04980c000400d000c90b6490021800c060300501c10703610112000f8004100c3c000c5103142044407a404000540c1c00741c415801d11210010905001d805405422070402e80708810036610404c100101070226551140ca0100c00704607400d441c8041c1005900620044c0019458040026603204124413044145085041c201c00941c500180340706000b036010380d14503529550360008842c1c2482c0300c01c5442e8010f0107094080d0500005401440a40e1010300b820401202080c035401580102c1e041100c020a100c041031304020303070098400035840f500c044c00c4149864500940307c80564007078030f40741d000c50100c6500f02a0901c440040c43c4068038440710304d001188000e89002e400340044103034150055070005200000c5440307051842c0011603107c2c0409504551a260280d1240c102c50803000001d212405103820080c07017030080714092650044958a0758a400d6004805454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 733862949 1250 733861699 733861783
    0x30c03082805130209040b04061a09310b0406140112060e030d0501030f21050405210601060918050f061c0b090d170606041211060d1d 59
    0x10f11420000158694141071131185116150010141c58107283c10004c98100100740790b919807484a04102c1a1601c510880c2c1110f4900c9041d0950f10302c600c172086200301d00b17401c14401d01d02c48007080c01c00c0000864000b0b00481c49980144022044400341800404091203214280b01303c4000060109150381d203c41101e811000689152a80380002003041d907100703910444205c8a10301c520f07002d02401c10800030204055200841e003180034204010824051401084c1c440c24052403102c07201c80c860711140c030380d13101c4031020b648156944080181201d03100c0c1c420317044400100d0102001462a900c10b880c401c42c04a0744814840d2203980078048154480300e01101001054581c43d00418003690034248130303103811002000304a0901e0b03002000c81c2c0810740318070b01c620140c8082c04801d03504c0c0c1040e103094885901600c8004403050401030402800410780d682c00038400a49103151500c2900704c801a000030610f40c0d03882e080e4507802e2070740d14540c0304554220032011a07614041100501c0b000c080c0f01c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 733864199 1250 733862949 733862971
    0xf0503040302240108100b01051b07150e0312090d030e130603060501141903031b0803010b03040c0e07020c041d031206011e0905010f031404030c03082805 68
    0x20003d00502034240342500815040d00344030500400021004221301a40480140d100780f200383d101d03000280c018082c403c041041c000012164000c0c0c05410032548004200c0c00515030088004508040c2c040071040354200d0090003042c0c100b00b0048212000c6801c0544064417002500c415500d00303c90750885581c01d10303400f00420701c11034403030340703090040328041d6004000014440d45070803144810420b061192901401c0c21400e0703004108115068a400c81e500350034000032000400c0780d811510b10103400c00400440d0044000f14051071040040d5105510698005030740b0746d200d01145100d100200c50300340040e8420b0501e903c16003400d4010f0118980e40c1e140c8502c401c4540800b20341541c0050107074840040488007004540c4d0b80c00700c0c800b410040501060007524580900080c42142d003402054140000c17400344c0c0c4034043c03003540034514003410a424541c00342460b14004002440b1b880b0254000b07000b800105400c0080c540c60300c500740e90b140c1d02c0301001e50001b03d07040d8041c02004200200030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 733865449 1250 733864199 733864213
    0x170108031804061503060f091118010e0306090a0203061b1c0b0418170705120a180605070507060816030b0d02030703080301081002120a0b0f1009091b0f0503040302 72
    0x4c3c2076026229820b8801c0341d180840c1e076604103480d0700c2c510300540c1c0c04800303c1030400c0c2050243d20301c0c1004598100c0740d20010710b50030403000401600c610071101d8240f5010b106035010015624408206140010310803003e48440340ca5a002e203010080001b084020000300c104151101c80800408080300711050b1000031403041100301c0010202c0d00c620b0407140241c00303240d175940e080200200c10071001620f960412814003005880d29681c031903c0710000742182d1390000d00b8015290146a1074004079001c101c0000742c113901c2d440d00a026403c0300c00c048030039200301320000c5280e9000d124139034421b100001d0f030541d510800f50001c034080c0072078250807034122000c005440c000d600d003404182d0103940034411881e500d514200c61940342140d40000321003640c0c814400e001220f00b420b50070f2604161200ba0100e4080400d1000405d444100c1074200c0d401100842c000000c0c0390803161034011101c901b42c040080701120440c0f810307000070113040d54000840501c110781400b4092405150464017a00c112010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 733866699 1250 733865449 733865459
    0x15030e0d200703022d03030f07170f04060c120c030f1b05010509071d010e27250503060408070303090302070803210a091a130503030c030717010803180406 68
    0x1c1000c20511408241004002c101030500e1178800e1250500c0066000754504400103c40524501030840700030140c03017501076180100c12888064500d0030740c045401315650b5a880e040604561400e05048a41052010140303500c6405101e40c0040940c2607101c07401460140201102c003540069070040d001e1204481c00e5000c200d091040c06c0c400d0301140300800e100d604046000c40c10155007070034200700c01d030f1200040c011114030b442d810350041001020201d80d00d40c5003095015a9800607015482e5101b0304c104c102508200b98036a40250710001040303609144c5400a00d40c8401c01110090103c000422a02001920951141c0242170280c03055075900313522203e13800e045a201c0a0020f5450000360381c00d0411340e041c144d1168120107013a60821801542c0d64940120035074101040c2d42090b04c010004480342d030364000214406034824241d940e01c0c600503203600041d420547d14900041d00c200c000c814035503c003482440c1681c0a82c0d00450810f00d080804424001e0741d00c2d03445030072030340754040060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 733867949 1250 733866699 733866709
    0xa0302121002040e07090e0103110d14150402010e0301141f03120504080618060a0c09080d1119020603130303092310050c0f1602060415030e0d20070302 67
    0x131300004001a201030400b0600100b842c00550042404005024010000504110201d50440106642410078030216007000017010031b203030514410318003851010384006c600d03000c0701601c03544c07003600c0d2800c02500c900145402c03101c540051801455a200100b0504518201800400000c074076080d440079031640c4e44c00800c281000d205101040e0046010b21000b1014403010380d004000c200300384442141888000d64941c402f41000d15042c0d59106015500c4c0c0c440e4038110090b0200360f0455191806102004103440b2441e04426920b029000c46034403154100248010030903002801d607403d40c2c480c85a00c011b0040446000c50602d9950700c03400d40002e20800c0308101c01c0070642c440b0040010b0301020942441a168034081d000380c90f2500700144100324805880f14082400d07226521a0300c10038044c1c002507041c403c040c0d400000803070300141540740c8800060843c01d0a40c1d061040a01646200d035641040101c50008034101a001314040c0006503000480000301c0c00454500c10f94a4010407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 733869199 1250 733867949 733867957
    0xa0605040c050c191110091e0602150c041a0c060103060906230a0c0e0301020f09030d02030a05040b2d13050904020d0602161b090b06090a0302121002 66
    0x40400c10206a020400d40c080c4100e1010307840c2e22001c0c41310782615696181c51103c03205c003030700d104c1c81d4400d050810742032045100750003410101c415040707076010441110042409500c07840c4014032480100400070381c100421140644081c40105051604212040710000d060007000c888600c0d090101010040702001994001d41c0140800500c80000d8203081003546d880d01d03000190101e055015182020301e11307803c00c0d8424082000000c0382c48584000711404000400c16035171640c008100c2071010f066030b20050134488000c400700c0780c14002d242c0007a6164000c1006200118805010030070032000c0c504010011a403042d1000c00d20360403190032495545840509200c501080030403843c12460301050f0001c00b51200b120484101d140c290700081002c801c09000a10710340e0003160001e400480c2d81c54200c2c04030f90002525407244140c884c2c0c0d540c07114003032084100017400d20420030000d0400c0021902c200b40c0240188140034295003c0c407545008840700a10a03101e0410025152041e41c8054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 733870449 1250 733869199 733869221
    0xf06010c060f020913050402010801050f0409050f0c0102010e0d0903120309050102030411040608011418070f0b03090705010815013204150e0102030d0b0d150c08091605090a060504 79
    0x584501486090000034007005c058240030724640310038000542e800c81c41450448804031aaa03072f0351040f9001090241c050550300405500c109214012917000103d28000550f40c01c0c3d000300f10b402c45000c2426074400c7d442400a0100f07040395420b00201d00328698102198245043c0801c440740c0e940e440500720f82c0112001c0c1c541e06d00407d80901c0c42d10b441c2c0a02c030014442100240245c100d8800070017109100540440c0010f119802c54141c240c83c14400c0d47d00030140f0180151945a0f00c1e410f183d01d540c400c030f51130507403405000d4003c00d1944c007800001e80110350030769420450300c00102c010b4503095500d4486410703002481152481c0162241c178500039240c401e0210507200c900d4600100203141d5000219010700514000ca0680e41c1d078000240d45620021103c00326009400601250146091007805013003541c00c0b8100050f1000319420140030500c2d140d48400059540445c4161110351b94030041160340d0030703407404004510b007203181541c008983c0c80000501c01d50791400501102c0644c10a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 733871699 1250 733870449 733870451
    0x1703070c0620040e04150606020f0616090302011d130207060e0a0b0613021204062405010212090604081c092c0c0c0d0e03160b030f06010c060f 63
    0x4a000c210103405004070041c4038001c100b000c1c280c01c04488010b40114010203403111308000014007404000e59070004145100e25080001c562540c2c00251110580c07155245584502800310303082d0203121101508607403c542c2c4d800750f010f0940e0300440e01003140d00d0312040407a0520b03107004001d658007540e9440c48600da9400503641d018030f04d0801c003611071540c0091060740001784444045961750340b41c16413042003180d180441c0c0c1405a01c1100a0003030000810020302c41d4030820040049503484010414600083c09409106842452808101e03d0150f030340180c01c40022401c10f05090800f6203503c0c580100b07058200368851a60b240f800d12520782c03002404851502e14411107070801400c1024000c851441d0340759903601c810800c0601e400c8440500c0d04c2401800080d402a88d03441980c4181c0a09026a64015040c000040c82040040e20640c400d01581ca00c1e2225a40c00342d8403d0111403610504a0030350303a0703000b890808040d0090445041c4946101100001000741c81648282141d03120 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 733872949 1250 733871699 733871717
    0x2010c1101030219080711460f0b0c03330d05070f05011e05070218040c180207051b01051608030702010606030209061e0d090c0905060303040f0b07170307 68
    0x86c0142211280c0d07686a0203a08904541c03a03281300051004400e040c2c1180c2402d81b8650010030650055a580081803a603411180b465800c2081598003002c27064002e0400e20083e0f198108440390b603200654500c11480e4050f903000703107000300c46508243c41c0307010300d01c11f12045080440850043c5400c0c0c07804640b5070308000020f000c80c01030700784984c01400082c03a01d0424880507400b040201380169425030305101001c41e011045568031503124112040084400449051500e4503102d165441c0c01115840380819000c04500a03142c401e894006400070020640c107420760300c101415580c0385000b581000800c111815500308000e4064485074412084c80395a8a032601000f821900550844000c060040241a640d655110142c854020158117018600308d188000c0c42040e20414440c4160941043d803500c0031b0282c0390341c4020440d050410144500c0e500c00080584a10903401810207000c03030800300f480110701100140045c43c1c414010069030355080002d0320110b81040303440c9000203204c04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 733874199 1250 733872949 733872961
    0x6060f180a1a0d050a1503051f0203073203070f261f090c0306031a06030607260f07021504120f0504030209102102010c110103021908 59
    0x75030180c0c01809041901c1c2030140030b1110100b003d118601c215038200d0349900120380d441030283e1024901c42e082c001840c21304c5075a071030126140e044c0403050410048110007500003d4180d8000c891184400c0da9400d412503c8022170381c4d501741030000b20a4841048000d02070381700060800154082c07902521006641d030819507000300460343c18800070700b80004a10710041d20702c450000c107941003002c05110100354221005040103038101c80e0322252000d0304000081c03012681607842a010703240106440b075010381203040310a0007940c0c00c1da0038541503400a00001c0e900f500c81c003510002980c0c0e001018045e40c00758051201d542c08203481e00300d00a21a4005c1c8801150100a0001c900910b00036441c218903054a8001c403080712030b40100d00348a240c100046015120740111006103600034030f07069080c00d01c120414461003960041c0c160341c281001840064040960107581202d1741690790030340d4004240e480c92480405112860b040c181c09204070305460a0003c19100751400e6035640400c246082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 733875449 1250 733874199 733874209
    0x8090d0b18071401030b18070801061d0d03081909080d0c03050411040b010203071b0501020d020f19020d0b040f1b03030c1e0503030f07090f080d0806060f18 69
    0x10303841c81c0c1654001030782000882001c22034400b41d00001d0a002400c0c84d422408216113224107452040740c21000810000074a030003410880c1a00c5250752030000b080440364401c0a0841780c54003403544240006000c000080c803c0f0403096200e00142c0d003a04001c5498441c220a4414950b021136440e000812845000c2403580300703030605070109140c140001e04040d03c40c5481c03900c0c402e4055000d0b83c1c8850010070b16900800441303494139404902c0e9451041698a000d01404d850f0241a0042c066101c048171000d10000303801002c5841c0801501880409600b41503800c1108030741240c118481c0b0000e40082070405800ca4881c0c1d00070740894500b4100c4c0d160003000c5112140d44003400c80c418180910100b83d00012602c00a030b44203110121007407582012515007921084010090301c0000b00300881041803c804034081d03412900c0300c144c0d051315142000b9121010340940c10303c0303070301025880078850b01c80c1014a0b0812030161815144c003142d084083d0450744400315070307003060b600150410107905007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 733876699 1250 733875449 733875481
    0xa020310050312210103020904060e01020c1f0c02070b03072d030209010f180302040e28110406230a050a08070f08060912030406060503010c1707032708090d0b 70
    0x1084d01c1000056042d540000c1d40840050005048030759104190442d0740c2c82541259891400402161a03000e4007051542c040c141d500440c4184504001e014a01e040c00080d0200684442e03014a03421035649000441d06143c8214035040107117810306400c006001d94008260704600c4554002da9982102000500302c0a02ba902c01c00c10090bd0508076500e218802d005001900d80c11a8086105840b0440141c9001a170007038803130250380c660400200c40e1503da0208103120380305414800398907000030204812140d991080c0d0384600e0501002d544401d201004040039407100400c035014ac0f40e158800b01e03410714250b4000b414141d024400603c03038060241401002001d004006005915111040c1a00c2e00a144a4280c00c0440400890100003843c1c1000c005044081c0081001d9110048010886254108034011101c0034802181d4882e1280c007403400081801a0035601e505601108510800316940042e106000d081c80b00380314580e102da1124440c14040e01815029091001404150101d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 733877949 1250 733876699 733876747
    0x110423010f050a050c0a0b0a0510060c0b01090c0c060510172107031e0c020f04050702060615120a061d010305123f1005090a020310050312 61
    0x999216400ea01503484000c5400310b0f0a01d15090351594515610350740381c0030a003000103012a403440104081c51b510380e84828818203040d441d000d00140d0302c4400b1b0310400c01e0944042c1c100300c2410014060081c0d0794001080c0404036240c4914080d0941d107031002120825194401321001d46041005200c00038040c015030304010601a01034104811864040c1d24020107085a10702400b042401c14140944104416490782e05e440307016a84040764024102032030744000324458000a0b400c2405070501380304140c81610142c00400722500d401003006615214100e00c41d038510f0040181c010200c0d001280c0c507004045481002c51010b062022020307007440302458030600305003c20010008a580000e44107808411142e9140d82c41c4131424000c0411410b415240b400c4401e00400642c06451074401480c8118241d076621045031100000f00042c0c406038450103500060040200c1c0340808198001c6401954050700d5002565031f1300042424010070110b001c1401002240b03000c10001003801c000030f00300c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 733879199 1250 733877949 733877957
    0x13120b01061d030a0b06040209030708010504020405250c060e07090e070803070c061103090a0602061005090c09011416240b09071d090c070204060506090102031b0111042301 76
    0x1095000c81d948448210002d40b010000b0401724060341c40b01e50441c9c03207051018058070900c1d511441098042d00068030300701d018504e010300240c4004c002818080c50451102c00d0354440d0418803204480e00ca08402d401e860310344c0d13510207103c5445400c001d542d004008692011031289040e41015003082c0c001d6001d090250002c1003040001480801408140e07031242c01e241000003c6110f2181c51400b408003482d030012101d10000c07c1c0c031034000036070510034174882a540710000d41300c50602020001c2941e8840b101901807040c0141c0b0342c040d030381c0e030b4911100d42d46030700d810901c10f11038002e20b004504100307441c400011403089502040b0203505c9490703403440e44018080007030320402050310440c0c02045403040000e0100c50100d45110b130407111540c6d16006105000c94205000d984846501c201c2049205030728007000010b007410004103071448010f05130003850410103001c0015140860307080100e40365559509000003a1500000600054003005014003442a07000c0c0300444011541500f460502c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 733880449 1250 733879199 733879247
    0x11031801200304030f23120a0605030304090b04090c150f1d0d030c050f10060e0405060c0f0f160b01080105100b0a02120c211305040213120b0106 64
    0x1c040048a030020341c10701e0b00105400358188100c48a1110b89268002940b001e2909200880e109015024110440e860900300784c581c40708007000c440c0e0034810242c143c1c00c01d06c02001081c4041d0710840328040041d002141545066444904813246500030284040c0d40d1143ca503401a0710a080c0544414107090841c0388001510b04104141141d48080b0f10030140307210b003001050701c142c404a041a0340202142c8105440e20242038481c80a01c9070002214900540080e81c1408000150f0007160400c01401c1d079601ea00701c1e4135641e0f902081101064640c20811008400c1180000700072001e540c0c40740d80d0180c580c41c54040801c04040c0e0081c0550382c181030034004080b8080c4030f940203c4141c0311800340d5891884038181c0c00c202a00c2c000d50340d00e40001c91400c01d801030100702c44082244e14800300a83c050300e01e412801c0b078013407082c07c50024402e4080520090800e81e00500140344009075150b881c550f2450502c90030b900d01c2100311030019401004000041d08a030400c14160343c0d5680803014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 733881699 1250 733880449 733880501
    0xc0a03050303010302040507050c01140712092109051810050a0b222d0e102106091a07020106050d06020d140f0106020f0d0e0405090111031801 63
    0x26a000602005e80301d0780d580c5c1d001c40c0385103026408a03078a01c8a108003c0c001c0700c000cc8000b400c1e0790f0048601e1004540701810138180030031948030701d8103d2580301030f409607210503042600d41c100c2100110f00c81030068258003c03031603a031400030700508101f50404401d56132404410507030020940782c2c8035a019464042050225540d03170025a03aa01c10402d01024500c00d8211600c1c2d140d01c42039000a9280c0da10340422008000599051504403201d248844080350f03a88400c4541d0f41d10450b5841c90000300642c0500c618010003003400341038054406030140202642d00d498084a0750008100c0b01c0e141000e04812558000d084100e41c8001c0c180000c22105107004c002c1400e4040e2141d004004690011380e040d0f813003605501c04041314000f410000c4a82c40c002446000301102800303440301500c10206044001c9d28000f41041d94001781d0f039510200303201e000d02400082c027406050747e0000e548070a00c4102c400b074004095845034074806840204103050761902c40c2111040c024800540503056401c0c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 733882949 1250 733881699 733881703
    0x1080f010912081e0117010b0f011719110c0d0c0210030f020d020304060207210912110409060f0b010305010b1803101103040210210e0102130305030c0c0a0305 70
    0x101c0140c0a052200682c0d803524010b800125001c02080074004d40e900c00031a55080040380e400c13903002504001c00c030751110302041090a8021510290000d143d8448511360f2240c0c8145d5aa0042c600004c0d668059019200010a035816542811000e44001c1602079019204000e118810032507800d22503044a03903078010450110402040d0010715071a418030400752001507049680030700040c0b00464030781c1040d2601c080654007a08066515101e80c607040010f1036850b03000ca0ac820005901c2d0343c803e2070328109070b0700454620b0303060940b1200c03004041e0701101d0f00c55006d200075080c03150038000b40d10401041e00d0b10444413160405810180780a0040c055075000d5002c0b5140d05c1d524018840c040c80386880005d24025a0000e02c2c0d1003135041403c0781101c000244061800b852080b2840106903141042c111142503600d9a0f000c032019030091000107043c490750000da0100b00715030002d45011700c104152171440d20250310485040d400001d0506c0c00c54000c1c880103280302002c4170314040d03c61460319082e03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 733884199 1250 733882949 733882973
    0xa030e120c090c04090603050703061b020303040b101716060e0f060702030304051003060305070603140a0e211209030306030703030e03010b040504050f0d03050705040923040b01080f0109 82
    0x2401440301c2c001148100c02c07010283d600505d10b000080c000c0944030700e03006403511003600c411609107007002110700c0c034400d094400100c0c880c20741e4001e50443d0b4650b20360070b4445a000c2d0030740b909a5050b820110b0b13107151600d43e402c070f0441c466005101641082042c501c1035080356100d0f81c10402000c242c3d1810369113554030540e00920441d043c64890010703000080c158421070b0301055114808000c41508a0f406402101c100c9026005a0304001d544207002c1d01950700e500200034402100000103440e90040c0e0780b003066071980c4c9000b1a040d04034115013001c000c0980c003007100141040850b8a1214a11412459038446c0303075800614254105080420b542e100c0c50f000080c01e1190281265285403402d500c1804d019174020700c188011306050920a403114603040100642c0d008113450700c991075009003e183d000341c2e1142d4500b85414500782e8810000c0c010309016050180000c0e0500c2d220700c400c405158012402741d00010469450700f00f1141ca0480201c110521503410b0900c0350000c100344c41d40322 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 733885449 1250 733884199 733884223
    0x306060c0b040501150f0f0504020a0806130905030f13051203070311030f0a09140a030809040f020405040e070f0e010303090e0a0e0109050c0102010c180302220207050a030e12 77
    0x12007a6202e61500c1c03800b401901d0702c440308100f0f1001e000a62803500000c082c04440c040c440e01110a901c4609010503480340e03440701c5000c40e40c440042412410803945901e000c00b82c40400090b00700b03690f903e003421640308405000e80483d02007400f504012003180c03d00001c0030222000c5031b0b401c04040405850740a56a40981407100c80000d00000e0030301802125032400801c85c40d140d0b11140390601520b03404642c0664804c1102007903441140341445607044003a05e4200030041d040201c941c0070403020740f0102c140c034030711503400748400500c82d25a801400b01c5040032101605181d410030588441007041640410030440e600d20040020903000380e041000c0d80d01451421865940310800c0c200540101c01c581485580381c41d241c00b050190118003c420754500340d000303020540c400c250442d0036400503000e003402c4500203c0200018a80b40c0150a00d0034002caa01804400c1d549220b1000c907007298105840341c1d00002214410150b00000c08480c02c030003118040e240742031b21038150741d850030300c4808 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 733886699 1250 733885449 733885463
    0x30e0313172404120806090412030b06030a060e060d150b1c03180f14040e011103040813050904121808070311100306120b130b0c0c0d0306060c 63
    0x56004880e070184141448070b4001e024050208612100d20480000e0445095071070701d0005044401c02c51284400d04c2c01150000c000109544498640e0034524807481d0080d4145503490a1078080383d143c071800385120b450440800070310140345c42400c803040c078802040a4070900701c1c840030f40c0015104c1c0070018240c0001a0f000900103103040c000c56050103d80b450a085000811427000070154071251780240010400f1401489076034071802d28060b890f090150b85003e04404900381c8907400c0503072051103108003460011800041d6a0621407056000707031401d80d00f00d50002900c48442961001220082078241c400003050315007901c0c4c510080d01001500c030100000020504034001d00d103074403480503080090a50350f0b07031a40e07843c201c101c2030907060744030f40103078184450500814041c1c4120011540c0305842a203403078650796140c0031000380040c0502c440c0614108844003040702d20705420f101c0d04400320704d6581c85554104103480c001c82e0a00c0501010b0428200b800b03640d52020640d9141644038403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 733887949 1250 733886699 733886729
    0x2306040813090f020a0306060806030717030409021908151e010e090a0902090906040305030106050a05130f060210091110030f0509011407031b0c050c09010312030e0313 74
    0x10007200c1400d1503a100641142c02d1441c804200f24442d40100080350b00c6840801c021640c5107010f03207403014100c3e1860341c1038103c2041088640d045480101180e2805030070307039182c80e440392102412a0001d9010795882142c04070038081481d0045160b40c3c10414042450781c1418010300020100307080c17100300072000821080301c03004c0da034010030100300c0751040202481e403a454910018402031030024001d078850000480481d42d5a00003092140c0195059500c1d2450741c1c0c02c005d01980e01c2d42c8400026410007a0400c40b94550b40500c9100304040e140251502103500e15250000313182207a0b0340400301c041850500d003a400501903030f20700d400c50039003525420f00106401d54107400900c1c00034a13130010b2600740b0082140c1c1c03020640c02090618003842c0d14004039110500e04030121000e4103080e80e00c00094408001d2150b001e075882e080d01c1407140c0708683c182e80d41c00001c107440883c2a4401c07123030b1340000c2c0318141c45d02c1c1c0c240c0659200c12880307000540c200b4400382182245181e0500c00d1103a9240c0d220 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 733889199 1250 733887949 733887967
    0x2060a021303021005070203300f090f0a0e0106170a0c02150613092108101e030602120a0615050d020a2606030105070f020c0121061223060408 63
    0x50146c502c065001419184039a010403201c40100c00d1102d04c000d07020010441c01241d9410711025281c801c002c0f001c0303160805035a00300740711400e800034092a42c040d1100c200001e1144090f516140600003954852198241074815404070640c060128045a82400f01d04220390781d0008640c440810244074200c40e540b9a080401e030f0605140329518605420446824240150035034078148140408040400c4090100011941e011080d13800c0c50b105c441090302089070b02c00c13007007100900400c0a0607000c0c000d540c965a0303008a9100024144200c140740c003c02c501c2a05a11a507001080118a8420000280d10004015200300c00e800120b540c0d021407401e0a2502c00c0c20481040c0c050100d01c02c80240c400c017203041c8101d4040780d580340b2960038100010606445181c01340c0300060035800518255284200540d4103c03881c1050900c060070402042c98003c49501075400200080280e07006402c00905213100e42004030301c504980800d00c04031203283c08a00241e007e40c06500006102e4844100d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 733890449 1250 733889199 733889207
    0x30f0d021921030e010c0e090c0a05041403030f0c0d0f1803060e0a060629130e04060e07060917031201061101090203011401090509010515010f0c020a03110102060a0213030210 77
    0xc00a50032031750719022001c20402e401001d5a8440c0700200d0311a15181d903140300b0024103204100c040c0000030fa040c0401c2000003072849022040e508010262820007030180d4802c80550440003501c44c00d9030005e00e2481d002d41e0002e205901c40842071811014040404400324100000352000608a9544404072441c490060242449150380321809001d500e0b903450b056118040455005c9004a485a00205440480108a070241c55551051240032450140c503440b004900030402c0d84d00513124078a4070380825043c80700201500c619201c03200340d50b0170314844074408100824103820681c4100035545960554030422030465003685009841c8040812805014125200d40250150f0034119002951400da85000c4c3c162001c0400400c0f4a546403412079080c1c0b00155401d150040b40748a0301405940304407149400ea018034240300d072842c00a81e0100341040d40075441541c4405036880c0c00c4080d50b0307050000c1500080829410360030146408400b2501c40c4551000030710507220035461010041c0a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 733891699 1250 733890449 733890461
    0x50f07050c0712030f0f0809120f0d1118030606061e040f030b0a0c0309030806040b010302070206040b121008073507140117150609030f0d02192103 65
    0x4100e0041c15030410320b1802402c0d1009503003003172020a02c0820010300680c41001514400c45105c0b004000f800c400d51200302e9181d02c50314140014120070407031a80681d4842c000e1048004c09030749241d9407030b0751089120780c120704901c2e85d09119400c48014003040d9a541d0301901c440c1001c01c80c0e081c20303100c0701d10344408a0380b195511515000c44840000021300c0040c1c51000e210f500c446505006445c0103000c120300302c40340c0349030090200d404c40e004620641040c0e803201c2207030001810300610b0004140c000584036001030303021038004840024580900d91010440c10340101c1c0f9405a00d8000b0705210340251600003900079402e4a40150184801c1c480208000342e5001c01f90220300440c0c5da400411403600d800185c02000d0a074420074000450b254803a43c03611010958520300d051440c3c44201e00c00700101480240c55500450520a1100540d002c2c00500540981c0c08020300789600b003c4130107400d028241d01c00320504140040c0d031b540440e03c10403a507115494040003010178590f0400040d801008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 733892949 1250 733891699 733891709
    0x70f0b13080a050f0607110a112101091101180b0306150a08040c0b040602100203090f06090703030e090f0610121d1e0c0d0606030807061b0201050f07050c07 69
    0xb20b104619028403401044e20411619940d042e0b5100381e40d0050103803031001c0e05040001d4035500103050070003c144d481c980a06441e80050074050250f411305418500910583c024152603591909440c0810103510169860040b00b030811840e000c98807202d2011080d01c0d13110705d0000700300c0000068142e58a050314031542001c4500c259844880328040100031010441c0c0480d030010075040041001d000c02410360342180c2c110f90043c911000da000e00503003c1c0d04003030200c06d00c6110f81e10428120300c0050040380d01c607081400051250034070718280140810081d544281c001c240440901c6800310360981410703400402941e085100e059010360844400c14039910304080a45050a11000c0c0590f014035541d813a040402110302d90455040d05201e43c1d1200d91207080d00e41c3c0541541051800c01c000700e008424085c5000040d000c0c0d5940f0f50b8005903100880c2100d00304c0c1c3e01d50315503060703c01100d444414511203200805c420320744107009081001e0f0140100c070070700001040707443d0020b0041101002501d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 733894199 1250 733892949 733892953
    0x180a0f060618060602010e0a020a05120c0d1a15030604060522060b0f06121501140d02070c1401020a062f070506180604080a17100e0108070f0b1308 65
    0x548003800a01d20f60281c500154203000304004d01382000110a0740854004204248292070b150400030201c005d03440d508124051070b40010f1880c2c0c0c1d40100c541c84e9602a12200b07450410f1031040c45000340700100900c0b1400e450001c0303264540c8001400a43c03090303001200103020340301c1c9000e2441488106103015031240e808204482041110307008482020700c103442445d0107851740e008214030f900600040d00446201d010000e00c02803822400642e02c65010306201c032202040406c20359150740507041e401d2815170000f03000803c004071000c0c50801060a0084038141403e1600000d4032103901341c001401c070a40b00c02201050024a501b88a01c0c206400040003407545030795452a80c94100040a50701030040000042555080380030000b10010100c01510065480d40e80f0000c01b0f41004000e1000c22801a04001122a420b11100d001303040c448441301c411840c26842180c0004140c005903007507040a1403c00041d06c01011800c299800703030440607164401140140c44101150340441c0440c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 733895449 1250 733894199 733894229
    0x60503060f190501120209150702010e091e0f1e0414011404061a06030a02160b0903090316050f010e0301091a0a11040303050307110c0a060215180a0f0606 68
    0x302608002ca0300450f0003e0301c41d600554a14500f4030120b0041030600781d00034114031a0240040000300041c42014030505000301908075000101d03802180032140c00e120281020313542c03002c20b12202d06455110480001c0038925242a0310b40d992020000755200c0c00d05041d41c0d001c181000f400741c1c5a4420303010f161008102e80c1c03a0340b00303004002d001c05076000e4075040d103000c04e00061040030701070501d02103d02410141c51500c0d08101180251300082d4081004035210081400080903003880b0707401103055200840c0c07076600584c20141004540c10840c1100d46441004100c203449100c01a1001c0c0e01c24249040d80d5005080400d000d1b00046a000f0324081500002c6545c441c2a41d101500580280b501000100005000300e070b158400c030b000c05004240300b03200152590307100f801460a40e0a10b030301561280e50340f0030302007042c08029400c401c0250700700700e00151048104884140d0311666144000040f013980e200d540f52103404285c40078005800c1062a1814095150030000040c143c521000c80a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 733896699 1250 733895449 733895479
    0x80309070e0c09150f09150301051f09050616050d03200c0c060304060f11091c0b01032604080318031501170f0102030a090611040f060503060f 63
    0x203480d4540510032103416004081500394102809603403048001405444901d20800703190005500300034020742010b00100315102c402d03205d02203901080407504028545a5040c8010407040c3d0000580d2a101c240460b8494a4120350000c4868210786007602c125980da150303404001340301c0c098442c001e8164454000100303d99503144d8464010a9481074010300700780220000d49082d8441e0841e011a240d100c1e03115124545800380086400c41d00c52240050040a2050302e80181d03480001c92552080c0081040d061a080c500a07017030118186c50410351080e003140da6017008400060001030a242c071050a446c52400c8000c14000101419400c100e403544d6030340d440d060380c0390700415808141041803420300016080000d944a07440c0480c00060029038201558030044c0512542080e0f039904c5100c0310110114000c1c8029402001d10100100b0145c40302e082c00c0c4242d0310780200222445608100401a01d04240f503014166207803460216540d444820004007101105403401c0c0d800a007000c54295 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 733897949 1250 733896699 733896703
    0x12030c060f010b031603110c0d02060406051b03041103010e06010f0305010f0b060d110f120603010606050c120a09150c1211030904051e27031303030c0f080309 70
    0x4864024007816448581c3c0b5255a50042d00042d141c800d500d0a00341c0302914610f01075000200d142d0008480182000b0102c008c0c50f10785842c0d400c6074009078101d00e051000b444903074011680c0c04a07050904a4410154100300c2c50329200050002d094103166901c0c82015590030342003051a265100200c3c4c41a58581c410b104425455100460791980ba02180c807510010034052940748410040040b802e003140c040d060406081380e0101c0d1803003901c1c10000368131510100c60142c09165548040e200c42443c0c80c03000c2c5800c40745c1300d4000c0d00030700c1781c14001910f518034001214019180d08281e03458488040c40010303030300000c0c030390400740c0034664101400c44419031055a800765036004101c1c0c0103200802e440182c415485600c4040144d40040001c04940c0c03d10f500720640000c1c2410b5000c07401140000d4040d05100141d0f0a0301c4031044504008404411000c800452a000c030400395103441040403001311417103079034807005083c08002600c900c14003124486d800c20b601d4107c0c100e076a480c0381a14020b9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 733899199 1250 733897949 733897951
    0x20f03040b09242a04080c0117010803070813090f020901120b0303191806020a02130506060d05040816050c0307060203030f0705031308040803090411070c060e12030c06 74
    0x1001881a0341d121040407004500c243c2e5001c44070b0b80115020785441145150b0b48890359440899072940080c0c4105200c1e10f00c00074030052501e5005406190301c40000103056484004184880c04403a100500140401004442c003542e4440161644d51881e140d00030341580c0c4552203410a1417801006000b640d0f2150014550030000340c0c2c8914001158800c228121610640750700e4040e4420302000b0420004000002c100724001d0918045c10b96540000c198103540a07040800181c03c40e0170213404504201603c4003080c80081818449440d0000100b613481c001c8202c1a050b481d12078001c50140074013002203468415100591210210706030a00d235a8521802070054047d04c21940005041032000c0306483c019201c2041000c03003903c030810100e503243c00140c02c80b11880f90685042001845403001003004001c90b0307000e0b40e1100010402c0104650031100b20303da0302041040084001042c0c0d040d01c0040e517a09082400d040b410700700c0410492041c500e12038103640710000b0f210580503400a412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 733900449 1250 733899199 733899211
    0x7090b04031101111c050a0c23070b03011212050403080a080f09150a050601090518070e060406020a021e130603050f030901090e1902040627050102031c020f03040b 72
    0x52000d441d002035075a0796408015001d0014800c1020400074035101b200100381d4040e00d4071300000b000210352a0b541e4250350400d2415221091419010360100d81484550028409540590305640c07421454170444085584000c0c48056420a5003082d02d0180741503d001d15000b6400d607454103040702c80501400010340311040402112400100602c070300103602d04550302400706102c043c0d00d51003c60800f900000e800c490600103501404140707038580103d00204034014410001460501007405001d00540740b25150007004100001d102c4103800081224a00c0d60507540f114401846644802a200c0e940b0129a80840101100d0003d1401a008041924012001c0c2d8095024102c00700f41c1c0c1e80b103800c0310540440c540400820003a820800110f0340b2000143c40c80422000038075a032400c0380c0c0140c20003400714809595105980c00c800104401c080032182d0070645490800f00042d540e4056401c03035002401e2001c00e00429030540381c040e07034441040200f82c00e84904040c036049501c1320f011110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 733901699 1250 733900449 733900457
    0x3140a02030430050c010905010c0f0305060901050d031d09180c062b0b090711060f07120b03010b061201050102210f070501020702180709050306041104020307090b04031101 76
    0x249406900811441e1040f0000461580e5010341d1540c10f8a89800c6180400d80035580c1c0c00901001c1003080c001e8103e00245035603845503010a28401500300d03000900a2400313000c110300103119540303940c08403070300c80b90b09030502c0c08208510031000b05041c0d5140903044d800409401c1805214030482d001019011090700a45000540f0380d810b02140d805030701090380c5689581240840c6600c02803900030b014803510780000c5501502c00020401c0018184da003440014500c4000e50b1101e031090000e00d4002e600c1180310340260401c4200100f440700c482615491140c0c9c1ca1134a00e00703a560035484410710f0400540f50702c0c1c0300e404054030030340c10392003d00c58a805402000ca100c407000c0da440c0c03c404980c0000040345401c000708640300c40c1540e00305c01c1044480c0d642c204540f80c00750792001c10b000000c5a070020204c2d424641203000074042c02207503103c54000d91041003072000248281c000c180340304000b5540142c40781d07903184040700e6407501503009444031040000c010092001811280c04108000c0e21 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 733902949 1250 733901699 733901723
    0x151c030f1d060702060703020307050312060a0603020c2a1f0201061a0703081b1614010e100b0d080a0306090c0c0b06010c1104020a02070e06030307031b0303140a020304 74
    0x4841c4400500c549660368040350400100b03005141040103860264080d1040300d003061034503500c55203107500554038101c1c1641c0d104100180c9250501003040a411189000d50034000040600b5503200301e080003990701c42c50380ea40c0c000c105100d801508078000c2c0004049116a9071b00562400c14000e4075041030006500741007011900c409070300004040c02030712540c2c0d10310f003080d20f4600715441c140180102d250103915105000740c441da144042c08041c5003c0c1d66181e410405498080c4100504400c0010707183d04100204c00010000324031750102c25400c800100f41c1c60802c100041d1080b05112001340303074140c013081d8034118270750540c40749003540c180e000c04000b1481100ba00303965180a9910042284661000041c2e20354400c0401e250464441d00907080380c110f413500007d003641c00011032440181d01258080044000c4500c9150704101c0c03c0d0080c500e04049a140207103501c1c0160310b026a00c10b9a02c44180402d0310aa10031a01204109078220321401d0841040b07010754401d070b4041d640d40c22114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 733904199 1250 733902949 733902977
    0x40903081e06030334050309031506180903191205010e10060f2a15200c0a050703060c0806030105150d05031603030c0801080a0506151c030f 62
    0x4841030042000400550a00942071607140e19044002900e00c0c410400074000c002c0417040500c1c440d5054481c10141da2101c002405052402808160454480c0c0e03180c4103118003611050001e02005241d41c90b5100103aa501604500d10f01c00d1000c0315101044403103030360185a91010141740031003079840c0305001d640d0b614010075500d03803400d440c0c03202102c916200c2003041c3d1b070280c802c1c403030ba0f850107092170880240c0e1059815100100d80900d900d802142041d0b4400300502d00421050502405170b0401c220401d501c803503248602482a594030103040041e14265039001000010314882e03100c0121400d6940324a0000040d0403150300c00008030341d40902196072881c0602030381d44501c044501c40c0800360a607500304105050401d8068800340010072005001c40c00050030409018029100810361400354003000b0034102e0160302070341440d003200050740002034002c1400b5400c13160715007080c815a4069000140e1031009942d41940302450303043d0400806030446007520000619894810320b40e10341c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 733905449 1250 733904199 733904251
    0x3070801090b0a0b0d14070f0504020301230105070b0903040311040c17060f040207061a120723190306050601020706140d0608030307020109020301111207081504090308 74
    0x4000b42003200b16000110a04115072040301e070300800030302403d210790035901c2d00350001c4450811a0000d4018110a20200d56110a00310082100352821842d540c50b200000252007100d01d20300b10120038000100345560f1003a0b017076601c065080340c8015550704100c0315060f41c95001e880200c030150081c030146200c83ca090320a030080320103203480b40c4460507002c1d051102d00003401888036a02c000302d8009608a52602e2010f481c4903071040400064a5041d0b0326030000c2c7c01035a03414140724495058048041010218415084448000c1c08062001086110041c040006825030b904440b010b0841400c3e09044081401164007450b0100110b071030368001240c6a0803140101d0700450f507280031100c3c1d20150040100010700c000e10001401d15181c0041070300310383c4141e82d5000141e4446175181c00f540f80c207103d0b008000003400c0c412490f1544a004640ea90b06005001006001050f8001101c0404a541c0c080c522100100b003009542d09900d0040d012900c103480c0c40c00380300c00c6184030390494224 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 733906699 1250 733905449 733905461
    0x13030219180e01180b2e030b0703090206070b040b0a02030105060a141612080915130620120603030f270d03051b1203130804050a060e03070801 63
    0x4045901c0c00034203104003070200038003841c0e41081255941c0706244000d50300710064030720810748180048909414031100080005202100902006044540504071064407510b00c00840b03038032400a800c9035031001019002880e60800294002e540000c51800f00a102d45c0424481c6124202c0a83c0c252614240501240001d019464111000b042011641c50040c007030710a410140750310240c540300740e076039010b800d4072a122422113400d00f10800107103069400149a50b40070200c00001c0803220860303001c0c84001a4040d041c20f500302141905001071180e2504120140c220051403040e00ca200002c41034015400031100c6c80070303500c010780850018540841115101c5038aa001c05081040168091400011080340401902450000d40c13440e41c036003030318200d1349074005d88903240c4175010a20340c8180c404d01d2904040c081d402100c15100208103071400d4036000724201000342c56104d01460a491140315580000d0380c4038001d2000003800d80e90100700500405c0056060703500c41c41d03451000c2d03400d0700c00d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 733907949 1250 733906699 733906709
    0xc05070f0e040b1303020c040e0307020415060f080709060f05091f030c110604060c0c050d0206010603050f071d011110060611061618150e031b0303030103020603041713030219 77
    0xb0016484101e0300c8e10b07400c0500c550f036074541500d10301b88541c0d00080031202c50b504078200c12045880700304402c85c0c10440020080c4601e00302143c1074a88043c1c010300c1b840050103114244903030490394882c040d02c19003e4881a00300035203d50b032071000b17001d501340f080c2e002c0d054006c00107810f00302d8101d040e0388a2010740322200b0035400102020344131540c07404081c25a00516504001a6134041404070303000300f00c000021a07294001e4026035042400c01800c1c0c0e13100072302141e1230141100501100a038410f801c10110030390100f1900b100c400500040380d0074070b0103d10606230b07481000040454606141c2c442c4089400c2a21428401c03090b0402854030348404440810014844084194207640540711410001030124092000359880350403807100790220000d5000054203491502019040401030300c19089100d4141d00184501e07400026900e22050100074040d500200100702003240c1480300e09401c101c1090420389400c078210308800c0c21519444242e100b1182c803d070342c01103401c92185980984d8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 733909199 1250 733907949 733907953
    0x6051207170307200306010504050402100f021905070509090f060a0b010e0909030a1808101104090903051903022a0c060f121012030c05070f0e040b130302 68
    0x58906030601d001ca0301c120040d445103020801229000619100c1d40d6000d200c4040c004614100fa09020716182400503000f141c041d40c9000305000150752601501160590f203490100000070160308220b040080e10444000b4010349032500380304000c008a9000241c4006661007211903403030300991681c4101042e02d10b03a180d00b1038804101c01d07180c190413103040481d041c180750f24668040310120b0750f110743c01c403111241500082181d02d502c1e40c3c8541120400c088455241182c1402e040c1c101d40c5036007160200b54461590f980c802d0342c0d084c00c1841a10020141d0440800000e0b50360708009e44180d1040d400440d00081581350144500e00a00c01d40f00320426203000349600c07051151441a5000640010028a10a00e5400c120381c0d55036100800d07054585801594a4004000c241100010f0207003c404441c50302c650705020101e01170901d0155541c152801814006175820094200706a9400c840d40b80c4840071008039061000c03c9a084c05944598444c481d00c0c1d445040b215013503444032030024016 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 733910449 1250 733909199 733909213
    0x5100203150d050c0907050307020c0d020a090f1d0f06070206010305071203020a0c060203041401090e060d241b0c050a0206030a0b0a180c080408070f030c0f15060512 73
    0x1802d00621400c0080d116504a5030081c2c1500c2c005503480004803003c0000a030000708000c4807a90501c48444807180a550b40c800000003540040d034605654000c41d01a40da03901000041c0d071100d031f080401c10b480c19904060008100d1320010b9180c4003d140c001d0b03018404c2c200400c442a200180c0c41e41241d4200e400b80025038103003d10104104c00580b01070f401c6104014594002c1040460044001c00803074004503030341c1d886c080b9040310040056103080d0600c21458001c008885246081c1030f031010701203403c0d0070b03074a081e0b01d010324070001400c02e0140032102a09005941268030350080800070b51034800c060706c40d909004103c902c001034500080041d003040d1143c2e801810400081c5401c000c05031008918250703a007010070303101d110701e5005101d001c41e400e001c030141c5001407042c103901100c14030b040c40c014036054403078180074450000000c100d02070701d406d003070700741846920140f02c9a540142101c034414103509150075036180c0b48884020480c502000012281343c08070482810201c150060444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 733911699 1250 733910449 733910491
    0x8070308030c1c0c02120a05160201050c061009050f15010309020310110d0c020d0c0312020f03040f0204050a06062a02060c0303010e060109141903061805100203 71
    0x10750409004046480d00078401c52408800c20246101c00007051100010200b9a014000340781c0000c1078001100d5880c00c200d1400420346c03201c11925060010410740388103000c00d20049446200350700d890b0340240503032000d00c007800d4500d09010085414440090115455480078500070907410b41d4038640c00d1550110700e010650081d0000620540000c054903203490403c41c1150031f0b00d44140061105a4001813982140c0c101071041e04845116840144044584120042c1005026117005428010040e042034a030144035011120031049480e400b030b1701ca042c00c2c030f412507003441aa00100d12607801d10300001d0260000c7c2c404c2c48112440e950b41c002030340081810741581031f541110480407140d80c00b101f5401585800300108aa04800700c011581d0758508000d0983c2c010029240904102c00d000e803c00c120000d1750700c401c030365000885082c05032141c6054047c1c0c160702140e000a0456090070340c1607054140400195000d00d02501c10746102e01d01e280007403002c0f44401c44107003500e2201c2024800c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 733912949 1250 733911699 733911713
    0x6020319091d06010c0204020a0c1e02090601140708270306061012060302090108030306120f070b0d0e0f01020c010c03060302091803270109080a0c1701090804091410080703 76
    0xb0f0809018107080754000f0ba02c0c0c01103400d80c0e00016180010403600416601005084e8900d80089511b040c030048514407681d00141c154280540b02d83e0400100200741140c8110000c201d0310361a512519641c2e6034101200114a441500f13000750440c0c003030400c2c42ea205400d0114072288204001440940300d04040b01301903c03501d0200000c460240c1e81c42002200584807001640c0c043c159401c0190741301d1030051f0801103a1940b10141081940001d0580004074000095100658401000e4140c48000503020b01009080207405075100e8460301070240d403450010741c010003903c001d4100a0049043e581e00075000d070f6590f131000070b4128401c01c0c00545001000c0701003001a0000c0402d99240c6041140c255a12803080050f12910300c400308002404c0d90382142c000740051600101511500301c40340c075443d8a42172140301d5800080301c00e481840c2020020b500c031005581c0e01c6540c2c56150b0391100604001410b204180364042c04c44400400c1000200e0035505041314001c10040403290b00319520b4034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 733914199 1250 733912949 733912951
    0x3052509031208041104150302030f010b040506120c010e13140106180605030412110d0905130b061b0c031f050a06210c051302090102010f11220302030706020319091d 73
    0xc504507c0800400165001d022050f83c80f1013540003c100c2801e80800c00084030b001621680c8203084c02c0c0003041c41000d0208820781000c009007070100c0d400c501c1e100892505909100350055482c038144540c8031400d007a0b44814141d4403666039a81461032014148100c0c00410302403000030610a0002400044114003850000e441a01d040b01c0014061203286290010301194440071407892402032006040c407000c00c8013074682280c0188025030900300810420311420030901c01030505152103468040d0208034a40074810064111084050728100d05070380e22204984c000d02c003505140109240c1c582601480059071945565034500d043c1d020002111790141c0c24003120000100c0c20001010b5850000d20307010502101c0001d43d07215000f0000a00319800d0070440c1c0e81c840d01d0008905440e0314004140c0303170b04920404002407002d00c007103a00049607405510003507143c81000d1010941581c00f001400c000d0440d10040c0f1410b41c8a42030603640b000441c011544550322030006846181907141c401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 733915449 1250 733914199 733914221
    0xa12270503130f061107050108073b0306090a0c05060706140a0b090a27030306090e0307140304081018020a090c02121903052509031208041104 63
    0x200e18241c000d542c480b004070820382c03041a03074001031403040103c9a0007031050000c2a0816003e04046d900b480000381051402504034001c104442c9210000c100712090b251640310084111107a03890002c0740590f82190070800101e02134014000401d101c600c0001c1c80700d014030361050080c1920b5003030034140013440d001944155482915840c0120060004203404c9014107000d070004141400070400380304010701c000d440200c42c0c0f0b15002c03200081410380ea0010804070b98480c104468000a41421070140c91a1b4101b100031515102401c10503142c00030040200340d12a1140340701a0400315041c6443e130040b0b01c90b002c0c454101d0001c2700c0350402c0d40d50203003848140044640c0c0030031265402103411000356800440600c1c1e900d0540404846d01000b0345000d100c50400d2030f40c82c0c0701e00111501c01d0040f800d250030041c03688074408140c02185811842c0340401a60201013982228210000e0550101d0300c425110300070801100707040710344941401c0f442190000441200c10010009100080c0f50306814 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 733916699 1250 733915449 733915453
    0x605030705011b0b070c060c0509090c16060212180607021c03090803040308040302070909050a0204020a1407050a230c0f0a050303040b130b0415080703061a0a122705 73
    0x18400000c0c00720912103010b45c103a680c8080f0300600034034009080b181c244103103900788071040c040001d8940da100421580060384904040d115071004003022070401042200030511030001c600c0c0a001c084040d0810701c9001c40c503150241c1c268040880640b40d400070b5891400507040351120126090442d4040c0b030b08009145000660000161103031047d0f9081600c0490026803c03c1c18402070540c10404000a098062020403030301c1d400342d4a10b507a4260068000380120307004612241c5082c0a203140c500c06c80e68800d02160f03a040c4500c0c1850700c500d0020340440d81c501101c00341c070380320250b01501c003a000300c82e03c0002e1400d00151002c00040b0280380c0101da0780080f001001144540f0240080c1005200841a017604c60490031041a080d42c225000302c81b1280c03003408200182d00c0400d0605544601904180380e0580381c0c041d040b030191415800124040c08180400020009014000d10704100c96076030b038168a10b043c000e042c00b517a402c1c90003004102119100e520807000000d00b0000150b2003002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 733917949 1250 733916699 733916747
    0x5090703050903070c030501020d0b030f030406141306110d031e0906110a0207050f120d1b1205030106170115110c030f060603071a0a030e0a020a14040f060503070501 73
    0x5a81c5c4141c20700341d041195030380d4010942006014042c0200e680c418012405403030030100400b503655890040e48204003c1082c803120000711442c4e43c808450004911020180743c0d00d498543c0a054010151102c3c00e1900c00d01e9400400584603103d405100c0031113402040003c444080c4050203480c40740b40036211035a95400303900040c02c10b040140343d40e200c1c0341c018019184ca8001001a803000088000e4090b204858000c20481000f1641d12001c00d11070600c42689840c111113a03540421510004042c001182c00f811042c540010141d41210588d80d6031000360300c04148043c0c22070100b84628002445074008400540d40034111184000500340e003110000c801c3c100020303141c0340200146c00c80d00d801c05000e001a80c1400c0c010500a00307030182c81041c418019046104140c4a03824414040541c2c40f074070340606d0306042c1701e8a1003864000f04440f18450729400d900000d540000040c0d03104a181000d0b0031080c0311280a00c0003260301c000c001e0300c1101e20f4000199040c0388ad1208030091244094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 733919199 1250 733917949 733917953
    0x60e01120504030306260307020103090f1203150b16030f0c02060d1505010c030806100504051e0a06020a111e060307080105030d08060d0212030d020406021f060509070305090307 78
    0x4400c10784070b18043e9402084032403602c5500c2c50007003002c03d5001c10540b480552520300c0c1500004480c141c1e82c0c20b280009004c026424540341500122400600038002d00a10703d0074540d040c0c0080c1c070110b800e11289184a5541d00c0ea0500e54415044040306101c402d2455402181c0181d1020305000500c1c240154983c03415800102a27900c080240c0e041543d42d04010b0000010700381c440f501400c0282045040d04d03046850280819000400d090701c01c9808030841143c9901c210150780060801800c4042080c11240c100c03d80e0300d0000a181d03018121071180040c4040c400140e40b2015904080000040d200780d800340322900040c504040030000004103203113102e40b00c0c28020352103054141d44030440303541048101070074818140601c008001c2c401c028090503659109130214032aa0441d246002107422450741411409066100f480c01c5101040001e00990040741c4284180f190307803021011401f140300c04204640860040c030b0b40080354500040c49080c043c1d8440340c1c00c20015000c9900f81086a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 733920449 1250 733919199 733919201
    0x150b06040612060803040f14010c060203041103121c05060d0804081c0c02130e0a06060f06090b07050c0904050f010906020904050f0c030a0c230310080115060e0112 72
    0x350707210300002030320440008070401e068850000580b03808009580740a03c1c18201c6481c6203d2400790001c0d51511100004a5078024a0232041740c5070310500a6449203064241006401101c9086074040d0017480200506204102c0498400008285c0300300321f0347d008410f00b034004180080000d0307040360320300720b01c0e002007810300029000a001c8880140a2102d8800e0700d445840340c0120b042c000d11110b04d220800680c1c80840f90b05107108417400001d103840415032a0742c60f05290704405001d440c604480843c82c91121240c2005031049903e541c00050755030107000100d84030381c05015010307400c80042e1038054908041160781141c080c00485558400f140182421100710950071200b081c0e0000300d80e060f6081070701441d584256904242465881c143c032402a0f00c0c8401080c1600d01d030355945846804a00450441418203180c1e0005640549040306054040e4416201d04ea030f0302d0700c009000580d8410500a035100140f922403031840440c6068010b85410a40e910880d05100044600044038112 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 733921699 1250 733920449 733920457
    0x30c020f0a05160b040506070204020c0309150d0b09091510030c060203120601020312010b0f0d020d020706050903040627150c031d01080408070f0c1e0509010302030a150b06 76
    0x2d80060705107050703400e400d0718450989a108500050080c0010403566031104242d9004540580e000b683c1d5594808a503411032007060786440d40054072102c444032924045018106c2c00385070381c3c0d04201c03206d4032204001202d00e04866046c8541e1000381003601c061003503035145410003c0f10b200300204c02d4813540c410400c0c01070b81e0000d90041e400810f404e80c2d0000d8803500640c0100f42800910703d00606a410100b000405014041c086c22000400d419206000012903000c4004984d045440b80803401003c0d0182d4030040e415112641080e001c0341d8400c0c80803040b2070848034140c031203500c007582400c035100d080420043c40c0602e54072800700c0003c0003c042c00410075216010303926a1101400740c500074020242c6940c0840508100c9041c9030410790b0000107503074000f90017440302d507190b6545181503520005112001060841c4000002400100401031600074130280810300e42038a845909104600e2001d22001e5815840414460080f501c010303000d0941103030001000c02d0054410012402c0b80d80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 733922949 1250 733921699 733921703
    0x30307080708070806090a050606040b0c07090f021903050702032a0d02060712020c010221191e05040521070203070e0106021e150403030603230607030c020f0a 70
    0x12220108a0701c203a0022815602c02c1d01410440301d40d0a152003c0798044500070080c50310103a1b69004181c10790344600c207580007041c3c4003007500e0341c8040c50000580ca4440600c10640050300f0000000342140c0c0358000d03502003003004044280b04540e110703c101c0c043c10700a400c00d005d40c0404c01c03d1142c18244410800400c0004044090700700302c0400260f443c0c496028000c40c01c54100f02c0034024032a1744807101528400c4c0f564805a1960154440a4024850401c0c0d080500355451020740554581c03000b074610a10252a03403100110002c1c440609a47c0041c00303040d10300b40b007003030001c1b03503001d032035208640260081c3c045896074080c4c003c0d051055845044070281d010b00201d561003c5103010414030b800f5050f1852501819494003c020395240d182002341440c210b110029852805410001100808110001984030341840c1c1005401006240820341380040c0c4440481006800c02ca41c1c11404203007000205400d9031440012001490340130301d68800c5000d07481c20b1b805101010026051103034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 733924199 1250 733922949 733922957
    0xa060302130b1014030105150c03070515010f060509060a2609010f090b160c0602160314030717132009090714010f090b07060b04050106360503030307 66
    0x14150b80208584103401450740b0b010450b0240c0401214440d203815641100c0083d1048094100c03001c0050071360780600b0304410300521010030303154140b00000a052580c005900489002030346c0703541008950484038011480859000c1040d8135150903d4002400ca49481d4034140c18854014408602c0040c0c4001c00c150781032020200b44031b405072082c400d001032081c081c5020000719109503160542c21070002e14521003811f00211003007130503000c0c80d03103115401d600c50001c40d601c0c000210782042180700e40c9000d800207941621144500d400310804c880c0207188179120700f040c40813890304008031070100a08440c00141711180e108005580d0043c406020810007039004004110131040c80191030b8020801909540460002c0154089229070014005030038a003151286030104030a9035410926403007002c2e5442c000602c0c03000d01c00241c0c00010070301800c4405100c6640d172840e084031040954414841c5094681c856089080f00c45500759401081805428405540d034600181c00c41e0401c85402001c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 733925449 1250 733924199 733924211
    0x52b0606021603020904110102010209131a060301060e12031608040911030717061f0806090a0b0105160c030c030b040c081507051b06070302130e09150a06030213 71
    0xa01d8041c0324601c1c1e81400081c1c004202d901d1500000c000710320150016040c504101d41040c0c1d141d1003034040710720920000d850020108810300b0204001c2c00412414401201003420044030348c904513040b00d04039400c0350b88144004207404104000442c2443c0b81d410140300230804508480901618131070b440d0b01603c0d60270740362441c000c000c40c2621000b40e000d0b103e0503070070010014800e0f00064130110300b02010303203000036603074621000c2181c42140d02d01ca42690b00c0c1035080c1c5244154080b5500e4412041175420054036168540b050f401d1b40e4138000070300d005c58420b101c4c0100b1001d09552003815103024002c2010b505542c0d1700c070181085030581080c0d40c80e540c210200b00a10041005800c000c01c440001041354841c2000040d136541c0c0e003d002c03502001000611011043d01c450078580004811505a6009007080c40d80036000354070504007150301c0300f12420002141104484150302c9040c81e40c0c042c0080c5202e003400f4440c51038004040c0740ba1150f0b52000480980ca03041c51315590861142800a50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 733926699 1250 733925449 733925459
    0x204061803020105160c05130c030e070302011b06020d0212041b081b030a06050114040b01030605060d091718040e0309010c1403040e040c030309051f052b06 69
    0x44182248081016000c10200420040c2d13804811540040d8220100130b0005c05c6605c4d120750142002c0d40803e9124000c20600502c405e41d69100140082880e1410400c0c480f0988141d41c4a024600c8080c1c0032079507152130f242c00d00c0c03c068180c809092207880014580b03600030320000308a0304900da101d948024504204820801070254540e1403140c3c942c150040321340f0b0210743c3da80d1800350640300346444080c96001c2000c1c1e24100004001154403450503c550740e1510030800d0500985c009207071141d810001c40b81c889501a2244400781c40001e00700c2481c028840107500c001c2c0c042024215862121000038011300520701002d0042140d041d59046840c5a2078001c10040c2d0b81e46502c001c07019001001a003400d80e8000c00d69810030baa20a41a15244081070602e0381140182e80c88102c4080c03d0a0401041201e001d06000c10340348240c0b40d210003540c072101441903480d4054500d003c0c04203a0440e0100c82030142002c0c00b81c5503070072069040d140c0b1a0002400000030b00c5d00b12a8600303900d481003404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 733927949 1250 733926699 733926707
    0x10f02040e01151409060f0403050d08100f0e04080f07050706050c010510050105161b1403070b0702010c20060708030403031b0207060503040606211403030c0d0b0f03070801020406 79
    0x200f0b0f4000d00d040290403d084034161410b114581d142e44c03080800240c0383d0902d01040003a00c008681050969540040d104d80242a51108560f00b0822001b023090200380d105041c61f00c68180c50407038900000716036444d61511016800420700d4845460301303104003800180c041041a01808960307840c41e84800d0f40b0301c416801c2d42c00c00740905504283c3e607001032200d40d90110581d00c4140502c031510075001528200200384ca0b41224101001240c65000841c010442c0890005160401e03021100e8442c2c0e202c10604c06c602945200078001070701c014444001c0303491f402c070355254055a12888025440720360005041c543c0040012503a100c804010082859010700c41c81c1c4103646c881c0c4180c4150080b80200a40f107168901520f01484008800301d0b0a024a44d403202020b8070081c1596644250f403233011304010804036600711040e80070403030801604d01c40403068034044c0c1e1041c07642504105c80301007103001828400c00b00b075030452015000c107100d0f59000c1040d640141141c000060307031a400c00c0c800030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 733929199 1250 733927949 733927979
    0xc06020d021326010504031403100b0c1b090106021e0f0a030305070e0f09130606090204081507020307030c02060703020309180105040c0207080709051909080901080a0e071403010f02040e01 83
    0x1030120391505e81004082074000c074150140320803004c0c5e100e60325912808001680d01c8607400690302ca50740400c04010030b58000403940c1d4004598442d402107000c0039403c10200c402c09000d41c100503084500364203110401403008458080385030003600c884181006507145003c5446030306800007a210001c0c0710025803c40049985030b10f007518450b4940b6a010041502583c011741482a103c2c610445801405141c0e4480c9002c0c2c40e0181d0107556459844100e1030b03650100311241010f2100d5600070960b501c0c000411070308101d50545607044116259000c12031242c02c000425415030108010307508140d07803075100c000c1c0d090680306500f1302107504010900084072440010f0f002598031000d0140096000000d046013101c5662401040c04ea90311042c0d011200e03c9080060110360900401c0020801014050311000300280c2e07035a000c583d503c07000c060075518040482d100603042410309106044083c9a40c40b20ba8401800119004035070103a81c00407644260300034003a41540700018403111140c61088 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 733930449 1250 733929199 733929269
    0x2d01090b0a0f0b090411040b1c140f060402041e02030a1e0b010c0f030c021305190525141809011a0d05070c2001080702010c0c06020d0213 61
    0x10003020b410000400e5244002900203000c3d032180b0706d2000003a90380c0c0e4105807102000503152042c1460040c40c4004200680e0504a1fa0300404000e4100c806000140703405e58003600d00c0041c40e05407961b80a010080841038540b55000030302c4040907a100e1143d0000790702500c0c075100001480c03601e02c00c0640c2c00c1e050903c1c103012960f080c0302507840660390000c0e01080c40e90b000f10208031600c0c002c1c6025034080e0b500c505d0094110308601003081e103810300e6a1210340b0454242d01c0c071009070765002c84450221041281c2405141402800c40c034080c20701d4031000b01094016052142c20201d110b0036015403900306180030083c810302050143c0c014140984035034010000300b01034161a40c6004010500ca0040c140c5500f0300320750b614005000746100e04280e00f6059080174000003003c416007400001c8051441480740821144804511411b2052046100011041c0c1d00c6155615140c0d89201c00ba41c000c1030b811950b01c2d0207010303000481544800d201d0091581e4014486049200403482c0001c0b00003084c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 733931699 1250 733930449 733930451
    0xa150e0109061d01080c040e040f0b060405041505090705062d131205150403031b080603060c0a110d020d08010902090d080a0315091a0a03052d01090b0a0f 68
    0x2141003225a9038821183d241090902520703641c3d0b0000f05400034000d903400242e0b5460340700144414003014414250760303540a5074103040166605018802682e03401e4a0040c01075540f800c014008000320307801690070100050940d002d036031707039400001c405801c4181007640200b217030381d080b107800c07885140110090704d88000d00c40d08068a1038014408061544201090680c0c1d0382a140c041020034004a10000d884450400c1c10341010305004004041e03030f200c80280d01520f10350180c0c456014445070351042038020003c0c401c594441409001540050001100380007020442e40d881d40410310906580080544c0241790400c404080100300310b2041e44040450303841048809956110301042c03101c400c2c0c01048559480540400840003030401c1d620b40d10850711003940201d0120400e4120923414900e1001c410a224a18010800442c0c071520000300103500c00d840500000c1c06000c00c3c01c0c106d40b1007128082c0f001000c0340266003555038116046809a0b05103080040c0529184100071100d018058 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 733932949 1250 733931699 733931717
    0x70225090c08101502120a080402120c030a030e04110c01020a09150903060b06210103050f010c12090507031202010209091605030402220c020318030105040b13020a150e010906 77
    0x824038400214091340b4580c80c808551552020700070000c0d5401452443c01481c2d4800c412407008003001010b942c101d100c0c002511080340c803441c00081c920100d10004024014441c62941c0513a221011328023106d4116407500111282e080d200703030240c480c0e4010b070030001da0fa644a005008000c0552604010181040d045052400035405000d400c1665840100050801035000019201e8040c003801e5044001e030030411700e10703250a2000400e040b2032288040301d8184469801e0030342a1303600c1c0e510040005000f2491020034071401d40248082038000c0c000d4803586501da0f180c0c0700c030009030669150003507074000501302054185811540c0c0d00400d00300b4615550f46422a00600c40d10000d08041c0c803074000b0b1080040000120310020401051000081005d054004800b0b0344079002008010f1240f42003a08812407810180901c2d446150701a00a0546540300488143c2d0540843ca0903a00a501048041b850310000a24505503104546900c0380200a900005091501981190040001c2c41d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 733934199 1250 733932949 733932961
    0x60308180d080a0503191e0c080106230912061501050703051b010e071e0b0f030402130b090a060302030d09030803070e0321040608011508010e070225090c08 69
    0x22043e18452642131030800e640751500450030380c6210110114001491800b000d403418030816403c0800d070021058030510030512294420307030300ca620907c035800c0811000407811030741c4011254018000c9010354440750400d001d40000c58000152108405d000b40d000c581406141c1c20315910382c50741c81c003007441c1062900c041035400421030b004455000807240044622480741e800e00390400b0f40300002540c102c841043d0740f009114013942603404529540c544001001c162410800b08482c0704040c2c48880c20b01d181c0350756003400b805540f0340b0400d410b103950312000c4c0d0030350350f43d07518145001f407803940000700341d142c1940109400e00200e02129014003c44242c10000903a40c101aa0307803140e42820300b40a05001540400e084c40214242001c100340da1822840d809070000c4c018105850700340d651b48085a81701c0e225079441e00d80c07408140012031680f100401c0364061103507035541d006806205444d684451503255196800408040201115118406016090b41c601c6055284480340c640386806007886 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 733935449 1250 733934199 733934213
    0x801030519081b0c120105011404060f060f091806050a0e0f06011404050303030f160f12020a030605030105090106170312191509020a02010606030b130b0a0504060308180d 75
    0x540f900108001c00c070800c035035a10310240101c90095502030007016500e00030f40006402880240a82e0055440c0d810050360789003005c0c400d41048e03c0c49915101e112a00780503050f00c2ca4200d001c01d860400c5201e1001003240081c0c0103000da01c1c140310040104001b800c4c03400700540004207421a20740c480904040100f901948420340c1d400c10030070f00305410b4410ba4500131802d507200d02c0e04150380520000061244c42c00c51707180000d01c10b1030031407000142030031152411070302c0000e00e103030400000300b2041d104811301c12242d004126410150400090582e0b50b10003203400d5840403203030114203954070030080140c6002c1a0041c8140c0c40c4403405507107481c0c011036880041c600003030300103400300343c1c00300302000b903280e0b20b901803210069140a6003000950340c80b9000041d40c010780498005500301140091000c1c0030307004001c851103004100808640303205005100a040180380c0d13a5002d0460600054182c4440c410751703014501980b070543d51103503940d1065024165046200d4000c4541d814480082840c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 733936699 1250 733935449 733935457
    0x201260a05090705100207080f0a03050a121e020705160506070b0612010e0a0c0605030f160c060c260408030412020a1209092d0b060c010606080103051908 68
    0x4103a20b03041035040c03814a5540100d0742000c240c0d000c01585a4000820800b00e807005002c6560f405a00052540c0f42c3d01c0c40030f80100480d20034032211009034083d5404c5107403100d2842000030140c0c1c400c504452102018045240b01d1517001490341c0902005128800a01c002c50050003006454003000c540789114100d000340ca034501d0200800d10a0b51503042d04105d40785210000c0c07101c400c090004076214170780c50100b21840d44c64a03d0000d00c2a00a0080c0d81c0306460004d080300343d40d40c0d6603002c4208040c0c1e400d6050200540c649000000038a14407982203001c5c8103607a070404c448680d40c04080103070904100c040ca42d03480b14040000184464088a40c010340c04404255001c100d840241e103840902400140864020200307041c04c00e034064185401c9451058091020440b4904092890b401038440041d441c0d1803a2104050090140c2200c1d407040030150200b440c00703204181c03007070031100ea641020380003d80903001041400700400c02c0c101030350f804c505007401d400060340d200141c900c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 733937949 1250 733936699 733936711
    0xc020c011d15160605071209081e160b180c0303030c130b030a1b030e0618070e09070f2103140d0203070e040606090b040e0a111303020126 61
    0x8034503000c202c4800c030810640d860400c80a00615802d0354500e08440900400c50303600c0000b0309000000045008103002d00c900003504201190300e05049202d001c0d40c012903100707000708010000c1015010701d80a407000d140b03020b40280700c2440517040c80002c401d0b00102005036501154800114928a560044102c0360096000c13000d4643e6070710000380c0900111629400b41c1001078000c41080908035041d0400d52a0b500c14441e0030b00d04268194003641241c1c48032044411950202d00007480d400b6252940d080a20480b40454006698514040c00c040404440e5007000b6001000f04200400c3c50003c46000f40910303032980034445030720f51029a0040c4c05940080c1c01c11000303131582c10507459074508541103512481c038250740da4688082d02070701d41034401c0790780d501807032078004001412449000007605540e4884400b502e06450440840448080548683d0406070780e4140030301c1d04e2074004001c00c01160241c2c1034440b024610300000d27013038007881c00072504056212072410712030000c141e0006502c88 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 733939199 1250 733937949 733937959
    0x5120a0210020a1e0804020103050c030f04170904060602010902030f011407030b04110403230d020d082706041a070e060c1f0b090109020a021e0f030d0c020c011d 71
    0x144043c1d40444401d50f207401500c0408800001110a0b0b070307031080314075100314002e880a001e952500032603941030384411600a01d511310010003040004000c01600b250005d60082450708003110a400141102d40582c080d03000360f03548140c00310440c141070050710780358464800200b00000300071111400d03c0b031004010904140c0c2c0c8440071581961170790701c041da00842e00c45031280c541c0c0d124900f845d5412b40c49000c0c020310380c000c400d81000091000600201000d072a6016182c0a6007880c820b50b0707801302c05007000d100764401c00110914580c100700c41003030180d0304600400443c00c081c100281c0303005409210401034144941005850754009400100c0403400345c5003c1d58419034485d0076410a40c160911500e001b0040380b010f8125400e40d000907480c1c0504444c0a2a1a40d0b1019100100c0c410080c44c0c90150f004031610344d000c140704402500116074510261040d00090030391823801c40d440509006032039541d40c000c00010300e50400074010221403e081c4607503075081303980e54882046c2c00d030190a4822 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 733940449 1250 733939199 733939207
    0x14241e1306110a050604030e0f0a0503030d1808070f150c02070312120c05030105040c0206090a0f02150a0203030a0c020c2d090411030c0901030f0b040c12050a05120a021002 76
    0x200700200104074043c0c1e0007106031011741c103043c6801000d40c1200b5072503602c9042c402e60a00001d1400d00c0c105000c03501c2c02802103160540b800a00009427240600c0c0b03042c464410300030780001c2051400208000c034820303c92128000e15503c1c000c68290310415100e201c06140100c084013082d0001100011b807074103c8064099419207060486190640c0d5800125507420441c03407003080d6802c100030f94103941c0216001d0000e0002c44004aa54440c21903400b51254064802c032400324000560300000c890000e0440c1004040c02d240c43c461503440752500000582c4000100501c40801d445581200c030410f101400142810000056100508261600c54081d024084444654917103a982004c80360103403a02565213040e040c80d5800102d04100b1f14001e0240b1550401c50346804074881e4180d075440305074280c50340c0d0140c0b9000440000208222b504600d184008910b10060603401043c0c80d10070300050507030420b189000c900342040100f10740e102c58814071040080780d8000c80c1031141011100c41c01611 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 733941699 1250 733940449 733940477
    0x180605070f140c1c1e02060705031206011803030f030f021603080105090a0c020618071815060201020913021e12040605060d0c14241e1306 61
    0x481d81d003407a0002d1038541c400341000008040861800c040c11001c440140c015030004014060120701c80c0001410b02403c091514840001800c0b00c05495001505c207604101d15541c4042c030795401240c001e20281990701c1001402e692141d100004442c3c4e201034a4651841c0d50b5000c1c201428024801c001d15446801003006800f10398152118504982c0c09241240140d04000d04461030a0103840d0080c031b03009001402c0361802d401000340f07941c6254018031969440130300d2480341b00d0714000101d881d40202e0714009442982c03880415007031482010002021407000c044241c040c013195200d402564014041c8100b0380c2e44801031600020010400903944524148100d2900b130b24618103e02940d90115541800c0007044696621036132041c4000c10094403900100700c04030002c0d5200034441c01c405207082c4051640aa0441d07100c94014250080071281100d030f4515041c42c43c2d000c0c00b1322100101e49003440084c03c4010308100000d8800c0c1c00d280422502d038641c1540528014842441b00201300c50700 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 733942949 1250 733941699 733941713
    0x309060a0806040f0f240f0e0702070e011412011a060c1e150709030f02131b180f030f0813090c0c060b010806010915021002070b0f010618060507 64
    0x20707110f014102c10001c869054400718000e2600358441c14210310551441c00c02d03001c030201b1503410f0b00c00f0214128451403800d01c01700300e5441d00910320011409000b0000a0203015400e00601034064420b011651040c200c0074850150700300700c050a00c41c3c0c102030700c0705411100304103035600000e010f8503800da40d140c07801c08603803428051903100350a2082c11100c0242079100483c1224205414070f0001c1899103030b0310703000c6030096554040503100d0b2545c3c2c01100c00602d403006401c3c41010700074401107019012460365920491031ba80c0c40d40c02107044a0f42100200703041e40340c01c40180012020b801e03d414199260042c400440c4400107045020008024444000003102079008000c180000d00c154a8248002040300400007800c88c1c0107418800f01740c03081d60280e4401c62003038506039070b120300c0f00f0300c0c2035a1405956002402d1506500680e0700010112451b8002064030a000c0c50b0485460b042c02d16060340c010710141c0c881c008110150042d100c14400700d0074500202d41c1c81e0301d4550303100c01403400c00e12 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 733944199 1250 733942949 733942961
    0x60301110c01090b0c03010e0c0306130c02070321120914030417010605120a11040e0d03150608060a141503190b031b150c061e0105030309060a080604 66
    0x140d210008510302808a03015040348419903c5424003841d907480700800c900c4540000e0040d0000808040c0c0029403da400b88040e40e03202d50010078601d0b045402d0b892203001c03280c0c440e59441c0140c00040040c0248182110640003104030300740480500010030741c00415121098840303420b616120100780090058000203c3c40307101e019410b5030f40e2295103101d0360100180204200400d035003040303000102031401901e500460140000034052808442e40c1c0c0052201d105060b240e4000e50340d07400c24201c128108860300307505440b40c800083c004030b04801460341503907551003142004410300403c442502e134040c500045440b0584202c4078005c1d00070015245c0e01c600d4210a003054004070400c06625122007407592104469402044404140018107445012200340c8948082255030b050181c0e0901c0d03552403203060000c7e00405e0400780498590382c248041507440d400103a003905517420141c840c9840340c0d801050124010f41c0b92002580124503d4010024680103015a40b000600552241d8002c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 733945449 1250 733944199 733944221
    0x150c060906060803030106031803140310090509010902090a110910091e031101020c0105042603070b070206070f12020c0f01151415160f060c0c17030f010509060301 72
    0x2d01646840b1180280e0341d8000344100d000080c10290041100d05190591040702038140e5207556144108224486041d4005400303080010509076000480d00c442e845168003803034001c000851000858010040203200107000002154a820105602c01036260103c42d0700d68019035007072081e9545a0015a0b091040343d01c0090a003510385101d0441e9107090030240b00340c80c418038041d41c0d404410303001240e807003906000644c04a10100014000301c0031020980d403252404010306d0640101c24101c890843e0805001119444c100c142031140c0960144103183c2d0104862070300d1a20900f01010041030000a9443c0b40402c80d0300280940d4499810700040355001c01c900c000780008401d0045003201820188200010900c44601a00e030502e008000220303155a03100486040c1a07400d10361902c500d505800c1281e01e0282000243d00140b000e00506060600e1505c4035180900d4a0034181c41e01d803104107160008800c10020403d08454107504a410358405581e030506503030312000400c0c0181880785007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 733946699 1250 733945449 733945451
    0x40b21030319150b0d060302031f1b0c032604030206011a0703050702040b06131d06040e0a060b0102160905060a0503150f1509010605070516150c060906 67
    0x1551400500020045001d5009a44015003102440ea4190b0440e044040070819191104004000c40080400039011400d003802d800204a41c1c0c95000900d03107800140328158406501c03c54000012140c07140500302d802440c629055134107100700040480000d0364001b000d0280c160466000d0390f078042004040080030f40700105040c1420b08000c2d43d01c3e40f00348201c200711100100101100c40701c08043d07464031641a11a02e003041d046508120291428071247c0e82c100c03100b40150203101760307046c02c0c0f4402808118136020850324a2038400f1241d1308018011805079044c940d000400001c00104000c496810480004000c1104c40c0100c6c1424101d0101c0301c031031407015001080700000307640658000c0c00c0840b10300f038085030f0342c6003410303201d94910ba07170036a00507821800100740520440b03489500100705051142c040a0741000a4821802a00b243d4005072000c228203081140c01c000c0d001c2901c82907496050b110345406032140c0400c210301e203c0c1c010803210042a004103c1c260300081800341d40044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 733947949 1250 733946699 733946749
    0x30f0512030c1206010246030f020609010b0d02040c0903170405040b0306060603010b03130f0b04110906150702031609092102100207080d0603080406090e090705040b 73
    0xe00d4400b0303005440c503202002c1403440481e00c590300010b2480c20550601480581f0124500500c03840002035501d86030403103c0500c10b610048001c44080103c07144a9183c03450f03e80000c0800a1034044001c0400c00700c0ea140c20078150280e40c0391700b0914140c0d64103e82c0070a500d03401100480e0030100c2030f400100300d02d01d41000c03203d980c1d01290103042610005e480400000100300c3c1010341d10385040e101c0701d80240c0301f00018004101404015a030020380940181c45161059880e1500402018800d6072032442002c10b1004001c500c50040300390320403c54407120b050030004002011844801d01d030202d18100001d4200845d00c0030f01a8441555183c0a131407129562252580d010b4610000100c6610035030312280580704000c1440c0c80b4548201e9401003851103040d10301000250300003e0240c1c3c80a40c14031592000150034014000070f14131a8680359140c83c5401030180c100e010742c3d0403555016980a08100c00002d000440d07404030742040f0343c040f070a9000310011a0283c055581d0307508800094131 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 733949199 1250 733947949 733947961
    0x411120106090510050f070209040f08040e0a0c020f0c010f02070b07050a020405090f060105090c1c0c02011a030c04150305030c030a0e040218010809073c030c030f051203 75
    0x40e03545003102c1050700e40304640b500c0b80304126803078460516038004074482841f0000150910034103443e48648980c00c2c01501d0305068540d101a50040d51244404069070410817030610303044e02a400f14060107000504100307151199440d01c0c2e20205204504000c0c10340d040418051003008514002d040914810780d13501d140741080c40e00d40302c0704070081c0d0065090501148001d40d00060402c01006000c0246c01c65900784804c01910031401307400c003100c0b1034040c402004402100c0303030380707100641d0002c0d000240483c07d800c0207425030b01e0425040c101445007100b400425100440c00c6040341c0c41c129000142c0c0b04400c284403401d010981c0001d0424440132032114441c0d80c0000052942e05400d0f01d5000c201c40d01c850800041c6d01c91665104c40c2d04180450060380755006a007003641004041040e20344007500c034104107012080e81401701a08a0200300701046030720035010010f190400c04007424a0341c40c195116000c688a05c1d01c40100003181c083d01b02d00c24000f05014040110740c0040c1c8060340d0342011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 733950449 1250 733949199 733949207
    0x90602040f090e010b0609011209150203090c030c03060118050c04091805060124031d010c020a1a0403081308070f12030e010b150c030717042907020411120106 70
    0x1403450f40050398a41514400c4903d8004203580c44494140e44002c10003200c19084c2001d0f0a242c4000c6803038070210000c4100d0303000030780050740c800c2007050000c1c2804102324041500c1d015507811028000e070040d0006001658521a4070031445882d204080341c81d880d5044041007a01c503550028070a1450312650125064140703402041103401001120056620340c40e44128070404070684040841180c1440181d1600a82140ca85407013105d000003a2004800201c90a580a02e02e00d01b00581007070039140c04110b00c81c0800800e5801d40c220404107440c056070003400c0304070007418428032540614090020011007404035400141d000e0010250701c20705203058100290350000500209013416611101114144035000a9040c010411a6010800c40c25034030180d00803441086940010040c90000c180d00c0d98400d02d9103000035000603944d51074010940c100c60314007440c1c0701400100984030b03446c04021340c00b0344504940450300000c3c0144c49081c0c00c02d03141715800c1044140d142c041d000089071600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 733951699 1250 733950449 733950461
    0x9020a0b0f03100602010b220f05190c02060f07141b01021e0705120a230703030b060a0804081303050d090302040c050a0203031b07020a0e0a15080c04090602040f09 72
    0x82d0f0300c09803541d100d200903801e0b80d41400007150481c0710803080c2800343ca201c14000c00440c01c10f5600084400c0031703ca0210584504079407040c01c0c06068020290040d04510072400801c40344c2c0301070032450501e0540c0c3e0b500c0c028080c004004104855540300e0703080880034106d8a00da0552100100e00446445055010703402240030819284a0505980010311084048030f038800d6008000e8844541240d40c018400c1c0c110708124000c05c201d1204a840402100451800e90740f4122005504c983d003d18000342568920b0f44124055032041c0640005550032406954000c0d50258550381c07903010500a143c000e10540e40094110702c207030703101180b60725086030b03540d41076134003d550500c0ba43e2401282a01c1903c1105c2c4171000513442080000c0741c10795003a4082c40358180740c080e4140340c262650001080c51525812a06600d451f44003401201900b5106010140301102502d85100e850400015150740184e0710361801540c8480c039400030080f840d4111400303080b1540c18841040d031158140c0c0d0003480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 733952949 1250 733951699 733951711
    0x10e060117090a020906010e0d120504080706030b15090a140303090a2c0705180a030602041e0504061a03060109090509030403051204051012020f0f0705010b040902031009020a0b0f03 80
    0x505e907000c500c1952040340000c5401402903e80300c40003005640700c0960141d0001082c003040020b010120300490306002c00001441c0c1c0340c0e00403c0a00440080250342c0c0b454542c20440101d00300058010342c0c440710302840c11216181700c0401d01f8640440403a00318401c000720580e1000540e5400b05d140401006c0b400c2065040141c80d60080d294402d0840c29a0815106000480c0c3c040c080c812006091a00b0309e0124007025201c1c120b40c1d44d403075a506040e41c120307412503111843c2e050070450030840f00d110403900800c022902409071500d4440d03c0f0442d10080080780701181400800112141d00500780c80000300201c140c10065031401400e0310b6229042400102d484e405070880c440701d410b02c45c10548040d92802040b10301c0f8032840002c2a0b5540042c1c0440120040d0244107030b00f00c000300800a80310781084400e09a0361071003d80350660842c7e01c10001d0f42c0c4198946072140015844c0010711b40e80e10304c031000d0001003030001c82c0001581201e1a900950f04450001001c2001410ba01c0285020385 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 733954199 1250 733952949 733952959
    0x1b2904030f0f0210110c0708072d260607120e031e0a0c05031c0c0c0506010e0907051302090108071b0305071109041a070314010e060117090a02 63
    0x188440400c441011210392100011303030103091034169004061340541c5041c03e82c001c032685840c0a0320301d03203400c103482a40002c80541112000b00202102030495030080b0a180046160070b080d440b001500d070802034003603200349500017079000c44446c55448881c1d100002e464200c50b0303285040d880090005600b03040d4050b8260411810a094800002c20f5400681704001c403d580610640b810844d40d400c843c0101c0d080029070356881001c200b086c4020311621031200041c15006a41c4445201030f02c501e09486000c0101138840c1c000420404654035054842003103280451741c45540240c0c0c6480441c0d086564401184440c040e0039280950081500200a80300c056490340c9052003074510a000410010800100180b5540000d1144000300b8140303105201e00e401000b003600214500c0a0212411942806a501298065500340c07030340035808506c900d4188400d40480c0c03500c004041040c410380001c00d41c3e8401140c616800361840d0400b24a104d0181c03e480d00e0040c49e03081d51814881c000307174060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 733955449 1250 733954199 733954217
    0x90c03061d040c1202061204051207050c09060a0b031311060a03050f06041b1202070605071101150b07060e0106050301022b0209060f03040309030b01080127031b290403 74
    0x2040308021080044d60004e25007820041d009a0307001c0000c1c0002d20450344c9010b046201d01080424001401105000d0002080060064400d00580711400303805030384100c171100310070805050007070200d9500c40701030083e030f603c082c142c0c2c604030300341c15420500380c0e0b88050301040c0e40d12600e47c154815442411402c01c1c6c02c41c1074540c00c0a2108964a054a140440da922030f0003040e80e41c003800c017940b0032400d1030500501d00391054417400d0480d4415035a0200192032507010400d820000d01034031000c142c0c81424030340141c0c1f40c001100d410b441128401010603448541120110b0001c0d80700300020240070f0300a55661032110401c1c0b0705402250311035100a81111202d00070101d091003510003841c030103000c1c00d10302a00c000e403c10441d00000c0049080064400300400000c45103000f06001305030800001c03860319848013030303030200244401030500c84080514012011944c800c1007102480c51800b0301c0c001445580c1401c20805018a1085100c0354900000f040c2c40c04031007032101c0c8641d02a503200741403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 733956699 1250 733955449 733955459
    0x120a12030b0301231f0b030112140610060e01180b090310050c270d240b030a030c150207200603070815040902031203070216030507090c03061d040c 65
    0x80c090030a450710000701e00300e00004005c58020008008621202d000c1d4428266070f640c900001c40d44260401c000b00905600e42000b040240100345100d20703445006070520740761040004040c800988105401c0090120010130307aa405074064030382d940c1961340700404c0c1ca030304d40b110328401c0d901042c102d90003031180011805180c4070f1031244601442d40d03a160203203010800d18204040c03082c000039a480d85201c008100c203c03544d8456545500c50700c40c0241208128840441e909020700070350b018441c0364144104e00c94181d6000c40e0304c550407685800c0801d40b680306410158840030300d04010a01d101d100203042414090444084a6000a085c400c2158444543c0c01d02146010036280d29010680c04030108256043c44240c0c1c0d41c0d841000f510002e00702d881078002030300d4540c0040412a17211400400d00c8441a41400724206d500050f00480b040185980d803440d0f82c94100c2d10610386030303e5403002154940761203604644020642c400003208030803414520302101200903507045900c61084000001c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 733957949 1250 733956699 733956731
    0x4080d1e0c08010608190c11060a0903110304030f0b09010204170c09280f1116020307050406030b040f060b060408031918030209060d0c0b0705060601020a080702120a12030b0301 78
    0x2c8036411b25050000d25180b040400e00140998450040c1404030200805080000c1044101d03c030740d040010204a07000e06050103080010b040c800c669681d08104018008500f240e1080f02e107103070340041540308950398201001d009008540100b0010207402c00c14211456000803000740f00c50003200e0500c0c0c2c50704ca01605a01ca500c5482000c0c9000007580351400b0385410b154070200c1c0340d10030044045407104406006010503400420300e0401d0b440249012025414104401400f810096404102150458403403051a40700204001c15900041c250721013080116000314124840203060380762100c0d102d1003601c1e01c030703082140d009941103078202120b112284900c1c00741540c83c1d41401040b407123034115024041101d500809043e0010311a6a101000030020b9420710b0080c00c02c00100c90306c0f100581741050602030040c1180d811540700d18010408a0001e40440e01801c0c1d0440d0f03088010b411040c070850620b20b004001410080f80c01c080d8010036501a00403090384501280200031074114042100d03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 733959199 1250 733957949 733957951
    0x10b0409020901052707020a0c05090708040f061e02030a15060e1201270b07030b0f04180210050a0905180c0a230a0906110604080d1e0c08010608 64
    0x658428040c8004000c0c40c14085c948040b03500b00c084c22100b80103c0815461800d54040d1000e00040c2d214103141c44c00d00c0002c60005002e85411200d02d80f160134070f140000d20555000c0c0c0050710b40b24050070f02c48200328841c0d04c1240030464000fa001c0d10050704045440094004813060241c00c2d0416000843d5802d80000003816111580c60b202000045002440201c0840480000c607540d660b02c0e013518440c007950b40c1d02d40c5803805401e80119480440c0b43c602c0113518041c120000781410900c001d06a9034422070702443c0044165000241180b80b400060900d0445900c040d4000c815240742031845a8000d004011950141c0c030703032992840d52401808170203c3c5010201d0404003864010401c401408002007501c40d040d458080d0302c10075008100016001051404200c0700d10000d026418150020002d2000340258186003103031040c82e000e21521190018070007082d8582c0058103403502e1002c4c1c1d11035181600a550032410001002c00d03c040144444807860300401c6d07002c400000c07002c0c80b0300651 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 733960449 1250 733959199 733959203
    0xf04020114160b0c0307021608100213090504060614011403041203141905060406030f02040905031b01020c011a0a15090b030f100504060b160f0204020a020d02010b0409 74
    0x841010100c0d008500030a03007042540c61010b0100303144210104a0302402a4001c0b0140b0400ca940c81c10032101c0070b0b192120b5280854000c40a1000030084000b0220f0150f1610600b0f00380542e440c1003140c4200284000b80d0000000c4500d002c0511040c42207690110041d00d090001101c140c444000044d00c0d03140d0000728000b000c2c441000043e000a10010004041c0212414081240043d05140082262049440c07540c0c0c00d540c0140000e03103004c14007946420540556003040302c03c0c1107440c0c286001c54481c3c2d02038041c90b100c145140402000700b04440c401412a414000704102141005007c0c0d80603c200800079070074003256110320110700140d6144404000c080140b503516010b00c00601044c00032249041c4400c18800040c0c140302e00c00114840c145251070200c40d458120a000305126454010380d01036803505400b400101d01c080d00b207a42044070920084209011841c0007090321101c104025040b600101d0004442600041d064000400e15002840b20454070000d20044850384000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 733961699 1250 733960449 733960457
    0x150503010203190207111c150902060901050c10050a06050406150507120504050d0b0601030c0801030c061d15070c0e1005010305070302070c0e150103090503120601021906020703080f040201 83
    0x9529003e03c0b09a0041505c01c0c4200d00344407001c01d04074002202c412038011540c100303000c1c4020300001c2048000405a020407c41010030030340c081900822002d000d03542600303060000010305000c0240d42040402d4030b100ca0120107101c68504902c4400c05090f80344107150145007410380225507021138a994940d0151070381d9400c0d082a20076228262021503213028802440400c000110361920740302142c3d00400d0040301861443e0514000060844d444000d413841003116080040c00090841c8091070110303502071404100441d14441000b404026a03801030380d10419a81155017129114001713005514002d400c0301c8440380d0b03201c07104200300c2000c81d505100300f03d00160a21441d8025801700703820004500d03005082000035521100d0110094020b805c0c003103420f100b00250b0760351090307401d02050341c02c0c81c0500c010f141aa65496403400390408240400d0400000110680d10800c010410244030106801c0e42a01070308240d4001d5101d40c50590024201c1400185040d1a07880e0f4580034580c1070751 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 733962949 1250 733961699 733961731
    0x20c180603031608040b040308070c0b030f07081b120106080c040303140706091e0c1d0402040b0f0a0e090d0903030e040f0209040e1b0a150c03020313060201150503010203 75
    0x503c40c00e031103c508111050b1000341300215010340210054400345100c0c0080c0c0399a403c00b420a0f41c01c90038168008400034408108201060712291809a0020741506020405031075486010381102000d448001d08a5400b240290302c4c0e14003144840c1c100c410b151190403403034549003024007441c8118000034002c00c0029085050803020500103040c0b90713000e813030006625031440d504c416031384004000650342201010042000d00c0b610303150b8079004102c04220300010f1804458a04251200140003030302c20f96407160003190725203034401b080c024940c0041103040303803549407402481c501e102510309909501c280c000700381c400c502624254007030f260542c84d089000d41c50300c000c000c00b400c0b0190390900703019020f00000f00681c0341c50240b4013031782840c0720150401d91040303040c845640c0100940c051040f555003c00704403282d403011038001e0907611480c0400803100f103414168035510490340d40030034450046034001091740c3d040d403141544210142019501580c1d50003058281c0c041a2070348015454022 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 733964199 1250 733962949 733962967
    0xa030224070f05030411090c09040b04020a1d0301110a11160308070809040608010e0705180112030f17100302030c24070309030203010c0e01080901051506091906020c18060303 77
    0x160165034020710402441d500b40d040340c0c6c00725040711300c25904040d010f0303408a10f140081c94240502480301d1000c4d41c2c04c604080005100400c490709410082c0c00039200407800d2180c40c0c80a40100352140b0390321140e16514046100004c00f4403400c821508550700803030080d02200f500c1034000000310380d00020f0490424181d030f00d80580541c08400314035401070fa20840011054803e0044003034540d41d920160400916000034808003c4074042d500500d90702050041c8088100d120b030103048250146000c0c0b1150741440c2094840d13129100140780040904820801511220142c0c1c1041e40d10079010380d00154410750070302c00c032000d00c00350f0001c0360124440707040390310807144c006000704902030300c4c2c03c1c98a99502d80201c0e00b107170110500500001c088444035000780d600451001d80100664008120901c0c041104000c01c4110715086442180002850040799aa00410f84183d100070301086900c50f130f40d44000b95a4500c410b8201d40a10005040007003069031a0707044502c07030440680a140703411116 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 733965449 1250 733964199 733964207
    0x30501050315180d03021305151209031201080109020a060807020604120509090a020306040b120c010509040204170d1805030613060e060702010603050c090411130b030a030224070f 79
    0x3c0203014070214140440002c41003c11141151316030603100141d071048080101c00c9911803a0308002d000e03002980c5000c2c560140c2ca821030303000c00541e01328954152100c21020b41540315404141d89023444910000c50340c0701040d40034901c06031084481c07130b0450303550381c50a0354800c0003241d0402c090b070000c00010340801d44080032546840740c0c07454034501e01059800014035070f080aa4a0206d20f940c04030030040541801c0c858081c0901c2c0840d8140620700c2c01030348951380c4000ca16002c034100040860340310385640b1207805131006401d50f5904a4401c41c5442c0324180e41e80540c0c414500060b07030340488111400861111907050f0f8201030044e00055032100c0d01411a202d550394215403407641d41c01c0b03000e404141803040034024005603002107421840d40c2042c6180c046040d0701c051003141c80c0420b10000804842c84440441d2043c2e5807440f03c1e04004041c4c50081941c50034a58040c0101c1e560a0101740c0d01041c11144607411900d410a8450301d6241c072013915408a802c84040340e6070403440c1e007201e405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 733966699 1250 733965449 733965451
    0x7120c03090f020d0501110f130f030c09020f072004150f120f08120411300f03130905090631020a1203030e0c13090507050904080415030501050315 65
    0x80001240c070380c040d07c038008103903808240f5903081c03c0c5001c0303400b41401c810b6400c18401400401188855a0b0946e1a240c0c10000548280c80701658005140d28000c4020800e5501d0190000803440b40c020f049030000c01400204032189125a14240c404904010206201c00558194101e0242210304101d81ca5503044017008080d50140c01d02c1400c00c002a40301002003000400400010303c00f410b151404220446100c5149482010b00c40c249002c2c000307042e03010304031031a000354000c00c801442c010714509007003504c0050b9034103000016200c07840c4184010701404a8071003807410442c5940782c0c030859486850940d0051000152510146c000444840d2942e900ba80316410f0848991460380c0010b400042c60b5100c10f200c0ca84050b6000c041c180c1500c128101d840c01c6101a103600c254002c00505070500e0300004181c459a180508400e1000c1086410003912015012146604040c248040030f03400a00c11401024041c80107104407900c0380c010b1604030f4002078000c001d0901c0b11100c00102c070030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 733967949 1250 733966699 733966703
    0x15070f050f1b03040611010212040f0f02041a1005130302040b15030a0b040b03030c0d080912180f151e09030307030815120c060703090503030307120c03090f020d 71
    0x21040c003240d01e810000c07454050030003080c10b0040d55694076000002d40000d820700030740c505903481401000401b0016000e00b95119601c400021080b07000d5203400b05080c40c052002a4001f1303d01181d01c234600c0c0c89a2065004030500b21500c0400b400720500803125880355094106100001510400050070980c002000d50f03040100080a02110300440c405c06800480e10f00d00c9282d00c807840355241c1c0c1460b1196810303910301a4050341c50100f1009506c1d81c1c6507088009803040121000001d903100d20709006410b07003103c030881c1b029039031420081c02c403c248024000041c41840341c940c0e40c403020314180c2c0c100b8000c0841d6520181c10040c285641221019400804040704001041f04903060303901403008101181c801d460303124040c00c2019000c4a84d071416040b941c000c8010003e501840d120001d05c802400c1c83c2154110f03034030900e0b4074040b504405203601c85601072001106000003942c00240520b80710740d40c41c0d0200040c42070765004600703071054890046e201c000000400f4001d42801d00c0d100035024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 733969199 1250 733967949 733967977
    0x1270b0301060b070c03020f0607081c020c070816060201200a0c021002061e070203040504020309010b220507210b030708101a0a0617071103070803070215070f05 71
    0x650b480e044050241d10415007203170b080c0d4040300c0620461030020b24100303561005540c25400e100d0381c2e554000ca10710a90600340c0049504240c8003003041e90395012503818080c00021303180d5846e6103281c45075032100c030244c440322103910441022030760b98814403501310404040303562050072259540e079000310384e40180319280030410f0006c07514003d6203030f1402d021410402c650092009240600114082030108452031003204402e400740a5620307030010560307068890860380182d50303444180d50f01b40105220f40b0040e4200d16001c14181811480146041d8070f4020785505100550703a41700304950180e440c0c0d81d9140203500c0306220030107a072900c0d40714401020015040360645902c40c0f400c03501e094220000303000000e807110f02a14802242d021043c04211050325285c200c10b05144c0c0c040c0000c56458030b40360f20405148005090144500170f07001000301103006680d038a11f002c0c2400d100661040b00d0184c0503104006500c0215920815514071070300d0f950790350200a2000d544111443d5000001c958910 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 733970449 1250 733969199 733969211
    0x70204061409100b221206020715090b01180213090b030c060f03060411160506271507021612021810030f020a03060e06010e01270b0301 60
    0x68996208150152000300440d40454102008201c2039540040881c01c07030300b5030750004004d260b403104242c400f4007080a0104e081705640000a44a401041d0300080480c41c404459030207001c0ea03a8000c214881c01034450001c002c1000005006903003648900511241d4207800411020450006211901c0380113400503180040c1c0c00b00d51200141e9035002503501c150748009041032032a040203803942601050390403904003402d034480d01c030490000070034080c0502d4554107441028590b00003218420b060b08640d5030840381250070320903070b80c05003100c6046244407054541c1120301c540e1089010800110002081c50103d10f081405408030090300c26400e42c890198820844c00582001d10064012500780280d41c103640e0040020210240c0304034030603410800b06201d4032541d44038214003034a4000c0d803090070612480c8041443e0825561005e0900c030701d44241005032a501040e02412a80e1050215903d07989944508990410407803404180c03404050198041c003200d40c0041501d40b0f0010f00000700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 733971699 1250 733970449 733970453
    0x1502030c070f0302062d0c0c010e12030106030b18130203190503120c161b050a090212060f01020a0201030b04060b030403091806050d030309060f0e0a2102030301050108090307 77
    0x10b580c80c2a0220090b030402c02c1003041680810030300404094045004c0107a00301c040c1091840c00d2030140c42c4080e418800504e08104000c00d402406009003004129558003410180100303881c0c1080c020f00700041d080070521100391a020408410300e208110000506840d2484109400f11a040f012a0580284d003011500c3c0040d40321009995070250b4080c0d55104048900c58400440c01032105a25080902c00400850242c103940c1884030340c40194a02440c10401041c2044da056901079070740010b2411011a001701d82d600648141000c110207070880f134a9000070000d41c1d0350603059090042c4d12412428002d5072007a0032056207810042c02c00110301c1e8840810700d2955008035025004a507900348100100401c0e0100441407440503081002440d09001c0040d089421400300502010b8071540d98800380300b6558881c8016601c98001040045088900b00c0d8950b07114940c103441560038010400a0400005132b038120420956000c2c518582c00e05006690380c400182104865200601c071040c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 733972949 1250 733971699 733971713
    0xe070b16021305010909152a03020c101e050103020906061803120c070f0501081305031b100f1104170f0d030522320102070f0507060801031502030c07 66
    0x302800620401268009860400310707400180b002039000c01522304241c0038544001c501207050a04a105e902c0940c000f501300045002c1e00078152100450b02480e442c000c0d99403150b501860b0b01c2c04082d103000e064203040d02a10412203c0c2440042e4004040740001809450000c0090904184000d545801e140121000c40e181c00007420610444800008001400d0784042100c0b9006208441d10000d10508080008002e03580184c6050344c104041020b460410800303005450300311640041034466003d41031215030759206a41c1d02103c80c0c1e81b030306108500c8407801d40a500a460b020007003c5142500d03005020808118000c0008a240201a0001d07030f0300b401405000c020071080e60300401d0508085d105001c5081010001e200640504200d450020f440e200405540e1010f80c5018903180003110400034200c40c6000801d5169407000500c4010040c06440c5003d0b068055411150019140e141c1580c03e54020f0201801c50041000c1075409440181c00465001d19032641d15030400030b07a40e41d40c3d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 733974199 1250 733972949 733972951
    0x23040305070b04030b0c03040c180603050604030f0305100806012303030304110a05010507020d0b180f0115050103090503270909030703022806091e0b01090e070b16021305 75
    0xb030420000290420500801d164220340154401c00c06600e14140342c1c1e504c00784602140302e200d041030310340040c80a807103000d07a21000066402002355401c519061500504c040069410348010a00d800e0100344035034440d002120507508800c0051a0f50303421b00c07064200b000102144c0040e0b0315075404001010781c905002843c05a442144d100391000140c8040011690040e041a030400c48140000390250369086d210181c82c03600b00d1b071014180e4813000d10b11107412203400940c5107180300710403000c18451015400511079800d0000840e4801c0c3d00e52004605036080003002814030b90041c004c1b2010b0401401148120000310242c1d0814200d5980214480079011103001d03101e03802c003080e01402e140d014400c00e080d000c8504a00343c004810160303194801d54281c40003030440c6540710150400c06c0100c9040c010300c0f040880d09100718801f58900900810405d020b019802d03411300021060a010003d0704100b5503407401c503054200710309071071540004403101c05d050381d01071110b9815129540041c400d80b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 733975449 1250 733974199 733974209
    0xe03040b0403050106080313030b090a05010e031201140f060f0c072715150c140a02180723090a0f05100c0b150d0605270109032304030507 61
    0x41d884601d182802400c4540303550204185030000c0240401c0300d81ca40e6001401c0d240d00070040c00302d0f80c03904400f1914007243d02e280100158030b841c0b0160310703072007002001c1c200725256030520008aa03220620503e002118040d01c0d40c0110034290500340b00c2c508640509550041d144c02c00f810074440350242e41c40d0604650140703521340201d45502106040200f5840140a02035400344844842000300d848200800d20440861038545204511078500c0b03501414040f036081030780d1203080c00440401c01c4d00c0d04e4654000724424030b09030b842851043c180803803061250301652201000c05600c2a64108c90b0020030781a16001481082441d600360355201000002e031002c1920080e0300380c01d040502444480b4201d404003880307a10a030a40c0059092412140d001c81c20050440b40701e54048041000058180b00c001d0480381401d0030000300b2a1620412500034010080e191041c8222304c00060803505150b40207000500c1c07801040480c6080030f40b030702c1c045800c00032556107060740da5201c0783c0c1086565040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 733976699 1250 733975449 733975469
    0x3070506010f06120c0c020402090105070602280206040b061c080304050109140111070f02031905010b0a1d0f0c0f07420f0609060608071d03070e04060e0304 69
    0x5011459000544c240340c400524010000d1500541c0301901c48620703400000d100341d40009003003515901c190142ca6500c1c0d4085020354031108041c4043c4110001c00c058020402c40100740707907044602c0007a06901a581040c5000d6850700d0b000d0520044111120225111400390000500081d90140040d40f06501500c00011202c2c414508101e4180d00d803600100168100b005c601203504005003281d1030942e001401355041c003414404030b410501301e2444d900c1e9032168601c80e27409000703041d044514000b07400c41f501d64001c2d443d0404000d190b00d40618650360950020001090b10a050600582101e2000c0145003082451951003216601410b0122076400b084841c0280d80044001c0089048000724414451140f034500d001500c2c000403500241d489466000484c010384c6250b10250191181c03010902c24240c940710041c00b500400c0c5c2c2d82d02c00058800918504400b081e032941200c21900078003420b0794a1804041070540c2e9005407065500075980c10031000c54000401c002c100901ca80e000f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 733977949 1250 733976699 733976729
    0x71104110a0c11120d080915070c15090c0e0a1b020706090f0e190b03010c030b090f090303151f0201060501140307080c070f02030105010609050f0409050c120307050601 74
    0x10304030903d28075843c8902d000e00869900c3c0c0f40604408101901c1e00f0000b480d05920580e2080c6155203400c2890801014030800e89042c01112940004019008c500400c6101c0e2185810181001202e541c618080c2500005a106100303c2c2c0107400f18941211502a01050180307030045039001043710001900090380c01030204008a5400540c554010310807843e88101c021315044080381c0b460300003003441038005034149544441030461b900c5502103c0b00500208103d07613500501034020550300641c188200d02034000641d0301045801c615100306240d002540c211384500c005d205221401d03043c40d83c0e112140d0b0010801085a802080d42c5c41d0789554004281c0b18039002c00902280c03040b800b0148801d008000b00041c02e0b0300f0038409a0000b104c650516501c50075402c1c19050b541920500075030650819000085a6034080c401c801a01d501315074078040d504211003004126007000034000c0090b0010204041c203803501012078115983c0340d80c15245049a40c1d81c4043c01c00034260880700140314054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 733979199 1250 733977949 733977953
    0x40f0e01060b07021309240f0e0a121412040f0201170c04060c030c050a1203050619050621040501020304120302210405070b0c0105060312040b071104110a0c 69
    0x10141d400100380d015030041c9400e1054012134444442a01a840f005456141d001c003004250208141549900154250084540c440300300203001c0c1121001c9049040104418007071b800480c0801400703500c10841030580141d0340d0141c4108400c840c001c80d040304140209403800071200009c5129501c00c0b40c1c5052864814030001d0018501803035507008840c1800d0030040300b036814104a4041d500282092102c503410703071404031a0f282c0250001807050140ca256181005040c0c0c803031031900d0040e520b05000ca56221000d020029100e00c60008501e10b10400422003030906200a090000400018a40395203000c0d001e018800000c1e241195169400002c002c1844203000404031650305a150070741c90161500c40d45a540308001604116190700c03400402c00700501080722030000c1c03e038520110b448a15010b00c86008007021030341680a8001c0403c1510b00c108004120344c2541d00d490201402c017009134a80b0500214054200e90f0800d036a14260582039a507040907055944980c1d45610b0495998 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 733980449 1250 733979199 733979201
    0x5070e0106050306090c0f0717090f03031c0209130c080a180c0918210e0405220c180b0126071404031a01050315190218040f0e01 57
    0x140e00c0700d01009400d20900c02c1c0780d07403002c1809400071900b9802d2a01e454154491326524807071a0402080f202c00c0c2c0003201090300d11a400307011030f11000c481c011000c01003401455182c0c45191140c40b6015500100311440c0d51065015183c440340c05450719400465105010045440e0b01024501181c01b8070104102e186260042001c0300100508043c002d41c0316581c1c1121003200c502860520b1521a400118401d1032054a02c162030b0308080012000803c1c98140c24100481d4031a4000044840b28911281e00341030113198001c0842100d00c16082c82c800f545000f1140710204104c80310500c82a001800c03481c854444400c048010800084040a83c0000f42c00703052200992a50580000c1503a00715004400c0983e41c054511304201c00c020071400c1d03035840640305e65040104441704078490145102c0f9004400c0c2e05072001582203c58000c10511200607014048648841110311101e00f2064a80640c000d003510b40c003210111400c5841071000103044e95254441443d0103507654070065003007070007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 733981699 1250 733980449 733980451
    0x60330040f0e01061b0b1f030606050109090e0303060409150e16210602160611030f0f0108070b070c08101e060810021b0a060c0216050303031602011805070e 69
    0x15800c0811040c040d82820700701d00d641c040303409065038240f000010311200715403c800907c1d440041d5580c00e203a4036464088000c0c1818001c49000451403d0081125803003171280c040c04a04010095083d070b61003c0800014182944d01101c41c182005100451200f450190701c5404048802820342c0700c0d41098551200407081c0c0c012030340100182d001001c5590b40101d1024015004817001d83d4448060086402c02400700000030081c074903000c44d401000c00790780b0165006407100824400c4684494a00064121080c024420141c001540411001001c40c00500c2c90070712405d0304c821a5a50380c2c030b00d241840a20b00a02c50301c29100e24038540c0032130b100340260025034080002004520305102c40982d4400b60a5a1201c20550010b11549034107004051402c10744132100032035090b03c81c9850000c0c05400c10f9500c80015114684090b8071103100041200103407407010740210b043d5036038030140d807007030003c00e40c4900709556841c3d04241201c0d0800c07190800141c000c80003040c00c246495012440c40380 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 733982949 1250 733981699 733981709
    0x5010201141303031a0607140105070302040302030304060503190207140c06190509040b0a032009070e01030c0315080d0809011503022b0606080f06060330040f0e01 72
    0x8050300030040c02d800002441d100850b018a00007418482107656000142c12045041d540090045901003c100c0f07540c0680305000c0e0048000c2c0003503104c2d0007056003640600e00000758550024403060144030301c00e8001e150301110b860806030700d03034941c85681c6040340c3c48045c05503000000095242a000010003074280c01003429030b80c1720f00d4140d43c80903070500c041c0300520f00c000304040042c1e9401d03160f0340d60f000158803960040c001300d091503403490810a6902004c241030004141e40c21018041c0c585a4442446035403030740c54900c0d14201c900c3c0118008c2a84e10800428141e03112064441c0004202c50b01010b00b504070020100001c0c14032024204072001800e001941c0c1c1404d204545c0c0d80a554440e4013101c2d41602e1901031070a0a207146468021110b82c2035510301c610440280a2003041e0300503000301c4102c5025144580b401c408041e440d41d404950654255020440d01c20003842c0310800010a17490300301c4a610f03101c03a1100300c0e0180b544598400078544201c00300601c10003113400901c2d8010301d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 733984199 1250 733982949 733982981
    0x207062a08090717070302030607020c090a0c1b030c050f030a0e04021303240c02031809090705010e03070308030f04050d1701060f090510020d08010803090109030f030201111305010201 81
    0x490702c400420b6440300b5a02030007000e04030410825890110410211010b0b550046c1640d14a1521800003990781c132000c00c07010311921003980880d6944143e84103042e0300d6082a07541c42411500211380450b04151050304404015400b01080301046052050319880c010f20f1000d907640390b8480000600d0b1407040000c140c4260f00c104150f000513017460342008222580010151010450601100d01a481c0014800302081c02c0c0000765024990200062004001c1c0a0040824022110074481d174140c0480d407080d020703805204180841e60040e03d0300003404500500b101e04ac1a01d80d61000003540080d01c48009028008003032000b041428031102d10102028a03000d070909d9528284200c0040041c4155418441d203003090180c00b51050350306101500018042040010340740c00001d40e01c4010500120008425000101d00d890010040b5104000165a140b14890550b150352020044c910411400c1d59030b28106601840100030141440701c1c99900c10402c00351909001a00303440100040031a80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 733985449 1250 733984199 733984201
    0x3210f07053703050402040b060903150a02091c0c2312071809021f02120706060e010b13060509060a0513050a0303270e0c0304021908010c021204080304180207062a08 73
    0x1352000030704140a02d01c40040008141c0313503408500c00070301c9503f9140d60803041c403510f01c40910900b070946407031140c80f079080d00306550340d102d00011034452801c038200c100c8540201c40016030b00d08928a402e241c07051800b6525025900e2051814040d023400516081d640c4540120096240030104244901381458490004d000b02420082d2105a81002c48003100c4000c180d10060004560040d4040e004d0b01561606958460740c01e0a02608005c9812048640030000412240d114500f80d41041c40c000c0c10310341c02c3c032105034825601600444150b0807640e184402c0001d0307941e82d0048480041d40692140e024004000ca40b42d840207081461051000c1d17a441c000300f0022200402032980005100b82c019225100d602c001292a049009000d41d0381c02e00410110f0350180c1035104034821891a0201e4188080d0b11444086500980c81a5603454006110401c02d010040c50203000404050500615000903542c1d860208c031171400d01844104981c8091000d00103040840d0100d104150801d0300ca1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 733986699 1250 733985449 733985467
    0x10c030e120f011d06040314090307030f050c040903081512060f2406040603091e03030e070501020f0d030203042609010e040513060b0103020c03210f07053703050402040b06 76
    0xa94030000d84001e040050358102c40c2c0e6079150b24409d0304c120482c014142c0b1002035403410325420b81d445080d010b803907602682e00540e41c14035281c0304031034010b90f05482d100083d560364024000045c000783c80c001c1d0450420b442c03d0321a880c041c007a01d4800c20851100000781c7c18500d416805c42c40c9040081814001c241d06a0100c0d0f40d1170314107880c2110031070714000c564001c07103180200040540300040f10901c0d507500c1084040607050340001c500c4800880446004d181e4442c01260348840c51380540000307400460323079400e080e03109800540c0e001d409600700d402d804a0004e51030301424a80c0c20007801c10540440c611100c0d40e84020802a0414121410302c964100f170030340385a00503001c0c000200840d5455160a415034000c1d010364003a100000c060300d0b101c0605005404070f00c40c1407400070005107903030000282100b100718900760044172941e45050510410381040025100140d000c00d00f90303503048081080c0311800c010300048202156038049021f040a00c10301c0183d0740840142441500b080c020105 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 733987949 1250 733986699 733986703
    0x221010b1305040209120a05280b0105130e0706020f010507030209030d1d06130e061005031303090b1c050c03012106060512030415030504020f010c030e120f011d 71
    0xe482e000c860041c0c0d902668000580a036100c4100d13124680078240c00700d814003401241c108040782600d0200720140c02403203501e440400d85038000a0040d200740c00103100500780002c800a01082d820700019101d02215a4030386405102d030f002d5801130780070760310307004941c5000e000705e54000c9032500b030039414990548002600c40184501354810020042c12907100740041542c0003084241c06441ca075500c030702c13003900e00c10b00208a028180080402802084072030400041004001055a0310311382951101880001e441d01d649105601300003800801241c8552010010a030600242048104481d07042e80d40d0383c10748000038403060000740f003440104031041c105800b100d22068040f02a030007814180c94080d00528240c0c00254002e004010b0b03545072128000300500c2510071854502e5002d80c00200300318280c0c1e404580007034009000e1201d401c0c2c60350045045610181c880d040203003040500c180420020b60703680c1203c282c03a5000302400c40c4030000a20940303001020901003000302000c580e4200e6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 733989199 1250 733987949 733987987
    0xe01090b04090b0c0a0c1205220f0e370b0f1f03020c06040609050613150e0c0d061a06040308070b070c0501020f190e1e0103090203010221010b 63
    0x5521000003c117043d005218003003100216903c25a10314144814035070040a0b90040c5c2d0f2032000e2410400f0900e1600d114010580c02242c4c00c0c1c0c0301120415007000e40414a28901800c6440c86c064000a640c20300382c540310300d194a0b41e210312800b00d9494a034105141c00d40c4d901d054a50300902002041031110349030110303c201031541c01c0305082501a45108201d00900c0781e05c2200d03019000d02d0003444108034080c0c01040051740074004803000c0c1d468002503c0805070b403050004203640d4410b500c41c1e10070350054001e202000d000340300380c8001034031100204016883c28881181d03119a0b40e144001d481030901c020b600300002c151401c1d8101030071543d505106d03104a01c400b41100000e0740006803250b1040c0c0600d080907510000a640707880b00f8450700c0310300350000214081c0da5503094a030721100511030044c0b07a90a0720010541d894a8540f45e0030010a8411405660304040d00e403003006002d038809000800e0b0402c208120316640400568503203080c0714040e080250b02c91300400c491081e4030b20b001524 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 733990449 1250 733989199 733989211
    0x91d0106050f0c0f030901020f06010f12111003060e0112050a020910080a030507060c0e010e090402061608030a06080a050d27031104060b09061813060e01090b04090b 73
    0x81c550b40c0d03085400010241c003600308030700c41c1807081c4d0240f249004000b10107809440400e8085514180c000340b003042e1180824081e0540070350341a0300400003400310112140c6043c0c02090109020780702180070034082c04003811140c000c1b907180e4104000d1003400304212401070810102035054455540d460f151507239200b0720080e2145440300301203041d00000490140061140d242121040c41c45450090082d4002d20070956900785844803050b1128003803003014070114016503c24260300f403000e0811120080c080c4c81aa0001424070001803d003460840c013020b203a020b150616180d01e030107451181a03401603042140316411420a900019000180700c00e0101218100301d402e032550bd1045411515030803a0119131003c0c484000014003500e0655014401d2054030140000ea0303c44030310250074401d075280740742c10000405c00d40d00b2864008104601d0790b0401800d15040e42c200c1018941540e456822440d5000407200041020300c4961248000001040c0d0301403207030424503220001c1182c001400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 733991699 1250 733990449 733990457
    0x90904020a091b090e1902030414011104211a04030c12050306010e2d0301020c070e06011b02030604030309030e100801060f0201090c090b010908060408070201091d0106 74
    0x81411551400071031800342100792020041080d90582c002c3c3c0058480d803035180802c1c4c43c41070101d1001d0359904283d1007a51504900003208107038558020080d03200174030964500340322086413001d0900c280218094020b0404441c8c4d2a42d0402c14102c144484062004002076556040b910004450202c0c078800f00c00c05050811065803241800d41d140040784100034001c810440d602c4603503940200c003560207040203988003220515114103000000303800e640050070700008005e00781c1c1005d8009070702001c13504001d4005410450a00c100e0f61515080780c115001011011080020b00d5034010100030b0300205d000121605942190042919600c020307201030f04140c0c9440002c01414041c10031034080390300141c450300402c945124000c1003d40280038200c00202d00e031403c110118414041e1540c2c0c1500000d40052252420202c203004001310f01c000c6050141c022000a501d120074007009100302d0003120b01c0d6503289201d100040c14104250070000302c074562184203402108910a95a05450180c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 733992805 1106 733991699 733991701
    0xf01020403230a050c090619030c091506050a030b0d0b0420100909050603070e01031101120e0d1805100e030d09050306070e0a090204150f02060106050909 68
    0x2601808951040c910b0080625017440d031980c001000414000e403444040100100046030b2740e0040d01c03508000d5000b040040d219000b100302d040030911030103840b1803d105014009009203c0c00400705070781d41045100304d88541045421050304810f40702d505113001d1802011448102d40c010341c9035210440122241e0612802203107400c5841c0c1c0350072448604003659500240b400505055051068510000e50340000d038400d54082c0d07004078400700340440a440003401d80188802c08061052900800e00b400040210f48402011901e1038403600c2400840a4400060002e8000d00d9000c41d010021400c07044e00010700c00e41c090b40c190103032034030809040c200b5a4075101030302c949601900035000107118148540d098a00024004201c4420740c0d07101c60340c82007241c21580140350f20740e1300c0e0610411440d40000480071080400d03c021315056041090040941c020b040d070722405407036044 = true := by decide +kernel

theorem cover : BRFrame.Cov 733812949 733992805 := by
  have h0 := BRFrame.cov_init 733812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 733812949 ≤ n) (h2 : n < 733992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
