-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0173
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:15:25.606564+00:00
-- url     : https://prove2.me/submissions/d8b0b4c1-84d5-475d-ab83-13f02add4bdf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 30935257 ≤ n < 31115113 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 30936507 1250 30935257 30935321
    0x30b100602030d0b01020a0204180303050f0709091505030a0302070608010603110a0513030c060909060509010806041e020a0e040b0601031505010f090b0d0b010f0203030c0403020f06280201 83
    0x703850f0f080840000d41514070302c0180c1c02d040d4501e000a50080c5000d000c0c3c0100b620640101d1420b074000d542c00c11043d40c94088040d02c4010a4600c2070201d0900741c401c012030455030b08884500c1041c1114104125a5203001c030703150a1000d9811005a00244414840c4640c40800180146042c1c034050150031011014500303a0f01c01c044042042000010307110381058030030003a180c01190301030611943d8039a00c0c0c9005151062500440720364034100000002c030741c40c00b001c80300d0584042d50301510480d26140d982c1e601310039400404840d04040e044080002d030307031500d07210b00c020108102552498078180c900080e0003640208010b051500c0e0640c03807a50300e40900180d006407042070a1560088030111402d40e45107035650300c408040310000078268048911900300300d00511083e2107810b0300d0f40130b9a1059071240022503481c804080c09000800162421081400d582e400c0600303c02d20b0b190000441084014914604d26000d00364401820ba480d80d0901c114903013000e000112911507210346e004810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 30937757 1250 30936507 30936517
    0x2107030603020f1002240910060305060705070c0801090b060a06080403020a120e0604090902040605100503040602070305040b030f090708030a080c0a0e1806030706080c19030e0109050106030b10060203 88
    0x401138403400e006100c0b1500030002c19400403140d10103182d00c510000d29640e900c20049400600c06c4c010711100480351030050042e001a070758818043c03c0b11b030fa14000200d40c04d40040f003069901e0341000100040302c210a20404040c0ca0240007007040c986448820300200c062680c0c403480800c4502001c100200b031340414601e08295100c40080c0c2801d1074142d0032501460780b00f0005030f002e000082c3c000341002095010302c011034800d4030140700e16643d4400b000003140d155065107020440400c000790000b0001c0e4001c0c403c40d803003820b0050415407203a039480d210390400c5903540c0e407120b03050041c0a031502c000c201c0000103140a80c011845e00010003c0100300c44c03c081c08060034503c01003404100d03280126800c85d02044040e0003420814405000e00b1f5001e0760940c1d00c503019015420020405911402140380704999100c4120b182039101041241900f85105547d03042603681c3e074245810420078000c0c9622980510004601c0d2421070070401c10b40c03900035241850480c881c0904000094010003520 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 30939007 1250 30937757 30937759
    0x603180515060303190203070b0916031101120507030506030610060e0f1c030215010b040f030f020a050a2c0708010e0415020d050a180203060a0b152107030603020f 72
    0x2074190344402001c00e10354040c00d2400c01001101916003000a98000064030010340500d220085540b90352540030f840e03440d41d00c1c143d5000c1500356424008100d808030386450000c018507003020f00300c1c42500d40c030040300d10583d001c000094551042c0001440c04120107908078510b60a090801480e0040240106015603c0c00340154003500c03d90255940341a02d03110403c0c5503102d0902240200d103002500c2c1c0700e1764964504012059000860013806000c2528160354000000302c580c5411a00c0e48070000301c0740441203a114900306004241511a00010b0004201009402d20011290801401840c00a140c0680c00180f20001c00c041507902090703003411134140d5030100c0c1c0d194680d41001c0000900d42d84400e050140005800b41044d4070342c1d070020384a408640ca0030040b0703980180741e21020900c10f00e00658140e1040300454105103982d0300810000000500ca504024030b40002c0c050b098120a121070880310188030400c2940d060040090f41c401a5440c0030840c45040d5400240c2400c1ca2040007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 30940257 1250 30939007 30939043
    0x20070e0601110f011812020c030703060207140111130605130504050c0f0c0a060605091303080703150803090102070b0408060f060111030309010b03071703030a0504060b09070906031805 81
    0x810622003090005201d4044043c00038000d83c800d00070200315080c04da0b0022603003110301402c04180b00c0c1c0b0200700342405a4008016215442c50360f2120006500007150a40d2105118550600300030024414001c21000f0304500c251a0b0240d106000d02e803100d60b901c02d60510208111003d0b4201c813032a2684103076030046800007101e48504800d400d0038041c082c44180301d554005101c044020740000c034148024840c04092084070340760720034440d400310195480b500b40800c0c130f0740003400280101411907200c0c80c0303880c0c00905118881e07841400100107900ca48902d41000940800c00d5a042c807000000e00800c0821501e007a103442d607401c0e0380d80c0b0010031000c84000880007003200340c0e02c6010142941ca50800c02c4986038140f02181030300a00400701641d1081c070400a00003010900d614000054800e00740c0958216a00d1083d031f0b00140c0401402107a0a9550304220405a074803083c08500030900c598904010b9802c101c40501207605e00c460f50a02210054100000501f002034140c1e9000b05800342 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 30941507 1250 30940257 30940277
    0x604080a0302070b010608040c0501110d0e120307031809020703020709020f12040506270703110d06020c030a080907050607150b03100209010e0402250c09050720070e0601 75
    0x890090243c600300909441400000042c007a503c0f0a00c24050ba003d165481c80040e0744000645242c0903620b180010b0ba0031041692000b180608051013614a001c2d015030300e080440c8000c9030860313101c01ea007100450504004200b110b4000030b1500050400090f0071450820a0b4134060b59a207828401c086070b251300000d1310180240e048054600000302940d600800c0c0c05c052a109880c0d520450740c1240d0b0501241c500c03481c061004542400c06c00444000d001001d0842d12032440d0b016445203000c4c1c200d2032144000000500920084c03c80d106407c0107951a05e665400c001d01501019103540000d90000d181401656910b030125603881d6805000e2210f62800c0754882e00c094900030044542c14000c441c408000b00005800614003003a00f40e917449e400c3e00d00401040708900800301e000e001280c04200c1c0e44103a117400300841415502954140c00348a40e035102c50815038400700c840400096a80081460307095941c0c9015414840030300241a6403410042c00e401d4050004000604104443c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 30942757 1250 30941507 30941527
    0x80c01060806072007061b05030c060c070512041d150307030305031005180402040b030a05030c0705011205070806010503060a0e0c0406080c040605040909020a09091a18060408 77
    0x11003240101800029610350740303021540030f040f002c2141c020b5014110400007095034840081500c505a403840c0d1201d51150300c00041d840c90120100318111074900c4100b1602000107401c01216100d6a44110695600c1005290050a00840c25844012980c084c0000c3c070032152040f0f40040d1483c644c0d150b804555a40080700881480e100c1d00c2d2903054001e9070400b1050581c4400114880c00501074001440760740c500600c52010300307000c0380d041d0310f184010102d401458150003011050304014100ced1580c3c0103a494460456002051490380303035000303070000c0140d540c000020441001182104008d9468002c0000d810051300401040c10410000300040d100c0d034946807100080c20b0980d24601a80c90306100d104402e50043c05001c002c10034200014440741004000c072401c0d507200e80d840346e050030f1500d40d050003d4004183c00720380c0400d04500100302100706100f111080c0e4065006480c0684042c0d030103001001e80940400420b00940c0801c0021130b40c00506682c019a011203100c1d66004c400c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 30944007 1250 30942757 30942761
    0xe040f06051c0c21020904021513060f030506060d091b06020102040801050108030403120806041e0209010e04061409060301090b010f08250b13050306070309050106080c010903080c01 80
    0x6041a94030500640d07403503948a04075103203002e1862040000b101c0b0b0030345a01011403002092083c040c400243e5a421500508244600a411505c0500308070303800c2507000703001801d81d004440c40880d4803050f00310030032110b40d00c8940c030f00b0209401d06041000c0d091100200f0150b00c150907240e0f2203284c865072000100038645000761812829009090f4041d921440b00901035405803041c00c501d5802c240003c54003080200441d8101e0b0340c02003c0742c0c01c01c001e121056540c1c034070089c4802d501564901103d000c045422072840c2820310310800050b42e0b46c1100001425a6960b01107040c061494480c040c004500403540001c80700904030b4804000396943e00019014010340e0000030b080800e0f000001034414581013504040d9610181500d001c2c0007485034401c0c1103810002900c410000b2914100800076100b0000c041d48002504450b202540300d1021a00d03201081c2c1c0c101c2e001035501c41d40182408000c2c401c1c9030107000a440a440135042100c0001c0c01c0010900002d000007000164405813541c0075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 30945257 1250 30944007 30944009
    0x30b0c18090a09030305010b0c0303070f03020c120921030301050103020d0f060305160603020c031903020c0111040609080a020306010e06010210060806061f140901050d050f040c06020a030e040f06 86
    0x600051841c54800e410700b0141c400d8800c1240800d007050001324004400b0b00544108101e620300560841d0b13561542121100d444900e01000c0c141e007042601641d04c4140701016400c0181d89403036580d65488418050a07041010000481ca420440342d00c001c410080101d0341194800d103401344e1130748428a2084020210101001c0046250440c0081005400b1075500c9000801e8005164002c0e03807034009809074405d1182c10b403c00d800401a10465008842ca14648007089141c018140711a4034003c908451284402440024020070200541a032210460000e8100040a0100d000c503c1e40460f5a40c10103018404600d00d0405c0004d182e07074420801000c80c1c41158500b03201c00c0341d5903902981c070345000303880e9030b8000d076840407a050038812000072004003811207907980d038400c0c0c0c61149003441d50341100b102e56040150812078401c5004080c01054010481d400212003181030916002982c03100a6114400b550810500c1d8000309030400141e00c1d440105903004118004105019001400342e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 30946507 1250 30945257 30945259
    0x20a180f150e0112150f1d0108030304030503130f02060d0608100209060414011b0b010311090402010206070807031104140406080703020604170106030c060807020f0f0d051804050103031205060109030b0c18 90
    0x1091031300085640d8a036501d40346807031f103228070300d525030342c035510f0490322444104c4016010510410100f01d03120345414005c10b580d03011301106083e4811680c000348182c0e01c04107044140f80d842d4030050001000500440d15244c1d0041001c5162240c6800820041d003d680b00304d03500488604090481c0e40d01800007055200b00c0700f8540746022403d031510100410b802c0c0415a18055401c4074020389040c4002d00f18044e070740503002407425584a0030100e644020043c621401c141c0c4421610031601c00703080203007003d00420030040452140d444140811500d160b444640c6941c0307e80410409601e5040481e01541d1500894000b0401d842070001c0c090400741c1d00c001e0030708072000c200048055000c95200c0c010a8240d080d550351140d8420204e589039101c8402941e00e800034210044000d018800500d2407041030140d180c980d0003803e00190442c2c000741e0058021070a502192420000c003403164a502001c2405c00b44211801d54441501e0100003c2081e150600d0004149948080c03440c10384e000a10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 30947757 1250 30946507 30946529
    0x40501090e13051204030c0605031009020703020c03160e0f01030b0601051605070b03191413020d02100206180607020604021302090d0c080f0c06090103020a180f150e011215 76
    0x21310604480099171052205603941c3c0314868010400c0b6201c0d07412a401a0762440540700705500300400e26000354030804080341036102e04000c000d0303162001c3c04451040251140346072540e624040c05000b2140000b004141508102001800080d80d1b02e80c400303421140a00e0300310b441e1600c0151083c844000200301800306e2080d06400078411040d02c0040d4070075041200c1424035190320038026400e9a04680c0381c02d440e40c4004000500f00c0e80e1111084980c640010400501d5920b5900802c1000c001040f8800041e00114204600e1692070032500389034008090003400a45441c0c00f00039100da10151000b407048030061140d842800c280c1d01a0303001940014540709500003140707013469401c4d205208006460160810007454880301240e00d541c52000070b4681031800e085000110029070107158080c0610007403009229010342003100300400340110800903060913003044001c62501c22084412010418222000501c0e66844a2000017100f078005d004035440c011000d00e40c4012840b03070440c20440d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 30949007 1250 30947757 30947773
    0x708070b0316050702030a0b060a0e0f0402101806050f0403062a020f0c04090f0c030305030a1401060e040507090b0d02040510050304020603040f02040f0507020d0e010203040501090e1305 82
    0xc102000440c050074400504a6503484241d8007550140035000019505800500d5000301041840c03c4aa92000000b0b11401c0416101c0b5020f420540d810707108100520809002c1108504000c59070640d01222414116000303101e40011800711680740c0125010841b011850004c41540171007074078041c5901403814460070906100c8003004403200d4099100304040a260003d00500204030500980d82c0d9202800340390f4502c4060001804080c001250215544690f00b0041003840c0d0110020b50710943d5030583c0d90078107554580546900c0785100b00d00b03d0080c0010004e09400c8400060441400c1c2d0b00403ca80d998100240d846129681c04410b6505001510140d010695070082003958001c0701c1003802d0700301d03034101111540000c480082d00082d00308045404070ba4031108055500c0d100a0011501c42180c10b01d0030181c0e0015103000c0701580c00510b01e41e010341d81100354102d03101401e00c000c1d81010301c1c16000070004141807240c850303100d039018003003807504000c0c04d1415006e5400c032045600c96 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 30950257 1250 30949007 30949019
    0x209011416050c060a0210090c080a15050a0b0109061116270209060f1b1608190210050d090b0c1b010204030804061409040906050601020705060313060905070807 71
    0x80c0c00040011616400398048070b21040c0752042c266070300072a09034010704132487c0080d0810020000341e28280d491407600762000034034032010400030150a200e130401d0256000007204a03000e41e02c01603d42d06c1060309041202583c0c0c0d90081036041110034a291000b4001404040b03142490314031415030504002041d4082617164041c86240003101c83c828019140c0307007a00d03005200b2402038030350455201c0780801c9101c9000c1000406091070b003a00414030103600700a001d043d450103840913a215103890118000b04620030040c0701190020349004c02e060821125a4001900b01c000c1410090a002010413004107480155109040c0140d01c99039000c80340c1021017280c00e40e500070061840a5065814200181c0344060003901c1c100c944c01000705013080d043c00c0080d1000c01d0600140141e10105200b1144a40d65a01801e90005d000d088005140d06041000909001c0182c001e1800f40000300240881c00703410096109807141c0000300020f130117800c0e1400c1801c0c0120b5901c60b00061050030004542 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 30951507 1250 30950257 30950287
    0xa0c030e0d08191b0b071404060c03120504020108061201090204020313050106050a06051c020d0f090c060e0105190509060d050906150325080d030614091902090114 72
    0xc440342416095110070a084001c413181d0b42124080d110b4030a12203032000000b401e02400d1904200e00703080c81000070f600ca02e903183c140c0d04070f07901007000a12002201014160060480900070128843c00d101c1494203400107800c14402411503030041242d45602c401940082d800305d208203a0007802550f9904146691030349001c02c0810581d51946414070010b281d260905e0b080c4200d07a429120310b8284265800803062120850311142c240742c0c0c080241c0c125802d440e06c603c12071030a0540d0002491001820482401e0000340c11034018400121b502419a0780c03c581a1481020140d641810300f241c0ca140465050191a030042d42060700850402040880d40d00420b114140750310460700d45a681d600d015840ba4038400c03034150150802004402107410803c2004c126180080c10700e08495a80c6250518180c003202070200000e54404041c0b2507001205030001c5060011070f03070400c0b05e08003000701c0f510401d074031223441b1480369001032242d007164050314500c044810700300c41190f11002400d47c0000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 30952757 1250 30951507 30951517
    0x2b050106050901080d020a0f0c0e011706090c0a090209030120070b070306031101030e0708100213080607020c06160629120304091802060304080a08010f0503030a0c030e0d08 76
    0x2201d00c100000104d4040b07000280340e00e4001c81540140060a0241c81d501040701c038081c001d640907521074601141c0c00340d002911354020011003440c000307105c0014407605d091403409000000160405c5032903040e1907491064000940b0714094006a640306d036400024010200354940700903070603e500540e074021821740060240940a03075411107c940c0d40d003408400b20341e01400b00610724000110b5902040d4866413010000080c0c0204590013562a0014145000644080003007169000200b1628a00005107008000c00b00d10000700400d0404035070103911003150030b50060242030080360052054003038121a481c01c0e82c001d01c041020680380120380c030300c484036141000f40e0807050b091210f003d400d000300c0000c09038500704003550400d0f040c60340400242c40c010300d5004803d8140103040e000350b81d4000045019078820288a592500a050080d0000302c4c1680b0101d0b024110400400007500d000c02103c2c204e0f504e030b10300450345152610b015914a2451825240c129900c043c1c004100007032400105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 30954007 1250 30952757 30952759
    0x206010609181407020102040f060e0a060e130e0309030114090303042d030201060509010605030f040b0a0207051902030105070807020d050a05210901051f14040b060304030e011403040b062b05010605 87
    0x851781e19140c054500351042f6820300d0300403c2600d02000028400c40c0e03440030b22517005100042001541c25240b0681c1e02c4529914419040000d40c0000c42c54244260030007600350441c034905602d00071414030b460b408000c202614501040e144901003c1c030707000d5180c0c1081002e2009007030030101424000d008010600032240507440c81c0c0000320701540030300c0980c1c7c454454560900310341e130b8a076542c80f0000480906800002da801388507c0300041d1050100c4200b0320158a11080c855a140c0101405c0d144094100f506121801007440221039011030002000d24040c1800c0d642c90015410860701480340128000e4102d49061031034800c1120142205c0c0112200320080c805501d900d0580c4680000100c080c8030031000d02d81040003c181d4080c081c9112642c018000503441c4601001704106910488003100040c0140c80862420740e0064090069a881d10404506514040c2e5844201d058040d041d03078401e808005107c206e401d0101682d54120015000c1c40c50000d03518030b08140600628010701e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 30955257 1250 30954007 30954029
    0xb0903090405010609080c0f030c0a060302070c05010311030f061804030c0c0605090609090a062105010e010c0e04240b04060306080d020601120c031b060e01020601060918140702010204 81
    0x2481300e04c03420950059400400c054211141c0ba5000c011a0b4a58a1180c64041c0a0020f40c84250303619030b40c49800500703150700d016a841c0c0003031410007001185500600d051614080720002031103441c5007500d5211a0a0070080c0700703516040001348040d88035806212548450700100000c140c0d02c001c181650a10400020324003540714a010b032002d001d640403c9030003107814000207841e450001140e580012241f40002181030712071403107255440050b18040310f180300c0e0401c50010400d091181d108290404002089003a0302031038010022000d0148503885651180da80c03180040d00d1081c0440300a508081e80c5642594030420312207950880d100e00c1c1e020030300d4070300300041c00f03c40031800760031000c00b80d40980880d030309200d001c1d04070300c00304e02d801e403010041d40c0d001000082100c2c100900004102e00e41c0c407151032500c40d000340280644800c0b5030443d080480100303d100c1c1c100b84644207130741e20074210002c0a40300107030180c0180040720360005000010424409226019801801543c00c1c03e810 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 30956507 1250 30955257 30955259
    0x809010e040c080a020d020d0c050c1002041410021009050606010e12060106050c0703060c0201020414010314040303050a020c0601030b040c060206100603180503120604180803040f0f0b090309040501 87
    0x40104550070750b0254030100b40d55900095141240c4d5005100f2072940040c01402d03c03600303038141c004903041c02021102040001030085107520040010f1424a1a0382e94194681070400100348480b600841c1c40d50300034910706029868450007840303620b00111000d40108081200c6052059580e04c041d01c040780407a01540c0440d8103414100322000c3d5200c902d070020445030346800d1088801c0c2d40090781031241d40c003d01a012000401d18040c104d15031060368005601c07903040128194500601d00101ca06151805c19451003503850031074a01c1d406601802d0000c0d55a03140b010200c06440780d100d000002d80140c0c80080700308038002c45458021800750303140c001069140c04040c1e0707031101c055490350861011003d0402079244030780c000c12040c0700c8441040c200441160750307542c40c44c1c02c418003500c2d41948040401005062501c61070141c903e02602c02c9242d0009a2224002e510010340b000e030580e04070038426000e1040c1d20050b81c40250f41310503014450725248040c41d450340c22800300c41d44a5030038880 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 30957757 1250 30956507 30956509
    0x20a022214040611070201021c020705100215060105030108150402061c0207051005060d0f050a02060c0d02060a0b10031508060403091802071205030601030617030c07080601081207080f03040809010e 87
    0x10a60305c4c81581038009000010032200a0584c0308007020421003144900704000ca41922804113840f0038416a03001401e96480501a001c1800c90091170b140c100001440100300c503480019241081c408218510141a250cc0c00410518450404410500c049803425941103103c42e500500c455030046003942e005110949a80051302c03c156900c0ea403100d080c0403400003003072140080c01c00551055048480a9545501040860b00101c00310320f0a500850036441d0411303014411a41d20440d0038004004020798040020a10301400007082e007055524043c0c058a10458001000945000320840b442031820b4500101185824012100d400b060a81c103e01014014025103808980c01a102159001d919008440d5500018940c82c10981c640c180001d00c5039420340699004843c903000342d5940c0d4407180403e46000b940394001512030380004010410342001048415002807030900840d0744902d6418440502c1c002c0103400802200000705220400a903900101900b560a880e6142280030502c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 30959007 1250 30957757 30957791
    0x1e0a0c15020703080606030a090609030305090118031d01090302030102040905060102100204050f04050a090606030606150903050d03020f0f04060c140f0a02010f030905011503060516020a0222140406 87
    0xb00300801007400c0710b01140c880d00d000700241d03a000700e070340c10b001800000f56102c00e0191410f005081d80402d60310300c1030007001d100030700804e2090044460107180b40340c0c440c1e4004080d40c0d001c03241e048a003100c1c2d00200d01968031901201009580050080d502c868031170502c40b006100944444d07000d0310179803040032071162190007541c1c21110010000f040c502c1c0300b0000d1101038440202070001c0e01e40e0351915003001035081d00c6540041e50246070002801c4c0c0c145512400b12280070400340003881401d820802c001040002c02802e00c818610700075031201084881e54905000d095501c407410a804280440c0556014814201486c0501c2d080d01d48502c480d040551902041c0441000c0e0b608880340280155000c1c05401c1d04210742c0e0300d03000070700e50030300d8840500b15035242ca0f105005601c07228040007804000c2c040c254005508064800001051b400c0c00b0356291401040240544a0f5203503188420346030144034850f04001c505d0601807100f20320000080c1c03a5044070300312501840d102605c16200108 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 30960257 1250 30959007 30959017
    0x12030c09060c08090d060e1513080d0b06040b0c0f0607050f07020f06090307090b1005030f040f05030417030a1d0303120c040306020f03070e01020a0b07051e0a0c1502 73
    0x551114000c1c19296101c902141d0f1055181d05d8015564140d50400a20340340b01c0c05d0201c0d4102d0002c0d08141003401000c8005100181c43c10080c20300c03000c0c94802240c55602142c01541107603d00040d80703050600815142d0185910a11000d03601213162480810041030010305203074100c0580705076a413102c00584140c054001c440b1503601051203150014104090300310420302e4014030490030001d031700000914001c110740010005a0711107652100f941048038044541801134100581580741019004840c0c0c031005001502005000d0600340610130140219000790a040c01117100c000005054143d40f580303c3c000c0c041c0001c1c1d1540011100f451401c03180804041c0c01406985000142c1407485801c000150902055174030030000000010302510040c01221141e11203103499141614000c0c0c419445d414505065400140031300001940701c0d14a0366000325142817198030345a90400400c520072868060b42c081d0300c40040c40c44001e980141400c0001c038441d1011002c20504540c1c40020b900030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 30961507 1250 30960257 30960269
    0x30a0f080a0e100822021005040305060105040204030f1e080d090506060d08030a02070303061e030308010801020c0706080a0905071410030b0a05060c031309060510111c020f0a12030c09 81
    0x14000451504005e840184032651540c004444460300c00360002100182200729842c045600003d040040200c00c0c84440e00501080b1401c5003410b10f5900c540343c000390740c001d0003020000d025803114030720806c0401d00254543c2007001c5a4030b810409008a000309071018054965104410000300031b443d2107210440165446014142103803940b00b02d02e0082d4201a50403000e154559201080e001c0701c0101403c00350f08008000724089286040c003070101801070f0030100c0c0d103900401c154001803200140b07035000c42c1c1c1030389400000d41c1e8070714510b00c000b0700501400404130300582c68000360012820018103d8440708070350401000c4030305141542240d604641c0c0c1d642204000408200e6480c1007030240c50100903010a89140111000c4040801600c03900140c1c50750366110018400f9082c504c80d84c42c100745007428020710030945408090355038031480c4551415904044071a81e4a41c0c42449003443d141000800c0340c0d49036040f49883c5e1103054589000200080c94142c84900c002d11520240c011129 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 30962757 1250 30961507 30961517
    0x30b150319060b01090306020711040c090b070f030e040207030207060f020703020d0b1806010e150a1d150d030210140105060301060f050f07030f0206070806130506030a0f080a0e10 79
    0x4070503960040549440c159840c140a11031000102140301350006081c079522a07005551003006800400c0129801c00c00f1501c20000c4284061105883c500e04462220b9004566142541c3d070328a021501c0f005101000750300a8000704141c41010340005403002901d24030380710b540b83d220031a501203988002500c400b0754000039001e04800030981048000e0340051480e800080310b5607040040c14a03101c02030740001c5003921500f003040096a000d00c400d13070002908589907012545084480103500c4504d580381e41c01d0390300c80c00100300080000081c010420070040c1051911411508000c2d4443c80c10742c0340d4082488c1003c20030740305a07055400aa050b01c800400c082d003143d081c204100c9001204444020600c0020458001d000036078801410896102c0d80e9038042d1b850440f0002820260f025001c0070500c08000c2c00c0c840d9a07650b8410030750000104950000340c503a80c0e41c0001c1d2400b40703035240c098031441c40d00c9140c9050006800003425414140d896424184001d50140a140d480014035100090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 30964007 1250 30962757 30962803
    0x12a030305090f010219020f0303040b0106030b1801080a020a0509040b04030c0809031e0f010e0c0d2a031208010602030d0504051501090501091d030f0a05070c030b1503 74
    0x29000750300042d000060003040381d00107005001841c1c2207901c074072800019030040c8610025100c4e070410640f4a040c0d682006103003541043e0741c41000113441805000181500c03940c00c0f48903611650003444900500c02c000544550355103c000e034451002e000300380d028525048000c1444d0505660b118060795000080c4007860341c2d00d8400311140b1060a04c101e8000204100d00c0c0520340d000c10400c80d40c84507003120f0300141c00850300018079040000c000861641d042040380111802c1c041000000c03504151180a080059840e10502007041c0107407141000c0d03e0340c21081c2000248000d20001d682c400c0c0840307460045000c005a54544c2d0034400e800059004012059405d44190840c2c0e0f00207209904880607160843d889002d414026001609940d6680300104200b401c0c40c003500c40208110024201e4030310410309100e40b030388500d1720440151000064203c4481b0711801c101c03141c01d5000100242c1194a03031411081303d610036188041d001d20100140032580c034cc085004010a698561210011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 30965257 1250 30964007 30964013
    0x10f03091a0c0d150e0f07090e0f06040513030816020709020409090501110c03030402010309060e010504031107060e09010308180307080102040603051501120c030b03100b03060108060402090414010b0a1202012a 92
    0x11200003001d1700200623020000140d10b2510b00c02a0b03005283e00207043c0e003145000c038240030449400501d80c030351040d48a100c000c040794200501e9500031401d0266140301d20030751002680380040c95072241900d28400100018006610b61016070060b110740002c1c42490407501414099006442d9482d840c1d420404c04200198001ea0041e51001c1c814a000300d01006004a110f0031140201c800340c0c00b20b65104200b0003942800d00158020301424200040844101d0000c1070407010140801070010344001081603151a00700591481e00c00c0080840d440c4940314103586010790020311031000424140f101055a1a0745916000c003a0701069407500e120000440c014409402c11040d040c0506a9580040040751418012032809940b0100c0105184c01c1e1401410b1030100141e2048001743c2186d001e00c4016a030301c0c07074580e40141c0c11101801c60100c4070040c0078010986441081c0d84415084070000e2595004441d20300854000d80321142040c4681d2100c291b812840d070041d0380f840c911303000e041d800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 30966507 1250 30965257 30965281
    0x702070e010b0307031409160e07020304030204111312120518060702040b04050705120109050903090d170417010506040c020c06070c05061305130b010f03091a0c0d150e 74
    0x2200965280221b155800b400000309510004e0b50090001d0b000860100e04082072410160000c18010000e9201c0d0f18000380000e40703901843c0802481261030709900c3c90400035910691b106040096815400c02d80d90300380b000e1303440c0c00b0058200e6904243d1034000041600401c2a0750302c200c0d1292900c010203144204221841d0b10954040f80e0065988400d522607444512450b4464038a9885181d6100e80d00106803562010503030000217514202410070a80d488044162040d900e810344820107981481e2401c0c070b17290b071980310b9014000c00f008200001c880c80d90036036043c41b10012100801c61b1b0b8940307034144001d07103004034506000340c1d0101a00d801a402c10400030042140a00039070a40d003034503000014015030001301280342418081c2c0007400503240203800c995040c0480c0700d04100c0386a001002a140051013001c06d0185a600c01c04501404030a2900300158a001451500c540c41c2a5240782d0064106d08e9940e0801d91a06114501c0c050a101010082d10208a0342180035a94803001100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 30967757 1250 30966507 30966511
    0x20319020d120c0501061e080a0507060822030509010314060a150e030303150301180f0b0403030f020703030617030f1e09030d0201050108060f04020609040e0c0d03080105090702070e010b03 83
    0xb0050400c3e00d00001c14400c0c4610405801100007401d1503500408030b8001c003203410b80128603140c20407881140020300c0090210220743c80c40c14a00c5240e07480c40c418445c4510440c4903591800801c103414400c055011001706840c1c00c09803400c000110f40c6a0b030b46110a001210400d4100460035018022a01c6100e140000395125180200c210341d0300308013003821070b001030703850705d000c8000c0018079051480c081c082c040a001003d41714012003003c5032504883e00c0784101c030180140d004031001c2414144207400603104400344040655071001c1d00d1034001c006156900c02c554007401072000c942603440001c8115402240a0b43c640e5041910720100b100c0c010a2514103800b030700300c0800c1600d00984090086a6190045800008080d8540110181007120040910405a00a00c100030059807a10181d03034084000752000107030030301002c100518002030302e5609580b154003894031008040e4404c05450594909441d55030f019120082c00741d0743c4549500650310702c1c0c5020001440000d6044020315 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 30969007 1250 30967757 30967793
    0x4020f010c06021905040f090203070f0309080d02040b1b030307140904091a09010c0504030206160204060e13050111120105100c0b070e10110304090908070203070f03020319020d 78
    0x14601030020495000d0001d0142084d0042200030034100315110728108030070b00030041c040c015032031441d03e40303002003006480181c001c0a02d5500c031000720a000d0390400762860403503c024215038541d1620360082c0c2c1038218540608408251782c52814100b81c001c42668000e4055896050240000c0580e807081074109807140c54200796614007140c08904140841b0345410021030030307001c42d4240280301c5170a43d088a84541c0a00208110820041c0ca841c0120348481381c3c608102100044203100040181c003032644115000c038402c1c0180550791030000100c00300c240c410f0008006a12900501c00154020349400d00058a54040104103034203160119001c030030704c54a094241c16201d039840420500040d039040c4006110600c54101c10300340940e00c1c00c194001c1c1c0c1010050003403a056010754921540c02101d181c1c5803601540c00401000d0403d4503107450b4003c003583d0129494a61891000e071091006034420f00c01e07090034440c4a950b1841400c080d50300a040014a43d91640b5000e0340402010231756 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 30970257 1250 30969007 30969011
    0x50705030708040b0309070602070b09060318060a02090a1406030406020a1211030f0705031021050f03090415080c010804020d06021912020c19110a0303090504110304020f010c06 78
    0x200740055403103401000608411313842c5a45a0400c100c505151503402d17000081503600660090140b461040251204003404661541c1d0780d0385c483c00091030080c41080d00003418414074040c0151060300d45c006d0302c460f41013551085d401ea40c0e240c4103111808840d61078590014810030108010840313a80003040142b0b040d042490703560445504d45011a035030303503800c40c0d0a44408800d112040081c000c500303400c42e1442c41c105066090050000701100c840d4421791481d580c03440e120924a1180004d00c1c640340350000252600c14010618607a142d50101c06484d104070f141a03000207100302007421610989080c0c1d00201000e1120900540303210700081d209a81c0304074042d541500144060000b40091046042592403d0662a0703000d007001c0c0000302c00d0b809041c0140080c6448242c006814101004100e40d00e000840090810b0445c0020001c0313156040710440d03c000c01419002459602101da0580c0d08020701c4c40301c0303480203440d4081924002c1d80150041c1c08498039601c40d01151401900074500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 30971507 1250 30970257 30970267
    0xf02070507030308090606010c02030d030509010b06130905070207060f0806040204050a140f01020f0c010c0807050d051b010c050a030f061e031a07021509030c0709062108040605070503 81
    0x10306250911590040340003440c2c00c810004070700014490750740c0054013030034191884051a070001c2e8232022400008070030155548005078450300250085500030b070014000c0b40d6604441c42c0141554a91405a05011400d00f00031a55241c0300048002c121903541d9105402d0301402030046940c0c082c0a02a03030740c8a60240b2020665a44955416000380300018a500300850305005124403680c40c030b0507076415504080d0b4041c010300d01c00305500a000d0003d10301040c0310b00d514035001c1c010340520103018185100d16104d50b0000b64001c40201142c0f8402d002402041500400040c20b8a0036404481c002800034421034030414003079049601511100c1c100480c0040e11046034811442491300382d00300e1840b081204006204005051180c00400618014203514088001940d1284001075a038032034500c203000a03080300780078400c0d03030441103150f000d1342e00180e070754191100074001e00d020b1440c400c00341c4c0c80301c02c41110b00100741089042e8032610b560305043c0b80640c1910070303400007001a1414082081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 30972757 1250 30971507 30971513
    0x6040503190e03030d0c11120409020703110a050309011806020d2f010507030c0c0b0112030215090d090501031a1311070c142b03051b0c1905090a0f0207 67
    0x1001c3d2000e0002c10400245504607581e00800142044940d1445500003048241c8c0c0c0b40040d0b41220140c4400303002c0540e603664035160494050b41800c80c200b029010301200c0c1d0041000c00302c014500c0705400da1751540301d00280010030f403003007440e4421680541e0240b200043e1850040850f00c0007078141d81c044004000380502c0072007220704501411540c50350342e14100440d030341c1c2511480440d5481031400f101d1104182e0343c0c0d001d01c0320041c05019150310b4011020810144200020700440541d8102015682003d2110b0341e51107a09110740c1000c220304450108065219100e9a00d0b001120150303122512048000d01595039860954500c5a030346402c0b4031550640313420002c104c02807151520801052500c02c182401e1000e2004140c800d1101c00c2c81c1c0210503080703006120560b41c1c560303816020740c00b0a01d8241d41d14403c00680c0412a030900c001820000d80102d200e074010001902c0000c10414004101e1030144020b0040c1a4405021004161306841035800b460014109241c012b03e044401c0e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 30974007 1250 30972757 30972763
    0x152709090d030f0c0c060509010612080909010501030903021c050f04030c0e060406080607050f090a0b03160302030709121b18060801020a0c14010f020a0e03010b0306040503190e03 79
    0x2120100c06a01203a1000c000c1070780b5114141a00c0310310041005180038841008152550310803010300b42a48450102e01a41c6080d031048005004100791212400007902d490310700c0b40c104460359445141c3e03810001030294000e00550810a50580c007500415202917084d16000c0c512880e0340b02004003d0114209002c4c402d001000954040c44501100038a41a590046100c006105a00460501c1c6c810406903400164854010b8154202562198500498642240030380c102a070703030155605500150803002c010007503028010410f141d60040c030102d8802d5090f448282c0b800c000081404208000c81c2c803c1a0a00000301c0c4100c5103a105613004100d900500482604080c0d1040010540031761a010395118207001070842200a5040c01601c44024001408050002c4c254985c45003c42c04c0061307007903001054918401400310345942c824040202483c0410304c10501942ca004140c40c0720b4980061924440c91b4410011440d090104800c1962988031103a00014010300d01408822a9414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 30975257 1250 30974007 30974011
    0x70908010c050702030f1903050d110a0c03120e120c010b03010527010504030906051c0c09061d1c1a0405160b0306010903030516080d0203090705152709 67
    0x142ea10305440d003980d13004050401d807403c07451407002d50005042c1006540c0e403016094000f60141001522180040d0310200a412035080d2452030344000a44541007a0300603464441090095585002c507101c414070350011079520907010030850740184148408620090003c0134069079000012403920f6403000403d00707482d0140c580b49245202030011254402200341c00300c1110074071b1002440039080c00c1c2c5025165880c140680c03000c00c600060b02401d0f1407141070320700e42d014400200401c5811301501000340110350030700510700047d20078078440380d82c080001d10340c0000a10081c5820f080094070020805150720f8280c040b210b0032048080d08445078601c8112600c1030780664094003240c0b010381c2c8001000d184a8004070041c00341841072016990740b1562a1094a0381400c145641e45240000c2445040041000402d0346000044141513031640380c001e0340c024248c2d0f408403595140c03554204441d41c00020104500070105000722108101c0255298982802c540309800071048103002040c1c48080c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 30976507 1250 30975257 30975281
    0xc0b1005061209010c050f03160e030a050f0d0302040605041806030c060806090f01030308070e04020f0d09020a050904150f09060c03140a05090705012303090703060b09010b09060307090801 83
    0x2481c200b0100110a0044803211784252819034645280740c40a500b49004c0500700440c9141c0001c0150704003801880c500d80000801400c03100551401e2511a03514008010b4140c80390098412400700f01d801703030003618140c070016200c49090604000e150143d800c4000c1034400e076291945000008203c42c00c04101c0030307186546e50000c1381d02e048001c0c03000201c409085484000c048200400102c2d9101c1000c0c2c0e040000761500e246810f2a00000030040c0c0640c8640c0e1214a10010311200c0d0b020b0590320101c40b043c0709031901c50f0241e07038880070440d13074000445d805003040b40c0d0100d101503507003003607441600062b803414000689440ea5480d008100c034500e652050120780e0f00d07000c100700b090307110210650102c00b48005002a1500540860321a40d00c0d10a00741407150b509202d00d00d141915800e224031303001c1d41000f16141d1600401407682d031400341c031080d10030528200c0400c1907801c15035842c606a400c0e6041c040d16001040c0f0500280e5800180400c040000d140c0700801d11150a014130008040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 30977757 1250 30976507 30976537
    0x10b0910031103012705070f030b0408070f05160806090303040b06060c1009030302070b060301090201052208010e030301170d0206071202090406030605090706210b011106010906090c0c02010c0b100506 88
    0x4046c0f0b402d41ca0201150071102ea00361a60310100b002610040c1600e074032070b500603c0e60741c46800314589a0007051140000405501a0b03001e2600e480207035418500032204444112038041c3c580c8003a081e2644416500686010240400038415003024030007407684024140031030b04581c0c12110100102c400c050401ca0000e0703000100c11040c8a00700000a1300010210020802d050155002074210300c1642d40080c40540040314241400c001d001d5840300a00c83c2c038000744950040d940c141c580725132007400346212024520483c036400c02000504030a40000c2a002407660383ca9018040e5010a40c0c1100200d41c59020480c10f011611140205801103100b20703000315050a00e00d1016040c03101540084003000401e25108501e0030890a2102284903a203000180d020013100040326044071040001107540f288000009008003550f001804a64181e0010004001d155401b00c44072000800c000e0300184034100c25030301242ca50090150050501143da81400356982c0204001d90465504001c10034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 30979007 1250 30977757 30977831
    0x2040b130203101404020c07030213060f03080910020607020703080313050f0607030b1813060b06030f07030615200c0a03051606020606010801090c02011805030c010b091003110301 79
    0x180103212460b5004d0000c0320154200041030061564400e11440040d22a0304840c5905403014425030085c40a88501c401d6021095100c1c00c0c10120b81e4001c500341c1c0d01070341c109088243c09610225149024084941c0a003240368615240e1181a81001c0c00907950700c030403401c103c00082d1003000400036000e403036005002c0526202d10041c1c1201c0640c044a40141c92240c16422801c010259903a481020705ea2601510402814988001c040c1861071580004002050045403042c0f00629846010039036814018513403205840c442c40134107103640d200443c2e401a411481510150980c050041c10107080303900f01044080012054122a8015110b98000c00b802040c03440c50034110380e020b0a1680000c0042d41410710008140010520030100445d0b81ca0a640d0a5030b4802c0d00609642452026007a42c52000e9091558690f8051078285080e980307040030414071810004502c078820600300740c10380c80c0d092542e15044440c142c50400c1c80d41c195602d105106202c0000b107103043c200d200d9441060481c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 30980257 1250 30979007 30979019
    0x3180b07020f03041d040f0204050903130504020a0503010e06130606050c100605061608070204020f040e06010305010302010503070302070c03020307030615090504020f040b03011d010e1b060702040b13020310 91
    0x249442d07400c10a80e810802081c0090200315001d44502120050b04840668950400c00c040182100000750b0045c100400c0c8540640000090b061681ca0808100451030781c44080100301e20902d045040421000d100400c481581d100456520050181c052313290741c0300c04420f58045a2158119101060010440c04508002003080902080f10301004105450503d0b00180d035500a03071078a4200140021200800c00902d0170640d0905580a401507403281c6041c0110040d94006000d41c0718020064400140d4640c072034040e80381240e406845042c81e40d140d45004801952103900151502000441c00200688040000d480118010440010319072140d102149003505c1c5540008070b0b0b1401d010500c405a0754000c2c2550040404a030300240b214041030100b4050110340a1880c603030507207030030b1800c1064010740002c0920340f40c130015200d03004410015126041207061602d41c02981c140140401818164042d105460000b4064a41160f07540e482400340e1b071084680d2600d40700e0044040100d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 30981507 1250 30980257 30980263
    0x60c080d1b091802120408091212041401020d09260601080c030f0d0801121707050c090606070c03150204211a0606070611040815040210110d08040303180b0702 70
    0xf8480048000d511744005800a00b04644000d40084d2209400040001e2aa075032210000f4075072001000351101c0d414400c0001010703411034482c2244600c03c100c4024119880810010b500c1500d0f41c55014003642014501c000c10980e60f480b90000342c170480d19405e0b50010401015000b041820f005100b02d001c46410f00d810f180079080d0490160b44005010500c2981084905054419003488000003000c18200b08050340084144000e00d0b045c0050a07206110022545681629041c1c4a4a02c4c03602e03035106001180c8140c0300050920b0722541c6082c00005c4e2350120038500e40d03000041c0035003019240c1d14000340d218032041d180c01200344400340c00340c204180041601104a041240c0030710b603140100c007081e07183c480d0400003445e0a43e51190701c4004940c80d81560701034040030341200d0701c1c02905100f40c01c0d400c0e400e40e81684035000726500240c40d544a031100e996110001c00c00740c03090f086809029280c401d0054400c506142e1504203039030101a0180005e90014040c5d001320007181441480039003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 30982757 1250 30981507 30981539
    0x71e11030304091e05090307030305070504050405130308090606031002090d06060f03050705030c090a0207210903140f030405010f020c1507021003110405101101020a050406080709060c080d1b09 85
    0x444c8038140402c101c02484044181c0341340030742509002c5850396900500311031034441c503000b450b4014940818400c01c10450303142c00789541e1081c4c4445a954459080655481c10204d6203198180d002035407203c3d0300e0045801414640784060283c03100320903a40d850406032051034005c880c081c0d180e802c2c100300f880703c00c10101d8010041940907103042c09501c1d001c14140c0e000100b000b070000b0340004602003008007aa0909100300d40101c52002c41c00c801c0b102c01080320032540f000b640d030f450b08002c00380040c440121740382c01700a100c00015454145800015200300c02411880e409600a401c0500c603d5110401001d410180302810f0701c1e0b0340c403c507204000c01a100e084503001058646070803880700e02806000c440540300100c8420440e84045481145c241384850400c0f001940041480c54003250048058400c2e81c2c0c081d101e243c2c1c65510220111219962031017144002021982800042444280106070500c0700c1a00403c9030000444060038083e844030b0040001200c00008010030380d00801c9180c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 30984007 1250 30982757 30982811
    0x12030509070f0e010605030411031b030706030e0a0b04030215131203150306020d0e0a0609021203030c0d110702060c060106200c10030216120e0105071e1103030409 72
    0x482d0b540c2c00e00303980b00354115050040c803007030240001c049010321803803640504030980010100c840781084200c0c8ac0c00ca1000c24035045002c0c1c411100040b940b0ba000380500640104048020191081c0302d0300c0348000108003070070507025801070f809000c8480d40d007c00c0b102e11505040d2180020554107152014035003444400b10010586010980c040400304582000102d039005540583c41d6980c51811800800e424008044c1610640b0360003003c00403280c211403d07030f078000c03580d4200843d401502c1d81e44901c8101d8808110750303c01c000700c1c0403010903980603101c4a03501c02203050400d48142d021034410784c8800307004d002a900c42c0004100c0a584440010310003108002c0e458601d03108417403400e640703090304a03003144900d100101244491b4404c2d419107041c407500803003500280403030b4104448440e15150b001c4c00099075882a280307103940100b0450344480c0e4460301d04403d06202041c1800040c5d10400e00b20341203241c0d00c3d039200480c0d13400c001038006804015000104082812344a080998010300e1103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 30985257 1250 30984007 30984029
    0x309120f1209060c060b01050f0d05060909010527070f090e060a0e0307080708070c0b04030b0a0912031503080408100b0f030c01050307170115020f16060f0306031203050907 76
    0x340109913009401140c410303407241020401c1c1a0002c016107403405190310704605d201c070100d1007800c0c03130880360425402441d0543d00d204a80c0c840300d5402c0c2c2600c0d0700702c0f041012004604601b015501c581e50b00d110784c080760700c41942c14044d1100c00400e6001155031103841c02903203c00081c10021000d018640e08021801d10402c6250bd41c6541345d5128064601d02901240f804220306042c0600c1d00c0465120a0340525000d0240b91a8003503141c1e590040d020036182c1c1c2030080c001400c03800c140c1c402c41058070741103480605405215802180904484003102c6119011454000001155100a0000360000303c010b4004080c82d000c1d40c4044031036503100d00f445242034900200a84c5c40108250307006c10004c1c41e2507907503a91009801da907039404550082d05001c00700000020074130601106c01c1150401a425039414040b14014242d031560711040030007001800c00020043c031405000c007006404090b08000ca40c8035901d03141d040100c8020400a4082500e403020045d0801781804641c019103030030445 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 30986507 1250 30985257 30985259
    0x20d1b030e0c0906011107050901090204030b01080606060d090f020909030301060f05090d080a0903050f01090605010617070509030a050f0c03061308090f0f030a03030b010e041e0203040309120f1209 87
    0xf1074008020389950305000010b0300f0881c80d50414016030740035110142c043c4d035947d43c0d1204860003d40c03151005a950507030715000030403420808111140a1140280b00034242017002d4000c0d002090100303400c48408480b064104016195488468824211030300174684941c905040a007545440312144070401804100d8014a544ea40781e40390b4100c0e8200c0c5c1c10903115800c80c1d209a556005540001d000c6100d80c0504100c165015009004d01505c1000c05200c941d0b40d61200352030503014043c8040c0b14680e01000245954801c0b80941440d9500800302d48820325241c44682c20450101c00701c400340e801000c0800500d0030108070644d00080b92107070101d00c642c850340b034810305406410140352013800b0b658104000c5070744188840c042d1560040035914030f03a00501c0c001e802402c00003001404540190142c5900307180920035044181100c40f042680f21001c80d134180020b500050040303092110702400070407030031032250740000300610440714081410a141014403182c0c00300041a010444440c0c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 30987757 1250 30986507 30986509
    0xa0608060702010b21150c041406030903090d030219080316020307081204020d0c0902030906010906180203060a1205030c011113050d030908010c02160b03070e090901020d1b030e0c 79
    0x40c90091202440000c805500145d1203618280340d0711902c9454456110014040220003040c010030860b4003a0340d0002441201c103060001b036020440d60a0720319002402001c1040c01c041a12160301803091043d154a10912154081003090310f040c2030f60302000100030404412448182c203100b58106000840c14403149030748800d4144a003c0c10183d841009001180864581134842030055502c0101c0170392054441c18420005d400c1211040c059106100002400282d103124000980c1d4003d224656007010000c20840039500141420f0b0300880d01d258009003028882901c00456032241014554501c104988182911108605501482410090084540041600c0d0021988251110014940c540c2000e41d42e082d5203a004540d80c2d402c2c401c10488a5a0115445110003000e58604941d0707a11820b15150300c0c0411a0680c006ca03459103484240c6213015103106a11100d030710000b501c3c0140302510802501e152803c1000c0031b04840a102c1d6030b40c0c3c1c244c0104c1c1c440c501504000d00502d04104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 30989007 1250 30987757 30987769
    0xc040603020d170f0d020712080402031b12030a090503070e0c16060227010207090207080d09020a1d040201030506060a0e040e01020d0e030403050d1704290a0608060702010b 76
    0xa07001070403036900028100043c10044180e0b588051980b21683d00d501c905c9100402070340c48000c0864980405500c8440d0b094090300c55140229005401030800d14020180c032019011601030f0307158029000600700c0c005100800090400f0911039941d05001c40c40c15091610b4a8120f401c205108404581004403030fa40203c10f49500691910401c5001451030030020000e01c50180030b081440210001c1034030b010602c003400d00320b0702c0c030070382c200d41c400c9981d041c3c0c0354101c0c0112180240214020800d0035180f241e02d4110b03980300f42c00146030411a555032081c80b520b041ca40c40701d5102201010b01040195a01446000d9000d0b1041d500d403881d14058810080c000200003095a100317a55030b40304040003e6095056400c002811102048008280f1940c4c0d41e0300d8106101c00c40d520701c5151501e0a03464401c29405c680085a01071404454a0b41e5840c1003a080c581000e18506142c000c603000c60075041b0400700c1d07000d141c2801000840300d0400e00c00b1814464018802c2c0250380c14000e6140c101d80b210 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 30990257 1250 30989007 30989029
    0x8030c0a020d03030609050a060f0504020a1d0f190f1406070201080c0c01020c031207091a03093408210705010e0303040b09010f0c050a0309050c040c0f020c04060302 73
    0x403103901e801042c4915040e001003449800c1044820302d40401c2200000440d4003030300036180c200c05500ea40303075900d50403c0168842d20f03031500001b4604203000f0752a007512a4030703150f000c04c4c001c0000c01400040d4001c85c010031011402201c912621100400a42e850040c140c00a82a50051941c80c240820046499445460b0000b030410030001c1c001841c00c0840d2040e41c0307444030b004000390343d650260961507540c0d400041c1001e01208000d03010415541c001c5040904a03004408100e07800f4142d14131003211034200502d1000b0f5800380e50348203500301e0903c005001c40021001d442c0389543d080300420101c2c40a054019424a900070400b034400213200b201c2d0440d00444200d42d02e55943c400b4688140588920119294544008418401005040c1495034820301e1030314020040002c00c01e00701c805913103502c454600851810040241c403240300ba004200750501a2044410308494080858100d445000080000850301000025130310b42c14031282c0b440c140102d80c10300501d425500002e54100517 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 30991507 1250 30990257 30990259
    0x602070f0b030a11040906050108100e070503070309020306010611060a05010602100c0c06060303051209061005010c050a0b0106080610110304052101090f060b01020a05250503030c03070c08030c0a02 87
    0x320018501d5125600a0044c4007400350106481e155154100701c0130f030059000342e9002ca400c400001d084404038585070710480701c0c2d125540030191110b0205680950024145408240d100c12038800940c0703082000a008048681e1080c00c0807000f14060740c144032001c1c0c07481103a2403e10004105540d40018070712140100a60000740141095600b5500e100914000801e024203140000040c10340150140c0350031900b2650f14801c99072280d0702242c1703406007240c11100490514030240855440303400030749046807290f011100101c060b80c98500000310300364040400038008600304040c0307003042440342d01070100e00e0030300307400700500d0f80d40c026228041c0340a40ba010340007901d100c040d80341801e148100380c101c459000b00071083d0b0b141482c2c541988041c20030b540945c140910a1440d5200180c0d000400b5000f1010300303095195030307042d40350f903c6101000355a080082100414070f66014401041a01691801180c1c1e400381480c01c4622903080d640002002d03041400070070000d03031000c9070216038594 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 30992757 1250 30991507 30991529
    0x20115140f03060f010f06090f032013050a1107020916180801050406150608070e030309040c02150108010e0a080304081c090201020115060c0f0206070b0705130602070f 74
    0x35500400c082240005441e541889904280f00c0394548502481c0d06030751003480448210358480009031522540d0740b048581d54003100500b000811410034803a440c04e00c4c502c0800c2d80980040c000030342c840032100c440c4201c007555102403000c00706e00361041a050720120000d407800d0002c01e4002420700c2c03600515004050100441e01800c02d403058090402002d01030084420307003921b641186000b003c0031901120420300e0a00d04000c100b0202000000b19030b800c0d038440d000b680d200340c5c04444503600c1e151901e406100c10300c121241d55031540600c01045215034010211005080d2041c0c071f00c1d28040e8040c444991502408600d50040403403080c01040e040302c2c0e42e55036134130b03149000784051081031032021210031400b004000800c9950070040505000b6802401300341d90702d0101d40c0d0218014818000410740c22091000021014850000700b24001000301d828011207456041d003111040317605200080f0002003101e80700302c25003c01005000d00d403000341090f40c14600f1410103200781e4003982030a48 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 30994007 1250 30992757 30992789
    0x2040305031c3b030a0801080d08010321030e07080c150301050607020607030504031a0f0f1918200a09381002010c02010605040513030e1507050a02010f020115 70
    0xc020310000d1650701154004c40b0340c0c8030755101c0700174400d0f20280144c0e0405c1c080e500003042294460004603060300c0d00484c0e000711202003034203c3c1000b00350102c003400a064451031180036503107080c0700303d000600341d59001d8656040000100181850999900a4010030910041c8895240d035002c1c0d6071103c0d4161140e968a05140c10150703028001c13030780000c0110f403292980e203c45850b0740c50392a0180b040560515025120484180b10f15202159005084240c549000c5451001c41e007041c0340d105448840e58100b05001d842e124071181114040d03c400303203c551140c5030b290502c1741100c001081450301c200480e06140b001c04c00c0074000c00542451a00026034440c0c0c3c00b400d918210052644028080c0540d164541000b0b40605104a9400059440c150740081c003421b10303002e0f9034442c0246100306001045903070b80985826015200d21030f0004a005106500f6075a100d008109090084005100e400e501d440018a90620508003000710790400c098445103240411f0800c040e17945e6011140800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 30995257 1250 30994007 30994091
    0x12060904020a03080408010204050906010c03080403210f0b01020f0f0303060603060414130203010507030c02070315020c0304171006061b0311010c0809060603030405011e03090602040305031c 84
    0x480c0c3c0c0001d0007800000500007040340c01540141f048520980e1592620754810005449180304210046c02007128200000c1c0000e01c070b5840c0d14003c011080e0703001072031174402e05107908440e014503680c00c20f1581c513001e518556030104401c07003008400000030900c012040d8480c03900c0740000b40c0b0b0749008050100100c0d01c9503480350400010914038280300c20240c6400090304103101c0259605038001c0d40b030f1501041900b4403030700030301502c64010340003895a10324554990600d507a0014000049075400e000e2207110640500041004086200e0014980c042801143e4140381e0801c0c610480300340740000c1000b0981d0442d00c0001d080308044888180b0f5800d904064a048a00c141c828856500e4072600000352504a0307103050007060404102c8040780c2d200e00505070b980c0b00300e0080138089074a00403c0b081400e8150560102040140b40c04074007003400c1e6480405a0b0001d8200b220035401c0407032084410711800c800005181c40001b82445071540103012000c07842c070050040f00905640c1c0c80f080000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 30996507 1250 30995257 30995269
    0xa120e0102070209091b060a050a0c05030c01050408070c060914010e010e06030c041d0106020c090417030414010f0501151b0c0902130803030903030a05040f020d030807020c061206090402 82
    0x3000b83c016282c800c95103400f056294550a206292082880303100310440324a0030448180d562a503000d466652a00e207410006940c190304000d01101e0511003041185803017042805101d0040c0e2003003180c10344a20032864054611708050b0040c200300070000b04204080c0031103082030805502c0a0030300e980381d4025440102c8850b0800a0041d400810000c140090305403144000c004885c2807180040d8020190009190440b40070b10030400140d11854a00b001ca00e4040201c58000b442804600200720249804210580044900b90b0302c45c6d140c002c100350440f01c00e00802002e40c2d49404100055030514040b60f0007958210304030001c210620108800c80843d40300c10031044e940003422501ca880c0d03a0f148180203944159403881c10091903280006000c03500201303407801102c50a005d1403d41e50ba0300341074002440002c1090350b00045a40c0d080001d82c68101c00760102901941d80c1e0001d40c540100d000e840d1948451806000e09010012035090315081840d40760412021a00d01c44140c0700c030700020350 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 30997757 1250 30996507 30996517
    0xa0b03070b0901170c0a02010606050405061b0304120b1603050f0403140d06090204060e0105160809060d1503060510030b0114040b1003020304020901120b04020103050604020d0f0608060109020a120e0102 89
    0x7120244042c02d01518208000c083c28021b0700d02e600a00405803114422241c0740505c1c494140c0208090083d030b289129907400c480013021900c0b0480b41420350b03d07002e200070759603954000d4880450103000d0202c00c0d00d2401c0c18040344a10b5003000e00007800c00390070b00505d254000740b001d020000701c2204846914000d80c203c551159003840b0500019441e402d158009501906c6a00007017403100c441c8448650081d0f040e204025030080941450000d1500c5001041e4418a038107507000b202081005103c3c0ca05120347e0b42c9418540710320407102030031482c0c01c00442d01c000d0004c001c0303441c0b10801000007a05000215056403134400c81d0f1440a09040d0103e8003070074000b100300f58444040314000c02c6490303141e40917600c07e40c002c417041429039a0302c0b06248003413a08064090040681c40c00021301650003030300002d422020252006103030102e034403101c9088501101a0042842d00c6030010400d10078200503c030701400c1708801c1140307840c0350208081c00540e14040020b20040c0c8541e03418030b0b00701003981070714 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 30999007 1250 30997757 30997787
    0x50f04090b0f09090c04051015270e01060c02040b04090b0a0b0102071211042a0e010804080405062101080102040801050f091e030906030f0702010e010e060601050d1d0109020102060a0b03070b0901 86
    0x60707013154039918084c0c94122b00c00070035101e5031400750407030031040318040d07000d000c42e0100742c00c071a8103074280202240c554040d00016a001f503168a01c1801503182c2d40301d5442c03803c0c000c154005c0d4500b8083c000405490b01010024119444040180021410800d0b0750f4a0340303a00c00310420300c40c0050300100d0003900d501e0a860842000d06440c3c12001215846400010211691030946da01e200300015904201c040d10054444a0103000502c52802c110005001d000d0000175141c2d9100c844102410072450260800031080e500072400f04005102405420380080c03001d840c0991074900031a46a40c0d85014604101a01c1c04c90100842121010702c1183c2482002400031992454a03050340481e004050303681d01e00640c44c001c201e0126820620458401909134005001c00b0780701e00e401140c041e0044050728074070590341c07400e800e001c004c0d10010100303c890840010401d01c07103c1c00060b043c14801000200304a007040b10802180c0c0e404500c090545a017445002d4950104000403508005254004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 31000257 1250 30999007 30999029
    0x609060801021306020d0f140c1e07050d080706090f1704030b07080601020a03030c03020c0f01090b01050d0b0105150f070b040213150902030403050f04090b0f09090c040510 76
    0x450910819002490b000c5941141e143c0e52907a1078008981c1d940710411100d0009022444000c21a881500c3d00a1980808201c103400c02420a18160a041411402a00d14014070440c090780f410140a80c5000304002c4920894000d40c540758211180306181004000f07507501d4580c0b00800416040f50f41c0402e4001090b0a154540740b4194802580300e404295404104c5d90b0025201920880505105d10011b0b405000300c4e500f0303540c05802a006201c0d500c410300d5020301920401d0b1004016a10562140c58000320f945003c90809a0203c901078009030701038a040200580811250180f41d41142c40564a48407104221020002240120110340c018000300107481c000740400220410b0159000b200c08002c0362600c2c0e0901411506aa000701952000e004402c0000c0f0a0070341c080c41c1e0140c020300384140360107807000324001075910682100202c1f07a138070444e41610342414508041c10080a68201081d428904985076640c0002c4040358411511140001e4005021200c4a001031041c5502 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 31001507 1250 31000257 31000259
    0x90608060d02150703050903010f09020d02040f0605060d0204031103061e090c04020403050d0914010e0f03030c03030108070603060909151d0706090e0c03100e090708030310030302010c1701060c020301060906 91
    0x184687d001d00c1d601c40c0706e03608000d0a18100d5800d807045110480d8010000c0550548940c240400341282132281c0a41c0e66940000007a40d880e504000e180c40d0001c403000594880c06c52030041c110001050100b8003d40c4900104072090300c00e541147c40c0b541c10078110b604242e07281c40045150103103841c60b01d0b4210b400410b0000c01c120b0001a440c502003029102e03420840c0d1542d82c54402488800d55050000c5c0c1d400b843c4900506200d40000040c00014043e01e217040c5010040d1407943d44280e00104842d846040704005065240c45504003400e031a4000b4440c0b0f5041c0d8032010381c180c805004c0e000313680b0356030201c0540c5900b55950303032000c1c01d4004041d2043d05942c6d000240c031070ba205114808078400c0e4000055074400601c012607104401007880800d60504118100b640700000500c4074403288a8101c000c98030550400280d4480e90b081d40c403440c04a411450024251000131055a0030312201c1d02031500f08058040b617440c150b40716450052601079003800086d002d05000e42c03000003658a0040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 31002757 1250 31001507 31001513
    0x4090908040503011b050405100507060507080402150703140d02070c06020609011a0a03080307120212100e100b03060f0402030a06030b0c03090a02010509010908060f070f090608060d021507 83
    0x201030402c8490407402007140003e0382181a81da0703501080c0384000160200000c3c040b42c0740500b14008407002900c0c069080407425503c0c20100c0c0c406890b8100480c042d101000210714184044600115110086508101c495074000c0d29038002c02d42d0701015950089070306515240c9070750640b01e0660304403a2010610b6500d02000e5140c0000b520700c1e071001d5003804050611b10080c2c4054145405019090168540c5142c403480015000641090108080b041d40c16402009500103004600300000081c2d07100d040c0130303204249040791070b805502c42203542c0007009011440020064101e0320405042c6949035258000035070201c2180d02a5a07005101200b4001d2b222100d80c040403d0320700c07600d40c01c4940c2e140c2440600107400122042030030356118601100040d4814070103414008410305250b48015142d8101c103051080c1140c045401855810800c00d800d41c0c00f2101c9040b1305907a0030310b028101d0074840010300000300106054081d1050328200b400715124420080c07114401c00007060b40300c8150346 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 31004007 1250 31002757 31002773
    0x17030708040c06030207020312070c0b040308090f1002150408130303170604020906030c0a091503050901050f09070311031204060206040c0f05090f0a140c07021207030309060c08040909 81
    0x500d090b5650941c1d00740200c1c00740c1c002e00c01c66080303a0300180102401008000341800340c1c2d0107440103c98130702034a8800905090303580043d10141d41300d003c3c0d00b03840713900540078048880c0024502034443d4000000c603004480c0c000c40c0c01c0c1802c1b040187e0a070314076543e038240522a4401e0007008030741d0741040c1100000381640001180c42020028844010303a8036040f04010a0380103040c101544008104081540441c82c170b002444081030358100110400d40c1d070072000e0340c6c2c02c1855500b180400d48076000c00130100070a04c036180d4820409080810b0701c0c20014103059854205010062504070021650b0015540400014209802501c03546584c1d80d10707018001d4036001c0c01e80307044030910040d49020484400c005004400d80d030000d4a15031381395075410003d0656a0018108030007071a5900078000442802c03036074140c481d0f401061401d542da142c40c81406002800c1d000360341c43c541c201d004c09000084c1e1002e000e404446040c9001211035556042c00c000700d10480c0d208141c240c1c9414010700c104203691f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 31005257 1250 31004007 31004011
    0x705101715060f03091207080a03200301050409081605010903021005040503030601080a09020a260703050a0f0503040906030b0412111015080709050a0507020307030e04050417030708 80
    0x4590590158071181c006440001d01100385079800002070000076003e44441c00a5a40021400100c900d010362100c8411030315401480d00b51641c0d000020703285041d64040c0610101e01c01802c0c90010541d04606000c4030600040c024a48100e03154110142441442003c0d50591080d1580c00c410001a40c0341441c02000c0051303007180980628400c100c843c2510303101d60741c46245c110001e5071540c0c0c2c80c2001162400e0008145902c4240d603443c092004d0384544103a08060405110340c0c00c07000b1081c0752680d00d031600306e200742a91a842045d0600011380081228521140d0003000c10a24003400d180407800d50050340c109501c41f40c5010000400d000036001202c1c0124014a00d2000246500e482101e5104080301d40084640c0801a1040c071205903a00594000c94883d080851041c0c03113181c414209001544142d40c1d41d40c03140300f0303c81d20781101e104503a000501d0340011407a010955601525468401c80e1061049603150001800d1054440b00c80b11010b8041203481d56a25042001a00714941 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 31006507 1250 31005257 31005287
    0x2091008060c070c0608040c0b0d05010801061203023c0714090105030618100f060f0902040614090406030c03120905010806010203040b0f040504021b01110301030201080f060102070510 81
    0xd4800402d5404154404440001c0c0e0080e08000c0007904201040d01c400b40d003d8802c0722210b00e980d100180c1007200002501e4204554640800c9a514210180d400e5984a8003c420680000c0d4158030019400103210302e0b400da03070040c00104809c620b400480c9100c0310a4880d06401c21584106c0500410200d0302c80d060f9800d0075031000224241600b0701050381002d0081c2c0b42c25500a00c042003601d5444045040f15182903002c5906007003500281d0001e80d298070325461101d90301e4110610180c4112140e4001600060000b10304203403600b9401070400b040c81c4005d80f4600ca0000c0c01c602151942d4100002a41e004100012080e07903a150004014181c220000e0000380c6000d001f06256118181940c00703000140d0080d410642003100c444030550220032410310050301004006100d813200c1c0003800855a034010a0b8408000003da0f45003035480070040040c1e6034608000510060307070050079650300888030941c0050b896035030038010b0749403411503000264455850812a564264014014060310030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 31007757 1250 31006507 31006513
    0x6020319030501180518240a1104050d031106070c020f0f100e010504031b05120c060d020c100908040503010f02070807030f021908210702070501050a030902091008 72
    0x1200c040440403034000780a94110900e4040c0c030558002441d4200541092051005006005074030451600d440b803d0407080c040d4201200007000003a540c610025400b00400d9010710010350390303100000c0148200d00a251003940c42ea00502d041c140700300703981041c41c0c1c154012650340c0c0c1800302c4040d040d0502c0c0354040384210000f910340802810300700b48540c11424094003a40860a443c1c00c169003920700241c803a410024180000400304806196044005519800e1000360764280018841c466949580c0d034208c580c8010710700146919004110b544020314040c0044e1203298406074070703050420302c400800c800c900304551a82409040320051080780c0c4120001c008200e0b0b003080c10000d0380540750015143c8441030010740701090003080a40c14440c2e4a10564050005c03410422041e1028890192401c400104101120610004010005911508025589143c07002d0b0007540d84140e4000c440c10081c0c0800c0c0d0501840c0a600000001079009080d29000c1c0389c240110b40c0088031621555540344 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 31009007 1250 31007757 31007797
    0x3020a121206050d05101a1302041a0322020d080d0e0f010b0d06020706020f0d05040201021e0d0c0309090c0e0a0605030402090a0b0102030904020d020a090602060603030d0b0402090a060203 83
    0x45030456525425560040c00b43c9800c0910b01840c0c0001c03d0109070340030140e8051f00031800039559141c1040700004030744c00d006071100c0c1051b45000711b1402c03080030451003203002c00034030140090303548000b121109503070340010401e0924804160b42100e180c800500415022440d2000030240c0d800480750480010b0072106061030144680c0c0c20707291130015858201c02d000300d407800440c01c290010314904d07009000140c40e00006100080325075000d204488100703a51074040c80115a818420b02d0b0300030030000400f03034070805a000c034507440d05100c00424082c02100401e403401c00d030065190b00c0060294250400c204021903034090701601c00544224822010b212000c00d169010707505a902403a00640010500d0f5140004440241090080103040d03200c14401d80c0480c2e41e5070300003003030f1000c5003020268580701c96405c090409010b0350821010f54100c8010049283c400005840c407a0560400c0841d007203242e04081002442003206c0c298000c1a40480803d1243d0004000c014101140001390700203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 31010257 1250 31009007 31009009
    0x40b06030d09050603040602090a03050a060e03030c0901110a02030d0c1518120c05011503020405070906020613020d080a020105070f0318020405060105210105010f02010509060103060903020a12120605 88
    0x3408842507848041030028506002c01d081500103540c3c400c1c03107080014a0700c40e1030000180c0f01d500355841240c4907070081800e0801c1001a00803e8000c10015004600750300344145689802c0c09007050050410003a50030086000318100010f000c101c3e00a410744003980200c0000038110090020141c460660081d00344001c010b0302e110314444081d4210190440c441943c1d2008581c5041400c038000300581d84843c3ca01140c000c0c415442c0388038a0300780007401280b951061006440009106c8018010300780420050300b60081803859208044881d0400404540d1002461640c104500986607000100314000000d8056001c203000d9803468545440342020701c0e00440903907848010303030310440b00e980c1c1e01c00e00181010340040d03412100c1410010b040c5404200480000c1d103c0100c0d2180c103042110040002d540c002d1502030f060700b5540f000744a203203030900030302d90358600621004102b80c0c1d81d100040d00749482031100300744156001c60910f410105041c40140220450071039070408529044001400d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 31011507 1250 31010257 31010263
    0x3090411040f03030c03170c030106030b03010e0705040b030708030309010f140127020f03090a210804111f120b01050c25090f0e01050c031e040203011e05040b0603 72
    0x302e4100d032145140c02c504680d03044841c01982c00044007406040210b0414803210382d072000c0e12919120030020380701e40c549840101910041004140241d1400e07a02401d00c0c28041005070039030341c0a89020841354120008a450411607030b11003887c03800080140580c528040d0054000d5405d07a81d02442912644249004050000e01c100c40a0034800325004507150202c0041d4203604803000401400c240d1350415112250380111484403464109062034020402408606026580d045000000c403141d407600160240c0c001500140c04015011043e02c51a56444080c007401c40c60380e00c0600c03a00c5880d00c009440002c4604121281030700305184ca002740d51180040d80c0c0700b94082e800801c20351807040045c4041084d00000c003c454103000502242c0c401a501510303581010940000502c201350a80c03240c210f072009005100080802c0041c0201d45080c4070146c1d8200301c40340c9203070720141c903284002130040c0700b900452800f895a144242c0c580b0066a805144200d0080e41001c5095403800704140d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 31012757 1250 31011507 31011509
    0x30c090e0a03120b0a080a120827010603020301060e010801050108010c08060603090f06090a03090e04020105091c0209040609021e0604060c05071e0501021b01050304030309020f0a080309041104 85
    0x209600011040c800b1030303c5074192199441c98010001816102c0030046070304910030780c012036407a5000420f03c404110184603401281d009502d410b04840c240a9031819010002e03c03141c520407017072041c0b40401e800081d440040107560041c002c01520b603860004a0040c00c0901caa400345500c1d00000146c95441800355000701c10141e07907640040c6d41c3e400108116500050728003503d911500150060b0040200581e44c003c1807007a0040007008e2070340c540140700c0c0000e5046144400442000e000050f42c0140540f40303111402c8400302078050745801d000343d0050320351001a521100765024841408031661262190500a0b9442e200c03e61030360300200318115000d225540c20060401042184074070507081054518800d00548000030303500d80d810f512503442c2e031849000b00010030748100569a01002444140b401e1107456041c1428031800281c40e0f0f010082c4050141900c904031401155104810002100c034003d04440e012916070a440da038982120700c0310340c010352400340c4e41051742054400303540c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 31014007 1250 31012757 31012781
    0x1305071401020a0b090c09190605010e0d021002150c041d04020a030222020c060f060108010e010b031815010503061b0403081806070302060919150c090810020301030c09 74
    0xc03d10314456a0703020304096000700101d83c14060281050304544e40d1a54603401005044214000031209404040c01c943e50380c1c0c0050306000e022040701c040354440d4010381c0403140d01100c1c030b10f594894441003030303043c40c840c05100072010100c03204001003291818040c01c20f913a0241903407215074495140c40f50300e0240954000c1c0d070186031050104014a0004210100342e0090300100c1a4001a0000b04060782c000c0b4144a550307400c0201001010b203210349a0940c45002484c0c254543d51600c0000001503e041c0100b4400d5a400800241011140164449000c052074204c85421040000041c20880c007806032a01c42e000c0e16000c00c00c56400042c2016010340600945403526195903148109507203e21460741d884455803d2100059445101401d2802d000760044c1c85070f4500185141c0c1040b170045a0300c03400d5420404050080784c041164000d41e041d80d081c0020328148881026a40b00049a000070310318440d10f5004580e403032140c4c0145040b03d11031425040041d440e0300ea0407050715845802c603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 31015257 1250 31014007 31014013
    0x6090d0e03060a0c03060b12040209090606010c26040b07110103060f051c0609050303010305060705030c09040c0903020301050907140301020405180403031103040c080c1e130f0203130507140102 85
    0x100f4909059548136469000035800c000800e07940d2030203085055042400c035803000101141c03c000641c1021a000345e449240324018140c02d14003600040e1201c1214080176203052817000664206411100c3c104402c0d82880f15203d07150307a81c44103064040d134445041114100e82c418075a03251540607000305019183c0004002c1501403d020a1107040014008079085080c10b02d0088004110f003071182d04c20040c06400a15075941c15030801d20b1415401500190800c08d0400401c83c1c0b0704500b501b40e54004404403000304502d440d0b02000c503541c1501d6040694036518000034000202c4000940000325040c070720418001d10344001c101401c034019803240325000441d424040406014508600e5800742c03003403c0001d041480c200d01001e050b00300b103808450040384c10302c041c04a02e4040119021a98089a10b040c4000c403030247c1480c07907101030300311b04d0191600c4290206140903d400c40c606162290108640303a191101111040f200442001c0c0d1b014002c40b800071a00f264070b0809419442c2c0c0603002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 31016507 1250 31015257 31015261
    0x1505010509060c030f0309031201060f09090507051b0c0406140607030f0c0503040308031b0310030b060d060504060c0f090e1311030105070305041b03021309050102090901030506090d0e0306 83
    0x28051075901c54114040c00c1d000c208002441c00c0b4170f03400030754000e420641c0110740f5030380c1c0b0302c0300c0c020600410303040310040c081403281072410075510004078000d80d680f01c0710114058580d1801642d40d802052181c005441002c0d00e40055400005517016400703504131000d00003540e5488081e00080519504590441d0042103070718003007401504101a40c5082d803401c8514403d00d52070b46425a0081e420031906a00c0020500014004402d00300743e0312401140a2884c6041c005056000c1e000940b000412011a00f0002001540c442c1016901103070860707400d100b113103440d01e003000040032402e4000d804626001017548003603210f03444030020f03588a981c0308881074458a42500c18016041d800310340c141c40302e901d03000407174030207019a0b0702070007852b2008505c90900b4502032410051340c200d00c0350151203542d000c2026a84512807600103500f44c8074000340d080b02ca824141d0181c0b09000d403143c1c10101da6400003081000000310307280f0402d401000e0f00c0030100c1d110700448201a0142c0e22940c5036001e540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 31017757 1250 31016507 31016509
    0x206060409030903050a0b0702010b0405060d060506010311120610050901020a03140d0f0f060510050f091318050f03040f05010e0a1a0702040e0604020d0b10050a0306020307031505010509 82
    0x3001e1103550340039003400050b0980d04c0d40c1d0b031840c03e0391884080b10007001fa607061101442d0240600c00c440300c03048809200914011011880020340c54001500302d54850000c91b440e40d0183e40310409131309541030301c130741e40e0f40a039529200b002c0380c240e07403280c02015102403228460744118142e82c61100161f000d0003045000e80c030100c5c0c7c0b021040e07140c280941010421130030429024420102c1011103d000401c409007100307910310450340740d80e02090184026a0140300742a074072500b00c841c0c58030303c0700d0156207132030071000451111180303004400034007460a21485482485000512211131050b002c8950085100851603180e0059100d038411104070428140f040d58022014440c101d14013078154040316641c0c030721840016000600c0c11060310800a920400d60a0070300540c4004032201009004c541000c3d808180301c00c00b58003025000c20140c001081c5d031800e2010380d0340001d040082041c0e10490b00e81c1007500095206481d9140402d162007000e60b003400010010703030203c4005031101c0e070030f01c00303010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 31019007 1250 31017757 31017761
    0x30c03070201110a080a05070c032007030c03060203040b0117031801050d0626011b030e070306020d05070e0306040203070302060901051204080d0c11030307030f060305060f040c140102060604 84
    0x9032110381555242d511503a265810744024102c0d1140b690f80710501800c0000d0414101d94020b009401004074805269000c80c2e04800d80c1d9075440d14455034880007010b4034920504110300764200a003280d0184500000340070060300a140114080d565101d0107076a1031b5552891031100880c0090540c1080c40001d840f201400111280040d040c1480c40c40c02d003201801d84119041504080320900f042132410420100d401c41d24401c0b011080d00030000005d0310300c2c111528441909190b42016110300d102030b80036209000d5030000716070104040d900c803500e503000d44014181c12281c80000070780d4224a20715a180000d0780c140a29006805814000c4c10741c3c0910080343e000283c2c49051003400c00a0050514091560610803800303540d003030b52a02581c008540556868190103400c0250b000845400c460002c030403603030007404d2400c000a02641503131580010b40341517400640707a402804104410002640c04041c812807184801c1c0d2501a15041724070201d182112105005070301c1140041c4140c1041c2d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 31020257 1250 31019007 31019011
    0x30506040207060f1b02030a0801052403042001090e0403120e03070501020409050c0405031b011e020303100806010b07021903140d080f0415020711060a02030703090f0506030c03 78
    0x150000d441c1002c2c507110042030300c10b604448512181e0f1030400040483c0f20020751240340802e0300c0a5840d2140708000240700c0e00c0c060084512503510112818400100742c0e09908410200004c6e2135124905801c1c80e038980c41501c801c84848203d200310707005c81c3e580700f02d810100303883c9124203480da0f540b44c0b6101207550f4110074074071004040e80c410800040714810005071020b00c3c803450015a4450070b1190314070903581c01402d428242d14062000f44010b68011813420f5001000300100340c240400c5c0300040351141c21101a00128055134900003000a60120003948100c40c0c0c15002c0c00e038559500c090030307580c1c41c00f4031603e51203030300602242c4010f19004051020030240d620719000841d0316611508c9080021980d600416441600030108050300a0711203a0303c55001c02d04002e182ca0300707403100903030b0300b210100f6031a82c01d50006040c81003091050070a00d4080000c3c010548030000903501a550360300100055011804000000590706045280300d42500d1000c0c0c0903d0039501c0d103152000c0d0a03040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 31021507 1250 31020257 31020259
    0x1b0409020a0309210e0d0209040f0609080304030903021804050d110309040c0206040308090d0e060d0e06070908010609150302040b0a030f03090315140f090726062401030506 76
    0x112000340300482d00c03c8158102d490710024100b005401c031200007400c074000411400d801040014006c4000d6a1004034943d4029001030f08800d1034201450940c0040802147c010b00d800300110910007407560015040701038901c2507075480740420f01d41060b03190003501103038018030a07070044801c04a00d40c030403054035809070200340490b030400354070340001000e1303030994058a001603202c0000c00040c581e00039005a004501030002d0110710f01202002482c104e0100210750183d080002c40c0240d0704502d50080c680202100c064468506020b03030000c1003c2020701c80d44d02c840d030a02c0c0001c25501c10500ca00e06100c44004130700f000301d0385140d00b804040c0115444203540300155000c000702050070340b108024414031070740c0c6410b00c06085103400e10300b40000a1006842c18500a580d601d05c890f07110316541c2040d900301307504801d5a98204418648012600100020031044e0f03030031a011400f18a4000d41c407400c16007640e4080d6141e03814100c81c00c2c20100704062001028402440c0b40d40294401500070304 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 31022757 1250 31021507 31021511
    0x30506030f2109041a150c150705040e0414010507091d06010203041701061509060503060f060408010f15060e1809011103041b05061608030603010e0a05070602061b0409020a03 77
    0x90a4400a400c60b484031034001780840200d904290180b03000e81840000540d1400414144000e1840315903403191540e03070306e0040081e441c02060000b8010000e40b4010040240c0b00d12641c9868540b817a501d800015410383d00e0740c00d120100f00d440f03003c0e4419006a400d4003c982d0f80002241e03080c3c400342ca030050201d42c1903000411011410641c1c1c06404244612243d0020500e0b1345080300c00d11420b811503000300c040200c0c4250078040c50354000b04a035000b81c1c04a89568440410100241461040d03500c282e0f03842d80782540190b081c04194210703c0c2401441d000d00e000c401d946800070340304030751500c0100d940021012200d8201001580c40d95070000c0c41c010000a129160060344001980103075020317109008441000e003040481103010780041c00301990350340d08020307221f502d04c065101010401003586002000142075920250f02220007200000c04545c422110f07400c0168880303003a4010300e401401500c001906400a00c91100302c0e540c142003691703207070a1500d41ea09000350030094000341059 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 31024007 1250 31022757 31022767
    0x504061208070f02040507080f060307030c050105071a0108010f050a0b0102071511070b04170c09070f050c030d05040c0609030807030e030109120f021005040807080a170901050601030506030f21 85
    0x80c0b05c510a0a1290010f501c580c0340e2070500e00b58034550610001c3c500f602c242d02501e000d1000400d801c1e03004089038130a0070301d2515a074451601030003d1120b1408900f00248000000411100540088005c1c2e07200407410480741c0c1ba0f0903444400c2d0344084404e240903034088941003000d10060200f801b00e030512450300003802d205152016081a08030f50100203500804a410301c94035003104405a41c03206100001c04200b0300c1100410a2401c000b040141406900c02c96406d00b1070042e41280c1e504406801982d07a20710f40c1c8a210030040c84203a03801c0d03851000300003012840031b0056094100b41d90300849900d003450150350702110606607148100b0b80554890201800041c0241383e6810150103a48419140704400c120091404140a85081c4807908100c01d001c0401c520001b00d072086600070fa2407e544524244c0281c1c0d103000e9a04414090b0300748682003240416041d40000e0190a003641e091080d038890b001015034800c603a410f4003001d80c0150f6020301d0440018071500e42c140c114801e42e00e040c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 31025257 1250 31024007 31024009
    0x901120c090501030f03030e010507022808040806010306060e070e130608030d0902011d06040506031806070201020405030114041505090f0f01020301050307050d0308010b0f090d030e0306010504061208070f02 91
    0xb540d402c3c3d008403405101807281804040d0140507803001c0b650061700802070352610440c002d6503040b10a0b0101e0340c0855400344001c024020041550445401400d220380c0c590381c9a210951301c2c0c000348001e03100700e0302c0c0c40c102143c4c881a030380e1035034060001503881ca03000081540c1040b10651428000040c8543e40b031200003400c41c07007400540201501440c0c0013401529600014000f000f0300c49089942400c59919401941d0311902030300c0c280d450a90300305031259169048050342d0805000400c416100e01c4041180c4a90305400078400d45105030000e120b040e4118000720702031842914001d200c0b15a8100030050310301c15510032548501c61f00104c0d010b411801001d40d0030000d035009401e00a940010041c001810100700c6900200300075148035800b10120f4400400b0903d041c001c04405003800280d0940050b44803050703480d01980185050540c2d050f514000d44184614405240240620000026a4a024412f080c1103a201680d1084503d141d580d0341e880e1580305800c115059003084040e8009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 31026507 1250 31025257 31025261
    0xb0c010b091303172a12101d0105090a150302060f04080705030304060f08040609051507080a050403230f12070816090504050702030d090501060501030e07050901120c09 74
    0x41d90b450000169030505500b001004400c140700c06982d000211001e020f0701c1d5617107180c6504080200c9528000c640c040d80441681442001000d00d1110890400c1c8034031185211079039411602d000b02a1140b102004500981c0800c09100c3d80d9800003007270300002c0503110150880d07000c003000c021052a03100e441e54000381c0550030621101c0381c03c170800706d014010f000040011b4009060220002c50426203400c01c0141a0b4803031803009803c201000000c03804010460b00055010307507210040d1089002c5500c07201c0c640003c2242c000c8005184000403850505140c40707100e00460b05039803828000c00c180d0300402c0708030522900114142800f0080c01d024400c3d00f07006001a000e110a05d44160f060080c0700034001074001d0210f80f0569060001d004400350054441c0b403c8810654010a80b40e455010a9013035012b1281800400da0a00c00948204041035004000703845007600c0800508500140c1c0c3c0780e86400398001c0f541c1100e1120018007a17901407103004044240315898820030705407541070b0441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 31027757 1250 31026507 31026511
    0x120706050a030f0e071a0c0f0109030806090702120c120304060c081b0414040e01051008060709030203120c03070f0602070b010509040807030c0201030b060705070806070203030403090b0c010b09 85
    0x400201d42a107440340d15004408060104400522484c4030b000100703070f00c454040c480c030b803070001a500300010481d80c10015141d490700c0810a403200800200d08140c041c101c1c0c090704800240c2d1000004400e0b00c1c0c40344542d40105041e50040c030071a1028940700c405a40303c00690001e612801000c05940d414150045100d07521680010611110030030000c3c1c403545002e40440c500b40103140d4030002055201c1d00359403c42d41503040d50050080380e480460001c0c8100b11079144194200000c0041d0070944401d00000c4030642c000301d0f000b507540c01d0300441e585412800700031b6040c1c00801034000c11000a601030f03c0349414031000e0f240307044c0c1340d44d0341c20041c0400350104840b45070300410500d00380410031040d180140400d50310030b0054070300b5541e20f4050384206900142031100a448103419a4801c0c0d10045448401070500d540d02d11182c2400c5960381480d2140521500c42c8a00150000d403020040d41d00555041d19010b0a80342001c407454031640140c5014403d43d0340e20311203107000d5035989003294 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 31029007 1250 31027757 31027769
    0x1009050705090a02190309170406030e0d020d020316020a0b0304030c0309092307120501140306090309180414011a0319030806040207080d110a1106010e01141207 71
    0x1151a614203001c2c01110000102010f6460340b050050304841c46a500340c0030304480940c900090080141c5c5000c400e6841d203120302080130300d03012030082480d982560001741039184000865140c90390303103c422a540c450403071181c030040c1c1050120713100304900d0358540c0c81c0040c401000b502421791500002e201541044806030000f408210303155050541112499001c2d08840d6000e205642103031807000b02c4e02004240c540c1e0000500400070301c41c24841c807030807c00c03451118028091540c0d1880c200c1c884441c0095864424001c0c0700100f040d20b10300000310340044c00302411a24403120000c219101016004206540b05600c0507000209801d0038400c00d100c1d0010421204a000014030034149019600021801c1503080620b0b444003003a04108400c0c0c4c469021280940c0d6061185410070070341c06120403503e42e40c1d0a02c1c0080304402811405407010074466610349500f40801d107400e030341e03070b08081c0714002c1042101c1006210444d100304e40c00b100c2d0040500205030202100d8201131400e65258011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 31030257 1250 31029007 31029013
    0x50607081e1b0604020906010f020f01050403210b0a030803101a030403140705070905070c0c0311040c210b0f031015230d020a0803130905010e09060f04020102100905 73
    0x1408180e5152240354000982c524001c1c0080c3c40c0541c00b08400344070141241e41030221020725106e186108220003900c120350034000f4040d5081030300d13014006102c000c603420890720a1401440751401c8a01c94440c2004004102400c120f00c0d54465490070750010300103039060808500302080351640c1c0100d2403400c583c030f460708c1a505d00e0182030080030f0035002c035400c4100e04000c00000340814000100c00090703609900000815032100d1100b9541c5202e40d03d0020001032209100105020803090440321485e01030311300380005190742904444d01183c1040e10103140314090740020700141d0301c0e80400c1415401031700350030403260918000791418010075114034100740c507094030081d4440e180b50a00020304041c1c0b011704020b5035201e00c030031103601000090f50041140b198600d06641c0d590040e44028200308007684c3c0e80c2c181c0c0c0d040d1160004c1181c05400e4043d803c060000070b00d80308405506115042c280060f110a841e007204000e1a8140600103904602c070f4480d40401e8603845110b84807101c1e101c1c00003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 31031507 1250 31030257 31030267
    0x120b0103020c0619050c030402091f050307080303010312051c3b010f0b06070b100302060f0a0f020a08030402010e150a02010e100603030f050307090305010c08090c0a0807050607081e 80
    0x113050142d40300203064084203182401448010381b5031801150b045288100486002102001c0c044404410740c0e2003543d151084540000782405c3c084015810b072402110301052684c0103000544207486088001c94641d6080a020700661a05900100f0b5030f4140d141c030b041042003100000066092920488400d15400548940086c1800d00c140800303258405010300c00528081f0000e00e003070041d04409803102d9400c20024440d402d80e80c580901444d801071416450b03250358004240310390003050000005c521303968003880140b0300014000c0c0d900307039000706110b1131aa22540110f8220ba901d0170300b9904a100500078020307420442020f030200405a0340009034000e80b480c0c003580f0341842e04605401051419030144080382d44030340d1401246055082c40e540c2ca480d030b21007c0340e05c00c0306544003034010b5181ca0103480c0e015520043c1507005554040442e002c0305059410441990090b101da0640303130b4840703013040041c3d041c043c020b440741c903000307000441c18035007040704450b50b0707001d00c503010182040c0005d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 31032757 1250 31031507 31031551
    0x20709060f140f0109050d020402040308031302100503060607110105070c03060f0c1e03050903120f061503070e010f0e0307090504020109080303010f0306050a0b1002070312050a120b0103020c06 85
    0x4918403042c0c10855803c0380d03202c01d60001130420125801039502444090041c08155203654045800445d0f2103c45180c0c1e03403a107031008042554180300124407441c060024610081d1003242aa4040c1c0f6006010b1490b2284590b00c00d4403048003000c0d981d060200600940e000305003500803001c02140924030100f100c45101d1b5801080321203001640f01400202016076441d0a13800d0440d02c0c0c1c0f0515810001160b03120424814998000d07001c07800e4803040c0c070030200010210360001e8103004140680c5d007621705000d040c2a00103035001c03c44c1d0000000f245c1c400e4080c6a58031610000c41082040e0404000c651030250100c2d0034a620350b00f0594000352200c1c107100840d40d0040c3d004000740110300144d802c0d0350410380100c1050034644000751140d916107000c070b03041c0036065200d4454150002d00b21107070300e003001c48042d45510302440140c80082c00001280461400340f400c07503c4445099403050310b40d0001568610061206034022410950b09010140b070030081045064042c5910440491079858190 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 31034007 1250 31032757 31032779
    0x30703050108010b01050f1602010e0d11011209080a0c021c05030310050109030305070f060209060a02010506040c02031e0304061103070903050106060c0b07051608190801050d030519020709060f 85
    0x4c3c0040d041001c2001b02c403846110740707001c0d0b0703030410882d00f950b26184c1d00b14001200c054103804115a4044505070141040242d0743d501a000502d0a8131101c5004104003800e001b200e100042c082c00b008403c010103100c45124040d0101e81d544014540b015a409202c040e095804010504445aa00010a02003628200c2d15400300505003480d204084a04640d001059402840c00043c41d2101b007814910130040c450301590000c00c0f000d0a0fa070303120f2a0ba000000e02900058a20700c1c0110310382007130184030a00c0841250110b01d0700140c1400701d0310005180c2d2003154070080c0251962035407a030b50b88417042c04601c0158010351413543e412035207505508009003150a180c5c00101489600003041c000202c00008a591010721030070415102e038122507000351302c000382d00301c001c08850000a01742400c1481741d12140c542d91080c0d54003e580d0303032210140448454002009000319600744080400c134030180c003624544401c1031055400d0169140d034001d099a04a41002102031006802800305816071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 31035257 1250 31034007 31034021
    0x70207060219050a03050a02010908120103031d06160f0204020c150109050f0f04050307050a0503030a0e0a08040e1e010609051329010c0c030803040506010e01030b060f0109030803070305010801 85
    0x10032190415002c0070790301c03141d407075030700c0c4900400b401008104c18140d24001c0d4172140e907580c0c204800a5950900c04200f0b042c2031802d000850210322000c08040d006005900a10190007000c2c010720300c0e11003a01d91140480002d078804032049442199000300681361070005d0050385410b071008242d04c14100c00c50340350480050304500801840c01d001c1005690b41c129045401c026160047d0102d6210350600a0a5108044000d483c0d40b20301c051400c100440080114440c40100c07104001c8013540380821a1101800303600a0702c213060501c020302011100103e0203400840020030703d03441e000462440c0d105000d00342d0215010803c4a0400c22041c10304030b0550290440da40b038100100010050596050403c4941e60600d880425441c031032a85d01840c0074440203500006503048441e580e15142038145c3c000c0701c040319640203200c000a040b828200143e8180c0380d00000250155440c9000c2c00105240d02d1041410444010400400b2645100080d8080c41c2c0540c2c0c081a25810000c0701402d40e645 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 31036507 1250 31035257 31035283
    0x1060303080903130302012006100905010f0e060f0a0e0a1b090e0f040206040b0412021305011503020702040902100e01080f060307090515090c04090b01080705070b041a0702070602 79
    0x1c1000004c51058031203000801307807682400c0000c0320205824084001c02d03d400600101c5108140a200741c1556607840c2204440807008180981e82c0ca03000c9403038110099104442005a00c14041000382c50178507004c1042d460301520001030305680d0140400c2c07101c02076501d01c001c55540c2944104a40c4c900d01c0e05083c800541c1411003480303207041c4420320303081001041180d10410b56030106045550b401f048800500b44842400d403901d0712a24000900300400350202c2c07154641c201c4c2c07101015928020f050482d813a000502441900c2c0580076070280d0b0141d032040781c0c800d035180030400040c0e490b90201207501105664444c4400b18400001d4043d10011b0a2481c10f014032504210250354001740300d0040e01c41c21103001c40d00d500d0340703405102c0c8146503000e010f6001e42840202b082c0014404050300c00c44000b50001d01c4101c1d40080152018003007910b208000841c00c0042c0b00101c0c440e8890160894410800b2903a040303589030b01a011005c05842110050300200c0041140701d038102704034000584 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 31037757 1250 31036507 31036513
    0x90d090506040311010c0c0815130803010e09160f1701050405061311030d0c020108010b0309060c16060f060f08120d0c020708060403050d1103190b0a0f08010603030809 74
    0x104200025165000b1440003c1c000101c1c8025a40140d1080c020700741c00710b900c4046007050580301e0012540b00c0824404511305040403c0004101c403450745403c07510f80e9002040d81c1e182d6424070141810701e4100415600982c819220031f914080c0501305903a0017001c81041308042a810058100c1d00706a240f03541d181c06a0510050102060303004ca17606401c03080100d01e50001e40e0081c03424003180c0f0f844007400340c0d044c0241c64014807441d40200d44808154402d84c5c5045482c1e807600b50380b0f0380700d00040c0c51032a025404203001a40c3e060400000300702260340c110f1503900881c030300c0d55510151501030404801c01c68403039908001d003480f02c154110140a000c8007506940c94520400d050500812544048164403000e05030503e9000344454000381607100250b4106150500b405032255104008403d94140380800702041010100d00f034174050840106481096448074148101400d5420030440d4400020741d000a000707840f414056000304211070000c2400c42c82d505000c2c049080c010540c00480d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 31039007 1250 31037757 31037759
    0x405090d020d032c0303090606010203030112020105031308160203010b0402070f02090a060f0602010507020d030e0309090721090b0601050403030c0b04060204030f0506090106050114040612180b090d09 88
    0x6500402c030318199078810710340080d81c03910380f4094070114209503403411448903007000702c0c1a0340d030800701c01103205500f240111b90041d201d480049035a0321091203180440d440c0048a000191712910040d50040e0011040812507400c070b4541081030b9000e031045004640c0403424000443c1000c0c003070880c07000c400301c50450070b00100340c43d41c0d03115045244000b8420b54210b8000382c445d0b8000e62022018190000b4428401902c4e40c1001e802044213641c200058890340b1585104548203001d4900524854000f4600300f2812006002d2074460203802e02040c052154000344040e840b600ca805005441804086008112802c0a03400c03c5000350000b410050300300028800300e500322426440c1e00d98030040801c2e9941d11400c00d90000e0041d07400040107a846103c04409010b40002c146000d030810740020449035030707a00c005550400c494200030081881c10704c800c000c2ca6001e46084c42c80d030f102c4001c021a500d00526203076042c000e400c0c641200e0f03d18180c010b105030004200003140300d80401d410b01509007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 31040257 1250 31039007 31039033
    0xd061410021f0b040e010504080a080a050c09060d0e0f150906010803071403040e07051803060609180a0510140903030105060d020c03160c0510020102030c040608060a0f06050306040509 81
    0x102c41804103840e140d9894803c1110240c03500d52040b465070204a00030007050410345450703901c0c1d62100040703c0004402c08003049070f8560703034401d4500621801c08805c3c5480008014030119801c0058200700c0d2540d11041359044210500c880c1400101980150405862521001c10480310140c00f03400580d00280042c400450000f040360792254011440c0710400d54003086851862065800490000c145038050054440d00600903001c40d00084466950724040c480c107044d0303644022a00140d11401c0b0b83c021421340e8220442807404401024103440202c5d00944403145011a000641c048555450034022103886042c01100e030012503040c050b502d55407400c40000c0e0b5600440d40c0b00b4404980c001a0003501c0d180c100120b441c0300a8080203412200701c0349c1001d81720340d4442c0c40740b1b034006e1948902240c0d85034418822207100b95980e0600c28240740c203002d030840e810301d401804150002c0e442030002c03440750500f1180e880100803a6450a80c0d9140140600c0103440b805000f0010950162910401c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 31041507 1250 31040257 31040293
    0x10e0304050d02150d020c010b1f0e01050918040f0501141009051005120f0f160b090103060513090204110903060a0b13020f030405160b030117030d06141002 69
    0xc2d80781c044a503883c1d1040e000300f1440142c41040c8a9819182c4000f0b139075240740e481074203d44404001280c200c01a0f6090f115902c0549601008090010700580d90b026429070040e4041c10f03016001a018107180038050b00a0000d110040e2020754842040c1422201040001d00a20080c42d480388103c8459040c000454074024565005410300151180c000440004080d0181d00051100400651446840d28810780e01c0d40401003800d0700070702900090200c500700004601c81060103085420381c4040c50072416504540146050030f04040d2218800141c59890311130000a101c41002d0004000c21a0310402c0102c908201403ca258071080c415460f4603a40490300036400f814101010920184100000742440950021740700702e1880821064140c05405020350700c0b95104104a8400c03d100f041803904041c0f96101d40c8820940070070062007810701034513005a450030218101ca00f00442000d10030156903a035040041042202840c0c06000d00c3c103e800101161a5400035241d000c0100c40300541c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 31042757 1250 31041507 31041529
    0x506070302030403030e0301140f040501110903030d02180a0303120c0206070f050901020a02130c090b030103020d0f0309030602040b0304030e100801090b0f040504060b09100501023c0708010e030405 87
    0x2406100d86c6248410740702034005448082850b85a00301e149002c40001c0504074003079500792030b40c0d882c09940b41e1300301c0c40c0721080700da071090010000c0d414107450344c0504020f9442081d00c02d105441c2181b50f540d450311038070700e000042e43c800d07200c014a01c0005140d000441d0f039000c0495086501c0385007030040761a0481a0001c11003103910f480f035601e400240040c3d01d003024000d1700030341003e4180e0380240301451551090758240c40d10b80c1c9400d1060350700d48030f4a80354082804040d61100e05040b0101c0008d410104084071280b09080c1990810fa690311400c040740c20541c4981020b500c00410841051342c0f10b80a04c1458108031000071f129129820024003100701401442c0341075136546202c000310350310101080c0c08031300000c02c02d000619162a0900c0607103100580640200f1516010484c0741440c005c10b82c05998060b0f00608215010f0031085513140e480010030000d41d90042844240041001d10519003a84020010050f0302d00c0e11800c0c07400c4070404803940150741c00900c814410740c4e4034040b07036170 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 31044007 1250 31042757 31042763
    0x12020c1e0901050d050f060c0a0e0414181204031506061805040c03140a06060906020d17070504050607030e010801060302040506040506090103140a141e0f0403140a03090c0506070302030403 83
    0x1000b1413480c0782c55450640034404002491150704104407884c0083d00040210115580d07549034001003640c14030040d900607690013001c81c080580054050403132944d02c0750480c0d4442e01207610200d5850707401da029074030a420a0300c9110001d02081c1602c40607000d0380d0000d107a40e2801001c1c048501103601d5100340d403070146900c503549a2080c001024820b030056080b6401031041500c480c10300400450007400300384580e1340030400000700010090300102d00410240c0c41511881e0030030813030070595101c3c500000c00d03100c2031210510010411340ca031070b8084c0c144188240c03200c858480240c00003414000c0168002410107004005c2446140c82e4141510102d401c203071481340d12022014010780240444001071724040d4003107820000c548505400c10400104030141c40d5445454280a40c1c1c000d0801c3c0c01d41003a0180e0300c0003c90181c149069501d0b5000e4042d2408560711801c4282c904041c0c1e021075446800240c07900b0302c00e004c0c06080c00b222001480200d0358545007d0299074040c0d100d0280748006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 31045257 1250 31044007 31044019
    0xa1d10061d0f040609021305060702030a030e0d120201140f0108070902070507210b0a050f040308040f0b090d02010e0f060601120f0f0c02010506030c1f03020712020c1e090105 77
    0x680c001c0c1e125011030369003110307005000388030a030b844814050003500012200520500c0b54080042c00d400d001003100c0313200c0d0300600501012005034405403402c02040d0100c54103c05640e00c62408112921100e034020640c0ea40003003143e4100000c20b01030318030085c00000c14125854010410fa0000241d480c0444000603005601c030f0740c55090050625106900c141b2040864a501001c0b108400307000c10305903840b8500105240e00c0308001c1c4400c031442100ca014000f10904d01007800b0a000c0c03100703141e04c103110744c556040322905580d402e40110001d9540c82006d41c005018400d00c3e035028015521a500d4501c01802d4504607580d1140d942e40c005030440f4103002c11540d83d48130240c0c10343c0140000100c03085040c0511910b80f40c20308000d050501584e40154601000b085c4a03140c00f1900700c030304a03001401d80c82c9080e061300906111003020b2468001741603007080080006140c0603118005140550094285000010248001501c109000482d4101450003504d02039407005100da06440090303402d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 31046507 1250 31045257 31045307
    0x2604060f05040b040f030201120c08040602030402041b03020a03110316051309020703050403230714010c0f0501091b0608070509040603210e061617090a1d1006 70
    0x8107540e1845541c005500c030b400c0c001004110a60490f005e42d040303a01c00e0b80c2d215541d081501843c822101145c0e84280007070707049800700e000300e5942d0b0090364029000520000320b507041d110b6a4024000300c0c40044c400710750049050a00190588603400303000c035107000e05c03a14600e051407841d0070746041c209000060120114024684104032a00c02002c0c119411085540348141d04010349107420620003192240d00c6d02e11503540386a5105010a0407a00c031728001c03c042e600b4a4002d01601e0900c3d610f171410490740d00100c81c00716050341d5070020700078003030000058072809509102842c184081006040d84116a104200c80b41c0d100c0441c6902821601d80141c0b18004240014041c01241d40080c201003402403941d100c140601c0c40030740c1208001d0329400c0000001c0b8040c40010700545005240450415415502188080300c02d03400c800b1900c0c002030315161507c400580034403040d4112009909e5201c4800202030310041c140781c1c00c40c41c02c42041c040180b920400921b02c107400003400c41403c1e02125 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 31047757 1250 31046507 31046537
    0x606020c19030f03050d060b0a020d080c0904090c1701020a2c0d0506180c030c010c15110304051005160c0309150302070224030106110304180207260406 67
    0x200d401c015640c8501d01c0340004405090041150b000941d404540f207150240000398030403800708840d80310440c3d070040c3c10441c1d08801c0a9507502c1e001004020458030400560102c1d42d580d02c590441d0713622441c110440c95040c986019002d5801d4035000c000c50b8410800d401c001034001e01000c181c2c2e9203403c01c82c5a4040e8001d81545900c41040c5580e070014100b803400e400700314021400600c5801e4444080e0740d003400814800341e17540c107030301017054041e00100301c00780d86948a420b0b0744081c94040c2c400080900b0f500d5801c0c904660640d50480c3c40301034040103000802030f041c02403a806010905051205081c40c007064841250181c4048051243c1910414200750141710050000d04c2c3c203441102d1203000e064009400303980900d0089203c0c116580c5c058001052104c43d111601120a242c0c0381180e007002c0080d00e43c0200c0000382c0001b44024080000c484d40c1c5400c142d10001110036001da203482d124030342000000c0d91100c1d00000e1221030740b844418034900005407403c4846034a003400500ba2803103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 31049007 1250 31047757 31047799
    0x40b030c130305100911030d0504090b150a030207030807050909010b030601031803020d0f031a0906030a0506010803070c17060a0506010504050d1202071514090109080a20040606020c 80
    0xe88010294000c1d04c95648140c4500c0c2c3c80203910b00d010b0140d00419014140400d52504a8402080301081003803005105415081d804005014409007440501034455495000a60058020f03000025000100103040540c4803408035003051150400740d04140351280001c581c84014060740070801c00c0407000542580c8690480549040750b07506042121109060003500c0d29110514400881d0000f2503480c0034900c00d101305100fa01d80400c0340181505c6a9040060418020b48040d60510803600d200e0301064003801030034000c0c0000c1c13006603501d030003900d04030700b03840c9240d8020251200c441b012506440300c04110030380d021a0504001a40355174250041e1158003039a0449504450084000802c1150020300b25608100b15000c03541116039641080c148520303e10300880025407514075204030910100c001e0300c411103050506094041d2501c044500d0540051026a04840c011340c030641070042082d4181d60882c010b07141032141700c1c100b0002035038a6440440041c0600000115034803030380c0c020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 31050257 1250 31049007 31049009
    0x9010302070f08160303060605090108040f291b181327051203090717100507020d0f1d090a020d020f0307020705030c010903080d06050301060f1406040b030c13 70
    0x100d500c2a455146044c1803100340c090303001d0210003092901c1e5003c40c00fa801102554810300d0140d44801d503c3d620b6a8604000d01c0c0700031402c0320800600b1102012082c2c44a41e844154648041c4041c164500b8580c1042c40750500700b0380901c081010452804009a02890f040307480300300b5540100b80444510080c0300a003540300c0700e002ca402100300c4800c14140c0103650301a000780128104d80c402901c0180d4800c2d079100035104105c991b4419201004403100b0381100070a82e110100a981e040e101d110f0301d2a0a544044074410b0040e04a60003041c0721039004600c403a03030a0040c1c60503001d0180080e0a6251503031140c541c642c070520b48040010b601c610a40c045842d00d0b401c805040d91511405100c4ca92260000c6c0c0380325000d40502c20f4040346a040020392612600016521074010350f1440d1243c007120344c418400041070907260310001c1581c1d03c09020345401002d0382d41c0c14182c540d03d884c2100e803429098401c841d00c6208200000c00000c047c11080c0c13500b04400070200e594942050a1501c002451 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 31051507 1250 31050257 31050263
    0x708131d010320100e0a0b033c070f1704151523090a050402010c1104021b03030106140c07060509030a05060f011404021c0c02010b030604061b020a0809010302070f 72
    0x4045480034164002d590b40d0505c42c050700d00d0750080c1d882d1214803509010071a503200b25811050002454548c4c07071100d0003245030521202c2038600b801c0101c560102d4500b00e0700c2002007030b45200d01107000c950004101c00c44030900e000c1c84040d0b01302541c0c2c8914100d2074056101c481603e81d038141e0005030103503480c07100500c3c203000d8030480403d07800b401ca0540c4c9800841c0c54400c04800740010018802d40c0100c40c800c550503501c01c2d001244503962649203100b07100709107230040c0d801c1c042c188803140441c1515400140c11002076461f580340800080c1210389960001d02e44d200d080c04007060403440040c5100907501b0382d003000d644541d0600e01092070029202d2029041c0d220303540910481444a074582810b841b05000c06001249502083c00240e20031800c1d0040f0b03500f404124105485040d6105840c0c45000f0b00c00880c3c5102c80b4400a440d01d0400d68050f030f001692180b0109030a41a40e0310b40403590700b40c0c00544200340039a110181c0b01e000c0d80c84034a06050300000c2880030410040300b0400103d034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 31052757 1250 31051507 31051519
    0x403120801050f1f05220602010507050c07060503041121010f06030b01050d06021e030103060b0103060506030a11160809090702010606051603090b0a02010b03060a05010b090d06020705030708131d010320 89
    0x641324400306c00103c01c40c420000036519140c040340400c0e00c40c1086032145004840200781c0b180c6800b81c00c070394a620091080e2059181c1480084e80303540d0303003940e10b04010b0804c1040f18511801c29030380381c21194859144107100e46808000c20004150820050443d441182c80c02c0403015141401006880341404000000706060580c0400d400503001440c1030360b005510030810381d4903010054040320582d00440741e2191060001a12118594100240030f6881614460030100c00e81000140d0300484d01003100ca11202083c841e03054104203c003d680118548000d1200d1440c164000e040c6215900c002c5042d11101e0291a0905001d15000001490a1101c1c076a48841c441d400a00031b141015609120380100c4001c2076903000309008090589281e81c0c01d032440c4c45445010449880045041240d2071030f024400301020803403c1c40070703211345406a2a00d030382d641865804d20b180c42d000e60b040301242a1b0300703900ca21004030952040506403a44801c4441c0c032100f061004010305800c400407103502c91 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 31054007 1250 31052757 31052797
    0x10030609020d080316090501080f01050402070507030203010c050d0f02040e0c0d090f0308090d030b0a1203030b0d11030d031a06070615031203110408120f0f0403120801050f1f05 78
    0x5500044105c0e00100b0b5a40c41012058584004480c81001030300c60345581b0101030300501440c07070320341e00510ad400d03c500121410a50b6941c0801d0940c0d2611800750b01049000c910070b080d10440e130103620fa070090f444608500e4207040c0f0400e0700501c4409040c6181801000c101a0800070450f840245040e412602d070034180710080c030700180307107080c1150b901030b0300d0007420903180c1c48900902070118540d10041c5002d0303641d8100105a415590812030503006c068480c2c0d110b4003152a243c200c2041140140254460140c2c1a0305040c61300b0240015101094900309a103a01f034013100c1c800105441045a4460741c9403001e080c03010182498038146c03620703020320343c0000041180c40c04200c0e0b500301d410345090209684c6129110300900940c42124000e0f000340300000701c0541458018402c0201602c0514284020a80003040581142c1c2040f40c408441000300f28a03182c10080b55801460100c550340d0b000c08103240862628683c4a0103c52841c5070902c8006000d07000b43c06071903000d40d42d480900080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 31055257 1250 31054007 31054021
    0x1403030c09040c0e100e01030908040803030a0608060c1e0d020a1e170117150106020a020f09010311090702010b120a060e070602121602041e0b0910030609020d0803 72
    0x141d80110207072441180340108020001c0d005800c84880c0d440c0c01822103803c50a4004151881b01008140c0380c10543d0f00c2ca00d0300c000800310800782010740aa5001141c8034602100c202d4122001d84c1c001c2e140d1a4002c0c2c041004140d40501182c2c40008203404840172900042e942e90514081c0e004a02011800402c1d5110301c40d50ac5140b52581c3c43c918400550720684d842d4060318014591010350703031008022001071202000010904403c001c207182110409c1e940c19404e4000120203070440030041c0c20107e0420107625002e040c4415650040b20069034952656880c024000140e8248034052000000001c84841c001c1d400020100d0002d0843d080851940c0c0c03115448040c0c00f1400c43c2c00d44d01c1c02114850900e0002425010340e0304580040042e00390303898501548cc0c11400341c1e100401030002c4100016200c41c06107040040401c070410130f44010a1001c60185c459040a480c000c40360001040460380c07951111800700d980181c00000c0306001030010802018000c00f010342005c80000610006d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 31056507 1250 31055257 31055281
    0x30303050601031b0f0c02060d0e030406030608070b03070e030f06070309140601140603150604090c0807021617070e040c0501080a090201020c010807020a0c0308090a0506130909140303 81
    0x8120000d07641001000d81c100002d00c1c22580128601300058510400d01c241280074007000d28640380024a0700781402c03d03a80212040e12196601c2103e95000490204005a054040c0401400c0c0302e10240098508100840010380002082c034000c2065a40c0b0000c1951018018840c00207891410340302107207030409010300545401002111010300d1028030b082421408100c09042e1901c0d07076145503813030080304100f15207500080e002c3d083c2c404004110701c0f11588e42d880100020200c04102050041919001510300640201060155040300d80004200c12035840c0c520180c8259881d024100c59903045030501d004080d4110002035440302c0144028800c1084154017101c01c01d82e118130003a85c0f4890400203942d2100c400a000d6441903107100141d42c001d00b0920743c131181610441c0d11100e5a41c0f160680d11800d64402c0d5800100021810702e141810403022000c1c02c000e5031070510300402a0803502d9100340611070800200e503079204020030070048a550508514252084070b8890419100c5524 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 31057757 1250 31056507 31056511
    0x111060f01061202070b0f0903040b0c0c0f03060405060c0a030f0204030614070203160602090103020c15060102061303120c02031303080a030b0d11210f070f08061603200403030305 79
    0x10203c0c0001036a41c5401885000b01c540450740b081000b205521968250543d05501900f07490090005110101c3d61081c03c0000d005404c10320304c000d00e491481501030040011085400e640690030070320421002c2040015100c0d04080a00742c060b9075880302c1107045001748828443e00300010b000180c00024080c2581110f841082d0907480c80e00f042e207a203941079a0703902c07407094940460944002d01e840030031030a80c05000b00100c18100540b9003e11201d015045c00307003e40c0f44d000c0341c4080d24280842568104550341d07002c2d0a03030200c4583c404180e1000386c0380215203070031f1101c01519a500c0e400703414801e01c1580c805600c03d210719120503480f803034104000d80026a04500103803170310000e02010720f40f800c5c0a00400c1e41148190301c058000308244a1002103000ca401039480601c4001c0e68065800c1150440c015039079005424564240a40b0001183c502c0d03110410a5015005200500ca03610300d60211014883c240000c01841480d108084000000404851914040340c00802d02d0740582000d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 31059007 1250 31057757 31057769
    0x303040203100b0d080903010f1d0601060809250e0c0c0609010501030c0e06150309010c02010e030a02071203020a02060301030b090607140d0c091e031505010501080408090111060f01 80
    0x48012103003a2401e000c0f502507a00b01c5034480d1503113075108041420003000301080603014001041070365180c40f864058a9040b6a03410103241600445441c0d10810f12491f4050190782c90f00c06030900740f60850301d0356540b0031003005040d04108160407890780342c201c1c1440c0060a02440344a0a45000e02ca00f8019070031100b1001054040c00700003e0610a06120340e0341680d600102071401103044c4001e03041e944000800042d0000c02d040c00307104026256101075031060021200124842ca1038200003425995604488000c41d0f01c180001c03641d031034001c20440c0603104005076545400020303041c01c03840d0285541d006500010000004014011518034241c45a501030088400d15200c0034012200344e03000346410495001c0a200c0f0035801e0301e0316008003282040701e03c1d0402c0b0103030f05d80d00c4075003103001c2d0418115144209c4550820800294074100300b828030003843e0800066140c00e00103805154000c2000344001400990440306030301070070560310031480d40000ca4000307140c00001180054030070300070381d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 31060257 1250 31059007 31059013
    0x30f030304030813020102101a041d0705030102072003120705060402010f081605090f041802040c170105011202070b040501050105091b0405090903040806100303121109090c040906080303040203 85
    0xc0c0344410b140d80108411356040c0c0c0145161200c03000b040c0c000740344601c40610020007010000e1040e95a50103404440c200ca5450302e60325140507103400f840c00410f60b01260180e401400f80070041100f00d818100c04049810350710643c54925800a401d040360700d043e00d11804800b0644d03100340400052102e01c91031007030300e800007240c62014003960f074440b040b41c05442e042c0310032002c5803196101c1c5025040300741002d02612200780c10500000e003139401c2c262a0581c4a140d1030309034000c2d0702d0a4050000882201e0501c0081c0c10701c8070500c01020981401080e040c000803540117001d540f65941102c00c1c0d07940000d141411070416240541c06050b082c03281c0b40c0310315060000700e02030441050301c080100018200d20fa00d030525003001c0c06a0650f009082c1181404248000070b4059410710109100d84040c501e0780b44910304501d006040603032103c0da0031007030514088002c018500d65204496203041c6c12120a0016920008095a03501c25500241440c0e404c00d40d0000320741d84000701035401b0798821415 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 31061507 1250 31060257 31060261
    0x4120210050405060306040905070f08100501060e03070e060303040306180203010c0203030c160c03080408030a0305100501050a030218130b03010506120607080a0906110417120f0d0605030f0303040308 88
    0x100c400e4002d03401416444041000826100e24181c0d0203162038510501c1519041c076650368502508010aa0200115030071035503494122081038855035000d040f160a01e18030303001507140402d913210000e0040500c00807000002c11040d0fa01041628000d5902007424842a428641101542e10811724228041e60801015010403400031040d01d1250b060a036419017003042c44000260410440801955440c4401d040440032480c2d1000510140c100d41c1c0065903140d404240040c11110300411071340007900d289005009581c1c0c0001116001e99840c039000d03890b84c042000007003180070b40d200001d5000c243c02c01e1003458459150031a154514048008011a59505040c404500040040c0d0446501300500103490240900201c582004040794002180687c9545503011118505050001d501d008101001008030f400d032101c0441101c000900001c44084240b072070ba60091569415030b0401c041840300000c41c081d8400001010003d003100c822844031813805843c0d5000b0745007a00002c3c50500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 31062757 1250 31061507 31061539
    0x3060602060601030c0e0613050904030207030c1208270a03060501060311091804030c050106081606050a0806060313050303131703011a031026010501060f0c06090206070503041202 79
    0x20505d00b20b40c485440755400300c666141009180d51005002c010800355100d070200c3c0342c0e2913104019114920a40003002d2260440c04e00e10613080700c03903202070600c0c413020003001d00050700b50302516103420580305102030143c0ca80504248030480000f04641100c2c0e907500c0001400300030707040f240c121380e51501e00b08000c1c0b003a07070b01124092241d10705641d0000c4007a15009040701f240b85420360312902900d40300700c610b40d80d0356819095958540c00304160783e101c0715442c4002c052040300f4100234517640c200340785002c03d2254068880c0070014240c5100340008400100303406205c007006400325521100b82da030ba0b4175091018002020b4500e00c01d035003000b12844d01018800230201203a05944d61503d0122800071401400401d42c0d000810550114503500710004144031440100283c9034041460b0310414402c0489090031504160311100420640b801c10645090b00300e180349424075044400032510001034000301f02c41d881174407001842031000040006030305010351043c44404e8800c460030100181809 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 31064007 1250 31062757 31062761
    0x70306030206090603060312040b3a0506030c150c0709020406080f1302060d0209010f02010c090501140408120406030c0e0f010305040c09050c0d20030402011101021201060306060206060103 83
    0x8003009400040410802c03071580740c500c0103140d210000408032401e210121800d80c0c41600705501403140b441c1d012a1900f14a1481c055126040304207103009144136103001c016a80c00c04284009045056842002c9109510140604803a050026284040e01d5115082e000182d50206402c0880f900034041c01040c4041c2c140211405c807040da5440c95400c1c2c036001e0f200302c20780c0d81c081d00410150541106c1840181c480c0006022101701d070500041e290460600003400c00080250120110b9241548a80300d01da00000b0715019a84203190404414118443e1440c00d03110781d42160700c01d80310301240207000c082d4001c010019281c20755001d02c0a45034500e8252481c9110801103030b445101a100381210394401e50050341e200d03004180d200089503072510580126030040e40c08910ba40000900751070109007a0092080b41880300c004002411941c101302e04c541d02002d40020f0400c00780314090101000c0075010f640006e03c030640c58030b40b07650350751601030001d120520a101c090b00a00c40096101d40c080c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 31065257 1250 31064007 31064009
    0x50d03020616090f1203030f09080d0e0c030f060117160512100f0204051206090601090c09030b070e01080903090d060b01030908040306050103060e1b1e0d0f0b070306 73
    0x503800900860711002d54480d04040c04102d4070080010544000684014001c0c031540184000b40c07844400707000c242402001d44840300718841004c2d080819440000e402d85048950f444c01c40480040c5840041d0038443c14004040140ca905d44200f900b02000c1c02008283c450480d4160418045d043c0c5064000c86d0310361006040090350103c82075010072490808021604030718940d4800d441c2403840c181c100c030080b100d4404030b02e60030355400f140074820340c1422104640e00e249034030010318092806096039507440e40f05020307100f040c0b5101c503001c0840b1801026020051a84000130340c1103032034121b00060800c2e60510820f8006964400421034441c40072040b01d80090014026041350096515407001070002c230070030541019500ca0000d4046130040f4054005544501c1002c80c195255041c54800d80c1d10708440d9988a0704040405d40326018403001c0c281482c0300a45c0d8a200c8400c0042c071141d007000d40c0196864011308100018070422403001c9003082905d1052032003000e0741d210110101c0c03c031002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 31066507 1250 31065257 31065263
    0x1c0510053304080609070825140a030203030a03020316050304120c05030f0c06060414060105070318030210030b0901142206090c051306050306090604020c0a06110c0601050d 76
    0x40302030449030301e0040c000340550003105642c40c1903a504481e40ca880411200d04107140c01951060219040c28050481c00142070b80e55044c0c41c444481c18160f030310410380305030a1095400c0e111182d071616171002000c000c42d0028160303501e40c0f105020281c0070f98400c4170002c4100074100d4070f0640300da000e0015a80035941142e0607440c401c0e40120150b030300080c403130382c1569a48000c0c041c551207140e07154010b00b070011064014105d81c4c01c0c0902440280e070511a00607103e54035842c03c00038280d0b131010554030030a4141c0f4001022404191544142c1d10340740e000039400414141c01003540c9900350b000140551402d032102c84081e0303624422040c560340740c0020564000480780f10406100412540030146c143c10110020740303655600360100803202001c010602081012464a81100c0e1a109200040206040c00740c40d501e811000154a81c82c0184038070303c00d50340030801c020340500401c8014240c90380480200090324041218200e103812030908082540300d8140081541d00384510301c1c03c02568 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 31067757 1250 31066507 31066549
    0x1120c0504020304020325030c0f03050d2304150e0a0501080106030e0309030a0506060a08150a0f020d060e150103060b03070c02011b0609030809061501050c01021c051005 75
    0x304010030080654405030082e81c1c140b00d0a00e002c803000340054240010300c1070740700400b240750303203940f400b0007460210342c2c4041802c0b44103c004101089000c00c0b0218000c0340307481c0c03003d031020068549002e100c03501c41d40310085580207d804504a01c821480303200341c020546400303200740e05480c1081407103c51400703114009008440100b040c81e002e5003000c4103030740300182940c0c20301c110440030900d003215944094605a020005000942c200040e00c03c0180c004034000d80000b0b10307002e1500d00c3d0f0310f40c05489103581c0380da5800c224051002607030540b44903c0c0c130040240041075965003004c8008400790740f580c3c500954000b14440c0c540c040d20400d4102c3d0901c421060070f503503c40100b0380704104072202c16818054441c90003400740085070444400188111f0000944040500b0010641e40b4010300b541d290307510100910100000406401b000480d091805659501200e40400d000e4001c4401000344103072820070059100255801c104d00c1000d221506a084580c0c0348100100c1081c03450201e42004c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 31069007 1250 31067757 31067759
    0x1c0807030807141c0c09030b0c070b061804020105090402040801050f0411010e0102061317030a0507030528050a0e1014090102210c070f050109060e06010510050306030c1c0b01120c 79
    0x1c0c080c1c0c0140068091702e0624a001c540d0b2602c0b040040383c01201e0900301c001c0e000030310808211024400302c0e000b500645515035041802c42003040000c0026102034148000442e2100050395250100c40242c01c0b428024407841c14042a20044010295021110b00414000c1001d507544103100719154000168000e0841d1b0712219040c58000000f6542960f40c45980f41d880060031152000940c0120844c1030300044503d4a84002000c403000600b8000d0307200780e46401c80401032a888076418082c45101c00001c3c850b102c07152908024814a5107043d4140201c040c02c001500c02540204030f0401681592280f0356100c44945080f41f099403102c005690842d83d0520541c1c0e9030f805070035031084c650319030f1600c0e03c0c05a07241d040c1c44404030001248e46039103c60602040040354000c0038015049200140642c1d41046c0000300c40c0300400420404002c00880011003e580800c0380504c14840517107901c40c940c12104001e104519004410b4503848000720000840c6070203200d514000d5504402a84021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 31070257 1250 31069007 31069057
    0x3110d12020c070b0a090e060a05100f0201060305070b04050111010c1416020306040b0411041e020d090f0302030a140f04050f030a02041a0f0904020f1c080703080714 73
    0x350070200c44040b9030300c6841d00c003066011055000305030500c029110904810714101142414020003070207680980c2654100300315548821218030807600301810f080350702040c070603c02c900410312944044c00031b2061000010b2051645002042595001c0e07039501104041046001c0c01d07964040a20000607044003070322101001040e015001d10031200140b4941c3c140700f600060b14000d0151001e0b03c01c0000d02c4280020024030b5055040d0080b416982401401c83e40440111399003685200700342e280d500011115010406540041903c2e0f030302c07541d0103219101c2400c00960f00c4c0c118150342408038940c6c9500c860b0290b20b8030292690700c05020001881c1509010a1101c08280e40c400a40c01d07100d03100745140141c3c1c680c09109a0b0f8910b5410483c502c00c024010841100c6204000c41c0c060f03908a001d010140c0c13540e071200340004a0136500c02c48116030150300005c0c41010090060b186000100720300f4205070340300d0040c03030298165a40e0318140322000f003840c403264401c2d074007188500c0c10410450f0143c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 31071507 1250 31070257 31070261
    0xc030509210f0408100c080402031e01150e040209010501090b07020103020f04090507030c09150c120203091503010e010b2802010e030409090506100f0303080c090a06080403110d12 79
    0xc0310440204050800b1020150902c0369081034114182da0b8014a46030004074a003449510684809403515141d10304164010a0311148010014800220440200300c4006000d410802c2040012081c0010041e612404112030318003d81e03040b441010403900014556104904007025540050704651501a0550042d8001d511440d4008210312040c000069811709602c90740d803140000751004294803540d40d0000b4841030741c90300300800c409501da500b051313100d07440030314201740543c40380403481c80c1c51a00c00180e245020745060f1552001b40c0d0700901c2d1028106074040c5040741d14026070481141d80382c05603a0810300031010361031600d81d003802c0781c00754000300a80d1100c0c1a400d54000020705d40309201d0740c141141c1c816006411080d4855070301c00e0410004100c41d80d440030440000700701c114101420410241c0c4207100150421a0740008181d100c518082102e80302c00000b8840800289d44181c080d000c00c00403103080d408100c5a2140c0c4004a6000c1800f044059003607032903c5210648482c2c1c040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 31072757 1250 31071507 31071553
    0x30105040309141f0c0507091b050d0605060307200a020108040605040215040906061409060405010c03050d1b030b0102010504020105040909030903060207060605090a02040806150f15090102010c030509 88
    0xb0340002120040307800c800300341d0302c4c0d510091881e03503400b940444203041c014070304013a40d80110100703894a0f0140c01855100c45506041c4121850016070ba142c004c441000600001d0f048150312020010074009110b820053301c00d035001d000d002d079607070011030b808220f512442c00c1880039001c1911400010000348841c3e000d203038454401040590280d00382603404103a070b003043e000a002d442d40c40e9018440240c12903c04035980c2e903003c0500e8035105118000c03a520707009034810a410711500c8668602018010410b41d0b25104a040f000c000d40b89541703c1205030348060710900d402007032500070724803030a51041c00390758411601030b1201388c541450000d00100030000000b0603410014860408030002e0340e10f000910401b40146000b14055084c001049082e802c0504015601481008204440600800c410b68081c00a0075058605102c03903001c5600424420327103203030748400244c042c070702500094030140107030001c283c1c02001184616070055040b11420f6504d445160b1201c5807450343c4616040441c6c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 31074007 1250 31072757 31072759
    0x507080309031903020a030e07050a030f1509050d030609090308010b0d090f080301030209060d0302060a0b0109090207140705010c0f0602070303090812160305070527060408010b0f03010504030914 86
    0xb0f490003c0e220000460f2030701024009001980004004241a030300d4000c0c3c0c200800d4000240140c2450500000c8602c2c0e4203101c000c040140c2d290582080c8107800c2c0c080d441c01e0001c440306001c102c0300c0741fa100b17440e86000008100031a240c04030208400025100f241181949922104160390038141d40b10450b400c503070b001200f40fa0704d8003000c07400680e140000950942c442c031107150716541188108807881d80c0080880d8042d2380910407000119a0004d016a00300c0c1415030000390882280d0b0040380d03401160303000540128000516002000005440c944104003448284c580958484c001150410803550024100c03882e50306d00b0b5008074507142d0042048038407034280020141019900c0c0c940030381103114250f42130503003101040381c417080302980000440785034503080105140c40c81000c0d090b03018040c1003061400e608410340410b240e42042c42d1521490041c01c460312144da450070b4501030030290380ea19016443c04020708049040500070503024640c107032500c640a0b402d06604117082c0c0601150b403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 31075257 1250 31074007 31074013
    0x40806040312060f03030908010b010503060d031101090803190f18020402030a060e130c050312070f0215030109020d110a0905150904060e0402010206060904021e03031b070f06020601060507080309 86
    0x244c20340703050341c41c80d005510907200e40b00881d280c20300c0b00c0c0c210b880300c440d030b14180481081001500c1c5e0f9100e80344600e95615080c5000300c131032440096030050208690040480d2800801e00c94401000c41441144c136209080c144082c0702d00030002020707a4800091072810300d106210a1005151130340145a11041d0043c000501694404400e000300c03034151000400204103040000500a5691385480035010580c000d040490008034058210300c11003201502103020710850804540d11201107041106402b501c094407943c560405100a5015025240e4117034074191041d2410b04032202a02e80c20031a1f5100c2c0d40d03d080ca0441440150101d0066400d03111108101c0941540c2d1144245000b801440c0029244e52401d440068030300380c0085d2043d8420f01980d820040181d41d107007205074030350719003180c025007000364840800c1c603501411980720320700001c6410404c060100004e640040320010318944004954511003a40c130361100f80251800500c0801c403844c042a4410000c40e0051003481c12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 31076507 1250 31075257 31075259
    0x30307050a11060114090702031606050402011112030105040b011e080c04030c030809040b011b06021c020403290405030306010507020a030b070201090b0a020f0d0c020a020319030f0504080604031206 87
    0x2280c0d0910303400360410290080e90380040c0c0c070b01b401c0070842298030200300c0c0003c41c82c28401c0c440304116040d0900e8002d0980782c40b007000a003164481c00b10010941004022600c0e00601c4070f0003205590802d01410b401b940c9004080034081d80300301003041086a58801801504039007050032501c540b0b004140440d090070400c00000080c45000540004500511440c0d49451030101007100390388a0804540c10041e440b1104240c01400044410401d036009400507980d80c002041c03084100309865192103024408200017060150f07001c050549000d86240340321040104480443e4013500c00d50740a401507005100186455020b9030050142900040c40c058040d0350700d80c4d400d02c1410040742c0440c0142d44481700d0784100020a0070b0150040ca024400b54201260410344422038090940610400c2d41c071035400350320407030007030049001c040d40240a40782c242d0f140c00303442e003150003075400c0440009440314142d0071020b1113441600c00740d4400750040d0400e0b44030341c0c5003116055111540214055902c030742c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 31077757 1250 31076507 31076537
    0x501081b06120a1b050a0201060608010b0901030e070914181911060403150b090a0b0102151b04030320060714030405070f09061a0406020304170115030311010e010b03030307050a 78
    0x440302c40104c00399407040c0d0340e540c8280c4028203540395540141c003484080001841011500016109082403c0c84c0000703004100c00500c0e49002d0b402d42c88101483d28100ca183d81040d95840d10a1040001b0b80302e00001c2002040316640e07078544801441544400c1b21f03d29400a10000400020b0400040005041c2034981e01c94020800852032039a40e96a5516142c02032420074804990740410001700400450040000103925003c1500d2055040d43c4100b000409000950711180c80715981c400406440750381f2407501600e01d0f00d6203900c3e07005101c02413212070074001000640328410a400e0341e50b204500803500c9510400c4d04064400c403454040e0250100716003082c3c240c1100200510040070032150310705418212f48200e900c0701d40b00005400c03c820f05c60590004200c1e411107a01c087c903103003118480c05400340100900c1d580725139028450301d00001419070103c50032040c0044100204207032105000035038200d5250560094058106000041c003950142029050080d15030500022195843e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 31079007 1250 31077757 31077791
    0x20301050a020c010e0a02030d0f1b0f0308010b0c0a0803060607120206011703130e090a05030711130b0d030305190e0303180708100c03020f0307030501081b06120a 72
    0x110050704203603000c1001415a002400380e11a0303400b1040160000460030380200b5199030f80d9440703140030310208230b00488019210304101d40340c0d20682d154100d0100c4891800d400404054401500080c00410000c9406401c000071607200524600c001c22244042d1380e20504150401482561301084c280072500c080f030214001d0408205440d40a02150340c1400b080c10322050947c100d4203a00d82c014448049124541c0ea4503500399619041d0075181680c07040b013a28036107101e504004025001c04a00c0b4010018149100070800c6001c0724000080700341d983d00402181c5c8220805075202100e61a40d4022034083d0344416000341029010200e4003641c0700314507090340d01c8039510665a40c40007040103c4201d00c01d210003082c81080300030f000500c1c9071501e05c5981e60b41c2c00c00c440c2c05080d80d803040c1d0108a03000b54110764440038040c00701e80d103178603020a000d4001c0c0000d225441c03603801203c0904040010320245007000e100000c04690400d0040074000ea08004024200b940c0340c0e9864000e1880b1800301 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 31080257 1250 31079007 31079011
    0x2031e010f0905040c091508060108030f090925030507090501030b060d050a0e0706020304080d02030a08220b0c070c051002030a120212090604060f0501030c0302040e01110a0203070308010e012105010902030105 92
    0x1518941d04182c80c00031101d1030720300141e020000e46d401c1400380003e500e1003402263b9006904a80c00109503d9070142c0031240d56601c0001405400340c040305002980e010b81100c0c0c823500305a181c40001541d50001501511042c4001960041c4104590910780744154817441d081610791100003040400c00d191030303282040d1a002000540d00105d01009002e508202c01e044200c26440038509241040001915841005d400c0009120780c1101401514458004a00c20035421030340030241400d01c01a1031f18540c0c4843307400e8031442800340000c43d071400e008500d1154520107500840c9042d42250040b55070900d07001980241c180c007000340b540d03189100d90006010f0071250000d88a1401c20f4030709101101c8100c1d80c8102c855080800400c08206066080c2c81101d406682c0403450016450388240103010414010901d80008646541500e60010280440500c291504010780e40c03180c2600d641c10b4802d00c5000d014441e5000e40003401d0540010030598288130304000310f41d520455000038207452007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 31081507 1250 31080257 31080281
    0x1502010e031606050a09230109060606090501020c011701060c05150403260103020d03050c0307020910050307080f0a0201052203061a010c0b070810030c030602031e010f0905040c09 79
    0x2203000b03080c00301500c511a04094541000c00c0250f01942d207046a82d40644400c01c081100043e030848146000e40010f030300982d1080082001c15180d000140c01c03e4442d0040d45d00604c07515003040d006502410740c507450710140703034a1b00c01d040c1c2c644001114100c10890b8121071501414030f0902c0700c94841911071340618401c0d01c0e04404509400d115464140b201007240311811007c2004001584031401780d010f00701e8051400582e90010041214034510841710025040300410302006500d81800c2e408001361041101500c130f01d1541d13a9011666800350002210030740d006035144200543c0a4001810701c0341043e071140709017029005c0440315041d80381d4000d80b022510340f11401100411040071100075002400e001282003001d4544a426950040ca680107100810001c10741e80b400c0c002128001350b41c4082801d8100c2c0c0c50349042400381d0025610f045460040078a0b401c024600106014183c485034a50342c0280b84c548a003000c042e0001800c11740f204100b0040110320710f0014010807038500b107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 31082757 1250 31081507 31081537
    0x50109090521040e0a0c0e0a060c02011b020907020a060b03030c070b03061503090a021009081906181a180303040303020f0405060301090c0f090f1202040e010c0207030507050d0c1502010e03 83
    0x2801b0040581030880b080215449440c1c180000d00c000303a0450940c0400b00d80a10344010b00c00b0009440004d4041109c001940c41100202003002b090b9000403462012481408107100107030095050541d20702443c204005285c001440601c24010b082001e550f019900401070b0f419510a0101c0506a0740180c44005198000054840942c00d24000d030000700b0b400361815001041c60301401c1a1216104008101c3d51072100355414180580d036001840003111800e0000828111403034004006c5401a4008109001c820009105100306203c070300c0c0c5102031807010354510784c0c0d10758044000394004140f4030b0405609101c040b030790b92150f101950190404072000200d0f4003001001520014000c50241d0070055074040078002d0b17201400c40c1c1d43c2102c201c00d05030ba81245d10b03031000402504403e00000074540c81c00210030364060b800a00241182d000d04192002c131901c0b0004d11040812160740901002c039020300821002c1d6141107880000e00d024030001882d507520b5040d06013164060070001c0a000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 31084007 1250 31082757 31082771
    0x30313030b100608070801051e090c0418050402030703080d0906061206050a0509070510030b03010207061e201b0f0d1b12050a12060f0603050109090521040e0a 70
    0x207030b51400361030042d0031981004510717440c1804d002084c600c8140910750054409019192000b100341d4005054280024034400c01c40ca044114105d9640040c4a0b00201d51000c070480f0004000511a050095070042c016000707503070442e01c6209451b4030081d00f00141541da000701c2008139a8030310444e0080c1c1040c0321040390550190802ca4180c9101811141d407e03882c1c0000d10852840c00a007881c11031310155141e821501d224501a4003d02d4000d04007a01540000394440070001a60310010f00c20301184d15005200300d0b807099500460324007401d41c01c421040002e5505101e40c105000c0e20540401140e40c0551006d20000f60f81000290301000051342d01049a010340103030400d0f0001c1d02c032114900d06800803201e0361140d4120a800f0140041444800038100400e0361040500c9820021110300c28412140e503028407011602d030f24428540000c2c5040d00100d024030180c0154041c55402400074451200700b0345d40e81440032003080d070780641d8000410002440e00c00f00140a44a10301c01e80c40000c50b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 31085257 1250 31084007 31084021
    0xc070e0601020d0c0b0a02070602041724010605030408070f03080402130e060a020a110a15050f07081b09100e09130503190201180f030905010905060a0e030313030b 72
    0x44602400880c19034202d0604079411a40c0a1181040d06800411203c182c0e2079030455071009104503e00540486e00018002c6400c80010148481c900e1080b8111400c101100280d800000b040c1c0c5c400d85202444a001005050310550141da0410701802c0c03a03500c2c2c00d02980e80c51050b00d100c082c0c200c001c15409020032027035240040c29503c03071500c020b1003440310820300a034150316404000c00d001e41c0d07180d004c102c0d0305106100d02900ca034540b40c943c040314031055603400d0458181e407420075441941410000000c900300c030301d900214016921521007030f00a48a01c039030742c690000d08040d14900074005004141e4580d03504d1002601007442629404502442c7d603040c00703180c0d1401030414038080350b00155000000c07000800c4840501d80c5076202c5000038200f1108030301425080c0d802d0000c454803850114203202c810305a0941c030522039140c5035200b070b503140015940c403815445003d500010511030b2201da280260998540f81c00003e0a17031307161041310342c10200104001e8106495002c0704108001030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 31086507 1250 31085257 31085279
    0x9050105060f03060106050a1b0501060e010806070f0c02010e120d0302070b060f030a0f03020118030f0e121023040c03050706050304020307051203130e060a1703070609021201020c07 80
    0x40002c03d6015040380e41c100880a001da100c1c0040f080c0400144050103d000c41d032a8056095035a4414020300840c2e503a1080413800a4003030107080c0c6d8900402c804507003034a004100e030202484503a00c3d0140004219001501c80c4514240341a0b00440d00040c906074004041c04508205401a14016180c03200d0782003c0408007401015580603501c43c0028103400d03030740040e0309440140e110441607500401351400300d000d4541505404604003c021600042541140465154201c207507140503403480341408002100c0d0503c00d0125694010303500c4516242041d0b00310740308845401c6181c40710403c0c081c4da4401d0f038040895058801442d561001d0040040c18402c03c401001e4514116080d81000d400080c0c94034104c2c440d20b880751a01c0c55100940c18410310036144d01c520300b1441103046968610075003400100444080388540c158840c04902d695055030310915840c4600d0045081104541e154001404da07c1010380c1d0180da0201c0790000c24209000a00222811202a06200e441c0c211540f01c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 31087757 1250 31086507 31086529
    0x90507020c041401140315090307060c030b01090303031a0909030a0314010e0f040c05030307060c02070b0f0f0306060906040902040503070603050c160312090f0c05100f0806040209040905010506 85
    0x446107007040701c0c40070b861000b4514036041d1a49101c82c517101440240000746400030105d09400c0d650140d0b0100440d2140110160030a14080d280034082c1e000103050442c1115102c2c91b4240c04920442d0f001e00200340f10f81c2c8103215081c1c2c000c501c030b00c818694800148003c81304445404c5941d200050018185605004410b4820401d1200014550504440141e81c81c00281041d0700100003200280610070740700110002041c001d01070b06d0b40c64080741841d901409100c21038501521070f6010008000c00c08a044400007842070203100d0910260802d65007040e4009049294801410321084905594000050000b40180500103a90303a01e8602410b080c0b91a42d81708200f450300d010108001c07040903800b00c1c1c21412454001f154800c51038501521301820840d41010601c1c90545c6d00b000b0030900c04142141180a44000c0780c610f6500c2c0c041007003070101e10030f00c0000540c0d180c00701340055000b5015035401050080c0094140340c002c40c04501100c13407480090307c00303a44442c107110b07040c10145140c1d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 31089007 1250 31087757 31087759
    0x804030212010209011b03020709090317010b0a0e01110f160602062805060a09061203020609060c160507121a09010b0105090112150303020d02060a0902010e0105031f090507020c 78
    0x903003440f0b0644c002030a41d454041c8a07413481a02d103051001003510a000f428090400ac00f0100480300007400c000340340f400c0301c10808462811400c004160128280291141110315a5528094201c07802c0110742c0701c0c02415641c007052180700389030003100009102c40030114407124481a191460200024507050001d05000b1450344400241c80c155000c144074900100c0040c013000c2380301d071100e0003c100320100e00da00c0780c49014070b4000c02207511041000b1580c401b80c001c0d03003240c0c80e03616558070799929200103440c400c0300b0708403c10951001d051599030076003a46018000365200c450759940c4005907003800000440e00c46905095080c0400c590001040d003142121008019a0034200c0001e8042d01c106ca05140c10300c0802c03042410745441a822014100d035150310b8070090746a90f403801030366403550b18407000058006e8500141c4500e515201c1c0381c2500d03805070341c0d00d05101000d00c019a141d40c40078041c40c61403070b886000601414201029540105441e65001801e8600141c0081c10004c1e012102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 31090257 1250 31089007 31089011
    0xe130905060c0703120501031506060215280c03060603110c0d200f07050102071d060d0f050a1b08010e030d020a0207050a0e0a180b130c050409080403021201 69
    0x8200840e50008505901c1504482019511a024202070381d41030010702c100c5034400d044ca00084100034461401d4021014041e0003030000689a0500b6a03c030f000d02d015040481e00c400001604031101390200c039462059242040300cc050003880c2480c01e8031022009200883e07111201001200d905200d000a842d40c0b40f0346440c2000c080245503501d1308030740c002c0c240410090003000030051820901001e01e103c1c20000b2039030030a100600302038880f00248291409401100c40014000c001e12869101c500d030740ca980c01d2030550b01e500802c21003200018003070303a1a400b0b0108450000d1000c000451925000e01d41c241140b03c05c1c500d070007603060140c0c3c000311496410640300d156144000410341e50448040640581c96020000040b850106258401580322407240c1e000035421b2810b000d480d0149800c0c0c4401c0c41440241c02c0d07030b041d203e810341c2c00050200e00b125000400000740198290021031180444248103a80d400004003507644070783c402e6468210004d010801c40c0781c503c42400a8640900003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 31091507 1250 31090257 31090271
    0x204030203190b06040b0111070f0e0106020106031203020a0509060408030c010606111e0c040c080708090106050114030615041502060f0403080f070c050105010e37020c0109050303070e13 82
    0x600f030600d0b50290006004940300d860040380d40e07008417030703c1c1c000d007461000f01c5003a1913460b0204000c0048034812082e07078026250021401500c180514000e69030400344900742c1c444050070480080d4005203104041010a014140182c0c1e40e0000134030041c1441e900468960240359001821100c41d135009402748607050400c90302030000402d03030300d18600902c140148140f80d8444130320b0504594039143c0b035010345030040c440d94141d0002903403401510203581d80d031410341e03800312103d003281c0403070282e02d0110384e9140c101400300000070000c552089002e028001d47c643e0170787c03a4020940140c0c20042241d6041c102400c0b5080d410030105500400450002c8950b04054030b000d00240c40182003040710134155070004031002c0c0100d0031129507aa005008100a41e5100c03460201603a0903207030000d040443d40c4459044000c40d03011030b08040300c111034500c07006180304940b200951000c13420400a5407140d01030408030320188051441070b155501c40d8070320000000104242030800130600300c003140c94060307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 31092757 1250 31091507 31091513
    0x4060c0b0a0c2c03060a060e1303090e0601030e0106030506071b0b06063402010801290a020708070b0a081b03070e0d0501051003050d020c0303160807080d020403020319 74
    0x4940c03041601c03041c1040c2034000c0081070380010b0241e120300f00c0f601403180c0c50500c000b00c070705503000a0889410b0804810151140442d140028000220140000783c0c1020180101020511340c3d980000050400107070004c5000655400c0d5a002d81c400d0343da0390440030030000d400d5000b817041141180f030941c41c20200a89641e402011500291015004d5074012405408890700e185185000c10902424280180d00740c1100b5454400c0404080b07000038640c0f40000b9502d03800c0c000418403103450030092252801040000c00302034110070301200c214840c03205c2c009000310003840302d80d029048565413150390f200e0000300941224405801070301e10440d19100441c9034110305081c0c0781c01c039600d450218012261000001c40c0d0940b03540c0003a0003035103410113126810201041800481c2d10071804c1e18031800710391209a03162028104002c0e0180c00c10000c0c61240e41c10241c2440da082d02c00c00b0035500f00080e540b41d01751903420115481c021a035000400340250318042145540c1461b03800713811000d02d2801e503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 31094007 1250 31092757 31092767
    0x60f02030a0504090c0c0b04050d0215060120070518150105070201020d050904060b04060203031b0a020c0f030703060c0906030b03030310030308090c04180201090503010b0d030f0e0604060c0b0a0c 86
    0x480f0b98108140e4400030504042c0c031036104006d00580140540c45142014108140c9032200102d11001502c5132240031180341c1310402e8414820304058494070f04c010040e40c1c08500c05207002020100c28003811f940031405a884c0030f80d81c6e007001c0501045400e81d00e44a41c02c03030586e5040516481c14080144203030360060382c1c005440803001141d89001516131912101040c082c051302d800c05640104042008600e01e940000a507225800d06d103003414003000d030807004c04441c1c46881e0785800140c210b804084080d0604c0e00ca80f568070314001d803c9540482d641e460740410ac400302000400001c0301c0c020b00b006081c2c0e044c0250080300408402862542c201000108411010f602c0300906003c04031000521810080c00341c0c022462020380240b0018510318000c0f440440030810403400b01d01c958001083c42c2c24148640809564060030071711400080392026102c24025100003020001c4540b00e0308030946858014100034a0346840c1c8040c0b2001d00d142007800a01e000f010800020701c0d100c014401d2582c44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 31095257 1250 31094007 31094009
    0x30c03031f0510030c08130203030d0e0a0c0906060216060509040f0207020405010923010b160206071205090907020c01020705060901020114010e040b0708040b0f10120606060f02030a0504 82
    0x10940505481c44075000000800805500a5a103c030214a8101c04160141c001103110320b481d035614800c0c1d68803508174211034501d02c00b01a4042d070003030000300c95840055200c20b410400d820100c071081e0700d1507909e046060410750003003621241c5500b0100b2056404009200902d00f1a0350004121800d004005156010345040c0900c0380d500c2d491058a07252456045441c4140c01400c244059a1103040d4600940305a8120800d2042541c0407150010041c07032205050310b03440e05040340b500440b2001d00c101801a182c041e030740820200400c40001d544620f104a440090b0703141c854591044a0400000f43d100402c0380c0e056406c10b00e103807041380e039020505506645d411968507440f00380d410300403401480d00318001101314071920004128070f0030a00b100d0b44124414540c0c0318807035803051030444a0544c01d44000700003003c80c0b0041516490381003020340e800843d42000d45c081035503904684c14614103001c2c05075040c940e40c41060102c1640010010402410ba0000f5072800700c0c0301c13100030185c1c466 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 31096507 1250 31095257 31095271
    0x201050f090d0c0807020d030239040b221a010518010c0302031e07020a050307050d060528050603070503010b01170a110c0d020d090609030605060d060f020417030c0303 74
    0xa043e10302086858002d0b42c90268001d0070091410b2490302d40070b503542180000140002404010610300e1105d00b43e41c0070080001505040020b01d0802c0038040684405013550b6408005962080c0c0189000104d6000082c00610302040e00300c06140107000d828219a071150400004110f2f20340007596600c0c005449035807e00e84200e100c030fa24101203055000740003040b03a4049100300d501c0ca00ca0000b5018100881c0203e908000c00355a4001700740c0d44c1e40140c458181c20181140d020070205600d03600140e80b00e125403154107401940e41c05520300d04010300007002d004c40da0b55400d01001e814100b080d00003500e400e4008100074100d40740007815110203079139888400302d941d074002050703118140c00540c0c02041c0c424045459100218405484003400020a4014400d0141d98000540f003043e42c13404480603600c81d509080d007140c940310003030f10f0010325594200b4030032804080051498402e9040400040d5030050300c43d410f203126940300c22504009005241d006000700a001c56003c021a500020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 31097757 1250 31096507 31096517
    0x7110118031101030b0402030709030203150103050c010f091a04090509070b09040f020c16051807140a02010e070b0c07060503041505070c0b040303020a03050a051303030e1e0c010201050f090d 84
    0x2034030b10012005025100c1e100c07500a4004014800c2c4c0303e400590000503039108034190f0b00350030041200c0d0f1101400902c4007401542c003c1d4480015035002d0502c050075404140342c2007e0f01602c504040b084c05030407541e404503044000408101200c03192045a4028a420000d440b800d4503154601d18107009030911300d0700c00d035a81ca00340694003045034100c407400f01c1810141c40c440b03150a00c584282a02c1341c46454000d4120007044a00400380318113062059203d601c410780030440c4086c0e0800d4541203046407100b5596203003100d90341c455003003202c000100a1850f42d107a40b0b0600107003050030314045500c00170501c2020700030b0000142005180d104500180e5000003025074424008807504a2220360141402d0041402d120606506400400c01706200e61030901a98407542860700454800700ca042905880780e1180c0d800003403181c5c010410103008481116001c2c8c3e0700682490094544010041c3c07607920800c20000300d540c081c01140c5c0d00141580c1c0a041d64601409001c0d1555400020001000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 31099007 1250 31097757 31097783
    0x7030e060705090a0513020a0806030d0f121409010903020c010302131701020f04092406020c0103110d02040909020f010c0b010e04170a0302030708010b03090703080c0a05010905030711011803 84
    0x344130325446100804000b01340e0280510214004402580102d2190f00003c2c106800240039003000102d0b107200c0e0010b9554940f281640c0b100c112242c1d04115030400c4100e803554400f00c1d0490040e4111b5028001350310000604e80380a24029186c44203c010340c034141030040c09410900d182403406581192404c641d8000403034001704d101802442280300011609d0b20204010039400c0d0aa40700d00c14561040000f00f241c030030f200215404451091140c840141e0010b000c2e58269442a00854410000349248030304040c130140011059030000e400046865580e03140c40c40c15403420003919803220b542130030f03c801c68030310b1a21111034245050154a0054185001040820228588052072103200203007141d220090310500401035442620b001c00051400000800c0c140c8840302141d00440c0e01c0c1c00282282440c0d03a540c1c07625904501c0c1a05014002e98101c200800d1080c0941e01c015449500a035507a580a0f248c002c100200c100ca4040c1046003d0201843c0c1da0340b00e066030360581c2d8001400646407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 31100257 1250 31099007 31099009
    0x131b080402150408030406030b180703090c08061504060b0a0801030305130b030a02040e160e0d06060506040308040807060c0c03020409050a020d150605030114270a03080a0507030e06070509 83
    0x502e51104000b0510200002c00103180ca90101c0944243c4560343d50920078085140200901141ca850000d101c3c1801e00e008149601d001c0d0388401e0070140b18081a41c0c0e181d03070325040542820ba045607154a00c0da5424140b0400f8a414801c04019101100a940c20072045032802860000140401030500c500042c0c8099042108003080e001400d00f10402c030355915109031410082c0d000341c8104100714100c078002c16514183d50400e801011400d60b5621022403c0200300400c0c0c15000c1c1c0c0503220740b984c43c076011405442e00001840034601440302e0b195103914201c00d071441c20403e81e102404001800d40900001000035072844100e0750100da012603000b950f41041403c05101c814000e503c00c000d0070110f40ac01c06400392244455111400c208a000da440d01414240c40e0010314600c00324004000180d499580c0107912881001400280c01c0b4041c0e440b401c69181004180083e80403c0114042040083c2103001d690361144030362600348006900841450b603684405090750040c000045400d60f5a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 31101507 1250 31100257 31100269
    0x102070902180a05030a052503020a091b020607080a050a020f03130210050405060d020c0a0512031f03080a0e060906041710050c04090b010e130506131b080402 70
    0x6003460038021541c882c0c031200800c80700024508a140203c0070004000742c0707890013149549074513400201820740d00c4403541c2c034004505002e00480708541c0d81104080301607266016810b018200440c4002004000e1550400d00c11700900444800c40d40328200f00300351144d100400c44e8000c01c10b0140442e5039200ea200020181c050760360070200800001c41000f4001607007103202140d0314001e56280302020022041150207110303c0c0179158100000b0001c00a03c180303694018203034200000c4c03e4074000c601c1d50740e81900703051680d514054846808070600110104c840074460400c10840e524401141c503683c0e485005004070140c25090056030f00d10311080740c031100e0440301000c800900c42da9943d5118038103590110403c00382c0e001f81e482404005000c40d035a6118260041c241d601149047c00e14011800000c2d02d04200c0d014108a0211014040c40e1596505201807007100e5201190a107408401d01600c541c8125240070030a00700102140c2d20350b40c04100e44c21410061074a4440c3d50f0700c038004030b20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 31102757 1250 31101507 31101509
    0xb041b0305040302010204150f030e0304060c17160f051b0d11030a02060d0903021006050307150203070611040e06010c0c0501030903090b030103060e2e0504060902090a0c030c0513060c02010207 85
    0x1c5230410a104210304254401e00840c5102d04544080042c01c2d0741210301c0760349004a01841010621051243c4041aa080310b0243c0452170541440d1a10303d083c1c0c1945000403d40c10f08a40849680301c3c20310401c0418891101034811103458404201c1420380054094480440b02a12040c00000682d086031414402d10f41e00a8000e8100c958800d00e03e1420401481d4201d810f90060054440c050950340842c0218000c46130f000340203103142030400200780c3e1700420040c5000c040d4030042140358001005800b43c2c201a40100d0343c61606c039480c1a50800c02104014030160400c40e900507028005040c1c000d125041e941c0070b180c00a985000f40c50f054420000782c0c0c01424403044044000020440305401c1507124041c4542501c4034030a0744409108101d401d0308014884943c5071035950307020022503100d15071141c02041c01188060960300403d00c0345000362040103640d61540b02c50699140c2501030104540200c0c0380c8039160410306c405002c9100014001c000420403540d012034150380c0708003d550 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 31104007 1250 31102757 31102769
    0x304170702010e010e1c120e09010b0a03020c0f0a050a11042313020909070501022e0b011223010f050303090607050f070f0501090e0103050c040b04020f040b09040b041b0305040302010204 82
    0x1201c46030500f1f0000300300154103c4400003504803208417190741403607030f003050403181940b04a40c00d0114101040d4081e410841e50f9100521405980441505040090a945a0148015001088150a01903460040036204500860428514011105610b100403d6080e8a07111a014546485000b106000302008000e98008007400a1021140000c199842124070903001c40f01001c150301c4003180044c070030303000c0f0214001d48085101020b0100360000303141c010b014900215591400c20b03c0c50110703501c4004542030b001d0201100717a02c101e10400018050281c80751a01540d42c9006c0000c0d0f5a4400c03440120300849000c9074600421108000c04110a0204800d9070f81080e207a048840b80300d030039440b0390390003d024000000f644101c808134a50603a034204016003501d132451410b00004d00215075550707400c42e0b030030001610100504400380029085058815986015550400041d11686501c2c04e10480c503041103412a42a8007070100b140784510704010415544a080c143d00a02a0b64005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 31105257 1250 31104007 31104049
    0xf0a03111014060f190b1216080f0714030c03040c05030105240d0602071b1a0d1a0910050301060b090913150204030c0e07030501030b0105010e120f030304170702010e010e 75
    0x41446c0d0f0500010308962042c40f041805241d84058070940010b1600e80c4d1800402c0740b034070120340f607800140ca40603800328250038605003100001c0fa040c0020351084411084189004c0284008c004000d4010402000120028001e9080c00034041b17205106c082512120810400260b0181c1d031141516404c006030041000c544540726420403c041d04861a46180792007009400411421407090b074021050744160120750410030844840d00040c0b100c03000288101032504801d00c0c0340e42d18101c60701c0c440c941203030000f1207003407030b003010b0500b912220f802100036254103005101054869400f580d0b0b1013400c0d40c2003491035040380c0c1444031089642c400500700d014000100407003404011129442101c25030742c041e4a40d5604e02208070120f9100b80401081c100c058001017007250710603c042413404c032000b8042c2d03588000c02d9501c00d00e400034005801c422500080108010701c069036103000a9102c881c60b8003440d10000e580024064003003414075906000c010621664152184402112488280112 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 31106507 1250 31105257 31105259
    0xb030604030903170406090b030c070f030f020c0603012d0f1d06061201030201030e010f050405010504050d1106010927110a1401080402060307020f0a03111014060f19 73
    0x100364000034007068410726801c0801c00104c02c2c03000100c0e01190055030310240c400b42004240207855002404801d48203905101c48004182448466100c0b01d2290f112450000400721029040c05001c0100300e2140000703100400810a00140c0c03c00401d00100a44c05049001150382c0c00c480c007550800050220580d0000c2030405041c0b0a10086490850980311070781d446008200c1588542c1c108034903181c6070800104010b5000390810314500c03611000110300c6107149440c40e8202c4208a400303480c40e0703460301c0a010503c007061004a050030420b1510040c07540000491595448040c0b02c0c50000981d14010072081b40c50030302e001600da80200114801001d1241010014106425541c81c81400c8400000aa1603000c0e49580740c0c080040c1c542c805295915001c0110681009000e4819070081c00301044500e2014400341c0104e91091721307500c03510b07565000030034986a22449026412407400004142107803062038202d9200000315407403000b200000021407000c00078240d252001081001e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 31107757 1250 31106507 31106513
    0x60108030c060109060602030a0c05010617010b09090c06030f040302120d0b0111010b0a0b030c040f0320030102030f060d0c03050102030a02041e061704060b090403030506030f0a03020d0c060b030604 87
    0x1040280950012500702e40d8a62200e90304541c003034822480581d2040200c040c1103409400850b104034020400041e015a13100f03001002584a881d10220383e035500c8040d40414900078404581280350b56005040f0002800302150842c032015000400100d80c5800107000c2510801c09403150191806840340c45100f801c21590281c0540310034070b408100c6c80300e04244d000c05e05100c0c2c290803280003000101160f103884e100c2c1485500140c100000c07201c00700004101409031200070002944114140884c0d406102d04d010720801d031101c01644240d004000384103458210324035454128030308440c05070190b091032402e80304a403100e80c0014903035400030007048070705540c69000e8001c65400300500040d408003200c60250f2100e6900a000c003040c61065600c2c012644100d0040d07100340f2981c400600b01091070005400c0480803101200000d031a1420858181402e00c0003441c030711028070040c50036143e20baa000c0d40342c00c50710710b0000c20098103038500300501c81a41c2000c07541400141c140d4000d401c00c0d00b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 31109007 1250 31107757 31107763
    0xc0e0c07080f0301081506100e061908010e010909021e030c03060403020616020f070e070c0602030a0c090902210703021201030506010f06020f03090d08071a04020a05031902040209040e060108 84
    0x1200e035440318000c6c820450b50341d100208140c1c0c801c18004110207003042140c002669100900c582c0786400940c1403000408031301e1404032092401d01c1a07140c003010344d89070450301030b030003007050304540550381c01d00740b01c24011b8072001e81c01035012211280b084a08101c98011900c0c1004a55082e54076100740028032040c550041a024054010864000d8640003030702810b0baa524022010030ba55640000020040c82300b0704401ca540220140c50101500456603d0b01416078000fa5013201980e50344500519400380c2005480d00200707002c14056040401c0d40c2c0c290314020046a00c0e5404a1080c04000380071907101781c0c102c60500c0d14ae01d05c074a00d1541c490910981c1e4000c24062604400c070340980100703110b0b0002440d10150318030900118a003411810a0254040b07103903000302c4100a00f40080c0001503114030010b501032000d908807080600d01030040000c01d141a500450082d009011029003001a20003020500b640603240583d58041d075001281c010002e8102e40d0195018950010030203031408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 31110257 1250 31109007 31109009
    0x60512070e06070614070c030c06050915010b120114130f0e150103020f03010204080601060e031005070f02010b060f1204020d08040305030d05060109050d060c02011506020c0307120c0e0c07080f0301 87
    0x11405c0c00c03d180d54802060ba40c0110b1082c0240100e00308a0341c8000040e010f070040c42e84100341500351800306200a2200e0349000d020b0304030300740b01200450070411004c044119940100380c001e010918030f03107200001c10444812035003030034102c0b0b849816030241010030350040c0403001e10000440c2c8014000100341ca104040a00040f031054044400506003841e0500031b403025203104c80050006079180c1902522080c0000040640500a5103640103036014184503061164a0540f03448080713101c100302c02402c5813241c40c480c03845684180210190020380d0800c0e41c2c030220721140d080c20715880c0c600004090a1034940c0040584500040c013000300000400a04401c101c4030b04140724549926006440050450055036003100d040c650141c0811440c1d003069080005a000000e01c8a880d1041512518003030380100c4051307404055003081c07900703040040700f00071b005261805031a20340e1592401120003a501c50b40300d102a1000c01710354603c1c0020201c074040745d40315182d542e03a00342c242044400c5402c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 31111507 1250 31110257 31110281
    0x604200706050a1a130b0402031003030e040c020309010f0201020708030702010915021602040c11010c1e0207120602070201090e0f04020901060206040b04030f180308180a060512070e060706 83
    0x7800301082030f070941405198900c84840d0700c1c0c0742d48289100d00780150b01544901c0340c01c4498840005030060b03112072004501a0341500b0030600c2050450401500411540300300c68000c510703002d11000a07039400310070745900c0c80c000d00e044100d150308498200d01901940f00c010300710369000014090626015408038001c24404c3c00740050740107180b20300c5001c80c01502c4000240f20f00d42015040107280551010700750107110304003105a103400b107502d2405c440c9030f40c1d08240410016410700c120b144120040e0020000c040c030060032a6400c150308601070880c020340c0217000e542c01083c100c045a005803004000f5050790b9084a000f4640500107800005058405901614641002080b507900c0440c00c11b120302c1e005800100c02c6e485694080b2040d2550114100030421030800c00c880d0120300000c01d900950017010b413551107154070b080114004005d0400700c3e2041d5202e04c0100982a0000156880001c44070307903400c4183d45001c01a2034154850b401c250303000318002004020400654044018640303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 31112757 1250 31111507 31111511
    0x18030501020c160f080309010f031103040b0103020906120c0d06140f060109060801060503240409050c0306060d030210090303060504050a020a111f020705030904020307020d02150105060708030604200706 89
    0x15841004c02104a99070058015039001000000403550049240e0701000009182c00141000d9908500b035032900290340c1150032480340b40c0100300b07515180492940200003150b48403003010006040030fa0700c001140c040d40c010000c50184a05000c080c0c2d10655103110b00c924520303e1403802d203030b0802e1040801c88215000c682c0b00100400c80c03070300c20301119068461a445452450700c5d884015548038040080440341060f100e81f0100094546004484c80349100e0b0008100e03408140e070415050080c01442207008480d005a601c010a50003d4800c0704414518800500a12941401c0300900415080795030054140004c2c0690401540d0080488050795a40e0440c5c41e01042000c0b521f40340019210020042880d6505802454650040c00101d10030130403a4601280c042c0800c0603a0821500301000d40c100e42926802140c040c0120381d110358620001985541c10400001c2c968003403107002408090300800007800603103c90380807089501202c2d2122480110f411000c5040303a201d660101c42c514 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 31114007 1250 31112757 31112759
    0x308040309061409010c060b03010e0102090f0f010207121e08030603010f06060801090c0513030f02090a0612060902030f0f010203161b020d05070f03060c0f020c0307030318030501020c16 82
    0x81c0f03d044050440e440c01c05500d45000210001122801400c2909807002d035521550300c20306d541c0034070824003c000400005a02d0345242c20030001c0a404c0e41d1030751401807205048000180c1c0e804181e06045e159820b55980245e8010706045400c1c0c44803c0d0415041c0b509615a5010300580002071849050110000d00000307201600310b00a07580c0500c00c4402082c0220014007080d00303a07411040040c089482c0050501c883c0312a000100380c642c0e40700b60f685c5a0604440e0081d400e20184055000c0c41011090210750314001000902e0203440d54040d150315500c50049045580c14000c281500001c0011164075058040c0400c2c001e610a8504041c1402c031003684800050050702c411503d050901e420a20b001042d409100c220500144129000d001e80c200106580f00150350090140d0b0184030002000403ca0380003810b0001043c81c6141551310041184042e5980020321405495040c076240003400700360110f0786c50b18035032034200402e13075400841c0114440a00040c24101030240c0c54940e411030f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 31115113 1106 31114007 31114019
    0x105031f0b0703090506251502030901240b0915040e0a0204030c0504050c03130c090207031205060909070b0c07050a12021e0d031d0307030308040309 66
    0x7080021814206241c2d100c410000500825184039140081c0c040039800c070030080e84030642c10f14180004101c1001a62004218858a42d0030203540b2810f041d1005406000355000502000742884044910942484141c07011519100c40007443c000c0400184000380c84d1404030025802c908000c00140603560a903c40d100e030f4074001d00140c5a40c114540310f00d2454182c2e10180c0300300e0070031080c040000c03103c3c4200d9070000e044591490a0007034511f000c0104070340c1c50380058461440483d201080c550804080500c469480300c0c10400c50369104100603500c1c005440e15003240e072003c07c0500078500b250008000807101c0008030381d000b42d96940002e8601c407294101512414021550100718140800d6440d10074030307010107441031096000049910705048030005020003000c820b03180000300648a102c00d00c1761300602600d46154076414040d00480c4192001c0340001c031240400115 = true := by decide +kernel

theorem cover : BRFrame.Cov 30935257 31115113 := by
  have h0 := BRFrame.cov_init 30935257
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30935257 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 30935257 ≤ n) (h2 : n < 31115113) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
