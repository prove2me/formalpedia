-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4807
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:47:43.145268+00:00
-- url     : https://prove2.me/submissions/f409a775-edc8-40a8-8cec-1a5115b0214b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 864388489 ≤ n < 864568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 864389739 1250 864388489 864388517
    0x111005030412031805060a06150507080322080901022a040b120d02010608100606020715020307080c030d050f0105030a08090d0f0506070f032c01060b030112050c040b01 74
    0x400e8407118459403c05031100d450341d000c42c45100c0d190441601540213800745080c4448032104954483d4000c028020320901c0c04503d294100e002c0e240441d80043c1d5103540c0b07503603403180c00c000c80d002110600d0200b02c880c96500c051180303900103020604001e07021620101c60807220b040c0e592102800354a040820f1305810315a0303081ca6044a03400c10300180586200d6611203411a0502891400140044c0e54403002049092810041c40d03d481c80c28407000c0110780e0070800000d44074000c40c0140d48900d1045016101501e10030030440322184d8000285503110903548134055100d6010b5a0b455502508003408218940d40a08181d8100c0e42c0c010000c003040702042d6210301d1950882c082e200d600c2409141082d000c9a218000e00405178420380103484907141508000e01103180b41c01c011000c042c90081c0140076146611522000c20360b009600007079140d0500c1000b07001d0306440d04900500c141c040000100207803160241351a0354441ca054a8510140c40309020899040e41c4a1500242c2c0d0929a102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 864390989 1250 864389739 864389753
    0x507061806030b040906050a1e0507050405100c020a030803011502070803040515120f010312020136060e0c0307051e0910080304060215010801090f06050907090510031110050304 78
    0xe83c0d664041d002013a214100d48810080310b1040366104102600d82103510003c1e40b18100000400500d00401c00c160700b40760100402c1d50013213000f05400745440200700d10701c0901030401c0350102c6500130080800343e626440e0404007904284070f0190001b026003140403070240082070a0040d140118000c5013040c1c903050800100c05144054900030104c200406080004001c114901c24621400350b898254558900880c418030245480c07002c59140480c515141c00d80b40301e907401c00d5a148822450b0100c0c4540003008034001210b4020921483d00305a41c00d44040810304002c403402c01c500740c0d00c42c00e41e510184001d120a9130441c403400c00c4042182030452800000032904540da9200c80800310f6141e996803451a8825000a005a4044503c4841008400c1c2045000d4101c0100a01151090b595599440c0e0b0700080700170003250721640040c40180081220f400140b4441c1000e00550810801c4401c040c8030703502060301c900c068200101241d0a10030026510a081555182c0c0307556a1516045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 864392239 1250 864390989 864391001
    0xc02280c080609250504180b130b060d170a031b050f0405060c25030c050a060503160521090615011b050102040902030408120702010b0310020331050706180603 70
    0x10500030b46005c40c0a03155441544500340c4110382e031500c031110b90300340b501c804140107085c07c940c00c0210590100003550540e019422010981d912001c00d00e2038a040820120520110341d4211004560b000a050741900002d420940e210060101d04003130000848940c0300740740e680b00b15102c1c03c100410081c20700318028400c6d1b00703160050318046100d40c040103a10004c02020f2101d00d41145005000740094000448001c2c030f0100d40205001e4130b4410f001e45107010003081e0706140c01d040300406c80983c1c01003040f00c60345460194005110b003070b03040c0804188001034408924a20803a03001413a0441c1c0282c400007400c08c16102c81c00b042201c0202140400d01090080354155002d01c0f000030390081d41d001440c0902e12891000791904011458600201d10040201045a0400882041c6034030085450368183c80c081c00013507603903035481604090341900f643c02c200c414491135407204001000030155801041c8a44103a86003a40d403510308440200c00340a2142441c1e20300e00d800c109040c000e621003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 864393489 1250 864392239 864392293
    0x10f0e011d34030203010606181401120924061a0c0a02060307110d11010f140109180503040b1b060609010b03150a03080a1106040b0a0c02280c080609 66
    0x4903026030340b254042400d440351a480030012270004103100d07008064410b280c1001e0081010648080060200000c05030005c2419545a0682e20410b450078018841a41c0681e040c41c840302c0380d0991303402240800101490300c610000c0040401c652081c1e0f9420200310742001c2400c9000b000011a81e40030009182d0024000000344141c8105404d520541409680805462512100c0004800c4100701d425180c1c1600b000803254501042c4544c03240179040390605560443c6000601c1503d441c020001c030107501e5101420503c0003141c0011855181c000a11038092030f00ca140c0c00c541341c0e1401c1c0c5030707032500e0560b90715501c680c01d40d0045c0304244c1c2d40d0b005540e202c2040715030800c0c4201000042911141240c205a400d00d40014280d26400d0b00182c1d041d242030410340042c0031914040c1c0780d03c076805001401003407050b6115160310003a036201700302c443c10200e0042c0d06009207800f111484002c1d031900e004111030011b0321040004078202c012850391300c90039409001e015201c07110a40e00d58002c242c0c140c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 864394739 1250 864393489 864393583
    0xc130b030a0c05030c1b150108011407020a0b010b0a0c08030c1308060112062705161719050c0306180c090103020d11270a0509010209060a0e0102010f0e011d 69
    0x80d01f003501c0c0c000c5615078000c0c020400002281e01542c074000000450091101066500580720040018140d00b0024116080c1060080d00c84c08030302011249100010005440e1000c0407040c00040180030008165000c04040c0c601e1240340c1d18070160b81c076100240304000a2500e080c1d10927010651716080070400e690400400f20143c0221040c0a9546140035030698841e030040c00c52050ba1110488414042d00c00c1c003603105180466417644a5903050140c1000404185024008082180c104409294214002c0c20b1300c503503144c01c843c444600e456641c8068500d01c200c000c40d05c0039040a03440a0b042e03039006014500c16001d04e072030703426003402110080341d040406500841d14203941c902d00b6422204203c080082c0d982002d803a08000e56801811078030040e44100038a0009035905001c80700090600d04100c1c0741c003010180181e0060100e045651001801c0000d901005101980840c1648540900c10700882522000c00342c1e80c1c03000c4c901154420074240d020b492100f159541305803901841859 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 864395989 1250 864394739 864394753
    0x1120803040639080708090c240415020706090e0711100f020711032b020c130b010f0e01120207060902060d09020a15020d080c130b030a0c05030c1b 65
    0x85589098807010052021220f10910480d40968004140c0350001028540142d0700d0611010035501c5288200c0d03c14401c00303082420016400b588556a03c1801e00400c6540d00c80c0d07034480c031800c10101d64810b09801402408804580d060249140c40306954103042074040c941da030b0000643d040740c41220352640034031a0100c8064008241d010b02d000030b11a001001d40c840d151460401d11450908003154400e070000e200f100d0005181d444ca6003501303c2499510007601c60401426400c00200c103000319002840b949920200405680041100560030f03030f140d00880204801c11640380104403580760010350200d404078003000e100d802805616014000001d0582c1043d07000849030703403018038804042ea032900e0415080d45094a40d013001080c10ba0f030b007050303a00d40040c0025240e6a08040c12411300c000100400d0803a61201c080e030b0305140040301c41c1e404030384d100d14440b04107030002c49004016509103624500c1d100d11400959015071803031590395003802e0040054550902201c01e001030300d449009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 864397239 1250 864395989 864396041
    0x708072612040501090906050906150706050f01240c0206090102240a05090601030b07120902030a2303070f17090a0902030415020703020616050c15010905011208030406 74
    0x40100c0101d03150980700140d4880c604030025000c2c081c0d9501c2481c202e450210b080207546c840100c00ba0340b0150884000e1034039004500c0200300307409030b241d01030310144c9800108000035160080e4141a03460003809070340c1922402c13180b81200c030710740c0245600084180d4220f80c01820007a01800344190f050054800c9800d2520002c412400400c0c2007100001c00e22082c001442c140c0c0c4566908254483d010380025030650725111310100c1c0c054504c00030841c04414803240d070041c6a2100b010700c0d40c01403d4500c804c1c840e0801910480380c9441141801c045034041a0007110004115040703654030210050442c116a2140c42a85642074000a1541000c0111280c0f5a0701c122070b49019044c24040142c590034907040c0b1019507003a4494241c0d240e4810010800401c0d0005030701c1e9030010180301c6403200c0340500041201c0760300070709803081464401c200f4014100d00040701c14606840e0440001c00c510703a41d03034080310741402d1401c5002e400010b040000c600410103d400c031100400c004c0701c00d41362450900d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 864398489 1250 864397239 864397243
    0x6200d0c022205150103050405030703050f0f030108060f0f0106021905120403260702150306040605120d0e18220f060f05061906050c10020406020708070807080726 72
    0x2e40d000461580d0701c003003020030f103103050020144000078a01004a481e280da02c9a6880c41842d201505012022501810b80000340080341e803120a0b6809164803546d588814564a0000342c802e8298007642400050803944007400d81412140c460f8010071010b201d0a070aa41d000400f00d506860501402d01150f50007402c0e103000380010f5108540c01c0c04e45c10039405207038510ba80c5070035124000710810007100016079500d4407122002021001220303981d4444070002070041c42c00f5808903801001c0000410148100032482000150050b1641032800480c8070800034940c600c0381225103c0941030002c2012000c65032010418100b44003403182152202d80c030364030500b00c003030a070032035030750391289446000c20503140909a0801400c3d942d0100800c0c02216140c5a20b0850245600300680410503140c2040c080003001c840e0448910700b195500c2e01c60800944498550007940d03098898958001041070b0009499412070341410060442c031410060503011082c580a80da001c00301503195400700f10001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 864399739 1250 864398489 864398539
    0x302090a03081b0309060d0b04090605150a06030203010b0a0e0a0b0f04031703060d1103030f03040f02030c0909030301050108040f080c0d0f0e010801120606031b06200d0c02 76
    0x140b002c00c1e200c040c090300400c04416030055261041d001802032841e079807112426146200c014107400304604403e40042801840c0868005d4140d506001c107000c09200c3d001c60320300b09000700741c50210004d43c41c1c0000f0350682c4000e204010020b00c0400010520074460b85405084000080822443c103955001c10092500000e401d041d668400040800411810085017480c4180154605003075140c12800101175001c80000641130143c803034035441980e07500307200f04c1e119540321020700b6440b400d040c04d0580000200740e804a000e0f100c0d038074400c800791030204e203060f00c0341c86000000c52440e820100110b030501c8000d041125501e11840d004400280d88070003400e0003076002002800300d0060071100803c80c00001c4140c000340501c0020282e00c41e60b02004041c155900c254003200001a2070ac5c100f001000d403944050040d034905601001412807902e1004225103040e61107400000c048860412981c88246604500b9800b400744406094002c2c0702c0d04500a00040c80c114094012210083d44196 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 864400989 1250 864399739 864399743
    0xc0120030901201209031b0106050f0913060c050904230c090a090203090a0206040b120a2a0e04020408010e0708030f04050910090c090302130b01050f0a0302090a03 72
    0x2004020040710080034424200a44030086100003006181e00504003140b091100b91070310f40c68807000190619008000300c5400a2541c000c3c850403186100245008241d103000b81846010841107910042c03800f408518002d01012060035100001a56202c00519014101405104050010010b00e985501c500c840e9403864040002201c603e51101c0202410004c02e0140700c6139091001d0702543d00c60300d440030b00b5185130b903c005039a920350300105440c0c1411404001d50110700010042003005241d4003501e00883c030400c0014464a9207031102040d03451403440b0140b501c010410091031840c0703018119002c480d450500308006c101c183c000c1026a072098000f448269191080b102146800308050700003844044080d40c14460a982e000c05540724034850309224030690f0001c100300c045e10720501001403010f04802c010030020040040c16000c810b1006070701c00ca103840c28100e02c03c0040d0052401b0620141d40c0c2601d44284445c44402c00d400042118041680c24403003121181c48110900300514 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 864402239 1250 864400989 864401051
    0x41b08070c060603020d2405070516032f06010801021c0c031401030c30030309050f0d031a06070f120507020a0305071412070b0306280311240c01 64
    0x100140c20151030705951201f040008501d0502080790741903015064a41085a00c80556002810750400b20b03411428520411210240c00c55500700c45090840700d0300d03a500b511030607200103a0360703611914200c0c0241591160255600c001ca03150a00496100407440801420700084100801c100b050221400b41c0045030003800219080c070010804c00b1048210507103a0710201c0400c0224030300c010f042c0c480c0242c010103054882403640300f0007800b808401080c00c901c0085850707002c0c5121001b00506400401c0b144140d0302d040303010f800c42c01c04000b103940140e000283d0b01d01807105581c4540e0418420003a2204224040c004d0710016554100410020350140d40100040c9007004401c01e0000140c85c1c015200e00c13021401e0801ea6640401c049040362510100103490395187c40c0032940c0c8955035250b4000508030145040c40f04070308904130a094074000e40340040600030140a021a0804007200d0940785c0e0003100310301003041104001010841c03110300003c07550407022444e02d85080b4040901441c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 864403489 1250 864402239 864402263
    0x322080d051e190e0a0201090b07080f030408030103020a050d030c1515030501090c120519060212070305100504110d0f0e0a0c061706090a0c200c041b08070c060603020d 74
    0x94103c1e4003501d003680020390040c1003c04265400a0400d80641c4905c80c1600b40c0400c401e0140400c8100355000078981c5030f90666070f45003510f019400c90340240012485041d02201c0031446003000c1b9044094242d050700c64010100b0280c07941080c1c0460300016280c0b15440b510740703000241d00041704900440c8501c0000c03a80b00b010f4600090500c1d01600413080600c40c40c16003138041a00000c0c58040716404090340303074040c006420441e0103071140c540b650a52103042024072181e1903140d40150300c910702251490b803445803514200820748005d101039510020041c008004d410049a000c101041301035000018a0164000898140700c42601e05640c0316200200030001b4907000341002620303942030202c500142c90040001420044003521001951f640e0784200e05019000b449800802800c3d0b0816098500381e0882e060360783d40a102500d0300030360401c4a01d401d44254441200102045600d4101056441190458100c3d510183c207a8030561190030000150321403d1101321101e014042da0104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 864404739 1250 864403489 864403531
    0x20a0503220c181415062d120603340306050a0b09011502030307030b1c14010c05070c030b04030915020606271f090509030322080d051e 60
    0x850307014050001d904c00001040182400440c9240004040c0031a66151506060550084d42c0e0303100a50103a0b0006580244840094840018015207401d40507a9031090f95020709154403003026200211461001841c6150105881c15807544da030b4041c02c815a4202da078a4640308140c890035900e110001d80d55a00344201c6c0c0c00d10394000c1380500301440805040440c034250007585d038400101900d0406640d184142d81c2a0b9600313012607148100c0b610741c00c1300c0e540141000035103901080180100d0350b181c0742c51450b10718001c00517620600c2e00200d540004600e03540380c5848808000740110b040011028000c00e003401c820100041454041d1700900043c41c145090140d0041c050007200041d441d840b1061a0a401c0b00007915804641c049410248207186443c2103510306154028169003824401000b65070702000002e0b512511400381c01030300503030b483c1d240b030300c9441000c0c000540560410032132800211110f8000c0c7d40c204a40000c101440044821000e01441096442308112b844050a140c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 864405989 1250 864404739 864404741
    0x402060f0f3108033a06061d0f100e090f10050105040b0a030c1b080919060801030f022d3f0106150504090f020a0503220c18 55
    0x1d01100400c1054005041011960740e85c00303000542003085100188800b4081200030440300c10290348681c80b116044054103040182c80d041c02600d00059001c007415801c108d52006001c8070031000b600301b80c60700c80c140041c4681603c030009241d0901103401e4800341e85480d1500f40d9441040705085008507402d080e003511001c062150301c0385040100074801400092842c0b011580085110f080c000350841807a5010780b043c02c06460655803c1000c004003001740001c034001403001400451711004000040100e01404022a028100020720307070000500004c0c440c0286040140d00081500850703150303000700c4040107034980030510300e41c0200d14421801c0c0d090882c44289892203503107071048040c40440c401054a49040300c800441c0d0500c0801c0300c40000294000805040548810500c01c01c0c10780e0003400e580e01038818410380d10b2a0500c0c17020607104910a41c1d01810055644a10319210740000018070070704041551000e5030039a01300800160708a030104010f194075100e101c0381c801c5000c0c0141c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 864407239 1250 864405989 864406057
    0x10301a1501020a0308130f0204060801021810091a0d0204060c060b090402010807050a090e01120c0807050a0306090206090907020f0c011b06090309090e1b03150402060f0f 75
    0x241c159481494040c0c0001d421540701ca5000031030079913040d004011070605401d8005010000b135007181c54001c012845101c1134008240c501c0c03040c5081d4401d81114414402807100c4191420f000410140f0240061100004000510079005401f1400c1c03140403a0300d0800c0368002c0e0703c60008208968216820400c1c1401002e031250301c101c40038401498241c002901c0c0c100010002810420009000501c070750142d51f0701c41c050440103c0301c801d00c0da1142a420500030070003c0c01d40c0d840d503040100043c0031030300055044c1968405015000e4142c41c3d80d0b5690b0143c844160200e03802041481501a503450b00d40085104030200ea00512403051089421814144141d81c0181004940c0010624040380003080c60643c60780884006801c000300d082c03c0340d0582e0345030044841b036800c2007828050100002040700041002c0944103ca250032441051303a2181040d1441c20400f608100080141c0713000300c0074010390088488030b10301d8545c0410000b19a40d2044c0f85d02604800741002403940320349004001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 864408489 1250 864407239 864407281
    0x1b0f11120a0c05070801060e0f090c0103150b0a090e06030a0201050405090604021204050303090d09080d0f05090a0b0304050607092303070e01030305030a0510301a 72
    0x2080802068804194660362a2060300403480c0001031090340030780c458800c0c2c0081c1d64010095820243d1105180d601030045881400c00c0142e02c1c80228401110201003c0c2c001e0b81036800621001c0700a20055010b010b10007800c0e54940403c40d000500d40850714020081100c0698a00d407200d0b04007160400648000780c0400d01a602084281d001130b60401c0499050b1501150f907101103070386c1d640c0090041d10903480021071001804c0e0070f21007008800005136005400b5802a1804a402301600729154545842645807a034024421003c145004080d01034005001d8900740d40340c1544403000c80e41400c9940d10007074104c4000000c000c24004240911a044042403511883c1d00349491103016699180341c0f11505e600c22800ea2105080c7d50800400f401022401d200222a41e501d0401400700c0e08111561844541040c0001c0c90880c102c5031100240d40e5038040c00030804040300c41c0061f42c1c0308404421504032500407014404540c10282119010b221603500b0b2091340f81501c4940d0b0169041c2582c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 864409739 1250 864408489 864408497
    0x7030e030f0723040f0608370b09251d07051b0106080a0f02010e10020319020106170a0201020d050424120c120605061e1c1b0f 56
    0x401d002d0442c1c41a03e2404200900104007442c4000e031002600400b03585082d481d40301c0c030b070480001e4402030214407948420307040203803070b22044840040c0926007694418503100c2c0106900a40f00042d8244503090b4205120300d088803c1800c800146090b10300c000015032108440202040080340300c440c004029001c2c28a10010321410101000740c464020326500f103007000120003d9900c1e0180c00d40c0550010312050003212005503150a0001002440d03400a9000400c6d8209011031420320f26003810380054250b00039440c041040000b002000740c6994200115500e41200190a0320700e510500103200210000d0300e038600d241e10000e458041101c0c001e1050103402d1000b001420f035181c250441805122800e00e01020100030121000345604510001030f9240c04066401c01e0740c0f004010709810001802080085d40f40c104001d520300442204540c218031040080001341608009018441d10009a01d11800200295102030b203841c40c00145003008041a0000c84582c45000c04039140e2007428 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 864410989 1250 864409739 864409753
    0x30706031119021908070209010e040510050c0903070b0903070f0b030a020703030609050f040506100b070210030902151306030e0d1805040608030c060108030c0d1d0607030e030f 78
    0x48440020b0241800a107540c1c598812003107031070381c001d1003664001d4942d01140d030729900b11480e00c54496040180140c1c0104100000070990078080030074a80900d401000a01c0007000354a805000b0341401032010303441001c01d2040e007405440402a0300042c110706840c1e9500d60034920b041c10b01e801c28552001408450300042081000b81500407650894142c41d000341c1c0e03030005400c050380038003c180c1c480b0318510320700020071180e50b0807408164006e91003070b0203541b40394a5400000c2d40c1d0758040d00800d440c04078100310031001840e04480000c0d680c202c1c2d041c0810b100031250006401241c1c5559036142c400000110a0701c040c900c0508074001c2e03c15401c0800c130039001380485681d50255442c540c000c1c40020301c16140c440b0240b100d4000100300062041c0066929400300640b6a007023541e0400396449400d0000c995100d01100b610718044403500189145030560030100c8005d0310b10720303407608819080046140d083d2540d10041c00030314000d072034001c4020031070b000341460000344000080c06500045 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 864412239 1250 864410989 864411011
    0x903020105091212190618020306010905032410030605190c02070b0405240c010209090114060f0a170f0412020d080a0f0209030f0705150403080f031801060f0503070603 74
    0x9400e494229121140116070b040c40818a040107200580101d40310f4425000100407d9603150001d500c100420380e41c03140c039180d4941c14140c0d6400c5040440750010301e00016a90f5510005100d41d0f0f102d58843c4035004031680d071392500001c64000b91501850307600c2d90003294404103064000c64203a151544002d2020614103990143e06020b94000c4610071485c01d02c150500203603414007030031100c10405080d90783e900c049285c507000f03600186000e030040344150000950f46410385210100c041c00581528504541e00c07444060940c040c801c06028410542e0041070366500381000c80e0302c107c0314036003003644a00306402d000c0349809044000c0310444d0b10040c0c182c15620380c0b11401c240c01400700074002c0744490004030108068002c40f00660703018441d00390741100c0042c1c0003a00800b00c46050342c0480b4275510000003205a4440c0b4000231340a52410131102c210070700200010366202c0c920110179164281d05100032803c1d5021940305441e0040d61260601480c5400c1c01160300402c0300b4101004088015 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 864413489 1250 864412239 864412267
    0x7090f1d1f0507020102120702070519050310090f1203020403060b09071e09031e03030605030d051e2a070501031806050711031b0705060405090a090201050d09030201050912 76
    0x30a4181d0203030344600119807110b000b5016120704000c00c540c404410300c0c1051009664004512480d8410540302100c40d14031550840d4100560303c0140c0a000341e000300901d0f0038050602028201da13000c06a441d07680105410a5042213009070650303000d6a500c1c0781d400c0c10404e03200c0d03410081d4031400c240814404515003158090200381c032451000c1d06030740b24114040d5401425940042c15250300748201640b8840d55050072120a03200c0c0d1810011a6190801c0c982d139141e001411a01080042010040130402260b4090b001d00500e40c00529040c1244491100e007900e002c070030810a0188001105601c00c00e201d040041c000a02c0d0800c4482442403c0d032402e980301c034101030216651440402c000c14441c051b207208220b04142166910002d403040c6820140c00780c0d4400502d8000d490000c11075160560481d0200c510003009240103403035a45414004001d011000ca0510004111011500c0024085c1c080702e24000d4000040c2446e01c100f90300d080c91030030641035500e440200a00500d10182d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 864414739 1250 864413489 864413533
    0x6080a06050a0204050a141905150c0106150c030f0305061e0a031205040314060c1c061e140f0607080307030b2d030a12050c07090f1d 59
    0x440d0000c255600c1d5404004020b00c0341da0082a007181c81c81d980415481c03044004090461010b84405550f04402e0a010140000d0f6005240c1c1c4450f2071240803006411440107000c400d00030900004001c0d90b1040d00c41c01c5c0d0722004c29104007162410341d100301855040b04810382c0480041c01c090000346424800100c0e609200640c21140f1070103c0203403008c584450b07981c2c0c009180d00c01301c800440e1040200192090f00a40b01c00c0b0b68102802c00c1c00c40c05083d01246050103101028041420800108030289125020300ea800061a5552000280d510707040c030b80306120f81071a20b40c00c60b042400d156040315200c994911aa020383d5225504486944407081112007003030b00101c9030381d169201c044044001d09002c41c0060790020a00e0342e59402450760504070306008102401c80d5072078403810014151100c00b003d0000e0409180101031810640c0240d00402c0c103654840242c6092a8452100c002146c191007440f038070441d600c003021440703148411150241c9140080040c01d52201c1c1035070303040301c04038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 864415989 1250 864414739 864414743
    0x609150112030c06060b03220206030c0304030c05160f080106140904230309040c0f08010e0c13090c0e01090e0103081312060e06130f023115060306080a 67
    0x41c100c0700603014507110b104051140d0f50b00c46001e0202a58407100d2004941040c1c0340d0500500c02d00b69141c0b081c40044104013051640604110301b550355101e03200d20746410080c0250203105813000c030600010814031248010391051100108034038207008440010702d1040c1c108400903854071805001c2d98400309030040c01c1010442d182c102c01d6131103141c00d501c203492408240c089442c0c4940d018100301d2003c4040e14880030b058a0801151502e18002c840d43d40440c6419808500d0710001881103070b440041e030344e0380301003258080e900c1d00030281051030324840a81c0c4040502e17a61014142c8909900c0b5040c1d80d42c2403003d2030200001410117044804815042c840144540c10000d000c40d64101d0203441d01c0001c2044009840d60620a8107180c40580301600e03410b1101c2c0034120001d034000d0507a09421000c1d40e0000d505010808580c1c1c203218070040b90071f04c50340c104200c51101c1c0c9070007005401c4080c206c0700c02003804203500c800150520b4850f90107400441c00d05003131807024084001c0c001100e2500035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 864417239 1250 864415989 864416009
    0xd1506090e030702060d061a180f010503130c12080403050f060c030f07090b0a11011103010f03030e060f1902060903190c0201140d06030308010503060108120c01180b070206091501 79
    0x10402c0d011b10b001041d250b40071074060384a506205246210180c040c1150241000c580c800d0391201d5002c2041003580383c1170442c0450340034404500070210718030160905a2040b00390442543d1500c4200b500c42028000440d10904001818002c118040c043c8800070500394000300300a041400d01c0a8190100034192701c0b40d0985400000e06892084802800400355614840c2e591016050020300c01103201295007025804c0c031140c80b1001d0f0420040364100c90481c1100450141503075000c641c2c01d103414840b990320038014003402540802220080507803a502d80c12951581c42000030123801e0060062440c240b542041c410401e030219941141003a4002c54502615203d05510050350280c148100a020500021030b0010788020980e00c0001928000c3c1c80e03024003603903181c0c20560f858200340107451740340e004424006030080c5980c01400700980a00004145004810307003441d404554404203441205401c0180030040c1e40603c40d203600710501001902070314143d540b401a010b4010f101d07240f18a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 864418489 1250 864417239 864417247
    0x3f1008070905090d0c03030b100302030103060c0e01120b01200d0207080105040f0b070216090e07090e15100806090a030f0509150307110316050f0a0302060a1104050d1506090e03070206 81
    0x1441f9501c100c90790b0500500d03072640442000c40c001c00942090008a60f2031780341c90361007443c0e00d0241c12903801c101016914a0004140190101e0203010114116030522003c40220000400c00203490191902d032500281580b040c05e600080c03519409501110a0364500414400440c40d1450300d070b1728160f00042941e50a40347c07100c1c12850402c1b421002a0341960001c00452950f80e250006100960b1000490b450140c0725102c0c4e40490f02c3c20329283e000c2d0750068090301c0414082c10341c0030340d0040a95284426003540c1d480c0c09130410000b1142d003401604000c100350209500038140844c07001d060325200d03050029174004600886590005000b1808001c00007900f803c4c404c1040103100c0e07214000f40c0e52076004011310b0303548400742c1c014200c60500030601940c203c0c000000b1010030650309503005217065103583d5001002018031529103081d10504000201e40c5440d40180b4560662080901c10040114402c1b0b003021a440c0e9040714003481e04200d10301030324420001c182e490302c94040352242d0340d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 864419739 1250 864418489 864418493
    0xb0103270b07050909090a03032315011803082205180402060f0703030e0c091603150f030503071103010c020c040b06090a06021f023f1008070905090d0c 67
    0x43c1c01074901c4d6550100c0a00100504980042401d5140034401d07141482001c0b0000000c14072178a0950001c1c0c0d0340080c0d01d000501307611342080c0c916101041814034030318030300000315820b19040c40750700243c1e07040200103000d08000c15089034451071010a0145410042c1c100000181c0e0000801c02884100d945080400c0555407800c3c200d500c10f40000c039003076a44403650310303000d005048a11100d4405000b080c84116003400e2011030b852082000b100311142001c0e8131101540140b8912452000d00c86109202042500700000c82030041d50080307005686800c00c138940380404400003c18140a82d04004201c1c2d155a00014890a1503c1c11500403a541c0420000305119004a54040c3d5110890b42030005100360045040210301b10441e070719000c4406420070120581c440c0003401c015214600c4480302c0ba1031045594400d4054040100c203000301501e0140026560040d00c00c80e02c1100300c2d040030090540c04025450080c525100184440c1c078243c0191070325845098816400c0c040e04000c4002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 864420989 1250 864419739 864419747
    0x3180d150f061707051f020c19090c031d0c1311070b0c0901020f0606150703021501170c09010b0301141801061e031503120e0301020d0b0103270b07 65
    0x791048950040085070034a01c9143d540e095072017018001c11300e09920070103140c580f107030312a11895503400409088203c4002d2010f07010f0a10040310603040c50304408500a01c1c0d6000c1c0d4400008030350f4010504515140d114200d41c40701d028810600d500c01b84450050b0744600700505a0007080910015401420403c8030358544504180108401c07440c0e020480d130315400b100500300640c401c4e421241020b80c528081c550b1100240c0e203140d44111070000100e20780c00f00350010003484d8801e1040da240c1c41841200007a070f4a0082e085031500c403000142c50301c1c03030202c01c0060240c001021952401c0c254074051403030500b8401805842e1202503007450602160b220380041c44100034010344940c0c5d040da95100c0050481d0b4007410342c548000a001a10000e2a102e4000c3c4403000040e1042c0c03184480c42d6983e85420840451310711000d0000c0d680c083d8800d603800788080c103c0c02c01c0e144000b24104040c04001002c40d5208020810251407501c0c01e0240f0f82c444e1480c00d44e08660010404580344ca5411003a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 864422239 1250 864420989 864421001
    0x1a060613030c06020c15071104020d1805060610090b0d020403080304060507032306090928060c0504060915141b12041401080a1d03180d150f 62
    0xc4480108040000100030901c1244070883d46541e0a54002a0043c82009504070744c041c01c3c0703640740c45c06001c0354001c28404040e4480200000344010300d40b00100a031142560440300090b0400e2078540c43c501c0a208041c4249548404100d035018620502c02e04003502c0c0103440d00412126a5022a111075181c4081d8119409590000010760300c9103014034040f0050038040380ca40c40001e08014450041c1c0302070b4200c00305d001600800c6a1078039541d4205201802d080207042140c140f0070405694580c4801900b4080e00e5512440c1d607104018440c00c0240c00d41d05015040b204101c0704200420050b54080031540994400d2140702400d2405800200c0300b102007140c1084002d04000381d13400902da80d4014800425a04100b951812644203da4580d9070107688105100e0500b66480c6221544c425096594080d4a030640000d0086d4900540c03100d8100c80c6121030001c0d440080c41540c580c0040341a41d04c003500488404400c00b00365901c000101c68000e40c600c0700a5120222901c82c4003031600b100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 864423489 1250 864422239 864422257
    0x120203030c0718063204061505070b0f040f030c051510090b0f060a0e030a051207020a080109050307030503071707030b040c081005221e0b010c1a0606 66
    0x2a85a10f032144500112070800806002c0303a41c4c5002000604142d640c4c0c140a0901c801c4076004880e5003100310f0b85500300110154155100e5540e0030b001ca40c1480b0088500142c507960b9a1f540e498a06c94a004007048401030010700e02c99100404000000315040c1c944003c041d45071400800348200703840c0c01c0b464100c3c000300031721021101c2c5003005207403d908112402100d007100c41c10312888098409202145d5050344000c3d805c0721040060041e16409100341c0054080042c0454086012940311642442003c040b0380058510000b206400e502e85140494040d004110007007040c500c1d10791368980d40740b054940080a000007c030014020700d00a07020a080b10002c02605a2107140c4082c004000b0080c0588043c030441c503194200124a2040001c0e9125a4070b500c0340d081080c1c20101008400180c4804051820700d0411080071401d035036000c0c8180c00d442c1401c0ca540307201c0400d82000705075001500c1c0103040110020354038011886c9200e82d6184401030800c084800d4640002040e414842c050344 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 864424739 1250 864423489 864423493
    0x815060c100c0206060907030507021c05090604030807030305011508070e0f041509051e04142104030b0105010302030402090601030b30101503060f18150606020313120203030c 77
    0x2ca451078a4010075031a03c200c40071902039a041d51404815021140255943e10059014030810000c1402c0481180c4503007185081c0799040002c0580011029803064000300e901090200303401e009c02d0b8050244501612071080e9a40940326138200c0140300c050010b156004104c2000d0003000140c0b0303a0f10800f0021075014005100111050b03442103454030b12407061017100d6141800180c001a0710016040014403081c000c0e0005448540fa0103072100002501c3c0c0400e8001d03040014401c45c801c14481d07504a09018026480d2441c6051074284004141d01c0541814010410040181e50b035010365580070209003800030f55a40310001160070042d050b003120203243c081580d1036a1054080c0d031030600122150044a081c50500d040400a0b00c1c00306d4010501680d1601d820700001d0a643c210500d03100c0c074844000364440c80100b001015000c000e809a80c20050890b100e90f48803100c1c000e50014080b40d000031407900c2060151503101021900c144180f4840c1c4950f540115542031040301c101200140c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 864425989 1250 864424739 864424751
    0x60910050306090a060501210e010203180c0102010507080c07060e1f24063023070e0f180703022503020a15090c030b01060e010815060c10 61
    0x4080c08552040d200c1c2072040b0b100c43e00044c107452941c020380e015600103940d092540e0b1004160b45040e100da03030741e40c103a10070340344d8041d5a002d40c07003480694864003101306010ba10020b270015840c107189c01c1011050459040808104117070b82c00c100791603001030034043c2c141ea4501a50500100920fa1588891258021541d090301c594149405008100007203071010441a405042c0441d0b48003805100f81461160701d0400300321890140c0340d41401410800440d05d46c2c10150b040340018440d001c0403e49805903200c4074484429250a021201040c0602940c40241020300d805083c0c0403a04003503911541076401c0340040da40724100c500300741540800141110741002d00c4080c010b504901c0103881180c04c84a07080a01c034004840750810780c1d4040c3c01400d012044d648a000c0204421445420403d07207031a41d1138000b501c03248001c80103601a00001010b035050807001401e0750002d10100d410400c001051000325091445902e510f00070481c2c1d142e59801101020302c0c1404446030030140414a400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 864427239 1250 864425989 864426019
    0x261603030323040203060c03040804080d0507060c110714010215040f1403070f200603042d08040b03060d08040905060307090c1215090c0215090d05030f04020609 71
    0x1800c01400c6201d0b11111000346050200c4032140c02c4021103000c3d6041d4005800708804055440085030024080e040341480c2649540186150029100362007001031400120350b02448058800c210031000c003454081800e044900b100e9540c0c2a042c01160341c100e12a110030b00d2203a00030004031024a0000c1e0b01050903142078200100d0740e05a010054489c644860260b140c0c07610040122041140e0001c500d481802d01529480101d048902c0c005000064440589419035100401b4610a0f440b883e000313030300421580c3c41e92403202c10103020074035042c4d40f214188000880302001c2e9003c0e20308a08070951280e55200c00034882c1d519400004d8014200040c000c0b0ba101c0705600404d2094000b0b400300d4000560300c150b00700c1220b05800300503002039901c07542d507414484e03103410560041440403204640d260703c0b12006021917020000c0f00340981c1c1b185151484401264640551103640340010b8040b4880c141c101038041d11008089481ea01d8400f400101103559071400d40b01d54035806000f02040300d0001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 864428489 1250 864427239 864427241
    0x1525120f0e010b0a05061605160314010e0f0d0c0c0b041d0903090607060f060510090603050f01030201020d1809090b010302240a050d0905010504030309021305012616030303 76
    0x80020801e075500341500e0794043d00340811180704540d400740c603507441c0444000921140d0707480380d0000c50341c07800b6100c65a1180704500c2c040c43d0103140104500748140c4034000c0b44600312111400040da20760400309079081d95500c04100e507026040300e810005c0c0031400300c3c50701148840254001001c3c059000c140420044490710a90301c08040d02c0580c44950340343c0d400e0b030981e01d02403441c500d076004408015100003d00a60420800e1211012001c5102500c9800182e20503510380b440300b0004141c0f05007044250b030f140c0030b50340d004680803099805131f5045800007500d442076144ca240900c1110009102c0c03030503040d500d410080088030010851041c1c40c1ca05246c10345000c2c40280c0c86120b00c210049603400e80300e10840c0c3d1700d0040c1076115141071841c400c281d071903820a02045200980c4d900800c400b18500f070103410b04c11407181da00001e904d21349104204203101820404140d01c0d181130014032069200200d420f4031100c90400100c15141030144940c9440040420100e8100460300000101505 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 864429739 1250 864428489 864428501
    0x242203060e07080d050405030607030f0b090406050a0c1d040518070b0711010e0f040513020402030a0e0706080411150f0c0c090c0a0504030b100510020f1525120f 71
    0x2e9242660381804d1140c40441e494010342c0a1560300d50803040209215a00a0740910001c034040140450359442120008091100c200c6060f0344454545040026203070080c4200c1203117290310304002c2e04106034010070508007a850820303203005658400119080124031544408404000d9040703505203604c40078074030840e4001000480b0440c0050201d18015070003141d603401200f9010302071100342c120b08800c00003e404050174a8840302d00c0c01e08000d0143e16280004c40c890050308902003034011040c00081d1810310a0783c40031041210b07600c144000180000904001c448003110651340240d01d081807074865100e2840c006114510000e031039491450081021185690200c9548030b01e5522803084d00030511440c4040000110100814400036990b442c010390014140000148030035110804038a24400c59107102c2c015a100d01030084101314100b000c3c043d4599002c4901c865810022684c50014544404584040c01841684052540b203030321009421350b01035005110380c1000140720401450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 864430989 1250 864429739 864429749
    0xe0c0c010c0807022d03041e0518011806050907120b0909030403062a090e010518060618100c111008060918120306242203060e07 57
    0x10034403039070302001402071103418800d0b400341c2c001e0044150042039450003800c0269108945014030b4508403000303101040038002509021204a090a460440d414684a129400780b4860081d00c01410b04186c04400505c3c11181c05131070000e000608458007001401e540d800c260f800030441c03010030095607442418031400c0d9550784070411403100c0d40c106210b0fa14200700ca06c6a000e41c0100010000160664081000081e801041d00008012000c2400c004a5031401660001c1d01c11035041c008800d02d9103642d401005d0071180c140c141c0580041104050200a0005225140207d040ca1a210403a0b81c86d01944a0060070040340c0b00c10188064103030759480c0d000b0f862501d90080610340c90700f030188222900041c186c4910304d04c0d6540c0810404142c0c030080103e0904203002405d400c040c00c04101d02821711003415030864803490103030140260b0b00500c101140240d506050480b0301450f03030344100e410700d207040741000202110b410801d400b00782a56100511091514072a039102c41c9010a455081d20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 864432239 1250 864430989 864430991
    0x19030815030c0927071712090f010503041104060b2505151308040b0301060e030102120604020d1e0c080c0301060905010e040e060f19290301060e0c0c01 67
    0x584018196680d00e9041101c0e0410035110104110303403810080d4000e00d03007202d602d20a030038104070b00840c2082569480745040d5072600c407600d0b010a5060000c140304600c21030207c0d0621181d90f001031002c07001185100d0500500001040034000d45201c081d01940d0301400078000303030307030340b480029070a51041031b12200300000001703400c40b110242c000a1480c2c80c0c226004069502401c1c602d803100003c040c1400120503112000d1800107500600036000404010580949941c50b0030400f44c401412102a0b603c80e0b4410003154816143e14201c86800a10a880c0140c54060150541c0e005110340d8000c02803d041350107120070642500e820920307001131a5a00c0000c02c0c3c0701c03020040d815000a008038008542447e100b48819403052045c409212802400407600b8940a8282d504251003030303484610140c0d240c2d0800c25110041c000301c462100c40f00d0401c12080c00c2c0b41e0b40590303400341550070362942080c82001c03007225998250406805424024840305d6242000114001c0075030040405119075 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 864433489 1250 864432239 864432271
    0xc0503160603230c030903120c04080d05030f0f270309040c030b060d020919061e02120d0509070306060e0f0f0103031d0109030c060e130513080705190308 68
    0x12242442e0515140381201d00c0c0f00c943c0ca511072101e80b1904000c00b00d1201d40700c140200d5450391260701407a800b130440707116070b80d039180e06001e810350a1280044000f0b00340038081041c0300304644090300c02c0e0750003510303202d821701c3d07a848411030115401547c03160080c01c0707150035000c04902c1d000480140752a0008480400000c0e01c041c6c000e4003034820f0400c04551000080c080301400e040725400400403108020040c0390350000401c1d100f040200385400c92000914205020340d020149040c42d0200c00d070650008040311006d02900301403601ca900000910f45450310040b0306208001c200c094080c40e480a81803210f591507180c6120b0402d0101c8252506040740b80200d00c04c3c4c81701d208418166a01a55880320304c00032040941d20032070f180340e503003810001e103c82c0c0080420058001c1201902c0c1d83d5441603801154001044030400780c01c0000c4491900e0300b0701b0300210700f124181c50706c101d81d840241e41d5110700d0b890a200b820680c20420300044c0f0071420110340e00b01940103d042e8403a9031000d2080a00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 864434739 1250 864433489 864433511
    0x150703140604060f05010f03020906130302010206060306091011071a0f01090c14090d020d0b07020f0f0a030806130501080606040c05031e06040902120d020f0a120305040c0503160603 80
    0x7959803d00c18100507044c1000180100d512405e44118103801504001d49440c4601d00814103543c4400036201030100146c1c8184219030741802101e42005044005100600b84070203082c0d1901030f00005c00c1403090b540d000c000d001c001480709071069070ba00a00312291505200d03070400440744088404600140ca00d100204a114540c8243e02ea181c07943c0d40c0304244035400342540f14059120440031135202007099502c82c01030f610300d94038091880c070076101c80109040010002e490201104260f4080e5040707401e0700c038881840099940250354042c41c05c15900d440d980d02141e543d59132064040394142c280400070030380e1400000c10b130b03000c0d040a40e0100006508620f00b20303034502041d1021000400b1200f54030104528041d191500808001d000050040c41580014074840143c00d0100168003c0c040d084d0100f0b030184002071000d0080400740800f10b42170782e04c80d20008503582c8058249a40c4501040a02183c080c44001500c400750031100c40c40a50303014540d007882c10348143c0c00002e00704000c00b00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 864435989 1250 864434739 864434741
    0xc0a0e0f0a05130c110616051614150a0b03030702040b18010306060f270c05040906081006050405070507031206050a080c0a0b0c030723070b0d0e0a030806090405150703140604 77
    0x100c500c401c4440c43c01c044d240e9a0045a242d440400b031040d140964151180c003003544c443d41005a14410400bc11241e40a50350364442554000d00c0c0c1040745242c41c01d40125601c01004454074954121400102c0130f495000043c038440a5005030000c904642c000401085650340c0031b5410388400010580c0090303680c40711480d0104184a0300000180c8940b01c0040d0740125401c505420b01c100e0403c1c0f400d190b1203a0041d000c68030503910480203a4050b501d92500c02503548290030141005840a04c00d61030107000c05006481455001420001d0010a2110b01202540440013038600202508207269644200030366032490702403480c0c232803101d02c0f0002451903c08412100c1030008040590f081c00b6082d1212800840140300302c2d00d007421035424540e10400c062003c2c40281000302001d07070300e441ea0390302083c00b110500014074074264010079000d004280c00c070b0486a03000808541417409503450349095802d1959039000186082421024040c02581507044200001c1100d070040105d5900c40007008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 864437239 1250 864435989 864435991
    0x10060510091205120f0913020703080f1e01031505060103090c120501060b22140d080c0a060507031d010b060a0507140f07030b0c0a0e0f0a05130c1106 66
    0x40400c01c103080400070040c0581c0c280001a002e001911311008280d481c2800c0740e07210b030011610f14440001c030720109240039640303140c0342c001c1000d0445c200a4143d601030301c0007001803c0095202c2d40d40c0c00003400c23001c081801c1d070142407003400d9006d01035959103400c401041c01c49403040c10340ca0400000492652191158a400b640c204c04419041858003405000c8134059030005c2c0c40d25501c0e15404185d000f0004000c1046200e59100e81030007400303c0c0c812001c2d8295640141c0514803030442e044240c2e0382c03078007044480560068080ca944640d0305d20011f14058180ba00100441d0a12003004901c03038041d8441c02c03030f01006880c1e00644c00c4205107100c0c2250030150256901c10020710180314250311600250890702d114101d000200c01e0081e03002443d0641004803005660302800f024401c100c405003a0303a802440141800b0300b890308000005c2c10b00040e50b00110300407120424503000b40c0da2441d12000c006d10000e000032010000034240e007800313400300161501c08200d840c01d040031491030000f469 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 864438489 1250 864437239 864437269
    0x10501050c0c09090a0506090c010e0315070509060405040f091403130e070306050306040b250c060c14070b0406150501021005151206090c120c0609060706060305100605 74
    0xb0b03004002078030082100a082c06031030a01244560826140000ea0804c1854042c0c2644002020444280d500052000700d01c0c5242c14025081601c0d526510408005c1c0380381c0040c490300308144c485801c5401304410703000e80c1d40807aa000f420070360600d09145241d0f00c641d1381e0718045d003003100054202c18141c0e6500c0c0310f0034040e1007483d05061020014040a11001d580003a1140340101d5032554600000e4606941990169009030244061261803010042280040c0709060402540401c6800014066617083d80307000d00b030f180d11a03412980803442809507241918440707047c2506c2d100941010415941d04540841d109850607001ca0140a425840034003103440c164010100400365085e00b10140401030a4000b20f100c0c14001d4204580d40d108105120707001c41e0000f000c41c0c0c6040c40165107020b5201c803550b406400c07240e00030030b00f03d90080785006a5440070b84415a60b180c0c99401f2944500c103105000d42514a030000201c2041808030320310301041402c07402404204d488404000c2c4903100d0a2038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 864439739 1250 864438489 864438493
    0x12140603011d031e070f14060709051c02041d01023013110303191b030f03090c0b0307020c0102160506090904020d0204050a0c0f08010b030a020c24040605010501050c 73
    0x140311501c04008041002c1030710000d1420301200d69548050074560080880d992504d1f810024048541003020662000940c030300b021105142c000130440aa051190380321292203e03e0b940000c1d0b4999400040c42d194110b081c00308452481242a8000d4112070b0488800c01014100794034100303005d58126411113460138194006445d42d1900c0012400010421241e018071006409860742e03091020340040f56190a00320b44084803c800148601c072042d003580c0590310fa4040031004680c3c45000c0c5a2070606c28100018890418200b0188060762542f000d91300d614000104000164013052012202c5800c1c0c00f115244103540220b0031007010680155078100310140024110762501c0001281c02a0000c1e000c0c2018500c0c0d41c0104064440c2214440039807520390340c41080c0755900c400c0f4048503035010b1514280c42c0d41012a04180c17880081c00740106241c0205200c3c20500c0c080c032032809000176800c00071071980024101494610340464065688c00d16107000064194001c20440e40010301100c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 864440989 1250 864439739 864439747
    0x230606180103120309170c1501120b0103111309210504180209061c050402030c010e03060f1e130309050d050d0f121a0a140a140112140603011d03 64
    0x84004000620050315807201b008544080a0b03100c400620306081101c01803c0d0b0900c0e80c1014411115040e4442d80c0c440c58030384144e102180214900606590f48460072840350b2400d00e000882040c5000c0d00035841c185003400c03c41c10820700304aa40601d184004a4002503411034030190340e070b80242d2013032080721038409003030351010413065004008071400100344a042c07185540084010710040f02d24006110740d140184420740c5000c000903040b18a0074a0505c13044006a80483d4840001404a44124208401191000200c90100c0c00c08068586040d07246261154104041d00c51025040e000328070b0081020503e1700300450041c0c20140c101c8014100070940b002e08540704812041351070301b000118400031545640e20301401040701c1a0360002641040c2c27450400100040c2a80120303610140d030303070400e160740d210368002c41c0031100c40710008510039008100581e0540c05c4140382c444c04901d443c5107101d00701d410380c80c100d0140b003054008010f1000c0001d0b07800e161110404d02c2c4240355000344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 864442239 1250 864440989 864441023
    0x30d0906051005032e0608030c0f0601060c0b0405030d0504150507031109130f06060f180608040b090c1804030206070e031c020120340609230606180103 67
    0x42005c00021036401d00303c0503410380200c40e406c4803880d0300202902d03000001c0c150880c023001c04c40031040146000c09455154903081000e40044241c0e140103200b0034641000030f042c85820b00c15220780030316054082c17161740750030b140c40d00c444040300166044091420004c01c09d424030034400c60302a4505650320390701c2c0c08240c2c010013101100c4059070703a0170b040d10343c0c04011140d807081c0103800007002c090311040071801c04068042c00204441c00301c041000720003502005545e074050301d03558100760000c84109894546914082c10840400141d50300300c2216011100b2001180340300300e2249010b41e00340c40742038a50160403195a60078a1031258154007440d0300a0040b602d4000d050003100d442c5c0000107101a880d68040349140708440c40183d07040021a4000d01c02c0043d109030301d10103404201080a0045100c581134403010199400b420303075542c44002100300444612132520354a000c203007034190301140c00c002d03594070300d821190940103000c7c494000400d0b145071441613050703ea0100f51259139506203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 864443489 1250 864442239 864442273
    0xd050301090e0a02280902031005042703090f0e04020904080d060807030807110a03050a060f2403060e0c030322030210020c0405061f03050c0903030d090605100503 72
    0x124182c203006008038207038080180c0d00c0e982ca01098542481400307a0000310f11651804c3e0b2101e642c45030021310700400c2009903244a204100302601c00440300042c4a030f8170155084120301902c40c0500702180a500b0900505400000c58011036400c554601d48858450340040c840c1402914000c0d00706d415040860000342151001d0042800140705c0041c0041d41c9141c1c0616020103070b8002d460f420070015090043c00300a18000c0549070f020384406868610f1655115074038a00e03004060100d0b9500c81e040b80384040c0d160010402848c40c0800240002c925105008820780240300c115280b0b0301c0c000300210b491601050b100f40c008401400365042c001d40f0b807480301801e806014007030240f1000040110041c2d0703074050800c0c0002c0390395008007d00a000c60a00007102c4000e440e451051488006c1030614010305100c15007018a01d18011409031510035440b1001d000d54004a03606020202e0b00c0c3e156464590300030042c0754042d031018046038591110450440009003c1d0a4054208442d03610120940c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 864444739 1250 864443489 864443501
    0x15020c0f030c18090d08010315051b040306020c0c040b01050f1e0f040303111f0209120106080309030c0d08030601140f030a05040b0703151a0409021201170d05030109 73
    0x406415030b65403952400000340c00c030100314a010540790503003050255442c2d041000e503508040d41e0900203082d5040d5111540c1080210700011030701900e400c0002d20304020300c038900d40b8201c40c4401c52611a612403800c3c0b4040c1d0041d1044809078410006909a070307183c02d002c1d014500f58181c40340d9217030007100000003009500c02d0f1b82d910828221101e48000744186403000300b00c0f0100c2c60040310740392400c5142c010543c40214120340250f03841880741d01d07000034514000200001c4030b82d00040c0d407050f540c03000c10942407049400c01d045502c1c0440003d0080c2c008002000100c0c070441c25181819260010040c0c0c0509421002d001400305000003070903540914505051301c0312040d1280e0505541c40c1004c8040c0c0d10803241c03e2101c0d82c5900622007041800c00443d50462101e05081c000c00ca2128240036000c007043c421142880000d10342940c0c1c4070042c0d01190301601c0031100540d5078001c600c80d03080441d1000c1c400e10f03108403103480448103150404034112400a2050b0b4426146910b0014480060700e0703 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 864445989 1250 864444739 864444769
    0x10f030209060d05010510030227010e0a080106140603040f0210170901062c07140403020409051c02070b07030e04060824071805150c0d09030203010615020c 69
    0x5400c1054000355a02e42024145058045101094a604002c20310403290003810100302454014004036210301280114214019160303e80d0200302e1701c109004031090b40b01c800343d55400c5003180d035000c92740c2001900050256a203921000300740c1d5225801f130210f41d100468000d0061403a8420150051410160003000d8420b14941158464030b035540403044810705075001c40040e03550316010002c420301140945104421501c08400c4c0006604580100302801000c007000c001d401300038001070b01040e00550b800303940c010b40100202c2c0d041d0300c1c00300d07034412040000880116423181410540340c4001081001d46140c01c40c0a4107028407903400741c503001e020300c0141f07a000707031a80004903440d00c080200ca4010040c0a82c001c68607a0405a55140c200010789000708208402660724000c44e400448401201d20680e50b20b2410951001034000501401e500b20009008442030030b052690b010441c001528000c800801525039210810101030041e40c4801000d40c101ca004190240740c203102c1c40305406 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 864447239 1250 864445989 864445991
    0xa0b301902151306051305010c080904050a02040915050301110a05040e071b030203120a0218090901090507470a0c140106030615050105120c07020414070809011406010f03 75
    0x100f0007000e46120858020100103500801c05009001e5030030b0310000100004c0c20600c10104c1e00c1e8075154500d20601c481a4003403503c94001c104510900e0341150002c050382e0001f0007800c0109000d40d075607000da601c1143d11035820500840c2e402c040c10011581d0307000281d2034140c54185400c01c24040f8030401031404007488010900040c4440f40800800482e501c680d02071681d801c2c03c034900b0001d903074000e80728441c150310601801e000ca0040005491100c801200c80c8010f641d11100d056000d4500b49400038150f0007034810003d0b00d00010401c8a46000000996400652400280c001080d0b02d143c0007100b0040305444405200c214040104020881481d001c0c41105050310b80f0400300e0301c6440140c4240c0e54802080080c404e4a2081040344001002ca404c606460840020a1405111030f1089000000c4001c00c0340300b200602104d1410340d0251041c0301d0f2907200c1c01604900c14007140c103078000c00d541c840050720054040c441c0d9204a682000a1003042c0c543c01c0c01103480c00d0882c05014181 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 864448489 1250 864447239 864447247
    0x110d05243103020f030a08160c0210270806010806090307020d0f030509030a05060a0e0c06030a021c06091b0809060403050c07080712110118060302030a0b30190215 72
    0x18040510042046d11215103a0008608052400070302c01d11004071780307104100440c040c8a0041e61513502e0701550001d6440c1a8041900d204c95905005e40e081240c01c051000301000028407201c040fa180d4125098082030f542556558884992280314001009601440d888803600005400001f20b12049001c1d1400f14100145a0b02291808800315030503280e5038851002c008001010b4000c04210700301e018050000c04140c140896914000a0010b1111980114a110b51426480046443c070801d001d028029150f480080c60001d0804060341910161100390250856004020450007500b0308401040d0039174590300c0031125034000c0920400240240c6d03000203584e0008000d030401604181021110042451400f544404680b1605074103100c0303410035240101c1da000074000201e41403401d01682e256580500e0000900354039400703941c00100b14a688107169400308440745c5051000d68009801c1500b010b0180e0785141030f80c051412201208851030050600e20310714141c0c055a1350300b49042c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 864449739 1250 864448489 864448513
    0x60f0d18020607150c09030201120c1b080409060b07020d11130204271401120203010609020a0203031504020f07110d0f12020615010c110d0524310302 66
    0x4030340c00a80141c556102101684c0403111003841707032220341002400d150039900d02c4c540c000b0384081e00e201d081d040c401d62780d01401e034051405800050f43c54004003844956402d000c0c40e002c06280c00502840c4810342c9854408500100441c2c11603c0c0c90ba0002c0c14804c4140d107607620280308115040003240c20a010710342600e040c0009002030009030070035983e80d030380b82c0c6141e1070406000c000c1e01c120360240c1401d14120340c072440c034403280e1a419176640c104e0b100900701090012a014004030350002c1d010760302c0014010b000c1640413000c0d40c040c44080e0340b403805601c16413041009030700a903c07003517010040810032240058401401c00c82c200c44050b003c4024507100d0303250a8604d0301860f4091780c260103a030780c17225403050341404600d5205503009450000c2c0740c20000000e00500319000700514a13000e44401030b115541e08030542c8400b036842400c071140050401040c00384502e6000780302070325200480100e11081008411a000125075141c40e4202412140004a0900071040150250f0040c00b0445407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 864450989 1250 864449739 864449749
    0x1290310020412111804030f1116140f090c0d0e0601030302031c0510030f0602070506090c010f1412190507020102030f010501020a0b0402150c030403050a020f060f0d1802 75
    0x80a03190307400505107801341407540c043c08a0a40c5144948020741c6803410305000c0e42205a040b9416181c0801d186010380806d5807480c100e4000e00c5a54452855144d09480340201c48170b060b11850010a0030030400382d0213100031039009512960b841084600010450020320026100c0c2d88081380c4041002c10348001014200301081e0030540058000041a00c002800701c050400701c00c2000d0b204100600c0c1110008540351310342d0000a03d6006905181e1051020344d8040d079203aa900002681c4181c2840e50440343e8400c40ca0503d2030120704402006442c0c10b010f03505041c2c00a19296049141031038501c44642c0c00e80f070062207110100351107141150558180d2203960711403800ca80005a890510209410154105a001d581103510922044001800141c000c07604242d064403c0c0402c00e9503440401514080c16070b5444a07440040782c00802d001000405002d03080c0240e0b420311030914868180103940c4500762040c0358000c0200b0101c0c0318050213034808444c40c0103034013055c0491507641d400a5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 864452239 1250 864450989 864450997
    0x90b09010909052814010e0c0702040b150a091401020a0519020120010903090e0105010e010c0519110a090605090c0c0a120806040608060112030323040305030f090129031002 76
    0xc404644c0d0341c0082c590301790100c21450b0150408400081c810f2500c01c9103151a4481c02e14001c2c01581c55481c40d0116842d071009030b40315207000d070311072903142c556071a0018410209841445059003140224108650021402404550704080500b001c4807981c0014030003154681b900302d040002c00d0345203040a10100b00000a4900c810001142000f0a420018082d19507904031a520b2114607004010a80e00030b1201042690207090025856000b030820300d0602251000c115045c800910300c8100700020445001c0d03d54408444002c0e10580f100070784e0048030024020b8507049034154000c103000c4542440604121851401140d6031142c95940700c50603107280d4180350340070911b010103010061800e03000b00c601502c03412006120b10340c540320000c1c4082c00c200c0c0e00601415501c000040620b550000302d000f90740b2508520540b00e00b8a86401030840e44210360504072884140045240f41d001801002403030f0754006100d4203100070100c08092583c03042c80445900d403050280c10b454481d054000341c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 864453489 1250 864452239 864452311
    0x20a0927050c03090d021203071d220e06280f02161101170714120124140d0f0227011b0c0312120219090b0901090905 52
    0x54980c240250340a02d41000d8917540c00c10340d0040701007003020200380000d40b5407000051a00004c3c5a0340b0b00740710010000c40c400c80301e03000403100c0840e0144543c01c01c41803a6032031905404001410380c001d0900c1e250b8500380d44948616400c4441481440c40e12111014800000500003d88000c0740304080100c0e40a00c0301e0080740007005204109004a906d100c42c003013407003030070a0ad00000301c2400d10090001d00034140001e1025600032178030b0014491040c1e91a613400760100501c2ea5840344644c10505e00c04020b0070300c00e0a85c620b442182c4c1c078425510110034803031034000e0a003000180040c10010301706600d400301801e642400420150094400c944c460310240070800140d4a071844001040c889100981e42c2c00c407155600c15800003144a00c1c580c040304c2d0462801ca040302c4078400210f402d00081003151030000d0001c01c003204c892010010903490302030301c0e484030707440705036140d6500926000d1449440d002c81c13841c1004101200250f04201c1c0c1c000721800311417404040c1c02d83d6542101d0488001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 864454739 1250 864453489 864453511
    0xe16030b01061704050c06031f0306061a040308030601140d0c09060207090b0904020402130f17070906120308060a0807060206090601090203090a12020a020406031a0a020a092705 78
    0x40110b039400040200c440341450100c60143e14080e00c0d9251395814960780c0034080e031400800184107090401d58094012942d41103800c030b0654a080c2030019121500909070400780c80b401d1103c05480d140300700c0f801c0780d5000c40c009080d52f40748401035030201080081c1c0a03020100300424601d4007045d10501540722003075101d0940103801c0c104024602582ca4001010041c580b80c81c032209a0742c0c9100321680180d0440c3c0c0981c0d0740340b04c0450a84040f8055014020b5044a01000b04e48851248010402c045844040751507080d610b40b0b549095179428403c00e92407501e07070340c24100482c0c400d01180c0d6124a0242183e95410380e2004003a00c2e01d0003542c02100141c04c40c8003030040001c4140b00c42801400700c02d2044d4154200b000480c2c0d11982c90400c0203040861061074007894038001c0c411032107429001081001090f0b607030704180741f14090400009120010700400114104070754030980d00000308599507100300f541044120165007111481071031a54024820f50304041d0400c1c082e091107600b082107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 864455989 1250 864454739 864454741
    0x5040b040603140601030506033a0206070f0305160c0501090203070b0c0705150a052b0207144e04030203190f08160210180501090305030702040e16030b 67
    0x3c0e501e46600300140c120381c10107080c1002e124aa690004858400451403114061009801011017450920030706114040c410711030b204131000303034000c18001c0c4100c00e140c541145c4601c441c0001c5044400480d0303400340300e4841e0036a40d0441c9100c0d01c6601841e602c03410002440c0b09150300040d28250700e59000074031032400001e516008a01c2070280e50000d02080d14205000510b0b480403450034003078081154100400030520751030640646480c208410b001148031030300410900300000181d031107820300355000d03038070120344000300710002408044943e108002ea50307007510007986022510381030f141d040305044000c1c0501c24503444d01861801140340032640b00d07039075940f4520605040c2111740110455001c0c0c0d001d69900071400c0c146190a55070740c007801d480e68600c1c45203140b462216225034040d40103a001500700880381d030030058000401803030034400140d1980d01c1c801191440c417140001401c0d41c0092000398014100794225654108a81050780c3c0705031a0f0080c601d402d0403a6078419143d0070007100c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 864457239 1250 864455989 864456011
    0xf0e010c030f0608060a0203060a17030405010f110c120f1605030c0105041d0a06082505040213120201052503030b060a02150c0f0a02100f060f030f0305040b040603 72
    0x120501e5181c040b2280188201803a0020617900c40100a00c00d0746002e400000280c0c0e555103800816018104644010320422106224143d49400a016941c003080940c101004040d00034120401c4c8081c160b002081881e10380c1040c44520032607401d08140031311030030b58100300064041c008942c0d000c51020210340b00b0740c45c00b410036280801802070541880070420060180440780038000c00e0040740502000120b40342c841c481d0005105540c42509240604a0141000d03659920150240c10308044105481600d50381003100b01c0c800c070f800e0044103020040c003c20009000f043c03151141d0b401410942d0034100740300030f0500d0701d0b1207001c1158000c01c15803020004154041c0b0911900c4102614000d0030480020806980e034008540d10070403609440c000941d401b081c0808850002110410b840d8640c6080503010303656212601129079061b040a1810545078014401c034001c884900c580307812414a951243d440303a00c0310440a504100c8100b0021a207040144c00420042805580000da091095 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 864458489 1250 864457239 864457241
    0x19092118090b0a120b01030b190c0206250e010305041104150f0603110f090d12020c09010503161505040302040204030f110a05090c0a0c050d020105091507091202040f0e010c03 77
    0x41e4011000350b13046520703030b10007107800d01c8100d03419130b5408412010030391202601c5d186503d607042c00f8143c1e001c0c2441207203420280d02155050150f8480c20150003c085410910340c040f40d440150140060041e442024541d8800c0d04640e80103800385021001e452103840103d0141c0340445144c001c5c450300910104844164008410000c00c0700785410005072560071201c9000e03200308030018072100f001044408603507071000c0400c855240d11a91912880025100107511a69030030000340c840c40c0c0b403000001d2181404a000180840200c8e0f4103401030b8100f080f6008086060401e00c01007041c21701c00030006842d1440108041c42c020304c01881203409904c0c11b0000d4803040304029014003803900040103a600c803541c00715004034200052684495000204036008008560084c00b684989041440500c0e0103502c202e020b1014103040da40280c001d40300c106a100b01c00c1c2c51320b1002170b28992080022204440e01013200c00e20042c404203114903c0b075150020b03a09003001000302039550305074004c0703c2501 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 864459739 1250 864458489 864458509
    0x1603020a050d05090d0201030207030e03011a040e0f06071b150504060b061614030d05150a080f03041a0904020a030e0601080a0c1505070c06020619092118090b 70
    0x561a04034034013007080021030101039511000905044e00410400c0c00c260151511180150000e0000c101d20710015806070901410080c1e15401186071041c070700000031010512412465094000344940d841d07070001251054404018480451403524500f8006500d8030002e250b4065616804589401c2500b04401103c0341d020b4a148112410004504d0392000740c0000f9824640119507072456940a080071801d602c01c0890389103007140b906042003480d1000d074055008154060325009212510b036085140d68010110480002d68030603c820010180b04031503050303010013288074140c140025100440c0c00d030b0300008c1b040004281c517036040d8441c3c10410010349004140c2c810040044280030b44502e107280a00380550f0081a074041c2d159881c2c41c0c0610101ca10541c0d202440d80c00c0b196031440e0080d03c2d40400d40c1c43c1c015074484c4a4030940340003118002e02601c40e030000518501e0588412070b8020401682e0200380500139049610500310074155a00303801800c0302d000204448020b03004008074207007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 864460989 1250 864459739 864459763
    0x302010f050a0504030c0201080709150519020109030822020d050c0114130608090102040b13030b0f1e060d150606140403030926030f07032c151603020a05 68
    0x45800d0030440400d5004d5120200c0d44d40a0a00041c16254400c1c1114980b80d10f8000b030702299045682407010cd6031000c000c00d81a0508802d8101031007440d003080f401d98100c0e4034050300050b6010b01041c407030488c502c5a180080e0540605450144c0580e01140e1a82110841581c5a03003050000c8980c0e560060800341942c60ba50310600c0c600b0015044842c407901a0780210b00030400002c000852100f401d60468015113190b140440d115002034805500b4170103180011540c0c1c0844030003286010349a041c003180202341070550340c1d459284c8030750b00c0b4513600c10040115a000021026480c04a481c003401c00a0440342040c020a12a04005021340200c0e0001c821128082040004201081d03100e10b81d481030318440c10800451015140d036076040e0601980c030360407143c0000240c0410442805005040d09407103030311001d219091001000814100c80e4000c40c04801070019050034625082d542c5d000040b031640c242d40d08010201949500d402c003191001c6001d079218100d0002409020800d18224403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 864462239 1250 864460989 864460991
    0x15040b0906100f1b050102070309060f020d081f0f05120313051504231201090308010308130e090303070818151b0c0a1514150d0f0302010f050a 63
    0x104000000c5264640c00850950400040c59400000ca6104c2d90300c0301c40c052007a01034008a4141400c01a000f5406841c080700810200d60000560500810340741003000600d40241c0200c3d55039500a5503d810300030607205d50032810b625440c480b03038201052180030740a640c0020315007d0401042c419229801c20040201d41c0c0240910804180307507500d07000955106a811145407445480c1c445003070300803504141d144041c2040d070400c2840d089010381c075980004481040e100021240c4040c2258141d01d0f028001414410051012840400c0213006540c804200481c849030f0342d0324160200c030803d540c02c948580001003409045540500090303001030994400f0500044200c0e503813030f174949242070200c6c0070224010002d141415141036040401031028040c0b547e400c0006030f03464541c05410380485034006c45440801c2480c03801d00c503200180c148442d03104025210340040c610410303240300314030b644101d6031400f103000151103c1d2a5a00f4034800d40012aa0800c001d450f001a00c500424211088d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 864463489 1250 864462239 864462241
    0x503100f050c070803061e090a1b090e0403140c0a030e0306070503060d110303120a151a1602040207051501030b0108010209010e3a140601080d050a050702030615040b09 74
    0x111303001c1c20840c1d401c004200c039028414150060000d0072001300628103680300c0c01410130400300041c2da400081100b6a070104000c0241026030060383d4117000c0780922541d0300200300015000034080c15906180c1c8401003005418026030030b600600e0842ca0302d60884c00a1107101d40e40105040400910750025a2810035a055181400c0420307020040c0780000380441d880101d60794041d07107042c411078249904002d0440083d20f4840c070040098500000c0c1620300e0301c101d0704c00290644146152007070714140ec6001030714000c240b25800700c61390f44131001660f20940c06c008510000c2c200300f22481e04000030007403110742585103090581000d10164030100395640108005241c1d6070303004140304003c8204540b0800b0b1140c180b181c5800d40201030310000415412003515184018106140c4030501e4444c02904528040e500c140ba41c40e02c0c028072400803a64000a1340c030104034002d00180c48120745074500780e428000b09400103440c2c15019112000404104a140112401c01d4058041c1d40781040d1031240507 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 864464739 1250 864463489 864463493
    0x203012715050c070209040309051509210613050f030a18170712030c14060619080606120f032a0105070f2a0b060406080604080a03150503100f050c07 66
    0x1c038403e404c0001d1095040354000b0f01014003c0704900040c280c0604142c42d00c9000c0e80d040c0315070380d20064456118000c4186a881c2404004041c020070010000140036591907204004801d58441034007215a4003074621402e9000c803040002d071488003003550700d60361703aa00340130420840d02d0300c00d80000c4c02c00942c6c01100c05400e10b00041840c110340100080c2c0c100b118860408a0307001c43d86060040410343d0714072900c1e002c0400064428090310b000c86000c04540c480e04496903100300c080c443e60a190f045140000c40502e0b00b941c601c0314070600740701a50481a2070b601403a0955200410142c0c3c480311103d2040110344098194071740d0400c07008002c1140341481c4c2c2c000b400c5030030012501c030100014a50015004040301000002d4000480c10391400e00b40c80e46040309540c50121046e9000d2850301c1c5001500250029141e8000d40c2c01006040c9403001d4103c08601800000c02d405825180303a060010341902e04000701c018001000c100094200ca0414541781600c00240420117200b80601903240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 864465989 1250 864464739 864464761
    0x9020f120108071203080a0e16050901050d1104020a030e0d02060f0708010b03060d0201050405030d080a0e070303090902031e13020312190516050604080c0601060c0b040807020301271505 82
    0x9800340c160030040360340e07525801d005010323000255014040d400b038195495810010b80c2003000640718202d50480007a84c991042c401002559000605000c2040c0c1c1c0700d800700d0500e0703402071424400c503282c04a9001200c601d4546450385c64010000142e05c043c00f040740450345c000d0400d4000405203040c10a03549869a42c0b1080d00024000c0c0388508448010042103a014004550080c03c010701038950303440c000440503000120803070b400d0204500700200382003d044c0100b640701c1540c3c0e05840d100e440a080403c0c41c002904028000d403600218900d21620348a00788030f4062142001124540c0e44003aa4810300d420090010701d07401c00c1c41c00500c0121b0b0346d020484060301c0740082901c4c103291540707406602128080c2009034081c1403401440184024880c4580080c400000700604541b00390341d031460304898584960310081c000c001603a0104000a003403900070440140014000f007840d51b42d0300800c010808100064001c40e00816520310108445564100d41c42104e1590800c19403401340c04c541 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 864467239 1250 864465989 864466019
    0x90305030103030f020a0606080304060e040608070623030a0e0d110618150a091211031606090c080615010e0609041d191e1112010609020f12010807 65
    0xc00b44402801c090720224170811024100c1da03044102030102c15a150900d980f030743d216004410010300120a40c44041c180f6006144c1203440c0c5a0080855501c1c00008481c10307680c032610b0000f020700c02043c0e00ca0100e00d28014500a0010017800101c40c00c4042c000ea10381440c070382c508418808403810106058001044969000c00001c14400c0e030b03601030701a8103080210128030742d50340c43c1c0e5250074042e1301480c030b03800045411311403039011882e140341c0701040d500c1151074524030301607610800000c803010000c107501c444040d10a09020440b00080d541784d001c0c045a40c2c02100342540a8400c11041c49010a6526809002030038084009051180480c841c0e21441d192039000c6c03138032541c444c642c100d0301c841c0d4003d0030000a8181d4151500a5000035032040d0094800d54080380c20701d030385181e01000d0145408405910030003a440b452154400c0c0411901e10414200580d50f90b107a0000302104280028007100c204072038060790b100d410f01e04a01c442c5074181c00c400760320351200310280108455803d4034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 864468489 1250 864467239 864467243
    0x513060218190503061b0d020a0c050318040f0b0a120507150f03060b0309061603060b0a030506130902060f0c0106050a030b0a05060f010e010302030408090d0503030f0a090305030103 80
    0x15a4502a80c41640c0301c200040007000e420840481c05006401d0781806441c041c1e41085080e1000c98a80614818144803090001080b4200400c4141c054000303179801030040c075501c1d0400c407410b020144c6909003141c0010b51000079402e00d102154650b031801d8807914801b800da000081007132886440200d103001e0054050a0382c0708003441c1c0e03044140312040001000924903440104068070303c80c18004c01c41c401c6004030202090404101040041c0854240c5c0d100d0800c0c00014031956035100381c07031902042c014030450145555520045441c9007040000c0c00340c1c403100c1d100407649003408400d000c040910002c0401c80b142c0740a01210050740c03068226070301c0b61440041140c03190841e0300e04130b0050400398826030348445090300c00410440c813558014490740c512082089255034203800d104900c07104004d80f81c002150000036140a60083d409942c001e4080d070510780c2000c1e041d1003c130342072082400081d0742a80c0b0100400040154400400d6440007400c40244480b410b16600a41180418000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 864469739 1250 864468489 864468491
    0x420040302090c040f061205060303090d08030a09050102030a0903020c06070c17070b04090506040b01020616050c1f021909030f02270414070807050303041406160605010e0703051306 80
    0x41007503c014101684c0151100c41121903902c3d65954000e0b00d00d2500c076403070030700381420140003403002e16020055541800c0060814050b44440b640c842ca40350748000c0403011540e55480032880483c4091005e10710410201d180024101600d00300030340f034142c8810600d0310038802003180381c002a50240341c4c0c031f048583c011030036045480403203410f90504030a0b4100b04c501401c08a00003442e407040c1e40166000380c500b601c080108030300c20346c0126280d1408444441c03804060798541000707207105900501c603030044041628003121794441003a0841003500c064240482e00400d5100e0006c3c0c8440719400b1280c00e600340310440780d00d140e507404400084110060701c10004e407112810f074244180303034640c4411411802c2000074076140c80e10150385250301d41782d5600381c483c94070048dd000000050040030744400600440c00c0916182040f445000a414a56080702051050300000070048004140d5284614000309056050003101200c1c12401001c540070903050a003031081aa4890820345c40058000300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 864470989 1250 864469739 864469741
    0x90f0b0415050f070b0a0603020127050f01032a2a0f0c05090403030501090e031215011403090f100b06161b030b090c0d050312090a060c050306042004030209 69
    0x50090013629130240c124000c050802019841c41e03802401907a200b62680d94440c414444608111042c120301c00303250a4601c07005202c01d03d002d00500290120524000c0b48a5110f0507090091078202c000000400f16141907004400d504100d00c0d14031050003403032042c800c0c0001b60000c104000900000762091030400f02d68800c1c01070502000300603020207010900c3d981010715000b4000c003400d03c0781200007807405201552002011040310084030081c00c80004035101c0795801c440d844134401100f414017040c0c0640400d21104d0001851041c008000904001c2901600c42814101c45181c0550210b1a00c003000d10140d484078241d43e500001c40d447e00388000003500d412403401c1c80c0050460311010050000004210142e525544980c80103000d8030014087d40082c01003884080400800700e8205001c01906490000c40c11a404406607048801c041c0098030b500c81120300000700100055000000c20586042c24050548803004c030244030030351510010074095039070007076000003882264000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 864472239 1250 864470989 864471007
    0xf0203040f060804031e0f0509210610050108060a0b03280605030f061308030403140f03091908032202030f0d14031b070303090c06090f0b041505 64
    0x50328003514001218207403054507548003502e40e8000312002c40c0012004000c003115029900f000c09040145030300c440c0030b40025240c055907940c00841c03070301c1e401000702d0b0841243c2e012940c8500040c40b1282000e080c26040418005092035001c2d0011814006203070306100d09925816680000c840143c404244c4075107442040c0c1c2d180c0c4088080d04e42003251840c45c04402003540d58022821682c044044401e50700c034a403403c80e2900011180071042c2200c001c41c00300403c0f00c5e140115030251080c0350254031107880b145069090341015501031860070303020003017203000842040b40c04114a01075205403000c50540d621003030a0b00c00240038000312481220400800481c0400c07405a0300c0e03000341650305202040380c1c2d42c2c1d034601c13405100f84001030071a84400c03162f02a01c4105c0340200a42c07034604c00405203401e140c180c0da40c001c2d039088040640c1e42d100c49010880d41d44454010f0007090380c2381901c4624100d980b003510032858001d00300b0040204020001c4c255038409002d0903510a0408903101c05e510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 864473489 1250 864472239 864472243
    0xa080309030705060412090e1b09030709020d060f05030c090a020a020c030f03070b01050904030e0405040c090e1006050103140a051012060209100921060b0418060c0e09070f02 77
    0x140000500e04d1081c030040c4400c1164450780408040c0d0241d82e408130156130f5220300c485400050380c0010301c1304e00303000e01810700c00c01c001c0050903403034406000c45200507900e84a2000b01c0c0e00180b58407a03e03503519a024807414004607220001000214020240110050000765401074040c01c2c03200380b0b0741c0c0001c400000d00d0090000014100c00107040c0da80c95890400510384035407120348100d5940c9841070007c100381c40c1418100b0702642d055070310b05003607188140610005203000f90042c0d40d240440c48000846c00442c1c007500c50710044100140c24460342e045000781c25100d243d04040c0c10f05043c08642718070302661500460b40444055404036031500c070302c031a1400d48015900102ea01490b100302240521030309400425808100783c403101071500300110103c0b03140105002d03c0300c2601005014852080c40d18000e840340234010680060806003210019003107581500181c408090480304a01c1486114890613007c1c240b0b908160016519107000502c0401000f404101880b414400390080d241c42 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 864474739 1250 864473489 864473497
    0x1061107090606170924040b070f02250e1306060509011a0702040603080a020703030f080106080403030b0a09020c071406030c040b03040f06060311030f210a050c06011409090d020a08030903 83
    0x283c8100c0801e500c1c040340021b04003003c01c403003e0311041490710100300030300e228401c2d00201e841240c2c00b80090a400581c3c980c04241e010180078102980400085040181c1400b85805403080411000505100c0c0c5445030a48040350301c8284501b0150740100480c007054560000c03848240350300305581d04098030014000f0078441c0c0010340340310008140f0600c0c09800181d407100760387c02030300d4100c00100c80303c0d001c4840b02d009000d41c0c0c0c00514500c000c01d00290088e001000010760051401e0506516150308000300d0300301c102949a15070211204001d036071258038144611201c2a2116031542c6440007103c41c01d881030340300d186044400000000d040c46180301805000c42c0d40104140092031f17a03030a11b46003055100b0400e40c401e004910280c0e0400200040e0008107800c039011444a00002d1480e4140700d400080803241401820010244208030500103e03010301a04000d01c810000340c9420b00a000b0f00003044984c1681c00010f005084540014516000560048416a407562005501c5040d401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 864475989 1250 864474739 864474763
    0x10b06031b120a0e062212170a1e0b0307030f05070306021210050f0f1c02041b030e0304030807021905130b01020609010b0a0527010611070906061709 66
    0x5604001e0040c0348010343c00009030034010004990180c0c950b0900326400545003480c1d01c2c442d000201b036080000b01d07031072480b0b1400e40c0a4104542c0100051181c542807100444000202a5464560151466260068032000300003c0b60400c14119000042543c0b40403a0201504c403e20305410714003001010898980919130029041d03486600c12010424503400a4030050240d480d400300218207400c240003010711034800100300002180d040403c1c05066012780c0303c4444891001a60200561140e02802c030100c2050411300d60f1030b04031482c2c02401ca5164040d000382d140c00070041000401c6100d02510030b441e804890301034400440303184041c10458030384d1000748c104107020b401c8107416500307a005104101082e026901240d480d90b401c18203c80076050b00d81d500020581003402181000301d1980302d40082c80300102d44020b0718010107a03100d1001d80c4044001100701e00030700c843c0402480303200d0042191050500000c0c0c00c01101400c45202c00000003000d24041d00010203604040104403079005d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 864477239 1250 864475989 864476017
    0xd080a020f22050102150c070f0302010f0c0c0203010506100c03210c02030a27120227090f030316030506041b090f121e03020c0a0e040212010b06031b 66
    0x49010001003865540b40c4034490150251861900295021184040c07090911165040c41c11449030345a088550320340c4c105074210344d0f03100d010341c00012282c45202042d00c0d56072168050501c1d948105800d540008220602805602c07008241d6240c00200a050103645810a018041790a0010940b01c0044680e101e100905040101803019000b00090104051719655194802120350070038071210001c1c901509008000f50f0104060329100c01082e100c40d100600581c0503d50000740d6015003049400803403548080e540a2001d90714080041480e10801c3c20003941c11803802070207034440c100d50746a00a060648410000d02d040e91140c0c401d4410003140e040055642c00030f038400400c0c50307501c0c1c000c0d8a50030300c11420100b80d2480c402049407070203600000d6245041b01002c5000d03071145141504030107520452041340c8090740c80c2c42c40c4001510021001c00c0c4140b80600400c405240b075290f2240c600d034504299401c40d515800c4c00c80e5403220310301d07101d040764032080d00201c075241c0300300b4903400214 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 864478489 1250 864477239 864477277
    0x2091303030e070b04060f020a1e110a0e09070602010b0f0108090c2e031506050a1e08041a04030e190b0c01051b0301150305100e07030e0105090d080a020f 68
    0x81300a10001e001070380c1c495a1034600f07800c000c00043e0b996040e07030701c03025002d000003050b0100d40c41c84001c82510614400c400303004120910901240481d4000e40002012081601c1000b0013208200000401420944001c2c086060700c500420000c0c1c1c64090b41504116001c070004a00b1a02088080d0504001801c043c1291006000c01e030040045031002e0840e03400725014a4036260b21a00941e00340c0410500c3e0f080d8110301d0b0520564059202244c040d00f03001d083c441503042201c1c030003400440e0740c0442e15046814030700351800640003030380d14441c00c6000c3d404505210201e6801041c070003d1250036100c405900c2ca00b10b60807000180790354006808010000340c03070111800d040d0841400b540c1151140759400111104540190000340200004048075404500320584039402041e00032242c002e04413075003511003002041c815012103007000400e807144400829050244140381d4401e041ca005400c9040a807a401040b040004d03108000c000d4001c1650500103001310100d03562a11401c01c0e4000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 864479739 1250 864478489 864478499
    0x40207110d0b0403020d02070501020717120c060a060902040b09010305062101090b0901060315110d09030804020a050609060d0b030c040e1501060206010b03010510020f01061d01050d02091303030e07 87
    0xb2580040310200c0060285401541501c1c4c000240c413030907242d05070081d00c0c01505043c085815405140e4098000b8400c9030400e01a00080307000510000751000c02801841c9044907454060300e0440e0b10900031644100020400145601c0c02d43d8401c0400b468041190b8031231400003500a90905040340f4082680c48503801403900c154043c4288502c00d401c50001956501d96441c222079061101030f0120308030655070b0300c0041d006c2e444606000300040609050156600c060400c40302d0040084010500781070030710043d842d0130070000c001081d04039902c0d0305d40094003001c114540540702115101c1a02c507094001d4541e4148030811280001030402c100c0c40180e0700c200791392400b0714414180013034504000450001d1011401e24143c444d00e0112a1840e46048240f04003045440f01d00b5046000c3c40300b01c40c092003800e000f020010062104203010f07a0304420035004010f030041e80024413442c1c8031600f071001a11400000d03036100c000140e0b44900c564250500340e003d000501c0c4841428000c06c0e20100d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 864480989 1250 864479739 864479753
    0x901020a0b0907031a061c030512240301110f070602041802030613050403020a1101020319080106030b0108090604062d1d010c08160203041a0403050d0807090302040207110d 76
    0x21603000b07512110302000c820741034424449040d0f42c0103030400c007039201c60022900380200c034130f61f0b80d07220340340081c034120202080d20040130f0b00356070041404061411131045103075580c400b44501b050483c002c00141640186e544402e201c1c0080309181901d000c0350b041d09000c0c41e13a064400038050709150034801100b046200c002540102e403d036100b652601c40d072000315500d500c203161090f030385600107080441c61915208442c03c1c450204a04620081050040c104030380740703a511444155407100200f03035040003805026140303c3c5024904001403e400c0007007004000031055003107078020300c00240d41c003100c01c401d0b40c41d80d00380c0f5042b0b0710800c100b10070840c00d0001c03a803010748600340002c0d0510803010103640d11401d80d02302801c003800140e010030100f0340e0849801800080c090484c01280c1c07401d0741c1c031840c160380b031031102c01e869500c0e02c8003203400c01c18420305111898018185140c400340920301254064054150b600010303018a40c0031915008101e514442c0d10b660400040590310212654030f0181 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 864482239 1250 864480989 864481003
    0x80f010b101b020d02060708070f1112250e01120204110a0c0b06011101060e040204050a1104060f0e09190c0f0203090123070b0a1a060405060901020a0b09 68
    0xc0c011181203500d12a01441000b003624981c02000e00518020850380030007400d4200c0103010380e4024020828900040d40c58401082443e10510700d03443e1410580c2070403c041c0c071009801a0189035928a0200c5040c00031503a103c01448402401d40064000c00c0c0d010402f6019030400068400444008110100300101c5c00c040d2501c00c40b000c1c048040344054825240c0104059103020a1442d005070001038000302111760710050624081010b840441c0032582502e0b419444504100e070508180425814180140d0b58862409041801f1554210188054500c01e0348984801c21004030800c41850384038903203101c3d0001000b00402d641e401c00c1c2c2c1d0103908201303400d40c01c507885925084c8505900c0f801044403e00c5001d894014505003c851f80054814143e956404030801310f22400000080c546240503000c0c050040041c10031030706c0c200c02c213002101c800ac04101904144511440d18551b965011902583c10603603050361a5181500142c1c50035000300002411180c80502700401403400103129 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 864483489 1250 864482239 864482261
    0x1b1908151216060c0305030c1b1c0215100b031906060306140a030b0703180501020c0a0308010905010806040f110a14041811190b0307020d091706150406080f01 70
    0x10340c403079614803055070310b4060604e0007008030b8070a20000e8910b000901c05410305500c544103c40c010003110481c0d030700308119110911703042072041d8001044c441d4100700000d00313402001440750b9181070045440f180d91855218480b400700e800030018207425030000980303c22544d490014400203442e017801070041c01041c014024003401141300660146003c100344c01c100c9402113400c1c11580c80d40c0c0b200720060b10804030745200d00541036005100081091004020040151002c0c040c10140384c9001046440107910807180103003402d00610035030348007141b2540c000d80d2201c89812184502c1c50400007211203035550326030001c7c0d0810000b42040da254004600700c04101d408001400f6031191030f6108996414010300b6101e150744600c28241024a4041d030204602005103807403550311025506c45a00484517640180c000751110701d80c198000c01500050284040c10400c00032030101d1082d59105d0003040842d0390648032090304200e0301e40f0307485200908811419034081041e400b0b10300340a40003080300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 864484739 1250 864483489 864483523
    0x3070b040309050f01020318062a030d05181209040b1009090c050f19090302100e0f0603152b050f070503160303030c140409051b19081512 61
    0x1311010766202004403542c0002151441c02103103145001c0c07101a800407040408055180c40f00a41803201100300c00651840000003141d450443c0c00e2400300b80e550140000440c00c407001070542441d0404a844415070320b0a4902e1134581c1c1c21200090301802e40d0a1200d80c0091100b40b43e4002198050010307000ea1f4a07004060040d100d0365901120184500a04103900b03840034042e40c01c2c5070161501009003d0803a03c5c1c1182072039241d40000780f0207010500c3c9903002c02c03d8510080310307a040016035040d203803904036a9242540361552030a502202c600303400500c40c1c4100150a003054140b403450800702e090702c2c010300103200344601e80381d0303580d83c0642254400d51050500000703041c0f4000400580364401300c007445064034039582c5c0c244c1c003514100003100140407003400101020074682020304010180c1d12400315090408124003508140050900d802015007086040084a1008001000c810803441d1a1000703503601c441d681c401c05281040f00340d2205a01390100e040c0ca1000504408038011004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 864485989 1250 864484739 864484759
    0x20d1b02030a020712050a12021c02010515061b0706111b01050a0c0809030a0c14101e03020408011103072a060b0d1a100501030203010803031803070b04030905 70
    0x1400380e0307880c007600c180303a40103900007103051020501e400f0000c00c030b0a12410444e4420525642da4a0b00707042d40d02041001644410100c0300140650501c501c2480d82a000030041c0f42081407a90000783e01100e051806400d000a0b00300b000d10344403c01a000041348010f0f2443c80d0b440d030500801400c00b00c0c001306883e00c2811840c288582c04001c0f04804500142c543d5458000580c10a840100d0001400c2e80c408005011602a946091008240140c0b00c2c0e040044d002d82080c011601d2107443c0c2e1225400f407441070380c0d29001c0580001000050075090f02e0000d100422020045001e48103030303000710b00709500b42064010019800310145024080503100e04008004d403d01a50086080b00418820303c0040030b414000b189440e440040704500203450410344246944030540341001001c44260006814410801c40c01203525102010384024a010340c90342d450080c00c00d5407400090580c505a1840d003135a100510740420480c3c40d002d03403088002c42c0c545002d050181950f580351040a01901c440303e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 864487239 1250 864485989 864486041
    0x1107060e0a0906050f0f061e04050111150a1d0703061a0102060702030a08043305071b0206031f030b15040902090a0908090a0f150c05030a0819020d 65
    0x10080c3c07800d607403003d8401c20341010304008202c000b60300f6a0107990072240070815110384409081400a503101a501c1300e41d900c600d0440010b160310111764042c1c80300e030090b03d000403420b03800418647e00100c4801000c40d03081e48075103014100c8285140039014500c922000002081410781104040c801480d240c01d4620500c10016600d0340e408032200c00040c0c10800c00707113403014000c00045e50068000e41c40062200d401400c60078110382c03072545000d02e52800381d00942d5120031601605500103943e18020120309400d41440c4c541e01e1514000074800c040200014030038540c0c1c40e6543e40254210b5545041d615030303030308000c10f00c03071701c1555015a2801c44050701200340c01d19008403807031300c0d034090080d20040d91000b40150003042005d1088070785060410801d040c4d5907481804802501d04a1003c95015252050103052501c1c0142c481c414404030081c044003044012096440c00300140c24001d815903102c6a90038410010701c82d9906443c0d10120341c0600c04005c541c0280351020003408061041a102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 864488489 1250 864487239 864487241
    0xf12120c1c0206072a12080402030f0f191110090311031912030b060c01060501020105060f0603160504080d0806130603020a09020f1c0c1404060f0e011107060e0a09 72
    0xc45601001c40c41c407a080103070546003807003180441721455210010311249641c8010484103000040000142d80d0403e00065180c14031030540301e80c40c1000101070240000c82d256803214a215980f00500180d000320000740011000d0392494a900101354548400140c4005001014540010360340004400540d04150a0002e030495507049203a20b2038103401e07005e40c1c484040f5085074041400301511550940a280c4852024010880d400c100201c0d10034203090009003122001400c15218442104111902d611190201e0f6000780315400240122040410142c2e6148a01d03400b0300c00500c02c0380c3c1101c6602c1c0d8410315284c003030481202c5800d6074894101164095806a002c041e40c401c1010f1000c0251840341d50007005c24204100407241410900b01c62804644481090300e420141c0314200391081650040ca05c4880301c0d03242a155051509101c4028219144252498140304441121004980c0210031400a0622041c2261129038582c94000c00b9414000c0c4c403540943c903056801b29801c1c2403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 864489739 1250 864488489 864488491
    0x50309042a110a2003010c031d030f070b0915070c06062909040b0d0f020f1801051009080f0c010801090207051213080a11100306050f12120c1c0206 65
    0xa410b00030800f1509940f14007107460490342c55096080e88400c410004c0d0b440a0080380d881801548001641c00c0300e00c0c00e85207030602407420000907600100694580c15000e03200351000c0310f0b0016664102540c41d446c1c0039107001c2074000306a058035441002c1025542e0b008425041a601c43c0005104940c3d48803d42120140b13a101a0304030101c104c06000503003800782c000b03429407903001400411044040740116000c0c0d41041402d4401d50244602c40055003040101000003041c03d0321006022031a080038070794142018001c0c0c27441104003402e41d0310102d11403042040903144480603074040c071511b003000e15603841031031151601017040f00000047c0d10100b0301c00d175003040d134011018110391b80403809200d000e9442013201d19610a208070001c40c415400f000040e152130310814040c26540e03965020000d03c6141451440200b5040941c103221a0300c42e05e850400484060312102c1504460043c04c50500501e1001100101c0d40450710510074540007480c0107662100b061040007185510310102e8403100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 864490989 1250 864489739 864489767
    0xb150901080a0213021332060d050601022107060e0f07500a03080406050309010b060a0e0108090d050f0a0c080d0222060905010507050309042a 63
    0x807a5044003d4289070300d04c00c1440c18000c80c0140b500010420610868825810a0b01d4000600200758403106010800b102d03201c0000000c0c461031804000082d60600c03800c074110008944400115005034000c2208907100c081c803200c0c000c028840d04007041c9590700519810344c3c045051018820a019012542512403080c0c0005030101c903040c000440d00c0c48440860311404410210440040381e500d070301d400c0082034101c14808944e4031106494002a1340754030030700e0744203c0c085101000002c0d0280119411244075003801c1d601c07035840402d00d0b80148402452103030400c50016500f044503074000460224050240c07105811170701c44070b42c015629440030201101050040001061080c400c90103458038201c4c0d40707081040b484190741e40d00010707040345e401640400e130045490006c0c05040d000300300e00c2c1c0c1107100003d015285040c074020200892032181e41d040c440005001801d000c0180211859034801030070038403c003820f50894400000004121003150780b400c1c991542c5280c0704c2e03400140040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 864492239 1250 864490989 864490993
    0x10b0d0513080d090f05060f07110c100e0f04090803090706020f100b2d1519081e1003210f08280c020106060507020d06090215070b15090108 62
    0x70300c09043e80008204403001a200540c18240c5100011000c00500f4454044030001c40b0881c1058100a40305401c1440040c0c1a03400c403001000d950b85414000d242a024036140481a011030360002c600000e900d04080c90b0420b0810503240c0a02503040002c3d030040070400e080f40c01090b516a01282c0740d00f0781c19844951500114041c401703e030041d0b0010080c9100081c040c00c1ca0701c1120480ca0907003c140640c20000380c200c0c006004491801940b116090ba03486050280f41944042c1386031030701c0781d01e062580113200000c8041a0180ea49804894601c40c0b007504194081c00d0107401840c1d5409540720841300d8010000d001e20f0012004000c40303c00c1e65454507100c000e01241031003600d91480080154418603640154214900030796202c3d0302020061040009540f460b01a009003900d00a8000c842400300030044000161507980fa40d013021500039078001213a954520001c1c0c400203406020000b022008245003081c00212640140104c6172004d500891040401c203001c1040c0c001d1103501340c56 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 864493489 1250 864492239 864492247
    0x15010905040506030f061008060709051f050d020c030301091505030604030806030111030708091c0207120204090c0305030a03061d06090403030617030901090e0f0711010e06010b0d051308 82
    0x60501d904601d4009100070140c806030b1401c0400d16142100803284100c07500b92103030b01048a05c1051000c284c1094542c54801001c500700b43c00724400d0460780e82c115240a101480e1081024032500950b04885682001035541d50303405106a07a40341c0081c0a0980703813038900749000884030710810760758085a501401800c00fa65031503c0559480c0c00c01090107425549510f8504000600d000c021352003072020ba00c501040b401d00319022842c00595912403050441082032135040b80c0e4000810b8000c5844400c500c05c10002d09201007009440014001803507802c0b400c002008101010000d4404c0c403100780e40030403010b66544000141034010b02d4550030802107880224460381000000e01e03500a00a007004540b45030342d01500b1011407100350342c0008540021406086541e8401d03602001804c076110031098030b04019200c0d02c0c07002c1d00981680b0030b0204410341d4880300c0c402034001420081c01441500c4e003075a075410900d082580324101082c1c1e881d18060005045c0c0a8000d84802c04940084640e410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 864494739 1250 864493489 864493499
    0x6150f260a0b19150914071b081902070e1f030209070e150306030114040b0c07030c060501060203090f0924030102040504020d0f05090708120d0e030d060e150109 71
    0x1d941400b030454101d03c012041440042c5500d8002c03140c01d0103011503001051490800d0071800c450401d2a00c4040350554000d105156034004400a110308030801c1100c0f5540c0c1c1460045a140328050284d8001c0d060084400510b54010400b10200c1e62400130284955641203448080d403195180701141c214600a0203002604009680c10ba101c0c8603070402100300c044200c0040c0e8224843d9a070010b058030700104100c690309080c0151544040b100c1e84d40c0c020b40c2019034030a040043c0040812032404404102141498801d030403c1d400260016420082561150300c000e460764403000802d80100c4030945400c1d26801d043e414682707c3d00750580003001e4401410005e00d884000ea00c01554190b40030b100c00f02e145e950794801020b0560312000c0004140c0100c001000907140001c0604c41a6013142004101c55140424942040c0d51003441d61035488100c4075590005214105862445110210300380f003080d0201c3d404a025201c005c500c543c03891ba19140d944a4441481680a0024001303c01c02c00c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 864495989 1250 864494739 864494753
    0x408030711040204050315060a05150712033e04030302190303110c1e0309060d020a051207020d030f0213030303090204063f08030f0406150f260a 64
    0x2080315000308091316003660340c40041d10389000000e200d95158410003e2020078600b034248140100015100c4020f85040348407400011b00400307001500c0d4140c40c80b000c48086200f540001400c031554203201041020781c00d0341da180003580001101c1c8050305000d0300c240d40e400c50010b0b501141c1c1d0650040004014030031044408000d01d00040b0141a120304403a011402e14401901040c01000001c010f0051010813410302f003030b105902d14840d600208148541d549401c41141c1c0c1070101844050b13519144d10a046030207200c0c0040d00011130028805202035180e0100c0c484030041441c2c0e60a104c044d0b1158a00002c074468502d40c1d801c240031182003000001d0198004843c6580003d000040c026581c1414070800e111384215090b160700c1d621030780d0032005111140c0100c3d40181c200c2c60b810f0b95200741c2e2248190720002c1c1500300035424800005003004542d80100d440802094004114643e4948003407c0c980c9a074095480c03440c0300100007003030803000d000201e0303080420400100104003030394807080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 864497239 1250 864495989 864496013
    0x50709060515091207091d10060e061009050306040c03210816021204080c1203040b030c18030d030209030706211125020111030703091509050301050412080c04080307 73
    0x813200c0c090118002403610395440b46403c9040c08121f281c4000c40c0c02ca04240c1021100c000d10341c5030600e4080140440e100b080e480a41c8014182d400103c0540c0d45002640d980606900c03140d45846900100820803520343c00c08400c03203100c0c44040803034681610340313014030f02203169054000603d81400901c6030341b03201c042051958010f0050b0303441000d107405402000c1c0e105812801460f4801441c262480c100091135121840c0844081e6003401d080003148500c4c2d12019010115405004c940440540602204075000d1078005044481d401560007003e00603400a00c00075100e4004c011000903000d0140102d880103200710314107044007403180c0030401d00a00d4005484103400105000d00114031200750494075104810f403411008400c441c0c03000620a00c840040071a03240c1050001c003002a400c401202c0580d03410f0100a00514558403040700e140c41c20350b100e16031543c00c00c81444140062002c0700a07010383c42c1e560b403020301d41d14401519140d219600c00d400e4103500401c4030a011810700141c00b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 864498489 1250 864497239 864497269
    0x604080f09030a06060302091b0405040c030b120c040501050d02010804080a0309141005011d040f1e0f05010c030203040f12170906071205010602101a04020705070906051509 76
    0x25505026001c0086880d10180040448103982c0d0780000703105502c0c00000f00d40d402050101c10450f022910300c03021407140118401c850103903458a0301621880c0c065003100c1c4500401406030302c1d045000d60480340c1e54020080390980114540400070500d8140061907480003a01278491001640313855843c0740c411351201c0605020166103104640001ea179846041c45410074640040000c200030715481006c6070f0707041c3d0041c0d1040c002c0d0380e49817181c206040c641680c415000100034020660310705010b11202c3c0c4104030b80e40000f84182c2c40b601040300304001640c0450150008104071a89840207030203c4c403080c2d40140001c80ba8801c070b500096683c10a165084405140101c036400300c1c0e01031264551001e46601c98a03030032031410000065840801d00c81c01a041e0101881103501d42800a5224610040501d04203a12451003844510f00d40040995000000c3e10841daa100365041c915140d4026000e01510301e4284900000c2501c0e02d9a24818a0f00791051450b00d4092030030b040000890001e800313 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 864499739 1250 864498489 864498517
    0xa0606050a0e0603100e0f1819020d0516090903090503010c140f04030606060519020d050417120a2007050a05040518010f060611150109110f0a0c021e03060408 70
    0x1000c40d1361040648100d018110401f4801c40f1030401c3d88036500400d40d034040d26461544010445022513148076000101c154055850746030780201401d2280c2450f4070301c0000c1280b0303900d0040005d121105544802d1159000f9035602c01640c1e150000c1609172003a03c040e400008801d43c00c40c80402c0d0b1040c00030a08035000494a0780340691380d41e0351205807038143c0c1c00b6201003040459180840d405103644070090043c113201030031441c01241400b80882c0214000c614501000c4841c03264004810030034007011031100000d1580303030080040003d00d001c0e10b4150444990014041c0c001030752000191280c00e44100078100a00c040c00c2038213002c001c1500410f0701e25001e000c6c2002c1c228001c4280b0803a8001e040c841000b04a0300e04140380640f004907080c0248080e03a00200c00c7c1150248545a0241500c103c2d40b0003080580000800000764080d45074084007901c000070f40d003040c81c0c0e00074441d0341e0001e100742c0d43c80c0b0031304502c06c2c1052025400000201e405800c0003001500103200780d40188108864009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 864500989 1250 864499739 864499771
    0x605090d1a0f0a021603050c190b011502120f0706020403121205010b0703080c0703030b06041503060b0403050a0308041e060b031009050715090b070602030a0606050a0e0603 76
    0x44a8106100051600707100414103000e11080100d99406540d200e07918580540c5420459032813005181c1c40010003404200340440d45040e1100c0034003009030180b05a51041c0035810142c00d000174000028440e8980c10b03141806520034003800852010140c40b03000320360f107080200a440c8501e59034002141140e0040e401c00010001504030b540ca40c448060540da41c540010800203a6000c0f1030040e04a0765542109100ad6400240c3c440503007507110786517804640d12044a403070700350050080b10390039030f9005001250110b0310030104522040400990754040c4080c2d5540d130103044e01c83c821170001030030540040b200c102c0440c0c003510f0312607003140c81000740c10300c4801040d414a0000d201803e0032143e058960b175524945290401c0302c1d40d13402c0c19448041201102950700d05a40324106e01c90750642070080d1680e0141207000f1803c20008265031b246240c0d0b0b034483c500c0e1031002980101c5042400d0b80c9004000310303450303200351b080c0ca03011565070315100d00c0030490404010058000603c0b800d22420300c1a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 864502239 1250 864500989 864500993
    0x140f030a0305030a141302101b0602090301061517070c1101110c0a0b0403060635030706091415010b180a030515040c1238070e030c06130605090d 64
    0x4a009200d1b040032054480003408500c100200320b44011624410840003514203810488004418568158040b02c010ba42d40c240e08040390140039941d0001c9146c0242d1071006507065000300142140c02082d041002d240c2d610b03000250384a0419036009031880a0074441c0c0c05065001d54050f0f0130840c155401c690510011000203203004045801140d41024086810000c20000c0e004140103060810f22100301c0c50403603a50141c58100c9884400c9001c21040300010074004140304a48520303030018003e016021090034009030841003c02a5800e9102d142c840e9130203c162a010581170310f400020291900c000508c0c403a040c01c08180520740d00c154520000070008004100c00c044481092201100914090070b040100c480b256102001810340c085804001521004c401c0c1440131074156240107101502030891020160ba00242c00700e40301c0d03501444005604006242c652a10407411504811000c0041c08401d00800102c0c8600c3c805101d810f008d8603000310040d041c0c0c9400030303201c00c2e4006056 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 864503489 1250 864502239 864502271
    0x10906080601051003331d060d29040b070302120402090a060e0112030908070b0405060d0603150e0105010911180303120c0a080a0204080a0b04080c07080106140f030a0305030a 77
    0xc6c1e000c0c0307100d510703c6000d5400140d86c054680d00084c001c3c6010a204428000080c07912150010101407044800140c008100319070b03c122615050010080448841617440650a520409503000c1d42c60500c46d100041c1410300c280211102200b0304620b03c08075889070350a010b410103015000880b21616203501007407401480c150f040c0202030f83c03030b0100350510702820080e0030802a50000c401580020f441807216540f100215411141c05603070070b903038480342e8441c500d00500c2240c000802800c80b9251503844010941c02c102052980b080c003c00c000d03683e8820407022500065504a42102d0510491107801c00040d008182d06801406680c9066244240ca00b00400100c0384000d42c03517004078804900300ea00c034036410381c4030011901c11032400d41003070b4180755111a2624000d0104000c0320008040003004410b45134001c403484201ca03900f40e110440c0364064811402210260383c1008180400c626002039001011034000d80540700f4041c668500302e486506c020503040300c0c1c60700c2e0742003000700c0444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 864504739 1250 864503489 864503531
    0x3030e01141e090f03070f03080c03040515090102070915090e0f010212010f060c032f010606090825030f03110304270c0203030c09190303020d08010906080601051003 73
    0x10351800b0940e03500203c4100414040c8a02d1100d01940c04010f09201500301901e00030142c940000000391555200503405245204540001c0d8008102c002c0010590032804042d142000c026004d9501075615812100c0841f201c4d5400009002a42d080030048200f069005100c803142c02e04c10303180d0048805030f4107801d82e03200444d84016462164010406a01c03400c0700c400141150789082e206201c0f5a4400400c00180b400020b007008058111075800c0c8851405040c000419000003407100301d03039901e8082c041c520342d8490103109000d6103203002e652215101e0900900c0c1c2c1d5003103043d502e481c1561940540b01740b2004045040c00342b003401380000c105040010303000030424002c0030011404005180176030032016900d46044141048691081c058010090f29070112002409076101c6400d80001a800b030010703400b02408500c695808400e065001c039400102017559143d07109680d0343c1c0c404500c215903c4e8807492206410000040c40507281080c003003012030307403e40740110b402d00e20701001d4204104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 864505989 1250 864504739 864504787
    0x3011107080c0f0f0d05160c0e09100b03151e0a0c0e032a03030d0608010c0807050c06040f030e030105100305010b0f1c03030617010603030201060f03030e0114 70
    0x103008195040710700010010f02440d40400e1010b01519100350300782641d9000c0c28a400c106204020490700d45610910098a961680015520010302d588982c2e80844100995814040380540c580381125080c0d640520402d149002d4020001d000014450500b080c402814103292070301b02e102aa00500704800e02d0a02402640305d0000b040c103c1d038403000e00703c00c2c8a500594040d0b000f01c415103502c5070403c1e40e180340c03035029208124809524000020304502c148001510307007514003000810b20b0b030700550004041c40340b42d444403450f031b4031140d50941c5ca9000f42460810107a100e50006000110301c4003440c80100d06c03d04000d0150081a0002403e5070b00c1200d180c8004901c0c01c0b0200103010003405800307a03900040c1c8042c10b80045002c01f1070707000d091420800403581c012480c1d00b0100b510984c0702d100142680d04c5403040803070301e0403410b0f406804144400d40c015070800e44082040214840690120b82d0b050301ca8294504964006591001c1e40c6070503003005420038008811ba041c021a580d081d015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 864507239 1250 864505989 864506003
    0x90d050f0a5319180303050114060f030a0e19050c04060e060f041806090c170304060f0f02160801020d051803070f0501240330030b03011107 62
    0x1846281c01c078580380c80141d015642c4120b0603440910041c1e02c0e01140350000b040c0c0701208480701006038801c025090103610341c160b00c0816044ca1090582c1176104034141c50001c0700d5203d4408641c4100b10107405401d80c90041c0b50010004610444007030361281807003426240a94600c203440300c40400348404152030540b040d80102a5a40359440d0900c119006091894610003150400c0e00110b04901510341074140030b1603039144948010101101c0d108006540680180640322171f51500403c501c0d0700d84500ca4031001251000850707603401000340c0741940c6e4250b44032244d8920401c07049036031009c1221601c1c1075000d00407000701901d890b4070792800135081000c00540d450080e141400111007005217145032060845d60400300c0c0b06004011280b07115003040100051031305509086005225007060120507450500e86d00c01c0c42120503001e4000ca038010a2607400c400a41000c4041030450601502601a1206660b100042c0203511000130103001a0000610300314500f1060040d81c0600c106a47d14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 864508489 1250 864507239 864507317
    0x100e10030c021009051e07120c05030f06131e0b01080102030907081b011404080708060f0a05040c03260301090603050706050f04050105072414090d050f0a 68
    0x89804002c0e0031403901441c80200011511600d881e46c480c4004040203034131280c0c40d940c40d00507140030000c11003c6d00040c0070b1070490562529080c0c0102e10346101d1305019000702215001840000b01d511880360718403070480d00c00503429a40e0b038000c16401a0124001814400a10300032500c009080d501074a4090001039480c1020260945000da0790fa01049032075104160650f1020045526039011081c00c1c203200f2304a1490340c3c8a0303891801190011000d5104800c00016240030008034a8054034200c140c01650b03403030311002c800c02d684084401400700389803410f0070030008000060301c07141807140f86814100c0410a2041c01d1080d030084c1c1c4a4010340d0745500080c4207004061028800502550500c00e18045443c44030312001e0180f84182414020302003800303814010001a0301c44003400d040d2081c904891410407901c003d124140381c030662100c003130b00042c0080600098612502d05c0546883e803c0c0304000c03405410715441038600c402000303001c51050f028180922007030780b001e2008035441000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 864509739 1250 864508489 864508511
    0xc1202060706140108061302030a080c1c090612020f1605031606090c080d1b0203120f1e0301060e04090606120804030318050108010302210d17060f0f100e1003 70
    0x14099001c2c000d4010505601c1e8881d00503278001400e1071000e50300c04840f54072103108800712401c0c40040c1d43d003d0b41c928100d1850502041d4030402d9003046d9440c90300e03442411001690b280e001c07401008603840182d0420003500428420000d540a403ea00c03a0080320b2411100035800f43d0000e45807442140d066445580c4442000048481040038140101c02440a407071300c1b01008100c4800a00750582c0c1a00300000602075417002d00c40700c4000e2001031a0690f50388040b51094180790b018007100a01185c1001d50f400355000c81c102124100d07421583d03100845601030702007100804400c4011100c1591b038450000c0d501d8211011980198001c0141c2610750340341d4280901550803024201c0114180107034240401c0c0cbe0080142e0741900d8041d17840101d0711405440000c0407603294142c108980c4540f040e1040d034680d0200045820b000101c102e00c1e801e0300c0308002c0c80f005411110299501910030901c0d1695401c14500c95089400d0500e850f18004010300082031024a04c9814000069202c84c07588107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 864510989 1250 864509739 864509743
    0x1906140306090c1815030a08090108152d04090803040210030b03340b0301090b010305060603040305070821040c060f080601030f0f0501080d021204030c1202060706140108 75
    0x40c0c0802c01070302070201c4280c0b0000107025000514009071038208103001203911490484101c00c4403010280c1164120303002c60805501c5500b002c0700407400144110005903400d52100b059804284c0d029003600030f003150210b001740e4001003880d12100c486590b1648848240c0e039031701403aa002c40c0642e0040d503403030600b40103000ba0140d10a00d0603050600700141c0d040e0356140002c220340b1071001f03901906107802054a80540c0100010801a506500e15078013049010184000398102c6800400412441d500c00c4010340c1070319004c4584540c4850144001800300e8014030051200900c90b500080ca4500c040f034030f400c444041508010f001d5203464040004020707045030741030058261820300380030300180444d00901c0d450008141a04054480c4605484100b05810030b010380030790014103202d15a1210031541c0c2d1160035182c10b1005200c0c08441104008481013114203481d0032841280c1c11f40c1c103011103e5a0612034020803a0804420807600c0041a900d00c2041141c60090b065240e040d4504643c8074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 864512239 1250 864510989 864510991
    0xe040908070303200a080402060706090318080a030905040e0c1017060d0206090f0609100507061b0c060213090501030809031b01200f1917030118051906140306 70
    0x14404448464411990000e00800d0750030003400c606d401015681d61b8408902d00e4050369600412141c284201d010805d6041103900e900c24800680c1001120b0340c0b82c0303015690f01104640507001c02c02101c01800170341410340084250080b028110340c1d0540392100400d04502d0441040030015203900030754030880886d403c0c141d8201108548641c40041c00350002851031140d01103440c442d00d0b00402130380f6652180c005503803002500900c154400080c000c00540503a0049004407503480c074040941c210f280404805000752440741c0e41c1d4000c9000b044c0d07140030080d8000d41444911600303007200000e0464007401b400307000e944a454541d03103903010710f001d01d4640003100700a400700341441e0409104c1660712204a00c0c0c0038000460b10b9824598620140d41400d600b10103124190154505040100d90f414000382180740c89041e000b40c0105220010400d10f000178003038490401c00300794102003981083e070417107600050030060100c098403240280c84210b8040f64820100c69200003588540351030140525 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 864513489 1250 864512239 864512261
    0xb010201020405100f0306050916030509061006050a020a05070f05040c0305072a08190f0305070e1512040c0602071e0b1e0a080f13020d0308070e040908070303 70
    0x25030070030b0f0520000442c103400e844c1c506810024002c61030084603201e508400b00500000c3c00b940d0050805003400c04484080542e281c0101e0704007404540b01000000e0311500c02d6804e4035040b004542010011260796101d18001021841110144000308409001403030052410101700d65006103090f00740300650b00c40b05115030a00d03113040208945a40c218500c03404013080c4c22040500c02541140d030708585000c07000081d11103a4089441142d1468546004890111a0b2a0406248000c5104900b60343c4110744074400aa00844046514141003441c00700156841c2ea03050704080750b2054140c4800811a016a018001014100b06054042c8030f00f00203048070b504038900d40250824100c3c1259054818102c02d1080045c440c0c041c00c440418560100381c4112010390360700001480100441030650f484c8003041c5528003c51012081c5a0b004e002040d07014003510700712003080d01c081d58140401084502400a011304000d0780f41d550344500864144a10441e03910f442d060308004044a00103824 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 864514739 1250 864513489 864513491
    0x90c130c020627030426070f0501201b0108010f0503071406120a02030103052b0f02010b151b0a0807200a180516200a0210080a0b010201 60
    0x344940e90101e21594412020000c0d11901408014610b000048039000040c20f808040b5000c0344401c0c051003140d5800e41e04804100081c014014801d45910451103124040300e81d4440800180d4041d00c05c0d48a40044e00e0840e0f9641204034080030708240d0412030150640c42c001e80312a44541e00080d001c0c0c090720303e10000f00c11413821703c40400c1d40c4880314000d900c21171102405c03451040d510801159241440116002042c0c242015410041d40080c0022100c5010f6240a506505141c56a011024080c000c12a14101c041c50090b101c0a50f48040e6000f1035403a030102c0402501c582040e445425003944009607a2181c60b0000c080000d0402201d41c55500301c3c5c0103041c049009401510706c01c40d084254181101c100503050752202c3d01c105d0400360043c804202c0069030000f00243c141d2004410003060100384c1c0c88460102001c8130f000e4408010501006030000b03004240d40e2594607800c2000201c4030040030640000740c0c05288403480c100001c04c5401008441d201d94091006009403c0c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 864515989 1250 864514739 864514751
    0x19021516031e0207050d02060c01110a020f0a020109180605150913090503030f090c091608060a210f0204050f160e010c082d130e0f01060305041406090c13 68
    0x79100c01d4203100d8175129801c0c0210000540d03031a002103a4910380054000c110362030701703076040b01d1654002d0601000503003d902c512066003900400d40c40500c40d8165201030341c05003001071200041500d00d007916403031a0303140307408070311902d4101030707a850001c1c50303d20241c540803040d00300034000644030401460581880010340c0010000410369401c80b450300600000f80c1d84217413442d85044181b42d81c240d4050584014400000c250300400420301d85155076582c5640d603018280940e401c900d118111684c145088910600070791310134951060351154265106010040d00060b05445050303031200c064014810500c504054041101d01c601c6a59003020a0741e0880f0328000783c007440c49110040c020321800202d0600d01aa2102140d02c07150580460302511005ca0408a20340d81001c03c90280807100090046103002204910a12400c40c040d9069401c1e070801034110083c14001d40700321011601c1500481031a44248003c40c400e240b40d800134042c1587c50803c003c4910180c00082054929000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 864517239 1250 864515989 864516047
    0x8120a290d030509030a06050c0301061106250311030f102304020306120d020a0c140a18090807050607120207030c12120204030602090907111902151603 67
    0x207240086101c1d01400c0642e11941c1d0760f00460709140610328001d00d410b2501c0100300440c90043c0245040c0d4400d50b4a42204402100403559540f1040d50200b00101c003240c500d18164101076006000c0d9031140c90040380990b08041d00d20025081600c10740c103010503072010030074001c003c0d03549000100300d00c1544905a03421000044111211055410b00844d000000222151110074800b016070081b5021240004c10884000b9141d0760003200c103c030260002d5400003900c038080c0c000001d40d11001081885400c1c640499606005211103494071001c1d04c0707040744000b0458100250240c0d50140014044624000400a100070154000122050310500c44070300420b81c0a20601c2076140d00c0500003081080403441601c144007400901c40b1298000940803040010f6500500100001070300d4100440d02ca024080d104903083d0003000716907902c02c800f211003500820105199043c009010526240c030154000d420030351004440c0c0c00450354240c0144d00705540042c00c44403e00c4a580c1c580c684500503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 864518489 1250 864517239 864517249
    0x60411161a040b2a0301121b080d030e100c0513081203180703060509010903080c0a020a1704030606030b22112115010312030e061308120a29 62
    0x40c02d1090344a0360310200141c80c5401d0607180c81e51a10800030350b6120342e5100d420391025144503030102d6501611101d81048844040b03108022760710408046e02111101c0c1c0f8080307000300514004415130f44503150801c00c1c000c0051007149880d044558446540f41070282c0c02410012740da60103520726900040c601d0307200000007400d03070350402203108414000d601c030780c4d203000e00c1c1c00070680010f4005850a014800c0c1014154840409107120b52911030035035031540307250362407401100440070258004440ca4000140740500105241c10700d9403800d41401c0d00c80c0c03900300c01c582c6030303420495440c0750040c01d102d8040741804c940b0104d014a0bc0d082017001600340c4c5c0e400e10750914035000c14083e400000d44452040c0d003002c003a034001c08081d001c0340d4007640700011f20341d400f010a01c002d4508842c074a90344034160340b2034000d1a602c145000000c01c015100d250412042c80c0301c042003601c03102814410169000c2d01c030014035005681c0400045800041d59040600300c4160079041000800d580114000d15151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 864519739 1250 864518489 864518491
    0xe24090303121017120a0e0118090e0d020303190c230a0e0f011205090307022206060807050304020f0a030b09011b03020a0c020d0804030b090a0308101d060411161a040b 74
    0x31519100b503d010500c3e0040c9e803d049096171401c510120b07040d000c902d490143d0302c00e9511340d0030007048440e10440000c1c05d03601e900c01941d01000036108140004c4490840d80c1060880c040301d4035000280c41086148488a0072008006985030b040014442900c3d90b80a81100c004110031100e4004601a1000180500c1c03082e844241d030041d102e00c0000c0078000103005840341c00341c0141403c01c00318103a800000c00681c0b005481e40d00301c1d04d092000b06a0b03901c04c1c4400352281c4035035110145113444540070042200c9410007140d9100b2490f1801200041c121403104d40500c0d05040080780000b030b41c0300700310b008228441c4428101841030051150007644544032003146601500c000b0030012032414070349480e10a80d000680128007500500c050f6140004000e401c150282d5143c010f1070310b6030150146010890301c2000060b03444141203003032400032a070000d50019801040001d4403480042d10300e8490304002d00380568540704a14202c1401303c240400c2d6804c8010a40c641150302e0b00e030b6191103200e10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 864520989 1250 864519739 864519757
    0x60601180819021003110d090606170a0302010b060a051206030a061d0d080f07030506010309021c0b18031207020a08040f03030e2409030312101712 65
    0x84000002031589104091420180c070300c034416100d00c21021018291500103a4404034004c0c807040e4621603150f4481d200e0345080c100d0400c03826281c00304d441c00d030740058940380744195041541e8210000e80d10720031300441c2c0000c3c050350000c4c0545140506001e800c403000217941c580212420842100c24a6100c01200c50304150704194030031075101c1101082c50040d401c10000e003018a4060034442c0041088081154203181c042215400700c0d00c1002100d040409139141c1044a070700c0008204c0300341c02600060307880501031400103841d0701c1a40001d034403903e540340d0034000f1507090002942400000091103a1000f80407410600640140c0c2c2800c1d86c03440f40c0100045c2c6032103c00c0110320490300c00d00078007450b1900444540c0c2c4071501c0c1c105400d20380d8000c1c8022400b003541103c500d406c90030501101c691001c1d0144041250640e000002d16403a40300114540c3d150004202949140d040890341074003406840010140e224288107403032411500c40d01d4a80e02da980580007100745c8150031011580492 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 864522239 1250 864520989 864520997
    0x109020f01030e0f070f0810110702040f02360409050c1203040b07030801090f0903020d05030703090501020403051b010810051003060305010e0d090b04140616051b030106090e060601 80
    0x3c0310440900305080301c0c820244030301940d480002c0024440030004143d0300700005441c104024507950008546008000c42000e010610441c409490158405000c0040201025241c81041c4040d00c10f5442c3c600ca2281c9804108110701c0c01700c402d04000312165540c20349040110105644580380e81c1d00c40c402c01c240c40380b042031050540301e14040c81035800404916403901e840d0751242c94054080c4c40240590f455480c60b2800c2c1d00c40402560080c048055050340207010600e0541004032480c3d40007c04220134140c403440c0482c00030b10309200500095010384058281c0411506841540701c40c02c05515040020981c144071a88410b8045401110b1040b54095a0600b4420b401c0d00034103029480a08154a02005a401c80310040b4500e40e940040340d0f40d050525032946410740c0e09019030b004110300005610301a00050500380002c00ea03c440b120742912012400c0e80d10240f500c2c0e058a40c61510311203660700342406060074094070018014a1800303000c951032510000e5900c20004040324104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 864523489 1250 864522239 864522251
    0xc080c0901030b030312070e01051c052a091008160e041409010902010809061005150409060803040e100338072118150b09040b0906090109020f0103 65
    0xe0b03000358001c0002420107015207032542490581c0021070f200c200c0c2c402002c21a240808151907100c0c1c0d04441980b60449040406075181c0305e004002884000c044030580c03480c2145102440344045241410007003049034041d510a47d010620031a689401190b401b400284410f000b61700da14082070f0f1000c01c090740303010070240003071000050242440d0f01000c11a403120b201402031004040d0030911341d50307000f0380300c40c0800d1700c50690300340d900c0504503403900c8001c11640c001d01040c40c28206551001003a001181d040a460703e16110848205031701452256100150401c80410b0259420364000c15512086445900e548c482c03005880107a00c40c0c0d003441c500300310002c0c5041180c000700d0440e24070503101240c00d0701d0700b0200a0000103a80c10060103e486000c09070704040c52a0090700103183c8969080b0341c45421035522540341d42100420380102c039803560350f039000a8441c0c0d02e60724460b6010341c6045c5424100100400c0c00d144024007400b01c280d05200405015171140f1000314801070b400c0ca000070365 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 864524739 1250 864523489 864523507
    0xb0910050a020102220501024305041b140a08040f150507110c060c1504020d050d0504030201030e1606140d110a0f0206100b1e0d1401090c080c 63
    0x921030304540c5c02d4201a0782808004140071054128255082a021240c0c5c001400510315221084040201a40c6030356410420314004d078144d00301c00c80c0030b03000c07800e600660b246c900013002d940d4121040d100010100d8641d078126a170200001412001588409103846a440c000600b1740304000c0014002030601d00205041240c0e002c0c11480b4100c0b6642c1c104450b08100c0d2009051481c2c4035040d05a41c803900340c16500600d00300040300d00c245070703440090180b191002a00001854010300a990000f0a1200100820b00c10700c0304443c244800c0d80d41950f903604510000d01281d101030000c20040c3d1203186102000320340c040d05142551418245441d039a126000f10650601c100400c1180701c03410019202d02c00040c800140c41c044138282c840074011154594126034983d0126160f080003107054500300200c0030010010481d107038a046000a901150f00c00c252243e80c00070912403500b940d5005105101582c0c88807040c050084008180484410000001c0c004c040180c4419070078600042d01401e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 864525989 1250 864524739 864524741
    0xc0c051f200d0209150712020105010504110301030213140411130c2102040f060801030b0c0a08040803070c06050f07030516020d1101090501091b0503060c120406060b0d0c03060b0910050a0201 84
    0x10710070100781c40d00381d0b0395600740b911400c50411f4a41001c0550300304000403a030351074a03000e10750626500404039401c5070300c0e40c0c0070006c0030f12516035401e40c640d6441101d000020341c01000540b0030340c010007084810407414002d01012210070513200200307515145101404a9008040c24200d42c2c02c4c0c80b19008203a03001e00c50340300a100300e5002000300d43d141140003800b9500b09103014122406000d40e036a0320b50303411401061500c190940400051100340028001802500243d504030078145011b07100508241e8400d0111002510341c204d000c10310004100c501507142c06500d500480c0e03603030b08280d034009401000e5a2003402c1004441403080c1880c0280098400354403800149801000034040009241001c1d0140b5140d594240c0c14201c80400210313007814009641030048440c0084036140c02222018440c5910000e002122015210400000c403040a0406090809100310f40000c060701030600280845003d91b0181c5c0c002401400f0441140e6200224541c100e002ca0902d1640c1d070711900d00484c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 864527239 1250 864525989 864526009
    0xb011b03020f250909030c081804111b1b0f0301021c23060306040f060e06091b0f06070b1f03061d03070b04060c0c051f200d0209 57
    0x2414401c2114803e54401007001003801c85030008802080f25031114890300a40c0c0d010403001d004a1124401400080d4218000301604014115010500c451000008003503440c440f02040301c40c407002c0f0b8690111949941c454120020302802401142451303400c44401903049d01e0050b10500034245203400a440a404842071054800d100c1c130140f40210400b13030000c12008042c1140d145100203541c1840d9194031159000368401401051561341d00c0e030f203403100002442d030201c0d407480d00ca842e020458402000b0740c074090210707000584149501111520400116804100d101700802d56060043d40c031170b4000c542c0c1c810b030810a07006d903982e40c880700860080303640c00084511780c540310400028001194401111452005148070741c0381100301c00b180d604e0080b4100500022500004100010b10650100300305100500304001010490745440307050190000301c504108240c0c0d06c070808050b065114610740d0144844e4005a0f00840c500c440341c840c0108040c1e120940e50000e4070200507615801c0340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 864528489 1250 864527239 864527263
    0x1606053408070501270b011a04123c08090109080601080307031205190c020f1f050601020607020d08070c08070501020c06070914010e1917060a0b011b0302 68
    0x380d40c62040e46030071802080c8140c007414903411028103185402000032421200c0036001030040742d02e03900b031608c450400d400300078000c8179000c410000041c10306140d1040c0c80c056030140c0c80c00e45800f5252400000d040b511b00300003601d81801c1a400c0200e0040b25034161200c01d4000c001252580000310050f035100110350480703c428480d00b800010070f0380b0000010800300d4401c1d610514401d07030299200041d940c058802d40c180721140004902d21541c0b5500001200103030b44129882c2c59080304102d4102010b200c04070b07504003a03480364520342281a0090b035420903420300c0201414503203050003d4844210484a034108400b04020031996482002100d50460b0459009541d5010070701e40726000b0340c4000340701c40443c0101e0340094002030240b00d49800f2190f084241460030500b803401114400440c004c070300c0c1c1c0070307544042e000103604080130601c001d0f008800c51001441c2c0035010031071411030004c0000035003500303050070144242d074421060840a214001841c09005191a050341403411034405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 864529739 1250 864528489 864528503
    0x307060212220308031e060a0b13030606060c020102120c070b03100911070b07020a0c0b21040302010b0a0e010b0d092402041505090a1707080102040816060534 70
    0x110134440004000c601803245002000900002c1c040c02044940c0101e450590103038100501308030b004927030380c018041e01c0a00c0c091a00b007030b5126590041201c80d41d400c07030340020305044130304011548c041149642000105da041800c4c11000c2280d0317580c590490181d11b1f070401c07000c0701141c00c84031b5010818024000b8a0011b00c140b80c9003a0010400d60400301080e15661107843c0400d110314004540c0c0c141282e0440110603900703041018500041d84504100c014020403ca90849030380d030310414a9020303622903800407590305108820080740da1581e4100c401c150300c00c44010040180c26404482c000650502c000c510241c040c1440c100f60441481c4d081000d1005101540d0800144ea0003003050b1040561300d00000508400100d07007902410710382c25000a8000400d1011813150b00f5040f01d150161821140c030301d41c44004085c20380e04a5401001540e12040001252900d40c140c036002130005440e01c1c50401c06848000004d40304810040d80b19040c4108998420301840c82d076003005281c101d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 864530989 1250 864529739 864529807
    0x1b060a1e020d08011715060a0e09102003010521010513020406080304030201170a061703030906010506090d02040915320f1605040906150e0307060212 66
    0x54041c0d107503590114102c00042c0010004544001104c1100c114907510800400303803400d4120140c0ca1204000d440654082e20003c0002010754141d1600d521481c1c0c520090200005150041070941c1c0036105a40c00794100d0744031a00100e450710f015030f03046600440b01c0418851400040302015030b0414603508265007071404000c1071088a000ea010420310a46040010030364a50fa2141c4900407400002d001400d020004d0905908800041c0d8003c240e001c2c00103142a681c5288500740e2030440b03541c0b80c0a8102108208459200740030090041105581141c5400c2c60000001d85012050000900c00c81c1e8444c800c0c030901c4130144200c00000720700c0000300450381025048000074841603103500341c1183c158001250141c040044c880c0aa225044001c55540300c110a0f83c4800c010a0300140400500380030008840309035000303403402848101c030b031400d0803003405000070240042c9a071158040d50005004004c09580042c892414003030450010b521404800101040e6485100c42410810f80241d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 864532239 1250 864530989 864531047
    0x3021216060203012306031b180306070c06230703150801050c0d0e0309011b080903030706020a031404030f2007170610270b180709081b060a 62
    0xc0e214071520341c0c5c601034142030151681003081e14882102e03d03449050302078022502c03a40f061000350412145030680c0c00c042e0000240401e24100080f5071640001780482c01402c00e01c60948250459004610103250a51802004945d02410f025101c00d040541c0c3c1e111850400a0b041001c6001e407910340700034005414414240c3c6100d40085a6115a80f80b501541041a610001c1220418001a140c82c5000688408545050700c6070001c1a90440030420000701560340a0000307000d414820302c4016211041580010100c031035116045201065040034400030030781002e0324004200a47c5050001103540c9040603c203d002040c00c0c24003481489070110380075210303e07038820840008004482d01d660b520300d820b00700f802851160403600b1181d0409010340b1144540e0f0102034940000e404110301d03007a24046030604225007800301781140d00c0b00030b00c018198004804070040200f03e00410440c1d1024041030010201030700f034207110700030001c0d0b02442c103030096500d282180382349141030100c01480 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 864533489 1250 864532239 864532259
    0x1002160e0711150403032706060e070c03020c04150b0d0c030e0d1205060a21050d180e13050d050309120a02100c12020c07150201090302121606020301 66
    0x950307021000c5862101c00194240e800a50b103444490343c0f007048030464440d40c42c00e40081040070840210f02103500303000c00c010301c0754207468400c00744107a0000500511306400382494030000741511040000c000160b01c003280e4000303420b0340348140403100003400c042c040200d08070040940d488030140d1007000c82d42c0c2c1c0015100c2c2d400104000c09070f440c14041038a041407a20b4440004c1a0b1140c00703d12812207011001001d60b020710b51050014107481c61040c0c43e0300028000c262002d0740d00c0040000042c082c1c040041c240060ba05041c0a07007001c80c040f14605d81346000d400e100d0300031841050484d1b00000d402842c1001400b2640d60080f0585501211071540284913a004440c3e190b50f9205444020b11400409821101e01060550282c0541007400c0c2540000c4c10383c0c107489000308610590f0201c0001c1051000300600751442d402001d18526100141c1d4844503000304100c2035903d0019402c01003074003c10081e2114810160740382d6501903154003d1490001e081e0050071a03840440049214449 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 864534739 1250 864533489 864533491
    0x18040b040c0507120809060103030c0809060313060b040b0109030b040f0b0f010e0606091f090b1605060105151c020d0203011d0610021f0906090309171207021002160e 73
    0x69451485094951a0103171100b18090b9074a400c150710510041001c40d2042c3d4180120364401d106076031914619030000385c101d400c280c03103005225810140e1582000381074031030a20400000d80d01801102d0491300080c041d0102840040c05c502e4050f0001800c0210800f0b020300d02551040c021941c0303040a101882d030342e120900803103201c404002c010800d6494880d05840f14514003c04d1620501e50780740307014541e2240c4001c200d06102101d00e011841c281510041c02d0354015800380c1344010082810001d10308003060384000d0142c4400c2c40890004034000c001c03651039014003000c102c0400d100c612160000e1003112444d262045c4040000315440000003084010b13656180f03003684207a150001044072115000c5240005030b4080c0308201000e070324011456105c0c0302421b20010740701a1948854003694802d41c0c08600044003101c062098038900410040c20120200041160469003410300040d41b007140c0c00070748200d1352200d60143c2c281c420404a440d51000591285100341e880c0104140100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 864535989 1250 864534739 864534743
    0x60203060a0905010506070f06150b0c0d0305090a0803061801030b270d1b060509070509070c0b0606180d0501050411030325020619110c09010b18040b040c0507 70
    0x1568840001d001c0040f405141e041e904010081031030300c039030303503565003c1403c20310070454690703468268820032459030402c0107006055843d0380319034400603402e11a0038101c441400ca0306041c503000034401e0310000002c14031941075200200507565151840007407004e603810401d540c00845a0400402001003601105024440710b0307000e01488610b1b40e252221300044921b40e10103e50201d10510f0340c5600c984141d161101c0682950b0070550016100c3c00c060b1401200d00844692080c80100a2400c3c00d0707902907440306140c03801d2100c0102ca642c070b50180d060080c0c80d00d441408040b50b0702200c00780300d120110225000911055021301245800ca002e4035084800359602c140420065082d4240401165803405911005001e00a92541006200d41e0307002816a044807007031205040a4100704501c111818140d01c40706480307000a01003d01d01911098801c0c0651001c0b0700401c034414040055442584e00b516040101d0071503140030800400f5885029a0f12034103240951307900540040c01001c03064 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 864537239 1250 864535989 864535999
    0x201020a09050d0201080402090601050415031b14040311010e1c02041109100804080706020703090305060105031209040b012102180a1401050703090e010605030a0c1403011401050f0706020306 84
    0x242e45000b04540e12445074000707400b003402c40000500616003460300baa0302c148141031580c00c080e1142d040c148540545000b000101e40e880c502c07075242842c03100060190390344c2c511b402c19915040c80322180480c0224030001384081d5010f240341c80c15a0040325a80d00c0000c024003884051a00b5542e2040020000e82c3c0590040303182c00503010f07450100d482200d40c00b0342d0150041d01d10603e82c11046071580b4000b070080c0d4455a0034010340b000944540000e00d4994000e0759000c0b491030030360030031604000b8181d200900c01da014005145a0614034001d030b88030a1822680043d09007a5080181d50b650500c4403a045242c0000c1c0045d880b60003d0b40c06080c0c600c1000110805a60940d400e100c0409441e00541240c4a16590200c0c03507584100000c01070707a4803a141401540c2c1c0e4480d0b00c520040c1084e003202c80455801301c01c102080c1038501c0303003460002040c036040842a0340c2d1405c8903c1c92106000309610302c0e0202100d030000380d00583c100c03464007099029450340c40025042404c0250001c0d035a80f4802c1e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 864538489 1250 864537239 864537257
    0xc100507060509010614010f032007030f02150103030305091c020102040612061a071e0501201602091f0e09070f060f0302090a0509041505090d0c06050702010209030307030201020a 79
    0x883d0144200400c1e5070134810b08400c81c0660200541d201c00e43c10500b18105034039045180e140b042294480d002e8008096149500c0d801c0910300682139a80c000050011580070340b502c0e44005d0304030030640707046036050306001074140c035039540031401d018608001c011080c800c42c05d5422129030540c010004c881443d40c9030b10080c4071781c001c030505403450392180c5a8407140015010080c1c400780c074020410a88502d4400d160302d20002e41c03400010000b401d0960751740c0d542c1c40c1d2644041030568152440c06041c00c4006151201c1c0040108590b07a5203140a4051030440000502d4a030481c0c4020402c41c4020050701007031507952075403003207034101100c1002e518044d20300d000544480f001d0080060f900c1546802c0e840c2c0380642c03400c40003500a941c8040d402805180001103d88801c1c003c14050340c0101d42400403c0c00c800481019280040e00b2140594442e0481c010200d03400207403c11190351204000c0740503140e04408a019020f044c41080d458000041c401c41010b40550003400b8100a9850301750308 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 864539739 1250 864538489 864538501
    0x5041e061208071509020d03030204050a12021c050f010612050d0306081507051e28091a0c012406020c0108042303040b04031b03030c140c1005070605 66
    0x21552440c1c00c010288202409018001400f40e00201e90108004000040514441d00000c0100710b844c0400e401082d80094184040d00b003208026010382600801400c151800c0e50119060300c9603001c079000c5521041c440e10742005002c2c03202810b0009800b00a00104c0e840c0d104c20b01403d10440022106840350754181c9003030500a028080464000701c000e0000c102084c488406d5002c0d00519070010030008102090050785043d4070b96032458141102c064603030304000386010300c80740c00d00d44080a012201c000601e1066024040409488080240f9081c691246800d01c2590141101c40c5041e9401d006d000c1c0403121904d034040e80c0000c03c0801d8110401c1d070311401030f40c03500d510302100750000d0b124400003000308a40110540d134925000e41a121052103400007142075400c00c0d007000c010a88001000c105010345c0481c0061a4002c07510003140081c41c5036405483c004440c9002080d03241080d4001c241c1080038030202c98140006001888868035010009003254032110046580c58076003000b00d41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 864540989 1250 864539739 864539759
    0xd0f110a020715080601080415020304030f1209320a050c1c0b1605370e030a0308100b041e090902241b0c011106040f080a030605041e06 60
    0x7143c0c90070343c80e503074665100c0200460b03d5180040044c0d03000c884004800128a442d84001d51280d80240e951441c0e84490810050098510200901005007403040f01ca020804000040c25001200503c8106040c01c140e500d142c00950b41d482010b4038080c8009250034020b006c281d80803240300c00c03500000c04101c141c82c2c0e2001c002d0420409480840c40c0000510f51503102d00c080b000ba000d041c1001400d2004001020f024000106815022510b07010740851030b0910084600803c0d81c085d0030010300f408014808240c1c1e540d180c090181c108084480840c00c20b07040020400043d00407900c0c02c0b99200c2d120304495408158002800c2803205888500195410a81c4035098540b80d000345614446981c4c0c40c1811995411070102e5021082c1c1088210b89183d00b0b452403400040030403020b425821030110004d440e03804500c081056a07040a000c000004611001c0000c41c40e511407105603c40d1507082c0c08400514060b040ce0390098603050400100700c956452101102c114140288400703922000ca41c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 864542239 1250 864540989 864541019
    0x100c03111201060e0d20010c1e031209051b1f030c090515030f07030b0a080703060c020316080d14010303031b0e06070b0604090b07080109060f030c0501050d0f110a0207 74
    0x85c051101d00c0048040305103c5001c0d40018840514011103c442d1988502da00103200401700c4027a25985240c83e01010b07000410400c8080f0100f10400191181d83c54103a160700140c0391021000b803c16049140c0e50340c401a03101411081c800d14182ea48101000c05402010a03181400101e90804400100307450240002c41d5030144c141800b506680f110345c5003808901c40503090400781502c440120506407901c0c203000c0e0080040310014107040b403450134044100da104011205c01c41d00704100c41c0c1c003c41013285441400d241d000021950345d0498020800003002d1001e2100b0700d8108000000082c10782c19007012008004800311140d480c9007101041d61901c040c162010340242c002d002150100d42c001d481c1a82c0620b0180012503210840d84d40d4845220084541d440400c00c0759006000b80380384c4d481880060482c2c110003030346d08d500315240c0c071201c00e0544c8185030401c280007070034040340d02043d0400552008108410300407000001e4044000f9041a099880140300380ea0000600760200c28903d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 864543489 1250 864542239 864542243
    0x309031216050a050a0e04050a240f060c15050708061207030c2d080607020d03061202220e030901020f0102040e010e1b070b04021e03100c03111201060e0d 68
    0x1468240f40e242c0c103403100e400c865009030600914122030700c80c80e101d030700480b481901098000100c500d00884040741e00075520700c4100c10102e04040c1400000c0101102d80184e0b545802c00e05031000051402544a0f2030700c10703080c181c941c1450180314a10350410038041c01070b14201c0f074916566540c005c00d595240824070025214107001c16003008522841d061100701180b0812605040614a950800c00c0c1c0d40d03580c4c450001e039440030040008040e07050180300700024441ca814007400307161034548032070b104103450702920030303441c3c8403201c07444c0c01c42c201200840b07a610b0082070010f4400889101c0d2281c0103881c0369409401a82c0222041c000d0601c00c445c00c1c0c50b085001524141d0904540b40240304000782428011885030272901160441d503805020b6a03480350519110625162040c44940400f01c1c08009400e0616a0220503d590100740141030a00d241c0000130040b0349403c0031070190480c001c5030240704000149401840c201d03110100e0503100c01d43c44072242c598030764090055400c562400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 864544739 1250 864543489 864543497
    0x90f0a0309140d0309051020070f0506040e0105041a04140907320d050a11190303020a350c1902031002070204060509010e04020909010e0a0b1306020309031216 70
    0x181b01a19100040002040961030260120f65141300c288a40c403c48034241425503010311003c00640d404401500301600d02035a000b03003428641201c0440e420f406005003032066403100d2629810050b0500c1061003c540240184520b141c84d4040b00344040342920b241909014242001c07a41c0024100d0140790800110308101064602c040b280407000c03050303032485a100c078042009801040e82082007003000d5001c2c05d12007404039940b03400c0010384440c00300301036100b040c80c0004201080d00840c1c4440b5490b00166540001c0c1c0c6861005070040d181c903040503042d981c05003135190160003688040c00c4141000c0040f40e41140303100400e1f60600008800c020362550010030f03d0060201c254000e0459248064004604c613038950000a490b06802d03003120460700444000c200942c901100001d41200707005000300002c208a90500752500d55001010b8440341c0300c58081021200d24000d24030005800c524215182d09007039032059280e070f00020140b410303508240040780301400b880071007205110241e1030f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 864545989 1250 864544739 864544757
    0x10b10080406150e07030b0312070f11060d0221010f060f0203040504051501020d03140115020c0411040e0c030606030115110f0601051806030a0803090f0a0309140d03 73
    0x40880300c9610007401100d54907182c40024100c60307010100c40d8040d10008600d4005803a02020040c1103d44034030b203181c400e45c4081c00c1d03c00840341d04c0d022140010307000418184144410700700711031b44000c600c0151b07421440004108402c5080c541c00b811304000c50300c0c7ca405c0c610411818910548200380a0310f00d40a2103004100000e90140fa403200311480e903070041d04d041c9030f80c400001d011a1710441e459106480710710708005042da4140035000080489003400c11405140324001c4038500014020001034480055140f01c0c0140208000400071100038414480d2090720b0203070716a079402906c0b40b100d070040f514001c906078801d0441681e1180802400e5203007141e29100c9464003406060490005000c0b028046d00000e404c10720524a9404042d001003501c0d524010901c0340304985565510035600154050042c1a580800c0f00741c04584c022100a40365156192b01505044484140b14224840c80314031a0416030005100d8040b64000b2070480e07034194900003400254002d6100080002d030b5401c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 864547239 1250 864545989 864546019
    0x304090f1b0e03330708160e06040308040b04030c060813020d060e031902120903150726071b0f0204050c09060d02041503140c0a03090c120b0702010b 66
    0x450155042c000040450b01c000480c0f6005003002d411424100390031401507a841c1d015a0100c106594101e140f034a01130501d031500d00903488840d103d5080300070801a424129024507654001502e001d107402088081e519a0f680342c080619030300601c0110f822040551000400381d0044074118803c140410700500041079643c02c1040304c06108000300c540d9942da2041c8500b0b80c500704040e001c0310703c0c4d500f100b5241d80c0c54400c010b0f20742241c44002c0c0c00695410170202e2035544000c41d00303100c1460007400b40046500d941c1e0b810345110349603a4030f0031020050000001c0c0058200780123140203020985501c0002010740e8020140720002c400041c01181e00041408014100b550215031300c0f179000038040b4209a6481e00295060f402070820080d41e07900400e05000781100500c0d601c045040508082029041428004490f044002d05580244601149940c81d00d8040e40005500551007161044065151000c84001c030101c81c1e001e031b511104035800211414014131984403c00c0e40281105004002e117 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 864548489 1250 864547239 864547247
    0x901120501060306020f0a0206060301201c1506080105010f200f100902032b121104030c030302060a1a0d110301060f050913030807081e090304090f1b 66
    0x20000449481d03603503020000c0407a0041c40608400502109107950b0384890600007860000301401007446039151401e01e00c008084000107403411038601100035101c500b01e10a14560094009500008034240304442c42650140c9003004103650158403000e1003640c861004407240400b00d20f203c8003284500c0e05250b0014400c0c0081480c1c0c04050003154514082c5402c014105651080c21082658039170b1008821441e00b07112021103041c100c00304800d2042020780b000c00c0a04009540800e11040420502520b0300716004031840c440c00c1300381e80d85c1d0b4655915040034565a2440150014010b01d804210050305500440b090818612002c0305d842d8004010400e026901000807900784400d1000c2e0344e1117440078010b0781c0080000c3d800210340507140205100c46007030010620480541c4003185080000c0c0c00c5490f29400c4445e40ca410095981c0300503407941e0b040410f041e0030400c900500200300c12400000002c0058071131030441071003c0458010780e2016144040801c00d42c01180d030000311009441 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 864549739 1250 864548489 864548519
    0x70b030f130f0c1e05030606030a030305071b0b22051b2704050705060a090608040c1d0117010204080705040c17040804080d110a0b04031404060e0307060507020901 72
    0x20b444500b450280795998640242d009500c0000801040c07114443d0310821801c0c802c0051809902500c1545070000009855504081000341071645d01c05c04500d0b9107120345400b2184100364018003200d4170680c207102c0d90001c8100c43c1c3c0700c0c8041107042c502e0100b065140310600390a43c44801440316900035084d01d8114001c00c20340e140c01ca243c55012605a9800542e0310300c503c0c0e052007091015040c1401c100742000440c0d0005400ba031400c00403182c0c00f0f50b001d14100d0468100f4901071202d0b407183d25003100c4d400001d0b813020b51119000e0200a002810300c07400c171030413213800d078264102e10440450310741d00f0f070b0103140701d40c11041e048800100410300b070540040d001e8440070703d085141c180e814bc4007101c21032005e8506803403d03003000c10240404c60f0104003028020406081483e00101594030481d039840c800100100140555804541003500aa1100c80c5005c420307042c0546a54484ca0700401401c0140ca4541c031902c514040081d0030780c05441201d95041d0060501c840726820118081c2000030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 864550989 1250 864549739 864549743
    0xa080f060a0b21100f06030b07140403110d120e0a050a0602100b270a0b0f06030103030f1107060f180807050d0c08010606080a140108030316050d0504030c05070b030f13 74
    0x240680f2031000b0425441798801d07200c184a80002e01d503040d030030241002c032001003c56007804000b0050180c05d1483d02c0a450450b5403001031020700341460000318204200f400700040501c1300a0180d00b91040c0c01c40c1500248032801e440348170006036100100020928103204460247e0000c03801c4005d07207000c40c1c01c04501d640700980b4081c00030316045584089002c61100300b01c24a800a8244501e503107007400f40500b07010084403240190070701100000c0043c407040c8802000d002c0100d00740807982d07005c0c6040c210426483e0090751600b0740e4541002e884070118011402c0050f00160050b00204600a495000d6411030030003005814103150a0080102c000300f0140c0e0318034020314000a841209015903005840f03150b9401119040c907080e46c001343e5207802603803082110810014441c01c01300109507076010a413403001d07a5034440e211b1000d98075031003003201d00000c40d07050038100420b040c0c114000244da14800d2044410480d601c03580302086000980b210020f14a8680120750014150366000010074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 864552239 1250 864550989 864550993
    0x103051605370f02011e090201021510050a170c04111b011d0a020d12031514030f030a0903030e060c010f1a120c15090a080f060a0b21 59
    0x1d0303140c000940c0c001008542140581d0364a05442c003103907011844010b991001d000078420b80010621300c41210342003101c0d0282c00c0350789400074025a80f08004000d10300d291400c0941c01400e04480107401510f59004050103244860340006045080b4411040b40c01c5903440a440c605401c04100805032402d1108030100103400d12034030b04240c0c001007070b0995407511a000060035400022000d03003042061200800f040c2c2258803d200961202d41c1c040703d0f10346d0301000c4d0300d0403070300041010780007451103008071000011241008a0303000307034900d1342e02e4000e2412802c80f004150307084520b85d174910400000200250024401704000780c020040c8842c0d0540003840642403070002c0305141c0c2100e0196192110315512410105079a19020680d481e05400540ea100110101c00c000c3e10b0740c2d1006c0c00d440c05e018140c03071031030344001c200fa0000780c45a4180003410820070343d9580345902e03640e81a034501d810a9004500100d0b2542e9414402c0c0c10401201400d41616140018464400c22205031031030f800034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 864553489 1250 864552239 864552277
    0x4150f24030f0857150a060b16050705150d0b0607020d0b06100206161b02060c0601030b010b0304030903060c020109140304031a0606040510030f0f1a0103051605 71
    0x500304981c4d00442080003c4020150011a566001500408504055100b00740900101020f01d4049196178051a010300002c405448840380e50009042941c4034086581001c04c5100214043e0303248000d80b24003c400326903555888104000c03101c401601101000c0c20108070b600c04c0e04040ea00a18295134004005900300601500840c41c51040500110f40e8801943c0401600c1d262024005526503032038401844a45031404051400409490f80720b4148010552003d65076192a8250300c0d03415800707030880da101c100420140d075955000380004c03580c541000d030000c1200340014080e2841290545e03a10043c0034690f45850307005100d203424120465484500e040301007a0400529211400301c000150354951541c20031040b40101401c02d1951400daa40500c10640d43e00c4081c0d80903101d003216061500700f2006800c3d00200491880b80c00e88509003081518441d6050340210760000c00d007000a404c690a40004604481044501d0450010704400c00310101c2c0c4034a001d000304407002c42c94807805c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 864554739 1250 864553489 864553537
    0x5031218092716090e010c031512080d02070302070e01090b090403080705070f0c060e040b030604120504032a0501111b041d010b0316060905060304150f24030f08 71
    0x1020f0300798000d2075a8035116403807070100c0c1900f4032680d01c80001610f4104101c1c2490320310040107035841d01c590400000e12002c4c0c4800e2150ba1703001c941d080c0003901011035503909180342c060348030f082d14800c0c200c0903d142c0000140894907800f501c501000c004000112a0751656415942c072900903000800304a028020701c030003e4041c42002d10290701411100d1551751a000c0e00400d2281072240144c0640d0818140700d0450320000b4045400c00d500551840c0729144519045905000360b91020740b960101111040250340741c0c01d12120604c801d034140505581c0c0b0741c801510b00410a0b8003031136080e8845031040c128516015058401ca540c02000030071282e0792070150b040180c108950f148443c1c0d540d00e90f007003014542005022054002d00d07500f03440c41072503d01c000d00701d4041440785500030040000080c007080588a0352010844000004000c03200f484400d100091010704a0020607954002c1d524030340a002030918400c4a50241e88800301c010240d40ba00c820350860810101c2c1c01c0b54045000030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 864555989 1250 864554739 864554773
    0x30b040b071e09081011030c07050f030403060515010f021b060d020d02030a0f0b0604060c031206030b103f020406060c0510060b07020d0507050312180927 68
    0x10b80d0089035a5980000303424414030a05081da00703203c44103181c0c81c0611410807045800c0c03d90394800303240361116898800501709541441c0300440d07565501c2c0030000d404010030805d5400240100902e041c94581c1021000041d00c03010b610b0442c410160303120441701a1104c1c03410506100c42807001e041282000f940c0035000b0140d802002660102507004420042803450380d20806c2155a0b4010f07081c0402014400455554404c601449042242800251050500a000c80244001d030850204122952800c01000034039042c2c846654000114070005032900c10204158107102c812150801c890600d4071140000c62211003001c0d00b1904c2000756103000d0303581c610840009000a888948012860b8a80203003440c01c240c4c1c408803403a1a1074421b200006541040d6200c05070f05582c078400c9158070f410014030304800e5520032541340c450380d400c41c040c18544c0c4001e81980b143c024141c3c044d01401c182000440701c0d0440b140d0389281a50b08244a0601d4000d1b01e802030780000c5030a84031560f800c0c0310051 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 864557239 1250 864555989 864556037
    0x180f1103160845012c12121f0605040303030b0f101b17090310020717070204090b090309040b0a03082a030f040f050402030709090b030c130b01020c0307030b040b07 72
    0x2e202c038550452445084956216810804d0000c8041d124440c6c0c107044214890040c0c42d4152001007200000074445170340c00300c15404030b04c8500008290151740b6000208603600500040780001d003801070010b80341c2030814281c000c01000400100d9040003c1c00c08644003d041170010714003000885158000c1808106180703100d03c0d078555103039a80c0607a04c00741450007801c0b48840c001244100060404148101c085103141103030a520140d4500803400001c02614003e20064510818a002d101e44d0400000042080410984007400320854020401c10420414440903004a808000702c140840d0310503140801e208140b200001ca29a1381d040d0285550400260104ca101e4002424004028854080030082100300c400f0340c0342d0714103564010104400c9101e0102000d071290705544181d5818047c00a0380c24010b4010541c00c00c000c00c461020305005013206016026407401010701f0b003404a941c00c2a80e030814007a45403138545d03960724106240020030240411500800c2c0200c100c01c124000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 864558489 1250 864557239 864557261
    0x50714041d01060203030c0405010f0e1903030315180b0a03140c040f06051e01030f1a09090d0f0c1e050a1b180f110316084501 56
    0x380c5414a6035501041da001c1c8180c0040055520500c1000000310011046500ba54820320300b15121156001081e6800c940c80d260321a80050b0201d0030751019030340d280b50328044138000d613000c1c003011039445203a00074a81c0c05c0c000c001c40000f00da0031070500041d6982052006103400f03840003038071642e44e4640c0d5581401c490105020340d0007002c2c454565207080e000300c81d030b640074084c01004581d01c0c1c100000c1e2101003201d403841c0000034400c1040c0c042d0f0300a911198524928900611108040b00d071088c0f003a80300008103d114104401c0072801807240061242d9560103d52141c2c1c0b00d00e0b6003140e064480880710380301110000e003080101c0100b0000c403c800b11003140719a00030700403181c1a1824003248003208100a000b000e03505000c02600321803007900c000c01e40d03c07400001400c10a15040601411030020070b140174503130000500c908a2120b0b01201c01d582d525544001042c2c44001002c10070300118104545403403c41c40c208030002c900020f0440541d04c1250740c10038132503c1004510b083d90814841 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 864559739 1250 864558489 864558509
    0x180b0609100c170a0804031d18070c0b090106090608030412231b100c020a0909080d051f08161403031c05101d010306020c031303050304090f150905071404 68
    0x5100801d500302c0003013520408500c0119075500607180209030040012745500e011403840c400814006809070f8102804190001100300c0c0c00e1902c5000680030780924418030fa034443c0b8004001591040c04420340341a1126000c01d049481d005448000200d500100400100c00b50414142c80460040094240d418204582042400441e07410000319054194480c030621110010690043c0d4443e44a501030350030103280080c6150f12414070032054060f10944003205890304041c00462280607815403850351341502900c4550b0748542c00342e901d0369140054480d224030034600038407082d01d112181c03800d0304e0000b40861f0306040007202c0048400b0301742ea5201400c0303682d402c244401e90100d00c00c004090700701207907242c103800f0001103400150034051201802081e80464604000003060044404008840e08145072080e01c1b4102241ca96102c0c3c0700e81c00081e45818207800c46460300340610806101c82620a40c101454240e1000141200500c11810407182c0f002242ca420360707841c0034001901013829 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 864560989 1250 864559739 864559741
    0x12030f0a0201050133050d09021203092b0f150c0c06060801020f090907110a080c061005130f02040b0706140601030b101b0c180b0609100c170a08 64
    0x3612401744800303038440071030074500200100da46a8100b6440c0b601d1141c42d01a0f540d1042c060f042d0001e0140302c030001c0d40541c01410050f56280000060a40314be0201d480990003092103542d1610709020084892030301107044045e001040103208041d0704a8011500d4409843d5601a44805c031a0703d41c4c840008070b050300000605000c110720801c0083e00c0d01c1c400841c03502c1a4040c000c6014080d00340310b14820803520780010241481840844c6400c0192400c544084201c0c2c42c01c4069a0070503941884d4a2040c0f100081f840002d034903420040314006003034040202c0c14640e0740d5015045802c45582da0f00e03001c01000450320124030040c0803242c014074000800c02081c000c881d1058002070302290405040c580300c294561741ea031844104c031480e681000100009a12004909501c400b40003601c0c40c104074000040301110051454140414440208800700000040104500805429680042c07a40040d400490f0150380e10702403150055210580103190504d40418540c06182d500e1f00080c0500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 864562239 1250 864560989 864560999
    0x20619140a0906060f050604030215090a081005090105070c06090c170f0c0a06270306050c091c050d0f030e0a03030e1504020303090621010807140603010305060612030f0a02010501 79
    0x4401c6001805d203601c032003a560703071502c400141507008a00000e881580da00903449200c02901c401c84103044070103041e440e01c559441c03009644031042400d2103003019003024002261500d042c803078148160000c1d111941400807584429006124070003080342c800300c1202d004076480071a508803481c086420350061440c102e50041c2d09040c03100980f4020b0040503c84424480103400c40001c940541000380241c80c4440c11100c6003203c503265500282905103054140301c120410311004048106041c0e4040c1481c100091100786000344050000c1d0060b00561034070503c5900c41c06e0b80b40c1d000065880c02152455412040d0f50400807100c2003200480d9890340035901c20705040c0090f101c1d03005503840c011401e1030182c02203500d1b841214030307062040d48002140e94451001c9454001c40c0034103120b55260742e68645903a550f95680718092510001c083d6080c00810340f41c00001c49050302c7e80b06010301035646514040c0111501d83c410801c225000520454410b548000040c2a2411140c2d001048551400c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 864563489 1250 864562239 864562241
    0xd1508010609020f04170a1a062106060609030a0512120106180e0a061d04020f22090512031006180b1207120603061b020607020619140a0906 62
    0x540e20400d8102d0044c01400c00c1c2400000981d82103404095200601880f80040241042d9046000920024006c101821006104248207100f02825280780d078203204e0710001220065591003d00c5582d03800400020042d003000f40181181400203012181507440c03035950581441c200d200c1804881d0b0000c100c182015290915940c014680341c288103601e40e01742e002c10744020099001e113a401c0744c2e0300c10108038101d807554064002064072940450800018150340a03150205032801c0e4401d04600c08800030501c0d0481b140840d1101e244071404181e49844010406800744520584890081c44081e00d0090b801e00021803203442d01e503030000016420b004018008980c0740000503a4880d0182c0d00b40003d18a240c1254407480490500600079505c1e50012101c142c410010b1400090030401c0020800a00341c000340394506802110407105050043d0490380c6200c02c60b00840144e004101103000d0a40030040c000c02054071300b00200b90490760007161011594166881c15041e5622082e01d403d03c401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 864564739 1250 864563489 864563501
    0x12050f0d0c08120405031315080703150311030a0206121008031c150506041502010f090218042d0515040b0601030c0315120b01080f190204020d150801 66
    0x14101041006115155107401c3d010755660420364010751800300f000d000082054031403040c142c080341943c036501e5072818007072022050b42090200e81d48034041480d0741e0007401011024100750b0080003203585552034610a100b1690400381c0c041c02a81c24030303c050b855040050451306e0007821091418100405040c0340d5040c16842144203410034450b820380340842c0c40401c407948003040804540f40c0c40f060444140c2c42016409942e00c40300020f40000d101b030f554030420782036496903002003000c0d454080c41c0c07505480d41048003d6000e00680b549030351210840c6041034025004540c25090681c0d80b0030120122810b014601204c036900940000c00c0110410841600920350b641101443c185540c45145015018003200d060503102c01004002611a83c0031082d82c01482c00c00d40390301030382c92450144031007a040069500240c0303400045041a80000c2c12900440800c00500200c80001c0d40761203204600f0000b260b20a408000c00301ca07014060180039980b40703103a1440310165140904a908441c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 864565989 1250 864564739 864564763
    0xf09041517060f1b09181815010b16050307080c060103060507020307050a1707020301050f0a0509030c0d050d060518150319170f0c0f0714030a031812050f 68
    0x10881003003020055081c0b0407443e004c0300f07071480071340c940020340c00142d07810f0310401c002c0301d0b04545d0000b0000c041c031014041414910240058450650303a01030740d002210b109000d910f061743c400300140649107540c400c2c400d074800c2c0030340c0640f42041481d0755442040c0d070000c0f14021060b0f0000c401481400440d200309604071b40c09000440c544000f680ea420b8842d2840007000d03022248041100a110506204072100c180c0d00038000c00c201c4c03a2240a45010303c00527031f0702c180901d1a00002800000000049031000c0d001c1d000203100c141c0051500b20381c16407203c551301d000c131602c6040014250b180c100c0400ca0800142c00002820310b03154400d50501010400b41c0d40c800e42c02000211a8182100c0c5c0c211103158004890f04180440885d4160706442540061900074200007072501540c0008034900070009801001c0d114a9540c2e81580b001043d045811a40e2682000c003020001034041d540c000b06011040303846e140d880b5500c0944440c440c0702004144e8a5802010005620708414005d04050403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 864567239 1250 864565989 864566011
    0x302040c0c11040c02030405040c031d030a0507150603060c03091511040302011125030b01090219030c0e062a0102070812091903050c010f0605060f0904151706 70
    0x140058450114403846031007480d0159698507029044c4030300c01c5c41264041e041c094018020324410350001002808050343d0300080118201ca0f80b040001c0200071102c15103169501d070380c1010550b841c2c651406070f074660302402a581c1c1d241c1c00800254240a400f00300103043c0c50000e02c4203001e04003011898403044400072542e140118403840032203c1010384055a03020319040c1e03000140c159901d0b00d410707d080041149800300c0d03a101b96a103081d12150030305403807140f0442c1180e66078a902c814107901500039020b6100003045519a41a07109911042c0031032800e2810076002c080007004100d440c1d0259000c0070000f109490b2141d0307403003181c00c1c0c441e0710105070000852910105844003000c901030780e50170b042e0070501540400c5040c40e00300111a03c4a180045000c0482030600d0701a169600c9541d0f10303038107542080800d40c02200c00b44120380c2240c2001d000720780f03020042144440d081c0d0040c05c11030380c416a034000030003401070b029102101810344482074510161640101c0c1b450a5001040c1c1105d030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 864568345 1106 864567239 864567257
    0x30409090b091209090403082a1b0304030b010308070c27051609030210030e120703140f0d0f02040509090624010203070b070302091201060302040c 65
    0x60080ba40071285521014200c0000b103024080f80d595118204500190100b070140350b0309940508220030050680304002c42130b207a01c010500010030314030004907200301c40310103156120b112500d0f036200860400d85199180084044140402005950086a4002042210501640a001c40035802002c0c060b000485000350142d40041c06800390801002c00c1043e0701d509070201005405540701c10160b808d540901096240c403041d00380c2050360710054000c482c10103122103000c0024641d12150744881c85c1c10001d04003180500c40d507003444d800300202900d01905400301e90701d800620700c010031f8001100075400001c2c084e5500140d000a11a81009004200402d26600c1014400c440b03101c14450035840c02e01c00d035410f28100380542d108100307100209415620050b441807003450090b1a10090030082040e00300250000b01160f91100030070302c1185045e00a4040d00c05651901c4040 = true := by decide +kernel

theorem cover : BRFrame.Cov 864388489 864568345 := by
  have h0 := BRFrame.cov_init 864388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 864388489 ≤ n) (h2 : n < 864568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
