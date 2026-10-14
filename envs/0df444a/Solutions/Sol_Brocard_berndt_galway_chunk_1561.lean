-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1561
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:34:58.575264+00:00
-- url     : https://prove2.me/submissions/2c0d7103-53e0-4edc-9285-6e273b1aa33a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 280575539 ≤ n < 280755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 280576789 1250 280575539 280575553
    0xf0c01140a0c0f090510020f030408010906061d010302090403030b0904050a03030c0905211219020106050405011412010b030708011d01020a082404110a11030a020a0615050405040503040602 83
    0x2d03003125814490301e051400113001800c100442d080c02e904041058a0520607200000b441c5440d5514562080c1c0c40000241e41d5409a4000d12074548030f1340001e440c11070019821120401000b5051030011b0001a120f03496500220701050300076444040c051101030034030100c0e45007070305045440c2e07a00c4060940200c0d003003610503c0b107a4400d01c25441a504001c090500004c0c00b064904416421905c2c400c582d4881d0200c0c608114020304050074040d082d040072051001c0801c074000303094039413903440366009508150040c080a003402500410807681034a80700100d400c40c80d98580501180001550940500e80b0046a40a0190456404806013101032344201ca5901c40381c03802c034410b0400800000340d51002281e0031410501001100c03d104504a20b4906440710005045510211076800c0c83d190000300da0300259045403001c0c41003181240518200740300c0c0200079413074405084000309016650010401c100e03110040082c0541000703041001246007902c0d115a07280c2c45401038070054800e0305 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 280578039 1250 280576789 280576811
    0x32a04050604050c12040f14030703090501020610030206071529120d270b090f030a05031804020f0f031807030c030206030603100f1a01051306050f0c01140a 69
    0x8040c0314015056644c90610b0320703440005013143c410020300200c54407502980140081030079010001c092001c020051603550301186400b401041c400d82c0481d05542107042041401c00071008144100c9030180c5003e56500410301c0c00205a00001030950007040c44c0c0003459038038001c145460104500f000103030343e0500054001300074081e01c500c0540c14072a40300c00d540310b488911945540c11040c11854a4485161300e007c40c1500b0520310340c10040e0b910302d01080c100600d14010b00078103007224059024001c0c40c070781c68071080c1d100c0c403500c01d4000200c3c0071010700142507140c0358125003505240010350707622503200c2203403011198420b881084c0b203c81c072000003103299a00401d080e021254820074001c0c05610319401d0200316003000700255810b0040e080c10246854035405000e0301034164001c0011411603400905040000140460f41006005e0000c2c500d00306080118605840c4942070207078440e019090a50f1443c841c011600259500306201c0744045d00d0f03e4072403a40511182141401403809807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 280579289 1250 280578039 280578041
    0x180c010201110d1e0c0c021023090d0c030503040620030313030507020904211706061e2704180201030e1e030d1104060f030b032a04050604 61
    0xb0180c00d81c503040420070319032101c10355402880c500d40c0c48242d0403548180d6410110466803600d5012020800700fa50355000c500d025803401901c1807041c01d00f4420500345039113950f07504112100c4020795a00c00640120306603240c01a42c00b145034400044000740713032039140c070782d4594200e40f05075404030f0701d401401d10407030045100700e90f1241c608038000d504554441e41c2081d14402e9002094041c400d0811501d0090788494581318403071801036500b13500c001c0f01034800c1b072206020702d1008000c126041030390300c00724035510041a41018003100d8542d141c1c00500d4410346e440c01144c2c80310302c6030513000441c54502510701c0d4070310049420703c1c00400301400451044c0020b859180c01189004641d03000140b0056000340d105019244000c4106e5280141440070000443c0e507810910006602c080340c680401c146602400b07400c9440c0031051410b25141c1040035141c2e100041d10b440074992103050809154a08001d2004840d0300340054200910707070301c008507004280b010000b60280f4182000200c10f8182 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 280580539 1250 280579289 280579301
    0x1502030706060b0c03070f020f060c03120a0b06040e0402031501180b04061a0307122f090102060105060a03200306181b18030a110a08010b030307081b0105180c010201 73
    0x283c1c0045c51600c03506591707a20140000c41790403030b031007203003d8071b41100c544816000d4461140000c0c0119903400c5032545402c01e1aa0050083c2500c40c285480140503440f11400d4070708541a20701000f199445520000c3d00b01941c0c031603c615a002c0070000000c5004807400f454480e115043c00810090103000c1c2840190382c42d42c021410021130601054164880500095612030b0003482c2400c0c51241800900054800c4040c1c15810820400d04034040078050714460260081c0b100801071600c0703400e50020351240760520481c0d02c28400842c03051130040c081e4001c1680308071b0064618000792400c2ca501c2d0703110340050f03c8032070041c01a40c0b51b080b1036900d80001c840c0240d650b88600d180c600c42d20112300405900c2140350290204211021684a403010001084024031501c1b62150a8540c50b044c05001040b50703001c4645c03681010060702040e200842200e5580390400c803043c0d5542489032514a8007007030500303007402c59842e280410080780249081c039415a0455015aa007405000004900f80d80f6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 280581789 1250 280580539 280580557
    0x10302030703110301020903010e0105220b070302070219030c06090e040b0606030709050405010305070515040b0906130510020f0105070e010518031609020408070f0803070b0406061502030706060b 86
    0x1c4030389018400b0446404001d18103000003000949031040c4000843c0c00c0d202d03c00310304184e503911003007804040044000c03140b5030fa404039000b451345103149071550301d0460000b92140003030581c0011071005544601c0c1c410515140c5520b5550100e965a2030001c0e10401e4910810380010000c00f0301213141c0910800c51030203190424044481c1d901c80c0c20070404c0c280c0c0f01400f11804c3c01024180024142ca0310300403075000758010005850000d24243c1440039034682d0002c80031020a0420061210307002100540345000c0c8142d034403945801d4004201170030045035401c00ca130701004101d055070f0403e0f07002500d0b002840401d00240b1141e11030000c00c0d200c20095000d00d5020403001d000c1040d0206040180300c0100780001c003100c11641c002c0a01c080001169001a8981500010280800c0408104200040501210304000103141c82c590b15104e00441c2c80062803002c2c043c0c0403505001d41a006000070701748000071910440780400c0c0281d0b40b80e00942003266490b0916200155903041c0c4030999030088 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 280583039 1250 280581789 280581793
    0xe0a05070509120717160b0901020d030902010504030f08071401150b0c01020415020d090b090a060c020301110d1413030c030f1806050702040e070311041a06070605061002030301030203 81
    0x545848100500540d6503c92500103105821001604800c1c03610220307140d501c0a07004c0c207526800a4102901442d1940203a4a172103402c00143c0001e90307001a80926440c410303c0c00190003035803440126424400c940c130250188011052000038401243d0080c04010320454281c0c6030401c00b041c0982c280c522044400c40d80e60b614000c200603203440300c0010000b5103013602c0018640f580780c0a161050315014520350005134002c542c084282e0340c00c05034810180900501660402c0e0a400000d1190030301c2d40200d8042100d440c4180003191025003252a1040e02880300940b91303403001502d035004000b003204440001512601190703604131088100700d405074260f0350350072509070307d51802d0b01d45030190b072581000c104001c0c024410b02511050584040c00031503489641c2c40b08140100400d07140d43c1140190703150040e8604100242402c00b00c682860b20980c0e0105007001c3c1e5080c2113030380001d0b881030709030007000008000003001882e9104034414002124101e4009440701c004036501d02003400029059 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 280584289 1250 280583039 280583047
    0x106022401060c0f1a09120304080301150507050a0b100e0108070b1309140f0a0203060a090c093b01270b0316032f04050c0405190e0a050705 62
    0x40c43c8a5998180120300800d03401ca81d0054680da020300c80c8015a030400391880340d42007407180186060058010213501042414110304082d1a0100c00f4481031243c4c0c144034041e245149140f130701441c191120a5007207000d071208000542072481d00320404660010051446071000715403804203913070041c1a030391590000e040e05030800213503480e2a402030941401100d100380000448008038050f0010321a90b1107100840c0d4140903030300e405c010302d006d0481c802650041c4101b1034183c490202040031940007001c04200c803030a10f1426035201c003058000b10415001d845a00304021007410300c007070145107201d060313600c240403102d11910610030a01031040f8014248010180d060261031110010340c00d4041d0024168800900007450301e01601d541c0301c28420468002c0050148a450000d0383c00740303c030415038240d040100c102d540c12007400786552140b5581d03004140c0080c1c420040d1405000c01509010f461484800c240710180494410144114803070800517840b0446800ba160280b503140c2c990500f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 280585539 1250 280584289 280584299
    0x606020a020906010504050d080414101e030f0e0601030c080a0c0b030901021b010c020105060108010f0e040c050909030d11070c09020706110d090302010605190b0a260106022401 78
    0x4080682891304021003800302003515038a0346540170070704d480340120b1552039140032154944200020103003413107000281203511802e608460821250003080e007004d40c10322074010040c0c7c001c04031050020b14991801003c0140520005100c40c141e0b40580c81294103240d0f25641d240e5101c2018000801d5074081d82000c01881803900051078110f00f1100005d403c1c0703010300307000c0c15192404244440050f034541000340049038080c41200d4005c1003e2809030425070402602c410020258410300d8910000440006d0501c1170a410b0301c400b401006000d900e540c00e006541c181e4a030041e220300300c2402c1c509040c810f16121a07000301c440035548643c0c88803240f0310b0082c2c7c41000b50440e89081e034164ad103d403000c401e50301417080180146035013034000003801c0c405400c1c000d0031942c283d004580104c081008264042e0364052645084038203040495642c3d45844c801100c04940c034050044140c400408128000320100c1c2c9c025040e03482c654200c43c403e0181c0e044520282680b0b8030300300d650081c01401441 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 280586789 1250 280585539 280585549
    0x8030a05120a020706090b0f1609060c080d0c09030c0603020a020c0111010207060507200318040c1b0c0320010c0602030c13080a05010506060c2508011505040e010606020a02 76
    0x6031220030110010304001e00c2e51174680503900420011100d80c0710341c3d000c00c9000d0041c1c0c3d041a42100c0c07820562030608201010290030f165180c064a03040c828040a45410050310b14100d45207401c518034284420b281201c0040c000701d1040c00b040320001070300300022401034428401d607003d0001e194000d14650000c00010350345040720310002c81c013a54081256038007144640c0030345401020580da0300400c107a502d0590f0740444101c030101c80f0365034004100e1b060403e07010b07034501c01d0071100444000641d0101c0072419200003401c28400001d21007012520414072040380d400404681c00745c00918116540112801050600105264081518818403501144d402c2d0f001d140c0c0a0801d5014602d4605490040b010755000c66102c00801d901418120003045030038056550030113400c0e9001400c040c242d41c411911201541c0540d082d00d81d500d01410341c8091001d02142c010b000000082080b240c4900c84013420310128000d09000343e08100c954440707030700c0500c00d6808888480d8090482c3d0f04459003084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 280588039 1250 280586789 280586791
    0x3140a051b1203121609120b10030506010b03240108070804140109060b0312030f010312020c060309060a05090d0903080906071209150c0c06030504150501080c03060108030a0512 78
    0x141c0c2044a06005144942e01000281a4408254005481440c05000410007018000451410001c1c0040200702c034528402414045613803080706114070b80e0751002248480703071099202500c28400e000000490051010044d80900800003148e804110f03041d1000c98a810b0568000d400100303440300041009218864464115119485940101085030106404d4030240315054901c0303030b03035400c000303e9600c0c040000c0d0030301040190465003545010440f030760000e18144006041030039440384292450b8401d10405400d1080149a180c4a0410a00ca40d64501040314401003061414011440c000c1d400100010522001c2c0d0740c660740d007401e642e525002c603000756020640103c0280207140000e004085190500c03c09903484041c0e461426542071580c2c180c0315544028099900e40f0000843c0d00510000c082d50134a0030f0104158880346400c1c040c50440c80341000c0110f140c24004140c0c05000316071448000021002c541c01c50740c0b01c88400f5140c1c420f41541d8004500d04102049400540440c0e103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 280589289 1250 280588039 280588093
    0x151107020f0d0c06051b06010506041a0405060301060c140f060604090f02100327020d08030720060106171003021002070e090319030e0601060e04060b0c0703140a05 72
    0x60070002c259070300c04450744043d40000010450100e100c1c50100c403131000721210700440d44003d1286505d048046070487c40759016024081d514459540e100d0600c4408a0b4010500504583e907650780d1000e0040402c04101c1003100c42410650f80b42d01c4050300040d0050a807003803100035140070b45950080000800000904881d00d14600321801c01503034401c562204481016240400c142d1012030300c83e0302c80d840030240c106490300e0350310002001d89c854681e000680341e403045040c1d0340d907221710303d041c0c41d91110f2188440a00b0002500e0b82050400820202e0490302203450313040104210145140008804950345d992030321a03003a04001515204074110310b00c800c2401a038103600c0c1c51354002030b240034040f5400a50b60b400081d16510107100214140c442c4480b9140800c011036120099036111034041c032990042102d002000391340c1e644c0310b908c4071008005401300c1030340d10701d10140155280d10240c441510440541d4014040041010490440c550785c000007400e58000202c102d0a1900d0000c401c2d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 280590539 1250 280589289 280589299
    0x80105060c0705040e0d020f15131e0f0b0108070e0a0903050c060906042303071226010326070305030405030d181101030c050d05091203040f151107020f 67
    0x80001c594584c0e22416010301c1c02031018002c1c0074154540a482c00c04c2da081c035800c2c660310054844000884d0320180942080c040e07450b90801d101c40341442d00c000c104c4c11107600c0e00807000003a01000c00110b5030312000b02610610240707070680c0e070328200ca80d00d6004510411528645980005101c0c0c44aa44001c056500c241486410b00d0001d0030b40514011049589048130b0340154203120500c03441411840c821000310886544800c11058100d4072801503010040001c0000401d07130400c94040c0b182d1002905280704031036141580024541e082e06420720041d6413014001c6040140b10350344600400142d0100822140740121643d0202c0701c40c2c1c8020400c0e186804284800f80390814240521114021250b400408019050034002d00f04404030030400d060518002c03104900170b4018040c4ca13000802c05400050965a9241e01401c0c90000132581c40094400000c0004001071020403486603406500038038a003184551480c81199213601c140071003490140644001490b0090f0019000e0300042d007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 280591789 1250 280590539 280590553
    0x8090706020a03033b060901021911120307200c030712061103011409160f1b020603010b0a02120711090403170115030b0609090c071b1203030b060703080105060c 71
    0xc0001d10803600c000146170045009000201c840034100b003001d42000010f4021841d00102200d11052400740b00d4480052161141079002a2a01817081031041000c00c00d0465a074a820100100709890168150100d450020341c1c41c8840a4000b41c000060031025006281080c1401429854044080d1040724003c1e125804255121001406140200310f050488914101a07204101401c50020007840d4a00b450903052031101d0351007035289803280800d00b003400350214403840600043c0d55005020f500b21100100020340d40d4107810007001079540035801e40340140c03864904d100071031007035181c00741039000c4800940e40ca07454900111038001d03100e8244060340c10945419141d80704000d030700940701d40110018400c03095030075000d0640c00030011250b0380c0c589540c400018824500c064100e410032000410144204801040b030818140c6840c3c142a00256031407072920003020010304110300007400d221091707000f411700c2d02c1a01e07002da6061312185426801c0006109440e00101182140c51041c94 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 280593039 1250 280591789 280591841
    0x1e0e011a0d082b06050f012102090d0203060f0a1805031c0b030f010504030906110a0b22050706090b040e070806010912030c1103030301120f0323090108090706020a0303 74
    0x1410000c0d83c0615943c003c64510f14140800c0703410080fa0403042e05000020782c0344000c05803464900c4991590300007006881e44201400320b01046141500203400d4440c020034440310350004801c0324440c5032400400e00149000e0040150794a5418400405550061001c0040b1040300b4403100b11300d4062241c002013442445001a1401e00900280102655903c06010905a020600750040d002504041d00c503541060780300c542d6510400c00103072034403030100045000d00c0c0144610880303210203c080141c0e0340f081030421540325521f80c824000414000c00c00001c40c12901000d6070112000390b5189000c9075525103003a950454010311190401c610403001017607116a500c0d1607016603009a0700c0d03454241043c03508050b007003044c034401c0303201c2d60040c401001800180c0341036001680e44850024030414640c50140e8091001058080080f08440e070300140341200350300a040f0b040026628081e4a460307040d42c3e692207082c01d0080c0001a008002c800380840e000350852059100c542c829000180000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 280594289 1250 280593039 280593097
    0x50703080408181f0306270f0906050126010b0d0b0907030506090d0e0d020f0105160803011205010c0309260d0509030c070b1207080405011e0e011a0d08 67
    0xc06420790880c03001d1121000e40c07612030b40003c0c00e485622114150006484447e01368a521024541140c4880182508802580007100c215034841401e0045584030783c7c01035800420382d64041c0c0c00c150f82d49030307202210105008604004002402c0e8401e2101180c86d440c100307413030041240d0440d12580c4000000207e00700a2207200f17043c458051703d1706401114006003030602c4c200782603104508900c0d202d005684c0791b24922005480908203280ea8019011444843c848040300c0980ba9140c080000070740790040012503040b80e44103000802c010401c5d040c0c00d07401c543d00c4410240150b01c0d880c0303401119450030451061b00300c2181075071030304107415107402e40e0607500d0868038075003035420204003180c1d030507020490007001d01080341c0d40302d00f024441704861038441402840e1408100c03c0b000860305201080d400391451940a8a0f213a80003010b5103408000340601d000d142010b03618281a204460303080595800c01417030001c1c2110070121503520b403003d003030308030340103000c05490107048400c820505c2c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 280595539 1250 280594289 280594309
    0x61f120f0212060106140306030d0302090a0b07051f1401090b210703051504050606010f09180501140604060210020a03151410031802120f2a0105070308040818 70
    0xb040c020101e540c10300c9002462030026207072105150780309005200e49558007050101240304503140040c0c80e120790750002224900d10307510a50030144001001401c0c030102217032003240030205107221488401c40c42640c0044402c0c1c07000414445404200521400c030194110200c80600103000d114440440d90351f6100f042a81b11300c0802c25441220204100030082c400480181940f41c2c0580d140c2c5000e44645460303540003844036040100c40c00d5164190340c019802d80015008034001c41680d44140011480240820f000702c5a489185c4943d4a00914180c802c03241a00d40715405000d10100304000036019400c1485400149502d840d104c50a1002d0303686140c008003880e2051205a00020080c48009409090b1840c101410260701d00f11103540f45540104007a415110360302c1d400030501503036080161500b8030708410301441c1241903054813242400e20030a42c0700100500c0c285100401580c04c6e1188a40042c003090f1484000b0700801c100c4000f400001006110030000280c903080080c01c6015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 280596789 1250 280595539 280595569
    0xc0a0801090b0603030906031506070b07020609010605041e1d0a030807030b010503070e060703021518010605121f02070203010c03020a0e030601032102010605060a11061f120f02 78
    0x9990041d8900348004021940d81200e019005140786c10400700210301e45104c01440800d42c07500750344120440d40c60300002c854540c0d80044820240d41040d8400a49950068590007a150300b440d401181e545021700ca1452941000070780c0d8002000c1d07400306100940203810030f074288800300d40d40c220140c001c10f10030803014038403903610034005192055025085034080741101d4100075050003040034141d00180c5505a100007180d0003a01d0350110300e000ca19001c0c550403140091070003202401213001c840d00e40c1845810711000244035040c3c850007800803100651100d0620b03070b0b100e10590a01254040c00b80d00030101c2c2204051314168541c0c000c2400e480c56020b05900017940000d01e501c2081e800310b004807140030102c000c1c090552460329292225500e10031142400320350b00c210340031068001d50240c002020090500c2d9100c80b640b06000e030007110500c0c15034807280103850000b0070010799010300310a480d9082e015034941c01c1c101813508030000500c40044602241400c60a40583e40f181d441220080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 280598039 1250 280596789 280596791
    0xf1803050a020118050a090504060b131a0103020c07050d03090b0c030a09050409030f050a09270c0923010302041d01150e031509070315050a1401051f020c0a0801 71
    0x114042c400100f2508140c280b401085004030000c0c002a5030349080c2c4407c961901d2408612074480c4d0900d040141130031240150300c551100f60140005645410180d0395000c055941c060580109006505038800c030031113043d02c0e805c10340041c00607143c40102c00e501103000385441926140c442410060b80c5d8400c08040e1115840400c00c1c41880d80e014800740c0140000396014060103a06076000b800907400038214105020300844e4400210740305d518080c00a0007602904051900c1031241c019003007401b202d4001c0c8031030030001e03100a03032800b6201d50b330202c03030010300302a00c544088482485203803590f0000a041507000c001c00034440445000f41910300980e065a0201c5500d081140b030030400b0810b9095045c00b030000400b161950b40890909010b11b080c0c0003041c025514160554106060380d000107281c1c01c840c10b1030509100e070b40ea1203144a003180c81410003c40355045c0c01c09816035824072401e944140001c0d1080d075503007502c07640012840b10781d00454071550030708030005400e6201074101b0070709a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 280599289 1250 280598039 280598053
    0x2071505040e0109090803060907120906230402180c13170c040606050a0305091606020a03020d0201050c030105012d0e0a0e040b01050603100305120406020d1403070f180305 76
    0x40c0e002e581500d0040a10000401c683d13401550f4840f4640001850103219044250025481501544a480d100540d00070104400d0070103141250060074000354644812842a0b05400075000482c20f50b0f0044e0780080c000c401c407125182c020000138000a103201070482d802e001c04000a4580d00e22400a48100b41d0500c0120000c074503180c1c9010b222945045c8141d0410b4001c0214070f400070200e42c145252890b021415075141100ba5141030095000381d1a42000309800050140c2e01190103d0007510070340c2903a800c5500f8180807800c0c1e800c01d80c4e030b501004d581040100302d698042d00600e0900642c08000b5090450101c00c0700300e1154500c41040040b0309502040e40c21442c0247c40b03100a00103541e6541d085041548850007161750500a00d030088000001094211340090b00321001598000101c90150000c85414005504903126a0000d48a1054054581ca000d512038413880c1c030300701c03000f00d04580e20031004076003941e5030900600034410150758000084080c0700e01c070009107000704024624 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 280600539 1250 280599289 280599299
    0x60f04140d1a0a09062c01050c030106031802090405070315140c0c0124081014040f141b090708070c02040b0406120602031b0a020706030209010e120a050c0d0b0a0c0207150504 77
    0x6580341c1c542000143e45403504102c9901000700c1964194cc00501c2d0015240000243c403a1f1048400507010f03500900c0842007104100002540c4e4007502d1003025460661148236251000707032100c02c40300e89480314940d000104100000400b62040c0e0b010360001240d011a80c00c0b25030105c85030000403050200c4400c905001e0401c08011924001c0d00c030780e03c01c20124622001c5d81224650244c0002d00e400040508602880040c584001808041905954100400e0032000b03404441074540c0c24015080000012241401a003000d0300c9860151030340106210268208402070000d0409598043d030340c3e400100c0c10902c2d0180780c4800f11312503500140c4e0313030610340303071840018124805462404900b001901e00440d40440c00008803504e50401588075054840166103181c90780080c95044540111100f56901c400180c1c102c5080c00340041c1d0f80300a48000511072138484803034024004903004004998184010f500149c000c3c1c0c0d143c810f660402c0d4940003402c0c260010500c40c003001490201d01849 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 280601789 1250 280600539 280600601
    0x20705010206150d020d03171603140106050306040902060f07080d06080601030503190210090819030c20010b0d0507090b0d120509010e060f04140d1a0a0906 69
    0x10f00724070318040020850900000080710642030b00da009000308421a520420980030382021000c0c100c0b424141d02c4549000c1d29907100c103145c80240c2c040000d0511500d02c100401e400100c0707040e96a150303150380c5541d0f141c105020107080400f5040741c00182c2008114551501500609409072148041c585c3e00c40c250307412502038850a0f0000c41e12500310360010400903000000b11840380c110144504400742c000d003401d03818008100c501003403c0303003080c20355010000000010203402d041401d281041d203d000d41e08804440391404031001107036003a25030150340403d20140d000c00c7c002d0368001185c0120704030041901e401c45900129540d9209030300600800c1c80b54000e01c42c5000b400c3d074000510f441c0548a80109003214002d400034400b001481440c16445041000e0040c0f801900381381d901c0205103038400065000d403140410a980003008245141b8044001c8185681c104403600a00c4c9200e000e003d96400000c0c10205400781e4880022000070005d0041801404100c10b8103000e50031000e24041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 280603039 1250 280601789 280601791
    0x5071203120b09040308040507030501141602070f12021201090308180a030503060603060315010f14030a050c0913060e03090901060e031c0c08030f060f060a12050c04030b07020705010206 82
    0x11801c9007048840c00081c0c80c2c003000c055106406240c000007603115401c029041840fa60005001542030079207090311038a000207440d0140e01110807201c00d40c3e8a0f10001c0380c44004a02580189a8032500c080000700b40810440d40c2503400241004880b6204881e5242154454034048021441c0d403800c0201e500e00202082d801011941c014110050031503070000c246100003803030170b48250b801001041d02c0303480800110b1b40c1c1041030310b1070f0445944c40317003d030b020508c46500c01c410442020041d00350280c10041a1b44090365130041c000c000100b407500401a83c04030013071004651000030441c03940810329500454072081c907014080c56a03141744c0001d10215510503046001804844506c0a03079070340f4002112030841c00780850344040321002020849010300c02c2c81d0701806220010084c0941c1c00003c000b21b600900c41107415841d61120001840f40a0043d00c102e20045590040401441c503034035000b05070f114070340350380710f904d0b00e0340700d980d480b800941c141d0f18040140d10408050050b540c0410440e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 280604289 1250 280603039 280603067
    0x11010510080d1b0b180f06102922030c06020114061f03021908010f050114040303081018050a051b04030f050312010608100605120105100c05071203 65
    0x2c10f1400c480241c1d81410941c410000074068804540040c0008400a2000c800c4030441025910513140c80440355070b542c81e05803102e00c0c654050400018805d201d2051461580700326596120591000e560340c04a107400c01000101c410902e00e1440d5041254080c84501844c410300c41210514185231303000782107400f403401c404e00c40d03034940c42840110b50700c0383c1c04c0044900202c40c403111842d6400408030044c0c02030300880e00d550813880181c03007211a0000310803416550b001d4503120b400c0350b40e4001140c000d0031020242c42c07010420802400864850710200354003480d00780345030f180c482e03880b003198424090034200e80750020b9440b0107200f500042805540d4022020540200d001140c600c005c01d494811840000c04540d0707001c0c0d1403401c002c01801aa5559000c51884150315a510140602017003022038000b00c24620542020903468003441c10380d01e02243c600441d0020340e003000d0034080702030304410400003804804080341000540800207a00a0003042d181703d490700b0340e240342c06440440600b01c1c3d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 280605539 1250 280604289 280604297
    0xc0d080f011d13020a09020a09170312270d0302071b03020f0402130302040f06081e0d0f0e0316060201060f03020303032d040c0513020903071511010510080d 69
    0x5031202030b2980401281d00030556220f210b204165910000e01e0102280d0311130f00c00340d4000302c1c7c03180401390400c2100003158004004c1c80c9403150b01c1095992240300b20707c1c0504190a550021030107055900008d480612103003c650910904034031070032803174001812184000241c0014941c802c010745641443c600350400d80649007064110385c0092a545d06020610380a2a40801d5482e005c92190030380720010740d000750080280c020020b09020281040d40614012482240051100240d40c18040c03001000080054050345117408030840c1c12030700303042100041000b0100001700c0ba940500c0400d803424280d0035541940c1e440c1c5034003c5e007900e01d158004680d0f001c50410400c050384003c000c40754000d4017206100252514001d61802aa8501e103d00211180c00802c2008002c15030180a0030b49204990b04e240c8001981d101030300341d1040c0c03a070306509500240700400c46508030404c1000c00c84d505041c0340d0110140c0300daa560845200f01c402c1c486802340604100104a820701000112181600d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 280606789 1250 280605539 280605569
    0x60a091e1a1f031e090512040f050913060c02060702060601050c063108070201030b06030903072d03020105011701110f030a091e0c0f050307120204020c0d080f01 71
    0x88074a010050b6070070050205000a410b0306200340d2002c84a020444612008505445003640050070409411207141c403811200440090a10060b00c04692140f24400c070400e0a002c180a400c0300c000d0824251134820001600000f072180c0101c2241d40070390f9000301154600803070028a020000707081c040c14804104009548840c010800582c011035140842206088800c8000320342401e1060b51100d02c114100000d04016451000f801d0a0b4000d903030601017040c0b030b501009150300c0180d981217890790040240d030000030703a0f01344020100c45010001400204800c00d00504610b01024110010303550f55006000d59102080144c1d04004050000c0000c00c284060b0107400307228010383c048458901200103140c080141d001201c0c4190700c07821101d40c9814019031200e184903440d00840306503a0840d40030400740c1144100208507400280213280b01807030501d48500740c6000c5542640c0068003001000000d034001c1028820220040d40c07102c1c0c05282030b410b210304011041e0801031001704451 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 280608039 1250 280606789 280606841
    0x71b2c06010212090f19080601080105070f08040501061a1b0105090304030b04050a02030d171602071401030227090a0902030a03052811010c03020304021503060a091e 73
    0x400714860000485401c3c0e40b203001d00b0009a01c1d0f000c5c840102d07401212902d90719401c2e0f0a0104507402c4800307010031101580d8035030f041113090700c0b4211050b0b80001d80340090040c2c10352042c0242500b29010b60000034283d603c0c4c090907018101198203211080000082021011511b00c0c10780c640448d03e00b000f00303c5410481e50b003686070311941c80050144540e01c1c0104080c06403d005003503505074010704640b0035010a11004d031400f44541214010002d404001501d002c03010525011201d48540c007510030282802c03080d5103c41c18440b0340a040503402e000003105141c5800c040c0d11030042c0d901d00c1c03500003407546041011080c0020003569085042032021001030b10b000404624140c0e16080c1151294501c04c2c0001c810f40b04541d0000c0302c0d103035054440408030f4119400301100c41c540d00080c01100d4449006500303a2100f274500075003001a00740601c101110348005981c0100d001041c0321011a1741c3c04441007515014542c65001c00b0548054633030160580c480c410b41c11181c40070b60784c0d0003c002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 280609289 1250 280608039 280608043
    0x70504090809090903040806041a071e081503030403111009080307020d020409020904030305090607140906070804031a07030b10050306040905190503030103120305010e0a02071b2c060102 82
    0x100d5a40c014036003c804651080c00520503203002d0500d041c222030003443c280c1000404034085a9100902450190100d208c1e00d20580407015075004080d40380811464211003110640c1e0000d0400c1100d0b000c541012096981c20700040c4000c43c0106c200141d201d405c8410010400c43e5044088140103d26108011810010007520032050b01124003060038649800418098440050002d5202103403030700b00003c142e0550f11550141b5807000440720169030344041aa881038142d414819406401d0042c6070703852030440f0040c2040e074404d04005003400d81e280d49200c1c0010300c03082e080090400c0c01040014055241c030640c19203940441d0401c541092640c00038049100107000c0c0c50149417642a00014414200b081c1100710110b804080300c01039490900503160b4100f030208859105020820154040c86030007128161180f81c49100c086840300d0f12800c0c000e612000c0201c41c50f018402c0110440c20780060082e0003060464101a0600f120303600360340340040c039600300d44030501c1c4c403900388502c1c1d0b680 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 280610539 1250 280609289 280609297
    0x31a070c1e02040f06080109140615090c19120b0604030f0609030c14070501080c030f01061b051b030c01020a1709030705060a020c030f0a0f080d150305030a020705040908 75
    0x72940e10051020034034004a0b01420103111301480d001c0c181400002d22483c1503010400e05400761012500c49604280e03043d4540c40c042c2c5902d40c0c03c0328042d40e8542c40d4a40032a5168100c10900d414500c2c1c40d04200d1b050030320501c90060107000c41e2000842d03a5031032001e802241c0c031005046600620301343c116540c80322110f688410203030007143e6130242c2d141010f000b6022a8001a04224580301d15865a901c01d07544004500441e130002e90040b001c26214495101901d001d1400c903041d4a00c203a007020b07000c54045028100d50b130b211000c00d5003060302162060104405039090242c01c5d96003011104103061501e80c1c010f40303060465010308031201c0417070205414501d581407001d0707600b56100c81d140c0c0040d03d426000c2e00b00552101c3c0014480c5011500010000380455054056507060001c035080c3c0c648550803080017600300c000034002c500c00511080d00500500f009141e000903541880050f13004940003d80003162103600c005403003000c42d6010400d941c001c1c1011134050102c0080d558907a601405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 280611789 1250 280610539 280610573
    0x2406020616050919090218040b0a14030a12030c08060d050619060801020f0904110c0303010b0703091211030f190609030504050303030f1512060708040201020115031a070c 75
    0x50205481c82181e450900c1040032131805003040e0407007526002180c000f5805907112440b00300e01c2ca01010900d0070540607003100c03060b0042c200072540385082c00111103071800d294825854017528048000107031256079503c0c0b060f40296000510f01002903000fa0843c00701074500e6103c0c82100c0d2803c0001000040c0c0c40d644000028421842c0c403041500318000341c006904200515400820700405680080018002d0001c00700e90034044400a0400f250701c0f8450506080c1803500204010301400724a807000380350042c030a1510113641692080110702d03891032544225014600c03544a508a07280c2001095107820381e41024140e40074a40d0b1039044850021080184410348910070b18080c140a10b00ba9002084080c0030b5035038929004820a41c40d1204884903130103403501010718000c6041c0103104003160b5070ba401c01802180c56049060f1035004000704101e04541d250043c1164a44203103850f100114441c90704c031400202002c1002000540080607001040020314400740842c0604804601c092 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 280613039 1250 280611789 280611797
    0x10605091e060d0c11100b090f1005090108060a0c080105010f0809100c0810090c1403060a080d050c010617071a1e07030e03120301090c020a05012406020616 69
    0x1420503000c24220b004690301256500d15107001003c84a0304504000301010b17400e025140748017501c0c03680804865845480a401100001c00030b60943c114081068220480886401121781c1e90400500640403d03000810940c01c607100340f000c03600b503a0044c1d03043e014881c240b4052030b60410000810f40b40c2d51100c00c030104540c0740042403a10005002c0313180c803401010410b01c04055410700c00b41203c50705a8150305480440c00f400611080a0b100f02d409181960b51000b800c1940c11010942c00d4001808050f4009200200060303203240c204940601c0384401d445441c0c69a2110524a08441c240c1c0d10050401148104450440741c001c12190180c81c4103588125018121349205080f501501e1b0503a00c610303449407210144803c01d20041c082c0301d4880d070740f0745080304100010f158690564003050900c00c1c1c010b000520034420386401c901c080004a01c1110829070861701c40c942510303910b00484075440303c101100c00c0c05c0700380b5840e500c0182c043e50009005505144900c002145003004002c4104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 280614289 1250 280613039 280613089
    0x6010309150606030b10030606120e01020c1b0127060507050a0b0910111303080f2203050105011d150f0d0c0e0703110405120a0b10030b01060509 64
    0x201c030076048900384140a600410510303880c0c1d50041d000303200d07004143d407050b241101c8101c0e100c0e1003401048242c1c5d03019070b074990710366480c01050006800552040c10107550203100d903540036041040a000c3e50300302034a404028640f480700241002651540c1c541c8074900d0f0751138224010400f00310400840e059490210340d01c1c2102c2c2070140c100000f1040050647d0703000c10902294100024180d409008117080400145c0c21102a4800703503c00c9481d02200b040c4030040800104024601414401142c11500c030300d0005040c5024200300320030026604880e0140b4002d20502009116150142c540c0c0c080e60000c586400080c1e414a0500400d6240a241000e5011890351160601c41d5912580a440c210301150302e4603010180d1591801401c1e286145100040c4d5003501c01e0084080c041c890442e00c43c40d01381080c0c180090500400d00c1c1041c140318620300500000c806141c10352060311081c00000c881c9045141c035208840c01139005c441088003d0215015990f40c8510046044010072600e000c2d0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 280615539 1250 280614289 280614293
    0xb0703050403081b0c06030105030607200111030103060b0301050c0f0702040207062c0d051608120907030b0603030403111c0b0703020d0b09010b1b0f1c02060601030b0906010309 78
    0x359104580008010600100c0d02c20084111000010310610080080c3d40102c160301007885000c1c0070910440340e042e80701202081c01240500e141c40c030084040800441a00384081c000380c00d4554064441031601000001081404801c1c890a441000214000d0005013000c0d50791074098091090f0010a00c0c2001a07ca800c40d42d131070b412a01540d500a9042c445a04183c440c2e002e02540d0001001003a580d02140c000300700d1000c10002405403c5031240c03400d14a400c2042e107281c00d0701e00c400300e071207100401005415040d410102c4c5c0c414140d000080c031543c1c5c00c614008c20146405400280681d200303000a00004220382c041d94070003841600c840b44101204066040403d660390401380050282206201d012540f42d002011108071b010814018010f180b010f00254034004d11400409001c2031104960040d0040407004681d01202c0032500724202103c01541006410001c4a1264101101405215405024103507020b04242010012440d0340c1000c220140001003425040503556100002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 280616789 1250 280615539 280615547
    0x19081603240207060501060c0605130c150c050114010501090f060e010e010e040903050c0c06120a02070f0c1d0a02030907140102010914010f110313020f011403070f031506090b0703 79
    0x10f1a00030b50240901d5035259405003070281c403d6001d81c6e0342410f01002410100703248910b0018135901c0848490014a851023403110300310000718440070026100900c2001c50824040e41ca020340f410307910303102c59524010002d0a81841d40c0d00081005010810411099030000360703100c880a0282003e5200c48a2030f40101c6a14241482407036000f861314030003105165001c4003502e000c013580011615206c9084080100c203014401c0d90b4043c000d02c200028403810030135000b030300125219180b6a0001d0300990340e179402c0001d054000c2310481108503d030302c4040950044994001e9100481185542000c561054030b0b24100c1c007640440c0c10081d0140540c43c0d100754011400b9513044003058800c51110585a8041c00c00441100c0c00315041c404c0304c0179444203003000c032400382c40c10540e044014003142c0e081c13045d00d40780a0003c0d414400540c0200070280100c1004501c6881d0b20b03520240c40740c6c44018080c085460b1300a840d0369414501c40207100b51a000107491064800c1d0704001510b885003407034122 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 280618039 1250 280616789 280616797
    0x10e242401170901051909020f0d05030909150f010801150f020c060a050c0f1f0c0201090f06090b09120a11100c020a050c040504080405120c190816032402 68
    0x2c1035801044003001401d40d41135104d0b500401e2080d41c41c042c0000c09004610664510130006540a41c0b070400b020542c2c5406c005107044144a001601e05118150000994900048503c142c0d20024101c52000e1031038010791000401e8002d0a01c501030354140382d03444d00c401d101d00c0188030038001d0740510740134414001c000712a440703200100010303070f58000020024a5a04000c280c01c80390302c10324030b500343c04140210341d01968203c0c0e03604940c5030740250683d181c0544500c40800301995690703100e8178045103107142604007003409813001140b10703000d0345001c200901d001000c00a441e000782c0303040c3d03003142c4c1614101c0d59034044a18001d1144e64003040303031505160458440e10484c81c642600c1100085e0049a820032080c0144207840000c4049018481540d030100e8004001400070041071109250928440040740c00d2a402c540e041020b40c0c000c201c03001e84112110604503511003040000f20341c100540d514200b40c00c0240c1c0c0d0500c3c80c40d41c500700c540400c0f6403401c40c0c20342c408038040014802c5074162 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 280619289 1250 280618039 280618067
    0x1404030801141906020a030207080102090f010c03140a0c0203061311010f030b03070e011a090604150507151b0302160f020d12031b05090d0b0c0c010e242401 69
    0x2c0d40403180d4620020b551540100407c50250088000014003250184280c1d01c2a8030701038400101181030000459049003c00000c5041c1703e60710400490520b95080034002003d0a902c82208031160390040518003100208968140d030001c4510f40c0002d13821085447d178282d000c0c00c0001400c0c0d00d648040c1c4c05401200e25041d05481030100004e4000e07180401e03581220319000c0c00485600400d001980390748901088035030002801c000408c00704002c0112322060200e070b0700d042c03410700103e95242d554494954944040541e2200c1d48420401440155082004904d003400c51030291603d0703004031098504100603000041d000d103942c055440302c11181c50010b610020760500d81c4120031014006002da980840b512201860810301c407640a40100c4842e40001050502c0c034000694850341d071400000c0281000803000d00803904415400d0140d081c620350054042c08410421564084910400041c1020000108070501c249000e0312288174403903404008204159030b4803080140c5482490041c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 280620539 1250 280619289 280619329
    0x3040305010908031609080d0c06110318011b0c0b060301020403170a091203050d1d1f0b040207021509040908030406050906010b0c07260312040303140403080114 71
    0x1580c04010103100150311a4910000d200b908684111741215003000d240030b841196840803074044c103400c0c0245207030700d8024480c0350040307000100d200b03400c1040c0e001070340c00f000e00003480e60034000110300038040d9805100c0e1041210300e400c90610002425400a4000908540741d044003044003501c082d01110040c6401c0140214030172400f9420407400c0c1e024084032000615003020100300309808007522002e00d500b40d590382c0c1c08d1039000900e9000801009844c01c003441c2c15201c1d8100d60384400c1c04480118200140303e80000c1e00441d1403002500d0b40440b4141c801c6204002140060340c1d68074408a203d00000e030a15110803050000c640103080d01800a010070001004102c100601038109074898522181035075a9a42c2e5642604000e0140035010281900802c4080c00080076025078140d40b0b80c9004240c0e03101c044198003140c250ba1250380c0010080f40c0000070031080c1a01401402107000340030342030540078501528020482401806503c9451041d0015101641c0e40c0074061960600b00c410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 280621789 1250 280620539 280620551
    0x507060909060503120f03250f0908010513030f140304240c0509010e010e0603040501020310081c030b040219030605010e0306010e0c07170409151509090e0304030501 73
    0x1000e03020080e18400d468440d82445004500744c14013040e041060b0303011020440c10000750410400d4030307410090015404c002031030b19a0740940c000e8400c842e5190001d84481030f41c0700c50050300800031040c580040b80261704040500804107900d41d40301103269014a826034005000031011181100c91300b20030100103001200340010300c641d18030300d99045100d5100c03003c0c281601429403015511000e14074004108148410303486940501e034941000d50701403600b01c00180c20603001a10707581084c0c4041d80c0036035011040111245000380182d003c0c0441d40003d103694076001d8070a480e04800b8600034020140c84980201c81030703c440d01940d1441030f40601403041010102c00040c01071400340306050004448103400551424003282182c1030f01d04428140700c441d0b40c0e005004400c1c1d401110122040f0f1580d0b21150a00400d81d4090005001c05000109510381d50001003100d21a481c0c0111f0826058940c088401c50f4000300018116000e00101185402541c81c0c00307030031030161b40d0018082e542810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 280623039 1250 280621789 280621799
    0x40312110f160e0f06100509040e01090203300f0c0d020a031407080d0209180406060f050612180f0d020124030201051e090d12030c0201020c1e0106030507 68
    0x305803485a040121070b028520340c0d8604002003900707001e45401d0002a2a180032848900f030403000000304000c1d6052070b41c64903020401103802c691424407030a401e41d54884d400c6085240500a26440340340050340000c042460040880c4600218541c41000110000b0403074040882c00003540c0c0105030000a441740e50f072070001c0103903d50010450850014152000c46110b4218100c261440250069000e07801d18001400d26002507002c01601980a24882d000b10b40a03004500c06a01c1280b0921001ca0301e14a050789020301e408154004070b200e01030901c1a00040d07049c01e0089640541e140d1784119640202050060821a15850125960090400416100e81c05406c030148600c4510b4000300f10035001c06071502e00c0440c60100130b00084007041900204550104410706000c80440781d9031400d17800038006000304070807007011944503403a8011800f1a0b50544224486410710b0f000941c039140c00710407060b803034204d25403100d2004000daa26103c3e040c48250b111001035076101e0100c9061076214 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 280624289 1250 280623039 280623043
    0xc031a0906071b02090c1b151311040b0a0b1801090504140106080a180c080f0609300c0303010f0f0e01090e0f0d181703040312110f 58
    0x1122005103500c50800801c0b1000e20803042ca03101208102c6043d00101c0c4076034204420301c04c02925078030608400303220710045111100388644c40d251740c102c014040022079503c00e08442000a2640107288141c2000302c01103071490300081c11111049800042204148002514043d0b41e40c001880241c03001c42c95400e8031003405072260030304000740c03520100c0b03560f100c0402054400900201d01821007820040220602940c10560060020038000c9041c4101ca6201d1071f0b0341c181d01381e095842031320000003005a60f406128502480112101030400c0f0320349807a040d0b590b0300024070450403504144004006a1103801100390018034140034003a1b41b103141e5511030750307283c00a01520800020400700013404000140c0400c049400c0305905078420381c42c1050110052221210031901ca00540c4c2207900c00c0c1d80240030304481000c0688440c00813201340d0012021303c00e400d400800c84fc0382007280b0032003206d0002064400f1a0f0740500520103a01d000c10b030850700c031210310349401c3c0315200b1050894a08140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 280625539 1250 280624289 280624291
    0x21150601020c0904050a03180b070c0603050a020c1515030601120b071805060f070f0c06120204030201090302040203060f0a0806070201140f07030e011506050409141608040c031a 78
    0x9034216004031000b00100254200180e030000c00d41d40c407460120303000900030310742c4141c0b03140068041c070482035803403032000300541c80250125064070519206103c1150144207131a0400b01030036045040400b030400899480c01851030003031181d52508009441408207800ca4021040301a09881055a640300035180741e020b40d03102211142031020000d0052407007617030806202c620020521503540d140000f8498568050000038010300c00c01c1001d100465002d42004512501c5189808110340c075258000b0044002754501405680c0108420400360b81c0c40b00340c58056940480d0016903d8450400040c41708401032280d0b41c1088654a001944040101c0d102d440751015400030300c0003e0441c0c4c19000840021140300342c1340400640401e1a1030310952064080b840c16100004600d02d0b0040210001c1c0c40c0c1c1e5000e500090720010b004d11180c4480c1c0101126040d019495441904200751407268242201a0801c100100c59000809000c0c0c8440300ca0000d40d040348280818001081c0c440d8942d401c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 280626789 1250 280625539 280625551
    0x180e031605031c05180a0206031f0f14090c0f09091806240a031a0a060305060108100e01061401080c160807020108090a05030412050304050a0609060908030304112115 73
    0x1c080c818000b03d640010510388200395004064500d165520b80c079504150306d407502d0048190140c2c00ac04101e021407808203502074458406d1014484040a0800100c0d4000612074035940c00141308404c0308480c4101501c44503101220000c1880c1c0e9480c0d48842c00f07040e041c6c40c0025501c02c2c6020720400c0b9110000b03081221182906010881041c0020300141b0801c0b44002090620310086245903010b5501c1c05c19040031811101150150382da844c1c5a00d008400e8010700b0700f6420000812404407503505c50342664000b00d030001d110071464000745002c16207215800a050103090303c0040e00e41c00f00c1100726400a80c40300704041c40c580381e41c10036010b5900910401c030b010980640201d0816000015100c00b2107601c07c009500d42030070300580c5803501c4d544510486040c4410b01012810740e4030300044d400900140d03070340d201541c0d01c2c00400801b09030706540301c10000e80042040c0f00110361b4058007107508002c10340b410824680e42e804544100c00c02400c118005002c0c44140c604031300400398009010700c07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 280628039 1250 280626789 280626811
    0x3120a230331060b0402090a0807170105091209012114090a0b010b0f0d090803100f0b0702061b100902130e0307230d020106180e031605031c05 63
    0x590740da20541d8050402e02042910008564000c000100180c00c1007040820260015041c020580046070700740e0416048040d4036000039206000341401d5006e006000c803140f0009004908100381d50345d03100c14a074248619200c40010300303003d1036402010600d41309030030b142c40200b5010040d00117074010911104c9000d42108200042904468006007000301a50003d181032542e03441d01c0040402c5501c51a4400403620003030000c401c000500b480b603414158003410706695a440c20a0025901190300c1d0040c07000c41c11400014003400c2011019940300d10b605548441c2d03502480400e4906088141403180303014420180d0a501c0c800203a080076a40b244282c8407c4080b400b61103503082074401c0011203002c29030003440300e030000c580e0400107030928070f940d081d40b00c5008030300f80601c0b8108440c0d00d0220b40540e4590300304000302002480ca040000440100820240381004070180c0c40b803080d101040c400060140308901840300500c1290304018508480e590340c0504c2038100c802400e42218127003a41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 280629289 1250 280628039 280628071
    0x30309160602060f060103110d0b030d0201230603011103090c2b03030203040206090a0e0708010614030a090309080102040603061e054f051503120a2303 67
    0x80908814403054841a801624065403080c1061142410080c01d150415403a8407a504a48030b500d00105054900c082020401c00f130060b09046ca0403040c1e44000045a250020003902403140160100c0400710b035000c5070740d03a0b80b2084006405854200595036071410700000b80142c1000005000440500503111540b400e90601d241d40440480080f00e2000d03002d5041403080068800c1d801954840c5c40100340a0603d68000003050004209402407040c0010003024400c09a4221003c540140301a1814594050b05422007400c2404050240d20026845405140400d40100c15580c0a007491600842d1141da4030304005014040d98416040741403013014103c0066034031384e02c0010a44101404a000c0c030f60040c50744030031401c03403280c9101c0c2e0704401403040200840c6030000c604016001c008107546034804080340e401110406030a0011058940440d94040e0f00c000c01c002950815664403103441d003040160075501480380a482c0b43c07411289268040086010750080d50007031162018000352 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 280630539 1250 280629289 280629313
    0x1e13022106030d080f01050d05010905150601110a0c0b07060902031f0e0c0603060d0317070503010f12120302160804030804030b060625020109090e011a0d021f05130602030309 77
    0xa1140c0c1505c2d07a4104d01d51322001441541000a030090001d031090000040c00131454a4483c20040003200f9000868140c0051108540c1d001c07250084a0b000b80001c0c0c01101c00030f0356111802d24891003000c131075540201c0c4800c244015540321141c010b80150a985840d048024250050b160300b6202d01c80e1181b404050758000540001c0e4030740070980160016103103445020800100301d03000f400882c1003100441c8030b0319030765044507071090050809455103a1603504110310440c022100c0c1d080b5801002020314113801181c56075600e41003030400d50400607520300d150a07501c00c089014030130141030301000003000010401e2120003031040340d02030040f00000d51202d00402580b8480d00c00d00401c17001d144603990070030f08081d048001e07446105043c20040c40d690780d000d54090720008802504981d6461a1900d400e4040340c0c4121612039046490316405210741e070000e2407130100c2c124803400390900201d04809150183d02192604002d080d52802070943d00c11000b07644c2d90003121511903034014003d1000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 280631789 1250 280630539 280630547
    0xd06060807051206120319051810050d0e030d02070311010b1009060f0912050c010815060409020f091225051513090f0204141e13022106030d 62
    0x2c2c000790401c3c0b644810b8656104000f05100c1e440c41a001c640000c001c602c4400039a1030b464040d100d01c5803a0244c40d07041801854000c86044160b02c1c0c01403000000c2031100035030103002c8030000e44595000103030640300c0d0b582d804c0c0385004119100c42c0e010320020390304082c103400401034600d0130384100c0280220b000d10000c1c004012607411000780410a803002c00d1200e54016041e0907520001c91a10300015a81c40400710310905104505440e42c1d005400e84c03240d5564041c0c103041e4030101c02c201c5184c101882c40c1c0461003500c40c9200b9415540e501150784000e00c800305046803040b4000030014800c001100d80b0b0a0b4a07008000007546d0100c3c039112200c03003030b0010b02a6003c00c95000411100c21100e059000c43e11f21791100d10130050400c42e503030300410b10310b1061280080400c080c9000589a42c288102c0c00d0b2140e00319418140308023050301001400300c0d5070440380182c40000707881d460074031010100010064001c0200b03040305004410b80b2090f11424002d001441980120101d85003807640000c191 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 280633039 1250 280631789 280631797
    0x30109021c18080c0f0115030303050708190c030f0f0204080d080906040209040221071d06100c0c03140a1e02030a0209070215010f0f05060a0c020411040b0d0606080705 74
    0x100382c42081d10a4140890b00c074101802241d40c2c500b0984841c0e00484401c5803c49440b0700d0480700c841c0c140b580a0003810ba05208076a40000c903803c044e4914202070300705e80341840c0d8a0803a064210384070007965111503c6070300f180704c9440401005002c1c0355140041840650014040c02c14a0b225924840340880e2060404a014800d908007a0004d45c13103640a220385080020803d81e080515085038980040102c401a000720900c98062b000d40e5061411035000985025900f040c0c090100c3c0070701c54260b450b40003e10f04026a800c200c08425441c1c0b40100080701d550b40003400024042e280d0b941c60319000b01d000300d000d038400c030404d01c08980500c40340000034030212000ba406910521040c0014200f1914640c8c22107403074011192041c030500510b00d00c15200b60822000b23001c603074900704049046d600015000d07000485565007031507040c9400900f21124060302034400d81c0c03101c1c1c0801184200c4c0048070042d10000600c559a0f00d060031031340f800780034944079880c0082c00032800100f086200340155 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 280634289 1250 280633039 280633061
    0x8040f150c0b01090504020f093102010206011203140a0905090c0a0e13060b0708090f0a2d1a190306050f0915120609060702031206061303020303030109021c 69
    0x14410b1642402040c100a00300204100c1e000141c40303240254655403070216030322032900d0f035a02e4400d03440b1948080e4800c48280700e20085c800d00101000b40140c4c0c0100b4414103441002d800c068103020281030466454200c2400c48150b010005618070159900443c40003d8800903079810406499031341c1d8a620754130880c0c05060001c0c88501e600c04d641c1c5890300302000300e02c0071408003140b041d442c0c4501018580c001d500c12245018002401150780c280060890200181210700100140c5002500d81e02060442c50780424044801601c0c43c0300c403000300080000c1c1015645851912580e05800202c1d50b101000d081c0c142e840240200d4501e500c00e00610042d264081d029450224000d024000e4034000505240c14042d54001c4030001902c9a0401564a4014070020800e908068110701c4c10b0002c0900703810b003190400c1111140108404281d030f0f81284055038031640e43c0f41c1019004807076280703a400c0213516000010000540c001980c0240803005a81e82d009a400881141113504445d0b07005c140d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 280635539 1250 280634289 280634303
    0xf06090b1e070302070902030a0605030c102f0607050c01050603060c090f0f12010902010f030e0604031b021306090c0203040f05010c1a011d0a0903230708040f150c 72
    0x181541a105400b502c00d0b80c0c401c0c012998840d4490030f080d400d07604125202e0840540c2c03150100940d25080149004041054801e0000c010340314070f00034414007000c441d95228444096030030880c003804115042000603c9825142ea900b01154000d240d6442544200041e60800c0301042d901e140c080343c0d00d8001c40788050854035101c100c03002d11480030060b155181d404600c030440c0c2d51080c0c9404118401e06040b4900000e201001032001400d076a500458090403d1325116840c07001503400200c05800a8041c1400e83e0001441d004002051000c050300039080f00b01400852072184194100005585d1140e9041c000c2120440b4103d0f5680950700c5040919202d0190410203540221000e910840c0160144503581070b25018080c042071007030348540c4a982d1102400c030180a001c0c40a02e400c528084020b01101c03403070b510000c00c2000080f40c02041c2103036410550b07000c5a83c1c0400c03078000c1039004418a8840740d64000034904410715204804289a03011244064035204114102582e540071071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 280636789 1250 280635539 280635577
    0x102181f12050702010b0301090c0e090d0806041e020a030504120e0d0b06040e150106020d0504030503120703020c16030213020a05030a09030504050d05010b010e030d021506040b0a0f06090b 83
    0x203010002e864058009015035603900b40d0a103880c0c5003030103441c1501c0d000744900000f2307601e0321580c45905040100016050307001107035140d250582c401c07d007a8200c2001c84c2c0100d0b0500c500b016891809440c42c0d80c40308228800110019090381580015103d540691030f03c0901034080c8009480b030240d4880000d5010222101640000d04d03481600d54015101800c00290303c04103406e940e20300145c0d80da8019001050000400c0b07225410003100e89418501d00e052030900d0301c0c540e02c1507524014911000303180000c4200242e0610f100e6815280b95508035005ca415042c1d41925048829240f03000c20ba0007443c5414100340c01c001d06008030380e1203030410394036203186581d00b01040005000c1148110100107003004005803581c1c64010b0f16400b03078000d00001401980880002d8486010303958a00c0c06034006890380d0b0551900410340d28880390003403410b6840341c0d40301c000207030003081441c00c02a0701c9041c0c40f20216541208948c1c0d801074030b8003902e81c00409900d07040c8105c82e5016501d010301c0602e04803c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 280638039 1250 280636789 280636817
    0x62101150c06050916030c0e160906120b06160203060a050f0711120f030106021606021c140c030a021002070c0b0f1201091b0305191104080102181f 65
    0x1034401c84c3d01406250645196030114030041c0030462603603000b0755103214034200078002828116503154100440340120400c036140c1c580701820304000c0d072080c1c00034001e4003030003103501c04940c1d00401d00c0d00070001c1c002581c070030204050110940d0b280600340d0007840303410002070b2118001e01c145400358408050440c072581d0703000f90403140c14460252044003030017500c0c110140c9a0080340a41003d804028010f6142c0d810100024501410720614041001d513104041000301c1d0081001d540d210600003030400da01402e928156003c84007000319030802000010b0740e901c680c101001400e000d403ca642a65007240d000d16120040e4080c990019240341c151013400c02040c14020010320000701d1007500c2c50300b0410f03012030310003116000341d00400405459a845200c01403980f401c55144d40070500382000386081a40581c01d031103003c11401d0010f1907443c8a00000612223170141c17001440100004d42d43c07420b40842c4141031a07124151140070381116104044002220b50381c10054450300d540b103841d058884 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 280639289 1250 280638039 280638041
    0x2f0403020d0312020a030b0f0913110105091f0305100e01300506041407060909020c0c0d050312060d030e040c05040503070305031b0601180e0c062101150c06 69
    0x4071401c40a1226040314895091154000351001094036180054503001c0e040c1844880003440c101c00d40708400340c0d003c129003c046644071406654120b00045d00c48601c80c070041e2a1442003032001c13139014004c1400700b20981d004000c1d822034801c0710351f818445901c51010001e01c4500d1402030218000d10000103016445140640005095980221a6408002d4030040d041348a80c01e10540b1181c00442c00c00042c4004080101c42c0e0300080d000801e440d5103032440091017098180205c800e8540c00240c64404848104031440312000d00070420300c581816231520543d01c0d4442c83c0d0358500410070f07100240f07451401c10034002c1441d400d51588000419002d04200081500c0145002401410300c80421503440c00c100b484091441040116a9052441815003015600c40180d45031a406540107104207414410b0340f20503005090008503101035070b50a02c03424030320000010798101c4808140da1050880001d140107407020070380c2820040d43d03200e85100d00200190045640450700b00c1200d18001026 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 280640539 1250 280639289 280639309
    0x11070c06030c260a060503060601051204140f0304150314070507020414010810110315120304031a01050f0406050307060c1103010603030c0201081e0a0203180f012f040302 75
    0x189056500c042814030420f01031458048107084012140d410080240214803070a00502401c8008110354a401c000081403807140140003a803c1d01c4840c007107010051503041400840c00c0e524240d17402d4090100c02e09961340c0061241200129014200d07100c03141c02449030b0040c008514000341550355034550203032000e40c46400101d80080d6103480f00040c00494250f941d002e07101d40f03005403000da400c1d0000002901c0950761a100264001c00511a580744c0d01d000c80503228106407a801c610f0280300140c03600710b000d1580064070100041034002804803031243e03134134180c0e01d04a441d178a40300600b80500c81180c00f2401961b0300f690000320280003081c0078000d00c07000d032842150502c0390701030b10b040828213550b9960b00c03c40101d00014200c01c00c544c0c000781c0a66124420804040c03071b030000064601c0404402520240c121346c0d00002294400c2c7d01e00c44000c0300720300110701b1500c20b541000d41d0b160090000144000c10420004600074000008002080111480500c2c0381c1c00c3c203043d9002c025914403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 280641789 1250 280640539 280640561
    0x1e0f120503040215280503092406011407140c0a090515010e03100f0506090c0a080601080a2c160503031b010b0904031e05030405060a0b0406050604170111070c0603 72
    0x40d404054100ca80b801170b002010000941d99001d440c1c2c00c3c510500d82c40d0558001d034492401441c050303900c4804003003c591503801002480d06030240c0c1c442a108000f20300c10360101511520151004408801d40007803070000410058900d0000d05550b1070940d01190f2094501955a120070201070780c0e5503201303c02e108640c0e5001020384c2c10302c0f1a400060821151440340800c6019122000c010540c42c0c076900b015800250103102d24540380003980000d00ca03840080189052000c1d0001244403403807280c4c8842c00c0c1100028142116041c41e2404500c81692829a5001c91080701c40d0303006629000040b00341221800380c021402d2210818600c6205013501808079002c4d982e85521404a40d500702929000318066100c00706940780e4104980d40c0070512040c1003051183c02c1090100051002480952141d400c490025465802c18001400340800381d00050348410040b6002c07502e120362141440001c03070481c008103e001c00c1c43c030714940940940c0304041c200d2590402d04021540c026080114a42 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 280643039 1250 280641789 280641817
    0x6090501140d0b12070e0f0a091208071701030803061002070807062d05031b03040b01030f050a060204081f0c0906110c031f05060102060c161e0f120503040215 70
    0x52400c8000e0300e0401550300086c80c26840105102256005040c0c450304400d2805007407040c644640c840c9004070030441401400c002500c00050703200c5116654255074802500d125a6080d44d40b0300f81340f601600141d0303030144292a1956403400a9000140c41401c540080b000b82ca26640391050944010701504585400085e05500c51607400c0425080c0c81405141ea0310340b55100d003070107040241c01404180a0000ea07200820078000816000b810341130450b0b80c07101c4015030094692412505083d42c440c0d000f405c050003c900441c12030310101d600380b00301c1d4051304070fa41e610202048010035914400a040f0104502c00410f100052245480741d0354105180225040060800042880c188219180710b0850320030943d41414410303207000300da4105509100902043c2000c0c03c001015100d9940300001d060010900070741085000c208542e0701c4440b05c00b2555006400381040042010000801c54010108210000c1414000e009982c0550703000791010420612919046105520440d0f03109c40c50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 280644289 1250 280643039 280643059
    0x9040b030f06011d0702151306090803011d0c030c03040c030c0f0617072007031e050105011d070806010e210c0f030c0f0613090606090501140d0b 64
    0x68808000500451001c140204415032528800010354604141e0380c0c0741d42a0038074148102d0070b600181107030711008010081584c0703484031100410818507140000302198240525039003804081d4024604a403008001000c5004034802107a048000484560b2000b40d02400402e0a14403108051940a4411200220140d440e40c0b580368500ca010b5205a00f4002c40351030900032142d01569080da5030001507044102410410300281c00750380b103107219904404686800f014205000c100800046801030a114407451340120030a1402c641407009480350740c2801c2c00052200041c2c503801007207007040c40300c00d65a03480d2000e04444207400600118100a10814036003107640d140c0d280768410f600c03000d44a42c41d010407580d8050520054585840c403d0702d808840a419460104c3c039090241c9088032101070413085940000c0d5580a05071901601d250103c00c041040c0316194400ba05861a9858940d036842c1d869004558210100c0b82c1a049103c00b0300c107101e41c038002e03500f20322a0707c0303002003000c03650f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 280645539 1250 280644289 280644311
    0xa030203060f070f0c0302060612030415020303090c1504060509060f040905041109060604180608030c07030501050c040501090e040201170a0606170106090308130503011b1701080c04020904 83
    0x107000019240c0000c02e14810050041030380e00704080c00c01e60b60190600b110008001d44010f501e0311300041070140a401d4100160351820380603c111800750101d10b42d8404501401e1100958030b0301700301e444070307194814511501101d00d01684280a6425007200052416003410003c41c1e15801807a14650440c506004403011300d44e1f0b6a001d00050640c2d000c0004041c5001d041c40c5c26203040341c0ea030b00360103540c208007440120340318401140c0a4503820440c00d070404000d6200e180c001d042a0344451720a01010520304d00f0010046200700c2120b000f14001c3c061515a50146026071140d827141901003880a0400c203c030030031160445070301c10f005041110018240540c0e605200300300301c0d9013900381641c8010504c102030f0400d1030a952009d904801808942c103140c400340a02520f4040641100b1001c00d4203c0b40142440c000c1014200180082c0700c00e1115500480740681c00c458460049042c001c9503a420841c0d00b20312904031040721000340140442c81d002d01000f940280f20b040e400c2502e80d43e005013 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 280646789 1250 280645539 280645543
    0x40c0b0a0e0301020d0c230d0b0307030506070f0206010b03071d03010f0507031b02070506070807020312041508070e03071a0904050c0d0b030a0c150903150e060601020123060a030203 80
    0x114142105c50301142202412000526404030031031000c4c000c2d42920311300d03030260030801c0540344103407180d500004002c080200003034a80b100b5035100626a01c1038908109070203a2015250041c408039800f2034181d43d880d2180348160b808204d07810000079907040c024540811888420f13614800001c0c00002d51408043d42c0b00c81540d03000ca034600c000c203442d40c1c4011141144159507a103441d0462014002c2c260414002030340e81c4c840c0102c0903054043c00300b910429981c4c00e0220a20600c0c8143c000c998640d5596004c4040c010107050020201d00d4803000200d000d4025650124803140080151170000d09050320100240d403441000c030f02501062201c401181c9a07403050342c1c064600803e12a07100c1c980104640182c424428007240a83c1000c6000310004860399100003d854800c0512005440e1441c000c4800003143e50000d800402c000d2450070405c81c0580c01480e03d44140303000e40301d40350348030001603003641d254000c1e084041ba9520321840c80358030160203458100c0001822040380703903079a0300024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 280648039 1250 280646789 280646797
    0x7080421020a110604060203030613110703020d020d0806030606010804140703030909050c041206090f15090c170304180b0301021c27020d0201031e060302030f0105040c0b0a0e030102 80
    0x250784405002c0043c045a0100c083c518207089074400d1516090140c000d40760301010380041d025140e4110600b5001c4000d40110007400c40f9010500d840d0b520728140250b4440010703201d00050b004e80d510f401009882011392a1048101034028034103030b10380c40c0c01140d00d0407001340142c4c1c045619801505004406224030001103000340c0e90410110700b401c0b04401203482c041e10300551620104030070400100042d00f01c0c1140e80c0c020100244070402400c0912904101034002026100c60030009160244a0303401140e040703024100c130040042d141c806804a50b0b0600c2c0450302d0f69403046c8400c0156a048441d0b00303048052003800030920100e5540480d0a903001010f803070805961001d022010109180b01d4214602c1901c10072403d298413000c20b03520550b04048010f40581300d031000140640e40650444890b00034042107034054800e03410b0b0420010617650108030712074041c07270903c0c4140403030501a0500a03a0000a040f502c2440c1c610200c80f150b1010910380c0500c0208100040b07699001e2000e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 280649289 1250 280648039 280648103
    0x402100306091524020601030212030d0f05040b091209060d06031e17090609011115010902031806040b0106030504020d05032b1406041505030a080a0f17070804 70
    0x41e076003407802c0c2040c20314a13025440b0440f58139041e10315107010302540000c015045070740560702106810114600d85066201c1c05898030304407030811280059280345980f05034800c130300a14400b256601d070795003200d07140c022004503590a0041403040d000c151270326100400718030f82501800a1850742c2c0392b641201007020305402000c080c0c3e860000e4024061500454113910103845a030510304600000041d06501035000500c0c10000d41c640c00407840304042203001007944003c41d40c08080c0d0796485002c400fa43c0103c960301c0424501201c611400701c40000d900d4040e990000c1801826800c0c24001c50003050300034010703644040190200d074082402070008050b0400000e4070b10b00000600100070098510105101880c146821484003046190f500200c0e0042d2044070701180450751111418a007540a1f0400343d4180640395a0400704050f49004103422050350b10741d5007502620034000d85921140d484030f14925038222000401c0b940c4103010303990780244280002c0c1403003c50895814a454802080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 280650539 1250 280649289 280649321
    0xc040e0c0309010b03060c030703050c040b130f06030209060301031e02120709050c0a0807030b01031113090c0509221506020a0201090503071503020c030d02030708041a010e040210030609 82
    0x40c04415a0b00303014054071321609070300900305400c02040329000780c0700003069403003055a9071010807501003156003142c0c014000340145c507407100060195006400780360300c42c080024004d107100140d007600034002d40e01d51070700080180341141c0c6152198504004180d010480a031000b1800d100140c1c0c0740e090301042c0c0c0360b4410050207042e05025000c1d00701c40001d0a0003243c04d1040c4040940c00b41e2004220b58000d41d54030700484c403451500010390242c2007142c1134000c40313100460102d45010a410780c25085642c1c290080c0101d8061010940b484d100d15402e25030010800d80c0a040005000400115030220741c485c00607156242e090480e004000c20b800c5030700141c11580704141590317446141c0ca405820701701c0141440310b16203100809100c0d45080500706254011030300800804003402a14004d42c000380e004d5690b441c01103402401200100c90442e031588054410200c08a51504890705030380f9544285490350702c0781e0302007092588143e41600e04254171103102044203584c07409005104491240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 280651789 1250 280650539 280650541
    0xa27090c080a031e02010501140d050a05030f0a0201051602031207090b070b01080f12041707050a030c15030903080f1305071412060f13020126010303120207020f0103050c040e0c03 79
    0x1501c210b10030304e2904210840e07040600501480001c01c5201003e040c00b241c034100e10540a2500c24200784540b44094880d00000c180c10f450003082c90004c040304840d40d0300030411039641030950003c00d00000a0500140e00510004295281500380103400c2803050030404c801d43d50f50802000650b1182c2411140f01c2c4100004000040b81080007503c070f0082940900121681107003500c88500a80c415403d0440d40403a91420203501448010064480070b011000620303202d09040b2000c000c00e10808504449000c0200d00c0c071442446552160355041e61103100c19103441c0c814204141d000b400f0304400d03c4a036000a400180308004800c014941d80442c900d410588504204444a13924060b69594012200b04960b0840a2041c2c550004110080f02c807000fa0500049940782091128540480f50024002250712070034030b140c03030480740700740d0f9000003e98004803540184e000d0030100942003548000041d2041d80660006507101c4000002c06062564880c045c001048040d640c0c6000402d0005c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 280653039 1250 280651789 280651817
    0x100f0209090c030403170a09061401030308060306070203040303050a0504080d02100513020a090207060207023f0c09090f0a2004060503070303050904060905070e0a27090c080a03 78
    0x58581c5600101295802c0c1c00c600c0c0503240074000d132008510a00705441c0c1d441c0001c50305c800340d034800c0c50016080301040190700f50500b00d614501500380405e0340031a50180000e02189170024116105240960140d070034246036540590703960300040043c100740300f0705000c04560210300f0009944d1018a9a00402c11410314032010003c86001070301000038055100301c3e00b00540c1711300c6d00d004221450180010781c1d03803030b413410000024043e0b81c0000707501c0803032611101074010402110400300070b94080c240c5d003040205c1440784580f081c90741c054805a0003003c20341c852442d1248082d540403000e0380542d9040c03800c1114080c00c044192a04440c0801402405c1c442d50381260001d12031700006176010024a8103020020391f0300c1d40188001020402d0008000d5401e4441740c02290080120b08402e2009007130450f00a0f10b407035172107a0540e004aa1280c00050900382980329103149058200c50040e00e0001a00c010000d0312900c0015200c0c060384120011300c0a0782007000407400c600907940c1e000180c03905 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 280654289 1250 280653039 280653049
    0xc1003090c080d0e01080603120f040609140a0302100e040e0115080d020304120606030209070809060f040c050609040603150e0706030902010e09090c15091009030506070c05100f0209 80
    0x298100e03038890b61040b4040084181c2003202000313488401d00741221241e442c0f10002c1d142200c0c0c058088810440485c881c1a21004400076105456003900d500100301c0e100e00d5050321100fa807109803680a4004d000810144c102600059071025161030507490f0b0b00c03221700c00700d0140d510741000c11084da0b65920441d20351040c4d03004400c01034a03d50300900144440644025074a020b0f0780200c01c41c88003049014000c011942d846400103560161104042d4a000c50025100420465401c034090051200040384034480e03180c054070542d80101086a510308000c10b2103441e030000b0741d416402c140d071500e0200201d400b8410304050240000b03000301c2c100c7c41800c02241031440c582c1c40b010505052074080300050382c001c100c031032034468155138070241d640e03070004c100b0b1a203181645615042030b650300198201400c3c680003804c40b800c0681d000030000d8112402119801480d11001d4407a410070402f0a0380036101d22a201211030240048035103048c00d00e21070340d0480300c4c121035152206900245081c00b41c144 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 280655539 1250 280654289 280654313
    0x30d051911030402030a0b07020f010c03050a051f031101140c010b0109080327060f1602120a0c051017090307121d0f0102010609180204060b16080c0c100309 69
    0x1c80301c81c0c2415030800f035010a607a030800d814000c1211441d0400220700e507108020564183d04810024080c0e61031068002e40201000c0d20468400c40c284030000d01040714044510111001e2001410000b91440d1680540f0a0120351030030304011120440c07408202c5240044c00168101d00300026021f80c5840014003e104194080ba40f280c00501940b102c02d09013240c3c00c15204203101030349001030740310303000242c152141150200000c44c01041c0c502183c1a02c4031048060781c402d54884400c040c0e24200f0340c2e980e000741c1400802900321a00c0910242c284204002c003181c03614142801d8000025550034502d010446030120720b83c1c000b003000c02c01c1c010351840d54045406035003894440c551110210104003045805001d02580805a040340b96034800d5005400070404001c0802102100c011034041202030118181e01c05ca00780000410182501c0086440b8132950417002c025144055680310036680016000321864001c41813120303016100c0180c444101d82031541c0004448007680750a2103d00e0f5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 280656789 1250 280655539 280655561
    0x21b01053705040812010303021b030c0f0105090409120c210813020d0b0a0b0415050306070c0f1707030f0e03031b07080703060c0f18050405040302030d0519 69
    0x3a50841005503610400c0c03400001081d0a240840e15583c0c0e4209841d03280f0030012910702e229402c0d0000014103074086681d01c081d2442c4820704044a400004047e82c4c1d0b40d810440c82c1c3d10950781d1508001c03541c0140002e0480320005403000c90203140b86d03281c021070010255101008580344440c400100030001c60007c46056001d08007000d10001604c00401400000702200900708443c9040360965540c0307120302d003005900024407441854076210036009030400b010503601850410f036102481800454a4500741c40c0c001e0005e00e45951200e6046600050061081e40d00c001210010004140da60001c4d0010041425032690380f6401c0389401001103c1c4060441c0c10020600c280c407105079401702c101c0e00804000044541d1880103a460340341000c81380d07400720103148a200302c00020000190403000c1c2480c00ea0326a03c0c00c401120b4400d03281c0d111600840f142c080109c05040c08640382540c00140c01c980030344110780c00d00c201d000000c0c04450040e268035401829180c0103020a40c03d80c05030110041c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 280658039 1250 280656789 280656841
    0x90809090a020f1b100501091b08010b2203080304030f0801051903060b06090a080d200a0f0825050f2407021c0503010806010501050405030c13021b0105 67
    0x840c1c110100014020300141410282c44000d40460b43c290403c07001c445c00c000b4103010031455a440000c400280090002d61448000700006002d500c2c0c0295250b50403110700001051401403044103103441c9103c82c0640c9030311030303100c0840400401d484e01d02a510a030301c646c45820f549501c0c2c2c0000391401c2c8050340480e11079420145e8545520800040c0ca01c03c0742da014030003103482150080018164003800d00465006540880c0c0010302140010344d0502c1100241c458403124032404c58050480d840c511304013000340d846035031138400003042000a81580e80c0544d03001410141066003a41c0c11501b034104003541040304600c18130a200d424000d01214542103002001c0e8860286070419200c081c11302c41c40c0d0440701c400c2c0020040ca0080c03184001d00d0b1a0360b0b0382400b1990083c00003901c0d0f60400c0c0640c41c0c0f2442000004603155000e44110360a5410080040c05041c140108201840c02122400e03046942c0074071804500f000f20740c000380451220b403400419980350074104050007500c0691083e4040d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 280659289 1250 280658039 280658047
    0x3230f0f1c1a01031109030d03020405040c0806031c090e18150106090e040c031703090d1d2205151906090e040c0b03040b010302030c030601051e03010906090809090a02 74
    0x111510b05511861040207080c0031608000480c084a00f50040803042900340c05850450346060b03505078028010350341c0c00c94082041801094003107800e41012102240c050340310000d20606aa61812210450b01c0145040c0001c1912000d0a000084040e507121001e501d60241c440708501081c0308400d07421200501840c03c0750302d000001441000144999000b0311071003000708090040c031035004000381d07401c0000341d000c007901c1c0c41c00003056a1044507403640b14080e201601d0320f40341c401c01041240c5016070a04c101625010f0040017403560340e6030000751402c7d1044010050100060203228030507003a1804960030700306000c051000c540020781c880b11a10f00c02d80c800340710382a045024002503505220001c40c941d42c4a1410800720001a0042d0040241c08000c001c100702d440c00145058a10a8080c0c0e401103046105155640e0000c0c000d1580c40a1014804400801c03180306e41c0032400301c001c001050038001502ca0341c0885024a80a4445802c0040c1420762410441006500440305130b008600e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 280660539 1250 280659289 280659311
    0x60606200c040c02011b050703090b03010f0302010503090c03010c02061902030f131e0c050406080303090a0803090c180a0b06032806050414040501110703230f0f1c 72
    0x264801c2100031403207030b40d5035036203000094401d500100c900350b00d00219084544c20751002400903003212004900050510310041050290641a20b0490303511a030150541070031540151103641000340381500510404400c812250740c2400354196190298020b0003140c180310102c4e050985081c1d003100b019074010010320249040301c20340c66600095001782c2a084071035904e08007454418003800c414030300c4403408009041c055180c0800b812900102c8081204990350b00034070381c50740012618861240c010700c0d46600801d2611004541c000805d00030f403103000720900000f42d4040303e204c0d01355050300070f14400c01c20070b901c1340e10540240c01400c81d0070030b06614200070600070f1100074080c2d10704024040c40c0500c040c00c05030b800c010080c1000030400e020031900c985410025080c100c8003a075596003000c02801003080c522088517407450700b6070340303501c01c415100c60040004500301d0f007041411182003151a103000f00c242c0143c400d40032014440d643d00c603042c1d02400340040030801e06403074952a182038107036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 280661789 1250 280660539 280660543
    0xb072d080414010605011b0501110301081b010306270608150f0702070e04030f021002070305122d130b04080403120905010f0e03011b020f061506040308030c0d060306060620 76
    0x18640d110103202402e1f40c080c518245001d0b04403003a107502061000300010800301d5000c20f80e41c00c0b16420302150302c141c1181c400114203071503991241c058908803070764100d50b0340d001c0c241783c0032000e40c40c0c5280402d646035214006442c04405a122007100c80342502401900d22215074180d800529903c0100809800c2100c280c0c20341380080e000a0910041c0420340c844c0a00901c074030540e890058804548504141c18081e1940c0d0110300380726454001040060300000610818011061045850004219000303107036a14555028010104121001d211607000400c0294458401c5204086035a20303941b4600d0700701000e00c1168188818031280f210140080d90b4070046401c11414a8a0202c00003444d00012034010060000301102e800c40a102d400007040d0000b544503207102e00c0c6000c56560b039850004007a2001c03d2114400da000c4804c2000b040802ca2910142d9000680190a00d1400c42c00c042c4071030403107419601c101c0b40181c03134800400c04240c020b003d0520038501c042000065607131203400b1030307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 280663039 1250 280661789 280661807
    0x3021e0916090905070e031606021f090b390307030f180305031b0301050d02010e0a0f03060902011e0207300507050406060c0b072d08041401060501 65
    0x450060000000c002561050b01200010724403900d0410081c140403500620000c00c01c0b414034040c2c403a2028111200d111200444216030403070b4090100c0110450403202280c210718146100942c45040c014003140150460341e000350f101400c440d0903048200e008a5075040c1114004030154055061801c6c13001c89181160b5200c1e259140008030310b1000f0b40031900401c0309055001c1c1c100340420303081d8205a00400214060311410204408005150110400e544402d019658028110087e1040103500618110300c0c0c0300002083d0503900c503182c65911980d145075500681e80c041c0c944204409558128a0842008000d056070002d01d081d140d001a43d50f6600d8400c5060b030000d85080e030445001402142408101803a0b041483c1021034240195a000781f4010036100d540780c5100050b00c00d01620446010a03031020b0107148542c1e80804c140c800f40ea00c2d20003404001406005600c09400300042c0709080e50264a4100c29070410703081c12198085446410600c2d60314018085c0280c2ea002090301d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 280664289 1250 280663039 280663051
    0xf0906080f120904140f0601030f09050304030834020a050105090d0b19091a06030d080a050901060b120a110c120304110316080c0306010b03010b07020a0e010602010603021e09 77
    0xc0b680e607001e008041402411404030a0400c00550004e01103e6510094490b008040903601070018101d842c0703000b41155141000208194400c00c41080052006400b406604080103c91804102d0613610180388507071401c181c01c1c0f100b01e1990410214a03010b640540508020300c0c206040c9418400410404526500c014012404210014901405031075181410803503484d03045c0a8415107191010140900311803c100304c071850b4002880c039040005030241290119501d0132100d4481041c460010701001c0d0092845540701c41001c21a030001c40020f000040340000107103414a45042078078115140c004041201c81c90802210b0048180011080f4401d0a850003107680c98855150201540051880198041c0143c000c44e40d1215003500c0c1100c02c03a62902d0645640e121034500301603c80809004038140d0000c1400144085055440600b6000f8070103071098119644580180d46d250a09074030440040c0e440700020310450409501d200b048200c002070980301c0300c12490010712948802800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 280665539 1250 280664289 280664323
    0x80a06060915090f0b042903010506030a0206070303142403061b0a0306030215030108060c0a0906080c070b0f07120e0304030201080402011205090a1a0709031b030c0f0906080f 77
    0x15484e00581c450380910b42e03201d4028002c101c02d07200080041100200a1140e140b8504c05480e60042410103024891242e00011f02170000f020080d800c11070f16412524042d4101a99400052600301c640c000d414000ca0104131546c83c4c0e98079510701c2c81e0495008a1840c0d000350031110038003a241c0d42c002540142c055030328107040e440b2240c05008500404590340040d40c0f18510b015050424540d400003503043e103440030140d4901d50f0b100b0560704c1e480e100b9550008009002a0410000503100e900480c1e040600c0115003864501c580d2685081da6106440c000c249080103070030f00c400c01d9040440040c03070040c41c03a4180681c41d10ba83c0c0711a1640280d00c4064180007020001404581c8121b20103078a0228a41d0200014100319424580d2452040780403160029106215407207401d0036010a8412082503941c201c48034156965020783c40301d07860003075103124141140030000402c001650300c00391844d0003005040a1411030018181c5245e54444540e58021048000455a0106011102980d2024 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 280666789 1250 280665539 280665551
    0xb04052a10030e190c050406060212092b030305060306061012021b03040305010203150402041202041e091a0c040608010608090a0210020604063608070b01080a0606091509 75
    0x1503040d081c07594a4400200c000e10130f403002c0003000310112916003590000c2d2010000561541c17016652683d48001980e0100300600101000380740110030503009508214114191000c484118451030310240c1d401c40120780c86400300001421704000240e805034049400001000500002800e800b00d40c005c01001583c0008070001103110901c014013000c61024101ea5030f0b680d590614030b000350000d56000d101c500c3c51084801040c502070003030300c0a40724a450f080724203050326820800103045030309100050400e00c605042c41c460240c401c048204c1d001703400c6000c92a0103103401c40c0705504000c2100b48051001e210500c6820b03404400302e815900c00c2e003019506602c0351000c0130303d0100c410303400a41c4130014081c0c0303461055000c101d460150340710b001c1c24824401180700d40b41c4d140507032501658610306e2410950010041c03c550f400489400b86948903d4030081b6204d0741c1c19030809030413651455000d0a240f60422050b403050b800180b09800e4200201122032884689081603446007000194680c2c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 280668039 1250 280666789 280666811
    0x2805370c080a0308010905010506031909050a1b050307120c050d0c1206020a032f090d0f06060612050708040807082206031d0c090408070b04052a1003 66
    0x1140050140c01e4000480c0c0d100c0101e4035005040c1d4209002d030320111410180000ba0398108841501c0c0a00e060030303e0a0a1400c1c1e030074061000b0680c1d42402d50381072180040b0b41020412140301600f42045850286c540603052a0506180401950000520351004216440031803404840601a12000c4551401c40705541c2484000d9608680040151004402d4088100304403503000301030342c0d0140d4409100c1345403401b55a0100720500e0b4103100ca00400010b00c1a04003911301c2c000c00042000034002845021144c41d000700d92000d10f103040716455501c403c00d00c01950044070803044512a00020b202a142005000b040c131100a03000914012020a520042001685c00d0f2132000003050340400c2500e0b03c1070411801007040b0b1007944003080ca00004440180906a20301d050030440d1b1004240d04401c5900b030180580c8001d005a0385d054090142000050380c403103216002d41e0294004241180038820500d1440714030342000d62115255070b00d01c0032182c94800300503000f08114140018040c00d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 280669289 1250 280668039 280668053
    0x120213021608031005180f010b0c01090f0b1b0f1c02070821090d091809120503070305100302031e031b0f010e010b09011502280537 58
    0x1080340107102c03a902100b00010080d149560b00b04036001100e01803550662a0782103050a5800d44040ca06002c0c1c0300d0051017964802002001d01100c071200000e5040d4582e1501060750030440d10071513142c4496014400200c0c42c010f07162406c2c5400200301c40c50041c0d24456642540300d02182c1c03641d03070a002078041c8038824403681a00e86054010307400f19541c15a4034030307450604000304a01700b0503002c500003045814400148d802081e0b201c640f90303d40500d040c02e0401d41b40fa02c101032070302c048585802080c80050304110f14590a01c180e9112980c6a007405000074041d15801082c6a00c09100d01c481000941d800040300c4015154850508480c20708032285c240c11071060200300c9081e52100c021003a042c0d9400100080510111802000300201c0202c006080e00c000c820080d5100c1d4141e001031090fa01d07682110300300170a60340115800f003000030800000c1400710b100c0c6010750100c1c41d000daa05000c42882a00c48002d174900c001d440034201c45100d152031003422072000302c207800f1341c1070300004015003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 280670539 1250 280669289 280669327
    0x103060f1202060918070f031104140a0b0c061501020c221401141207060206010e0702011e0209100c0308010909061d030a1704050604030f121109010912021302 70
    0x40600005c401a81010303aa08220809552010019141202d10080307140302c0c2c8901051021120002841c20b8504210544010000419564040c02c00e020008040040b000100016041080a00610b240c00311320f641c10240190702c483c0c1035401c1790035812015a80d4040c001e011004050360218190104001031008100360700340c014060040e0000410400e0020400004180048440e0508203054149080d01c1d000d29101e82302c0582e010741c0040c0001c44040340c816501002520000030180085900c4a050f482441c80c0d0b5501c0503400101170b016424081d000c0e925246030750501942e0380c00789036001040c0c1101485000c007038a5840f2421420081590462400e18002201d10200c030307401c854500e9180d034041c0380c088000c01e0008407020801c0b190000100e2042d50448060113180c1e649882c02d41304c05020001c0700081080116224420310790b144150209030340b58007401904c640d010310015010383d0040d0003500842010006240c0181e039241c0c2c100290a03070b10b6101581311302d0440810084410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 280671789 1250 280670539 280670557
    0x7080304061113060302091302040f0b03060616210c031d0d0b042901060e01050a120c0c2306010b09061e0c100203070c02040518100f0b0103060f120206 67
    0x14403103c000503030641c16005481c2c82c1c1c038101d0700400c0b2007030881d1116080344107600c1290fa4848494004000300304400f0003459003c031024080911740902e0303080080802c10b00005c00c076101e4000300d1200024110303e60305001c01301c041e810040d208082d140c81c0500403200115070003150103c580300e400b1701515152108030419600101809083c01d141c5405140b440f505070380360540d10290410034021302c110a02c074030304855140d22180c0ea10070102004441591000c01c00f40180014080007a030000310030b100340001441c8694a00c02d02c01054909040d80d030915245941000d21081c150b4200c500b004101a0304650189110540d504101c0010568901810070002c02ea1444a041701c00110250801400c0d01640a03007607880d00079204852504a01058a14000140744070602e00014103003980100e406c9030300f03c441c10f02c1d5003a44010140c6401e880808520400e6111020101c0c451410701501400b84024201030007911b00304035207000c100740d03984982c0007100500c2c4404800c0d51159800c48203c84 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 280673039 1250 280671789 280671817
    0x3060d031b03020f0d020106030305040b090616050a142e140708010f05011d010507020a17030901030b0306010e040312140c040608060108040206030a0b1201150503060c070803040611 80
    0x10079414080c2d02d40d107942d00e101540e4001d00384918206407041c40b0383c400303503941a01c3e41b500f00707420050015901e0304050380c03e5400040070807440d0307010443c002907440032a1040000b007504201519000034151050201c20140c1e902c4030511442e040410846404001203149c0b55004c50840c42601101500c1c00001c0403c4544442040c82a600e80c085641030585124250000f4542d64840046507030f80c40505060b040e4030322012402086603c80c00c000c0250300d00041142200700d0b104d034102c002503c03003000804099840014590700319600360051100002080b8084c00c0e4962615110f9000d503407000380024100090200b401c0c0204040d03510032400c40c1211646200303640381a1000010743c1d8002c1c050780c0003003514040014035541c1b24246442c07140768050f003480d0440d01c5442c14107000e007554202e41580400d41088000100c402441030314801100810328600662800341414185140030780130400c00b0b1003c110b50008200d0100881e600030723500c60800258042400300d582c4543c050648005289 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 280674289 1250 280673039 280673087
    0x1802091503030d09050a0308091204050f030a0203070b1b010204080a020f0d0605130c15020d050a03061e030c1703030f100b031e01050a030201021203060a0b0f0c0d031103060d03 78
    0x1001700002d803102c80724813036205c0340b086844a40e8240d540d60300d03d641348804100100000c1c400d03070508540e400308a1034054100c40030252282c1c006810444513400c480545003001c1030f1902074142402c2e1442496140d03000031071802c1d0418002c151107802d1441c01038060488040c0f0707012142c58005008040079080107080245050101a146010350746001c151540c2c8901c1201140e040c906072581503101d12141c0050180514041054030b2540141901c102456540d800002d4020901341014200d00681c1d0a4600070031f040d483d2400d42840f8507081040004034286c0494002c8400000700c903004100b410101489641d1946802c15912054021075400c400c00b000f0b0040b00300c0c2414840d1102e000c01c035404180c0b0b81c0c0300e038140000700280c1d100181c0140d02c4049920f503511049001190030940c05045d00302c006031142503050700360f03010701004044e40c0d0700010601c10004091144a13894101480c1c14031110006010300700da01e0002801c968460a035240e614410580a2110307400b0310103074001184d82d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 280675539 1250 280674289 280674293
    0x10914041112070503040b06010302030105180907270e0705011d030723030c010f020a020904150c0f12050408040504020c0c031b04060f050108010b0318070902070203011802091503030d09 82
    0x454000b540d044606600407c0418515802802500c0c141c400141100d0054410001c08030701604000d02900a40c0c060390300d011955401107111541041900441c011064400f104503404840d42c981c040b500c2c075005042e0a10050b0390081d0040030303002007903c000e0184406000001d0406540780d00c040c060700c482c110f0000c103d10300010f02100d4ac60048040d2203d1141e40d40054a070b44218003090001a004070403148010700d01040380310381007805044c201d0b0958004e00301800480380014121004160301e01d040e1410517510a11144940c9000c01050140d402d0540e25011940140d014481c46150003184440c0c01030f02c10042ca210801c1c004080745c001c8148a4852908600040c01c0580280c1c24890045520311440c60b00c442140c0042e502c880343e581ca011700c2194503403c00782c51700315641c4040c1c1d04404030354020072a19018091141005a403000144100340c21550990b98450040d0690220100541c0c0c070388241c1940844042e003030915620812000030b04600c14600359911240ca40240902 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 280676789 1250 280675539 280675547
    0xb04140601030f110901112d0601080c0901121a0c0306100201020405100507170c0624030c06030606040b0414010e01051612090302040219020c01091404111207 70
    0xc0109800e032010408400710416501c1502c2c040f1042c5660708104010301e002a5108010701100781c540f0405030f80c001040d0f100090f446030b41e00c20701d040c101ca9082e40d40c120b00e001c1c140055801025070b007009051850521010907480e0205104440d003401c0080c1d10401807008203034500e031342548400c1060120785001c0403004440d807c02d40d003190203003400c94003414200780140308503000d07910000d101e01c16015030f440084a00d54052002100d0340444003400003440880d00e0003030404404c892000d48080d10b041f029000d24280e010b03604499800c041440070b119510301069070b0150b40000d885185e500d039103031804100248030b80e9001d045040c50010b00016440742801002ea1421310980e40d802c01201507500450313141c000c1201c810b04081441010f03000190040a03110a4201c10f400c00600385545ca40006040360888070100e518101112942c560055041c4040c0c50740c48002d09001c9110340c149a00d241910503401d075510701503980c07000c41c203140b040780c034040c0da0404075031520040340c510744008024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 280678039 1250 280676789 280676791
    0xc0f07080f160302090a150602010c030c09060f08090c10021b03060c120a0f0c0503090d091820070c030b0109060b032404021314040527010b0414 64
    0x41041c014200c4401c10200302107410b02c40c402440e0380300580c03070f811a000c12407181009406c01d20303c165200d90300079004541c0e454500052000380c0002501120140018054628442101d801c10640030000c1c01015000303011085144818585540c0a5a44501140c42c2a41505206c0d9002040031111041d0560018003107101003502c5900505a0414406240c1d07184410f4030084030000c0d0030300070b407800d5212b40990b003644500210800300e0307014214003e00c401c84100410800014100200304200c039541006540b00401d0340d0319000706042d103041000304e040545c1200c2110300ea43c442d800000d50842c00e1040c004400011204030b555a416031403c4510703103e452004940ad2150000001751101c2284078510450300b0a000e50b40c41d40d13551201881d98001040c080000300e45e00d07007078001c206458034800b0300304c000000014404032030304010b00c0a10055035075100d00c0c03086050008100312041c0401100303111034803803420051a0a000d101041c05808007404280e0000e1030b11341c041d42c101e03040c89191 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 280679289 1250 280678039 280678049
    0x30315030b070c030e09090f07080102040f12080f030a09020f1f0507030c0c08010912020f03040308031e040c06020c0f282d05040240080304031202150c0f0c0f07 71
    0x1519215900c0d5082b600342d004500c0760b0850401b0703e80d001c12910703500e010042d20042c07245250701c1c5480c032140c0720585660070035280225901d0b540c480c2d0008505042801e0144207408030340c0f482e842c00001d481c1c21041c000b40050703a8100940450b030381d404c140c0500c03480b0088681c0710b21001c1106031159561802041885d60a6440c04010250070303214074008147d0704008032112016601d861b0654540e60b60300d80c0058100e88040c094103800f20880c0501c0d001d800d01480c8101407072052240350680084c9003d5282d0751040c0304107000f510042143c2c0d6409540d65411000b210301c611040c1044400d01a50101a4000c3c00035000300b42d240c1500000a07189900c10500307a07032540c1e030020b48500900c8100e0145980100c80c03600103500b86810b014031039030081100c404910b02d20303c1c2c05604031040420b0315100d80c0860304591021a0a00409c013070100100060903c40c4010200d4030b0031000307980c5440c90301622403080810300007035515030042041c0c2190749808280e0300304c44121140f0002595107504501c55 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 280680539 1250 280679289 280679293
    0x102040e091c0f0807050f0a02010e0d17040f1a070201020c0111040302130519020a020c210631030f02060a2c03090913030315030b070c030e09090f 65
    0x20300401440c1d019450400e04280d580c1c44640c2c0303102000a071508000a00442c1c2404030034446504021801c100a08c0d00110550010594006d0701a2903440c0284000c1a202484249111007002012a009499000744c004400c466040d031a4145444044d401c1c045400b85000c81c00200001c0f00e405400911018040000801451040e8030f510301c41402075010095002540c4024030700c46040542040d50051800e41f9111130141800d0031520490744595416809608160380a04551030120f223070124080080d043c0111290f0307140e0b003203911168010144801381d020301940c481d07040303450214158a4001c2c50760300b10340b008031820054400840d01c10824010711441000840300c107824041c0d0264a0706100b100c040c07004981c0100032003076140c5981303440248418810100c80b80c0e28814054091000000079280001c510300b4000c082d2500208140b51400c11502d0070400200714100455016031607251002d498285854100d501401d0140c5442c1d01034051030a2151215001c2101d20a001d14002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 280681789 1250 280680539 280680553
    0x803010311010806010c0221160e09060c04030b04050709020409051812090f240319060b0403081c050106020c130603200105070803010905220b07050903030702030102040e09 76
    0x200450b0803c1003101e805001614440150006050044103841940071112202c3c03c400c3d048401103203441c00aa2200800d40389044041191000c0120746942041100002c0d024625000c074030408075100e40e02c001045058450002010f1100078400b040103425108804c1d0f5980c3e90b5080c0c0f1401800d0240c1346442036041144a0301940d000c0042c0c02641140168226801c12240f0800c00144034090010703181c01541044110f800e550000140120000350003200c2c5899040100b8420004110a07004c803085901d4540d003803000b010031205840c00c80380d2001c00280c0d944a02d05440692070072890040c2406410b01d400415202c0d0081071010000c0420359040d00c2584d41a5a0749080c3c40f240d100c007818681c07011603038510800c5c8036950441018010705050b482c180c425901d5503543c0c0d000b44c0c814880380340c6d104144030b0700c1d40d22105a50003840c0020741640022017142c070ba11806440260128041c0500040c0c005681e480c203000b0b44401c550018000c40d10780780d0740d0b0618034070002c003128800898000c2d00307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 280683039 1250 280681789 280681823
    0x903120901020304030c02060f090303120106090602060c071b18050a0c0507020906060a0e0a06030903080106090b0a120615090302130207050706031e090f140c300a08030103 76
    0x110070780c4d100c0c68150765420100c012640902c0800c0d88500a010300c01a810000301ca403580b82003000306540f00170b000800095614048000b444070303001d034100800b1500000107200c1c02e44451010f8030708494028a6014500c8132a49248002140f15400540603c2e0b49204900d0142d29951003e886800106814000745810460443e564405c2000095005035001c001c5801703804c1460180030002c3c0e50307003042c5055111050014030740d11201e901150010b07850f01c0f0044200b40c0e0003480240100701d0b5050001e040c5003012882d40303042c09500d407103004101c140c081b0100c030307820344d90003c000070554049951161090000e0040542d4150b000682c0107010801c2d00140704a014800c40b000c19404c98050000b0500b0904104c001c1c12401e040000818041c03152990341070701e18400c9040c807034407400d00c24105821074a44288643c8070b002c3c03921419005050507401c51f403034240d078001241c0340040c442011620004c840e02c4903025020b4403060a031080340d50480812514000540c140c0b07000b258510301807000380d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 280684289 1250 280683039 280683041
    0x1170c09090703030c0f021903111c021c080a050c1207170a0c02060409020d0b0a1a1b10090309080105070906030513021e13050906070c050f060903120901 68
    0x15607550365a075002d4901000464810803076103490503c1440041c25074019038001804138019001000d20880741880100100304600e0510000301e0000d840c00e1701c00c0740301c4291113500032204071000780c000c66005002c4405c2c00c0b4180d050706005580180c0c056251040f004000344240c100165090300b0740b240c58070080c1e0b00e80610003a9910542d1120070010140c4040c950340c807042d044030003c00d003802004003007180180c2c0d8020162026140100300180c80c0c00c2402101800e6034010707920b042c00745000c0740c0305201d446100119900001c8070900025038400300c4085682c200304005c0c0e107001080c02a81c40d10b50590019400041708540a5030320580525200e00d061401c80e0815a1914003046d03030140d081141038040e0304150380c8007030146c6003204003480540100b59820980c3c0a2a800903101803116074043c6041c440e00c6000340850942000507250024210365661400751400c0b00380002d00306400c0801000f0808918481140130075030f50103050404a0a64a0f0000d9444552045c10500050340150301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 280685539 1250 280684289 280684291
    0x4030503060312070203031b0f0304080105040b150315070509130b030c031606120603021210061208071b12050708100506010518040b0402040308040905010f0308070b070306030b01170c09 82
    0x1c0207149231400c204e0321400005a030b00071000880c0103441c56484203a0041c0084c100070b0000c00700100c1d481c9410314240070f109000a01d024425004c81c1c01078025610001140c082d50101c80c000410b680d214014156410302500013900e5000011281d40c000900c266003060680320000d030121003404500000f09911042c100260411060340d804080240c140b0465494900702104940091034075243c0d0003040c00c00761800c0203400c250f8801e0000e0742c0100c9151042a00405604458210801c000e980c1c400540c49419000b0f8200d00301200103081440607081c4580040400704240c804810b003130303d00140c552a40d485200014003450800c951882c41c903014175480b4007030580d201e91504a4828020103990004610706070060b80d600038041d42038845100500156000314005a111031800c0070080940300142c00c90603a06c0700c0c511040000601071415908450303400211488180c0e11804110f00500c2140e001074500021200009200d40403080085900323907840c1c06a82c0318140318018401c80c510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 280686789 1250 280685539 280685543
    0x1020306031b0d0f05030909090705030d39110414070c0303060b0309070528050d050102070206030403050702012003031311190f06030c08010308030a0b03060403050306031207 77
    0x202c00c1d44002c440b02c0c07001022103940700808035041407941e0707102d809204442000c110340329400028142a5442c1841251358004462002001e902e4181008251101d03141100311041c003407483c86042081d081d0550301d00340030882007600704002e240f005c0034560001a54405441e00f4184084400e0641042d014900a0200c035070300d801a1a00c4114007108c01c58a070601c254105640c1e1000070a48880d000300860090b5003040091840f14141070030080040e0041501c3c0203001c1c860445010411140c06022088403400c55229400d20b8182c00c4c03050281c410305000035030011000080000301078000010b8502603000b82d85012246001041e0a02c540100034200000e0380d006000041941200089070b00c1920711624918880c10928400700f860201007040010741f141e0215030900c00b0340c805000c100001e24182c40c080c8002d440140c0b0190404030103000282503c4000000030700c0a003425008004202005812540e00e4030f00350400a086400645009109000701422203401c0320058054130743c655 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 280688039 1250 280686789 280686793
    0x705040f03081b07140a080105041a100b0406050d1d2121010e090303160516201e150d0b0901030501090c0504110a0c080f070503090405090102030603 66
    0x3801e644490840e50480300468802c101810300c2407111040c14042c01000344468410f40705075100040401c01c114419400401d010b80c580f000300400319903181201e42a0410106640d07000351110000ca1900130740640219200101c001400902280d02100800c46a0140b000030400111000e07040742c40d4007044580c081256205103101c6059001c00090704044104103401039181002ca449019403044a84010b58000c0754600010841c01c81840300c010740c4481000301551071460060f640c80c60214901c0c5001e8101f10000c1504190042c204807422003503900164000d0a00d4000710780d00e006052901119401610034209420b46e440000c00000350381c58000b0301c0403440003032014155210350080800842e0b0f0f00d484560000c00e98440303250950181d4080c100210704401c8605001a01b400507500c494015450852400030b40c003c1d900944450101d83e02c2c11038038803007040c1400806401011200f000300c0f94001030038020041c00000070101254260343c180029a0707110112802c0380012070305140c2603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 280689289 1250 280688039 280688069
    0x6040e010504052203030b0105090a03080c0c0604060c0311011d0c041505010903060e010906050106121b080f0a0b0a0603091a1005060a12090308091501080706030b040f09050a0b070504 81
    0x24080c7e0844000d140043c0350460420030b1044c00a40058840e074000c1d00d107481d0004118244800510040220030701c01c0e00c0c0d072407926140800080c0444d40b0002c0c064200546495022003149003900183c0c0f1100080340e50801c00c0030346a02458844c80c4891504d84138510384401892441d40340c0c032100048031016151000024036548440010301002c0100d5001c40d5620212a80010344a101d45c902070915a950300c0c808048003000d0f9022501c000c0c609401189003d8040119980d110450039800720b13248480d05860b840301c1c405540601103902d4015844100441e0104810b9810f90020032103134081c800d04901c002c00c0c03e0880841c80000c0da0900304508544100740805c0c10f00000a0001c50380d145400221030f03090061400868011800c110001140d041c14062082c0e020820109041c14048126255501d0204803a5640c0d40c1d0307104601c20f0ad80c8802003690160741d40c0c0d000f426446d02c2e910341800000850300d416a240e021719841200c40d001c241012440b820310036420744050303552003541c601d90 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 280690539 1250 280689289 280689293
    0x1090303022802030d0e12070e0402040b0102030d06080303160810140d1b0e06030d083106020403060e031903020d021b1c020c180c0906040e0105040522 67
    0x41c0b8105030002003a80000b401041c00588080020416106503640c0d60b24104801c4810001e030707a0030414045c4690b0780084e6092001031b406855071504141e044400040204040c0010317411405813106000d06a40341030b40020700030308040011071007800c180125140d49200402e050ba0354510a03141c0e03140031800400107005e00907448801102c0b8020060242144441c0c13aa10b082880203000c089101241c804001041a400d80c00c400750780010044000d4450010543c50082c84004001c141090030030f00d00b69007a07854480000348030003060a56000720440345e26802e03c075000e90702030300c801c82e000c0b071801c40f00504d5101e0100c15a0481c4d0292820360009622712034049000e0340000c0c00401c00c59908000c0c285502e10789200da90324600e2402c02508801062004c244170448141980c4015500000c400e100386030380782444061004c4d02d100c0000003544640f8a224010301440f08202c1d088580050041100c4080b8104a4122201207a05100a81da25030000216085400c8040b5001c4c03690703500d10f40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 280691789 1250 280690539 280690573
    0x3050d03090b0c03060d08041e0909030c02041e02070614070305090d0f021005070c02090105151c0f020309060115050a082e0b090405130512030c0904060e150109030302 74
    0x107001000204040908510351f12003882036071080c2d01c800c1458042c0b241056a10390800c000600138403c0d9003013002180c066840181c151440315100134482ca0740e40c00850010040401004514101980c0444d2104460b24100000340502c0c00400401d44200c0000341e4001c1c800d002d000e10030b40d41140549800c414202050f10303440c0c00d8000000660080d0040104801030320300ca2940704030b4090351000300c174110500500c10002010307007045014081740881c40c500b490000c411503190b459045240114400e206402400038203002c4120040d04e4000420301143c21400a2643d043c3c40000c4003480f41003412180694076886901071210106003101b0000b0303604603034544030a03015009174041c0d403030040c1c00c0d4600b00301ca0403042d00210395289012070044541d0405200300c070f500c107140004000c0d01440c00c0d1501381d80e844503910301703000b480030000001d9080941101981c0380700c000034005020707098541002c040607080448940d04141100368813210700d0344c410841001202d03015000340045080c1e00300c80c20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 280693039 1250 280691789 280691791
    0x1030b100c0b04030c0f0b042a050f150d09120509130c0e030d030c020c0102030304050a24020c0318040c080a150302180114010c050c0609010c06140103050d03090b0c03 74
    0x14040c402c185440c1401b00e01d00300b030150581446112041241c1c5000d1a141c181e40801502000180e20b8031081e4102c2256401070000941e40f003240c0c4110320001d4000002c000c16122014218200b201040c1010b4002c6250006440c8034400d1452120091000001315003500800810310790005010395a01d8980d01030364440000e0304a24901186140300c1c85020900d805400307800070002903696001800184c1e81803006003011007091002d503146050540721141e490480d5a00074248e03000c0002d0500c001d4404001000c01145080303015034072000403180143c0c483e00010510b09184041040c02c40003458180700d402d40b0401e250700d42c5000b40d102c00240c203000b408000b10034042892910008000350b0364088910740010221a0259480d60520f1004925010160103803030621188450504c006100844c05001c1d00a09a81540e102d8490000403250000d5241024041501d01419405000136501026050340d004604441d62084000380c100c0407901c4000c406054654001c001c1801200544011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 280694289 1250 280693039 280693043
    0x181b07020d02031c0e040b060d0f0b0a031101020c010c02060d11250c050d03120e0319180b03060d0303051b0c060403020f06010b0a0305040c0e01060306030201030b100c0b04 76
    0x140344001d40c2e000c00e00d0050070344d002e01c1c90540c08195401000e0b5020010036a034a0064506000c00740c041c201240242c041e400b07040d011a82ca40c40301510300c41456002c0b000a82e001001d8450340c90796130030922a00005503200c94018081d461a15050b5400349a180203083d5000e082907142030303c41c120f91801021740320440b1102e860100b001244000718004060011885a004900700610503d00700b08020b600d607000b14010360044210402080c1c201074198800188440c0200b094040d003001141903203da80340c5440020280061000142d42c42400240c0d404c0d8000b4074001815100e069412103400300f102d00f550310030303003c0740f03101c001a10903040981c001030a540008901c41e0002c000d031002c3d403c1140c01e401503501180c100801e040c0d040022064003400140940f5665050800c0c02c4054880c84c004a0145620303000420200a00908010006d210310540c01a640d619a01c005024048602c0180e00080c00e24611101720301d4a80000c180315616030710355100030171040d900da038a044001001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 280695539 1250 280694289 280694299
    0x303190903170a0609051003030f18030b010f061b080d0f18080a0f0c050a11060d0f0e01060b0408251a0a0f230309010e01060b0306181b0702 62
    0x2c2c0d068000400b00b0b00c501680790700700c010074190708202c035100458500810102e04606841010800701e46c0102c8040300302d100324a0480300200c40e84407800a081000d82c4002c0144422500000e80f5610306903884068030740d01d0f550300c140b03054089014403c0d139540c007201415400c010010040300070615440403400760040740e408544400d099a0a40c102c084141094072844800500d4908071584034a90454800345420100b01c020303107a46811740c0c0d8804281e8010910500c1200b001c01590329542135881c4040c203040240051150031980301c02500024054004542c200000031030300c0154402036030305541c2008001c2030b81d28a5120b029455440e00d80c210303e034003041310308046841b00d00105e0b0321800d03165103a11280d07602c0320202e00500600010051404002c0046c10341125501d0b0036180d08018107a280d04140c40c3c0d1100c03414640107001c0c1c010080300c2507181c60400145440d00d6800707184528000c65001e960031000c080c100b5400f00044401c07803003c1f24003c103020030542440c0e0140180c0350002d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 280696789 1250 280695539 280695557
    0x51e070504020d0c030e03031b131212030506030a03051207050c0703030302090f09010b090405040312140f1008070603050c0d020301030f0b010506090604120809030a03080a0501080303190903 84
    0x10201c0c0c200d9100f104050070944c0c59243c1440c400f509130052481c2d00c043c0800840c994030b050504075130b80007081d0b0f84812100300d00103106440480541003410103858038070111922048646044041c04a4111301500480e09010010b1034514002c501c4c1b0f60010380648450b403400142d2a0b0070284090b0040a54051000600c071360702100b5820064240070754843d40700144e071802c80b441040320300010007919a100760300c018014882c0d6400704027901d500d0b42040e500401c00c0c1d01d651070140d80d125041d040c900340080c030b0940010103980d50a40e03003500525100a5415250300c50808034000310406006610555020b16410050688240d03c81c55001041e04811801c0a60440000041e03900c00e03481540d00d02c034800c00b000140442802020300420084407440c0c90070b0742107008144140102c1c45441110042c20300580140f090007401c9074000c032001020740395115094a009002002c3c1900c9040400d46070ac1d00104980700d002040382d0160442ca0500c00100c0300340030b209009051007000403410444000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 280698039 1250 280696789 280696799
    0x1b0703120e2d060103020a03060c0c060e03090f030d0e093304051302090a0c0c02041515020109020f06070f061104060314270f030705010f0e0604051e07 67
    0x212020002c8424600c010405560180111106051001c0115102d41008004000503a02d40071b0600c2141e40c043e0f00031542030f820420603210b150030310340050311041c04d2407403500c0c101308003100524000d0800c0381c100b2407450b038427014581d0b28004580150041010300c655034001e860200d50a41d07110703411800e00785036200b05030040310700550110001c19030a42c6070080d410080c50580101a4441d040c82034610045441c0c1c0c00040b200c88014001c4107183d6030301e020f00b4405511501094650036000f42c414403404211032041e070a800f0080c8600452040400031400c02540306005110046030001c05810b6603a030020100405070348103d10031548551015180000180c41c2d0103907012184294401e13a444a20781000601568000c2000c8200203c1ca9010000110b20469a0310b00f05c104400d4013241e08209058824900401c560880540d8800410014100b203015042550f0f0100284420b00080d00141c00c00c564403401070300c00a001c2d411402c00d440002d4000884003902c40904030880700416034503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 280699289 1250 280698039 280698043
    0x1002160f0c080307050c090105031606030c0207080f0604020103140c030402010e040216030908121c0209030106030506010e0103021c02031b190602100c0e010c080c0a061d061b0703120e 81
    0x200c035086506400c01c1e45100007d240c8002268010f20054002d000d20304c0000304034580342d003210b000788012701d070781c03182c01c0250b180c42000003001070032903142240c111401d41d00000395070741012102280003a0511002c40e04204156050900400d290446d03242507442e00e6006489036041003001a400950a200d40d00c1e01e10844490300011600a071511282e46040800e16802d2a418050403100d150003027045868190b0b2181c442d080040000c8001600c5a0404002a025140f43d0344007500c035108030400450050320b400c50181c1240d200b1215000d642d694001c0403034094035080d2004c0c2d815000060031a40d80f10701d1007640b00201c01c0041421141c0c40c1e0b40020a84104041c0e003002c00144d100442c07104c500300051051101d5420b0320304040e411044940c00013070001195507001841900081480a0720040070040000c2940d40001c040c0a0348140e241c917181c03506200e100225161240001144000599a040480d00321b20290301910706085500c0c00e581074070f07030701c00003102031541d80401d804c07000c01c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 280700539 1250 280699289 280699297
    0xc060708030901061406041e030210020d02101401090203040c0e1504181101050703020703080f0306031e030d090503040b040303021e1c0c06150b0901021002160f0c0803 74
    0x1040e440140c490a02441140c00c5800b160403900b80813269254000583d40c03200d00380c2d812900d0703081619100751840c3c1e40c8448c210511b5400250030240c543d81c04400c064022840f4107098902c0c0d4219142520340720f004906036004c1c0008002c580000783c0c0107200c60041600295401030042000341c4084d40d40d800c84e01e1248600300c070300407900300e124944001c4a19140c0903240386540c0e60100c001e1034440c9500d0b01000075200d03804080c14080300080d9081014020f00c0184000d5030801c108540b244544020304c51b650303000703c1d00c0764070038010140540403203510044141141a0154001c500707100c45202000c00a008503101a0b17a544418000003503207500d884011b002440c820380c0075000116940030724148417a2840e1241045400c01c0c1080c210b00009900c22030004030032881d000007400c1c60740c1000802050385051103601400d4088003c14604009001031800600c01c0e82121910361b15039840d503049000f0440d103c441a10036146400101d0703000c182505d440c40c003445200400c80d079201145451540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 280701789 1250 280700539 280700543
    0x9030d050d060911040b1b0703030c1a0906010e060604090f0b040b1806060d140f04170f0714071d0421021e070b0a0206090d03021306110c0607 63
    0x50001c0d0540412286018801c0141803800d418410740001c6111000c407030140340200c808130031011034044498191407210410340e01075a4240c800b0035480e810f000307248401d111016125420303c050741081440708905907521802100f806080164285600502c462001400c0c00c0d074044010321010a2104030f602c540d80441c40780e120000b8054030107030306000c10340b003c14451610031000c014407103100b00344660515603c000300301c030041d81d507c0440201a00600d2504034400b000361419040100044151610900641c001e02050541c003030191003100c414458403c03800b09211013400100b000403884025194001915002e40d0401c5444c0c03540c0d01d000e0180e04000c1c541300031150083c072050002941c14541011181e1012011041c14800041e54502481d83c0145c008844115210a025024042c0b079028040340a0b00c141d031911854030095031a10140e403076016501610084401c070501034030032960001e0b40d01512851052402005545002449840160350300903144102007a9a5900041035a14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 280703039 1250 280701789 280701797
    0xc040c0210020a0809010e031201090b061312020909031602060705071d0a0b150a0c052a0405130c0e090106150903030e01020a0c0b16021002030705061608010e090309030d 75
    0x1720b09000f140c3d003900c18103009282c403038000308034103030100e01c004040e2419115041004240c440a01001c00c13024491480840050545003601051568280d000c50806900031140b42650752a03404a0380e071a8420b0b021111742c03a00300c1817070342001418940081c1880d14007800c00e4403009550381c240020b5000030b6111140e82403412030100000010700d07109002078860213651196403550140034100161151240320340038072200c42d01c8541084020041001d001800c004081c090004154002060b825502c0aea54851800c9c04001a8031210084034140381a801400f210001352030071007142001c00d00501820480e549a040224881c90f85078154010202c03c0e940c0e00403800e155040060080c0810440039045400ca02c0c2c204012803842c007108416a094180100c0d900c480740c7c18080d4000a034448001d401a60703002030710503560b4010010b010840e00440a48a81d0394521000e1960500c1d44004200401d8010340144007268890003080d174005e98100c02c41c0e103480d002d80c002074a00b414800f40c4500107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 280704289 1250 280703039 280703041
    0xc030309160b0f0d0504060e0a121b02030604110a12030e040c030b010c060b220b0907080f0f060a08060406050106090b090a0306020a090b030112020a170c040c0210020a08 75
    0x1500c1d2103941c0c0c03002021465038031030400a555511008603c1340340c11025005484074003040503c80f5561000b10f407024007004464142d1118a0007011042081000303070041910352100240020749400240750b41680203015103441d13a2280e50743d0f07003004c2c40e0404942d0814070681c0c0100f03102f0f22070b80d8089101c5009459640c0c20141d0f2400304000e8620b4200c2c1c2400f050305190400f121070b44c00c400b030044010390000c00442c1404210b00854400302d00460144c0001c210751001c00003c41c22070b401041c203404281d072050311542e6100727015250001e054a4208000e0159800200042c2603202200d0704081e00420b803560142d9201025440d00e10b081d5000e071401c0342d503400100001d0f60007603082801082d140d812141042c0c580300001d40c0100103480044c0105400090038842c503441800d4150150454407900d03030700c81d42c403000943c04240c2080c00413800b56851440c00b003402d50000d41c8607030340300743c80000401918081c0403d00014004c072200d000c3c154030030402d003800b032040180090540b44d480766030f03251030b2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 280705539 1250 280704289 280704313
    0x140709240c0f060f0507050403050a02150d14100909241b030c03060e090c130b04020703050d110331060e0d02060c0306010818030715051501090510030902060c030309 73
    0x22540058036010601804000409c0060f1005c1203041100c2d0701141c10780e8007080400c5085141d481142c580007555840d040320f100265000c02c05d03c9004030444007800c02d6040d11441c0c4030040718003026024108a078804da03200400515156203848201c1025000300d0324a00444440c0700d44001d02201038082074440391820001070f418840d4000800f0800c11100c01810907184894542c2e800d0600140144202080118a6401500304140200c0301401c1159a0200c90400400c0740c0c012030040307270304203040840b1180035008c60310980b8018100701c16038071004000100007040300c1e4140300902d9100c2c0710b0386800d2004141c040c0309180805000c0005044040090003001741001ba0041030840d00c100f0070320600c1040d0360300c1b11a0030b6000f6010840300111420384c4104d645980100e40c401080d0142640c0c404503d94010b8105a010300c110041c601070a04102005490304c10503070107916049901017141c42c071000d00c640c0000c064240040c0c000b6180c40103400c80705085030b00c01c850000403a4000404060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 280706789 1250 280705539 280705541
    0x1206050609150907050a0512011e360e0124050a0e0601031d0712030e0f1509190f0302151305041e0f140709240c0f060f 53
    0x103844103041d0700103481d0b1000000040c1195001030b102c803080100205400c20344900130412130307a0714581c4c4000c1000b0303503a440b2000c00728910080c4951042100d00c28000902801000840302210a401110300e14070720111001c08042d500c084081d4201b03611620081c1d200e1b4006c1c4215011080070000b125000750b04d12880c1c5070326490941c0075a003e0298804200410102e51503400d40082092a020851110340004003520915000d070640c03550085030300c00601c0d0314440c02020380541c400d84404e2100c400440401c40e46a00d42400e580c0c002041500c40f8900e11801c13401404609001031441c56940401400c014540c1c0070ba41014070620f005180506c194a04101c080412800441c0600e19211b40c149034414030f60194802c4c0e074000c40c2c03181e005007440500c042108820488a090400075024041c94440140000c0800b0800d52002d4101180c0340c640304142c0c0c0710943c0c21030004118009c0c0202e1010651803050840c035410080080c44040004190640348500c007400b070400420402105d58240e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 280708039 1250 280706789 280706791
    0xc0a1416060606090b031302042012010e2503021605010b18041a04330b0a05010f1103071202060a0b090f0a0c030f0f0903090509040c1e1206050609 65
    0x1001d22004e1001003001c80c2410301126408110401c0070b0440034414030128010b0400381217072805500e8070448203164003003990090070038640b59040b81074090340c1c4d9040d44451010142c0340c0112000c80103040b1040d4a9000f0b2001e00d220b031142c9401440c0c02050a04032641e40d415950486041e5120030715400d4071303c1c1c4100318840410101d480c0744418209035440442403810340b0140c0324035000d450001414008946081d0042c82014000803992500c07406403804400c00740150041344c00d07d01000d280c03030360410842032410303150180c56400450b09201419034603140140146d628070b100401c03d50001074000100d50381e0458582e0001e09030344c14015540c03030666111078074190088100100704609402c141500c01d400c100e003030701d0010b07050003141070460103010085e20200c0510300b0a03e004001844940c018000c0c03500980c0ca15001e1074448013044452801620702078000c881100003071010f08001e080696101a507054032a061943d1203c0040702d492401209072080340e550020041c0b030741400e011017 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 280709289 1250 280708039 280708049
    0xf031e03222d05040204180c0f210b0a08030c060c031302010503060102011416030e0c030703120908010903091401050c1f0b1203030403021606080c0a14160606 70
    0x9081518105111000c0b26007040424207024802d1030219456512056001e00103010060810b660b59034940300e0111031400000000700e01c041c41c10b102c3d030107414482c604d03041110155940f506a10b140d010304600301d0420394450403101c01e42d5020a05265038412a0b148020403c0c0700c003440d200e2050300700f6982030041c01020914070000804c100140d0340031901203001c4103582403c0807500d81d1a801e004034010000c441c00d04d24010040c4050040b18000c00c8c41a60022030705603000c0c80b0310017003c0c802c542c0710032406801c1500360f03020000a00003d06510b0010103290366918050345050b548111590075034400702d10503004074015800501ca801034601d13074011400300030308140c0c5ca0300c04207103001551036041c1800300401c0340b080d40140c581c95406401030102c24200802c45448242004113240d160f03401620118058031070060040c034a420280c801100300c821a843d406410b59840c44492800e82c4488143c0007005040da03102c443c1c41030a60007030698955180500020322640b40b5120048982540003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 280710539 1250 280709289 280709347
    0x14040f1805071107060305040804050913051903090902030403110a0b0403020c0f01050a03110903010915060603050c070b04030e043209100f060b030103030f09230f031e03 75
    0x209041c019001440c1005c1303440300e243c0001c007a61241040c2006000360340003a940702c10700d10140406615151507610340140074606640b000515016401c513034109a0300010f012038a5214100f20000680d4080c50f4001d009041802000c001701e140c40c3e041c403d510f14200c4159101030240414154100000300403c03409583c008004440c00001806600604007202c04254880620500c0442c02c101610000d02018000b03110251041c5070005980b1100000700101d54508400024524468091240034407000300f501481c0c0764039521820b881243c003c2041c1d05008001c80402c40c0d40d101c070b2203514411000180400741280442186c01d0300c68030383c3c0d0303000da202c1e8104a0900010301c0c00419080540c0e07030707401800102c80c8840b00344000a45070507409045d0198010000105142e009909481006a690b0301c03045904c1e11414a801c052542410320317a075011000c60050240d0804152000000d03800800b22009000c1241e22015280c0344650031f803031540c00220b90803403803ca82001c018984c0c04281c007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 280711789 1250 280710539 280710557
    0xc0906060e09060f060c150c0702010f050a0201020f030a0c020f0c100c050705030f012f0301060507110a0f08010c081b0304080c03031005120309090714040f180507 72
    0xa00074229100c07546000e104414140120b500ca41e5080e00042ca281d0026110350740b22156620325a444038084090508030720003800c009101000d03004200c96056038140c5410081020b001000c45103900b200c00280b041d50350070042956030382c04d014007451084003040c0e408514107250f0080207007130490321120036806901c00032a004007a03541e05410545042075140c03c901c511000d08089245c02004da2216806008004c1402d040401c10f400015420501d5032030078040324041c402c6129656500f000a0700041420300c0144101d40c0b04d1801400d405001d90070641400403100d0004a0b0200980c0c42064608140c03903041009610a00a203101c2807014200b040e40343c508448a00340904205185554110f40000014100007a40e010381d0f00c1c0100ad84201c80d1686005181d820450030203001303007841010840c442451244000040b40c1b80701e00d0291010106444242c2e0944144080c9207603148014000d21020400701c080900c11802400800c1c8460440400c1e0b006140480d03201401c040b04000b4805 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 280713039 1250 280711789 280711799
    0x9021909051c0b06042903071a220302130e060622020c0a1202060f0c040602150a0e010c0c020a0f05012a02090f0a110901020c0d060212070503040c0906 67
    0x4414a06102e0308041440d903d40c0d5000000380c0104050244820000c0b071030b050a0249290165900c050300500f5012a12519202d81486802c1c035046280080400420400c80d41000c01d100078030302200e40c1182d281d0034820707100d40c0007810f2a06800106003282d503031403c29000b100720401141da040171040e0f1381c4100c0e090302c9907008142c02084082c641ca407a50001100c4229400421254100c1900561258010380c0b0007000251144010ba44d031100d0002c03c000032071031086820080710700311100341c3c00070004640a070100c1c04410324000c19200c4060303690201008003030002e000324074800d2000c0e80c48501010162041043c69400d5800840c5d0511900d5414400c50340c03c1101540313401c40c1700b40380d4100b070104040b4400b000e0003214002500300e041d01c81880346090300720590900a000c2120240b0070301e45070348051781080c0103444d0703840d00680c0000800965401e1029281d81154016030002d85802c00e1320481040030307102914060000342c1e0000411050207401d20320743c8060000740390700f884018a40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 280714289 1250 280713039 280713079
    0x1305070f080c04230405041b0e160e18011701060f0302030601050d080c011e0e01050601140d15060807090603110901110a050f0102091801030512070c0902190905 71
    0x2038010201100c120b410105844e4035804820410408014402d02451902c0e00c0c151401841d140c0c4c0c2501342034440d0a010808014080030140701c0c650000c4101a2640481402c1f1191500140410f81045c0c40116014042d0f052548040c060030202d0060400c80004404050849006a0148204056600d0300f4001039401140d901d045410032119042c0000990809810a11840e08a10090b41c42c0007000308084031854000e00d6a0740702100d0420401e1400d0311050300b62b1790100c466a0000340c0880b1401e18000c06400903001c440c403070b441c001035241c240c1d4594109082d1142c1042001ca00070004010790f150340031002e000640500e160a03c003031503a2030580e951500905d0015814868038000000f490380d001c002c650380186e00141280d0701101d001300c1041c000e51004140c1e84c000c80003400e600c1ca6030501300703403d18100c960050003000309441c01c14007002c5503008248100e84503e4000800144010b81c1d00203070100041c0c2c0c03660b41070503c90700075000c1c24014269109078054500e14461045450071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 280715539 1250 280714289 280714297
    0x109030b010905100902040e060a060507021f020c060324030d0e01030b0432060301090803010302330909010f080c010c17070c030b0711060c0c0a021305070f080c 71
    0x1c050104054490000204201900d60030070620030b4808200044c0942c60042340c20701604081d074603482129100c0c0310403a20342c0b0695802a403c100000c00882000e03290001c005038039403d83c410f0b1084200040006402603005541c0104206210034415a0002e0856100d02040c0000c80040200005081d805041484c590740c590f0305065035031012181d10f40702c80d04104614025003805200e00390400340e1487c02ea0301c201014914869201c0c00281c0b050070705200d41841c85400c905402d045030720715030030028407611010098000c0e20000712070604d03d03000300e03070303c0d503cae55074520703141600c03000c107801484484601640045c8141080d01010400c12001280b5180318007405c0c40c050388040c846040c40724030881c070f22803d81119800043d20703500348a0124410b07030a0340c0c42580c810941e03480360042101d0780942c8480841c1242c104201162003040810001c0c80411104825a041080d503500001d00d610445072601030103640f41d10030410360300c2d4054911180700d505800c0009060804341d280081c9402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 280716789 1250 280715539 280715549
    0x417011e0506240f120f060a06020a081b0303090321060906060304030c0503030a09060b041407260a0b010f030606020d0f11030f0c060c030105062a12090307050109030b01 75
    0x6229100c49920390542e80c220b0f0180d419401e1138540d81c0b54458008044080c0407255015a92182c1c00443c0c50b0385008103254088032001d41c010300b80c410454580042a50140c0524101a191b4902111182c142400950701c2144400059500c0b01c4c40f81000510311202c0900500c0700c1c00d250410001c456403521744190b08140281d62031038407941c0703928043d12005070070800071780284408400c01c1048000740c0c002040c564800d2406000100c03054050000f1343c6c41520912a61540314000155940e12515040c13880d810f051080c44000000003100591089040c2e440d00007454440008000f0f40d608901694490046450700b08400362501000039102c641b0402000200940414241d406c2c500c1540700495407147c803001e9950f43c6411888940c00d517484280116164003403080003da044840308152412610040d20242ca03019203d070128052403034001d50662100d03d207080000b040c5404104401b012038140d81240d5942e80d08004241c07506085900080c1041048141400058816860035044078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 280718039 1250 280716789 280716829
    0x10608060319021908070f06030510060804020303120103030e0411031303080a0b181006110705010f171003140106030f02061602120601090606030218010c0201050417011e0506 77
    0x100721440015a140c003c2800103081d242c021300c0c089051000400c0f40d4003154030b980b90303000d03040d591040c01360b0503500c3c120360f6850925200901044881c0c01102010342c881e20007002e0328913288102d841d5150405c001c1c2c01c294001518820350040d030342040e110b8840031050400c4c083d0300310f03d40041e00d10000c9030445002410005080c001c250350a2482d00701d1a412440105104403000100711028007208080b281e00360070244000000800b50b0040c103017220800608c1c4040d220135402e22006441c0042101041c07130401504201c90445228041d000b54010702c14044d410035031a05e175082240c2c404460000d04090b0340d16104081000601214412048690584680d9120100f00303c544406d07040c00c0030041c1d044008038031400000c0202052290595940401c1004202d464100450881c0551503003100e0702e00500b14800f41541c0224076110041e88145481803a040e151a8550020006180e020501c3e81d1101211141c41e2031002c080004e10301003210030442880d201d00060a405460901e1011003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 280719289 1250 280718039 280718083
    0xb0f0f06031308040b04081011121810061212020c060703080a0608070b0318060c2713020c01050c090612090f0a1103010c14030a020f07020307030309030b0106080603 73
    0x1c0440f0040d00c0041164120064072955680344064450400c54413a034102450102d01c0300ca02d2042c80b0503500c10407006940b0880c0b55446c801000c0d0807550f4000e04001074814400c03c5201c180480c007600e40a4000d001950626110b203241c0f8a0301c6c4408540c65800395040425100d905440f4401903449140d094036002442d07031140c01c0da10004140e150004945030080a0000c507000b06003000950140b86515100c604100c100f0517266110340c0c0688100b0800c0d68104041d4220150301e40368419490724458001c0001504a03000541c00c030080c1159103456500420100b0420070700388200340d4010072602a040c5000f0305100060254860550000710490018001c64004002000800318985500e022141d0501140c103260082401c1e00000b01d00c02d60915000201561042c0003d80072600c00c01d459506540365074801c500a90000c00d01314081d01001e00040d8056602009854015400b9031071300c003000ba007181881c840c00c43c0d0581181e828420070a090200715100090501c4203a0b042140d10f0340f0b5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 280720539 1250 280719289 280719293
    0x170f0c0f01051e03041a07091403032a01110408030712020a170715090b0a05060d0f0b010e010f180c03020409090506090f0a02011704050a150b0f0f060313 68
    0x1035402000e2480f40030008400c210042c2d000168021409640203850075000c0200004000d142c00300100c4002e80061902da0007006900900c0e03e6030119181c0040a413404c04060310800d5041040d40c03d05210389442200c03420289103800c0c03003884e102180c004c20b202e103028100360303ca03680e034814030800a01c4ca20491400d400c00d54400c0c4412011680d10aa60a09003085803546000c030f84c0043c041602c2a48940d00e00b0124280d19100d078284096021140404641d80e16000340c0040c03800400050b00003103c5ca000a000403c40880d083d5500d00c149200001035051801c1e4038412503058000001f010400001401000c106207101901c0c19a60440400d8180034184200c000e0f000e00d80c000c54041d401c0040f1601040780110f2064814110201110010999421001e65813580203030040d01190010304335a40061000c000598404c1c0a8800c480d0068503981d50b207040a00315903020492a40c2e01c4284060510701500216001c61701108c9503c02c2801540005202d4400036000e5402c107492000b050b01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 280721789 1250 280720539 280720547
    0x30305150315090f0f2407080a051008031b0d030b0d0b070509060d02270f13061d0103060b060717031302040c030f051f0501050307020313030c170f0c0f01 68
    0xa210400010395610748040c0b80501d60f0f44541003848100707400b42411810414041b000132900c0b410060381d490400d9200c101c0b64000925000d48261120000d2110101b43e84208100030700b100d44820524403001d0352180c049904029091001c12308060410501040c04d5035410255408203412403445800c90b00d41070710598562003402c420710740051011a400300207070601c1c1d011b03050142d074980300800c10100030b510217a803c40340055007650141c10180e595050341002c110013111715800c0303a80003a4490b282c120000760800700a043c40b040d40f004034014020440d80d8003912040359000d8580c1070030000141d5807212140ca03501e414401c0d00d07802100242d00f09001d02030043d02140c01400401921416442c01000ba00c14210404045401c0201180300c42c58a9200c1c910342e0b003403401109100742e0401d40111810780c0040c00290451000f0300100c80b401180c4d510392802144204d66100c043c034030b408070070444100c0c1c515048000f900001100056000c020690054150b401c40c1d417800c07500082d00050b2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 280723039 1250 280721789 280721803
    0x307050c010b0904080304020108090d0503130c050604030f021903020102060601080a151503060f180213180903080c09090103060e0304080303100f0f060c0b0c040801050405010903030515031509 85
    0x60f4020302100500c001c0c0548a0b0046000368003e90f910343c45642d4a8050365510341c9046001030014004000068400c10b11040704040c4502c516420001c040d503c00001d40140c016030002e460b5001f030150890b04516190b207001c0080b01e920081c24805514640010751208001411581402400b400081607004547d024048103103540542420850725411705c11013144403010b4080c0464903103140466060341c0741031582c0849000403400302c409050000e44602a40040d421407614145241d40030483c2c0c0e4484000100400f80708000041081d96400c0c000c0032800d0180c14502031500411070a141034581c00925415281c101002103004c0416284051640c89503034880342c280c1c0000300030b21400c581040c10403011034a8103004031300713080d49948810080350840d1080c2000b09034086030781c3c030008042000c8141e100f021491403e041944e101030560075148215422103da940d1094003808150300752041d82e4209068042e580418680790740400da80f108140106209003840000046d11030408020785 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 280724289 1250 280723039 280723061
    0x30c0f020f061803012f07050715260f0a09150207080904051b0715090c03051501090612030e031212150409030912050c0402040b04051c05030307050c01 67
    0x2e5980c001200d4400e1000444445040c420b508100c1c1d00005051990b0000301028100101c5980501542054659603800300100b21000d01075148009024000f50402d60070200d82c680316264000180081c003001e00703950303900c100d25103003882c410b0220100c0d01030598cc1d0312030b9002100088280309c4c2e06007141c0e01541911101c1106000060b200300b003140b07500161006d0380040d0703000d20541e2681441c2101410150f60039401c5c00f8014804400420458044d004801084070000074030205a43c03280c4c80d41841c290001e46840e800164010107148a4102c1c00d40188002d1130304000c040c0c02c10840440f426075014015081006000080c400340c4c1c1c0c2400041c8141c000104100d0b81c030781c08a03a0892112070b04442c010404104c0e40000061420310303016000401e40c0c96075500f0300581c00c240c0800300b0071080301d206690320303c034612f601007183c2c6803440104041d1002d0500203440390304c6c1208000c0ca080e001840306140b0711181400c18009140001a80e03046660381c20460307101c241c105801c0d80141040f80d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 280725539 1250 280724289 280724299
    0x30902060a05042c0c0711100c030f030501051513051201050609090307050d140c0d11010c021204030305031801050a0b040506010507050c120312091608060103030c0f020f 75
    0x481c8541d80e085001801150402e04282c02c0c440c4482d9080b211407034a40c6612580000720800180b0420001c400a00240d80b2424a5000030300003e800b00c0c2d09504901740340404038284624220901d60010404105503501e40303030030b100541c1004007050304000d141003072950b50100030502c11880c0254400c603c000d82005014070005110103e40c10b40a080d054503403034090801403000c00d146100c003108940c140e80d0004001c080c5645c00460481d41059500010301c0d00b2081480400c01e121418130407100303d243c541d81e9108000300b424001c0303801c403480602181c05543c010002ca18040c200202960300306d0381c15007812500ca81d42c400c0642c400c042c0d1302c1071400841d40b07030008128641c00c207070b40921145101580d0402240d6240801505c103846809805440b540c004142281103190025840b25881c140070107503400d00300025004c10002105482000f150b802428103a860690380400001c0245034000c001c1100d9451601c3c050520309406901901040d854007411040d51035403482d4405000010701 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 280726789 1250 280725539 280725547
    0xc090711060c090a1e03081606020c0604030311070c090209121e19020f040903033908041a102c010905090d03180c060207091118010f03090206 63
    0x103074000d1035510030103001d449842503041c003080c242401c884a220642176043c00c0c1c10120305549400c907840d04025280d0001c1000f9a03440000241c03a40054000c01804e1001484c0d5410603142c0513043d9480014007003544001403052001160a4078960001c031800180016541c9111001040a00118041d444082d03c40d50301d40e92900d4079412504140040c1c1441540d03c00c1c00c01e41e50708041c4645240000c2e522800c0d654056020786055032005803a10b200f82000501900c4e2903075104e03020501c07444400170268000c10051841c961800032200030095610341120749140540c1c030100d04100c0101101c410b0207900e00021501000e000b0014064010b0300020fa00f290401003040c48180102c182d554441d40c00c0e580009070034600750254034003601c96500640744099002d03204a009020029407080f0005041c10458003142c800980fa00141c016940540b94003070403d0081020b590100d0340000c1160410844180c074031411298942c0d40610910713003204c0b000603030b01044000e046844000703580140009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 280728039 1250 280726789 280726801
    0x10b0603040b01030c0504020403080901030b0a1707030212030307081b0c01060b04150c2004061d160e0109030b061306090203011806180b190603020720030c09071106 73
    0x2c40901e040300e1181d0010801c16842d10188010b030701552000410251341440000c1c41d80d80203400011840002503d0300d01c015070b8410360269a0400551140882d4000050500550400c0b0001000d141402c1700190b00d1820908401402a030317000300b0001090f043c101580f8103081441c021036a08500850007032003030503120f144001541c0d215204005000c4040940d0076842406401c4c41d0f80b0041d08034a4000700190039915451400d082e83c6078403a030141d602d1030046100000450182c0c800c40c8540c0a0344517628084116804028440c0040000e01c2044d00c811046a070b071258203841602d52000c0c01050307a48802c0041802401d0303c00030003d031503081c4000401c00701c1d465405141210703a64200b42000d100c40646840c1266124003920200c0407403401c0029139090180c22036400000c010b84024645203800032101e510020540016000a40018801080c01b2801b00410a42a80294520309850031800081d0340d07030a240c8469405948034070005442ea90054481ca0a12403980d015100d49240c89 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 280729289 1250 280728039 280728053
    0xc010c0306061707020d1101020708120907060c080a0f03020c0d02010e0606100914210619020306010c06050a180b04170c122503050d0c110d0e03010b060304 69
    0x180180320010304100250030202c01a0902c044c0518002c2e00605425000c0400c11105000600e904070b1056408115030303000070b007814004296000c24450701661604200100c5402c0c112141e000c5000c0110b1340c91420702003180705044031501032450034209900385101e04150064000c0b40050942405030200464159406422041840710400203417030540d076804041050b10071f00d11000600040180c0d10a10840c040a0020401544c0040200d6080e04048003144001d1784a9800c203012600140184504641c40210080015404140c25819490302c1e02c0024250000c00001806190300c2e41d02140e034000c0564401c0c40e4640c54004012120b81c15400c03c102800d605880403210180700a80513501004070344290b50000801c00044d0105103404418090250402d01d25015000c00311140c40581d810b0700c51007102668440d4617055202e800c3e11009030202c4003c0540001889030314400800d040c180403c0c854920800c1c0e04141502811001c08a4010001d03c0700e0740e90044000010701c410703c102d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 280730539 1250 280729289 280729301
    0xb060c0a020a15090909080705012c0705010512060a030b012904120b180601060c110108040206090d0809030f03120108070812032206020d0f0501032003030c010c03 72
    0x9075200c80c07980d541e4846034000d07500c42c0c043ca400000d802402c2800343d0390040d04408a0540030b0580d42d814050151519401c455415100047c0f009002c07120555201060322140d100701080c0c0080c00780d5528003000641203106a01e1071000300705c040c42c0002d2156440342c1c1000050754000003030300c0c1951307161043c01c610075544245503481c0001d042740c080c03074070b50780311040b00c0030f45400307040c42440e2804541d2040e1060b007024080005c421404900043d00280400c100c0b4000c212507680e600c1d900c6054140f00c800307800d140500c28108050b0303800b0030002d40c0340d003412681c980c030058800c03030032007803290900035401c0c01104551a85030081880c800580700000001d0040c0d01c0302d4515440440c2d0740c840c10241c1d076008074031070b075071031600007007034000075012580c0103164031030601080c000c242c071306411042010300c2c103400044440076808107140551442c01d100c1c800d4070040f030100c1003010754110b8645e0000e8440303c540e5036002d010250483e11841d101402606e0905080c90001c0c844104018405009030003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 280731789 1250 280730539 280730543
    0x1e0a03380a110301050f04020c030c0a05060105010915080c0c010605060d0603060b030607021203060a170d02100b0319061401030b010302091302010507020427030c051e071203030b060c0a 82
    0x2050448110480d0700720401c0f00d0480314000c0c0b00c40081801d000c14040650400c81400120b400248018460300c807051041c4112944203c01a000f550b0400c800904000c0d002d4000004049140440702410794000c4486500480b03250b50450302c80c2e81010855000d01aa9040107030460004100c00014031034641001c01074a00c107010500032480c04400b031540d101412511403005078400301c001c42080d94403000560f0840c034050140e008098440703c40d100c1c0d484000e0070400740c50b0700c0001100b0145a05100d40003400d003101c0000d01440d2131181c0044d43d101506001c101c10354100200b00300400202c2e9100852040400c10110502e40c2d490502c94110042403200340c0c064850f46000912001c041d6022800701c40c0c0c161940c03404c14806800744801400c0550a01003141003040c0d595070144001b8901c407241500c02d0740c440060794810303e806270030010460000d266201044d10707004203107a004512201038900703410040100c040749003000c82c05803244000c503a2700700c040020140d5181c000400c1040450f8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 280733039 1250 280731789 280731791
    0x20a032f071406130b0a0c12020303090f010c0c30020d11032a0a0b0109020a03060503070e010b0703030212041127150d080d0603021e0a03380a 63
    0x20182e03050010910680d10010b4401400b00030a0184049a00c06040c07070040c01e1600308652412aa42c02006160501c0c0c101e0141c2d0001c0308101900c1c0042069140c9240080020b01c036444411718003614500ca40400241101d142030101241814000b4041803458030f100b003d49080d200c061006074480750040d41010004402044074604a100003003181c0c4510b843c841c0100e4080e5180c001c1119500c411401e0440380c1c0100340f541004030304d4040c0003d02805a070000141d40740d03030032307400541240d081c2d43c0101d0180d0001d500411070b819660010904482c6c03000310117a034400252a04a000380304880010801160038803c0c80248900d000c0701d10340503001602c0403105100b6039480e0200c150344403070313003078841080d0180003074101582070b420030501d04406030100c61451001e0b55083d0700c4d0307000084d1185000f5940d01c0208194600580c0c24001040c00001c02e04000030500c010a07524442c900000c0c1440103d01e85818108201c6a00403861285444403d000e80110728003920b0580c01c1038951900301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 280734289 1250 280733039 280733069
    0x170a090308250807030f050a05010f0509040503160f20010933110a1a240409030e0913031124070e06040b0408070e07020a032f07 57
    0x7810022140b29281d44074144110a004115a04458010300140700500300354603000303c2922400540140c0340a5003050034003064540c145031500110a440c4e90185104039030900c20702011031004001c1b81c0c0700c1015004044084140f40c01c01003c58411804000d010070480c054201114060801011811109a0342c1110460365400c05105a1703011014200450300716038103264096014000300401c040040c01c0401700521241416420948929000c2d01c0581d40c100803004104064082d0690108501541c20b00c0140070700300090b0008100320002c0c0c011a80e9892107400d00d0b004a23141e0307104a000801307004451404941e031341000e5843c560100d010a40d02144148908000309040c0000d0040014514001080404408142101030050340030300041724a107480649801d001040906802c10f8900d0b902e030f10b0911220703c0c0c40c0450380300001004802080c8400c2903800314030403c0158052034000b0032183c44600b4249500034a19600340c2030b600c5200225040b000104d062004c4404e40082c0c0506 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 280735539 1250 280734289 280734301
    0x603051b04031a0414010c0903110604081009020f041d060105040b0105160602040906031b05040213090213210203160501080708102105010b0409050d0f170a090308 72
    0x30a00440c080180a0640100300110103034940c0382c1103902c44e0044513000c2a017030f000a00c160860361001a03102c00554150350600521007000d00b0002505420780f00640f90903d042d0503103032507045001b2448481a100d15040702595906125422000030043c020854081160402c0796844c0b440c59410b50302e40900e6000088918107032007075590390241030719170354500f8110030001c8071070603000d0744111655642031001040700c0d40584030b144080d503c100401c2607041800c52000409500c550b0000340700b03034010015044402180012502103a04c1c201002d81c0340c098002d200101e00e50715402c6950b040c41440310340303040f4140c1c8410b036601d07141c02076064070300002c0e02244a10124403a4040c540c08a04c4a10101d02858451110950300401d50f180c2c1d102d03180c2d2581c20301c000203010182da5030340c0c0061905036001807200c00e100d031603200801141c00300036010042c0c0e500c40d104c040d608480000e0065000440d0803d41c01a030100d005d10740d5450300511a46004c83c80100284500482a400207440f8400030310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 280736789 1250 280735539 280735591
    0x70b15030d0302090a0801060f05150306061602030307120305010f0b030103020616020117091624050a020106090207050109060c080c040e071403090c040b190509060f0a060305 77
    0x4026801a02a010315114090198081e41c000d550040d0009040c42000510380c4080c8103090250481400c1008a0392600c000c2000041a8140c076a07002d840030014411155180012035040704000f078503480c90844030b8000603085001e1800082c100c80c4003218a044000d9140e48424142d4403c10054580d50761501009200c90200b404000d4001e0302c10480b100740d040070955104100c0e84145048241e030b07502d440416440b40c0c0300703503442c0020b0742c020107032040000000d44456015081514164059100095241c03202c1ca80a40c0960103111002a40c0c0800c07034400c2d04a50041c0c045154159030b00c46441c40c000d8000c020040c01a642180344c1220b5100141c03241c52800d004a08666485040900303103080a4a9000040d29100a210280000e4964140c080b400745204440c160003501c80740c1e8000c8140016559450f4010b403003040c02c2c010381c00d05150b42d07032200029684180d03002d8826640750340128070b104a07600302c000c0e40a601c2d42400100560304cd08072512a80d1039022005c08100316805100b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 280738039 1250 280736789 280736821
    0x1407020f0f0c090a15080d02010c090515120a02160302071406030106140d14040510050f0606072a1203020c220504030c0b01151106040b1f09020a05070b 67
    0x241d001c2e000c140402c13064072540d0070803c1c4011848078501aa00d6a807400300d03240400c25080c3c2805030351588800c0e07000b1600419024000d20013a659040d9400a02e1f508030150301c00c244403c4404a070b40004102e08501035810f40e41061aa04170320300c9203103210305010307503614210f100304080c2c40018031800e8450f0a0003020350781242c041380c840f041039405014222110750040144c8030703103480e600e40340b0800944488000d80c1c0114011005014044d24181410707064410080c071500e001c540c048280a402d84032541110940ca800a030902851351000302c119a07001c19158480e50074061207200803034207134070280404210301d1280e02201c0000007442d06211111000640d00500190340d403241d8480011960892a4024401e252030394401189581e0074588080c01c0e0005220001d6a1000016060f000304a8102c2140108000c021030320b01551620722040d0001e2601c85068a080800d1801c00140b0480d030f07018096148007551a2003000380004c2c401d41055a058684424102c0800c5400180202030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 280739289 1250 280738039 280738063
    0xd09081609092f0a17060c0a111504050c1e010e010306080a08040e071b0b060103020d06090608070806040b1513060305030a0816140313021203030402030c0a06080402131407020f0f 79
    0xd407046c0d43c1c404104403a1500312101303200500c0106040e090380c8020500c05400b01e643c00000c080c1b01402d060500c0307032074468101e081038051000f00311010700c0c0714294440c3d500d080a0900e800f00d40407810b000124040c10003540180c0d5140b140c0c2d881074080269604c0038006680c0ca190020a441d9502d80086483d481320003c00381680015480c80e030081130303a0104046d80084181000341c035055140c040d00702112001c2d0b01c03040c43c0e00d40d200390501420303901344040001403503034000074019818182c803407103030a0710045c0c0221040ca0501d00380907000e803a00007100310b0105814004105071643e1303060564403a40103250290009044100154007005003454200c0121030302d90f541ca100501a03440481170340d2020f001c08000c400315449000042e61011001405444240050354407814a4414140782009040e281441000d005105104040e80a48000d90041e0101d901d00c0348808681c0c0810000d1030000414002040104200f24040e034001600e0381c04000440b0865200c4003d0300d0780680c40700b41480f42 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 280740539 1250 280739289 280739293
    0x501021b0f1b04020f040b0a1d01050f1602030f0a0503030403170f280c0512070309150c051b0609120c19020a0801020a020d09081609092f0a17 63
    0x542c10726007001c0e4090404204001d5a19140980f0745444038055003280101c43d00003040f00b55006664201d1040c01c00e0304080a080c50750070600040c2018410380070300fa80161042d208c0407000d01c03d42d602000110400c080c0b4006072003201d80782c0d061841c0c8a5000325819404941d15150506481c8a0010214802d50420b217403c00e00b0b46039480041110704400b0f0034074541d160b1035407850041c501144a10034500c003d42d1941c0d60303100b142048001010340b00616900c140344c0b13404000c0003c182d400b2101000c0c10031900700061401c0e01c0500a035840e0042000800c255410040f02e2401d00c0f03400580640100c0a140865610701c4208941c0310381071040780403d07480f0741c0000000240c0030f07403184480e0002c144002c2c00c149a540c2c98001c85804c9130042040400141e10544110608540181e40c2001416406000d840c86010901062610080034440c0e08036641e0786502c04c00c10f0110301103c49061102c035000441c1030350031b003100c16440d8261007984544a40c0c2e819200007220249a88140d044d0010a40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 280741789 1250 280740539 280740583
    0x20d02040e0c100302120c090f12030708120123030709090206041a0301150c030f051c0c0905041805060103111305010605070c0905040c090b0d0501021b0f 68
    0x42400302400c1c456207400410b20031411000c0e2943e0790542c40d52400700b01a0360058440641c14400c1c0410f05014003071400c800c0081007142002d841d00c00300e50480d440c0548116512131801d03c00c1c0d900e503204080015169034004034600c0c0707104090050050481d685d80a013002c0c48101e11400c06030504405015907490790041c01c0c20032103a1190b0700203940050009008a0506a55086411400620f0102c04110348400001880b0300000c0849490300c1046900d8121508003080d5005445400011202410300c04041007000c0c0001040c0a144c90500c0d0b8902c003802483c60444000d0000d111501400348503502344207180d002d02420421660b455074119006010903440e41e01e03030004004516a145070898900301c0c080c1103250042c0210381c020101da035203035543d42c18141002429000c4a4018190190904040c003021410b000c8018040d0b5207001000550708105400080000001c00c0740145954004681c1d00d50303003c1c2e080b044074401400300c0f0980b401c0c804680005500d8441460348240030041600b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 280743039 1250 280741789 280741793
    0x19060b120609060a061205030406030b151602030106140a0b0c1501030b09070f080c040b01020313030b04020a0506030115030903020129030d0f05070303020f16080c0f0a020d 76
    0x904140060000601040491500d10341840e080010484022a95a00081c00e0088410061103000014100c0b0303d0503007801d000347c0e03a41e0781c1c40c0e110700e100710010585c4508050300e690ba0b03070350b803000030400034625900c1d0b4030200c8661240540b45c002205034429443c0c114001842a2054500981d0b49402040760144604003207070700e5096080000705030101d01c00c14440481e82d60003110348601031801074040c001d4629113603100c28644900ca410583d414541c0301810080034000080e00c3d241d103202110085905004103004030b10314080c14101d0f69a407090098008140072030750342424043d0f40252104d44070192614103201c0144070a00c140c506043c01e46100180d0a07120350300a8101174460320001c940d02604c00c3d14100313049200901c000c11291412200b902a00c1e041010000c0c0c9e0180d400d00000c0d400340202c01802c58024078002809164000501c034800f003d054044030752102c5d0340c1401c0c0c40d000c0c0040c20040040d82000d40b10301c103188507001d00301c0c030402400581604025802084010140865 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 280744289 1250 280743039 280743041
    0xc07081806070c23090f071419080a020702030a080a05120412030b0d0b2a0a020601080d03060305071a120721140a020a050c01020408030406030605031906 68
    0x10094050310100060000d540c1075680310000d002c003a005015400c2c45508003c0140a160f5441c0b40c07000766108100d00890030f90b1242c0e0302d0319a00c00c58864002034036990701281135034034542500c0c441c99030010002d80d00407807140c40004a00300c3c1a6a50b1080810b94403598910204c3c4101c160195240d0b100071240c40000b04d2450042281000034504517080100f11314281c1944a01900d080340ca4101c140f0303010003801c2d490b00c64007010301e60464098208018986440a004d00090000000b5440001030b0384a109840308030094000848001d10380d0f200070b1500c00945901c070a000d065203d01a100c00c09201c2072280c081c078415250064007030400507160818140d0300c000b90540c689901c080501040b1003100c4000e0303826102c0c113020f4845640c4071040c145140d2800601040c2c0300f070310b140750042a007803048855090039805501c03000d0050340e401160784151410700950308400c1e0158000500480c40700c802001401c200d503c507031001d000e00c2e034480080645034400c00d82d811117a05600d48040002c1145 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 280745539 1250 280744289 280744297
    0x1213c05101205060106030f0510090f090b01090b0a0f060203030604020307091805010302120109030203041205011512020301060f05100e040209040c11150f040b0907150201090b010e0c0708 83
    0x80d500140440350345802182000580d590203850f240c100c180100001c42e014010720f0800e01c0072000c00c100618100f00e0220a0a5160140110150755544c0e030200ca4040c0d0f0b80441080754104c0e040c00503641e910f52800000c1c0100b4401c07070340101c003603c40020381024401c4402c03007940c00b40d0f0059030650360303001c0070b000c02900000e06903c01c002c401c00b0001204050f601c030007407115a4220340481c0c50344c154010f01061105240c0c91f02840d81c9030500c1480443c3c0c0c04000d44064030001c0c801030684031502c3c03c04a01601c0f003030790700488c0300c9080400003500c00203084c04009094400d40007842056a194040c0e10301c50701500c60540c2102c5003525110300c292180c20700c0b18003088010001820090741802103811030305031401c188080ac03854400b207418503900b0010201040b402900c0a8100d2a001c0d4126880c4440030300000c00b210001d41c0466841c1c64180b050102809025000c0c40b0703031642040e0024060550b504085e1134a15200c00040303642481c100e4050310801c1c0c004c0340c851404c0800e031384000e40d944c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 280746789 1250 280745539 280745551
    0x47090106120b040605150d03050d05010b0a05040303080c0f0313030e0f10050c01060e13030e1f1206080d0c03260c0c030d020304050a140a0b06040b01213c05 69
    0x1401007090009a59200e10004660723000b03585203622201451960012904183c010f40900003081c480c0500c6558800101c50a6035410318208840307489400d4198203a02802003400c005c2c2d0004010400040c2d0901a59400b290090ba11160300141d91414072200e8100c580545400842e41d1005024841c007480080802c0300d01c48000180c1655204a0071038a59410f4917100d90005d0004859018168400620706059208803284803004454505001090900c0d070b1503881440f5425507403413280243d6030302000003040b00000747c0744c900780c21050041c20035082c50412804541001c16100420a580e6944a00b413910403000d0603017038072402e481040303d4201100401c014802040b0740561401c1da800514041c51240c0700419462503c3d14240010704448150032200364010182c800c0400c114104540c0c00400640b4000380c2a180100100c8610100c0381d007158200183c2d140c8600580308503480075422404505440c4511545607021340303002400342c110194411000c02010011174929480150410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 280748039 1250 280746789 280746811
    0x1020d260403170405063c0601110a0c030201110c01090b030a02090a080c030706020319050a030b030a0b0609011205120a110609030406180347090106120b040605 71
    0x35540c0007210f107854201c50440301da402503014010780061051138842c081268002c00300a5030b4401030100800c0002d80d582602d4550314102240c42c590082d43d00ca10b0200416050f0351004280707051072007050b20b4600c81240012505401802202804602c083c071104050351203102051800c11800c0c51070308054006809641d00700300c0c008031030740c50f8805c1e03d00600345030014004021042c4205410315445500020545d0001c1190701da2100f62400380020801c080d040c01500c0d1401c0803021402440e034484030542601c01d117442102070208900030107100b500d08031180c0304c4507a21199501103803171050740014441d5029842c60390212260501406102c2402d01e0105c00c2c821204a01500d086c0065450700c603075400c0010144441e560091502034121030741018421510718542d00c409441101c0746804000384502c5000f02e501400031041c00701c100103d54207541c001110040300d034001e000160740510f025132070715000140038400f5240e9001003c0e0000034403109641c69481d0503018060080c43d1f99051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 280749289 1250 280748039 280748057
    0x80a091113110a0201050103060c0929040314030c0f030406090b070206160b1006020a030c080a090b041d06040606050405100306120b0a1a03071a07020604060201050601020d260403 79
    0x120a00b0010344124402d503400480c003540746084c004100c0b00001c00d61001c0100f05581840645200c00742d5086440841d00d00704503007031403134520840600a81d0001400c0c1210304241c5840b10400001501c030403040d03030702510803000019610641ea0303c40d0348903034000314180c40b10800800c1001005468031500241a0030b280001c84000c5440d0b035000400111000700c006014010312a40d2030056101900a40c00208000b50f0b290300c01526120310804024441000098075048032482411900018180380544503202e0b40c0f5250208100417141c4841511013100e040040d03ca841c2901552003121559245c3c3c07807420f42460b05000700c0c4881c01c903000d07060584500c00010b0b0600d07426808008a40100300442c51420030701031310703401e507415001c99204100ba6210310b03000c55034010480b081158018094201e040ca06010a00d0850244520195001a0104000078001d4040d0002d80c8200826400d460080c007400c042640c58031003031521000d01020107203040608602300c46601c0d812a00900b80070b152 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 280750539 1250 280749289 280749311
    0x2030706090602030f0a0b0604050d0602073503060603130302030c0a030305010e01050402090f01030506181311090907090b01120921020a0308160e060a02030406080a091113 76
    0x10760302000c07821100c0940c00801c02003c002c007040e4541d0040c0c407420b424040c4103846000100540954000d5510038000080000208100c9a044842e07142d88900e541c45005a0044140c0302200032003141010705800c80c0100d13a03402004403c40344107400090015066403110010001140011903084065210070421003106007410030401c0d215611030750300030032030b1f6041c10810b150045045c1e1185001d28014041c1d125941d0320720311082e1000340280780001d119074070b11001604504020300d8003540c0d099100140111b43d00300e41003150005004514102d50600810b05112050b103003201c07603408c00c0d0450001400541e02503000701e0b102c0c3c401490701d2032900124040d40b0b01161f43c0309800315980c1802c000740941c1c5d04044002c2080101d01400504080c0105171009092120000c2009210844120003024414018405401104030141c656034840c80c0440b006582c9074468095000450345410004051500900a400f02d03e07510560041c4c8040d600c0c0184400e0450444951517200c0d110264029 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 280751789 1250 280750539 280750541
    0xa0201150b03062b150f0905010e0601050a030c120c0902031501030b030304050109170304080f060f0603060705070321020c0c010306050415050d080d020d140a05040b130302030706 79
    0x30140070940021a0741e0b040c003604211401c0a52540b40480c0c48580502d05910343d94800761380701d02600021010890703d02c0c40350742c6000341072903d410740359285403600c90010701105520000320b8421040c03c031140c1da600e400c10061100e605100081007901d10344005e0012943c130b00c4000030701c0c51260584412183d250b801c904240d0f0412110359070400b07a00b1090309119a45806014040322050b400340d482e103420400024100c030490302403010544507103819014980030410071100100b520000303841030303050344c0c00706c185d11180c00761200c4202d6580320300441c002d49400302d503090150880c1e0b1621458181180c1e0192140e00419003a10301c80782c4e644203207442041c81800200a0211034101510740c1c03125020001d0103c07146c46e04014055441c0100e079458800300001c03510240c400880b101040041a8a445d0840f407107800008950f40c0d001082106198140b07811a00a9074141611501c0c2c580c3c50020b440300b2200d0454000e045590b000c07000c10490040024010b003140d001c1e105491a0081341c1c0c41e050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 280753039 1250 280751789 280751831
    0x220b090c0919060518030a0501060f08123405060405010516080402060a0c020a17010c08010611070311031509030307020c1509041512051f200a0201 65
    0x1400c040c400103411a25407800710300c040441a02e40300502c103807609041c0003c04034040d00350081c400c2840969840320658040044241c2d0940c084002d00c0040e0310b07031032a1311150855120707540c02031054038003032425051004240c0e0844145285903d441c20b03409024450541845c1213001d118504a03050344000c90014050144941e02900000c20241040340000703c0e680c6541d20b0b900100f00c5004203000050352000101c8240101e17034602100b0260340b40c0005404903400360b00000c1007008400c1c0c45c000010064001c818054455283c0a0980e0f03a07902d020303501603045180c05a41034114150501c0001d200a85501d040341010302116a151100303603400300301e404140c5490541c0c2c0d001108002005904000d2070849070820350700c9072220034850500e440765010b211000d5100716200e202c910400803002034407400070f2102d111150100c00d114109640c4400c5500f490b50401c0002d00308040e00307821507005500c05d0a4100f54002c202910003084607506030041c04c2d00340c0455481c2c80307103c001004820404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 280754289 1250 280753039 280753051
    0xd121503290603011512050c060a020109020f010309020d0f41070617090a150c120515090a0209030a0317071d01050a030b090c0417070302220b09 64
    0x250300185022400c40d40c0008018141440f9a04026810b0300c000c030200386440803a00c01c50b4a64480c501c031403a0940c240503001450355001880070801c070700d600d58150007804001d4025186503011441102c0110182c1d010b00360080c0d000701115001d00009000a400c80007010301880142102800c04080c5489444110000b20f1240d0b0003403d591021041d0310b110580c40702d5503c0010b103161483c1440250580c860710120712149103100f03001482024050003640140c039488030200780101d80e890b80c1710004000c0111210b00290340c1030498400c50149106090180c55850103070f440070b6054004100c00d0280c02841c1031900c03a028001d020704c5445c10481120340c107104c0d441c0c1e00b2a42d0903000445084c04070040100080000140e00e200d0b02e0f41040b40121082c034020b2070101e6031340101e5407058010342141050160481440c2042081071006580504141c8055107001400754035a8500e0954070355540c02301030340c003184542100d0b290450311400600f001d40ea40d040421a1449400020f580e0300c2e0458034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 280755395 1106 280754289 280754333
    0x10f031713050a09020a030c110712020a030609060903080a0b010903060b2d03012405010305071211040e0705160b0a060b030c09010306080d121503 65
    0x720700500009020115032590313482d404d0000f503004100030300002e850555140225880340d0b11401481d00410700903d250b50901c1d612841c1520317094800c0303900c40ca2880000001070f24a0044440b8140282c1002981601500313014002c0c41c0c0c021309510400707250900502540e07070449540c3c001e03250440e2000400c0b01c6883d01203072202d42030b0750111115030a03065000c0036a0549100f100200c1c0b500f500280900300084a10900480381c1031401c2040d1150140c041c0415440b9512169002c0c03041e190519000e00942124011201070303d081c45116040001e040c01140c0c400710605800000301e02c0c03c3c81ca00037850480d40c50b48071482c0700007058124005c02142480c00903802c800007074214030310120f80e40e09004040581035404002d019011030304080b000241c80101294170040740d80c0342c0c1c4400c50101c0f00d8161080003000103040111440e0800b00c4040b001c00d0300e0781c200032000d81240030 = true := by decide +kernel

theorem cover : BRFrame.Cov 280575539 280755395 := by
  have h0 := BRFrame.cov_init 280575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 280575539 ≤ n) (h2 : n < 280755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
