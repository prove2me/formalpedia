-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5016
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:28:19.735753+00:00
-- url     : https://prove2.me/submissions/490385ea-64b6-4678-8849-ec8d1e159caf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 901978417 ≤ n < 902158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 901979667 1250 901978417 901978447
    0x13090c0e09010615031b020f0c01031806020c0d0207080c0607060c180803040618141011190506060a2603070602040305033c03070309050a061b03050f1803 68
    0x40d02c903945c00305420b2a00c440842c0448091707a15002191301c41e904002c0000c0e808115503600030000d207408035000400300d0301e50400903403008000d4441c5100007104000c039140010740c2490140550207449100b070307031400440e4944988411158102e6800c0200c4c0c80090300c84c1d8010064640c00717051000b0b06c85205d001d404600b00342030700041300b95803000400744103c6802440ca90300c404180030591605e60300b050841504600484d00b81c500803a94140726038800c1d80900d40d50346c0700740007203800c44005544240c6241c00002c4c108205480c20b02400d40030480c41c2c100f091800c01a08d00e0000711174180c4898200d1a400b10300c42c0075000b000e6020600004000802c3e9000a00045006100375600c40014000901880700010040c7c0381ca80429103500c205000f08000010b00850705d0b210103501d070f40d00d490042e000b510340c3c000c000b44580103400c01902003144990100ca011001c02d60b4040c00504814000d03000c8941c181c0c2d820b500c0444a000140d060181c100d0595030540d04c41050340d00f414a040c1c1e40b000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 901980917 1250 901979667 901979699
    0x9070e040f06202205130b03120f030f07050304031710050306130b0f10030f0f02041e06331e1706010f0e0118120606030213090c0e090106 61
    0x1c148800040380c40403150b04d40c00c420240700315180d030b04002500e01000501d0b05540b0b80c84211025440b5000340050340d90500c1400040000c59040da80c2d030301c4201101c0c0819910840350a41145001408292a14440e4081d07901c540da25032124880c2246217100b541d40400d008083c1140c2c0000300c44c1c00309541e281440503d019643c000950600326100b407070034011629000340070458060540702040105603c00b814441100d40103040e42d09021040d0030001c001e480c00c000080d4100381480c0540e41c03c4000044150311114100000b0460700d070300c03014444d8100790322000741d0032018186c0c0c0c911100c00204060700c001450b1a0300301041041c03050340000c8442c4505620403030129064101108050981d5424158080c400b403a121401e0303d0102d0020701200c0e4a0304017a41001405207001c190414403908900c00342140c0d00e07880c06084100d05d0031102078a1903000490050031010301e4891035800074000c0e01b05441d88055142801418030724410013800b00108151250740d20f4000000e594040e00300140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 901982167 1250 901980917 901980971
    0x7030518011410051503010b0c100e0318040203060117360607051204081605030d1a400c0309021206010b190c020a0608040b09070e040f06 61
    0x180b86190841d10440600d0881d4401c1e40220070000601007030442c00011a4152094503035140d4132403a00368842072508000344004546145841c0007609090300001c0508a40301c54044074034003286800d8148016404180c0e8018080360440d01340c40c20180800394031541c409404804003a42ca4150003a080b4018a462122000703030071100462400300105000c265401b481074107110703290041940080d1484000104050b0036150007284428556254108003e0300c190407000301d9803240d0182401c03c0042482580e003542d40f0092601c524900d0030004038800010200d460710b1000c03a40c83c40100c0c844000e4294040e02c0b480303055500c0c43c403105140c1c0700c0d0465088d00d946c0c00040300c40580c41800800c0d80c2d1928400407560000d40104000c2526000b15440c3c6000c1c80041c00e0203268900b804e54102003001d60007988120181000b05207036a000740c80900c41d500500c0c201f9855216014182e8a44407039005101c0c03040d244100203001304000804100c1c0700f500c207200006034001009031000c2c4000c440c9a0340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 901983417 1250 901982167 901982201
    0x20406090e16050d0b0702010e0715030c1b030323090705040f052505040f08280c051e030d030b04050c04060914031212010510170703051801 62
    0x11401c0e400c0c04100d50b855012404226600260030407001490a02c2034050041072a1149000203444510039005a1212848001252802c503290103102014010807a02140004c1c034103c058554144a0034162400244190501012045d540c030102c0117041d14117901846082c2040c1e29000ea02020b101c0b42d8854070f12540601104c03800c000400013078609488090300c3c014107000074400c41e480003013503000c2d65000d4500101d001503c0f10005503054007582c0c0c840b14500e200c000303000034500402300781c1c01005908030614051460502c61410807140030403002400540c590301c03050120b800e00100e00540e06040d140161518180d0b1400039181000c1c030000280042e40701c5003401c1c25070520b8018550058a10595542864142074008020300022306c1001c400591200305000c4544007400b5510f00c0074035420781d00380e440340300d040046520502880307818000c85040d10300c0303000380c3c0c0301d421903061803001d8141e14140c948941d4005c0f4003400c1d026203080d0820f10107460080c4001000d04c40c1c059800817101c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 901984667 1250 901983417 901983431
    0x30c0703021005030c030f04030918050f0c0705060403050c160b070506060a080a06050a090807050d09050117010608040611030a0f0e120a111507350c1602040609 71
    0x6000b10728030100308210078440d042c4280002907a401c400d881d4001012807029006680d68102200d584040d5800700740c00540c0c0507a1082e08101c0c87d0000791207003813121141082038a600458104a2140c0303003001c1c204c0c2d001140800c000034072980041491041d010102d440c00c0c040922401c220402592206404d2540020114100841440f000c0e600100468010310741c645041411500e5645002c2c3c02003a03140e9038000100c1c0e04450b5881003040725001122103031940d0700c82c03134100d82e0303402600034920100c1c4040740001179542c031a4071081210041c40707118550592900100b581c01c141d000c3c0080741e0f4180c54811180006400c107010307611646e8040340224000a0f00c064560480b8020940043c003900945070039030580d0008401c54800d40460b01d40f08180695407030b0030505081450214403201011070080c0281c01d0b03405446000e00b44a0514820340d400c000620076441400c007070601003084400c260001380044601c3c0d000d0840c58041c003440d9220500700f907002404035501c0b9000070316102e9903400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 901985917 1250 901984667 901984669
    0x7050a02131b0804060b03011a01230c0a0c09050402060901030902011101050a150f03080306010807050d0609050a0c0203030f060f01030609062603030705041202041803030b0310090305030126030c070302 89
    0x880c00f083c1c0059000300035980d61060030011006a42c2c407541d050bc19a900c031004a01c50028144041c288041d68064466070302c4952251500d0b44400207440840c0f12000100c1c3c0340145125280c040d40d0300074425071600128000540103403000300000d80c10300c4a10088503014110038041c1c0b6115110304500001e180b0071110040404011769046192049800c81080c00012240400c51b60001ca003403d01804c666a00d000884a501c01c400340d000c06a0700b030617400201000c0b41e0704072901880b00340340306100d081c0c4c124000300e969010480c0e00c2c02c24021b42102058050038151040d406141040c907002c16003988030708202c401e54190703620248030031025240d120b40d2520503007114014002c1510107549141850b5100424038002c1e402070007c6041d00740c3c240c2c011551103900c032080d04100c034102100c42c4005414080c0c0141000208076000340a07020210084490354850a0303000d0b585a1203903401e60f400c01c0c030922003c101d880d650301445014a20080d0407158200013525680020200400300360741144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 901987167 1250 901985917 901985921
    0x61203020d030e0f0718180b040b012c07143f0c09060d0606051b03090a03060209060904240b040e040f0f120302180607050a02131b080406 61
    0x1da00d41d00ca03007001a0313940c6520004070b01e2070112a080710185203a880304c607000340c000b0a1400d40c407898511a80600c10300300240141424803171780c0924000c07200f03680d88841d400341502c0440c1091960041ca0000d001d00400c0c006466a000403580c54018030702441c16214040a91041001406580d02c2085080c200002981d0200b003400c1800c403100780400548814201100b0082c25100c41441c0101d1002d04a84400054605101c0000070030300615580d100c000d0110781c40b1038805485d822b1064118001c011000048520010340a000b20103614a10b440d020000e420980815601c810f0800c0381d40d20660300c9014070349903281c0d10011998101e203400b0b040e14082450798005003c00310140402c002c0d004010040c603601a4000b030000c3c80c000114904810000d04003030008103580964840c805280c0e81c1030740548070180d90000310387d03a81603201e02040840e0103103200040c030b164061070040c00107041c2210180187c021b5000080343c43e203890042c07024811f58200d266000100014204400c2c05014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 901988417 1250 901987167 901987181
    0x160209010f2916051218090702150c070204020702060c010c1e02070611252907020f130e010c0e09090c1002120d060f0806010b120604061203020d03 65
    0x1100107840400c100c080e407881e0314010918800b4210400b06507000c03d0050502c45c02060300801c0c00c4580d0b50740c04002d00e40e8042c41c03243e0b5446000e001c01c070000550450002403409002009a0300c0003910b43e540c6007152500341c1c00520201d811030340a2281c080181c81d803001410040c0a41c074000308d00d010034104020300500801c51b105c0b54048085502d81000354020030076005032015450143c0c4e85031030381002c0600c1c1424031449100001d02e50f500c4102c6071400c0384007500c1502c5003400005079000081a50fa1982c1139108554450310008110620041c40d081d01045a1031001402626110541800707510032507c00c42903050803a5140c100c85400e15500001007880980110b1700046207040091040e55078108450740783c3d004000780100c1c0107215008003c2c0c0d000c07060012400390340d01e05003902118003030501403058408000c00e5040100b41c859020a10f981640c1d050300c64a0b00341001c40c0c8413034100c094003521494205980780d201058038008101030380300e0310340290000c4c072214122090043c00c507201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 901989667 1250 901988417 901988459
    0x6030807030219080304290a0902090a150b090a0807090222150806030f01060b041505030105010507110429030d020c0d020f0328150b0d0206160209010f 67
    0x1481880c030000844c0d000c20703030360450703000a4500c0c1c49840740440c1b5007134084030001c6444485051410002c0d91615500043c820314804d0b540545a80c455812000a503141e2261640819100c95002d001b0003514501800903514001c0c554070b50a079603036980505290713886c2c00c00403c0c1071700000c84481c82c08003c0c4403110707809081c1d00c214007041e04d06101c0c00368005811030460104010a4007003442641e0801001600300391000c000c000a03035071840e01200e10790051042803080705407100c10000707141c014030030741e4125207060715100c1c075007209507031102400d0855020b074a50081e96080009808250340340c0d05081c070480e00380d45607143c0100504061410342c600c140d001c115401002c4509030798a030300c0c0140c11002d81c117840008400405000107030600b913508200c40401180c0c10000e00b031015400d44002503060007401400c5040444040c00c07400d81e04441489034221522044480060802c200102071845c4014280c1607140815400140c00040a03072000801440e600c2090010186500098a640c50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 901990917 1250 901989667 901989703
    0x100906150804062003191b0e090c0403080406030501050f04092004110d0207021e150703110d05040602070f14060a0516050a03030608150a0b0d06060308070302 70
    0x100800024080790006000600440d111040c14210310914244080790b00008000c0039280c3c034003001d200c0b02c00c00650b0341c80721143d802d007500403503100c410640c00120700d580c0c1c1c2d548010381c01c0c00c2014065150340180600e22110410040040404d0101006e04050700e0940d5000c81d1075403402c02084441d822025040d0b214524100300000086c4103080071901515000c6001c580e004800340c001030040004010307106c0d21080000c0c0841600003141d008101e024400c46154100d54891031140f001c21003200b40341d503000144107a044400200c08000b43c24868402e00d01401300600400501e810034290074102d4002c03c00115040c0803050301031009001619465108201d00340c540500709580003000000c070b600845000500c503448500c00d400b200c441042c01d01c07296520903840d1600ca5511100344005400080c80d2040118103208041402e40d003814212010140540b68081da0000900e00701078925803040c0c1030400d0b0303070009100c0d02907100210701461b94203845000710f08019040820703003403541c88485 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 901992167 1250 901990917 901990949
    0x103031110060e061026060409140c040e07030804180e15091c140a0c020303032a0306060a030b01022e0605010509010903030c060204031a2e0608040c0e100906 70
    0x49040c0050454900707102d28014495190318000c14018000750327601030701c1d03000320b40e603100709900c4001b03074a441c1c0030750988040103061030107625a902c1d0035440c0001000c001080000300725070464000d450100f844002c900150b401c42e07c0c601c041c5010941c0c2d00300c1c440c10741e401c81001500b4006000d0403800309031000807138500d44603004004016030383c02d0300200143c80300807500980981c49803508102c5958050301b202e40e00e0030300c40003ca94261110000b80c08007600690702c20070407170605041d24041c0901a24441c02c040040c04182c010345040411a81140710f842c3c1f810000d00400c035031050f450440c10032400036070b500300b400050030349640303030802c80c14050100010041039034404214003c80360103140900742201e0502d00301d0301038411a4000341038235100c0399014140110000103280a05051048007040f003001da110140354101491660011000e03401d020040d160140e481d00b070b4804d105040d03e4544588529500d00625825501200c01e03015a107402d20081c40140314840140c400d0004140801e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 901993417 1250 901992167 901992197
    0x4090f050d0f0215130b010602031905131206110307050c06061f210f0c120902011d01120c020a120c0c210203070e0603070f05090103031110060e0610 66
    0x14844c1c0caa04140e04522690000300004444108007140c00d61200c0c804842e56944d55000703590340c00c01c20b05a032041c0c1c801c04940301003a00034801c1711500004030422558031480e2032403045203100c05480983d405511103985400400c000d00045201d10a5525200d40b607084002500780762900042156000d5902e945800707542075205044c00c0f45c1c1007100e10344100d441c0c407030203c3c0c2081d1002051500d40500c1c20301c6120404140701da0400f691058030307540c9107082c045005000106844941102038081250760034404035031238031007250520001c1c040c14030030000504443e00000712011045468010b8001501d2081003100008503841001c49910f090b003a00b00e41612400c80c4018076204181ca00b902400300e2011031404a000b00c40d5054000707064480069640400c13004458044401d00d00c00c1c0a81980400c5020401c4000c005a50000d41003140d2a03095940584010080c24100c581612980c00b00c071680071840d015400160181d84d078040d0b258185001030018817207029410b8414094a41405060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 901994667 1250 901993417 901993423
    0x3030304020d0f06091a0a0b0108011505070803010e06090105090c0a030b2215081f020a051e0c011b08160e0303040b0c060901180312020904090f050d0f02 68
    0x640445520300b82d800185030049a400080d04002c00160500080c4018030001c9026929460f08030344032484650b8647c047c00041786c015042090100c0c00b014010701402c807810307040f2072061019007041880e103000c0b034941d11000e400036407041d61084281c00c20000c00303041060019005010076900d42800c0d08080745d55420701d0184c600c3d80400c1540d2070b1006100ea990302c1d5004291070002c545282500c2d24403006110103400c0290240e030000c00350380c0c0b0000d807034080014003028020450003c0c2d1761a9600010700d0000e5880300e58000c0801600740320240e010700d0908130112004210b401034566801c61800e4280c25101c10380904503078180c03441c2041658580101c0300c0303030b400344400e8a055000c07001e2400603034002c1040e00c03003e80c06101c04a00807502d00c403804024941100c0510469818bd44c5000d5030034240d8500c0f0300e14020358424200d050002074012580f4501100810001504240344800442c04851007002e0544241103000c854030103000d070511100e01c48100034501360740c1c5140c00b1a00603607 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 901995917 1250 901994667 901994671
    0x608011b030231030f0f05010e0705010c06020318032a06010e0a020c011407020334080c030405041107030f0e061602030c03100912030501060818150f07110606030303 73
    0x10f802e0300e03104482d0350302c0100074550100c1c0181001d820b0703080c510b8004c00380b01402c44a540c40c08040c98100100000c0301412520305a5801039550201e0392000003a400c06001c070994a1010120102c80744002c1c005440d49049400103070a4402920b50b2031650030110301c1d07030007610750400c80c0144070b140c00f0308103180e9015440002c0581e558480109075401012200407000c482d0700824140101c1c550b0100007404100d082d051500c554402d8206a1042400d000758181e100c54508007440001841c4e2070090b1442d006204c0540741410354072004a030981d00c080412090214000a01500301604659050b602c0140b620f000c0304440b0803040801c0071841020312030707048030310703044118002c5540801c402c8402e10400b501b40c845008003086200e0142041d440d00320303a05070400381c1c02440d0504c644941412914503945080d19900c0f40c1c03030580180000c461105016000e01400010301d0301910f000d0502038085425601100e250400c401082c107900354100710220f400201c14400b481d40d0003c2504d07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 901997167 1250 901995917 901995967
    0x30916050d1101020c0307030305033403090f0f0c060f050c070918020d0c030308090a121404030f030f090920030c09090106090519060c030f030f0608011b0302 70
    0x40300b448807070006034500b140104903960300d403142c84808420554030401a40c091070710622250a8550341d008408a040f0401c1003441104640c40c40402400c2c0c820341040841b1070040c80c112103100441d071504170500031060b03170a440190102c0340420641d640b1055184000050b45456803d00703210740c031480d0700c2d0700d07203403181c08101520740540d80780c910440500100800d03402460750048030810300c0d00310300000c410301c400c2c0c000c03403c108000342020401007842d00c0110340c41000021800c01d4141c05445000011309007512402042c480400021400180b040e50980242c640e020b150242c94001010781c40660030004c56142402421000e6004510000c00d02c03111019000b9140e42e0b0700c0c20851114002c00c0900c075846201e071800003402c640c00c00c1401c820b44006444544034420317500700301007111055100300000900c01214642c0030070711800a00e01e40c0006490041419a0b010348401c0646030690040140ca942d20102c81e10344840c503210000a031681410254180040b4451118080c2c030027102c0b007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 901998417 1250 901997167 901997183
    0x50906070f02070902070c1e0e1810050702011433031c170604150605030613022a1606200105010b0301140a081002071103010908030916050d 62
    0x3400321500070300400d0f0250903514421521030040782004542019584190032540c43e000d01212007600f000d9103540700741d5403143d1801d00707561500c80f41101300420810f486443d0380034011800851002c2402098010865070b800890f075640f2b64401504070507800750070505001d40c0a1b02581101c91103088204410342e04c80c4880c0100a0024042428000c80148820761088211550302006800070310050442c1402c2070203180c26611a4140001c44020701c07411045002071507410082d82d80b10382e00441e0720201c050010000320008a14400aa80202c0200d0714030b603107545007070b00300c000c0d165a119629559400080c01d03402e01403040da5130803c03540e002d060100b04078040c40b04140e5039000001e40202c09104002c214541e92000000311a030130a0048100d0984240030340d8038180b405408034405e8400075006031405010b40c804a00c003c0d400140304449003120151301445640d801c1c4615800c0c0d034010040b070340d40e9103440049181400c4a5584c91201601d1010040c0300648415480804c043c0d400819 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 901999667 1250 901998417 901998437
    0x6020904020f2511060a0e0d1202100207110909011805100e12030a1d07140f010302121f1a03010801110412120908031909080a03140d0b030d0810060305090607 70
    0x1b04640780324840030066003285c45400c0703420400000c600c96605007200c540c00d44010707004006404d4141d100d10b00000d409042c1c1d24911489600c2c14110303040e00a170555000041e10705a0b0ba00b4103155000d58001640c06070001c0c0000c01e40241c1c41d0140000140c9510040c1c240302402c43c40220090202801c0a81e2081d0b82e2115564011003c401e036188000b5040c0c1102c800c9990307600c2090043d01541d0503d030184040c08445460340d40030f40292107440c4015900750f5120354940d0517000d620b9501d03c00081049540d00c1000500d804101070510b156070307400e4402696581003858850030344c1d4940080d0f54000c1d034100303c02c000d8204500300010103131740d004001c00050403000ba011188000950451003440c0000205400300010480c0d034804524071a84a8841c0130703588610b4181c40d1004000e0243c00700e00035510300701c004a03601004001400c04004002130800c030400120780741070140b25540c40480d202c2014000558000d4070240001c1455141c280100d2500b8208252035a1020300903605100003201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 902000917 1250 901999667 901999687
    0xf0c091005090a0207020f28151d0312070303140711030406030e03091309120810060e040f050c2214040b0a15050403020901170c010c06020904020f251106 68
    0x304d01c0c88406001000f081912510008021741030302149a0942c0c1c5408e040d10002d0101000440c881140b41d10780c60383c0038408040301648401003d80541c0907414098490700e540e01000381c5018005040c043d03030300024219103c0030a8440307888050996401d11803448020740c0c51001c00000c40c0c4c00d8801602d40420444c0c4c0101e6564614000c0e080c1140e44070005c107410902d00c07400c581c80318903c58050f80ca0408480158074099400110944204c050010b0340c900500c0b859024040c54610344d6405400000c0184400c580300007201d00641d801c01c9680400103030314100001040c1035040c1c0c14480d0881c6001c140c5000c48035440c1c21454140766000d0b0741c5403440c0c5203460341d0360036410005040000c0b900b541c14030f40a90042c9550301500049210307000c00e40011075144209104e0860a40d42c00001b4100040317400019036048001c1142243d4594080004d40b9240d01c03680040c2000035003000403152520440300c000c8040d1000c0c2a00a0401d000102c400004030f04002c4100c0c050f4101661881d0365110084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 902002167 1250 902000917 902000929
    0x71e0c120f08040902070b060d05070614041701060e070509060712051204030906020f0105090604140a14060105010f030e0607050c0f0a1514070507030f050c0f0c091005090a020702 79
    0x603005409207402041c00603004c0c4458000b0100d0520030b100c031108540d1400f0407c0403d50070038001500a41c44001e040c0700403401407602402ca043d040a045042941e600754420319046a240003520b10f0751590310030010200325809890304600c003400d0682c20b08212401064a500451402400307140c40101c08000007401182168440383c810280c071142450300d4180640002038a105640040c4516540120004018850300b40541103010140013a51581d450300310280445686410701c2740aa544c048001590202e55620a5400f410180503075601d404009812a68494000000d00d8100a032954000002049195100960f81020354a80303191092081c40d0600200c2080140d11505030380c07100744260340504c1c00c1340c4083d00c001806541d03001340005540d50400d039403100224005200748c4001a00a6410305103001207032910318100f90071840301502d4900d150f05042c00a411100d4183c080e420705070003e55000c00e161107104a221310302801f10b0718680d802040b0100c00f50b404a03113003045603144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 902003417 1250 902002167 902002193
    0x1823090d12060504090f0c0b09090a0e030f040906151403060910120f2904060906090c0e0402040e0607020705060c3c01061d13020306010b071e0c12 65
    0x103402085105c4807860242c2180d103500d00c080c1c904d120010750004141d503149007100d403004005040900c00752599002d0b10003403c480390685a241c042030180c0c40704e048400018000030b249140d000304465107081d03c90b03200100d0200503001009074140140c19090380c0841120f80280b03003a50f10f4a4140e44503544000d0b07080e081d0304070206030160561001c1c00d0050880b8003100f08d80c00780044807003104400c032030641c100708040080c00002d81e0050000d0080b403541c0e03008180c0306000301804038006555948224070442c5641210103140030002c140400d50400348140300210076290014410303401c000c0750213903032084103100781c501c5a14005030501140d0300a124a244d040c0c5900c17882100c100030703000c850b60301d1307000c4111180d5040102c42207200d800707405024030022605000000f810040020202e442c0c0404010070618105040440140050b241048a01c0c0207050402c00326855800d9032600011000e9076004403040b851003c1c0c0743c07030b02050f10300c00044201e404560014a00d00b01c2490881c0d4600c0c50 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 902004667 1250 902003417 902003419
    0x20315280b0909180c09070c08072009010324020706140103021903030804020f1801080606040b010926120d09060c2105060a1823090d120605 62
    0x2218000041d1901c0c880041c20020341c0860301103d10355191250241c202002d01c04402c1541d204c030071495100d0800c840d020360000c0c01d81c5480c0c251825030752141c411642c04040c2c00c954501100c00c0740100030062240e00301048000722070802c00c03035241d40c40c0e0000c417401c0070045007141020807140d207003100210303812181d149030f0241d42480480c4030441d0138140b003042484203030b000f60f468141c2c0784a109480c4100001b601c0d45038450b42071070340355078003071080c480b800060f050740001030207081a8061440c0c1c1d040318002d01c1c10300000d185902d4024184000e079450440014140102841c042c05210b8044280000150300300c16001e034201e8811810510f02000300ca90f0050030500000c417803081e40074a0704104441030040d40d050115500941c421240356a0710000883d80f107000701030404000c202c1d504003d4002a0043c0141941c6450340c51191024001c0d194040402e030340c40c942c05251008080e043c1c140d0323000d2a2003811103490000035031a1640c80b40c0307a0300c10400542a00c0441182c0c81d40d40b00c88050b01c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 902005917 1250 902004667 902004739
    0x2a03050d0e0105041b05090c031504090516090e01180213020909100504061a180a053006010b12070c0c091401080303090307060f0b062a01020315 64
    0x30f090070918000c0b012880485151704a00340c1c081210309100e00c1c8a4090b031000c00d1001e144d55624060f0388251103000c07a8841e8800c1d00c1e500b89001142c03081280d24072402c2c440740c1e9050302030b161004a0702150804501d00907143d0614242030708091f10b00f0340300740da9030f6015189500c3e10380102084c240248100750000c0c0d849910201813280e640400540101502d2040e02c1c02c00c25140c803500c51000c0c0c1d50202c040c0e1001004100a40c03802d00121800d2008901c40142c01001440e888030001007402204010f0810a8859032800c45008031051000110002c07010018002a50500c100103203503100e941c606042a5400e00f01042106124524520b00c081d000805018a0394407401c107100076100d50071504032198031205c0003180f886004401c80740268022001180750460a589100152401c1c2c03001044503a50365402c000f41e501c0310703c01400c40d640f81c00c00d4040d80203070b07114000b8808040719801e814070fa032040c01080701400302401c9421803e20104d031b106012204240b0002d000c00e07140c04207a00145 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 902007167 1250 902005917 902005921
    0x102040b0304141606050a090314010f1401030206030c030c131503050709270f09051f02070c03080904020702030a060204050f0108042307150e012a03050d0e0105 71
    0x802050103140103074403c140a086581c00c1807100ca9813148441550480c10b80c1001c0c040203614060401000c1088a6040880506640b43c03101c1883d0001c094003550507035100d00d80103480b01c54a104481c3d800c001d07642c600c0c4e03c5505640101d961800001c18041c024213000000c1400241c0d000c042d54014000c5150004c04a41c50350790340d000c500f85088200001c282040302264201d400741034000c0580b0584020a403640c403c01d20005408540c014400011580c1c610100b042c11005010b490803890240d4020003054039011100c011241184541c64190391051140d0700010b0703001c0f05407500316508480c03550785550400000030020700c02c41100a6045c41090454000c02c001d58010b00308840d1700302e505262602c0303070f980103440820040798010000410101005810340c1c0b1001d448840807003240449113000c0c0c50b108184a0030050301508004600411410301c80d66a11030b04241260042c0c10100c40074003404084844002c41c03109000701444404241c1811000147e801200f0359441c10380203100368 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 902008417 1250 902007167 902007179
    0x6030209090906060f0103020a110609060403090f08061b09090f04060608031612020a050316060c03020c0a111306230316140316061710080703061d010204 68
    0x2544040caa0500801038100003800c14403000c1041881418064a007580c0392581d400114000c2d40702e40c220b0b00901407005031480c11660208070369446010f90340000d203041e051605000d00100e40650004851001c004000d001c2c5100100e23031650803100700701150340d200011030b40c0388481d070103407041040d0000000b6007013000004602002902646c000c0c90100865610b500090ba00c074400c1c810b002d0a851510007056000803a81c519802c0c83c0c016900c141c640c041200d694040c210344c040d0443c450005402503200041c03240a01c00c880c20403107207050840c504090803041d15140d05070701c2c00107842040c211a8184031512520344d030100c1d4070703000d100030048152100c0c440040441c0c007140e001240c00c03003001d6203c040d040014000c1c0812101802e4609a01e260046a000d41507000a1454250050b00e00400d0a809065280b6010706a952074040702d21032110000e003000c0c40c2c0104442459900e1000c02c06c040540800c148007034940002000c201d401040101c004104203038083e07212558030002d800640f03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 902009667 1250 902008417 902008421
    0x30f0509060402040c0e03120d020403021203370c0309270e0c0105070b150405101706040c06031a10030c02210307080429010f0b0319090c0806010603 66
    0x416407084604102140e00d25001b1900c6c90300c00d0381c10303507015030100c4081038903480e4100107400c41440360700c800340c541910703640819188d01c040296200d4587c804640c0a001c0e0400300554002d805401096007291401a100442c490b01d10f0000402400b50202601d01450702c9090303040044c00440c0071008038a440d504e14a04541c501c1040c00508520b011072035150200003090200450005079551400c00c0e986880e5425000d1000d42143c1201540c21419540c80d290760203003500c0f03026090b0741e4107211842c08940b01600307403c1c07144000080e00301804210004901c4011b00059500515002801c412032607145045c2c071040324020b039071186810010a4001703926030401c0f83c0e030602c140d090300c10410540c2c1e401d0000341c3c01405d00c041002c20a000081c0c50700d10a000b0b017030b409409041100c120600794091004c070103d0141d41448500350080c010300403000c0000381140103184a035051855072401c080680c01c020020458444020788490945041c891a0200f041c05010040180c500701e503907c01c40900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 902010917 1250 902009667 902009671
    0x9060109060914010311010504030f0812090606090f090a1b090617150a02071a01260322030506090d1b03080a0b150403230f07060f030f050906 63
    0x2500c60a255010441080c9805075038014004102000300d0742c2d0855845401d07032280441018108002880008003040301807a00283c6140940c44540e9907035075a000540109100400b034140c10740c082e1050020300d07218440c1c0ca030350060441c2da001e2a03d4031100710a03402d00980c1c0e00080d0400107000c040b44000d80407113240000700c84c01004108409550f580d1182c1c000040c0c098071052a4101c400e04501c0c80f05c0484441d644045c51a0006180070003581e034034101c0c01c0c4003044025030109a00014820154107584031400c48900040d0701d260031001084031660b038490301c410b000c1880210510301d0030710004030424501960b800015103003140385c00d14400e0b0f134418041050400103001d80e040580701d00e01005000140030780590f034411440d0745050740400940540352100b5001043d107003940015811800203400514403414598500b50841011110500c4020000c9178154101126014088000207902c50403603d8030b0a0807204105068020f80c024550103070b0701c0103150704000c1001101980412614 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 902012167 1250 902010917 902010929
    0x100b0301060f1719080307050a0e0a03140708072d080303090f07050904171c0c030b03100b090708090a0c06110607021203010902070203030d3b0d0e030c09090601 71
    0xc40401d118080441d2881510713002034a90102003010501c0644100000d0024600c2030801038030380071203c0082400d04030554400e0301c0e070070710314900b0313000450b01800740400500c0c220004040f0b280c101040005000099252001e88c0d0030801c44000070188030074102401010714906a0303880f80f40540c000e5032103003414420305480c3d000c0c4c81400b103240e00e00b481003540a02d801041c1c0e054000703001c9540d41415408104032080d8000c1d04a40b01c0004941d40c084d07050410140d41c0d0109481e2070202c03e052400084400d51aa03075400d01e64445401d0b207a03a5841540015180f40c580159200c20418a042c540044809000416041400b2804603003007841d80c882e01d40a00c08031046c0d41c1e28a1030480e01c80c40b82405204d403040080004115041840c0c001d40312050008080d01e14148600301410101c64800d401001180442c188400c0014180141d00f966001100000b26410003241d100d25202d94071082200240180840b41c00070b207840030481070a2445c005450f0b184103007400c048d4240d40b54000d00c142c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 902013417 1250 902012167 902012173
    0x5270c070212010c140c1504080a090f14150f070c03020108010b0924280801050d12030504150509070e0601050c072c0a060f050a08100b0301060f17 65
    0x11000d000c030148201c6000c520a0b5880403003800c1d00703004684c17456020b2000349540e84106110100a0360f8401405805039110b81d104642d00e215102c409401810707140e0142580000c9101d0800c60607128040207810403004442841540800403401e0440c0d000d24030020700b00080200d07001003003051922810042d203001b600c40354066a61005130002910980d005240c021551108840301d09200300402803c41c03052031815824143d50005032200080b5800d4140b01c0e01c000d060103415095000115103003d8a029196100e500358282c0301c501c486001000103004150b030307a000040034046100305103a1404a00c1034280441e0070180901960f4003500d026694441201c01c0104009602440031181c00ca0a5070300648000c0e4a020700b03410703424007001421084035010800f602515100d24503410b02c540c00442c000607455040416840610001d43c020074028200448103004800000591214540340510302141d0381ca45171021a02420702c0b90702109084000140200f1422958800f000c8100405412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 902014667 1250 902013417 902013439
    0x706020c09150904050118060b10050901020622060603060b010f030b10030905030909010305060f06041103150f060a050913090b130309080604030f0816050405270c0702 74
    0xc0100a4038291220b0900700070a501001090030503e5a595003d030141000091018441080c646400c0c480b2404a40541d542d600715142450084401100c801c0fa52504a0500d0704150020307558220140046004840302801c0075601d0900050301c18405038440e81c1440125500e1034840d0240000c615503602141040d2407035028a4401d110f595080d04004004104109001c02c0c00d1740140b014243c190303510f002c1000110144d0b15420001802140714800601c6103241c0722080500781c85000d88030901c11410200c944a42c0305405d03007503a402101d4840e0408025040c10001040c00380030f10380150300100007142d500c0c60700382c02502809005505030740200318100d6903041750003280c800d400000c02104408012400800c0c948201c122410701c00d04102035601d8517124110300d0300e42d040310f084002400c03144031030b6203581d070040d003c0303800001e20a2090300350f06c3c6114002c1c00500990207081d0003140c0b44040d1084407003100d05004400b0280754405680e0323041680c4604d01a81c4019016401810217a030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 902015917 1250 902014667 902014669
    0x22030306081011180117010e0f07080c0403060b0105070507060917010920011709031809040c060509010302070b0a2310090216050102120a060501030908090d03021c020706020c 77
    0x10301901c2c0b42d05040b550700d840644d0100188000d03940d05100d0420030070f0800300408150700d0311000d01a04000c2403001c028942100100c01c07410005080f60200701040c03042c45030030b10018041da0141c03a401040400c09003d4900104d5250182d40c1c0054520301c0340120000300ca5820004c843d00303807040c00c0c81e402500b80149a80c0c078241d82c1e42620082c600c1d0b41e50a59460040c1c2881415a00c0610502d8000840b10a0401c00e220b02c042c02c2d100c500c10ba40000a00043c1c004800504c0350320f440c801e480703492503442e00744c441c4401214030b4841e07141441740018100c515a84280e04603240070303902609400c09801d121114400501c903003284c5140c10700541c02074442c00ca10341c03014184076241e40701100e599a4201201d44003e0f42140005500d18039850b4031642c0056001e001414501c4072160350040d041c600858070501341c51140e030005060602c1d000440c800300e60150102c40d00c151081d0740350740e404015803a0491400c903420300481d54614480000625042e40401c940c0d04452041c0e00b110b1403c902c0d08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 902017167 1250 902015917 902015921
    0x5040215120109050c040f150912020906010c05030c030c0c030d02010908271503100e3102090702071517010312020f010f0609060e150603220303060810 67
    0x101c55510036650201c01000016415000715034803098004902d810030b07503180031030710007100141c01101030106406601002294450301c1c00004020070800f90340c00224680100f00b0907213014042a04000841070841c05200c820000c54030140b00783d400f00d9548119103045140c581c0c460200300e520130b002c5d440ca4210340071700c140112901e4541260f121481e0a291301720000740241c040024804a100c20701f1403800707507584d05101440b91201078001c41e64034506640f0380c958a0307006800070220a14180180300d2010f0905511251062240012942c006459515803d4410040b14020361082c00d02041006090b4041808011200c1101651803110384210080d2412000e140c82c40c2000c0300301000401c08036506d803070403142402c228015229001b1109100c2400c1d1141c0903c0b6000060320b4050400240909204020090842c415105801d040100703102058845034401548586404000b10740c01c40d82d00c220504003918100c44540402c41c10b8074029020707000c1842800b04901402110091881d224 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 902018417 1250 902017167 902017177
    0x50102060f070206131104060315050a09030203040b1e0406020d110f0a020f1206071e080f280203010e040b0708100e0702161706010815130f060f05040215 68
    0x160090201d990740c420700704164204441090301c5c0d006c40000341742030a40b10762040401a5020754641c1c86030b101182a0030043c1e40c00a401800800e25100c080070101c0e5011065805548146542d107130b540c12651482e01c00340441244850305044005000100e0070380000381d26610b0a50360716640c414041522025450380400c1c0b200060300e0700303d42082001441c280085991008008109958424810304000c0c503190003201c040d030100e0003102c451300d181e41c1d004102d00e000c40b046107005000d514004100c0d00d400100503084424201000140101c41405618030006070003454404541702d40c0d44120050200c081034030240d456518030404261071a108213072a0b031098050080c00320801d4a070031290684900010b051a04600641600101c040019044c01c1d0052600c02480082000300316070442c100030060f0710100079a4002e0116080340e1340c5140303915610400c80400c2c02c800d10341604000c803500d26080401400c03140303007485e03204505403180d124602a500944030301254a0b55143e08038001c3c452 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 902019667 1250 902018417 902018431
    0x1e01090501110418050c0f070f0201122003040201050f071a061f080405071211130b0307090b0a0b07060504061b3603030c060b03030304200d1b050102060f 68
    0xd44c0390301e89031a80503400c03141d00800e0110f1842c4c80c044c20007000716001c0c2c100c450100d502c6c00c19101c1220656a10422140902c001000c08200302f160940540300680031020007440d0340707031001c000642035a00030006d07245400941100c0c9940e500651070017551154406032071969011041c80480c10711704181d000b40c0e0202d080620481d003c20a41d60050b0341c0c0c240c001300122030500c580e403004100c0c0210207480c5950704c2e2040d0602d040e2100c4420420031a5200805044201450302e0344207543c660300000c1000450340e610381d000401049040100e0389072042a000903006903070004d0900100f0510f680007030b102d94000e100070000c2c012030f0390b0100c80050112100c000021100c82c4c1d84040180181000c116401c8110050a400d40460b20315842e840001d5105501243c1042414014490f02c1e0140c1c2941002c00c40c00b42d4514a06640c84112010012425000014a003c4000117944504989852094014052045001c030420b81480aa105400707818014000e05010401650442c003e80b801044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 902020917 1250 902019667 902019689
    0x20d0f0306030305090f040f0e0a05060c12010e04030c0c150e1e01180e04110108100e041515090c1b08030606070302032203060c0f020714031e010905011104 69
    0x1c801404c0086c001e0f010413115500998680e23003261450100d105182da180c035200003074010020075042030b6091020040031103031020020400050042c042840850669a2140303005405c1d8449044c12210101081c0e8000d103c150588400b1500340c030650350071030700171a0076a01c4901c02c016140a018883e090705200b842510030480002c202907000380303070400c64111100301c0745400543d2059402e58400041d42d0035502e840c600c0202042650b401203d10b0307030090080841034000c0d8035100404440c818020400340603030080304c00d001d16451b01500903683c0400c02246c10342a1f191200d279003100a205a5a2150104560040e1017103044440303211500341c1c07074203c580306095584080030700140354040c503c101c1c1140000c00c00c0b034800c000600c40c4010b032100b040141024007411803030b007002192405c034242400d0280d1000a45021680040c6040c180d940c050b02062803241e14070301007031404000400d00150607440b07118080300034074154848113038140620004c3c40009085500d07584580316500039915608 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 902022167 1250 902020917 902020927
    0xf060717012903090a0510090204061d070513171c0f0504050d020415060504050312120718080304030b1501031104061103071416140a09050411030d020d0f0306030305 73
    0x405070b071002e554800140800d40d84a205141d03903107403d000c000344802207060750b903141c040298100b80c401c0401410440324090030403245440075114625000b0101c0080100004401c815041d034190a00020010030f0000d2170b009401808081e103035042002c60303c00040d40107018410591040099030520700c0d1686a561509007000c05000e041c10380b8810070fa8110703841700c801024115240703404134000c1001340c3c1c2e90382c0c8a03401c10702010301301442604170401d0001c06200f11118103010500382504142182000d840e420402c80c0030030a071500c1584511781a000c082000003e00101c864414403e00a0041c02d000c4440ca410054085075000c0c5414044034500b0300041c800300b40600c0ca84031440c01c2a500b1242007151541d0344005a004072848440c103034100300b0030401d8003424a10090060031610700030210b2000c1e40004a00310114603c10380e20b130240c0b40c03404a1305000301078940700c0346481b02078190707014012102006940ca201440600c00040e21428034442c40c144648110000c1d01ea0583d140381c641 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 902023417 1250 902022167 902022239
    0x406092901091701060803030c041a0304020f0f120303130317160c030e0607030f030516050d020a17040819021f0203060103021c06080c010801080c10020f06071701 72
    0xa85614140d0f6040b9907940e17802007503003c420009544a803170010030580e82c81e03080c47c0025000c80061900c0c480707200b070144113120060b41d614060b41e1542405841184075400c100c0c1c001100c1d040442e0405440f07020000c1841a0b180804804151070b6009440f5000d105240030650008080c0c2200c09a88002064480000c218420075250b5a4203000746030502001041000240e020303400300d042280426010f442010380a901401429400060284000079030400c0c2140a000d80c0b0a005140100c10341c000b50a0704a41d0007180500c610302c0908d0545842450035283c005010b91045844a8107803090250701d005e540c2c8001800314600402c01e031490340040402550340069040a8131880c1450b40a100c0341c03022291000e140302c10030b2600040071a10611308410300703040c600002001c60405c0342480040c0004000061803a40d601429145031100d640060422420b11b4601030030309400340201010300000b1a440720f41d81c0182101d0703525000e400e90383c41504400c0825440d80d5042014000c6070035581c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 902024667 1250 902023417 902023439
    0x1409030405120a060e0606010906020102030f010b0d06080303040f0605010e01230a15020105041e032123060103180b1302030330100305070315020702040609290109 72
    0xb40049000300e40b60440d5a0b0707601030650740c1d1046031226541c4040100855903038403188103c0100341e0390000b180b8500b07107100b4200540b03105001c0c0990381d5200092000b0507440590041c0001d191b01c40c1926240c3c281464544030200400c08160742060030400081220a00b507400e0a04030f40f0103001c07648900804a14800d40040909141c9a04c8424800b0001d0030102c6070039404584105a4000500c62600b440c0819808a2810744003403540601d20311100001e81011000c25124580314a040030303410f40e071001038060081044806859500700c1003850444601d90190340c007406090300c0c10b002c0c81054083c1074074648a010801f420741c0300d229000c1040c0009054a0120290000e401c0c0c07494000100c00c4042e824400c54002444d800c284450340c2403002001205c140c004c0110180454407502d1510341a660301700c980801f0780715200c019144600380c8403d42c12a203a5507400f510900c24169990603002c010300e1410700182da81007240e49400c500203550200b0307140601e01610b80b0131465050440d9404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 902025917 1250 902024667 902024689
    0x503041a0603120f580e010c08010801180303051b1b0f1207080702030a1b0801150602071a071e060b0406030206030106030216050304030c1806030b0f1306050a020d1409030405 77
    0x40d038a83d0070b0401c405900c1c154046c81082107900c074008180e20a04402c000e005060582c071507140d5074502070010150700808280782d0a815018075010030300b078076101002480b61940901c400b84000700041c5040021140d64034800a140c3e440c8241d07008902d455418588540c068041c0101c01c50b4100203110009440c2400303084001e001404890032200f495132460850075000d11038001407064400c1c1000129000d0065044402411a0b2403561038a441c00181da503076410f00840b8420241d200849051241000544a4276500140843c0d13000d42d1101969102112001041d142c0d9810b00c500384c1100d040c40d000d90b004583d4080c1c030807840c40c0c1c60400c04034000c0d00202e6884490741c01c2483c641d4007081d002c00107030010718050300d280c2001a103000d40e01e00010051901400039075080503030030004a51004070b00341c0e0207007411585c40030a0350784010000d030035201130a0049c07120749820180201010680c1c05428800803c0b4410806480d025100f00c1d01c0c5141120440402d81c8200014045405d068400311 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 902027167 1250 902025917 902026057
    0x11a031312170106032012131a0c0703082202011112041d0714160201051612020c0402070b040204020d060e0a0c08070503041a0603120f 60
    0x40e2642c1060700829000041c2030340320400098a41a5180c2011103440b400c03a0400c40321a88146020828214000078500007450720038810b403294022400e010042c4900c8031200350b10700901c00c180c038204c81c0c04025908500400c0d800035040c0c0c00007554102e05082d020856401003d0f031a1814002c40d8011280d200490817010881d009030a90100c0404500c40600064404110344140240c80d1615940a010f001003082c410400f20003030703003018014890120351600d412510f0014540c011030005035818404c2000501000502005180500811080d17607090b000c03803942641ca010348088100404d074000c1207000b80418280b407022030014640340d03000b411950b540c4000030440c0399851300c0c901028601141c50411442e11400c040f184150f02280c1581d1000480c20000d05605180d103441c81103640080748104c00c440c07048045160356030200150300009071010039841c0da0f12034480c0c030210700c2e03000116510184a981c15440b0010001410b1050100c202101407091b6030b0704150100d00f010381c001c1c03945 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 902028417 1250 902027167 902027177
    0x3030c0209090102045f0d02062101080f15060a030c03050303070f051321060f061403010e15180d09060e0405041104020a090914011a031312 62
    0xc806c034a044010340d2000e40285011300c00814008895901d9010040141e203c802d86004c10601102c665902c0c007154512000d00c05c4109003000108003c1c0f0030342e0300302940c86080070400c1a10301e00f290000b0341c0300a002265040d410b981e070303c02256589110540b00c001c241c20003452091400f24200310f03154400c80c0101607020050b41c0b5102c8004600c1c15130415a807580001003003111498200004c0003d00c3c0061500900d40086a86d40020010060040200d220b084600040342c0301050340303804400301d1b0440d800700310401018a528004080c6031068480082c0d070880c1403034040c601807042c19030542a0303801070000080011110982c900006007010039004905c1407100404004100c042d80c006103586800951504050019006100b070020341403059050504102c0091a81c2c3c4144900c41d005450251b110640c10006a40141c119007080105030310b0404c8409038041420b02060499000d22020500c0041080701110180310031140c00d07a40c3c41c140e4904000103030008803001d40704d511034646 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 902029667 1250 902028417 902028419
    0x41e0809040b04110406020303100b0403120e2106181501090c02030c100c0e06070c091802130207110105070b0f04151503020a05061602040e0f0f1b010903030c020909010204 76
    0x41926180c0242d00311b070300113900100400007610304103a0b100018080c0c1108a41c28035145540d862100c805465944d01003041905200c4010780703030140249a519a4800b6030700403508002c044a070354000848401000219180509941e95008520460251642c103006115a0f0030f00403c03502030041d485a1a045100810001640100902502e070700b000842c500458801d089600c02400d4040e84103116211354020448030001885a08804044842045000c149610038021040b0a442211406904091030508490310a2401e60003444920711a4056603840081d1500440301405101c80042c4102020804580642e00c1070700082d52207441035110a10010048480c00150350421030740400c034241c0c4020510841c5090220107000c0c0105640b86410300406020400204400c3c00c0064025035403110b00d40d60410003403080c1d400b12020042180d080d099480c00c642d941d51011302124070000d6004c00b000c955907109841038001c076901991480c01017a6170b6002c10640d0324015100e000e5035942040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 902030917 1250 902029667 902029691
    0x50910110609030901142a101401360506041d061504020309070501080604090f0c030614010b0a0f0e0a14030114071b05030903060f041e0809040b04 65
    0x8500c1d880348039903902031903e5014240000d072060044512005803840184080e1034102d143c07904000000105244420040003031800b91410059040d05030756945042106141c102110201120b04841307500001c5611441c0c10000900f0070143c000455070203611001e281c401c0c51079940c0240d6002040200001142e9018062090441d241000b9545680d00b289080010b2030010800350028020706503025407071454402901a00d641490052505014220307011031010f03104c40d481401c0d0941d2250641c0607214407420070070380e000241d00c01115a1130610352641c40d40c4400d8000340b4125800003403c03d0404c0210701080c2c07195102c0303c00960401409002109140e0384074010305008050082c107071000d0740031043c103046c00c4d80c20302c2c0854119001c0580a100c03002d40c4c0000c0f1015081007032118400724154502c1c02c0c2d0b0131031103004002c603030500c2541c0c140040d225061800c10300840c031843d40ca1490382d000905c0e00038020032842d0041c08000c4140814601c0d4189600700c101012002440001c200d1440c1c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 902032167 1250 902030917 902030923
    0x3120a18090b03152a070602030708060a06110303040807150c0e130612021c06320424020f040305011517191109070c030306060e0105091011 62
    0x16108035407007601e4003200d0000e41800d0103506440306040041d05541d25000200d4803209070081480d0610200021a0000350413580040d105060b6011906541d83d0070600c000801c1036809403101c910030324000400145071380c01848082c4440300b1800256003950790f103885041842d0400c403c281c5001b0040301e541c0908408a01c5151a9500c058503114400d0001c0b00c01d028070000c20001d50800c0c0340c0b401c60148490105210801c4020b41e0446848550034ae0308100440c0c89940769070010070340f60410080400307070000403001182a10100207486004003007500c01c05403a910a0380d02501c00c3c0454401d811012207420004d850701041144058038221000c3d102841541c01a801a07030341d40d640b011980000f020f261481c4000740071450900700700b02e000c2d500c0e10384c031084810b50000c0b081c1013110f1358000704040d01803c0304c4a00c60003811810795281c4218047d100700e69452048000a1400c50701142583c0030340002c0038488810b07503941e410b011411040c4150291400c0052080c00140d100032000d0110030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 902033417 1250 902032167 902032169
    0xf08150402160314130b03040515070305060f010825020c10030b0906030102070803070c051903171b04050f0333150603060d0c0e010605070b1503120a18 67
    0x100d0300e01200400380b414002e0808074030b44100013090300d040040041074002035030b616094450310030720036540e1b40b2149420b80c070f80070070351140b400c01c102860100150260543c3c0154441c59090300c3d0307072000124003001101c1e041e008881506030b0711501c1880c0f0f040d051000105500324400e500480d011b40e400c180024081c000d4035130807000040d48482100701e081c14000d1015412180a600039410039249036180401c0e4000140b100301000165034107801800340c10000804034040c1c86c0005c402c039075014100200721280c2c40050743c0c41c0140c100080f030502061b102e2200540001c5c14403840c1070508003010401c80d00712402d0400d0f8035202c1e4034401c001c041c0c16075410500108890b001480c0c0212018240000701c0c03001060341c60303000451244030220361114402c89900000c00c888880102d0b02901d440f5092561079041003240c41084000400c0c00c58000b0000c184540c060442d0403c20303501c004802401901c1850241d425400c100c0072103916803012006045d00340030500b03008503421030700708375000e0321307003071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 902034667 1250 902033417 902033437
    0x414030c0c0301150305030f070c050618040b010c0201230d050106030914160e040206190203090a080a080d1116030e01030e21030a020c0f0105090f06070f08150402 72
    0x200a425000c0d2900b44608800250400a200070759859610303499240c2c000e2300741c0030044850014105082040c2040202c015010003000d4640718000c443c0c030f00e003100340000082c0e80503c1ca0601c0f000b2480d0b01468040c0d01e4954140e64036425650700d01401d034070500c0481c00d80d441d0703024140b14114242c1a5030040c103005c0d280303503540021502c0c01c07410150110801e0200c0c961140c0c00151922080140804904007a2084009038060300d440d40e00c0410001e01c0303820041e07041c1170341d20141542c00682c00300c01094441c204650344844542c840201c5a00d680310302500078281c1c6030030488114801001e0b0400c001070010441482d0074034001c01c220900380d4a40c0d240440029100180040c4290b0301449a0551524030000400d07202481c820031881c0040001908140845c0200016030a41000d804852039084a401a5042d003000b14040314040c103010398a24030140980d02c403000301240000307810703440740031690b4410503810400a03054810b04405801170b5080c0c110040058000d440b80e000902040603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 902035917 1250 902034667 902034673
    0x50402030d2a110a0506040806010e100e0403090f08070b040e06010e0a080709050f010503030703030f0609060303080f16050a050a0c0c030f03030f0204061d0a0302180405010c1e03050414030c 84
    0x5410f03420000001c03280c0d040f661040303c2c240700501601900241d0581512030703410b400c552548410036100c10740d8290743c0c045409000c03001c00b04420142e000c081d00c0c1c03c46a156001044c1c0580340c00340a40c4604943c0201054600d050100300b10140c0c1c40190035030090b4040c1402c024041009010420b01c028035040182e80c2e0344102e03400c20070110107105e03040d0b005511504a04e829414900025103078441c240000d0100758031046140d0580a060b48800001c000180b0200700e1182d4074680940600d0307044402d40050202000090185100200c440c42282c5603607981d207280c140c410809031420b41004c4515002c1100320045840050400d12020001e140100244405c950048c40c0040c00d07202c0c5400c214505500600040001580012080e88041d1091381100b02c4d641300c91010030a10075041c1e002a5100b000e582c0d002c0314031080e280e4550f000d1801200248000c0140c4107080d50400e1140c2103032a0b0703414010755619101c902c40d6001c5508244a260384140b0361b0201000149541c000c0300d00015030790 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 902037167 1250 902035917 902035943
    0x2304090f030c17120f04060f0c030c020f0a0807140c060403060222180e030c060c2106132d0f151a280503060f0103050402030d2a 57
    0x1d80c181c26000b080304000310f00b45490500d07000c60761031030000b9006850305806580481d04001554000d0710302080d280784104040303e255680200603004021045026002c0e4420341ea01168011400540c240e4106807001d1074007026980321f24041101000032203840c061114041c4160b551140104001d41c0a5503002d6100d022101c10f82100003104981d011403a48013501c10089000d4031040170549050700c00300003544001584841c0e040d8440c8020040c0d05014100403c42c07180f0303d0030090003601c07011a019070740c410344289265140744415944258446814204c0b600204055000702c40500d190b62407440c90b0701f101600000391038814420889200d500c0b0400510010964403826101080c42c0700030401203845d0541100d8400c1044603e00320b68400090210010000240c000c15a5428030303022910b45402c45500601d140c1041c0d40e074a2040c001c00c040a0303d558880e00645004540060140c00c1c9401240c1c001d45220050b41001c0441211400360f205440b00070f400340500c0203020b2078040d0686 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 902038417 1250 902037167 902037173
    0x9050607031b090512070306050f100f300602070f02040b06090916020f0607080a050c03060102030d0f0b060705010504020a06020a050d2a210203042304090f030c 71
    0x154010b002c00003805241d0340c644a91040e4040c0000c0e04503881581c6402c00c4034a290740e02d6040101d680c02c003a00b5030b4142420b00c26202200f140846c418503c0b607200c2c0708216298014103a07071015500c80c0020464103031104800086850b0584840e08500b06401200318510390768440907a0000401540c0341d90f460340c1030005504040c055074450580895005240181c0c4500240e03045c24064006100b52140104800749640200100d07113058400c402100c00500d400310000f04440c0c0111605030000b030910003c20083d23042d0030700b0b480c05490140c002d14200f18000d4108001424141d078010300e11500c490f4014006d445400c000e0032502d0040002084070300e802c3c010f10403550035550011045500c8440000c0c0481c80209031044103888601d8000e980c0a02a0001d14464810785400d80c280d51040c0030107c200036000d40310155092926102c1080c000300101c0590320303030213035105e817010081a226800500a44030300c0b50480007030006000094550048d11b4100501603890f0048010030401d14420040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 902039667 1250 902038417 902038421
    0x40b060307091a0f0f130f1d1b010201150306050702100e07140901030803130f08031005190e07110a06140709090b100e01021c0f09080102070b0f06130905060703 71
    0x100c0c04217803109481400c0784004101440d051105034001c0c1d590f02c00c460b08400700301e500803640c251542c2074658985805000140e45400554265122007030201020303102a50042c0070b802c5020802d240d07446c0c1482d255840e81c4000c0d00d0300910007021400b91403401010084035104034580803880c9002080068101144a41394040312660507101d11006170041000510703003c2225441000e07001e50960740031103842c2030241c41c41c0c244801000c1403030203c01c0002403800d00345078204603201240e0001640410b11881c4021744800d00030499620300703034800140164095101c10b506802e40d00e04403030355a01ca03602d6003000c50f200c010074001d140c5020414401d01a9000d04050041c0010900c1009411010000076800a000268500a100140c1c100307002aa00a0009a1130b0030074808c044c0e180340710a0304000309060f401d0507000000c103054960100e0128014400d4030b500643c480f805541c1a101d940403001c0c0514000e02295100d02441d00340300804096006031034006200310014041401c0c0043c000d02 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 902040917 1250 902039667 902039689
    0x10911030f06190b0a0b0304210305042001020f03030c180307152f070303031a0a0e1302030f030d1803050a030911060c06150303070506040b060307091a 67
    0x1d0300e034024000d0004000c21032101c94070500340c881d00003400483d1500440c441d40c4c00b941c00b0188003e000301c02c100a1004c0100c000060341d6a2003a0160124038001c07003501200c50a480181180e003041c81c20110000e94001c0d102040d0750140110744041140c0080c051840e40112507400015a0101d0b00c004001040386075001d0b2032500311702a000803814081c3c52950900c1011a0204020030020320040409034110202102ca60499000b8180507411b5091952001c0500c0b080b000a0b203041380010101c0d5031a440b1000c442d0300140007612030341c81d1075041411464003a0111080e00448010080141e50401010010081480285460b448030300c1200003207038082c8160018016007100703040b001079403090460f40d00d000c82d800c0000300a609801d102c1500c452036001140c11000010310446109000501c80d403043c140c108040c00450420014961240100d40d0028900d52009010a0010300c0803c20039a000314060104c950312a501c148900603222007600410003508011180e641c2e40c10840000c803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 902042167 1250 902040917 902040943
    0x7060b09010e0a1505040e030a1106010f05040e03041e0e010e0c030a0c030902130f051506041a12131103010e0c041107060e01050717010b0316030e01091103 69
    0x80300035031410091602662008246000e039030b41e29140740340f6040540844902030400640104620014440f4061760f0381d0280155a010415081c440c0043c12000110107042c0e48040400c051440e1a0600780400340000300c40245840c00b0a002c0410451047c5040c924900b00200c1c0e041c0e9820b2401d407181e404004180c2043c0907a0021008000200210000f101d4111007243c20018941d0406801200100074158000303520850320311648048050940200d9550358084d1010040c0da128680355510b02c44048118542080040c0800c1101c017445030202c0d41110180c14105140051800140c0d518400c00c03100c068041c0030181401d000d10100201d44904104240d008010511042190320ba4038245000210700c07d41d02d40200308401200b20094910290380320806002440d200075841d8080c02d42241c0480000369900030900d0320188801c40b182c1201e8842b55080e2940d11500c3c80d00003c100d40c0340030001419120620b000000e1310034800c03100407901a14a5504e11051b03e81010b007881400c50340b003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 902043417 1250 902042167 902042179
    0x519120804080a051612090617090d030e2517010209090a2d24030c06080604090f15050a060501090506090d120f1206060c0b061207090207060b 63
    0x20001a600b04121040c1c820309062103a100c0c0920b40c0e241c0300104c00f1400040254401902c90824550041024002e03a000e603181e600019800d610308180f013a004442b00300a942c4010024100e06000c0d50100802091103000e840b5644000b1000702520605000d06040480d00320904010708669030200c0c02c0e82000c15402986050300d03140c002680c003040a0311300e01034a651403010240c0104005442001c08040c10354042400d17503656286401800100d01032034502002172034014861f80358030305030801d40e640b190080c1c501c21300341710044401400003801250015641c0300d4110100750a403e40d4000e89210380d214120700b004880e4100e00f03a800c043c200031065400c0200500c19a81c0240340a010303540150784240d1580d070b4050000c0d202c900101d401501d07074904125410007990f4040981c007507905042c2c840c1e151200003404603400b15005442108002480c2400f0000001d103004800780c0c028100070300084610b13090b003e030b10341440c41c1c2e07a00000c00e01e07500080b41c008004c4d850048101c043d82c120f80c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 902044667 1250 902043417 902043421
    0x819021318020f01031b0c020a08030a1e0504050d0609060c0503090307060b040f23010f1523040b070b100311090405010e060708061905010509010509060705191208 72
    0x101e030003049200c0d00030701c2821180700a0800e82d21030b078080c2e510880741e20711040c00d200c1c410402030020020900142c3c0100300212000c0707881040041107070400307611a0340d0181005101c039101d40075480101c09600410500304400103255542081c00c6c251580500300004440100b454410b00b1604000030200c1880b00a00810800c0100841904c000642242003c01c49140060015000305100328030740000e00e24016034100700139030f51001d038181c0c0c2c90725645107085646c0f580303041180c42000d44940180c2900004055040350710944805608450103070441e5515091540202c603c0c2d08039400030b0301507010200e41d00c0704bc4a45c0d910b0303240d04421011901e6201074119240c0100403003008544074010b01c20000490208a0250300500d03c00c6109800d6621324100018020003185041e038107240b24405c22500c3c0101c1104844005003280c0050315628540300c43c6000541d200e410aa040c60780c4918140600380201e80c00f8085004000000750a503205030f0702d940b0b0010060406901800204444101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 902045917 1250 902044667 902044691
    0xf0717040203032704020d1521020d081b03030604060f050616030504080714091e0f060415120c0e13201c030206070c030206061908190213 61
    0x10486500900418a5040c010144c0a240c00041800520560001d10002d50f90746130030b4040d803060f044008c1d8456010011907a8503295201c600d1184141110321b1800c003965401031a088800916442c49402c0c3c4508010301120880d00100401c001100300b500000100100e902d0309110f40c0010b8802c1c1f00c0061489410f1a01140b070600841d07400202e51001061404240750140c03064400501340c0030100c0304640e4440c03100081c07055040c220035000b1310524000c1842a1500705150f9202e101d000c0e07040d0a99603030b000680c18120005001240c01076038400850f9245140c0000b80800750400711a2442450350f2864062054181e950102181e001028107200b504400402141d403110742064001c6c1c040e560b42c0342d8445554051000c8039900214900c50341c18500c1a100100011074020740940e0f866541b01a015142c210f1180c50040044e0001c00000e42580f07032140c04802c54443c0c90030f036110065190401c2e507103801c20111500700c1c285c50b026440c0e030441c60902c842d4034071044045000d02c0212600d175 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 902047167 1250 902045917 902045923
    0x5010506150f18030a11010906140901080711150105030c0a060207060e13230114010504030204022505030c24040201050c1c0c0507090207020d08071a0f0717040203 72
    0xc1000c040031400000c42c9038516aa40c469480c0030440102030f038158418521707000750010540a40f540c00304080d02390028030389000d0305130389074103802925450f850811000011600c000d0024032000a0000000c00d03071011020401000b003411001d5019010a94100302c105481e00f41c504150b80e11919441c1e10030300c03d0540c04900c0724200c40c84c0382086600011200002503178000c2c014035401d000ca2400b00c540070780005c0700101c200040c030800e13244034942e6241c0302800d41448011500d9800300d04204810001403c0c180c0c0184002c038100100c004644000c0c010406581d02402d05c25901503101283c1e0300100c0d20103124001200d0b5140d0310180510405818100468100820182c1840b0012803007c04d00401400444a03000002e03600d00d0103030490040141c001d5410710401d44061184407008106060113108031a00c0320740041021070b4814141e9241c0c02d407584400412500ca0007450070080068500c40b50803070050900b540320089520340b003a402421443c0400341c0f0303c0c0c1080800c0510015072008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 902048417 1250 902047167 902047177
    0x3060307060f0c0b0c030a0e0a0b061507050601270501060c120201021b1605060708040311130f0506130b010c0602030c0c0703061406010807080a0c0c05030d090501050615 75
    0xd400c0102c010300007504155203440c40104080e014007030300c904209400000300020f51207440d98540805c218405903008603a5001c40d03400080145e19041c02103035091603c40c0b14014080c84180801d0b2401183c2d9807035a0602d0000e90000031402c44181380b60208603003440c1070f17907015008a00204032540c5070480c003c16411008201070044485405240d00c07042c405e404694a062a104901e00e0502e01500c00341d0340c07140c1c110b110458100350140c02092038680030b42182c00c400e4104003001c3c145400c685810310740041e14000300b0f511070350f9a000d1301c107500101d0086201000340c20100140ca85010424022286100c03004030340094980300040340c9507038101520f0040d05411000040e22035540c03030349a80d95442041e204441a1103504800401c101841e0441c2c01c0c0000c900b05484803580750500150740601090b0b90810200701140001042443e15520021140f1540c0ca0a4007007003045032030703460441e80700c2d0f249d000c2c0054544400ca4240301c000d0043c20707003200046d180390349110901c0000903003038015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 902049667 1250 902048417 902048429
    0xc0904050c0d030302093a030905060c070503070902031005040903051c06171e150a150b180f060a0f0809010e030c0d14090109150c08030a0204030303050a0203060307 73
    0x110b682c100c0506101c0c1d4155507050501405180385e07a103520744d0111300f03080d20410032850030390049100d26500b0440260281011303450b8032600c8000f82402c007080a01c6e00550f00c201510b110f1100000342e40e03541045164010311181c1e60060382c9040404600d40000300c143c000500507400d00c59a14002544402242e0310720081c3d90030005001c00c0c2103403900180480303610003c00e0b200056001030b41c444e0089580401c1d284203804803001030700351207900c1c0e89610103450316018a0b804d80300007031007481c080d0f000003045000e0304c0d280820490b02c841704007540f500b00d1f0003a4020104030309549400c03820282182000c0034411909a401c040844100410b2010b042000342c003006100d1011a00e809000d420001c3c403c070f01b001c2600c0c1c444200780c4045903203a8002704070b04001260385880b10000d100d580c0440f0301240d810fa49100b28542002250034003001000700301410880c440e80b420340800e5005020b1402102d09000140e0345610354103009040d40d6000d42800961032040060000c0c0f60340001c0c2080880300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 902050917 1250 902049667 902049679
    0x1505180d09051834120b0a0512010225060b032a060913141006140f0d05011401030e010209090f06010903050303040c170a03270f0f080c0904050c 64
    0x61100600c4650729080030001c0b00d444d8040000c50100b445442d240380c2400019075602c640d03d99040c4007078040d100c41031941174000015100c24003c50800f5541010124449000940f4002489581102300354114620041b4411040004000c0058034003400c0080d1a0841c010845048070001909102c81050020001030300c4020194600380c81d08400e0360000c41008081170491724450545c6c0001d40000109091642c0c1c41d0800182c20740b80d144454010348110760b84d540c0c4040454250301d9442d0380040d0290916080034086029640b016024640c06000500500100b08410710005401d803115540594400d9006004021031034440c60300d100d0307015010000303a40158a48500603914035005030405022408000200001d000c0d0046206003240c1301c400c00c80308062403400340580c99420100c002400a441e515010010809a0003101c1d0702e56440303420301e20100e03a1810345800c0802281c0c0480d10b42140c0c42d800f0080882d05026003048280282c030700340740500d00b41d9186a100d203011111603210350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 902052167 1250 902050917 902050921
    0x30806120c010509041e0f1b050315040f05160206371e0b0a05040b03031803070f0602100f1b0c0807080d0227031005041505180d090518 60
    0x80c1c4d0b550040d52000040b111b8101c01e0740b0403c0c0e07484000c1d150002803c8a41c9042c2444000d4078040c10304058880040d980d5007504642320a07400320651120b03201b110ba4001c0d1551003030344001c1441d110300e074001c0c2d014145540d002424100081d00b080d000404881c41c00541281708481c070a102d032100907450340d203c91030018980d0042140002442c2200040b540c8088035201000201c1c010340c09141003031000c81d144c0003210796810030032040e2101c1c86d940c203401d9001030160340284001801c482d26140801015262250f072215911040750403d6484840141d02c9111b20200050b12072240c02d0030440d009070140084040d0200c0001a481e000e041d0000b009442c50461092180581c2a5482580e2000e40d6542c3c0310621004003010703410200411003482443c040184c880b6100014461800501402401740c51b0788101081004000041c001d0310082c0c17040c10420300d448100d10440d84a101c5181c0e0554182a91031503c80c40c008445680500348240020306020b580c0d52088034a00c002c01034200700c0295 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 902053417 1250 902052167 902052169
    0x5010e0d02060f0f03150a18020d06030b07051216090b0d061a1b0a0b13260403120206010305060a0c02031608190302031306021b06010e04030806120c010509 69
    0x38030a083e040303002c100c00030440c1c00f500c801d60b03030065020343c0d41445484155003030071040001d40e542c2c1d84510f4400c032402c1b1010034100d203015000340004060f1441d000505568070b440b070711b0a1400444d408000a4030000d04030000184880540c1d40009403081740e0143c83e04020302c0548245414000d4030b103040000f080d68409030030310b604424040c0c496103002d00c405074105028000550880c00100200045007014440260b43c00141030383d50f00e03048449401e02c1d80319030000b0010b8000e0f80c076080e02c500010001054803102844042601c007070300000c800c0d45d0744d40382d07043c24810400011842c41c00c541141e00108040707a00010040d42014808600064450111006074a9482000c01c94402101560200800d0005240142204c4c11002440440000200804500303d10084030928681d40081c40c0e00d5011500590181444240f9100322054400102c20010f1400101342c0c48960181000700400c070400d5400603109411103010356911040066141d030954440513455212410010082200409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 902054667 1250 902053417 902053429
    0x30318060d0608160b0a0e04020f0f07140f031e0a110d0c060b010203130312050412080403051524030705040e01050907120b0a20030c030412030605010e0d02 69
    0x20740010500b08600341e41d03800711035204c11002c81038040303a000700700002802c880b40c0b0b01103a10b1440c41c3ea44404850408004000c020341040f00c00041012041c44040b1b81c90903243d000740310b46409403140010701c0ca401061146443c0c0155120005500240084212062411107282c105600d0301c52407a164000804211a04015100c2c501d11501c2031b5040e40f840d080d0048004052503010717182c24008010300f1001644d0707a01c00d5019880003000888401c0000c20100440302c20034000d9490510b03c0c4c10368802e000905444030381001d0f140420006010001c000301006040d28641900d1075002c06441e1401c03c60b8402044441c501001c95441d4942c028940e8050003e1005454003c00070008042c034140418001c0208440341d00c41c038881d004002c2011110f03485c101c0c4602d980b14200504c1e940e103031031240000e0014603c120f030440201c400e110700c1d00409840076500c0341e0101264942c41c0d1400d82800c44440035261024010700d8a450000e00043e684020030050a0000340c800c039910284620210310 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 902055917 1250 902054667 902054677
    0x915020a0213110d0501091401060207151d06030c04090e0a03170a0608010f0b01030b181f05060417010506011107140d0c090903090806190e0c090408040603060b030603031806 77
    0x1388161401c1e0011585030162342c094841e41e000d40640c1c18203a030b203d403c02d0342d6521150182925079000042c1c1c2c146681e108a404c0ea110100070842c0d0140f2100c0040030903402d40051307c091510b0344001c1400e00100900e44140c20307090381180c0003000030b84240e44010b05451500c0c0d0508050350700f1030002038440091500401d004002400003000303040508003400004242a003031082c0080d050511001031413510011144d24000c00440031300303454580c505141004414598051940456658001003a544800103440203003008101f42d09041400d254460031600014a194140107040401003c0c0c0203000586600b650300d16043c110400c00c42e140050700452140c00c2c000c0005003807800100314401a0f0b00301941040c4a03403a644034154036608031035102c030703000c072041d07602c0c8d01c05a10381e43e0030021290403040c81c00c4103400a5840a51501c40800c82c10f400443d01a2001440010100051b03035161141c070f001010040f00f918203508090300081d84a200e048025140028151984241c594071003041391 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 902057167 1250 902055917 902055937
    0x120c060f0a110d051b0604150203220516150c06051009020d0c110a030507020108180d0810140a030204050408160f03030f05220309090c0915020a021311 67
    0x7030300c0c0f4440b5400080075035108500415030004410802008400300040d4180225481140241072400300c400110003500000d044044c061500c04049040880c000b01070346010b4010000f805a40480038208003115003903504c901441610941403071041d80e480040c181c0016400100802da5440c0e18bc1080c00c10b80c6c0ca500140700c554030004044071203542aa02c0014018140e4072080d01442d0304944258440d140071a000e8042030003000702c0c02c01503104802c80741d44682a950246c85821003020001d142c0503220410401041c812800d00800350f102418003001410300c000c1c141054001070700030030100b0369203104c003c2c0140c0e144c10100303007004408821f0364052503601a940800843c6810500702c108100322040c3d020030300c0c04050100c18100c601a00b445881d03003500c46451f4070113410a030090240410b070b0070b404002c3c1e0300c0e10209541c42d040c01055841c00450307407003000c040c0c00c0252000c4060109507655040d584203400407001a118443c06440080b8000c400043c41c01b900750305c0c2c507002d2140907004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 902058417 1250 902057167 902057173
    0x50405150408060f040f060b150a0c1a060d0b06060904090b07180e0103030e03010e010c180e0f060108040f06061203110606061b07030b010e010302120c060f0a11 71
    0x2500d0000340600944200d48071041280d03100c0d2075130b00c209003802e0400d5602801c001c603400c04c0e900104040741c2000900407405060300c2c465410700780b401c80300c0741c0007406900001010b0203514014001c4801d00f41520314020482c5248a06080e00002c2118081c1100200703018008000200e10707580b0030081e01c0311180040d006200444240ca45110711076400c96002001ca058401042030007a2120250800d8858250503c11142d0035610161180140c425840b03900d0f6480d20280c0309101c00c03e004c1c0078482001502c641781030340f00150664902017050740200300441d81c4a0700f001680c1180041054101a084c20224420786840c1404190401044400f6100c1410000c00103592a0f00c089810480350080e5225030501d200c944071542c80e08400d440c183e074844418000344000d01510301400c1c400602304801c88444035903a690f60300d83d01509a010b0400f112814004100394240b00c1598038880f030201010b41075507050600050028000d03002441d200341c0011903050a11406520341d108081070703101c00c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 902059667 1250 902058417 902058439
    0x71e02070e010b120f0c0912031b1c0e0307031103160e070f050901020c040f060302031902030c03030310030b06210705030120040902091f0c051c0e0907050405 70
    0x811403180e400003114002d0806014005000d103940f41720581d000c3d0b1100b284072413038605540200041700d0941c8800f4481c90008001032502000110b51049070040c1082c003030302070090010701f440800381c2d400110790b080c03114225050803540d40c0890030000752a03001c54011154100c12010915126407042548540c038402940481d4900340703206c0e640e02c51001da0703844094020328102d040310540250401c450140c0e00101c02c0103101d00e095044203110203440500020700941c0c98000a203484106d02042080da800f881c0c00e00b055040500229200007c103900451450070100044803266031140320140682c1d44142c049400b99440e980b075455015100550710b095800c80104443d00c940091041d14483c1d0f2802000380c0c10054206141c0b0070413050200d05508241c50600030720003075400f2a003110382c003540005c00c04e18003240d10500340c11140310a548202c0d03140f009142c45407038080c240440784240c51252003444c41c920782c0180c444c1e400b940143d07410300c1d10b61030326102030303605006903005268050941c000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 902060917 1250 902059667 902059679
    0x905010b090c0711010c080304110301021909030c09050405101a06070501140601031b200f24281b210c080412090b2808071e02070e01 59
    0x1900000b070150b040c1c00e5002090f40c00540b484203617600024000c1f0790500000300881e031b252002080301d800150000d031600c00201002c00410b02d0044da02004186004030510501c54400301031030242141c141c040055080039140c6d0760380c81507004011103003903840f1586281b292051007000d0005250240115440341d03824030740640a4440b900030701981c4212030001801302d6100340205036001e404241131200b4030450020442d000e02c261084d440d640d14040042001d2404c08001ca07003130211100c4007030f014a144040810000e107807612080e100340422402403040506000001101e450009500b080e40b42c2114404c02018245d0040c06421450a00508180864008805801183c0401441c0c102d0442094a400840e2101081d010000e204138000400081d0598484076240c0080e00384000481e50301c020981f020351091000030400c41e5036080d4000d40c07185e01c20781e04080542a003011105494002d030300030040200c5243d000144996001d4546100d4000e118103c05003503440c8154a0130742e1154 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 902062167 1250 902060917 902060941
    0x604031101020606090709090c050f030a0204061d03030f0702120a0b1e102105060a09031103030f0c18030304090c0f0f090b0f0c0d1e05040f03060905010b09 69
    0x1103518094064803001803d14588030514510959050f141e800d00c540c00d05140130020281d950080c004d018040041050a40900000c1c5200b8258084096030369410040000c2949800c0c40050426004015040f8219907000c4142c030b00a180010b50301d9104c8005e400000d82034122564404001d001c1d400b1250180052158854070608415108850b160105503000c2036280c0708440d040043c0c8100e040034005145070341400983c2e2002c03500b224029000c140c6901c0d041c803d06403055003400380d50340e5100c2c0400d40c010418010141d8550086c41c00c44c40d2411801c50103000040c8a940801c00001d4909204560048580340d00c0201800300c0707403a26101d00d5030314010000507042c100450124021100310324030483c01e0b41c0e0b205045580d207008544c5022001500358000a000c1998100140704000b441c1c0e00820007281248480e561b2210380d00c601a500c0c00c01c441c52902d9140c10800100701c140901004001e021040f2507120800089403d140d0910300c1c010000c03000540d51044110050203002c6900b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 902063417 1250 902062167 902062193
    0x20c0c030d090e06090a020f030f070f0f120e070801090b060f04060503070b07031e0f140a020705010c0812180705030c090a020a03060b0c0706090806010807030b0705040302060403 79
    0x258221541105195000d4030703101030612401d50b054150b140042d84c582880990280c111942820140c28605021418403194008546c14090103c184080003810780c1d000030340e0f02416040e801c003c45541480d0380020841c2011806200980d500c83c01d41001800d010490b9600030081c41c8000c008000540c6064000f2000580b5034610a448991407103066181510400302200c8004004000c403a10700394104d040d82c1c01011080d41408245103a44145086000c0d040d105001e43e0394a000114000903000750013000d08500c00410804e0038000902d6071a00003500b84107031102400d000c0ca003559549002e21591065502c060300d00b034011814041e450050314038003000c100e00ca900340c40c040c40d110300501d65100903808400e0b03171210500020410313006140c2d00034241c4207500d240200b2600c0d1100062030003544000801301d204c0d840a4030420815610851803400f0304802d002600389545000101d0b541c464075400040c10350816800890580c6004104a4006590241c442d548860341d030f080c094010105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 902064667 1250 902063417 902063419
    0xf030408010f02120708150d0309030209090d080106120e100b030f0c0310110d0c0806130b03031b070e040804090c032d0b04020c01150b040803041503020706020c0c 72
    0x30048503003180b01c054000c0d41d000141031402d611850303480c2c4204844441c40a000c05c03480d1003050035948801c1d114016074901c503034020740b5400c07542e5140d8414040524001082e540281e00507100f203208660780000c1b4603045909910f0142c2c0100c8942c2d0b89000200405240e44c5000e00c0f1b148003003410304400b40c0041614040c2142620101e0382005a01600c405038605000d0b459080801c456014509503072161060860402500e41420303100c02902c42100e0b034104041004c141720381c08000940c900030030840745060051030240040d0a000f004a50f40c4d028281607440d40c00c4240e80c0300a0074240810092008107404102c1c403440b424281081851944107000d4500c000d400d0459082d0068024010721440030034a00c0c4442108031110940c4100002500101c820302e919204204010380d198009011603611780c0000080030703648031010f10005903241d841b82c0580002480304000c04000071068030102e6103c500f074000c800400001c02c8009100d00d12009041e5413012a15605c40700000407030101c1018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 902065917 1250 902064667 902064671
    0x1f05090a030c0812040803030c131d10050f0a0506090d1208070f0807210b0a1707050111100b0d0210180f15050c01020421030f08190b120f03040801 65
    0x103200e15107100c4c1d5108034050700f03125500c2080800d901118440080c0110190800d80302031954445900310030304c201c91b03a8070207090078000701881043c07051a034a110084c80c2c100c5018030750b110550046540c040b95442024480e400206048610b900d650103e5113510354411400c1d54071604442d030142442206861800004849143d02c560050065007441c2c001c21162302c5060070345442c806200a1038800003a42c4034180d880e02c1d480101501d91240f000c001e40318203940c0c010002c80750405145000c07a0743c0d016078108201c180504494000c0031601004e21424240040707030582680004c01c0c10100d036a00020b4100e00e0a420004449500601c0707032240000c0340031046202030f41c030400c0c0540a840383c01100030040c180c0020342c004070300641c02883c08111000000d0700341942c0e1400d6290341c1400c8402410003003a1100a0800c1560155025000c10414149110039003000c07620580c420300e210750b0286032566550f14005a950f107494504030003480300c108540c621a490030800b40c076a0001d01c2004180e42c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 902067167 1250 902065917 902065933
    0x5060106080a050f01120b06210d0e0603070f0809071a070320060a0221010b091005030f0606070f060c03020409060b0c0d030506010c1205271f05090a030c08 69
    0xe001504c40f43c100c4850700071000308a0030341d44650720003050203405598050b0400c081202038132311091030a0001484030006d0b08040d44880005030218604c502024840c220404c04c000d00b1603086403a1840452440c504805e007651020303101494560950020b81c155458581d030110707400740c00d00040080c14807a68450407010824000c8290307408441030000025000f900026845541d1a03001d0310410002d00c200f21003003081405000304071300003070b0490700303400b800001c0d0b45019060062a9403580c010519105280d40340100c80454080000b62846104090005010080c400c5800701e800e01030345c0217001040050800706014009620900c10102358604209000464240c0d0800391a8002041400750403068846042100204001401c43e814050f4101c04840801c1090a0840702690107841f078070754601c2400c90450340c0000f80d2003030f80c0300c100242d40001003c2e154101025010245841810100350308114181c41c5401551103080d007240d0f8400002090040651a0100700d40145040d10401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 902068417 1250 902067167 902067181
    0x210b0112170d0209120d08010e1e0c0301030201030c05360429180402091e0403050a0810080d081005040906020d0f0e031b0304172b0f0c0f05060106080a05 68
    0x11b00c5c114600b00089a50100104241d841c006001d030f0303000c500401101c0f0303500e00e0308080b80382080040e82d092400410100050046507054483d0040048130703410a20f04245590f9540524102c1581554810706c2808583c2d24032104c0000e03a00e01c00090080050110f070000b686400340000c403101c200254034074181c003810210700740903141c4024030099480d1080d407035485e42c003400340782940504020380005009400a003484282e00c00140141e1280c0d403115030b2020108801440b00101a284044918000c0000c1142c3e1100040f003801400c0399040c0002a940c0b80200341a400d040e903401031740c10038148041002008440d90081c403803c01d21401c100aa48007140c83c40040310f0700c0c00680c510741d6008110341c14240100d0b00303600c4a0201a042100d20b4a0f4883c02e40b40201c00c1c185890001e15030000900d41d25401d1ba02d26014800e0715a03642405501e0380c03191005010004194542c1e00703201e4009228802c0c051000d5413800c149402108490b869650b40034018003036501210301111041c5044080740d11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 902069667 1250 902068417 902068423
    0x150201060b271c02091009060815010617040311070b19021c050f03040f21030513030f1119080915040807050103240f210b0112170d020912 61
    0x18903a0544031400031080d41e9082c8410603101038240742200e499106c00049000d0b2900584018000c8100036005101200d28000740180d8181c115006010400b4010146c043e244008503034403503014585582d0f424080213115041801d150840001002c1c0007440c0c8151401c4134868290140041d421100d03460b01008455003008801c8a010700000c02c2044000c80c480c4005010b1604503018500e40444c3e01c1041d0348522041d030340140500e0300032220a401e414825007611900380c1c060100302181c8081080c5650040120302c0710030340801800b203c803c2084103600304209000b058a90407450420030b200341d04091a80b600b01c10348a41c0320742c44901c040401d0100b1003040d201200c9400c8010700c9078a06210045d005031a401074550429480e0505040302d10000d05424001000280d46105825040c61384808618410303c00941000412600d54000260071002050444400841e04542d40e1080d15004031504d0384602c08211036500030901a11006040e4024450041c048a01d490100101505140c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 902070917 1250 902069667 902069689
    0x204050114031b03030a0c050f010c03090c29132601060b0c1009030309061d0f19060e1203190501150c06151a1e0c0601150201060b27 59
    0x40c06405c1440032005240c02880301107102445001a42c000d40712810341c15084414007a01d54000a4541e0356400c02e2041442a44002d005ca1f020700c04040d03685943d4003010030309040401c0b41001c4002401c86401138080b006140509814a9040c500b0340500c1700405200001d400c10707039640d5180207070000d4080307000b4044034040f524030000340884000313a81080c4001c002045003038052540b54080a030025400384940d03c40400400f01124103401c90b800d402d0700d801003100c43d049481d44400c03038020194003080d4081983c1c5620070000b2400307500c101c00d01810300c1100b02000581e01004014840c03c10841244450424124041081541c1c0c3c0c4000a00346000410382c510081050800c2031000f142c080e41005403301c14025848503c1541d804410785101c2141050280784c20700450300c02000c2c140e03068508022201c1080050800c4070f6400310741d41b511410300c5503441e80d0700c0031001c080c180d81c001e4020354020f200d01a2059252540e00701021503d010007044640c10244013503510780c076450001000c0b8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 902072167 1250 902070917 902070919
    0x102030906150a03060c021f09030831020a05220b010903030c0305031005100c02190308040510020f030d050105010215040c050f01030207060504080403210219020105070204050114031b 81
    0x40d1103e4510303103c86000f030010341101400c60003140c2c55074188910f064014032110b60500700003c2c17840018100100860409400094070101185105918002c0da03114090a183d24841d4100701032050300c001441520a0782c00326400c203000a941b07140c0300744000401c5c000f5550031fa000740101d010364801164410703c2c03404010301040308220100c01091151000d507900078001d0106002e559202e00005294070741100e40c400c00101c042c5015001c60924464618200c0d08540c0f082d80342908682d41d0140030b0203513000c0c1c0d40c0a142c10411214045100300301d00b0003e1140881602d544400c0900048040e01702409650301510a0042954075140191140c5100f945c002d26110100c074140420496032041e211000360406809110a50100300b243c0f2031a0b000d1480b50000560f21895481d1400a24617091054460600380f0f1224000301c0303030085991301f0f01c2159951518000c1c07a640c030040c1d486015120001c2d401500e4840045a5050034070741c0ca2018200440480302d820b4094104c068803141100f000c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 902073417 1250 902072167 902072179
    0x9090f0f16080a09030c0b09010c1b02150309070f0b0a2a060b01050f041706012405090406030813051c021e150a03201809180f010203090615 62
    0x14040030403561000422500c249800390399441c6c151111480c580040e1540d0031103941d1080780f602815001120009031004803c1001d9580000e5000114054000035a50b014071000000044d00e050051045001500c8139044841a00e030f03c902110505401c01c04101020601c050841429800039600000e110001d0303d0140090724081c0d5170b0301000c2d00c18845041e061107404c0c071128400c044054050005022501304201700151002c51091074517006030301c041c41c3d42d00658001d491010310420040c5402400b82480ca9403004104085001840203070300240c107095002c83c07540e095142c0c0c982c62200700c0310200c6401614100f120108c7c2e0489611010080d0700103440d56142c51242d03460701c07201102c2d802c0101031036a840c0d5130304080302c80e9030b100d100c408000903036461080c44100e504010403480b030102c40d084242850b80c80d10500c4420b00d12940158490b039107040020b10f10040044144013040d0300042030703030060b88081070810701070342065441c1c5101e802814005940b900c0e20100501d1854070081c14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 902074667 1250 902073417 902073421
    0x30105061602120109030203031f1a03070c0f081e0301210f02031e160b0a030510050303181e01050f0d060f0f2306180609090f0f1608 59
    0x41c1c03100d504840c200490700100c0c03540051480200a215086400c0e029401640d903074541001c0391280c1c01154101c0354080c0c0f40403882070040c80d10040c11046443d00c41800c00707649494505081d508590f01160082102d1000803020081000341c0001c4c00c40c640700031420803501008000441322900090081c0758144560b603044140d15641c140300d41d1081401142c0401501a41d0b0700840e0400ca41c1200081c0302d01c5888034040c20741c410070440c1c03d04001c00316042e0b011460500c48c0c8030144e4410340712002c0c101900d03140807400c0b91410381221002070100404407513582000e00e26002c01030026418161144280c1c01d5854510340c0d440722904801d6405070b6510346047e40d1006096440c2e081801810f07101581c507440403c0c50840440d8080152070380a44040c0b80900c0c19100c000200f030042448444003849404c0740d0200d40700c00d42a0b410109040b81010703a015221004141c07540036a29000354070404910a1000501030000841d0051204d003644d084555650079410005480034650180040c0f62000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 902075917 1250 902074667 902074687
    0x307050f0f130e010c14030c030105091f0608091018060507050d18150c020601060509060708040905150307060807031107060903030b190806010b070c32010503010506 73
    0x7804109808000b454281050303580b001d2002142c22118200c142a90f681ca01c4408031504500030050f0300c490720614610350714106000320410b000600c80c4601503140c00d004074507030700001100c005280c02c2c90514421010340e940401444500283c43e040c080c2d026080da146030302a400c1c058154900d10305d04242400000e90382da10401030000400160403c80305011b01d07003078030b0700500130020181100c40010182c000d0b207080400c107510300f800c0a0303464180ba1198003079000d500400c41d0350452303001d414019150303100341012036400c2c865540001c0c55070000040101d00c1310540d501103401010500402c003d840b120300241070f91802c59000c0d40c1c0100300020f000440c0341d44260000300411114440290510000e0342c0c80ca0240c0340300c00c00440100c1e8603803c04003050708001a40340c5420481c044410051031030a0103854841c681070080003da4100050240c05204071805a070004201044102d90744060203a200300c0c80224100d00d0340740f082001c1c142245150b10900c203881c10381708000d0481e0b1500804c41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 902077167 1250 902075917 902075929
    0x4060f060501171f1502030d0501060e0f01032d1d0109081608070b01080102072604061209120c0308010b090913170409140a02030c09060a1119110307050f 68
    0x1c1303440803c00c04005020401240c0d5009046407489240c0003191500c424103580e000b80e4505030410b80400807400c2a020055590311b504481c1c210080c02d002640000d41d90020b10a84400d01c200d0003900d600700100c9080340e060381d0041526490384000f0402040c0600c032118281c4e04003140281104006000c00918030b18240b0f440e000c1d0910422505203465240d82d81c802c0e10320026802002e19941c00319203030341840000d0852400e0104904090544d45003cac500c900e0050103035000703480411804200d11683d4401a5100a50041d00081007552500903901c005041c100c46100c110001280d40c03000080b200a68001d948019100a000175020b0b900c0c2c1e460342004210511007a1403070b04003a07860758900c2143ca001000a4860080b011a107442d4030210303100b00e400081c0211103094410400c1003100e8a0f9201510841032044482c2c0b0394618042c2011a542c051511000425000d0b28071340414480c0e80500010440d4861161210104440820152200454410540c1282101501250074a440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 902078417 1250 902077167 902077201
    0x6040c0512071203050405030c190b07140105040b010510090509150118091508160308090a270b03060405123f22062304060f06050117 59
    0x1e40c0880700c010f99140c5403080204090041540403950026051205080c01d1111141014003503d44010310950380c2c3e02d400403030a041c0f040e06481200030440c0c1080100c60080310141d001b11200030b11690405003404007045800380f00301e610812100302010f050b030340919150001c840300180101896038a044400d21500b444c0310700181006625070540c0010f20040b0800005002d16074000551900c09074409000c01405030003040c1950300c0001d5210150183c6092442901e03400003619449204910220704001d03001e0f00600040341c9101e0442d0000b41c1d949600c041000d031103a80601c1002580001d243d00c803041654041e1541d0403007000c04a030800d900000700b110240e0b84030381d003100d03c20440c0c0c0c901c480b03141c020b10301140340e0341c0f400b4154903000f900d65a640c100c500c1c5603072000b8410162840c1650b02155140c010320850321500080840c2d0703000140c4c40380041042c424400a46080d24002d002400d0034214034845600c3c2c0400494154452403200b0300809040440c0700580e00c40303100840c891f0b415 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 902079667 1250 902078417 902078449
    0x2060f16081909030917032802031b1011030f0402102003030a050c04060c030c02030703020a060c140f1510050d0f03020d0c0f03030b1311040f0806040c05 68
    0x260302c110619600244203a56140f4003981d40c2441160a0010700c00c40d0354644526030f801743d4000e02c000861109848001880807d10503000d4030203916200c4142d0441c051a070059075100f0060070640d9007080089212861050560020002081400140c003118001612000084441c040000e001400c106c61800d100100d9802e010300d00c01600300c0c1c05070602045281d08961904040305204002240740600c5070010b40c048600c2e41042c2c1040d0009081c4968400058100031000400b070055440500000340650780141000202c01c1c1c40f210081c1800400060449201a001581d10890710b401300d2102c00381d0b000c440c060905520003101c03081c40c401c8003400045501c100d0030303400901c580e50000400611441068034210300e03446410301a041079038480030101440980700004001540580003c0d822030fa00d81000144100c542001c584101504011040350901c2d044111034552012400751085484038100341a072541c950315181c0d00c1e01c105450052119001e51414003c500d000441c9510f13002c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 902080917 1250 902079667 902079691
    0x62220010e03031303030e030303070c151e09210509010c0206250b0a11040302090c1911010e01060e04121403070801091404030f1b020a030b01050102060f1608 70
    0x81c800000303400c640c05400e500f540504243c104004150300210074044a082c1100a1411450255005850032101007001008103900c42c002910b0300c1902e50112071500b0402601c00f0000088035140b8000b80103181040c1c0f401c10301c61141103c41c0c400c44040150b0700c806030303403417908003401d0030f00546106a10202c1243d0003201400040c00c07616101d0103c1001c9014000a0301a48407507003001d406075000604440320282c10240c03155002000bc0d4100c0303044070340c1030701c1181c46039403080c10030910b0b4040d82807845505550b007000c185140b50701c448403800fa800342100030021041c00b212a18200c442c1ca12a06403844a92400680401da82c80100107245603282810f141903038900030100c1190f807088501c04042081480180b044500912031610210410b00c00c0100900b007581b030180800300d1350540c400803c055004280c0318000d00105030081e40ea40544980c901c01e03201e1070680c3e200300e02400741d03c2c0144240c40009140b100b405c06050300a0040c00c1030083e202207159411070303030010f0041000111070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 902082167 1250 902080917 902080937
    0x122f090a0e0706180902030c0307110f0a0803270606090115020c0f031914150915070e032b050a050708030a02130e04020f040e1911040e06222001 64
    0x44446c0001c51061200092103136691400d040301500030310444585001710382c000480d48200720307400145141481c0d0400707405c42e12030350b8203002640080b410000030b90301700c008142c245032201000200d560040c202103039440c0d01682ca50100c500c190f0301100000006901c05041c42d081d50820350304103401040007400381c42c4a01c8407074203c2c445038105c11104550b0300c803444812002101b4140142c02841c24210342040090502114240c0da0b00407803044048100a54000310301c03010300411240c440d202c000b130180c50b14100800c07101c81841c10343c10300902d41810545681c260716449842100c1d81320f216600c415003820b8241e194aa02900001c00d00c141c81c540c01c00844680740c5a61864500511000275054010700e080c2c811700890844000c40305000321b081a0717000d001c8107000f007070b00102400e0314048076018500d2403c007071905540e003248071504030707240c00c812a040139000706e5a01d1150700800b50406449104a90450070050441d2014291403440d0140701b0040111190400c01424145001580d00b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 902083417 1250 902082167 902082179
    0x170f0f19110a1e1503050106050406260c0703030605030a02010c15141003031706010e0618120a021810092c0606031501050307122f090a0e070618 64
    0x1090b1420001c5083c1000a0100304031110080b0340c12507031005140c14030442d490990081c05174003e6020711028804004411803200b4080280422541c07250034810a40d405c20811082e810b80c40481c0540000341000070114a80c200054070350700d02581a9a03c061f0282d55440d50a02c0e882c00c0307011a01140e40b0b5001458002103002002805208001d25044101b403075454080d00401c0300800d50342072919001c0420425a80220501e55a0700080d110203030b071584080e049244200d41581c1039a404044d0b03010641c010800020310490091080e15200c4072071213002808000c0910803104d1059404100c802440510915005404004004400740d10079110341c0518588200d0003484160b0b03640d1007601000110b1404004e840110000f0056540081d41040082510b51460703009600c0980d409080e036600700030031801c04030703803401c2c400411100c580c90318041010b4500c0c1d00c0034403500c20000381e404503040d0003941c440c03160101d020300c00a0084500d03148064802c20311640d52000408104a400288 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 902084667 1250 902083417 902083439
    0x2e0614070b130f0c06171e1b07020a23060f09040207030e061c0507030b13050c120a0b01121b1103130b090301050c040e1f170f0f19110a 60
    0xb85c581d80e00d40740c41e694500c401c42441c2d68070085c0180060710110040e540c0c0c0c10358030a07066400001141c80d500160401c62090100d81c46042c0b0f00a41201c00d0341000500341d00f90452070305d9015030780090000d0b1110f2407801c001e124001d50002c444c4903881006600000d1504d5401072403258403a040444829948100041d43c54205a400c4c40284602189003400c55841c2e10941e94840c46504040112440b010041a00341c0d0039990300c20308499271000480c2c1e40100507000d40711720425021420020b03282401c0c0b100040d100800d05680881c00b0010213480b0a07006005000009110400304256461506e13009c8405040758205000640420410041881030503182503010700098915a65284084002d05003120f07401407040d0400c00040c04180010751140210b01d4024865611085104407480c880e11820301c0c80b5030001100491050802d003c00c0004101c80c2240284207054404681140c40c3c2e0302d807640840350150800021380e0101070300040c0910350002c500700c00500850100ca44036005011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 902085917 1250 902084667 902084669
    0x3020705150c0921030901032003090304030b011406160c030b07050705070b0a080103030809010b1e21060117150702011401080d08010902032e0614070b130f0c 70
    0x3a80c2e14000500c42c106007030507180250b03450704a801801814008440750b6490b409503103180b904140e02c40d005403040301e455000074110b0041c0703c5681552410b003441e44550302c0d4013601c0b045416048100002070b0b54417005042d84440203004e0318030351078001100342c8412210b115403803c54680040303103408000b10714161212842446141c0f1019600d1071142001c52410081d644080072268040040000c11035216100c90304490381420305084680300d4004250141014035182c2c1e130820500700c0e01d05c030701c22901c00e0800a841d8065a03d00c0205041c030109140d122072210310341d60541d12007001000f21041c1c0d08003142c22030210310181c50a0343e4000031f21b281600015583c450044c1e45451072a10454a6030a0240c0100100802452543c80003c00901180814400c400403142c0c04400120381609c64042c10307510300800c500c00e028044c00c0c122a510740403a54000c9500103620404800c0044010f00122038031150030010701c000742d51b5618000c1c0ca03042c072036000455103450410002c200180c0034810f600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 902087167 1250 902085917 902085931
    0x1e030c110a14010b031b010305060a03081909080105281d030304021f092606281802040209150f180103050412200714040e010e06070302070515 63
    0x2c4003082c0740d41c141c40c2514410f1021030701c05c1e00207080a007840060600d20205031942828085103a903038140c00540384c5080b90340f0260a82d800040e90326102141c40c5401c1d54103105036120300c608540c45150450807206d0403250200f40c01c0c0000b060b10110034017643c01280000e607440c00811403446200b203010540d600b4030b0440016910200c140b008524100034510201c214542411046070102c400007440010148540724594150325640e08250b0707940c100710703001d02041000f101c189050000c0301c02e19100034403200603030101402840c0c0b05401c03c60301402c017005840e00c000c00d010f011590200030082d804159078540c81902518110041040100039080e4001a0102ca03525822224100d20303184130000c0702070f0b04041ca00410000001c821030b400c001c0541151034101c4010025000810800c081c480c0168258450384000151007003110780a890308400030ba505002488000261a0a0746c074401021410341d000f00c0c0014210754803a90240c1001070084d811901e0000880740d404d0340e091001c0d242e00f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 902088417 1250 902087167 902087183
    0x40f090519142508010203040206040b21040f030e12100203060f04140109060609050904030f0e060301090c0212071109070302090d0c030b1f14030c100c02101e030c110a 74
    0x41034460303e42002400505004009501e0b600e003560002c0c1070b510660184c04152040824040e102c0d01014040c139043d0101c80360f1050381c07400e142c00d1030805c05000c441304900242441403810b10b0380c10248113046140820500070800714404441c50006500001e0001d900072110103071403c0540d6581c0a1844000c201c0140c003030070b9504016110041d00c005802500504c4404c0e07108200c40d4031b85041c49948a42c26203858041c001c1c4042c42128501c1d49200400d80c00640400040f03490046030b0b1180c00300292503021200406820b08521001b030141d41c2020748450445440004035040c80c010395544024a8900103180c44054000501a02440c0000b40e5640703040c00c00500400c01c807080d4858016160350f0700181c407504107a41a85581e0070314082c11500280c8541c1c40070a07a03c04004058a000004000c0340800001c003000801d41d0003603070400da1003032000700e48921005002c1c0959200b080c4103019810407800801900b9000760400e12955420807080240e84180b4880c280b0141c3d104074424040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 902089667 1250 902088417 902088463
    0xa0603060806130201020a0215090406080c03011805060103021005040320120f0c010e040902091927030e0d060e07051e010e0d0c0e010311040f09051914 67
    0x420707071601e103000b800b98944002024800015031303000038254079240d9040f14040d541d03c030304e14055400c5004075646e00307400c6170514502184210700456404030030035080c2d00070004658024202c45480d607100074058241c1e080f4600500141c11302444c50328400c2060b042c01482c060b526602c0850300400501027195004604100c1122813030508200c01c600e81255004000500c800707040c00c0e031503001c5050f080c1c1c1800600240c280799500c6d160040c651181e00200302009034640300800705030b0101c40c0b00c0c84c20011803610010404101c0246076a40d400c02083c0440d001c0e00c116940c3c146e800a1200449503403003154a848400019000c0c000c00503000e43c40e4000e03200385460002840042020381c039000c07240544642540c0c1990740e11000300c030819102126800411790040c18503182d001ca05030469880c03240c034040044140014000e5980c0f200c402a00d08015203404002c648080f00c140d104010401e40201800200d00a4200d085425040c0600070700b401074062961068500194008248640004141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 902090917 1250 902089667 902089679
    0x20403020312091f031d01140609130f0318060c050d02032b0f060f0f0b070201090909021315050102060c04150f210203010512010603052a0a060306 65
    0x100d003020042d6003001e400c1c442440b0005104400c0d0051941c40c9082602c0b000c88841c1c4a900014420480c031188131904900844042d4041c158101d5580810f2001402203240f504160300030511500344c410a05180d5240795503540040000c00300f0580420001d0030000403070344000c810103002131001e6200d003028042e0610300780d41802c8410306182c00355041030100e03042a04007000d21800382c1031007180c100d0204031002040303401001c0c2481c03064009490100701140204041d10b8040659400300941000e079070350380001c01c080b0b11403881d00038001908450100510341c0180c0145420620080c0a010389103480e04a81044540d0a2608440c0242b0034004201d0365805000d2650171104550150b45001d06001d48600001e030b11222078000c009410500ca00300c00d2003807185401002000043d201402012072188011350800e0040310703c250900700041c4841e0303105105400031680d000e40034000c418040038030004580d4600305104054000404003c0081d07888d4028240a0f290a0b10f0015103641000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 902092167 1250 902090917 902090923
    0xf07020112110306042004080106180e03092709060a0f090b070c03021509010501170a11011d09162601030f061e0e060c210601020109150204030203 65
    0x101e0281c42034a464090341c08080142c0482c0d0344580140c034085581c1204070012800a0960740b000811001c0106010820b01410740200e81201e0125001800070b029209000d01156492617092116600030001024182030000c5403060030b404900120744000714250007032411040c100c4000c910b6030020010821071201910644414000103001080812500e0340c41e03882c00030024001380240811440d8450400d03100b04104981080107100c0d0b01907a04069082502805081c0141d10400d2109803200d0b000d80b500040044005403c404051404440d600055800318401c0300709102a08d21010202c400e42c54107400c01e03001e6202013104801d9045401402000ba8101c1c002810710b16583d0558600c00702c1d1080d55860540b83c02c915068540081c03407405400a00340c00c0351440c8000706801a501b0701181943c0400300f10007860007070f60b40d01e40d03d405451405116984a119044110002c603003c15140340c00c006d544024180000501c102198586034402c6078001d00302510686c001609004605040c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 902093417 1250 902092167 902092187
    0x10260d02060a060609030803060f0f0a1202100302071e0c050d030c140102040e0406020906070c03030c03020d08130f061401170d080402180405010b0909010606030e39060f070201 78
    0x4d850300944075811036590510034400602181c3c800c400d91100740362540e0700c40031404480d8034001c11441e035203076403241c0c50700c2c5414842c14264841c645100d80021258060300840b449507500028810300a0000311a0f44001c1c41c0d041c4040c0c412101055003c202a00c6031946418001e0182d01c1d000601421480d140d010040e00d0180c602950340140010005c0000011031642c0203a0b211801585401007140400e2003800b400d500a401604641c4001003410341180001480c14069825202c9280d100e00040c1d80c8ca48042d103000340800584884d050103d96480107a2034854441d82d40400c0c10102c004141158031000c0e00302003a4035480740e12000c0c41a004000d140e0640170341e82883e900900d0281c001925005401102940610540d80024200402940881c0043c0802000504036040c001c0085000300070a000f244003283c40c1c810043ea50000c00904000240c50211040c1d82d5000340380e0310074883c0310f6100d050390040d010f9030310b5035103d41e618480a042d994080300b031502d40703442e443e0000402c04130720 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 902094667 1250 902093417 902093429
    0x1b0f1e02100f020c07031707060603031d01030b22020c0d020d0906020604030f110102070204090303150e16050a18120209281a0301090809040b03030310260d02060a06 73
    0x10400003140c00d040e010170f100040341d412001c0001c000c880c074800468988540b10008002c0380c60800003104040c1c000c40b20351306403040b0341c40c06468038030104010340842d880b11071101d502116151000c00146000c0a00190b509070381640941403031100c821032440c1c01b0150b105240540c0266480062160740200c078a4001d01191005040d14100754501810b180401c1c94800704000d40e00e400030000450940407683d81a502400400104036075044c02001400b0691403003c401104c4400007852482020002c0d0003114079600b1090700035101c20b0207a5060380509504410f205640b1000c440d1000c50300c11800040900482a00328009544100044000020100c0d8901034032200e2550589261101605920341c0003a000038501004001140365034034507000c2c07981d02d9030070290980100118400540510002502c0900c2201c031103502300741c0c6901003102c6003021110049030030400c28016280442a000c00384419041c0303400d80c000c1cbc0c40d04011070740200c8805a407005041c0300d20083e06100d004001c02d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 902095917 1250 902094667 902094671
    0x21e030610061d010c0210020604060b10090b07030c0f05061608193605011104030302100c140f1b060601020a240e100c02011b0f1e02100f 61
    0x204160015142a9503034021400500d0000c039403c040d41d00844c1c0d00110719070002c1070360700401d803410f8000795105411642160214104182a002814032119004944a840e244d880c40c050500054402d23580010005804010b104d03c10b0001140c9030705820041540250040c5c076684ca404011103030083c40d042c8029040003d40000c0000404414880710040518034402182c2260580c01c035500d5904840b506504503440380c2512905601d9404550081a110f80002c0c003207014040c0302c000c240e001d1444081c025811034503c01200740c21561041c00171001074184042c103000c1c040200381c1c054000c0401400d01d01c80004035255030f40c101c0e0600c03081001c2020020403092a124000170b4880107040c070010101c080101c4160b02e400700c915040c0c40d40c1d501c41d007010001107001e030000d141c3c4d41c41003203851210140f0b8004851030b00c9106014030b550007218091043c0342d000403250b003160800f2800400b0820080c0c2c409070215564031490300e0b4040f44c0c074140d00804900720040590030440382e5110300645814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 902097167 1250 902095917 902095919
    0x60b09010807091802011403130c12030908031602010c05160b1810050a030906110708250f110612090d0f110a141e160603051b03060607021e030610 65
    0x80e0388030740200355402c00c80d484a502d0ba100c0044250b0a8807403442700402001220f42c0110300c0c22103910801074018041c1c1d4440f041c0b00c2c1e8401c5200c0c0c4070b104076901c0d0310058003800300b034501650041c900c0e202e03071038401d00881d0010400d0020b03110121041e0740000103031200008181c410f4807550001c05a480c01c1c119001c1002000414000c1d080e4840c120824040c1500c1d04a00014030049a00c60b0030305c41000c40131107585004615010215901902903504609009100a511301e040c5d9192507000540c881a00c090300045a2600040c0d031400010180e409203081000c0d496050aa40b003850150482400421112400c810060882403130b4005040403c402100c2400d103028000682d4403c0ca5001548101281c0521300300d02d091400c41001d035409815001e15403004101d0010300c020307034a14000c0161200d01d4840104038259101901c000324500181900c4440400c281c10007035410040061900307182c06c030280e0200d00c5090310410744900150141c00381e5080d0303040900500c1e6011440c0200f141c85a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 902098417 1250 902097167 902097169
    0xe01050418140109020d0c09050c03190902040605030115080616050d02030907080a12020601090504031d0f1801090b040207020d0b040c1d0703111e0304060b09010807091802 76
    0x100010400290410301c1059501040b5a07080d407008011580240036280009018182001070a6081c461491801d00c1d20740020740e08003502d03081d02e00418100c95540c2c282c01300d02100e600a86581502603034403940e50070001441d59401d128200c011070141140a0b00c00340b81140c0d00b42000030061070808119840d10500b502c03160311908451000880c0000180c8a80300c60000c03510703002c001e0700114a24410300e030184080c0b00c800d0441e18641c00290f0300312030481e80c172a041d010030b45009480c0100880c6007164a490142000214200f038841c0180001250300d09450010f010078459150a000b2000084014840388800e8055900c8054083d64103500d4402c1a5020485560049a0140c00140d043c400320b003c0101e03403c1c403c801050403912500004061512880000009480d1070700803a241200c509030210301c81058034948080c4000002074030f0141c3c075000059600081c0116012507448002e0350706a514801d505010380140e03001440c20900700220343e01111094207640707000c114000842001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 902099667 1250 902098417 902098451
    0x18030c04180b0a0924051b0405121c0e13050609040b072d0f11120a03060803070311070e160c050c031515090103150b01020703080f03010e010504 64
    0x60540e2180001045940b03e00d040c500400d04014000d21441d043c200200d08000c121030414000f1100c40c0082001da224031b11218007142130303814112a10070060104214614021065610f284c01c402d0944461040001075600512548042d88001c40c0118103607a800e414200300c0b4119088040608001ca42010b000140380080010001009420500c000071511071140f2070510009500170321103440920b66006407207101c8890491f1200040c6951018412203204002409148800b440a03045001c14000300703000a501074880d40b020300d5140c2000064201c020030080c07141074082d03034401c20202d0b04c107203120b41803126641c800c030510307000c64040c000e400c1c1903888850b1216103642020035901c10381c2c6c070b4000d080c6603401c4226135140c02003d00c0760200038081c141e80d5100d01d80000e051080c0d8820a410044860340a000151103031181200341c13200f001c0070794012042e10405004903000c0316940d50764880c0d140e2007001005c4030703000044010081816032404c0079000d040e0441d4213101042c1c0348080c01c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 902100917 1250 902099667 902099711
    0x14090a0504020703050d0204030609020f040b13051012050706140403110d1a0a0605040b030a0b0f041b030c0501030501170606010e04020d020d021c20030405011118030c04 75
    0x4070880d4005155401c15008034101e41000700410015500c40d561f0382090002410703000000ea00441c448011a200e51410f0704c204411444001c1c11103280c483e00d500340034000c20300100070381a840d5900030007150010f1040d00021181c0e00c920020b109190030500c00410001c0c4d4141d004410400510040c400520800000e4540060503140c00c0380030f0031282041e0303031a00005403160840d07508074420303c6940c03070707442d08020240c44058a0034401c0c0c0a941040c15aa0400d0700f030081c01d1200c000000c0781f83d0308542c480080d00207004285909160031a16007034070000905900480d030050702014100310075601070064900418580e51000400c90541030020388034200209541d040100c2c1840c1500c0316601c66040c5c0f08040d042500031901d442c0440703884002940092443c016040010034020300e000c5480c003525000340c201c1c1080c0d00b0b01e410701b404080c046070005081201c040d500c818014214810600143c004c07108c2070500385400c124864241406c00305211481c0d030040741000c180c5040080e0b0038030512 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 902102167 1250 902100917 902100919
    0xf030d08010b1c0c0f08090c012f01020c06180a08030a1508070b0d0506090c040e07031e060e0f04080a0f03090818090c0705070504020906090907050a14090a05 70
    0x1c2c1d0762103d0401001003201143c0001c00c94074944400308590590091751909807458a880d103161076190320401c00e5a603500410045d00165503d41203004460001d02400c0c100e42e03a5104802c3c43c042c1c0202c582d070980e04151041100d81c0d100108010404d07a14205070102d4896034405002c905c015500c0d981d4982c80000c220003180b03505d900030301d81d884400d2002100140800400c0d00d01294031000310203255480300f58802c9516003007201181407880c0c00080f81d8018100c41164628151801090900b0510001c0c205400c9c540d484185091800d00030f0345103181554007510008542d4100343c1400f904090240c42d80c41828184403c100001d9455000c481c00c0d6115420820f00d4403a2030311045002c0c2c2001c500050240d070000c41d0514030200301d11480002024100d0b1080b0305552140e000f000707035009012002e0800d031302843c410803540c10a03500400510401502040c58803001401142c2000010360300c0714005807000614401495000f91020f240300e188105680c0361005920008158001703601400d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 902103417 1250 902102167 902102189
    0x12050d050306030f0a0303050108120301050a0e1902030c04150813110d020604030501020a0f0f050d0c170f0103120509091602010207050609060105190302031e0708011a0f030d0801 79
    0x8580c0550f01004201c022041410880715112014540240600001c2c41040700b00c5c40f54090101c104d00c03202d01a241a00c40203004503030007519111660349110303006041c0288002c3c2c24444d0506000503030005500c2400004d0498be5140d140100c515a40403440300020b0070800343d50184411030801c4640e52141d15040410000545910000121071144541001b5031003040068000100541034000c0e00030301c000f076102e81040c1c8003044801c1d200b42c2c118000b4440000e008100c110200106544007940e00c43c1c052410031a84402c498200307882030750560300c1e85080201c5900400410607000d20101c89082700d464107504044040022034500c16010700049103242d8a0b05500581030702c00d6040c0d80c1030b6504641103c0403800d10450561f140c50702030003600d0040304e5030307000d4445505240348034100716940500200380301251642d285c03605035203006e0140403034020070740002901d1000b4065081400302c201d10303c8040703c0d030300c508000030a01403490140c026040740e0084a8013a07004a400d504682d60a000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 902104667 1250 902103417 902103421
    0xb0118050d110a0506070c091a091b13030809190b070b040f020607030c0c0b03010b04170709050c0409050f0405030304080f070b0c040329010501051308031204050712050d0503 77
    0x14050160b941140717070004008210f20003488000280601140ca07504006c20160f400594500c0c14810842400e0740c010710303100046074001048144101c40642c44142d15400c1c0342041c000c4d02401681548181c03200342d0045602c01142c0740c005601e040302e01d89107003101815843e0800701c044900503220042c3c01c0201410014050104000d0340c250010b600805031076981ca80c91401500d0341d0250302e8166035050b540600403d8061030b45041760706885502e43d0300e07030800c0d03d40404080030b40c2040c803080019009800c00040c44405502a0314041d00c020b242d01d0340c445041000a908580004240c00c00500a0009010103c0c9000c011250000d81042d40c440d80ca0b010b25100000f0b620403080000c0060040e0010058001c01000150040e60303c1241c100d185d22440d010818850382c103e1007106950a01400100003960040005080c1b00700ba201d00e5140c26551900c0c620b0a40d0030600700030428100300010403040010903c1034001608504074480100080e68a4141d5182c42042c0c426041c0400000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 902105917 1250 902104667 902104669
    0x100c03020c060c03030106110c0303030a0b0303090306091b030c0d02011404030f11010f0e09070f02070f09021e0408030d0902060714010b031c050f18030703060b0118050d11 76
    0x40503500912014000ba40e407035401102ca25943c0c0d209201b407000281181504058548010a00240c04d0788020011030458880017541801844c0d441d0825a1601c001c0000312215141030019070f2003000201c000c1c000c031f59845805a00c101210300d4196100303030080041d941e203a40e02c00512000b42038080c41e0003c0c4520803800401c84a2045400180009400c81510810130001c81805542da04081e43c2c0c0346811007180c5401d8545074200301c8038651000c01c49000540b040c1c860600c581c0e0a812a104903070019a9030790101404c4d5400f600001c045c0c6800194840401c1040350340c2128510700220164038003890015000e4603030040607885180d41d6115600318080d075403610280e0710401d41007407a041c0c4640d289100e1600a14141d05103d00901030442d040072410203c0d81001482a61a221545000005a294503555101003c052144802201c0203022a1000c2200a018500c1000c3c0000c03000e050320005400f01680d4054081040e0307041c903043c080c03511002c21141c3c1003540212040c0070031034a60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 902107167 1250 902105917 902105923
    0x302100b0111070e071d0d02100302220519080d0c11100201140114060403140127050106080105010b0409020a0c06021812010606081807030f030c0b07030902100c0302 73
    0x14420302c1c003440791542c08200d20850701265030041d00d264030b03504000c9640f5a100181040301c1d101142d40840030b10303c840003500300325803000c510441a240040c68000206d8030741b1103c2d03008401414044042010500c898100060b0781051201c10721a0310100610b00424240c4d908841100c500810000072844010040c0d0761366145810300008184031942e00010310000e0080404204121a002885000040180380030b84170b0950400060f00c8186410b0642e16500c440b1801485401d280b5944c401002030101d82107aa8544280c46030303040749680035541c1c2046400d40c4c840b900a01c0f10359251200402c03100410341e0446040729941800580c64422081090b01c000d8050038002d072140e03000148610312000759152034542010211800201600103480050032544a80101c2000c04d10120100f10124038100800c0d6207007140304111540e00340c0b240c5e10701181103403e850440100310442e00c900c003001070500302d05a00c00740c51301d0204016070031500051100d00c0e100540e003040c08048002c0000381407080c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 902108417 1250 902107167 902107187
    0x18080405010c080c1c030b2b0c1d0603060c04360f020a021501150806030712030309061b0e151312050129041107060903020c090903070302100b01 64
    0x60003030b5040d503000100700e10517070454003a6100000b407601c4800c8401c1d02d0500340e4121402186150049131b1a05018521490b144419058400d40c2c959040011058100c030800d480c103403998000e910f918200182070600d8901c000c0c000c140c221506100610238151548095100504070b0342d62040c1c6491078944100712940110044140c0c2e6080092159070306a0b02d40003000040825800c4030074861f00c5000d0391548800a00030f1a0040b42c040300d5180903540f01d002c03c9500b00c071009098502e40c90703540c0d100b04038480b640030701100800e80f2158004c040c04114403c944410300c2c1200340051007100c5840c000c08031440300381c80a11844000110b000240c0c0590140c40501100086005400780c807a10b06101180250000304d420b0f60030156188807014540c1c080c00a0032103400903125031400b14000b00700c06048151080118800140080c00100f12203007c1e100c80796020350007504041c401c91091102c118402080d508a61744204105000250b0010301c003a41052041ca0006200031500c004032030074004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 902109667 1250 902108417 902108437
    0x50d1101030c1101140105030c100e0f120a0609060609020f0715021b030d050709050619230c0d02190f02030f0715171e060a0e1918080405010c08 64
    0x81c0c080d14000401710303184154181e41c401c40868100307004c81000c01000c0c41c3c88540c0c13080010030681d8021428244891500842c8100401c03034011003041c100e8041c54480c1c021030540706141c480405409004e40c4d84200e202410b0101800d514210380f551601040341304003440240000600004582c081c1c01c0e039416a48002d040111020b0b503003a05481c131503a2038008010300b1a000340782c00301251580b40141000f100f00c2c2d4000d46040d050a0380b0103072078070010854180b80c3d02481120304000d8250140d0598520407007500c12402510b4141c0300400518284000b42d1100c21346d030144803507040160301d098005006035840ba4184c5d54030181c40c03002c6400c1425003000d40c000d91041b0380001c00c442008845800b400ca003150394504e03480d00b103610741c203004000550304059a041800b40c1200c6460400c0311003940060040c205100040d40d5402010b403c001c121030100c2c2c3c2c0200020000c03c01c0c03842e406195400003280a85515405483d210100c05100b01c1c45094140541d28195604000c200c0066400c421a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 902110917 1250 902109667 902109671
    0x30a05181f1d03030c0a1b0815251b0602070c2408060105090904051606050d0606020c0a1707030605070e0906060a080412210f06050d1101030c1101 65
    0x400e500001e010080d007006401c11880b00b1084095840c01e0000650ba000341e50038006102000e5241c0726041c08411950a0240b910b4450030046140501003014020b14068440c11107030a00c3e1820905001e46243d1684800118072410421034440c0c0c480c0c442d508010541151841440700c902d050b42c024030400c00001c0104d540b40b423001072035a40d44400c102c3c6103a100340f61414401c2580e031049800c54400c50f00c9501250b4107100120450501c2031415500520440855420240c81c16152800400c40e1f402440002c400040c54410384200d8003980c00104000d00041200c02403900c0051140600d6004208842000e00794000d4006420405a0019901708404210134100181c0c024003419480548502424824000c2181d5051201c1181c07280c1c246540c41040b151500d0b43e0f00c5c91411000c10450003008071100d0042041524121818190420018000b8040c0070712025201561130703582c0564030540780c28546402003010141c900803446003d02e0b0010b4136115441c425150b540d250760140c0f44c60741c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 902112167 1250 902110917 902110969
    0x15160215070e090f010914040b0a02181903021e03030d09050c1003050f1806040201230c0703140105100308031003060920030102131403150c0307030e030a0518 70
    0x521951482416501b01440a0107040345041400c0d003408410b075070040c03c81200100095441c2455405440c6407941c4217159009920080000741d4a0380d424400d01910040301d1204200f1881e007020484802c0b03843d840d01d8a0451100d8000075105d000d48450460081e172141d020074200241400172440c000c0c00100301140100903498000d0050604440d1500d10000200c04111801d41600c21030b00c45001c2000103120b0750b601c0354011512042440110025080c829101d520300364005006042d1f41c1c10078100800210303242d800e0084800c00e003a401c58130380747d15020902172036005502500041da41c00c121070755900e031204440110f01d600c2542c001303006545003501c000b040090f400c0c00000341644800c00ba40c54003191108040c200d10076030042c52130f145010360040011502000f000b0403d4100102a03c54090711003242041d01c4900711a02080e1030f80000c100101281c16104000c000c1c981140118181344515801400f0b62040503542a03580d24184100d240b030342e81d4401c0b405d0031203101c9210090b081c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 902113417 1250 902112167 902112181
    0xb0315060d060606260412120b0a0b090102190203030910230702010809060c16050f0d200609030a031a0d03020c0103200307030504050f010e15160215070e09 69
    0x480c000200020220280a104c48030840c0c1c1701c03c420f03000300e0708410240c0c0030240c9038a0135200007036100c074900c2d1007540351140000ca40c0d507505128801012144112543e5101240009090090101c104100003c5034011903025840c008143c501ca81c00584111a1400000c4000d882e083c141c8110202081d4800d4600d00d0407009079005060803604c06c1c0c0b1803001d1070700c4900b4001d855490032244a40101e000f40700c500c0080d0f245003071a641103400742c1e040e181502a1300c0b42007030608141c906e140c008039881c0003511858964a5030055034154901000d45198202180725644034414051420201901c072590300c0c44d4145211030b0420042c41c01070a000c804840d078034002e1348031005120601d01281c41c140d400000450342c00c03030141c07415003c0b03100149036641d42003042d0004c1002500035201e0348214210206200d10034424941c417192014001d0007900c105094402074414010300555200e10f8880442a103280c00040c52162008200c859003050717500c079241140c124a08440c004e0340050241c1c14070880c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 902114667 1250 902113417 902113427
    0x5131e0c2d0f11060408130f031b05060a02030910031d0106081902030705062b0902210a060c020f0322080106030b151915080603010b0315060d060606 66
    0x59440c980782d4190041c241201501c0e50003446800c040d454010b00002070000b080080140102d1000c00c0e0030070441516115081d0610380c6a17042101d00c080c444e803107201c94081d4800c81900410040362490300d401c0d0050380003074a901480710b00e6806407002c808101c40f21030107138110b801184800003050000282c444c03d42ca002e40514461100b450003444c0400c81c847e028241b810704020303000340090107071600d86001d015107540b00c50351812a41000c14005030440d02903e6001003041410800407500c2c1e1030900400c20720440d409240e081c3c500b05e90600b03078000710000c07690302c0041c0c0d04404005100b800f401c40c00e904266202110803464000006d500d24900c0c400b084c0300d201c05c060030310b0a011584d21011203d00f220000e00020745242c400c1c0c80040e490700300111000702900c0c400f1f001c00c00d025400451603580b0038519088444180503140d60741c01c0650748a0200c503032014040f4024415041600c0c042501d41c510326058100401d0300c00b0004082e42c13941c0c65440405a8849070410040e96200b10081c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 902115917 1250 902114667 902114747
    0xb040f020a0c020109050a21110907020d03061d040803060f060d020c1b01020304031202120409050601030b010c150f021207090602060c0f0405040f1d060105131e0c 72
    0x4045440c500380414903042c02c0401c10191405040700d4007840c19171b5240201403840188e021264190100851043c54075400c40381e81c02025160003d103004508a100501039908681001d0060450807034036a14400c11100c64a42103500510102d940740c81c2d04010442000b032030440035400c038034006280c0031881543e50050119030920401d45889404481800401c506900c22240c016071051000340003203012201750528880303c1d401200c200c1040f9007000700e2250420340c04980781c0c5580b0310070003107556050f0140e1140c03500e09103811003960340302c0daa604010000c0c035048002140d81d41c205401181e038a070307411034103540da00480ca0040391070514802402125680030304001070142ea408141900e0700f290507101c50343c240c1340055081c2030070b06060000a194890341c2d51291030300c40404005400740510444500340e5980054000e03903040a00b840500020101104507aa241050186003001e00e2820111004070a070070210b41103010f201c040340d204004c82a119140e5038669552640104100504c02d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 902117167 1250 902115917 902115919
    0x1120f170309160806150109030507080d0f050304032003040e241e0f060f070c0e01080d020703060b190902070b0a02031e0403032301090605060306130b040f020a0c02 73
    0x800d01e0700204104031403510f561103442003a13400380380807585135405001002150381d41807501981240c0c3c0c0380c881502e05105648410f281d508034840101c0c4195120100e0200d506090508031b02d1810940c0e00184064103080701e021040742a4507003c038400d40240201d9004240401c45036406042c07411100301c04108804141c140c54007640f180280c00d081200300c41994155817510202102c513850184a001d90040c4600c5a02540030020103080c40d800e036026052003405200700d42c50550a080e07000c0b815100c1030b0052505540000d001490b960360010350321040d42c0d4480801304201103120302042010f100320300010000b4240c48004148050294007605010f401007070712003003584030382508a080707200c1a211103440c03029190030b01d0815400e0070085030b001442850000350840c0300708100c1300a8032403150499400410000100074910f0540a004050041107414511354101240003c1144c4501c0780f282104a1321a200d90740966510782c0b120140361403c9405554036852b50b40300401e00000c0103070032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 902118417 1250 902117167 902117173
    0x20a02100b012318040c08090f060610110102040b160308010501140703050a0c050102031303111506220504030c0204052401032a1e0f050301120f170309 67
    0x1c0c0040d0740c8156565528540341c04402402d64180c10403000c0e0907800303048804590a4042581c000c03944852017058180f8406940303042c1a03041800640c4c0c2031407c6c8076120f40c02c6600000c14000c80c0c1c3c0d54200707200d184801c0c500f881c1d14010141d14240e0b01a0281c0d0348203454100c00410191505e403000f03140401301a11a5550f10426030300c900055400281440031160710784024884240003d000b0f10041042007528240603004881b1070755120b0076a4021030307045400b0b00c2c2c0091031004151300003a04c0384e07081c05210b0241004030b1030601c00d150074a0700203203428811401d00c41c091071100f035008902604d5602100080c40340c0d2411f424041c0080007001c0d0109c2c000c40c43c1500103450140a150040381c11044840c62100418a40004401800c4060a0300d00d1044038094060b060042d103621030300388d4219a031510050f0b060103640d51a8400c280040c24028044880c0b6040d24459108040b02d05680c1800d120303c48035001d0b400c02112a4042e00b400621040f06070400e40031070360505014511850a600071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 902119667 1250 902118417 902118431
    0x203040302150c090d1b080f0714060d23010e07080901150b18040912020105130f0b0c0c0102030a06090c021f0b0312180301140402011209050709020a0210 68
    0x84880503a40440c3c40d4150608240055a4245400b0100a40a078022581200e40c0e10510000840e039004075482600103a001c5003542407080800d200c1c2a00810001400300c0442220b070000c51003038400c200d440c202060750740c13440043c550441c0003030145a280f001450005581c42d9400c12001032000d030b0361103001c45c1c05040040d80c500b40c1409100c00000070300d00c2d80300025242c0745481c000c0f0740107690044003402e08080800c3e52500c8520442c080503001d4a085e20315901c80f0403000c4d086660151081004000800204000c00c06854441001f96032100420250740d03101038192200d402181c0c482019540004140000d6115503080a415685e01d004100100ba00903207007681c0d2002140c3e10f1070f013210140b41c1c9007040d46800350300400049102400341c0d00c2030001441c44100c10740c040507094003c0840c030b505c04d818a003001d21410119048030340007100350f420036800207880f084a2000c640ea201d612080760108006051000344010030100742c040d900c0b00390b0134202941310b499100b00c4c4407856291480f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 902120917 1250 902119667 902119693
    0x703090f081e070f20031209090a0203010f301b050102011a01110a020406031a06030106141306170a1a0c0f0703020a0206120406050603070e06010f0306050907030203040302 76
    0x3c80b0800c80c0c0c00a040c1d1380704403580c0e903035100341c4c070380c0310101c800e0200646402c07105510300340000400c20500d04022903407410304a040255050014180c1c0501e18418030042c0681e5910300c02010949803101501d20304580241014041801007404c480600c07030480b00d20804001020f19182c81200985151454140c0c48000482c00c945102c000500707401644070202505500842910010103004030a699040c4003d4020606a900039441210b0302c041d20490311317508000615416401c010b08600038014940b03003551b60800d054041d10450711411040b909441800000d621000050001380040700004403d024a1502c581e4484002d071110141040c56040c44c002e4488014400c4001484060400050b50300d4180d0325000040d04600b58800d80c044400035950b1840900341174064070b2401c0609180501d40301d026103401500d5140603611541c802e02041103081422a40b201080c40c00020010881c1001c4003c5d0480d40c0c0b05640144164040c07280ba01d0703042e0015407103180245c085901b408940a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 902122167 1250 902120917 902120977
    0x4061812121a101b030e01090906080a060c050c0703080d0b090105090c1e0415120e0604020402030619170d02070602030d0507030605030102030a0e0d09030803010e0703090f08 77
    0xb05011003039100407a9500c1c840c9062012628044084e1a00d03081c00c0014842c1080300c400c07504010b9001c1441600d01e15034960703002035038101811120748140111850f1400083c0c1d203441018000705065101e13184041004d214205403802500808129410241d80f03043c601c95a500c40c4100c0c804840c200f10250354603040c044d0400e412140090403412071036440102d1090b0b583c100466501301c601d220f019134510030600d400540060030b0b040041d8100c144040b00094001101b01c1c80e0101c480f4100b040c28402100d002c24665401501034901595995803100054400d145d007003283d402440039400007007150049040d03044070404001045492501c0c001c2c0050b0303520700443c810840180d20800200c0e042e03003d55040386410000030308011a0740354461000a003680c1040ba0144c171855565454026030360700030803040b440482c0c2c0f410450360751811a21241c40c00e2105008080d0f02e042603501140c10648a603000810b078075044181243c081c0414502040326038000350001400b209001d0050f01c1e104490 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 902123417 1250 902122167 902122181
    0x10031407090f05210f150f09150405010608030a050423100e04150e04120f050403020d021c032309010f03050402210304060824090406181212 62
    0x11011107116280c00204403901c0c038400004400395001c3c3d00b0541030103104020203179080340f043d009007060130390810701c640541e0300007041608010607030300030321410b141e0114460740c00035440b846200316031350b4904207103015107481e07071014000c1d00c400205900001c4e03000001e04140d80c0070000016405400c0100f11440c82252a01540d1100040e1100c01b6124000c00f000da810749d03000303030001c9404547c0910b2001900d4090388226811803e0104203c10000080b40d14980d240305400e0036040f01c4080c40e0010002d020318000280518100f00d00c07041590303280c00344800d2440180e801003206903c14503004240103140c1008220320345130750060444056480c026a021001c040e035480407500c40c41001140501005801a03070810182c5080102140d41c154142c1010503c4000459485181c40801480c040d801400c00703402c85060620040020180c0c220b84200c24400c90f40b100c15501d540c10040300a141d01542142c00c03680d680c2110013080307075000141140c84002d8850751100241902c058090311b100c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 902124667 1250 902123417 902123429
    0x150a06140a08070b1c0501090b010f2a0303140109090c060507050604080d02070f030e030705031203010603050403110106240f0806060c03120f010e0c040303080c0f091003140709 78
    0xc02c2c060000d980c3d900003400170300407402072a5116036401c070154000c03101c0070703042045a50b0320b80340c416425503080340f02c1013a90011494100b5060044040a051031000c01418214080c4221200710601d440707900281e0790b0041d0715602c1d210301d5954904150090845440858506003542800141c0074043d006440c032030781d0004007038801551141c3d10f030034140c0e102d01c0344004101c1e42070001740081030030b003280315101078400d450311035024414200300b5203400d442da84901d00c243e02515640208612047c1034138115a05d034140450242c41d1882e0503142c10b20f0303038039508840750b18108000030038520b080700801360304495180212b401c100080003201e100850190f0000400c6e62a030110708581810401042c84505110030b890409040c2c620a200500058400d00c00305002c0400500950940001541d040091205030030f03c0c040c80c507079002d0503205d4010a0341469002c046400c5141400c03440803200000d00041c130101e400007a61501500038040c4080f20a801c041407400100c034039001d4800c1c00c055901c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 902125917 1250 902124667 902124673
    0x601020d020d0c230606040b0a030804030609110d03050904060b192a0602030402130509060705090406030b0108010e0714062209141504050c070303090302150a06140a08 74
    0xc0000d4040d10701da410101c084032500d013481984c9440b0603d88084040c10916400a01004d092030020401601c0d6441525803042c0400002080001c01d41000c072003c90340d0200c400304e10941d060501003900b0b03282030348080c1c001c1000c403902d0007015408070042c410848201d900700071054440d40303a4441030103150139564502d04d010400c13209040c06600000d42d45050503000783c01d26040904c00300d0892841d0307501211110b07008402d000442c508140b61074003192020100708140d140560300c00366900070280851062000c00944600152030b1900400055500146d001045596919169000b41891100d900460041c200b0200e03400d8061070140d95424001092142060a4104611500c0c11140c21105075034481450014803214a806286050045540428840c0c50402c0e91140040c01d010702c0795100740d25050420244402601c107440c011909850005014085490141c0c5000c13118020301c640b0000c010100f1103804260f4003c41700740c0d4a150321841d480807440e81400900c5805025901711a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 902127167 1250 902125917 902125933
    0x12030204150e030f07080d0219121b170d2a2d03140a05060901140d0f0b013809190b18010c0218090c13140601020d02 52
    0x1030312407011002280c20050640d0440200c0d190713202c0c07420304258042c0242d900b00c80340403285203405025000c1130100c1c662685007505203d80d91842100380c4100c0320014450038046070209098504407840c1500d5000310300103040d101380c60752508590000902042c8907805e003822429139900003111980d552040b00c071104103a1114000640e0220700503074861502007000c0510447c0404244086003400029171800101e03d1240c072241d403070010000b0a409a040e00301000d01565859200000781143c1811041c02000860319000480c42a5015000362074080000c42140030302440140242c100e4107c200d003114118500041600c002e80c810055500600002c40d1013408000c40100500e001c00c0700505050340362000c05000c1030054926005111400c034085600001d2450b0450441c42071103003420011394000c0590f001030b20300422a19207200c03071400e01020a5142e402040400c0e02880c00401c40444a11088292170081190302d00d21007040041d2030100781903500206000c00206003542c045c1c1849 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 902128417 1250 902127167 902127209
    0x5100f062c012a0b0c0301030b160e13020405190e0919020607030e061902010f1a0409030320031e07021e0a0209010e27030d051503160312030204 64
    0x5010f20600840072614000b00f0400036a01582e614070a504414111744c6950440c2042c0c0c0c003a42d0b005246200f0f11114002200e11a80c0000d8480704035003040303803000704043c5800742010290040d54003c42e04800000624031001d21440030300b2094960f40c0c159000280d0300e80f2902a0348400d81c43c10721000c2000600c200000d4145480206622406410f282c9410701040300451841e03030108640c03010144034400c5c5105450b50a004a041c030481c4c4500c22702a480c90040c08055103c1302d03103402440b481d0f0300d40204003018060341028007458214041840202c424549030b00b041e40c000c460050b06210824881ca40440d08030070424000c0132030790f000341210104251044c900c00070022000545224006012005a85000c0424081d0940c100415001d0522610000c507a0728507030003c04402441c22804114500d0020030354202c1010044040b0351512800740380d0201542060075241c2502810640811010110b02648110380c4030300089500a140424120300f00e00540c01901c2500f800c917004000e035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 902129667 1250 902128417 902128457
    0x11b050d0b15030c030702010c020c01090b220f0306110a08010b1303021e030105090a05100b0f0a0611060a110405041a1207061407120305100f062c01 66
    0x108202038403510328110b105a410074903800403101c48030403400000804c080f296082c061484203000c10300040c1019030580002170001445800b803060518400710302c0c6c1050902100b94036a000d031500421041c0151600e1781c070104800140000eaa0260922000700030042c20407045801890300c942c2d5035007299080c00d0305140c03564003600311030b088466110b10210143e9111181d0300341c0b0f520030340ca01801c0d44030000207050a40e5401445d83e416508103120f008042032001c16410001490701c0380001d0103151240028440240c401c0d40b954000c0c0d441c034004038000750050a09006c031040141151040d5071070455003c00ea03041c51405001c0750b03000340010480303410035806c1840131000d18603c0b00c0c94001c0950125030444640c2d400140d541d0704c0900200b1607141c0000c801c130601d1002c861807600e080504d850b07000701d41c0c01c3c003000402019512070010700804900100040a400e044201141e1f0303940c1c0303084c02420490701e10441074820584400b030b100a2544a034102034101d0042e103642900b00d0b0346005200c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 902130917 1250 902129667 902129681
    0x80702010c1502070606080d0804080d0608060f0106140712080604020f13030b010504020c0c0910050d0302030405010305011409271e0c0103090b13020a0902031602011b050d 76
    0x305100c0d5051a100005402c40c0c100c0407040100200141c80300c420b81488026551aa40404525081540140c601d503a2202c00164025084590039a5400d0208801c1008050300c0c0c1c041c0761180580c0c002d100200864081c46412907555550700d0094161171342d500e442134420708400421421200b80b02491a5006100007548440d004000500f407a030901c15403107080d80710160502c0644801a03041c020400b00829003030141c102504d046040c111030350b100c240d5074010b036052513204100c1d4100081c4261100c0c1d03000d038094040502450f600607214600a0358942103402802c1c040382c240300003c280410801c100c5112144010525907940d120145404600c03841010010000710844c607103251080303410403880804400c1d500e9456580754042038040d04014000e800e59041500700081d240100f42034450064215280d4180c0d2914406a03100090300c0c81881c1d444200d115001000300b01c0030405040581e103082d51a03800900c50401d13030801c0700442514411084002ca4410300078451140815070000c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 902132167 1250 902130917 902130919
    0x406060f0906180f120203061b070b182a090c030a0209151914071a07020109060609090b0609092d0304080d110105010302100f051e0301061416080702 66
    0x1091840d214013003441c450310035030440b41340c00c180c3e1000e240441c10100400e0354403800f0f1480d42c4461003181e508140c5c19208400019010742001004190b030103040403061807259111500300ea40607403001300c018000c0c100310422a241d09801108520b1641480d00c140341c400d8000c10b000710310399902c0c44040c0300207400501038a90000c070703041d0b0141c0c0e081d11017038010002c02d106100c0074041000726510040c0110380aa8992040369024064000012088420412103401a980401081d81d81035002c078018200c9200281229013001c030002250349071544968501d5001d042c1c0a80c140d070b220420700841c050b054500010561010a0480000100c00b8241c9140903d120798000c00e0002c0301d0b038083c60b43d0031a40000c02c4139002500145807040c0c01130094080c00b070b20304000b17000b65031442d00092110510356a511043c440028600006644984200c41c00480d0310041401540c44949424680c3d070403d02621021892030389540d00c4a011803170945049024507044c120314280c05030b40d80046030308464022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 902133417 1250 902132167 902132207
    0x3040816050703080d0c0e030304050d080d060e150f090708090309031b09100e150a090f1b02011802190f09090204180b040204090512040e060406060f0906 68
    0xd0400101c050100340011806866051345500340780c1000d0f821100c0101100b018040f030303039582a10382d0b02c010090b102117a504403035031101d0700e105080544891280c500b042407082d03d0000045100340e4180020b90050784c5a90b1020015069841849082c96480c0001d40d44518044009080c0c3e5204103c02070f8884008403d40b0705201c044c1c0042880c1094250a40700d500007030610f002440d04121031301607400003010f8001c10507545402c04541c03000c00090580a01034000c1c5220252030707141c204500e0028044841e041021140c460000002440b000241000c030780d2420350700b00120b0344140140d40d10107070700d00c0745070180c40743c26802c10200e04042401400096a600b01c002180d28807468407a0050807200b0005c90600d199104100864200e50420b6400c480c005107d0307004100380394002c2c0c1d440381e0b054800141e07181190800500c0c2905210320038424640009010550340141000c003801000180c1d0f0500c01c140e101c410a03540c490031a03000400040001400300314280c46031001120003e00c2c0c0790340e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 902134667 1250 902133417 902133457
    0x20d0e1008191d100b06091e0604171005060405190e0f03040e070908010501150305070309170703030b0d08070b180601030c1d06010f030b010201110a030b030706050a05030408 77
    0x380c1d10103140003103007425082e000310040740204c80c0180100c1c503843c0400c0340e12a00e0f041d0302000141f003406813000061000190a01c9000c0340707858a00844001d01070003001300c48186810b06403241d607010115160010345041001281342801c3c18040d040c01410068607400e440d0b60845000d03402002d90590541d15480382000030076845e2402d0009001400600c86100c00701e140c1010098104041903100c103d1076894280100108850064030416901caa8a07021130540c8410f003045010344100d1101030000141810610088913003800107120051080d00c040c807180c0380c50020000c6060510301d000d4142e0300104001000101c0400102e03034000e82c602e03040c409a281c0c2c0040b461904400360406c039440310380d19805200c0048030b50000702d144003048002059505d030450009215005100110044c16140e089003c1c4a170300030f41001c0c5200e8071155103a9100c4c09003074002006424214840c0e8001c0c06031b40008a0171a1048003100c0a91540d070f1030316495511385541701040c0b40c0c06040082c0324a002194 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 902135917 1250 902134667 902134691
    0x11e020c03071b0e0115020615010c0b010608100501020106031109040c03060204080a0213181205070501020d1d03161e060903110f07080c060a030b0907020d0e100819 73
    0x10f07810300d5090312118090b9141000c034102c4100c030301a04408401c18214071071802d00d560001c0c007194040802d07000000038041c200c00688410b0f86142c00108601845400407503101e900444a5100e44801c251565140e50b0301c20069007211024000505603003c0100d1600c030fa400e06c003e43c140c00622072036108044559075210f0004981080c1c02c03401c900d800c00000001175140c0a02e0b001c0c02042c29520401c80e150300383e50b418005c40a2010020300081600b4059403041c3e0040d01540e4806800400940d07032002d25040490062540402c440c852480d14048034600404c0081074620207901f40d003010014030708645131300000350008480450042d680440300800503807d030180c0e0f4110341c804d4480d80006024210702904103010404070040a0344030b5542004010400648421200c5041d0340e003964841d074918084001d00403200c07065401800e8041804105540012170b074144c92a00d5031515040f00c1801c0401289220f025803c1d800591440c020440d0710003040c1c1c004c8500041c030388001a2001c0c10714 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 902137167 1250 902135917 902135933
    0x150c09010c260720010e180a0b0d0b063a06110c1b06091c0206090a0821040b030a0f1506030902040608030307020319020a0b010902070311011e020c0307 67
    0xc004a03409411001d41484007403802d2420030400200b424224446c200c2a004110b40c9100c14204480c818a280c1c045100c5104035402002c10890142602000000500b450020302d036003078501c2070203100c1d00151a10a040c2042480316608030700c4258100b040c200c1101003000e1001304405481c110360f5100202507a0349600010b1003403410150242283d07001c803051501201038400e18050040b0403c1220385196514154103022405680e5425206100c0ba40003013034290060004840d0444130307400000c01c0074040001e8190040c805181c0442c5111180f0360021401c2c01103114410614105001107450010306800c00654000a0707600000c40a441c2c0e00300012480141d44584e020903a01e08103001541810f00841c80a419400000c5185007040a40256a071190781c17071100004009142d111607482c401c0c404520291b400c05001425542c46060407002580001e00480c045a0a640111521601806840c00456000381c0154101c3c1501d030b0400043c2d800840015841d000400011000035214 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 902138417 1250 902137167 902137177
    0xb010e10120c080d02070e0a0911030703030504150f0206040f02180c13090e03030106030908070c081b09060109061103041e06170c03220203060405150c09010c26 71
    0x50300354540d850f01d846000750510a140d80c80c0070071904400c0c030a025503410030744242d401c8490305030001030a052500307003409178010491403d03505000312440082490f9110340070348282e401003242d0b10000c088281d800d4601d000e00c5420038000d60091000140469401407103c1d1140e40040c0c48101070315901660f0001200c4105c07480442d1840210394078007040d040c992100050703c0724500070007440200c50040c0b50340380414030410b0101034881010000b04000030040c3c0e5000c03035000820405158482021a844107043c144403050340c0120216a030241c03a1400449004c2c480c1a11802491800e16500711801c0007080c4100d285031204100003d100601c0071041c000c807000c074642c0d011410742007000083c01d1070a86000c001c6070302c0402d024049514050740460307400c403285002d03d002c550309210001070703c1c0c0c20083c406507250203094100400d1010105251011286003d81180e03143d40d03503283c3c1c1c1e4541c061044060300140d100e000400003d00d0586402c8107451004540c4180c030794110f031030a4510780c84 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 902139667 1250 902138417 902138423
    0x2040504140c01111b040207080f12060f0f121c0c05060a06050112020d150306140f070f08040219080f010629030403030603060e03130506070b010e1012 67
    0x220304401c1c00c0c0c034001481000c00c02d03007003441d00d46100110542182d42e80e01303019500310703030358181040e154070035994a03412156507176880340c1c01d80d4950f150303055940141c0e00194145601125814002851443c1595484025078001009035000200030010300c081c4448013007a040091090884032241e0b0140c50b0703101c0350480074507601c490303505409203001802c0c2080036041039041d60524005105a82c4c215103001440c10040c94016191030400110314080d00c4080c0700108441d10055010050080903008040d44c00c0f2401507203401c94a90280c8a810140221004800100c907182c4106c4507503c50f80015410500013003044d81a401c00d0030313140f900c602a550144031268082d010722103d00e01c0a000b07a00c010a0901020380b9144803407140c54440460401d264100e4100c0040042d003050701030b9001c3e002442e0891000c0202504000305550349622802900010b9002030a00040500c3c22000301e640590340111500300316440c0c020701088600307019010824501c00c8e0440400c030380b40d280c0c001e110300c640 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 902140917 1250 902139667 902139683
    0x7080309010e0301021615021215030d0e0609060c0f060a0c08011401020d0c080c0604030e0a0506131502150c04031e020904080c030403060f0c020c09091506010c02040504 75
    0x38000c0000d44a0281c030320300180242d00600c6115180c030300c810303e500b140320b400140034000c210119060b03a0081c0b00e02d00c0980481450a81030050000c410210040d03c400b0590468118542c1d20030143c6500c54ac1c071084650200b005c0124400c01e0419802418100040200302c81d090031065040c1420001c1c1140d0304070f45a0341d6400c4404480740d0088901d4010301c403184482d111b9603003070f40c0000d443e08080f405a005009440e4401001c018200d4200d504a9007101e00383c030400c2c01d0508e4000e02c44400701030300600c9015802c2c00410f5502d0040202d400309100c0ca407411b60600c0c54500615041060400443e055000c1c0c50102c1001c0030724480140c0c0b051aa502c030840c0c0c0d0b10309501e441c04161009444442c2c0304100c5000d10401030b2034400c0e40640143d04100556102c1409107806481c0d032160b500000c042e10b003405200d80110b40980c10035910910150243c0e030100444a09000a03540103d400c0e0b015a409581e0210704004050a410341046c01131601d21403910345034021405131003040e141240d4800b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 902142167 1250 902140917 902140927
    0x5120a0c20040b0d0b010909021216030501110f0d1107020904080301030b0a05040f14011e0f05182a040e1e03030c0a08090a051606080702070b030f1305070803 70
    0x2c5814818481d54640031500c901004a143d2107282440005020b003900c00c558403c44041590f40c2d40350032039041da4031901202c401c2407612010078480161840100c9641d800c0070744e00c1d0552000f0a045c0c0d05c00300031340e1100a007881c40580d189000360204118400303c0341c40070010103025840341203c0d48d1144d405440d681e81e0781d51440c076002c50b2041c001010540103500e450203010010301000031044030709400c0900c0380302011424116030300510154250104020600c031a00902402c80c4c2c00002184070f0710642000f495451060413901c07001482c00b00070503901310200a00c0d141103451100c8151204e1a10440401c14604000c6012610002c0c0f044545a000c00c80c442d181e000107000070303410814410080c50071810840446c050500034900b24505000d0150300080c604501000a541c0300c0e0781050856001c1c44210400b03141d101d90760301603100050440c0700020311460002510104840b00360480710315540d20030106c480076100c050b000f285105ca581e80303050081a41005400060311028001d95520 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 902143417 1250 902142167 902142169
    0xf0106170a0f06230603040309060521070215060a080a0201050c070504020d020c0d1815051c06050a06021c0f021011031014090610050c010603032a05120a0c20 70
    0xa01c003814013144a60001c0041000099104040c80c048942506286883e40c1035001086207541c0d0100028035000f0700324041000c104c1c1d0000b07141c00d5041c1c1480e200c10464030b80205012a110050140540e00d0703004d40f94110040d486540102580b20301c9c0d00a90340003540b00c00010301603a000f09000c500c01d507004203070b1030040c440501c0400d000f00d0960420f001c4188851000e5440350103280709011204002482c1c01000600800450780c07000e1500d134840d1144914440600c0c000c01c1c440c098240604100ca10210741d003800040d00558090040f01050808040761004079454408001494114080c401c070f820b41b8036075a130094502e00844000b1054481c6090b9500108541e0640e0250a078181c40e40c0c031880c00ca88600207210b4200034140c0b058000345008202c00d40e120f00c030702001c9010661803d41e0000038940d000000740f401100680c14284441c1082c0d185100304101c7c004043d020b60030503898010784c1003261008144200c05070801407200156916541401b1107654000c7c56072008001d40c115039 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 902144667 1250 902143417 902143469
    0x91a060a1a031b0c1002090a03051002070c050909030d0b011b0321270c0f0b07030207050402070503090f0f040c090f050a2103170702150f0106170a0f06 67
    0xd861a0801d8090078404c0810403240c2c0c1e408901c4010701015800203140c595900c0f14280f043c09980c101c030441d540560702d054981d0095000440541c1c042d007982c1c2c4041183d02c0e041d400240103101d01402141820301e14060b10b4020110b000c545818490036040c1c081054a4003125004018002e81301c280c80c420f00c9004001e613078014020080c400303500e481624031329640e0321b03004c94803865010f00250811400500e09901d0112040e001300201c030300e10207400956065040020030145109500b92400d1a0b5940c00340026406190401072260b042800407a016050034405060040c000420b26510004000003090440702d0205403140007824061003031101c00030354181c400003800103031741c40c50009240c40d11030300e855000440c4880d551001d0761040d00500d40300700030003403845814020444060030b102c0c002175551001246100521150740d40001c3d4051441c0f28024100c070415141c009440c0801c81e80400d41240041c1010502580d0f500050809829449144007400e440c1e24003040301d00c010740c4e030460 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 902145917 1250 902144667 902144701
    0xc09050a06060f0c200d05030a031103010501081302180a0911060901051218011b12060510030b01110f01090212030703052b0e030d0f091a060a1a03 65
    0x10900408400d0f02d0380f00c07540304083d5030b14140c00c01000d58524510f441001d0b0812034070001e45a0001000d952881840700100007407144500e0347c0c50800084401c6494240b403408244142404501202c0c0051850380402c060751802c644002c041100004d1900b048411f201002c1c0c40041107030382d45001c0d450070007038144022080c140e01150b0040c101211500002c003607200f0042010240041080401d4104001607141c41c9400118402805090789903141c985680f064103084400107110f01d03409000513826485040150b0354041d001d00e00a5600350820340140c85da041300130703042000114001120400601c000b1030350313064060010441c15020b0040024281020964180d01d410410080d0000b0740c1010403911a0b04200c0203c02501c6651420400540e0310003101d00c4025003414040701c06030358040020403283d400c0c0c00c1c08100101d40c4a0780c00044449081c8000d00d448a6003010b0943d2400b4944203030350080000b030051210740d4480720342c8001d001c0d20341c000500020020003480001100a50148 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 902147167 1250 902145917 902145929
    0x307170c0a0b031f03080c100506271509010b03090f0d0e0d1a0403090e0703090c1a1b0d0219020117040804081203010f0506030f040308090a0c09050a06 67
    0x7559503030a01e00c801c0403620019003083c41c62003800386416200e041c5020350300005c5401c01d44042d05ea40200328090b40301d5a4014001c0301c01c81c50000000c0c120316003001e02404240752150511005503c000003404021800350041c0f4454084c030080500d15a59034039120302902c0e03010540740e200d052120b40f10386400394071201c400458120400c1c1204031540039071410000ca604940c0401110a83e007058204012040409200307444e91408100501d50054028000c407818052505600c2c8c4c1d40d9602201120422080141003266140040200000c040e40201030300481c25000e6140c03801c3c4022454401c07040000a0506070489100201800e4052202d10307540b030500480542e042c90907600081242c040c02c5001000a40c00038041014041c900060300e01901d43c0d002140d00c3c2002200e186200d64109100d64000300031141004125410134505481c0114018100003415072510350b0103452500004110140b58410604114080ba40c50448100101440b040000d0b107810304041f01410756500790008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 902148417 1250 902147167 902147179
    0x31308030304030c0b070309080c030a08010501050c10021b0a030c0b011a0d233402061b0f03040f1109071d0111010e1c02070f06030c0e0307170c 64
    0x2c004613070888500c000f0140d1103a01c528040c0c0d617010b400d40040014070f0700908048000300709194100c1e400402008041520348603000c03982e07619001110b1034860444480d90a8111300111510340f01d29401401d0b05102001c0f121040804002e0141c3ca0252200819000180291521018000700003e164050300c810844c00c010b28a0320300d01d503441c603c21781c1541c9003034070b5458070403840d021844824498284001d1006843d11304081903072130001041000d0303400070000728030182010440607810100c84460150080c04480c0d82e40006d12402d520540510950128100f002d48480c0356000300a52166204104040d44a8901c0c1480ca2041420045150080c400b0300c0c20301202c56000302c40e0b4011001001021101614214012a0180c414250b414502c3d030804201200b0003002140c6501c0720044151450084545410102c6e0781c0c1c07030203105900c10810102e0041c00f42038460707000407100c0002818240c5848001c01c0100b40b03000c01175400b480304c90300400301e0041140c40c02c0c004803104100458030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 902149667 1250 902148417 902148421
    0x60903120c0a090b0a030b0d060e3a1205250512060f06070501050a061a070b06060703052505070503010603030509060706091707120804050a14120c0313080303 70
    0x1c0505009001c1c05210b0118130301260f100d078214440e82020303140001c00303040e40700f100d52546000701c06011000f0042d000d034002c2c124901e060413401e641c54003203400101400304003c00200c2099646140055203c0104141400c050300c100e40b0501415018512110703800e070a40c2c031840c0d012a40d14050120704801c12030104405180d0003040c6140b503800000884541e4000104280020f0b518814014005d0282d400e00301041f042144607400107003100d80c1400045820404aa603034500d5110340700d03000b080b03800068003083c000d00341040a8600c4c20300c6030074481e10f05000f43d50703074040750030500390041c2500c6982d00c2301c1410041c0501020009000560091207254210794028090340151f180881c003541d000318030002408400c5e0400500c03a40c21029250311b645661014480c2c3d548014010788a0484100700c1c3d070030341407240b14101d1045030018054420340d0102c1d65100008507200d4810b108a02c620ba032034920180321078005160707020920004503034034110645014400441c03036100d681c0329041481 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 902150917 1250 902149667 902149687
    0x312090510080a020c0706020102180a12060207020d02130b0316081203130f03080f06150f09040902040e1e010b010221120c04050f030604080f0c0f060903120c 70
    0xc5462001094100060070f80e0320b809019009001d00340301c04890f403203a00000107070135030198010a6104440e00007261a540b0316001c0c002c248099118000303005107509a84170110b05141e0240008601c020314000348240c880d000282c220a1900381c02810343c0d5547c0010039a49030801c400f120600c43c201403080e00300e00d8210035a80310700100d40c84600f02880000007480c0c5d030b0707054940140803580c04027815403040f0003800c00a2007004d046541e40c4500d40c10f1404241c1a1401c4090411301c2d00f8040c015034038040f0030302030030322854100c2d110191b040754480002c1401695240504405c2003c840300529940032506140c1003144004110b150f140d9142c241d044a650340d0103d0002010116440c500030403202c41820070740641305a01200010640d004184518800c8080041045900440300c0d0070014030f4990405840306815036009080080410508810800840103041200030340801d95070140c074446001400d00c0e100711100140794000241c114140800d800f4080d4000f12a1000b550800034060 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 902152167 1250 902150917 902150929
    0x9060108070f0c031701320a06031d0d02060601030f060e07050901050d0c020c0414070c030e0d0f060b0306071e03020f041806090e120706020a030b030303090703120905 74
    0xc940104402485000285801115111170310701c0c06860600066945101848945400c0e010005500361003030210b1122540c0611003010544004142904c803501d018800d4001301607180c1c44411200d03d0311003070014a42e0620008880c018950054126071a0180004085840c101502c2c1d05440c5400c000340b0429200501655000d02e040c100903031b483c02480b0042e0380c0c41c02200d452005560514601a0b0038a41c046048044c007582520305100120400e109541084800c5030210f0001c3c801d8081c10001c03074400d2868180031000036100100404079030315071010b40f481d0b01c030702540e0080d03c4000d003409a04040003510f50021080c60171405020900240d403a0018411000508054011811281d01089801168000c20030100855503010300c0c46440009403240307220351140c0ca40342014800100c00045250700d01043c8482441c0d103403030880d80e00e10000b500000e11440c200b6640d8000118240c404000440c041c0d2603140081c4003291070340c44d12040c10000d0314214020000142001c2016403650 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 902153417 1250 902152167 902152187
    0x190e0c0603040212030c0a0b0a1415010306050d05070e0c0c12090a0906030b040210180909060608030301030804081207022209080a17010807080a03110a0215090906010807 75
    0x48551607500c1c0c9850002560003a075036088282180000518450740c0f120024600203141d10580d030208031036840d0a6048101d81c0301100000003485100e000a4159040c101c0d01000d1600504000500c0f90f1500e0200d0101c0010718401c0307070b890b4818030040c004284480302c01a031001450360181d00e4103070424003c5440302c080d403c1d6561111004154050603540f0107040b14090000d00c1e07400c10100c2d070780c2e081106d0303688000e40f4140d01401d4a122101900b40c400d0300481d0b6400b000b40030645004c1d10700b8290100034400304006603070180d83c5500118032120f040c801540258025840e050300e40e03003400f001da800c0401c031180000424104028400058450783d0135104403800c014002401ea108040c500000307000e500c540102803000000304998100c0e0010303d0362034040f002d950b08034001d0380c07a028641d50301d602a004031009640315841030400248540e4212903455407030800d4640d500c03050ba0114120360320801c480c0c0c906640118042c2c0f41410031040090b0f0040c0d0910744255036007001d81300a0500100c1e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 902154667 1250 902153417 902153419
    0x1014040e070b1e03040303060915030c050f030f06070225030c090203150d150f09150e1c0c030f03022d1606020c0c0a06140a1214190e0c 60
    0x1040b448030b02d0408410f0b0b80c581c4000491401e589140903d0018021718040c003481406915200c10b41401036030108200080e01d9014903000b85080c2003100b04101968034040b515171600c0707031820342007640b43c05010030703400f80c5160b400404603520618803481d00922030854060040d800135008102042185802100700c61031070000681d6038840440d42c00c0c1070920500150780000e10418120200200d0012008d100c1c614000208440b400039103880e400d46074600005003140f2801d1403803684442441d8440051040740b04116814501ca5404a642d10031031442c480340030401d41541e550a054201040000000341071808514200300c8080b82840d00703200c812910f0032405d6000b24000d44022200481d080070326180603258001d0014900240030354400c2c40c0700107590043d22252a942d060440051060b94061344851140d85060001c503422a0003007040300c82040032810b420181c94200748202076000c8a00c0070414083c1c5040c0c802d03100911100d04d88402c00a14240069401c40000301e100d000c0100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 902155917 1250 902154667 902154689
    0x806060f030606030606220501030605030a050a06020f070b2a03070f0c24020306040605060702060708130e18160b0d0504080f04081c080c12090a0b1014040e07 70
    0x5d520001c501c6d94050b018821102c10f41015030320f29407038030004c12031080312026a014000d19482e2401c1c940c44411030800109164410780110300000c0c440c0c0c025181c0c080c520311900d800c150407a1240e25007600c0c1581d0681580f41200300c54403096000740180502101c1c001001c51460078000402481906144919070030003007903034241000c00408250340703005844a046211142955620044000d40c403e80701c039407240b882d204000559080c614260b52509400400d0703281041d41a03207450005500400509121030018203020410380340d213180c7d040c0581260400c0030444415a04031910301080d00c0d9941d420224034000030851074650030100c8400715100344001c94541c071545803120850003020a141c0c0d02c50004500415802000107120103000641d20b00c9030030700f4083d810141d81205081c1d58403003410710200441c1e005a103540554a4004501400315850342015840d401c698038801d603844070320b2041c0313010308200d40c00301041514404007044801b003160704072400c45246d480c0040c5c0302e0f80038505 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 902157167 1250 902155917 902155921
    0xb01140a02100f1a0a0b1209010b1503040b06091009091509030203090a061b0222050702030c0106060216031e06060b09040c17010605030c07210806060f03060603 71
    0x203882840407900000e1290307010302c84820450002c001804c1d0000c903980c500c0ca5003181115092500121800c01c46441c0ca03080e9103007408074034440c0c0180e800188101242d6490350704242803512600c0e07242145111081c0c8980c0c4034145450310a840010281c4030b14428032502c014001501c080443c060210307141140d0004400c1c0152514401c400180c41e00648140d1234548003206140c0c01100504051000712a14440c140d2551010764403d0341700a250744000d00a82c10500040c10b003000c019a0140c8040c00d42c1100c2c10010200d0003e07288101c44880c0180c1010030128400d41c0c09009100203800310340054514000c0d160f00111722107940f03100141050840301d80c01d6903441c900d48043c840c1507400c0541803084c5070301e03401ca078001580000191350045240c402e481c01c01e0303842111400b65038034a00a5030081c07070b460030004640c59000503240b00c074824400c0160000107400042011082c6103203505400d00d200d00c0d4000039000210080406000344000c12444c02001040411242d0200044503841d49a03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 902158273 1106 902157167 902157187
    0x15010503012d020708040b0a09080105010f050108160e090c040303021b060a030507090518091513060e0c0405090c0f0f010903060207020d0b040b0108060a0b0114 71
    0x198440c4001e1104140c0250000c1481c103000d080082d01b80b94070b41e506240340340e001080d51404aa2034a004202c103a4081c05040c0c010720f22442114281c906d458000b901921b00240ba44243c1e2505900c05420140500c00b24481d80501608842c50f0f03141c5401001c1207540a0b02082e000b5216500a400c2102100c100640401c3c201030800741c144100c0c01000e5029180244c0f040040c0306c070803100407655459040364110369030740220500500b41000c0e040c6605240105001c290426072900c10426a003400019149100350f00240c0004c0c1200c40b01585410700880880c50340c6e1143c1041d003031010401c0006184d1400ca58104e86201e2000301d001c1c1040740d5003010180190104106030403c001042c0c4c2940904407080c00641640c041c0309003607403288080070040754101c40d00d0700340c0001480301c1030303040100e00e80c450b01c040303001c201074400c7c9030019001d40b04070711041c0d1905200240100f14 = true := by decide +kernel

theorem cover : BRFrame.Cov 901978417 902158273 := by
  have h0 := BRFrame.cov_init 901978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 901978417 ≤ n) (h2 : n < 902158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
