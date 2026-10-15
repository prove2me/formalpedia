-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3829
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:48:18.952931+00:00
-- url     : https://prove2.me/submissions/fad01ac0-35b5-4409-9216-4125e1898d57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 688489208 ≤ n < 688669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 688490458 1250 688489208 688489223
    0x40b0a0c03030509190b06030a0b0a0605010906050406020d200a1b050a08070306050c070b0708100b0a050315060c070f0906090e06180c042c01051b090f1c 68
    0x40f54080400140b030b68429070403036a60302c41543c0c072680d86c030101c9500070340050b070107118010a03a40021a491066407142a000074005001442c1200041552071305038411010b0120400c07040c03251a0380032a24400110081c00d04104144201e40b0365a08082542c455501901a0603219400c1007030740e038031a00e4010035001c0312401c201e8903842040403030362061061540e1036000760300400010f40302d50071155112205d498081c1c1000220748030107640d405e0896000000408001c00c010500d4003154126014040d5031070708a0402c05c070104050014440940820035401540c01450625a1078804456100e4401029035003203954803900b15032a4001d074000c06400d107080c40c0340030071540240d119075003814204000400c5181c80d2801c0b0400601c1200600c2c0340c49000d07000e0b04024580b2140180140d1081c2811040307610101d00b0715041124840401c1342c841d0764100403d00516085820283c2c02510111743c000c0c3e51a82c0300341c0041c1d6405c0c204221107810941402c591007204c2000b468000d28075005681 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 688491708 1250 688490458 688490461
    0x50604060e010510060c06090812010906090209060720040e010b0f3c040204060512090105101a070b0708040c0806040515130b012c0f041205040b0a0c030305 69
    0x8455080e078000f21340068100540541c204403061050181e102c41e14001d100000e0382e540c0580b80c0401903400425010403002480004000071401441110001c0c44204402c40c201b82200c800108907104001024100308a0030508414010384000b094220010040c402c10403042c8428026019000482c074081c0301ba003c101d65150b030340c03c00c2290310030301900f83c40c0031125544200c4446106001c00182d500a00380c0c0c006a001d080303031a6403004001800301c40d112180c80d110b0380120482004401045003910740d040c40c041c05085010b1341e40130f2050b24007031810300c02d000c1c2441c0103a02c000c0c054084040d041840c1502800000c64000b20114040c0c1d00480c0c165010a4407400380d20b036281015900100079500420700c840c44542c408400c540c0081482d0490b5080d50181c0c0c80b030902041e02a0440c094030098494144544848a140143c4581c44412444074918050305004580c540092014009200b03e40c100a1400e2242d1304a0b0050002031000640ba113824200041401300030b03000441c0444d02c0c200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 688492958 1250 688491708 688491731
    0x60105100c0503031f03120302132102040b1504140108100b0405011407151514060304060e07150807080c092d1017060405090a0f021c05060406 63
    0xd01ca4105540c10100441c5181c94074869100342008a09100b0601c07000114080000380085040d42c482e82c038a0369015031940b00b00700c8081c2e2101042e900001c004203800440140480341da805004150380c040721300041010002021908650160990035076542d0001000b1070702c0c029080c00c1d0b480c8100d0a036503400f500d95950700d103a0840360705405108404141804204590342c0306503c011050300034502c445080c85660703550001d4030503600c80201086511032480d80345800380c030031400780204918041c1c00382003442c0c48003040003440007400c050815600c40780c2e805811241000030200901400801d018010714a1342d004001c000161201000940c1940224a0440d401d506461a00703030000c0c20400000302103203a02031504242000c00b200c02c0180050084150f41e11102002d071a01c0307a032100f40d11251301f01a2207545690082c4414442c5240c0384c2401400ba00c000380c080341c003642c08282440690f05500004c4d0b440c28120715034805058000d0900740070854041100c5010b64481c00c4103001513070082 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 688494208 1250 688492958 688492967
    0x11040f1505031f0c0e09041103010b040b150f160b0712090201090b03062107140a06020607110a200112110a0f050f0a02030406020609190f2306010510 66
    0x158a05030b00410402200f95203000030b500100610500e41060000c10314110b000c507180410894094554418410030740708542401c0c002d100c4004012902003014003210b0780010318a100f000240585414041201c40440d0800011507800740c407040994a0340601c0303460001d88001c01100c018000404200500c10900d41c0c40c0a1603000690585811101c0343c201546184c01c0d030030003040243c0c40349644407201c40540040301d40686d0320550030040c1801c1810404070304003c440c0007509500500b04114100001030380898000d0300400a07182c51903010342d002e20b2540c42d042c41d51300040c2c4104546554801d51045168501401c98400e80705d0703c0e501d0f042c0e074a58504450003800040bc03d61801c00c021042e00e13209100455030741c8441e081c0f0380c0c281080c00100c0201a00080500409a03000180034009580c04215080d40000c000e0b004195035418520b07036010300406a480144004001003500c41000030895103a0035446040c01640110007084d9402c0783e8400c02842864021010f641c107154016119 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 688495458 1250 688494208 688494223
    0x607090b040f05130902040f06050f150f03090a0c06050301060305090607170601050c06010803070b100f0306020a09031b090e0c0f0d11060715060e1e0411040f150503 73
    0x36905030b001c1c1e00f80b0b08428050b50780e040d00c100030b48641d82e60580720010307035482c403480340f075445202d50000d81f0380c2c200340a001c443e411207201644a0708204440c04901c0c020141200c801c40250030b40303203840380c40e182e42580c6483c641070b0000305907040005002c600c140d371001c0034604a6030bc035036060005807100110245c40701c90a482c2c07000014410410009802961201203401142c180b50140c41c00b400078010700d040c07200a0300440d00b5500300003800002c6c0000185016080301e6031481e0036103c0752074000360b8800c4c080035120003400306402042c1d1900050103400300b00019500404407000464217032488450640850040058052800c81c4060312044009000718415070080c11090501a001c8204002d8017400d01d4100c0d41c032004a1213100250f1909005002003034411810540c1041d580b0200b44141c41e07503a041003004541080800102c5503200c9621b0701001590300601d245a00d450a06c00b805100c0d10714069080307403d041d40a005035009511003464044042f141c461426140c004040d1242170 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 688496708 1250 688495458 688495469
    0xf06020f1c050a0807180e0405102d1506110f01180204051b0c0303040b071b0f110618030613080301030b090a060f0b0117010509070f030e0304080607090b04 69
    0x418000c0480480c02035206a42240050406512860340e005084c0031100441d00100001d147c824248400c00100300000c18442c0c0c2c0d40310f420b1041d01d00b5a659001800015200030b50520b0010700c0c20311f656002a403100c2c6140020000840c2e50980340c03000a40303501c2d108540310b0304178482c501d60340c00007035010302c14200b10000345041c100c61003860741c080201500025144403114070340144008103100301d4000402c0d102880d039000d9505e03494207007000d8100e500d00a0110060180c01d00b801c0082e40201c1015003090b650001030724001c941607060002e00c04032140c00258000d00005030404280c54000300000c0c03e445c04a084403d01e5456441e91101c2816100000340079450078001031000409100c15181e001081c03000722042c00040762141070940d1103c1030080e010680c0c8034004503a650348180c0c1942c402d647d000016a60b94580f901084004000030022800c0141c0042c2442410740329400050b005503403482126141ca80361000c00c0c1c1c0f02c60b002e9803003001180000d50001a61070003130044d10115223 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 688497958 1250 688496708 688496717
    0x31a01111b0109080d0f0908010608030304060e010207020d050c040f1b0333230114091c050f010506091501030c121805060606120417040f06020f1c 65
    0x65080c10001c0308001c8401a050140034100400d00d00b034108101e06800b5807995a5070403200031402c01030003040468008190590518000f80b064150000840390400c0c0d0064000170720220b5400003e00901841000035400341d1600426800d1200000e0084400e00045408100016150070364004646103018040c1c0505070084044020341c0c020f610402070002c0c9140b035411a4841649600703240d0f403840d140503061000c040e00c20f11041c4452a66200d052041c0b03011000100c26040010340303807600b070011103d42c001002890010b59207a210003044a000c0d901082e9603000d81070310386039032158444554284250310f4400040e1182c540311252900410000e69881501400100110061b241c03e030008420300040954050b04800c492013600f02d40da030090702e41c2d0304406a500c0d1040c2420009081c591207103074140316814007444c01940058000fa030001c4880400007580c04103082a00440d80035083c00c81d25808e001905a40120f80f241c0c104560806460740006003005a50040200c001c030b84c0b0018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 688499208 1250 688497958 688497973
    0xf090503060c1303080d020d11030903070b060a120b06100903120503150a031401050708070e0f0d050a0c0312050310090b0a08030f0c070902030c071509020d03031a0111 74
    0xa050b00b0010716103c1420551403410503200e85444403258040300c41d03ca801903001510384c4407805907114074071040c19140140d0346541015031605940e40104070000e000402803901007041c03503895400c020010720180104442c420542d04003110000000c480355030140c5510501c486440384104690404e8a44c4041090741000c03d00354101c4450300010924010080080c0000946580e110810001140310f00c01401404250780542829164054031807814413440109100802d80c10985895128205581c595506001e2100281200e120480301802e98015000d4490038028404449020b0300c2c050b4004200e5007038409001c0b2103038801100c0841c6500861030040c8002c92690f081070303490b5103000b0700389400c40d6180c81c0300c5030455001e11801c01c0d601000040442122005011020007401c8500d021401c5290074081c1800c05e2184040040c501100464861120704c501da01603054580c0113000f03c400c040d82803030042c0040004405403042600c4010072460650f100d02400c0d1351071200740b4050b0524 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 688500458 1250 688499208 688499221
    0x308010b0703020120090102010c02060f010618031a0103140d05033403020c070506070218070c08030f18010e0a170c0f0c10050403050a080f07210f09050306 69
    0xa40000704202c0865486a20203030716940841d16018040b0301c80c100407541c0322440c500190031661036004110542d0020420030504a24920019045031003a0524404001419011010841c0150401404682c0f5054007020040e041403240d4103072441084510090843e00440300c0d41c1d00001c4006100141003000003c0100f040f640c203a04a1045242111149548160300d0340c900219035000040041d602142041030f9030b41c200300a80003061700341d403c649422015008200e049116401c86801d81d001100803602c41031151010014030703904080b12680300d0030500e11000081405039001003000381e00400010b001c0c1c6042c8110079039005644001d014034042603403922034004807014000d41c0e846045c0501f0010740000c1c01709190014040018000b1603071064204801c0e0b401d0800d00504200040c0300c10720014000081c40b2096076003040d21545c86030200ca12408403440781001c020b110b800b606181c800500406540402806507982380d81c085c000507450126681c2c031041c41502d515134008004241c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 688501708 1250 688500458 688500479
    0x609060a0906020408030d0f060f05090402060307050412030c0606060504230a05030a05070e0903030c0406141c0207060b1e04020d0b061b0f03070b0109052728030801 73
    0x40d001d202e29009030429070b0342e00115045400c0003d40c8802c40e51609000000701c2c401d403050501402c50a011900290300380030218084a400030310083c01060004041000d080c0600f0941e801040c000f821a40200021301e1300401c02e0b45017044c1182e095081802c081009401042500c00b90f0b11501100c48c081400c1441248907036035012125900002241c0000c182502c09212000c0c1440c041c0e0003d00145241c03020a102d40c080003043c5000c2604240203002c040c12140013124219a41c61501d11483d01d04001104100c2c440d0400002c4d124001c000c0e06039096481c0d0f00a49040d40c01380c1010048109950144103c3c00c1040e10100c01c019070300054010719191135406403200240c044c00000769158008023155203540040300121780c441202c142d40d0041d0a0400c601001c1e600300e40080e42c00c0600c0d903550001c24403810300a064510f40c4840004071036404240614544115200362011015004605aa200c100e0f014250b9010149070b03180d018080c0c2e0110000c0851581036588050581c84c0c40c04044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 688502958 1250 688501708 688501721
    0x50a1b0e0406050a0b0c15010803072604031a0a060f05041a09250c080306040e030d090305090102010b01110d030b220501150c030c120201020f03130309080609060a 72
    0x95000340e69242c0441d550b22904219800760443c0881d00c0da86041140006103424104650201105080c0005000340d44010080c1c4135200d03804280d16005100c0b0800b0b001822000080c07c828107500818000144030b406010640004040341d05404151940d40f003003c10342d00140aa02d2203d46582020406c50509a01c41001d1405208400e001483e8510000c0c4440c07070705075802c4121300110882c0307402980306440d0055007000b10341041c03004484d00b075803a04454000140300030300c00c2d940c55a80304c0099405000321100c06001a1041000c85594078020b442900404005401503103000d4115665501a1280b09111400309005194000020034120041c00804000700e800c140302c0702036180403d000e50501050301440d40303008170342503041034060400480f507015400200f090b00c0d0406004290020081030b4503580229084c40040b5900da0141d0180c882c50000382c900010000800c04002040c441000700c6610a42d5100481c9030b0ba18510f40e541d0005607040c49564000c400840c4841441c2d42c806c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 688504208 1250 688502958 688502987
    0x92103190e010621030c060f1b0201090c06141218120702041a180a0216030c0203060a0e07140307030b0f040c0801110a120b040908040306050a1b 64
    0xc00c0c440600c208140107070340d455245000c1c5030b074684000307104010103500240d000740b0b02e80c43d40f0241414680c44c020305855100070040c3c40265110203002c0400c0242d0003441184856224a580c40e480d07001d0001e0007400641000d40780418041d10201e44544106202c01403255540403081c103090303e104110952101c00703049081c00e81d0040c032215a041000748000744080100d42c8082d901c2d218035005000c10b8920740c1c801c1401807050034090410703079500c00c220810001d0103041e501d2141c0c1d4400c00241300a1084003107400000d6440d15080f000c0540c480d6080840b14400d034140d40f00d50704e032920584140d40d00034000c40e2981d084a01c0a1009040d01d5a40c1950358000034201c4e10529a6038450452640d4192045600111040100301c24080c40c940e86400901c0f05030000c220100490030b8501413030041959101c10420800801540340d5402c0e000121103400c01003081004001918015005500c288000c550039420070000640d8030403e40f20380c1825020034200c141e00000801001c50700345007142c400f07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 688505458 1250 688504208 688504231
    0xf0c021b04091208040309050906181302120102040501090b070b16050f0a120516020d0507210201090b07030203040b0705030402121b13020c03040e0c120a0212092103 73
    0x2600402c42c00d0343c0c403200384092a110b845075030070300d800d0050001a00e5000140071f441020306200d129101c4600300b420503c0b0f04418000d982d21240d0232200240c030b0b0020065404401e060741440d03420b4040d80100304481090b00c80e99049079a503200a1040d00804078090310303081010001408401c12410484540c140ba85002441c158444415803066045400d10b40c002444021707840c00107502d10312030190003042c08140c035114100c14120080d40c61440e92000b40400002042c180104a040307800e0130192030400303103030911a01408900a00904c040041914075200e42d42c08207964900910890b401182c001c0710404a3780c0c0c40282c1a0340c0c56001801c22a0055211a201084075405024800080003682001000b4007800010007048400c0135401d100000c0c410052420748500010454049401c005c0403013070309a9803900d000c1050f009a1414100031695201000031a510650041c03e0340d8403150100d40345a225610034913911344108288200e8130003145c0b644070344c400072075000d150700c044030b05003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 688506708 1250 688505458 688505471
    0x1e020901210902041119031a0d1b0e0c0301050f12030a0c02011206180b010c02090a02030714090603060103110d0903080103170f0d0e0c04021206040f0c021b04 70
    0x4078107550718188070a000c0c0309542c500071030301140740901034449a012450fa519041c403050741c0c0c5c0c103903e9286402d0041c00345551410554100340600360040c010010042a424001c030490909100c81c008004010b643e094070003802191480444132000d01680300001d42d02d0441e82000144802c3e0400c03c0c0890740c1c0185040c88030012800e00300003c0c1101a400c1e070f03560411150510000d41003a0000c150a590f01c0d090481c1440a10401d10100c42d01003081e9102281c0e0508040c01614403070280c0c100607411803c1e440402c10025807a80055000312120384c1c03454907072082d60380c1d4854180906007481c0d074080c4007007001c42c18561181c0c10190740f900c0651750075860101c0307004460013100c0b14640102c010810000041051001081c50070810500c0c081100e46010608030f00c80701188507000d40804016641d181080340a00108000362411401510442d901c0c60306500a1000c2c840c02c0301c280d881282400e8a004004134540240100c101140c7c0040003540c11100b8000c0c442c1106c800c9487d00704d541c542 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 688507958 1250 688506708 688506737
    0x809190305210901121d060408040e091605090414031902010b030708120705070801060b07020f120d03020702040207020d08030f09010c0509010818101b031e020901 72
    0x1119880158840c0004000301d110781c01406030044420201161440800d01140f111660401c0201d04601c0c2100e20014541c2c08802d0395094402c050710f0340145510410b0204401c100c0100010400c0c0e50030800c0c215030f02d270b0301e210100b55a042083d50f004c0e624404903008115608105c1c3c502a00b280c440e08242c184d08024103a4986950400d0a008c20854101c103068030300c541d0280300700d401c02042600501244c4d070510070303810b0f5241b0110600210800001900308140441808080041c1900b04000e011a0b81e9078000c2e60701d644c0144030280d11072883d96201001501d0300304003011511010b940178108034030440806178000d400102d020ba80190b02000034000503274600303031401c2c4480d1060200e01c0d2030381482d603400424a0401003000040360b00d0400c04a001c00c0e000426201c9021003440c00c19050b61328445260a64000c400d818801072050a182c6101d006035904402c2c64410b4107980385082411030394045041d01c03450501c0b140210584a9210160381d0b0035001440c034004107041c200380c04226071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 688509208 1250 688507958 688507999
    0x70816060e070f0b040f05060a121404030e01030c0e01080a1d10051b03010302040b01090302041d0d020d080a0c02010204080a060b0a060e010e01081018020c1204120809 74
    0x5900305402c440c5040c007494011685503400760540000040c105820318040c2401c1450b03901840c0c1c880c150204000d10120b1041c00d001046001c8001c0c1809110003401d0030310016841030b141103010504d500403120300782d4860311a24100341600d540320000c0c0c00000005458800020b010425101c3d00c4100b03071850016909800c00070040e60780010030402c58100f5078002140d134060030380c00101c01c0e43d02402d04074407410700c1500d0642e9011030f00016110703441c00041c1c41401c142da000035003041c100082480d0004009a40e007403440c10200588502101c1c1080032038486002a101101050004000c00c04607035095121108044040c000149015181c3c81d41903c3d2842401c130440d105911040502c1107030900c0d40d4000f0040103541400e504100710400040d2110312492440c6042109450005038001e0440c84103c00a00f00700e0410030101e104101c5401c0a54084081105a07101d018640304c0810f609208171402c40d4141040700d042d03510b140e80c540105078442080150300070b885da07015040c1290780c5e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 688510458 1250 688509208 688509221
    0x10c0209250503090c1f030b041407030209031015060c020a09141e071710030c060224011202091b04063506040c02010204030812010611030a020307081606 68
    0x31502e60725207920b005412107113060550f02500b03000d13041c1d0000490100030328102e00c41c2034207800e040c0802e1900340540420010440c0300b100100c9100f210b802e1044968040d401055007110540c1980c40c6070030251000402d031604281c681884003682c0508200c03140c4150388c40e426282c8010120b01103e07540e1001e1034291404144107803c510001c40074005d0400e042c4142010b40d201c05482d8000300c0c500980082c0c80c10010fa031000c04268a0900011110501c18841c0d5000c0c60f03202d01c0c108100c4c4c2d210b5000944e104c240c042c00500e0003610303042c1401203182d040c006034101d51180300903102c007551540c2802003c450281100900d04103072a480c41410300058081c0000d09003a0313484d04001c82c51214400390041c2400e42d03801c040d07000020300d00b244843d4281f40c0d0b58058000c3d0f034013041180743c803041280240306550000d01400b0011400c444032074812084541210f507980d40710100752401520f00c68403071154401000240c0d104006260025001c07001030300d480d0f40300700ea442041610175100e25059924 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 688511708 1250 688510458 688510531
    0x30309020414180601030314071a040b010f0506070215220816350304030606030b1501050a022503050d03050a0f1a120a08130e1302010c0209 62
    0x2c40030405084140c40c840a00000f43e240280495403554a000e03003110883e0308500d0103028000b900405000d030004502c40c405004085402707042c82c2904003010024800c0c008e062250044a03800500c501e0440c1c1682c0200d900213140c44401ca11014620007107a210064800c5148481001b204080031099510301c0240542d0000d0080d0003072900041006801541040c84082c00524541c0380b0301c001090500c00d095800303c040c2e1100042c42d100640f0350700607036100804850626202008000c6201d0820b80a4000541c040008640703000041d904c9010321461180140d1246208900000014000c9540252840d644a003015207948802e802c1c80446202a00425256400e11456000d1840781413051008414200018210059001c0030340d405a00998801c601e50721241035039030380511040180d180e04c1074046588803005501c15001d00417034819181507070400000a01401d100074018140c250b4143c4d202101e0b504150b080003411400a0300c1c20308508004a04016084007212030031040c0403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 688512958 1250 688511708 688511741
    0x305190303140f0a050c030412080712020f0403020a06030902090403030f061a07031805220e06130c0801150b0a02070915140303040b071509022d040509190303090204 73
    0xf070021340c9442604c00161403441080341c1042000f010429a0b000706904080e1403501b1740ea2601c6408084900c1101030568802142c80001e101a603e01090b000700100c0e8401e841050b48a960340704c0641c112201c03400040d400c141d4201c009000030307100b40e00004142c04841000910305481d80044c52a0110381c0302c034507c0500000030070500b419000104c0d079140c280e06860b00c1c01c1e000d00300408902d80a500c07103810f41e000b01d4001e141428001d030300d801a60040d0083ca0888070350340b80c03000c0191041a00000d055075443d0030000042545c0906000711590128000d00d80c114861610f2600c01080c0d1010365018214040d4040124100545000e00f04019030102030940c1c05909088026801100c460706c1e052003980204410049c510603d8250f81380c06801c00e0440000001088180002d40311922000354080711061200080b61903003400e0418a490340816003400c82c0d21903007400101c0340160307002d0300180d00544500c8030342801c00380d09418240c860720300890001420350100d01036548107800010640e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 688514208 1250 688512958 688512961
    0x9020d0207030e102a05120403030810153f060e0613022b0c0801090c0e0603060f0d0b090c03030703090e100b03070e0310060305190303140f 62
    0x1540c07103500302441880c03c84134155240392840001c1c094810707090181c01d049401d424901102c1000b01c4ca0100d01a4101040e1036040307128160b8120960b0007400100c01190700b4a02107100f0a0f045072840003620b50841007864070011080d0b040da04051250400707003502d403d4141003050030801c0ca041412800c00070000c0912031916085c07a2382950207540040c1a01e0704400100b10599582030081ca4240d0075040005940d0300401682207000310001e050380d048000400118500d1141c517900402c40344035103560b09121641c03580303000c006031080f042011000a104502c3c41c0351600e001001140c10100c02032924445c5580003000c1029401102020f5503525209400c00412030310502c9500d001e40000c401a510308102a0b0b0041c090b03000d10300840c034003400e0100c0000d09038000380d0403840142103070080d8107840e850007844c010b00c2031000a5400380a401110b22406540c0c0c02801410241c1c0d60007000f81c5100070940c10051030f10300c5100000c1d8101919480004598840030545c0b174003c1d1041c03841207455 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 688515458 1250 688514208 688514213
    0x7120e0112110301090207050a020a0e0603010506040519110d09140105010b03040c170c0d0f0c0509061503131a090127020607020f0406150809150117030409020d0207 73
    0x910070810a403031252800c00003031203802d0707800038100d9040d94510000140c0390300807410201d15160310b402c4c0c001d4000480a60104035403604041d11880b510b01100280f02680c0e03640240801d44070169051703600a070b40c5060b40341410b40590441f0030419020450182840c16414584082d10910b8006440c0f034000e078000c99032400003e00881e4050000d140300d091450805950301d9200100d240304a4030711364181002030392652010b000d6114180c1c4001c2040e0301c2c0341064204504040102042140c1c200d0a140d0300150031308112042a10a100c01000201d031340d42d00c500c0c98011a807004006001c01401a41c1040005075000b10761220130728100c22001003480d01600c85400c40b6034969009180204455a20b02d00c0300c0d00301c4050340c60a0f41941c0c9a134480240d03102040c1400113070000143d20500b41140426940414201aa0803036141d0f5511480303510b801d58941d0f207528540503591811901040144091584c1e501888110440c0070110380c038260340d54040404a801049519031201c2e00052003105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 688516708 1250 688515458 688515467
    0x1d1b040f0b0f06072603180c030d0f0201090b010b0a0f030b0a031106130806151804060e12190f050c0c210a05030702090c04060f08040807120e01 64
    0x91269192001c10901c140000080c4050200c10000d0703125000000d9100c00300103050070b024141251620300060741c240001d004040c00d4100319610011002c020340705508040b000100340c2c0d05c011001d805803407a041c2d441d0381102c0340440c0c0c1d07100000750340d00d40b80c440b00001c400e02072450013000314140c9030b910352400f00001084800307451840b20030035040140840040e507504003550116070340000c00c08420540200442d00500801c00e40403600b140e4501c0015401c003010440601c21035850303120740440309840c81005245042844c058007121120000a000100e8551201c00d04c800c043c0c04861a244c488860b084881c0e00c0501001c231288061401811400e8201c086602c4011039400c1c2607007030000415031170707507259803340c5143d224010203024800b0713183c0c00e034034203001c03861200b400d6584150311801e180c0d13030b01d40c05001e0803402002c1c0003000400c2007030840107407400c1d00d8465450715014610050b0807924013101800540d02030800308400c01c00500b01c81c9480d82d40e014681c0712013201044031400940b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 688517958 1250 688516708 688516721
    0x1e03010b0d05030a21020304120201050a06030317060a120318050108061807050c0304091401140901030f081b0f060a020f0f0d0b0d081312020609041d1b04 68
    0x901070701d00d441c242000604040256580c1002500d40f141140c908a050200c210584030080040240300009000c01c0c41f0305001002843c40054000384150b888003030a0340f0842c1d40921001c1e000494611610501c0d0b02c40307000340e68101c00c005126140b0162202d50b050882c5240f10400c03004180780d0301c07540100403401106640107100900b0151014a442d00200f03a40d13400c0799100d100580c0b079900020f90f00900a0b0103030340d1000034143c00c480c0c4842e140e861180081c43d0070103214461554a0000084031400500c6280101c4009070020000e0392031940d0304480700c4000c003030868290109000c4240000325519040c3c0c04224500014450140610f101509000015001d800000c7c010080f030006650241d04480004001c110000d603604908054140140102041d43d548080d034801f60034280400c040103000c2c3c414803083c21311102c1f0340d02c00079060700040c1690001e410610510038802c81c0d24050740a1074881c2100106011100d896400142c24030f214107078000d40c4c880110b000300e802810144200e2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 688519208 1250 688517958 688517981
    0xd050106031103070c020d14010903201504050a0b13060b01020c03032a0a030206180a020a2102040c051b0601120b040f080c03030a0c03021303110a051e0301 69
    0x4100c0b46040000444661100400743c0c028003148051480864503801030308030004e13070030070411000080c03580e0400e4060041208107800044c074400310844541951007160024030303400801000c0e140400c00060f044064001c1060717405020b1001107034007146d064104140304d0048031030000c0c0e080d11140b500c40200d4035074201e410f0455202c903031f51100b00e0710000b00300d031a018942c0100d0b06824031601582c0c956402c0c070b80c3c80b00c1c1190055540e46002c243d0002780c102d0140740000540f000341a2440c560030b982c0c00c40e00401961200c41c4002c10032581d145002c00b41c10b0003e480901c52420519034010030282c990011125001503030020b00003800682c0300321a180940c2d00c0c0405001b25501d000382003284030205030405015450346c0004102004001c4941c4441300d9409080c031034503078501c181074035100d070001c8520f22078850803d100040903074401c2c400c4a01824411030801c11160464440040d41c074201580240c00282b42c9801041c550381d11a40c0160500b00d0188a55a44ca5020141804d4aa01d01c506 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 688520458 1250 688519208 688519211
    0x1207020c090f06060408010f0203090705031f0c050d2307111024120b060409051908091201020414030105010605070303050915070c020306100b040501050c0a0501020a050d05010603 79
    0x89103555807034a803066008100d500724850305458034400219a881a6031140749a0b6207814003040044040e0740196120b84613070030582d1803160340c1ea000d2580b03640d20602c1e807030512400007414117000101c0ea40f021190b0022807410900380040002107104681149001c9013803901000411a1f4208858203001d61003052880c040b0700140a4104541c1d13a00c15420030b010000b42c440302c045040b0002c1c03100e1011910420713074201403850f988170354280746003503144425038040e150100051883d0505004020000760710100503c54441c1600090034900030403041218508001c0181c7e2030340365030344c1ca070007140c0b1240100010b980b2485d0040c5043d40c07003820f4044034000c3e418a00100001d0760400b0660b41035541604011031039998240c0c2c4542090f2454160b000c07840c1600c0c050140a07980320b0446962544287c0844105c1d8035000c0781d058034111030380709070340113124104410300c400c3d446100500071004d04002141d811208a44c0e6250981c0c010039021000914042201201034401d8024980180480c0c1030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 688521708 1250 688520458 688520473
    0xa02030a0632120c0d1e0b09010e0105150d110603162a260406050c06060a03020901060e060d050c03100605120103030e0d0606060818070503150907120503120702 71
    0xf440c0d0b265603208481038460a00002c060003400310213680c030048042c03c801c5001c0340d103005180100c0650380a07251071250f0f620b4030104620100c014882c25004061070b40c804a0407414001c100605c2821440e03048500040d43c00003039a031074440d400614014049642c03a60384403e402c01c00200b02b2103500803820b8100c14048601c9503001140c1c800914055003001c0c5508a0f518000d08a0807031052001d500c44e9064000140041e80039407160260103402410003c6d80c000c0e031a84020000c0a524500000e5804003002004104450003904041c41400e00500840c1c1015641c0d00080c2c101c0340212035481d4070443c000200b100f9058072a0405000e0a801e040941c18039011460319228502d0501004040c010603050189441e610075882c10501c0307610020a120003a01d905000b05000010b0b654582c00342107008072010200404900d69060350f174041c004143c100007000040c40c0260015004d207d1600a507a070104112400c04200c0040d02e001c0c20007595622651801810845401040c66045400081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 688522958 1250 688521708 688521739
    0xf03080106141201031101020a080a090306050c211b0304060c0f050c060703050c1207032a020a0605040c08070e25020607031d030703090905100302090a02030a0632 72
    0x401c3d6815650450800454201c0c51001130f45042445200a01514404514810030310303809940c40b400d0380c1c45544188120b81703d00c0c0d14000b150068a00e65040085043c0082c421003110601c0b0f150320006002018800103180702480c0d031136900aa41c1139070420786404e00b0126040c1c112400010401c62480c0c0740e032405400d0b460040c2c0795003014060320101500e030b02c049002403501c44203455031486414a4030304a82040100580180300e0a61503402d000300080c070520041140e00d0061001c4407813500a0008001241c1e228002024014070071191400c01d50000301e169041040142d000d040950b0340c015403030818004103003240301614410028419600c60716450340d5808142540c0028083c100030a282500f0041c04401d207045048a41d52880045104030a15900079410b80480781c40e41da0402c010f8403803100030f00945c0707181d0102030341000c2900040740c00c1e0302c11503006503400580341350300041c996220000300d50901c070450f0134108152070907608076a90442c8100c043c0718040c2c00300c501155126408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 688524208 1250 688522958 688522987
    0x41205010b03061e01120f0b180d111213030c0807081002250f06110912030c15040503040302060414040b0307030507050613330309030e04090206070f0308010614 71
    0x140186c2d0181541c02644004201000c20741c06001d641c0401c411405150490803000740346860a04c20801d88103000746240d446000da0512080541544081e01100f2000480303034419a11003548170810181501c800008160016500070150608c0c0700a802550301d4416554030f40610040c1810600b48100b007600025041200e8150b00d001c0800345c016900416802c0100141010810203061700381803143c0040c072411010014007040008841d540b81c242c0d91122550790324040c0c000c0d444980d034010084c5078503041654408503031040c880c1d003c5038a0700391298040b6442d508550301c90312a0078041c0c0840b0105203014040c19020641c142c0092440030b2540e10b41d83e50b01d001d00e109290044900040f0300b83c80000120101c80a44040314042c440c892100803082006041d40240b1541c4c00003202440421138400e0003454043c82c2c1540d1542088011907003080028461001e00b00d0740420100140f20008080000400312180a80c4442c5641d41c0740c0f1401030800400740780c110140440c00c210060070b61422 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 688525458 1250 688524208 688524211
    0xe15010e04060b011b0318060801080d0c0804080f0106050f0603061e04180c060915020703110109181d010b01050d020702150304051b0a0b0d050c041205010b03061e 72
    0x207001143e100c0201e00182d4128160090440070b00c08283d4054041c550460091912005940c04a2000d5640d9107002c68110401303010300480c9801c42104405d54a00c40d0001800c050b000f14062441c007030b6100c0d211449c00e40351002000059445903c00c001c5841c100d40c0083c0e007030806071503007461450140300003940504503c90000180340605140e020030349a50b03100703074240b50103440b0706500d410460602d404103035503502c10500000d90700307071000c05c0800d0380446042000d1580e4006207041c40c2142e4a00f035804250203261070400040c21070028410045a001803a520382c0800005132004160100300740805285202c061541e040c011150001e0341c0c808115070480d5054400162103001c1880025145208084907800740c201c04802e1000f4410041075458200d445078070a510008101e40500c010410984620100300000307010a041621442c3c001c070b94404190b040080c03901e6258103050104212061080c0c1c0c071695514121007450408010290b04240301d03e60350500030343c0022100d40100780 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 688526708 1250 688525458 688525463
    0x1701150324020405040c120b010e1e01170a20031605030a0b0603090f0f010b0603180c1c0302010b04050c070206130b070b150a0f09180210030e15010e04 67
    0x9440104803282103160b4180c5003e0030008105004807002c915009060305411840c00050501d801ca64550320744c000c1080103103200c0043c0c480d1b01c50a0890200c0c402064480389030f203040c002005039011641164240c0030707101e030810620000b0851070391902d00b02c510b040040044007402013007043c840c0d454414880e841d03c188031440e1003a074907690181010090a161010140c200d2004420703c1007042000c24602944410041103032511500180000e00b61840f00b01c007240c1058081010030007000230a8045003c2c2590803044880d00c0745020003190743d19000030340228251034200800b808166080c0214012101b08403002d0005040901c1042c0c1a4460305000034840d60000078650344142c04a080140202051803a1303589a40050604007000e00c0121000ca04440200d414000285001d43c0840152254105d00c060b44509000b801c80040204c03401c9155110b980710001c0d001642c4901c0401c400c00455070b000304c1c2c0030070918541752030002d01024450540a03c0c00c0148170f03011036440542e51003078 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 688527958 1250 688526708 688526753
    0x1b030c0207170c0901090b0910060801181b05090103061d010924060305012105100203071106090709051003080f0706060b070b16050c06011502030c03030117011503 72
    0x5115074031061405401d106000e401007500c4c3d0002540c41d480d6404095034240946000c12503035502000115012800c3c0149800b043c0d01c4401401488103603481c0d900071284a00c1c00080c1c1071038003140840805143e44064001900c0050448800d5034580100001019246159251030550440c540309240050181e5a030199450315810003c00412100c601846843c40c1d6454810740c880d04010f01400c0d0901648140d074407882c0005940624101d0226080c68000014101d030016903100301000c4d51002d080307581040481c0b840c00000350001e010160062a1010003007020b01d00d4248410300b0b44030000c0910107040c1c5050f10410204c0c4480c01145d034800c0c000112b090380d400491400c48000c25098000e03a40c54a0040361050801c504004407601402072444a079a0341c00300a181260a4820080e1510b0310360809001040842028801300301c3c0c2400d00c0c01078a00301042e494480d071954000360310561070341105101c0e15150000a20500403100010b2518446103030039502c4805420f4480e00c0800c0d8000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 688529208 1250 688527958 688527989
    0x3200117150f030d0c1412040b0a032a110c100c0b0708070c080a090f0303030209120c010e090405030d0203160809030f0f0c010f06060c0201020c0d02150d02120a1b030c0207 76
    0x680c418000c0d01f2035080350407415522070343c86580644041d04a8015140440d20308203450403805080915020031281e034213020405d4400707c00048400c003240851900183c85800002102c0e5a03401001040c0050155035580107001142404102c3e02d4000d0070315020f11039100c00344404180c0c024001c0141d160040c4c44141e60f840500b000300d03040c00190740300514825000e080401015450b40041c07640010450341d9408610201031010f8847e0b90040c0010b01041a604849025050102d90603078441c2c0a40c050302d0501c1c0382c40209109a030b01c11544030202d1441c54030302da01060340040d6015048003148004600b095895244048544a00456042d000b2400710311001d0050094100c5800d40d04240c909000b61a41d4440c05050f40285c10703000c0707025001e51524444d060401810400a65800034111200007810f031a001c48183e010940c1440000c0d020004507a80c1c7e6061202d05000341d030070402c001248a0124481c040901d0302000038001c00d07060904404406038001142025100201c1005160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 688530458 1250 688529208 688529243
    0x207030903080f07170a0314010e060f1507030c0c06020f060c1b0a24020c0a0311070b120a06050306090c1005040503070e0609070903200117150f030d0c 67
    0x42c2c003131584010f041302d203070328031000801c03040c88064841c0c070b00d56450a04c510303107a401030700102c4102400b5031200852610006125440c02440c4004400300150221620f4015514190510342c0f041e03905070007244130104242c0c1086150f0b0b5240000703001c944040c180e00d10013017400d25281c0c1409001c3e80c985290100303080d00f03103c00e41d03041900003500107400c0311510080c502d41051800000f6441a084505614036040030361058000c88048a45413000b90441414a0b50181c0344d0440200015095100b4580d01080c1060303000020070036031061402e079480710300d0000f4902d0256201ca40000e030203030b0000d900740241540c0000719480540b404480035402c210380c0341411a0f0500843d030095505103d8200d0000b400403403006114010581524070b1f449075520040280c0d80c550351840010018004d400c42492a00c00c496a102a400d40502d0841011494900028400141a0b920f2044c0710002c17002d070342c11841d14404200f090301c8154050f01d112618a400a015005440400b40507041006100300c030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 688531708 1250 688530458 688530487
    0x4060f0507020124050906120c090109060816121212110903010b0307060c08160f0516050406081e1504050a0c080303161b1e03080a020703090308 64
    0x14450002102000030786420381000740030340560f2405018a10195801d04405103040100e00c0070380e20082c052045580740c60085c050302c03840e01d0b4002d40702401a22000034665480d500c44d2802014400c5002c10307094103240c0c1c102c0c00d1808480b1a40c2081c112400c0801c4281c10340080148002d400c82d010109401c8a607000744e071030141c2c408401c40e1483c034003000d001c4c1716400d22014104242c8290b0080140c12461403e269445405010756408a2111550707440000d01400003080b10042404101c540a01a070341c2d010001d10b40854121900d4019410180744164900000002440200c8092013490300e03140243d500d03002100601d101c03241a0584c074641c1420200441a485c1e00290154101b503c0c082c01d1841d26541103080031075010b011000c00042d1450000103990191070100e24001d02c03501d0f6210f040c6e8030004140c0c0034001000107003d19001052504c0c4806084560700d0360030200b4081580740007005054000d002000e694414050f04001c2a0712008090540740d005c00400e680380c840209412 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 688532958 1250 688531708 688531721
    0x809031c0f0b060f280e0d0609050d17160f0c03091a04150f0e010c030e0d061d01060b1204080d020309030405010e010215040209180f010605121b04050406 68
    0x103800c09800101c4070311800501000380410f0174121102510205809641d6040541d0b4a03a900000b0700f8000d108111403901c04102d5038458803c200014242102c1e80c0c0b4242003010065114002c0384030b03c0300c0101040c400034615030340010304049000300c20300310980240c00079403684441010001c5500c9042d007094054449a0003601e20400f100c1c40c0c442c0c042c10146440c1c2c0c098000c0349040300d22040d022038014054601c50850150584030210f12803042c40c011981e403940e00d035094041058000a400d41c60b20380542e8000b82900442000c5058070010704c180c401041c107014900280d03031604c8800c10404c2141c3d0191401e07060010300720803041d12103081c44a4580242c07003040140c60301c0041070125003034001009000b160402c0c1c131004d41d004030380e00040e600c2d980d090301400c5002c200403001030014601115010350103682c280c0400d100301000c0c031000b460241c4c1c0042940690f03560741c00c24001450020800c0c0c980200c02c0006003603001c00f040e501c0d04902c03082a0800e000f55250b4002c1020400280c101c3c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 688534208 1250 688532958 688532981
    0x28081c0c21030e0610060908062202040f02120106020c06040302180603030403140303060310020f030610031503200301021c0e0102070b070f2d05071b03030903030809031c0f 76
    0x1300e005041040900745451900d10510012072240040001c84200c003196092003049401400104404266054007a000991208903802a0359094581004045202138000408a04480321080d81070140103403500b01c0002d04640714440600007080140d4810000c160122741d07580c48a0030b25281e240102e0310390b0040d81c000420403c0000307908080a04000084e43c480c00c402c41c02c40c0e250341b8015200328100d126881a0b410388040810024016007861000b080440b80b5500d80002c0c0d41544031025401400b00d50011203201c040c00a22030340e518121707082c20345400b604070001c5107055068900002d403201502da4403910b00740c641d240490029420742c181c0d14990b401c41c2000700549009000141034010310b204d030b0320100d8804c0c0c400742010712440d96110020f60340212041d11250b82c20364251040e412015003100c0c0010355600e00e001030f1110310201001140300e070315402007103411854003501c506002481d8000c01da1003802540080031400603603600c202c070950400690a10482118005080c1d8039054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 688535458 1250 688534208 688534213
    0x8030703030e120a0215011208070f0c0911040905012414090a03060606030c09030506060f13060b1902030306011403070c140708010c03050402060928081c0c21030e 72
    0x44d12070b80d008500020000f044415803d001d03a00c4005600884290000151422900303124910000d10303480c2e07505280c28092024860502d5442c088801507070340d5034106544002c0c3c0410700b045100c80c0350041502408042c11008030a40080002414076240000d070001000700c58203880d540c0203410400c5600307480d0058900d60a20341c0300d04141015010a10403000020b01c1d120241c243c4600c40c1e02c0c5a42501d52103800b8080540381c010810140000c444c1c04035511124482c00d040c005512403158400400d038803503010b80c45918142000e06610110400c031070035500b040003085881d0781d10464007000c01c0102501c8a403a500e445d0421540100c1242000b450351480d69003d690911f0002181d4048410510081c02108a10340045051741c80643d002500300e00c081c050740b1240e29115030f21408900e82801c409000d9451049000c100b52603a41c4404015000340320038550050800d034450b103e1408900b442c0c59014641c1d910f6034801c03124038010450110392000b0180546101e07811288443c603c0b2002c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 688536708 1250 688535458 688535467
    0x402031305100b0909030313120306050402070c060905010504030b0115050d0e0a020a09110301050d030e031603020112060602030304170d0903021e070b0703030f090602030c030406050603030408030703030e12 91
    0x41c920000d0038003e48a62260b0540000240e04032800411a44612040d1101456010b001e0382d556142c030000c03580500c00e0540b00c0c40301140c5512540301803c42d00b4024581c480643c1d00e45280904900c0c425002903041003020030052000c01e0240d415181118000c0d00c1c00186400184003c681500860140c5400242460203e000310400000c544100d28000c44600e55155560041c0318111800d60345441d1f4022014401000300c2d140200100300914001d04040e500c40c8042c0c5d0000f420008180074992800e62205010f06c155640805000e161660340101040300d5030801601943d44d0000400c020080700d01210025124440709054656040074007206002c80a80c600e000307501c43c41440100281802403048500c9400400100082102d000f072459510b0850507842c124060720300300039034010b8291610b54410020b40c4504c019881007003050326058890500303281020507540d001c0c1900748254410320081c8402d4401200315083d09a05007800125021240c0845041c01c900100b000710070b202c00320b03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 688537958 1250 688536708 688536733
    0x111011030907150c14120408030d060b0708041202010c0501020a03021b061302190e0c040501020c040e100e12070302030703172208160c08010606050f090402031305 72
    0x8091801451294203442005403a05009100741c035185044070005444e201c001030220b2480004010b5141174002611945444020b2180c074a070f200740e00c103401c198030014444042010b60b106800240490f425041d02d0f003029503d510b03516008902503040710142d8030820404681c000d60b0f1403400350f68403c000307548541241002400941242c0791400d082900204083c01030540440c480c1d1042c1c414111501e40d0010a07001c0c4030215003054128036040f440c0910118003128585900d91051b403000009e00da4640c2004002800c10240049040c0142e003406800e40c440078021641d0019040c840100080c4a0aa165458600501c03004111a200000103103801816804802000ca260083d250340c101001412408a0049811100f0004428525204648031800d2400b100013144c045c41d105400c00f134001a001c20018221401180c150030200030070000c20758280030780030043c042400c0040c102500808001560310480c10352612607580040000e107010042d0102190450b080000c44e501c1c0c40b0240c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 688539208 1250 688537958 688537991
    0x3031113060230070305161a060112050f1506040b0403050102090f09090a0b07091511100204060509060702040e070902030a151202101e0207030c1a0a1110 68
    0xc883c44511225146407036080001007240749202021a100c02d20300e410035a443c104e890760801c0341c6842034031041c1104440841c0039a0911244681182d40300c141e1420300c100050903e000c40300003490054200030030086c020200d20b10081c0c0c009480b4a130000c81c401d403180001d500c0c0c441c942019111800100c0c0101c1406815070190004a205032440207047d668a0104081c0c900c00311051051a40503000140000707851704501a0410754506041c010151252510310002e402e0180c09000610340c5006c580050703408003c0c030a9081c0381d1081c1103250600300780c0c004100b4800c5111b101c0c0603040009011045489581c0284880c01c030308000c1e954407036252203014000e58001c0d10760825040c00c08011a07880a10710801130b0842e030780203880d881006595424001260020302d004428402240c009141030056040c1418041d29140c1c043e14500d411441c2800c1403405681008803440c4954001d1000780d9040402c541701820507041c02005038100381d00e6280781861a0320b80c404890700300154445c0b8404d20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 688540458 1250 688539208 688539223
    0xc0c03030c09080307062c1b01050712080f0a0c0f140f0f190203090f0409050a0203060a0905010e06060a170c03160510020a030801170f0a0f020117040807030311130602 74
    0x546280005100c1c4002d034209003000287d28540140e00303d5800c540a801c004091f0a100c3c1d44181400c2c1d08001c51511120000d1041c58108000710304450708100075141e000c0040e586c0000401400c00201c612a0340050641d0006508502404000203140c2d0304002d902c1e040e41c4841c9900c6240541d42e413614244800761703820106003940c0155002505c2c41034035001006031141c5080103400004800b886404102c00b03040a80d80c00e40710b50055840d0080903803405d02102c3d00c5451181008603428246252003821900c5103070030301c501c80c2c100e9010f00c011651458080000c44803034401d0480707005201518141080c5c800074031650308d881420248402580c0e10354010003143c208440c4400c01d82603106090f600c0d0603038040000c001030710301c20052001c03204030310303070b603002c10100500b15030340d005400b80302030720303083d41d90105480400024244404540e44035404407800b034610903038941c090909607100100c3d401590b4004051648034420301203051000d0060307a5402c1c44502803040d186070781e0700019443d09003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 688541708 1250 688540458 688540481
    0x903020d090609030b0613090203010e0c13020403020d060506030313270209030d051305060301181b121d0a0f03030b19030204020d110711040f0c0c03030c0908030706 73
    0x800c020001402c1d4010080704045a401100310145c41c4d40740800c00031b01c43d1503140c0510915545400c05400b60310700b48589850740d11207074020b04d4420101c1e8108180700580d071516054050042200340b0050300c0741c4062901c65540b0403000f25180d21a040000d0850040001c42c1c282001c101d0341c0000e001c00210040251068042e152407880234245e4110400d0340f145482c580c0d0160700c81007401c1030081c4108000e00d40d581040c0c04602505444500040080d4030a0f4400c80300d8810400c0c800000ac030ba07500c50f483c00c10002d036500520400c401e10003c2c0c0150200e164202145a0b6816840034409505140c1061040030000b41c1c2c0c00c50070039150140604c01481410340019240003030151071030521000c80c00c0c2075030b600881d91800300d286a003000003961200d4130707840c0e6003a2500802200508a4000742010a100301c440600781c200b03c10900086034842541040514188940581c8194200707c600c000e0640505d008a08014030240565451910703a21103d0349210000710b07030003070003940d6025200207031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 688542958 1250 688541708 688541717
    0xd0b090715080f070e0a090c0801230a090506060d02040e18010b060d09060e010507050c0111040506090402030a0e10150e06030d11100c03230108060c070f060903020d 73
    0x51505404994904003200c0000e40700e0844030205520f280160041750078682e00030190400c050f29a0302100540700030300600c0d8041b81c07031071005000200f143c1800c1d8014420b50f06540810400381d00c001200c0300924451000215951404164241c540c00d04807a11060644800c0d07540e65650003154100400031240c10340e80c1040801c0d04200d811040c00f98a043c61070040000d401c040c03010075040003d1141d1002161107a540d0710400740580d0080c000c1511602c01525410b07102e00d5a21562401d40340c084840c409645403c203c2400310799a00015180211010303070b8016140da4a0500c03101c000d0080c060902154440d00301c031401d440040e9009804180d2115814020041d5128440206603405990741c50b03161f00400c0c88086268460b5640068034100901181c16880050307900030200d85000c0c50302c10000c0e45410240d0141d010034101078107210103115040031150315049400d501c4240c0645005441140007401d1014001c0140428251642102c1c04008600e500c4c0b80107036642d0707403802114000c078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 688544208 1250 688542958 688542989
    0x100c0b0906010b0d1104080d0905031e0601120614012309041a041e060911121507140c0105040c0b03040b01030209070c060f0605120d0507020f0d0b0907 67
    0x140408a181d90403902c8521405003400400030600c1c02800020448035800b20041c040064000e0007000360700000c04e40c503103039005c41d6802c040502d810324880d12015000801e804803041404000054868115041d0044090a510051078036401070030a04103500030443c444000481c2c05084c2080803e03460071950500a200d003914424040c50490407513000e0160038a41c0c250300b4014290782540707a071051140c1d14903040b25007000c1040303000b100000d00c1514000e0341e80460b80200060701141e03441402e0308582c181303192000c07032540503038900c000341c08241d81004a41c08107458600070545986402c1c1d1410300b4603202d4040c4010180240011075040e9249400e8000c00607032001c0c20350031070340256085103584c42540c0c06c0d40c0038440b21841c094810300401031502d10600100301d0320303c0313010038550000320040b420341e107000100700700304880030441802da4103c0070788040150b8200c0100c5500303682c195808207411002800040d034421010708090049a103440802c420000045076440641d508005030f14006c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 688545458 1250 688544208 688544221
    0x1207020d0c110f0613091e0902130c05090d08071505040b241f0306060f050d0f020f04080a05070b0414040506030a080c0705120f1509010605100c0b 65
    0x440d4042000903280010140a03907a00e4101560801c208010140000d4030340f100b0b003440e100c5c0481c203da01c03c101c901e60b0340d02c841e04824450004689110702e01c4200b0302803540705400240fa031102a200e2106901e6541c107405d40c0c824000c0c03050ba171840c84000c03c002c81c0750340709081800c91036000303c204071a08500e42d20443c545004907c030785401250051100d10751a43e85203000e51015601c8407168007120403040d0540c41c82da42da0103101150900c5222024a8100f6503000a010354556400003003d01c0743c000d090100003540701c0180d4080f01d12a4602154050007800000000d128035112450010400240481c4880000401401e0b0a1252045902044e0b64401e141d001d030142d0b006015000d003e800100001745041d0f0045500460001d09503607003240c031540c51811310380c0107003e0f00e10781d070f00b15440802007481c080d00031080b0784038810003901c005500d52035440c0d02d80401000c1c1e4002440140003040c0c0c489000d6011001402c40a002d81c0da808561110103000f401030f142c1c04a45003001000000c61 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 688546708 1250 688545458 688545467
    0xe0a060b0a11030903010f060312090302280b0a180b040510030e01021b0706110f070603090f05030a02031305010c111005070501021b01140103030c0b060a08031207020d 74
    0x11035484080c528141591076904985046140900031028482400322003400d0354207201d40149501c4d00d150000310140303036140001e0424848070800b01400a00c600c200f002d44c41e134140c1240342e47d110700642e00f2145001004580188007541105400c1c1801203062403c1c150420500c07a000452a11041700781c40d602c10100d80c40303205078050341e6004139401900d4110f2078044d4002c2c074840a103c200150030214100340751000040c4904204140380c1c0460740800056412003848486101c8010161515900e0340c07054580d5003285200c5c2404040e0380d03501c03034001c1c0070980700620440340d0b02c1030969583e8555400d000707540f42c014103e89000001da0040018080d0300030301c00325480076071080044500c519428100f05100d03000c405c412050207000c0201e080003400070310052400448400f01056032000212823107085601705045242000184c03001440400d4011910343c461030f601a07000e4440d0707a01c50700811503548085e48040e4840c8004107101e11366184601d0003a121300c5240d0b0842d03c41d0340f14400100e4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 688547958 1250 688546708 688546721
    0x19031a060111120f0f1b1b100c0b04051e0d0e061c05150a09020d0b0103061811090a0914060922051203100608060411040b0c010e0708070e0a 62
    0x3645400070442103140390004000f400e170700803800d44c4c2c0c10b043c85041c0c1c0350f002c58442500800c200d0b5400c2545040c0c80c200c0380c1c0d12641481da10945100001c110f4600010303090340101c050241c00103034204000790401c507041183c140c401020901141d01c0a0050810381e80d0b820799001c0ba0400315402030840012810210b0544010048000c00d0210f8139540340340347e90050001501c20f04050200c0c50200d0380319120b00b421440200a810401030b5526000c00f0074008480080c0d0034541050f08084041100b100441c605c1c00e901030041c08006209a001e10311070680d445aa2905034000d0100c0800080346001070b4000700780e680c8120019280c1d03a27541e100b00589900c013290082507000d1441000008500f9a00b00c0d03094051052003110318806403010441e400707420884403081c1c072101c070b014103001e02c6600181c040d80014040c0d40c00c0c440c0d034415100300da00a001d00c4c0101003210030003140d822400c1c03009402400c2d514020400380c40d407131510b40aa842d1a04c05034041c0b026502d01690109440c0c3c2c8286c032502 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 688549208 1250 688547958 688547983
    0x50d0c050a0f0507260705060a020405010e280906030327090903120624030c081501030b040f0203061525080415020105160c1119031a060111 62
    0x1031890b10110740b42918190440d40e030940b80101504842901c05050319000300c403440e800c000c42900d030b6031140744c01460f1440c01484a551580180410042640c0200d103403044051304503007440060614090340c448107902c04e044d6441c183c03140035001812486030303800300c07059a0003582c40c0c544012449058202c060a52074010170307800d04500003000003040329404103802a2080c5824480d50100c03100181c1901c5142d04031054401d000114014540c80c1c0c50304244c04008070b42400d00103a81000d0000d01890341c004c181411030800c0503900c0764541e200c0c3e030020715071000081c01005007411070180309009401c12904d0070701450012001c1e80c6018008030175954074000015084a01d80800b180b05895500c00180c1140e510b9000c0c04045556011000c8409070030030f103039000044601c0e00a1f0b05104800300ca01a134402d0005a0304120040744009201d0078504a0a40d0006180400d480c0840140580c035400075107071510703d1040c0c1401d50b0040d603030703a409076009a03155490000c0240d5581c1d00c800816081 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 688550458 1250 688549208 688549217
    0x6090b0c070b04020f0a05061306020c10081b0c0f0d02010c0e03060112020315090a030e010f050a030507090807030c05130e03120a0b2806030501140d020d06060303050d0c050a 77
    0x703001480c20170106034000c0b00c0a40510103e0766103a0124803290040030000d4010301c0382c404207000d1745904000b20300642c60211860002c400240b1805043c105014204558140268a0382e00410780e8a00c00c4803082c060318011034001080310b414003902d0f031b5980c010480c01542000341c01e0310b45520800c045901e0701d5004010300131503441c0c40003c8020007048001280c144c01042458100f03150070720b10a0748100b42e0440909208080351500411700e0b01d010107d07a0502c6070003290811920f034498180c401d0000541000101c41e200c0f56800e541c01d840d20760101010303106035100402003100d0090180300303e41c015626080c502413400d81a805541c0d03000900c680c0d55006000d4810200e414845a40c0c100d50090703400a144104500454240d14840c211455004002c0c018041d1441915407140c004207000d1074104810350514075400806101070744200e11424800c04085c0a55641d41c02141c4100e82c050340400c5030942e03034600030f00300740c202849403d100b41c0303865210911140100102c0710703020310907500c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 688551708 1250 688550458 688550461
    0x102010501060906080a0f05130c0608040b040f0c030507061d060405220b0307121109071e0201140117070603020414090a0f050405010209032505060c1906090b0c070b 73
    0x822108900c5c000c24610700c154a440c024003002d2858800c280c0101842222801590301074240800c0e1100140d2000c410008000104404146e4030321103960821361002d01110b8034442802d10385007441a540003d0310b1340c0148500000d420b5041102c80c0c00c40070390300b090504a0700a00041092038052880381c10f4001d6510010620b50081010b5004401324500d4000240054220080b0b8508200354101c030b0a031340c030030040748410300160b4000c0100801088981c038806160040e8001c1200f0519075210559480391410416014000e402414140385951003899031982e690000c1c00c00b0700d80c91020506540916800441d50034880d00848041d101d1702e540c80500c9029000900080c0d40004007608110380c0d8840c000b001c1400180609401907000d0000980c071008100101400c00c03281e001084e855031440142c201d00001a4001001116801c0b00c0721071b1254642d0742035070f0503c10f05450486940415844100030444141d21141c1030318020544021569144020000c1c144125031010b05407068980 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 688552958 1250 688551708 688551719
    0x1903020c0c1206151c03171317031e0a0504020a0e01030309050f0d080c0d09050d0507050424060c15052206182d0b0a09050a080f0706050601020105010609 68
    0x18000c4501c1300d01804070b10814420500d40180b0b000410f5088000a09413150502808003075080c80e0b0300081602c6a0020800103540e07a5000c44000b1036441210900c04030001d003403500080d850b0381d0690052000c6501c1071a010075200010902114124841e01410b0700c04160250080000c0781601d50540321030340d14a0405041007c001010140180c0c00603400c41e014001411040180c890114a40024450243c400d2000f8009480940016001d44401251a0003007500010034404990041c0d6000540c1d0ba0ba13006124030624014040b400f40d40130b50400042d01d02e42c001e086038200c0f40030b82c030241c207003000f507400030015208203640240d203030352034030b070920040c5800c86000c0913001e88a4040054060428035454044400085054444143e030711203a40100914048141ea543c000c41034400700314900d655010f0301400050b2180d1000b60351740030b02500300002004103051003a048903541d600c0d02c0020503400c100e43d0085400b00d40c800c2c01c000c04285e007035005000302410303259582c0710a40c143c2e0030903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 688554208 1250 688552958 688552981
    0x1d040302070e0c0904021b10110a03020322050f0c0604030327031e1b0e0c1c110a11010605010816020322060f0c020a1a1903020c0c1206 60
    0x160000c6074441e0708114000d1150703510310041c03a0707514070780011008507454181f450313042018601c0d43c0102c0070f041196903910001c00724110340a07114141001a160303142c0d01100b5054100c6011640e50900040700c00314244940055451003a00c07050707013107070000004501881000c0c0118400203012550f4001d600f0044005030328200402040b684100081c036607a030320703915040e0f92202e80e640882c0780080044000d01c003104048840e2034103101a07080c0765614000c225400c0d840300500c92500140c02240c400481c981408407201c2c3c00b07680701c1007800043d012401c081c270540e200050200c00b2580d02600050040010300410b411904140c49811040da80d401c02204405c1844900d541107010400c6000b022140c800c1c100042500001c80b0901054140310303001e00319622060980e81482840c28117000180c3d528105641620342c80f14810380c05100700300d00b0040c14018522110351504d5412601c12080e54554003504825520004403409440083c052166082e1200a0381c1c0554009000003040c01c0b224 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 688555458 1250 688554208 688554211
    0xa240c030c050601090e0c010203031e0711161d0f061302090d050312010e0906040f03030b10120c0c0201052a0d1d0402031302010f09120c1d040302070e 67
    0x2030304200c81d400702542d8665003400f1090308010703041d5548000e400c42c0e2a80c100402004c0c3c1c4000c0c0019451801c0072041d51820030b00098811111400c9100024051440351490f003135090304000880700c0d4003240ba04420303404004c1d40104060800c051452040884800b240c050044400d00c0903c8519110315042c40b0004e80e200016502c1190204001440c40e12004c401034400ca0081c4003458441d01d00a05200e4900010380c008a010824a001e0183c0454041186500300768001d04054462803540380583c040c244c130744c943c6a0f001000c0800001c410f6044110b15030340c0b89100404104003051641d068811085818020340014000d101028080d0000440281c42ca001c40400d03030407645c02d1401440c5040d802e4400c80d400a103e070300180800e4192a10403940016003100c0035401c40ca000b8003006601010064007a04204014615030100e5000301c00540107030903030f1010604d074007038142440c050714644c40c482c1c1440d86841c4181301e040c00034203640c0d0b68001d80d07065000e40482840c110050343c04280 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 688556708 1250 688555458 688555463
    0x20409060b03030f040915081c140409020a120606020c09040203070f06020a0302010501290706060b0c0a03020f0601050901050d1502030403170702060405280602040f050a240c 77
    0x161031a07449059681003010f450303929440b4601e65a202c5c20b10301040d00b918640042c0c10b1030302d00c041c0007d102030003000c5514241c2c9150701d283c6900c07644078403408682ca000c03000d00055a903100000d001c945025260001d10803440f940c0c0310342600c071240201080c11640c840c0305003801038100700303004991858222120b580141c00241200e00c881c1d214080641c84800035480f000250b884101301200301502030060b58014140300022003040f50000b2010382001062001d000c50880d4005001020031a00f54002000350603030b070035815141d4000b002d46580d03860300f458003580584152841d1300c910920000d640e5060303820262104c00940d1900e8180f002d00001420304a441900e604030801032907880d48061031041d0b00035a12070002140031100324002d48000b60031401150040e02c2008042100021032400c078500749207180a42e0685220f224103038a1004100070b180600003c1c0c0011101c20004014003607400445100c2c0e44550368207035864182c040046440c0300032101c0800d00304040e003e43d1400e10a80e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 688557958 1250 688556708 688556711
    0x507020f040e0a0209010e06030d0c050a0b07050c16140607030909020a03140c1e0a170c0304050c031c0c020f0d05070e0604020c0319051c02091309080702040906 71
    0x32060300000c0035602c0d801c11240d125402081400198038191101030f004140b00280405c2038105000442c0d00c1c0d48141c0d03501c0090024030b01d01d100c00c00c8010040c0c050f80c0b40d04001b0005150505900041c00303a48800022a900c1c4650b1070110b050b503150900704012103c5c00d803c584040009202480610740285100750103110301010f00199035520341c002044081903594001550762307209540300e04c0d14180506104e413030010500500d4840b6840f2221100d24181c411074061b00c0e03800c480c03003c5030099100c1109000712120b4500340b00c840c501401c060350040f44141c007500c02500ea00000e043d500c00c0b01425821048416480d1889454001c0c20742542e06d0740081e10741280e032070042c40403840303500c40080c044500e41d01401041000040401503e0f8005e0003c603815803908040a0000359680250401c00850729400d1a940008030700540440301185c1c8480280c44010346503403c00402900554a82030080182825a803d481458810104c00c543d1224086003024819000d020007000d0182044174440d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 688559208 1250 688557958 688557979
    0x20f070b150108180a17040e09011e0524040b0a06080f060102010c050a0807021515090109050c041a091c030806012f0c0604080d0e0f03070501050d0b040f0504050c011e050702 77
    0x91321014007480c03103403012700004640b41c4083c03e2030090841032900054030862905003400803404100b1003403030301010007101c40401800c0d5103000800800078600e61a1f4020607440000a8880d084821184034641b01c00c104811a07a07900700680c245c1c0c00303105004000030003c02a000006019a00c0103411401a05c101c86000041c8001180702c100306032284083c035680c40909810728a00f203010180544a40b07030050010f030928801c2080540500c3c00b420200210584a060f0880014030585000d0311008140c0c140112500b000855222000b00c8203400107911078001601c654001c0a021036096007201d01d030124403242c0031000002d00c680c80c00d2030900b4041e012811920f99140f102410191400f00c0c060041d00d0300002016290071000d4601500456035072000d03d0300303540c01050440848400b801c1c01540c6221111041004110103601c041c0e00c10b2038100308141d50800b039445284031b18818403c98050740c14800042d204400e030755042003540780c415010303425514802c0c0c000d022114805408880395 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 688560458 1250 688559208 688559219
    0x10b150310030606030f0510060e0601050c0a12051201060c150905010b030f06160309050d230d0c0f024c050a0b06040f0603020f070b150108180a1704 66
    0x4d59000b9801550025014020322040c0702c4d05000c41c002892040d80c042280914107007001006c0540101803505016001c91010b86c0f0260911201103030642c13000c4414801421480040c050380c000c4048482013400b0440082006030040e0b464840850f000300d0b074038004000420191010304000e01c01203c1a5484100280107070310100009450101c402002e850140381150300507056000b501410020142404c2c0e40c0004101c000c80c180302c4c030300da8078600700c6504000340e0505120001e0b03501c8500300030b60300080c5010105006521001081c4c2b50381c1d0f103551003000203d2081380d450b2134441101c01400000e00c0f02c149a0030f6a00c080070415040b61030b168852462105480d049111a10182c1000036100d004010b55503400344907a00c10382200f2141c2a0030315080031010240c6441034006c90b400d0503400030b102c13030715421100d06641049500040780070745072801004000c003001d00144072a001c10760540120300c03404185080242c2c4005441d0003003958081c0ba440b000302882c40d0100c0d06a00e01400c01c0701061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 688561708 1250 688560458 688560461
    0xc040b04091a090c0307061202031b0408010b090c04050f1e040f0501051801060507080f0d021c060b040b0d02310e0708040c0b1809090d11010b1503100306 68
    0x70b03007000e81105050140342c503002140c1080442c0c01501c0c82500051420302440e500300b0480080600651030040c0c5a60f2061410103103280d041181100501000c40e00041c00d94054021035a04001601e503072841d5110716003103c12901030b60243c950703c8490030b610501d45043c0b41002014095000b0640c8000c0103540c0d000ca4116500303c00c0354044c0c1c94079000103001c20f00f000c81c810058030ba544000c2902d1985081d2009100307005a01d00280006800590591aa451001a0346544280300d1085544108084400801002690b21044c00d603007848030001d02e01100c2c90540301250403000446280907a11900d0000030350248074205801e8448800903002500c10f1000204060310650401c0c5600c0c2c00d04441d48100c5038014a0902081000b50400002811070712508045035800203e45031500605011072062031080c4075a41c0d000a501c00411031540c00010b140c00c5509203a440e11781500c10f150214a0030f84140b400041d0304407240354450b00c040740c050130003035512000364290814001c0e229903030b050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 688562958 1250 688561708 688561733
    0x50c0a0f140307050c060903040303080601080718240e03030d2c010c02100507090e06031009200a03020d11190f060e01261e10030507060f020c040b0409 67
    0x8002000440c440c642d941042040e207030007c90020045040034075582c0c00a1000170028003160420210401281c401e40c05904200402c038a1000103100a50b00c03140094060710040342500c2c91044003040c03410209000301c01000c820b0b0340143c091032074801c621880801910840780c14403405500000c0442c042c560407001d00d00d8440310b20300003203180c0d04c204d0030003072808032443c141c0e0916501c0c003005d00034071036000b034111411105101c104040d180d42c0c0100103030900e90382c084010041d500740b80c44038081240c0500012008900d1050821400344c6a10070311600300c01d9800000e410003110480303c1d0115440703414200c80007000415400e02c8149171119040081d40b90750001d04205645082406504c5c0c002012a101010a20300041a00a02c00c49903c01d003c82c070310500c00b070220701004141886045038580428040c2907640b81c2c618100140000011420740c84155418054100d0100b40380744100000e0103806e00310340c010050303001307035204000061440120f5142d002c1e41d03940b42d20002924940d51708 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 688564208 1250 688562958 688562971
    0x1201030f0227160302040b0307020a1b0f0e0a09050304060e0a0501030504020306060d0203030d090c1e0303080c0a020c09150108010503071d131a011503050c0a0f1403 73
    0x44010242071040c0210b1444010048001c1c0d0100da440421040e01d02c65056401046140722505403644000158000c0c4559000004410300010410004940000350980305e0740c812011200341400038014546410f0f51806420000c0503100b104101c401c080d03461080c0c00c4000200005451001607440c945982c0c020f0340f0210114001c42c4120010345003c00994000781800c0c20301748001e00d020342c002902c1c0c081c018409885080942c0c149801d544081041d5a16844208003c10148250742070008100c2c2191258940304002902400c0781004269a030000300d80e490b0b160030100d51540da004180642080d860349085202d209070107101565010075090181c030700389804d54451491540010044801600310600071303030000c0f400300403000c0c0301120050740010281440d43c29440c2c060003000c031000c0e00c050280c40300d0f0304400200c00d0044118900e40c120f818a00c2400c0000484080036015114200c0710181d004900b4001c24446c68004c1507514010f02444c42c002c4221341000e1015a160342040d40c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 688565458 1250 688564208 688564223
    0xd14070b04180f0504020d0f0507031e020f030c0604060809030c070b0408010b0d170f0c0102040303080f0a1a0d02010519050a090605040e15120105040609061b02100e03120103 77
    0x604900315075500c00d10318808800d03a818004c51030141c0106200b0105000c0060003410f40700d24080c00e12009001ca41c010315841410b0002c0594501d0031161f1a190000301a4803444031981000c00500c0c0000d44d0826a80d0041d100038141807a082084d2450340e0020000c3d4a140401c01c8103c810300d200303000303d2016001c81620310f5203982c2014200e42c2118941ca0304c0c5809808808001000704841108810002684050282e500c01e80c3e00c4c1c4818050040c00c60803203442d0b0012402104154104210511507003e4402c40c0981c0e03515800c0030400e451129801e0110960340511101c19030800301c1145507490b00604016207401c03d2041c240701c41d00400c04903000041e501056401031164440800c60090501d071400604042c00c144d4803000d02c00024204082d000301c58016090a0340701e100c130100d00008544000c1150340f40604003540031300200f42c000c586642c540f0b01002119050001c0e8804004a19030040c0500c00d143c41645d0000c1c281141c510b00da512091154042d0b0076210032005001c2c40c41402c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 688566708 1250 688565458 688565489
    0x90d05100207120c020a1802160b0402090c0f070807020103021c060e1003050c280b070c0b160609030e0409030c02031b0915010314070c05060c090d14070b04 69
    0x1803c2610320081d01c01002041003030100513026030f0340d0f0501c09043e507100e2030440c00c06e403044102520080c0b10b001c040542c44046080840244411051480d101b240251001840d51b92911a80d84083c0b05004210300c2c41e61043c4510b0002c03c1210340030340701e1070344181001460102580c8451840341101c0241c0518151618400d100d00aa0400764980042c408000c59503254155501c0c44e44903a00b805101e4020346035580031010321010510001400401481d80c4500580c0303a101d1800140e00400c4141e480204504000410701d00041c1116003080701000382484464403075641001070003005909030f0800c6003840d803c1d803842e9646d200c0e0b08202846521410140036162040c13500b003001c03080030103841c4821280e040c48962030f9021801d03485214109030b400000541030060f801007843d4101012109510382c200b101c0160002c1185404902610840e032181e07590050452851003941000d50300861510719420000300103d080c1c1207402d043c502505e01540e1180842602c80e0016031014082d80290314 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 688567958 1250 688566708 688566713
    0x807031b0c350a0209060a03080a020d1107030206190c05070f170604110904030203040305070605030a200a0c060912051c0c0203190314150109050301050417090d05100207 75
    0x10101c100d1540b86080030b6072042c01600d10141c40700c0a500c0040e0003a911000000d1240d50b134000940b010b194888480e41c0c40380001e1100a5944100141303140c0814802c05104600070700c0017039036404503035004001ca441e226218141c1e0b000b80c850340c001101030000b004050800114180052005414014045022903180003140104052500c13800c0803c5d070407180a0201290750004240c520820603900751255854614040f032861199900c00b810500030754030045a036a502c038000354004c00b10030b5801c1c000b4018600c400484080883c41020103076030b00b0040c0444641c060024401480d0250b0390004824645d916003440c003020451110000500000d180c00c2c0354042ea40d00080181c05040d400c01c803030b10104038082c2d5244a803280c003000d1014041403030141688690000c42281507542c2c2501e00c40c3c28206240111700800d281100e01003402d400d0301050394241441018032541e00094800c0e05500c0004110075958450b4406640000c03a00c1480800300310100203900418080344001a510096030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 688569208 1250 688567958 688568009
    0x3012a03061410080402120303090105011d070e040e12030a021b0f03120604020408010e0d021c0c11010e1801080c0409080910020f0a05060a0c0503040807031b0c 71
    0x103400180801407440315400c03840d00c1e801e01500052025003001300072a121070001a104540c07010145500744000010000c5d80f100640000d0704840c4200802c0151000c2024414441c1d80102c941d40c0018a030f6000284503441e15800c440c001040000a54440b102810366425003544102c50320814a83c00060500c0705005e180e450008462954006e01105100300100315103074400c003401e058034140c0000105040d0760b0340f03074100da008006440080182216400328240c64002e01e88109016000d60240003007619180302d51081015803642d40c25103001640d543d04e08520903240b840c2410420080c00c0140300c1c1c0c5642050040720720510981c28825850200c0725441d004403002002d01030741c2060312810009640700e0581d00d10391811506501002180340c012450056040004100382c811500448140b007004100580103058003c0c050041004250040d9090710081e1001030075044204040004a4452001c603803540a030140e002103241d0b0700341c4480f940d48600760407440940c40196003030102c0d450003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 688570458 1250 688569208 688569221
    0x10539010b0f0a03030203040b0d060b03040623090d050d0e0d0c290402043602040b04090c031502040f170c04141b040b0a020c1801080d0e03012a03 65
    0x1200d001e40c03811304581e8020348901580c0b2034071040343c0011804002502c55900017401604500c1017650b22071620707051450180a040c3c070041000700500c1151039030296541c015610130003250703004203100100e640040b00e10b503214030f5102c00855943c02a60740c2003a0305200c8800000348941d184044612281000c0c0350004c841e0b817403008852074100d1040e80007040702ca000c503881030701200c000503290840003448043c25410441c04c401c0810403030701760001c83d40f100f52a06829009850400c0340e45036030010b020807a1400480540f0940c08120b007000000c800700640b01d1401941000503041982e1191800c9036038131a07400201c10b08684101c4010001c0040007030b5201d41404582c1401100c070607410f01c0306841405072a16003500d40c44121095111001070445000b0f1090100403659038000c00c1340252100410203495100d205000068014042141b031454181c499540151181d100000d03802d840c88040341e2141500740d501d13044082800400340f600001e10a03401c0c803007150610a881002805c9441 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 688571708 1250 688570458 688570489
    0x10206070305091b1206070906030b030a0803010504020c0712030c021e1e010c0507090204050f0a0303020309010c0609021003052a070b060414041505010b09010539010b 74
    0x3030b000030401e000e50b0010b034050131130300507041c04d841414100f400310b101d50102c905106898810001400070150744002184126540c91307808100203000b4900701030b10747c44140f8010306048001c0c0010320180c9415401050f83c1d908000841d00e05a959607802028440c10100560209011780304804c150709005115a1410342d001014100305803149000502e030200c07802440040051440344e0911a90151a4171501d0580010480d0003440e43e8070b0b440b5010f54841e009140c01282c280c0e07441c03441070421700781942c1580d501d81c0155061071400801110805a5140b05664090703c2c2e03016803006d600c0350030039100301414650700840d062402442a8102c1214030341444c480e1507143c0c030b4504482201400740e80c4025801a00c56500e500c4000008000d040e010300c80034030032103208040c40104090030703546007410021710b131090055a99a0503e8030940c002d00003581c3c003080c8104800e5042941217030549011140000a0803500c8421248040303181d482d1280a1030642e54507440700016286c038543c06e080250303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 688572958 1250 688571708 688571711
    0x15020d1404030209070f030f151802030c12060406030c1701060608060a030312020904110403060510050a05061c0c0201020909010509010f0621020f0919140f030f0d020c0102060703 79
    0x40ca143c2c0454030070351005084208200c1c9201c2d05540310391194100900303400c1c12290511088007850b44c403d83d0303814107100700150786011500c507240e5042e150003501e10400400303003054200b00e0403c0015600f02c1e402000650700590312400070000507039116420010300b02c0c20700c140311a6074280140304e003114003580140082c0810881008404c1d541d503105030f17007070f04c1e40751420082c5041c000360034001a020b01c012982d807081c00d003241101c00c00e0401c0007902c2107c0c014401070080f07450b140303050003044426000311038205184c44401d0204c0e0410600a201c87c2841116113500e40030b40c884040112620301d109040140d4000030b420301c05250007203032540034003000c0b87c0030415545450484c00c1c581003d1f01c41d03402442400282c0b4082e5044000d18000310400313900040d56541307407484120703490b54071603407400784148410840780030170115039410b2005603a40c1c0152040300c8001c0c0341c204a00d984c4640b100c42c1d450f11624113081c01078002400110742c4440c058009144c0120300b01c00280c1040d20091521b800c26 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 688574208 1250 688572958 688572967
    0x9090415020f2a0d0507020307080607020f0d08010f14011e050c150f07110a05060705120723030c04030c030812070503090601032003061e01080a0f060b0a15020d14 72
    0x10100840d000d003101c1c016040151b0b0b038a11034404642048901d0344142c02600400081017060b03900490b450f03140074a0794081c0c1d603050340301e2081924200f900380a91001380121200921550226410300594800d05040c101a02c3c450403962450560f2444640b000103140401c0305410101c00f0041320082041e102503008031460f1030701c10380d9203c0000070000010072810081002e0702c0402801140401c0350001d0654585183c403641c050702c0c0703900c42c110000065100c600040d2000e0f128607207018841111642c90b940e042040c005040c215040648611900c0c041080008002a09481c0303500040d4032a4042d607072241c81210011981180051049007804010410002c14650101d43c19064a174000e026020103c1a1145598104800c00b200e64040c41032009101c0301c0e50301c4008071407a0340b6140d40c608159a0701c030180c00303440701c0070242c00800c803070202c0c06490000707506a00b00c914944406403c5004080e683c000300b4000d810040d600e6809030b084526212203070b941c0030a101e000d00c03160b2080350b40741 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 688575458 1250 688574208 688574287
    0x2030a0b0a0b0f1608040f091b09210c0f14030609010903083c0417040f060509060f161a06220f15050916020309090415020f 55
    0x81c4580050f0111301034524549204000a48040e50b0107000c0f00701c0c800340840e80b40c000d4140201070110401c041000c40c0300d42d9402c00c9120310300f00c1043d03034025040b6101403060198070389044000c10300100c45036004440b005c5000d0344245000001045480e80c030780e0443c1c040c00141410000702400012059060a191101098001e05140d42080ca10000450b54444c0c00990508030780341203900b000c0f1005040302c818415118032907554007a03805109070300b030110700404103002107200f1403040d101008010601044450b00880c041c180c0303442c000d0503da14000d0a4130610b90380741d1188031000c0e0814031000002080c4000756010644107205007280d82054201200000c1c0c084942c40c0f00004600a0003c507000314400c240c201d4040742c0b25076003060002d80302030300700402d619403140901809006070a0000d590140380c41c400c1900d0150503009140342017190410322003020001081074802000305030140300c148100384001c1000c130416000e0182c60784400070030110034003202c2c00e900703042002c0c01032500325 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 688576708 1250 688575458 688575487
    0x160801110405150705121903090519050705030618071502030d0b19030506090d050711100c1205091507020f01030b0f0307030501020a2a02010e010c0602030a0b0a0b 72
    0x15107000300c80203400000a10300d200b04a11402c2c80042403406500e00e030002443c020350180452440d0000089050307e840e040032002c442c40090013601c60340c0035070702c52111210410701c141d030350034001c0d070030f6420458a92021070b240c2801610b01e400c20f0840e64968003c6e0a10034045038014107441400204020490740c002552030066113040301c141982c0790071024141da0380c400300308003541d40504460380300b41c1e41e41095174540c0c20071a01c0c06003c1c0a510f02c5c100c0c0b600d1041d003c640c1c1160307200205412013210201072006990705505c090b000c0c0000450b800010408c8000e01003603681196035000d81e0b540080301485a100249074090166603001d00c801801666081300c0034110b21004c0c81e00081540445d030000380c011541402c2d09800d405502004818420103400405d2445c44030340300c05000824a42a030010725000c081d1148500351011200c03401036100b10b5520210010515041903000c8407512003500f00d0b4002d46007500d600395140c8007040075061400000b4010812078007a2801c201400d0310944 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 688577958 1250 688576708 688576717
    0xc0a110109060827010c020d02010609150312170c0306030c01110a12050d020403060b030c0901050307060302030411040515030c030105010602030d020f130f1403010c0e12070806070216080111 84
    0x245070b03500d4130801d500a08018050444100781000c000c0c451003248180c06900c0e9038090214100650a0030804110300070a40207511f44000700000c02003c1c0751441e00c500e10410409000e0004010340070080890741400c1c884c1e0f950182c1d04007020260b8a08010007091b20304000600038605101c01d1070004941910007282d44a4030641001450b01c245203002011611885802080e04d4220b101280c04014066258030a00d0a80002c0e400c03540e21104420400031101d6091144507415409a4070610803d403294001d150400e125840c54260481e0b41c10009050300d2044404c5900080450b402d4805403908120b805503495054008200550400c1c0c4025200d21842a41d036010f160001803904a407410f0f039044031680811080c504810a072a00079407180041a4031030b000803640580c40c03110b100e2a0600c0350034119012916100e21814141c401d11110380302c45888061603001d0b040d0300007000d140078488244070341210380c00790401020743d1420421045d080e0300b001020360301d0800009004105c0c00d007185c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 688579208 1250 688577958 688577971
    0x1a091c03020304050c12070906050301090f020d030504030f08030a0b011409150c15010510050c2806091103010c0203040f0b0309100c03092102060c0309030702060c0a1101090608 78
    0x142c1d407a41c0e04d0030414030306000414441d8000c07544642c48501c080c008076401741910502c10307040c0031056540d4100350030707110321100241c0414420113051005107468001888100d1181c00c006081c641c0d6130312031004443e211942034851001c00010004000024451480038800134207000f503400b549541a4042400350414550240f1a1074400202d40e41c100d500ba104a160308004960f1164406c05901c18449802c1c40380714000c04460340c0e0b0381c908a01a01c1036418580442c0d000b098098002c4071200300380308070f645240e502c2d4480164148040ba455029a031b031210301842880609102d040700745030071648035800c0c1070110340040c4802d004a10141c000c80302100d0b0318619542e00c80d21424000da040403c800f07214a045032910108482171a01504840c0c0600d0040000c00784004c8040143c2440c002d451811000580021000417420503044000d540c1001211040320305016555000c610142d02c10301c08019640c0c0181950010480b0034038806001450030b01e0b000141c42e15000b800b03401020003074000f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 688580458 1250 688579208 688579211
    0x111c09180f0c0c0c0b130302060d06092a080c160b1504090f020603091501090603030801090606050307140c03160b060609030a0b060102100c080711010b0604181103041a091c03 77
    0x542581d180031506c40d00165400800c1c85603030344848a90400200050300c5203584107400c1054280059504111710703004040c3c24245580e0018102c4811118003030000c0420b80e600c8024010804140c480d107600404042c80741000c507405091500030000b800c155503044d2031045060680e280000340700950380c1041300f941a80c02640b291142044a804c009026820b0145510008000110189185c0080040b81e0094881d02c69030b90700c41d100e50056507201d0141c0004203404001240c0341c00e00c5031700003011201a0f000c5850a0801c0c00365520f007542d20004202d0744140345401c40781c041c4407a5090454100d078007140c080e032900342d40c031010079100c178504400605141000da00083c609d90090180900d50a150341d4100195a40f0b01c0c80070340140c00c03d980da01c0010707803040316000b8480014030074031518070001441c2a0400d0b20384a1078902100101489807015621500000e0034904018059401a44200860303a11701040b141032a200500c000c0a103401e1f540912102c020a0003c0e8040d01901e2602d441c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 688581708 1250 688580458 688580467
    0xf03181415130317040f14011e0c0203300c0a021011010f091a010e0c1615021b030a1b05030c06010b0d0c111c09180f0c0c0c0b 56
    0x18010b4010350241d10140c62100101d00340c1800664000040040e134803203074600e10f01c20351141e12521111030349608841c00705681601411100f420003811400c020380a141c00e156074a0560f000c01d080c0980324407043c0301488098004018280030320303095622000c00c01c0c2047d09021380d0554441e43c0f200c0001c00a801901c0325240040840d100d02c0c0550b0b250004a03000384103010004d0600b0340103200c060030a8400201003c540e0b12a41d03d882c8000d8102c03400c00740034146d541c541010710341c0140e003c88020b403480c0f0003080c891000036212803c0405d851108641c01a00c8442d2224004c030000c0e00c401c4110b41c2d40d002004110310781a08205061494002d11a0190288040b45016880e500c140c0e100c002c03062203040c00019010b450107004280b044818034061014030030046058a658541c0194415680c110400b42c000302e4003070b95122428501907150a4180a50300e60fa01d606010355813500d030403115141c040004441c061409907000e005250301c0c01c03000c0d07501c00c0d4680184800d01030003020301c1030381e0008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 688582958 1250 688581708 688581727
    0x105030c010c0819020304150207030605010501182705011202240f0307050c03070506060f04090c03060213050d080d2307030917040b0d0617030a12090f03181415 71
    0x580700039008000341601304040050012b5520700707040c0700403251981000c0c0089425407040121101c81241000040e4805081c60400d02403034552240103e0b04400340c40b00084900700030b003d664002d0038554a40210100c950050201082034068550b40403003002444440210045080fa0b0a0809562641e1345039200c400b000c80d644c1c03143c1c6c0d1540031b407848046007000078050041103003805a0012295540c00394843c00a11050760f8000f40c001d0501c07402d8210810103e1500d40040c904c2c1070240c211503040944810020b20725004070002921000f9021407010f4103a0400e20424200d15241c5031491403110682d034208000c0761000700305804142d103508581040200314000790144402c20100140c4494031051006401e400c00954900c030300b801c0030400944140483c000444c0038028801661601c900c0c030506441e0f4a0103210282c0d6410b1369100841c2c04079901d00d10b002c1e101807207591003080701e0f100001c101c544d20003550007011044014000410321640c0307500e10031600c6051013548a40b10713034103035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 688584208 1250 688582958 688582963
    0x120d0b010c0c080102030601181518150207030311060609070c0510020a0e0f18181903050a081b0415170112140a0c031103010b03150105030c010c081902 67
    0x1480140319851200c004265441c045d00a144119000c0e81c0d1030310210340c080d54650000c3e10700d1084540b20b0300c8210600c0c9c000d03481140060000c100f06000100034560380c0301030b10b8104800070081001030300441010700070954013110402c2503504200c0203040500b07041c2c00049070240c02403e0072080c02810340141d01000b4087c032100c180080018011915515010f101038040081640300c0d40c400d03200918000308601d0442d038503040d2480044206a0703142d69031888540190385590003218103205010304c1003401110500c240034141c0c03080c0d8485450703004da8071000e0f0240b140540491246038030040c00540100c0e009003500c045a00c0d400440789420782c1c040c000d441e00402007542c40c180b80824800410070200108540511a2040380800000c030010954961036040324080200045402c000400120341641c6404544206c024000a14501d011001a1400302c2c07104107607004850600041100d13280c24031101c503581d0800c0c2415080000c4607950300007540b027400301d81c03405605202c544080540c801c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 688585458 1250 688584208 688584227
    0x252a18240311180f0106030b0604030b0a060515270105071a071e0203040b09010905100804060c03020a1e0c080c1f06032310140103050f120d0b01 64
    0x402590590041d01c074145015400019a03440e409000205803d0043c501c84a110030700c1060385020031080c60742000401c030040c001c1490f145520440920000c00400c100003c4140600c0410070006882490704050154440455000a244000500004540c02c0300030310390f520644c50890f45a0407140100b801600c0c00e0080c184013500010b417000408509104c0310743d50501030070301d43d241c0381d961003a501540080084070040500040c0c2061004020101d5070401800d4001c00505040715065112804a68101d4283c4d4502d0300140700d000600007800300b10700c41c644110040c1c0c64194901020204041c2009411809203507240c280303241c180b000e140c444c1200e0001a07a11260042c1c0d686d034132020060b62031003040000e07044000e880075245100442d41c840c0307004580c1d101280c41c21050752541e41201c001c04100481d0340c0d90041c1b0003503541d100f40910694115621603050b40840d941141040e071b203480e14007090140c0c1070348100c10b1080c2c401100c505aa84410702c08101084540c1070030f0040741c51002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 688586708 1250 688585458 688585511
    0xa02010c14010915050f04231014070e190509040501090503030414060907030f0602030a060f062d09030b04030e040c0e030d180b252a18 60
    0x43c1801c00c1081180d451200140c8840c03e00090003d91252010510440010780300200444101c3c0c0042e40d07400c2e4039459041141c40c800c07080e600c10141c9042c001d0252000c00c9020384845800004012a49401c0343c484a4002025610001210807419100c00c1e010b04900035944108841000201048025081480c0c41c640c8041547e8803801e00346414401070799081c5502d0040e009000c000341d901c4000141c000112034001c411a154403d258580307200a506c00f9100c1c4100685621003c105040c08054181c01828075036038241c4402c070004401c0c05095840290300303401c10f21401039141416402440402500d1308000b0307292190300c6502d000d031303207210390b071074595030024100344043c40e205170000720000341c0c2a000e500341c642c0c540210b10200d82e00e4455648060800d500014240b00319032030400a440f2420070300f00100c0154591009191a130710300d2040480c1d007040149140130b6000050901814002c4000000b88240c40c20551421081c014200350250041d17540d4940a11010801190844d08807 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 688587958 1250 688586708 688586711
    0xc0f02061207110c0d0201081e15040e0715111606030203190504030206040b0a06170102190507080a12020405121501080d02060a110f0c0705040b0d050a02010c1401 72
    0x1448035490781038410040750082c0120714145003c6000c0c120201d01c0b13003031088001300b0444288000d9401900c502d50051700c000c82c2040c144114640040a4015640c01000815080b001c01e010324002c02098076140240c1141da0782001004001111260720b680c4080070807070501c040c9503030542c2c44451401c4480c02590504000b2000300040f8250168000c6010380d0000020443d000c5800102d103003915400d4600800503848400010049071103603120b190040f407000301c00301d03890340c1d82ca03219032944150b092140780036540080e19025000315004039001248850601d00d0801200c0d8450507094098050050103102c28040703442d410505550458001e44001040300244d07040480c98540d81c0d503200720001410f00e20440003c281d0520010346410044a194000e00c078aa40303500c038940160901c242080300b5420305010030070003809041d01824400c9055801442500d16160400007030392020302c0124042c03480c65038914003103100401d41c800c1c21502030034880c00c2115076282010303a41038800103403406035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 688589208 1250 688587958 688587967
    0x1c1707060212070e1003091211070f0602010212060901050607030c050705120f010b04021e1e030718330c0606080109060501050604080c100c0203060f07021614010c0f0206 75
    0x21600b2501900c44c590342500c58030070000034041e050302110850107015200042102080489a12600a80140f04040b60513110a290342d54103018016907640c001001503500420f1183c607107000000b12540c440b42c1100c410205501d80804a0b10700d103d00807020301000401e0103a030003880302c1001000c00078139020309141c41c50054400c98a460700f8100035101c0055080580844561419000b5200e1280e48580703d00741240d40d40010344596401564a40203c0341064410042c0010520203144034a1381511001c00c1c0c0900141e0220001c00c083c1c00c80a00c80c028888101442c061080913001250710110f15584500c101d120b00752500c10b103000700201541d04040340465940819000242e481d80314034801e10459032100b0400541d80950f0040a04560001b0480d088138030b040c0b0742c01002c0c00058103184c0070305a03d64000c030b8100315084607005c0541c000d44040c40105c0c0e81c1009500e4941515100c0c824460b070a2070315101e4a10718424000d410030420041c184140300c410a03031072410a41c01051507a84 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 688590458 1250 688589208 688589221
    0x32701091e02040c0806150714010906090c0b0715020703030b0d050106080d02071202042003040f0b0f060906211e12160b04110409111c1707060212 65
    0x31411403000807800380d07050180035400fa0b40078017607050040d4001000c041032104a443da1903406d401c01b15050342e00c1401111080d444003001e10408104500841011a001002c0e04000071600040c2d4000d041c514070800035200440c02007114000001440d00b03025950b020030303040c110050300005440544c030029140b804802c2001c1580400300700c541c01c4050710034080c010701059840312070912034a0190b43c00c9485500040c03400da1300c0004030034080042c03940d0910050810000580044808071502100da1160030b003401409404113500c00b40790394030b1910500d485400701d0784c0d950014003098010031040d01d856501042d0b101407050300e101594119a01400c40f444d55480d4030b0701080c2c16601c02c0c041c056030491041e86003012620a1059881c5004c4000796035641c02e181007000030000e842d94611070785500c0d419980c0740120103085005103608000b954031181000040002001d041a0400c00031141600140000c981100b00c00d2403031819580360320719030900e00c010b4402c4110f040d540e030130034504110300c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 688591708 1250 688590458 688590503
    0x506120118030f03060e010e1e0403180906120f03261e09070b0f040513020309010605010816030e0c091608010f1410020c04020c0c041103270109 64
    0x2a01c0d40a980c4507064903012080542c1200c5282c001c2409503000c500040c4139200d020407105401c140c100800a88030100c1c802c40d10461003081d84c0440029001400c2242c0c0303001103449040103000c0ca80004c01001c0d1905509070403c2030800001403800410280c0e134401d050040061440040d00030043c0b00500320f00750039a9407d02400c42d508281e02003060210a51489192403552080502e00002e01483d030404c101c034817003504158840011031904010200b1940c903540c80f42601c1c012403100268690070041e440b5801d54030b040c0c11480c104250326080001e076158402c100305102510341000901e650085848508040d640c0240d542c020056201380120010700120758040d10510341e4518690781d03228102e07a40d0260701342c4690303582d4107140720f09190246828000000584a070f0b004980c000886032000c1400da8002691807800c2d0740103116048910f05143c003400f4001c042c511482e51440c5000f40d0049520030358106d0f00000b443c90328804152588003540940000c030340002d410003000150501418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 688592958 1250 688591708 688591751
    0xc0503070f0f2a0b0c0a0503040212071508010806091c180f0305070e15010e150705060f0603010606030905030301120311100c0f0203070b0c0309150a0e07050307030f0605061201 78
    0x585030400200011811817510742a90304100c140d9465a00d513071126002c11000c1d050805112650b40290280000c03803154030003c00c8516409511007480341c7d0f1604010038100072000f480c44c2a0b80c0c202c00007440c050b00100c0c044800072880c80c206601c40104440c680a20111903400203600c0114042000c81400f80000b048800c0700c0016001c0d2240c0e075124442100c4a5040d10202c0f40407401400e242c03459440e017041340c0000c104144000c1d81c1010302c0c41c0c50b214984031050b42c00c0d0310302c2080c020920400307003400e0098a0140c54641003d01ca0102c00d6030b585d5903644414030560352030400c034002c240304151181e203100e90141500402c4543d030151500c01c0b100100b98115007000410305100340a07403458008400d440300b80d07070084d00d4100c4507540c200c5c07000090f074401000d5200e41d004d004130391004155440d00c164010460500009103021400611501e0160250040f902c20380c0200020000101078a00341102154400c0c0040740980f9240041450910f030703290050b906500302100414490815074039078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 688594208 1250 688592958 688592963
    0x11130314010506150316031e0e0d020c031005070306080d0906080a050105060910031b0206040210080108061315091a0604150302040b0a08120a030c0503070f0f2a 71
    0x20040b40d1211003c010030940b1411251103000e80900002d00c030084031410105281c0036a0501240000b0019040c2d0003844810b182003003000c1d0b8650600813510010020301c41c90300c03820700007403441d070501e200025a54001d8048001445440e4000a03944a01c40d0300310b44001d181307002c200c0300360950084e0041c10900e0140120400600f030b8100081085a0724001c2030304a5074050403c030300d003007030400c00c1c090703481821402c01d07080c15128262105100c92854a4a1400d0841c0d07015082034149403040103204e01c2e00c80d100ea006c20071064014004c0300004100036401464104a120b402c001e58500303a1320302074041840c03030107580c6809103c40a000d0082c031b2100c02104101d1007840680d580c0802c00c000c440c07490480c24032030085080d003031005060075400640800c1c0000c0508080c20740e180c051600c0c1c48203c9000c0031103a000855824081c036014050051480c11070308080c1e046241c212802809611550103480820403a040b90014103802150b44000f000d442c00d5800300d4018440100c20356003c82460304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 688595458 1250 688594208 688594211
    0x318040b060c0a0b07030207170d0b1e2e08040309050901060806130621021c05070e0702062401050705060f011404050c041e1d060f0d050706031113031401 68
    0x8445d1031003807017140c0a4031350064810503105019145240b00b42c1244a9026401b6569100e1400540c2d13503000c0050910320f4441d03c1c9888201c0380050043e2000070790701084041207000e040c40c0c2d681c240c1000d5641c040140e46004807003a81c039410112100360490380240e4025005400102c0c1d030550202c45c0d42d2103110140c0c0c0484903104100d10b600200e0340644a845644003850648a0311f4035450182c2c0720419000503d0b040610b600020840391481c5120021191030b40205020002640550b1000741d002d4114000303004580346c40e0580c80300a045151180c1404403607407440c00040c0c0e0140040d0388401da0003c04840e03041c940301c0c220503000b14007030040140300d8000310b0b2420320300c0c981800b0b4603100f03005074010b00d400c080c034083c419280c81c907840c1e40c100c04101c0110b40c00305041130b8a40f400f00840420b0320401c00c0c1802c0c03100501080041e800003c50244400f00d05100c0482c000040300c0e4100c2c0c4644c5000140030b04202580196400b58012414003044941e100000703102c0c0b6591108000800e1000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 688596708 1250 688595458 688595461
    0x7020109080a1a1f0905041b080303040b270a050606220c050c060924010b03070e01050c010606080619300f0303020d06170318040b060c0a0b 62
    0x4469680754140b96005018074074140091051100707074445590440c0c00301c00c03c00701250422100001c04410f5400c085d2000340c1d00c204100600020094551401c1281e4038070344401400c1121040d00c901c0000d1010302040000000f0504031510000c0320204541c482c00804080c0a10102440d02c0d45981c100a546600c01c96001c10103526054207503480340f940307800d91255070307001c008030f0240a001c20344a40018400c0500c6400c021600c24000f15100f0755804018205403d6102e1400202034020016000300f04400700050100340000c0c401c8036000029410140f1680880000403201741c80380e0b4800d6102c035400c1c00c40020b103a80c2c100e02c2c0140540c004448007681464400034080c0010b80510403024442c2111240114004800b024919422992030360003115a8080c0c40c1c41c000a0035604044000070b90002c0c080c0c1c0b20380c400f0b1040710041c106501d080d50750200b0b03200d80c2e02c0d034a004e8080a41b80da002690010803040e529644038405000d40a4107164031681010489030301c40450030381c107940e4a241ca40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 688597958 1250 688596708 688596719
    0x515010f030b0307060c020d0203010c02030d150608010311040608030406020c010219020a03080a0c060606050307120b01120f022703072103030203071106150f153c07020109 76
    0x208024160050014000384c1d241c071000301d034808182d04050340c001803441c40b00c0c0c001d41c6081c040c403c6954000d03001199a070781d0301440e0000316074a4551403410905103910611100380e2000d0709504698204030343d80d003001c0f15000000d0060401e41d02040881c0700008001480780d030085401210324000342c080d221500501d600e400004090084001d5000d150024240300184404004d010000c282e441c01080904042c2c0d01c1c0d0f4110f130015007007c1d001c1030000c803c104416038040701a03140b9800c01c031000d102502c3e0800c0007a054115084622004c2500c84188041100b0158166103603041540c02d00c40d101200c40e001c0d400603403840c0d401c2c50300902540d400030610807003206149059503019003401d407070f01e921503d00320000d41000d0004002c01c01041d103802e00d40941088050300600c2c6500070803001035407520400c141114040400c50245e01e0740344600110703502400565951281c3c03160000eaa0b503034803102000c1244a00c55030076072090000c21200c441103102001401849200f85ca0700301040e500e60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 688599208 1250 688597958 688597961
    0x90506010f0c11220509011d1f05060f060708040603060503060108030301061b0f0b01090509121e0906211012030f031d0a1208061e0f040515010f03 65
    0x1180181443c0d0284282c039000c0e050411350101020035420380445072561030346207030059070000d54140d42070360744510207141e00c51500170807200c00c25000c00007049041c85840d070300300c4407c1c0c0c1c005d100106a40c0d10b0f8000751150304d46211102110200034200c6a50b00e4036890502011b4000c1d01074040060316201c1c003c02d007400c0000ea80c50684150a0045056a10b0900704903440c9204a1b8241c484040705101e4030005041b0039162002548601540151581040c5003542140e0700181448003540c044120701400190003400c50740d0307940302104421f030a140005003906162149144558009600040c200d641410500491044021a843c00795840d22003003058905d45046e405204401c4504080000000740201d1960100740001d090125800080d0010002d03000021602500a608448407186c01c120307448120040d08009820498498105103010802c0f0140740700d1036a101d0007900c0000010307503841111010410200038001e110030f00e0040d5044001180c24400980460784d94141410414082d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 688600458 1250 688599208 688599227
    0x61701081501091e0603120e0a060e0f0a260d03020406050d020d0906360302210f1315140d1802120a1707150203090313090506010f 58
    0x90300c0c401c1d081c0d9003401032810003010b02c002598000c0c00c1c0d1800d251010b01c0306000d14802140502580d0845003000840038003002064002c1c80e110307080061707081c011240c005500325541e6000381c0d000c9011801e96000704005100c0f0350849c9072018a400c605071484105510f00421000c040740903641c41d0030305800180c041c0e005a004a00118000b400481c08607541a8080c01120b03034040c8000c00c890380a502c0c0d407c1100c40c2c1b001c07500820044007800c0fa04540f0741c11200026844041c03840d0a1a56442c1c80c02915000d0356080d00010000001c0000b0000241c0c90940351030240c8642580c2d900d040388038112842c00741912a09408035025003005958074050110340c0901409000214504240d0661407c010301c3c510303031034103e20340c51400c0120240e114489807954841c203170340051002001c20305148000d1501e4142c0b0003d0000104040000031300d05551895084510710300168603502c0300c00701c8a00318051148060040e000d0b4400024602281d81c2003107008142c284c894502c0035000490440301d0051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 688601708 1250 688600458 688600483
    0xb03100f230903030f07031b05040518040203030919031415070f02070603020d0204230406050306070203071e05031303030905030d020c0607030e06070c0603060b03090c0103110c01020406170108 85
    0x400c1c000070300902d80144010303602c014a0300e40015680400300c2509008014008d1b00c400282c00420240150304013040039010100800c0149140c40c40d0650000380d0760300c02c55015074002c0010944016182800c3d10501019540c40303000a8000c04416040d0360ba01c6e0b16203100021036490400c04148124000d100078030094405601801c038590901714154060340c00000c1d40039150b42e00f08000645981e106119640c8080182818144907441d0410001030340c2207a004103100e500803106000106800208803550140d004d1051441e0841d09000c1c00085aa120303800b40c440c0c0400103900212209203005101920301c603484008005841d070088c140d407071008d10a8035016a128101130b00709e83c503100340540006442072400300700d480c1a410100751700360484102150100c41c01030041c004c403038050003141c0c091301590b0101425032900d18030040e80d914000e01c0990505503621040a9044c9014007240d40790b21102d0029542c030f0f640e65100500c0040754079001e400012100d00086504030011900105410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 688602958 1250 688601708 688601713
    0x1101080609060f01090902040801020408120f1b0a20090f01060e1306050409050d030b060a0905060d06092301050901061e02072103030f060e0a0b03100f2309 69
    0x307550741d0512103d020514401d5041c09180391000074005002c1c00104080d02c800400540c83e1480c0000c1c1c80e01c1c04221200c40740303c00c0f00502568504131100c4c01a903100c03403d8200009825404c80b540d0505007100b10401034010041d088545c074800001c414040c1d03040c0402c0d2103061060351003800d00880c05c1c0083c00f50b2400581801190071039443d000e0b2a2207a42c1040d2103000410543d00d10020341207543c048401ca480790005100714103000c1c0c152144241103034051722290303d80404003000400c0e1345a9400340300d224610110300582003a06c04d5120f40c6c05404c41e1001040041c890300c80d011b1011828000081d040400400082100e080603c0194101c1e0025151098004000fa0409204650100803042140714480b8000350f80f0055100d000c4503441d141c0301040802d03080c0d060041c01c0e2007252100076000d41c1420010000c901c1c0d000821070380414100310010741710300d40e000001c1c289000c0000f68012907041040c400350a810540c0524200300b402d4441e20300c0001c0d810b42d51140351008880100064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 688604208 1250 688602958 688602961
    0xc0406200706141603020a051b0901050402071407030b10080f060f18071203030f0e0a030806041d0304090b100503220807051f06030b0a0c031509091101080609 70
    0x580c09010a0001d000001c07100f1410140d0720390442d04520304203042075005030311600c44441440b200b4054940e54900c000002c1e180d0b4001c1d040850040c01042c480e4074003da90008001c0d00b8844103000380c12075845003000361100a6030305d041c942c51030803080d40d42d5580840c000c000007403024400185030744401c03090405022540e9503c491515010030041c400c2160103034048903440310319810321000000d040b00f010a00d44070b1340039040050842c1d41c04411044503a14120a011b900000000d00707160313041d89890a000507a80c1c41001c10f0281040e15401e03c00d403001d261110101d202d011000d04181c13032081400304141c40d859020481040408405000420b1040000c15000d851906404c0c1e0040079415002d08543c00780da943c6001ca61100d181622140c10282219540083e040c400002007983c1407014040340d030868540002886018000103031855580c2d81d220f440c58080d400080000d803020001c40c501d1070740c561650f409030401d01030887d024840c811505186c5d41c0100c01c000d02552019000d030711907 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 688605458 1250 688604208 688604219
    0x20d08040f08042c010e06010e1002031e070b060a0308041e0b0a030b01030501050a050102120c010e070e040c0501080f0105060307030e010518061311060706140c04062007 75
    0x80c840344540c281c9891100300b0000c5103491141400030851520b42045400020f40e42e442d407913944006030000c1c180300480340d090002582c0e200c00400e844000c100d074001086041050140d1841c880e00d803080110950101700f005490340d224002d09569800b40c800030341c1942e1514100000030900d400020040c0800303000a004406040207200690b05104a40c61400350703c48a84000d01e4014008100c0065200c070701031003407542d150141314014081034405807061810040042e441d0899110240150b66001c10540803c607000d410150b04a003d050984180035110090441c000700116801c0c4c0c2c007008044000030700d1f5441354840900c9100d01104020050b42020100301da19840a000e44041540b590303070140454a00f0302c01c1e94064507c0380a00803211034940209410220001c021140d419001903901000c0f82040c0d9008413140d03030480310240c0c2c03182240303006030081002d0f2070a000300300d4508007000080c061500040042d200310307882c1d5654007880701c841500c5085014400340c0300c603042540101302 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 688606708 1250 688605458 688605473
    0x150108180d11010603020301050f2512020901020715081f0803160201030f05090d0e0904020f040510030f0c050a08010b1008150d05030d0b01080f06010c14031204020a06020d0804 78
    0x34801d50b4400400d0a81d0b1341d400013825204240d0f982807107121900c06100054150242084120f0a581e241426072044807a001c3c003000150b000300082c03150005140c1c0403036842405048003031b000c0c50030016401c0b40d030f1050040185c0402c43e10101010700c0d054203a1070401d0b02803c05001c855811004614111152640e0040d80c056000100d051644a540b0b80b104030205000f218810510742c0c004011840411100403d452030542d101406590100300b8440547c54240091290210030f0b3f501007201c1d01c03414806007000a06a1002c3c1665449013201010048c0c480b031035808840c000c6588190a50710b6a490500321400d0485071a80036068000c82c41d0143e02402c030090307124070403420b148401c81c4c242011030607080441d80c040b9195000055050356a0780030707126024443da02071801200911b8105c5040c6c01c6041c001d0605070511141c80e108000708a6a0a006034a42c07280790181c0e0307198005680d2164400c031007510124421602d014001c68003510020f00d6450110b5aa030352104561142c2d00e0b00b48 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 688607958 1250 688606708 688606727
    0xf0705011410052e121a0a06170105061605120702032b08060402090a0807050907110d1425030f0305150105090a05060301060216080c010e0f18150108180d 68
    0x13014065002109070200056200b21074040c1100e005440f8403868413020084400e405800007424050702001c24140404100c4c1c2040c152241950125a100400804080b030303500c601030000c200344154103500c0740c0d0b00440c1000c1c107200b13032007581280c00300d43d103024503c00010313483c0784440510f0030300400000c01d040c465000c0d10b4003e54094001850003980c1c401003070b25603800d03811414181e4411b100c00c2009003880111554084898a80780c94810075014101e40c03500b8950b10340b40200048005922110001e140c1201d4000742c0c800040c4080c03481c070700e41c2200c408100030815000b01d44240e084007903c601a000e00d6205178101030300801c90241c5c41d4015100313030b08044600d503080000c550000c030341da03121305005502a0140c0c3d002030807981c6200605203030040a80d00b09400da030300040c8a01301183d822400d0401002806c4951801078184500415079140b02c850a6100145014083c0020301240740c0002104407801e07070381c86039a0343d2008080c0102442014a485555028000200260740b1841144 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 688609208 1250 688607958 688608049
    0x190f0e06100c06110d1a060a050a0f180906091d030d091104020a020303010509010b0c0312150a14040c020c0a030b07021203160e031f020f070501141005 67
    0x1900c210381240c0c41d185401642c20041c541e551a01e0202d18110504403d186e4204125101d40c544050054003c0103801100c0790101405031000f0201d240c030740610010003d907102c01d01c40c0c901722651004402c011305810b20170400b50900c1c2c81205051204032941c1d454003110003100a518103400b00300c3c08402410920015552030500303140c10079256590340000c00581c030b0140d0085889504110800c006410706a120100c040c104211000000c0f0000c8107860040b0240c0c0a100310584e41c0e501040c80800d042005568440c191403400b15080030348500000801e0303800d58041000600011040e6615400741d43c0c2190302c010300700404c000050b15160b4156000303003d403042c3d40440c030300e40005a80c00c0e007007620501003200c8014180340c10280e01000160a0882c110000d0914800d4040c0d8143d00600060102c11030715000a160082c082505040b03408455100700200904044517030071a034600c8055500e8400000d01103000111840c000101c55032121542140c0703683c1346080608a14200611900c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 688610458 1250 688609208 688609211
    0x5030711040c0c08030c070812010e060306011d06010c0203011503050c06070807080c1501031101140f0901181505180609090a051f06050a0f020609030405060c0705190f0e06100c06 79
    0x3031200250231200681482495484841d940794108240c00d44e1510f4010722690091340801d00401800309101d89040c01c0d2000645a06402e8442000403a80044202e6002c0c2d00341d800d14102c041d900400069907000c59010346e0030b640e0004d8910041104a1103680c0c07025000b40b6042c4039046c04032394820001c01c0ea10408004844940c4110103071080d00030000d0b802074504414210422a1950f0002058a602000c2000711440c209124a0b0b2180398042c4024260421914034500c01480c0f1807110b4090160080f5101c1c0c005805040e0402010342c2e22078444400c81d645a204211064109402070341c1005400414820781036541c000008000c01e402000c902d4200003400100300e4072800c0c8040c8034003034009070b40c0c0e6982c0d9403031901024100d410b54915100c2158804810002c40000110545050311403c88000b40c2c0c408841001030b18000c1c664028980c040121641c03840c0803107040340d450040f11440c07090b02d40d00507541e07200401a000f084400a4102007454070a19116104034110360607503224440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 688611708 1250 688610458 688610467
    0x6061b0c0a0b040602060924150622150c02010c0615090e0c0d0b400318080a0f02030a0b070509030f071d2205030711040c0c08030c 58
    0x18401d64002c0d40b15281d03441000405209660b41808041c4c4e010b8001001050f2002240c80301400c881031045641540100302c80100b8440140e140d049680c101000b840c150b00c031100542c035003107607107161803032428146c0c014240010412200c142c1080e9031041611140c00b004180c1c1c00540709405440300c100c1d11759a40340c0c02d0200c4d0081002966000d0624080b00145554035104820302e0403400072079061050715503d08010004070342c0c01c800c5c2c1e402030341d6240311841c1920700c1042e03603040c1c03040302d82001271080d060090f50b01443d0a1030b00302000d03e0190355000f9290f1520030051030081c0540c015500701c1d41003994003401081c100200f03900c1091016003100d4034614070303443d00c62840c0016104034000440000d1401018a03080100202c00707140d0b10301400036a8a0030b22203e944440080038000300c184040001100c0796126103c00040c0880b0090100070004a03140c45a140da001c400116400c42941560149604061044281c00001915030201461081e21441341d0b6030402002c00085220400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 688612958 1250 688611708 688611733
    0x30702030c010615171501050901030b06120708012304090809090f010306050a180b0709051908010c0306140f030c03100e010501051014030601031803020d020c0906061b 74
    0xca0400106a03074001d1004d400108803000384404070400c407540840c40c0d80300600006101416030740314020000d0070029502c151120041c1c014141c203990b0182c0c4042d020480c07050440080284505c40d00c07031680c1e82d078196030320380391500040d1203c415100d20401485050140074105507025520103801124410300300401400020b0106c1001c0781e05010100c1c0c0000100100903007402007d400c282044001c2c46805210301800b080e4102000024040000303410101300301d03502501d00d08024103c00b0301001e690390040040a0b00300e01e1184581c00c00c82d0304e00009000e155110740300b540d065440761803c5181c071384d5072901003041d44906881e0890f4540594400801b495604005c014030750003210340d011589000c840718442c21074105034083c0b0b0181c19aa00360381e000550006c1c00010500e40d401700305440780c80e94001203004128052036481074507d0a0011418160000350b030940170320b030035801c946280202e4410b20400900c10380d84242c01400038014040300d002c03481c004180c03400314030040780d2031242d005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 688614208 1250 688612958 688612961
    0x503150604330207080322080106060815100e010c050f0303090c03010b0d030903080d061a030a0c030605060f0d0b030d030b100302040501080a020304020d05010f060603140906010902030702030c01 86
    0x20301d414107014442d0204032242c03892604844000c2e0200740007520882e0310303100560b07032a8813400c007116400310300280c50300103201c140a6020f000340036108020080183c0310107014203021001e503075186800702d0340d0350008040d10b0048030099042c5002c0c2d554141030941540159208254043e00b01c92034010407198048080081020718401e00b203042c001c085a1b04440241400c441000c04007502a2036120004030110b078201a000303003120344c082d14a0b9650101090a44020015a0005800d0881e400c0d0116101e0350040f016600030b40c0da035030042280036040d04055044aa182c8a15600210180003130701e103180b071240191084c24007148000c560b0000c2d030400a418904c1945842002c00d0f51800408120300b00104002c8010400e81400c40c80c4c039041c1400030b41903500c002c05407194035800100003000c54459030220002103a102000b48041c803581c100074409040c031400f0f1040001d2800c0072000340490300414450088208401410041c4d007130008000107036100814181c00e41c07004100c81c91212070309 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 688615458 1250 688614208 688614239
    0xc09031005071202132d0f03060621120201140c122404110f0310090f180f050c030f030c07051e281814070503150604 52
    0x100000920b8502034001074100c000c2c19003041e00d82c81c810302400401c10864102503066070000302048003030151550226164000030a80d5586105d044c0c03c001528442d40100e4400b42e03445100240001601c0e88601c218000ba11403040301c034400082107000210341c0d48050741140c40f0641c07002041d0300280b048015040702e029a08248014400070b0248030f40354900b40306c15006500d20148140f02401d0324240b0108500080403188200d0340d400050030b5041c40c0804980e0898458100f00703882e8030380740704ca0000042580c407482c94244d041804907650601c2d00d01c0340c003021200040900c40c020001d5101c075040c2074400e0030211914420000c86404554041110107440340e46400103690300c10b41042036505020242c1d01050160b984852903c0a180e0001e00c50961900169810407081c4045e0314060300e034225612644002c0240e18401082503901c15000d01c65108050b04140401355007005445104801241d54200185051003c14100384e2090044c030001000101031605044d00c801629400255 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 688616708 1250 688615458 688615483
    0xb0f030a0f1b0305071a1e13030b0c0d0c081303030902060d1b030609140109020c011d0a0c080a082d0a081e0c030703020d060909050f12040503150c0903 67
    0x1c855003c10000719040001b1180032103a032029404d0140d40c2294500000c5200c1c03210341e014a0100346d030020052401ca40e10003c642200b03103480c00d8201750540c0781903644201d40d8400c030f881c1424100d8a40c00c0c05055540c2c010601804295800d00f4152412001000208022603010004000c10700c400b4140f802800310083c003d503001a10100003907405421600998003080b219410004040e095a94843c00141100c1d11088003507501c406484103c0d00500103c81e10003028040d034455030103c00c00008481c030a2600c00d6030101c3c0410f0312000c2e007940d5034848100051407154204445035441c9100c0c6c1c0780c0030003001000c01c41c40e030b01c030700c400d015400d280c020951a400007071031038040144203010034001985812800c5600c1000781042c410304111484010f1044060680004000c4101f861560084004240c907960401501a43d440c1040d01c5900a04c044081031041e0700c0340b07845c2640120201d40440c0e000900a00450000c3c645420782c401006000040c0300c00e041c4501e01d610344040c0102100b105 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 688617958 1250 688616708 688616713
    0x302070c030b0a05180c060414032b180e01051012050c120f0f04060b01090f08070801110421060902130c123e0f0c010b0f030a0f1b0305 60
    0x603240046442c3c0a064030ba00c03088560007035038000047c1d250320040383d05644000e890300c1701d049000e0010a00e0114403078880b00d0382c880b80180031aa4101d1001d5003903048134a0f6a1206100804101241c2e4465902d02480e00a1602d0200400c01450b1a0b0381a03c1002424100040440406000e00301107804c11200d00b517075040e0000310b080d07450000307450b030a5000900f01c415400f90704054042418010001b000144141e549903030300000c5070700808440c401005c1100e85401600d031541c10700f5441e2400342c4a2106150b09140d4034030340071903445085d201a40c444900d54803001c018503040c0943c40c11351000c02e40b0550356542d00300004d603c0b44005c20404d0070340c218002c11072581003030005208404002c1d01e9440b0a00c4c00083d5081d0405030032075020481445e99008095901c18040300c2d280c07120255241d440c4040c0001e641000c184180080e001c075041d40ca000b08907007021301060250803100d039890b441d89600300350184400107034014140510305008494a1500d05281a0146003504c02d030b80043d950703503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 688619208 1250 688617958 688617961
    0x803030709050102010f23090c0604090e010501050d02150f090d03051305091b031b1204170406120c03150603060e060d1703090a0c03060603032c010302070c030b0a05 73
    0x3560240524500c0e07640f0082c0401c000213440541140e03421f00440320501c920100d0f8041030501c03e0030820341e044440c0c01071150b41d6032a602c41c0140003c0c44400c000309865401c100c00001c441c50440b121407241034010f40075545010070140c46001c4d0340d0205103a500d06941c1401502807540302c4000346100320b8840d40700d00da51100b10500340d601030181a03024a10602074001009040e202000d151034810500e1a00da540b43c0e01c0d00c959403184000d1460201c00c4130400810305400d100b122044c068040c2d80110310320905940c01d0485c0140074481c1e80110b01c041040c640d1240f00100196008500d000f0307542c9000107400244802c9588020100e030300c900c00080c2c403044140450140c0c480c541c1c0d00484100c44080c45030070380ba61858040080c29040f20000d60b800320000d88400c03014008214013a50150000144944902d0180e00074039072030000354000382810305610f02c0c180d81d02040b5041800304800d80c10941481500440181d408010101e031150a00e80c0c0000024415030f0629001d0703900c88001060340d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 688620458 1250 688619208 688619219
    0x2c010b030f1018021803011401031202030705031207180b0a18050f1909060305070608060405040201021e030c0601081c020d0806210a150e07050315040c0803030709 72
    0xa5940a4050885220702c42e2003004011001079464816141c51480580c07954a50300c4607144d021203650000350154240f031200c550480b00d419816040c0c80c420703801c81c0c1c500000c0749022617a900942000400360303802000745101484001078515805035861500e006a40901d0b45069004080c1d035001343c010002c00700340e4141c480d4110480074003101280725440c0348140b4140008100b01d00100d0300a005015407601c800340700303160700080e80c0640b41750902400301036640d1800d996aa003a038030400c0000703814240032548529181c06528051501640140000c4a45400308030030800300c50410810791004214a405082051000d01e00070b0034580060003092071031038080801c1c000e100648204641000f0f10a038116600583e925402903003e56815403194180d82801c007000c0c022540d0002540700d1030038484100f2044072545680c0e00c1c0c4403c020300480c103c2c21040d5568070031500841e98075402c0b080c210b06001d034028803010b501c28003440c044100590b840d0001406c542c07060303c1c1840080d0303030a0707424440b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 688621708 1250 688620458 688620481
    0x30b25020c09160207120507120f1109060915061c0b03010b100c03080c070f060b0f01031e1e05071112180f01030605041b03242c010b03 60
    0x41c00b0801c90b01020814961100007521280c01e4080c2c402c403500b082111b801840b000b0440e500c05458202c0e003031060501103080c030046042c0c03a548103c61800410000007210b0070181c0c0310390b014600280c01c0020507102c8440820354004544005038004100380014144621000c3d074200d40c07072080420018901910b40213041c2940d004000c2c06014040c0100d003491410f03441300a00e0a00340e094a0240780c02d894140801c179252140200140c40030300324241c580140500d69201260080e81180d130050a80d18003001074041da03400600b5941098005078451608038160f4100040d50701c0c0d8210604030f01e00d017100d01903003219800d40d00480004d03d1500e1501322003c040001c001d40022008100303080c4071040e90010718004000c44014042d00111003641e19590094100340e0103040010814803c501c280c01001030428803603c0d0301000a41007844144c0300f00b403070a40b440e10005840c1744181d00b8608000c2800c0d49141110008a00c40720b03405c00d9a813412401e43e15150190030211100380d03803800c20544210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 688622958 1250 688621708 688621711
    0xb0316022a1e06031909080319050603011104060f050708030f04020307140a032009010303110d050405060403231005040b070e011d06220317040e01030b25020c09 71
    0x2041c100c100544074019629101a69440100041d40303045004c0e07503454030340141007071401c001c18418008c0f090000a002c0c20179001d031035200c4c0300402c010507900c42e8205400d0351790038072003041c1c460400c105c1031280e2449150412400c2d111400c0c0145840c03c00c0d80d0308081d55000b21032035490708942d1790601c41145020f02030100201100e10040000c01c078118005019400381e8800100282810142c110340010046800704900300c00410090303da40e0340b0f06010b030040e81d540700520854000c0f2210780302200c2c000c0782a501658405008581454110b03a0b44141742f00b205a0702241807880b00c591071448a20400c2101690b2002c444041854207141c41c20a40c0003001410f00ca090203c444491092079078040781c02c0348038540c480d0440301d400c074061000c035030f040c411150154504003075141001d80d01405c01440c1c801b2a407280c51520002e0b02c401840700541d008034010103d91151107401080840e0142190f00c0e0091780c0303e07140d107503603020b040188a10244806064805600002d1544850740742401285 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 688624208 1250 688622958 688622989
    0x51f090f060b04210f1a0603070501020d1e0e060c0307020f0103052208091e100201091a061c050c010e0307080c040905010b30070b0316022a 62
    0x2c0c02c1905024040c451343c0380044100d502e036140d80c42d1400900c854002c8580d40f00b030b00300340c5124035450071a80e0740804005c111425402889007103000100303540b001540d640815015a1245505840d07601007502006404402c00c0c20800d560460f8007160b84c400c4000c10300080c42200070350786c94580c1d1050040b0b007c0000200f5051500d00130030400401c86090018954005070070031540a010145020a040d0060700801600300291200444503a4080c00070994048000c40303501c20000c0c0108801ca0036181d05202c020100e02081d0701d030500440c0e5800d24260030940c010324089292030b0440a04640a00815050320a6801701c03010200958004603a81d0f01d0420078ac0c040e244d4242005004c03982c0c0c10400500d24012940d88143c40b060003029484061410001000c064021403415154001e281807150300b0360041d6100080c3c200e107136000050820858101c0068241140d48007a00c85d10412007541c1d05006500803c64003f40d07102610421000c1c650840c03010ad078040c82040f09104580d9000547c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 688625458 1250 688624208 688624229
    0xf020c21031903180831080f0c06032e05040c0801060f0e092412010b01021207020901140102160609080d110a06020f0c01020409091a060a0504051f090f06 68
    0x34004039001c8001c403010840c64404d90741c04886c200804900c2c584501401c4101da004494000c50f2918020810110790b0340160100c03002072880c0c0040003034900c420b4905109081902d244100610740d50000010070030f41d41c403a012422030b40e44020405940326407000c00005020b1000500c455034020400800c86455460103185003d158030200d0040364003c0c00b07000081114040348086a17a00c20026600414041d1008400d0398000503d01e020b0009000c0142c0580640d401402850b003020043d40da51503001009202240d103080700c001100c0707190209441c1140680c03c9103034040c10604413110014905643c444034102c1c07600c4042030500d2030f2001e16908120300c004000902540c006500300d04550000001a03a0340e1100203a2040d13481564854600c2c0e500100d0006800c1089511040700c0320b014a020080e20100140d1a00c0114403c44030b1036807001c03040e1800e10075401e05502c044c1e8407280449100d540c2401c20300d07119a11051542c000ca0540d5110348606000a6030707802010014a800342c038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 688626708 1250 688625458 688625501
    0x21050a060c0804170a080708090c13020405090f040507090b010e061303110109060909110c0f01061a0901020a0f05162409051003020c07091d010b010f020c21031903 72
    0x104814400350a1f002006401c1010940741f80040c0424488003030020700c0c98580c0c00b0840300c0103020f5000341c480da03072103a5903210003d07150449190350103208960010141141e54204010b81008144480b0428100984814541c0042d1240703002404940e0343c7c40c841644140c51851301061204040001314100918100c040100540000d024415180c480c003001c00d0800d41d4210500b100c1c0100004a07280e48103c5403c466140419409132054809801c1a49840c20240c0a01142340c030a0316180b5005030320080e10400801c80c04400e0a04587c4180d003516801040d038862070300980b0060300305c0c1c2e01c203c80c44540d1351801c03c10740001c44c04090b803504080340c0341803521001036091303c21310441b0004d1680006944000c01d0040c050320002d060258400c2007142c1d05003540088042104036042210740c6040e035100749543c0a201120b500507007035401400049000e2040c01841e01c00300410b1044403100c2c1700306500691046c805400210003003047c031000000c0b007030001000e03030321042d00104100e00640c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 688627958 1250 688626708 688626727
    0x204050c090a0603050919140609030f0306010e0a08030a030c030e06010501170a0e0106090504140a0b010506250308040203070909050303070f022e0b01080121050a060c080417 77
    0x119040480c3c0e5103040c0011280e0b00c175a0940d05200010301c1c0e10380100058400c0744104002c2c0d62002c01d425010000301d501d5a40d501e401150390b4490050320010010081c4001040b40d0712501c04c10303401d01c1003e040b00e1240d0795031384800b27440c40d00a14020004251110f00d840341c21a494800c2d4074510581b18000c00711545401d001070400c1c03080038414203441d0f030100c000130041b0007107800208002581c2002009010b81c4c803a100c0d002082c003910220b8111031003c43c000300b01100007030701480701d50f0450034600d01c030b0346080200b0840e0340c0083e0380c43c00b401d40011101441d41c00700209580c549402611001881d15140c81090704000c01c9410003640c052420900102140c00001541d40c041054184000a190980801d03440d010700d54452407211a20f900c0001c1d00c1416a600111011548110520000085800540389010300740248c40c1e50350201e004040b450002090b0828545000f4000e4602c0fa118989a032030076580000c002d4408036403000309110030013007c0c00c100c0c04108e49520186081c06501d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 688629208 1250 688627958 688627969
    0x81e04050d0b0402011403040b041a100603180501061206060b1c020f04210506090d05030a020906090a0f03020a090606050706151707030b060a030302031c02090d08070204050c09 78
    0x360701c041d01455580000500316401210400d24600343c400030380d40c0386d107824a00a03c100d40212402c0b544280f8500789940190003201c100c0740194900c800c6d8000300750608500b00c0090803000150034010090906a80100e0020311511014144a2005440d140042d007030800c1662104da20803130740d1a0040296a0411000e480c4041e401071205501590f2408a9601074815000b503803c418079031501d444554503039010502550450070f20800c01d4a00d29510340000988400071214214046070b010400204180300b00d500030048410024401070900c0465400300e80705842c2500125995050f0031418002d502e4916450b800504154034188001410144000c1a500400d03200504a503103030034002c0100d018000403031000c2c100080340c0c0842003000c00301043d651041840140d45007083c1c10042042410072002100903a80c15400030b501c1c02403502c284041490150100c040710a030b0a00c80c0f001076076510142813510301d01401c030740354030341d0b0f07190042004860010b01213000c22001000101d10750740340c0703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 688630458 1250 688629208 688629229
    0xf0509030a0f050a0e0405070c0b070207060c14011119110604020a1205101a0f0306060109030b041a04060b3c120328020d09141903081e0405 62
    0x20391800310b89404c43c42c00261035100c026541c3c17a038003d003080d041003119a4800c1041c11303101e0085401074141c2d294060140c1e15000c250140900054400d40d4180c045a2203042151180300054000200300b140d01c018031400b50018004407081c490303c580c01050b2140c0c001c5500c8094008440600045c0c20503070300080e00d801041c0702c0e240150154030707480020700038240120a1a01054642405042c01c2100c0c18a1903254401c206440381c03500104101d110304001584c644600340c181c503400f40d183e056071a42c800341a4014402c5a030201c0609600c00d094101304141401580b0811021484003007070000c00030340021203504150002407000300c101041e40c26001e0740500460103c0e0842c2110003c81c0455100d0b20250a8540b25200003d0b00b0151803034900c100d194141907140b074081c0007198101c13003280c0b100d103c040907500140c08410184103003001c20b200613008107401820158140200351921303e50075000d60058410500124240d8219100c4041e00f415400c582c1821a245c18100710000721a0040e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 688631708 1250 688630458 688630487
    0xc0e0108070806070c020607050a0606260613050f070b0405040e011406130b090103210203030c0306040c033b07081002030a27020a1505070314040906090f0509030a 72
    0x103170141c0f80b10654850030122403900f034000058030044200c1d42000009442940320740350311815006102c15085041c10b94101000d1031900c050321858690581c1098040d03e00407060740c2c28040c6001102020108202c40380080005100680d10f4603c0c1004000484203107100e403c07002e03410481ca000c03908081c120a0780d4003842c129807510341c00c0c0c10202500c0041610b080c016400044aa0001c0b0502c00b10724107954140d03031290380301900350f070381c0c010200d0700c03800152003d20f1000801d0002c202d0074a03080e0410b40448480d4503001840a60040e065000c44082e49900b0155101c8810b40901d507469540c04244a500301000529403a403600041e50382c0d80241c2b49a041c40b040d40440481c011100d2500142110304c0321640300e1301746402124006000c0b003410a0228070506075210b00090214070f0400401c02d0307200c907440d01402c00b0a10384003514086290440180744640c10400403031002841e205000182905c0c030b800050844614542008a44018101030307501c0e070040c8035050309554006020341714440e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 688632958 1250 688631708 688631717
    0x603021c051204080c0a0b0c1209061201090b030705030d050442031503030503010905060135090f031b010605150a02101506050a1403040c0e010807080607 68
    0x500c28202a03090040b81c00711202000720009000544c4400090306000b0808111420000c1c0e955a40701c4c3d40c410320071183c2214070b0703812001c4840c5002c000f00340904940c442c05880c0364035143c075082113104220400d030401e0482d1540c4c0d0042100c03d090070001c2002410041c0e0080c0700c2d0410040700070f0628011803140b4154481c00892800c50f00700c42c1050080c51074502c0100c10b81c054100191400000a11100a4002031510802c10408000782c01c4840c103c035016110300f0302d1a400d2124030300140c0002010541406814180030080c0e540c4800380e1400540070386400b84049460300e50b15013003440c001e40000d070294000841001d60443c040300704c42e6010301500391122802c0c4c1e12103082e40076282c40e5006ca6808a041c1921b41103e0500070028040d6408950035100c2412002c6100c40803074030000003004002c0903510041c0310150045000704050711007420145003041601d900b0007100c1d401243c0488010070848010008c3c2c8401c50303001809032000401030b04482c0d04140c140b958a4000510070130400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 688634208 1250 688632958 688633009
    0x6090405030319181a10120609051510080106050102060c181206041b05010c0c0e06030a0f051005010b270d02130c0905120604061109090a140a060302 66
    0xd207001da12003901ca284000b01c0e0b008180d52814902d001e502490800c2c0310100302e81000486c12100e40fa081c1d41a07503803a050440c180740e89134841c20700400001c0c0e8110745a119041480d8540c4082c003491074451b4504c0c5154035002c0e030030300e403c0c0c0e82990010b61204d41503510840030320040f0241002611440c60381055800603c2c0c0100002070b4042018404141d058082e00040c00180b0811528000c9a045404c1402404641d60401128400782d40d08000e010001d00c0303202841904070099443d90820401800c80c0c4d95600261101c445003614008100e480b90300c020811140c00186009860040c04040a01420305800300d103000700c2d10f01841021061100d140b03000c13004550351042d4940304650090b01c030b1407400c83e00d260035200422a000c00c0302d001c252800c03400185858a00084c50351000c2050241c90640c50342d83ea058003810511f581044450320512048103641c4407603101e50301c90320307022801081c0400d8001000010050140100c100d00d0f09200d02480542c480d0700c0c0082071141c80080d2a40c11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 688635458 1250 688634208 688634251
    0x5060a05091e010c08010e13060f0b060c011b1701090b03100e370803090709230a060f1401030905030a1808011a011206030c03031205060904050303 65
    0x705900795129680d4106041039802d000401580711504103150b9403284202a40c84140c042c520071002c40c1d0b41c0806580c289001d400140c03c0760018030709054500c0d0042410f03034600c0005074090b00080c1c90644203a5552090b900284000c0b04011400301c0c090800e01d21358044062800085041402000141c6455201041040d02c2c1000300300b002c5000c848042002400d04099640c4504100000340d000d04032100d10340f070b56241240d12031081c17000301c2d4043c05c001c025030b0354a1300b50301d4000410444c128014a000003403a80a01c0c0101b020040c1801c100e04071a851650307083e91002c4003c1d007160a0503190a4090110940d01da070003030290f45a40c00c12108000010004801a003c2c9202c002d1642c00082044800b458001c119070f60112407123248504041d40341e0740c9032802c1780c0080041259822000341c2100c0c155004003620507d20321a100013240741510703070716400041c103980c0d402140007032a4680d4480020901e4031a940d00302000f103400210500300381c2ca825580707010190410310100f080c0c14400c0130 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 688636708 1250 688635458 688635463
    0xf2d2c0907060c080408030706020705010c080c0a032307022503050d030f0b1e0103060b0f0904052a090108090d0804200432040b13020a090e0a1205040305060a0509 72
    0x1b01030f40c4044a44d110840c2c5854406900810005c0b0307801e60820840c81032641c0506c5003680b06e01a1410514202074945908030060302d0910361112010a110344004c0035011a100440c4c810351040d00140b900500444410005460304003040c81c0f040c1c00f2000900001d00f01140100c4540e0301031901050f07500c41084041e000b80300382403241354821201d48c4401b41c01d05140a80001c440400d0b01d0402105586416090880c46580030401000000308101074180c5040e41c0f20940101d6404440c095980d0140d12020b40494941e41003840414040780c10502581c1c82503503168012204c1c00504844c8001ca40084d01c0100007810060800114202c14042030f11001515080034400038000c0c40110042e0310343c030b0460b3340a99807102c0c03000c0c5d4440c25040071244018040307010f664055002040c41e43e5022010000141c501030480e03100001420020304c10f0a213000381107224145c400075003101030f401e00d082c0708040310110301c050034441d0900082000c81c0002c40c4555100c0414000450503641d801003c50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 688637958 1250 688636708 688636717
    0x12020a0e0402030907030203010e010b1302070302120c1501060c050615150a17010b03090613231605010305160302090a030b0c0a14040f2d2c0907060c08 67
    0x940182c8040104a4113a0000450500700d0340268020030018000042541c00e0f42c071440318254003c150003042c0c291386a165401018003501910603038404840d42c1c011400c640d0b201c6044441c05070300901d104030491200080d514018a01414191683c1620b40c0d07440da03e0b00001465400c1000d407a0001d185c0c1911800350840304110701c9102c00f03a4800200384050032890415003082d2400c14482c00214a8102c0c440403039000d00f50383c0000b000150b03076102c84072211000d140000c5811302d041e0044041d440c0e01040c010b95404414001a0002010858010001d844075900050402d81840140089401e800000e40800c05440c500561740b00030b00c01c0801d10f80c1d916a031000702100788000401100c0030703110000c1c1000320501e80d110324003c42c40580012a0380600e010f1a030301c0c3e00040c141080583c0e19024408003a22800c103a001c10140001030340008a00d84c4d6108201044158103203000e405a40c81d01c0440302680400d40790b2031401c0a80e00b8030f540341603900900342440030400004090144940544 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 688639208 1250 688637958 688637987
    0x3060e06090901240e0a020702060906030703060f0b03071b1e030207170609060106050c07050105071b03081b06390d0c0e01020609061f1205010e16030312020a 70
    0x4c800c0d00c0803164000c052540c1522905511900d24004034179154501c1c000c0750800c3d9001000b00741480c03205010025180c0c00503140005040e92200300060f00c01c12026801d00420700c4409d295140d103440c640241c2a520540214058020441310f1040040c1d82c105a1121f81c442c2d507441400b02003101e01c1d00360703c0d003203039900070303564408841d480708408240c0020400c0c440e04030303a41560116680c60b03070f064496000c0c0081d50010358000c4c8405101652003907002d030200360301500044580c18581d403c0400f44204e19081034908140004201420302505c400d01030514502500901c030a15141c80f0300c0d2591340c1281034452084c031210f541c51000310660154010718002d0450440e58070743d0140702e854000e20351a06d0420204104800403080c542c000700b800da20075444030010308140e546001880d00151390100c814680e0f00c450301c2d0007040b451048600f00c41c4d00b5100d80000207035001c1f800203552501d010b0520009210780c800b0000d100103980a50011b005807030512000d40c480895050030b1710145810140d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 688640458 1250 688639208 688639241
    0x4150905180f072c15011202070f0201031d0714030f070602060603070f0303231e031b0405011d030309100c0605010b04060c11060706140109050703060e06090901 71
    0x84181c4110082904070480b1103004003920941c400e03420f444200e24840159a01101c4044005071113817605a0411206a00c1450080085000307100d84004a03000110155a0882d071003141008650f0144155440c255120754070786880002c035001266541aa801541814003040b04601010703203041040500d03040e00340c000c0e00c5c030054a4a0000399030b4481103590038842d100c4c01e000015054007000c0f80b182503a426a64001d401080d415007c00c18000c07901c4403403041c6908102c144a810f82461024110307283e1224010303928103000031a0401e06a0f500c2c0b03107000c41041040104a26038005540300c00c903c00d41b803072075420001c50900183c01c60007150141e030382040400c28a04245175000c174045003071b00d10840c020000f036600e0701202403090040780110000300c9d441e441d141002c640f44030003a000300b05004207000d2070048107a48000507603807502d00c80c500354000e2900500548440d0b00440382d120140f0b01d4108981440d04030841008040900b071107000c0c0f491900800c00ba00e500390809001e00154040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 688641708 1250 688640458 688640473
    0x32402071b060302090a05040509071a040611030f091e06070605070305150f06070602040f1e1205072c180c0414040201030c1101110a0e0415090518 65
    0x4295050858480140007440c0d40c400300441c84900030320a5030101000602000b940d281440140002800b01800702c155904c12640009814038501c0014001d14a1002415480e00e117000c50240012942c4610005203030018040c900540c505082500c214090480720389007040081d2301d01204400c6820705003a004030001421105100c1c0c0754010502800d0659400c1280341c0c0c4065111242003c02e201656205c150b619921000b0320349440030348140303401070100529065841440b6145400c2c00c2c6d20044819107441c41038400d020402d1700e0b000c0100b04084081d400a90a40e440c15140c06080c081c0c6a80c184200f203034081c21000e10b01c0382ea034100310700e107039480414101b491a00f846442c00c02010b507000c1c0302e07602141c1541e040901800303280503181441c5e80741ea034440f46d005501800d18554144100300044c11b113120304080900a030044e91070801c82460343c1c2c2c0140d1000800c0b1007880d845031801907007050000c06d0040e4410201d142181c183d901d0000e51030710343e540c00e40e0710202000c624007281e09c180d11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 688642958 1250 688641708 688641713
    0xb060d050f0a110405090c0f03011103010f080d140306060a0c06020a0801030b01150c020609010c050a030801051509010804060e1c0503100e0f070c0309170307060e06090703240207 79
    0x9520041d1a020f05421200c0104103c100410b8076401c50f1340c803031036400926504403a41082d4580c020300ca00010008541040a00400e0306150400d0340523000e91701c5c41140c1044018000e0011094180652410120302d580c01c2100c2d00c40c1b84070140c0101d00883c00082d8035070360144648040002d8943c048000e5581d0b68000c40c008040650038081030f10318080c00000010700c4c0382040b00c40c805010b5151120140500107408000182e00404112818040800400c5001420500c212800240700303494095155050009103c0f041340040c0c4d0b040c450440411022b01c240e0380160115902c26841200030031110b840c40740640c01d0282400c00480301c2280350000d400c0d141c3d0424081c61090300488540c0c0c000a58802c011185c0301400e5544090220038000825403070b5209003c41712005000c0d040c0207411680e00e501841d01c428840f004c0d09040e0b00049502c0003080440e00a5020801d000001460316080941c080c0b40c43c1d1007184002460281c4a03a40080f0340c02002419002c9119504821902ea41450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 688644208 1250 688642958 688642963
    0x130e01020d050601090f120c15080702151012051c0c170307050405010507080412200108151315060504211e050f1f0c09120b060d050f 59
    0xd194001e1128180340000c0c03402d510841d4a00d08403041501140c8101d03107032800d0075641c52210007065a4085007024003140517690349034901c6089410780d6a4007860320f8106002818100c4001c5220681d500f10010301c40050040036800d000e0301c404624011031001a4544549085005e444000c0c2c2c0c981d400c40703c909140e0700904100b01c107500846040e803101070035142031a4240710484111000c524180000d00c05e55200c3d10141105601c03440e0b20380d00d40782d15031600d1b01340e001c81d252044420904030b000c400301c40d042c00346488421010070301b8030b54101d0521520060300c40d500416914002c1c004100414007888054011030b003a0a0781442411180c1e44640c0003c04a40c420300518039025080d084501c0704580c9203411068568000b030203102c1e01918102805980b516032541901d4900c5100e0003074420fa4024041060710300017030285158200d406005403000c0d640400300c058140a82100204805201d1010510090380e200010344040d944090004142150260010306248034507020034800701c000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 688645458 1250 688644208 688644217
    0x10e0d060603140c0d0c211a19020307021c0e041103090106060f021903090b12010905010803040602060a200a080f0604020c1005100918171215130e0102 67
    0x3c410a0314010710120f000d001c031203001000000c2c12500115402c00103034041c202d02544620403420001001c2c081c5440d45905a494521192100c01c0040c0a111028003032041385540d0f945910710a50035498010406034456010034209201000682941c030b5503188a159040701c03294008104204520b00f48000c0d01e2117030011100d03403081c1d62070b040000c1041400b9040c00303240d40307003a98010401c05210310003c003600340f0f183c8811428000c2110010036042184006020200e030b10b02c0d20114207603d052a800240c4034180c1c4180099017042105001c1e00d0707400b182c40c5502c1203100c180030401c4588404c8480f8048180342000b5a85070000c41d03892882d642c844a0180070705041c0741d5500d9140c68040401c800ca1140700c00e502034590086900303d030440348603000640d01c40507804612881641d60810785041d07c81034880c107045106052144c03410415200904101c01103c4141c903401d002a40b02c51000c074000141c00d481e00110016611516652815240c00c84d07181074140c00d107c3d5480d4082d0081c00b1390003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 688646708 1250 688645458 688645493
    0x1e0906101814101704110105120108010b100504080703030e0d0b070f0210150303080709241d0a0b0f09041514010e060a1b02120609060708010302030309010e0d060603 73
    0x41182c81080644d00c00c42014142100e00a840d41068980d659451050301500800783d0500606104107600c03c500d0a880340e000302268000802c081034620200040a2541c60010081c02410321003400f1240e40003e03010140c0c1d6040c1440100031807544009031400901035001081d81c0e05020800c800b81d9844214003039110700c03540841d03044da07015030701007400d072034490810f401e010318549002c0010901c280c2c0c090380c001009040445a060302c45410b400f00310004185c55594001d1a04413404060340906880c18260790800454141c1e04481c00245080c40c2c14456039001d0030b03021420014840e09101240d22100c4000c100f009004500e490300720966030039214640011000c40c01d10b404031750040803008000d40004260601e42407000c1d006682040c1070b80071207800c07034608200e0301c4011303102c000000b4244d1aa0340d0003046140b418034400d5250160040c500020010031000400043e1400015150540d4003400e000c0c190024080100701911381c10500500b02d00e08080000003032010740c08042404a2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 688647958 1250 688646708 688646719
    0x50616121413020103060e27030f120a0b040c181707030305090303040b041202040501060509030a060c143c0a3b0405060315060f03120c010b1e0906101814 68
    0x220b404100c4c0d442b0300424014201e071650402100300b510030040c50840c0d202203a080d002a01c00300310720100701213031040104540416901442c030040000070000c50320050400c11211400c07044504507003901d817a8644401000e2000100d011189a0360900644001e4924042029280e641e0b03011580880511000d0981c026441e000c000309070a48620201c0d8101d1901800418910316107a454200030482401c00c0010800d1255a6480c1d908604000348003011048810415030360719034006454030311200e80701001c4210b021005d0101d4904481c01e0312080303070117070411179501c3e105000c0a40903008149003a00090348484141c18620f40c0c0c2c403000030131070b031000c0c5c5080150741e4031501803540e2516204040b03401a0301d60400110725103010540c1b2048064050280c90a50f441e40201040c81c0e009242041d0460751680b08000e074504101e442d0b0302e003500306807a50101c1c03800c80002040c02c10714043c0106002e0312007080c5190760180076601d25030240c200154849051aa1540c6070000b0061769103040d803240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 688649208 1250 688647958 688648021
    0x3050f1f0903020a020108060f0d030809010518070b0a0e0604080a0c0b2a0106090905070e07020307030f12090507180f11031909050616121413020103060e 68
    0x604501c589a1100d038103400400c014202030700196541000180b401b50b200c450010060011f0301e1386030840500b10b11940f80e0552170b0802090040c02d5507001411202c104200c2030310110ba84100050b0765040b500c002500703e55641c02c0301e804a85c030a50700b000d4250000700014000038041c5000601e0110907000b020300c0300720304d030700d13a80a1020b9106051080030104500e496000380e00c5000540f000102c649080005004c56980c180742c4142c89401c03200361582c0e000400100b02d920b0b00c0b69916540510749102a500c0e1200ca66400390119526403040010400b80200c28001c8540310b5002180640c2c012040303562055490380121504d034540d1031415903030b80c1011425440d00380d00b406400c0d0b0480560100714115a68100f010304480e40d0904000940c40e1108214000700d94140540380c043e0005100700c2860307482c03d90010300307082d45201001c0b24180c68004486c4001c0e45200505401580444903504070030150f000407400381c40c1c207412200351401c503441400141a900d00591110b00001c46820251 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 688650458 1250 688649208 688649263
    0x60c0c1406070e0105090609100306080607050705031b0a050a080c010e1603030810031506050411160605060a0e0a05060901060f0905040c17040506040b060d02010e060903010603050f 80
    0x3118419260540892881400e83c0d20641c0642c0141c884500040e00e4a4201100c200018103c5030040c00000e000c01d0b61880705025021060000d580e120019040003445d01000c0c1d42d0b8190399210300164994651031840744080c48241c00e0044074921a0050100c8510300f010b4104ac1d10994000c02e40d071141503107001d440c5118036101042081240480c4145da900c140d24540781503030402002462613035214055400400000c40010381c428042c1c1090030005000d40c01d0030140001c0307503949a5103001009040c0002c442c2013424080a800c1c4591122002c1381945070172021401682d665002826550b441030200200070421703900584c46004200c446d24090b0b641e0303500649114011032192000244100e4060200c3c0c20039030031500c00d06000380f47c189100e5140054605d0010410b50781280c454014000340403e00a91109540e00403100f101c80e01c42c44101c3d680041c01164042c803100b401928041062417443ea02035200000442d040303400d85d0261440d082c0708a0311012140700c2c208000705007401c0d1040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 688651708 1250 688650458 688650463
    0xf06050702012901020c1e0904050a0201020d0801140409050c1e040b120a030513030206070f0b0a02090a180e03130e131a100b0a050a171e04030c060c0c14 68
    0x50f035103040c2c01a154185100050241c3c001e443c984c40e06098061a0007a070b130319200d0140b007030310030b6002c0c0001c0e25842c9a984002420002c03100b101804010b0303250010b000c101030312440001502c608036000150155546800b5080c41e0b140c03450f2541c003140824000102954409001e01070001c00c43c1c04000c5105e41314100400b6442c00e6005010325404510020300090046004080000030240d030700307821598a900042c080c1c0d001d10713421105820f40c103040c60204100d89120f550840c950803015420851a240455510141849070170340d403030080e0300b5007825024035901070100e4108200a0781d80c0d642502c50100c0d0751003a02d204603003a5100c0d542c0040e00d03c10a1004a0100341d070f00600407508960103070070036800b0b8007000d000c01d40901e1f88001c0005250700203038002e11500c2e40d1610740e541c07100d0f2400ba01600030021013a0520b01d205401081000350250450780b8005c01000fa0f10b82d4505454a04003143d0b210350307d1000400040c030b05640b0b10b40403070b041202c0345401d0307100b0303032000d0710005190403d9078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 688652958 1250 688651708 688651781
    0x408010b040c05121857040b041803120c020304051512012d030b070305040c0803121504090b06120109060f020304022701050103090f0605070201 64
    0x6001520030f100701c0c040c24850900e00b41d04103008500140d0048510381c1643e0910a12000469401400c952450a0011080c0314a4900d072010407841d402d000f640465048200079071b1035100d031080c1a007440601103580c3c1340d015140812014108010115488121000900d010f0b40705034082400c009804840d0411400303291078180c02640035508140c540001d01c0140d60601c4609010920103001c65074034100c0c4484050b0003802d940100c8950014100c41c148417442d5080701684140d801c44609001054001880703d0300b01c251031600050a40e1241803001500c03030107070484281c50000203221001543e8044401d8080ca045000000740702d400700c0108411a840480000c00070016880007400741d261105201701d0481d66400049445a00790b65803804480f2405070700000c5a40c08001c5c44154244028075142a0340d1f031000d100b24200200010f4900414144038441c101510741500c1400c00500c603003d0308166a000d0403d100600703100c4806800b0380040011180040068013040d052101e0207400758 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 688654208 1250 688652958 688652981
    0x328021504170a0c0501150e011a1b01020906070606080c040509061602100e1506010807051c15061d06130b0306120a030504080d1e0f02070503120408010b04 69
    0x2100466503515414059040343c07641d1824814510a00c201150003801448013080d40d5099010030f80381803002c600300c26141a0880e001d454089402400e084810340122044100410303108002c14440b4101c60b40640f01e125821a003003240403814031704009680d0000c0c0709079443c00054070040b0769440240b0040300c07400c5513081e40304e500c07140100307044013180140c160740000d00744151012000a00c0303000e4143c42c100c034804205540001c1189034503019000185e50041c2d000d10f0459542d09060000500c140500d100e41d82c21061010965039161046a20031800410a40641c0c40081d98602025115004003403003a0101c4d1f14902c4041c20501d8184c0454006651034030320180118201300494505410040c480c0d504144043e400c11b512103000c00c56640704030f120344d84036595581014242ca081c81c000c05101010b000031070b03008000d80050240d0040f941003c620384141440341d108000c901c0c21906030701498040c024031080850035a1664003c1c000c0c2d561440017480440c52107400e1000b2204180501c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 688655458 1250 688654208 688654223
    0xf0803030c0729011e05030a03020606100e090412200d050d0b040f0204030311060f181e01051e0408161703011e06030e100e0328021504 60
    0x400740041c41d40440c2c0d041c00d014880e4040f000305441280440500420381210303071158030213280188041c2c1d00c0c40d1401e01802096016004c603c001d0303900a0340d20303a03001d002c0a109001c00781320150024800c131000030707a40c0402440c6001c6410281080394070000f0314201c100004400b2020308040c4c0000d940d4241e0110b014100404000305140e07001c6925400505d100711050362a0980c9884d260f6950045051401e00341e140141d41784d16604d030103400801c10203142042030b04080100700d410b503a0365103041d500620041c200c1e983c104100e102075042901e070110780c0207039401007007282000b420158412403180c1203054100a0664410744c402024501c01c0340e0041440c0380c00c000b90700e2558a01048076080d03a21401d038115001c403840009030184e4000341c214209102c8410358050303910410004031802030241d030030700300050095450390f141c8a000a0903400c00d5103490f00180c018420080049451004049490080d0440c102040d9031240100e9910000140300d199107409070070100d048814051a4062138 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 688656708 1250 688655458 688655467
    0x105040818120604080d150b1305150706020d0902100206090f030708040b090414010e0a1802011704231c0311030703111303030e030f01050705120402120f070f0803030c 74
    0x5174120701c2e6200400c41d0380529280e240f00507280304500b201d203025110610710b10361114090008103140e0300741a44418490484413802d090200d195004a80b000c580040340035965812403071204019200c074000088d040010170540c0100d865011407154010b501c090281d9002e98800303e000e59907802070007030260003604200820044c000c2d4042c01001c0a8402802c00309a0244401c0c44a0102c4401d901c02007083c003003802002559110391155890380302d954001481c60040f541c00013810810300e08070510301d500007180840d007030004031010000d1140b021444a214414545415134403071b018101c0840b1405007482c2c0c2840240e009000b000e141107183e549041c11030340c070000202d01400342504107440c3c1903c10005060305031040135032070010b50b000b900c412080000003800d05142814480307419a099150100b072091a6600c03d0450f50b9599185a100c807060700d032800094000440b4211044040c85400c408114160700414034404554209062420003981c8009840d100c4c8801c80350b60061803400c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 688657958 1250 688656708 688656713
    0xc0f02070e090f0607080108010b010906090626070c02010201050c160312020c03120612070608063607110a0c03020105031e01090b0f0303130311030f0105040818120604 74
    0x2514554401c0a1904488950320f03800443d03403c0c241d05903100310020b19503c005001c0004240a0203510400030318015210515080e001018403c140c040d00041142d080c020002007400e00040d000120104c070f008524500344110702506170014900c0481c00b550070940084c0d246180007098450040b502452405035000c10354084a001c0703400354100b01501d900f4420302c80b800c401040030f400320010300f03e000300300340c1020400c018070700d00710280200b2550b0054a0a0010744d81c40403409801c244191003025988210301c000300314089601d44c652440402011000302c01d040385040750fa01a020944902c0d405c0210f0112142d01c42d090b0f0080a400341090070300030001940b00300d0095612000c00392540b51581c041b16050849190b0030f9008061482c5c543d07007000060301c0c1120210002c40740c2100114a0906543c2104c2d484402a1202070a000c20480b0300790060380701803040d9503031810780000801c8903181038507098010b508103402c8241c2c0704030300002a00c1182800403450030150740f03000050601c4e030740c0d65 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 688659208 1250 688657958 688657979
    0x1d0f060a1118120a150504021c0507050f0103020705060907030b060a030503070b0717130c0602010608060c0f04080a080c010b040506011d0406150207090b030c061606020708030c07060c0f0207 84
    0x3c0c10600300f01e1090f0858580450783c1640c01010030001c0000202d00750400d401004811074040d4004502d48908601c0301e40003480024501c0100c95081d103c040e001808800103070028020480060194080e840400503255004900740084d288102045126910f07400140100c0c82e84500006105500810084010800c8025060b5106090385040114009078014948800790240c9580614607294150003081014021001005c0c10083c1b0080001700e1a03e03045990b00c4c04050052451500300003a0b62031088555011600500040002c031542000b40303242c25000781c4d2025141c4130241d441d100424030540380c40d0156501030300050b910300500c030401070f0068641c001d9403481e05600c80e584a40010f90a01c034030344040c010420540141103020f02d03101c3c0d980e00340d4000044040c0709810401c40e07681241d581380241d0fa009400d40108145250003481c22030002d125451019101220200421080905c00c030010491141300300014482607105c41070541d1101c04065550f400743e00180c0c01130142c05010f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 688660458 1250 688659208 688659229
    0x30f0c060a03050a021e0a020d02061608060d080c030c2a040e01060e0c0c190c03030507150227030619230c0406020d05070210031d0f060a1118 63
    0x903000181b40c240302c006000d407841e4520f0300041c203084021448182d280d80600c810324a60040c1d0026201a01e003401082d00ba10283d580520140f103110b402080240d01ca001607000c10300d6200785443c1d510080c40070b00664075003044000c1c1210b0301c1a090600b07501003008407245800e10349170304048041d0b42032008020140580c40e1f80030f0741566982a0004c2c451480900d03140c0a0308807c2502d690700c90f07441c014641810700e00300ea0070410440d04002c0c50009245110307280c08480c0c140c0f9145880e040c484c600203509100000744060040d0011600415250130301d91140e8114400c441142c030b4034080c0030141500d5a108076441c818000500945202c00d10107604030261080404201c28210307030691081050400701070f140c0124500300070034140400380d0104080700014606040060400c0141d80c002110785140004482c201030701c40c1410308551191056100c0f0484250341910b100320090355072185d480c03030112003201000d402c03d2611043c401280d811910346041b12140101500150000d2000d00c403107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 688661708 1250 688660458 688660471
    0xf03091c060f021c0504170a1107031a160903080d200c010b0915010e0f1c06060b0418020310050d060b03060f070f110304090606030209030f0c060a0305 67
    0x101040e00025641d01c609615500038100060302c6822012112025050319a03801c13030309924050500000c548a515402c03031b210760001d40380b40e5581c81e01c2c604440960700d44140b0a203601c1116000310801140000402c0080c02c110362044c0703159500c0c05004a086503100751307800800e2614006001050101e402000d0f010707040f08000c07805a400701c039029105142d8607511075090300040b4030700800050070b000d000c0440e40122201b00e040d041110b1100c802c01e039201040c9040c42040d0701a02541c2d00d4031300e0710824002008110b43c00e40c00c0780c00f5101c42c503222500e030100e801c240b8044000c01d140c81008181c50655a810902c0382d04080f07040b030000025800903101a00c05105040009011f540382040019402c1c41846c0208412940000307251800d80c0150407031144000080412840c0b07644014501120b02c42840d2900c0c6550180f550141140304a80010408904048000c03404541540040045010a808440310604d84c0e41e0f105850b0100c1c1030066602001c08c1010b540017500caa0410782d04800f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 688662958 1250 688661708 688661749
    0x306051008041b0e0108010e12030c130e0a1407030c0905150c010509150604090f110f060316020c0904081e040b04060f081e0112170c010501080f0f0309 67
    0x4007000c1c0424074000c1140c4c0700c4c2c000c180401c00144030548080c0502d007818041c140c002c2240c50000c90503c101400700610603c02d8000201c3c8468100c0303080b040701c00017003000762200e02c41420211b40c440c01501800c0d20310254614441d0118031020300c28800e021007070b100d40e030310800136605000810072186000b40c66542580801c1c0030110314402c00303210781800b54800100912803541050b0200b51000001403846210f14a40390210f00810300300d0542c6100d43c0d034130803510a18a40c2e900c001800001c0f43c092601d400c100044104842c16100b0031074910300c00e011782c08550006103042c0400c845014121002001100c0500c000f800d168103204044031020118a181818031b61210f0000c2455000380c0d10100000d80340364401d6000036040803c41c0d80040c1c0c4075402c82d85d9890303100c030442d00c2003206200e07080f520b4108810003028401c0007502c2400d46240000c00d142d480740c0c1c10506601800080c00741c1d081e1800b60701d0103417241c443d0028101e44542821006141004400e904102104074414440e40034031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 688664208 1250 688662958 688662983
    0x5010c080403140601031b06020c04020c010e01050103060b0a05030601030809010513030b040b011805040f02060d060e10080609030a0903231038040908040806010602010c0e01030605100804 83
    0x300f64030440d4804640b10740c000e007520340c9503003800c2040b11a101c0051500d030f45400814000300b07601042603d190b00c01601d016a031031541e0121980104100d07142800e96528000001c020018660032860030101c04503031501003540c0300d038109521020280300090500000308243c140a5004502400441c2c00b103004500a60f0b50300c1d00c4156510104580445010f8003000c01408102d849184080305400701c01c80c1045545440d681c0c0e600308007002107010344103240100704421140d10b41e40020010b0043c91383d9108890800a81e48003003a8100c1c0944107143c0214000106d00c01e00001c141c4416040da030340c03110161032441e102e0030303450440140d4000e0210b044c08080022010104020b0f0300000b4201070000b00d541402c0a00d0801552071510440f42156181c0180c044030440301c0240c090301401c0743d0006000c940362070702003085e21941c0d0101c04180581c00000032500c0d010360101074840e03010348035810720000c00401101156002d014550340001102e420100da03d00c140c02c91540300c2d1051001e01d01c40e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 688665458 1250 688664208 688664213
    0x301020f07050a0b0714070b15040c090911070f060504030302091e0f0909100b030a020d1203061a07030309031101020c010b1305040803070c030509150a1106010f05010c080403 77
    0x1591100900b51415440111030004100c40036164030781c011618640824003c0c204040724020f0b01c1820000360228412030040303010090f080100030051078004004001c030518000000c1c08034412441140c00d034620300000990040c00460803100c00e543e101414038021035450742c2c0c0f04000c1601800542c201582400707184c1d4a84c5031040c280c081c01c94158101902c8000303c6040100360350b41c5010b4136004980c0c6a041c8008410000380a0101c441a1440498503001b1500403d1a040c0c2060010b5400020704120070305200701000c03c0c0c42e070903035036690601440f034641c0d040c3e9950304001c480303190828104102c81c4011034482c3e4440542c1c18400e19080444040d881c010909903040548100d065940d5070310000528942515540d00355051107601348034524282c0c8070340c0c2c0a40401803104040c001e84010070f00c01c061040c012908903080046c0000e918580c1042c0c0480c1030341024120001003410008044000c040008046048501102c0441c1c9141c1c140b00046903c1c4820080481b1480e205000c040300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 688666708 1250 688665458 688665487
    0x2c060325150903061503111c0803010b130602010504020d2004090b0a140412031e020c0102040603050114100f03020c0a1101020c061602220c09060906050f070f02030102 74
    0x1c01892035403118541815414140f040b104952651795204100280400c0010ba00d0001c00900345422a900720000e880d9894600d03500044100040031604000001708010303000c10080d25007000d040040308d16880d1a40c0040c0d00700d0f04140c801039800070204a50f400098506890b041000032018204030b22a110040454195421010220740c41000741d0704001e2500305030300c1000d52310241081c030301e01581020b84809003681104a000000c050321103500700c220400525410b1180101d2a104642e90714030884554000d42043c01494006411300c400081d400401031900b80191800a0854a0100514400303441c9195801c00031070500d5000c2c07002802c24001800a80c000f5030140808186c1c0428601c00281132a0b645c88115119010a00c00202c0025030906040001e55043ea62303040390071201002c182c400c0204988121215007020001c1210661041000084805603201c444409844260586090040d0f02144600c0b00c81404a5400300e0460019082002d002500041c50410351541c0d03c0c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 688667958 1250 688666708 688666739
    0x6070c050904060c0e010306050f0f15120f060f031b15040605040503150907061b0f050a17040b091c0c0806010f08060408040501050903070801062c060325 68
    0x94500d99071300707034141e03403030340c001001c429032090034a02084468200740004803c0251300d81000d025407001022060903444400b0702e1217282c261083c40d60303110b40303130100c4000d111442194600107000721240801c3c40343c20440140010072200070080c2c043c0c6501603220410310260607040550140013001404120247c00c00104054100d507564140e0702da0610003072500d880d6450784292060040001003150940e40400c0c1001611024985440c03481010315840d042c1078112030001d031258440e100e84004200c00010400000d034400c150b010900f0503050f01d00d80c1c042c0510300c200c6090b68010000200d081c50004000802128584600b814003e099100c4002c2d081c1150099007441d0720410062010903942c0a200005210090007015030740b810740e80d2008140160f100c0d180c180800820041c0d01c030358042c89400003a000b80c00c002c0201e00d0361005102c44c0c2c44170042c403010400400200040305105490401e0b0b10811001c0e00130b095602c00d0a880009000d5103400c204920020b01c0c2001c100c101d207400809 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 688669064 1106 688667958 688667963
    0x20c030c0d030c0f0c0f091d100b1906031509020a0c06020703050d09080a1710050f060708040803070c080a02091504060506122205030906070c050904 66
    0x4d10141c4003910009241c4005d0b400045883d402521000c1c0032a02d0004040c40801100c8514011581e0100c4480c2c100340c11103050900000c1850300100900b0902901c042c520044160b14089048059040000001d840b6120b145140c108507029401402102200714a40503038600c010389820388018004064a40120710780f003d00d8000c409036094040e40940510a00c00c007858400740f40d0b4055001c0b50046030345a410007240e4042150194414141c0d0620b912045080c8810030401a00d0950780c91340c40b00c02000340c04001029076000d170004140728030045807140018508015000e6440d084139546502c4124181e01580d2a10501c13274001c0c1e02c280120030301c2080c1c0d001040c0a003403180c100c1c5070010790025407000c1248100007940c0c07048054500303000d05031000c02c2403410941d20107040a0100c0c0e000788800c0c06546004001004994401c07072800c185159180041206420203d405 = true := by decide +kernel

theorem cover : BRFrame.Cov 688489208 688669064 := by
  have h0 := BRFrame.cov_init 688489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 688489208 ≤ n) (h2 : n < 688669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
