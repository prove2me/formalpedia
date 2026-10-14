-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2916
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:07:23.062763+00:00
-- url     : https://prove2.me/submissions/3f69fb76-e291-4e62-976f-667b9e39f077

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 524280575 ≤ n < 524460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 524281825 1250 524280575 524280593
    0xc0807030e0315190b010e0904031b061406030607050705120a090e1317270f060714010f0c0c061505220b040903050f0a0207120b070806090105030a14030c0a 69
    0x603c030113006020701c2070780400442c3e02c1841c0003503842d400200b95010030000b90240c00010380002018016070203134001e607241c803021070b00e02e0701c3e400020756040800c102480c038013031020541c06002801c0c100d0501c031240c0c540d1aa01c040c0441c40f104200e50004481480602030b084200040070345070281c914070b151510b2001c01e4140d0600c01112905040e41a4400f420691030903501e440e1500742c40750540000c4030300d0312031400c40d007020910f4020f010320314007a10ba5111100101031407806034001c203000740d144000e511b00316824280c1e40e4107014a080c64090b10554003614480c11540c02070b40225800601c034600480c245d232a90300840c2c1c4020b0400c00214001821036207500e40c448448401c01c000c58801051100366041d420008001490070000301c0094840d031806080101142d1044440c41d03501c1d41030800e02c0c510ba030042908c05842000412150030350080f2002e078000015903101c142035160201284d0307501140d600007409529201a86001c0c910100103440780c6641c1241151000c0031181491285 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 524283075 1250 524281825 524281861
    0x60d0b090a02180402090f0306090313140d020607020a050a18140f04080f07060f0f0c09180c1403010f0e0c0304030f0c050307060501030b0709060c0807030e0315 71
    0x2524002001034040c02080c82a40e00c0c80c030315051628003d656000070800258002d61503290300054008401e25151010081203104038004401903a03641040702d46030010300003907400700401d424004540321550310380d1910341302010b6056900988440440c80000c550880c0c540041d90400d5000c480008c001c103041d80c0c02120400040000c020245241c01c807008102c3c4110b510302d840c1c024641c00b10740083c08090040ca18041c0c01c401442c02c0410556580055415000300300400c5900c6040003940d1201c2d0307118a41c00310b6601d081c2100c401d40307000744594142a105603480781a50355a04085070035070045400d071144002c10134006989685800400b012901c09010301c04000909034000f03460341640c0300c01c4900940d0580c60b0303203055141e407250403501410403030400c0711a40414820301001070118000d45004e50b02c1428208001d1501c0c9100505481c641c1e0b101504102424240c1004900741c1c03022030703c900b80c0619200100c1c1100747c000c02c2c6401d04050119812020710001c100030740d0700100440a13 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 524284325 1250 524283075 524283079
    0x12010f060914040c0302010e0d0b0a090215120619030212010905060f010b04120317090a020f0406060c0602090301021204121b05100f150801050f01091107030c11060d0b 74
    0x1118251564000c480b100e0200d0740104051600e407018000366007c0c4541c12503024005018000c0e00c2d09032390350414032050540b426000d40d40c9a60b070090852030100082d6214041002030a801c5c0302c101c5032203822018014121500481441c00d040c0c1440801c07052540c0078540250402c09846c1f0820f07400d80c000c120304241540c960003003c0101e022400250704450407034403850340c0d40b81090700708000388490042c5800308906008038020507540a00080304100d200302c40b59006015026228010720141c070b040d000c0c485100d40d00d04131050000039003101103500c5842e000080141c42c0c81001000c0b9009108845079801411004410403003003103041010b2407984a2113a0707a25481054048124404070382d114401801e54000d01000801080c0c20782c030007482c0028001000c01d55040a00a0382e00c20b0416402025440e5100c5003040500c80704041d4071401000100d00400c030340c0b503900d401d41840f4001c5400040030014440e0541d0240909039800c44560000100082c0e511801e40d51000010040c3c02c4520b8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 524285575 1250 524284325 524284331
    0xe1c0b010e06060318010204090606020619271401290a03170309120d020a03140601051e130e0703140c0912070801020711010207080c060a0c0212010f0609 68
    0x1c21092100c500d0705005120142c2000e056844080d50100d400d10b903002c0000b40ea650a1000055541040c01120000c00a42d000380c0329034100403080d500c1c00000c0c40d408441841c00c19400c10001903407085c0c1c04480400003011080802c00c285840c1c00c400d803d990340010300c1d40c2442d820000040c02074401981e00c2440c1040b4103154200710f0b09109a2132000c0c800070340240c0d41201d40034900c8041800455101164500750703807103a541c0c5055090960020070b001014194040341e02000a5010300c0340c9202c2c114280d19160580c136100f00020214400d564800c9009103072583c8a1212100500644440d0350000c580d12036050f03100d010410188208481d9030001909045d1003581c0b040121081a0041410322083c41c0351844082c10701010501d0030300003004900c100d1500045091081c8040d0070400e10480e0808008110180024501030041e0454051600400f0581c5100d98560003182d2421003107040c40f10a0752454000200304070740102c0044010750070711001c2a210459980030100ba990008020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 524286825 1250 524285575 524285579
    0xa1416140d06062a0204020d020d090303021c2a120c0201150608062803060f0903030506030304083a1116050306060d0602090d0b0403020d1e0e010e1c0b01 68
    0x81507103820704090011380e0f007403d01c2e98090708041d0010440300e4200c260141c50b14a000f1941001c590b0710035000d800203030380400c200b054034421907000707500401400400c2c85202d01a81d6503055106840840036550900800c0c20780e02180100c0c2c15084003103038480104184400d104001c0e01032300e103800d0a408103904040d80071454038020006180501000750030000035018003041240746644051407821a0001060004001865801010022680c151005c640200c49140180a40d0fa000d000c1510031b0f0000c0c0f0060041c00c17800152010005c0300001c5446c00a0300d9a0500090240d0412003201c210010000300310000ba004800088140210ba01312490381e0a42d0900c005429968002c070b81d4150000d10100d003042c505141500600e9015090040c42d01c05950006045a40e11410440d40008440200024142c051095202161550424a0700304507100000184408a89400d40074031990298000c00f50f48560458148040e028010201c0b642c000c483c170038504103030f0100031a1448444400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 524288075 1250 524286825 524286857
    0xa0305071e09020a1e021c0c1b030b0f04020d0f0f170f0d0917071a0703051003060e0c090c091203070f0215090901090b03060a1416140d0606 62
    0x2c5540100c0070741d03143c400d07481c0054020600b400c065440c5e081107128124103d041c054011200790000f041d40d807541000304a10b40340c100a289920341c410303550079103030304001c00200f0342000c4800e6100019414407040d82d0340d60720000f16103811390305000d0403100648c1e01400030800307910701e00583d4501450301390350004a460b50300300705c40c4610400d2290400090002c40c141c2c450325001211894420400400040d6441c2d0031405180c0210200313440000300d5411500c0d00214195030b85d078001c5c000385028005403810100c6040d502095101c0280030907508c0314246a007003410f00c401028000010064015400c103040d01c0f2140c0c0c0c01420f9924864007641000081d503000000441d058203038402520b1440342c126800704400e2460f60042e003811413000704130180207680c40213255400317001060000100e85200c0c005052030110001c00c510141c2e407030101f020044403281d80170f5983c0a01c9041140450180107a02260701024200740c0f48801907022503440b5407000d05400240942d03110b40c1d01d400300940900c070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 524289325 1250 524288075 524288077
    0x10e0904141207140109260906070c061103040320030a050d110c03030405181308130317070c15020309041a0315191d030304031205011a0301050603060a0305071e0902 73
    0x28001c01407400c070840202510f0340240704000c400c401c941008d003040c46c0c42001c038090f54003411040303880b900c800e1010b21140b5004610030881d110110020340c01c2500755601d400c0c170800503d64101f0101c000d032083d490f02e43c1e82000501005039021080c0d0310700585204001c2c0401042100b40e4a003402804070025813810300009450840d20024011400c0e0500503580680700c60000d044080c0790620007400001083c40c0c0c2008180300d00565070140b0b101840d6007880c00b0400411101d090005004115840204134100406800d8032034100684c0030300704e07100d4001d0780b561040c00c1d00e8039000750900b081101004020400340c02c4034003040c0c080e68105091000340b10742424003120002608400403920030030600e0641e10240e182d10f4404802600003a41408040c42d58004072002c4000a440055800c0c4216981c02200d004007441d40b00c0c02c80359490000842d00314081401200d02030040880001c660b45d4529041c10002c40d040816600426103d442007442d1405114002c95622507401f00010902600d01c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 524290575 1250 524289325 524289341
    0x90709020f03040210031407180501092916050606030d0f023c0303090f0712080304060b101112030601090e060109080d020304180902010e09041412071401 68
    0x410030301d5a680c0e582007005e41002404414201035444585401ca504c0c030144c0c40e406401c0546514002c805440c014602d4551207030891410040610340810a42043c580b044d0080d4078020b4044200c20304444e90001a07015010320310301043c0c12000200240070010072917030f0040b0f00a40658082c0391402100340c1e588000c4a1403100142d1140111803072201000c0e0b0042220241d81603050071080040a10328075030b50f000200504580c100206005103103808102d01070745032000802410141e450040002e810025000c800390040720004001806c0050586c00501100b01c014600540d203034414070300a06044a04d0035851702441403c41003442c414442c01a80e01c07070b01050395400445405d10701d0403e40035602801881c14072002801c0440c81d4501070040c400064040c0d4002c42e12146401000221010041d00a42c0100d1034641c1510260740e0240c1101841ca8082d20709445a45440c541541111500440039103075010703640c42086881c4a000040c407640f8002c4280300c80d10600c1501031800c0364004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 524291825 1250 524290575 524290597
    0x2c0c0d02092409101e03170f0d0603030207030b070e0a140303120123150f03040f0804090203010f0b03090a11190e040203010e060114010302090402160b09070902 71
    0x207000003032060850720303420924118060590411070980a0204418003403c1d1141ca5003001020801d2002e4513814101160f0f48144d03180550704940703140c403040a407020381d035001d904120f030000d6082550f50580040307520885030140c0801032155039003070082d00d508807030004880e01c103203800101d8404c600c0345100d007041600c004c1501d2080e1f40703401e11b401540c800d01d80c02c0542600041c0030000c008508401010300034080c221140c0103000ca442e000541d402c0402d11900e21801d03001c04981c128000480a43d5000101d405c0103c0d80d039181e078148507083d0b44074940c0060100e50002400f00300c41c81c40d40c01641c100d030b290413010450b043d00c2c1e401c0c15045000817100080e056025081c43d500acaa00d01900e9800441d018110b2039483ca140701d150380444130701d9013145090000310410710045041c2441a0076440c641d000242c51654144805c8100703240110b0361080c100754004c03820401d50760380c0d0b03811a00300980700803071660520240c2c038280c00030078801c42c0c400e0000e00030348400191061240c000c4403030100c1e007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 524293075 1250 524291825 524291839
    0x40f050d03020c13060e040c050907030c36090c030b060c0309150c0313030b22241a040e0102090a06050310050904082d0307050a02012c0c0d02 63
    0x908428003528104042c1113208190329500d0000c0c0702005900c0450056000b10442c01c112400d100500084803130282108003014641400340c41c100341c2c803403c814051440a0340c0240d21204068842c0d0820b00301d60703c0c9462021580c0c00003d01c6a40c0ca510038540841c0c103890500c0003500207030401049e4000c541160000f41c00811071740b00c0c1c500d40070314002d00c014503001341a41010061190b19245030014910751000005440e8148140802d404815030f000d42c1c0d061b802071005298420030210200881c400030203600d081824007044900c048402024511031543c1004441c0307954241c042c0142003903804c40d01440c540100481ca07840103008950a403040541854407040c600071084400b42e00090800ea43d0828080e4003240b00c0e641c0150040c004d50051051035140c5452800807180c290f142c800b1200c0c0c446044c140e80041040810507243d0000c0350f82082a26030140c0b03070050703024101d1800007460300440110000003540710420186564080001190186040c0d1014808808188440031f54020a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 524294325 1250 524293075 524293093
    0x3100b130914041a01150e040f0f1415060a0f050d0213031a010311120703080a08011a0306030703020934020d030203090c060919060e040c020d0c06151a040f050d0302 73
    0x802010400b87d00c8401600c0026003440625501d411550001143c00b51144c843d1054180c01c24044902b41d0800344502c0c01c080349030142c0d0b000407554800d2142c80014004004100d440682c055401d83d00c640408600640d07035400100343c11a000d2a90740000c4401c80916071716400520f00c0c01c0b41550607654400518001e072004242003001e540c1004111113414480c0320380110000300740e10058131f1284801d0f120000117504044000c11545180c0c582c1a101000900400c00250750000d0300324112501940c444c0b000f61140d008010310a951181d480c0d0030100d981980c00382c0411100c0400000c0b0b4810b0b0b09840c0b103421284000c03826403000b51451a80c50f8000421187c4500d0134a005000c3c155005184444540c00702a14403010401d590003c1c0109080c2e40383c100d51810300f4024880004503c1c4050b100c0c80c110501c01034000715a0010113070900f41d940c4648802c0d092a00c2c1c03c46c01a0003101c0c0080c3c41c2c0402e00c1d40c10011503102c1c4c05032560516603080d00040e24244805015840780d07040c1c003c1c001c412 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 524295575 1250 524294325 524294327
    0x17031009180f110a080d020303040b040f021012050601030e1c2106061b050a030c051212040615030206031803090a090207020306070503100b130914041a0115 69
    0x200d07048521403510001e030501d48000400040409803243d02c00c000082450000500f0019006800d41c0045940d03001914146c08030380e4040120b0340d10980c0b21521076003a454a00785102c1c0303d404220f000350031105040206d02204e40100c41e00000001040080c0400d50381e9000440c2611441030b500c00065101ca003030500400c00408015840c4182480e2a20f01c06074062140907241204c1f0304100426541e070b003402e015241d40032810038000c40200c2074003005080c16a965a43da800d184801a08220f50f01034150104841800310724000041d42c20155103a589805c0b00e14500ea40554040710b025107020b103004503810f0030014034021070780c0051040b4190368440179a030222013880000c542c07060104004d420091f54400240f000903041103100103072580980d00c145840c0910241c880010703c0390910030416905080b030307003603029170300c0e11007007207840303000040700c00000314882d0b00401d0310581040321550031414908030179417041340100d805042c1d00a290110f500c1c01c403006e000d0581000030b1107030900901 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 524296825 1250 524295575 524295581
    0xb07210f0b090a1e09020d0203160311090c030601051804060b040e06030d0c020915031504062003010b0d020c060a0516050702180423210f0901030908040f03080717031009 75
    0x640090100c000e1031fa41580000d0801e039040b2030075241001d5138103050051140104e00e0034030245040e14070400d40d003803000896a42e03010080242d4104480050014440c4482c15003640010780301500502800380c840360440c64581050045401c2c000e1400300150052400203a80440c19040380c6420203801041c0d000c0c400040801481d01c01c003030b100b203014400703075440403c0049620900b500148005060901c0c0400c140c0c0e41c0c2d0010381c0400742198000c1640e107014001141d0444006540c200e80d00c000c510a220080e0281c00d102c2022030003070404200d00011150003d03841044803c400d995482c2c030020080d82c003400b03401d0000c1d40014080ac40b001e104110075a4494020b130141304d5808078403803a901c080d02c40c030080152282c0d080d0401510408050120349502a01000b02d401c0c09042805c5c043c1800d0701802290056810581c9807079500051120000441e4080c241008816040548030f060140c01c070f5100c01c030222141d10154509882c0207407002d042d01d0090301c900100f20300d0245041004005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 524298075 1250 524296825 524296841
    0x2041401080c07050a08030103031704050706051e0409060f081f050a060909031e11030306102304140612040f08090402070606080f07030b07210f0b090a1e 68
    0x703001001c20040c3c01040041100c580f22601c1042141c3d607942c114030300140084000c11071030000072284010300000071400305000e403d0724000e10b80940c54a1110f40491007824000701a4a48000b0001e00841e00340705a411042c1540d070818205080155280140d41d84c61340c1d8406035060001c91100d00c2400380341143c200c16040890044003203070980d2540e94401c03c0340e400300c5d42280030490591003501030745c0310360a91901e603c1e0325041810160385200003481d26407000a14181c402c2c400c1e8000d449603240541c0351207031400f004800545098280c0e002140069010f8051503400c413400044078005450b20000705c8032000c000050b200415183c41e60380710f4840d07101007001c841d201b0091003da442130300d862010b0101c2d203000c0d21004c1070301441e0614044c00c0c685641001205c0c1c0d00503190610114910010707a541140c13040c9001e1201911125045400703401c00b01c00b04100302c0c00d240d86075684900359080260110f408554481d202e07101d80b038409048400c0c06170800526142150108001d50603503000d444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 524299325 1250 524298075 524298091
    0x2104030215090d17010503070603150e100f1a0d09050f12070606080601030305160501060e010902070b18071701020d020c03070c14301e0c040204140108 67
    0x1203020001040150000000c032211203060f84600c003442007466009001c10300020740009008055410305011030748500441c029070b070625403180d11071941d44088020039801082031911030015803c1c034806c8000071070b03007510900c1e031740304581c82010500d0b251140a0340c0b13220780a45100c614280c1000d00e10000340c21441d0050310b0900401101d2000d80c641841481d0302c140141c00c4444c0d07a01035910b070aa088500d83d8001e000141e20560050000a03081000c0b2480a00c0784840c01112003000e2600901400071604101c031740052105c000504503216070082c11586108090060640d5034141030403c1c1d00d0244040c842e41d9030b00c40ca40401806560860350302031180040005450400100d05080990f0b0246080c807000f6880083c8600502002202c1840509890001c480e860710b640c0001501014001e40c0d422282e04d4a020407095100125009840c804600019120b4944144d050410740c00c01400500100d0b0081e02c0c0100068030301072080305d090341d0442d03c4000050b00120011142c69400401c440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 524300575 1250 524299325 524299333
    0x501110f150604180206030a0b190b0a030606030902101404080109050a0b070207032f1f08060121020a0306030c0e1501090806150f10170c21040302 65
    0x1103160281401921114800401100d80d981010340600c01203448001c50811800c24220003a40140d4502c800c0701d400c040780c0c85010a5804503174000420040c003980210740c2c2000c00c9600014010a14000340084103525201007141c130355552802e07803d652040350000d43c0400801814809a80601150000d07808110041401d0a413100844c508440e100720701540c0c0c6a0060a602c0100407443c48581d030300c40d07228800f900c511303880c5544800202c04441e01405060301440c2401005c0c445506c600d018900c40140254101c0d1540801142420049501c044c0081c0d84040040e006502510b1102491040c0816106400782c00c0c0c001d18000b5041980c5034004c05407240700000115500f04441d10281070740c80070105d03140c00d0131210080d00c4001408814140b0220480421201d500854180d5200081180094482c400076001801d114120001d035640405500c801612496100301848010540082c01404944400c100c0e046503028904200300c00c00703a445005d5000d0f0610005064101d44240129 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 524301825 1250 524300575 524300593
    0x30b060910150c15060803033c1b0306060f07020d0804030308070e03010c0e04020903120c0304051309020904120203070503040905160f020d0f090306050a0501062007050111 76
    0x244812201c10421900080f0a4190a401e105080e2410b090302c00707901c2c03c10072902c0e1822031800d450703001c01081d1050b0b03c8444c401603031250300004980f400c110040d003030580201c201b12140d081602c02c02d803581241801c0781c42c090b04105040800b181e0080038000e01c0d1606100114060b460f1a03030044804076006441094440009030070680508055446501d814a07546454500104045c480c107191a00c2a81081035580b101ca41007242c00b003850700c040e0790146e610186200400c0c90917925040039401d9440000f14a503090400ec00500140c80307048885210f1054003003602c02c2540e41012010798880710100100300010b00420078242d103000c450040d24217082c01c0307880b040d04642003940a610166254020482c0c2d02013034580314154800a4244401c0622540301c0080d5a0148180c40e0f0091040d02d407600e0100b980210381c8d60004550041080c801c0d4076098110b00088d080a01c0f030704011502d254848541030072050408060001d50034004e0040514040046a140f40148560706a84c0078254034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 524303075 1250 524301825 524301839
    0xc09050d170c060702060708130b0c091306051e2112070303050f0702030313080307050c0a0c0510110c13111314030f07090203061504080703110a030b060910 69
    0x82d10318415140e015000701d2500420203400c0030001000e0204001d00941000740c40105c410741c081031140c01c0031244040c4d6840c2d0085462074071400040b50740c0301001c980300e074040741c2c0c03550005816914166200e0741c00c0c02304640b01d04812446030365041d0f40095582c2c85214403428100880c1c00250070401107899582443d800da6210b82d1240e84280d0001c0d480c0c070700304804c4072515000c1e5600b040341d43c07004502d0340c40c0510240541035404900100040701c00808120300320301c01c07816510b17000100130642d40303140b00628240000030200e20820b805981c400041d9090240641d2442da01c14039944081c04280b0300c10401c001b02c40200a030302940955840d003000c4402c141d10005405201030401c0e00f00c0c074150801205030009503010001c0c61080c0d000307003003046c40d141e00403c0031405c80320b03082005038480e00e0b5140010b1684800400c19012800c02140c002003064001a0100c2201c1c0108400b842d100001410b11204805900025110704085000b01c1c00ba4203103612855804258600c40841480d240c5c1c00f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 524304325 1250 524303075 524303077
    0x11b0e040903053f01060f08151804060b0102012f0403060504050a050f0607052b1b080106020307030503041b0306020c07140a0f05240d050106030f0c09050d17 70
    0x1500a40c1142074a84080c52101c2002c02100d09801101e4100710541c54403038014007450003010300382c08001100c00130460071900c400c02c9101051000303008007000e2b00ca062003040c0300001254152006800c0007a0700f4150750040c462048400046c03684c00700c9461104c0724175400780100c010700170108041000004040b92092059a019a105a001d0011100241400c40c03511042c118030400c81e4001e0b009001c0c000741c11800726002086200707007615409401c5501c20b0080800e5400c20762043e4200201c1246484130011960f07002401c985410100e40d0302c61400300d0b0341e402051401404182c00300041404180c41048507500b0180c4100d4010583d6129683d810a981040300040019401090103012a481160b1b002d401000150f0381058400d1a040c650000100075200f01401a19950003613010310317001d00e40f102410104a00c1c2e00d0b96901c0e40c01042d85c0100024031888002034901030030680c400410313000310341100d1032643d113088481e4104401c001c0c9100e6210400c0706c200880b550ba01c0315007402a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 524305575 1250 524304325 524304367
    0x61d0405040804060206060f0105040504090303180f030f02060c1206030a12020c0114070f031b0b130b090307051203130f050c012604061e0e0609011b0e04090305 71
    0x111029101e5252131406842c004002d17041a1081e101c401000d801790340d000301950204c8000300d40104040e546402c05a005050300d54100d030007019000d0840041c0003d00e548a03811910a56618501c0c0c0c107101e4040380c58070815503010f04d56040402c9510310107a540030306c4942004005082e54050030440d079030881c100c08420749100c0580c202b9201e024030366070400403203036a017000c0c880c03514905011550348440e4055281c4009051003032140101c0120900000a610b03d15440880340e9601c0c02c20030f00d42c99401da21000211080140c242c0047e00e006000700580d4045580540145141001009584001d803c001c001003000007480d01e8080101d25000310100007140030b00080c04c20000c801000501861100313546006418180c0ea0444400c4620b903940e5070b005801160004003044000d00c00e011540b0031059130401c1c80c0c03e11000310380c08100419058004ea07070740c1d002042035440008903880540600302024000c207000380030b004c100e03007013540003901c5280c0b207464114600300c00f4404151190100c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 524306825 1250 524305575 524305583
    0xc19170601060207233c030d030e1e0c030d030e0618150c1306020606010e120c010503060d120f0e03061009020903070b2709010807061d040504 63
    0x801000860340601c407140c050000c01c1c07001c0c003c0140322020500e000c00c0c551505c600654000d0111800340b841080406c0c0401140c2c0c0c2154503c3c0d0b000664140b280240751050b42c1709008404141401c5e501074850052100d0005001c0d1882c4c0c3d4a10342a03400355070301d07906020030500413240082c40c503982c01d0001400e0f00305c064400003414606050030602c0c01c2001400413011402c590485a501880028aa040042c00c01561009039980c035070b4448490095401064148040340c00105401d50040b9071648a004280c0e21208214240001c0180b82c000b01802c007011030701300204640381548203000a5a0062000e460311080c001641c2d16030740e041000c50841000100750154150f4071680c483c00c1c040211074101c0081000342844c02e03c01c05201c5461041990311030703000075182c155803024000b0100070300c4450034198030b1b80c41c3e00049a51158280c80d4400301d0100480b1805460316200b1409070507664490005c080050510200b80c502490341d5541c14040007148098014542d85e60103420320035482 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 524308075 1250 524306825 524306833
    0xe060a0512120f0409050105121507030e0715122009010e0603091e01060f0b0702040e010501140f0301020f0a030c02030d0507020a021f0206190b0303121f080c1917 72
    0xd1700c01d40f0782c01c4541c1a0041071180d003071044000807881001a10140c100f40e03104003012203840710a0207030000c09a54008244a0213018000139442845103a0a002d598181c3c54404508510080110803200d441c00d4911605911220201082c00c1075009011400c4040c18108060740c4204006541a0400c0300d40b2102607000c0740040446a44041600c1c005611410090086504003c0314000f41400f03809000100100810480259540d9810071184004000c00170041540c5440c0d01d900119070500c8024003c01340c9032820010342c1014400c40742503800c0480100d0401134840801c03406000b140f150407003140f0050183d200c2c8182240306050050b9440c0d001407c900711184140b10007442e6914070304240d15102c1c114401c640750003254040e4000b0307407403000c01c100000390b85809000740101036025406100204a41818400003220070340110500d600c0507102e0185004508441c64660042a0258214540c2040d603418141078243e5185500da04245505455000c07520103d42c4690100e5801d0380 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 524309325 1250 524308075 524308079
    0x80a0f021801021c021b0f0402180901080307150914030d020405090c16030f180b03011d040f030302090a0e0916170703020603100b0f04030c0e060a0512120f04 70
    0xa01008010420004c10071551640700301a400a034541001e4450017864031254500d09003103540e01c03400343d55400f10040c001c42d220310900380381e40c5c10484d201e0320700781c061030709170780080754144002050345c020381c0d07000200035080d6560030461000382c1070400d81101c098200c29501c440405050000c0c140019060344010b072180d150604110100d0405030401445207810484003000e2840e1581e009600c0342c150906481d0080158011a8018880e50040400704e07207810b0040b83c0394007410000c40c103d448008014401100300030920000c4901554014140b105800b1210001f90081c4c020b404404401002c1401490b40c8150101076140c0803220031b40190004000c0e144040014010f0002900d107031006010b450454001003690346195000103485080d010000440d143c0d0555201d0f0041c2541c00d010350340382c0c5644400c0c0d03011900180030032545008a17641c0800c0e038020f1485030340c1c424400141030003121407400c0184207100000c3d4021441e81d004a1a80a0700f442101c8010840080c0b100c000725610b038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 524310575 1250 524309325 524309327
    0x110a06020f090a08160905100605090136091b080a09080d1413151e0c020307050f0303130f020102010b030615130b06070201110f150f0105040c0c03080a0f021801 71
    0x1401500906d41c903c2c0303000c052001c5844420129410342d506ca01303150b0756a441c00001604c1d00d80c0070016051012006c40e40100746110040d1141850500584c2d4034507606491385000002c0d10340c2c3c80710444084420b0001c40862a1042818540020b0b02a800250288050700c6440c25903100071401440c441c5c41c3c900b691b07403510085141d02d50240c50a80810001c07201980c80d100d03013282151740d00030741c1c1382c03503940d000103025551004483c4058207400c01c0200344403850000c1d40ba40c001505c00e66440c001c1031403d905161021044a105000d02c05800e0703205215941e030344600c0303000440c0c2a411036503103150111458404000c9180a049101c0c1012034a41d0b010b001c0104c001d030034041000940307082010301c0c42151103a0f4141e600700e0f44d090a15850a40c07640009515000c0c5020041100d0f1095144c00c545c4401204c210382c2c054040090310881d6a070f01c03a0b0a00041c0d441c00b4825030000745191902ca008244101007558100951040210b84050140101e400347d810829040c41c186d07a0307003000d2040755 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 524311825 1250 524310575 524310613
    0x8010c090603181106040e010e0405120c19060914550803010902030703060e040b060d2a05040c0201050606040b0a0201020d05090303090c01110a06020f090a08 70
    0xc00442c901031080180440d480800010064001050044c402981c2d8510f50b59210959002d0726414610040390342e55880b501420301819a4291210f0003040101603031a11110111220304402d10300811502007502c1481c817007071540b0f40c1e0641c0e00580d205d11403800180859081068074500e50000c012541c41450600c243c4129004036003180c0c0b020300026600e0850080b070030b6142d102d50450019400180380748081c0c0b661100c4000400c02d002c0000086007000043e07000d0340c01424195820400c00e07031202e809072942a0700766400b800c0300c4443e60005071149002d07005140e840303106440c10104072800f4a040d486d90100380c0e4103100c131300403403036428003050900307204041800d00d051000384030506001011074014072890151174042600081e2144501d03000b501200c11340307590410104894905181281e40325042030b64549400d0044001004081d0300c42d004102840b03020401601012005a03074010083d1f201d10708041c0e1510003444600c07e01d9541c000c46400400313004015005400603e810b21001c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 524313075 1250 524311825 524311829
    0x2a07020a0e09070801021e07050712150b06070f06181e0209160903020d260315040c051812160303080c030c07020603062806020f030c0c091008010608010c09 69
    0x41da03105005010500380c03404000400c602c7e040410b80e594131176a0510509114054010550b0905403000d03140030070500e80007000c0004a1100300300a8001d003041002400c1c8500709018004040b45000c00000c600c01c0e601c181e080140c80c10326200030200c16502d103114400c01e00c51701003100715030f41141019400d181c03108036444403c2903541e02844000d10005081c0e0442c500010f8000c86000501c90704005249010811030000e5541000e2074140c80c0b4014001640100c0348002c2d0f446103541d07200340d1420140110100100307181c45044c281402580c1c01e2420038041d00400380d12504800c0c000507298000d0103e604070008120400d2196415400c01078080784000d00346e400349840030020003049080d5074041d80c80d05a811601c2079940d86a000010341c0f00044001040d01d00010180c040194400039100300d030498401e034003940c14040031980380585034040d40582d10403d400c500c550070001d180210700c09922549210402c86000c4c1c80d2007000342101c03200d4002145583d9601c030050485a0050344141c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 524314325 1250 524313075 524313089
    0xb18011706090d0e030a0c260c210114012c010303021005042102010f0608150a020c01090f061415031b0a080f100c03052a07020a0e0907 60
    0x2a078180480d210b9a500c1c81084070104000d10504c10368079956061088000031901301201007081030300d840d408402d1203000c851105403a00108244410010081040c020805008084004139884d0f00c803940d2081038032942d04240c0d55079400c04400301c8000c1c00900c5000e02580c40c2c28207048000c040f081c0d03800c241280312844951940f03c0c01000080c0d03001910310080700d200d15001c500c0e521140342280c9a0010002e440005070b02c400d00070718445505500204400082c98018400c2a503105d130b5664984000803402080d04440341700180d5080c105070000e2002400003400000c4021564a5040c80000e01d07060803290541c80c1c2508800c2c0780300301b0401c103402c04c2e00d02000c08480510f1200007551048600344034040640701400c10300e0a60741e080c916078010000603040d54009464400c9140c0c8915424401604151500c00a440144d110b445840e20400110202d51004004213103040100c00480c0011000c10384200b0000c0d0049e00c840c50340000502078540b101d02c143c04c004081c14102641600440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 524315575 1250 524314325 524314333
    0x20708271302091305042411092101090309090c140d0e010912050d180804030b0a1514100f08060f0a03020405040308100f1505030a0b180117 62
    0xc5210380c0d403036000c20707140350920a006980300c0104001c502c440c030001038102c0d0070034070b400c0c01c21040c0061003030718040500381c00f040c00403131480403082a8200c4000d61041c6000c0e070710070320a0400070b00744070410b60f403a4141400780c540c234081000c40340f81c00c0d2015030401314002641750070300300302800c1c0c18001c5d0841415982087e001d00c15052100d0312950160000da000f01a03140d40045a100101b0f42c41022032507004400f521040242343e00c0500564840303945000106d14050360050b1071090b2850f020b491589c0040c0b140d142030301d55100c8a204c1c1c8409025500d140f0b039a24401d00d20010b039030f02510010224030a01440b44140c601c10495040382d50844802440084160b03000c0b0f07a6441120142d001d90201c23140c1e4903183c01130700400c034000300640000750450300d00804d000c2819002501c0314400ca44134075400340590b071900c6807420814a18030918040102500e41188460f02582c0650f03441400c40e44000b5541594a002410311010030001c01046c1455000600000c044820f480c1c000390301c001300030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 524316825 1250 524315575 524315647
    0x80105060102030f07020d020d060203060f040e0703061d03210c07030c15020c1905010e03040b040311151201140d05030315061603260f1513020708 65
    0x103034581c130031660f079248130b8000020490215904d61114085103078000e41510760340030940c5040c500070340c4280c64207803043c00114481001464140203000c40c80c4480000b07022402e182d90340e41f101620f44201881040041038484003203c5004002400c842086a20121100081c00c85822440c0c0750281031031001c0d180401228011170b4100e50b030b0124455201c421040c4900b00c2d8090b010090085440150250085421080e2442001080c5d000e11900980080102c00c501d40c00072035481c400e5103d86190a241400100b000c1104a0300e1103030783c00d401401d01c10a082030385480003a10340c884140081c41d022454014810080c000d031140c1034041040d5402c0c0520240c41c2c5403d44d030b900008140c00c51180c440c840c070035119110314040d41c005100c0260712402c2142c56140207806502008042e500d0b074060900f03903042d042c80c50301c41c03240142c02e240c3d0820501e8850250144c2c0700140e41c1c08403604203c020f01c504514000c1440100050380c054903440e0b07210780e807101d085541005628000001d000a11000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 524318075 1250 524316825 524316827
    0x1b0f06150509060d060e0102040e010306060b031e0a090206030a050a0f051012050a0206030c0301081c0c06090c0812041802040b1210080304181d0712060624090801050601 75
    0x388a07000f540c210b4110701c0300c41c8107140900103000c1150509145500209001840140d8000d29034103882c464007003880069120818680d49001c11180351101d50300d00001e840c1a0880c4060b103c0d0800f0240c540801d4084c410307008230303050398401d540c0b00103816030300c40401c00d106a151084d0b00100304a14028481c9003411400396240c142940075901c82041c044900c030007044020403400c1009030307004d0105c5440f45800c800a0303000b6002403044903658007605082d80d5000141100c404084121a162080c0e03510481e19404001d140801040729203000401010580c40c40c1040000009081c035190310750340341e0504091801d039141070086c1e055100d0043c0020710458110300140c620802c480d11801620383d5030440c200d0401005684881c00074000040e01050b1982124840130818114010030700901d007024002c401d100f41542480c529641162505106a140c1d08910350701c0709014050107e40c01b81c0707401e01030710b0b880303c0d03400307204c44c80c0358442c2c2c42e0f9481a4204104000911a0000800441c601480 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 524319325 1250 524318075 524318089
    0xc1315120c0c0506190f090302150c04030b160203160803010f0e04150507021608010203010f0e151210060e06090108210d0e010e010b2407080a1b0f061505 68
    0x5c0301484c9411250030300c5058504d5a844050f404105074001c0c0000b48060a004e901d400010b00c1d480815032902d4002448002008211022658054251150741c0c3c1ca104d81d44c22004c203840d011500310700041010700e0130090740b2442120316134041e0b200c069695142900410070b0120a50080b8000340c3c05404002c0814445003000140444a03203020880d6a580c150403400d00c0702c5051074445003031079001c02140c4446c055010b141a00e0180d40c0700c000850700c810920645201c00ca803408200052100702a2480c185a54502404240a01111802228142c0e4842910203d03000800c42c8005241040364915044010742d0041100c040038080039080000c00c11264014071a1501000d44001801000c210301c6038030805919500030000c104062514480701d010b8500b46844600c0307425078030040f00e00d40b00b88601107551901d912022a241030003903130701d60310382e9040340c0c0324881444281d100080c0025446100e50031541e01c41c170403041c4042c0c2189030250840d6910761408003100d01072501403045d84c662007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 524320575 1250 524319325 524319331
    0xc05070602070215030709230607200a03110301111603031a0d05030a1404050307061b020306040302030d0e01051e09011d0f0c180c1315120c0c0506 65
    0xe0340160303860445001041d100f10b40400e0304025010000100145a503200c01c2d1001654511104c41d0101c80040c84580c90160b942203500383c0c00081003250700005410351134900024810a440030691080344400244403c45951043d1500080118243c616240030b1007111100701c00c0c001860300b4030b541c1c6503a1510300109500300030181071362071129944d00d41003102e800b2401040280b41a17a80c85032480c00310707280e804c064200000b0900003215481c40350700e500251400d5950140040100f01d180c06412100780d0b9040340914400c200342c28070403016880c21702c411441107019800a50f601c0c08001d0541c4100c5401c090855110b074540380c144582056040d9821400c2c1c444a941d103003c03501c07283e802d24014201c610030b40401900440c0c0300301001201155000d2a0700c0c084054600c1100c0325801c0c031440d0384c0104c85170100101342c000092011804d40c801703890344140901031501400e4130794414040d50424206d80390081000180c2c003a21004031400703901c800e03004d2840c3c58420b0303c04a03910203079115005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 524321825 1250 524320575 524320583
    0xf09060f0503071106271b0d0c1a0c0c09010b0a050d0603051e0d03020403050a061d01090506060a060201060806011502071d010e130c03140a050604110a0b0c03040902090a0801020a031e0c0507 84
    0x10308525400d00c801005400046c041020080c0a4032b07550f051000e00607802050714601a00800b040182300340f811100460485003801c61a502c1d280d080c83c01155075034050390201c2c20095560034003102280042241c03a10351041504104d1207088282c10381454a4031022441040500401c000c1c0002040407507205800c0c2c0e0f10840100b90b0251411443e02d110048070b809003001d43c80c2c84404400d01c240000c13014003d900940d080702c14252a018200e01f60b6859018824080e13001c0c1e0010000913044401d010450001403064800c1161500d0808a504800c1505e500e0344503489801404004c40c84500c250304035081c0581051001c015558046180642e4032024000c0c15404c0003502040e0024804c08820b9a8410203843d4149010319261100c40d011052441c001c0c15103c1c008200311040c40120b6581e800c840c001542010305c0c0c070030120301035401001b41c150011301500c00090140000d00240c9a00092601c000c2034a08001c00503c00782503541c52445186800c0a452140c42508103003150411604 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 524323075 1250 524321825 524321839
    0xc050103090c030f05070302040b0105250f02060a080601030b010c0201170a0f1401030b0601180b03040f06020f030a0b0a06140f090604150f09060f0503071106271b 72
    0x1800c1420000185520181130031030022100c004105000c5401c0090f6842290700700030b41c0308403100440309402a000c104d02d040000d48060b09848200081c0240f1880c4141c0c60305a06a00c0e0382c1c081490390304424240c1010502d5801400040e6030107005403006240c0071310f4011080344d01d54000030b003d0010b040d50010000000c001081e1100c10b243c014400d45401302c1d00c2805200d07200080060325070350074842070b5040071114001c09c01a42c403441201c0c2e85070050f40c00d441501800d1010350174269101030300803940c8245118080001403014000752207207211182e5510b0726407800038031b070360291003018030a01e2282009000c14020503800080d11480e011007065020745a94920110240611a00000070f42c0b1450200d40060080102260001e01e0916503440e1520614490f80640b50420030b0b001e440d02242c65890700420151040000d10b500c00a075103800300d6106203000c1a00e0a0000940e41000005440c100c02c1604600041c1c608503040c40c8440101405100c0c8070030021503014414a4a1240705 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 524324325 1250 524323075 524323091
    0x211519021605010c050d052d1305100b09090d051602010c350405060a050c0c0409080a020f0606030607140c25080303040b0402040b030a141501050d0c050103 69
    0x360780390314200407992141c003c00100d81280300240940d0060031003140600d00380000103a00002450f03030201e110304c0411304d072a204640300c2e260121038040145400344403440f041d855404075000b0003180c801d821b8180340c001003400002003401030040c001040b801003a8048402c00550741e41c08000c40300c6520a0301c402090000e49880100c07100f01c40c50130301070721030042c1004603104420405640f1a810030301d1450380082509841ca8400c90b401036100d044e500c50b070144840300302030b0301503c01406120460703001c2d6211000c00b140010201c0b41c00503400e5480401c0402c0035a005a010006140c40203044070040446143c00000a07a0381d240003401c54040102d00c620440030b01a540050358100c160150903558201840003081643d044444e0b0340d00c8500c07500000025001e040481146d02441e000a10030f45603aa0351b03000c1c880600716508440303802d8402d007500c15010816070054488071910703001c003400202d1205400b00c40321000c1a0041d51140f0001c00b113120015400ca200501210000e08010650310 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 524325575 1250 524324325 524324347
    0x2031f1b0e0a051903020d0b0a1b050d0b01050f070b0103050f0a020f0d0c3c082104091404020a050306090316080405090c0d0509070605071b0521151902 67
    0x81301c0c544c0000c4d0003505005143c03007002501030010340b1424074401c08120240b00d1251115940340e8054082c008a04100a12a1000c1558121320400581030402c071707142900f06448140a940102c07820f0350390841e03c500502c20028140144122113690b4001889004e1300d60300000c00c115000c440203440703005100d00d401d04004804a94000a000485188800c2601041031460407860707070412003400e0003000260b102c803016030111142036446400080031050b82140340b1040b000c0035042d020480351400e00c40041c041100e070292003510f00042003200101c1c20284144007d050054000a10a40100c4100815002c00005448200d040c80c0c2080f0301d504c840f400d10003106e2269810241d08408840100f15261061000900403801d4103e41008250b1364120324617101c00c10380c01203400155040245002007141c0090001008035540e0300247d00075a05c2000480da05e00e011003504011800c4010040032443c00d000d4062088256a00c3c880145800b0000309005450042e40c101e030154003048021600b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 524326825 1250 524325575 524325619
    0x51e0603060d1b1e031a0601120c200f06060607110a0605091009060207090f0f06140909010902010503060603180d020f011107020d08030402031f1b0e0a05 68
    0xb05400500785080c0c1c1d0390035041d1903242c00b03441c0544c0e130496030f50020801502c114000e0036011a90007070240081d07810341d4030582c2400740c0b01500a60400c00058031240201040b8410310b10700d252103441d030102c044407800c5401c000680910014495810900d08540340b40700c041030403030f40420200e03404d90344c0349058540380d00600c090030041c83c0c2164000501042c0035812400800c5002030031100302001143c0d0300e90031564400b240c0240001600320704002c2000e0042c58014541d0b84000e000017149180d501302130b03402281c0190340b01c030394680d0040341d074412541440c0000a8104d80700340000c1c007203881070741c001904911014005ca40a120000300046030b00b4503c00156040d503501c4c07800c2e200780c00c9504500940d07800131140c1281d129441d001000e03200e45044c0048800a95015140d500d46031460b88075082180c00003403059801d03020395000d051044001c0e61821000060003800010200c02c40038400314035403000c0780079005208620403010542d90352a1144011a202298140c02c1800540001d00d25 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 524328075 1250 524326825 524326849
    0x2040e0412050423120109051f270201110601150804080405090a0504030912051f020c06010f09150b070210110312040b0c0406080c0c01150605090a051e060306 70
    0x4542425940134100e10304101070320700d440b40d044070fa01c0b08040651411508070740c8911030081659204c60980c98481e0724210546802d16503480001442030044020916030038199112800486002d01e0300c881190b802c0000642d004816100404c140d40c10444240c03900030a03000010b042c004204009010840082c003100d02a0002400c49112070500c1801080601015a0300314040b4000c0b49021800800000c409030800b6000b500400700c4542c070740e60a0141101c01100e0200e065020451980c202c442080018028102d165520300540e00d0613180c01c0441d003038819403158055444a0420009401c1c2c0f040e20344007601128105821881c50100b555043c03062001c0c09418000840c04030103581101c0b42c1030748164007440c000140741d9540c030313062042ca1243d0300594002c150814003080000900e07202a2060070540b40c00007a1405118141002c07200b896840389000820000720b21659007090442403000304403d945429445d480e109030b500c080740140d0001c1e80110400b0000a415a5072070b501100c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 524329325 1250 524328075 524328089
    0x2030a0c05120f120f09071e080d08100b120c090d06050c13050a030b1f080601030c060201140106050a0302130f0305070f0806040f020f010e1002010509070902040e04120504 76
    0x1550f82001007202c05290402403441e05410600000501c4038403001000d240310305444405005218203041c4002d1805c85241c81745c0d5007246408402041d075013010041c0e05810026511400024a481c0c030110061840e15000360643c0c103804c1c41052003450152610b035030400c8150000d076071030f500f084000c281c00003684140a0800c44c00e21080c00241c081c0031000b07001030045a42108501c6031580300380300010940e403100500706003802000500b4420368005a03014040c00494007070007556100185803030101c4c20b802c15a0500140710003044900e409203d281400446100080a00d40c074020000d000c81c0641d001840c02d160300050850100119030044001030904401f1881071652242030060b528500b42c000e511640c5d80e00c1c00302181c9031b100094030340d2040e031f4001243c8003034640f2740e0b00380010342810140c040d060042101d8100718990f5101404122901242d00008007132500c04d03056440c03c1c41740d42c000420584100030a000051a02006070750003600a8a1040c0b04402c1003412202e0303110b1a4001c02c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 524330575 1250 524329325 524329327
    0x9020c1b1c08190503061201060f031b08011410060c38010f031b0f35060702061006050f090a03151509180b1503030d0506180702030a0c0512 62
    0x55126801001441c011b0006554031b4400c8041e1001072070880780c050052602100080c501000014210042c0c0d0311440d02c4c2c001410407050f07540780782909507100204080c2c0c43c0d14880f82041025070040754400010a601d191994800c40a0784681d904401c445884502c8071400c43c101c01c01c0b140304001220548445800c8030001e80d0b03034440d084092180c860100b11403840b882ca02040c050081ca0301d524040e103c05621102080c0d18012050048401c0003110f0322000c0c6804e081d0707560304800000c2e101c00304e010b103001615082c688080001d00305407006040c00340003080c541c018080290321105403002c9a28600950b5510350040c030000b15030480030752005180140c1e240b43d1218080654000e03400d00e80c14600809181503c9103030038800e031031490200540c5c0e5880c21803644041341202603815000b4003d60001e000d205c0e42100400d0031940240505d05926807134009101c2c2d00c0c2420201c921070000f143c3c00116580c100400000d4992080c010410108680c084000081c0601805551001c1e01c240d602c00d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 524331825 1250 524330575 524330617
    0x31501031b05030f090616030902010210090b040507050909030a12090203071e050603160f0309020901091a060c070e10152a0804090207080405040609020c1b1c08 71
    0x4056a000303c0c3d5603a20a58071a0101da45170750005020342c003400304050412071200384280d0407002030041c420706078114413a08000308000ca1061007144902c900a0620000b45d1130a400c080c2c0c0b030804681d02c20350040b0803034020408204404820f40704102d10f00d14100d92728011030304503103002c0c00c84c0481c081d626000e81000065025003104107000c00c1104003c51141c0340c0c1c1d46204001c55800121000f808100c0c600480003070301481015032495084680c00c000522071120740100389408003d0b000030340320a03074803c030140307100b40004203900001004071003041c0741c1150140215110b10a600ca104180349514011134000c00385c40114030b02a100240c22040ea00300e868600805010031800f00c009003807000c0100300700d90341146d07400c4450203802a5501d031900340b51041c4030000394041d810a0392114400d000115060b0b655009520003442c2c0e100c000b580315031200c102e86003010011b04188001c0c1180600f81942a12003110030100350029000c2e03001c800000d4142441035100303c04006045040c85011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 524333075 1250 524331825 524331827
    0xb070204110f0c0d0f020a0b180106060917060c300f0a1d060c090f030a050102130501110d0f050c1608060109020a0e040504020a0e1302041a06031501031b 68
    0x41d02800300203904580ea002aa0385041e45d082401c050001c005820222410005c43c0189614503086203000781800410400c1613041821203900e9001440007070032841c4200319140c10100e00401500b1a9070182409052810380191544941c6148640084040303095170406400210922aa00b4071500603841d1460200c41c3c0e0410480c080340c040d0701d01c52800b41100100b0004116480c0780300e180c0c8006001079150104050941c1e0400b90107650302428000c41d08146032020f11501031201d00c200000358070b42040d100e40e0030b0f08444a8010034100034907505e902c450300300000740903200e0310182c0c10240709021004030121503038403030074404c41d01521810342100740c3c0300b04180500044400003401c0e11010b0342c035078154000382d208020340400095003104540403d442c01e0f41c07203590080d05c000c05035240c2558640c440041c0f00411551298891102880c4109609003030003200c9a5a4606d08100360000d58072001a56600001d030008001414502c902c2625034041d5111003803c4883d51a802c00c03e2035004c0c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 524334325 1250 524333075 524333077
    0x91023030a180201121d070f140f0607031128030e03371b0603150b0403060207020f0618010e04180213091a090d090303090b070204110f 60
    0x607440050318500048194848901d0b88580041d035030594a49106024011410014000d04014007080c040d00d4032510398961003c005840040451281c41131015162030316507800780000e0310307240d4024400802c4180f029a1680112941c0e40c3c1d15040500c03001e0650300340c041c40c2101403038500d841c4030703480c1521444000303100c803c41c103155102e6a07620507034810329428581c44182c00400d60b0022110a40902682c40540b541c17058861132400e01800c4412090310703220000d060094401d204210f9644c1c06105856140c010300c1e0a48282d048003050342031811a170100548503911015080b1036010030a9000c551f038030070305c2c20032200c1c0c000d16003910f5a8020b0901320b07000405240c2940855805020345150b03041074015840302e2800c03d4110485454981c091207210594074420144890740c4004940001e00c42c5880120707008880c4c0040009442c0c046201c03441c00c91102d154505100004000300000b039445102c00741500e0382c00b10390685807042032021030080c1c40090040c52040c2c80210305002d00301794880c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 524335575 1250 524334325 524334331
    0xc0305040b0d06140a0303140904020c12070506150604060f0302160303050a060e0f042613030b09010203101707080601140a150503060405060604150c050106170309102303 75
    0x118541c1d00c0342c0d403002000a01d040c1c0f0711004020230b040c82c9078144032500c480301816106001900141c5084030880d54070b13080040d14030504141c036030046002000e0100030000ca50b448070000858440a07804c900c0040ca881c0610711410041101d109100030790584a0740541c1c016090a0802e121081c10b43c0c0707409006420201ca110840501c0c2a9000444080c40007101d0b02807603041b03042008030344035611005550748011940380001c4085401a41d45640044010030500c4840900012641d0551628406080018082d040e80ba0b005106026035140c840c1c8000302128039000154101c001c5038407095003052650703881a0503034002c3c00000156072514400c0715505100450300e07910515100c0c441e9034014009010000002441400000d040e03040542c8483d81141008000c942015942c103040d0f802503055a0260001415020104041000074010703400a0240316140400e061000403c183c4d84e40200304001380720b2103205014800305406048145102d4600309556008011b0b0030726241d007268816 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 524336825 1250 524335575 524335589
    0xb19091203091b03170702030c0919061401050a111006090203010f080f06010e0402150703020102120f28110f0c0d050f0f0d0f0e0c0906090c0702010c0305040b0d06 72
    0x10f0740c1d81c2c4000008000d03400090b264030070b00131882d00403071a240c22800d030440d0000300d0b0140308000c807009142d07640001061050094a002101c210204010281502c845a2090851485091528509070707044400d80e01c886045103003151107041890b01c220300e031004203207190300310310319040002c201004c4640081d41640c10a002c0b07500032644d5880307059a585112110300c02d803908030314010304c4000c818a60075504507000901203400c401c02030400c05007651101e502200540e50004e04030002505410565510401c001102100e5103480364a008030b540325030400e50003050141c030f01c01d82e20055503844041d13240c0b01a02d0a9485882220080c14036501001001000e4810240f0001d5500e00c11400c450360901f00324001070500c1e000040f01280d9420550460040d1a03c3c0e041003a00d550261113060709403210040102580c00008043c403500000203450701d4050fa4102d0b04021005c5403090031100c0640e820300c3c221a503003410f03080844150140e504001110b00340014505454001d580194056130341c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 524338075 1250 524336825 524336843
    0xf0605011704080406050c070801060b040905060a0305060720010f0b01120204060917010b030f0c010e0901030b150117040f03081f05040e0a080708030f0907030b1909120309 76
    0x8490300141002104840043c0302c540104005d02c02c19200382c000c1c0c5042207165049908250700d0355150b81c02e680302d5400c550705900002c9030400180c4514000d46400000968840301d1550071615820b84404c00104100107020300c060402225138402080840c0020621000b0407012107000500c0300544440041d0b5400640d40c50347d480b038400d4051080b03d0444809850b500d40162400081440d00ca100c00c070064059560b03000c115000f52000d22560b02107071050000f0303051460418002418135100c4400e0540640d012074010300c0001d652108043c1c125649500c00000c0d10031410049034003028910003010b04450080c03d1104000440c0b40014400740720761201c01883d0340e42d807411019444010325003a00403080450410450405600510044c164071050722580c1d03a5580341c6050681c40b5100403a40000d001080040d4a002c0e0700040d60040000360141c6202441c0d5211400070510180c61803120940452318030540d00301c070354054001d26620421130a610030400901400402604c0c00c1a00e40c040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 524339325 1250 524338075 524338097
    0x6080705040516020a030c0f0503070b060108010b07050a02040f110a050408060f150f040617030316020c0607060b06090a03030210060503010501060219060204080601080a050d0201150311130f060501 87
    0x243c19010214680c80c0f50700800c0110043e490403110f080c00a1010b0702e44441c441c5c9110041041030009181044c01102d5400d4203040803800181445816401034124100600c1842d0000710003040103941190101c5020035105800c0e0710520007841218085081c560000414003038107a00900504120ba4200054942e20398078001124800c500c11100e941e0608081040d64815240401c02c00c0c54000014000103506500c480782420044030108000e2041d074804001c011450030b030046100018903151002c0d1030001c1191002c6000c034044d54000400954a44000c400191103080559141103802850f2111a40e51390401035110500d0001100e4002c0c1440e001103501e0605019070780c12549243d006290001421200600024404200311030042c0c0810001a441c001000f4250182a184000d805408418a000ca25003030007a420395080d0390401043c01d120781c944004c1501180c4d0849603500310103a0000010b40c040d2212658604421f1412120b40e11203049507201e00169182030b01d40a9091b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 524340575 1250 524339325 524339341
    0x2280621182604090c1202031e060d170a030b060f070b0a060b031305010204230a090b060a0e030a050714040f02070b131b0b0711043c060807050405 65
    0x20070400002c850000410082204240135400600d400e80750785001c1051110104015041ea4025207000b00c1c01d2001728030991540d03001c06440c90700000d0440d0f0001c8009255616103801c0036600f1400e1110302d50124a12465a009800508811030010070031641c2d814038100300ba00d80d4000400a40341d0300400c2c0300140c02d19619100d0308041c1d4200c1c040460030b583c0d800c490b039002c141000004440d155000e0000040c132030704082810307110900148542c45204000806d00042490307d900500c0a94200381750444d03180c84000c00c0340c0340b00c40d41d85400b291825071080403918210201078014000d109640b4002240b0300c000301c4050b1141c004450504c5690014860300060b03003d40c40f0007401120030407001c5180c0708901c50350300e061a4401c0308000d1b08420907128001c641050703a40101c00d90000007502000f001400c401c070145103a012a0208a01c0b00050141c00b003060080802c1101d115288540c400400d00103001282c3c1c6e070481c01014403202c1d444a6407540c5900072407045600460502001c10040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 524341825 1250 524340575 524340623
    0x803010e014106070b010b1b06160509181005010f26041403030103030f0905041a040903091502010b0f0402031e100509070c0228062118 60
    0x1452032203801003a00411107040c0780320b800c1c84090594091010002d480002e565108503600920f265556540c4407100701e5010305c03011074111a03520050f005042008108500c1d09040314a0b40d013140703007450725903e51502250002000d841000d00d1801e50508100c85088042da6a2042d62801c0c0d03a800c0c1d00c8003640009031224070032040c242d9074142c4000009281e459252042950180c01803030802164800781101608542c02070b04260002400752201111564000050800910080c0c40410011503901003004201121b0592940304030380ba046003805040c40303480400e002d03014400034400c0345171001a02034000d008241c0124058402da00c05050075241038070030740f4801c1e11503914410310790306e0300e200084110b400148903080d8252202000b080c6500c55a8680b8131554050b00c0d0f03000f07441400e00400c025100d07000c098a107031201079410382d540130703085004420031501d40d81003c00100c1d107100c126841c2d04050b11001c2109520303000c2d041e50000311519600c2039641c060340d5540345010201d001c410702 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 524343075 1250 524341825 524341889
    0x50103020309070603050a2703111902042c0c2b1e0602030703021c0507021905150a061505090a03020f060d09050106051216030b040c030803010e01 65
    0x1541e000083c0811140e80030340c000980c000b080081c006032003403d0915200912180502045201d1074022410042582010304030040154010003440d204080c601d9010060b905120024022a110b18440e00586001100780c80c000403a000c03129070a4075450440c81da43e401d0a80d015104003595070b12908142c220031140b640ba6098640c080c2010341c9540c031108014506410038000a1550f00c20410101e90944003075400351003103580159651310110103800c21245000c4466085a1420050044d010f0300060382801e44644400e12080c030506a05119040080000d5071710401c1007120f0400c00088403980c048001c0d2003515990451110901d10304907164024104000c0d04007420700003c0c030151804e114200040100141443d14207843c40200a003610300d100f101b00e03400c0e074440388280300c1454508840200325410b0001000e040c2292580200410184e100186c1130068007004281480b801c0c42c0203501840d002100030b03603a96502c00884801c041c0034848c031040418000789510440011007000c0f84 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 524344325 1250 524343075 524343091
    0x80a020c06030402310204060206060a080d12050a0f060b0c1c051215040f150b090a03080c0a0f0b0610080105010804240f090203011a031c030f020c160501030203 71
    0x7403001c418011030030600d00442c20036400d1401c40380d0b445179400c14a000910182032290b0140000d41001c1003800a020034540000c0030b04c0e000074800c0c40741d0711751011200302c1c0c5500340040498180c0b1303400c000b0401000a945491403090801c0320118404400b9001013080ca0307003540c1216080710100108012041c003a020000004204000d04096a21170005543e044603134500040000031400c000901101d62640500d907466460369074003c00584807241c0300c1c00030101a503207507144c05081d4000401d00169400020180d80001c140742d00481810080340010b81c0d480303030504410034507908000d6105401240c0040c81544500c81c00f1001e00e204c0d4141604840c03040c2c56018098031a9030b101c000400d0f0032090109001c080c1407522408000a010b41024080702210018881c081801418203440c9000701c08071800140702c1601d02151000603901c80b5070f0f4000f087e14064be040c103030001c40103440450149001d6070300110700462003144c04203c1992030400025a48804d60707554005409a0000b121030755 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 524345575 1250 524344325 524344339
    0xa050a020f03010605030a060902040615120f021806070c120c0e010f0501140307181e05030f0d050309030f0d0606020105060306240f030d1106341704080a020c06030402 74
    0x40001403080d00072201c00303440240007040cc152200654200004400b05d00c0340083c412000132004d0801a214900d042c0780100c0c015460b00d01c1600050f800d000c0c201050700d01407107001801008ac00354110208024010004544080314031030f0034407a51043e124010030600c80c895600028030b006496080b00c0c1140d82c10f031507103a26000c803500d03110713070b1070b00001c1418082c40810341c0354040000b1620040e0003d012117100e43c048200300c0c0518540341d040c10703801080c0254406a0401c14046c0001060071414082d460615500d0717031000700980c11030081100e44035640902040c00c200e031540d6500650150b402d107600800259594104260356040d0544103088220403000c481d01c1070b2003034440761100b442005040050220309d100d010a01c2c2c5080b41d071000e00011001c0301e2441403880c06100d020740000704014076002102a880f40d41c1c1002400040c003800e01c070200380c98051064000c88001e00420704940071202135103030a00780020b02e41d001c030100700018052005140070600d06641541e01540d000384c000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 524346825 1250 524345575 524345593
    0x8040b0604050c09090702030a09090504051e120307090e06010512060907140c0a0b1602030406030b04060801021603020d031424031c390804080a050a020f0301060503 73
    0x1c0320041c40e01401244078900100601010b60302c440080714010b2103190700643c0d0b1294104030007000130002c7e400c2201e40034100741c184404650000b6038141c080c11441c032142050a003000708076251200c04c0c900c0009103d03000c020003a03990703048403c9504441550080b00800e589020046500e4071500f041881ca54000c43d001c122903060041032036a2240550508042d1803001d89050151a001207412003135950000c0c00d00b40400050789aa540c0224440c044c0e10100c00b0310b401c010703450b400345021750420166940d01140300c036540c40e040b1000500c2948001c42d5116010008103182e02280003042c0e0140c1f0980e884404400d10074469070a030340f1300040b00c2c141c4d203440710034515015141180596010703d200c0340c10303000c103541c0c28400b003c1100d00a41d20003007204c01038000a45100e0b607101ca000240c80045021030200c207540c086106420405a12010b4840241d00c1d10b2266800307207401a5000d84205411042007200000b88000214000c88070744850b2148841054240e03440c50050f241c140d007000b1030f1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 524348075 1250 524346825 524346829
    0x305040e280b0f0d060b0f0103110f0d150603090605090c010c020f0406030c120b01060f0504090504020d0b011403060c090616080705060415050f060102191b0e040201020d08040b06 79
    0x441182d401e0300501c0007504a01401c0002e02c02818400141c842d80d558008008062401d024141c851440c20308062058401c0820342c0c4c061401900c40071144000000790404c03900407a940300b8083c104210303a12130006600c840c0000d00170591008211a00b62402000ca0004a0001a8044c0503041659500c800d1051740c1d0910400210140c11213400c26158030000c000248501c0d8040c0c060f1100141004d0036000c0381c2403029248006034405028480381c4c0e0000c5d0007c551000894040ea0081c000101d056100c030302c0415941c02c076812000c0e0130311251600110707040502482030800303090110110740b5641c0f1517440302c074103900c00c1180c0140c1c070540c10002280049044c2c0b403000921401071001504240380d5884003410030108680840300712480c0c01341d54001c10301d14414241c0100700c1c000c00e403601c0c0ca0050000f03940c070b010541c0c1441440101d09442020818280a45d1417074042540e000c10108ad80c410020b8003c40041d10b00f240503024000c0c80201c918420085a485250410705005103a207460301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 524349325 1250 524348075 524348081
    0x406050a09020c1c02030712030c080a020306030a120e210a030315091103040308180d0e030309040609090506092a130e06040204060b0a0e1306030f0305040e28 70
    0x24200c41c1c98000c2684012440a24105111300c80e6038913005903aa40c1c6a0340b618240c1c06800821000506142c04003070420107a0241141e07a1003601000016034071b4840d40000303454200ba4040082034080c00000c950749480c0d005e084101c06210903100e03042e1072140e201c407080194013420100301e03040d4800c3c07485001091080d040b030b0700010349032100b40308044d454000b948161811684a207030156400001e100c20075900900b480d0380300e02981d26001c00149911603c1c2c1d1a1080f80900004104034450316075403940d01802280c240c000d00030000c209642c0d803681d226024000762001910b1701d00030900019160340300411040801d07519540c4d0907251824850401000030a0350034155001042c0c07215082441035944a80307880b003440302d401841d1604e040e00c100400d03600c4542180909001c20f0007603001a03908124907152003082100c6600681034031504640c001c00c402e81c80030301005141031500080c590000010401c1d035858942e005038603543c0e000410100045146100c040035800b0b050122030850542c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 524350575 1250 524349325 524349337
    0x3010e010b0a1428030c0e060a18120309060302040b190504050a0e01051c02210c04050f06031c1407020609150a030e0703021c02010c06050a061706070903031101091e050c0406050a0902 81
    0x302b4500101b0700e1243c0c0002c844211a04516a082488007000c0d0502d504101d10300002c088602d010751802e41072a401100c280544129582c40d101d0b01080b42e201e0700c1c000c209035405071501a200c003240c1e0303039180045580e07402c0a119480c000c00c00c4880649190001d80341c0701f20b0032038014050741d8041e00d0301545d0380c0c0e5840b0301450110142c0600d20140d030301c59a590041901482c203840030b030703c96824100100b50410400e6662150491426003064414030340010404184664442d243c0d522050b050010490f2445840c0003160701c01d00c030350705989a00351284003400c440100f9035010414a0200602682c1c0d941d598000650b00c035a8484011051003500411040c44900c18500050100d10f15951541075030020746e060b0901907210f0b40148850b1250f83c850501400000300100141d00300b04202400d6454a030101400b00011004000c0c2940001d40080d4455603204c40461440b00c03001000a48007540c64608403214007c1c1201d86d216071805d0f0190b8000d039800103002e42a4a480c050a20009521003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 524351825 1250 524350575 524350577
    0xe0318090a06050d060b03060702150c0c100903020f060f01050a05040203040f0606090c1116062307111809060c1812060108060c03010e010b0a1428030c0e060a 70
    0x81c1c4000301d5980c40c4c0341030281d005845034401280700f4004408240c00c00300c000b0104001c55020b4071168002c205580302c203a030015610358085680783c0c50704408504040d06078801c000d01a00b0f001240c41055800074003680e99100c010151803031394442d84602d1400709001e10441d47c3c816404002030000380b601d0f500441e00241300e026022600d408903941d200070340e0300c2ca501204126558800380106560003d1515450502d501c001c1c0065a280503444000030b104d82c0588010414001910b81a08802040403085d010500302055118040303440d0903000c003101c0e40486409800c041c0d00581e01000360003440c5004190400141c641030740c031003207a81d0442c1c000348003061588480d160591f81c1a264903a05141d2018110054262581001e18061501c500074084041c1002c0400040040564074400941544c028929981d51101214800c0f0b40740e840380540a90007800c00100d0606984031030124403050061000c52405081c000c0398103504682170071365520040717028142884494134000c0000c1000d03100b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 524353075 1250 524351825 524351831
    0x201140421030603140601060815091f0b070c1a120412090b12010e130b0705071a070806040605030606010207050409260a091e03020d06110d0902040e0318090a 70
    0x2c1c0740ca51032807511400a03011702c0d542001e00144042540540d07200e51101c840c4010302500c04074540410742201e0300600c800c5164200c008203005001a85000c48014100c100780da035121b0102e401d010101002c64894609010802d1420304200030f43c04c8203072852002034220f01d140e1941d554542c0c00c41048400b15100400c2034018020465155074805046181124107158842c0e604265100070202005404002c40100c2050b240c40094803420626070b00012a02c0c10781c7c0c0f0ba040625061401c0c2071482840360907803201604001004c0c0d48004c0a601c40d50084401388a400e6480f410701da220b0905986450060b048a0003e01c12410550042c06442d44a40c168070310a060002d04105046910820310200d003100140003201560720610400181c070002c54080f5600c80c406031500e501045501c4020b01650a50b00088140071142d4000005034280701e40165940b0f00f00c0028000410754a14120701c500e00e001100940030100000740d8100f43c0c81d4030f01e40c81c100c9418004001c1800d02c010032200c0005d40f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 524354325 1250 524353075 524353079
    0x80138040b04021308060c030103020609060a0309080307080f061e15040509070c140601080601060815091915140402070512070b0a05060103090209040201110f030309070602011404210306 82
    0x702c0b0b10052110003000000301c1a030500304140c40d0b0070600c0113420000003581c140014000750742d44408507035002e5030858005603290002901a405020792542c060810b000c080100300301d9030b800000c4541b140000c01200d980595a0f40200051a40e11446c01d0304002c40c1d140426199041c4085c1000d004540c1c1d1280d1800d01340d580d0000b03a40c51400b1625600050200c1f00c00c4030401c000015035030640c13018400030340206c3d0b0500f40c105a60f008144140d40c204520400031401040109201d12940c1e0405403000d03a19240c10b84240903c0e00c500b0350860034452402e058107078603400e42050b0400303860000c80140c0940e82e2141c20000071350084442a6060b01500d00581c4014200e10000d0000301e00c01c41c1448010710b0081381341422500d004011034145130130f1011070f800507a28400425406542420000580d5108070040c924249041e07100c004584000002e11240b18070008101d004c490550f8000d2091402181d5200201c01c400e982c01400307070454104540c000e414212070303051000380c54074000969907 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 524355575 1250 524354325 524354329
    0xe0f010b1810020c130e061308070807080412030c031e02060609040317070c1b060210050c13090e0607090f060f230a0e01030513060906020d0c09080138040b 69
    0x10030740d00c8144c80003559100c00c51081b48090080e80d50200035010b1042064405444210052080c00d20007040300c00d00084143c200a045016a07000d045182e180010f46c01c030324503016010080c85c00b419004141c107903940000345500c2e00c0c80109000d8059029280c0754981905001c90003002410440c04d00030660740c84c41910055503e554841c0066540e8100707100c900d030502d8911000750b644645030385011000c00744005c540016000c4c2015201c2c00e800a1680d0325040a080c40d4000c8803160039461403611000a5803580c80d03048421010000d10030b840380342d1101320042e0b90f45441845481400e9800040401c04540209854944050701c0c0c200324010407180100100c1c05000c246084d51035240c081128641d080c0c0c402084403c0b82403c2c201004103082a00501006c1d8901c902d005088640b5440c00c4010000190181c4000341c41d000380502005051110142c290082c0e4050380390075602e4006188a45440e004400c04803070394290f460020710030703203482404000070b4028140d500300c2d442e81031610b015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 524356825 1250 524355575 524355589
    0x50903010b06130e06030d09060e0a091e140402091b04210510052802090303130512031204080702010c0f0c1404110d0c1205010e0f010b1810020c 64
    0x9608032064802a03e07042ca80907044154014004600031703440941c28003915900f200544065807814108880190520000035080d80703465084941e8090070301d010306109010b0360481c081405407024091102550311660030542ca801150041d60180500b401300c1e140c19010041c5030a04140342c0841031800e5164201135078480761180a0032403200d0804050818030a0510050803549a10f081c14080c9007400866441e0f60329007021301a041d480120280d049072080c070b074116000b07000b020341074a88986001d03020300654142481941d00030511107584035000100441107a0032400784007811001030f280d68607014841d4120326005c81c14061004100008240e02c1408a0a074502c149015414907007403640454a50703041000c1c2900482c00c0c80080414401844141c0f0001c0d4038241d0005100c98809a00715603d010f040c900d4a8018945400070401074030140d400f5204403010180060980d80e510161544c2d8810070384126158040352207016554548003c001403030070400d10407910038810070b10000b025 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 524358075 1250 524356825 524356837
    0x20306010908191a04020108150301020c1509010c0c0f0b040606030f0f060c090e060402070618050106150e0603060907021e03120906190e070b0d0b0108010504060f06050903010b06 79
    0x96030354241c00041000f600075070f078044c0620400180c040b00d05040e40041d000800180081c2d070302c490343d9a44540300351400d5041c0d0307450b81c2c42c4c4c1c3d08485d606100c184070801041c0c0241c8111a00354280007040d041207020b14080c0c00303026401100300091041030f44071451922005001140c0042c0c80d03500020120380340709030504102c1d01801018000721040d2800c1c008407520391507e6014004603010801100c251901c1c040d03032101d400d803000342e035540c1c00e440c10074004d02007044402055600400e9038400d000701580840107803440300c4203524214058540c1600d510600703408031680483d040000402a040003c0425003004107801150b0300801405001026100d400a01102691010945000c144008089150424815009030183d82080030841c41111050040d018000751606690380c0d2051040007403c0080c41407500c156142c805040603040034015400100740028038100011499181902c1a10100d41c003d00641198500d81501640c040d0040142541d041d5079071142d586040c1c442c40001c0035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 524359325 1250 524358075 524358103
    0x70203041712032707051c061808040905100b0d090c0510170a02070f12090513050a0c1d0103091b03050a03080a0c020d0e061b0304080c15070204020306010908 70
    0x13081541d8840041c0c415600c07624900895002d60010041a02c442e11102c04125140a24103110308035828801e0182c80a4860018101d119603044401e06c1140070280040e105100804d001a49400c40001101c107001e0003070501c5108100b00c1d06015403440e510030404580315461000c00c00703648000003088000a07160f071401042102450340081c00c803a10842d580030f000c0c44007c500b44002c80d05c6811540b495028024422130481c403020707504500803100c00000b010010301207415151642d06d0040500300658840c0034041c04c0c0056081198001d0300c911181e2003071104201001c142c880011405000303580429681d209403055000e0504600b51240e9001e94020b84c02854410f050b40380003042c00e20300070800884146450240d81d00540d001c40e403079240801514050200805032130002d00140701c0c060403421b9800c0207500618200030044060b008072443c100070b880c04550000d00380a041da0500b1402c0490a000300007220061400e5030140d50401d0301807400c05191519a0100b92a09550040c002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 524360575 1250 524359325 524359351
    0x21005100504110f03060622080307061a0f040c0311030901150602074509030f020d0801090f06120605040c270c030e0102070615050907020304171203 66
    0x406a030420f070203080308200001c4001854000d0009020850f40405800c0034803c2c000021034401d00300c3c140321103010000360f044600342d0341c680e81d41e8003039925409502e044440500300215040a61001c40d1070f001c0300302018000d4081d046141c000c110091030101c0842d000e050b903d58180e11f10b61440d40180d8400c00d00c050001400f11032508d4101e039505050790000c0300719844100e0074400a101c40c084000f003d800031030781c00b040c841e080880c2d0030980e00c0550169185d035140780802580b0601604201000c034003030b8803032002042c82c0040407a00c0740031003001c3c1008105e4501c01003201c00d80d1640b160080b0300b07501c800050303620303110b031300c1191540d20221040c0c2c0c416488005000c244411400320f80004c0688031111700701d1801c44043c1c59940d24044100d0390360f4a0751174010036a0140280c100040c8460814000c55440c4c0c0123160000c020b0031050540c11081d401101c01060504103d80118041d80d05e0760011402c19182079031901074000540b202c11428040c855848010304d1040c00030314002c0300901101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 524361825 1250 524360575 524360579
    0x30f291c0c0f0e0c22050409060218060414060d1b05030106080a0204030c031209091d0606040c0203070b04080408010207030f1b0b0c0708190c0209100e150102100510 73
    0x854212002d6005010702e407084509000c9110341a504072101021804842c40c25855804040340c0b03002c290390301654002c1e04055640c0c0410895500602c80f03003800a9286c80c03c0d10303912081c007480d07000d035000f18070707a80140300c98610b1a86442800b5003051000ca40d404268000080d85115007182c0c2c3c02c0284000c00d00100041c400f0316000b0800640c0011003050444c109403450300c40c11b0b0001083d20001c2d003081d8806840300d140602c500b088002070f01c00d0040a2002c80024004815003d04658030903c1600401d008240f20749010b0061040f00002c80c3c1c021420001c05490302200054003501c11074081c2810003000400e440c00f0300103070100034040c1d1500e8000341040040070342003030754158020034203238906031603c00062000f458590b08902c00002540d202c04041c541071403281b1624031f01d130404600100f1100403503648482c01150300e920a9030900b01301e840b05400a0811042400341c040c0c00708040c00007580204181c013403400594014030454445813140d40c040301c01c9480c15140d090000c14110343c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 524363075 1250 524361825 524361839
    0x5070b07020109060c02150a032d0b0306040b04060e150f0708161e0306031a040204110309030a0827011d0708100e010b100c03030f291c0c 61
    0x40c3d003008044600380002000d50720750011f401620030200182c51010082031401c001c0b44a81e020803807410400c03091703040c850341d0f4004404201c00c11542c0b0010b42c900f401344961079820040b589502583d4400e0b00f202c8207413070b150354a001801c09104203502510403007450121800e00c114482d4012641e0340f5035045c59050000c030003464010005c0c00d12209190500005541c41d500050140e074050b4402000007175000c10000840280c1090350010b415000011a00d10188028044190180b442280c04000105680c0c446001d00d00040711483d5003078006110a800c4180940002e0b45e00c282000c2481039010f0641c840031491b40d0104a140c00345070741d280d0a4642c14228820800c4040c019040101981440d09030304030b030348803440d10300071005079100c1c089110070032800d42051940d4500200513001044102030000d0842a04d41070540009003041503c03030440440344901c0300300d040c00561008541842d03080d0001142040003c00740c0100c09014681c03121482d2241d4400c0f8a44a111650754040c07034094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 524364325 1250 524363075 524363087
    0x5130e0115060504030521030a09060b060706060f060206010302030a32030711030f0c0d020a030212031206040209060f0a0c080408010b09100608040f080c0d030b18040c14060705070b070201 83
    0x7047c40c041c1d00400e40c040c04442d007029268043d04824000c01d00c100985412400340c1a0023520580050f40841c86d002040003d80080c41595250041079016640d21001280c1c0e5034000c0c80041e404d9000b0f014000085044a51a990150075146891b8050401d0702c0b209180007034031004030340180d080411420108011820b50f1184118220000c0c00c00c9800940c1890320703120281400c910540803280c0c0c0e0b00454032200c1110300215001440710a40c0e00d2104103098407548003048298451007a40d001400d6403820788280d98211b44050031b16400c015064026203030700d900910541c401e00c007042059100058030f240042020b03240b05000454110156014010107500191401c10360780c852503014000300d80e0100c101c55000b40c0000d202844d888a03070810810f244070308a01ea008900510390010a02c2e605600300c3c0080010076035065000030440303d610401d440c019a070007001921750400411030752100e2000c400002400400b641d161980e142d49651800101c1e510000c2d1041e404501c003019982c00007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 524365575 1250 524364325 524364343
    0x30f150a12021e1e010c0602070606080601120b0a021605010e0318090c03040b0c0708040801050106110102030f01050919060e04060e120327011a150405130e01150605040305 76
    0x8050b0040081015000800340202c440300d1800c5140c440c0c05a04c0d06070300c035551170420b00b90010741c115507501e454240040034110b6409504007601c50303200001148003c45c41c0072002560070411465460320b0b03a441017006903010501108110441001c01c4000c507d080c0305180d450f210080c0250b50352614110002d0005443d180e5251103000490200541c00d0b040d6001c5a912903480701010b00c980d91949048800f40c01810340107804128046004a645041540014148c809030788402807111540c075031103800e034881103944c104a58040030042001c2d0401c00171241c0c00c000e01c11030741017050780304407030203000c84406900043c030000703200c001c1c04140700c0c2e81c2c170504141c0928400507064500480420b00020701c405042040035041441e64142c3c00c0c2058058031070381345d0100000344100031003180111300c2102520a0700e4403c402400c0340b103482902c200c040f03900b15500500000c408140c8031280d8001403051550084040d500d51400031721607009200003402615154035000c0d25182141001031822102c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 524366825 1250 524365575 524365609
    0xc0518041e051e0115090b030606100c0609020102120a0801090c2316020406260d09051507120c061b05181f020a03110d05030f150a1202 60
    0x808141d00415008692409044110420304403250400c0701800d00412080c0d80100d11030f10031070b00c045006030b847d4110701800c410440488600d6102e0800301b00f40c2221280201021654084003103000402a0304110002801401541d084002d40800fa5500b81d2100c070840b400240c0440040c480c1440c1481070441241d075070700c0d280c3c0c044400c1e68a4003400d400034100088801101150001174050210324241100d41c1c00383c8180241030352048454082c0c40e46080907184400340021071050100c0020b00c00300c60341010768682d101a49030000781704020400852642c0b10842c20800350010422001c4230000e000055a40c0618610650800e04104e80b400c0b1500341d5444a10303a0740d042c83c1c941c04025900800000a443d0791010f0400f4002040d00c1c00540c142e01d900040940b01c2e44d001500491015400c074060744400c000c0c09001002e058666800306482e4000c41e40900100b54854182c00f50140e108480c5483c040c201c070340c1003000411100982d8001c11007440711400100031401c0842c3d0102c61200e00e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 524368075 1250 524366825 524366873
    0x3031605120406210f021204050c0d080901051c061d130c090f0e0709060f0503010504020603131e121116060e15041409070504080a0b040c051804 64
    0x18020000c0c041301e4949060884060301245040701d002d8207034003032010120401400c65a901c8105009081850200c505036118003401d84241c1c682e081060600f921203074480c514519004407a001514213800c90051408088034913040b44e0f1403480c0610683d400b4081c0700d01d02d159568070840b101c2d070343d00c4030043c107007800b2071012034108000500d02c42c2d140080e60040316000c1040c041e000003120040c129802c103c0c04070301c03405500043c000c41a40c00942640c40300910441c200e0f4840c0145800d0381e0701500d0081d0000401c100280b4903e6224011103203c074420800c01004012081034442440075450060b01c1c00c0e4030200002200d55042031504010b04041c5d400b5003181000141c5908462202c8d10a00b0240b05500320400d800d83e480d1040f04080d0f20000c4802619191039602403041d005c00e600b0103030300580c048004034404500420659003112040002800a00000c1e61043c42062029204664002403c1c2011400350340b01026181000300a424001262074136090440d40c640d0b0010f00e00404020b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 524369325 1250 524368075 524368079
    0x50411100f0c0f15230a0606080609061f090e060d0b06010e0613060903020a05011106010b070c0515030702010f051621050c0a0e0306060d0b070e030316051204 70
    0x50082e003000c02107600a035070054042107a040282d502d038000c056162031980b070081c800c801c92108001d004444611010540da06984210111084030154012900400c00c078800141c10f41ca0701d11840c40c1d0103980036020400304862402e03245103011040d207108001c12103030141804402904820241d2021086038041a4130450b41c450b098144005032419040199042d280100f98803658101d035074030b1a410416a40c0c140d55150010070080190108a101d2014403200103859841000340580c0c22003201c000c0c006503480c2200c0c080e80c551001804440e0342c6010000015141e071124440c001e510324410403e41c0d00e1410190017401c507100399124801d005c1c501014810481d42440386a5985000c80c2801c00103d0214601321808140741d04103080701c0c40c2003408120800e0b08100151040054030b840d910351500900b400c042d11904110b540c55040001c02d015180455100303503101d5000308050501c103c174031034280042429070780101d240d401c01c074070b001d201c0c03a00704030301000308060782002c5040e1981824 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 524370575 1250 524369325 524369327
    0x1a0c010b0108060d0f0201020a1b0e010803131203020a050102030f041412040501050a09090507021c05091003020d1b0302040f05060301350a03030c0f18061110050411100f 75
    0x244d0850303006042c05410b22140d40869008020020810b6048800c00307961032405124009041c1c1240102c0103a0350790100001540314001080d50001e16281c1901c9800a00b061110740180c071003980113500f103200b245140800700c0e03000e100a40c0a0003030b001c429246407405e07080c010a03040103103d43c10f00540c08103000360110f00903003050b1003e40e1000d2800543c0c80c100d40304225591051600070090340751515050004682d00000d003200c7c00e89440d0420700440c3e1100c9c80564460040341e000b00c1d0400b403040555030615203c0d90060124105084000810b04c486014000f1044503014903e40426030005050000642c450810380c01040211151890340d81040400d03440031003985205650b00205074440c142d1000b418a4800d05a99042c04a442030795084c1401005412650031420104065494102040d40709011840c440407580c000700e510649041c108545d0760408440707010b614090300e1302c5a40007140c1c034000c03240030f80d025500c09041001e00c1c400b0089659000b403c540309014036106c0070b61500b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 524371825 1250 524370575 524370589
    0x9080a05061605040503010501080609010c0804030e0105160b0f0103030905061e0304140307150c1e140d060609030606091e151203020a0c0f0503030708030901061a0c010b010806 78
    0x5040b0111070a4000700b0018103507428041d0340c104030740c154200070002c11550f9000440c44d20820760300e0700a100c16108403109175005202528044c00180a6040124040d40140f00401c88105c034030305409000c0c0099150b8a50030082500c24407000205800100305240d8805210300240c00c04690742c611307082c074221180380c908101c1035000c1d08025001c400901444080d0701ca070260310602c0c100b07580c0c2c0c809051501c03240d0310051300402070f6024900341c40052040d105030000c10300d00c1038614418200c07c41440c0300342c0304500e0302001110380e41410051101110541e028000080685484403100d40e4214a00201030301c003560428003c081c5840d8032840307000315090140d2481000c074a400200c1c0d9001500341c06240c05a50807000401010b948400f003096400a0098146401031454841c4541c80e610b4880c0443d07503a225241d03040c0e000307000c080080344e1000b00540d0401e02080001490590355030031103100002400c0c61840c9060f000c81c18803503114007070080310358082c4246490750081c0380503000075600c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 524373075 1250 524371825 524371831
    0x1507050f21090f06070c0605030f090106050a27060f2603030c0a0908060c030402090a05070e060919170d08060d0305090409020a0308030604140408340501020a09080a0506 75
    0x10450116072a60b0f072948418084800d42500615000001912483c01900310350040d078110301e0b400b400000182002c0f606100700400d40c0c00041820303205a01c3c11140103281020300400d840d0070088211303040310585880c404c0c18001c0426030b01c1c64440c54079100c0c4220742145205c0284587c0f40904480c005075001c0070048941c80283e840030300343ca484101c8030880e801002500001c8461141d5000d01113444514006180b01d640b088a203182941c0e2241109802d5401c2034424074041410090b0400e014038150002e451400009080d1401054032000a50405020340d8090804001054118080c42c0d1040c402008100c0c6217050620490a1010105901c1c8550354000780030008041501250ba030349507044800e51680040c40000030036160304010b00e4542c8280d810078840c0d4501180c522443d118020202c0c401da0300800a01c2c10424a41035812a01084816802100c400e100403850a2000506403d1105010b00700040c3c44001c54240070b40b420445800c5a1140e034048c0412500042c1c00080c1c82e54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 524374325 1250 524373075 524373079
    0x11a12070e100e0916060201020a021b040b03030d0e010c080f0402010507060609020a0908010c0905060706020703050c060c041d0105030a03030f0b060f09041104050603010905061507050f2109 84
    0x14a5841042841d08141c0d243c00000d2039055181c01e0140b62040000d0b4403480715140d0400d01821940c4040907400c07480381c160502c1c00343c0c00808083d8514031031074184000844000e08040382c541144400281140d00060003070280981d82d11201509504c240300e1551186154101200d007410500106a00c0e6100144000d040001c0000d840c01004580d401190040107000000c0d1345817010036001808036860303402001995031030000101001403240e0150344c04c0758005446546080450780765900a580000130aa0500404101e40d19012400304907003445440101c005640700c5040005a0304001e13035441540c4502d12003000107100c075940104403aa040b0703501d4100000c0e490703e80c00b10301000c0d1183d1450690b104101140c5055001c80000082080901c112420018101250720340043c42c0224010b41b90003e00030300042c001c01c1c100e0780c043c03500400001d0450a10070604440400164072030300d01244c45030403c41c0b0001300d400c41005544402544000c2001c4001d100b03a40d4490b060192180c40d038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 524375575 1250 524374325 524374349
    0x1140919150603060e0c0909010203010605071509020603071e020102071101030e0a020907050d050108010c200312040f1a0f130809060a08190c050d1e0e011a1207 71
    0x1e507045910798041d00c011030380010240840200c580003540c9032500f002107180200d142400080c800c00061085a05071000c649441d801c001f66500c55003030003800c544e0703440e220b50f5680c01d40c000540d564102440c8145045ea5a1184a0303801c44c2100c1422072507251108150fa00503c0043c0005001003204001c4000a00e40010342c50b120310b940c140340a0100d03a000c1e41140040701400140d940c04801007220600f160b5091005076aa5107400d406ca485284640300007030b0f00344211000c1982010080e031311041c40c070000c4130f0800d860103000108241c415a000c80e440c443c100744207010040c030400843c202c1b140c100c1154842c0c3c584018101000301d0010400800d07807400c1180081006031040c01c1e03d91040340074291a03145c0480703044c0548400c000f41c07003078480803064079000d070b0070003000d0f009407504080941d0703a03541010803401040c0003508440300d4101d40480d00316542c4d0280d462070300c15212080440000800d1004111200040101d1a084d6260203402c13540c80640c100a400620740044950300240c50b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 524376825 1250 524375575 524375603
    0x20306030102072103180506011a1b01061809030909020f210402011116090203060114130303081005030a080c0c0d0501050103021011150a0605040e01140919 69
    0x40e00921521100a00154200520310210b450142c07120070b550740192400c121290f1b0100350786200742a030640c01002a44401e005104440e520400308111420a00c0c40900b4001c078400c0c04142c200900c010390045039500c030000c20803a188900000303060449079104000c81c14064034014602406030045409468000900b4071501a0075002c4810a1038601c4941000001e9501c0c40e590025061360305900085500401031008413011503204485540086121441d92801811802070f4100034003813418000c102d4030f0741c0c0152204c07400a2949810186800864504529010b441000c01034000e880b1403c6542c0180001c0d103000505040554002c2c3d11540c46111449a50b4500811010025001104a005403080241c150011070507070303200f03d84100c0c2c811101c04084a206410f911502d0b030030b9200e01080c0107418607100d5a80e0308007103046004107480ba1035802090990b00070180340138183e0f650712501642c0760080c80d0328a4004100c200605695144140c0c4902c21144010001c2c010301c46810038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 524378075 1250 524376825 524376829
    0x71a010b07060b030c100e030d080f0a0b0102010603170a0f1107060e060f040806040507090b0a060305060a030501020a0908070b040b1c0204080109030c1101080f151311092b0303020306 81
    0x301c000340701001498103154640d46e13203004207080e110004040c0248590130b07601c2070780b50190b111144501820500d01640c0d607180030014020340211320302706065561380c0001001151462403600c01405210f20401c2c2e4501c14420700500350036060301044108000c41000402000e0041070110440e1450710740030705a086003000045581c8640b610310001d1090005002403495004542c6500ca0340c09581643d403210b0b0b4802c0082c050381e0314010041c0c2e203c0022101400071901945c002c0da04601e0240c9903030441c5403260354107400c9074051159800400c0c1d0f601004c00104074200070000c0a4041c034803120f4141440d085881c03526000320f0320540081c924401111101c20840e81c107541c010943c2200920001001d4200500a030314401c1c420b582c0c44542c0d118840341940a00c6000340601d618081e0303045160b070303a10710040c0f8080032200b07142d07404144040d603084265454015529404410040103503204250001c03c605e4a0b60a6501c04030114003a1450602c0f0021840c94070059405040169a0750307a4100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 524379325 1250 524378075 524378083
    0x1518020d05040c050109060206010f260109060515030304050a0b0a0c050706030b13021201050111030c070f0509060a210614092d03040b0a020c15071a010b07060b03 72
    0x40d96100c80c1c0c40c1c44100310034050311140d941e0444100b0380b1024001a00d5803412620792809008903002108024401c0185d11000d078028041c44079540580396501140640e620300391031000c281641c404d80c8450038004603c4001d0840c01c01ca45040300118a0f040c584000308944030b10520070820301d100b0114a820703107580980c1501c00038590003400c0d91030403912180c1c090010001c5070303e010b003d8100c0c203070750081242c0d5910841c1c4800c883d480352502a03a1030000115800341c1c03032910f89040340c081401040a548410059440640700101d940300c0300750308100a0240004009001611640700000c0c1005215065030042c401a02000d0f80d0b030700300c22854109100604181c0c055010480c010200304404082c0104010704601c40c041d0846040511180c880071a600540307800d03c1c1c03540c00030002009000440801020003154600580d03241c0c80c034010000d031b02440c0d0000000b00358180025410b080010002d0351076031040f44a412208194140240c01c20039000700500100301c1560740240100640d8200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 524380575 1250 524379325 524379337
    0x6020307021606020f070506250804121112012703051c0506030d03020c03040501080402040908030c0d0509033109060803071a07230c060a021c151802 66
    0x1d0302c440d6043da5244001e40e035108540000361503018040380840c482c0707480c000300c400400c0880b59051503c0e050b8a0201076075040c16908aa030003508210004103080c101e03500254150056510030f00e0308041005010160041410020803130745415009409800f68851603200c00001000c1c030f105e41c0d40549410b407885d10881c00342500c40c09061005007407030881c1c2d0f004103100d010203406031191100c10300000d030141d00503415510321075002804140010352040e0b180039441030009101146150035903c45c582c80390700a407000c621301e42e03000501d0380341c100b81340c001c13550403403080d200452401062442c03a01b402e800c4490354505411419401c2c9d82039010f20289a8081e19585204110140c0da80d04c00c0d503980c0e403100c03408451942d84130380802d155030303a481c0e00c0034401c0000b074942012010540b581c801000c3d8a0341c10040111000348400c15980f0703000c120980c42242e19550040c0e4507643c2c41034070340d601100d0f109140045402e100c54080c8010900340d001302104c0785181c4042132403c810096802a010340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 524381825 1250 524380575 524380603
    0x130f0e010603020105161514150a08060115032009180c0403020f0102150709060906050408030d02030601050f0301060c020a09230c30011e03080d110331050a0602030702 74
    0x418520b000f00010910b240c0500ba0b500400e0889c500000305005042d8098411075403190004c0c401003007503030790703103d12031001501d21300e0006446003880d8140a01c03280030305e04000401c1d4021030840501d0504401d400440c04202c65185614039110120490502ca1800000c0c095106148103a446900030801503000070341200c460a902d181c82d0384000c010304980c4c46905e0008103420400200b0a00550132078064070311140140d80b4041c1d00d80a040c02079400a4400c03810070a0401c11903014804e503601840c041c191071b9941412900c050700400044030800c1d0032880c0c40303514000c070001d510500740507039102c0b003088540308400b00da4420450703001a014800500c118040c030003480410b640308a0f615005000c84a454205181c0d0700c07110041d424090020441010200c112010b0000c504000046d140c011034080340801c511002c89000e05040d0010f6644000d4840070403480d003002483d04100110400d00403da08a0a210644403c3d46c2d489a4000c060074090740000450104d503c00d1003468291040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 524383075 1250 524381825 524381831
    0x4121d130b09011a07120e1503160311030621030412050d1b0813030602040e0702120c0d0810050a0305060907080c01170a0605130f0e0106030201051615 67
    0x284214000103480c0c01d91480e031041c01120004103200402080c0342c40700003003002140e410410255141000d20032105510020311055903810f14003035440781c821011600e00c520190f40c40b0b06040c82c00b00344d0100c60345005028141040c03828150a8000b00a69920840807919a48031101c0c1280804d11154400d084032800e000002d00032078440c0742c8283d80a9518071400031640c1030189420122a00344240d00841403a40501003131030041040c207800361000c1122542c0709000150b5a540d500100e0b842a4810810b18908000b0031541540520800c9907084503400c1d15072803c0095203282d03849008041e014000e0014400100319682d55841100001c2c0001601800034541c5a007081a6101d40440384645c25100d040c00c086441c940224500000c01d4040e12011010030203104200061403005104071521a0342e414001803650303552000e05002c0a61410014004180d5948a0141d928040c5940c1d016030501c0c07000c00060341c0c4002120b42c02d03007414017400c07401c059902e05400c4150800c2448401141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 524384325 1250 524383075 524383099
    0x100513080f033004031d0a06090501021005160f020709111e1206010c0311060411040c05120402010c020d0b1e0a1b03020d14090a120804121d 62
    0x400401021140040c9000c3c841c842000000902400200d08014550007074503c04200000d00604421000d2044c050107030784207280c174601080f80580d060340220001b0b01070550070411541c040c00f0505100c0107203030042c40589014140380d14803100d800d240401b0410b0022600f04124824421880a040c0b403202c14890344440650450440d0803501142c07080c6190101c06490b45a40741c030848040700d01e100b03d24919035441c0001501e11250588059090198420000041c004140324041c860351051218200d40084a01440f080b02e07920022031090206c208484086403603140d44650f4040e80c2481c0c12400030440d0700c085584e816104200820880044050290798200c2c90143c014105d882c40070f038500340e614140000c00341ca0300c40032501c000307494406030a030000b48a03400030809005032540110352840b07004c9251318040011140031007035402984a20382000340c8404d52070311ba0861071130301c5032403400c0540720407007440c43c0b0494044c00d216080360b44100214403130030b0070000c0c50801055800307a1301d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 524385575 1250 524384325 524384353
    0x705150a090b1810030e030d0c0e040209010c020f0102030c030a0e01030b0f0f0f03012903010f0b0a15140714100c2a020607030c06060807030210051308 67
    0x14020840c4000410860000400c03120b00c007205076400e0f9210b00140d0950300b0511000d1000302da00e900101c508154844d81001e01c003080c20401081043c1c0004c900041c11301c220070005100300d094084040c032950040040d06100ea0340001c0041c40c0300e40441d5911201e00500c030041c1d19612030b80039005503030b000215454040940040f04005000001c1e01c2c00c0c82001d1492081150342210801026842007841300c80c41c00b5810b00c400d0b00c0000100141c00029500b99400d0002071000b10005d04001d25803170f2401e0035800381028000d03110090010b1000b400000b4064000403c1d100c1d007400313034081c1c9401c880315480035144240344d0280e502c01d03c3e1691980d01d0074030b4100510000022034200e00e40e44aa404030071101e101c20312402d901b40758180d603400841040c4080000300748141c030b00c030364010080d07064680d005640d03410300620f0118885d840740c044d440d4492a04100ba201d00b5030001c9295001881c0403c0036840341401c840e0700700204d2802581c0c0c3c030010f01800ca0003404a03084041c080c0b08540e5114510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 524386825 1250 524385575 524385577
    0x307050405130b1e0a1512030c0c0b250201050a12090605070906030e0d1b0f0204050708041502070f08091c0b0a14060f01080c1612030e0a1112070515 66
    0x71304078810032a412544c0b08007501040d40d850010f42410814004400c2190301c44000454a145110349882001c1d03481588604524801d40d40040000040000c3c0945240080c03c4800821010000c00c061010117140c001900c980a03468a80c411b114201d0070380d110000c000d078003c202041c0d00c030390300300140d080a010040030615a80650000310346070406035100d1040018840000c070316203a440102c00c20343c451062681c2c4203495000c84144411050401c0140d499000e40d074811012503440c0003440c509820084000388032128400411481000100003046846840c0280300703402030803c07691002c148001c40d0140d200c00c0031114150303628611200401c40654120b0b0702603130f041c20050001c8080c0c100700d40180078060343c2d420703400800124850a5940284009a07102c0008240c5905080310500c003a038042c41d19120844061075241c076000300d456058458030072041c885000070101d20781c43d43d42e400b22035812020401d00c030340381040c541e46400d10104070400c060100904960750a4044018251a03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 524388075 1250 524386825 524386861
    0x306110306011704020a1421030703030c0c03140f0c011d0622260c0a021302030f0f04210207030203010b03030f07033902011d0307050405130b 63
    0xc032020f041c0c041d40d4504001c100c1c0101d8004240d485824034103e484403803003090f0b811998110041c01c2200342c0c4950003e07036402e041c2c500c0c1c2340956036071034492900800300d821001c2164140311070b1210401c0883e500c0445c9840c026002040c130366607006d15094800c06402001c00c0600150300b00750341049480c1c00c1c0c03515241c0d42842d940441e01c4540754001e50640c0c082e220001294110700e40765030344002c038000e41c8030004651817441450140c100c0340c85e41d1070800c1d41700e0305481400da48681080740071070501d0001034007100a060001c42c1141010000e250700610041e10b919015040d1502040600800781c0803640e1818110000ca6001010701102070740710324140c030090b8803a5190001800c04c5003030100403a200c110402d01c22a01d00311042e5002d03522801095000001107455010040429014820010310003000d0000d03070118000a00c00103000c5a400d000400c403a5040c8001e1032240d80703000a80d0019518100c8012a8554070108001c078480d00989014203156150818400088a18984554 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 524389325 1250 524388075 524388077
    0x5010f1e060509070c03080606070614162a03110d03060906090209031e010b0910031506150c0203100603060603030207170d0f020321070f0c05060f040c030611030601 73
    0x21115035074100304038100c54104c40240100b1150f0070f188001074410040c00303a01150091003d82060841c0d15101c04580a00c0c5c07d01104812180901a00701c1d0503603580b0300b00351080e10f0440036812075202003240c920720814603503020000c00f411340700070140a950001e8036100101c0c101da403941c403000401005049030b4824010050700d8088049104400d034021507000050141c001c20140903282400d045110b03081044085d15583c510b0185081d690f0800e501e0f0040403000041c4040d00c0c1981041006481c0c0c120003030030034a14040007001100c00c0400030700700121840c2401e049030a5280042420441e44d1442038601d140b40081c08400c01003254001825280240e085a40454071807403079110203226029050a15400210061541403150104d204009100d1064a0410000c0800703000302404803041c000300c02115404100100f98000c0c0c0d011264502440d2030401603440e80c985a46410002d400101403031540d0001900f4004074045441c011035101208000c2c00410a0b01100643c0064440318 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 524390575 1250 524389325 524389331
    0x1b0305060a060207030206180a030c03060504110306040506040b4b0c190e0415051e010914010c0804060201020d0c08010e13020f0307080a05070b030f1305010f1e 71
    0x40741e960b03c001103403800ea0303502411180c6481e08041c200000d6943c004201a405245550f000c00019103003d0700c0001507100380c0000c58641001d00d00f00309141c9444032094025403204c820800414800122150807540104150b0314586840000044074421074020303200d1120004001c42440c10042140c221925a5100908404101222a81c3d000070181c3c0c0c900c41c101001d01480070503580c610b003140701c005d0050a03c080d082802e640890b05403120044803840006c0c0c0c2d20700c104181d0500140001c20345903c00204c0c150810f4100010304100214081c9031303a142c0f824418401142d0060120f0341c020ba80201040303480781d0b51a28002d000c3d61001d0b50310360209080c01c0c1400081402a010b0341d0503a81141c170580040c0d61403c900742103004440701d09982c043c0d940d83c1c8035806500e060000c2405840510701038900c1c071601d418014607003505136108041c811400c10403c86032594407103219030024440c5484a9000f00b9500700140940b000310a040705442c41d003a40740d1180c0007066401807012005540034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 524391825 1250 524390575 524390579
    0x61125061a0a091a0a03030305041401020910050304060b0904080c0f0604030f030905120d02040911120414160902040627120821060310090c0b0304061b0305060a 71
    0x72100c080302428450b0b40100e040c400074051200c00c0e070084550100070b200c16001d5810194002450090103620540100381c0d10400c1c44140030982c020541c028412a000703501e8190f01d94086881581d0668240d0100000480401c0800c5281c1e00324041142002b80f18441c0d40c2020b0038080741660088202c082c05120310b40307004c02c4809000c0b500910a80d0103464050301c40011050036005800c014100319118000c0444580b491a80800a0f241d0703007001c040016100c03410104003400f181c2c0021403c0401e00d1050240c005100c20f800001c0d0750140c2d02000a43c2da80d01140c01061a00d03801031070401c0d0070080441c01140e451000d41c081c004488040c1d445c24030708885d00d00b680708100c0c0ca90303440c0e020940c00c0701401d0011004041c45522586d1082008520301a0100655443c845004071030100c060800c0b0180401498100142031900c3c072442800c20110740c1903600e9002c8450b541c4a40300711300002200280500c00c0c180d000300c5e581007000041e0880a0a83c00d4024010032040b51000d21030082c0c8480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 524393075 1250 524391825 524391851
    0x130e091e0a08090622030c0807080606090a090218041a13020312090609120106082505040b060d0c0801080706020109050606130b0a030c03150509030706112506 70
    0x711025070040546490822400140030300c42c2d00032007814074640100c07180c0f000c090010300903020045009a00300381400c0d051501003820007000c1c0e48481e03125030194007440900d0352140d518541062403d203000900349414400301b9070500c005045004640305d41c10030042402400704000c03035180c1101d08200b540e80d0b251540d0210301e00d86507002a41550020f441c2d00107503c4610b000f0212900014201800d0154501c0014141114141880c0395a511081d0400070b8000401c410368803108501d55030300340d8404032840d1000800301e03442000c1c8a50340f11a48081d00c0c0d00e42008a9425004100003480380300120180500307400400e02c140206445440c800141061040c8205080260b004c805003889407600703403c02c003610010388044402d0590340c21090b41c1310361301c98601170010346c402d0340350303d00c40c51442c1003548102c03500340d030040c0c40182000708100003c038001c002c07600510707488080055441c501582501142c000c10700d49448010f0750801c2404034510302c451702c644041c424101440b0720307818890 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 524394325 1250 524393075 524393083
    0x603060a060b0715110409020c0c0303040b0a031503150506030d08160c110d052518051306060f081b0901050d03021f2301050312130e091e 61
    0x802d541402106000500010720070550004074400c03d8400844c000b0158001e0031440c1e4010340c484051181d000441440380081402100310b44d4500710042c40c00d00d4030340a281c00d698820b6140020825130349000016010b030914246402035a00310161405103219100100d00034001078406603ca442040030110301c2c00c0c485c0c070300940701d4035409550a00c1051041d200b45c9030392000100c00c9075000e2488000d01000d464150307012080320b0280009212000314007800c0d050000c1450098102010f00303800600c5100005110030390b090200107000200d640c5d4100440552050b00e00c2c0c028102401c054002071a4400d00c4280c805495105080d5087c41000349822403075000e94080d000e42104417200100040d18140700350b046228041c0c01907230044c05410000c603080081400070400c0041c0d8600400640c0c2c0041410710100c0c200d03c2000001d03550500c00083e03501d8120800d511300349900081c00c106000c01c41c460f11f60090000e0000d551190900301c078440c0e00c0304d0745c01009042c0048151501802c20380d00103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 524395575 1250 524394325 524394329
    0x40f030e0f0a090902060f0304030306031a04170d0e0706030c020706030203011d09150f0708162102160507030227060906040b032d07141e090703050603060a06 70
    0x510602c8407901d4804204040e02e0281e105a81c0010700740000d1030100d003444002d5215a00c69a80050500d007989440207030641d05003200350f0398200400c04c03c0009848106040355410b21402c2c81134603440c40000800c00b62032840d0000ba094003410710b0005449416811080f980a26602034981107510741100302c00300d0209220300d0014a90001e54100500c0f260210143c00403210010765610148511101a03c60f10540301600140002710400c0700c46a4040305854000c1c80460990300091441c0000600703038060300c0d034003440d8245040c00c4050414500d03811920305480700740000300e40c0509828400c1d00c454080c4001e80c0200c00a12400c51840881c500e404d41d0503811003d822070740d032100000d01482082c01401160803075981d01c0100e43e299800c0203031290042c4480c1d020b075050042c10690100700c03012140501d095501040782800000d81010140c0094901030340c0d4a50402000c1d2100c00d10b0101204d0020b801c4402c141c14080402c1d810303080184078680a0342220625160000c9150071100a8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 524396825 1250 524395575 524395579
    0xe130c0510120b1210020a03060b0304111e010831050312010f050d030e040b1302090f040c270e091e030723070902030c0d0b03150c03041505040f030e0f 67
    0x8103150f10b81c04c0c1446d502401004040745400294140c88050100003a401507509880d16441002e280240d0706e040c6240d1006a094010040081c20030f0303a002910580c0050107000d420088064401e000c5290302080c0d001c02c3c00e0b840740510104803d0b0400306e40317030f41c0302c40c480e02917881d109800401c0a619410683c0100c1c3c2c0050034100ca50041c07500c08a41501c01c0c42c0187d0b0703000381c0390154005503580d40701441c040c25a0003900142e64444490410103420300850a036401141001c81c007000c2150802e0305448000801c00c4140364002203140c0398800c042c034036004002d00d140010180406100001256072040401410710307258000c0c460441640c0307014044001340103411603030003003440941c406c4042c0d014440e03403000c443c2d040d602ea0b0700b500181e8004a613840304800000c1800d4030f5100e01c900410b445404140d0180c0307a62852500c01402126008082100c81d0780c00002203401c00040504110748200ca2420400c10750805180c20b503400c0b69802c405a000030324544103043c507454000803140c854400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 524398075 1250 524396825 524396833
    0x801360608060f091e03070c030b0708072a060207021c0c0f030b07030225081c060e06040c09080d12050c0903060103060e010207050109080903060903040e130c0510120b12 75
    0xe090100100445c0b440a1001c9000074040c000024004900c003001a40c4036010a5500c4e00e0042802009544000d208004004d0038242000d40000c07543c10010103140000a0902d1007006800c20002920410000a40220004018006000418240d940381c2c03031150403071054041d9604a03211014149000c0a024103c612010138a104d0103540101a60118100344144006030511403185500903010f040e1031004000552141c480a40d2228a6502d505410204030f52803c00c02741001074100142001c1c004c035503401d0b580c9441741c0210340040041ca052800c58981c0c84800d0b0300104140214400710040c541001c01180031207200c5025206010006001031000c0e80c80c0d91514800b9002e0380c13041c0c40b1595400c100707400c0855400c0c0545c2030128068140c42c0e41e1454514180362826100500303002e01a0014132040c030602c550304840d80d0304200c0d07017003011200c010300b82803804000031b4a50016500001d00204e110100740c224040850344480d180b010400502e41005010a256003200301c6603190308 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 524399325 1250 524398075 524398093
    0x10b1201091a0306160201051b0d05070314040c030b0a0525050408120c0d0201020301050307031502190f030e06060315040611210105100801360608060f09 68
    0x480b5400a0080365902d02c2c030201d01401d00000c6400c0c008180ca1501000c0328080101368403070380900409400c40110f046800d00024140c410441782d02400b40075501c09511000070440e13251280d003103882c240701d00f182003403038030b040a14021829001c50300c0304031444861007000031144203040c4540c900c90080905291502c0350044441d40c80521351541c0c600c18044c09101c00702d40c50303008116080c0e0041e5000030a640e106040240e8500c2e0140100500c01107a00404c0107000c5030300c001c21200c1c2183d6104001c11528410464900041c3c000e5094807000240c28420310001954000740c0b034a901c018544041001102d60f141540d101d0f44d04441c05501540a0a40080c0110005c0100c582c042d00446001403806904400e204044d0300004030720400401244186600c1c03c500051240103003000c071103000d403040c0c6001c0090400b000501c5955071247c69410003c141d0380c0541c68040a0000c4030300980314222510041c80c00410150007040c03011f1240f030340002d040303401052009020344801c1000b401036034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 524400575 1250 524399325 524399339
    0x614040608040516170601050402070c050d0c080307030302030a1808090d030c0209070c02030601170c040b0d171c060b180d05120d0c020309010906030506060912070608010b1201 78
    0x981d001c1c00443e901c1c800c000e00801d07041a4034004c4c1020381303400d9465804180500f040d4a14103441030b0482e0b4440ca104124800029141031082d80449070251001000e60f07226003441290b5407050303440b0321068040001e140c010582c1c1a80103501c514800b500811561005401c2c110ba40315960b040104800b504100340d0816241064101003460300c24600580c2101043d030204070020400e459400114165148807002c524081c01050301401c540056641c812010134090b0b41c0e920700d8446103034011903440ca01540d03d0307140d80b20100384031900081e0b2540304180d81c5403100e82e03d038011000c400519403130f6842c00021031941d025040c200c0d01c00c064440c1c00c095241e42d030220321b40d4040c01030a90042c6051102000940240150b960b03c1c609024110b85a07085a00c040043c0c0e40840c0b101c00441d041000010b81aa030802c2d00c950030b852241ca0000380036074406c40440c00a1207540a01d5034840d821400d11841d5000006074041607409903a250b149503640ea03c0d40007001d0144e00d204d040003d20b8400144429 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 524401825 1250 524400575 524400587
    0x10506011103070b1f03050f030301080111031302060f0c011b110d02060f10031e02090601141c11162d060c140a1d0105030106270504060e01060906140406 68
    0x17094103c407800c02016a2540c0711450030304040a00c2c00284c0000c8010440780401384140e40072110080c0000d8614504100307242d075031091005009105000225809a040d1118016507000004400007003200d030740344144040241c0d0a604c003082c0002d510602460010802080780c030f000348110780040645c0e44403020080801000240f46480c0a0303852480000072402e0304c4014448000c124074105883c8055005020000e4002421141030001c403404640034044150708861015094020001c042c11290074514042c200801964081c15404115103000c21401500e580025101c0d110340c034249282028a00c6403105a00c4110034921400310880c2c2c01f080e42030b0017407031402d04c0500c0c01850900e1726050410b03240c0c0000c4100d03000500f084a02c82c592644941d46041011000d080440c2950701d81034005107840c0ca11486c0100c1d82070080700c0c5e070f06803c0c050003d12001e880001c0c07040c8a01511405d015008080921500c4006080f032840026410300a40e0400905500c0341040b91401d410b052042c0c0348 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 524403075 1250 524401825 524401861
    0x6090e0a02071703010311030a12030c0309021e010206090705060f0a0e0307140f0f1e0f0603070c15090804050108150901030503130509090a030f02030706060602010506011103070b 79
    0x400741c003005190002841c205003000d8418911103140d48035415030421205030022803012500036032240f840c0c0b00c041902c003400310141540d5440d0100392403080407000c50203804128002500212441041614404400004034503c2c0080c0e085500c0c0d84e58441641c0e5075000301d0f100306500b0201c10003003206d829000c3c0d8003c00c085599030800c0107404901d007010a1401c0301c1940308010181801c2e031800003501c1c040c0300c0429424030494840c08000c903164005039860310000030084091810400c4c00d40651940c0f51030282c003141c0101107540301d14000c9000303010044003000882c2c1e209000b12460800300740030312400c00c50641148400341000d080400640c7d201401408007519107000104107072480d903d11507414040c5200d400511786075811817041d00200860358014074861010002001401440011038114094061030840d941526014040c0c0c2184502c00c030162250381084008120720b40c054110600485081e62080241c1c100351407030f56128014540010202c103115004181e020244800c1c07904 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 524404325 1250 524403075 524403091
    0xc0406030209062808010203061003050405070b0d09050a110301150e0c0d0e060a090303060f0605031b0c120c0706050a08070f1214010e0705070c030f050a0b24010906090e 75
    0x58a0313200045602101580c4d075004a0181c1c2d0000200842801c042501d0559409241420f11242c2411342c0c407940c444000b4040d0300000c0c5c40100c0c04030080d1030300340c0101620759045070039180805018140400d070300c205152403601941c200220782c100c103010000da100494500b5007034081d05803940150040c0c00d5204e081000319030b545441c521821329505114803809012444800114500140b130046c050b554180d02600d95000d01c00c00400c80307640c0040c01c59a0000d200c50307000c40c1c1180b00b082c220160740540004c212140c481c441820420600e10b100038004031402400712100c0c141e50b52011107151051022200000c0c04c048041040c00c0d0080d80e5030520032046040000044000303800e46000c44200f4510001d0401650340100038035004040043d0f0403210350300c0c00c00e10700580390b292042040850f1000a10b02d002c11607203141401410700c803496229138803150884160400c500103100401c11030941c1032040705460031207282036020340d000108655a9442d403180b09440c2c4147d010540d0b200030215a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 524405575 1250 524404325 524404369
    0xb040f021c0c0803040609030206090a081203040c0b04181d06070f2a0803040611040e06041a010905010e120a0b012306030a05040305070209040507080c040603020906 73
    0x80010380d2031180e6441c002503511150808190203050a0450704003d030b00114064004020500100341d1141021080c2e075010307a00c4a40d5215420003044034030041c0e40c4260000e00a01040500d06441013001354025406103442d520fa0503103c640105d000c0c41140305090708031440e00750040040c0500c0d0064042c001e001081d0480924010042906103803040711031038001680035901f05440394110b004a040303c42415451448002495001d51000c100e001019212000c0840041d0030000740f038020b482c0c00304180840580352542ca501c8000000c4003522624400c0b41002c000d00d120618010000918440594943c90f16520742401510700441941186401c1021035003551541c040400010b015188244c01c50305d000e40c5030403c0b0b4221030b20071040252044503041443c1411b07599403400d40e034100000c45c0c4000b90302d868902e000d40740c07072140704002900319070310408200a010340030070310100b22004882a40c41d40c03807402d1b0800049405e00c1c04020f41c0070010202150150a112070110040c1e1001e81a01c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 524406825 1250 524405575 524405603
    0x912050a05060901020a12090507120510020c0c180f04060c14180415060f050a1b1a060d0203071802090d20040204080c090403020709060f0e1005030a0b04 68
    0x160510b0002c880182044c0c3d00000c10544040d4401c0c020620701d00c00c16420002c0921680d240b6441b40a5403203a8505000305144000600c0b40c00d01180440182d83c003011543c6c1e070084040030f52038243c501011485008108240c40006060030091480740c8910b8000180b01e45d130b2a80c3e100c005080704403401040105a85c4d06d03a028694034030042c82c06440c00310007400752801e01c500304015500e46a400c001c0340c0924000800000b034100250450010389800c05503203414503c081101c02a0f4a40c1202d00640d00c620104010320800d11402c01d03c100000b400c0c607243c1c1e42c40c1000c1c40003000842c54000d42607030219008200c3c8a8003e02412921001e010000d854012180e0005002e02c91004080c3d5058180e06900e8006000307104034940c050b00140c50541c20300346800e522a4403200d4001d140750180810f4000a000c15100748086030251401c8082001000d4a60060312100c171040d0143d0080688140e001c0348014102194120448074020b00518401400b41d07241d482c100f00151080b10501160041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 524408075 1250 524406825 524406833
    0x924070308061509010804080304031404030b1b04061b0507030b010b0307030e060c3a061a0c0c01050d0f06031202010c0804030e0d14070b0304020a06050a0912050a 72
    0x1410018000c0da2040769500301082000501c030380000040522080c1002a8201030360041155503226820586e0181c90f6500c0b42401d0f03030851450040a02e87c0c44e0002008400c110080381414000c1c94020001403a500c0182c3c513080c9288541c0c001d1401040d60140c00c6000c0303800d04110125a14461030a882100c0e0b0b607030381d610304003081c203810070045a0f00100801842d594548900c03182d8500c40740040180341044020b1030b0040c8102a140d0a141c03010722860314541c0d4a2100c90b00c2500780c4524548c1c2d00302c5580e10407030000c0c9614000c220006445000044c0040100c800703039481001c041d4040d042e004104401540e440e80081c0071310030700c5616260308410040462207240700031409050000d0b031012044030003d0071505e400d1121001c0c454181d0510000c281c0c44000d9165441040d200403840c850f19091a0200a1101c01e20720590b110300709000c83c491400e030019500032032080c1c5841d03941e142c80d070728103a6403809280034580008800ca1070030400110300b049081809800341d8203540200e1140d0321 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 524409325 1250 524408075 524408077
    0x180d141b010c0c051c0c0807051c05040602010b1504091d070618051801150c020a1d090d021504020a03060e1b030c0102030f0c01020c07060809060f06060924 69
    0xe01e00108030800b2000061101c01d05c004045058800c074000f420164000014107030540015014010060205220040007000c10264907804150445c003120f000528a00800070b030f1040c011000154240403d00015081035818034401c1e0600307025981c1031600b0b20003841e00070020b202d1124028441008152804101444000c02905043d964a409030600c01c2004041c0180c55200900510003651031718400d6458406c8181518280342c50811720701c401520440729000700000181d8051401c041c0055284a08041c8652001c448080300d50315a0b01c250940d912800ca101c150340150300800c0e010341742c4100b01c00300180c1c000d1004041d40700a940304d407114012103900c1054031000d540320f02c0a5100902001c1440040510200e000f456015900c100003502d901607207081c0610840045103030b00c407200e000e4040e01c91555000c002c17119201da4502d0300403d2202c4c2a078114500d80a14008150548180d42c80f1911811018140f40d00d8040070380c0c140003802c1c0110220403401c41d9041020511198080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 524410575 1250 524409325 524409341
    0xc01090e06042c1b09040f1b050402040b1206010203160f080706090501020c0106091e0f020409050403020a0605100509070e0a0f090905011d070608040503040909030503180d141b01 79
    0x208131808500442202c40310000b90341d288a8401d24080200088444c806501440d500512821400714509a04100c410f125001990300c1400172a021480701800c1001c1c01c5010764001c0303040c0c000e0f1540d5005903100d2007026010400700101c01c1071800402c41c145030001c2c045200703000080c07600c038040d15540201c489100046400b80d400086940c0028024040d001c040c21440908200c01003890098109101f807002e61075800b580c0712a030000f400084e0f94190360040c5103121082c40f80e440e06207002074a46041b82c0007103803918680320102d60f440c90f044446205070b48010348141c038030781c80d04401518000d0038200709a84c01242e001d40458120001e40359540109001c20b400b05040d40d0502d006c13802d64000101400a04082071070210514a0000d004400c861b0f480c10508130355260b90401c0341c110700c5a50480c94506041c00100f03020190300c24020b502c01c100804040d044581d6500e540c0303071281800705040c0009840d8602003803003a000341009284817030070105050200e03001e0340341c5142034034080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 524411825 1250 524410575 524410661
    0x306140402120c0604170313141305010f05061c0e0c0a091a010e150a0e0906030a03020a060b06090301060f061e080115030204030f11030c01090e0604 66
    0x1006200c11401d00c400e4160714024204040c0c00000440c0c808101036010303d1213909002441260f801039288070038030031a42c52603030555403005410380310031304c1148440c00c0c0c2c0f40c203a001710705020138020a80d501e48601416150350f140508042c0789003600b00201a00b10022403401d80c500070110440910f0144035116113404140050500000e451041007a80070340e5510a24210381442d0541c0c0104046000300c80941c0f00c2401e15078100b0420b140400c0d55542031047c24205004c1c00604041a00c3d00300124000c428011200100746680f14401e00d5100c0c20400e00040151b070003688208000340380d41e044044d40c0340018110600b82400440001e00b0b46260b94400c04c0e030480400d4042c00707a56030102e1480d024070740f043c81e40c002c41c6140c0e13000103140d030a05106a12404001e55a80c400040c440e80441e801907800031030806001d50340d81054540c0b00e5124030003070700c20722514143c21015400744075208125001110400901e036902d00a00000c0c004000d00c000c00e090b02424014210b1410a001e02405118 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 524413075 1250 524411825 524411861
    0x11a090d1707111003230c210901060f1404050a0e010204030c0806060409020108070c080d020c1608120a031a040e0f010c0c020d0f060b1c0203190c0b030c040306 71
    0xc842804941d1084084d04410181040c44000b4282c45e001d8600b0144000181c00458907550003140010a01841c5c1c000040c2d030a104d081c0200c203540e0001260300a40d5107200030000349603980010120101e05100e00102101c00240c10415480c1561195500207041da0010a1224048000500b242e0164004a60f04403007603a0600200f01f0070842e45602070005d4138108016009038002034501d000041c214810050049011010840d0410648000e402840001d40d207030310402d00501d44801209800103041400013600003040400090207182d240b0300071a02ea450300c0c2d0031541c1140138104004c0c00b80d0303482c4284100c012141c0c45510070140f881d98503038090041504940c1d26a400c1d6101c2400c24010090801d8103440582e482101c5603c40701c1e8044081e24060300903140a02c042c6ca00c820100d94071504602c03205150081d005041c00000c0c0c8200e0036113500400410981100c44014403001c0d00940d60301d2414445400740304015900804036918490070310b6a69995001a41c3e03031004018103c2003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 524414325 1250 524413075 524413103
    0xe2104060905090405060c0a03090203060a1a03060412050d060803131e0503150405010b030f0607020d140301170a060c05340b06041d01060e011a090d1707 68
    0x5070000d4640050700c0100c44440c0c044c1041c0e2512640c544020741001224000010f803002d050b802a8000810954040c05a03412450310790507010041042d800c0b040312041d10029a030b40d0514022880d1445a5801a10811802c0307542e40119a60742100070900c1010303658203004901c145040000d040442e1466540003041c504203200004403e09102140b001c0d802c840b0070134811580c0205840c0a168600074014402d0b0341d51f0306255001d00203e20711f6903014090903000004140c07012a142303225a034039400302c0d401c9181c2e11104035040c0c0301007501c0e19801c2c0c00a10041c444100d9000354100e402c903685080f96a040c506e07844810403201101031642c0840c100142c032900745400d80b4030314050340c8010018140f01d00070462074030354004c50a210041005500300b00003041a0356940c0040b0003030145089160450000c1c503c009d009010360f014040e00440d0840c00000c2d5041142c00900c840e02c0380c2041e09040c00050411b102e40c2ca1200542203512400208034900c036008040080c11a2034010306035640d900c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 524415575 1250 524414325 524414327
    0x40501090b040c020d05030411060d051003050c0a060c021c05060a0e15070c15020c030d02090a080f120a090b03090a12031503021c05120a030624030e210406 69
    0x1403100e5402d1010364205000e8100d20346d8001c019a54400d030480361464030080b9000020310144600c00c0c0d1000403500d064244011780e1010503407801900e00c00d8044880b030071000f1003005016080c030300c03d02c00010324600038007005090010b40800b058102030040440741015648070703424607004441d5940c50300d590707803400d0f801e15100b00b1000f4100d500b544510000c07418402d100501d69021640081d220718004c400e00c1c01d440507d50704035030001c1d038a00207403901c900003004550302a60002c170009202e43c02c002d81c0443c04240116040740f08129200c01008903400c0d102c0041680e0b048405002c0a00c090101d0002e01d20485900861003040d611029002c41c0d20546442e82c261024403e0f00c1c0d041515059030300d4115002c0c1e00c0305105070380c1c04079810380000c00742c1c148262007030340c840d84010824056400380b801c140c0e940340c0c0604280801d5450501002ea190100350001c0720010b4101c0f81301800d0010403c4482c0c0c00707940032072807210340c2780140c41d0105060300c4c0031144080d803103200d05130312100002c0c100141 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 524416825 1250 524415575 524415581
    0xa0503072004140112020f0303040f03020a0e0c0a0f0e040603121814010c061b0504053a060b030703030f1413030215070606080c011b0201120515040501090b04 70
    0x21000480c0c003000418030f44080d445200b9014000d060300c02031400045415540e8028902c113003884001e04481d601c54943e2040d0004c50014403040703000e500b011134045245c220302c60300da0b4800d220390305050703050011141c0c0031076001c00607002c000280070010130018425100e40c0103040146000314210301c0c0c4903068140080c001d60f5610210001350700001424415100c0207001c1d020322030400d1800d0115074003281007240040100c0e00100e0b0350611407031903211701d944e006005402241ca0840300c080046034844203017414922000640b4940b5447c038409140c55182032620000300c64011400010100d180a020a14024042d0404d0b4045a081811009456844500511003807007100955080c03030710b4855040002c0c9094000203115941d012910b43d00c400c84ea0065070000343e0040024001d0b559039950094803046040d0301580007640407010324003c41d06040310350b400d1641c1030352081015600082c4c0d4400801001d1300070003031202c00d241414031590f01c60250768068591007000290382c0c60302800300011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 524418075 1250 524416825 524416883
    0x40308071202010c090b130b1c1d030f0f07081611030a0503030103120339031109040507090504090c08190b0705030c071202030a02010c09081e0a050307 67
    0xc40e81413444100c282a4807102a9040740c0300c209a590b100c90310b407001c0c03510310049070300103400304480800c681602c58503581e20102c3d501c140520801c42c0f4002c3c0c20a81e600310104070b40401240d40100320709220581104001c100b04c00d48030b40d565040c8039250b0348141460344900c12a01120015014074400d2013412000940c52480c02c500a00143c2ea030b50365080d4480c001440060300e03030046455801d4a060084e0804448901d403401c080703130307003d0131104200d4592540c034140300041600041132218050091262040a00c5c4641c252414042881d0400001d0702000b0301e800308100110000082c99100da0007071840300707445204106203031410640964034100c050340c0300480c0314014181d10000b0130306111135070b50407444520300b450f569520b1840b114001c0c03048800003440303441c2c0003490f0742c07a40750302001034000100c456000b80407862000c0002c8400e80d949009522281e0410381c40780c420004002002c030541d2042105480c0640b040e40c41d81c9041d03030051401a1010402d07114004100d1000f4110141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 524419325 1250 524418075 524418077
    0x108090610030b040c0911070b01151d040e06131406070c0f060b030a0b01031505010503120a030b12030405120613110d14030a03060b0f070b19020403080712 69
    0x3809240424818510040c035100181c0101c6000e000325092000003004040030b44000c0c0c03024084018500302495056110b8002903c400c1c80c0c0320000300c0c0c648440b40024000300010390307448007404d03034144a00381a4610b40c0130240e840b695400004e048810284800c9110b9102402c590440c6c2c2d0141c00c2c0f0000080703803111001c10036088101040182600103031035140c180d400016070403140c8018075055008010b0140c100da414400c4030000010001d82f00043c90503648120b1200c140d0802c1001d03a88181c0780b003801015410b401c00541000842c0b03c1901030598010f01c0d20b00881c042d00c1840200d001c110400e40030480a42000030144014103003007908403101d8a1080080195143c980d104809403c3c803c04010484594000010b00700c0c1d03180c0d0f160401d169040b200111600c440c4511072a900c3e03011044520210b41041000513010100206603880f01003100200c40c507080c020340d02d5100d9180000d200302c064565405e60f802e50244248058030103548121902c5650b0a050b0808818110307800805030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 524420575 1250 524419325 524419333
    0x6050a06051e0918070e0405010504061b080403030c030204050607080a030c0c110d0204110c0705013f091a0109060902040b0d0b130c020a121e050a0e040905030306010809 75
    0x4199840f00d8980f5944134840d100b8940c0369261034501c090800a0316403051201c3d103200350900c8103000040d4452401244610020071560380a0028007144910714840034000c1408440054003003802604100303454019890018a029114070001d0803035000300005455026001c0381c41034403941c062151000e0480b141c03d204c180d020240d55001582200110b0075030144003082424401c540b03954100c040c0c025026080c8940700c1360254403803a96008248910750004680c101c1520f40d2150400810380f00c115502d03200e4414911460301d015040c03184015460039559513002d00780100303207240c07220160280c1c1581c00d0301c0c0551510104206450440e008400118410031003040703052020404c0354070010044e240414038607034010000e00d04c07196400500410718201028072001950216400442900c18414145500540c1f035040b03a10b0040318542c85414081c2e0315414801ea806080500b10500b01450002211004180032030280d518118040342d2075030000c4203000c0300f50f030425042035118090308014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 524421825 1250 524420575 524420629
    0xe0a0e04051204180207170729061503180703080a020706030605130902030c150a200309281d091b0d0201031d150a0e0c01050d0906050a0605 62
    0x610f40d00301c00c41440004240c1c00aa00e20400c815004100d00c0d40e00c036241ea050f100c5108d41452000d040c138100c1e0166191990007640008080482030080c00390101900e641100c5500310005800d5510203015000ea0521003401d00d60b90780420003000028510070342100d41c0f100b00703442001c4d01e0000d0b0364101409060403e0024010b9456103549180d1043c29580c010034500494004070b800c00a15441c11a040500c56000c018180030307501c000c0214051300d6980c055083e4944100703c220400c1c1a40795016504100f000c9021480c1060740e02008402a000c104503102e0000c003410403080700395101490404407251100c07000a16070b1900c0e0390106400029122020000c1c0c20201024200e0046c18420070400740b5250075a446a0320120404401d1800a20300d442c011340115500c280000003542c002c003a01d400070781452202d0003180303000318008004010741d40c40140103540300e40007400f000c2801c60342c0c0c0c00c080d00461164003070301d40524007040b0001103072402c12045c81110400540c10040b071144101c0ea07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 524423075 1250 524421825 524421839
    0x1407080f06010c03050c060a0c0f030204051809032503030c051306050f040f0e040b010614070602030c0702040203040609020a0603090309050f0a0503070e0a150803070308070e0a0e04051204 83
    0x45558040403d19210400c2501c0b440e0580d03650285544d8500d41d0300c1940c00300080c40c9103942c0880c1d8000e4540e00c64070741c1a10704003022800e9229602840d50450404184540800d04440030180c01114800c1500d05103040442034107904122101000d48001c40c0140c000700345a054420700010904501c0c001e4641461000000341800080c0314640070803500044400c0300e288c000342941d01a0800d007400041084e0f8561f00501502416202911460b1410000207500c500560f41c0c0a180204903c0c03075402c3c400d042c2c07146402500000c141241c0824108040f00050f84c07184011031045215502c000395808460042c0042c41646070800e800303051800050300086500003900300d00700e07401100d00350a058448400b1070f00c00d00c4254005a018816205c01190219155480320302c182807891040141090706030070003440400034800d0b0851601304018003400300c0c0c4240c00840c0d01c40940e00f011940e0700300440101e9101c00160348405e6000314140c090200f0000306012205004041c48400c0f8101428541 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 524424325 1250 524423075 524423101
    0x9040b040219180905060c0c0703080708040e0a0e0d030b130509031303120806010e06040605090f090702010b03151501051e0d0902031917070212010c0201140708 71
    0xe0301c90442c11406641e4603014042d80009850120740d2120745540648414000d4290418125564003464000984501c00a415640f11480e50401841c6c1103146454168455000700401d46556400301310208003003060b10902030103400c0340e60001690030782020b001d0703060080e40750f0f00100300750400007012a1655108c4410b5482004e0503400101b544a00c0c901d9031952107202c240307141d2003080483c0041030140c8024034145009c00e07619000041d07594403004450b000d40c45419940d00c09420320088c07003c9445040a404011000b40c8a44001c08415001844170541280c3c2c40005039110701800b0b5070f0b030406110140c00385481c0c807065034290501200000c4a200c0c0140030604101e0085200004640f003000300314502402d10494070303a81e4a101000c10050100150240c2c000d00c5055680340c010002455009802500300d200304000050012005481c3d41c80198182e074011034a02010120301400e10a210161089400004055001400c000300c00e410041c410000c0c410150100201071007840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 524425575 1250 524424325 524424331
    0x61106150f27040b060a080601062a050a0501050105011413050108090a06050405070302092406031801151e060c151b0f12020c0304150e09040f1109040b 67
    0x4400d002c0d21290000440c600c0719034040d4040380c01c0b51000511040c00840c0000c02d0207900309490703800729162201800c5680c1c800030310030480003819002503006234000f0000702d011030140544060140d6601c54072054075204108600f03480a954a50040095603000086d140022100c080d004d41002c0c03800c5074000b9039031458803d00341880611000150540c0080c014400080d90100042102d41080d0a0007230340c0c0c80c590700080b80124000c8020450000305c1103c42c8402120940101c240803103d801445000d800c0580f12001d552045051804040000c1c01603079007603180d0b6010001da00b450f05d140c20002c40b12404440d80d5403003942d201485001e921140018050340c015000070500c95842d980200240541034000c0d1400b49201c04800b50700f9031200c42542e00b11501c0e511032800f01c80e82844041207202c0c00100da0780c640d000300020860184092190b2004404a08111214072100000701d02a104100d034100c8190905101610800c02c0000035000070185c181c0ea0004549082da95500c2c0e400f07009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 524426825 1250 524425575 524425579
    0x5060907090b150726040b040305010c110d0c0804080f0615010f020d0513090f0e2b080c040b03010f2103090605130312020a050105060f0312031b04061106150f 70
    0xc10a80954005c1c50590f4200711404e602449540d1541c40116000f940c00500048801c4d50800c400881924807071403100140743d0204016010000100758160b0f40460405c0c41140c0b220400e1100144003041880705070300c040a040040c004515140041d4810342c0700d5804d034241030004100050707000c99400150072080000324102941ea030300002d0b002e154048000d03400702030003038182208540c00b60001c0c1c000828201d214802c5640d06062803080114621144030803031b031034441011800704024131807028180c10440c0c1f10181c605d01600c424812041d98400d80205038410350081d820001c070103c0700b00c1d02994500442000d21412041d90f0020a140d4035803181500b000b1020880364114000380c80300c82c0c0110342c010300d180c170462782c0c000c0f02a4641e00004415034644d40713400300203038543c14400d40700608200021302070800c41c070001412262942024100d4050b42d840c4550814405140708010000341940e5211080100145c820291a14030020300b083c0301008914440600ca4803036184811a102c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 524428075 1250 524426825 524426843
    0x1d030a0f030b030109060209040f09050c0d020f03061602070602010608031206180a0c2c0d0c0e01120210031e1d07030c030203010507110a110d05060907090b1507 71
    0x4080c9003280501280c0400b81d9042d4038001d0b108081204c01da0042a281905a806000070107415240381c1c00c60b800c4107805401c1d60000450403540b4948506258000344c070040c55415000048008a4070b414000c80d03e00708900340c42d60058204071f40401180005105920091210600345010300d6102d020f11811600f44480032800703d041981c070303c0e14440c0070f450b522400e031149280240282010f040c2041c0c02c00c000c1404403006201c80c0b52105401c00c00d02c180900303041c031002641000d10100818040040e200c040c040240070901009040d5900d00900003507995400300803c0e801040030200c920384c50715043c5494010030320101290144105805455180002440c42548114039a40c00c940079881800d400b03880804010850040d050000780c0380280d008000360b0750381c0e01003503e052860440341591176000c03548000008114403581030604001410143c04400386030f90300ea14041d4150341c0324072990002e0805000300f80c0c4600c100c1411180444120030307101503a2040c10298070075200e0103081202 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 524429325 1250 524428075 524428097
    0x3040f0b0f0a03411005150304020a0314100b0105030402010215071107080609010b03070e0c1c0c05030402030105060103110d0e0304050303070c140a060504270f0c02011d030a 77
    0x540c1014130001c001d0800c4150341d40180c0a403401e400d00300c400208541461180b000c2424030000c0003a881c00d4800c06485015071030203807d00301c407140c1c00c001c2c0126800b0380c0340507010002920b1540b800d0403014200005001c04910908800240c45062800d50704104c402d1041001603a03000403c0ea088501d074440c03401090312400000c0b070390001c4444c61148144100440002c0174000054100d119040010007008092240301c1016141d1750248210503d40c0100d0340400e42550646008050031a12803a00e80d02c034140ca0384484040d140340a0640c004101d0103c03c100c2581400e0041640c85a03091a040092201300c064008407402041c001ca104a0364a5110014000082048a002d00300044c11030b51110114600f50b0107e8001d03006629070340d04c06000042d22414900810340c20341744251110380c285801c00c4014926005480c014400c20003c021103042c0d049050b2041c840c2c8010100c00214074070000030406800d5510920115107110b07101c01a0031a84030380401500c456034050f20b0300c103017458 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 524430575 1250 524429325 524429351
    0x1b0a05010e01120e070501020f071508150a0306060302120616050c07080f06180105100b0c03091e120c030d03020a18090525020d08070306031403040f0b0f0a03 70
    0xd040046114000d1030702c04100e00c2d900000640c0c108446c0260708403020040c0c5600e00940b92002841101040030420704459221340c0601242640314404420791200c03840c0120021354501034980c000c1d0b48441c1c1c2c80c0c0040c4254244075000c5031058820300c0040695040440201d00c40c510000d0228040100c00f08a104a082c800d104c040000d10b1a0030440d00070b41100444640c8071a01541d04a00010111483c200852418000c0e603106004c41c202c0781d160a89050300e165019806804151f01c68001004800703050740c2c1e43c003a240317810059440c0da40000004941401003190a040e85c035030017540050581516a500011450f034039400314580545c40e0150f460080e01d540504c14034031462400b41d0440460004111b501c00392040a0380030301000b100901103180c45540e800c00c4045001a04003d06c40042c50340150a5140c0080c42031600203060741d5644c496407402e50404550354640d420018007000028001c1c1488000382407040c1c00b20386081c000040400e10343c07094100c4a414141c891448001c3c3d6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 524431825 1250 524430575 524430587
    0x11d0105130f11030a0b0a03110904030507060e0c03071a07020f06070203060702010e070905190504081b15090c01051206041e090303060e16080c1605030c1b0a05010e01 74
    0x40c0d00654001d001540d040701d20001941c000301ca1070701e9814a41306c0704800034509080d54500b1250403408414494079040e040c880d0301c81004000b90140501044080300051103440341c3c41c0c00e91410405001c4580001040600b01002039002100840b40c41112050444d000412a202564100c840e400241045000705105004000000c1d6041c0154401c0100d26601900808170039019401511851902d036585101196003e86240e0f500307c181d0964644005038660007075402900075076a10342040a500800084403c0c00644440c3ca504103540c182a2819941c20481d000380180c00942003600110000030a207004200c440030106240303001060302a21541c2c07009200305000b1000d140f44103901450306d005800384540c209d000900d400e0000819071144140d45005034560003940d082e2a103403a404842945001c0c05900b01c540b0b04100030201c6a44d090000c42003d485030b0051920340c410310203010309140340c500b400310185030002805039440e0b44410702e10058540909001d03140c0d4294000403158 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 524433075 1250 524431825 524431841
    0x3050a11041206060e010e060d051c020705040f1b1b0206030a09050606010e06031f120309061202070c0909062c070b1204061107060203010b0d05011d010513 69
    0x40c50500080c0810408406010900711501031038081c004a0b0303450502100380407092285014440c10f24012584074a0b241280c407059a00400480381c1040e40041c008400c1250400c4242c096441104104064200f40c041c422a44000c420200880891f8805494000004c000d00d101001001d08003240304040704c280c80c401c1f098000e4000e685915000791500003c1507a21400d851030b109080c0068902d610400303042604013005440982151a00c104017090700320283c3c2c48041a07005000c0111703040c0080492102c1481c044c0d0340f0400b00c24605100501000c2006200f000081d0040041e000072a403503a03c031400700e0b5074909000640840707500b0034500801401009078075804011640f40d0170700703603050084140842c000c0c0a0380c207550340c1c0b180001c0b400c2c400e01c940001c2c0341c100b40c00010049001b550001d0103400b02d504079146481540e55031702c4201da04c00d8000c035456460200d20341c803c110840c402d40740504224100a00d41400040ea0205540f00c144200e41c40f4006103110304c200c1c04002e401081c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 524434325 1250 524433075 524433101
    0x2030c060a020709020d020904110a0c0b0606070605151f050712090b1810020313050f0102190c0e07211a15030613111206150304050a0b070801080d03050a 68
    0x140700c200c00242900070303608c205241c40c8520306068540c00e410052800300e90740100d1a88034855071850039507071032041210040a0541c0181e0a124290100301140034062141e40b402c003803010580080820040c41d0b0f000c9680c4403100c04580c201520308284c000d82160799982d0070100142c001c480686080f159800e00fa0401c00303100c9004100306007040443c1140418141c41140d0600d036030080814201e940c0c1c000c2000241070103460320400c00c6181002407a05481c2c0c4011300c1920401110840042140c0000a90031980440b0303c4c03030b0404c8486008003000c0d070090030510b04031040d860800320104400f00d9040400c415a030380c0d0031480d9070a42548145480d1054040c0035030880c060300a0b6588110340085807142c0c00b4074041106002348648034070078140c041ca82c000c16282084000070000700e441c04018540d94100c1500c0081240216100c006980301c0d503c034030004c01c07001d1401e00d030641145902800000a1084e10b9006021400f0f021451030008a89403400007041e69a20380810040e084d904403000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 524435575 1250 524434325 524434327
    0x9031207141e0a110102090a0915030606060503100b030103020d0308060a0503061807081207030f0e060301090b0f191502030f03070801080607020c0a0b0706090203010507030506010201150302030c060a02070902 92
    0x82c2400c04400c2c00b501c1c03210041d03181ca485580e100070010303081c1e00c5480b9482c1e520600c0701c18240480c3c00d1075030000f40400e01008140317080303980ba42d40c0c8600b1140c8a0300b0120200c2d4020007007080303505410088001404090114030b0842d45141e0100b40099142d40c002001d000009001441e0b41e12084100f400400300201103d40301d060410550a032707015424190b900720300a9043c049840c0c400003451002020903102881d25190003620221078180801140904105d0b00e0000c4c40d030740343d0b2424045e5001c0c203007928002030030760265000c0049824000195070301803903103544078400c80410303040c040045410282c076080005030b2000e8120b046108444640020060100c14800c44a0740700c14080c0c10f0b10a004103d6290b601ca41ea000e999440c1c40361041c81c0c0c46500c2c21014042d008085c4d02404140d40b083d5004900113005034006429100300f2104100082c0c0d0700c2c030801040f9a0309015203401c3c3c1e2804802042d0107030542d00425291031281a02e64000c90340000d0145050344200548002480240300071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 524436825 1250 524435575 524435617
    0x2060c031e031611070306020c070b0f090f0f0a0b0903030408060a020919081b010e060a0206040506240904030c0f0501090302100608031c060801180b0903120714 71
    0x4a003540080c3d6414405680c803020300b001440c0a040c0710042164950000c00d031803807542d501d10010b50b110b1200410540604000001d41150745c0e0080d0200140400559848119010501180c60344113000701d0300c01c1e8a01e07001e0500648820700640c05482a010b030255803041100086455031083c1d611101c03280c4681020485051070b283d010f003c20030001c90305003000b251754006030b45010b001030241112075003140102d04591480d0500075160000c0c18141144942c030f030500011026003000099001581004d0300f04410401c00340985a4080020790400c2c00074880842c034000d001c4543c003200c90194842c1c201040526000e0120300c188260b010803076540c061602c2c641640070f4455020100c000d07101d03107415480c900301c1170f006507003c0d40c1c42e00000718240103904884841c1d0070541310000340500d44c0c880d004550041c5c2070040825005607158400080720032441c1074000d0201c02000b90301180c00510207260084002c12030250050001d141140d4034245c91070400c0414480c455401b46080284004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 524438075 1250 524436825 524436877
    0x3160f11120c0606030a0201050a050307090b160b070504140d06020d09050d1e05070b130c060f0e0406060f08072c031c020d1101020d02030f01050a06020f06010302060c03 75
    0x3020307500000c1d415030b102c540340c2c131042c507548071580407000703010031808d02094503990b03c1240555804602071420041c240c1d541c114800c0c1c036034001320646100e0a05032040c40d0520240098282d08400146421480c103450110000015200d0301c1401d80320f200040c00ba401480136a40540b101c000b248034040002c0c3c0103505c1d0040c0d94090b0030308008085201058414450700140c541d202205116031102864850107544a00000c44020b0890000c00f0200c100390001c20300000080b009080c2584988060050b2402c000d040c0c02c400d100d40f20321407810f00c8014052140e002881544240a41c1002c2d40305480f400c80580d12160b0844d1255059480360000c1c16000085010303800380550264182d07402007001c05540e40c0417440d400348010169102c5681c001800f842030001c11241030300000014106094212442c060781d10503074a20149080f2000180424a410650070005100e103000614812404503c840c0e190401448042e226100100d45045220400d000b200e0745031010008002c82e004144c20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 524439325 1250 524438075 524438077
    0x203040f08070602150103081602030a170d060506130611031902010c03050a020903060609180a0b090c030a17160813030309081504060e031b0604120503160f1112 71
    0x4038543c0103215041200841c190451802d0381038070b4010250ba03140142c0b1010182100100c0707a802c0360580700d000f4000b0f001c2200408a580981d21000d1a00d6441c40c0c440041d00a07640503030441c0d4840c1c8000c0080700d11511202c0864000c031400740c14840740e03100c0e02e03000b0242140148051501100e5810100c000c0f056070640c82582c000d00144c50822142d01d50102c02c03402ca00070032840381e0300f5074410b102054041c503200410b2580002003821081c2d05000c0d8040081c108800c00c171007111890b80c84818044181c00c14419018400000d40091000e01010b46520504401490248060040004802d0100b200316014021035941048040b80d50710030400800464082c01e1006400040071b0100200340b0840124440656406a82c12080942c030b071512890014500c060303600450381b00401420300401e401c01e0416644da40900003401043c42c0c51f080448051106000d40403c202040040020309245406a4400ad00780c0349050315640c0c4510000ba142020801280785051042c1103401d2004e0381014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 524440575 1250 524439325 524439329
    0x1509010b0d0c0f141011120403060203040c05030c1309110a03030810050f010e01050912010c110105070e09011401090803031f17060130030f320a0203040f0807 70
    0x15500b40101c2d982c501003a003d880c040b604084d4040f4140b50f06817030807481049550b03e03080001d0140c443e410380032502c140c0c05501a0b8012185250080200300c2031044003070041d4028003095010305410b20800000591200070100e0502c506c42d40e920a60301440013454000483c1d100c0034000c401056107a080140c0905070840e944101d04001d028045080d040c00140c0022050301a101c0c00c200229540c01990103412164180750014aa143c080809507424000c50a2a4030280ca0b1401640001c0b40c4513401c0d580c00070b10f46c01c00d118180781d46644641702c2c0340035181101c41c0303080f84440d000900030048808803400d0740310700c100303100c0441030220100e41415040100040c1e0084804400d42d1844d580080d440040c3c0180056000000100704219071840054486807001011440021a0148200b0030b1500d80c142507001400384031581010303c6c2c01c226000300101d19003031541048001030400e081000300d00b200641003c04086210503496000f0410784026010300c1455003d000d4849140d5950340a84d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 524441825 1250 524440575 524440589
    0x60a09050c011103030a1a0402040608040b01140d0b070e040905161d060409020112020a08040309140901030201050d091a06040c0801080a021915080a0e07081509010b0d0c 75
    0x103101621030035809007440e9086106040f003e5030031a40c594005000401c444d96403541e07030742c2c42d4444095490781c580c40140b010f0100ba031240c114034206410b2001152005800074003ea181d41018070086640c0c0c0140b54554030b5024084507220b50703076223070b04a8220000c0b5000075001402e24a0b4001001004500c0b202d018000c1090180525a02d88040f8181c47e00c100480007190151000b0840320f040a8005a0400e80103041010408822154500403a8046140f000008032410184800c1640c4000c4c000c0c01424040500c0c1000710052001038248070f01840300070b050050000e00304082c845c2a030800c03145c00d40c010380b1101050742c007030b5580421024101d520034415407801242c40c401ca0b014200950683d05050028080742c0364603070278000c2180b01c1c1e030101240c281c10000c0010301c812100358a440c2c962825500d0081c14101400e0f2202075a60740604803035981c00c001018072044000180c2c02000c1040906414070649031588050300400c0101e002c0382d003200a402881c400c0c44440d030044e604071150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 524443075 1250 524441825 524441833
    0x4140a0c0f020a0309150e0312030f01050d02220b0303211f06230c10150b0a0305040204090b0c03161b0f030210060602071404060f03140102040305060a0905 69
    0x2480c1080342c5494076500e00801103071117a20300f4040d404155a200c903081a45003000b10f80c904503a0300107031034001d5203201100d11740d4000080044c500641544c3c140104011f840321000300007142e0001d04c04480c90401c0303020651014181e1001803c0710341121000c1070002c1c0c1580d5444c07940c01401e40701c200e03c500021001d40558008141c2894420f580030b4108414014810302081c2811001c54030640d030b881d20134070310b0703103c0c01400780301040340f44e000346000b1400000411203000c00c090b09030203803151981001161820f45800b00102504802290641d9695180000c2c540d50f40b4800240108030b0303002c020b4002c158a40c1005002d280c042c0c01035001d881c3c00803400c7d040d0082c00008541e07035100c028841c0e0500c00102c12100c0002c07801522002014420b00550b107111034080c0003c012503880d42d21100041e88400b004000c241410305021901e40016141030003002d00b800c000d103543c524244001003058050300144490b02c02c0079815107010f558417906544203414000a000040c042035407081e901409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 524444325 1250 524443075 524443097
    0x60106080f062b06140903030118020d1b080601020a110103020d0f09050a020108180a0602030604180b01051314070c0807060c03140a050402011e0c14011b05070c120204140a0c 77
    0x174822980f900c20320f4060010f40c916802c00807004d0481034914014003419800340418189035107a0300410703181081601040c0011149104024030560014010b6070554014a5a10000c41c50703100400c182c1950030709025903200e095485040080001c8101c1c07030348140ca44150242007010100307080302c0d058001d0b039a0340341c20b8a490400c404011010040402c299000c48240c1c1d0000d50765401540d0310000003040041c070029200c02019980e20445411070740000b1690040c880c6140c8600c1c030841e11410014100030700103054172314020503880a0000010f0000442c0007500b0880d0762000c6030b000a41c042d105110011040c1c80c05400744ca000c40c03001403815440f8001802a03071140c07180d103124540583d01c0180d040c00307003100011700520181c10807041000301c880b10f00114400b40c40e242c505c502c0180c0009804003c1c441d03440b8205d0100050042004410040e05000c11808401c1205a80d441c5550488161304c2c1d1000030010140445a28560400801041360000880d400b503031400e4000e444420480c0e03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 524445575 1250 524444325 524444351
    0x1b0206160c030c1406040b091b090f0406200d0b010e0310091b0305060f0106090f15051309020c150601210225060b03060106080f062b06 60
    0x4050a000c21000400069000012030310501e1500d030b07014040c4412030a030030707440800981444070481d4141e4a111184082c81111601003140500e08a021420749444501d0100007c0c9240f6014240c030368644a020042028010395070310040120203050030003010820750180226458201003a1114207a14215400701d455000d503600382881c03a0700901030000054030115450060414082c1950b411141a00c0c0c50b041405110611001e180150014030042c9010040114003140503003002080010409d420080102d2141c03294090b03c03c0490103007010800d1810403603003405101c1120b0300ba021001d40000d000c0c00150700501e10021000c0564001116031903012541000c152552800928071070300c42c2031b40f041100c1591140740348600c400f42c0742c44031004400781c100c41c40c00d50f0100780d122040607000400c40307035210f81c0b9007010082e0007030240b13580f4001c4040d046280c01808042d98001100008803a5500c0c00554044905903407210020358004410f117011800b0804d408440b05440e20081940326 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 524446825 1250 524445575 524445601
    0xa1104081c17010b0307030605032a0d02030d0507080702030d120f0c0203090d03020c06070c0e01060801060f0507050f0706090801060501050301030809190b07121205090a0209070507061b0206 84
    0x405004412402d5691801401c1c90ba1070f4402410002016502d00e070100d9259001d01c101c0602c0360000c40399200104c070302d201a070714030000743c0160f610a1050850500050324003003034481c0700401905186483c1d99050038203641e05c2c802c82034001e5040c01991140040d11350801410051880103500c104207440a00517018201c0c0d0f80b448a40005d84d200340810030441c40c2500d00410480d10030310645500c402c030b501c00304480d0b400881040706d0004610f5000c3c4444003052508600420751403429030080d501d414030181c10030740c020034103500700000000c0000902200300320541d00a84070700c3c200d0b00c80c1e40c0e890400510001384d60140000e554204000054507612420607a4180c80d00801e100d482c2c07134541c104000801c6401002160540020000091001c1201e4060040f007402192285046aa11003000f420044640803402c0041d14000900051840004030203400070343c10303200c0c1c1006403640d4106031502d015541000300001d0800c94400300500301183c800b124410380d07408550741750b120300d80d541c212 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 524448075 1250 524446825 524446847
    0x609130e031216090e06061c0608010e030f0403060207020616050d022509020c0f060403020d0906030504080702120111160c050f010215100323100b0d02090a1104081c 73
    0x1341d100b8800e0040f1429081c0c640d80007107000309807900d8145a503020b00d00e0550803400a0941076502e00c1c013046500c1c1b003170061440c200b0461025500d0003140340c0c5074801c140964000608015404107100045480c0e84e4100d4124000c40c500c1d07540303409001d280407a030b0b580c0304a5001c40140911104c1d070580151000d04d1400d0b5000350b00c1c03840c01c007034108000b2a000350014039101302d6512403c55401d90901090101600490196000c0c0144c030700c1e002c0d000b0303240403540d600c8641010b182000300004100d101c0c0544450540c112071041c60394440300e0f4400c0c09041a0310031480c07188400241c8a0f82c0019040e00e00e079a103840f85900008496a410400081e92490048030703002d600020040b103034809406000d268444464500e80740300c140c8075190340c2084e14812121a00074007449402800c02c1e0f40c200468030590091841c00e20042ca000700114a55200c80000240200e03000008580c602203030b41c00c00c8102e1000c83c4811600d0340d590300c841c140d88001d03c80c060041c4880c0c0542409a00e84a1101019 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 524449325 1250 524448075 524448077
    0x1a06010e041b18050307030803040203070e070c0501060e01210609230c0312030f070318140f0601080c0118120c0f06020307031b0203030d05010b1b0114060609130e031216 75
    0x71002c7d00e151a4100c071a800100304030b03414041c0610110b00c0c803030014145070090210f0b59036030844031043e2600500f150b401c1c0d0000605140c03143c0c0100429003034125000c0b95500d060280010000390f0340f0748035000e0115664010f04002071401074000002c100d08040e01c85140341812914041d0012080c503480e1800212041e04698042000030000340c58031003403607003102d21890001140c0400e11080321408418100480da00c141403158182e400340100810b04500c9503000103800d8551500c40403070f95800c080340000e814442c0c0c04c103404803501c1c0c0100501c002081c039807541002c0d01d50b041c50251592400350140c8141c038108920f0101b040d0303100100740d61070340b0382c1038655019103100e2180a2000601c4104200e0745403000f04921180d50950707020b45070003080c03c1460142ca0381c0d071100c3c3d07600c031040380c9500e080765913850a40141140500c0c6500c06030060019100d1960760324415000c116010041003c1100d16070400b010440326407400070082040349084c2c08280720341d4588010600ca074481c200300c114 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 524450575 1250 524449325 524449333
    0x203030a18020f09180105070804020103050f07020c0919090f030f021203010b0f0d020a080901050c0c030f0f071a0a1107020d060b061b0114010e041a06010e041b180503 74
    0x202d900e06110311655001660fa0400015030698005646d003561422030300c140000320a00107000441d60540200341d003004c3c4040c403000700d42c81c0845000307503500305012159200d5401c60f00030a01d900041c00c403075140300ca20524140040702550800520303000e68180304400143c488280d094106101041450000c0303041c031811865079103481d07042c1d100ca4120036003081016408200035000d2590318801803440c00000d4840d171074145000c0522600711240289608652a010014581600c01c08401c5074003208882c0245c40e102d0041100160050059401c0180b028402800c02e9200030307a04c01d00c2c244500d03007995080c44a00c500300082c103024000c440000b074000c0d074049075003030004040b60814075000001505950030b204001007041c0b00002c010f08801c4169540e0f4103103055000c1039100840c0500062a5500c0c400d080a984148a003070104640d84003846242c40031580c00c1c0c0c800c2100003010100204144503101c80d103641c180400100201810204400800c1ea000000400003080c04465004001d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 524451825 1250 524450575 524450599
    0xa0209060d020901021f0e010e031c051005030d1d03010b010e090618010f0f092309160b1b0d120b060d060303020309130513021507120203030a1802 65
    0x700000e034100608550560250005032500d15110f2000302a50103c080c00204050b00c03041c001d1400c49100c22a180182c1d04204414030301105005458110201c9548002030241e07a144100020081150442d40d4580614003810f4a00c17036000c0340c903000724400f0050741a41d04914800300742c2200e10903440365021415020080e921482c2c800c00c01c81d41714002518100b403142a080d200003007128260403149090b03a44500074440c844400903440b0140407928410040d884074005030741514200ba402e2030030780401804c0000c9440c3c1007404400440440c0304a400045034407200440a241c0010720030701480c480c080c183c141c0c480b50000f100d858404464036840205043c24028001030042c031190030b9007018041104001600c0c141c03141d94000c6002c1d9020f10b4995481204002e50010440003180d4194200801d01640385850140d94014030f80c111100741000b0030f00503020078503000b038000103089803413007100402c00690003000441c41485068410094452245a05010441a01c102030b400c6074284500d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 524453075 1250 524451825 524451847
    0x71b0f02010f170702030c0f03031005040e1e03040e0601050a140c030f0706050f010605190e0d1a06030c0a031e0c0b0f130b0a0c0204110c070e0402090a020906 70
    0x2030050304107220f1914450a890710110b01c01216426201000107900021b08880d8051061040060803000c0101442c6507040642c0d8065041169006440c030030f030703901c415000c40756104011040c4601035a41000383c01c00b0500810540380d811a10031040c901303200c00005201c540c030402c21074018443c2d6450390b40c40c0c1c0407581503940b0150441901008903200412040f400d55260b04050030034244244400f060354030f818944d00da024801030b4080c2c0d0a008041c080bc51900744a254800802100c40c500001c1e0100000005602d0011034540908103102007242d11030030342034500509109078002c1e01202d0300800d10005114a1070703598440501408011400240419000c00503c0c900c81d01074413803d81804c0d25928440400e910410200003410b4001070294600d0700600034000060032100314080c1000000360b000b41ca0034900041c0203110316501d00360003800030704140a07240c0801210f8100e40400d074965a15284420702620164812071801c0001140e24045000300d0b41c14182c0500014145420491 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 524454325 1250 524453075 524453087
    0x30b04030c05120408012301060507121b0506040c0602030306180606040504060806011a12010608040c03290c030112030c06020d050a0903170903031302040b0315071b0f0201 76
    0x40110b4903405607801040889403004090400307000a400005810341d05103e00b041843e071040503480e01032110300300401031140c100d016a400e243c0c01c2044502180c251180844004003c80102d001502d42c2542c1c0714140007000800c0ba1040b40b144505a18068407414180e03074a000c2107030f07490381c011208425058035002c030340c55aa0300f00f400902003034100764456000400b6a07526800c0f05126520a1004014228240c0401c41d12000f415105900c1c06c0a0302c0d03181d14412005018440c10302004002203000c10541d050003400454001900e00c140c07001ca01d920102000c4c094031b004c540c40150b403001c00c40a2142004803412200f40225018160381c541e80c1c1511074000a81e001c2e03d03041d5082c0015040b545040c00340500c26540804006051810b610f0060800e605c20f42040d00402c44000c02c00c44183d2001003140c0c2c0000305039501003110b00c10ba10002d8058a44000f030282c040c000d0110041491034001f00060052520382c0f90f0100061000c2a16006c400d6038001c0504103d8005c0843c0340035501500d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 524455575 1250 524454325 524454347
    0x8240d0510090503071b0e0103030503070203090315010f1a04090e16030c0e0a090309060e03010f02210c070302030f0d02070b1008071e090e0705100504030606050109030b0403 77
    0x2001d94407200314600e035820444450480c00d07100340d08000b40610820035140c519117554107a4843c40d200040c101041008400c90500008081c000004045030641d0b00030070030783d548280010f08840b0410029441e0901d4120280700704900404902408100c17120a480c8258020841c900d42c50309092403c0303d108003800764060400c516000b807004000046c2e01c07484042020314007820304448802d15101c90078880c0240200003141c1580b820501200203540800380c41c04450149c5881e030020444100080d00401003900c070000c45910000d103680e1821003010594050b2503000c6a460101d640303e240810301486043d0002b00140c008010080c0c2035107503800a00a40b040741600181440c8050f911100ea103413098500d06101c041c44801000003000c10804040a400d070b01007010910b4900741c80741c0801c0f400c103014034040180c80c0c1d0303202c5210072020400c180c01031500414180c0500d60010300a030050340680415600300382040404251540270742038460840364010f01c602d100317581d1900c3c1181e100e80c03d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 524456825 1250 524455575 524455583
    0x702010c1b03230d0c050c100e0d0308010e01060c02031c0507060207060212060609010c031116150306121203090f050601060e1e030307120302040b030c070308240d 72
    0x500020012500d40c1038012900d0350450310080107a945000340625041004808000300301032008517400013503000c41c4001483c101a143c45050141501003030b82d0403c00c607410706030042e0145001c4014941e001d001d05040301c0c000661488903907207604040b6989042000041c0d05540000074000195141402c5400b085100c2d24216042a03910369230f5409070b03400721005540ca03070340114906080180c810707600750300000700301c0b44145014540b10029044100c0e0306405011f01c9903510a4554004081c040c05c5620315049a40c502d4a0361600b4020b540c1c005004402e41c00240340c003002044030043c64603c1e00c51a40c0090b643c4041c0840e012044001c1c01c03183d0030460f0001600542000014030801c034072800380c02107480303c004c030003800c2d018041c1a11035509102520b958405100b54123071000b0040320525070304428001800215128103601074401d41e40102800d103000070070448620500f0018208042c03190f9108a03140d210184410000a1103030844e82081a00000e004014603090080c0e034111407003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 524458075 1250 524456825 524456873
    0x180408130807061101050f010f05040b010c0602030405060906070c0804141201290f06070b071b03120608010c0806130902060f180907080a0510080307050a110301020702010c 76
    0x1950794079401c0c90290342c840b202040c095501c4004a08081c001c09a00584802c025031246d03142c80211002031140d44202740c02940d0302c0d210440300703910500b011702c200fa80054056607203040c54a4020f03964541202c0240d228000c28000c100c1c16031150306200041500281000d0a180c240740c1044041c00010301c81e06d03880f002036200200b00d450280200708404030b00c82c10b18076555500e103290aa42d460b9541d211880350001c40d04004050f07403280244d0303c0140e04080d14014907542d200b42500c0907194044481107510f5211100d0081551283c10040da044900c6020b1100c035540300107003070030b803401d200303500000c600c00100240c05030400c0e488400c1100c5031140041006151034000c10025401841100303c0300f58001803400c0d02121445041c420ba4401755003103001c51074602001054120094026030007a511000440c42007440d4509000c09420031400340e03555102c280c07801d55500c200d080821201d82d482c1601603c001c0c941072081d0780e4a550180c40d070f000d01d101541d0712000a4400ca288031114040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 524459325 1250 524458075 524458079
    0x40303030b180405010c020607050a0206011a0f0f0d14060d02010c06020d1104050a17060a050c090a06030b01020609011b0c081b030409050109360b0a0207020f18040813 74
    0x14042070b03000d015030300600001440b140d81c000028184003006040b00144181001401c00d80c541c00180d0b2411603811805401240b110f0b4184a1404c1c42031903554800303070074085040041c182105000741101c008181c0108031070000d01418413140601110840d070f01c94642d440341009540155a030010303003032103441c0061511f8120500c81040790844002039040c0b04012506100c1c80c00d249074a54050105142d0b01022984031000c1a42d071480c0041034058000c1c0c95a000c80c4646014800340d07035003920001c00041c980d0f030704c41d84010028060822070a005105a40100340440810b21500f05e20003c240d851006524070440c1c2516034488540017200d04070802c004c214500300d4a0410034541d01c058001942d1f035140303412040015184181c00241c555460000d0000500c066035100200408049090002894012000c12180f2050390030107440c1e05655010800401c180360b00818034070740708461070740c0804102024088003603032101414074090503800c049400304a041001e00660804150401c072101e07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 524460431 1106 524459325 524459359
    0x30303361207140601060302121005010509040c0516121706060706110d0f020c0709050c0a03090c0b041806062d0201020d2a0212040303030b 62
    0x881d00140740d4040040d030b4195820b011822506407002ca680d2582c0180c0a54003c41240021650010000b001589010084c009407001130791554108020300d01484001c01c560145002800703001d020806402c003101c00b810012610580c3c000b2200068154003400c2044d12501000101072041d04101c0300740c423100c0544100580210b400f080300129a41111218411240d40789822801c00d40403218100795a0002d0000ca560003040f03840b220390322070301c12080700d1054640403040c003800c010103d1558400d420805209001e44410080d8690f0b0f40c6a000c9aa4484d0b800364601510556a00800f20198800c000040501d410242d44210302840404c0307034074455040d02480160f40326912005140300b5816034125103050035040080351604440805410b404024080c0b540308040c0240102c2c1c0d2000c00c4c1c0400e0010744060070340c141411350f642500078090514020b42c0112151146172800 = true := by decide +kernel

theorem cover : BRFrame.Cov 524280575 524460431 := by
  have h0 := BRFrame.cov_init 524280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 524280575 ≤ n) (h2 : n < 524460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
