-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2727
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:33:41.041987+00:00
-- url     : https://prove2.me/submissions/cc2aa0cd-9e89-474e-bb0a-cd75510be850

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 490287769 ≤ n < 490467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 490289019 1250 490287769 490287773
    0x90905040606030c0305070f0906060f08130203060c090a1706160201020c10050105040b0f061c0e0f011d0a120c0609060e030306030c0d050c100c06050103050312090d0804 75
    0x240001041541d40964449010001a41c0840720200842c0603000426040d41054003000b851075442c9e00000001d03191420410981c1e41085a4a03080720350b40c10440d14907518a140c0914200200030000e501d8000c2c48104044d00e0314210183c140c40900340d0b00c8020741d68403543c07105082a4001500703141c0e6880300b00007481e440c041d42d05203200d00c07603d880090b040c8005080002e2828000c008610203860710781e0018003030780c01c3c984600c01c60240110303079090040c000c1ca80410514420b26260003401944401090b880c01d003560440c01301441440c0403a0044690420360500801c0f44e00d47c44001c0c40704c1d00c200c890383c03410700003440c0000c035800c64580c031070620014006442c29a1038500c11500035844880180114903903101d4640d4200e060005141e603464984100f60900c8140386110748251144120329012660010b070205003030038152000f071500703458204140ca54036041c2000070256400c02c070020041000200140105080340c541ca40510b403118850140c407850483c08200009032060000f0700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 490290269 1250 490289019 490289021
    0x3010e1b13090209010e03030a08040b0919060504020f100509101209030c020909150402090a0204080618120412060b1315050a170d050a030f0e0d0908030a0909 70
    0x14501100c0114240340889280d002075410701c81e03501c401c0b607541d800300340d60095581050301070202c900110069031a003040300390301078044040540040c1110130b00c100040c000f12000c102000300205101101c00e0000845d20300880a04406ca6049020751941c1c44030342c03010700340424041d0052000f503c0e094145440740c030500c074602500044171400c111404522000805a034030490036164000d03035803441c1c481303c240140300901102424202c402d50082900c002c00b208441542d41d080750303040343d401c940d98072108844406409907410201c0c55008807800c0c407080e961415641c427100103c007001e91742070a0000c40284a58011407040c10302a82d08440c100c0000740c1150f01c04503502e00d0042240c0308107108602c503001203414103078003800350301e504000170700040c078290b0800801400c01c100410054001c0c41003940d2117503a10182c28040c0507000c1a83c400946c001c1d00300d4030310044040c02c03c0090a403a17480c120703554100c051191012071281203001c42c1c0b41c603011046070049100e03900c070045118900800f01c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 490291519 1250 490290269 490290301
    0x402040f150201020d0c0215070e0102071418100305060106020d05090d05010905060106050a030f110403030809010f23130c05010f0203070b010b0c1002070f020906011e111203010e 79
    0x1074115503081002020008843c032030f00084100701d07401054896104e050906c05140d02503ca00144026000c20140f03981c1e0004410083ea0004e4100c2145082000c001c02c1c00c0b40403490444400d88560420882203000703c03c0d405040f60701030000c440390750f41d03a0030041e03840c0e0300035500c0203000403801c200b03503081030030418131027159903104100016081406031038150412000f0780202c0e001680001ea10001c40742d05025091040d01c07501c400304010307a0401182003051190344402001e101501000942c1d0307900070b50100a00c00000ca9050001d4011007010042c2021904000b46080a0500128a42c4000461400140c503401065250171504060040da2100316044142c400c510041088a0028580c000030a000b0956100600d445a21052071142411031540900b2001031060180d100481d1180705010b1400d0b40680e0728032595100c1e038004031140707002540b105281126143d41c0c00c440340e6020b00c0020f01074070400252401c0c024003600c07581142c8000c0c072440d074183d80c01c1804128070050304c005c4c40b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 490292769 1250 490291519 490291559
    0x30603032a010608030a030b03010501080c04110f040f060906210218120604030807170705030709081c0807140d020f090a0f031b0602060f1b0c030d06050402040f 71
    0x600141e2480340c52a0944283ea0010103081d040801c2c031410494150045010755902107000303000940c1403805403540c0d000b1041d4424422600c81c43c40342a038030044021034105800c040d40b940c1c2d0341c5440c0d41c54045521460700c590000250300c0d0500207400d0344180c0c2c1020203030607880302c805191040c1c0d03545880a0b4000111b48844243c140c01a0040c641d01c5104203201061160080c040d20318003070a0185c00c41400070b20000030322540e0000600e2203d03603071045541c005c08500f0503e0b20380c1c98100080f50084c01603003200c0d80c40d100b8869501281e2220f40f5010403840d40307a5540b6101565004070450b250700303410040032030840061113034100d03080c0250090049458002c000030305202c403080004540320105c0c3c1c44a008403110010a00a004600204078000c021010f40311285078a00203000b5607a240060108545084c1c002c0403d02c806802906130100c0410f103404251540c4100101079100e51007540c20b6414140f81240006450400e8025202204c09113000400f07840c0c503182907401c40130840d08003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 490294019 1250 490292769 490292827
    0x12280207090c08090f0303010803030403032304030201020304050618070e0c071a0a110702182806060909090809060d0e010c031407081501050f040305030a03020a0f0503060303 77
    0x20425071400c1c0304001d40350791650b98500c19400c00c100c6a0f400d21043d164194101c0e0420401401150000002c40b074001c4c3d40b500c1c00040740c489425201c508201e120228030103c54002051000789941500698000c901800a0b125036803115201c46540c0c0ea03c2a140d030000d50804c5800b048003182c0d0500080d80f0407100705d00149400015550028000c01589400b8107410704402401030908903482281c503500c100c004190302d040600d070001074800c841c0c004007070400d03208940000c1d00e0302030611081030100761601107250014980811302020b045903028120004115181c001409842030054000068020b0b0600341ba02c407a00e0140407099000040c00300381c45485400c03103c50101c0900c6034024070241e954000601e034004002488441001402c00c608020a43c400e00c0440440c14052410145090901540d10000304a400896004a40c000f50443c000401e103240d4858064005280d85c010690325620502c1d0303460780a0341c0601090302c0080d0564803d108103002c500e00300495035031b0000c111103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 490295269 1250 490294019 490294033
    0x30e0d03030b12011409120d1a040f06050f0306010b040314120c1c0512072102070f021503090c06070606080109030306050f061215040b0d1202122802 66
    0x70102d0055001100d5020303d40c2e668034074070001004588411030704000180061314038003070709144442c014041d07651110104ca50744c0d000c003100c400200d102864000e038050030601030540791008034002420503200e014064100d00690460310300d4081040ea040e103c0c00c3c1051402c25003103031250058407161445038001841103926040c1c0c842c0440019155071031261000780f544848031a000c0038120314101000d4140041400f0211018020302580d590184282c90f010150004005200c6004d02074900c107050414400600d100c24090307121601d103000d50082e98002e90304d910002d59644a48821220362006d900410b0140b6214030f4000b0007025000d0181c000464480d46500e0f040d0300310703035403c07208402290f600e2108011909041c29100706000301280d04508107a4517200315403406a000740340d140e0300352004510342c11a55607039129528214014180e001803034641c3c036000b10301010102020015205422503030b446c2c6c1c507018048902c000018100c140700d0301106201c030400c81100750b40b07100c1540129030f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 490296519 1250 490295269 490295291
    0x3070b1803030c21130f1e14060f0c16031403181e0d120f020301030302061b0415080601140d02180306010311011209060f1406010804030e0d0303 64
    0x18502881943c001140e64442010340c800080c150381355406024080700c0c0070044581502c0d030352a09419044600890703540000d20b055008019400a000d145d031200303400003024480340044541c0b10711040c4007220415240e4600b0a031a25004445c0b04032810307010455002c4403c070382030340034102d940302c0d00703100096003100311000e41e254008540068000881c0301c2003491841d410803100e000c1c0c0080340c4802e20388641a00c06580c4985440300034406101400c0c8a031138508080354020030800c40d04070000c540325612858000c0d00d4000c203076100114144001000300d050070b40f4204440c2124404070030008031204050b03040d94007440003820103040c00f40da00100301c0100c0b0500d00521101080e02d40c0180c4d80e40c680400c040482c031900110b0350290f44a0f0005200041143c10320100500c004d003044801c041000c18130001914000000038219410801c1410f181c8003650055000740e04885804010765a42c3c60044602c103c0840340600046c155841c0c804140c20880d11003048039009142c0481c9800b802 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 490297769 1250 490296519 490296523
    0x30f0807031704032c06030a0b010c0606030302250b04062010062c0c090303070f0605060f040b0d060b03070f03050a020102060717150d05100b04050a0204060203070b18 74
    0xc440640100c2e03202c10b041d4288400703170110f01400405000707083d40c1d01200030000c566035001c020715900c1e0b030950700e015118042c1e014456000d400d503030014090000f00c0c1c03a460020b449244115846140c000c0348008000c480111402c1e040649908202803424245040c0d4101c640e11fa0303054006582030107104a002c2d14100c180104030f0751291801021403100d103050507045106000c03200d0b80f001c0744201a0761040030540f21610300c4d0030000070340060382c44860410000f03042d07102c0d13013500070114400c80902d1000c000b12908010f03c2004121a80c00742142002c060005880040c0211580311b50b0b2070300d242c4001521548594860f16010f401ca480c05500c600c042400103499400544403640514043e00856038100510355101d0311525000282c44070440090141034005400c840003c1e00071010041c6940303c040d80807100c140c200c003c4a4040381001c416000070300d80f100965001d5402d200004045114600071a4121000365008500e40100303a02c40359580c0c0c201400ca5512243d0344001d6103090340d07007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 490299019 1250 490297769 490297771
    0x14010c0305090910151407020d110619080a09050d12020f040807090e01060509040b1f180b0603090c0607080f03010314010b01020a0c09021803070f0e10030f08070317 73
    0x1a04d410141440e0400c4090324440e008041602e04006075907141000009014040c0d9060681c19110011020003d146c07a6501d0b202403c170150300f240b804940600d00e41c417090b0380b170079008495403210400da48480c1718050035501c1c4000054003960080300c103201c0b014441d124642d41d045001400600380034010124001a5000b40e00000d40d42d4061081400000d0103481814102070300b03030008000941c81c0401207059160700802c0603124518440000351081c1d240a003216007001040080384103552915242444031810340d1217a01c45904d05150350206041c824200c0e406680000010300024150404010599001043c11141c13407005015492003000040040c3d03010307502c1448051034508201c400b0900711a0340003400303411948042c0c048008114600584d200780d5040203409687d6a02424201c0508400803c0254151040310070000745000f113441031a080e00c01c00400f408036a142c0e2041920085035600010345804900701c50303080000c00000042c4020742c8242481200d003500890781c100e190078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 490300269 1250 490299019 490299031
    0x1202010906060e10030209040f08040f1e0605090f011704060b0112090f0b0a0207021002030d0c0e0f24210a1e0509070e010b04090506010914010c03050909 68
    0x3440e0940c24041107528080c500c0a803203040c200c0151440c1000e0303001a00703240c03440064041d1f02403901090030301003100c0c188200c15801455113540d0300d40c1c0d80160360aa1003140b1403103400340e0b030111328103112020445550048500b81d0f6125400c2c08048010003d08404400e04181804011011030101c1e80e20b51580c4d501c0b0741e008040008416140800140405a0303808000106034604090710000564031511002c4554000700540c2c629034850360394000900c50060003941c003d85840d9066049603000005203401310034401b06204403013051100f0744038010b00607451503010a8500c00140705040580760180724500070381070240c070715031729010003081640525094070038001610800c203035951409110b030360440f030f0b0000104081c14480c040e0300040b88034020f02c0c90405880d400881c9564070104030110243c0014500c417050355941d0111091a5801845204442c03030420000928540c0600a007404503075548071620364404c40301c0c004548a050000c0100c0500000b40300103450b6450315a000d038400d0f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 490301519 1250 490300269 490300271
    0x1110f01060f06170708060f12100e071a032a0d1b0518130c08090607020c01050406080901020415120614010504180e0303090706170c190309120201 65
    0x3034204901014800e2075900310300c1c00e2101000c030402425022444c2258080f4007440e01c0e9405448603000180036810160401d94004034114020b01c151001103945103040030f00407402c1015580c0c140c401a1074001d0351198002c0b40100c5406190a40041d1009561208407a210a1503881004244a08940360007240c046982c4d40480c40701283c076541d00c10070104900c003005011100110706c2c002031051181020a1100144c0110200380645400307245001d031095108043c0600c030103460000344802d83c101c03580401c1d4465000800d2006001281034042020103955451030142400010f449081004c0e1030251159403c0000043c1d110011511006005556850f0360280a5410521065815641001d01c910290170680801c07681c0080c01c842c00c890410003841c0500e100000b201c0c0040c181d441550040c0d001c00400c110b40c0c0c0c40c021a9080030340d03005031110005900c0c108240650134404499010103d035003004089110f4505108004483c2000e03c1c0202d11202c0c581e6580300020a9110b0b100090b03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 490302769 1250 490301519 490301531
    0x1a0d093807140d02090343080a0f03020309031e0d1e0c030219110909070e0c090f0a09051009090f060c120203150a06020615010e01110f01 61
    0x15600485250342001c070381c1c90024800000303805200810310505020340c0002c1c1e80060440c8170760320b091009255455956005045564603090024141d0502800f032034002c04118040c0b10544c120702c10441c050320704075801480090055500c0700a0384245007415070662005001e600f07010742d0300f00a1081c20760780003001291852800c800c502d1811100c58844d0b010b228000b100d4902c0840040508010040f9030310700b1b0304034508c1504041e81486010360b00d43c20850b10700548101407000c0100c034102e60300b40c16a0480807540e54101140c3d1588060700507c11180f1801010034040c4a65030040d00c042500180750800e2154240e00040d04060035a02200c603441d00e84040088101300d82480c07800030440120240300d0840755079505180d080c0940c0c802010b00e6036600c400d8545610980e00c0c00014019910119900c0c24403420a0b0602c14541c02c1880c070507a440c03032010038035501c0880ca2500414400400020500c624001503910403200b0321200d0410030900b80c04c08007180108448415003a04000008007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 490304019 1250 490302769 490302863
    0x7060608011d06040203061b21040218040506010e04020a090c0315120c03120e0306250516060504080d020a050409110301050307170a06021b071a0d09 66
    0xe0070381e00042d45a0040d0b410400540c90200303200364480749400021540b41072040e006400c1c0d0007000002e40e00e01e46480c4504547c11490f005c641c1c00390b80210b442d20051002d10038209003811048030000c00540100c001080003921480501d50845d00c01081c209190b81c4034000c000c200d0b24640506000242c50f0094141507181204110000e01100c84c1c00303c01c40182d03034550020400440c40018281041d942031018100d104044080c144d0b0f400800b0b5070440e0411200c6141c1c11700b04070858401e8000c1a10300316000a004108840181091480710b02c400308060b110a0001d1800500c140e66041e410030804541c0c2c942da00c010850704c117613504c426440b1820042030204803a240041c10319245002c00041c4160703a00054208201d0700a88030144100c061943e105003021040040146504c0c000b02d285181d0812244c4110f14503401d2404494242e6a550381c440b03146e200401c029510040704101400252220303030855042103028080050140b40c01d03424517551704084424400f00f805640a40c0d5007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 490305269 1250 490304019 490304051
    0x80d090b040b100f05091e091509031606021606050a020c07050d17030405010e0703030906120c1d1c050307140a0503030a1a100e01020c010c0b01060e060706060801 72
    0x24100a09440d280c083c9803c0c03000201103d06075001d05881089524001541080440c03480c8080108240599005082000d449650b030100810702c010180711103c002040801c001068600042280203251680c18030340c0c951100a600040c154521050059903201c08686140206402030700710001c0180c1d85c0c00f020456074204141a0005481039003d03c000d14086294448480803031160180d42c80e549440d54a0114014280701404081c40d0154201c00000e060300400b0a0007100c0b001e4a45683c8404412405011502c450352520081042d203e854068072124042ea115240000b0b040e120341400d003c17040c5410880c070000304032020780c40064200c04001507000d0a00c01100703000c00428441a082c0d5940c0d44034000100b032084156994110712005100c0c01107203005004008d0800d080b108418040180200524001c1c4c81c09445076450000700344d4400d103400c00c80240c100c4030706103190f401c1000850b00c010300c20421962200e8244098004144284078107402026100300010b00e031408208010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 490306519 1250 490305269 490305271
    0x1b06051801110f0702151e1c0506130e0c0301050a0608070506040e041101170708060114040e19020903070801150605030606180616032127080d090b040b 67
    0x1070b081407070600004800381c4502e410344220590448a0060482da0052031412a00400c1c005641c402d04d030b07024658080003103400800080c0d0529101c030490441188440c41500c1044d1003190704401c8034884903c00510542c8002c005609007004d031848a00c4a60000c1e00350f850030381c0c695040e140e50744005c02c0040700803c0304038000d2206880443c10245080303c0610b0205000703002810714076221072500c6140e0302c110360080d89410401d00080940c240a000103103c203108462103404a41e0f052415000c0c041102d0603202200c000c1c0031080e56079078486440d080d543d5190010a02e5680d000d01c22000030790350030322046001d812003000001e018520130086a01c441e0465000300248030703040041c8a450b440f0784044654582130885900d41482800c03010410b00e100b0700000203e4000507041107010141d108402c010400d00c51070b03031407408000c000307250001c44207110035001c1210a107038180303100d01d000d62403040c0d4401d008903016800c1c0a210710f2101e0540d00800d00841c0c40d20550000c110402038020849 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 490307769 1250 490306519 490306541
    0x7060b2404080708010c0c15021e120114030a1e050f0a11010311040302040507170c04060306080606100f020a150b1f020601180609020a03021e0304020306071b06051801 74
    0x91206d40d00d440c40c050925901c803100601039813407441c81d410600b030464044924140c6500c0d900c140c0f42002c0c07038001c00b03640c02070f807010800104e21781c00003d04c08030500132040c0009801000344c2984a600c2d40c13160030511140400950a045108800012907402c1c015244040c00300000761410189500d80441c50105050066041c1460401d2032030106410310140c409407039054400103481d80720a42d00707468516000e20038903074881c020300030030081844501c0640101c60143d00c0500c1613070f4032040360b5070b00d8200888079190055444d100310080c4910a64080c00c441d0134034010359000d01c41545072181c000c048d148020502070b84503003080c600c909004e03400c040070f9950100056410840300d8002901c5940620480d084d84450780c02c185d01d2100c440d84018010010004210740d207a008840150103900702a03280c259669800c8100d00702c682c0c1c001c080340e01c40d650040c040c00f600e68803120b00342e0301c07821242e085480c0303070440443c0c2c140065103600c00c43c1c1c003030594110306003d91003103030440d54207582d099000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 490309019 1250 490307769 490307771
    0x4020315130201050a2f0f06190221040c05090105060304050703060b01050d14040c0b03040c0b0d090f260c030414060c060a0b0906120307060b240408070801 69
    0x200040444001c01c0031000c9542441c1103959030300030500444d04003501082c5051404952010302940800c44200072980d2440c500c10b885d000320481c0c0380c040e03d59908849114409080c4160740f0300c040595401801c0c80c003490041140340603c01c803105050514206c90447e8500980c0740203004920b8081500703401030808070b81712491441c1995a10b5100c4002c1d11000380000c0c0c1310f1510502c0c580c000d5043d25204072256008108141c0040130915000e0410740b0150703807090100a010030b42c20100700c1101e1040b6000035805000c545441e452070402d43c071980c00703d62655591030200002030f14080b1301544050082040007401d409080c0000c1441c43c4148a1340f00c43c0400b0410126083e03c04015642200d4646080c40d8403055480301060591003007401c04a01402018100700e44403205501140c4000d40641c0c036014180c5da4041800064a600707040d84499078010711285000400e2a000400e43c0103000c4e004c1d00b44412102042d03110f5841800a07100104008101800300440c04c0002c0302c01040b072140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 490310269 1250 490309019 490309021
    0x130609050307151a3a0327060c03080402130e0a03080f07020a0f050f030406050a0306080c010507060b0a0e090109061812050f120109021b07050604060e030106030c080604020315 78
    0xc0000d04065205e80b181029019004005060808513440b40400740d81a24020351414954034009100300600940c0003451401c03405205078408111080303005030f564a8075601c207480341c82d80b019510008001c1c003c0360311640c002c60300b5805d01c070503000350f03040e06000b000180303d10f60707403864082d101d0b0030020070f0f4254180d807078000c001490383d0000c6c00d0380c030507500a0501c500343c003118105942894040e07911041248400100014102d500400070801c1050540d41006155155240c01c0d0725980c1072040d26000035401c3c0085000710b20343da8000b5071a99030042c08003412540d00d0700c1000203c5000c951014042c0d545a96140520030540905560040c0f00301c2d594a034211250780b414002d030180c41108080140c08034a5440e00000c1d40200c54a5001d54a0034442e03d69495032030714042d40c01900d01101c07010850394029050391001401500380da900802d454101030030402c08407104a460349515901d90349031040000801c6075015044054040b1001915103031425005051404500c598840b84c4102020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 490311519 1250 490310269 490310321
    0x5130b091b0d020c100e06010e15060307031d0d0f0e01090f031e08030f01141806060901020a021e090c040f050607020d12020a03032313060905030715 66
    0x4040302d42000a622005860f0304503140410724000e20902c540e4101c5282950b4a12039406c0022600d04903205d24413000d0b81666170345c0b4400700340d600b00d03542c542e0000400d1001c40c410742d0080e08a140340322950840d8485101806040c1840c007580c0c0044c034004141a40c80710a2400c0d070004149502c50020700307140302d01c5841c00c000e0f06070210b040d11028100d034001d01000064044007204a03100950000849901d81c1419007181c41e940f0740a05c10700050121860340e0113410304141d40c500081c0140303a2051a040d07600c1000703101066000c3c1a06504601401d4400070040e9550350300102e81502c00b145000540c0c00d18018418015005007617151041380500003049585101908401500c90948041c1e03101d100318070110307000c02e581c00001040c150322041c0c1045441e6000420320480c90017540d0501c401030a2401c0e4840003503240c1042ca0402c48060005603861102c210030103a851301c81e610018805500c1d807202d13070854101c400d0803113809815080e11044540540154142046c8044804840d56154 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 490312769 1250 490311519 490311571
    0x140103020c07141c0507060e09090c011d06041410020106050d120306050603010605090405150a0605070f0803390307180b0c0a06050a0c0206010302120705130b09 71
    0x340b041800c461868a0302100d15144c9103451840d0810b040b4a0044a280724075055407202c00c0c0e4003c89000840440303a1007070074580307042064043e00c0c3c200094907464806100448007420f504500b800100c5850f955207440340c0b109001480202520842442d030048644200426401e9518048045a0628805100568500600900c00c590025101940c02020541540940001c1d4072541d070105011000140303068201c0c0040903003120882c2e04018550b42d1b122241003d944001c03065070004032202e02804aa4001d600900e000ba00405148080c1696660f400003241d108540000703036011500d40c40101181611259840524000e00d140380c07069409802c1e041c1400020034607420011404003080e061010392480c3c0c805440040101c0e070362860994003c655658810608844081c6040c00081c611719051142c04040031b05540a003041e6441c41c0c003084280d04001032403800728055440000394170faa40311400c074101c2030410b00110700d0b003191780b0400c21500f40051141000241903810001d481c909 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 490314019 1250 490312769 490312783
    0x50705061806010b13181a0a08030406032304050a1505070206070302070f0501050f180c030c0d03050c010509100f020c06190605041d07050a031113110a09140103020c 73
    0x6070b02c4082d40c42d0112002c2204400801d03a1000d480c2010200014481803080e800c280c41f04030b01c000054203c0c101900034840109200d1180d10500d40042c403044c04868030981041c079a200030340c15040c3e07100c0050b4250315200350b420b4404443c035070702c40c1d0100070400c034128068014580945104205900d0040c5002e5100c2d58000c20384010145d00090a03805c002c0890051448c0d1034110000308024901460003061020060b42d031090300025516080c4078118001503070301c5000c60003034080c2c502d401e19502480b00c0b195a81000f00c0a02c0002d000382c4034160000d21400d44698040c0008000f5071224110100c12603844c0000c01c41514010007044621800c001344d41900000d0041d44031040c162011441001007119402850340a414454540c1e60120407034a01c18000c02c07a0004d4440c455514010400202e26600c0020b210504c40020001035107040441743d103910703515078070219030090050b002100a40c802801e0305c020a085540030f004021151407104010002828114a441d824104d000e641d219 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 490315269 1250 490314019 490314029
    0xe0114040e04080c010e0f1603030e09060a0b070605011a040602061501031e020304021801030309090b0d06091505071412041b1805070c1106130302030d05070506180601 74
    0x1c1148089000c1040300c5044601090140c0c0c001c02148000c2c1801580b0303402e0030b802c504028810211640440c0d4001075086d0126645a1910b00d0041c141500f880801c078401001241d00c0807032a00c0003d03082050354010900a07108082c0012158103150302c1d01640b071030342c02c10149040410300040c00020340006040d50400b942c0190801c9441031480101d000d000048000c00c40c010b203407001401c0c43c0010360040d50080c1e1080359050f9400c68020041000c0d0f080903c400b400250308000100410b8082e90b11018511402034540c650204554440c5011b4030442c0b50f0031522415261202c3c15044102d01c15580c00004500d40554044806100e40c0c0310381c081d401e18058000901e03404503082120340b11340a031a0940003000c05130b14035960307801841da00c601c1010340364045051200283d0541e105500c001e0810b0340c8940128003105401c400c0c0490f0350404040343c0e0703509044100110259508010700c40c1c050609aa505d9610040c82c90300b281401d001614001d41003103002c0300c4090b151004100c1c1e50540f2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 490316519 1250 490315269 490315289
    0x1d1c02060c250f06020406020c0f1009060f0e0a0e060f2e050702150301050a0e22241a030a3f020604110603070c060b210109030e011404 60
    0x3540a0510a00d01029404000c0c4120b00c00500047c4094000c922125092012101a421181440144450040030a07440300004016240a101841c05410960b2548443d03150080d030034403d1801041080c0c001e42c0062105d0742d4204100b00852a1035010808900000e4034412540380034a40c203c41710122400038510300040e0742644480c00c1e40300302c0a44131400d400408030158004144141c0031141c8c800c4c01018028074007a00041000c100c00d0801500500d0b801c2c0509400540c07050464041a0070240212890004210307001d445d2010b09035102412140fa1100050b0303a00c00c8042490b03101e400d030f1005402a004101400d01103404bd9a802002480010150214400440d8006682840001081d041141d5410700c0400a64000303201407095103c1c00d0390400d1050f004040101c20b01040ba031100c00070b2038100d00e060001301070340c010040c1900013602140f4061a00304544a130386102c98605001607644012003401e155100800b002d0582c42802d02d801100034660880b03880e4401c0b401401e68030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 490317769 1250 490316519 490316587
    0x14030a030f0e03070b120624071401020d0c0306090c0806090a1107141006140d050f10090b010905040c2c07050310061404091d1c02060c 60
    0x502d018441c030200624004055440054442d4218a92908810150806504020002915402c00520b8a642014241d254401e0340040c0240c0b412658000e85040354120f4034210b408005840900181014102c0d9410100d504022058000d0880d05c85078400c20a0505001c40414065086440d15400030000d45040c031499848603c80f501a0010045061700c2d224000364480510281d0315000c50304000120540301d103403840f41420801d841060240031001e2403803a42d981d96a2030541201c1c1c3e01144950151007101c2c554075040741c10050544030100020703407142c000000f00041c1d100c40b28054401554208803030b040549130041008403030b000701882c40b41505a404000151b0440084c440354a42c40300c0f514910b0301000c001c02e6500706075141d0128200300754010035218000c0a80e20605440c0c0b007446810180303080e210802606200d54a200440516814550144014001d0000b9244409801400c0201041009161001c01072091000201c244001c204200d6000303007898244018a0104240c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 490319019 1250 490317769 490317797
    0xc1518030307080a02030a17101202010e040c0906120c05161b03030e04050a0e030f0a030e0a120f0f0207120230010b0111030301030b0405030706061404050114030a03 73
    0x18501c1500c0c0c2c060310000d00414a900c81e664000002e0654003565512500441c64070140c0300321148080d44c0c0251a108a0001440b00b010041c0014100314014500107604a003000701240032560443ca420000601e042d0081c410541c006a019504444400e000c001505400340d000b0800e015110500e0034080003140f480c2c0a12402000100502036006001040e00c6d60f02e04c2c01030a00e91a4004160095007040001440c4104500c9207500c4429000055840c100f070146c900e215a074088803181e820302d9569035040058070401c1012595a40c03042400182100f10040302812252130100541c04008000100c080440d0780881c0c104100c035090390300c14101034802e1002480c5c5040303030b810001c02103c00c15000138002942a081b04803076001000200b1580000034011600c00c00c0380c020003011940300300010000100c40c035000c00c0d4407500940560742001810b0741c40d401521a1075012051900081002c1c000c01d1415124181c01041041d03800303c0001601004a501d51081d214042c09000c44403000041b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 490320269 1250 490319019 490319023
    0xd0c05030105030705090709080f0c040b040207050a0605060409080f070303060e090d230a180b070309030f0f05120903060c03010302030d082206051f08150a0f0912020c151803 77
    0x1000d02040c002b6103002c07907041c0308020b40e2007620741881403186003001d40740f002e40d0030148200c1d84095041740242007422103580b85c9001134003025140903000342d65216080d000c15410340103040d485c124058034640d02c29072410001c064540c0c580200034001c50160500c6075500c800580e10006500500b040c085101c02c4801280100d611807902039059840060803071503170799100c40d04498001900c1f09840600b6200c400207452070142d8000240422a64070080c0085a1601400718503948580030524043d4107a80c0d80508004960715103128540011480b07850034030301031180e1580582a20032850841d855031300000d0352020307102401820b106102c00429000600c2c148224180c090003003c000060f500c40c9807004c0100000c984c080c80039850328084243e0550b1615030303142240e5000e0018950007001d000140c00341d40c0054548000155607a01c2180b681450740500d0b440c0a0140400d0744205204903c082d04010720319400328414034240c641001d40f181410300340c61040990328280b400f03100ea40c1010074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 490321519 1250 490320269 490320287
    0x5030a0f0204030606080c030d0806012c060708032a090d0303060e1801060b090f06030a020d05040c06080601020d120902060f0c0705100903120e130f020d0c050301050307050907 78
    0x160125040002c081051040002c240611110a4080315440b07540800222b810400c00d8446a001807986147e00046480d00740e01408010902c040c00d20380c10381c05c840081d1407940040c20444120340080100070040d42a150340e034015501e400484111102d146d106070b01c192041e065454800c04030f580c02041070500c65404078000d04815024100282000031203030049034031304180b0448941c00d2110124114030018103503550044c000d0002161180070740308001950300028800040c483d824404240701d01410b00826000314001c2008074600d90070444001c0509200500702c41c1550b0084000031102c0398404c980000000e6214400540001d9a02c0020560b11071584a82155100410070800d00c4401144040849178112858a01004c0070201a110071001d48401b40003490b07524080e14482d4080c0b035000311085002480d881076507003442d4034942125000000d100d00c2070703404180e040b0120110301c107091011000d400c1407411981b41c600000e940e001c280c0203041c080c544840c08100034034001c811035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 490322769 1250 490321519 490321523
    0x903031b0501050c0903010b15030f07050c0109030507060b18010306020a02070302040e030a0f020a050a03031820040c030207050325050f0a030801050916030b0a2c0a020a05030a0f020403 82
    0x240001e013010b03882d0110681107912640c1c0700e5480d2414206442c902005094031402e22134a01c20304554440d091103646031402041107060010402045403002c20a104448155200f82c650b2521458941402e40441c2e06444e5500e011340603d130081606404015100d5046a034403020150b51500322460403420b100309640005d4016091801d07001c00c0100110250400808a0743e03017560034008008120398800c091240504643c00584a01010a109810100c02c102003c07000380011900d69441c0c16108000700e0b110a420348140001003072a02c0e01c1d000d402d0701c50b4410320701541058a55100c01d0340300d00c140803ca50301c1d81c0248400d4600d0003110600c0109441d005001d42d01c840380074000c59903c50300840c0d41100001c901c01c0012a07a4503140c2ca9541c002d818a070107039080d8001c14070058000b445c442c401c00b940071140510010705100c000d00d8007209941761541018229800c000b001d082c0c104040c00c116031883c01840181000f03071380902a0ba90001440b00302040c0c00c01041c4a981c028820b503000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 490324019 1250 490322769 490322771
    0x2102040f022a010e0a0803220803040f060e0615090907030803091c031509050907270b101e0e040603140d110c1005121f0b0a0903031b0501 61
    0x2d8291072490141c41080d194111000a20800a00b91901c9440d8040182e0061003d681030000c650071501030349030185016039841e4001c0d10a25180c90340240740d041200c08980031850190150100300c81405185da04241d5000205030b40c1c10135100642c080e2010051a07402000d0a1000480c4520100300c80002140c2041c01643e880c1410000e40382c407440e42001c0c100840c8100c10014540344c1c40b03441000110072110a041d101e1a0500300b00318080c280c0541203039064400d207400070504442c100e15801e6110000c02400548a40d019a0102078513400d840780c51290f80c03030760f01100c611504a07034100200018005403105080d6520340940304601140121340e0442d1030408040b04100c810410100030b810807604441d904403440d2030468412100c22500358013500304074001e03107803401c2c007880400040b4000d00f00181000c00e9a41c5650300301e441141e107080d82d4031000c135030140c20650400915000e45103213070500b4645507030031130060f02a40040c03100600700700d1001c04104440700c140302107018455100780 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 490325269 1250 490324019 490324057
    0xa02070c1701240e06090a09022115060a0e180f010504020f12070e0a0207061b090602031206150904140406060f0302090606210f0f012102040f02 64
    0x1c0914000c0070785090780340b11902d071071590008800e00070640500715054030800100381d5403004117001e0514030251416081c99100c008010050303581411a408540b50102c50700e29030240c01d200035140914103090800020041c009004458454506a80980746503021000540c1c844500c0c0e482e5001c0714084040306401405440caa80400641101d0300590086460001124020f0100a02e100c40e0b681d6050007607000e10b10421a40c0000d040c101c1d802034141c00014245032554607218181d5290040d500c0350546080741500416411660340d001a10540c4000c505040185204041c1588040c00c00e0384100269103402c0030450103001100c10040028205019200072141c3c02d4100300380c15507003291614281100882d09a5500703030001d04890f0000c0c4044500c0c1c031000140004c80e4000407103555010044c801d0724511410888990340110100107c0d10140c3c60408103600d080b03e4103801c82621094500c2842c0f42a1002d0707000055490340403030380081e81d03101108103a4028468060f07041100e2012030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 490326519 1250 490325269 490325309
    0x3180f02011403090f0606010504080a0b1b040b0d1b0c170d020a180b0f070f0218070c030e090709030312140705040303030608010b100813060f0507110c06030a02070c 73
    0x400c0b221703000c26441c0b040f0380f03254540c1310040d80d81d4000e600440380594840790300d04020600032085150041e1b540d04000c4040003803405100e40507482500070311054440055401c8031404075100b681c0456011071000c21034080d2584000300341300340000000e0b291a140700c0c00d0007088000c1c070040301c00306507911a0855540145c100050280107040710400d21442a00000284d500c50392021252440a2040039500c2d1002076a283d03004415800c4040e42c1000c03400d510314001140c1c070401c8034003643c03070342d04c80401e240e04610b40203058001b18426207001c1c01c1003c05002503950480342c0c060a0fa0f50506010f030605000009110040c0440190402012068418410001d03003140040003035a0103a601808072985851141d42a18442c481258004030410000c024107881107182c90340142403900c241c440f854240c1c03101d009890440108054a560b503005100d030458209181418407040d000152402200344000105e0b1400001c6c410001075400017408001c1042200d0041c003d000250001c0394149000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 490327769 1250 490326519 490326523
    0x81e0711010809060103210309020301020c010204030507060c020607030e03013b0601030b0129040f062a08030717040b060111030309030f1303060f1a0103180f0201140309 75
    0x81903006011a0020010070001a404604141a203400c100a2080707046130074800c5a21480c080009001c051784ca403050001a42e085c002006640e4211001503150307801e46c00d201c2e0070600303241e018006002e00c0156140060301c0d1482980c1e03c0300d406042070290300312400301007030160101400ea0925000d00103002403101204c10344440500880c0325811500c499480c0046940389000e010150010040c0b20041000d0028015925202c1c0c81c035603110410004200700b5101030b03403c0340c1c011b031460081014081c0000ca40c00b04001007072141d00f0a021002e25010340c051145c81000782c801402c0c3d55000000250720601418400e511a1000241c9078268030302414828000041900c510f80055846030074a0500707000001941d004000c640013840c500010070703204c42681e0740804000c240e02016001c000000ca44075100d002e0514900001c00f08440f440f280f02014078504c40390311941490f00d070010151500e44404418901e0303c3d845100107e50140c94001070310707215507081c03401c1c580503c00420030102484c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 490329019 1250 490327769 490327793
    0xa0c1401171e22021905090103030203180f060d1508030c010f0c0302340c060302030a06090627090b01030302030d0b0406030218040309170a110409030c081e07 70
    0xc002e0076041030b45410410703807401c202003503562031101d540c0340652015242062043c0c3c0c40541c006a2a004a941e60000c920030349400d07070080d0050307000400c0d1442c203404107050a200701202264032100b079890784000102140141080004103550354402101c902140040300310180c2555421a5181c0340c3c1551814041d0410510321002542041b00002145000b4001d03225a05d000d0409000c0030798594000641300e052031030720b21300b500082c0351a4001056401c0c2403000a82116580541d03a0b1404004040c26108258402c5107010b00e066010881030b8440c4881c1444d01e00c0c0f00800208a100c00d41051000c0c14502e41c025188c0517520740000701301034001000b881c150b44801e1040c421404032000300400c907540b501c000b80d0083c400c0d00180c402c40c20307171982d02ca9103e8441e040c48206542c07550f240d1154440d0603582d11040f9408003280c00280b0100040c140c0360f0501c1103e00b4400c2c40410781c0c0043c80c0000350326000f41802d0f000b20b15040c410003205205807a601048070b550b61a409903040c4018203d107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 490330269 1250 490329019 490329061
    0x18090c090b0103110705120304030509040c03050106020d02060415180c090c081509060607082a010e0f0a0303020a0c0510020318030a361211030a0c140117 68
    0x440c181040381135807030400c01c1e40c01144c0c01001504c0004240d65003a021680b0044c0103c082000c10081915250b403284501e42a001c2e0350303540003440f90304113080a8039006400c4021019540450101b1000680c030a80c11220150b14980205070490b280d5081e01000c1035001d8000c0600030341c04008507041040da400b0801641041da1850040d40311008841c107001d1101610395003241d6088006045814070b00000c002540c0300700d820300c2c0f410400c1e905032202046099144e01c1004110409a84100024081c0300d81102c0d040014001760030545d00c44035562880b080000b41815008103003107071201d00549010b0b4585400c03000fa166003c1d009030240c0000d40c02200d85030b4440d0450000b041c80203c0000c00d030b0308078010701e40300c800380c1403038034406201c3c03020150300703181d0380c0022094905902039100c00e002d200505401605100d110600d1501c6144455281300e06802540140d8001001c1180580e440c0304803811154030384006800800120b0f00e550b080405c010b00a41520144101404042c940d80c030402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 490331519 1250 490330269 490330271
    0x121b09090f100f120605060111160603110c0604020f010201020f0a11010c05091c080c03070506090c180426070f02090c0922090506040b0f0c070206030118090c090b0103 74
    0x652140082815500180144844006130300240000200035600050304140e0504004402c0604600c65518026500302c2d040140c412100041040c00d406025031441c103040802280e0030315585116466a90f18001c10180c800c2c45007043c0000240d0003981254007030288000001c0c3d0380c03118500003400081030710400e10702c150b1030001d0f050441403044041c2ea001c500000e240500010b500c0d090385004030070f400302c1a542c14104200084210b201000100941e81c8102c002d40194541600070506000f581c41099018001e28500307070020014401c1e103194890b5105c40620210b0104036040b240180c2c00c844600000180011680d051100902210206070310031203582143d50b07034204000000e405049211034201c90ba0415a0404101c80e60301c81418604506002545107481d4079594a012015a0181c94800c0200180840801c1c1d90192903804680344484901d4088140d020480e41c2c4414494141103228502080c42d40340d000f07400030b01e181e0b50070040c2425459105d05130a0010009152481c3c04a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 490332769 1250 490331519 490331551
    0xd0602250c17070f0e1021030e0d050307020108130501090c03020424050d030c02060d051032030109050f01240302130903090e0a0501090b06121b09090f 67
    0x840b500041c85002d5490f1203002d4003030146404010f2440c10b0016205443d145040ca001080810044901251400d6101071000c010446424003408250f6402c244500034140a14070b4000302d00000100c40c4036507820700e0301c001d095464424000d40c15408200040095003011001d41c28843c143d030782c00e010307603000721010030a414a0580c1074800c08080a641c10031600760074020001072030449040c04189019050020550000c0e50024095900c10303031000384e0041c1c0d10f405200301150940010006090055610070511140002070406120360140003142840c044141390629117081d0006500c0c3d680c044102c1d81d00300114a204e40c082c00842c2c20060304204403007194841450014090f0341140d40203420a100c651010303070003030042c1c00a51030035020310a4881d00000c1e610300201205210325102000002c095040034142d03800e45070007519075031140c201840114181c035184007100c0d0300006002c2000c9042d00200c0c3d08030105000e400341d01c9078414160000c0149000502d46a2840303420448500429 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 490334019 1250 490332769 490332809
    0x1203050a0b06030402010801030b07050f040e091e03070809180406050402030607180e070302160c08120a0512090705030a05010f051e0f0c13090c020c01030501050d0602250c 76
    0x2c68041100c019000403254401080451009000990020040c0c07603d185840490a082c14059000768015680d05111400700644090300740311600d01c032105120745603c0c10121024582e900d015014015100301c900060591150365032280f44084122a6480031006180071300b41b8100910301150103034060302070760000a40003482016070400010646514480681c2040e401d00c5020a00800c84410f1503420031880050102c0100880c1d0034901c110100740c1c1090401130924184868040356083c039074014007043d08425006010f445041c0110000c81c0083e41e03407103541c0c5140c080c1680c481c0b81c06002d80600c1c50705001c019040030000074600d400511243d19210902c100c00780c1c0800124241c41d807004003041c0c4d0f1842801d2895082988021100d003413815001403285000d03110792014510340d50324009141c4654061007002080e03402400e0400c6151324043c003091420381840001050954005183d500a880002040901c03d140c107072038699240c1c5900d480600e09085004500c0024100390708640 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 490335269 1250 490334019 490334029
    0x2010e04060501140f04240306060e010c1506180218030724090b0d1e0e031b03040b1602031203040507090902030a021906271505071203050a0b 63
    0x7007151010380d80c50544000c02c1c15941185c1c0c01200b95000840707420070000907030405642030403580712110100e801c0360b070b5295100a000c4910035400f0b0310510030100300d03944681c0e03002409642d5017030300f0618050f0050303011030204005081c1138114640326508203200c079103001c14a9020307004509003003614010040b00300c000c02d550340041d403181c1200c96822001c1c00d203814850941d2103020f41014100070001d16214051065650001030480d003502e13035a070310304200008500b2180d00d400e82d0044002c02102c1c41840e40b058681c0300d401d280300721280c01d505580c90103060800c1203800801803165204e8444181d071703030292a1803c40c110160300c03d208401c0c5185086809070102d82c06264800c1c0201a2503203090b500d000a131101040980c0d26008032038154015840e0303034521030305031010100c44040c100d04045001c2c26901c00c0e09050700d092204c14803036211020a10344140c00761040400204a80c0d80c2052040b00c2034801c02c540100740c00d65440ba0040752a406401540c0215182003083c880000700c882402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 490336519 1250 490335269 490335281
    0x60d1a161701031211120a050702011b0f0212030417070e0601140702040902060c100e1b010206150a17030c06010617070e010318030c0b06010305040c090506061204030c02010e04 78
    0x150400e0010314413010a1801a205460005401d405941d050a52003200303440316041103514102045001445004540c0d00011040030885000032150f400581620f9803034131050151402409040142c06440d02d501040054800a2110700e1064148079500321085450b044c00348280e40200f11101c01083c811340c0075191440d0720b56182c251842c1015190b408000150400d4603003aa04000308000008101500f8040d8010740061f000c0007043d000345503a181c915001907120381011210a400304000d1582c0d02007201c030b0b004042070303074041da125610000282e14844581c4c41640ea90424584039110560044054031803c6d1005d025035070b06aa86000644220080c2050304100d001041c00003541036000f03a801001d8100c042c500040c944510f4140500c0313110100c2c0e819000b040c42010003034100801a041035510920a19050146003481e0307880c00c08021460207101c000c15261400184591104025103680003076064800c0714600b05400c001e019403005031400e03800108448110749003810036028031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 490337769 1250 490336519 490336523
    0x30c060e030f031603110414090603010e0a1b0806100f06090f051002120c031b03070507060f0509030106180b0d02060f0a18031109130b060d1a16170103 67
    0xc0303107581c2c2c0f60944c80740d2030b903402400301c01496620344040200c2c440c010040e20103072400b84601048042014104582d444009099a2083c0e05096001c007160b100801d61070f200c55801000030000c4544508003c45c0400c00b50000c001c2403040c0b004100004102000900482e1488072000c10a5903c6880448002406008815602c0d014071404c12007401c0c10198031b05008a54410380b03a480c481141120801c6d404641c00f503401d0790011860195450030701507032200c03240d1442d0003186422030a13510aa12000d90344154024840d120440504c41c0c2d0080f41141c8594034022300030840c2544414009442240351742e201c038030305450001d2074007103800c0181e00c82c80c0070341d0000e00850800685044201403544100401010002203800f247c10101c5810000406148148801c42c0e4007051072081c0183c1d010024400c540c0c240c0d910800e200031a100c1c0820940280c1c00303035400303070170102c8904044184400c440d129215800c0d558081041142000501f100182c403107a46207a45010301800481d001e000078000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 490339019 1250 490337769 490337797
    0x61014030a020904060e070803091921030c140a1109240402041e1a04120809010309120305011a0a080112140d03090c1d1f080109030c060e03 62
    0xc00340c0b610f484000d9200788100c0c80400c440100e5500d640c101807155005000036400855621200d10b88545e010003000c19262100c0c84d542d2070802000c2c0c00b6150004072480b0741c0000303840e0800781440340301031494241e044044070740300310100100300e5540c00750030905035035824450350300715007034544403940d98040d40c207020074336125a00740d040500b401981000120351280c1d00f004000b4a082c0354003580c0e451500c030040400d010510f1310f208859899010103007030884030000c0001b0311800d00500c426410940d007244045441c1d100c590010b8005001418000d070806080c00314000205a0641000341691840c0280700c00003480c0d2810000103000d0200f0320030100e18084014000304450540c0c0702c0d00140214078041603d9000550380d41001e41d04940e00d40001c2d101c1c12201c0c14008107a0792600104030051104e00d007a944030b041061000d102810b0355048a28000f031500c05498454040c038003801400c3c0081090641914001d050210301c0301c81100c26a041c000b0310344003844040181c89040100d92a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 490340269 1250 490339019 490339033
    0x4032d060522030302030118022d040302040609020903010606031a040e2104080601051e19080118020312030403300203280e03090d02120f06101403 65
    0x6104405400c004091954048240e9400c0c041c0d09442c18000c0d003a00d000f42c60040c2e4950500102c2919580341140d40307525580100100c0d04081709650707118580d05074403142611449180300034086070780700e213600103940f103801c2071004114920301e51f004106844048008000c429034030442a02500e4450200b1102e030000250b0040780e90600c1c3d081804401c00302c1d800c0e1040c142080c50789104114406100d509048008a024000c0300c00801510340540001c81d5000f1075403000806280da091f10003001e42c1d00800c091400301c0c25103200c00752004098a0200b00a20111900b6100d4070056810040305a21174450350481002014189007207034091a016611040c03110004007010320358206d000c495040e0b400b24040320ad405012984059402600300c680181c5003806045490b4103c900100750700c4884525200a17141c01c024000111200e000d02035070080212210b500000740142615601d0410354010705118070078048020442c984034111107901c0011164554035900b00e2004c581d2841501039110107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 490341519 1250 490340269 490340273
    0x809040c050409020a031b090b0d0b1c050c01092c130c5406080105010803030612030307092105240a0212040f0204021e04032d 56
    0x508103100c904240e050403032501c3e40d2015010101d900c8080d001e00042d9580e440845900210b40a1000c0b408507450031125003030900410a40602ca0505407588e801d40d1104203030403a40710040041440240c48074080020710890400c0c0e0b444051400090780026408080804e2642110b0755040c980380100f400d90111141e1214240f5013441c0180c40d01c04002d440151890004000081c904003410803410000154075000380402221011490100381392000e00c8100c464894400419000181d01c505001c95240039001003000144580d411405d1075508120010030702000002c02035000d91400c0d00c02c50100c0d0411007140c0d84a010a556420015200380303c01c100c00c0081c1c030900722161240710414801c0146c1a940d403443c100419528440e90008a020705500384041241d1036401031710344101b546054041c6d00c200c2c0561000500042285a102c0e010009544895050f200804543c421460000e5107090702c0440d02d0b00715200440d0804500b5441801d0642d01d040d2254001121904130b2602d22615 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 490342769 1250 490341519 490341521
    0xf0b03070e120a060b06070201021903090801060602030c0d020106031a0a0b1e0906101704050a08040b0301150507080f070510021b0709060602061303030605060d06080c0409080904 79
    0x9031102041110000003500306640d1500e581c2a4400d500b0024024090140780203801d840554a2143c411a010300001c070160342c001c00c2c807116040c01010101da40401c240380c00d1311038145035004041d09610340080401c18640000080180c140000300f2650b0385020514106e080e110070340401014a542d5451065205454102c039a03004084c00d040803d00e034211001048e502040f00c00d651081c1c3c032500c035010500d810456030343c540001e415201d500c0c10043e020707000703840b014041d801c50f28100c00160021f41840001c1c05510011684802c3c030f40c2d070b525a5104040c80681083c0030386252140103111100703000303004408603840b03c0d03403111900b828640400d41005075504401d809441c1c50040c402d04055140d50303440142505124044a005554442c080b4a86400656000b000b4414603101c002d2044580015005600140d80c0c1c4040b1154202490124050035081d0301c6250010004101c0a4100780103070002c2041d500250f00f00c03030b840001942044203a034034140025040000802c1995954101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 490344019 1250 490342769 490342771
    0x608010f1a03100801110406080609160f05130305011d070f0b0d2315030c0a03021203121303120c090611010e03070b0103061d1216022e02070f0b03 65
    0x240b5035a0f0301e1265890103d42d0a540e004500b031a000c020000b000d1042a8005400c1504400c0c1034403c0203041c40d24030880700c862950012008103001c4a0542c3c6e10880d440782c1c00f2142040c40781010510304030359a00c0c3c124042c0c10201c00d2510f440b500c95030506060440040d40c102103681c10360780303800210715101342099181d1000c0030030740055032900130942409480c0850543c02191607461180e003840d1102c0010810b00c1801080391090300300d4000b410301656210844d0382529012229011001c00c00000640fa6101d100720503400450b118080110703844001d1000c510a81c0240c68030310780c00000c0030940d000c94894a4418003c00c02200d000d100e04c5108401406420484000005940c07510205e2945940c01050003155503881c40b100600c2002003502894003206514803e0071003d042101d549a150303160f084940da540c18000c1141c022514031715144c0038500d40c010785043c1201e0010070500c014400301411250031645c00c004d00200c040e10000b841c0b401c8820342c40343c6141e51400c00c0711071605648 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 490345269 1250 490344019 490344031
    0x5040c0e06180405090102041815080703080703020114071d03161410080606030106030207020303091c05060601080c09090910180303050c0711040504030c1203060608010f1a03 77
    0x40d642035610100c0d1603000050034400100b20141e6141c0d079041e03003000b0540703034004c01030020350b4011b002c20003c06044012911a445040e140840d55414800b4184403071103155001890a11420900205200101d0010310b9628026802440b103840340001c9045240402e8a482c00000c403d480d200303508004114081c00001002002c2c0c88013500d18600c079000f070440e160081c0d0520341911200311a503280100c2c0050015038075090480007858508000b07052030105216034018150001207010071964203004032410700d20000c00f040b1b218004070104410780c043e150002c0340d0920400c00411000c1d80246181840742c40b0540c3c49034540040881803060081018140114a110305d140e608803541c000d01480c248048950600407000300c441c00c0007400d0f1361000d8039444118100300444008100c10401e0155102010394020405403150f14044905481c1014040d14050003106038030501ca600d034100f202107070490303924a00541d8031140d01210400140c42001c2d440006004540e8910040381d019541c040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 490346519 1250 490345269 490345277
    0x312160e100807030e0304060f180f05100207030503040308120603060f0a0b011101060e041205030702030d020703021903090f1703070204091b120b0708060a1a0d0f06090c050c0705040c 81
    0x140070017003014a541c00903001031000c20004025048459400b00c01e0790103000c0e4495001904501d04a42501c25480340d000e4107000c1c040a9450102c01d9008211180003154440101d954407982da08103890035400820458000d40348207c08a2407a2034001803481c00703130700c0703d81c906c880a403610500f40d00241060110f15040c40740c40c6200d00903581007071081d54020851011920402e141914000d0010b04c1c0350740026052000074414000c800e0360000c16145400054280107035070300388a0905a15140044403541d080040110b0b070503041507482440c5400301d070aa8008a40320b40d442da13032001507400704140c1401c0c180c2e20a000b00005480c0a0700480e41660080040011812401c500e0984165454004e490b000e1886e072440b2080040c10821690310a6070340c5400d400c1403c0450014007412400e1003800d032455502e91400d007600d102d03003080ba4070700300c1110410410503a5040c00f020260415121303008140340f811048880f00350140c41280c00305090036000c2e020303003401c04d800c0100074030183c0d10081c104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 490347769 1250 490346519 490346531
    0x6030614012c09010306060905090313060806010c2307151d0d020d05011407030501060f1110090f0b07050403021f1e020609071a18120312160e10080703 67
    0x10f40381e44180a02840c014040450b204d070801100ca82560006440805a60720402c1420b080360500f560b0130f400e861706850304c02c0380f6480740001260702d07840400029110304c1d086444000041201241200000403900a0b500007135a03a152070300003407421031404804140c86000301c1e0700540a07540010040b543c010303c503240032800ea0b00130594043c10002c046a007170795240c200d50440c40e00301d00712940c091818078060140d0360400b800280031910040d800800d103c5500c504e000c003040103020049201c210b0305410820b0007002d0404106200c00000f05555121061000c03600c00c5104804031010380390094282e50fa0010001c4210401d1108011110200281c840800c3c801c04e0554010702d5100605900402c154101104001e040c20803660050102102001100c400d02440005548041000c10010b6414400000214291501403030146031203000000d0a04080304d00380c00c030140106110b581c80c9002c010309460a40b03000c8140f00045ea40690002058a400c074418078000d648813143d45408254 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 490349019 1250 490347769 490347857
    0x10140901050d060e0705030403090504180b04030e1c03080a0b0904031202070204050406020712031e0902030c060c0706120506030a0605072d030c023c03130603061401 73
    0xc504041d07451701e002800020a0000341a400030003040940303011034041042d1a508008408243e0031940010900309912001070241401440103012501c00501616040100c00050102504211400f100401c0183c0c010881902c540d20805502c3e9202502d8220b95460b40e48055030752494817007070030305020b07001c000c40702c010303107440c0242400b8510503100541c03034903030300c0c9403422141d4005021441014038280500012010800030300c01452a1040c000481e4006800401d042c4245001c145070040000600308031214000140c03c03040fa02942d4032182404107420510065031002e40c0e9140d03143c0d02144450340451210740c02281c1002d000d00b05004000c403640340190020451261801c00e06440f440050f1041d50140601c03c00080544007a1128451041c14648020303081c0b0800d03c1103912808844103155103c0391103c85515505080f20740b20b00d100e1210381d6003000c2600540c0c000904052001030040c1c41c40341c020070700341d8050711400885107aa4100e002001c10b10103489072803820b00400d00c41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 490350269 1250 490349019 490349039
    0x203120d1b08060102060106050c0a0204060e100602070803041521091b061211040815090106050f090714041a040812091305040302031308010b10140901050d06 70
    0x148001a4050104007440d00c2140c04650440c1d541c0c0050500c0340e00d1041110701c1ea07011994505548980c1495601c4d0242c1120440c40d00002d050002d4201c1e04d4a0400700e040a40001058480c60041c03038007201c003a0b00c070001242c0310711f900c0c81071044660040c003040c00040f0800d0030036a1046000d14014813075a0700b20840e04501100018002c9000b555032030360030140801c080003890854609420b056035586030001c02460031050b001c103c643e265031410042605c45240080320001c1032003004442049214060395008101c040d034001040d58070341500007030f8074100004100720b201c500418221140e40d550109907000300d0900e0394201e800c4401c010100740b0146084802807101070f04600e26441c5c40c10405450f140204c2001050b010f10006d02905045a90b5100b42020f07054113440003145540b11071400764a58019005400b030310084000d8003007103200055118a0604204071911924204580025100c82000d40040b8240c014108082213155021300001c0c81441074186c0300241030f0340d952100c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 490351519 1250 490350269 490350277
    0x50d020904050c0c01140601120e03090a030308010e090c090402010c02041506020732121f020d2009010c052d1606020627060115021b030712020312 65
    0x103c202900443c5000c554182482121800700c4d00b0400100c40d0709241001038108580f403c0111042502c40107a0038404c036003070040d00c1040001400c0c1040c150340760716006e040c0c0707402401449101001040090242c43c800510300018a0003d444125151915001192100700008081e41c109407940c647c190b81c1d540c001140030040007264090071400d400e02d50a11980350064001c00380e00c00d034003456401e01580406024210f044112401c10f45594a41c10a40c1040e8080d2000001151a611744107403500780f42c0c00605c0b000610890030405a428840c0444890902c03002400d401b600920444c00b00703502030415424018054800c842e400070f040b1800309882c484e821100740a2b400c1403025030b07054100c01c000c55050110088014000d80b8107000b0029500d01d002000e0091289000c40000b030b0080d40e804801860b45500c03401e40d95650f854001c52a01586400c8407840184074825003094910305143c45081e40031001006440c02d20b15080e0030146500c4103078400daa240c01007940802d001c001c480010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 490352769 1250 490351519 490351531
    0x807020307083406050c0715020d170709170a05100f060e01121707020303070c0303080c040803030f1b040905150409080d0e160e010f12030f050d02090405 68
    0x41203011020242c440300c00e403107000d0443d50b016a86440203502c040074101401a01c00b1490301c03903218190304221529012071075100e805a01e407104c504562a076070118906041035410340700c05400c42f15070b401318072030054121226400a10f103a41c2c280803c1e803800d00c403074040e004010215400781c0c41c0d80d2103140c24800c4404000a5807139484c4c4c0d840c2424111401544010315040c2e80320b2210398506596640b066240c00002080c0c02c103442c0c3c140c07042c1074002068508040d0080c0842c0d8460a01c0d2418841c030a035540030603000b080b0a00001008180300320112400da42004c4080e600390f40b0380300090302c00850081c03c4000000c4600400529032a26070b00070b00001d0000c000c011070541802e9006140d522001d03803c050043e401d04201c000030500d01c0e002c0350315800380c031a400940c856400e00802c6c00c207000c212110550f41050007000840c0d80e07003030034242d050340c06a14002c62081d50f00c516400c0c4100701e500c0d00402090324642c0000d0b036140a84041d000c1700515201c05450031190000140843d1804c0b280 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 490354019 1250 490352769 490352773
    0x2a0321010f060f0c060203070c0b0103062c07091109090c210606090d170406030b040509160e04080904050c030a180c0b070f06050921030f060607080702030708 70
    0x100032281c9140c1420780201550b0521220301601c02000038010041d80307001030842d5030000042030480d0301c11610201c142d6007025400015503180c0c0380242c068504000d00c013140c5800080410310000c003081507a0b002100782130050610b00d00d8541510007510341c0350301001e007090003407105d20340c20340300c02e80910f100380c400e4000e0320b503070b4140c121284000d40d0640d0140c00419040004000c181d840e02011a00000360480d0b0082050b10946001d80c1a8100d00700914080d840c0801e00061907034050b040b0701da001004417403d00c0b09179291401140d4070707458210682080e00b98410100556031b5651701a981141c00780300c90502d03000c0d458020505444050321745d0481d6403400000c10021040b14425a00214020510704081d8405600d80d440054843c0c054120103240000d400c0c1c1c1048031110100000681c0b28200380300b1450000c800c0c0da1943d40c0400044e00c510030300000345400784010f40c100c2e07202c0e885c280b14000c840c0d19110709003c40741d00900d41c12103100c94200104030150b5400c2040400900400c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 490355269 1250 490354019 490354021
    0x10b10090501020f03090a0e0405190b0702011812030e0f150103020f04051005130b120a02150a05030c091219111912080702150a090b2a0321 62
    0x8002403400c24101342e20300058105129200095031841c01900c01c9581e00e481400003a1591304183d4100301400101a041460002c01d000c1040380c80c0d0001c83c8250b08540080050301c503100440c0d100c28884400041003111204541000c4038007960090001102050881e00303862a041030051500c5486452265400b04450040085150a2000c64402e0361700b03503018001802c100e00b0041c00f1000c540030721803040c54a12341d07000703070702c10140e0020340c0d02d503801000d10480070710498506480b07200c142e81c16402012082119181c49448004403611103445540c0eaa20355a82e41e10400815042043d046a00c0340d056949021010020411415950700c5041c11180790221442c0004042c1c20035100d0302c2c05000c10400d80b41000700c801c07000707004450100c0400c442c14006842c11105622070700f840258072000c2d100c40c549030a0300c488094014a01c2588a0b00f90791078980e41503103000c0c0100000c903064080e40606002c000b60383c0030784000603101d0302c00403681030220845000c44400d00e2905521104807240d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 490356519 1250 490355269 490355279
    0x2071e0c0b03010602212106150d0204050f010c0203100c0c120503090d021216020409120f022b3e0c040c0c03081302090a0b032104050111010b1009 65
    0xe1b04201d070700030030400c1c40c6081e4003c07103442c0340322005603001422004404006080c54039038a502501c40440401087e5440008080c1140203400c20301031940075100104204105501072198210550340040051202c449042801005072200d108110100120807074504005030784803051000010560f101d01c0d44903d0115509454001c0d1600e02c0f43c1158400c0040031030205c242400c0381e64219040044013880c3c0b0580c00400d0103003007500350007880b000c0d4a41c3e00804540c0e101d000c034406400243e0980b0201e904240a03090103086103c0c0b400c001c1c02c0c1c0c880e0030b0f40c1007500a500390460a811601180700d040020b09255010f40c202e03600312040841d06040d02e24040381c0c14004a24000c05c00c032420808500c4a4400400710b9980a00c01018000b00c00040703041e100c500090814880c0d4000c011190b90304c0d040718070102034407414a40c9070291140101030041154008401442c81442c480003d0a11b480c0c03400440d1550035841d103040e5103540c0c401c03420901e504c0380290324912900369256240100d06d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 490357769 1250 490356519 490356553
    0x70309020111160605090a21030815060901050a0e10090513020f0409020309071701021e0a0e01081e01030b040203060702070f05040b060f0711030c030102071e0c0b03010602 76
    0xa880d602d159000000702034078014052001e94203603000344c5042038a44040744081500c03610340d07801088200340c00c82c8043e9035003500001c418141500c42c4da100346031602e40201d18800303000c103164a1548080140300e00e061552241c8043c240400c1d941c54040d07442804c00f00072450544122fa6040f0000b8144d40082c005400c020444259002c01c20a007140b070a4a01d00200702d850059010380d00000e07400001042e2190780811500c0044c00c0f030311004008004006c2015030007503201035003420149608401d4041c00d00d00d11004c6e10301300c200d80c0d11005054100d582c01118010030042010442c0079020150316510301980c811180079500c100030154580c2024010185040384c000d12003c11903000d40824802c1d01118042101214415a8081401d07a28040003c0b40c5001d0400c1400207054049950001e01501c04200d0803000b030180c055580704031104052509074402c142c00688a8601014100603400314602c085500ba030117000501005038403404a001d50b58020b03481100103a1168440000c52104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 490359019 1250 490357769 490357787
    0x1110a170709050910090e0f03070609050a080d020c01110414010c1403071412030103050d140f0f03071d01090515090a0e09011b0e1909050115170c0328050703090201 73
    0x7c068000c240e030b80c6070b442c3c20b02d64074483c01c3c2000745100c3e00c814070300003004000c0002035031540e0b0215045031039648103002ca00003501f02200c8080c05e5805c0041d91445840b49000312005e58194403000601c00520600659003803100280c1140d00d088900030300b020401c003c0c009810094401d0001112403020031061a18000e082c4081c02d40c20303942003004100003407000a2a0710001c0b80b6041c08104844400c00a0400e400b034114910411200011500010304042c401184945841c3d00d0f820402c1d118168510b406e50b002c002400c6c086000c011081c0404d00d008a500c440c08140d54106624081c00e0301c001c100007403115485802040355038000c2c00714010081c001ca0384039a02d1901c0720800030a5031040241401c2507a04054050240d11224000c2d030300e400500e0300060440c200e0248680d5949003a00c01d40101d0120001c00060300000c2810805c0a0900d46280501802c0b000b4a0551b02e40100d04901c8406885126100088008481100700350f0340c0070705403141030141c0380062240110b00015104182c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 490360269 1250 490359019 490359041
    0x513171c022b02071a0412141c0f0e07061b110607080904050c030108012a110312040b0a0c110d0305180303130501110a17070905091009 60
    0x401401842074414807014901501890842008501c1441c07080882c0284191003000d800d6084da10000108100040c170b280303004610640024074500304409040f02c1c1d41780c2a1100341c2d030070801005600240140c1e040c1c240440034420780300144d222412111241220504925949141c02c004070400569070040d509040d010f941c2041c2d058070742c18660342c00014a007903082c0c00d442000c004c1143c5091010980c242e46500502500c04c018600b07011024494a4009104070640341d800d05818244500349611030807151100c0c109039443e242c007000400e0b43d0000d503195140340c841c8030a005032113500c00c4986040f800b450207602e0710f400c142002c9800e0383c151004020180c051040c0d2a05040284030001600802e44403540f9000940c0d4079042c12940c296442c50107060441c0c403021041c0800c1050b100e241c0500680700708000c1005680c080c00d21038560003044a03440c0492400400b1501410007500344c036500801341d1410351451621000059082c072429105980c0c640d064500a2114845900c190082c1007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 490361519 1250 490360269 490360271
    0xf050610170408250c15020d090e0a020f160c140906040905010b0d08030f010509250905040e030a020615061c09080a0513050d0201080a0513171c 64
    0x7000c0141d50448454094001000b211000603203200009601e0451149001100b000300c842075241e04052042e420903000300b42504401c0800036920600002e40b26aa020094945180d0386140070308010389140000c1501400035000c1080490082d400c4004002208211001c038981a4440c1040d880492603908610304803401118445415a1580c2900358004000c44003c1014045c0f4070345a409410800794580d0402141c031407040030403051b40081c43c4103150f42101d864841ea80d680401216883c141c0b07503500a4001c83d480502110700050700000103e40909150340d0702c5036100c01040c129000302800980c160000f2130600b00300f03a814400d50350052509050703025640600f02c0040d095104030f86507400848151000e4400b03602c2141c210720422078010b00c040303445030b00d14040986140e2010010391180c0086110100d26480d2401044d10581d0301030751000401d070344180300300000305000760020303421382032003140c050009544c88203000d072182174090b1060311184200c0c54002141c0b040c04160701d640e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 490362769 1250 490361519 490361537
    0x32303030f1906030209090d030f02070804030312020c1b0102060f0603100902010e0301141006110d0f0309050706030c1107050d060203040c0308131d07080103120207090f050610 78
    0xc03440007900320ba00821072444a800240031503803600000c0001d50700c000d41240c1c0079401c004254102048040f1800c841f038a00b071040c0c0c0c00c0c2003105401c034401d00000030b004900500040c0080f034400c0c10f603250011914140149050705113814145819011030418106458100111620b56414058507030031004101d51070340c450814034006500d5030261000006c0365582d8501d800290b80c4142c841c1915984060002c20401d854280c0003500302d10100d5803101c10f118050703400030701e44d84102a070507440101c2c48060700c482071001e0011500c06019441c9201015154000c610120b031040c85481c00074081a10001030804800034040d1409a40c0607018115411020041049854640708401c0c0e8507408040140d491ba01d034540040c1c004183d400184c00c405000c0307140c150500100c0307009001e40701c05c81103401101c0040c0d810301e50414022135140b4001000715004000041041c002208101010b0042d00c4015842c3e42e0303a40704a8001007590000707103031a0340074003d543c00c003041c0060340c40203545441c1c100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 490364019 1250 490362769 490362781
    0x121209020901140402070c080724140313060203090c12191203020c07090603020910140f12030c1c0203070b04120c120201020304060606090f0308030903090a03230303 73
    0x40c1c90511440c190b51109101e0700c0c0107580d60b513049a03003140d480342c101d080080d1280c40e41540c1d10400d01490202000309090021210802a10b42c401c045080d074429802c2d400c45411240d040d00050300c6150b55094210210000a9150000d0f600c01e010030401400c0c040110402c002c003041040c943d441c0240c001170481d030030411202a40d5620700d50011803202154034050800c40c0240f080010704503260040c00f9000c030344210326070401c0d821240200d511002c01d4032115a014103238880381c42080c8035810308131003170b59050524080041032820000d000055805445e0401d0341982e121041031003c030340080c2c00070300110740e5100702041000c078580300440c03e00c81e150f1f8803402c514002900241c03542000085011406100349110303510715600c15403e0803c0d440410029020790000d0318120740b00d9052580100d24144204e0780c0b14216a6030016146040780765443d00d0080e5403001d001c1d00d4113800b0400036200c49884020941c001548961010889032015008169503400001598052038200f0828000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 490365269 1250 490364019 490364029
    0x70b0a0204060e1507020301060e090f03120601030f200c06131106031305031308060a050610030b06071b0812030903040e090f011419020702030a23070312120902 71
    0x72000c400c0e6044064003411075004913003030040820003075056003002c1020a1245201d00040d01070f404e488101c8103a01c40e0724034102e03100e02544002103011120080060310759803203600a50920f101e00b00000034595112100c00600745501d0300c030116045800100408501c40c104a19a48000020200c007000b0720942c0d82c50203442c3e000b0680508ca040040045800e0402410704054520707031140031241d90f6184044030004c0d80e07200744280d0900340290070005681e9103103405070f00e206990046c8800c0e820722180c1c40503801842049207542d0010024420000041d81c2402040f5070b02c0428804034294901e00140d103841d00c1c40307004000d2101d03002801030240300f400000a8030141c5520603184001641c404006e070749031900304c0310400007035030a050b4850340100b80d4001e074601444070044e14660642d80c400b5040141d1240201c000e400d82d001049000c003054520652107010885448084298a80c4058851600103180c00c1500c01f1128115262003258000c2d05d000328107428002c092001030601d4001907 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 490366519 1250 490365269 490365287
    0x40503060109093011010c090317041e0509063a06050f0103020108070f170603070b0409020a031a1c02030f0d020114250507020402040f0308070b0a020406 68
    0x101d15030f602d072205101080301c1c07180a441800c0e00d14402e0f403408020825a03061021020342c11202069402c00355001070b65045c06100c0700c02c0e0f0540c0b1003008203850f6030369429503224028040240c1000c2404081982c0d07d85044030985c1b0741c6480030200381241040308204960300c01510b240c0c03056004500c1d04102c02403950709251001000da28105039961503100491407540420801054a4504805c10407101111171559040c0da00030b0b42e420307181c1d50b640ca1040d1221100c0205034008240c01000c0480e0b0b020040304140e60244000e410303903c899980e40480c0e102a0020b80001c490031380c02003151198a80d1610412510200c28502d0051480d81c0744c02080c01d072040904040700040c0c00c50445015910104800e03030051140ea002c40e11b040c4100303040203000307002c002c0c50035030101d03070380740c00b1820302c80c84403c5029680d99074034180c0e42034840c04001907400390b1007860120f8029400b03000019400f201d400c42c0800440c019803416aa410480c80c007264102e0005203605090b500c14841071290030340c0035041ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 490367769 1250 490366519 490366529
    0x7080f0c10050a0306120f112403130b24030c0f09090a0b09072603030f220b011401020a05100222080a050f010c020a110d05120307020c04020405030601 67
    0xb940d59000c20352030842c0900901c0c0c01c82c038221090003465004101c040d51484402500070510101212555410000c180e280e0300c01c0030095008a44008001d803481d14021904404102428174540f0995074403150555130484070600082607a100141c1010003001c40c1098082c3c01310040d20048100c4400030360100051204503000f18000800108182c0c0c0030005007440d240c1098003500146462800da9988a1050058032980004071039a911001c0c600a14480c106c02001d015504560322901180305100c002400400c4902c1e452207050264151102c0e80c1000a028403c40041036040540f40c1903003024882c200e50441d0720820308040491f0010410003483c00c041c1c1070160352860842003014144901d078001402d840145240041c500000040e0385450702d00c9001920b51103d501c903216800c840d281c02911000d80c00000c40c0600040382c2c3d030001d040e03107240180582c813962803641314030340317403900070510140f0428000082c045040e4040000c1c0c0e10b15041140c00b54905400c00300481c0d1580010f106e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 490369019 1250 490367769 490367777
    0x907050a090e0316060b0a0b0301030c030204020c10050c07020f011701060e040209060c0a0203010b06120403030b060d05090d320f04030215031902090616030e0301060807080f0c10 79
    0x1c2da00084180100d440c0b0946414400c01c3e242443e042480060041341d01c01d0340301e8801681e001844021500a0740e040342c0d0031000c8203821030b00d16000c0c00069400020040d00034002d8025244a40441c3d10800b0700801e03081c2c090f1900c0b580b0610502c0710403901125594140f0952001c812141c1140c2c00e290b0f0305442c42880d100308080300d0b0f41c001c00e020303000d0391a1055200d9408a55510288400038021000300c0c002c0700244144843c0354103100c3c041c41049440b4003d0200c0030001004a8000d03006402d440c1406460280341a5141440e1001c454095a280741c00750460505100714a602402003855995040509510018031000d00405684ea4030b6030015104004902d07030105001c00c0040e1002560094030781520100c03541d105040550080726840e401c1c141140782210750401c00e20a54140d524007401c06840c11541001001c106c040383e5000b10200040c9480003095030301c0038001ea40c000e1100c0c10003003203010b091019050807d8094804044681d010290124550361881000344d140d07803807814 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 490370269 1250 490369019 490369031
    0x103141504110a0215010605160b1009051302090703020307050706091e1203061d010308091909060905131101230a050408160509060f0d05060a05040b0907050a09 71
    0x400305028184070b841444520354045480a00540c000c194200200e88071503000030a0381e20791030141c0d80c5009102824400c001c1601c001300029800d1014190041c44409500540c280e0b100401c0c002d6a600300c40c3e4050600e1110700c41d5046050440c1c8454000c19203040550440c6020500240326010b200000f514407070700c07901391900344011484480c0121101848400c4508110708000083e80e1141200c03074002894224000b0b21413000005522140400640503200c80c1d28584407400180c2141c0c8100b90302911500f81000310010074128030004000b50030011a400d4031703203000f80c400c95500030004003105d03070105d041a000403071071505011980400d007015940110140003100081e03845520f8400c120350001000c1d0f1880741c000002d4000c4411039000c03110b600007030755400e08501c2214403400e9040001750b00810414641000d090311181c1020b010403844800300d86465142410035900030140c6940c4400340800d0207038140302207a00045810060091524010100b004400f052007182e1016580e60 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 490371519 1250 490370269 490370311
    0x504050f150d0c09050c03180606010f08090f10051501051204120c050d200d080604050a0b04060e071707050a0e0a09050907150918020d0e030417010506010314 70
    0x2e4000c901031300102d0410006407401c1601e02c9000d60065410034207001051407540750503a8000340d1107102c0c6e40c069481d5140803421403010380c5d0601c005003902c3c9150203040c1c0646580c0d50304001c8011650401080801c490408010b90070f80403544030002410400e0801c0311015805d0861359894000e03038001e44805445040d081c1c2110f510011038801000e901824500c2202c0941c40401080ca41c00c401f00f010001c0e110310703d80d480da100c40d424550f81c081840c18dc001540ca103040d81c08240e100d14507940c00305540c40741e9000030341103c1c1c294000112140110041c0080d01d41e01108429a010840080d584507003017151001d0018001c042c031800411041d14085016521141000c41c01080d8043d03050210342403442e419901c0d05858024016026a030f440c1941700e4603c21070380002147c8071030985403102e0b0100d40b1003001950080011404080e11088984d140b01c004000400003443c55100d00444c05122011050030340b08060000741c109410410322213900e04d0000341603500302501d44000c44401d5030038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 490372769 1250 490371519 490371533
    0x2107050c0603010906061b02100c211d06040e011a070c081b0303180d05070b040e3411010f0501060509030708060f0c070314130504050f150d 62
    0x10490030360060004400050915681e40041041e14210f0711454030f01ca080c0412881b20350303c0030780d02a6005c1500405000118003a10301568038501803240c1030500380c40341c4505000d10101c08a00000141001240440806c800c044808010030454041d490a4a08880d042c1c1209040c05503007414460480003070030188181c0112040280d010580d410403955a404035902c0d101d104941481c01000d52481c4070030f91034040112042d4003590155014215040c000f0b020042c04160001c0300c00e4072908002103102502034016100504e6601c041d02c41600c1c1c02c030101307482c4610240002071050107100b510b40040040c144210b40c05146454115007a8010641460140c4644080e85140c903280400216511358032000810040405900b02c803034141d562112150790b500c003211001620301100f404a00140e10100041540d90b00900c0d20800002c000c04c0924550b9001c13600408413454000c00410440c2080d000f01a8484981c1031554880e18007201034016143c41d11454500c00c4065552000c10480c203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 490374019 1250 490372769 490372783
    0x20321040f0e01090f05090601150e03010e01060503070f0806060d02040b10030605120303090304210c08060f010b1206060a0203071b0e0606041a091f081008210705 72
    0x3261000007101e40d600e03201c0281d80d48081c080c0007040303410f00c0a00f0303400214038090300303000741e04110007091140c2c82c2059004a40e4006640c0d4800c1100b502c1090515a40174055048441040000011701c04e150000305890400c081c0e21418000303000000801030600701044644d440241502c4ca66030240662000030018050010401c1c3c0c0079803144000000706516901240644c1c50640e038004003105130460242e905d000c01c0701d4022a95004001c180040b000b03809400244100303ea800c040800c40c1c40c0e40700c03079601c9102e801c85001c5a02c442d081181c1c1d10100e540e400c1c011301c51134801528010100e44800744001c2c0c01403e150060a0000c1d104607082d1081080700d10b600d801c840748160414014060120100c024460203007402204408650146041005c1b201215800e0710f4030000340701040c0d003030081c580003a1841030340304202e400780100400b41601078100c00c000e40c0d65a0103480c941560b5111200760590040345455202c5800025540101000d05c18414241c902e011f880c0c18007482c10714039010b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 490375269 1250 490374019 490374029
    0xf030b0111010e07050f06040e0c0f04031505090118031b020a0b0c01020304110102070509040b06041409010209010306062102031021050c09070503060409030c05030f13080303010302032104 83
    0x228141e41c3ca10000d0300070800c182516070850301104a45030301000c03c24075000740c1c000c100c048000f00303011441c51500c0500820311002001010350810340d50ba10b52681104042c070220286540b901c042140c0203c080c4503556141d11a038080e42c22449031520000c040ca0808014140305c070307480184103c00d654440b01d0010084c464031040b05c0c0d9480c001c0d42514042d40041d00c0071103014811034140c04541d0f002244a03415150040d12580c15903031150de4a0036000809407000e60855980d8028401d410080e01c0c04d03500ca2030b0703240c0c00035a40e08082400103040300c405911000401091010b2055500c61180c1291000b41c05e81078096220f4480301030b4840c166003958440c08012404201501803003101003824000d4074081d100b621b052240041c24402c9103002290800c0004604100003000c5103010b602040c0d500b4002d1502c0d00c0c0444051b510389255030701c55500740c0c3c401c040100301c07181e6044d010710354000585101c4002e14207551569010075920030030084d1a94904018484d64036203542200c0031b0fa40180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 490376519 1250 490375269 490375271
    0x30912040f0501020601080f061303050903070902120f01030c060c111c03110102040b090d080c1e100923151006090b07050a020111070b12060906100f030b011101 71
    0x41d95400200303100340034a01c9100d0140c0103140000a074901d021960301741e4034103000c001c1d203030381c2d0b4071078030798400350315103081c2c21000d000c8244100022910304100805c0540401c07140103036643c05900101c00104401400d10640041c5c1c0c00050001803104030080003181c00c2401d000c0403081080c03900541c50008600d031242c00507906c105409203400c91800300119580241c681c2c4034402001610780d4280d2089006040c910700d0100328a0b142c90130900038001c0c2a60085a5050801e0000e1380c03901c2c1007280c02002d40251046186187e10300b44400e00c0070720100080444200040e0041d6941c6000034883d02e0b000c1c2190900e224020500701c041030010755003890303440b0f020105514103500c1040d603075a0140104400035150791004180e04c40701034101e4280d160003200404800c00164011140e075100c603003a60a55001300c145c0012000740640150480c034603120100000c030720380300c01070186211004001902c5070a4014040f0700258100d0144040a1028900420200085001601c003c007207161001c2040d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 490377769 1250 490376519 490376527
    0xf0305090d1a07030509150c09040615360e0c07050607030f05010e060603062812060c020102044a0a0506061e0d0b21070509011505030912 61
    0x380341401980b500c1802141c4082000b900c403030b0800c9969144000b40060300120b08808070300103609600181400c48802000444d4164460081d4901650400044408158003005403695010503660b400490318070749200414201d002d00884204140034031500e014004003002250000458208660303200c0d07002401c59495042004009004110903074100c0142440c080010a180c0140c1c00c0c210300480d0700804850840c1c5811042051034103100701021108641d0a555986107448480000028600505604003894136070500d074040c2c4002c00340c001c04691041000348040c0c0740c150807480c5003d410362020205c0490008624080144224455007840100c0d006c80e00e902c00305101c168804c05034100300b4415900d8000521a2034024000c00443e00d04a0348004c1c41d607941948050102007049500104d05007a40502040ca00d110001d85542e00a502e0780300c80c840d00030104611001002d090f90104815032411140004c5641c1c00d84285c4100030000001c00c0c0104000c00c00d0140340f124488240d50f071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 490379019 1250 490377769 490377803
    0x6150301060c0c120804051e0909030c011b08040f0512030408031905040512071703090a0b01081908090d020a0b0c010f020c100c0908010510050a050301090f0305090d 73
    0xd032894041100d0140c3c207000081401340040c1c03040c030420f030ba00081140c02c09080c00d0410117400c500107464180144a0a0007114550301c040b0507601070b603031143c09107959150700440304d403c0d1805802c080300461940d00350345000d598081c00d125032094000b90880101490fa24110303080c05040d03569508150b40100901c4180507100000710301503489001440e8111002c0c80088040c0c400450707001d4015080a0f81c4c003804042c4440c024074049100d8210075945a9803100a5010b41c0c00c140c1305a0803d500090a800c1002910340355140980307000001400d844080c00c08044480041240060081718041340c0c0504545500c54201140c44d03000305144e04c801d8940c1d03078456107600482c0544000358281144901c44100300d10840e001d100350700010341804802e440c0828040d204404010040240c0c0e41705c009603440081c07140c540182c0c00407018440395481c120400031912081d4014034130030791407d80701000007100710150045045d032508103182c540c1d50844c00a0300e2149604006404010311030840c3c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 490380269 1250 490379019 490379027
    0x120105070f0e1f030509070f08030a0215040f0f1505090c01090906120204150b0c0105070e0a061e051308010204030204050c0403082502040c0809061f06080615030106 73
    0x1900c040c0580e078a028030b01245040120051105448041c0e450400200c40501c1e48241c000f0380d808000720302103914140d610b2915000c2411140e0240e80e1541001c201801d40315410300c804452000c60031500748803130415441d00302a1004014008020400a05000d010002c055020109410081c5000c021074070780220301c0c5450741c681400090010740c6c440000b0801e002a071088030140c640e4200011100b000b50b0b400d000c02008109621000c09910800002e00c05d9480c000800c0c1e08008500041814201000c028152040607440a4401c14541c101402803070740c020302064809011001002e04031104106c00d4a5a10403915101484a0309080102d64620150020000c03a48250707810045a91081c030492542d009030301000382240c3d070810000851000038140e151180b210b4101c10f207481c80c3c0340e0380042d041702e198549060102e40c040d410445900001d000c62544030204002c60300c40e0030014154559400f400e801050103202030807021541d0f6403204000543c2030504001240e941e9616640b000e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 490381519 1250 490380269 490380287
    0x30305071202011e091b0f0e0c03190207170c0a0c0b040b1204030e040f1a03011103161206031407090e030304062307030f1a0901120212010507 63
    0x19401c107000c8054200c02901c144910741100110f21000803000400074620f601501600400b500c213a15030504500c01015444c091000404480001410452401c589440440d0004000590540d0180708109400e55070740c050744a40b45145600507a228001e20b0080700d0070500c04944400300b074001c1681008d466000403400c08150042d100c61b99560340c0d400e002000c0d441280185085290140050014032111a00440e0000e1090134403045000c1c888007c1003c030345213101489440c42e05ca142e030154003d45d6146081a607003080d0700a00081ca00409451902d210240607400000e080e41140f5940601c150007040c03a001e6510307070610100b80e5900340081d1010440d415903100d07008507840018490a03a10480b40c0f0000f95802031400c5607501c0d00e5141c001c1048401010000d1801080d0380c030040d400e41c5006200385034039100040c6c4442c00c82880350480b00701004801a90071030f12500c81081d55140703152411a05225007458800400d071000c174080030380e4842c072503415600b0301d401e20500c645c000600c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 490382769 1250 490381519 490381523
    0x61d01020a022808030702070e0405070e0109180b0a0e06100f060807120c050403020d0c2c010e060d150c0f05070b0a090c050a03050a020406050f03072d03030507 71
    0x1d4507401d812080300141c50701a100403c200e01e40342c0300448000303101c9101656025603140180d460290f40d8011240c5000700440c0d048440e0b4000b1740d803c2c403400ca00e42a00501602c0c462208210220400300c00b91000c0c04240e03005030070b14050500140902c138098000c54a507084400a440c90350824030862554404907010703240c18481002800f107811071280c00c0070380c8031f0700711969912648000a05208003c000c440100003c01c0403c22011015860b40543e502c1c5903403060080c00702d22840c140c0085034a6208518000f040313401881c19010220880e54958191042c10318600f8003034072203030b0000d00e0307040c1c40d004001c100408120400d0304800131070b032001c1c7c910b4245071201c00c0362405804080b0b45a128031072000703202980a0f0081600b050741940042400c0344a030303142105440c3c0b01c0c00050b081030486e91045071581d014500000450030701e8010310b401007000303907021014000d620000a84426580c021001652810100d03006020018035150083d00044440031280039268180108254010101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 490384019 1250 490382769 490382773
    0x7050a1404050310060e01090b150703090b030f040b0702120703570309060818030d0b130c051c0204030f0308060108060108090c1009030c0f030314090a0302040207061d01020a02 78
    0x2d0f92041d60152710f041500081c03088288500a0b00d0300c41d91a04161010f42c00c00c1954030010170741c106200c000b5409052901c50400071454945000a2603680c010030f44000c40d00705011a012032480031061300d031140d5150a009030034040701c80001d50044070302c462494143c0d15100080101d40c8a21880040c90300610300d408004140c07403003500300d10015040004000840c001130400100d885040c856030070403c2c0555440b044000d0060b21490f41d003000c07502410b030643d074503407000140c6444d8480b41402e525004080c00b5840b500c0c00080e1043c0941c080314601008001061511010380303604850203903900c08880340c1d44030701c24140182807620032a0124007090031800842c000350f002c1e42e0703ca441f4201c0040140400da00000c28000c2010032101e882080c000c0c014008000620150000c0002d4000601e6610610f4a9800c005109040801c4034240584041190101c1c0b5101c1d101c04001f501e0f010340300981e9070441ca140040051402026002580c0204140d0708a544410340080817056000c0d82 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 490385269 1250 490384019 490384021
    0x90703090210260a18230f1c021603050303040209060405060906040c0507020405011e0b0403031b0c031203090605010f0506091002010209031603170307050a1404050310060e 76
    0x6420b42d00c039100d01d994091030310341003040d004810320f030054200d41c025030252000c641d03c4000c4000c04550b030503400e0b0844c0c4804540c06000d0110b5200d00071a000840c1c914000c240350803002290640390b0b82e0780d08482c2841802c581c20411281d00030440a507031054081c1d07107120703460b03964104070792030341c0098408070b00c50310300e4501046843c034190084901403030000702044000d0711072a042000408844500005210041c400c28000d640c0e02c7c881d0600070030241d00048540151211102056902c41e000701d12228401c0c40140042940b02c111a0f0600d081024651b18042e02824604800c07400e0f540010491017170021840b410030760640000f010b04e881424117000e16621000407154441840c05200e400100c1400030304014a001c0050f0055034a80b40001482d1104a030003007402c0004603032800d0500a00500e0400410031502501900002d00060f05030640c00d268ae4010403610486102c41d00300424108400759504c0c0c0e15080785c0061200500b1150b0072107811010201074032961040201c4520110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 490386519 1250 490385269 490385299
    0x2180106121a090415020408060405010513081b03191106070207120b06040e06040818041503030c02120d030b03070906121b0f170f0a050c0402070602090907030902 72
    0x8081e000959120000c14240520408244560310030004d0054031840da03501c120180160140c40148007604041018082a1a160130900d0a40e44060031010b50690301200c0b400100390b41c207040d180d1800d06d200d80250780c0c48140084e41d113540500c00c507111036208035403003039801660400d43d0200b80301e100c00180e8016a588a1040c0d881e81b19a218014110b4104841440000c5404c0359896201c42c00410028041071400d40e00761402000310350403182c1c600005000081c0d021300d030312048100c001c00c88052050a0a02045c04e04140492000034140480030501601315900d00c000300e03414030a040100c410300000c140d80100904003008075913000f4002c40c01d020900c10518014002a20400c143c0500140040c0c0e0725201d005003d07050318440d011004102044082d0144003402c000d0004829074818403404c00702e01d42c18032104c01285801603003c03501c40000540007150b50404540100c1d030040c1c0700c00050501c907000e03100c0d5502d1950b00104078420000da113034141d4000c40085009840c4c00f0940c00b018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 490387769 1250 490386519 490386521
    0x903030e01091511120703020d0801090203041221240807080c0f01110f07031e2024220e06040b0f03010c1112040b0702060a020a0218010612 62
    0x26010b00301004010041c0f0040a901400b4015003c00060003100c10700c090003100c00b4269042608200c006130802803000b21410b600c5202d95014100503401180b441c00c0998443c00f00c9400c1e400c1c60b10511001c0030307a011021801002c110b400c1e001d00300d8244206421100c00c94440c004450091000e6a019080450083d600050316826142600b0040000c0c903102020408800c403a80c07601410058400444408418140603012580c0c9039003000304541c2d429407401001b94003141e100d41c182040400314030001309590004010302d0b01e4449400a08502401e0080303440002004001ca08c040da003403c0091a901e000d078010b250280301950f116030351030343d48a400d50800e0440d101c0c561007500d103180401e00c00e14141d4410158200000d04020000341c00001080c00c1d50046281c03000410021040510750034814031038400c81038481e030011403a0504104003400303a4003a0b44d00c003a02440001c25a501030034020000106855002010020680b0940300040340f112000d006520000e6928200720400b201d40b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 490389019 1250 490387769 490387787
    0x612061314010504050408041205160603110a0315051c12030608061b041a07061113140f03010e03070309080606090105010c0c0b030a090c0f120f050c040c0903030e01 73
    0x5960740e0400d0320b0340391204100241c400900282c444080c100310000e8124040302050704898406d2016289180442500a06072215688428103260428240d0030360511b4003021991060030606000600e0b8a90141074180c1c505150450342e005418080c210400c100d8000780a14410704c40d9205040b10002804100c007500e81902c03901c8019031002002c110301c0504a41d035060320240f180d44140c00c00c1d64403800003100759007000707050302000000100c8000b1721805000e40000092008105031900210b0b40441616040500c2205400005000800220b5880600c80c41c15504014000e0042112407551a51a0b901000045010a02d52000001c07201004500148034550081060fa0070368640b80055800800c407080c100c903505040c0801054201250019600900d80004c0025008426140102441c1e1403078000c0d0340d40601c20203040040c03070b008800c6a101180e10010241c050641840c01c50300d004489013485501a00302010b2405180d4004000e500b10307070080e5104800d414806006480c0016 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 490390269 1250 490389019 490389041
    0x30d11070507170f16150c0c0603020702150f2706030a110c120307120b09010b07151404020f0f13180b100e160c0308130206120613 58
    0x2c0104070301c2c1e2086404095100b460b0080d120104038440ea81414041204101405402c003610288400c405456112403a641c1e0303410000c400c4c2a940e00c564016021621966080603000a038500031526403140c3c1d0414458102c0185899071112a0200047d4200100c0c422610351000c140006408401280f00030201c0c3c05030545143d5118603c0c2c0c0c80240c84070400c9600000c20421007244022410000002e511140072a410380b64204500020403e08600b50806440c1c0e042442c8841d03165074404071641100d82007104075603220b081d071400c003d480641201942842e8601444004460402c0c0803541c851031003191a5030001c240002001180c0680800c034540181445440a000203a01d03441480780711000c0e0004c480c0d182c5030f50351348020440c08940305440400400c50800600360081d801c2c0360013800c050390210020080f014005c0c0412003004000d0100103500b03000c2410a2000550030041c1174014002d5942e403990091600b8000000362900e034000d824462015062018a11440034182 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 490391519 1250 490390269 490390273
    0x72001020a0e0114040e130f110405090304050a14011e0c03030b01110604030c08090406030818010906170408090a060c03142a011d0f16360608030d110705 68
    0x1400d0814440c2000300041c0a031003420b9004013203102040d01c5d8411718023614401d601102d5440c680500740302c15114040d0950b001503000303104c20f00c00365440990f0181a02d00101c40004095110f20040711100d483c0b80607003800200d80014070f0007103580140142e070120b000741c8091002c00003800c01120303112102c0d0144025034002102180020f445040c0401419028402c110b040540364000103080340c1c5503038000c6601c1940004ca048a01040452121000c40242400c109091034620007410082c001c4060144400300b5200140c10040e81d80c054030300e280e002415803c000741e126040035080d802c940c0d50a80114104118010641e100481110b80d138006080000014402000400b0320020b11384130080d155540f51403442e241007100102d8003102c40420340007400016491191141040c0c40f960160194080b01130b41805014444d2302200303000c800502c42100c0070717240d030810002c85200d5881d20190711404c104000800800000c00b80002425000c0c0400c41408246641c02d100d11402c08010015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 490392769 1250 490391519 490391527
    0x61f180609030803011214010f0903180506092803030e03150c0d0908091008160503010b03040b150306040606060e222c1c02061e072001020a0e0114 65
    0xc0400401144041b500c280540c240050540346038a003075072101e00d0455038550707680110710705160344107645844000d207480400d400340d0b041202080c00c41c4160030805019601c0300d01e4942e11401580e1411034502d455041003295540c032031a00800c00c00d18030134518400d1088010003a44014200f10b058080d801090110345042c550401201c082d2110b0001900c01c00028404201c4a0b184c4441144500c010361792080000c2c541340150303844121118044e48208075082c001440858107000840ba0442e420585021466440e41e03641b0300720050000701c041d05801060709000c1004904d07080b110984e02c0d961107441d001c0c1c5041e4141700742d03500b4a0040d200703800c8000303070004113a0505520021804c0381451000031201c446c4040c0030744207800103800354016400041c042203401c0d0f03015034001e0809500e20150240e03082032960300c01c40f20704124540c913400444001144c1c42501a520103148030200039000164a080725041d28001e4001c9510400864865945015298410304200c9102510b0404440c14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 490394019 1250 490392769 490392779
    0xf0a0c0f11030d11030103120819090804081506010e10210b0603071121030613020409090f0b100303080a11130e1515040509061f18060903080301 64
    0x702105180108840380401c203c0b0b48081410342c010380fa5a0030101c604150b9a515510f80707000d030201c40c1d417141d03000c001d1b80340188001d010700740d00c400c0d4003e85030240105940701582000c1c100ca10075980603100f144141d0382c04001c4207a00d40b034107520880c000d80751070b03442e03400103002d002001003105000400102440981ca006c29250f00421074150322441001541c0c050800105200d94801d8841002292001d0324400e1041000c1040310b0455802c0b110703416401d01c174881c8100e00c0380005040342d84140d440c40780c03007892000c05070b06403001801c407801c09000111260500507081009d40200360384c601c4d003110019101c1d01c04a10200212070b8103076600f08241e914113200384002c000c00204802c0700c200c2000201c00c15034110140201030141c1c60200403243c10412409983c03002c800503424003a040c40003201c2c180f000305d401598201c541c240e4000c441a0b0300d03a400034203c44240740c80350460840d040e83c80000306500c000300f02252131600c14488040c5071510b130203070b03008074680c40002c00e402c40800051003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 490395269 1250 490394019 490394027
    0x1005010e0418020306040506010801150f090b040f02030703020c01060803030c07080d090c030c091a011d04090204020d020309060a1a12031b030901091409010312050f0d050f0a0c0f 79
    0x10310b84111100c0120030440070b60001e41400010741d03042e10305621210061018440a10424440d00c0b00d003801c0000803071824010300b0001d10181b1038207544941d5060034111031b0f00c80d6081624042c40300c401c01c640d07070700d446c01006c0c000790442d850806240d032a0040104101400008890080e4101030500c1d0400405a5030314140741e04c603001421285840b1340c0081c00017884c1880e07e02c0a90710030020303d0022820011a01c00301c0c1c0d0201c0d400c0b0100400304400b80d0403a40c103c03490102c0f00c0039001e43c04030b50300c050f000410b010700503441303000390442d1001480000c081103943c05580690540010744082e6200c12102900342c542e001000d850040c4200c100c03904515010031080e41400c40c01050381d0900c0003c000134600c1c001c01c0b602e200010340001071411001d43e0700c100d0b40d401400014183d504581014404169010f00500000303050760343d403203a43e000b66400b80c1e060f5801c0210340510a69542004401403001c0e10041e02c6040614071140085100301a41c1d0058000c082e50541d1406041c1c400d07120121 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 490396519 1250 490395269 490395281
    0xd02210306060906071b03030509100309021008221208100f0b0310050306151c230703020a0f06080f0906073501050906030a0302060712150602060f1005010e04 70
    0xe49400400d44106c4541e800296180f006500130344520351240443d10038080000e0100700700c40c040510340000000180d490031000345d0042c04070b190150260356001d14400d150100c07000b100c64280241c0306480c1c00c2201304020201c2200b220380d91008152184011034910814034041d421450b0012141800002500406168001d8450621000b002c0d95030000c6030038004c0c01c0d1742e4400054008000c0e00c8071810115000281881c403400740c1240c40031a511082202c615695802030000c40703000c040c00420108000040240d50001d1401c0c4c1c40564405250b40d20800303170b00c190000b140d004030000b60441e42805842c1d00c01c1031400e020345456598910101c85140c100d104c84200d90401d802002440b681034061101e450640403d01103495040508001d198040200454440c0e8821100080000d038003245003034100c030b5030f401e2000311b0070800d40044000d004400c0070110840f0000000080d050f40c000b41c00c0380281100074080c40c6580310081010100f8035a801268041017508011040c41c1c10710760b00007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 490397769 1250 490396519 490396523
    0x18390605090105120f060a0806060d0f050c03030c1501060c031d01180909030311130329160807030624170406051e01030c03020d03050c0d0221030606090607 69
    0x11504d4424040c030120b0b10308100780c0700304010100c10380800c1082e09100d1201c5000c2e003040c0c0e00070085480d1401c000341c003c220034600103028845901401d8100002082740d020190030050650f40c4900c80005c1840d61402c106044141200b40540001007540c011100e0b43d4807603030141da8403d5050942080001c40e02c0c1448000c504010094007544070000b503001d064800f4000f01340c1c02050f02406420002d0950300041901d50a04c1d404110418501d00c020340490105c1c1d44c0080ca162203450507801040174400d504441034400900c4404001804c10b282000001181ca140c5440c200d540b00c4140071006c944490141d43c44000c01010080b40111062040031084111803808100c00201038003e010580000d84007210501c0e11817040c0702942d4549046a00f0419040c1d100705911761540d00c490751f1101070b80c44080d0085043c1d041407003d03d03102e042110300d1108031400701c4103000081c5170700039a144518081c03045400c4800c03500201c1555910100c9000342002003e039420203a9032010045030703911103030007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 490399019 1250 490397769 490397777
    0x1020c0c1804120c150c3b0904020a150503010906063603020d060e060117030f070204181202060105030a080f0901021903030515060705150901183906050901 69
    0x180b0489042140a88000e40307020380c0d03500c00c41e903400b5903090001d441e001480f00587d12100c1c0546030341d03e00c170b0001020707181c004a407000c00585840c0080f0303046501540098020311112107102c240190010b00660488000c5081003110b542c1c0c41d6021038030400010042550304d40044200041e01040c2801038880c402c8001092130300940c0e035400520110300c54442200c03515103564070140e80080c1403041d58014074140f1404a20f145108001ca0340300e00c80e03540c1e18a00501d01140344d0003035441e07651000b900040307200816000e4440c0790a054007105d07519205803006208082c0003040605010516140466000000600303004803d13008140580100b9051411442901c0036140311344ca103c03600c00d452a0098070001038a041c400d9020354282c0c0140d0640d40a19020440d15001650024011003408215407140d205034840031411405006041e54155600f4054407091061001134141c4102d10388051325180f8031403c0d2004003122a031900b0b59294040007910204020303050090000b0505c102d01450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 490400269 1250 490399019 490399043
    0x603010e10060f09110d05090c15030f010602241b0a0f030f110d0209131109121b0111100c1e1e11010e01020c0c1804120c 54
    0xa5615041c0c103200611010307502c0b40010001ea04008800102401d8048400d00c100308190014006601c103441b07000c813015079135200041d04084140250b1a034100010b1900c03000000001328440180c009072488102c00d51150000110b02c0d00010707840d003c0648450090044280807155031714469001000060324403508401d035405090380c0c0008006960142d2900c1100e00040e07000101125205004510940e18000b651900305158906852000c7c0301c840b805682c4800a02c045401c103140307a900c0181e26402c160751900c01604020190041d0032082d10803140d00078a0503500d540e85d45924000701c4c65252201494100ea503c42c005104080c0940d804581250303030100f1388101200c6d014400c1c8070000c0e26024284490400320f1740300c0e2030940c02034138004100c480701581075008203103045e09543c10300522005a848128080d00441910b42142c0c00071034030350110403421074541143c407100034841d03103142048000c202c1d01d102c489801642c2154221596007080c50003503034040790f000c00070b03a03010022134 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 490401519 1250 490400269 490400291
    0x4090f0513170c010b030d03020c19051b190e06031207020604211a040b0106051201090b2b030e06030f1308040302100c02030d020705011227060b0a06030501030206030708060301 78
    0x3c61fa20f15603003990300594580c4100c256130f06114201034800302280010364903401007a030014000c01c680300b004e00070403c80c000d0040080c280e9130395000d1044002550460014854052440c0c6901c588001c0d03050720a4095013284240c07441c0301d2000c0081d405901408103020030008009148516410700f8003232409a80320307803034122003203080c0020781c0b4a0310b0606041000704004194085c3c0100324a04100b428800245d54070060340505015011096543e40740c4030001d41d44105011620009800c0059035980001541034866480c007501580800c1030140c0550ba075040090480e4170a01000c80c0b50400b98886494034103615100a1090759520824000840176035146407200840050075211018070f81031520603d800c00e02441c80317030000d64118100c100b00b42e980000441d807a6240a22002a420404456148070907401001d8016070552515202040040c568400000c0b400100e034018251030380c81100b00c0c1620000d0000035003100c170038008101c9650203842c2d0b16801040090021600740000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 490402769 1250 490401519 490401523
    0x20307050a120c2a2103111e0304140d08040312090e07050309010e0f121b1f0b0f0a090b030a080a032c150403110304090f0513170c010b03 61
    0xb0301c18859402c40714580c03004084400c9500c0001c100710304503100e01300030400036100102e1420a01601f4006621206aa0710f00305200c0f003c0305020481c0903100820038480160350320780190080d010455081a454541c1c0e1034084410074005d58425802854a421503a0b5901c8a49211458006218031880c010810440c9800702500c070721590f5648035140c0c90841c110500b9204d0340120901c003a00300850f000384203980031403805c440c00300400241d0703603856128580c0c3c00301007a01d650b180c03510b00840789001c2244404211501c5810b03101c2c2e8007404402c00020400c4030001680a01c139901005181c01001403640e5a00034406091004055410803511a107880e10303d030780049003020009035141105190b68942e10183d407801e0350343d600034a210f500c50300c0d903080c1d03121a000d80900440610100041c1010300c5800a0301c1d00445580543c1e403601d41e80c01e0008040d00c000c0c0e9040781c0c01c0742000000340c7c00754070a076810098950012082980310a4518607a1607550060a08607115502c45076004203580781 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 490404019 1250 490402769 490402793
    0xc0604290d050613050411010c020f040507020106050901091406130902091501112107020316030809102d030204050402120a1103070503070f111e0d020307050a120c 72
    0x4903a00c0880c0510f0081c00b0007641c8103074200e40031000d500e440b0600000c5280000310742100c02c0c00303081100e16a905030000070614116420019413040c240f00030040704641c19040070b01211425141001c960742c80d20a044142c0e8007810004240f401d944000403000d19210710440303020504070000054100803034000c074416840469207660340b11021038415502e940d2005002103800f1040c0c001d01700300428501c0586a0304a40038100c141c0b581c010446900755034007402030810250340d6468000030140c0e0703442c01050940055160520481c0449a003110f4103001e1203c00e0b40a841026040b62501e034041003120b00d82034421500d108165003800040743c55103441c8018a005441c542802c22185130050440080d140302c20360600c0d6804003403040c048410b4001094a41000c132500b8400032a030f03251a000c4507003406145808405100f0071821300c94160000c0728811100b45500c090f51904010b405099030399225410005145600600181d40032034048040e54000041703603d0300b84952403642c0c58020703040e14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 490405269 1250 490404019 490404037
    0xa02011d130501050108070903020f0d03050909010f090b0109050f010f030213060c02030c0f0901060c1718030c0a0b040b0f0c060c040e1501210902100c03110c060429 73
    0x82d6440040c03000d50382258803154003000600d00425498110360203d10b201c405100018040c04e1900f007400704250292080c1c842840380502604120741e5030711180180d00e00c04384182c2d02064070f00050031941d0b500c00d01c1d0001c142c5001410b0800d00d04120380044403031000500000040683c01e00a81c004503501715a0703900208110780d240c19100b2142e00405003050361080f034051085018044603401e5844189070107045900d41c4c102590500300504110711100f1114198043d901c0d8009085e0758204260702894485030801da00315040383c504541446280107042c0100003540e034041c031041120b1400c100c01060040404080035040882c42c2c50000d141c10420b4a845c0800100482d081c04041900202c0c0341d801403000c0f8000344e0201c0510000781c10b01e24520048120700a0700b480c4c40c01101190f40100340103d0b40034011511002c0b00b58002401c0d00300c1e80408500003020481c030302e00020000a0681d2180da00180018030342031030580d40300514984940002034080000d40c0c0030a000342a4030103082c1d508 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 490406519 1250 490405269 490405271
    0x19031b09030510020a0e01110307080301030f15060b040b07020f04061d1e0403030905241e091b18130b0f101701020f04090e07060c050a02011d13 64
    0xd815407908504180d40c120100840d54818070050501661180155003041c100382080060202000c1202c0e0541c890090041c02881c1e0002c000010000ca54403044074140c041c2d448a00545502c80c2180240c07000c910684c00000000e100501c04500c03a0001001402c1c40104181064201d01d03010500307403100340d032064208400c100c10064941039031902e501d41c0980040a18020301e8411001e4080d0000003a101600b0107507070311081800c100040140c5d100c9210b02840501c62180850b200f031100c118200c500701c58805a50a8596407001da90b46020300440c1032901a000240b0200c1062042285c038100c61980651210542c6140c00790b9030302c07054000c138107642c17081c0000b030090309111803e103d01500d041c4500003500b041040b540314101c651800d681c08244071191610042c03004601a009500c6010301000000400040305072255106c1d00e8210078500946e125990350b901d058502100c0d400016040390444405c1c0c4006620441c03031001031107111518008907540000c0400d000e090100804090300d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 490407769 1250 490406519 490406537
    0x13050108010608010b240d0204030819200a0b0417031504050601090302100f02070503030a030e0d0503011a03090a140f0106081f0b1f080403030c090b19031b 69
    0xc900070b01941740359a4090302e00003061502e080c0c1140d10390303d601d6158074800e9404545000d8545843e01100d0080d40c104020548504502121030900c00110030608045100c4100079000d01c040c490111103202801c0020b410303803110644a031002954006d100711090407407800446000ba40c0e03c8050341c0103802640711000006160300511041301d001614646c144280306200b040160f40d420380301070981e503843c07070700003100113458805901c0d00c06140c1010303a2501021a04a40b41c60703042e0b000c841018080300485914000080e41919284401c2c02061041031100141d0f4000214280045030800810000c4400300c0b401c81e103502c6241e640380c00c1420f540390000e80c100c481c1000240a5440900307408400780052200000319450120003565684a545032030f61904515030386ca4442407910f6203083c0000c0c508110072840000c0030184111001c0300442d02d400d5401102522650180056600b840001c502d01686407a8041342c100e80c221145c010075072201010890000d82002042d94650142c03101020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 490409019 1250 490407769 490407779
    0x80c0a0c142508010902130b010309052e05060a03020d03050c03070308040506060a0632070f050f0d0f030e0a0c0803030a0b04050405071e0305070f0608060d05060a0209130501080106 80
    0x544542e41e002503030b240c0c180182440540d0b00c00c0030134604000e81500001e0000241c5005038046c0080c460090194001c1d1428041140061181a84101d480041e440400606060b88804980c030584803260800d2150806100500b055240d00d640d481c040c0c2020f90030020018040f6166520502c4102c0001d081f81050008001003082150b80082c022192944d5841c00c1c010b005168160a0b00c04d529280b105142c582590906e4511903c41c1c04003500e980c65584000341062109010380c40c3c0211054810f1508c4894506004207440100c00c1d01c654441405051050080b800381111a8485031b15005042081c0c000407000345900c1c005200b440050754580c03034000004000c803107020403140d0045003000100000100040307081015500300135400c0d0f14080c81c41c5400e280c05101500000d1040c815103001140710302000c01c04c0c5086469558030103100e642c1d1107051290305170f5a544000d00c00e502080228404440540141c05132010141003444000c045003802c40a9501c00c0c1d0103180c06954418040c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 490410269 1250 490409019 490409083
    0x709090c030506180a020405031e0d0206070215040309050d0f030f030204030b0a0e120a0c1e021f02030f18040b12030708030a0b04020403051606080c0a0c14 69
    0x190032869410204a686405008501d002a021109040100340c040c00980100302a60580303018280c0681190440b580c00c4051010300807205407640c81c14030071990203480807440000c89a10840c0264050625a03a031003150b9060070701c7c050422801c0c009a4140450350b0b07201e00418101c2c15004e11210102c00c01c4500700501114030700610f0320708241c0104400d101062180c1011500300d00c1c0c2500c002070650f00c030218181000c0721705003082c0403c2c1d00024820320b21640410811031260007103801156031001c00140b080031100742c1100079084007000e0b0783d0400d032000481500d0003200160064a2030185160882c1c1c42c40c0d405495900285040c64a203d20a401e051203010540c20050702c407070040c400650b5000756a8003961800820281c03002000403003024154001a080a2002d041552104c0d03d03480c0860715002d00c41a0010083e020080c00a1070a20600c503190280b50309018240c5030a1801c18101e40f43c0811340c806981e001c21062281884800c200006940d446001d0b48007100e08441442c40740d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 490411519 1250 490410269 490410281
    0x8161707060f020f070809030c0a0f09060503030a0e06160b0703060e0609271009080301030b0708040210140c06100f09020f1c180503190503041a0402060c0105070909 73
    0x401c010f00c1400480d40e40c0c100401243c81d5950810b100646400c6240002490b00b14810080390b003200403080300140021020540d0380503150f0080301070009588900c00e00d9078170b0042c000e118001808407003642070142022401041d000d11003c60300b2240c2c81d9691920020603e0542c0c1076000a0f5407940c0400000f81300b0a48240c000070200e6000d40c203030404003900080741d41d14445250182c62300b00e104686e1100d0400041400190340c0409006245003420b01410507002440180c60000c2910700041426102c2c0001510a42e40106494491828184103c030b40c0d00840d185441110340410000c421000d08003d007600ca4034690100680050810820070001c6c1a2980074601c0c0c40d00522442d03100c00c07984130030303140314404e4034034503804501c00400004080c110139201050075000480b11642031107001706c02007044607608020a103605902c1e050841300b13488100e03070160484401c141284112103040c1082504a40002d000ac1c1c01c10f10304401c014210303401039590f1004200c14580030040c3d024907004074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 490412769 1250 490411519 490411541
    0x120d0e010506100f02071203021e0c010903150b03030706060f15020d1d04180318080c0411130f050f0a180914010204090b09180a0816170706 62
    0xe01c242e080c80e401155840840075404004d01c0500119282c20f207108100e01c80003811044615050f18504d03040107034845003022581030800300350b0241d168001d8400199001d0701501a95840c40310392541c0c4071002c01000c00080801100d48034400d000482d80c041018040b25800b807080001d445107448a20142100b071584848040402c100301c104102c0d801040c00000300300c40e030400380c0f0f44441c076020055181409031001a41702d8540308203000c2c200003440c10279000c030b0b00c25228130304034061001e1b03c9100201a4400d40495502c101c0c82c403403460410390070807440701007042075942c2403031046020402c4104403034101802e5540075541c1005a850021107550424130151038040285003401300d50044041e510361540d400310b4a5800c034030200b2034010398052003c0d0300c0000071505c03943c5800690001e0a1903401c158454030803a0049000100d0381020380203008400d1000f8201c104840c2da80119980022050502041101d103d2b4001303e00024100415480302c4000165075500f07510307103c0111500d000d00d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 490414019 1250 490412769 490412771
    0xa03110f0409150b0d08030a020a0e060f041208070803090d0201111215131506091e1e0509010609230f0f060408030c0303010302010f030b03060601031d120d0e01 71
    0x150b40c0410128080203101c4802c0d0314012924050780c0000c035903000386000c030041c030052000007000050303041c5d03074081c0080303040d196a08420303c0084010080e1a000300314003d01203400c2004100540010b4010401140348111212814020603884030501f0790011620342995402030328030841c00950a20503c2001805190f00380e040c4144083e1852403484001c08202d508198040d180780c10f981e500700502c061140c4480c0c20b02010481d0794180300f8400e07280c41400081000603202040c50003103a4a40c40d0080c11401e040300039103140c8420380240c4581c001400b00101030070140842c0e10344818100e24042e00c0661103055000e4545207041407240301040c402c007802006100020703400e0785c0e03040405441d60000c580c0014802240f00024449100302da0001555220005000441500c0400a035040300d0003602c8140c00319140a4040e17080d200202c0c60355605400450000340d4540c041e038441c103844c1100020011645c20301c9045585043c1035001541c41c5601c1c04505d40d0012240c50080010003c15600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 490415269 1250 490414019 490414031
    0x1115070c060b0d060504030e010f020c031510120302160b090a05040b0310020c0d0e030f070902070c0e07171807210b0f0a1d0604110f0a03110f04 64
    0x204008240d0000404180d2503078400d5840755141c1440882e15608000c0400050500345400340100303003226642800700d000300100c00c50441c000f0615554070000540a0868060200c1c0340907101c5000400c1501402903181e40450486010801c08980c2da06c20340040c403c501b0400d41c0001072035060760210384155010000046141c541c0030280c012a4025280801e0902518000034100702000f036400380d41034408105840541000100c10340c85007400d496108118000e2001c2c035442d42401c2417510403581c0f0440c8108412640e55004201d80d5001c0d0720112400d40d150f000c46980c1580540d07005000841081c0c0d2803050b801c651300820b4000058680c00e244894031164100c0d00c81010b84140f8020111b008800068208c1000d1103070b4000794401d0210706a460240da00c02581113040c1c5030020300a103042801d040c01c01404803960390200c40d50006201da03603200d42d00d08000040500950741c22180206c004600d43c0c440b01200720296100c0e040107a0304101082c14002104018201c0a1041741004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 490416519 1250 490415269 490415281
    0x21504020f041e02070501150815011401021f0506090a0209011b080415050c06060103020313020904050115060906030e0c0108060108090111031e13030801331115 71
    0x680110071002510082800e1280440600c0000012000b0410150000070b000c0c080001c194892003881d05070b042c80403161512044225955203c0081114014210714010301842c1405a90400e080c10144100c914800d250005000b00032080b40da02141c203620359041c007016240500e14554001d10643c0210f00309054000024124410100592150881040020284202c580c104c501402032618600807e0b1a2010002c10036405650380e401d181c012600420015842802101e0055810001c4010044010707000c004240c900034000b1582d81d90780303901c407030004040245800c00814060701c40c1d111480c0391940203419104d01c00308034911600321a24014007a0703040f116140e0010070a28040f00140d41e1401c2c400e0040082d1240c03080340700c1d00401040350000802c140c2c400c021310110b81403809510f603240010051102c55a000b000304030310300014822290f00180000d8006040c0c026041203051010340140307168000407501c00040c000b410b0350501c3d90810401440c0302140c210104101d49422 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 490417769 1250 490416519 490416529
    0x41b03051e280e06040c0e04080304021003020c0124050d170a05160813090504030c12030204030c080a02010305090f03160807050607080916050105250f05030a02150402 74
    0x90558582a542c01c0006202200c441c50044440908010801124000c0c03079106030344074003c980458400036455030100c0c42115456480780180d07440b2002c81c1c03e64846508021110428100f054200365003840503003081e0308240204600007080381052240441d00951104c03000400d908914010359007010454001000151003180d1101c0380050aa22482400300880341c034419890500c501c60030ba01c05c24014007507020010103080c01c01d0062079203043c0d600c2c038212040d11012500500032451031079010010901244281c8041021440d0043c6019100c0c1e5600201d084035410690300380e40038050314030071943c241c0705241e086a2088000c110b408280c0015654034494490594030342c1162209207810414068103a4001c65407020070fa8030f00e441c12a5009007251001c0758203031030503c2184161104541110240c100381c1b070040c2d4031240741c40044454040084208468540d240612003050400700e407a00054010f154441c10145a4071102980c000b86000070612505004803010700c18400140d5039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 490419019 1250 490417769 490417771
    0x6030b061c11011e02070816060c020d0201110a0305180603061c1703150406060302040602070302060c030409020f21010b04170c030708010b0a09050103020108041b05041b03051e 78
    0x807040b48030003034030240801215a110307100d0001d0502002c2622001415801051400c1520f41050840d070328442411401071606070244504e0000c00c100d814251f005d801d0180700900c1190043c1405004000f04050491421900a500b9000103102103002e28007400c03008105240c00c181100c803d41141444000200351100c041d101c54054001200a0310402a00444204019240f8000039840b46480010400e40c0d0707030110315041c8103902d0a0f10208417140240700342d40030340305564000d104080c00c41c0d0030700080b40c0c000c1d05850910f00c01030000044c1e01c481070004144840c100001a625100d409200900c19603000080d0081102c00000510540c442441614103d440b0b01c034040110080c404c01e4141050f46000d070362600340c0507155010030010300c150000c242103401524403000c1d039551840008200c800a0100a000030a800003080100355403250000740480b60501d100354040d034500c006011607048607c0f900c1c1025410b20b03161030154051043ca540324008029082d0300c200140c0d00b503960b040b8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 490420269 1250 490419019 490419023
    0x60305030406091a04150c0609150605010f020105010e01060f09030206040f180e0604060209010c1b17010b031b01120204121a1b0c07081e1e070b030a020d0f06030b061c 74
    0x421f40b06203c0034850a80c008161050700308407496020100101c0080c007814450080e5804220045240d41d0001d10502c02c25048403600c20104a40b41d08200c021210303007910051110400941080200140c0c2d13920004200030305140513805480c510301a07145042004c00c480c40442c062a02900c801c04084c0490b00c0c580c0250710074001a0740d83c12490051300c240f6403001002d0484898403846100c60814004000d0079030300034883c3c444140e107a0790451402e9a4080c0162a091b800141948070100e4040c0906412501d05040c80c007400c800901c149400c0343c00c44da102d83d00c0c8042d90f2115105000000e03940c11020f00318041c00808501d071040c24261003545904d40e00e001030344000b42e05d103041402440361030040d01d12001640c48015410021082103900751000c44603a014600c0d44000f81544c4000e6400d8034001032000d400e44910b000800c0c0000c1e0402003007040ea55408128465800cac2051081c080044503e1400041003421801d10b19100d00e0004d2282e405202c0300419132410100858244500513 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 490421519 1250 490420269 490420277
    0x7050604080d0608062823040c0e07080a060b070515180312040c050a08120a0912050a1403040612020706020f0705031b16090e01060305030406091a0415 67
    0xc88000440c000418095100d04000c1c0545d034140f01042c540f0030004660030003422403100c50807a83d16111400c407480e00c1501022400840b07000c0f00d841105800c400c1c0e00a0103421000d21440d81c5507464249080100c0d85030001600e00010494040441d102c2e03800a000c66000c48d6081044503514581e6510800721806000040c1800140200c0c1c0d03612002d00380c0b05240303c1901d484203142c0c4034004c8440000e94040707078242581c174030204d8141464080d5004886101000384001c0400c101c2070190380e4070030148001000301c1c000003c40e003a0400344110003030512501c010108020b0318104400c140c103603c89001c40940040204001c1154030000c000e2001c00d10800040c1d44507410f1400700000e206140c54103907400400300d9841c007800b6001c030160154010004001d05e60400d100005502c0301a129100060952080c80500c0703c603000d0341c01030610303001840c00010b88030344175181c2d20b14540051340040d001601141041c4104040030210415185000d20b24500700390501074a4980380025459203c200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 490422769 1250 490421519 490421527
    0x151503060106172a0c010e0f100e01020a08160201060302030d1115270712030e0310061a0d150803030a060902130e0c04180b0a2106110c030309210705060408 69
    0x108203502076460985102c7c01c5400d6100c0d03075881070741c46100f100051030b0306615003c0c10390100d0344107000b1206070b54042e44c2d44641c1a541e01c600c24400540f0003c1305c004547d40c801700400103032000c0200c03c000905ca601c03a100c08580052101d40341c8810043c0d20201c0c0c144030824003804e241c103034511400042800211038a600c89038610240f0b00300f41d507885001041c40b4848800c0a068211284011541e002d50603624403c084500020540721244101c10800700b07051a041100740100004d09203d40484401054150081d8200c1c00f01c0c1d0b4103a041601c054100009100804c41c042c03140c18003c06603003005506002c0034030390004107401188681c2581480c42e400041c0f8888212003158054039003400300c1e80c2c400c412202410010614007050307a0003804c0650010450050400011041c10801e0003d02203002c410340d00d9002809150995030b8642205100b442c07030000040c0b020314403808008006283c2c002d000606104c1d0940c0103078000100d400100b0503400480d502041d0941c1c0650008812035031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 490424019 1250 490422769 490422787
    0x5010b040c1b080c0f1504060e070803030a0b04020f03190507031a0d0615080102090a0603020f1c1107031805060306010c03180f03060f0f0e151503060106172a 70
    0x100703004544911170382e0282902d011288901c82c8481c40c0140d0149004100c0002c640301c4031540c0314460f004510090780140005607035250150840404c0754000f80001d402c0c100c1c1260462801c0e001036409980b404064002030035810160310940c0c3d07102005190510981c0c5c01003140740c1d004400240450300030b06c0c003050031f1428480203800007000000345550486000d41d44407801c5000b0740041d50380d188180a58000020814864000c1e110801854820b1901d40b0075007209070f5402070b0b240e020402c00b164031582e0202012140001914030039005e511500401e40c502c101d8100120721a80003280718000030300900003903076401152120070036030604060854503c042100c00c03181c140e0768000e80b41d1013541940031042107850f802c00c10041c1940c1c50280318000301040b5001c1551424440c00e0001e030701405092410000410005030041040010a801e0307602e80c40109003050f0098001c00e01281d81c507005511a00d40c44d0b9402070744140d00c0c14662103100ca250b24030943c5404954030b10842c00310003080b41c0344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 490425269 1250 490424019 490424023
    0x110606010e010e040b0907020601031208164410060503130c03050a030324030206160204140901020c12030f0109091a0115030f0b060306010305130c0305010b040c1b080c 74
    0x1401ca00003c1090541f440c1c40d1070029500c0300e0900003141c4154840082d0300700640951040780c06400d00c0702812100528108013141c80015a0b4000e405900070f0440d5007a41e40710100000c14625003112803202200e21104020841c13200c0505030a54140034200100030680d84a81500d811110199903081d0401041c100700710261025000038046004400c00c400425030141d100050b0702442007654408200c12200380421b00040d4803003c0d400c9401000743c84156560f00105040d15840203200150b00070310005002c7c4000002c81e807c20303c84e076000652038290002003000700b580320803101603e89980b6000038030045001042c41000005c60f11005603000300400b42e0410300d29107d000c030f10b0b04155a1342d40307820b884a030522250300020074600104606114818002d81c13896500140110b0b1854445d200110000c2c5001000c10440d25a40000b0b01d000410800e44007000f10b0203680040b400d50ba0582c108811150310303090304824450300e007010b8000c01c17164400d403620041c0c10028032507e40c142001c003d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 490426519 1250 490425269 490425281
    0x50d0b0a0f060309210f0e010809060402041d010608030403020a0e070509040b0f030f16150206010308090d1a010501120504020d030806030c040608071e03080d020a02070b0c0d110606010e010e04 85
    0x1101400685c0521840b0700d5108072200e1245440d9542e102d84480d4040044d41c181c4416641042507070445400180581800c0c1c114956802000100c9a4038200000b00325003102d07955000051690070000d420020340c40c01d5030703440b0701074000e0303400021250030460806012440713441d001c60300031512050301d80a140da45142a020b900b00c044e080d245a004c5445a05484501450300014580120140428078544940b481d0b598842290001c2c40720f6421512050195000481101c6c3c1c00715117041c03501e0000c0c401d40074400c100d001b04451800d06504090001d07003201082d40542a030b441ca03240400c009640c1c0c401341171103e190181014203c546030b0002080c107100700700c0d04198010341424000a1603800004070b146c2102c80701d80180a5a1903d4864042e0f0400213120103402d40a05000703810040c20300b98000c0450600b5130040345c0005980d00508030181c0c01100c078405c5650081c005000109421508001e09082c0da00090861490010000f0781003203081c5140504014414001c07115030b490b41c0d4000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 490427769 1250 490426519 490426553
    0x607030c030b060f1201080f0a150b0a0f06030b03120711031029030f070e090a0b240a0b04090f0204081c020d020c0d030e030a060c050d0b0a0f060309 66
    0xf5503941180980d03284c0e59480300700c1100c3c0e2400e020000084030100804d4440c00440410054200c0326040e40718500c1c40700d00c54911807502c0360f480340083c946548880f1400d00914200c08646031440c540303200901120305c1a06c159000b504003040e070540d15220f903000c4802c40c03980409107407460b85401c00401c1c038041c002c0166461b41d0f8507180703000c2d42e000324044444c1d149407a10400d02591061400c20326803101341030801500e05a0103848180040c81c0e20390015a40000580211141f840698545851a000c180c03100c1c420803500d601d4103d0402d40b2555090413088090304c2404201c2c1c41c00056004130b02c0b03940f048403019591044071410703215080d0121001016800101e07640c1c2c800e50b8201c0b26041e04004020030242c40f4440714659103038004100d05100000042a005500c072041c3c8090740c40020810401e0742c103000300380710340d800250b9912940c13110104590710306407a50001c9100c00102c81e54440600c3c410343c00c10341c0400c444644c0d0524281078482c94a804900d40929181001015143d0383c90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 490429019 1250 490427769 490427779
    0x6030d09060c0303472706030319030218091009020a020102070510050628051c050a140601080304030b01230d03020a0204110c100c090f0b09030607020106080607030c030b 75
    0x110980488081d031203140c8051101d41548901983c174001c000821082c07680760304451600108008036000030a03d03982e031180018043e00e18240c0150b241c2c150040e81c01c58601d0101c0d6001c60f50910307504000140c00d1141400740c600e01401d003861204c244019049100e04000242c0004021410f180f007174054424060340241221048440c80c0c500a001d0001150007501649101e000860040138810509004419040500407101e06150510101d851180c0480c070355058040d0520b030014001300080d03080940500780d414403442d202d410310780c242501039120160982c8240002c0c4080390880d850b55046400d0001c03ca2400e800080004c00f1079518201c0065100b50b00e001c000040c0743d00842c1d0074034064400c40d070810584c07540c03602d203c01500905c01d503a060342d803103032040e07030326840c0d05a1240640e4550b9003007001c2e03d00da44580103000d25482e504140110840410a444507060820849070081c03800e0009011140c01d200342299500001048582003603107032481220386030301a03440b6a11104000d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 490430269 1250 490429019 490429091
    0x9051311041b1205280b0103060b0708090108090624030c040501031b0515040e062103040302090a18082b06060e0409030e0f04020d050a0506030d09060c0303 69
    0x140143c10704540100b0200514101800500d030400810070b516045482424010803640c14910384000901c80d580b800d5060658898000c94071036041d001400c65144601c182e2555107448400040000c070014240740440d40c000070a100082d144018210619041e52440500d040151740c0040c0c40c0c48540803038a50800c0ca0305001009002181440d406054013480a011a240e40c82c4140190b6034068201010005401e110034050844403d010507040a4010081e032090040c102e6039802c03000114850a42903400002c0c10402c5040c00540b440e84150000010000b8051045040280c031541a8000308002c00c00078002085035010603072407200b0300401c43e200c4440101c20300701d00001d00c92402188041022030f09000118900340c0034020700141c1c0b664400104d411800b0038031100d180d00840159000c1d80a0040f5004a4150702c5181e1092981d903102050600b45002403605281080c1c10500400c40c40031014803150b07401001e41407003160f052500250a10400c0d000c0311080036030301c0d080d50442001d10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 490431519 1250 490430269 490430321
    0x19020717070305150103050312090c041e06090504120f020a05190b060316060f0905061303260f0307090305010e0a02150c060c070204140f0f010905131104 68
    0x207008000e403031041c0112101d05400b98481c2951500912000b850ba504c01c0107181129421140c0d1550884020800c491650b8520f00c00102a0380003102c200310401810ba440c4020b10503640502001800c009c0d500f040f45080c56196084411204880e0300140011001107000e80e40c420007807100705c150040d09850088411110398561080d01c44c9080d0744254244020801914010500300403042e0603039080351809151034819149c07500000b041e2400c2c080c81002c00116502d6010082002864044801c0182411460300340e41c00c900000381300401c14004039180c19035216080881e512301c001c0c3d58a0070340740c0c0c2d00e04008a95101440c1c00003815542882c40e00d020f070010002c0d03d00d040d41c1c8203c03180442d140341d0b4081d03154a8081c00c20103500c20351290340494901c03000f1000500f01180003900108010104030200a070206d0190758441000c003c0308200b000c607040a103503103405449000014492400d091000415950401c400a01148070400c00e00d0000d54480d40166854005060080003034030b990 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 490432769 1250 490431519 490431523
    0x1020304060614100809030f04060203030f0702010c1b06020702060c0c03010515030706080901020d1407090b090a1809120201021c06030203060103080703050f1b010b100519020717 79
    0x36541101c100d030621001140c10040c0c50740c591407aa0004e000511001c642e01000c9600c0c10b006488200d080c00100601c01443d030340c181c010006003409030015644c80c2410002c000b6240070051101d011a40b414074002c0b1100e074040a4280341d0444458401900c0c4002d05080f4002e00c10075400035072104c13000540a0352480003062000003403034214004c021640d2424500b082807500103200981c1a000704400f40301c4a402110440d4001c40a10700040c00c5c01e1480d5013800c2103500c00243c070404400c2800c20840d440350700c210307900050306a044105040c0300c1c01101140d5048850300070340416101003054803204010a40c007075151581c015810056200071202c0280c000d520110814000d40003540809030800b46902400d4220b0385d000e002011283e10315142e4003143c1d08142d10803030400c0010007055100081d01009402031510704e20301c0120f0003802080d081d00b1079000342d0000f405501c403d08900f11982d0440c0540d0484607242c1c40e2000842c900100883c01d040341ca03000802e01914003155403101d2000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 490434019 1250 490432769 490432771
    0x7060906021509060109020d020c060f1006141206030f0604060b04150f060e1f0f17190b06040306060b090307060207151b050f010e01051506040b0304020604030f05010203 75
    0x26001e0715000d1480303290216242c60200d40662443c1e2105004002d8440e0320b500801081c0c00c3c580300181170218600301641024030507607940050114020910059051801030320009000d14180700404030701c5400060840d00559015042c000d0a440002c1d422303840900000039140d605078165102c03881c1034035054000b8040220302134000e030310b06440001101c1701100c4401c2540c0c2202c507030f036545a1800344200d590b174140072140c5800c82d1180100d1000c01e001e103002803e41c07129503240c8200d4094440c0d001080d06001e01e107106112407010043c407051110020210380700020506020410090350800300760f262050b60302c0105190314088000540101902c0a410800001c8050301c04007030307649004903990101da0080034003c44400d0f0030714000d940600c0d251045400d44002080e140e4000340c840b14100750140500c0308941e515403102c004180001e06c60340c1c0d0b00401014901019402c210003040d551700941c06107041e11880080400d00f03643d01c1038192070045500842d091424038040c68100d0203900 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 490435269 1250 490434019 490434029
    0x40312091a0703020309150f071104150509130222020d0b060a0801140406031e0302250e0a06050916020c0d0b0606070f0b07022d031b03040503070609 66
    0x4448690894600060411640030b1609903000314180500301c0c00b00701c50000c40250101c0200780402c46100c40440041c00b6224171030098056602e0004c1d900140005c3e81c1242207401c0350038003d000c0500c044e0342c40d07080040d00021180041006013000f44040303032007003179880001c0030400c205050910103500306800905041a43c0101400010300780024004240a4400300501003085800103015100d0030b40d18031002d0308d40040000c01c102d035a030b84490b4805040d04000c03540b001140c030300c3c0d0390516404003c0c550445110658a4140013042c80e1310a4070040e00c3c2c014500134852007008100044516005000a490018900c0e4001e08208104000000400800c10301602543c09041010300d411023604801c15040002c82d421640c1d60f00070400395600c603910845414440c140d500000c41c11404425202e420107400405510079004000c4c0e14414180301991501681c01019103541d010210a495041c141031620727444800c00a221281140540d800058144c814048001344095001c40383d001216 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 490436519 1250 490435269 490435289
    0x108010c0e0d0302030a08040f020d080d051302100e0102010e15040c0f05010801170322050a050d051002030403210c030c030504020d0308221a070206041a06010504031209 75
    0x14030300c103050020502d46180042d0140c0c02c18405281c840f0700400086078018880ca841452541d50340d40040d41a1242c0003050f140c0c440c0100700c0154849042c81070f907070030460b004034500a035121503001440f81c0ccc90400c500000c000300f01c0300150b0749034004d411000b00a0fa0080a44080010070848500c071101c2c200e0b4191003504010f980025601c5254907440e0075180182e480c12081e030f082c900602d64000c0402554801c603c810000b1007480c00c0941c001e21707003440d850b20900f12480d15060411078072a180781c020900c1101da01441400142c800520411441c480000140e103940c1d490505680a130b911108a954a00c400040c1c0401c0500c41d501199035010365032001c0100341000e00080781280c5040317034025080740e1501000e101181c01009000e510141c1041f0401d070703003004c00e00140e040d942c1c0c00f02c0456007031810151003500c401c00742801c1d83c0d1021644c0f000f00707518a001e8440c12110680e42c2d80e07000720b00c186007000c0382c4075912038412a0065038004607607a448156010005008107414400c144040d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 490437769 1250 490436519 490436537
    0x60f02371e032604030503060612070f021216060e2107060c0311120406020d060b07060c0512130f0b0f060306091c031a030a0b0f0c0715091103060108010c 68
    0x2441400c4900010f990303c1070800300c580d54555040c0d64903171010789240c2c0d10550620042c1408a50042e00d244103004a540e4103c0d00481240040d18098090444854041c01403040030180d80d11406001240c0750414000304104141072505424101e09030200011550500716240c03603600c030480245603513071160400700400244d4035001c90848080c14440c0f4034401082141296001b51186020f400a006400042c40c00680b01002c1080f01d01e42e174028111180d020500c007050145900c240c41a0102d181426894484010380080b0003034002046281a6044601000284480b00510b03a516540c401052003031410b10307036400c1e111040c0440b601c0d4030921804d00000d441c0c13080810303007955001c5407000b41380c4d152000304000d501034906000100413003c840480b424481d038042240e002510701441c521184d50618010100750604010540b0310081c0c020810000050821400c07180742c0da0a41c540004c1113085440d0400c145900310807160361600c1424008109100190301034059021951284542 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 490439019 1250 490437769 490437797
    0xa0b06040c050702061809010f0f2301180b1233010c020d02190e01140f01030f0f051008010617030306040902120a030504060f02371e03 60
    0x191560858070764006a800d0100e4070041c28003130007034404034203034410500d4034003203442c003042c1628800d0740b041d01c441040180030000144440c2c00390700602011a0054440300005106d04400e9840321091030422906031111441494600b103114040e03c0080800c60b61400c3d504010304050000780c4e201403005000e1646007442c50b9604140d5928600d2011400c0340d42c014820043d10300404101050360411801070310403006a881115100000c5400b0350300e40c1c030703080c101a40c0c62a07054058100c4427580303410314031703131003055030340421103880d180c02480d020500ba610046100084c0040d100b02090250625042c0300d040d05500c007518059074a403800030071141c1d5803031103070240c07010700e032880802241c2082000c40d00340c2c00d2541141040d1381c0050078407181c181b00101120702e016807070301007540042c80c003050070300565a0103400c0002d900d89600c000d120503a10192490300000164800d040600038070000144c42890344070340030701c040fa04088904c032448540ba8184d40480a100005c4001440040204403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 490440269 1250 490439019 490439021
    0x9020a0f020109230f070806041e0c09020d02040b161103161503021902032512110c0607080904150e0c0307020109060c021609020315010503150307080a0b0604 70
    0xc4410340288442e40740c85804945100f00c0410000c42d6200c0380100c02c5c049211081c200111001480b4107402003049182c1402c16010440c030f1111b0300440081028603070004150782c1c40c81d08044e5900240b00580e11615508000000c1c451980700000c6050080344180c040c400203900901c0050041841d440d190483c5000c1644424000365107204640e6450420b12086038500325031859501a41801880e201d8003164a090004000c1030503001a032000802c0f440c1c08400b013080540c1d842a51b41742500e080c00d280e03640c003020721902c43c1ea0010000616043c2001c5107040165504d07260016150310f07030781e04540c01e00107100d90065511078012800c0290b080f0641c588072101404940702000392100f181c032845460301403940041c05c01e00441d134881c026400032405603c0341c0110b6219a030028003001c0c5ca00c8010380c005846076803081c0707001407042c01002071511510400240707080d02440d00658a0b55484442007078000c041056541601c04c0e0300021400e042c00181d0011814007503080d9100750750329402040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 490441519 1250 490440269 490440281
    0x9060a200105010821120c0c0f160603020702040e060c04080c18041e080c070603110c0a0b090703021503070206150a05040b1f02250f050906011205042d0b1803040f09020a0f0201 78
    0x100ad104d8880c104116440303503001d0307c0c190344010700c0480d001c1c0c1078031035140c030300380e42518901c003018400034003084220420840a21000c03416952402c640081c2c0304880704007000280301811504038120416581c0c503129192a00442e030000b55692035080b4649051341c2e486403400f036100803d1034022103c0d07025005034291000742d200c100c000c0c0b240b2101640d400c480c1c0c00d80902100100d20a4040100040e940c903d0f486c0060480103d11075220b10300424024900b500103400081504c141f16051001e540310102440103803001070324007084a5038480040751080b0702e10081c0202800c8045407804003d580480c4420a8001c100ca112100905a200c0075580480714450035150141d1040c00b04260b04001e202c050784540141000040c0c0d00c1e40d0381103681501e108480803140c10758942240000200d8100300083c049040e80701000d6034041076510b041c0365031b5000e40181074a200104944c10081da0800c100d40142802c0010241603030759480810740a03420030760050300404c0744050030301d540c103105222320 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 490442769 1250 490441519 490441543
    0x10b0a0312090f0807030813090501090b10030506131808070609020f1525051b010f0512060609030a1401050f0c0315010e0609060a200105010821120c0c0f 68
    0x501180c6240d42d0b02c0347c1c1c4c20351110b154030500107401e03c0c00041905035840341074024211440045204079010081161404c1c10080c01410b144c82c081c2400400e8481e907044042e8049108000581e4500c05a240300411580d001e0080c003507000010352000b0401190042c9440d03620946104441c07850401c1001100b45001840f448084424070041c0702c8841244401030224607468400030008501d502c56038140341e099494440c0d00750440300042c6007075901c86400d4902e12130a142a9013014102148410030760f02c05001d09214000c08100c00700143c0c0c0c1400550300706540000d406403c07402d02014140644011a07812128101500001e051041110200ea1060000011601c011541c40c0d0054550f4421144441d4220000f8003000c946502c03494001c1160305402c2d100c000381d02045100300450751406400c0103449034148030041041c84c0000565940e02400d6160b007001a006003061100701d03004003886d130355144800c64248824100004001d040104072402512031482d0303e01030060703441e00d0100711 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 490444019 1250 490442769 490442773
    0x18060902090f041e030917030a02151b221701050a090f0201112104210f0201050a110d09030209060d020f13060306050a050108160f03080903010b0a0312090f08 70
    0x520004113090180040aa030300c0b030704003142d95607107400e102c60030010304104c181540e5200049510b1090f4040008180b040030f015503508051905901e0f0100e01c4000c0ba410914800011416a101c503620081000041e44180d05d400c0e6003030703640d1074003140d00709010805074815464031012a00d00155400b070808181e8201e00b680d1b640e186103900440d0b5104240d42898254042e000350a82101802c9046441d81028042ea0035201e5040800100c00004800300207091050303524920320000d03d02d205c0001502e41c0900300151921124501918282c1110303a00e003045002c0d4442501405400030440d800340d9000b691009010b035100070a0141d00364217030300d0180d0b12212540748a0054a0000c83d44411100c100c0b0300801c0066890b40c0c0c00082d50300980741c40006580f6400140510303803040026004010035404c10b0102140750004040c1850312a00016084d9080040e409802e500d0035000000080c0002d41241d119130b68034200b2040b4090501e0050b000030380c0070700000958980c3e04c06100c040e40d02c1400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 490445269 1250 490444019 490444043
    0xf0f0c1c09140108131e03050306120321060307030c15030617060a2c010c1e0807080408040b131a040f0b0c160b070b070527010318060902090f04 64
    0x50798071798020028411520380f0211841040c8400d06012121030084c400e80f64103460f81030410400c44400810300c611840c0e41d04c1480070720070140f07030041e1250310503012000c14009074540c140440c1c1071488942002c0d01e140549840052180c41c004a074514003c05990308010041c0c640245192080b80002d100d0403d030303c17201c08522402c07290703840240d4600c2400703000030f5010079070441190070340360101801c0d4072a5581d480710b02d00ea0303800c038114124038811b445d9040518881c41101414201002e0302820810225400040400401c94102c6021b4400c1c01300894884001c021490400445406022103074403010a401b0140744505096174160740050700c038030010f02d05141a60ba030603004000014014820948010400e1001c800303004007030000341864a64500c814140074a8400010344205d04118040013240d520003641850031440d110811040d03400c0c070034290f0040f0094075440d415a18503103002843d490800c4500d0380320400c00c42c401d0f0b8061015a95074043c1d803888480844000e0700d4411104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 490446519 1250 490445269 490445281
    0x80114090702100f050a050a050906131b14010311040f030209150a0303021b010f090b1308061302040605060c030a110a0609061d0d050f0f0c1c09140108 67
    0xc01030a900010302d1044403c0d443c801d903a40c2c0195015000e03d00046a560310500502c404280155035010082d2039060005050559525580c2c00000f0071000c224002c2c04281400c2042640c1c02070b82c440e0041070707801c28894884600580c80d20f845901031f070120385040a8111122002d0f0b0642d0102c405aa810030a1285140c0906ca8102d50007041040c1c501c0304401d001c5180d50f61a00000c000c0d5000e81d00414040c20590048a50860840d00351414403950401201c07120b90301c240c0e001c040d5880c030700142d51078951038068070340b0500c0c1ca60000c2d0998003501d000c100c4421042449041d10b03a00803241032044540c0e84061090758898160480e10726041040280a81401400e00e0310300d901e08441282d07108615a210301c401c50710301040c00c40c2e01c1a101c4250100a861243c40c0d545000166006880d04490602018000744200703145000402d40c049181811400e880080e40c48206a0806035400b5440079003001a0b008440318140c00482c6a00c140403446140c0b044105c1502101a1101c4030543c80702 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 490447769 1250 490446519 490446529
    0x206181b030109020a0b070302100621020402070f1b0504020705030a0c0807060f0207150b130b0307090614041b02030703050f2a0f21070501140414010c080114 70
    0x200c8803141c2540d00c1c0c0404400589400008400812000f41895150354a80c50000d00b40400c0401c0004c409091440c148580350a0301100c5594810140504465450a1001c20040d010301e0b00c01502107049488100203205a1903122040e03841000070003100386486800708400c0740103104001d0001e070320500490f00403078090b500c1c4004160180c0d00803420001295a50002e80d201c0150b40d04043e900440c0f41c10410488030018a41013480007410711030b040030040403c09480c0344014210905440e4002202c980d2010f2000b4000344c521131800f44030707151312000080d42400c1c4031021940658a80004590418040c900d204420441640070750310b0480740303460446198000281b40031401c4420040c1120810100803084800c1e190341d040e07009080d440c24030803420402c00c1000c116030f80d04200c0401c00051580f28600c02d068000c03503100381e01c3d400b042c1480d60040154154805240c042c5200340b10a02025108441c2104001c60007030010340000c48080f0340c24034083c0300b4004101c41034200707010140b8007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 490449019 1250 490447769 490447813
    0x18010c0504050f0a170106091a0303090d02060412111302090d0f051f09051203100303050d1d0f0105071b03030903021005011e05030105040c152d020618 67
    0xc2c0b224070496120190441780c0c100e40754060309a60b65034142044039503064000c1080614050710003004000e0070301c0c0800c0e100c2c07003092085481101c00b080002e0466413507505482c0a4032058015160400041c80d145074610356500c0b5040c030a004248030b81d2078041c224000c03101c82200c050030480b0b0800072551508142c2001842c2162a40610b01007020202000c500400e00c68140349804551503000d401e02a08080c881d4140785a601300400c00c1101c040d4001607c0000c0765850b2510641d02d02c0c903140103800621101e010f8600201070324001da01040d8002401d14100c1c2c2442000300031980b9001c0069031294810303107110220710460004500400d000c1e510207140d41e8001e0064032104020700342030008884098001d00c12021a0440307045038001d03406240c81c003405081d13000708045d062a450300303000080c0c02d10030f03050300c480146003141c0120310075100381d031100078070740010319000243e0b1030401e01c10000340c03520340700504c07030000014000f02d042c00c40c1080813880c0c0805420b036028004194580440c2c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 490450269 1250 490449019 490449049
    0x6100c030327151a060702040f0905150a020702090105012a0b0712140a180503120117060712020d0b090c0307020105010b0705280204050f18010c050405 67
    0x2e0340d41e862150030382c4416002d451120680c5007021803402549400401c1c0070b100000111018544658100c40602180c01d03a015900120380302500c0340301501c000786c040d02021003c46a810300745500d00c410003100050000c808a00c0301228401caa035180341010807401000c0700a0761000302280100100d5000700643c0725501c030300b80c0802200001100000c00c40750002003085807104a041c041040c01580318603140e0403850744650034003050104001c200c210f0304018002c01c0c0c5030382d59036042e401d140d0f070701c0481480c8165211094989030005103a81c81c4c05600d0921420300941c0a102c010381031840701181c0c143c071031206620788034622600c2c091203800a4016021480c9495600c0f16a40381d1566620700491040130f280000c9966850704010090a40d00c042e44080d202c14014000f402c00640c010407500801c0d5103030400c40140c0405280403210490716814040e4020346480700344000080960810b6218001c001c1c9050811410182c0540c200d421003614400065414030050040b49070440c14035400398 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 490451519 1250 490450269 490450271
    0x30c020405190c0807030b1804322a060d0b030c121b01020f060c071a010b180907091403010603060c08070306051807030e0f0f070509060906100c0303 66
    0x1c00c40251040450f003100780d480d00410800000c001c50340d50b00d070080e050700c00802c1c1c070041c0c03c0042c2c1d0b050b42101c282c400307040101307408020040c030717405002c5030000b480c41904405104030005241d115060b4681002c00b015504030100c0d1009000e003201a00305441d00e054024241e00d150000511040c001480c901b010340340d00d4002d07540004800d0f552050442840f002020140500062000c15070070b8820898150b2030564000e00d0010084c4074010035983e1b401030950410542c0c03602e8518010620014a540c90403428050600105421003600b026005000100403610b03003912080c1c0c100102e9030700488402d00000c0340740605102d6103210205203485c0400282c000b141142d2640d581000f0384020031552000100000b040118460741070013200e0042106483e081071045000f031003000801ea000700280c05140e2901c03c0c10700314240412a1404c03961551040e03440c1142e1820116450b41e0040c46018404d800c2c180200320107140020510303001d0b50707000b8503441b040500c030041510500e0b2014001c1c1c082c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 490452769 1250 490451519 490451551
    0x80a0e0f040e0d090801090b220204051003030809070e01180605090403030213060306030f0b04050f060106031b020102090a090507020a0f05010603030914030a030e0a03060f06080f0a030c020405 85
    0x294030349000342401c075030490001d403d2010100d00c0060084103107500c500040e030f040214010208000094298202a45004c07031210403c0040203200041401e520081d00a40740104000300380e540da000c00c0040c0e0f032099540c2c840540b00c00c081d05955100c0340c040c12b80303240c83d210010800840c03c000c1c403c92401d501c0801050903956440058101c850803541078010a0f000640080340e11050407910003d8906800d0400a81c1e00719140c00307503203580b00d940c002c1ca00c20001c00401c0610000f00101f91400c21040101e03803c960710b075003000313001d0700c20f180307545904007440c00b2040040c41c0107000381c5030700060103082c070b04026203000c1d401d2000e088050140300c01e6028107a001d40102e0900005110003501800003c59050301e0341c41c00601701c41990784440805070461402e2040e0341d60110310000c25580503e400d00f081c0c0301c0c40300007550b40a400d0b44002d140c14500040780c0b2102c1c200350840e2080301c1c3d80da402c0c0c600a0100c8941c0c2903c408070844020009005410050014a0694031035038000002207546050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 490454019 1250 490452769 490452799
    0xf0615030a05120c0c0a1d04110918060106030b1c032c010216142b050c0906060304030512070e04060311031006181109040213060f0c080a0e 62
    0x1c0010802d58443d001c1000911050f091000700310f03110300403005481441509261591041c0c20705c4507400d46c0303a0703821140000b1409001c8190b52148440d68000c100000a0514010180340f1800c4522903103840e004003000010210701030310944900e207030041c0150403140e2007100c103880100c400400840c02d00280b90300d28901821480c01c03503817584000f00110081400c504001928200303601803c1300700407100584c20301c111190018414034890050b9040c2042c4068111003401c5c03d07070f8100c0c00c01161182244e50005006001400b21140c0005a400c00301c29165a01071001710700c0110742c09404500704010100f101d07500301c0a0a40d0100062400d4040c01e40c800001800b503455540c82500e090035100c4142c035440c03400340007020403584e00442c2000a01e10b03002c0d1200c02c03e281c011148500c95640c05400c48844942c408550364880000d0045641c0c2d070038504003980000c03142c040e01000804071004021024006c2400d03044141c2c0041c08241006001038048038440c0d03240b008113400450f034440c8110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 490455269 1250 490454019 490454023
    0xa0e060d050f040b0a020414010f020f10063f0303180b0a150612180c09020417010c0c060b01020a120207140a03170708040312090e090f0615030a05 65
    0x100900c14116035400300e0400c2e0804900990029159000b11031041204200c08c8001018074803501f5020308040f04442139107030b0260704140110100041c2801071204408c0402b50640c0213000f91480300b065281c10702070f0992140d0f50a260007985500790780150219000c001d5403000010300300f900c01e2602107540013208007001518101800c04403150b090703070b405000700581c007406420035000c00d00c0c0180308543e28190b0010300003101a0101c1240d656520141d40802d40421004501741e6040b03110107120603500da1112000350b00c288650b548040e910a03c044c60342406000f0520000c40307507501c0d0042d000d05a224140140903489031141980714a06004000450300c038400d00040da2281c01600300b080c0f0388840261003112070f01010744110202a024400030309030320102c0c081420360402554807a40d2500d0000c00c54400d41e0405081c020141300c548050030b034440d640e04181d0340c50940408040c2c449036081e5a4900c00e48200e071302c0ca50021400100300502d00c010070030008138000c0071680c80c4a0303103444041c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 490456519 1250 490455269 490455271
    0x903070503071a0106030902151b0714190f03121e08070324090507022104030614040b040b060303090a170d1110020a05041d0402090a0e030a0e060d05 66
    0x40e000b1803012003440c0a03003e070000450050000c0e007000d00c059071040e07000984081e80c600380890398000c0420801381c100c3c400c000311013001c01900102c40d00151203401c01c0e810324002c26001845030790203000800400000d110943c04460305113800e0f0500c40d0465981104029090001c0c5040040f51144911651000940002608000d80b94220682080d06005042d13403107400c180341100010115041d45085500d8080c0111000d43c02c0000321034039280c60072810000c0c003801011500d004062075901d00e084020081040324400d40d000c02c492a011300d41403140a50403280500f5110300303030300000d01068030080303181e41c0070200031300b0303246413981104c0020900c50440e04188405860280c0011030100200b00320041e02d0a2400d18869003580c200b40b05a44e546016440c2640342d03008078941c0c8140340180309481c007610000542401700025042d05540e00c20013140e090303100301c48000c04100168101d228140305101d100003d90302e1b101c0032540903159503140ea4686078210504120003419a40305219003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 490457769 1250 490456519 490456523
    0x180825231c06050402041a0105070b09070803040303050a081b0901050706060b040906030501110304210e0a1502060a06080601060c0c0503120a110d020c13020706050c0d14040812090307050307 84
    0xf2281000d00602088901151110101743c41a4981c246540c3e04441621342c074a074800300d100410f580300c102c990700744810b50b402940648400300300403040540080290400c0c241580d102040703a610503601401400d504045070440200c10841104954842c0703005050040c01218042090b030303034a0b00b00100c01d50040e4444400250f5410050003000000e0003150740042442e0000c41c15414552540c0013841100c19840000180d24041800454000c40d07506000d424000c1446030456070750000a00c0c149103554440d4018001d040005a0358907062290070140c0d088a401800c0a0307003400d00c16264004828403d5842900c40ca0001030981e40801055000d0340a070300d401130300c8400f0004042c00c0c80e03640e07100c484110380140180e501c40b50360008801d100601e003256850b40c00c6a90581000007407050b0b841c0540200c0c06c0008001c44204188020100040440d008110805416045e1b0950701e4007910300030701d5a24100b00c200d8a2032518100c1c0e58200004070282c907c0d0486958449140d0791143c85c003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 490459019 1250 490457769 490457771
    0x70c0605220c051e06180d080706060314240907090e030403021503010e0403050d0b0409050105090c06130504050c1b0a0b1006021507180825231c06 65
    0x14851403c12800b0320040a00c0320300c0d42c410110f403004c005801c038002c0c51176412640e059541501d03c1561001280b20526400c00f00351b07a903400090a140c406001980030a03140d1140102c04901c00100000e0b02381da4480c000000300012454142c44007142080c0030b000c40701a0310584001281a41040c40760ba942245148011aa0b5070b1070f41c03061140c40007190720301c0103044400f400100b00f6555103021682e44554945032040d43c1d0b40e076160b5464000c3c81141c0e50a5000f624006200040100550155004100200480ba003544000080107881d00c0380c11040603c28008400410881c240b9401840c0c1040c079000c1c1141c1021101d078658524031003080500780081e4045400441405501019150060084800082c40d2414900040e5039100e11300c18a0740c68482840c0081c450910440c100389200c078001205580556881c503c2c160b43d02c0c1d24034000352680303e00c142ea0003010094000e0250444034a02d544051040b610044580c3e010400f2681c40c1d000f540d00c51400285000302580d81e80d0052280b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 490460269 1250 490459019 490459043
    0x20c0f0a080d0c1218060c1505011805061c1707020d12080603030f040501050a09090f0207030809010c021f0f02030c030403030b0d08030c361206070c060522 69
    0x20030141c0303a004213400c44c007840300c0c84d0180c110441c8922890015a0000d09040a4105007882e05c4100089000d05502c042886c0030008218041003901200c2d902c01c4014041c041d980f540c0b81003203c2440741807500e0300e040c242071a00b03e002603104c408450082c803c21800700d050040c00d0300414003060009800b10b80610141178071101558205080b41d4000078181d00440c00d01c03685008400d880e11803409014180000801d0074900c0d1846482800003400b810b0206000c1e183c6207110203406504900c03403c80100d08070200184040c0014803403c03042d4006940281032440615802e0f003c5010612004c11001e902c0d040c4d10212051a40021800340c1d00482d443c954910303180c10010f01319040b111040d8803c00b038000480c070101d070150341502e41212500c0d1160780e4400070548508049105180d0301000081c143c804e50050180d0100300c40c2e0741c0c04080d68001405440c032401240c8070142265900c000c40d1000e91a1804245194031441d40818100c0c2c40c0715222800920480030f21080d600221840c2100700 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 490461519 1250 490460269 490460273
    0x30c0a0b1602130f0518060402060d1e0f0501060207060c02091b0d062c0f010605030a021c05040606122409020409110301060618330e03060708010303020c0f0a080d0c 73
    0x401c546e4071048005010b00030600f820750016440d42309070300340d151095483d805100ba000e400b101e1002e10300100b0740c000300a40d00402060001401c400d1141e4000750040c9035000442c9801082110081030380107103d028182c0d111803c0c40314694400d1440c03110550180f0003004400e08510802016045031202982c010110000741c00072840740039420344030f0901440c10311242c090030620403415100641000c940704c1d51046103420090003517020b540c1c06001400300c1c117204240b07243e100c540541e000780c80174000d003500ca4664104a684801c4010305651360b0b1004c80d0403440580c0f601425012400d000402c00c4151500040c1c140c1c1c0c3d46003030543d1901c10300d84400400c0e18003480781400820342c0e4280110b1100d6240b0301c600c41c410032481900142c4484e4500622035244480500303014120030070000c14019040303d002004035284400a50291046601151040d40200741040c100c3e649503000b00002d1a03d10140121306d242c1e01e403103a070083d51410010a0000c001d204030b00a0344107130341e81e000c0c05010354 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 490462769 1250 490461519 490461541
    0xa0f0e01061715030f0d200f030403030c30170108070b030901020d06080d090608010e0103080912071e12020109031b150e030c0a0b1602130f05 63
    0x1a07100405210b0002c464544001d40c841010340d2041c2c1c401e038100040070840010038100f11018400b0000f900500d03201c025015008003403c200b01a41c0d4040011144a0403a542d669000030b50802940d070b03105200c02c00002c0e00c65010209083d2243e0101048441c403c00114400c09400e5034080215000c010a21442c43d0b10081403040501140351103885945040c0310244c035502c9600130307005101c10000c005280c501c2c0940441d2100c0b45102800c010f051f5684034140d440743c00d00603032840042c1030b0b10700010b000340c421284a41a5000d6145500705a461540e0380340581e0b001e0707131100d504072010440c003540c202c6050103040000d10302040f42070040b030701d0f03840c00502c42c442c1a00106d040100c620b42e10809030b644941d0400c283e0340c0c044804406403546030103240c5205103079807102915450405100c447c0300d03800303101041c42c0c0005808903850720b5190010015203c1c0c40340108544150180804070401003011100c8150a0000d002c02103c500c909240310150354810100740d0409407200c06110490300b103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 490464019 1250 490462769 490462771
    0xf03180f09040c120809060301170706050c031603120e07050109080105010b0304110a1a04030201030c08090c01120f020f07140a051c031407020a060c02030903030405130b0a0f0e 78
    0x204440d08810342c500303551811500a01401074a030102e9802c5040c10801103e1400c071810301a004120580702d603503c2000a46511003840076651074001c0007400180785005000351502c25107044040c42c2455192006800c0000206500b80d0070001c02d50ba07000e0b203a0a10348200a0554524005400d4280c141000580031341090360000c14a40e240070010020500ca0500783c940140c4d0020982c40003200c000000707050100b41c0c0d0800c41a9608551a40b02909221070051040b40e101703803000d00154441c0312003560304480884400c04aa00060001400c0358400c0f1002118082c0080d07000a403d80170801607800c903000b4503009280303c08009944000d01c80c20103644140c90078004010700c1100c0c2d03d9a03816484d91002d40105c400242041101e21285000c2d03040000c200c0d00e00b80070b001a900d004a002543d070001c98405641c05480d040f241d0101a20101c2200d0b1881c0d0054011441d042c6090309000030f40b440f20204442d01640c0c1c51011940380d0314818103070010900306070407024403401c2c5011002c20080c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 490465269 1250 490464019 490464049
    0x60904020a08072c091509090a050d0504121b090204120c170d14210708010e0c07080d06080607090e0109050415021b030a02030c16260f0318 62
    0xc140d5050780d00003144600b07144441d072065820703038a41c0d00d5031801c01b00c07400c20364040c045d4003001d40d1081041611000410300d030154019400c41f45e040b10185c0341902c0c5807107940580078644020100c0e0b00049001c1c0081d24290700d20415078024520794551500c030481c1c00035040240c680000d1540441406841120840070b803160491401d00e85812030040d555801d1600701e004144a40c038044030113040b40723480a603508400c5840a0188007048000c40e025181d90840310301c004a501d90002140d0004203030900d511500d40400481e26000382a1100780080d04051143d4040b56141d141c04a076200c01445001d024100380c0c0c41e0f1070b28580c180141c841911030140c00c9030315441d140c0310070400400c040440552580d00032480050b510820a4400102c26850380310000b41440002800c551044d800801070100c50301c0d900648441c0d01d0700b80c01c4c10000050702d00c240281420b88040301042202c035000351022500442c422a103d820140030074034116041064448494440f07401402228100602d170040750007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 490466519 1250 490465269 490465307
    0xa09080c06042103030f0507030b1305010b030a09020a08070e040507082a030109050d050903011d330109050a1a0a1a0708130501030b09040f030c02060904020a0807 72
    0x203801e000c11400b01021166520480c0c106100503481032500943c011b0400e050743c403109000b6407809580140191561210f400d002d0004100c5042d519140c138800e4a058a007004003807407660b202d04041e140a41402d80c1c0a9900181c801320002d0240c01c200002070003801e464078020681c0c581824a00d0a1510381d80c40250306401090210b000c4002400c6020103101400101840b501c2607100400d00402200f18003c101c0d102d61000305440320b401c50080c05058104034002d000e1240009400030940b2044c103244030f401c2e880944d0101c0c1c1441103100e51540c40040c48a0b44e512280b641c55220080340f2300781d00004007281e441c018450b04111901a0b402191140c0c1c14031003000320032002007002545030344038001c015448851035011841c0840119000e054122400c15115444171019a1400000d48122801310385801d90030030312070421460181c4541d0f0400007004660700962010713505135a4140c400c9038454010804000036036114406011420040c1d81c031f8260703134030301000003400d107140c8000740070400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 490467625 1106 490466519 490466527
    0x131a0a050901150506030a1107020d030503070f09150f12060f0810110d1109040515090c0f04180609020f0309011a0a030212120a09080c06 61
    0x404081d0020000080000d2942d1003035101c5200d800d822000520020700310070201d500030f031f0f412034008907204e1410310141d001a004800d804400c5002c120080107001d48258000d4021083c1413490910950075414598240d80c0f00c1405c8403a40100401c43c40e00960f0f03241b0554050302a62002d281c14480e40740c5070f20700c0070300e8181c050150340c0356441105004001210a4080e0706003202c80c101600f4035040001720500701400004c0b040b500007a80810084d0003a072514032489114034000b100d40c1851003004020420074420107070124107442001d104240030300302d0345000c0302c0485080428050041c4524240000901201d0744040040f51000c00c040c21000b102800135441400c40200802c00a42a105407115210a03c0404c6400100b0b4210a0005045c091484040c07040080c0840307a50f03503a01003011034a41d00440700744d80021010041004820010000070002420031540c207410 = true := by decide +kernel

theorem cover : BRFrame.Cov 490287769 490467625 := by
  have h0 := BRFrame.cov_init 490287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 490287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 490287769 ≤ n) (h2 : n < 490467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
