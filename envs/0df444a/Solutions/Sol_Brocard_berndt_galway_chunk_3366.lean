-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3366
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:27:01.653495+00:00
-- url     : https://prove2.me/submissions/16c33d15-3bb1-4d7a-98ae-425190b168b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 605215827 ≤ n < 605395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 605217077 1250 605215827 605215847
    0x90e090102071e11032116050f011a010306050303040e090c060c070f05060a08061003020f0a051b03030705040902070c0510080a06080c030c2707180e040f150b060a 72
    0x213400282c10400740050801040e0418200d0500c00100316000680c01100c250f90448612410901040741c1800c020800c104440303140b01ca2345400010700c0b501c0900346c0003002401c070510581410b00b4103000300000c2c1c80000854046035900c510051a54a07a070304d015051002ea024480d42c03100380410254208a404074100d1704075a48500050300c583d5032a41408881e025540320382000c121648005802d03800c004c2e40840c030045d560701d0010700e442564400b01c0c0c610741281c007618000603000318bd403401c0f540301d001c003020444824100071411490660001841c5124500070140c809402041a0b8100803141d16000007901d0000c042c807c200100388402840510101c1c2c001040505001c00010440d80100b10140c0c1140c001e40034010141c0800c0500c4500c072622400e2440c10031580c405404000200030324039004079000d540d442083e07441d02030308400d02e54140d0060800c08100500b400009050031103200040c0340d00003090031540220481031f40042000c1d40c055504000c00044540907641d110300030030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 605218327 1250 605217077 605217083
    0x20415020706081e040f0b071107120206031605090a09091a010f051207090c0801260a110409061119031a01031d07090c1b03090e090102071e 62
    0x2042165035041c21152800d0a546025604500340540f4813080d001d00e40c1d076980240102540040c122a90751080d0082101f220140005484074110810041051110600514202410880e0350505800040d007a00c0046c00005840d140f100321190b41c0e5000304155444440010140b03040c503640c42c142c500242210704821030710303028200b881034814051401454180d82011200e6903066042c60144041324600300f000840c1c1d0321940f9400102c007900c5005a0610201d40d6480c0705035075150a1600d44d42d60001d0340c41403c0c03000e91030348080c030081002039100d44107500000d11344188135800c03012030001c5c0f0614001900700741c1021038400c072002c410f9000703020301090075100c52408001800c2c100c044030040301c1760620303406c41c420301002a584281c0065600904401030a2101000401c03158a8810541d1041e035029440703154019442e0740207840f03001c109681b1a1821400b40c029039006101401e20301411214184450200310070b207a0960540d2402a0310031015010324a80c04d060402500d0304600c11 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 605219577 1250 605218327 605218333
    0x1b06060f0f0e16050a050903010e0109030e061e071e032c010c140c120709060f0506070311010f0f061e1511120f070615050607020910030602041502 65
    0x38645038035401c2c0c522491043c1044800b10b600103408452661100b160350701086000d100c4111150390a101d0400545516000040e50f00d1091502900e85420140001e02c10402031000c442c411007031a0110a00102e1101c12a9444000e8036049008401c0e51035107030160407081038504101034000c0c00304d5012040c001403c1d0300d16403255141200d66105c42c2d1a80340028003c3c04a00e00041c40d41e10455034841c2ca14094485290014000c130390524503c1d03c0d203c290b0b40c007400b4100168605407040034090140c2d00c070280e40b441c0c185400b041d0588a102c80050800100c12910802c0c19001c0d4045501500044d800b030144441d2011114082e11b1103000300c90300b210f5072081071228011008818001c41b400d0b00c6d50f14003c070041c0c0d001528142072007d8003500038041c844503115440c2070000144101c00440403681e40b603464a061180407240c20300c095048807034811005001c140d4608050300e03456039044496807a560795158050300f480d0a51760004116134000f03d004074280014400b0034003618a250b080b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 605220827 1250 605219577 605219579
    0x5031306082401170a0b2d040204120b13150606030e06011208070c0b0307120b150405060f090a09060305061302061602042009010201180b071b06060f0f 67
    0x3282c4001c20040d5840c1c041440134011040550ba0b103030949130301c17540a40d40000e00d4a4801c01184004484503402d03a03488012800c142c51600302000d80c541c2d80304065804601723040c2004074016101c000c80401901030704032040002c100e04820741c15210081e5201c21140b403031003c0d01040300003901e124081c00000c2800c000b4a20500d0a000030403d04851040010b49107007002030f182c40d02c441d0300c400380949105604007804581000003500030f50007000e00d5135801c80680c12000c02401225100b2144a00ca50341c51000c1c122419115011350741596412207440d9610b8801840c450060b11800e80c40030380040d030090001401c0c070340540c0a0f03801c490052050b21500d039290f07144021482d50307183e4001d40c0f00d6400d10501e2820900d072440a502984003410004512682401c11842c0302802400d032001703110002440714031035a081c040c2c4441810f504486c449009041d90310003000403070040c802d1040040c901c0700314014a034141ea24881d11030300500100300b042e40703881034180583e41d40e000e04084080a6a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 605222077 1250 605220827 605220871
    0x127050a15060809071a0307050717070309170c0a17010e07080c01020f0609060c0f12040c03020301110724091b080c0d02060a03050c131d09010c08130503130608 71
    0x44030121b0040c007000d1803466a6200c802c0c2d440750807409058840c4128040f0040d030383d60a0038001c2210a000e902e0301590145000070504e0a2071560381281240d0b0080b2402c1038454a805005806849042000c0030f07155001054560040240c10900e14507803050400004900c040814454503030582039003520382c07040b14843d0003942c840c02610301030340319030020000a550400d1400980014480d8403482e030b1034500484075204c4902e105440a83d020312800d202002146030910030122403c8680303480e141408a9601c0d07103140d581c01101c40440324038640c03040003003d01065000c030030140d912160888a440ca031604d14000c14403107003c0c141c000d00c00c030072850360180f401c0c008800e0b08a5000f04040e150040300e40045014000140281c10700082c14410f004e5030384032054004c0068250000349000200090100e140c100d00080d08001c0b10740d00d007002008125912a1610340e106018110406151455241680c618855041c06101c400340b81c51011949551110b030140c003c074502c0181d0030307101d02c17010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 605223327 1250 605222077 605222099
    0x30123060910060e030307150e0106081902010e030115080307113015071119081b15040807050c0111060a0c180305010c080127050a1506080907 63
    0x40c4039080103400c02c6008000c0c89118400244071030380041c0c280da08004031550340a1500b40000c2c00d10003420344070b204009190200b442400c0007400780c50010701490000580c0c0865042e21240064100f0116003520304140d2000d40000011100c0390190400f0f2640d1181070980703d40241504460098a20500054524043c0b4060300e6204d1204281844903039074142e10090490084800780550152076108915102c80e488a00d200708030b180c40c1c040c1200c14020030a0304005c0c2d06142e001300282100020030110f1080c60035190103076900131440b41d200010500711490302c0c3c48406078504c9200c050f0100003c025030300d4060302c2e4607407003081184c0009da410340040d60501204846c030758032584200c00081c291000ba0b08070044a03029070508214060202c0058000e40b10641c0040da003da4440d000d1808060340300d50500d00501d10f580d9490760007078041d00c1d4168640c0c1c00715901c500b00ea4540d00402c01c00c2d0000d0b4081714501441000702c01380700d47d903040080c7c40d4140c110307400100c5000c0c1c035038006180c141ca4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 605224577 1250 605223327 605223331
    0xc0108010e0c041502210a0f05030c16032a06051812030a0b06130f0812070f020109050d0b0f06010c1e03090f06050301082b030f0b0301230609 63
    0x10440b507428282400300e44c202e103951402000d000c5124142e4101e40d02c00302040c2122010140300e0780c45d45d45a21044002c1c0003150403071043c0381003050400410003441d552405650b1704810000380c2c601409420700b01140c00700c202c000b040390810b0384170180044d001c10801015403524410301040c0280d540f9411618480f0140b41401112500030740c40c141c8500405000941d840419024005109030065000c00d0040d0030001e1902c01c0c1e001c2d101400e10208912000120080948100900202e1091101c02443e405030490081c0084c207005c2c10103045a000d030b0b20b0103000d820044c014031075103030315401c3c022054a0182c1c1c600d40c00300001408034001d03501ca80b107050840ca03008480c15565400300a84000300c4000506c00b0340c100315100e8804074101e001003080900800c041d50310b09484c0d505003d501401e140380040680c00c002d03c0c0031158a4401e0762113185601e01c003010704000030301c501008061005040214000b0703a0551810b08405401c0414100d80c580010210b1101d001d44d03542c89080c010001d0701 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 605225827 1250 605224577 605224591
    0x504020303030a0b04020421020f040b0a060c06110c10050a062304060812031005010c1502031302040f020a03060b03060a150507020402070f1a041e020613080c0108010e 74
    0x104000090710010507030031500540c98017030001450540e60320060040312100d21141e0aa42c083d00041009501c2d20b164071140c801411541000314181050010781d0a61884c851501407125004c100d40c2403020075441681a07500704c01c0160380e84da1049540d0754586081c8490019514500b00207e0403001a83c0303e0035041da00ca0a600c0e5841c8650404046150300ca02d00210703901c1a22004082100002070041c100d4034100140115282c4c18119110040f824464004030b04111008a9000c049043c401d00b085c1628a2141b0050703890b114012000802581d1290194200b030404e400700100c40616802400050361759902040307950b071510348800040c4001e0711002d500c07000300002803025a00e5090208c0c1410098100103240c800c441d80801e06a8124070015501100078116220030300c544122007103003c070100100300020b803900382e807001200c030f00706148445010940400d0100715190a0104e45c80c8180c0d552171502002d81c2d600342c280d505e02e9120b5009002500b10800011114010a0301c0ea015000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 605227077 1250 605225827 605225833
    0x6051501090b09040e01020a08060a0e060102120307021c1d0402030c0406030c090306060e01050f090702070e0603071d16050a12020f070b190e030702011707140c031c05040203 77
    0x45410300103040ca412001d10f02d50301c180da40c60000348a500900c014101f80d02c1e99280c018183c81e100040180004941d0f000c5504000d1503400c0004607039000c40d20030105001503910301d03101c3c3c487d005c0c200c3c54060079651a0352a0300c020081e148a0707680282000e034080b4020840f9038803803a6032109000503408150340030020349078140001d0100c02d0190f0030003135002100c4c6c54252465541d0f503c4403020782c1d10300e0f4013456010480200610460a0112808202c20025034003a00340b0308150400943c1c5000c94450340d00d1030031100f00802e20b542d90a2020360020075004040c0c0d441d443c02d104903030381c4075941550403030f0703101081020100c039040c0504291084100982c0314400c1031900081400060350007890010b8221304200301d0a40001d964003580d0b03020322049a403035445003203440c401000300c43c0c02c40803103001617009100b0840140e030b0013002020440d02d0070f8031140e419113400005903900002c2004400301860085554012140000046e0000030410185040b44dc010702c40780104031002510082c3d0550 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 605228327 1250 605227077 605227079
    0x20703030e060703020309031b1e0904020d170a09170a0203100507200102191d01050f16030c0b0a05100905070903050613030809060c070b040f0218040605150109 71
    0xb161450140110030f000740140ca140800140010b800e00444005907000344400310501507071070820042505061107034070102c080700450000000e03100540144002e2080405440b804200405036101001081c81c03c000070351a0804040b024103499941d014a2941c06406011072128132000070340076086a4015001c1c0181030712281b503140c081c20b4010113500034000c0100c01c8031030b10f5008104244c0030f0040c2d04001620b400301509200c00c208000d001386000c00400c020b5961100d40c0500c421415181c1c00d081017540c2c0c6807445230001c85402016400400002000085014141c102d0070807120144140c00182d91940c8030301042080b1801918111040d00c8482414483e0308545d6014a410204605284900960301da8541d4a01541254050445280c1020400c2056041040c803600006070001404013498100c403c0c1c0035030f01030150003514042c9410301040900001300c1d0030394907031038022344464255415040500d2102c841520300312030440c60000013407400314640303c140881c03c2c1e05a695030a81 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 605229577 1250 605228327 605228329
    0x5061e090a1103010303050703081501020705011209020402041202090a11190516030e2b2a0e0f060301141b040807090b030d080705090d1e050a0204060501020703030e 73
    0x42080280701071501969010b40c405403491141c0078600841c40717565401e5581c40750b0301e801801c01350003408501100d0380d0310001c1c204a07078010403400242d80c020b20384109806aa0710222002c2c019120001c0e409c5403000801140d68103503110142002402074508090300c0e1500100c000c2240c510807850307001424240103180b44042a45031039000a049898214102142510040c40503030a00300c1c11404120005c40c15a20f506040c003801c201d104100e00541081c1c2043c82000f100b80c5202c2d00010180c441d904d4010191014410343e440c48401c0c85903461303014603291641d004489000361280034411070994001402c500d014020b507070321040b0043d011030058450f03003880d0708681c0d079803805002022003d11021800c240d00b0409200200341c100000319400078480141800c0100020887c410003d01108002c00c0c1c907005011100300e0941580c4d19100d108180c1400c000e080748000b2103940c0c5075421240c41c01802400144200114004c840402c4080e03920801640e45140d00c0c40001c0100d28400e0b00c0c0491 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 605230827 1250 605229577 605229589
    0xc170f0703060b0d090314040506040e07090b0f09040b06071a040510020a02060f0a1b0c0201030b130b131b2d090603050906010506040519090c090905061e 68
    0x44200c070305000c01c1c01501c40032410030315080103400183d03041e5902050340505900a100410708840121910302e0b150400004c07418038465401143c90009400c1c0100d0380080c0b0034441c04005080107807400c2d0b101c05101e000401642e000600d4213114600344491090f492610004445500da8003403003c0000c2c00d805040b5003251180140103403500d0140c410501c04c0b1880600082c10a0556507010340681e151407440603000c0440546401d0140f860103004c0c108021108802c00401e401c84c1c148540e84031000c3c80100d016102c40e00c1c015030000d201c1020001e5003841504100c00380d85046414000d0860400002000c0701c040c1c41e00c010f20101c072580c01c50020f5010b481c91601060810394000420723424442c0108d41c0a81c89042080020b6411404000c0c1545c103105aa401040b600040d148a500d400e0015005000b00e008a074804c00f0f451040d100b0840342070600d00c0040038840d1050105190100000d030180c440c92040074106424000011641d1421041501e412611520309815180e46036082c440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 605232077 1250 605230827 605230831
    0x110910170303190e15100f150e01110c0a0906050f1008011a0405031207170301030c14180f01050103180506040f080d180c08150106050d0b0901090b040c170f 69
    0x200c140100e03a0042c0d0029910385e449803040002050441c0e80900c0d0141107421003480390320808481c111a240f0820031948041480300c40c040c01d213820781c842031407030f2001e40c100400741c1d01040e03119581c0140011440026003019044410440b001040300001106001c2207100b25911030000502a10050210b1140c080a20701e85000c03140340c0b542440c0d12180460314104c2e449425292404000c11148100310454482142000348c4905203411545581c0c0c6610903010340d4010121180a002d50a10309600d9440007091034441c0398107444141e007410f04510b0001e0307000303015150020f41880076055045200c2c0195400080d440700c014402652142c44100b18862500001c0b100c06804201c2c452006109001d1003025a030142300b6409040942e00d80300d54004071a5011084c550041101d90811790030200f9501d0454101d4180700f03503201181c00340340e40148040014a9400035240001041c0e40305194030502c5032006c180c0d81003041c1210311700140d50b0005140c00044411100d000020040380c4100c0d0714503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 605233327 1250 605232077 605232101
    0x306030b162001090f0c0f0b04080c13022116021212040807081314090402090403030914010c0905090c13150e09011404050601082211091017030319 65
    0x192481130b6135a0300082c00340804059500b154602414461501e15500080c0101210f0b08400c0c5480e1501c0c00746030311418041081da00c1601d10481c0c5161182c0980c040761003103040150a94140110381516686d0398000380d800c00f40c080d9508403480c891500010700841c4405002d00018200381c60380303503160082e10300248100d41c410418804c4600058410006c0e040c20540030088103149070030402c0300c00c2a05a55075850344125884014031002d0303100c0c1c007002c030b0300581c16140100c3e0b055924100340d11a00300c04103911940398030740001c1500e41540441d0110a8a1b0112181c012940720b09440303603403500a5112044403190015002c10591000508440c55156070b41080c1c1495584a4000b5200c0b86090340622200c58091101e16058a441d00c82c1035400700003402e10b280c40f41454a90034032201c034072071106080704194508800c140018200641c0500000402911032440c1150903030130440001e1254864240d0300c110f01070400f03600441a0317841000d18070b0351050072906501409000e005000005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 605234577 1250 605233327 605233331
    0xe0913290106170a0c080109091b0f090f0912080a0e120d0c0207060807110a050601060509030610140103020d0f06090213060201110d051e070306030b162001 69
    0x12810018a00c1410307000340996280e8155501610407101040b240003482c00005901d0481003100c0c1c0f941144c01c480c150344041800003000040791400d104008089030b8045960303800e11500181c9522581d80740350503500e40d540c0a210500c940360380035058401d0303540018920708582010100003032007804141c1d0700c41c0e070b41c0c040030611200030b41e502814a5074000c440051ba1100203001c0481c103549014220500405100900980d458820300500e243d102410420402825910344940700404000074450310ba00002030390020359640901900c554051628140a400341000141c008261001c414045541403184000d12081880044000b0343c0000b1000e170b04156940c40c1d214984505120708005400c1c0e00c1c40043c1e45c1c610021300d212481407158801c804580c1131100210703c4c0030300c9100f40c942220308031001084076100e140d030042489030800c1e05000b8421044080085407031703064000c070b4120380c01482082041e48454101d00f1458092a0580d00070030707541d000d050300f02c030280d5007902d0406c0405400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 605235827 1250 605234577 605234633
    0x10908100236010e0909210702041109041104081b13090b0105010315060e12070503100f1b050a18080a05070f0e100905070e150a0e0913 60
    0xc4801c101c12452494031115862154940741940c1214100c4e40015085130325070003d140603004035584405528141c914003912013071100c0d03041422010b90740038550080040c0402e900c06009889182c20400041344038600b00690280700c00201401c13501590041c07006441c07000150601d242c0f0040300e40c2c00480d0000b90a44a0500c07420300c61041c0070a1612410715411a94540000141076903030000d40340102c4136898904000264106491441650064900b540311081c0c03c1161410006c055100b03503014001c140251100c0704555101a0201800c1c400421030f616541d02e80749060700034540341c100824820840c88104038080d0b80d0f80003034050a921421095501c0d20788690526018110880f9542d00009043c84030040c808405c01c050f02c25804420003524101e4480125002075100d540f8103540c1e50740108410b113101e140d0203040d80e400980401491048012140d0050f8800c041c1c1f08000707000705086000e989007001409002d0710384804842d00c41a41c3da200c8120b5507007140b030b40000d07001d08041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 605237077 1250 605235827 605235877
    0x2070e0402060d051306050a02160219031b06110a020927100b1c081605030c0714040b0a2402031b060708010b12010b16020a090b0f0109081002 63
    0x40d8034481e2100104001d046002458100d05891001c8d002c012521300500101440840d0710403c80300c0d0703d070120340c1440c020301910564040b04031507800c09044001d60240050050311aa07039154120ba01564070040241000003455455402e02e94009510220100c00700f040c080c2154031050b0120003101e450b130340c03642d400c91303810786000e8400b0070b0000178036111003882080e45421903605048039150b200000e11075040d943c0c1d000985c0308403200c0c0302050900102d458140701c01001610b440d0702040d811075540588800c2d003880030010944980f40708508041c1b01604c107092100c0c0040441d2140380c1c446d071000c000321034150803803201030500340c04520061200b4291840c0c80701650749914040400307410241000341005048050507001249010810054941d100100c3c848042c112914614210340ba100413290342100350740111340c0654440d004c07220105c2d0603d40d42c0d000b0340101c0c000b1114040b0100c00074006540c42000d5204001071038101c400c2e2030248062580060491181c0c02040c4036841014503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 605238327 1250 605237077 605237081
    0x417040b030f0c3c040e0a090f050a0f14010b10050a11010f090501060f0b0720030604060e0f0a030c0602070314030c030915130f02060f1206130c02070e0402060d 71
    0x10103d007060000030031500684c10000804c2c011615031020740e45040d04041340d10780c1d10003001d04012011640d0780e41c468244280468405000d0398484103a41c07403c0400e08000f40814522003080d612002d01400c100c40b0140705120f181d41d170007070290260b0a81805000c055900f600f01800002c24006e80512802001030280304503c5400340b2032600103000d0744c1703a04040d0700711501500720760812141400240603d12a01081d41c0f0256848640740c80c3c0301d00304c03005010f0700c10b89070f02c5600d8052050034180401c010b815003203200112894000c6500c42c204902c10290340707920040014020400300c95501011410039001000454002c1c10301c10303d1500c0c1298011121f038401c4900c2104041c0c04001d10040003003d21103c3c03401e861007000d82c0300c00d042c1849402d500d482101c800404000c0c8501001c800c54461409441018090010050f2500b203803000005401900310780700c0b44102ea4881c004041240f09114141c1031202c140d000703200040c286500c00380d200d1b07800b40080c0d901103000d105009051401e4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 605239577 1250 605238327 605238367
    0x20316200f0f070605030408040e0a0b0402071101030c0806060d05040501061512050105060406050913062117040b0f0c070302130c080f06030d0e01260417040b030f0c 73
    0x74600810382c00102e41c85071420500e15802c40720030088204244804203446100782d46c1070700d840c0484202a48c4036800400b00a00c0d4803030720160090300205503c8240324000050021651007070301c044c03004ca0101201280c014000700e0381c06505c00400e20401c25036010561100394054898000080e05584a010940030408100d114400090380034501c20043c0580d409400d006090554007642082d08040d401b40c803038014142d50078054802d104540032004560740158004040ca20b019030054142400c4130310724551002d4059468018401c0d0408503020002d040f6000c8858000b030701c0d0b042c0b01c401a81042581d00005403201d252041441c0400541e03101c0c6415210080400800a40d480306201d019150502c000c200341c05810301c090401c882c2d5100440c80da400010140307030031603605510f000140c8107048403101000500d04103207565200b5140030401d0501880c003905100595814400c07000c42644100c1c000d054084005202142c601880f82d00350603000880c0e00c0e090380c20230900c0b0b10f01081039010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 605240827 1250 605239577 605239603
    0xc070816080714010c020a031d0d031d06031608130c060507030818070b0c0a0b090703050f2407120221010f0608060d020103090b040c0e0a02031620 65
    0x30000c1c0c2d240400414082c0941142100c00090050309400c90303002e0340302c480d8008041c0070b00c05000700e102840020100340c03844400008018058800c01818010941046c428507002c40c501c20f409031a145250a078241c074815aa580d41081c000f074030308181100c01010252181d20a00d03120020040010304500009016043c96540c140d01d9403010b0400500341000035044030603060b60058401d40d03105000c2000d03429642e08405259448903291a00d0b8030340f00c502c010103002d40d1512024403d0716600420241c0031240600220303000b00700c01c0007019071038841c000b4524056803080c0d201c1204858080307030401e91103e120306242c06140c9181a00b4000e90384a1900000840104520b123076001e900c1c00b0342240900b10410f549180380e810300b00040d2262101610300380c41001821318502c1103a01c070350883e003003aa5100250145c40c1c1400d00d4013a2000d0980c1c051088a07094000c0082d60807803562003960310440d202d0b1200c0403030b00751440045c0d84103290082d4859410140d18080c110600e0f080007818078400c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 605242077 1250 605240827 605240843
    0x20105190e060a1a1f0f090503060a1508031303020a15090306090c050607030e030d0e0a06050f041a0c0607080c0405040207021203040f0f080a0512030a180f110a0e0c070816 76
    0x801794500030300280407407202c8800c0c014034500038005d580340090610f500441f0340d60000346c0080c0082c0c411110888641c0021070902c80001c00707030700c002640388031041120701c284d600c1c0c1d04003a11031041c406092104880d00c000920011003c0010506640003040100c8c01104c841c8045502c590115207503503c005401c2c0c000c130304100100000c5040c1001181440342d02894281d80200d010320016890035524454042040404509001a9038180c030480380100900c84109207442e05540240802e90420300381110140103d600180c00e40b40510580c600c560181040d042c42c160900c01040001e4100c2c8200f80c0e001809400b000846200820050003e00240c40c1e022695501c0c0240d000c2d80c0c000541c014030a1600314440000004500107140c00b04180840c3c2103a499a8880141c01c0082c00030500c0303546190640d403096030a0100da000310303000141c09003404e815440b246100388281280c0e04c0c03060300e0000c41c0c4040021101c804141c0a0080f407485541c046c1e191001d85d209031512000402c6080c1c403420303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 605243327 1250 605242077 605242129
    0x5150f09030d091e050609210a0506160207050303250c2601020c1c021c1701090b0d2405091510030c15030e010c020105190e060a1a 58
    0xf186104c504429074104440d1a0840c5041401141003401070b44a664010888070700a14920b0791005510f2403588207020440e03000d00c01c03078100203a903a481911415a0b1b06100184146014400304030442aa50040c00540c61714134010400281d18407401d00b803c400b810710312224000204107481c0c180041c0300c1d089510440301c0e000400881820341d09001421785030b1040260340001280031451f0000c0500c80001d800c1c444181c1801030707007449104201c02c0c001c1641c5103110180550400c0c900395003080c031001e000300a60380310101c4000700c9512440d00340d80800100d403080300144500302907810788140b11488240d4181440c1040080d12001d80b200c640700d030405000010b001c01d9600300241d10552801350000c0c0b8070303c0c1d51550700c4034a0407400f8000c4c50f21040103824441e01e0190f0440c2a841c0643d00c000c0100c8072010000900a040540c4c164080004103212200996220b0081c0e000701c00429000d09520349440c064900102013a250380c45d8502c1074105001b01540d154807003656041d00300340c1580061 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 605244577 1250 605243327 605243339
    0x7120e010c09030b091506100201241e290c0706020708010b06041802030a020909010602010b032109061c060605120f0705160309031709040f050105150f09030d09 71
    0x2480e40208501d070a51b02c4050f5050480c20745040301a00004241c2c0c49903650005145c00300e01402071b8000d102c030f441080c003140030008800840c7c20780c11203031813901a4004584036054141007030242d1194219560803620301102c0c800003980c0c148101c40103202c046d0310780009480c10500b0401254403c10158000304010003200e1001c0c003401d02c1d40c0c541219124605828100782c05903070100d01561310040b607408400a2022603080d41102c003025002003500110750387d910402406400b150392094040c0c0640e401581c120000f42002d002204000c120181c1403403082824440c1c207410520b8003803204854401c80700820111441204083d0074030380e45441da100701c0c5d14079000f4144409843d02c115840e5420401901e25401019510144100d07155030038400b07110305040b00d0610b11034002820340f65019825481903006c0e10014a00c10700141c40500030346010a2036841120750905c50580c000d4100403403040402180750080c00c170f0006401c002c60810204001080ca041c0900e00c1c00808601c12600600130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 605245827 1250 605244577 605244593
    0x9060f050402031e0c06070b09100b090105012109052d1023010f090f140106140415050702010e030c01091e09050c0901200607120e010c0903 62
    0x1011400010a00c100e04060380465075810075069000c0002d20072955031441c4580034814820340f000024803940e1141100c0c18000d4070034009035882d1050f0301c20445980700a103070394050f01d218800002c0200d922170f8a80b0006403569003000d0f400c01d04200d05042c052019900c0ea01c103220400e4090401001701a41103641d10041940980c5d4000001003026440702c0000000141640c404900600c04524000c035100f0a245018291440500c82c03903458001060032003082503044111140c01e0020b200d0740c17520385805000c0b124400f0b06e03841c04c910298012300c00b00780901d00c000300c0c507118615000e01c2d09a44425100b10f1103010250a4005040051803105541e0b01100c040a0b41d14100c01810f180b006400001c0c0040c20345104801c4246220100c1130344c03083c10803140d48024168054144280e14000030f00c216981e2209100b18003191281000b150451403218010703401c4803000707009107507035181d00c1020358107800c886c24065041d80e10b4594285450710203014002c091541394031b130100294214a40941 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 605247077 1250 605245827 605245841
    0x304150c0804060f0504081b3c030c0612040c050402120619090204030305070204060f0609180b04090302101b0c11030a08070b1801050402011e0c050f010906 69
    0x4101900d6054408900d448044408803000c030700308400d41840c0d20b042035030a8000c55115400768001c140c92802944804821304040460480c0e8140766001c020104100041c4000c403a5031007082c071030310404a21401ea2000780700629000b02129021004080003d905521444102003840c10b60000e000c00c2041134040107020344002c5030f00394100408514860507590004224a124520051280d0040040c052400028080003042135558585a04001c2d00d160701004e0100e000d140b404200084070302d00300b00d2410030b8801954900d440246007000541076040d4074042c0c0403106a0322070213441c660780c8521805403000d00c6900600710124440c20110200c462800f052802d80140e04c1c070034001d80e0740c041d0704586016400041110584001400b1900c0c0141441c0b0040855a0010340f00c005d01020554441c4201e00d030320551003224080101d241e0a8490913540240490f030b42d911082890000e20300d9031a5200c450b40742c0700c0d82e08445034582a2078480d4041c51310740e0b0307a591f8031040000d008203401500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 605248327 1250 605247077 605247119
    0x103080d0b0d11010813050318130b09011230180e0c0a09090c031b03090c0303050c010f050103150b0d0213020a050c03210703050714030a060302030a050304 69
    0xa881c0b01c0c0a442d21041420a1040c503810003c145000802003104200c1c010211038001c1d00312911180b030822103018401e068030005110390080c00c044003001681c0d0185004844000d000c0b4139499182400302c1d045070740840300485540841c12119402440342d90b040c80f5003001d5000307035082440314412014084000d004600c0d0f207006401da5042c030161700c0405110b5080780200304010303907541014404039100c50090700305145050816000343c0a0b80d6054112080d00b07030b80090351070488070300b80c20142d04851040d000213202d4100c00c1002c00c007080c007540180019034480d200228620701d03500540070880303030242c0044501422f21a9050380d40c401c14030a03400341e45801d031442a000c0302982c0004030710440e0050200391254000821140b0310744507a0540d9400203014044a4440e03c016440c6203907207440c80c117029084041000000c19a902ca4011580201e01c030351501013620420320841d0f541c9a10003840c2942581d103c04c0c0000058070200507416096000384040d40e00e5030b0a0116001c0c0d003c58071440301c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 605249577 1250 605248327 605248339
    0x60504020c0a150b0405090f070b12071b141506030106080c0f0d0b090a05210d2d0603020f01020a0203030a0318020d080c01050703060b0a080406140103080d0b 70
    0x31400141e000940001858000e04031034201c080103030300d01011385011640d06400034181020322030541000186c0d2520040c2507030a95900644854425100d40140682e00c106244094007207031440340620401d61030701441d001c441d854100107031a424001001044400529888189840c404200c04000d658001c60f0480090050500d80441c66a0314502c210700380b8450052515194500c0e91400c941e03403000c80c2d01031041405450910034194403842c000f4015610780c00354108603580000800400440d209100c80c013141001c490a841c8402400c440840d84c0343d0b4400c41468419100700900004000006084003044490031071060102c9940d00140e06415540202d00010045c4d501005070f0303c040395039140000340318078455041680d8000d4044040c0d004411b000c811014402c0d01d8008080c9009140000d1015854040e030440441d105440780c0703080002c05120241c81d0904c9410002d42041c0074520104075400f908144000402082c1c0c01100d030088002030121060000d4000c49403280011200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 605250827 1250 605249577 605249587
    0x10050307080c042c03040e10120f020a0e16090b0405092802191704020a15030e060a060515070c090914010e0309180402030a12090801021c06050402 65
    0x301d54802c0d01103400c51103140c031040482c4681d00ca40c07800b508034510440032040380c2c0328207004240d2a0740c4280a00c010042c400c00010341c05140201a0404a4100d201d90651808468640960040601c079040346c1c0483d40c0100000c0c0355042d001ca250040c02c202840381242154038001501240203a8002c080b88031081c4030820040e03451840d06a440b4000c01d00d0b1080c014070b5980021f1644400c440751400707543c4082400340200b4070f86207141612a8040c1c03510bc40b0280008012483c031041120001e5101d0550a420700010030884041008040a81804212089041100c90034424116400d07120903580318020841c03071070700c20300c00c0c4680440c580c50030b85410782d9611000302c0b01050b4041d44100c6030b21030400e081045910403c08200e16401002000794a030460503181c0c507036210011940c0304010605030080c0001d020001c0c00e0003580d0040c001d00c00007405640b60414100d80407201014800c000c0b0001611840a00081c410308911441e03013000310202031880003c031342c12a0021f034000c1c0d1040c80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 605252077 1250 605250827 605250839
    0x10f060f09030809010c080c0114060406230f04140c030702060f10060e010504031b030209241905030a060e21090909100e03130803090a030b0907091410050307 70
    0x2140c50004c42071030110503c02c090f043c41c02c828850344e101e5510944c030b0303d100410040c034805403250094000f140c0030700c102595105420102d20022000e03000c03040c4c9072810014189800c40d0710350342401d00680040791043c0a86202a00303110100c0308004600d00000402000d9603040c0600c035886038154802211b03d08003041040035983d0f044c09142d0610100082c02942c1740c2c0501c090318005c40d44815420400034504000d0b14404000d0320089000f01c09070740100e00102c3d1451442c044503201d20034921202e401e8a000c10440c0c0c00b40004410204d281814040740c661403d11050000c0c500614010500381d01d00001149000c115250703107003880400c03401566840d2807000440e0824141241c080704580c070782d10032075414210f0300000d0030740151800780000d20054012014207100200c60070307100d00351503681d06025200d104000780b5680c0410700d43c50a20014100d20406908a080001180d03042912641718204940014040034454074203141041000c4d48902214030103018103601800555180403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 605253327 1250 605252077 605252093
    0x1a06220b0c07030210030219080901141f0b09010e01030f090b070512010806060109050d05010b040f140114150309010204120f060b0f0a0918020a03030305011a070b010302120312010f060f0903 84
    0x1052200300409d6002003044100d094000300b66100940c0440e011504040704c0f0307401d280d0201c5142204c80040c0300d00000c3c41c0d50782d002c1540d92440040e110a05410050320044009003400c1d02c507092020303505c541031004601004140e51140c60551a490355070040b01500c0858004140d003c01c0c11940100100001c59030702031041c604075441a100c1403068074081c038081d8050003929002e650402e180c84040951900290460405031044129403007040e40c0303071403c015140c00300340281d80d00040700d42003001514148000465102500400040c141030300c445069540001d210815902440081405414403070389202d42503207104200c84c028a040d401ea80400c139080c3c0c051040c4480144d423009401c0d010f003c24060080c1d03c0343e0041ca500c2c540d640368500030f0020700080c00340b03160080f0b08200d41c640d070f0103054048625040e08a0076005540c3e18544c02c2089041c0c003040050101c0c0418003102007102c05100d11607010304a0300740f00d080039504040d401801111445542020000b07150400c0003c24584 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 605254577 1250 605253327 605253367
    0x4030305030606221503061212020f071d01090b030a080a110709020c010507082509120f02030f01020f04150504080a08030702011a06220b0c070302100302 68
    0x608100303440e550790000090743c41c0a0303100c1c0742022a44001c00100316216204c80301c0251003660700c81c2c40485030509000c508880300f40c050708446100507900400072414500c407130303c034152042c4120b1388424024104681403110640c0000342c540550000c03440a02c1c0380c81e25290141c15080020818444040000781d0b6960803003034040c1107450f00140e540040c40c441c40030058190260710441d030034181c3e50f543e118002e600103900180254a443e01150301c0a21960b02117010b0520302c08d503890901c0c261540344840c0c1c62205030903404d00c1550500002c007800300203170a8012078007601ca1032440d40340fa4018076040500900b80702050b6441006240301d80130201d4140d406850300290940300d007510040c1d00796860b1042d6081180c844c410981023004108120b0001c51003030003203078001e004598a40e001c030b00300000c400003200d80c001414004400c1c60b440c503100103c401c612007131300c041e0b40c0703070307a40d1440c100075071107061280f0050300714142c184154209030036076074107a9040340340c11454081002d04d03000c150610 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 605255827 1250 605254577 605254583
    0x210207090b030a1106160812010f1d090106051c0515101710020c0d02151006050d061a0703090506040e0414030d050a0b1009060516170705060f010f030203030403 71
    0x1c00e04a02d81c8401d170a43d010342c00d544440e0810f0000c213080c516030036040400d190400d8a81130002080381c40e060003d10040740c01d44004811224a1311500202c2c0500051240540350368900002070315a0f6000892500e500610342550780e501c2890a0203810034504040060308000f040341401140003000b10f1450846110401d0400d401509c3c41d01141400c40c0e219500000e2400407078034407070409000c100c030080c0e102c5e40e408461010500c1d04c0260540042110302c490b00d03504406007001814007440c01030408800d01c2c00002403098403814452042c5400c010400000e14020441108058100140e4006418111100c50506181040246035050010b20041c80405405000c2c0c1c1810401c00640d40340d015070400901041c5440706001c4020400181003d2203054130303580750300403240241480020344240b81e444e149068008050740d902c0c0701540e14122101c0c08030020f410b0b40044111f0140232414415000b5241c9810f10440038820404182c000500b1050005400c1005a0300003044904907a8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 605257077 1250 605255827 605255843
    0x7080705011b06060e1021061a1201051504110a030b150c03070b0705090109060305060d050a060b04200904050406091b050312090312090409210207090b030a 69
    0x110b415141c620356940110051641d8107003000411902c001401c014400c07071a003000305a10303960352800e21070383c1c1a0020040511031503064800000c9a40c1e07800078100728041c140780c0031030130b1001d40c04661007004030900700503a030359114140442c4000100c0310350322407c0200c03424006000e41c11014105440359810360002c1c16565100b2030300548564544480c00da40a403411030b1507000004805441c0d6100c43e400b15050811303600020203043c0154151150900117a40b940c80b41810280140c00a0001516065100420f405220002030301004441c40c014440da001003002c500700340602003900c4182c12081040c01d8036100c001d54500c0d10506503504404100e0f8081032035200d0381410002440c02a1000c0d1120f0756090310303074032500c0b01407240c1c8044a03c16000c90b102a6696044c01c41c83c0e02070401da80354190080b00c2807180b4407861001601600900a100040403c1a03680d00c184d19800c400516123032602e40440c107214207406000c5070004021840e002e02402030360200080c0c0361058107000400441c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 605258327 1250 605257077 605257097
    0xb18060714030a05100f091509060311040b1c0602070c050a051e010c021309150b150d1119090801020708041e0f180e03040605040302100c0614040302010e0708070501 73
    0x403032010220050000070842006152142d00c407602816107100c1e400c1d08500a07080001e0404101d1103100112a0002e2060140b0a44001048007812008020a5000c0c00c0c003e06070120700e080c0701c0da4fc010303140304900050b43d50000749841e041801060b84500d102d4a10b04504200707a4075031818808108010008041084002000503540c4080c01d19010750010140c0340170031170000b00d60b408640c05a018000c2610140361003107410050301c00c9424041c3d08020106510401249040e000e4030071448018000b1800081c92580708400d500803a40701c00b410400e020800004076007000503403000e008a00001c1d071074101d160b25400c000e03100b28441c0072402c1d48040100041c40d0100880b84c4050840041e09442c2682d0f15a044c040d00c0ba6030414980800f490691443e00c01071000044808503666038461500b001c1c91a020080c09101596030781e4144000c0c0500e9000045e0f1500c00c80e0407811107849104603506150400a00315000021000c850790700c0808240580580005c98000f100c00c00d2030100010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 605259577 1250 605258327 605258341
    0x8030a11040e010e0a0c020304050f040b062a01020a36080f010e0a0c0504020f0d0204080607030e030a0804020609030f0f24040b220b18060714030a05 66
    0x2498503644080d4480c0c0c01060100d000704108035024121030595070500b14a495141704081114500914080980c0c0200010080b50070070028500b44203d0080c000912208118046005079004080703100e2440c007441616641c441d0300743d15012429003d08001c5041c1804031030090000b00942603801007074018050380d44c60240c0251944072000e100c540032a101d441e03441092684c0c90065080c800006d50030301142c55020100007032081d00302a000704000049903d44010300009522120300050403820402c6400380c9040d8a0004100400344200200b0752894994002001c490b501c0041e0f1805030820001c0311101a0b00c422840c3d0000c1c0c04030390722950b461420000034074084210646142c14090807040f101d040ba404901c10380c2c18101c460744885d1102aa01c10728500c04000ca030700802a10f00c0c42d010480040140c1d030044002030b00c0d252413600d02006a152091001c000b100c540320070701180744070024940814400e43d03810100314100001944056004010180802006048035075569070003e03903e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 605260827 1250 605259577 605259581
    0xb040e0a0608011d1905071e0305030a0509010207060c1101080601260f100803040b0708130e0a0e03090d0308090709050f0406050906011a0d0f0c180e0106080408030a 73
    0x41403140020081c504000318000c20000c1200c144440c00e000e104d0040c40312000303041c41041c125a00c40702501f241c03410243c0603c2404403021212101100016000c4005581040103019130140e84d00c5468031107035810002490000181c11400c01c01602d0405803000a0480303443c05080d4809080c506242d40d83c00004803000c40c0c0c860107105400c40188551900041c5036010329000d900c48481d003001594480d8280e8041d10326910274500790398020030007044411841005402c0e414420242d00e4500f02414099080b5061180c20103000000b05005103c012200780c4910f1410440800107907060002e184005001d50307070440d03005400e00c0410b800041c3c1c2d003101800070314003900140c00208010305103504007816001c03049504032085e514040115103140300001e0114102c44106003000404000707500c004c081c2d0382180d40b002c034149484582d4428440d869000310301d0300b0303066917860124a01611420350145a070940c0a00b00d01c200020041c03048660110120b40c0c40368200f40c49641c1e94407800b20384e01c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 605262077 1250 605260827 605260829
    0xc0314011b0c031d130618090c060c05070b0a0306180e030a032a0801051e090615192105100b0c1002030a140a1a12010e010501080312070503010b040e0a06 68
    0x3510405014202c011703007036180d200e5000d40301881500c04e0078810041032001201c02074100940281494181000f03e24030132140c2d841070500c144140d41204d5038425401c1917075040740c040900805e0f12507506100400c3c18907000c0030910651041840b0010044041c0340c0c403071242680720f00030552112004101c054845e81614100c1c03a80c090320700d554401803400100868002e00403d44111103080e00c11406d8000421001c401c4400100a882c16444100c200009240404400080500d0034010390580049001c41c01506884584452460340202e0b8000c05c0c1d90705040c514084124507000a00100040300462281510130202140b5074408240078580e2910044000142065000000300441044250003009100d60540710034062910342500e41d0054030a5600c0021225907600112209480d006210420890b441c01c000580102e01c08901030940d6001d0304610300591000070402115000312100b694002c1991078001d00755410035042d0070191003140f04042d0012100e2000c21550091940024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 605263327 1250 605262077 605262079
    0x130b0c0a050f010e01110f04060806150d050103031418040b010e060409150504330504110403020a0b031b0a050f0a17010819020402070f0c0314011b0c031d 68
    0x10307010401c1880020301030300711813446501a500b007050382c842c43e105a105a540f0f4003211a802400d180c04d00c0411111505c004051580c0080300340040c1e00d2001e4408000c003c00424090013003425815410047c28590700b610050303901c00c45c20007038542c0180247e0400814504100c60101c0c0c10400580100ca207161040d0100b9400680010009018196079005454600000e4102100255030b0000c01c402c4a8145003109040441c0c402c400754041c8000034440d50b0440380c50f500040c1e00380c03108041340c11a44520324064401c4000a03082c42903140c0215007100174070744510140d1035071400040c044030b40c454401e060621507070302040d5582e409e07000d50706a428005d04628072a03294181100f0041107402405860601070b00c4010003c210f001000c9102c103648075921810340d6003841a5424032000f913200d40c08c180d076040603020341c0ea00046d171441d0300040298020040060207200340b150260031901c0c4801c0001d0300ca00d0121060210075041208224042d40604095681c0d00360022803c1300d0800046250b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 605264577 1250 605263327 605263333
    0xa0e091509010b0d05090109080403060b130509010605010e0405160804030203280e0922020303070215071a060d0840080105040f0b07120207080904050606130b0c0a05 73
    0x31810f1481c0344064501620301c50001c0c03040f40c4070310860302d00300c4054410140c1404010042440414a6508100417020000d4981649000c04443d0b8100711007068441812503519400104800d6a00c0314960fa14041e045408024506044e1100150320702280400e02c02e1007032540000381418004d00030384814034405020107509480c86040c00c90501c49049028021440358803c1080d0b5041501c1c01a122f5000d16201045460b40d170510940290f041100403641032208000010040e00e03003011380c034810903180040b00c0d11070043d4500140009480080703d03100b44030500c1000311a655420780030101a4000b90720565a0600c07902c145000c154074178102c0d001590360424040d001201042403880f1404410101d07405549900d000382c2a14802d8401511040d1210f21800c003107100003020541000442c2000d2250b240303615000026604441c40640302418082442a1981001d000e03440d0302080031200c40703103040c081d0440f0704100c184c02d028200724524003085004040c00d041002070a46600b000032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 605265827 1250 605264577 605264579
    0x1e01121101051b1f05070e060c0c12151305030a0c0213090b0402040f0c1d0102150109020306100c05191b080a05100203070c08090406050a030b060a0b0a0e09150901 72
    0x90307a851103d6800380130342c15419040024195618400c180c041c034000c0d9030341c4114080910070810a03800c04003240d24180075100394001c9a0b90b9a80c1d81c8544c080c000302c040e11144082035a00c07a8070340760040008008801300c01c16640000e50200807601300c20020304208195030003500200d420b054008100090703551605121000780890700300c0e0a072082d8421542032000c1c400740c1c1d20800648000080110105a100c0079041580c004400c0b682d8010302c2c1841260700000034031000e144d41500a034030030700c42a64000107100240c1040d9003814088403142c24002208070460b51000c0c0d503000fa81030384800300c1050719078207802c110818002d581050110b111555205803100c0710300e900c03240750280840d000e00ca030141c050010403550003038901c610002c0d101c0c1070301084580c6440b4a281d10548030070ba4007603034642012549655040751240514051031411416140074005c0c0080140756402290280105200103144103074001c0d040c0c480604144c0c3d502c02d4a49a40c00804a01200c044500b40d0041e00c10b80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 605267077 1250 605265827 605265877
    0x70512040f120912080c030d02030711070803090d06150302091e1e0402011115071d01020a08040b0c010e011a0a17120309030c0706081e0112110105 65
    0x28020320042e018140030516022280c0040e50700603840d01c40c074101140d078104243c02207000080035100c110a180d099a142c00c04007201402260300c111040790100704400020b11142c0d80410614015105241c02145404013010000d89100800c450040115407508050200c620300d178100d003c002c5502501c0c5c8482410190f0b00c0f0841050025030080002400c1c00c0000d01f441610142c1401c14890b0301c1c580009611190011920700e25902c2840c0f20368030481c842c1841c0d05000802d01c80c414120340c0c3d50048501d42c003018806424424030703040d9046603c2700301c041c2c0200c0e55960444084507810b8046c030741e071000d408142d94050007141d00095001d500e054444001000042c01c5c08032101000c0700d00150080c1c40d21240741404200c401c25104d00c2c1c2c4150350104081c0341071002160441040000c032400c00c0c1a1555091030203800d9000800010b00350780511400c6003c049500110780c001c004559820f41c1410300c900c141960110001e004402510038000c0640d028108035181c05200103010301c02800002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 605268327 1250 605267077 605267093
    0x10501060e0114040e010618030f0317090c0a090b2202180a060e0d0618030c1205070f02090a060e130c0e060102032209230a0b090f07051204 62
    0x440103001c5580d90f460b03030307049039140400c44090f01c0007070b1910703207290f400c0210868010324003081c9030000c14a034038170220104030b00ca0400134400f4801da0359411805c1c120005020340820183c0142050351000c24001d0540da02d1403101410307501b8034100000d010400340000340740d852000d284c82c0303040c0080e80d114550900180d001008140384024402d02844094410f21114100314418000040c006110750441c51030036030b111400e07003401600c0100d800030451808800702c0c43d4940d402c6021840f41d2182404100718005040f500701802e007040d604103500c54840139610a2000030082c13058030b404000501200711503000c1009005811440d120900d0b242559411500d01a001030b142c020b1100c07000200b042e0b88542c5a441444e043e4040e5040142c50051544200b2010301c142c41010a5280b0115a5140d14030402010303419208520307076001c01c0d00c181c460380c03145e011780300c141501e041c000240c0c400d4031400841500201440c000e86400d54400004039103501034450420b03020720581003444107100d030341 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 605269577 1250 605268327 605268347
    0x2070507050f09130f1415011a0904090c091803110703080f0c10050a090b011d0705030709150507020f0409050d03020d0902040501031407060f0905040e0a0501050106 73
    0x54088034a115124010402265003003051240c0c8003e60303038001485420355050412001d8400d034100f0f8903c0784581e40c0c0c0c0310400c021072404038030b07980700050401e00c1400c01d0305000e006141071003600c400c24000c408031140a104d9212120f0103a61a207040d07600300100c4080b440c004013071003501001141801d040300b00c0c0d84211807800750300048400c0701010302d02c2804501d020440e64000c98451a03e4003209600a160b0819140c00303555005001410440e04000d006103031091607031074000245400b0928080c850301a040c0c00143c407840c003801500391802100209650446140c2c20256100e954000d0100c80b808059001468107198160311101c41707a8110340a01440c40c400c13a0981800c001120034041240c104a4020348203600a08001c05014004c1d4000c1c4850500d4540109104007541c01142c10b0f58801e80c402c56191401840721080300e8001e1002c00c1c00b6210516081c0000712611000801c078440c940034080c4103507946c50342181c4100f000c00a07000c866070700c0802441650f82d2600b001d4114901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 605270827 1250 605269577 605269583
    0xb0d050d0f0519080412030203090c0f0d060f020d0c090e04110312071208060f031c0c1407140d0521092d03070308040b03040206040e0a0603031706031903050f0c010207 74
    0x10801b00d114181d002e130007504c0c401c440b4800109843d4204400700300301c0c1e000a100384c941180c1c51155503c0402e00d1401951203100030030310096a1120345c50140b008884a075180c04081080020f011b00030007005030041c581242d08070051200310388101d40003074204100b115a8022014000660004005181c000c41000306141e4a0b91201c681e214418021400c45107050710754035411103a80c1402c40d1aa04ca40710030024504e281180300c402460783d9800008400c1c0c2c00780710300d680c821f120400c01080080b4400145560079940c850403e00c1030340c0c40b580d1b6208905e41d40c0c0010700244c404235080255600644000c0c94000703020b50600442e8510328240e05070003480c13100a4800114640505040000d40a000c60754000001441c00d450401c04101603003010304200d038012402c020008071070b403840e0034180c085c548410340010124034602e8098441d081082020b2031009240302004507550700070030382419004241d80e2420142280d49000c031202c0c892030500800040b400f04980c0020101540500120f0344 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 605272077 1250 605270827 605270843
    0x30506041505010b070f0309080d030609230c0c0109080d020a0f11071a040503150a060909210e033c06130c091b030b0d050d0f05190804 60
    0x50703407110740001c0d51024022140e184800300411400a408101800180d90003850000c19032525a45403908241041418500098440b0414080389243e4070a2820700c000000e110803000031009560000c10000138a045070401d0046801003448200b0341003854000c0d400700d8020758400c90003052034020b400010740d0000242c92410411205805801030403981d8000b80000d0a9451a20480c2012182c416140301d400c540c2c144030006050300c00b005601d04400355181d01c504180760422a42c421501e40c4e5010019081c148124207000c203991030010300c0c0000070104000c1803103418200036900941c80783d050503094401e0345c2410541102a4440c12001101c00615101300c2c03043d2402000c0c078007915251002940c1100c004039509490030710030510400c0c40740740b49203045951204250215984078600d101d80025211350102c00070b5140c8122401c0900496264510202584546980703195a8400d00144403449007610802d0380200c003601c9074400969910704030132198080041c1005c0066504490140e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 605273327 1250 605272077 605272103
    0xb040306050108060f330a03080418060302060a03090501021c0b0102010e2404050f01050403050322050d0315050a09020a020607090e1513050a0506100905300703050604 74
    0x5c00394a007240900e600e140200082540300c02501804007501440d01e00001c4540d50420075610b4001e03841000798080d41c662500e90345404980428031882c850741b814050302e000005e10042c2d550740c0980301900d009180024151090303190890092248010929007405003440703d092604d02a002441c03200c0c006e9000b4000241c1a03680320383c0d03501a072081110390422070343c140c2504080c504c910b0340e8400e001d0301c119a02805072291f2582114130545056001036400010030814041c41c0040d8035140fa0007208221564810782c84040c1c5800050b0306040401d500c0d00058800101201c01007405008010f203003142e2203680b030615400a41c040500c600140c000c03a000548202d02403103100080740c480d0b001c0581d860b034990307a0b45400c10301d00042d0300c4d901100b2090007022102d09403103094031030140080c0000305810140d04021b418800007403a68200b0220b490180055158120240ca48001515840440400d181460342045218928202d918030840d02e001052042c001443c070b0203180144000c80c402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 605274577 1250 605273327 605273341
    0x705070317070b0a0b1f08090111070506241002060105130e15091504060e0709021e09031e10060518131407140406080f07050105130b04030605010806 66
    0x1a000b0350201412076100000003940d1000540c2024031030b4800100000410351803411078000d4a1001d102070800202c0d40b000b001926503003441803082c0b4004404030642404510342d103241d0384040090035412254a42c2d40542d481010001e001810081c0041000b450802c840758000d658503000d214041c400c0e01001d03109104940e40b4440d074486070000c500905048407102215620b03046000e840c250040c403410795a0300342d61898900080c0100c3c410702e40881d0071650b105010b0b10f4001690051080140304100000c0d00403a43c400b04052003901199a079164801100040d0030300c403003000400700b8848402002e18030b1000c0400c0741c10b04141c50b50310820a0945420a0040c075498801d011502c3e0b4a0903030209604456000010f69000c1c03190b00f0325180760f07280c0c00f0b606003801038580c0400e08000b0f03140c116004030301d8240100c2000c0c0003000700614100c5210214941e41d204540b08260500000140c1101952910700c005000390448c1c2c0003081d81c0703555905e00640104000d03c00c010301d0340a800045078071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 605275827 1250 605274577 605274623
    0x80102120a0b01052b093f0c02010216060305010528030b1302030709050a110c0a11010c060501060203040f06020303040c050402030a270c060801060c03050703110307050703 76
    0x2c0c2181a5651401d05400d600764440d9002880f42803060796100b88100882c00744c1c1e41c02000102845131400c0b01079030f500c0301d0803c64038900c0b409030703c01c805c0444214091020103845004501807030354034040c86d40203071500040c0e0404400c0c00050285181440000c10170a4054000904070340003554202c1c070207a05c1c052000d458090203122000c5903250200108003141514440c0d13600403031055209000b001040d800286466a15804a04203035280d00070441440c800307100700c54406801c1c00d105458901c840d4001a00c622008070000e0100c80081906001640300f881304c1903d0710b901c40d0b010001e40d611480069a070360054403c5050401401c0c0d40031400d03c1c80030017a64040c0364071000d0b00d034070541080c0401c03010390001400190003541e80d0b241040c1590403504204c02402ca0081c000c004401d1508055546074030130380040381401400c500401425912070000303202583c261401544400403803504540051404911070454440410b0200038002c01140c08404c4920411900304200b8105003010342d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 605277077 1250 605275827 605275841
    0x80d020703150203180a1209060c020d02060c030c0f0115090207151a0d08090f060a02030a0815040507021c020106050a09091707081b0102070f060e070e01080102120a 73
    0x201003000500100c0041d0b64000d10b8210001e2182120807100c046186460001e0302501610700701041480c48200c05c1c0c009800102034a07051614604540c1160042001c0054240f0020f008000c00a04445a504240151350241c40c000055031422100003542601903c924410a5032141c010341000800681c140300300d500c2a50710658444403030751340030035500007000c084205c118400103a15045103180e965541401015224059a5071100410ba082c440380202c0001c003240968800c00c2011005138002083e03614201282c03500c1111a640c0c098000f0401000150060300f00b17040000380138101e81c0204540c48585540c00380c03a4101100340204174266a400d2040c140c101c400d4020500c030401140d00103140103405a038040c4024200d09607049031680c010b403c1501c04d00c001094912509000610007000701c407e500095051001d181c49400d1201c400080080400c0da58020006100760107024240080100001e569035640c3c0d1228124041d61041036103501081c108000a4242c2c0c2903031007051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 605278327 1250 605277077 605277083
    0x607021b0f0d0f05120d1503020d080f0708160b1312230310031b0f0501030e010b030607050a0201240603091a13030908010b0f100302090310020301080d020703 70
    0x10450907201800c0c40402c00c001e20094a00701c89481c1d4560209008024030940da01c1c10442d49540ea1005d282824100c90520265101c0000c41200c03c1002d6a11100601200b5400010b00307603544c01030300ca0440061054410080c030b82d0502141003248140b040d401220301902440420485940312030201c81c9190324000d004014424032046103403003520600032490903500c44020080d42121070000c1d085c01d07030002c0750701c0e20000704a030400380704025071002c62105519805c000c0a884034180400814002c400c0c5c055030b810580d5031220440200c03c00d4101080b0244003405840315410a40b0300280f49520003006031000d9800c00560b2110080d41451a003015000d507041d03d1002c034140b0400700d002d4030421105840c2c41d81c070706042d202d00300f103408030440c000d02c824107a40f22644107a18000e00003242d15848204180d140580460707140d1600c1141c50354184049813004c404e05140030040c3c000380111413000c1e4141c0b1903c0740c1003200d14241da00840c1618010030898200020100e0100e940359400d000c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 605279577 1250 605278327 605278339
    0x19090501090915141530010f05100c060c12110901080103060f060305071d0c09061801020f12070606091e0203100302100f0906090803120406021b0607021b 68
    0x1001a03402030101c600e1911070003009a071024210b604c401510750401c41500c00c010840100c90658a200401b000201d022248402c03605580341c180707100f800b0082440f5241c0034010321510581030b2440f0390070756101c1e2540840b0030410054141d1001f02120851038040d000e941c0703000d82c40213400c0802c805075503e08005a4481001e6030a41d034400e4090001d036090030b403840380c40380804000100c0a00c00b41000d003041c01806010f04e048000d406103100300141c400701300c81004006803041901c1d03200413248408400300d582d000e40d8507080d0040786490528000c9000034018801d803562075829580c000c04aa0b07016400c28498140c03035840780c1c02144e0800d060609550074003403080a5108064011f503034050414020206c05a603a5004118808506144e11002951103a82600805d03006020940a0b10381e6142410a0034244030845070f403442080406900321400d000014100221901145c1c40221041401504800300c0680165603880a03146000980a05c40c001c0a10102c549550343c100f140007010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 605280827 1250 605279577 605279579
    0x11e080a0e030f180402090402190f030203150d1b0b04030302120c06010626040305070204050a150b0c0705030a0326040c032301290d05030304031419090501090915 72
    0x107925224400b0b50f4013603420a80a000189190b030b078900c040c081c0080c04801101c3c06d4201843c00810302c07540364403100149071051081c03001040b6003244040d02c441044d1070f1754501090134186880c0d46d01e0781d50b040300c0c2401120382000c1410a1864090801c8a01c29001c03910407140d040c90603181c90080900519456120900420106102d4280310404910390588110a402030300b4035103c89400465060700454000184601141018810300d503000710344940070043c08081c0900520b2250701c9101c1c908180da0045007499000c6400d002110060100504881643d002c900c1c002d0a015058800301400e0303d200348014001440c842c0362a403050340d01544001e0314600f10303030760204c00d04200070121148603001341205407400002d03c01d070036141081c081e09059828a80c1d89002107a1025400280070781da443c008480014400015282c03c00e9240c10210707402c1c1c011101040301170050f0446503003801c3c02030250a0300182c0040180094482c280d81c2c3c09800d40d202e107003027000d64040d20509140c0b0190110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 605282077 1250 605280827 605280847
    0x307080601140d171306080115080a020310080601030b06010315080c012d0c0519031704170a03020c0d0509030d030e1f0615021501060e011e080a0e030f 67
    0x4940f40845118a080410400c07600c00e1141c159046103400c0c68840f802a1014044c00360040c1916006040e200c1c541082a0420900104030480c0a13100780300c4a50040046000901c0300041000a0040c00c011a0341d02d40c1c1d2401c0c86010030500741c9040d8003180c940304855800c205241814401c5d40d10910041c40d00c038000000460301e440000042c0304880c0c845030244400105044508201d449070f6950701c8010000600305241481e0310140d9031800140f0400d0a400041d030000e00600840c00c0001e0301040765615801c00c80d090b401c00c500e21029000300019a15503030f54050b4040c18001000c14126405c2e80082c440558036440b0ba4184658540e2000401507409440b9070000d8094410050540c0d9403d51414452030350210b12411002c151038461001340800b4640348040c0e2640d8070b05100400c0e0841c5061070078606014180250340401850400d01080c50340107841d6060081c012400c018041508948014035080040d290042c1141c100b0458003a880800400d84886c24541105103180248030341c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 605283327 1250 605282077 605282089
    0x1005070b090d0f0513090e0616020309030706030b040207141c080f0105060a0e031f11030106080f1005060f03010509070c0b150a030c03050c0307230d030c140705030708060114 77
    0x71a18945c842c225580401e0050480c0901c0303029803006070041107a42818250002d100c006070980e00c0441d4401d01c0312205641d40040c01004599045c100050b25480804c00300c2c2c041d00c1240c001400d1a800035004a4041500181c6907082c803a4064000c0300501d120581280d90340030a59403c10105c00103001031004d850591300403c20940c450603c05008100080828180000c480850100201000364030032507401a003d40520080001482459503040403400b506481d4090807109840c00d08070002a504104114104044d10f0020252030300d444c44a40c441120368407d0060358045c10646000c00c0303c05010380e2494101c154405418402e0b0340d5002540101038450151440d427100c0e01440c0040856981c4040701c010b180940c0280c000c80e01150180f500d00301d42036212094020404140c2002c402030a2243c0401d003504440c419080c1d0118202151030b0405e03a00c02034030040442c0d00116141000145040840f103055040c0c58005a4460305952103010034402c2c800107590901c0200d020380703444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 605284577 1250 605283327 605283337
    0x9090203100b0c0118110112020c07210f0c14010e0d0303020c121b06012111210604030809010b0f09130c03030306060206330a051005070b090d0f05 65
    0x10340001801589011091015101e402400c0d64903901b540307683c1c0c000b940e01400904001260440139894010700e0240c280e41d8016078403c01f0748061700260803804c03241c1c0c0580580316860304000d00e02102c160604040c00208000d2190014081c0610b02c80c1c0107550040701e0b0729070b6490004000352040696501c09801940c000d400d020110f0203441c0d80d136000300700713045c0180c141c00d01c1c2c1c2418148031701d502c6000a40b9010040e0840e81403280003900d054100c680000e0704580081d40170b22240c40380c080e00404aa80607064045502c903880150300301440781103000900758415402076a03100b409480e1808001c0c00c85400381403d81e00000c8440c00c1e03219a091048100350080c10300c50f1b403064a08410349405000b441039030812400603860701030410a0300e40c1002050b130404802da1034525040c140b0380150303030002c12165009101203800c1400d034040d0341d2120407400c000c3c10054036081d11002c403140000e0259100d000103c13035080e283c4012481400d40050b2680d0880b2107903d81003042d84010b1402d481903008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 605285827 1250 605284577 605284597
    0xb06070611090303121014090711011d031905032214012c070e15012f060a02090603060112090f030309030206060d1509032d09090203100b 61
    0x802c001c2400103840801c010310341400d200300a0b21440c01c224901c2402555250f0000700202c1c4a021a1b10450740c814900c55004610750428421080c50107003510302601104526809800040441100c200e8010005003946007003045031114155910205035130901054800d5030111000030803114582c0205a000004640264400d810041d100c001081c00d452400080d428595a058032034410b01d642c4200c008a20300a12001c5c1c034544e8102aa8803200a030700034080c030481c4980c0750000c0c4107039024130f0030300500480080902c0a81080441c660213010180481d01c910751181200042c0202e240d8403e40c1c02c0c0c058002e10b0146152034030001104c81d100c8603280000b10310381d60303010140060822218103400710305c2901d000c17441c6020b904001c3d0400200525103802881c00b01488000100081c03400000c0c0ca08070900000c00359500e0034220f8500c810900000105030100000788411051003107816150302031966480d0700342380c4030f0b07070000260b00007510700302800402c0320014883c265110003d402038401d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 605287077 1250 605285827 605285861
    0x5060a020309090c07200603070525050304060906020102090f1017090105070f030c0206040618051b0301110c06010b0906190905090703140f1008030f0307030605040b060706 76
    0x82c60002038511101914400500c0800240380390070815440c295140c054991030b00340840c21141404100d0034400181160100000000e401400d41e40c614101c00700040d003003004c00b18000c40d078584607640764801c0c0182000308540303200000743d2a1050007242c0c5201c00181c201c010203065401408100320040c41248103001c0d04115a4001c1019020002e114000d000c0c00400ca604180320043c2c810f1200039240d2040500745494a004e60f50001000b0740c0099000c0030000c2d031007a03405140744a400021308020020f024080b6040b481c20760701c0001d4091444100c001300110850355080b42c1d481d00c1243c0120380c0a41003480104051580c1502400100c403000c1d299602e400e0712003034041e441e0b003003a40031140801c005040c1401113040c106074140d400059402d0800081040b00c0c080c0b0b1b1101c070000c0c804001040b4101c000b4401d0400414a00b00400c2c1800840b40c03200154034102a203504100c0310351000a1a00c040020b1902e0700d4010181d01140181101e440c0040313540f2a24060700000390342482c410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 605288327 1250 605287077 605287087
    0x1f090302030c19020f0f06070f031416050f03090d080901091508040b150f1210180b07050301030b070507020102280209010f3606141906020705060a0203 67
    0x4000d024802d0001d5508040301202c06540c41001808003210040c2c6011b910a6a0b0003100307500d8142c1140d066039004074519081d2002860112040e1001d0910380c96555000f0030405942000443c400e840300741b02d6000d442c0680f141c10489941e0b4010043d000354000c1e204c0a04078003283c450001424440010b02d4036054a54503215003028080e000d10802c00060651070130801031003400c030202500300404412650300c50303000c0320010316030904000344d29124030070300d14207810080410041c0b60a007100d1040d0501c18400c4d99881e041c1402904c500c15210b5102003000168030600c40c40403241640d0348101e540c9059120908215019001014101c1c15485854619915806d1000411048010801d80d03404420780301d02c1444941001a440006910b080e454280081c02a413401460722040e2014520040784500340c0807011810142c40c4000d52a00e401400715903100c91610034040c01c5420f07154030b030f1a40c444483c20040b0a110b03201360801030b0800c102c00d100790314000000f0100c070400f03881240c0c101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 605289577 1250 605288327 605288347
    0x6180904030f080f0402010228021809120913110d1104090f09150b0a090612030e0d0201080103031b150c090509192d15081f09030203 59
    0x601016181900030035900c01e0204000340e48903d041c0c0c1d00207405002181c0e0307130034150f001030f6642820001200140c400c000c20031040440d00070401d00100c3e0001d0101101c80d0602c0f031030042040d41a94511603501452000300781680c820b0044480059002d0050709030842c001d02d806d4000c0072003010443c0341c14410040020034000718000c10381c03241c80c4000c1440c1d640e868483c0a034100d850303c518000c0668180060b54012506c440c0c8201c41c0d007145140045801c039410b0001410b0304603070303402c801d00c4185400c3c80401c03440b40d0201000b9005100ea201c031040b24502c1c1080041c4c08440720f400074002481c410050002074401d045038500e400155100300818a03083ea511600000000003844102d80e564409050309075000300c1c1c0c0001841e05803201c0709070b4142003010300d00f41041400c05401141d00d518407603000d040c02c506051185c400c0e03150300702d429800484400024290505402c8890110070301c3c08560b141d40072410309100d54000501100700124803081c800a000d0150040d401d500080c4140104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 605290827 1250 605289577 605289589
    0x14060a0504050d0b07020c030f06040b131401050118110d090602131d130302031b030d02070b101e05040b040b10170c0301050603130c051005040e150108060618 70
    0x183c148500c1900100385401c150007858041d110060510030b0780f0141c0d041e00c92200114401307401540142c000c024955401031511a02002c089008101c844c00448481c103840066101605031103410800110788812120713118140c0d5a040148580300b6010021508182c82c0d5912440d1840e00c10303c0058201101400401601035a41e48065110701154292400940013900782d194072051004c505ea50348099910025924004d0300700c114070300f6015680b03804c0300d650204103465000e082e41c0000c0d5924540342ca4040c0e544a000d071400c60a100b120000410303452052158540414100384c4001006841c080400010780125060036404c41d03900c000704042511b55030b00982a01321aa2128407501800c0c7d0700c41c074070144004142165120081c00140000c0d902d000c03c6a800c4140405115070801603402d1160030f004c525480035034440e20b40340301c107511240c101003e0001c45000e00303022006076588885146031076030b503084058009910070000503110302d02034020309185610701d031400445161000c0400c1e8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 605292077 1250 605290827 605290849
    0x280b0c030408070b0708030f07020703060c09050906011713020109050a120308071e0c061509050a0e01060b0406030509030d020c01052d01030b07020f1f0e0714060a050405 75
    0x9160304002820b1141070750400c02800181a01c0c01c595113080426103c0c100280000340c03d01c1c94101e00103001c103000610800082c400b0b50f41018041111506405001d0720205051140300d0140340900b000892a60091249040e021000c5200180c55601e001c004050f13710859001c0f03040c07103440c0c4008190313912160314200290503144101001754041e420041d02d1584018003034402c001c00004405c004001c2c80c0c1314200c0800080c03c04c50300c0e4410925080001d013038084021098000151b60006400c0340c60340042e0300411096904115103544035500ca0b0a950030360103004102c2008010410079584250b04c0981c0c0b12218101340c0c1e0614103541820005da85c0b1039203240b0740681d100c00900480303000c41201000a550400912405002ca0060944c1803020521001d080025181c4c005aa02e500078810409400c654005603411516200000c070b012580940aa64081e0f00d081403c041d040301c0002e030407042c0e41c4014550040078268004105269016010910800200f800005901e48441d10104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 605293327 1250 605292077 605292097
    0xb060f040f1d0c09010e0d20010906030c020c0f190902070c090519090837020102030108062a030a0b1201020406120902030a0506190e01020306280b 65
    0x160340c070300040b2041030b01081000c0304030290a10280100700140004450708480e0a00300180c805c016103001136034980782c1c0d0304080d10000008940e118081810020300100180c00d1701d03a4880c09481d80021012990540d081a02680c0820019003032407608a00c2c86080c00002058082c01d5201100e03060140a02a40b150407910340114a040070010611a414098201c50300200318034502281c41030440480201c13291581a618581030046c40307414012140802d041290f24100c80040c0c0700da80429200c0076420007192940d148030101440e106000b16030480300201c0051510341c6490742d044600401e104070258410300000314480043d606007000d14840c90505000240e0750611506101001d0202180d4440c9079104120038010140c11101076180364400c040001a40700c031034404030380392086c51203020b4030070b01c2807500b009a40b560702c0b910070f81c0c21b29045000740309102e030b54400c080c240e0100395005a4400130b01003040c08c2402c5154480300c0c001001400404001d86d446000d100381d40d01c5032081b9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 605294577 1250 605293327 605293349
    0x201080603210a021209060304020108070309061503051515191a03160c03080109020d060918050f01060303090e0c130b040618050d0f210c0b060d050601090b060f04 72
    0x124030564050202d00d61a4503419174040c5450903010000d81c0c1da11004200034140400800420842c80c46a48200d4400b50301c84010010004103041d11051200319110859042c45170500150000c081c900754103004400f02140466018602810008002d003101c80060b2200c1c44840005450a4a03c8001c0544d09440461660764103201c0c043c4141c40c1000e000101c01c0c00b000c40e10040000368010700146c11600c5507000182c41d00c2d84420042c0241007964061806241070030032018030341001121111031603205008544500d08040469800d96446120140110322003040410001036403062030341c0e21107004a80d051505051060360b81c000301c80d41d0440c0035010804541031048580000500b514100041c0c0840d901c50701e020b001450a000c061402841d654284c4050301c10010034042600d42041003040c0382e4004481075000504210b804070701034130344494140204490b03080103610070b006540c20a01400481e07003005802030242202e8002c80d600100c08204113008101807030003420160007000a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 605295827 1250 605294577 605294587
    0x2b021c05060a1b030c0f0f0306120501050a0501081603080918070c02040608010e100c0203040e010303110c0402161b0b0d05041b150e01051e03070207080606030a020108060321 77
    0x314154150b00f0304110010700d45450303100c0c40c4240d000701080701e001180d880c08003620803520200300c01520090b841070b0309600c00311604204121040d0021442900550ba080140340c2e81c803c2401d0b03a0f056407a80703203a40c9030b2032018148041502c080080030a418003a00c074415040381c0d900c8006030b50380f0441c1d504001030280400c2030110b240c640101c40091140d03000038407042c451482c425442e0103074001d50488545d51400c0d04800715000340f065800401910b50070f6040c540c1e480c10050803003401c01400014a00400700440081c0c50544260742d1011940c28402c1d949000d540d550158121011001000002d09900c001841e2100c41004080b001101c000104007820a8038140b401104864645c05082101034004e00c03242c042c40c014004807104901d02028030021210041e41d062140320405030207860350079090032040c03800c8001140030f6020796082300e040943d01d00c54240c980701f05a4040d6450740004c1c46250166205a10058202e1401000d440442480409809500f580c004001c1200c030b9010517 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 605297077 1250 605295827 605295851
    0xc0f030c29160306060e060c0a0507240201091703100e160806040b030a0f060b1903034a04180308090c01080f0901021b0c2b021c05060a 60
    0x1e4400e442d107402e401c0c103125481c200a0068542c0ca001402c541c0264400b207820f08443c41c0400041160742e400509450303203903445812245000c100d000030100d941030700560200e5068414800c680410743c010341c01c0c00040890303100d5041158006051001d030240c102c8000f092410380790658500410800f40201280c680211014000340d00080400388182e00c1c00c0d128102d2502c0104490102907448013001c1d01000c0c05182003c000c0550b542c12540208128901881900c24034600800780d070b01903212600f041030701f038018941d001c907090702c042c0081109103005003074203145c0d0700e110121a0101200d0350202903014003040071110440f01a0380700010000007281410b80020600e5080031980700905000700d01100060650000607009100c40340740c9000054810300c0039419905500e040001c0300980046a81103c0d585945204006205803c07040b1089481c4c16024540310204040e41c010003418242070b020003030b060418020014400c00d0400360140082c1c1e05100152141030741c8032000408122041d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 605298327 1250 605297077 605297101
    0x18071d01110d360302211606030e0d0e040c090801090605010510020f06040803070c020904050d080a0e1f1d060103060513080d051b0409050609070c0f030c29 69
    0x1454034683d454038003603400056402201d0708059030b4040d102c00200d140288140c0c0044101110f900b0100d000c1c00c90490a48041d1300020f00407511142d0302030004000501900307880718165000c203400305040b102c0404045c202500020900e4074a03050020034240d40d03420b0b10b400e4800740720081715141e40d07800051080740b41003101c0300e0741c004581c401406451080b902d0581d8a1202a001801c3c2110100000d0012032043c41801d401c180d0191101602e0300b042e20704a0b6982079008500c0c0041050400013813152987c42c030035900c11940007801881a03100a00c41100d450540b07603030188219454042000030300e15004204118040324500a00c1198035500740f0604444c40500030751034008500c0ea021010441d940300350340c014988158006038907158074611585003d444908208029404540003850505907886644a9601910452841d54031090116070018110f90024100c81005003644042840b070101c100ba580e11840124940c170080564460500d6410410407200b94680b90070032842c1d101c49 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 605299577 1250 605298327 605298377
    0x50105040c02030408210409020a0201050915090c130204051f1803020609040e0c1f021501241b1101020d0e130b15030703090218071d01110d 62
    0x181c0701940c141401c105c219512401490001c00c00e210303400c21700c80825020441160001c044040c001c5680b0741c00440041d01034601104c20782004c0c00b41101e44545212003043c01e510890210020300190305104041010203006002c0e0b105100381e00784030109003511040c0700002032545040b044003103880344542c000c00906041c0895100302603050001c0006840e0704c016195044401c88000c6120001550340278508070000c41c071640d0024031a07108624444000c903504034112103c2d03094458210f0032409030b081400085c0303e06000740703004810510b10203e450803648241031007032901d241d01d0140380c810703251106c88810f030541e82035107a00400e060643c0c0401a04242d05076504028010741401c200261a00c0100b4203219940790b01d51450a0309542e4568013510801048001079841c0e0401200040007030040c010203e00608803c2900716441c030049009034070614a65a40a905600e03102e4600121150800d01d10b041c0540603601024000e8103000400e000c0780c883d5955614880c0d0190b800000b01c0320 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 605300827 1250 605299577 605299601
    0xf050a0213140a020a0512240105070503070201030902031207060c0906081509090c090c030601090b07050309100e0303030a0b01120204181107050d020307061a01080601180f080105010504 82
    0x98a100100441c0c078103035109910600380710300141c807441707035017401d07500e5108008503440c1038034a110401282c0d91601c0a01c0b080710f55152000c90040d9168030042d0741901c02c0756000b41095006005520040d031181d00080b505034409020307200c503a034454040c1e45440e00a004d0440308a0b456240004a956000a003400200810301e4034040c241131409680c09031440c100300a0303010b00f013030718005050030208125070076400401810040940c0b50101107100c00e03800c180c50581c00102030010000360b2928881c180c540054210014507e00302d9000d0400c1841c610201900042c00828001c0c0c030b42ca6a420310186201d941c1100c004220908490001000075401d03c000340d01c40b40c41880f0034002804a42e80d03403803c00940302000220a088016000f4040c021010010414862243e1b034402d000d5000c000b902e08203116900074440c845664110f8184410007010050009000701c0001c3e28a600c2a004040c84c0c802108002c80032503110f40c4c85143c00809500903038000d80d181da004000a042c14841c513510015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 605302077 1250 605300827 605300831
    0x60803040321032f090d030306080706020a021e0315090d020111190509040f020c07030b010e0f070f0e030601060207030213110a0c060605090a05041e0302120a020a0f050a0213 77
    0x2d101e030b411900520410361300d4804503084c0c1040002000d900d04840d8020f10003049080c0805d41d9150050203011700c1d0040c0501c500038080001511400020494485035009101c00c2101800d1003c01000030a05078901c0c0e4144584425a0300340940c803810180503080001c084c0c42e0382c94a4000203402e40b0a050f0040360078090401c0340040e42c06802c0d00f41590380200740707442987e404100300020040c3c441e4071400c02445200003842505004006400f0044910030180d01425a80e94100c0c10340360102213540702e942c4c80f800000681a103100d0b201c1411101d48501740b8019030382c0600042403400e0000d8005401580c00084180150b15040c0320440c180c2c09812420300c40d8104c2c1c101c5a001902844058005115034441104104059500f050025260140c4544101e2a0170303911240580382c1520260f407400f0086008200358280c000c48060100d0f015001094500001e9a10105980c00604000210300900155100250404401e0158203000380001c5c0590070140c0100702c02e182d101c2d000c10911134 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 605303327 1250 605302077 605302091
    0x207150e070315020c12030906190204030c090903020a2411090612060105040305011a0a0501051e030a0b060d02090414070c11040603080c0a0507080c0604030f0606080304032103 78
    0x188030f0b0800401d074a44203807000d80c9504000c80240c2c90030245078000d400c105d001200300000c01c18000345841c803440ba0310240c030840d4141404100304038811404082c2c40204440390070702001c85141c2150b13a84501c2032040360a00c841d0354a441c140c10011603258101440307a17645203c00d9510768007a0000043e00461101e162a0124000a20340d03c034101403400010300823000510180c1c000c3c0140c40046800c1002840021440e0f00480d44403c04c9000240c0b16007540d40f0081240d5100c3c006541405295070340d000611000c0d034010460030381009156141658030350341d911200d521b40c0000741201404020300581c49100000400043d55000480604408001d80404c400389600000c180e4840e80c1140035034450070f1021000c82e01901158101511100740050070344124400020f0110702030380288156a050f5403540c240ca43c440784d400c40d54035400b8800748400c0c004030385035095030340040f8070038080052580d5660310300701d040d60400c3d441501c6901c11902003203d0b20705004800703061081070307180401500c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 605304577 1250 605303327 605303333
    0xe041716050f160315060b0c0d02150106021b0f0303070c05041802090a09030203090916111606050c01091205031005030705090a050403030b041d01110c06010b1602040207150e0703 79
    0x2840c807000c0c0580d0b4a0317004141d0000500d5000e4000340498804080d0364090003084290ba55a41c03100d690010700c200d0900c1c0c0c610340c10400e0750b00d0580d07100341e028000000d100c1c070800492202060445030311045448170508074cd5020801420080c1c0f103002d28a0495141104100484246090224801001440460050351210a125407001800030001008074481c05c0403861806080c06198100442c00700b4411043d140350080844e0907074907620b242500b01482040740c1c440178860745410300452a01401c2c0206c90141c000b0341400e080e0040001281e03a040d44420841240300100030010030400410311055101c4004034002524080c0d00401c801752901c0f002c00c0303440d1401448185100c1d85d4030086403c02d4401d070095014408020400d21078244c0c004817545240404076100c042c0c1d07618001201d092000d2500607204440404400303041710303030310300602c1001070783c00301c0703507003803d40044059010059032544064104a80511406050490215855000c0707030702041c0120b07a10b82c043d02c0c0c20400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 605305827 1250 605304577 605304613
    0xe0a050a1b200d020d0c0309030813030203211806120408090a061e030203040212010e01020c011512030509130213060329040e0a02040f0507180e010e041716050f 71
    0x4a10410301e41b0b440c1040503414111025422500b00034503407400050310f0030300300c0350801074a02924021000d4030144080401c041010000d500301811890f04107200113800031f40a6503103503420880c0035000341d240110025030b280600d642182c0880c2d1415010910314102e0511050050107000d0b64200701c8500745135106103524010713101408a0805070000001011500c0d08541c0480003202c01001b40300300442d0902c420f000c4c4d000151a07440b1903103401e00e11090903044103010003c4951180c0307452902011901e044510354415003c054103c2d03910381d0180c510050714070040841c400d9524a0703505117401c041c0000c0a50f4020203440c4444001c4000010b00468483c0d10003900c0e46040307400085000900e850703a0305180c07000a01075409442e00c0c001801a43c11900b01c144500c54690707400c101c10058204000d0424414080c5142091003000140100c120040301c0b180c00c24014401003900d20100500c15203a50701004868880a014040c50030030480f0820054403c200981c014004140d1043c00f4194 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 605307077 1250 605305827 605305843
    0x1403030301290417071406040b1b030c031603140c030316030e0d090f050901031203050601051b0a030228020f0f0402040f0e01060302040e0a050a1b200d02 68
    0xc40d11075801031103280c1456007120f004100091081c4001d000030100399465103510710845030301071003e000c10f04292600304200e8056420100d40c440c2414405c2101079401920396040c1c2e1b04a205c108840c41c851f540410203801e003410303030020710044a03082c3e10340144404149003007401488d5041c401d1004409020060343e9108002902c0d6140c0c04048480403000703400150300a4a2a00a810900f800716500808000560b03220030440303000907039541c0a10401c00380904c800f6240507000008203480741d2007908050741041c0145811420814807481e4200640414012040158481d1140d6810541c05000f400440c42c202c80c59001070402201c044200c40f0380300c44000740b03c0c004800c184542959554410081064060011500c442c1c40b040c02c04a401024010301044041c83c000015045100340201d4050310850b4490410b5512103d04c21005008054801012241c41d614031644040e40014812071045a2350703941c503c080c11070040e198003d0301803074004803150040c2d85203c0c09250002520300e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 605308327 1250 605307077 605307119
    0x20d02010519051b0310090e070806190204030819020d391403071e050a0311150a0213061115040317011d1513020f090405040b011403030301 62
    0xc1550f079990903000500c80881325080c40050740c0030050002480424200d5802c1c2c0e0822202040072400481c00c6c2680d541c818030504555501510000d00d03c82d82038040000000c5c82d59001505107030702ca42d502c41d103e80001c68a110180b1031301c100b01310b2182e0f04000c030325003402c81350a04401f004003000d90b40400c2d242d00448503428210a0b03640d041d0700020b0665110550303801c45034004080840040040e107d0740014030a507000e403288100c107403103403807042c4c0e40510050f408002411110610395042e1002c81070680d0b00c060761f0181d40e065900010780800342901c189a0108010390700c12500c4001c0e4200c41c41900314030304000c5803280348010140000b071018920a202c0146e5102603659190868400750040a2400c400d02c5240000449000c4030302c0030700c0703184814408041a40c0e00d1310802c000a0011402503548500031004000f11090280c4c010003042045d00c0c001441d1440e0030380810191002650201c40f580c1c5500d00421901384103400d00340c84400101c02a5103154034020100000110600c0d4070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 605309577 1250 605308327 605308331
    0x30706140f240a03060b010f1106010501180302090406200702010903020f0a08120a020d1d04090204021306080603060109050112030e0d0210020102030411060406120203060a0f0b0a020d02010519 85
    0x30301e115507500b440b8040b05080c000e0050303d5541e103c4c6442000b0b010201011400300f0f0f1042d802c1c18000780100c03540105200030100501560b1711700380c01190b040240405260114030b5070400840961104501507118500512000c00c4d881322030303410302c4501d0b41d54400c00034210f0400e0040000603030344803c0a80489404a681c003409002100000e04000109c1c3d001c01e0440c03241c40d1409102106cbc18019016145e81078007600e90011012030140d88140310380c0300f031032401c0b0f00d8503404a00078076248e40f000d000540043e00050034030443d040c0c0c2c0b01b910b40060b040b01d0049a42001000840d240c01c00015000d085240b01c180070795498203215050794062880d004043c8410480c0c1a40030751504106606045d070024130b41203003c1010038000e4000d5100b0303203041e40c40c2d240c110340001d103d05000c0308880494406945820300f04003054218030081d00040c040c191b105085070b81c0001c04030300e08007480010f000810069541c074081240c02a02c2d00640ca000c580669050208104140e20740c80e140b60801d103e50100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 605310827 1250 605309577 605309611
    0x1050a120f060e0103120201150f0608180f0304140f060a0804060905120307030e0d0e060a050405030304090c020d020106030b18012301061103040b03161101060602030706140f 77
    0x2500030b00003035000000302c2d641d41030001050000c0801050443c0300c481d0000c11940718010b405507080d141900910458144420040000c80c0c81200500d40c8204d400000744c040081e05641641020a03141400030950f1000c00d0600800300c41c60180021280300b00c52200d141c041c042c0116900f40101508502401f0400d00001e0a06c4415000054030035400026207c0000c545691050250400d45041c000286065110001c0c290009500c2d00031280545078030303600342c1c007100c104032a6501c65030340070f01000300c248400581a2010030192021f40150100460785003c80c060003440d02c0c1d403825001007168140a41000400e20016040790048561125143c20005036002c560241c10441c1d00b00411000c11102070300003400842c6442c0c1610b02039501d03000345000030200103a60b4019030084221180080010818007144c15038242c4444000d410151300601003d0b0714903007101e2695108001607000040c2c940d04005440c441c0c503032410032070801d40e1503d05000d00d1030080200d0040403c18a5601036034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 605312077 1250 605310827 605310851
    0x50705070611190303020403030809060622150f06020f0d0c0303110712090503061014061318051e01180e0c0415080d0e060a270902030f0601050a12 65
    0x1050b000504200f02c00c0c9000d1000910780100250310500c03082c0c0c0000c0c0ca82000c40c0104001240537400340710010301e60003078015018065000407948502d21032201c0c0d030f12000c1101d00c901c0201e40c03000400104001d210394a161850190034440d022802c0700c9503411841c041a009904075540c00001d82d09890009010720320490710390701a110b4000302a1000303d0500207008816408178074202643c1c025000c2e5180ca454036a21074082410300d004102891000540f0210f017818103001905880303002c41404001150380c2d5603245401c02e2192614450703261210308000c084d81040301c1403071400c18242d440d07003250341c9803240c2c008040039010ba001d244c0944554141300c11250400c84404a490001d004002003680140d1002c19003034148540805030160840c400030503405070014030407818000e003250b860400d5003181115201d945506e005507207000c060b45840030105054124001d0001400300603640c1c2041c2c1d840095942c0c0c018801410400c2c100702c43d0409a502c60740c1d441174000d445402182d0050501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 605313327 1250 605312077 605312083
    0x110702181308090d081b0d030507090b0c0a0b040506180a02060a120b090c0a09051005340f0506060901180e120f25020a12080c0106032001050705070611 67
    0x80405020000080348070806c0b02031001611400c1080340b82191009108600103400350344086031a60f0100b08030400030008041240c0050400c410790000380e400d4500b1310350b5040d079005d070191004d4580d5400502040b100c648004a5802d422000d8030007800c0801c120b40c0018021711900b68000100042c0643c0303554103020350f03007112084401c01030400381c9030314098200700305540214120f0400900380440018003810700741d5811003045a5a41c64900d061a004584410040c0700042c2d04c1c01c49048a1100a01c1180710141e01c0306603200d0410180c0c103c03085d0501e5032404030064000ca20846c3c1e424010011441c2c0c1405608815241c0b0002166001900c803160703050244130b848094145400284403103200c03140c00e000b84044401501000044030900707840c82190105408003c0d00308122075428072800d01c0362162031415034490400940f5281202d4074203800c1d42c85551048a030000309243c242011410b01e1050b00001200f0328009082c00d856071120f96855100748140014000c10001502c9402070074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 605314577 1250 605313327 605313349
    0x30f14042402043f0b1906050a03110d0b01030309050a050f03062a070516061125091a0a0605090a12020a031a0f0a02040501020606100509030111070218130809 70
    0x3044c00811603045040011072044102c2c0c0302c501000c44095494a424803070711844d0b040da034015240b814114110355400002c0142c91144990002160600c44001446900c215000e0340c400d55500c0c080c5840d020511941030410b0b080741d4481d014184000d28182c1307001030101d07802610a0f5404c1c41c0c00e4100c582d4001941e0b500300d000108084005603a5050220008039880300701003101e01e210090380e80c0d00003101c0c040b1056410401030307004815002c008050043e500d140c01044106003441141d0340d44109801ca6443d40c0b0240e2030f010418101c080640340c01000c076030040545082c21841c00c42100002000d8084e035010b40345805404004102c10341d218240e2004c0910703446112191039000000300d411510f5011980c008100303800030001034007040765000f5a400c0f25010b8004000030307103a801c10004421410000b1100300714061201c128595002d0290840102a4541c8940c3e144503d00604c10039035507413a10a0000c20b0705200744140c0074103039011407607150341000a83d52510b03c2400003480d400c1c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 605315827 1250 605314577 605314679
    0x40807051c021306051008061003060321051312050111040605070b15040216060506010e0d1e05010c09051e0901151806091d09030a030f1404240204 65
    0x44a4800c000d204d4000c7c1d8400d001d04000c0310003070201420200114151010b42c000205003000115680071910742000c64030f000c01c0401d09180703043c1207108240007a0103051340e201c100b00151005186080c0b000a2044500c400000855107140500b803d1015100f841003900040c481d18401c800140020001c03480c02107110b600800655032180d1040101490542d9003005a6034030385000045101c56009e854081c50300c2d07401600c454000d0206c0d49a007030402c0041d045d01040400211112400100c082c494902200700076215000ca00b4281000d001c041602071409990410741121960816500c440c1203a0464810380702c42440e4020070081221324846402c0240300c100325010b03011a41d1900a4074540580340240100148078254820303410185009072003504181e001001181e10061080c0c210b0480b24403104c90110701041401071040c4181d03c21101071b600c0d43c50740c106403942030700b8a500004250342c52040c10360601d41040e502200c520300300f55230340700c1e0a04025034041c48080b61760313070000f00c00c44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 605317077 1250 605315827 605315839
    0x17060d03020106052701060302091309030c140f1002130b0c12070501060e090d120b03030f1c060501020a0515041a0f0109180506011203050f040b040807051c02130605 73
    0x500c08a000d0f12854503051000e828485800011a280c0c8c0700b842910841400104400e801e0225480c02c48020030700c1c44400d40411098040e41004190b80d08a80000002140300030013640ea50400d4a41c00e00a400c1071004006004010790030004007421090003c0c4c41035500e0180c1d48460158065103059282840760307010440201d03043c1c0c18400e0642c000000c0b203c80c0e80c0d1608459a0b1000000c2c1c03599039034685407000c80c44003a1803020715030b0190b0020820450280850303142c918180020300d00c42c2c22168070407074207600343c00d20800441085d000e5800100400e0004101c086266550705480e041119881d480030004840020103000140078002e01c452400302510b030300c034204000407036001d803400d0150038010303410701c1110004c130030301ca125101c51290003001070300c0d6503424144661030710745180c101075007080000e000000010329060020401002c0404049036210320340301703015003414515400644601c86409130000c4240030000044c0c490307581250740000001440190800900090f0006900b1030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 605318327 1250 605317077 605317099
    0x150909230702030901021c050315121b04060b03190b04060909080901031a060406030e0f01050106170901050f070e0103150803091807020712030320040e0717060d0302010605 76
    0x540c0100007011161400c1e400d035001ca01041c103c54001c1004099a0b1001840420014065000d0f00c0c1903c83c612000520bc084a2005090a2883c05000320f102c03003902005c0808800c210700d8644500001007030b103410110300f10b00d0491290320b80d03018115040010030741c5a080c0c140050792030ba40301c00d01400a40e181041b00c0101c1d81006c4080f034204618007408246414a40030910441c40380d0b14280c1500148035528180c282a4100d001c6e04164070340e04054030074581002d140074020701038540030700465510500d00314a18609007140b8000584918050f0f403503e0300344810449450001607110903039080000303581c141c03080101e008203002058031807011442c1d0030109009401000800143d402240c1802c0c030072000c041c2841c100541941e000000da0300482007040500301103000004803501a0078001400c0c05851010420390805400700c2036000d10000e41801088043d141950700b00c4050310f0078941c2d02080c1d2007010f9038920040c0101d0b1040d509090b00004151003500280d01400c0007a061403044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 605319577 1250 605318327 605318341
    0x270a1401061d09010b580e0a02010f1701180e0304050306040201081905040b01030b130302070608060a1a0306012703030c060b0409150615090923 64
    0xb0803902c440490030301000403114600c610b009003070107040c1c60313140110710b2501070362040b8010005062201d44a00d1066203010348039248029015143c96081408906080c200c0d0340950344070017041c0a0741840381490074407200e0780c1940c000f51b881034099082c281602d01003106642580e42c2101d003011540099100e50012540642d0b808041034400e6040384103110f15000d80d141151240201e006a98069020400140c09036101d49002070b000100704c920141c4180c41c845284051302c070704440070b48201340040c00400410920610040e4010030011245103002042e56001b9207540241c402c183c2000b90b03140219809a0b076100c030500080000120307103200b18405618461154004840d91800300b800d140c0304000060b002a0b00340700b42c1100c010000703039540c21aa400d481c0c01105103800c1e5100340c1d1720300c14520705450700d11910103458020140c6403c2c001c00203503000309036038286e0804d1614030340070035103081840c0d08044550203444080b1400b02d8005090400a1010811034a040c0c5d030340810740c0148601 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 605320827 1250 605319577 605319587
    0x1509180b0907061706040209100302040305060f090604020d050c1e09090d1b080f0a080f09010b130203090f0a0305070308010e221401020a090f05270a140106 69
    0x241841400c20006507940d25542503254002c0d4818100450500301d1284c01141d07815500590042c4000c0005082c80d0602c0c0c0131030101c00b6044018000300754005400c0c828800100140740c0d010310b501400b210649040c4100940b030f07001c00340001380a000e0405440d02000b5061018a6005801404050076811600601e92007254404103036409201c46c200800daa00c100455400480d130200e4032011200c054001e4102c0102c20181c0e4251841e110a011041c003040607400140030f4905640e0f18800241004944030900c08409801d48410303038034080800700300341c58440e00c015200b0400c620041e22a40d0b0030064906001009a001c025400b0344581c202c10150407030058102b49010340e807170b0710441c0e8136011400420542a240088040100f01c0007030603501c0c581e1703709001c01e84980f50045040c40c155000c2803da03040314220b9408105004018021905581400001440103d8000700f0090600d21001d5083c0310780d410f070310468907407000060050740320341d04140504c0b400521030020035a5603400c000c007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 605322077 1250 605320827 605320871
    0x423120c1507050a022707080702010f06080d0e0f031507081f050f130c0302030a0f140a02031806010e16021f1d070807090524041509 59
    0xc41000c1240500030101000c0003542c0b0070680c00b00081009401580070410800180311420601c0e0311049042040b040348203000700e00034445504c41a42030708207024080c0c00d540110b004144e190b86022400c11000000040d90b0b251480c042c28042c0c3d803480c240c0042202600980003031074051080c40004003248a80e15604d40c030079142030b5100d944540f10307041740c01440c0c07043c44501c42c031048094206000341d182258091102c0c0500404440e1410011001f07034040d40c5184c00c8030000b103940842001003030000d6003e20000500500420805128806612140034002a00c3c407081c081d070110001e83c1e007a000c0e900f281d441c00c1002d401c880c81c0350381d6010340807080e5108680510143d5900300351038100900009680d07640b86954041026458558001c0d80000c2c01d0044ea0030301d11005c3e0401900d8055824452a400b034101040a4071145060840d1201a9400079040a80c8403030240041d04032154801da505104c1c18089401091108082c4401c1c000301b449504081c0d405071918001003035428010754035103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 605323327 1250 605322077 605322079
    0x304050405070c15020a03020706140f060d1707020109050d05010203011e06021c0203040906030b011e0509010605090d06020a031a01050a050f0c1c0207030c0909080423120c 76
    0xc007041d40ca020303080390804440d2100a003c810341d40c1662590380242e40107005042c0070380c41d0060504007a41c5654007075580c03018101002011b107400780508001c4078040c07140c0c402400d0761500d0076032005980d2220358645144031034600c6500881c03284211382c0705003041c3d0020700700140540303103600700d070708001e03000754000c0c030401000c60400c03081c0c9030603612030544c890210381454018011980c0d2000c1a00c00945109502c18210b000400000c1405225880340c1000303076000300300f681d02a60404002d01c8003102e95006442e8000b2904030200301c503581c0e6110740c5055a201c1d10b0402e44076464100407840402191000515407400072500e0000d85505070710103c80300c00305113140f502094820b001586d00b885000e052000040080243c0d1400da41c031030380103012040e1400100c82d090001410001002d4007101500c0005070400701c410814060084d04100c080c221042d4200894000f664411020344681d10880444242d03030145c201d5841c48400c1000c0050300e000e400d40e42c039400b00000c01e9031500d168062031707 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 605324577 1250 605323327 605323331
    0xb011e0807030308190f0e0a060f02040f0315020d020a120c03050f0a1d031801021506030709330801060603230907180204090516090b0f130803040504 66
    0x24030382a0001e030074801c407509600d404001c0e4a44500503c841410300c42c41d0240c0c1900c2d071010780c1d070700c01840c031071010454400340281c40c0e60b15440c40c0107001e442c901e02c090b505030760040c08148081e1160009503022a503219506400c4400e51440c1072019025101400c3d926a1000c200c4080c0c03170f600500840c01494200904101204424505400b101d1099990340140c0c00801c0000b04121603544c0042589014200341e86001140d4420040ca0340e80050110b803000da0107101c00c5019541c0410104250800001c81958149072400210f0764800c0584101c041c01e6481c0d200c441c44100f42c0e82046000d075440d030944047d1801d0b440d5840c2c1e000107a540708103036a561074940f00080310751091040455040500900c007014406481e02ca03046543d01401040142c00362050000e5600410021640c980301000000340c0c50f0b07413a10790000c017254030052000391048140901129015803204000e402d030703103006510940f00c032442071485d20340e40a01340441840300340300000400c500d01d000016100321b807004c42d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 605325827 1250 605324577 605324579
    0xa0602011b140403050f0703020f121903032c0d020f031c18110405150303030f280e010c03020702061905091c03081b0d0e0a0b011e 58
    0x8908850044600e896121601a407030034a6030701c2000045007044801e00c02508040d22034840a007000300d2603040e0030701075214040810860824400015254a040b83c0c5002c8d501d00d10000c090311045080e4941c8036083c5003542803800c00d0700a500c4180c10010081003080085168030385c0000c0810b41c03807507110044c411400181d082070303c001000000c2c009010055810101c030000c10f020500b4103000000c800300d45613003503c0c1004d041c941c420724400d4014907803e0b070700b20703214003e110441380c01801090b481e410400d00003d050b140007040f603801141c802d214040603038030220300400d140003403150130f401100700880a603603001281d08411044580341000b04030308000144c0940c101d2041c004000d410030806d00154040149108003814440342034180503140c0003c00d80001e40401501c40300c0031800075016414000e0541c8801e030307036a108407200b00351038a5204001014459000700b280c147d40f100e88461030124544014421205407551000c000412561140385494100e290311010000c183c1141d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 605327077 1250 605325827 605325839
    0x50f01020901141b030313140703030c030e0d0605180705091003080318030a0507030806010c0b0a0b0a0905040807020306070804020a0e150a03030504061b05060c0901020a200a 77
    0x1003192070102050b1601403a110a0411509083c4c1002a1800c0700700c5003800c00288241061006611400d4100280d410782c81607845d016280303510000109030507900920050001a82010b81500d0a58240c03d0a044030b0100400041c1030280356400100203034101000e00003510800549102c6002003241654101030300c0c1c00500040240c01c0341c2081c00701511800400c0803426000055030040d0112019081e03d2801c2c000840c5564015000c0500180b4001100301c185540031013065007044013481e0485440c02181c0314451451030180121144079a03402e410005a5108031281000303000d110f509200074030305400e0814040c0c100070810782c0613014001c0000d008a03c40d621244c442d5034014607035018103003480040a48500003d15504203205046d0140c407081c0e598a030044010f51191f41c0da40e944a00b0b140d001070a43c882d001031414902c18405220002a001255403a40000c04c0760081d42c54501c0b020040780b40c0090300c0c0001c0c100d10116081800a03241043d913107007040b071040d50f00869003940d0314 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 605328327 1250 605327077 605327081
    0x1150f08010b0303070308041e080703080106031803052b0501030c0501020715030914060906100501020712060902041d0a050622030804110a1d0901200d2304050f01 72
    0x10ba4050703815002040020300082c055511075400034041d11005004c565802d665030b0412192a0302a1004080400c02d00d00309540481e41741e014040c00e203800d10241014001c0710550f800c07144002028414003107264213000b40c1c2203003240640c410b8003062030310024002207148018682800162a0b0200300700c0081840d5000066140840718442425141500c518000320000d100380203040b50200b041c0b40e0703031075001c00e4100160341c0151201c1c4058009070400a00c3c1801d4800c0d254400c50564000c50010803c40800c080c80801454200c0400b09440b103d520025000346140310040750807071011480b4118109002a407c854180f1810864109460f01251038502d41290801082da1320345e1182c0150000748262401504644a60304501c40e121400c00020300008082e001000354459984103604c220138a106d107160030400104c02000500c051600040c0e030640f00d07c07021480140b00090841101845070300c00c0000a54061030740040c080841c00e00e902c03040c030946040c5c420f4806e0617544d8103898818 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 605329577 1250 605328327 605328341
    0xa0804032d0903150209010801031104020d02030a0c0206070806220b03060709030b0109090b16121a010315051503222103050606031506160605040c12030909020d0e01150f0801 77
    0x16103030300c6409d0380b0710781e1201500c250802160760025001c0c44280304100e030310b0018602881c82e1343c9011900482d580c00c021315007840100410104071814013032022544035801441c004842c8522076000ca05840e02403080546040c110786505032203110200410590b01660704c0090b070b40304030340313410711750741e1340c1c1802d17002e4540201d07025210f00c006401085804064001040300101c1d103003040f07407000d00314081301e904031031208010081c20081c03a06180368969151140c00e96001c17007424252f490078105804180d56401c5001c0c00e000a49001000c100400c5d894600781522101b04115905000720030b103049030a84000c02e516226035440d10182c481124020301070a0b02c40c100c050440c3d400c50b5034643c0044044030f940324100d03400510802408410820988400456501822010489003003a14000810000075031041503424001141d00001070340c4a0602000c64042d00301c09600c42e00641c0e9248020030b14030401045942c0307008145042c4818110b11601101d0014141444403035a03036034513509a41c0300c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 605330827 1250 605329577 605329579
    0x5061b0a020901030f12052803230109110f0702060a091205030a1b33020705210708040509100902120901110408060604020a05070b010f030510020a0804032d0903150209 74
    0x13002442e102014400c1c001c0008c40c3c03191401150b01480741c00340550fa08245500003285000d62001484820f24900902d0005814512003501c7c20b50071051007031050084800080c802d0070002854003080348248000c60151a2802070038500d2011840c1c101c2d5294050360703910020865401d00c0c041c070540c401030301c903003240e030400b10b240c0294402103c1088944603450104c1c025840301035a0140304000340c03024200c0c107031040009044c00003050b40700c852200051541c1d42c84e8007404000001c0000c90110907030b0122681510444100c1d121040302d4003d1984513040029070320310118a5009440c607021b103007405081920020803800f80c03550503e50b55449a402400d00581c0a200414001d091a500074000d81345d41e490030a0904116603644a006035003a401724010309202e82091051000a10180d40ba81d1300c8001c08515103402fa480c042c04a6000900140a01a000e2109807003074400b400304100005454410300a01141540081c1649107240405c0d2001c85011141540e0802c06208543c001d4074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 605332077 1250 605330827 605330857
    0x70303060608090d1116060507050c09130f170c03090a060e030d1409150a02010b19140d02040e0a0b0123060a020f19021905061b0a020901030f1205 65
    0x4d070001c01a124110300c0440c2005620413020268251303070780340f4800005480070740d4415503140c400d403d0403458007040c030f8445440b03004c0b00702c2413000b07441e411148060100d81c00400000e070580c2e40d040065040d81c0e10504103084200009840c0141c04000c0300810500310110341080301d041d1210001c8500902440c40e541e01640a0010315100c030b4090800c165200d50030130391092400010b030010480c04c0c491040d9084584201003503c008080e028010104c400f04148c94158890181c040d10444418240c0b00b06031194440c444400c0903601c0394242c203c3d04a4001c0d1081c03005640c950f00f84c036560303040c080d001d4413018a03c50002c201d1700052860300c191041d6140040e041040318404102860b40000300c01425403086a01e030b601824020700c085840000158035815500105005000002d0848286903408a08501d01032046588034001c0c0c0c0c4035249520000d40b1100c0d41101c0c101d1070450920030180d44118090000010499001140702e0900d2280010340c6c442d0012003000e5030300340141480700d00903503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 605333327 1250 605332077 605332093
    0x201050f06191d01030308010b0f070222060305061501020f10050606070f0809040b011e050a030905100b10050315310903110a0b0f040212060c07030306060809 70
    0x490b22446080203076281150840015588880380441041d040048920072090f601c010014150016003560041ca4842c40a0340b038500c15491407081c0344202c95009100b946903451041090b50802d604000c40b900d41c0d2000c020240c0c4030b0030300a6543e0011a001246c000c80e800300001e1300c1d4408600380b034000c1800700040003249400b05030304000d010000c150300d03040701042c840400440c84c1c00e046100042c1c090b00d2003c0d5502c29032014001030340c0e030104205060008000300d001c1400d07a03030160641560000c0c43c0040d141c044000b030842c058460040081d00c14415440b0700517070751107a07606c9984020b8084508050712000301070248c0300ca000441d0303045c0301030107183c501007254103215044a807034540040200080c8000000c0313007040501c8850f02c200846654081d400101904a13440341c2442164600030000c0440f01e68514428083c0140300291a00210340030801715240d017601d25104051304000e4074024030705031284800ca40c0018030282c1c0024103200c000030f0700304e004840d00750080581c000904040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 605334577 1250 605333327 605333329
    0x2070e040f050a050d12060e04030503040b100f060e040c032307020c101e09140105090f0a0e100b09090c160c06050a02060a05091c020f06010311030d0201050f06 71
    0x49070300000150b46502801000c180056070504c002c003440c103110b445806490f04584e190008a54854003c10903221309102480040781c1c015080c2d0740d000317912402008440e40c480440200714400d0780c0c42100c9001200030b020031220340103000702c0c5601d83c080d1400c000903044841d0840649804541d4040d2030b2a8030048420071070a04c030303540380c2d20000600480b0b550130043c001142c8100000074020002404900140400c10600c0d2101402d030a003500e061610350303080c908140e29140191603031906204000440c020f15445003800303801c0040d0001c014902c040d5640700041000b070000c45140e07004141c50700000c29003605d50029280c0a20b0301400849840c0c1c0c601d820b141d4698006001c0760414a4540c01141c0000e8a11038036001030f02440c3d48050301c480c01e5400107482c0c4840a0204240581031004021119400240301e0300001c44103100300b038401c00741c41783c00d07810030101005407503540c000c007000402401000079911610706404d80c12981c1c4401d08030702c102d08030f4030305072000403170386d82c40c00041665 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 605335827 1250 605334577 605334593
    0xe1011040e070c020a0f150e0330030114090117060408090118091b050306031b01050705101a030309130b060f0c15010e040503040303050a1403090a02030c0102070e04 73
    0x402501400c00d00b4003c00c20760001400660241d01455414400c1b100074402022803030318084030440c16003050303421006100b0003e0b86401d110503003050301b502544030214441242c20542c01c000f1020f500c0f29956961141e0ba240510303000c0c03136841402014004000100041101044481d0342000000b40100e81c0321665200700f590700c0800498104406400c010080d24041e0b54494020540c1d00030002d03440904950344150004071380c40031024000c007030040003010307180440c1141d00341c010042c5402d0082c40c003c0040c0c425016040c0c000d48a445561584040c074045940a10421510040c0d1a01e08402040406a481c07162901003900000b89501000c0c0341d0b0101d4108034030403500142203d003005c0400b0038074400d40d0000341001469500803c8000b01c40900316110b40c0c090560a54440b00300c0c82c1c1a1100c45e41ca12030b900c4003d007007000001d9600c880728440d42d0240031644040050ba07a8074202070711030315501c8410080c164468004c483c00c907400f96000142c0441292603d040003001640d0390385805070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 605337077 1250 605335827 605335831
    0x1060206101a071a04030f0c08090405092a011209150c0203040909110a1502030a080919050307060f0506010e0f030c0d0c15090e040f14030d0e1011040e 67
    0x4a00c4003407140d040020340840100180b00b00601134030302c030341c64035040003000b41d103841010b903040c000e1881041010a1040c070031251600015103010610381c854803401440d1802c8020881481080c824812400c203111003072901c000301c0300342d0362034000d92009159802120000c160040100c0b000c0b08056003100d503280c10192011100e40180c0e428181d4440c072500030365040910455007620580740003541031524006c0403000d0506641078400030100d101020359240b04904038041406140400a5000942040464150285042c400d08180b0a80ca00380780d07a078001102c2100e2007400c10386015104500b40c03150a100707981c160f43e4a51140100018400c1d011641007419400d4003400440400036103c4406107981640700f1280e0303085031403600700d400a2601c482d001d80001c00c04004400c01007448903c00198001e500001c0428440d000d80c40c040714016102d080c0d0314124000464034464049050340f14142ca881403006890000c20054804070456a014508004440092209001c410341e8046029 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 605338327 1250 605337077 605337119
    0xf09010905190e0312090d05042d03060c0206090610120212070b040302130501030302030d051f0e090106140d080c1501030c180b010e04050703060504090507030303050106020610 78
    0x71200d5840c4505620943e10f5034907a0180b503910000700f600b0900b2101c181c00742d024015070083c01c901c0700030f060001c1c0a03106a11403030054080301c03809052540324a9500e8a0304402d10782910440c5981c2e4a850b1015001c10b001179405400f40c2000201c500f000810800e00c070f140702e0007144040a0034621030441403c8d4515050b40c02443c00c0d031824006072800c224007000740419640d596240c926520421028043d0314034600046401c1400400000380c000042d506072035072604002c0741513aa03c12404c80307100c0c1c3c80300103a00c0b071550500c0300107040c991050b100c500905040b0000d01010392078030705180031584001410b88d0800ad094212801086450000d030541d08071240569062228503045501a1031007a0003e5071180700400c004c2001101c2d10101444a0301e0608040c0150801ca400280030240540351310b0340200d454400244920b44264001c40180c0001001002110200d040442c0d5540f40d030701007100801d203418008142c1d103000060052240680384443c2c2541400c00e1400e50348116606000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 605339577 1250 605338327 605338351
    0x3060626072f060612060f040204090503070c030c0b040b09060a0509031e010c0f05090d03090b070c1d0402030d03180206030a0507030f15060813060222050f09010905 73
    0x416000c001c04649251001940480688880e950320009003400f20103030800d481680c80b4024840008000310f44c1a034080185055650035640300e0010034064246050f005050f400000f40b118100b0201041c507a040e240580c90803100b0f140ca0f0714071103d003403259006980044100344200c0240d458060010403030050079203005c90a01802c01d011903d05105140b0b601c1540c8a880310a03500180c1c2440b074002000707802e1400e4002c00040d5603000c0c1141c0f1852145600030381000e80300d08107040c010180000201448000c2c4c0350342c1e8501e4100885062198090502c1920903407407035a0004000c2c181540c040c980003000b8150031100500e0960042010100f2149100904010b820261f695003011750f201e91400d26000ca40c514213014010100e80403e02d00045062902860050509441d03900505846650522000c26110300b624090380610354540184124000248081c0c040c0f03001035092032080301c1c443c10a80035512a400c0141c4044040c5415400c14420b00040007d1648c035000150004411058 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 605340827 1250 605339577 605339597
    0x50a0b0f0d09081b010c0f180f270b03030406050c0712060e010b19092301090207020111010b0f062109010e0d09080616020f0d0306060306062607 64
    0x1004003070320396a010540d80310324003050701d800e00f40011181c809504c0200c4004c1014103003280b800350440c4001004141007000c00c008030a1480c10a0101c1d102030f204c22781c038480d00305542d6048541c107003c030585517221000c00075141c00c0c543d40c85402003164600c80240a1801d090500104482d01e030080d4410311240e204450b40050010f14041c0c1003001c040c040c0b10007040510392800a5400d40c0e20030702800c1c1c01960b020341c814203000d80d101400400d0304c81648020a2580302d2820010005403070790300440910004000004440450380d0083c070030f09100380c07036185401085105460032190710342100e81d0487c008151903501490b01e60001c1c801c21510b103e000984d81d043d4000380c10100c00403104803071280e550308240c122101c0108603581c0d0300c5e402d40c5030122440e8109403640380c8446002c3c15950000b1002c00c25002424000d05c20810081d0103001100c889031940720004010b0117441c4100000309142c0720340403804a100b601c00074860f5502c0310741b03000c10400003070500070b1618000b88114100812651 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 605342077 1250 605340827 605340847
    0x70e04080f0a080615070506010302040509030705011a10080f04030c171c0513020d290708010608072a03090902160c0b090a030605070212030a020c0c0a050a0b0f 71
    0x10344a03000595650b4030281c1340240500c10b03070000c3c1041c0030080000501042002610026a0f68190780c0d040e140800c0350340f03628042038518042c0480080055003080410b200c004030124074418a070000302c80c026030700b85580c21b0544c1c6002056a080f02d04240500000f00468020418901c07502c0c417418406010136101c4c030f0032000581210b001d88a983d8615407034600f01e110140103041e0000d118160000003044203500180264030805001481980c81e0580003500050042000c1180707109451852181d1900440041180c4402d01809011405040100d00801e12458036900c1c42e194210341c0800107400c003941c202c45034103810320840c01c00a00380070104481e140c03400644003140f00d200c040c0301c0c103e0a5240c0707800c030380c1101d80188001e1181800100361a6403981c5200e400c03282c00401c005065101e40300704070705290340c20a02901c0461700200344540320600ea8010008030070300300d00f07903034038680c1d01070800207811041e2080700e5111401500920000c0c06801c0108020250b03604114070f0314400e44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 605343327 1250 605342077 605342107
    0x50108280c06120f0501060504031e050703290c04050d11060c03040303031118060315060307121506020d030216050109060c090b030412030b210609070512070e0408 72
    0x500000c0c000f99208012240b42000f5009088a000d00040c0a01c000d43c14a038009040b801a40300140c071610a8000000308000486070760660203420006851003a5100d061403600e070907100c01c410380320b03444580a080300d503c02d030f024450159240d00b408030315240c44c100c10002d035103001c2e000658280c1e40e9900520280c0e0346000007048024500d50145071918a1410007804039103101080152010080008240d5400219a0300100c844100d03265601c2c0d8503505620100307040e42d2245150403802c004180b00d00650421100060840e401c082400707282200c5811040a109520400002d0381c040402e000340c072030003900681032407210b0201c240f1524501c1c1d01d810303080d80c0f020b42c008ea07441c5680c0e0094002c52580311890380080c1003201030440c658100741c3d5803003a02050030219001050740e18541c0b4080d955812480b040aa8100d04810110302403405005841340c02c00e46a0941c14422100000365904002040d084203c2c51a405803404600e000700c07803040b902005004442c4000101311000241000e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 605344577 1250 605343327 605343329
    0x2060c07060801050a0b0f0417030d0609090b090a050c1c0f0807060e0a0f02041112090c040c11030405150c030d0606020d030902101419020606030c0103050108280c 72
    0x981e540b440194074000900a500625410a04140c1d40810030000d0301d204490841d07044411426002041d90445214a81035024060441da5650300f03021340069040a0303900405100c03401100d8001e642c0e122109583d07030b00c544110000f4032a4120703480b0101d0304e16140800c2c1202c5950091854103024041e1307254005540c0340e0600700c071100c2012035450180200c9206088140341c7c05402080951a036468500d40017010b554024071a40c0c44014011402c0d1001d4203a514404406514400c43e00348044500d80754102d50b000f46010340d24261030086850b11819a5a40c242c00040c040c2d89814281014031240245400800c1903250003002032142070f0700300b0002043d03162182e010005006041a10083c20803110502410406003000840c0f0701699804000000b516600e003001e120409221030a64901d0145003260401020310040c031002c1d10340c0100e2460300c10002142601c0000c083d5000660443d842800307210340a41c41b11030030703136401c40200030707500940081078152410f4440b1030b90340d5085030455 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 605345827 1250 605344577 605344589
    0xf03090203070f12120c0201021c02030f0f0c010e032505151314030307123902060a020c0c0904140106030f02030c22020906040e1618031e02060c07 65
    0x40b452213401c2c00740700e000000c80d46480d460300d41140708007500002e45e200d0011244045c004040782440425034000c004641e0041ea12541458445105014400540c1c001480181081d400c2910701c080121012041350402000450807062185201c06100d40c0c40c4140c043c121001d200c0d03102c588410030940b07152217101700303000303001400e404006290500315609490600c201592040c0144544650007503209448510b6505c1c00140c6048400e11099899a84040f1259140d9050401281c01658903011000e104501e4088419076207481d201401240700347d07034a030320441d04000707500f0b10b0300e01e030507001d07640c0060040024140c1c00144000040c02c58089a00031905403030400100f00c00c41c1800c3c800440420b004460013050f0611801d00d0301d10201698080d15400755000428010365615541a54081d0500c3c00058a032032501649180d0354044100c00c20000c40c114001c43c20481a02940c14415698041c00701c0d41d0640d001e480e4200c4c40081d03488102d9221505001e26111908100103000c02400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 605347077 1250 605345827 605345849
    0x1180b01020307021e100f020a030c031b060507031103161809060e0612030315220e01061a0c032203050303101806030302061305031308031c09030f03090203070f 71
    0x1204400c2211840b03101d200718082c0311401d00c540f0407d940111764041041c0c0c01d410500c690813018601228081d040d92a09004410368030100001d10603964019480740d261074030104400d520820f8040b0190004039600c035140035540c01e1561605202c0c114226070041d01c0e00031400082c6d00c0d82004030a480e441c0e0406050b00ca000d00400901d1710f06404889413145200015500c0e60800024a813029210781d02541c0c0581c1c201408040070703440082040c0005115900b0130011a05031141003406010944a07100c143c0320b0101b90b840144140b9022660b19010182c000c1d89426804a641300703c1c4144418840180800342c42c001000c103105000440c414003c100304c1440039410046018404c2c0f8102c80c410070401d20b058824000a900050200d070800d00d1020348083c0301076185041855480b0b4100002030700000060002042440000035100000a8450303103040304044491210442c0c0594034068002034a003900018100c0c025402414424006800e94030f41d607407101d20100305150551f20004482d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 605348327 1250 605347077 605347129
    0x50120090901120308042003010e03130506041508090703200108072a08070210020a03020f1203150a030629190e0a1b09081501180b0102030702 63
    0x301e0403580042c0034100c0d1035004091000303d03031030081081e00c00410080c007601000c14406103000b07850f003d86128000c001c1c0203010424034410119241e810ac034a00c1103445c4000301c03012a0350b240a10030780c0d0035145200400411030781c12840c1114001c1001e40706090034011500080007180000403070540c054042d519285007007036450001002c0220061a030b4041044101c100d44000c449200300c1d20400d8009050403441c203400d424480321a01c00d25000070361016420080010311600403d40d400780c0e90017030b001e07900c41c00f490849081e03c544611408000d2091b04100094040c249400116005400542404200340d1030baa5407008640b0321201c0b171080500442e548a0102130386500d42011038030161340e80d42d08100c003050045044150ac1c000c0c0d031442c00c2d0860008032800402c2c1c0c0072594000480441000e001a00c80014200443c54080c0c3c0c40140507401c04d0b464480003401d0100c1c100c664400301c201d4dd1942200000004240b080c006a045000c10481c5102580d1600c4900c3c95441590f09285009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 605349577 1250 605348327 605348329
    0x3032d010b07150506010f030b061b010501030507060c0b0604181203060f060302090f0405180303190c0e0a0b0901110709150e0c0306010c0204020c0118050d0905031905012009 77
    0xc0f00e070000c10005200d04042c01c120321a64000041c9515403441e04000c130781945410b0000c2c80f240605110940114003041c0c1340d0386260300c1504024100c1e40100c0540c1c4416441d100c04442c00003000e14040c00c042241c5000c100c41c0c0c103055012078148821000f800d0082c4c111980c40e121030b108408242000651200d005110030190146044020100b9080443c80c0407035003001318100b1400e00401911a60755400051742c0c4001d00712507815903034800703429244c2c0d914094600001d41850b0320580c004451801d00f11540c0c60380218595103510400a11050502d4a0024048125800380000724100456142100440042000300b58040d055a5002044c0a010440741f1003c158040d8001002d06211030309104e071400b10441100c1d0461030a1a04900d40c0341d4500124002c2c0c490201100c0e03843d880d0540040c0c4807030a01d1080505248200b06480700034030301c11b0040358000118051654141c004040c80c2208000700d086410565104100114041d40701c00c010030050021841c08001c43c1d04001600052 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 605350827 1250 605349577 605349593
    0x180b0f0f0313110102070609090e030f0c030301030501110301050315090c18010513050f1f0312080403110105150904110a030302071d0708010501050a02070902040f140405060303032d010b07 83
    0x14072405e10040c00c0c102c3c40c00000600d0303490907104400c01c45994581003e01c44901707108aa00e000b0700660120380c2c42c0c0b40d40600a95a074001d105c1610305510303040d90841c0000158045a0407107030010b0082004034944a0311070516036010380003017424405c13500224210f07161780f503c640140c0c40030f031040142d561600050041400c04041d0045c03105e45440108180740c4925505582c1040101c150400c4400740c2c1c148030601c000c3c407034001820500400c4108540076620882c0c02d40f15a00c00e81c4c5401c0b101c2141c1c07241f036003641c00690340c504007401802d52030001802d02290859100c0e00030300a0740f4402c0b8414011401c800101d410a60058008000c1401940d410056015614141c00140101e41c50481341c003d19a04060040c14100080090702d019030754804c100c1400030f40b500c6c2c242150366075614643c1d41d1141548c0d2094074a800b4164042100b5842c00303103c2c807803064001802440ca1a40d030243c8610088280e420321004068000303041440d242c071402d82d400d001c0c1c054079106660341c459509180340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 605352077 1250 605350827 605350853
    0x30f0612030813031b030e03030415030e0f0601050420030a0603020910120f290901060801020f0313150501080604060e06090c010305091f09060c180b0f0f0313 70
    0x351006283c203441c000643d110000c0140400c140b440440103d81c545021a1280c2c034082e003040e898807001c200440c01440304060000446010340b4104282128080741c1511611566020b011a81000c00100510b0401c1c6c0c020f0312200c1a01150350381c1d103d1160150b0600303600255003924061359550424001c500b024040340d0b4000c0ca045900c0e440742132800000090020390940c00901e010b4001c8101ca00704880028200035200744050740641d14000743c50b5007460510111501400c0c2c0d82010b20010b9503507418400c1b0b8020000e0310b407041e45180d861071149c90b00c0f2030400d04220b803a1240c20601c1e40019546200e0540a000c4c010060401402c3c103007000c0c070503180f814041401641000013803000741400024901c05034402070802040d507039103400210b130400b0301c900500f11404443e021005e038400d4580e80308010f5540301e00002c00c0036a8101c14203c0d0201d08a401d0010074248804041c04000e403803401804e881050144c03a580f400c030b0100d0a0920540003640c030002501660102507041000c2044a29 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 605353327 1250 605352077 605352091
    0x906031027080306031216032a1109100b04090c02070305100f06050f0310091401140412091512061a090f03190b10080d020d0212070206040e07030f06120308 69
    0x1d040c03651380b0b0040e1100160a400007402d10010090150003627408a504114100c81421000310070450b40c200350368020604c01c0d00070701c42c965000004a80329485a02c1704243d40469580b0b03400e05003803000d544001c1140310308217025403103401c1c800400140d041103440b041d1440c1d910089031807100c88070101d041d2030240d08880c1c0304075086c0c450010142c0340052107180c4e1034115000030a4800303090400d00d0141c5007a10142400d035007400382e500102e1240710302040c002c038807415900c411800c00e00000c40d80a9068000c082400c083c070520800754034410024071055a142038400100340703230b070303809101c825482201d410101954082007221030340c601480c02100080c81a0043e1218000034445501142212440205055407081c0807582907080d20280c0005403010300211200260500e8010395144c0198042000500c9042c000031202c5256109480d40070b64068030365424181030030402d0301082d000400d103008241d584c1c01003080884040c0038030701c020102d025403a0f0000c082e07814010043e58008041ca = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 605354577 1250 605353327 605353363
    0x2120304030f050f070f0b0706150308030c040815090604080307030f062709080906070c0b0406110610080a02010f02100501091a030a08030c07020a15080105010e090603102708030603 80
    0x10031100803540201c80e0040d5008100043e003104ae003c41713100704103040e040a0244a0044104445c60754000d0007003080c1c1c1c1c00f91080381e628003078001503030a81c001e0880d00101d841e0820b00115000a00d0704000d55080b00a50802040c10042d10300c0480071135500340d1049003200b205031400c121041d0070b54819040c40e0010003050000e10a00c0d122101c05200d5001294011315001a0340000d00c0112803000000c0c100341101603907603960f12003006004e0001589007c44901444001c11141006c24100314121000c03200603002400c000e070015201000c44246040c194000c20502450300d009600c10745028080a100000309040048480c900c0032104200030b41c0a1b03802000d07044041522541900d901003414000c081d92007080c0d00c0410700c581c0f0140c0c400c9406002100c1c1a039801608400828160b0b2801c2e0385414101215608002c0c3c034040a9440c0c0e505034001c00d480c41d410701807941100341064280e0b00b00184902400541352a07a640c17418043d60304800c0402885000e00e41030045500b49080030a030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 605355827 1250 605354577 605354579
    0x40807031707051603150510060813060f060f05120a06051012030809060c0a08060d02030111040f182901020f0a0614090307030f0302030424020a030c02030f040302120304030f050f070f 81
    0x40c01c41303000501c0c0200401e100b00080003c0092440b003104be5612035010f101417003c80c03ca00791490180c030300341c02026040743d0801000305031400c1c015081e580a0078080002e0014a00548541d0010b00025148040e0320401c41008034441644d000024807052203543c0b05640b43ca00720b035040341000d0000d48101c5002c0010403500c2480e5078071601250700800115a02e080d0280076200203030040c43c07070310180000f0b1140440e00280c0c0e40780d4003440604032960008031040c5a002d02400d40e0443c0c840e103003500300701030038804112819071040c0500d0300c41c86018011103e82d42c0d8601d44003440d0800f0400111152a200c108001000c103c903041207410040c014003e60900340c007540d000d08280110350b480c200b003550100c0080c040c8080c2d10303811004200c800520140d80314a64041001a40c0700240e0300300400c0c148451084031610002c2241c0226058031850707810a82194200812249507002c6141640310a00c030200218505105c400c141c10302c80c80c000c2801c1051050350a05000c10380e40f140a00c034203e040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 605357077 1250 605355827 605355841
    0x307120e15130e0f2202010516060b090a23060907140d061d070810050d0501020c0303070f021b0a170a0c08031305060408070317070516031505 63
    0x2544a0300501c66490054903200c0c45142d1900b400200d60000581c40c0048003402076040c00e08004600411144088280b80c00d0309150041041140da1340003030010b05c00300a480e210007490000401c24034440e4201107000c20b02c180c0040d003000f40a85003401d0300c50340c0340c1020101140140501811114500c80305015141500000716034030720090420007400f980780d1884180294100481d80c030b40035580c0c410010b03d82c8409040028000b0030915140304503e007004608503034041c004540c49445000105a013060605003030000c6588142011a0159024084d650450000b480614480d100a41c2c441c0140c4070301500c000e282c1031201e140141c0e03501072106510030301d40310f405089041d40c008030ba95101f52046000c5c40c41ca8424071800c060045034001c000401c04010200051100281880540000544520030400e00d44514401d50304541c0c010002080028080d40c0020800c120305884682065000c1d1200b5061541d10240c0c3c0e0020441d141e41070041003031541b108000c0d00c0d00035000b08a9850402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 605358327 1250 605357077 605357089
    0xd0f05040f0813030b0106020d0305090c0f060a110a0614060d0506060d0c030f20010e06071b1706070306091b0e12012309030c120901030f02030403020307120e 70
    0x60041d140d40c0000645002408003c00c081c1c004540c02602e4181e1580d40d80c40c02902c038a2030ba43c4410000307040401044c462000081d0440d52908020a091890510b001c204805603002c00004000d204030643d21400d40302c03007030100c00741d030324011b44012464000801081400c0900280154491581c03540150b002c0340001480b02d5000000b51207140094040741003c4d00c0c181d841d03910080c02c0c94043c0816100308006007050020211103182d21000c40e542510041d01d034110090035058002000b4008100401d06d401040f03008410405030340c6da0010b40300d0700400c018402c0040480c142e940003506022490358144103e000801c0c80510800444001c0c0424480c2580780c0c6d00c55204101d0111116086680e0b01c4030814031a10004000308020408151710781852590089408501e48084002456400c0040200c03041c007555040603020210240303078000d9040d000300030400d04266480031010700190480c0300441c01503006e13030002c6807a00300070b19115078804250103c0408000100030a860b040d10f0b44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 605359577 1250 605358327 605358353
    0x180608070e0714091903030c06052217040e041407060e150a030e0105090f0c1f14090402070b150a29090d0f02030d02030414040515090c0d0f0504 64
    0x10360700942e91690313050005035044031000c00c0303a1442910054000109600040244141d6214000078065940c885844684440d4405040b42c1000040d503841c00024000c1c0501d44c05102d441a0a141003e4803205900c40254044400321a102102c1c2c4481c407004100700907500c01000c3c545480c030b40b0250044003184803400e5414090044e40b030041035058a4034040e820140c40d411038080204510314003461503d0b5140f40882c4416a240101d82521140341400202440c400403107100715001e8030040e030381c00c8850780382e44040c000c3d01800030311410320303942c0e914001007200c03d00684012600d0f0404001d5140300c8103400c5d040174447c03081810100820702604908600b4400e080d80c030785075004d0381c0300c024903414420101c01c5980181034034405000c2000c9081440c440a000740c1c100e4a92404074041a40d40c2d2056005045800701600e6080c28030b86419004568060964007800704846a548040f8481c08000d03a8102d04084002c00c020f000c0080324800d0502060f10a0000c0c8024185a04c07910710340614 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 605360827 1250 605359577 605359607
    0x20c030409110720040b0108060906062a030315091512010204030b040f060b15030a180b0f07030f0c090e04060b120106061407050c01080a06180608070e07 68
    0x2030340c10a0701807003542820380700d0054000c039607071000d000c03614140c04001c0d44c00ca050610607483c1c02c07140c601d25445001074500c2943c0162008407144c41d04002c000c00ba4010502c1a03070000b11f110b08110b01a50707091000381150750f11100441e241d042003e50107a102000d080c8107802044040304001ca40c640c207220a6001500c203840c44030041050444050283c41190006040c0321140000c4c4030411941103900000180100c90420048041104008012202020500002030240b01041408110f0790120304010700a01901d10740003480c0d9100c021002d02168410b500011840803c0001034042c000c030303420200038000400c1605210355000d081c00c5d80501030b280c6048540070004040002907401002e0a4030018403150103203060f88845030203443d142c020000003641124606c402265842c055600e0303070b1b60040190510f0040e801c011564524001d0550019684501000030300c0c2c60590328858030b034043d0f01d00200301d550500628502d03141c0b450740800400c603002010480126446502c1810b038800b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 605362077 1250 605360827 605360831
    0x6170402090c0c1212090601030c0905150d06140127020c0f0304030b011d01030816240e0c06030408120406020d110307120c02060105061b07150909020c030409 70
    0x5660500c40c6082c02900751160813441201c2000d00c2d6402054040c08450300e44220b0740150b5903440c55201d4440d0020b1000a0010b0f48140b003e10000c515500100e60020030800c0a0400e1103042e000030b4540d07240da986c20b60340d444d9075120048200240c0d031020f901501c1c9500b0030036690f08034450140100f07804501000c1040d64086015801c080d030901c40105950005001c603911551a820b001d20004002c0c401d0716010001003024520000e48000f00e18100ca80000301142442034a003540012954014021a1080962500003c86090020540490301e860300000100a110982854641403407450300d0f034480c4a007401000700041010003250030b2050084401c41e407a885030700e408006130086503441c1c000d450900c44149400d003459405907103c0e020a42d21295510520351942049600642071078005801000c014082401d00400a0a00c00c00e502465000700c5021100282068900e03001104981350b02034505884551201c18440500480e102c01c524190014000c0d941d03c2c82203100b50f940e120313 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 605363327 1250 605362077 605362081
    0x120a0e0f0d1d060a20071508060303160501050106030b0904121416030f08060f01090603110f0d02070215030f0105010c02040e030313020a1d060f1c15060617040209 72
    0x45030310219203404007000c0d24075500d40307100f10009490000050356028010007805a54505c6104c009080b8049a00c0a448840c8103007012404955403880100180e070184800c115082c0e200040c1c0a4002d143c3d80a5000090294104000201540c1a801405128001500901001c50065502c0c5041c5083e5030400701c2115003016240517490050845522140440c001e2201c141600311144d020717214066526403a8070340d508400c00c100704541c00c1400d4000703064180d0511500740282c0c0a0007a20700028889410b0000c1d84442170300a074406044040000d80100e202e60440c1094a41c0c4407811100505813803e40c40c040402840c044014410241003050701d0f0b8200e000d5444035801200920041e0094079581c1c81d050404605061b10181e049018042040c80051140c01d9001c092040300a00c003070268958485104101840000303130420b60b0320503081d03048071240310b29494080440a1060041001744001042c50008440050b400724084c08041d05e0080400c020f49540c00e507025a044485000c15 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 605364577 1250 605363327 605363357
    0xb18121207060209090c0705061f05030304032a1508070507080403050a02180106050f0309030c03040e070810030c05060a020a0b070c05060a0e210708120a0e0f0d 71
    0x2000351800c1034440d40001510014014250000c1041640c1076564544646640301c0c2c00b0318600c00c80c03d016085800810100e4540301c0901d80001c0381081100c0c03030741d40164a6000003411640a81e10860b0110b4120450110194041600190000850079854111460036030780c040002da001d100760042100e4000001e400c58000d0055440403a0050003181d21243c481c609180c1d03e00c840d64050344a0348042d0200340081c032110400740e050342c90940d10700e0f0070040c58881d440d585400180c0f44200c0b500080c003501c07500c94800c1002d4070041400005c18603075800c041d1000340c03680c14041c00d42c010b43c5140c14001d00108010500b41c008403030056410540d81c20140c10200c2c100703900428010040d05081c000d0022890740961041c0700b0328050015030700c0f035880b80c2218208072101c180c81d800d0b96401030301c07890a41202030148222900614000903103400c3d040d503140d000b2540030089004001d1401c3c41401003400bc54803800709461301040c000e04030000144501c035900c003840c2103d171040150300d065140d10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 605365827 1250 605364577 605364583
    0x60b040f0b160f0b04020103050a2a05210f0a0e030304240903030b01030c0c0b1506190c151a0909010e0102070f02041b1b0303140a0b03070b1812 64
    0x100d0703500107101c076a5420851414001d13600b02920180e00007070074100071602015451013003a00d002c00100c3c060440d10400d000000d10721840781914001d1040a000c0d02808400c41d12030702d00e89640d440705000381c62800b60070b00c030030805000c0c01e910040792800c8035500041200000f2070f0f42090300146195421264903800c0a440e07045000311041c0c5a08040d4480c040541541110407c3c40c801d0300c050003010000c034400c440302c07820a00e010b094003c60340c000c02d11914910001900406000e0501441d10025021450003d080d0780c10200000c0c15102a803018411100125003038480d9001e410310107210002000c1c1e03120b1404142d4988101000e001044051100b540300d0000500920000e5403100858104400e4000350458264040e90030300c51840806109070a40d01d020341081d480b424142d407612641048aa2440d035400c900741659014010104104c0000182c031415031484040b84c6154804141824400b403079112606e0148180441091100301c00d0900c0c54951342924049466068400350920b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 605367077 1250 605365827 605365867
    0x30b0f03030a0309020108150a030b0711070602070f05090903190e0a1e140603190906050f0603120c100906150e0405060907050112051b0408030409060b040f0b 70
    0x35140c440000d418042c1034042e006503494070f000740c0b12003a1035681c51240517141103907526010780c1704240c80018400512482121500135003c0e242c4a4424109928420725010880d0000340150b40b10903400c00141d0048403620000e000191110a8542811020359540c2e0045040c2c0d210b8502c404070000324064480e41c0b4461081000402e0610901c0e56000e01c41d034094800d0f540903941105815002c5120b03410403a070600900400b82160345595140e8003441c000d400c0c00003841241030303124012500032500500520703001d503490f00e442d210079080c49000c140c80c04817889000241c0010a10011060300e4022a02148000c440d00c008115180b03d803505400402d22050301840c600d03007503030021a000c1d8011004070705c15441141290616101c1000055580501d4461103000440307800840c01070300c40c15004070340c11050a10490f40c1c00660300d19020000d80003500b128105500105040042030385a0083ca0300030800c20380b0303442c07400d4204551050701402c40d0181c008003800c0007030860101403503003443d14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 605368327 1250 605367077 605367079
    0x5240105010c02150a050406021213030312180326010302150a09030b090a0318050f040f020d05160f0e06070201080405160902040e090d2a02060c01020415081006030b0f 74
    0x182e5407505c0e50344c0500300b07410130b0050700010312460f400f8201034010501212600c00504029900a6207141e4003103e080c0003141640c0c0055807a064540e11854018141d009402c1c82074072003505850a0b41d11b01c20150303e00701c40340045d03800303c00300400151711000384085545800400705983c62031002030507a462411035000622000d0f4580070044004ac0100c0e910300301501ca9560b90008101540da4818810400c2c017829174454038403040781c031052a10344e100195034007034080003504140c2c400034054215001295141c0d031101038041c02102d01c42c2c0c0150b01c0038414501d0700f84907002000399008a0240d0142c108000e040c840002c0100301804810051262980c0507101810311f00c86d150462031000e90068417512000a04503030100da080f14001c90304100c500701c10350b25a2070790480d486107281d0f0000450680d40120901003440d4025031136660050440c04068000965140d14044901c0200b000702c0d5041c01c20480e4500901c00202542c4004a044510398500402c900401d800003a60f141c83c402c40403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 605369577 1250 605368327 605368369
    0x9010e030a05010e1203042a150f0809010c02060408220f05040f0212040f02220e06090307050d030c03150602060f01060e01050405130f0203010f0305240105010c02 72
    0x907010000150446445506940d0686005603008004881c1500050364020708200040d52178001c65181c00010304059050324401582c1d19070f5460405c00f2004032150300710001070282004041c00e5800c522b450b134211103c18001c208000705140029200c2e040640018001e0304001078400c0c1c0c00403910080e88181490710a04010039030b54240c1c03548025141e10a103409a410203140c4026500a4400d5079040c0c2140c01c0a0920b907996691080c0107500700110482c0e00c00880340c4159076107456031b240e071039a118000c00c00203118a041c6180300c0c50f04100401088407540b040100c0d200081300411001c0303661500e81000308150b01e5540d8180c000d40791000034041e0781c07a462400040e40a5000030020b0181c13410a200c1c10307180c0d8945000704c4030300701801419404140b0800040191b42042641c120200e803090070001030b12a5500c031020300ba80e0007030b440041c24038841c0e0014014880248065200300d8412070007840d80c01d0380d285907080382040510600d8103205d0f1162045c41507480c4d00d500d040307203001c81170a0307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 605370827 1250 605369577 605369593
    0x203010608091501030b13260403031106010b0f07051c0509090601030b0102120c12130e07080609010b0901110a120e0a1d072d140310030809010e03 65
    0x2400031000b1641d1110a21400d09031030600380b682d448041c10b0300e400c2051034600c0d40d00e030003400f0311303000144004580c5650314a807500340303205402c001c092440c09041c001c503986c0c0f4030310300300101180c45803072400d80640c200c4001001000102421240300041c41003507941c0720031490800b5030602d051030120120407031351408070802c81984400248154035044035440c42c151200001101194084501c40d405a4084080360400c450908013a0035402c0000c0e00711010180e200494070000d81050310f4800401c80000310520100c40da00103540d6000351a07103030410030303894400d0016141e01c13810301ca0540110000520492144d20401e12001c3c184c852404072411070813603150007011180319120000028100c0a022070311031030041003040440300a69003001d504005600340c0000314002034444011701c95407103040402030b401c0281d1411281c42d071600d201c14120b61548054041e510144081007031107410020400c40100c25410501525009110103484440200042e1070302c030b42c0d41c1401e50f40342c45030800d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 605372077 1250 605370827 605370839
    0xa0c120203130b01091a120309180a0c360801140402120c0117070912060e0705060a0512090c0613051201020c0a03030b130f0506040b010203040602030702150409020301 74
    0xc12200002e1183d0b14204941ea40c9209007000c0f5101c0b07103a181001003070841d0300301107031400c0d4510201043c18030003940e2804c03903030b14000740480c04410b50140350000468100f001e05452031250100e0802d403420040c80903880f4051071490342c04111180f00308503540f821881c018095105920b00070780301100080100700240244142c5200049802b24415140c10070030421103e404950790b0011101030712100001c0b40039401000707400000629840800003a0078001034940c01c01c884d00c4140e00d000700030005000342e1008105040c901c0a41081e40184010014800940c0d80502141c1c00711950058010040d00e80045443c189202d542400c0e501c0307100400d00010503007840100070300f00c42c81214409903c41c61f0203606402d034000c0300b1034070519421404051020034025040b04100403c018060310031101c0030802007084034821140c24003629950b03402c105c1c1d5420329102e00b90740c0b800d09000031420f044c50040000d40c0c9204041c8001e00400c1640d8200e912088800d040d034020b420320400542d103139a10341c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 605373327 1250 605372077 605372101
    0x708041a09210c010c1b1701050a0507050307180504110a0206060a03170703091a0c0f0705060a0e0d02130509070b070b0a0209132c0105010e0a0c120203 67
    0xa001d44155580c0041c031004400d1980c1c8012810b086202030005000048015075062000e4030702a119440c03140503903c40e2038502254103020308030001c80740d00c0c10348043c0c02c11800c4900007001d02141600c2c01061000e02c54001c4156503000a49103014603001c0300003800c030f504081244e80020b400508114070044440e103c003020b4903242e0b006a00700c030481e544550400805500c00d110182c04000001429004104a84002c01000340242800740c1415a03c102e200c0c0a00c04e07180d03038540c415070003061030800484240700d40e061401a14000344141800d241c0021124800c07000e555090100214100c14141c99800c0d01812840e0000d0141007841c40d070700360903005044211042096402f89040c08103904200d10b0a480d12143c00080841d4103589a8460500940c01401c115a0050742d141520500400740d00a00340f03000c0b01d00c0d5160250040602c88100d03000999808100740b41d040c8001070002440042e44c1d00d502a440342000328154405401c10303079400c0316880c0040c0c4a54000020000d20b050f800c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 605374577 1250 605373327 605373337
    0x1e01050706052a16060c020f191e0506150111061f0503062a04090e010f060602151609030b0f10061b0615050d0f020906040b0a06050708041a 62
    0x18055070321602c010f040c2001c940c8a0300381e01c540500c4c05040a8030210700306a100b4102000140111024485007040e004d15044403c4a400d04480c8100500820080000800c500750244a20078403041d00c40c42d44c500380c82e17100041528650080301e41c18040d20b070303100b40704c0220b001c00750405903045030410202d900c4250b5443c2448118142103200c0c0010303142000180e240c1302e11104501130a400c0d281615a000c21170700c080900350301d00c509110105540020381301c1d4485c2035259a00001d440320b510001c2c20182c6526510101c195007003c14250101542644503944c04400d4003510300000030303120350640d01c6102070340016100081c203e0410041a91540542b805491064001202c8035954681120074616071030700209514400c050f40c40010320705030443c5060f00d0220700745003002900c80d070101e241c51f564580d041d50301000758000e002c258100400b03669000f841c04d490a2049c20030440225800066620401d81080b000284100c1408101c60603200039002082010b268101c00d100421030035049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 605375827 1250 605374577 605374621
    0x6030212070206061f021e0a060f0506010e0405040f0f050d020105011e060e0a0b0c012f0f1803030d09020f01080412030c12050103030203071a04021e0105070605 71
    0x200d40d010032003850000800701e02c107020040c107444c000c115507000a81e1849010803101c09500c180703c80c1c03503140d03245103c1c1007004201e00401481002401e003800c100b6110400010f9004500c0d1006015199070f02186100f41c80105460203c0d07180c81e9483c000300040340340a0064a6540044601030030090301103103840d1040c00c2c0c2d900038445e41c0d8a6001d6200301e1f168900700c007103d00b2482c14081203961b0041000d4452908014403401881c0c0d942c9000c10b40e036600ca64445401030755070300070b00303482d1300da03e102c058507010740c40c40a0602000b90f0f0740107a041da02c00c41d81d0b5122030682c0070466042c01b80c40e06150344000316000d070689407110305103005200548461345d0200d2040c0c0f03155a1407a959403003040c80510603500091100c3c0356803010f81c0d00364010020031181200f00a4041c4425210110500500303000710302c290b004551301c5810f0304026040685070310084c6404c400b0a0184805a6100d1400360923500007090021030100001c00140c81a00c100e5800525180c1032800304101d0040841c200c11007220 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 605377077 1250 605375827 605375857
    0x203130b070f0e0f0319080a030c050415082802070618020a0302041d070e10080307321603020102010c02070501082a0d05041b030201020307060509070f060302 70
    0x180d8190540c1e210b90200c4841d0009070300c466226119141074404241c860354080c050704d101c0c0d034000344a50400f2040541c1610642c4000a038043c10f80da2512444403c295107141460400e41803540b000e40e04080c1d5070742d00c020000c035803000c500c0f1808904900802c41141000b1140c3c000345d03000102c0041d400c052010355085241041516488038051072450100368003c00c0c6411040c21642000002c0c0f00d48054080000c0040301c1000c01c00c01c1c10843c007030203003101e10400800c0d0720700341176220340840d03598001c0b6409800600941c400210580c00310300e080e644280510b5040e0301c069074454082046070034400310342e100c3c150307545150900c0d1804d1181907031300030b0b4021b014038680c090080e41d40d075102d031190500042c881c200003042c0e0440841c0d20174244d007184004100c051200324003050903420040c500380440d9514814402082910300b21085078002401c1032109013407464001035100d000d1284007606a80e01c540005404e220180039400240070a0204040e180e44c031072100078001e4201c0c150b403441050b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 605378327 1250 605377077 605377081
    0x2010306060807081801021608070b06060f04091109040c031a220f0902060316020c04150b03280b12030310031203140708060120062202040203130b 65
    0x1c0d01c10001e1a104050f241c5a400c034949030074810001e14202c40ea0740280956080c0542c14120b10400307182d0045c0b5025800f5962280c000782400307080d49001810891140c0000c015800d20f0594100039142202e69003900010100100390b00803400c0e01c03d0f2580d607540320303250020103030585805600c9000007000124000400b02036800500080102120000c82c0f154500034180c20388503c1500000c0c900341c401d14000c14030f90343d6540848c1c0c0355082920082c0c042d2540d880c0564150f07604000410030041c0031075052105544c40c46107550500c0c1e282c0a0020701100000020f2124007036401d010450007015a0751014032890702080780c1c014110207074114800e40e80100c0c0c0d105040b030000b0a99020303d2100260003005461540d0b10440d0002d00002c41050544070504039403244200b40186111b44221341703403400030b4900080010109554140080c015694040c00e04009503400100d0a0344000050660002c0d0502008050991581000001c0d401400001004480d5681c9082c07031803007622680c9406482e03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 605379577 1250 605378327 605378339
    0x3050906070e0f04020d140a0c0215070503010509060105090d060510050a0506090f0d0507030605070f0203070308150301060905090a060608030715050a1803020c030c0301140f04050114100302010306 87
    0x80e070b40340100d502800e8030044605034030300355008014411500c200002d8080c10142290318a00382120480d900320307500c0d00d00400003601804526034034a002039400801d45010040508680011700071280105003e20000710240d0160007150303203160707008043d039500c1d2085141034009400101c8140803040940300c1c000806041402c040e40070b0350700c001d0180c0c1c2800220000d22200400f42c00780141e00c500f100f1203c00200c2c80600515010314000c5801190a24140b4405800100041120811540108584000b1a6020812640114051480a9401142500003405800c0f01d800483c50249028240b01ea903810000c2d85414092140e035080c071485650300c5919446e4001d640c0301405074602c007200c2c5040c06845034000d903405420408001403c401c441c04089268007200307030890159001c0071000c12140307010004d1500d601c0040380284a940241143c2c40005200603003803400b00b00844010030b04000c4290801101403500c018038070340c20f14114001c481c40098030311043e4042171503d007000c541 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 605380827 1250 605379577 605379587
    0x50109020f0d0206030109020a05090a06030f060605090d02040f0209030f2103090613051009030507030305011e051c050a082113140a12110f010b030604020915060a0305090607 77
    0x80794000304040d045d60b180c0304900001c0e610507140b40e000c0100410180d545680c4021010f00500801e41e00020340d11a011103c608480d1180c100c2401c2c40014004603000c0d03900d80049946c0140e06031004200000d00c04070b5940640209141c3c3e81d07150045071035102c0c000c1c03000140340140c1203066a44001c1e68036542c00500b45880241d40c0c0c02c0c2560031100000700c1c0860040782c180e0000b03200304202d6081800c030040a40440340c032203000710001240051410289035141c094280505180380701c00041500350b582d185100d19440c0324640c00341a05240440d10400c81c41d000c004800d070840156402c3d00b0b401c2c038104043d940150340d60f4044a02030300c40f030130309144011003a0340706075628014071380000c40e15143c03180801e168001d4800d071480b80c0c09501000421401c502103410055850ba40d64101c03030703014254144100356034014501d038985018a9029a0000b4849801c1901514a03260503203684402e42d0000d9800508950000b400145c500b101d81d90680c0614420043c8600b139503da6256501c2c1158 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 605382077 1250 605380827 605380849
    0x3230705100e19082701020c01020721080d020f070215040302030a0807021f050301170a050309010c020604080f0a11010804020d0605181608010c140d0203070516050109020f 76
    0x49950200c640c9002c61003d144070301540501545269041801d16202a0041c2001300c4003940240703c07a00e0340241301d5804005080400100340050b1200c2d81c204040b180f01c0300c044280507550340b400349044000380104041112041d0f210083d00b50b644520f098030061503640125022802200c25100d107803c10f0544400307440c107680d4002c0103401c81c01c03040c5d150207480760444041a0fa00c41030002c00d0b040b100400201420301103142d500c615403070398034080b06507400524115040d0200d0300154824800a0070200491760003800c24204404002100e001054503401949c03c580303150302c2005224000c00c0c20005210a11500c01c12451000113506801101d2400c0f05841c02900301000c0030a010016a55402c440c0e40030000100d5503551183c2840380d10314141099404001640c0001000d2110b4082802964141d08441c248540b00b0344c0921180c10341c910a8007691081144c0c088041140c85200340c0482d440700250402e0385030708028604015008158480d01244103c041009025060502c02003140d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 605383327 1250 605382077 605382101
    0x50403020d0c0b010308030c090907020105100f06050405100201091217060f03100c030e0a140105180a030f020a060603060b120d0c02010c06090f050d1205010f050d0323070510 77
    0x10704907074078554590036541c1010b0a00d0100040034809c440260710b9040f21a440342c11603500102b070f54240341130010462022500010041c020040081c4122504001110700320b0708240d60045929504080407030040c10707030650040200380b00c3c91010100c60b03805000100b1001c062481c0f6141515094108420111480401601500500180000000240d012003d140f40da42008522900c549414908045401408841ca0100c0d00010340e40c1c0700c1e0900c1100e43c4070880703c0305503d04c00302ca107608690f6000c0449005042001030740240301d28070304c00d115110340315034400402c0c416161a403030003038050444480c2490090741040800e8021b0103000031440401c3c50161208010118a5001110802982141907850f070b600c4009410014031510314410201d4000c1000c2c084424003c2c000070524128001c2400c6506d00303001c0140900849503204904a0700308581e8040c10202c6440d05a41d00080f04e240390f1004505812440c0c1d105480358018048144240e00366000074012403802d4044030694040c0e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 605384577 1250 605383327 605383343
    0x3020a08030d0c052106010c02030f0a0506090309010207050d140d0e01020c01030c050405120f0a060504020a0f05090106032703110c0306040f060b01210b0a0524160f06050403020d0c 80
    0x481c05a802c0244d40d17a41001040c5440c00d4812035a80100703180010000d00c40720203a00c103207110307400d100d0180310460b045103000340030b18901100040000e5462900740600c0c1e1040e81061181c1c02080003140380800145901c80c203840002d00d0551014000c94802c5c1000d502500540701444c0c410345c440e125505850710161501418103050105110a004020345010280d2181c0880340b201020100000c060280c4a42008941c0e0305d018418084000b00f1139100c00c441c0e10035000e05111954070310a1190544100c0e14000441e44912992880781d60010060380710401c501e0403032b900c00e1543c42060003000005080c1103070a50310034141450307030703035602110b02420041d81c03151a41d0004200da0007003001b1850502d400c3c500e0a5041c00440110340301b20101d01046980d40b4404821400d00ca0b407160001c007000c440c94007014100c04000c0f000c0040b2800d0202460900084000c8030003420790040c12000d402c41d0000c41d030701040b440d00b48002d00003a602074001d403203521840c40d03145109005159010340d01840d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 605385827 1250 605384577 605384617
    0x12080f090d02071e030b0f0103030e06131211040e0601050901150c0807050f03030a06030b01060503070804030e15040801050a050a06031208060d0b0a020a2706081003020a08030d0c05 80
    0x4001a12200c8070700620360240c0116000001c41c2c0d034260385501920b0307150031030521f075455403034080c101c41c54600125000c4c2d18244648440c0700c0440f0902c000700c402c103800d080d800c100545000e122030b00002c080542d00a240c140b0100c2419400902103059480035100c0c4403159880e0210405e901c12440c503c0740004002d1010280003070042005010490300c0f401c03c4680341070801281742d0840d00202c480c0c0c000140d4a03c0100280f18042c01c0d01c500610f40c078249a0f16505140c000103021079402071001d814071400b1845081175890301c9240602280c0810781d0301d40c841d911941d05034081c01080c0d480545031420180880c240300315601c41e4004880c1d010320850380d0820894401c1e99203460003409154021103a00d03c40380482e0241c02142e01c500049070006070340d141240806040c00200011108003010300b4548084105c1a4004500030b9944505241078903560702d182403d15212581c00c000e410100000000070081d200001030a600c103240e20003030241c440d60250440d00c0340a1048403020308000d9002d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 605387077 1250 605385827 605385839
    0x2090f090c060906040e090a12050a1d030a0b0108030d062c100b0f09031606080a0216061503171204060e010e010c080105010f1106040206090d12080f090d0207 70
    0x4010018090041c1c52581001e1b62041072058020084602c8495904058205820440c403035000705424400b6081860400309405401411204400c40c0d6956141010b551547c041d50200010305045900100d0580d05685850100b40c8903000701012002d000c1c241580814178000040015548041c1001c021011917160504c07400381c480090024035100e4244900451841100c10061048134001701001e03a4441c001c030107041c900306000365039070703400070441d44180031296000e0045030f04140980d10241c0c07211201040b40d4000090080010150b5203440e0b10f41c06801e503005030712400c483c05107642e05181c550840d00c100d8184151000071a0405031300c800034001030115032228060300c0c459130000460b11007060b80710f400c490381110b80c0004920705a00401466910454051040c5070754609910070329039448215544800c042c00c0244644408682000b0645a01540d2071515401c150019170b05802c1d03540180052030142c0e011004628040f001070b40b8014002034495080c00d80d50700529404e46044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 605388327 1250 605387077 605387089
    0xa17030c0c0706230909011401270f0501050307080604051513290f0409030e0612010303020c010c0f1419050309040e12030f19020406020a02090f090c 66
    0x40010032024400d12040150340800c01045001d001151213480703000c12185071101582090200c00c00041408208001c80b40e11006d000740d0444041883c4054041035000040e2401c2081200000120740e0b038103080c0506a140741140d8040f142083c50b0540b249484000446483c0b104861501c0490484802700c1d5050415500035039003e0140071078400b000b602940000e088040032820322031081d0b00d929002d041c010083c00519048202c4030810341c160042640421108001c042c1a540b081e541c41c17840d1002e25020700d000000c41c6100400300f50b40d869042c0300f4118044800e0005400510600b1501c5040b54021007101030307040d40008080030b029040340e4801c25003400c4580705599a024500482120842c0140100c0c1c406100d0009517851390300b024107100441d4103030100c54074203920049100186400d00e04c110398000c40d1301c2c03810485940d2044a1703107010748901d503055061548000b400040c10341d804184e80d03900711710841d4501c0340354442041c000c4c00b03c1c2c0241d804d00070302d4001030058441881c201c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 605389577 1250 605388327 605388331
    0x21010308070f0213020a0c031e0e150f0a0908070506070c0b1303021e120604080708031305070306020301090b190b0705011418070902040e0117030702090420030a1703 73
    0x28044c49600c1c3d9103120740000e07a003028840306c010030b8000b0700c01c004054001c440c2c1c0000c1015125000148110400004c114031010798005005221031404110001242e000b10348542000c143e1041e61407075030102c010403202c2180300b4001140220b400110300e0b441d10000300d0302100e80000ba4a400305040160403035444e4401c20621070b004512000000058403000075030081403610340d410351001d07120401441454088500b04620035080340c1c080200050002096480c000d4011007065125520314008611030700c00d030140a0300620a140d4004100980303500214184d41c0c60a405102084000040c0000104440620101038684800034010a400e1401801420b40984004100c158ad0000c4120349054190360403000c00301e4008008031141c000300070343d000070100d26500318a0f040c070b858407010f151a0103005424004000b40b90301e404100040082d107440e05c0c1c00400a030014181447e1094240c8020f5040d00020190701030018518038002c10310120081c4c00640d18014084c440085151941c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 605390827 1250 605389577 605389579
    0x41109090c240712050c0f150a05281e020c07051c0f080408072103030c0c050607020c010e04061d0601110f15062d01030204180221010308070f02 64
    0x2040c002600400c002d44c00c00000100203844559640040450990520801c615a80c1c640c2d4000120100207150040c41154040302c640720006682d04c86841e1541204908001d0141c2d180103e075000403055550340c0004411203452040c00c014882c1062803c059005903d0298269000250304104904140c4007100401e030348540d200d41509080d68458145c400254016103148a000c44c0c1801000700030032003000038001c5104075030320703a001982440791a9581801d0040400d03486080324050a406100354403801580203007650450b1500020003960b4441003200b06000681588480c0100d00705403003540e003039400241c24070301c0c1e000c14201000300c2c9000150509040000c4c0440c4c12003120000d0014a03040c8003050b024121025440d81817803041440a848036208810a4017080440a49510a02d002c0b0038001c403d40301008081c00140d0090085a2280300c40c403180142450414255030300510102c0400826003049440c004030500c3c80c15000d0100401e0704104001e60b0380401d803506052070311144 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 605392077 1250 605390827 605390899
    0x1d03031615090302010b04050106030501030f0f030903120e03070e010b04031b05060c0d0201050124030905120a030b01090b0301031112190609020f030d020c1215041109090c 76
    0x5041d50000480300910019030060b555480342c03409504d49806401d0040001e45000e2100d541951a2240701d09800c0d0070081469552a040380201030056071284002c40e0400a0040445100d200c0036000c80701d00365806100340550f00020445240320700f0038038141c840f204802804c141c1540d580c1d0070b00100b50300c45405203003000080001c8586d521801040c04c0301e20b40e0080c001c0320f00c1e03081c000380c295070043c2c01c8403003c801e1558030980c203000600c183e041c00e0b103150b1a010500c1103260500074180904c14044010041d0000f44103200c180d0143c00040742031700c1c06ea80304d070201039444c01207113010b02082c000200709144414070000180380081d00d8100a1841000341c440c0740506d1240100d5106000b10202c811503250324440d4103514020352030000005003503010706601480c07880003d4607203585960326449200039015400d055a400c0182c03030581154144644070a0a140c00c00c29040c0e05402c842ea4401c050f40400114841804aa01e0312034000152134882c081e00c242180044029030621148c00400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 605393327 1250 605392077 605392103
    0x110a0315090614101805060609010f0c061103072007090b130519181a1302120604051227010c0614190903080402040b0f060f0a1d030316 60
    0x4003189a0501882d00307142071000503444c0041401162a00c0e40343e0540c1c41d81b5210801403c0c0d207440d800c60301e44000c01d00c1c20f002030f040d140b00c6c143e544081005016240c1440c1541007914404860001d600404985d00c425800e5540b44e80d120340d00c80c0f402e40d6005800d8002c145c0c2000490295004500b803214028141c41c50058000842030460f542202d1454101e40300c0342078940111400c1c0308114248001c4142580c425880b40c48c0d0100d80c200c03001b000b039050311381440000c0a03000e0301403042e501160b0082040c2d1101c1011081c242d6907140a0321301307840c00d004d608124440c01480004079400480c103c41500301281e00180f025a044c022104900c1c18410a56800800201c0c00e1064600ca00300d0b014107802c16041265076450124900001c610481c1d1501b200070340400d800902c030356030040e41102c004c00c50400f02408540c40082c4184d20640100000c111086030046000c0a05000d01a542e90441800554040050000e105905d602d8040d001084402c0c004582320044416441c01094404050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 605394577 1250 605393327 605393351
    0x90303030903030402041b0f1107091806060b04081e1c0c11010801081009020a0f0803270d14070807060c140c0102071502070b0d0504110a03150906 65
    0x1544100c401c840950000000c02045252501c035042684c010032030400b4426000300c00140c016202c440341d10082c08040700d146500721400700624006040c3c004024081c0b8401c0074407902c905074071500c00700d51003420140017080000707081e020740c2d040f520504010032404170034800000c11400c4000904506d40100349c1d400c1c810030700302400640c14888507030300c000e240c82c11410080d40c40b4041480980c100905003004000c0050f00052460301039165007c0025180541e2000902103440c0b54030507541d20424440004507581c001c00070744481c0d000020340c2c244180343e5180741080c907070300040f140781c0c403500c42c00c800404070301c10002041c21084140d044500d00781d2584865032406180c0c0d808140025224036003141000340c0440400401c200c843c0080190100400020351144110b000e9031080388034070106001ca0714801c00c1158000c01d13900c07030155684d11071000208044c200444e07043e140b2821480e40042d03c3d00b8144d407441c00b102d401414484012505e150194086c002224003902c0c030740c1e12403500d0019 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 605395683 1106 605394577 605394583
    0x1401030b10110705030f010c020d020f03030c0f09040e0706030b090906010b0304031814120a0507050112020906160501051807053d09140112020306060903 68
    0x6070380e925002c0507140820640c0302950600c030300b10300c61840754019405900061915800c0e68031041c0100d00c140da4410030f50240b01241d5004000240307407026100054070110710754645040c039114441d80050145c6800c540d6088580e003040340204a20380c0c00d88100e81d40248103035208900b6180040145845200510a41c80700c40310000002e01094411100c0c0030000201c4012059100d07110031000d0280d50003601d1081c015803007a400f07030103ca10002001d901c902e50280052038464103240c01142e86201c44000300122940a100c89661955894003070000a6141081c2005c0c0002c1801c045094407805001c42d0100380000406101c2031b00e010410301d0543c2d00a8400089180c0c104100780305104010b04866003500003080c660b40b0010100806c00c6904682e0f90719405030645504000d004031080f074901d0780c046031121408020581050300510307800300c0d0007019242045041000700342 = true := by decide +kernel

theorem cover : BRFrame.Cov 605215827 605395683 := by
  have h0 := BRFrame.cov_init 605215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 605215827 ≤ n) (h2 : n < 605395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
