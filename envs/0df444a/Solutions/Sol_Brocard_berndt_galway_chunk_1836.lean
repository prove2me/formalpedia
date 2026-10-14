-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1836
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:51:29.302978+00:00
-- url     : https://prove2.me/submissions/3fc7dd6c-98e3-47fa-be89-786e81701aa0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 330035971 ≤ n < 330215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 330037221 1250 330035971 330035987
    0x1816031502030402010c0803270c03010e030a0c030f0e1005030702010b0a06050a1805030f07051503070f08040201110f010606021005090318131a10020109051c050c0307120f 76
    0xd41a51b42d000b40d20400d444100c0d140c2c1010341404001400307e46007410b40304c500905000c2d01c0380b0881c058044101e0030020142154042600b403000c6400c18404889160f07040700c9810455038040c14400c4c0d4003001d020003120519440890140d1007034107071039a8a940e542c010003131885050030341c000304a810341c0b9508001c102103181c824500099800c0180c044094480c1b401103e4101c03000042c0b00041d6102d50020341818001c1c16928a036a11825080205d45001d0610300136840f0540b0100b451401c11190040c0131083c0400c2040510004102042c1164444d06070444505148407d81e100c54070a08076140c0079000a2240c4401441440103983c0000f0f890b11426000d101c07401c00441c900040360344129110000000020b034400200300c0504040402405111070840e503404801d841c1c24820f0042084031111900050b04582c942201c442c0001c10015044401005c40407210b84080b150700006c03502c91184401007285404003007400f00402a01c04214034204e41c583c2c86038624034804860171110300c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 330038471 1250 330037221 330037223
    0x160503061303030b040617030a0807080408090d081213150c3c020303060a0b04051e0406051e10022107020301060e0403110606040e0307080318160315020304 69
    0x10042601c840019010b0f900c00c0550000c040c00c08221396541c0e80f491750400c4191903202e03140b500f0025030002c040781c0c09400c2d0b039446006818410014141900e511071a40100181c1a0051040709000c5c02408001800c2d03400d101440c55400c03819260241c0b508103420500801150720034a80710350805032114500501000c40e00560710003503800507680d0b41102a42403c00c1050000794410440005515180c41d023101003855500199642d050000270305c060705555a0201d080400c007808144090381d5604000718501d40f071442c19003004d0144030f00150003440a544427550025004d800720f01c100b9203134a00c5191102c003c84082d45081c45607207050380c98020501c0b031448103020320081d022028130100007030131203240044c00020f10306454501041d840c0c8003c2d9416000300d50485e280e864040002c0041d90342c003540664040c0000d04007882000d0750b07800344030802410b00740040002045604034802044901d0700c184200c9096042030f802c0310159410f9070009641c4020f0154150402c002d607802141d00403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 330039721 1250 330038471 330038491
    0x1509050a0b0c07020a08031c18080316020606030c09150406090e1b06161b0e0106030203270d050c0111041509090902060f07080904091b050405010509220b0916050306 73
    0x448c02219a80d0080c1041444080c40d480c040d410f02010802460107180b10302c0100c3c1309000301e91440c400c042d00c5c1540c002c01c560302ca82d020b55290007407510350b04003454103e8815826500748403080d1000601030710003032300210140c501c0d01c4010880110006084403501160503500c6041601c030500340324181c416a6a152941074030411750200254000780400d0020f400a0b2070404190f80341c2604504400303080e40300d8800240c010040c80f001402d5041d40074a042c11501100b8059201e03403a002e5160804100c980051090204a0038543d650070340001600b40c800290440d80d654407210300d1000c9090820b019400548001000314001c2c0e03003441000d0052360020215400e05921400b0820594401c0c0c00490f42c1e24018000400c0301d8456008803000207109151491402c0d90b001480d07640d202196104521590429004001c552500c0114540050340c00700d412031104d150058240a1403107201004141100d50030410103016404182d03051a5400031048182d0169144105036441005990008903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 330040971 1250 330039721 330039757
    0xc1f0e12030301151205070914030303160e03030409020301090c110f0a12031b2c0f060c032b0606050c06240a0b040e0606071509050a0b0c07020a0803 66
    0x804c000da04040d031201129803a1400f41112030141c8070040d50f00640c1c2440204020007028450703c49212040d010318041500110300b1481c10a600e5200d0a0341c0806003011310074082003111080d1024030841d000f52114001c150365a59507591940700034120300c601e45000516403401d0380b81500d0042149840c03240d094004119070191130302c8a540404542609505040d41c8049251180c00f64020084885855440d40c10324180daa000c05000c41c00c0c541c40b2401c081745c640d900644d81f41d582d0b0120000442083e601651606050106c1c5413542c0f1920511114506080c08186c040c00781100c0c1c40c8a800c2000a41400740d82c0c0e5a2400792260302400f40c94203842d41001001031841d0009101c11428490540e40c1071a4460940011a039100941d0b000401044400501030007110311207060150402d00580d40c05182c040941c858050046404851442c816100c15203802403020821800711603a07080340c000325041c24010350002c1036604c900d00032401240d100d032001030030040200940b00f0030443c090684617 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 330042221 1250 330040971 330040979
    0x906062a011a240d060303080703050f06180a022206030b15040501030f09060203011d130203060414070b0307030b281422140c0a050406050c0c1f0e12030301 69
    0x2100303d0b254040d82e52003241c280300c0001a101540035071001175009031a86079050600010003801e950004004c03200e821803a00a21925031101d4800c0c050712035100c5c0c017900c07071903e070a03402c0f001070301c1000e5858403207131403000d68a500303260300400c080100e4820740c50400031106007200b444408000408d80d01d401e0b1805000410055010782c00030b800442002900240d02c40c15550341800b2a00203030008191030313000100c440c06000d0900516500300d044004d0f00417140d07010340d00082e036900e40248001c14800c002079415095160400454014014040c88907889252001d4000d0041803400b540900c5441d40d2072860030650507495607540001480c2101c80b41c51800d01d440205000402c61075680c011426520640d04020b036400351040c50703064004080b50380d05038030b02c0000c3e102d90080e001681414080001c46691334100040724100c5130f0504005464002544815040500441c001604140700c80c00710444800103c1c141c00341ca1030340762a10704400032280e0034001680030840a035a0b0507801000140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 330043471 1250 330042221 330042259
    0xc1506030f070f060509130c020601050f0301021606110c060403050a0807030b01020c010e010203070f06020d0b150a0f0905090405011d0307021e0d0213020322110906062a011a 77
    0x1b0001210141c595085503a043c1c0200c82203e8458401e41c005802a9005000d5072a00100055000c0381c110001e50410b00203030110280c0c4041484e0003020b00740c2e42c11800d0300041c0f032403042e500400348510640b406458a41400750180e84050b01c510300007514600014440e0f4001c4c03003581212041a4003d00400002c68019180401c4907002541076110600c01000001c0000c0030382a05584601c9000d6264200c0d50b0301c1d2000c0e14001c00368a4443c0c0c0b00b40e01c03403400300781c880800e945084c046444c1c6200300613411002503406041540159810040d104c04102c2030140541000210420842d9081d0702803100c048803035101d01030108020f61002c003000c104030403840340341c08403100000e00070003041c01d480300d40d80000e4015940c086124900d540110030020307010440350204420f400c0200c00400c405c000d03943c411152080c101d588a1003094183c0104165403540c1c410b84294010134044805940402e01d07540f42c481186588039000b960031b042240040f5094601104030a6201610070306a04010030010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 330044721 1250 330043471 330043477
    0xb060901232803050705030607050d02090406121212060501090317040f170c090f1311060a0302040806011d2802040b0403030201050601140f0f0c1506030f070f0605 72
    0xc0d6881809498204420001c051803415500305041451401c1451443c0903405c0080582c000c83c46600114100b01c845500001100d0010a19500042c0d8590078100090002c0040381c00c4040d103407049100100c20031007d048000c0c030148035501d4042c2140d0803840c0c013405170303425805814000351070341c0c004000051040c03070400a000003211909040c00e03158088000d02c0798942c0c0c484403502e16540480b15a40b44148142d190345601590f022030070b860240c86400b5207480c058070a035103c5a05401d500248202d822002613246c50080c40f0f0fa650701012340c0010043e40040c09040d100d40035001c000640035814900c2c0364078811940300000d0407a616040401d280440399103640000d4240c8440c003101c00d2141c0d10042015205078029161038505504000703003119402011039060103c1400c3c9038800e45001020b4405000820304203da4407070000c010006107000e00141c1c0d0002c0d01c52840700c3d0040d414000c00d014410303074040e022070f42d0104040031903540d01c040602c6540e048040206080c00424828002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 330045971 1250 330044721 330044789
    0x90109020f0d0c120b10080102030c03060d0807020306010b03010f050315060415030f0506010e0a02131701140124211a100905010f02010204053003160b060901 70
    0x1681201d582d40c5501401303000840342105c94203114400c202c5e01141400080e4090070b0902c000b142540b4200078952228032020748981d225401c1d040c012000c21200034121000f04c0d90180030303582596511680314105810a01a01c3c0801170055004038440c180014240000c83c40e00c80308000c680c942c002800000d1008002100c0c003001d07030b400040082404240742c0c001c000d05c12002810340d50300d400600c00000e00702800001001d80104101c2c40d21030318190344a4260b82d40d0110035a69200066034980c010440d201594529090b064000503000b140100c00104013400703034800c44c4000c0940f820440d12000285404071214031050382040107403420f40c0c403035007540002c0d804c1c0d455644594000a09600960040e040005400b10300c103010b41e50b4070000000201410340029800d2605004c0002d04000c03a01d186500c251040a0240b01869080d880c0e110603155804141c9030b6071041380214202200507910295000c24224000c290760342040e40240e8103d0b0f034254220b5440f40c10f5498012100740c6d40d800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 330047221 1250 330045971 330045983
    0xc0504020322140d0906080f09101d2401090b010c060f021803060610120b0604170625030b0d02061317070b0406080414030301030b040605090109020f0d 67
    0x14041c0307400d198811a0040f40200040400c8041d6850480c0c81d05006044010421800c400304220081d01300300e20303c0c0c0007800c000a031011545c030b034031180b0701d01000d010036501100c1c100803400c5020142403070a0483e0b081e650302900c03c03500300b8030401032000c81042c8500000c484030400401c403400c03050340308003030390340052401051021558070359074240c80c00000703440042503000482c3c0d45010300314549584448400c6c3e0141c10070349004800509003280e40c034400d1041c008a003a10f0004100da40d400104009001440c1a17100ea49490812103800d4071004481070301d03c1601c02103030342e40d0400b171250400c00000491400c0680183d20f011005864010089a002600d2081482c0140e4a05000e0100c201c002400400341a141c100f50722481d001c6485040d09507004180700b444035030070040444096a04608003016140c943d032070003a4003240c5406c1c91004a000c040004410400a03000c0940503078014071062000380c4030008120b00300c44203528000d42c0328103407090403003250801c4094000d600780145 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 330048471 1250 330047221 330047251
    0xc03020c030307110f010305070f050c01180b010303020d0528030b1503070f08060d0204090503041d180d0f0818071203110703030f1808030a02060a0f090c05040203 72
    0x240464a183c0001100319501c4540383c042100d5410301805d000d460100074a814081d0b414000f002030f004480501142c010403200042a004c42042500300c05d0130244101142c0035400c0060403e11034031202800101c3c018000d080f000d62169108130705807291410b035480d41d00c5003107500708102c0c0b0801c03040182d00c60a16448807208007241d0384980c182242c40c2c002c00000c694034a0000d000500c0d14510103580703001e00130010244400754030744060b90b409150381610001a80d0446041a91540c040c6a0050082c44c3c03928101004062025040f0340c080c4000748541d4088015100d03459464100403100400007030218048488c249210f03000c030503040f441000d144000d10451920050910b05181c02c0501e14180000d540030416030300043c8080b450200d90080d007074050a42d81e000f00301c14180da184804210b90003046900d88121611020020884102120798038002d00002940380c2c03501301d5440610616050503c1090501ea01644141b02d0b0f022200b650010b080c40d04000c001c0d00003402c1080511540c0b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 330049721 1250 330048471 330048493
    0x50c0904150f0902040c021b060d0209090c0a030b0108330607030e091005060d051509090a0b0709080723061c0b061312141204260c010c0302 62
    0x81c1c0304240c1005070614000c00c00e500c0780d0041c0001c1c0c6e079000081004542c041c10440300c405517094244d04c2c024034125481a40d508905c400316010b17000701d50030641d10140f440d00307003e070109004005044280310341c0c4003403000c032104c0c0b00152000a821100081e144990b030715852514151441d07901c000300b0500c0c04402d0141111030200781c80703401143c030450200f1402c5200300080e1908640040c1e1045191180e002c82c0c42c1881c0c0495054061855651500e5803500701240840c0807001ca22000c0e00710280000304e5071b191505200c1d80e04c030b544071000e540f550207400106130b507580b2803508c00d819280f401d001007044618190802460300c40345109111441454510011309981c1d940c020070900c5e49901035100058542d524620031074910f21021845070004200e001a4200740103c0e40c000c1340c00c080d151f001e0360340c03950030012600d440443d101c3c80240196921846140d608401330400c0d188032142c101d08408200c01007038140a180e203a48a019403000100b200d8561003040e002070742c28131030300c1668011124 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 330050971 1250 330049721 330049763
    0x6010311040f1104170c060c0c01110703060f0209010e030c013015060801061707050f0d0501031410090c12021f0320070b0601050313080c0f06090a050c0904 69
    0x64102d2100041c0000000b07568142c100705001b0803800448880349091090542e00350750b0300000b41858144040200045281582480600d00940d0042400d101600350070351100025841034480c50f012801020301c201c030038180010300c0018928180c6030140340072008070348041c1f4803460701d000303c04804201c0032000e2a0041070041801c281c05410b00d0100355810030310017a0035043e050700310804112500404074001d0b505036070900e81010b55402c0c00d075034404c0e14000701d00b6244140f00001c0081070501c400081002107006c035803104010250141e030402480c1c0f03d032000a0f03610120001e080040d41c0c21091000c081c10710502a0340c9880180000c400100303500d86e0140100300c00c407501c004607a40310311841f50507110700c803411048008115558601401c585d2900c002032800f603c10381c108030001c0700080461040000007054245c01c04c9100740c60b6942181e200d5a100c0701111120361600802010a0583c0000500040300c127a1010190910360b034076105100e81e98800034415581c1c0d0041400c1c0e0004c0100d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 330052221 1250 330050971 330050977
    0x3060f04051008010e03030a0b03061e0c090d0302070501021b0307090e03120f010303120203071b03140f0304060b0d02010c06270812150a23100503010306050906010311040f11 77
    0x602000610340340d00c8c006410701c0c100c420b69800701e80290040340410070201ca441581d140c1c00a00d2034000700c134644402c3d0f40c0c2c0c805d50060510840d000300c40f000418041c10340000b107040441d0f90176422100d1f00c250040c842c81e520b29050740d80d80c1d01503100300300c20f100740100313078000c090076603011402c80e4101070000000074641401900c0001c292402040107005140c1d000c00454045080b0031005e600d94200aa00108480039278150949024245100c05d41014801c000161510464000e201d0b11904031120101040d4021b03141110f88601d03044e1050111b0526404071034920780c05840c0c20303c00036030a4036040702600f0801410340c0c04011100d2042111100402e010304500c2c040c61107240c03559904003409070054000751141210764401030150009690f00c00c0000c0130f48404c000510306000209550f02c240c1c6110181751540240580312040445034084007442c1200c1c003855090100340c503048aa1034940030b0078040680321841c501d840c12900e040a801c8036031040b600242c00602000094030840382c42d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 330053471 1250 330052221 330052241
    0xd05010b0d06150c0b1e0130030203090907030608100e0d030b240c01050f0916050d0201030e10050a0b0406050102070b0d1d030c07030c090203060f0405100801 70
    0x1404541d40120058910511015180040c2200c100c82e00020010340000c0c400711009082c001500002032015105a05540d07003070105507190303186940c4800e10448254410030001e0060109815225003548621a100403c150503030041c0d072a0440400601140c050300504050a0541b40c00c0009082d41c0304100404801d50340000c0010400c100c0c83c0602d003020a20b00f6001c04041c11320080b40140d41d50002c00b0b003030b0002d401102d61400d90000c00350745401c1c0148180408954039000409c0998044038040910400c07800c0292419034030074144200158600d4018140c20802400a00b801075000c1e901a005200c01d2208642c0000050003084040d91403c450841e00c19840d01c2400c1c1d641e081600664000c1e24090000c1e0002904100c410500740c0114400e00e19041d46801103e0411038041800c4c908127034000c802c0e690303103160f0a070f0880d41da2122840200d4890354080000551403c5c1c80c802d99004440080401060003c14070810019042c09042c40aa100c0748200000d0340000901c42c554041d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 330054721 1250 330053471 330053489
    0x21b091b0714060712150b0307020f0a0501090314071101030b0604180f0b03030a0e09040206070b010e0f0703060e06011116060306030b0a0608030a030504031403011d0601091215020d0501 82
    0x2901d044000103001254600301d030317070415042c51a1710708004101030680f0113540983e141c46489a0301c1d520102d2400d4011080350400e4080d002d8090180308040d042908030900a4542031070440301c1c035001030064440c051001d050032240c251605002e40c440d800191080c14020021402d1549403020f00200101190403850281c0c0d662015449141250040e001007a13801c070059403c01e40000800741800f03229800c418419000040082c0c110740c2c5040035104415000b0320884107560312402e2089105609660100101c1900300000f1505482405600103480c1c0c0280d100c10282c80d01401901d15000d180750b400380b10301902d412060199028284075000342103680d404a2901d25508105a101034081c250080c064180070341401009800821a03000d2502032800044682d501c1c02d04503400740000c2000026a0000000082c2426291a03d00c8902118451200c3d941d00c4103030040d00c04819038421801c400d0020058800031440b0b00004420740c00440c1000341c500201e258901041f210700340c011030a4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 330055971 1250 330054721 330054733
    0x304090926270109031502160305030f0901020424090315150806060303030403050c0c0d030e010807030b13020714070306060810022107030b1e01021b091b0714 70
    0x307000700300b02d007031140d0030450818001100440c00013000d1341d44501004d003208440c0740c078145008075154101c9200f41825181c2184104607860010484d40c829100c0001900c0c190020546100040c800c5400300c46543c0d042c22076030030340302c0225801104020a8102804002040000850b8003046482100544040001441400c0881c40750341d1380b040d03802528144e8040420840d1a0b180001160340003501820002c0e2194480c108032494a03104011154206044042c000201a000554130071201c4003620707201040d9451900c00c07800c45006014566001c20150039068550445900400a0600506040c0781e02d0300842c010074a17000180d80220b1f0151307035420003040714500500140550404142081d49801480c121750b100c52052150f1000350400240301045000380070fa4880244258050003104440b00461a0300c611003002c22043e5015000300c01000580030f1107201c0960f03441d58010700302403c0e07407610060340140c640520b25036104882d003000280302150084a00d0004d40d4089001454 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 330057221 1250 330055971 330055987
    0x70e030a0b011a040311010e0303040f0602010b2e08070c021206092e0f020d050f041202030a021203040606050904080409060f030210030b06130b04050405060d050304090926 76
    0x1103115551003040d40141084c0410701c00915a81c1500c1849403003441c102280c101c86100080c211700c100d500070306022044010000e81280c06411600582c80102c1c1d0303841c140d03401762720300d203100c0ca05601315007900c0600192120100d502a1000c00d42004c454506000c0e403e200358042005942580d2030306000d68441c13000c22141c038100300000d960443c0c5e0100749404180700a45800001d0300c1e48001603810720f07101d107200c090005281e4107580340c9100b451014012030400d20307100045d11200b560155124200c090b034940516000104403200400d150f03004003140d05518078010481c0d00301030800c55456840b10000951503840c05480d90090340030744030040e17441c0d141081d00e034103c0c4e806a00481070881c241c5070400160350703820340c1401d018460303050204040d11b00b8800100a032085042c8520f003e08641400320ba02031001c2c0280098800623542080309840f184100702100d000f96030000c0080d481000140030030b10346500103805c01031044072300700e901000b1003990010801486100064268020407101c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 330058471 1250 330057221 330057239
    0x281e0f060f03060603110a03020d031101020708040915050306010522090c030305030f0a11030103020d05150a0c0210052206060506030708042306071404090c0503091005010b03060108070e030a0b01 86
    0x1440c41c1b10201d45040d10300f840d65010a03a031848045d03000d0f00b40542c0b11025809240f080d01150809940100829611512201413000400c0e00c215030844594000c14041072506000a110341690f000600c90a07001d201c101070424800c912640c10080c0b07a40312904ca20005040c111000702452281d100c0c0c6440e1b181c6150010b51810b0000c042030300c92030814844d000c2803c041411681903a070107031400044828142807041c0351403880411141044001000c02c9041c1503690f004e5032101d00c00f6803c1e940542003501080f0151601a0303034801c03100c1c201303080c012408180142620701c42840f072000030446030b545800140c820b80007280c0d181e020540310380800003045a01d804620b05196007080b4804001140400e0707590b6030a00610704014820300310798080c41800180140c8000b0aa0203006000c5400c2e4060000d010390001d4500070380c248070b0390140010465040c0075081c140c425154510b800c60b942d040045030302c01d40240c50314050001c0103143c0c1c00640c90034440c03140d80340d000b04001a840e514001c428 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 330059721 1250 330058471 330058493
    0x80702090903040e040311150c0423060a0c020a081b04060501020114270703060207031107080d0e06092e020a02030c09040201020f06281e0f060f03060603 68
    0x75621500b003080103006820081c28003076081501031034001c039425450140e0354034040c107a0420030010500702c0c0802190480d0040100252156030044001078004909540700c4640c21320b8050358055070130700c040c002c5140304034101507003140002c240702c500f542d070f4a00072805c000030741c02028188072000c0e03003d100a042ca8007400004042c20f1000b01b2158005040c0e40c0c0c7c0044010b0504898641c3c0c156080340590205085104040240802d0350324181c0c1c1c9107070071030007507000103021804101c44402c00c0c2200c40740401d2210440c2c11003806854410340044003221f840031400c6e14941d103e0014020385489450b10707620300340d080b14895072200e19000c080c0007031288054492281411507103d00c0b2440016180403a04284008041e41e14803100d0f182e920040c3d081000344201c1c1c8209105e04820040c80d01000204000801078142c20340c1703070094411505c68150b480e00c000c5c0c045407086242c801a42821207a00403d458078140500045840e00c5d04140e03030a0000550055803200d880e92001c1c02408225100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 330060971 1250 330059721 330059731
    0x6010303021b10030902060c010f0f060f0605030403050d0612080a020f0d05040b0705100905150f01030218191d0c0d0c05060703110703031d01030905101806060308070209 75
    0x144542c0c4007403030000203c0745003e02c00c0c020101a02c0b49121000c540321001030b1101c1d081000020310943c42050100001000681100342009041c0f06000940e0803446032824251641561054903558441d102035616901c01d4045541b456920ac04c00903c2c6d405003061080b103140b00e00490b550703544c0e20303040080ca0544070402082d1079400000c030000032070350080d08503021202c000b01a203403100c0700c0c1c0c2070a40c05e0044440b0000c215604119a280c00c020011482c044144414550b03064107466420304003021590034000250445041040d201450300c80c8a00c0c80c1c0e104040c0c52020300820740300d0b4622425200343c41200d08940b62185800750124005010ba5a1a418150781d4100b10f19071a1319150501f101522a05004010001d9010141441084000018400d60040b148c0711584e07881c0080400e0641800b5000303802040301d801c2c02030340c824002c04c0c1c0302d540c000c801882000c40c501a41c0c0c0040c41c403442e400703200745682895100042c80900907000114080e014040e00c600e043d005103d480c182c0104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 330062221 1250 330060971 330061003
    0x5090706020705040e010b0d06051f0315021602030a1b09150e060607060e070e0a0c0e01030b03100f0b011107120807080d0504060504021009050a031502040f080601030302 75
    0x81404801d600003140c000701d88003110f021074006401081035004003004652141c110506a82050510507290407450250f14203001071140d105401d080d500c1440842e001c02400c2c07004040f101d804038042500640502e0340c40461100e4805403540c0000d1400c900680300b1281d55286c0e1100036a0900f01609040083c5003103c400d000104a45001d034180c0440c0e4021b4040780c203010720108100351501410b448810303034020801c02085800c51403482d9240800d10a882c03008100900050507020f5a0040241040b000e440d0301e41c1c0304c6103201c0158007908000b4140d942600c2200700594110203540505030b8400d087c80c0d00022082c0b4000700051045000c5501019203500c114010401c5070a51101240356540012a086d140c0790546085c01c4148544000c032069175080030140802d024050b440580114400c0358400481c1900400039968174900e407192607442110740070104041004203150b40543d26504000501e0251aa058044000f03807541014150742d0003800140308050b01000f0300003100d26660 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 330063471 1250 330062221 330062233
    0x501080a150e0c0a09060f050d080910110d0c0b091911010c17090a090b1c1103190308070315060f1404080a021503070804021203040504090305040503010509 69
    0x7032194000d02900501e001085940c500e40c40702c250b42e09020340b91600000510103612940d82c1d4041402800c0c25014139002030340d038014000b4035854611582020700d50300c184801c0c20100d400301000f41040d10b0741c0818061102e0b01d03403a81c1000109100071081202030781c40324030400079942015408408010010801039200d03c040061740350950759078519556200d04140c0d070703524100303004807023070426844010321301035402030101c0c5041c092201519814100342e41c0480300e203986040140035107010681c01c1e500a030b040391509400c0141c1c814588446030148021000d041d40c102c01007031401d80c00740c8582c0c3c98128100121010940d00652003608001e4600e41800a8400c403001b442031840d40f88108030030300c00b00d02c0d220803070203000f043c24607214030060701349a171103960303407074840752a074601c1d010407071040190580c41840040c00030181c07802401c040d0f44424461f40c0d0f030f50902c00f00c2c988403881a500c6200900c00062103603140d020360004c00b4803a6a80340c0c1c48603d04024113080d15030190520070b45400034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 330064721 1250 330063471 330063473
    0x140a0e060c0a0b0a022203170d060308040e07180f05040b030c06030c041d0439060e0102010f090506060609150c030a08130209161107151704030503070804080c011e0501080a 76
    0x30424407a200314400c88e070785e907030b4050b03246607400242880e90000f0552400400e00182041400340041e104039802c1d07c50058981960401c68003022850246034010302c642003062000e42001e40c041c2007800c0d07000e4110344030101ca0100140b060780040395202010800010181321a03901003266001401150302140d81d039003456a40e0b1b030710701b01c04040c0d81030301c2862082100d4217084440c3d901340080c900104203403800b2034448100405020301940042d0241d03080c40d00f211401c9801d0301c54120302a8001c4041c00454440c0c5003086016480b03190302a034084c0c440c409256400280710b00800c0c503890441c00130b5980e03038600c0c0c41c041d0000000907c80e00c0342880c112511005629100c0c3c11a900044440c1d1440310711113038581c20b42c0c845a030350f10082c4240c4141c031000301d4402c0042443d85814082c68941c86002c2c0e00207a001c0c8982c80d800c0310004c000502c180003284025019181c80c94000d80701740c407002c2c1410218641e076402c42d0f102070510000c0342c2c580c0c084100c00c500d03d840f80e140500f412401403e091205 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 330065971 1250 330064721 330064733
    0xf0d030b1009030f0c030f060e19020604140105091c020306070c15111c05090712080f07020604120f0213110f13050a080a03140a0e060c0a0b0a022203 66
    0xe0b521010704405803150042082180d114100805076602c40c1d00002500c0160070948024060703060b180c503031849580c0c9a40c2030340e40e8501031006003642c01480c046c82e0500305110b11a0201032925207606101d014001d080c1e00b541e07280802d800c5040b046075000840640c80c0101480d003140542610203120610781604046144040b028601d0751341202d000c180701c01c03040c1a07910b60384074124080003090014480054131211680002d03015062440c202c6403043d4882032184118080b0240044c0050020400b8591807035480000e8102c2c1070000b4441418145d0711144081500c00301d080854014503041400700452034250b68001c01c3c600206010060760070341c0d0047d142e00e4803032a50305003c44c0d44c000c40d080c518404015a03400142c0300c0034126454481e0b480c000250348100c0301100303c2c040344054800f007051481410685502011585d191581440d503034003448240d900c04120042d550044034000313401700d42ea03409014040c000c1c0034001a030300c10344001d044003111a50b04031510031810b0040c081002c602 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 330067221 1250 330065971 330065987
    0x8071707090903120504030c02060301080304030b0f0c0a1d0312032208030c160203010c1e02030a080403110a14070501090605040308030106051c06060c020901050f030706030c0509030f0d030b10 85
    0x502c01000445d900d66040545070b14444c4400207511220000000c5129900840940201d070311611138064076490340e4000356038500d42100c00c0e0420800a00040d640e0900c04c400c1d0303410080c005121500400b0a4a000ca0700385444228100c0d180c100020902c0884ad551440d4404c203240c91117079066a801080c0d0f030703404991002815800c0900030200d040040c0c4684072003104030700c5a00078020010300407200c4d80500401441c206080c0754206041d5503049440c0040100e0b80440429500c0c440d03a91384039501950218180d40ca040403500c00c86000400042c0d5448407400320b60f00805c02080003c0c0b800d0001041326086802507020040c3c14403003000000c030700074252410b4882a00b04036031a06039456400b85c2c80c0e610b2400e40a181d504100000a549402003082d071000c074001d44050300182e0301d86081c800700040201182c4c1e0541d01c003100030400030380b0943c40705040f1100c62614a16100402c00040c0ca13084d89800d02d402d142c1c110546070841c5540501c03d8a40350403064408a5407a40000b1000c0c103494 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 330068471 1250 330067221 330067247
    0xf0806100509130f0509011d060402100c0609031e09030305030105040c05070c0f0e010509150111010221100f080a081602090103110f030303060319060608071707090903 74
    0x1c18045a0801680e80b0a00c2c00c0e80e0301c1190000c01c00180010041c8000944000e581148195180c01c011140050311201049032594080004040b00c0e15154207000800d100043c0803010030480c40302000000d40e00b8020550520702a5075510354000c0b038001c01c503031402e40590070001805651213003000080e03000b50950b070454104071000a6a0505d02c54280c0710f40c480c0b050002c09519107940e010501200d60700b07140703060360b4000d6107000d010380e00d4209200c8414400d48000c0390310f903202c030782c001403540c4510101c1e02d44481c00340016082c1825a0072040b030005101c0840c211646081e02044003c1031f4400048004003900c9400213802841e058103561100d0039000301a1880d4070001f0034440b0b590041803514100c903400341c1418900d40c0d49081c80c5070240600803c2c140321301c56400080301e1501d40002920f0003010000c024006916000084103804d1103050001c44a564444000051200301801440018401000060103402011070038a0801a5a411403c8000c3c54400780d040440d500960128000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 330069721 1250 330068471 330068477
    0x702030d03020310090b060714060f0604110d02030619060f03110301120b07020f1218030a0203100b04090804080a14070612020c01181401060617060d0201050c1005070f080610 77
    0x50f4511010491f54031680d80050142040005520400480015603078403410180d0544281d6071503034010803050320100000d0060140c0144004090448154000c1d90001d5000700400d2485030881209900041154044004038801941442c1d406825000749001c400c2c042031000e1441d81012002102c0f1540c00e64050b02080702000007611450003000300440c1e400301082201d100300d500b400800c4042c1e21210000d0f8200566154599460800003420000d01d80e000b000752004105883c040d0008100ca581100da0254442c0c1c040c0012a0400c0700800c00f8080920190041d0119424a0054814845141451a40a103008129a40d44503201c04402c000c01e4501585d0355401581890141095000010110881403004000c200081810440c0c0c0f6544000a01a0300d64680c0182d810103105940d580c080b402010000b5018904025000d0005105041040c20092407070340e014076000104103111310301903464007404203a5422a100c56005c28042c500f400ca03520300300c0041210649804011014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 330070971 1250 330069721 330069731
    0x2102122103010b04122f0a06021605040f061d0601170112020402070c08010510060801060509010e0d08040b1303050c0f0607020d050c060c031305092205030403020603010b0702030d0302031009 84
    0x10049440d081244840c09010344110a0350748032081b180c0d40c0701c0b0800591142c0c060050004040c0c2c004503000398454804001c0218481ca40002c0c003010b08140e0000821240da12540824a0f1403039068100c041282c0d490540001e190000003d070005880011480c520109500100846460003d209400030b605907005a2540c8907440c2c44005981d05803c09501c55081c40208400702c2c408500040480e0815a00d0410907603131200190780302d02c2552040da00185a00c2040c2040303040407005015000c0c49500940d10b0b050381c40c213000c54542c002101320b440d8090141d4080060202c00c00c0440c844400840e48012401400c80000300c881c4610301000340030704500c1203040240401400815010034029150f15075508422030f601e9120352065000d617013400c19071000880d046c14503950a0748070b6000d003c03840c2c006007850790100586100c10a4120751a1004200c0800140c031090080c0d402030002c004c8003901ca20791740c8101400e142150306d18204041c814010041c01c84060481c00c0100c1c1d1003c400002c0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 330072221 1250 330070971 330070973
    0x1e0c05070804210c030302031908010620030f0c060a0b060a0f0305060a4202060106200d050d1407120b010201020d02030c09010f0f0206012102122103010b0412 70
    0x200d8200900d03018284c0c40c3c0c090800028141c01000810700440741c6445500e80603a80c2c0e030207503150701c02800340400040002c064240500440c0302266506001c0900b282e04090700200ca10b02030b6031204180101c1c90300f0007014040c1d02803060040407074485040b42c00c7c601f0250800001050544221405c00c01c068032103000c40d01d140c440f406000041c001692507548400e04440d10384060810111845010181d003100c0c2e84055009910340da0b500035100d84c05001d86920700358040724003441000000680801401a0709030702d0344100400708048110380c43d0f2607111084042141d084840c10004489016415400c029049611032075820340303c00142c0000038003500e001c0041340240540145401803d1000050102082141d00545142c0409a85030305c800b14484400302c5102010103d0000580d01080061008404070b402030280020f03200b045a0140c8081e40000b41d08040d00c0110b09556041841141d0888810060103480143d01c828440d246514082801d42c0d00d00c158400c4400520344003220740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 330073471 1250 330072221 330072269
    0x30e0c01030b040b040501260601150818060708100b13030303020c0708070e0906070203182b060c0f0c030207050f03120c060106030f1407080702101e0c05070804 71
    0x10513806020344204011740e182c4054401383d2907404040c03003204108400b00b4000c1480000c50394165074448401c50391003090010306854118015085050300400003880b007044403410062207100d88200c1c0e84e400300700d06109100c00d0200b0443d420946116004100452211154000c45403c4a82c18940140c0d20541e40320380d20305240d0503410040450150410002e90030784813242d514040c42daa0002d5481c10340320f0810990b0b81c1d100b140034503030700c020503442e1113a40307481d040b480e020342105c0b8580340041600c1c21042c1d0200c0b0101030182158559a9010441103059020341c01d90040c6402d4285010607020688029686060340c4c45024400c0505582c1c4a0315a181400700000e40504a4642d0391619000f000c559200c5c5c5090103614006844c0c9061919840281d01404810140d190001217042c0c81d80442158504030090641d400d610418040203503424192042c01d10382d602d00c840f4a6440c0320480e0421003a11901c0c0610b00800c18140059000305000310100e5080f01c0d055501202c2c001d80d2008a6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 330074721 1250 330073471 330073481
    0xf04060e0106121202010504030c1113061e050a060203040b03041e08042103201f0f050916180902030d090e130803063c030706030e0c01030b04 63
    0x240c005035092460000d11420510203100055120320710341d0400d8280124100d08a907411280a03000031804510000402c19469415a003420080c00310b14018088181203415a40e4030ba110402e0140011030f036004000c00361301c44501401c022628040c1091030300e00000e43d0790283c1d000d44c402c40388000011078104003000c0c415074080d80b0007090301303500d80e83c1c5400e0883e51070704280b060b0140121080003000d402050842003c40ca9a40340d20f9190070644d48040c48a02d140c2e20201d8a07900d40311300907280c00d0324005503a4150341303800e48a4000c80d00b004440741490075100043e00300c034500e50012a4002c40c2e0482c800c0100b0540b019140024048804d00002d00003805a5950194050103840b28203107c0d582d120320900161010b803900c82c5030507101c0000300e003400102120003401d4442c0510100340e15162150b071028001e01c0143c5c51800c100c04200c0b14101c0c0490803007101001894004071541130341814444c450003040581000c0058814000000d51500b000d5100fa5040503510b5014002c203a030366a000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 330075971 1250 330074721 330074741
    0x30a21090f0803030105010f0f0c0f02010c06050103060203090f190b091c0f0816142b0504140d020a02040c050f0c0606091b07020f010905090412180503060f0406 71
    0x10034419030b900d89402d91240c0c028000c3e02d00090103100e10540982c0a20440c1c20720000b00d030f40e10b00804c0d8054440400c8000e50b003004074104031070000f01d44040f852602585e4040d50080c400140e41c0d082200c1c00038544501c03a034500800390000328a1001070740d00100300a21103030f00207100d60210740da440e52260420300401c4c502011440074100700780c441d69021100224009030340d2520040f50f102c00400b030f0301e080c004000c01c60009209003140f4404503124005060381c4c5516a15203400400c00f000311568280c0c2c0303000c0080055990740e04000621226821110000b108000030340071444c0002e80003034030740c1800500030f401243c030307401c82d00d16192146e001c071061202e95a15454480b04a4500c0b40d0303c80009803101486100710303c000c1a0794507201c050b191521425456298038006642e400c0c84920b40c0310400c4c0e94180000c010000401c2e4540b90318080c4681e1240c001100100c00410014201007980e60220540300049441030000b80c400080443d00130a822564603007540d50380c900f550141c54140f40b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 330077221 1250 330075971 330075989
    0xc0b030403020f0c0409050d1409041a0f090c030f07050714010f11030601051c020409020403030903120302030c0426010c030902091f2c1003020f030a2109 68
    0x8200400d2550118003400300900c40350585031044081400c0000340c2e0a803201c0500b40341c000340d50860a40340668107109084400702101d03400c00d0114130000d0100c511500c01c5480320700d4064043c80051410000303100303641d0811140e41d00c0d0760600200b88022404000e061200724540d5101142d074a90150382956680d6900070080b0b40e500e80e8418481d40a0700c4c070101c101c40a00d0900c41404080c108500035280b0822041e51a40e09107070000c0c51540e5030032851108211055402c000c0810403804600040001c0e40c02a200c8025540c910b16007403191010301c0c403240081610500c01e00160091220460b001c0b00c04958140186d0414584242c0e0341d0125a40040420361070441c1552a44d60590000c111b814000c5580711060f0b62501c028414184200b80641d102000c43e01051151303417400c1c868010003201086c800640b1900f002212021030400b0703900801e074040304200c00c1045107080b080c4000710380306c160054111206a90f581d1000c096520b504552503125002c26a101e03103214405142c01050b603d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 330078471 1250 330077221 330077227
    0xa060e010b0726091306030816110310091a06030a0b0a15032003011401050904030c08070308060a050d0f0201050315030610060f0801120f0309030602030f070e0a0605160c0b 76
    0x405020761144d54001e001e01002540c004010165214aa04994000290501d450f09540b400403034075005403070440c1d101e00e0646900c12135807402c1000c2c5404212108000500860f14200703808402401c055034546101d106080004584002c0f41c01013000768000d00000307107910703190390080207400304c00007280070342100b40c3c0008107000e0f186101d40ae08036052100f5001034140b4000b4103007a5080d6034160710207250744100412190034130800543c0e22038000d10b00840394032070a6440603083c2c3d00a0009030300044400c01842958940b000845004220807240d41c0d08209043e503a850074a11031902c00307414031601100080f40c900c50b090030100c2402d030003000d5626910300480b00d003241442d43c0c004c910009601d030480f80b02d07180c001d200440c181c178001842c60301c070903030700da42e401e0403989460404601b0404e00c0c0c02d0000019035980007650150440000464103450003007030080c407603400900400d105403d10f40e000c000707007a041000c0f0f9040071158411446414030ba0308100721000540d03480614000000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 330079721 1250 330078471 330078533
    0x7031122021303030801050a0f17071707030302120c06040615080a05061519031709060a03051602031e0d0e0a081c060f1205100507170a060e010b07 65
    0x102d0701d4001502d12039140d601159807504240808050b407401104107010f4900414071000b43c03040082c8007614011021212000c0c0c4500c1244151101c800c4003450307036400f0100500400d0b4040c440144503084030100710341402c00000c209541c421000d44060811603036a1041e1140c01006203040003e042c004d412610b002c14180f4086070b03681005c0325141d84200c006c207000300303407883c0c500e0381d2101c211000c1103440e81c01820341d1210001c03262542007140710103c04102e110140c0d20790001511700350005480016452038103a942d002d0b44440702e00c00740215042044014a841c501407141000182e81211042e15103001d404107000808490030803011611a46007404100608400181a031200c501c5d8a801000040001c0006445090251001c105c031040028040040c90200250308280200c007166070b9404032444000403610291361410018044034100e80b40c110160407461380100c0c240c03204020305480d041104410721418041c80100b60070015000d000c5c000140f4400101e000c00608549207a0f0369 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 330080971 1250 330079721 330079747
    0x2061806040f090f050103030f081021060b0d02030d11030714070807090209010804030503070c1209080d0512150a030c0b04152618030d0f0506030703112202 69
    0x19441090b003e142001c0303000f01150200d000c0e160403668540c548031401586004140c030200401003c0c1c0003840d4482c1d1001030302c00382c0e201e00c42c20010684110100792a001d8240902503031300580c2201c1c0115000e40241d00142c50001e042203541c002403a1800c404084100c959085101d903e40142204c0c40c20000030ba0803980119104040310a600101d4500540d1040315406030f01440d40c1950100d80300000050100e03010b400207580c003a0451a2900c0100c20a545281440005406560000d02d400b802440080000c0109030b01c02c94183c00c103d401c01400366088040f101008100f00c450b0aa01c031410186a101c0202081c00345501c03118405007540c584105400c2c0c1c1e081b174400c0b101d1100c0702e0010301011a0060074a41d00c0410880c030b459115000c0e0075040a048180a400c00410615045001399881e00a2001d031a449036030840100d5468003c0304001d080da1406000b140c030a40100f242000080ca03d41c0c1e61800320041919501010b102642d0b81d54414801d028007034005a00004500c01c0c0d9a00f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 330082221 1250 330080971 330080999
    0x40f090b09100c08070f1407080a2705031c020a050609060919051c090504060b0304110907081906030209070804030f1407150f02160b0615070206180604 67
    0x454040200141c0b0b40390a011960b10302c4c00e0b10100c010502900c844410240318400003811b4109640a55240803156903480d250303584104000c00000e40003403810001c42c80e1800020391070540304048079400c5c0d07080c440000e80303509549102642c800f081d1995003100074004d0110050031b503000307010345190b840c100b013401c0d4a452044a00303545070700a00001801c103104040c2a0300348550040020324032000400d44503801e0b540808581002e0005000c00004d80e6907603030148901400041200c1503c2c0d0409107130080c000440b000d185441242e1074002c00c12600e070f00000c00c2e54460301c2034442101c151481158200280b1071a000a5003041e104420410022b4001c0ca80740d01642c400d45d201c0d1441003030030b002200c14501e81c0c40b44a084900c204503510115040100701c52520300821000034404e1400003c0c07070102d134000354102c4074060140480314180600d600300c1035807103401650107558483e05059110710a200744140284980d40c00b203281648114008103001c819000980b04039600c0351504e14481c0c2c07800c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 330083471 1250 330082221 330082243
    0x31203011814101203020c120c010e03010c0c03051e0f0403051c0905190815180102070c0b030c0d06030311010e070302100302220b0712031a040f090b09 67
    0x5410442084003501c58403070b1852203480e41d2140706910a003000c24200103c0c82000c0142d0461103964040c02007540c540007003c103d941c154009015180c1004000362498020058084c4280d00d04015840340d260454120a4030590510f0036a550f800396090310400780c022180c00704211a808605181001c3c200002002504c2c0180d0460341c1d0b44144481c0c55144038801080030b00001d0590008002e01c0c1407501944988050070000400c0c05a1680305c144e00c0c010010303407003078099060481031010f26603220103900210320424000707500e0075a0720744820769001402e100381817012130000001220850004203503810041070035000e000c8690740c1e040003010703d40300100d140c1c807a510303021034800c1d49000051000200c03980905204820b032042941607000f50000c5506404004005142454600300e01d0709280c054049190b00c4c52319440700d41071078a0140551400d540c10b140c6481c0c1800c08243d8120012110258122030106550b0f10070f00e210400351944407401800641004d01b0300600400c08502c282500d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 330084721 1250 330083471 330083519
    0x7140c0a0c030308010b1e0c1002122a090915090f010e100305060a0f1416021c020a061a0d06050a0e0a02130c14040909030801060203031b030603120301 67
    0x3a6201d9841b1b9800c1d2207100b070902c03e60101603010407140007000c0043d0130000507110664090702d024103000000c0c0c0e0f0048028071410701244c0d00700681a01c071b11058a52401c48640b10810a03001c03e825980684204000c9620495542001a1490402c01806c079a2250302070084003260801c070414400300182802001040c512042c000b07607041d004003e190381105d8001000b00540c0c0c44901040f80107020000b22286040e4540b0b02d1580103214259a56003e044107000a2081c0811303080000c1c2045000c0510000c0020002d001c490802d60019000b041d49401400014460300005201c044414400042d580c025100d4078070301051002507400030748a80c0003800107003d6045103078642d6858000c2c48030000e5102c2148840180b807407500390312403001110182001414121565456440740e0030960100d4181307901e404500080680c00450f860050059000850442c1000b4841050b12141c0030910354000c800400040d03030540d03041010703080142038608041d50325612003182859048058101d4810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 330085971 1250 330084721 330084737
    0x613230601020c06040302010507321612021003060911210424090204110306010e0d080301290a03060f0f05060417010e15011403120307140c0a0c0303 66
    0x6154000f10705142c0307a000092141e89881c0c11a4015140c613000020151080380182131381d0718001003654105441144050703c40c04024a0011607145001800c14280c041e044150404001d01280034540c0c5c580c803a8111070300c0d286225001005c80c01080190300640000e8202158648180940d000078030340c101860200e090002105902200340e000140c4008100501da051901c00c0d00501c09076140c494104040045000c94030f94000900b520034040c90480d035180c000007841060f40c5c0240441c01100c00c292902e01d0649000d4a8000460205100c0c86440740c88005000a5032410048034030f550401c40d00b8240d450304000c40000380104054010700da100300710070201003a107418040a41c403c07034000030490741c076042c1462143d09801c130904102c1061503484070031010190790144096650312030340740d02d542c54a61604444900704401140c4650198110600d5104a1580c00e0300300c81d848442d0342000003c82a0748108150a886030a0040c810350007088200c6040040c01038285084030b00980e11118 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 330087221 1250 330085971 330085981
    0x506010f020a15091e0507090501120b0604110c0114092a01030c0c06090f060f060b03130302070503070b0c160510030f110d0f0c050a0206010905061323 67
    0x10703903030405203005003440701c3c814051500b001e01d5410510320f07248100000a07101500060301d401c07104000e1402c4500f60840d000030300107902c6038030400d801421190181d0f4803606868950303e10060001d4a05030199444111019000c40180e08440d06403281b40020400a000c0b0003d903400b5042c01e032200d1401e40a101c12200408010340000030941c00c3d00c4403110b5180c1c00c007400640051140400700d000b4082442c0000011404a01c50322303c0440c06442c00904000161034403070203d03000110603200305490500140002000c0d00e080d00d60000240001035080070b12070409a15100440e40b04a505114619001c00c2e42030b00c8002400c801000b69046410545031800d6009408689009543e0420084150010850300c40d8000301040e20b0303449400101000c1010704040c41d0fa000700195900c090711807912860100103446013524a080d9441c1ca0b031300b40355610000a403034820620a10000b80d8841c4045005075540340303d02d000c18904e0761810420708031340e14503a01c2030b2980540681001c04498000030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 330088471 1250 330087221 330087223
    0x1b020f0f0609061810020c010203040c06030213051203040801181506060c020d03030f0e0f060a0212011e090f06080c0901080303070f020c0d06051b1801210f0506010f02 74
    0xe40142d24241c050001d607600da002d200c03100e42c0c606003070351854416080490503004892008200c811407070380002d6500e2605060000d103d181c2c0344c1c0f201e020948104589120884104403280a13600100d5450800b6803010a5091860060341c02c01e1505520740080c0e02c524141041d0f03040300c1a440350510118410340c1a8888007104c0700e6101c0c28011a103800d01950061826500c0f14036054440c1c240000c00800010100701155050032500301c046e0b00c90384014100c004204004c039400002050198078200b203145400071845010b20481d40c42050217000e200e00c02c420320500700050801140f040081401146004002d0000c82c07282c806240103102102c03003030307040c03540c002d90680c3c502c80011480c5440d10b0400300c81000c205c0704150118000c022311400b440d528142035140b00c0e80103c801013461300707081007003035a15020041c491450000c100b16403810400e1000c0003001000e002d0030302003c8420741402a980c105100b1800300a43d5240681000c04d540aa40c0064041d14082c0d03900d03001d070b040180b800c1e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 330089721 1250 330088471 330088483
    0x9010801021215040e01060803090a1a090d05100207210507030c0311011107082a070b130b03041203050903070218100308070503030916060e01030c031b020f0f 70
    0x50048a248000003001c0c03c601044020040c0c0340600000303215048000500d084447c0c035005440140c00008540c40c00f0b28180780040040d0100c078400600c81c100b0b402641c4090700c29001c810340201240d9601d80140581400342c03860384111071205641e00c60040c90700c611600001c0c007150000d24009507240c0e00c100d10500c2901d05066058503101e200c4803c0d5241139652840d440c0b06252207640340d81c00c441301018400c01620010303106001d0036031074511102d40b044500000240c28440d009420450b000d4607040000c101048034101d10b02c041e0781d00d10b8014400401c9005400040e0200b9001050100b00f020440c0343c584d5010440c0c2d01084a6210703592200d840c0d104164000e5070100d01400300c0700203400040b24464001803400480c003031145e40d95540f01000e030081d401c19501e60b00040104803861000f8840050400c1511001c0b02010381000b00260280c11240b405604241d43c6035000070040307019600c180f0780304221488503080c00a10002c001d654100780700f5000c59038010500031000c10740d00000c078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 330090971 1250 330089721 330089737
    0x504170109020a0e09100522061b02010c2705040c0e09090601050a05040e0c030f06180705010c150609020c03091302180108040809130603110108010e01051c08040e060901080102 78
    0x6490302071100410075014007c094507001c0b15052110600500607808410324074500c2c4542008203103a0300074100440c207410202002001d590400d00f94a1006a100a100081d600350120041400703c200a8001d0081940e8020a400c2454004e92401285d004074081111020865086800307542c0c151030561101028414030381c0210008005001524241d000f4604030f1624004590f04401e41b000000e142000c8400710f400305800c200c3c00d104d500c6240c909052030b000789103401070071464503000000345280038800001c0c01a0f020a05030030016042134110f0001801441e0303041d51100c006505468480d44000c40b11441007000720340c68a091080e07030082ea8020040380086519000c500401550103a00c004d00031601a0410007001d2400d541c3d01c2000054024060f01c0041e5250640c0f600201121580480034103014800703004000700203400000906640007540c01e40510003411040e0b504076030f00303040700401c0c039100490082070020003900840d104800c110b03440159030366141104c9080f4820400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 330092221 1250 330090971 330090973
    0xb030601120b0403120914010c300e0102040608040506010e090318030c030f0d1205011a0a020a06050f07080601020c03060403140d02190e06042114030a0207091a0307150504170109020a0e09 83
    0x1000001800d0300002b0703001220301c000300441e81c006900019400c9a000f40c01070320101d190f0000380801d00038100102c0380501513009480c0c9041c100045800d550f4000c210384a4844151084c9100c615107040c0b1002000060180c11600311030041d60b40381d41c036000019186800120b050a40044425060180e01e049030b00001e0020601100304443c090349030f010a40d00c0003075116070203241002411921403030748210480809140f803804c06545c020111100074200d2411541700d03640d500500d60340802c10507013243d8035082c1802d00c9100040101c200340101c3c0c1c078802102d0b10124011000b06402e662018107030607503658601041050030104191030295000c0e01100400343d0ba0800c04410358604900102c03405080341307680c0c11020798000e80c41d56020103075403001030b04081810421013860b4040d8030f4003022400d9109050b403081e000800e586074000e204010362031417690400607940b805075003100d0142c0710000809003000344845070b581c0a0007116800300e004182607240091440000c5d001e80b030040307034420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 330093471 1250 330092221 330092267
    0x20405130b240d0c050306010b0406210f020c010e0d020a0305040e0702010f06080f060c03090d0516120f020d1d0d05010b100c0201030b030601120b0403120914010c 72
    0x84405214100001105001020089044402c641d01e44008000c1144116421081300d4184024141884010307800800c504074140400e10007250010b9010083c50070810111440e0422252110058607010310701c12007403031000904604010f8190403880d412010700003262002c460f44c484c04c99a403001020081d000400a2005100c40186404001e82108840c800420302050100b40f04040f6901a802551564442c005070119503506000c1d481e0320009c400c05107800c500d0710a80b25a11101c0b0303291076900f085400507400541c0c039281030340340b141c59402905c42404c11038000f501902c1d60111200800c0036224480740344031824441d01e101c1c034503c01810400e810904082d818820f1400384458129103a5480d00d01801880e11804000c1042c200d0a80d560411082c60b40005421a8400f440307140c001e400c000e00600c20010300c1e9204514050748000440300b0b503a19030508a030b14804070307044190503d041c282c1e00000c1c03021023703648c200502820001c103c501101141034490046000c03003160012064 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 330094721 1250 330093471 330093481
    0x31e0c040806180a0b0703051602060c1b01021c05010e160e090411030a03021027020906120307060519020a080c0a0201091403030403020f07120b0c19030504020405130b 74
    0x12001c3e03a509074400c000c990021446680d2000c90f004201d4600c4000f0b0368520420001400710344265400d030041d400a480ca500b04a0001020385c440c0714400c04c0d000d00c94203000b407018142581198001c09160b09070114800d250000301010b48820320600e0041002d02004c1003810480003a210001505030306e91410414580c070600401d840c2c000c0003643c2c40300501c40d0406840c2c5080c40105030b018840d9000d8450100d003445104110b451003900120f00b03d11020b081c0d4140c1c5201440c04a5440d011109a5101e0341c0351030015141001d82007580915020100380e00302040a00d810040c000d1003c40c0303581c200000c0c1c4ca19030030300724080d9405400c0000c0001c00030441d094a030f81d0003400050120300c00420f180030f05884007980558030b00503107a540e50001041006256051003000542c100d034101074103040c0d1400c201c0207842e000390749001d8101c840c103a022813100d0320002c00311400902d10743c240403070002000710090002c0c50100c1c3c0590180d400c00000905420b0403440a01c0e0b6241e001d01c86502c1030b1a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 330095971 1250 330094721 330094741
    0x120f03060f010e030109151a03070b0d1803090302040507030e2a060408071403011506030b0a0e010b0304030e0909331f08010b06032208031e0c040806 66
    0x315004607050008000ca0fa0b54180c4084c0074a540c1c00b401450500c0340c1690100030f4400f01c407100104d51002c513030140d2000655a4022800034104e07428403140035200c0d0f110403079490081405c402040b240d1135084000e0b00400d0b4112814900712402203808100c01d07500c103101030302a01e62040f901c0c2500c0d0444031340000d000d481d00e075118025080d9035a212005607818004510f4940c0306422a440940c0812801c12140010010810340d90105070020302024040418500d0305c0380c081e000d0301040c19110a0404000d445182c5e00c07100034010b0100500080d40c2d20010510a98000c0d9400c2d1300084001a401c211410401c0300c6a020380400c06c02001070300d855282020000c2c1c0410218a1000d440c1a070540004907601e105a0050384640310401c060040c01d0403050740038206078080c25080e410010701c410280e5810080d40e40c000304403080351641c541001900016490000310080003100301100380114010034081d40c0c810040c40380802006070301c8404008000740a1072040704820b5016000103120080c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 330097221 1250 330095971 330095989
    0x3191b06090605090d0c23120d0509012307140606010201110306010f030f020309070608090f060c1b060c130501050306030c0118090507030f05071727060408070302120f0306 76
    0x3002d0780400090586540d042c101c40708040c0003800307c0c0c0048400c024007078035081d142c0745071188020000b40000c1e0948038018019005846466045c818007210700e1191000d50710003a04503020121055a46c7d07400d602e84500c42c0c110240102c00588240000600554014410380031242c802c900d00341d013140e03140001180d125000440d001e04058440080b60f411180d5030010754001c3d42441c0c05802540e0030400b00400346071004180f00866442450750b01d400000101e94a0f411842803686a0342d075103030b800d41d05030300041111540f040c2841604200010700d13050030081d0410800c10300b9600c21740c40d9610011100c9000540b12154940c100303042180c2d0560103400700010344103d0b0030030781030b066540360621400c58a044805001007600c0301d00350390808010b4400c0307a0740b0180604000c003411540d41400d01c82c3c484003c144810b071601c641410708070308120100400b200103015049071104c0c60103141c807a207243c000c1201200584940c40341c11411810440c191508112001500d0742150368540c10000d81a03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 330098471 1250 330097221 330097223
    0xb030f0a05060307050406080106030b070816030b0d082b0e0c130b1e13020412021e0d08120c091e0103150b031e07050a0c0203191b06090605090d 64
    0x4070070304c4030004403601c40303004160091074400700002c1d0306450340c00d0840803484010300340c00402c40728000b00405181c0000c0340e01f0301d60390245000a00040d64402140c4200c081180c00760261002103141c03002e40c4c00c85100c802c42c0000801000241d11000d408450540d4a54881e21156400450030781da05070a210740140845411004042009242c0b1804503a10304004508003440c00035004100d803403130511518801440160440842c505441c3c0003d4202c1c039a000c01c0024458045070242d13015200754158052542403000b0080c402203010703883d2007001588800903a02070144400c0000303299140382c0c1c0590702c01e020090f2021004034640c80b201d014000e860100e003410300d035a41c003600b258054000c1c1d83d10050b0186843c119030f00d0408914901c17141400940000d03180c10b014023000212580700e01038a01c1c01810741040e00a91105200007400e1840e1460b40046404c182c06960040c4441e0007a050140032440801c1c03001c03961207690881d0071520b203000e1007000c2603003008070218070300340000b02202003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 330099721 1250 330098471 330098473
    0xd0308060f10050c0106050a030b0a0c090504110a26010b0c160f0501020f0d05090d02040b040504051f05070504030f080d1d01150e0a090212060a02030a05010b030f0a050603 76
    0x807154160001d001c000d00000300c10300241011910180c003030403d102d0079020b028100c62042e000c41ca07554418400c1640100b48103040c1ea01c8004031554903024980c0d81014150041090002040c0c0404414581c2c101c0c1100d840090f039080c010400a00402000c01e542408104082c10260b080c1070800c00346c5c0c0d0101861501a21a80c0302c10059a03a034600c16102500540d000f800183d450440024501140c0100003070050700032005400f04240c00c0421a240c28030f041c0c0d512449408140005402001d9004140e40c0140c2400100401c01402150104680601c03507485041ca12003940b004044130000c0380da54000c00c00c200300520106040800c850080c0d481001614501106040190b0a80d01c00d201c0080083e440c140710b035400381d60b081c06a40b4407880003805074846070307140080c10b103a82080507152070700007940c400041e03042d0740341c41702070954007032051041f1140790510f17680c0311009510803194102410315102c008100080c1032022240243d241500074121030310742509060040901030505641 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 330100971 1250 330099721 330099739
    0x20a0308030910020a02010518010c020c1507060f0906051806010501030902270106121a060a02011415090604290307080f060103150204050315070509060f030709080c0d030806 77
    0x1043d000c0307000411510000b540041454289403001c001d08000010301115a64100050280c0851380003d04102c0a241124034014125540d04c89141324459820007031704007420b000542040707942681009000501ca00d4042100d0798800199158000c0304002c0072006802010040042d584641c000041080c002000c0c403018981000568105d0700703042d02494000b01d0b06000400c4210b4101210078011a84401c00f4024014003840c1c0311980b000d141c4c600d82c412040414014400751003503024400c42c10388480b5440d0f050801102803440749002400c403038400d1074443c1c001405420507001e104003882600002c5010010100ca084030300314400300170030744c01d44200c00300001c3d0f020040011601c8a11110060943da5045040210b140d08500e201800540d00401003001103840004003000b040d40d00c03805000d100d46480da0100e91610500130102c2d13004e4400306a0000b04202480110300410441e00c034013202c1c40d5123000302520740e5101c0030785585c00842a94a400480d0040013000c1d840180241040d107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 330102221 1250 330100971 330100993
    0x3030504121e060e010b0303031522051317040b0301170f39060f0a1103130816030201122c0304030201020607090f0b0a0201021b060a1404020a03080309 67
    0x500310b0001c4100359403a507243e54005114003001e120342d519810007070340130314918600a1a01c0c0d144542c24071462340502c0d8408000c151103060240d401d8010030918500388407600f40151a0308510324611001c1c1e81083d070703a40c0285507902c0031a080328202c4100b1040182140c0c41c01502c40600c900c40a4140d0b50b034002c6403048042480140098480c000400e6103c001070310220030200604000d48246002421105542d40c8499032040240c410244101c943c1540d28440b14008445081c07400500702c1c101d1001148007050080c080d00b02c08199941c42c400c4441900144004016151091001902084c1c1c44110b100365002e094002d96500d84e00001c0011449c1015002c1065034641403081d02c0541c3c00c082000e20841d0303030503ca0319801c00081d180041c8010300307000101c410100b0390320890708c031014000740881045000313405581c8202141114880001c507080c039140d89030710003242e521700340e0b92804e80701c405004d02d901e000341c0c0a5600a000c54a406040d40c0e150034440c2d00150411b845840b8a0b02218 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 330103471 1250 330102221 330102263
    0x105070501090803100f0b03010b0702121b10020d080c0f04030b011415030411010c060b061306030e070b16110a09020901080f22080f1b06100303050412 67
    0x2c004501c19119581d0342d1400415001031601103070442d4480e4040b04c1010000c00100c1400e072410340b40d440b810a5584c640910002c1c0c556500302d5641c11031400384010750b040038a100c924012010700e040c1c0ba0203902802c0351400b2605d4481c074410311008204280086800800d180014103424640c0e40941071500340c80703480303640007600c00360712910f03034000c881e07885070590b003005a82201c1e003d200042d03142c29410033390342e80b02c03001907081d45103030401c20382e201c0000c00d01545411407110008007a0200d95a25009041840e0940243c00b922000c40e092880e45541080b00003214030445080c260128146503481243e054900b080f80b0342510b10900d41990303182c02d40d480d200070000034400013100582c0e440e400400505401380c004c0141c10404034502c104941c107000420585041a2810580c071640c588600e0000120300545043c05491840441c135050b03608091425299001e048200311042592100e540c0c020752031880c000100020f4091108002c2515092551210140b24150300440b00714088204 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 330104721 1250 330103471 330103481
    0x40f031101060909051902130e01020d0614031e0d08180613061112040f05010f05090705030105101a0f07150204060f030e060c1c0501030b010e0c04061b020105070501 73
    0x203a5141c6a5070712680c003c00404112851320b614101c2981c001690706c40d000581c84c030100d00610baa4042d1141c0c50111a10400e504945034a403a0000421409454820b901043e600004d4142e00a1141e1b4404c0b010000a800d124030070b80c00c848000700603060341100704a401780c0c006003544d00c0b1540c030186240103160060040502c80d81d41101213903412149401c18200b0382c2d000100801440504005110207035209000c1103500981159027079900c50322500d0198010188000720220161031305080c0701d60000081007400c11620201c00a001c99101d18419a141c400503125119000e583e8141f0b58401914040203404112402d2681c2c0e13041c1400360710303500c102140544c06030452681c0040c0c00d0000c80c0e0030045070a000355007450f0400a4290046180756138032000ba24115201d1404070b503c4100400d072103005100c85105501c00c0c046541d6902d801c0a40d16000c0c01070b0450010b0700e07400101c3c0c820b10101034074100ca01c1541e9a4181c40168a12003410700785089081e41080b40c108603201c0491800d0180c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 330105971 1250 330104721 330104729
    0x102090a0b0a170f061e0d060e12040b030a0e070f080307350c03160b04170711150c060f0f0109110f03070905031f0b06040e040f03110106 61
    0x9071541da40c07035104000d091140020507800c260740c05a06103c4804400c00181e58001c0050344c002a118014801e441b52555100c1c03125a07010400c111603e04001842d00500742140428044941841d5514a204a0b0380a0b6002e0360240341000c0c00002c01e06c0c4510381009580729181000c2e29038032501e50b038504480002603000a82550700c001510410400c500ca80040002c0c520741c034680485807a41c44003080b441421040c92441040801c2e082c1c00c004061044031685024281c0c1d03000c910700d0915140310b2014044606a8065254660a520b180c905500315040c0030b5210017803c007491541000c0004501000700d01001510040c4285014000704109040c011031801e082c002c0d0302d2402c10b26050061405070800607845e03007440c6000040c6120001902c5425465000c1c482d22a903e000303003161010441d501c1070740d043c8100c219100f4003540000e58008020003e1205125501c200000d1021520803841805252a8202c000801145110010500c2c06110786086062104200549400e46560f40c04c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 330107221 1250 330105971 330105989
    0x7090c021b0619082208090d08091002011e020f03240904050609060603032b0b0d080a0e01030501151b06020406020705010e040c02030a11030c120409180203060106110102090a 77
    0x103000508858400da983e1290320040e000e40880b0307542c0c5d2001700900a00315054000c00100d502350081106100982e0101e102c007800301e030a9002d440b40024042c011591300e100150038150343d441440c41441c0210b5589030019038166140d0b071a8010718040340c1d00501403500803641c03c400705030f016998110205006a00401c02040d0074140503070400c3c1400c42c00340046100c1d500030851861030038032440c030f1008050000c02c500c00340d2821303901100b005841413103141c2c0e5003d00a900a04100a80c41014041c0a0003c1c0d03201c8044441250054084610a00074500c0c04807412043d4600c1e10704c100c1e000111507601283c0a01404065980c0d0000d0740c120381c2050001d600301d40404c0c03180c0d50748019102031081c42150280000d410b030745000707900d92081c0315a8000300100c028014403a12000c01c1140c2a4041e09422540072140c2d502500d003440c0c1050040d0010703107040007035200c071020107500c42d01255a0001c0251040f40d103440d100396402d440d41c1c0d04000303a954081c412000c03da56070690b80f20007841244 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 330108471 1250 330107221 330107237
    0x513080c0d031d0406061e3b030d05130b03040206192309100302031e060a120809040c020d0806130f02040f0501031503030903080a0c1202070807090c021b0619 70
    0x40b003003485013800c0a090754208210483c50404101212007a003041b500101d40300041c075280b03c8c0e078030440d1150390b4091b150140301d250780710454903901c400103001006410304400d042c1c58840d0100b4080344419900030358081024040a545e6010a4000d18241c48103424402d8001c0400400741c1c0340c400e00d680f4a62800c2001003070200141c00d005003441c2c0440d040b13140451540c0380c5414000450642c0303c01d00300301c184d548000150140c840601110240605415000d25501c0d81d00e481081c0c0e074003003101c19002e2402d1012707201800e400014144030040c40ca4941010a40d40c4109009000480c079417010100c07a183e8884105230b551038802000a440c0d0791000c0c03540790b400e1000140544552040100d07601c0111201080800e500225580a41303600c5010306c0da4a00540008596900b80860080c0c0114014807121003002c2d000601c06003107902c2242a80d140c507590f200510111031100481901681090380a00c88410034040e11000d0000014540340c02c1c8528584c1c0c80000526644800c0b0104500d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 330109721 1250 330108471 330108497
    0x90310090201140f27061b0c0907020a0b072106031703040c0b0a0311030a1e02031b0309031b07060e03011e0203250513080c0d031d040606 61
    0x20203d01c0075940603060340940350013104a481c102c644909a0350f141c2c40310b520151901e0707105070340045001ea0031009000b0b60326880080d28040e03a03000c8220301040c80784600c203503d0b2040e00b403255a4512410741d41d000382a0600054030f4884441a00a00320300410694003081b01119800c0030344002608804840001d0590940c9440c0c54810003a802c1d80141100174402c00c000280b245125005480c01241342e15103a0035440000d03000b4100c0200c04c0d5001007008000c00403254140d0348000040d65804003040b04000003484824104c0c0700a403000346c22503240c0200c1e81e103004e501e0b40007150000301d031104503403511055445c551652015604091900e130008203080249991140040c1c1c1d0400d0201e0082201404101e04145095440103d00340c446401000107130801c4c000c0c820807010204510007240d03e140502d00014141d510252010755459820f01e0080303141000000c4214201c000038101da8200849528140e130f000040d564403240201e86250804e91548890107094003c18150312005400c40c04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 330110971 1250 330109721 330109727
    0x31f06020106300201050706060b031302030606011d01031e050a02031009060e0609061f0e030d0207050307140d0602180f030f0d030f14090d08010e040f0314090310090201 75
    0x307544004540c2c20201c80e40c0107062120074280328142d640c242403280c2c7d07407285443e0071000741107260f01050360300d01d0100401510a65000084203154804ca0584070703259600c400544501d26000c45c1c0400c15180b0000c1625154042d503c11402d4070818800c0d900f101800969020598004407000d00c1c942d5004000d0143d1075000c6201480a004444000e001d46801c0120b07803564008000e000510810f841d1000c45c1e543d494500791000540048044030801c0b13200d201002c1c00340010404442c0c020321586581107043d42c80407a441060b12002030240860515090308001740381c1015203031b5030340441c17001c0e0f811001030210b1005144503440019141c2400d404a070402611007020004940640c02080889220000c0880c20784250001c904001800b54407902e0400002c148200e140d80f8000c11400601412000020341201b50021139501c0c07030043ea0b200c0d0130402c0889003c0d20300408111310003a6001c0002e000306116120708900c66a59824804007800003403400d0004500d05140070f956210724015564 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 330112221 1250 330110971 330110999
    0xb1c051905010b03041515090e160b070b131e060c021501212603060a0b042303160e0702060c03010605070201030b030309040203100801270602031f06020106 69
    0x400d501a505614040e2502511074000321110b0003459660490f00144040c0c035003d1f100a420703104400c01ca56050300719126074a001020250401c0d040c00700e03002031000f025000302c417000c40e0f120385824500c1d140c2541c030400c400d554003402c403441281d04070818500094104d02c140c54500441002c01c06400d51407000e410070030150036003c42800c1300030043c0502090000b0000014061120103030603200c0781d090100202c645100380328900c1d4800d038000100c082252001d0740c014101222030050a580d12444034242c2c0c82144114529032410308046518805d00c01107100c01503d001d005e880c0020704000741c1d40c80d00c40c2150004500d0212040510802c0c0fa410000b09610008481c151442c40d410402c003d8204d0142010003810917031980c103020520384050040d5240900003800c01d6440c1d0901801005d207020f00c0740a0380c00d981d8030f880455041104c07c034001461341c441e0001c17a0100443c098680708060350004000c202840300ca01d40c502e48440b41488800700410b0700d0b90002441070304054903100408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 330113471 1250 330112221 330112229
    0x2a0a11010902010c1209051201140604090507051c05030d1a040504050c0f01030914010b01020f0a080403110d050706030f0c0206061c032d0e0414010b1c05190501 71
    0x40c1c545859000181d803c108090203c507003008003140c1600d007001d01200d00d0800307900402d8100301501c914403644e01c015084800c404c1d03108450703001d10795a00c0081c082222030301c007005800c9510080c01001030742444518510115556901d00110140580319646941c0c042d8400002856035900c4c40d003072004c548481038071213407021141403102e402c1c6600c405a4035111700519900c129001200d0060380d038001c2d440352000c2da03031200142d14040202081c05000b07001100e0054058000c0d0b000f85006900e01060028400d1340c0524001e00305805c544429407010b0b5454840c070341000301d414043c004118100103610042549a4001c20b20045071030b801c03810755041a0041065501080a000380c40c2c1d903c0101014000e640290f82048600300d0808648a1070400c03081207100850703001d00d1698400082d0355070116003140c0c0714500824040d0052008a031244400401402c03200801440041c0401d801031150f44860006451180804500e02088410640b00302125500400c004243d000884c010a4010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 330114721 1250 330113471 330113473
    0x30103020901140f01050d0f05042d24060801092604050a0911090a0315050705030c1c0f0204180b0a050303030a0c030624020f01020301080c06032a0a11 67
    0x24200f0b00104501400040d030305030501c000400c04030b10000e455401f804230040d40c1f00c814410381c1064240f0726940c9126030b6459290300c010060752842004842c8d42079403526400405a02340c4510b0a002403994590085400062900d4010000f40c08009000e6940741c0d40c025651030900803400074100c00640a03040c1900d48880060004002607524809030008940c11080041424000503085c0c81c038612512000303a034041c00291010050000c1c807042c401c1205000401080a504d0f200c10549680c0422030f014850709030100501c20910755515085592881c50700d00206406180b510b07088241d8000d50048003000c4214100d488240300700380102c00040704181c58940e4580d01709804070b1b4603840b00820b042c1d00e036a22840304031560f40c460351010300201100c07074402000045500d600c4040d400c0b40400c0f00d00502c20308501ca120000103208a84c1203821180c01030000000080901610340c000900307400c10b21203004116981c80c0b0850712418581e240001095545034608070000d080003000712000211 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 330115971 1250 330114721 330114749
    0x6070f0207140d080a05030a0b04050103170702030f070b0a1d09010e04140303160215010513090309080f0123041a1302040e06011a0f12100f0308030103020901 70
    0x250082001c0007500c90008100c2d60820380da501107150160030b02001001088000751040c080c5074000f001d14003c0c204a802400003a0383c0e4801c2000780e580a01014040b440c2001c50ba02ca00100c060080c50700900c0a410344100600d0141d5240c10441e90350b002c071041000000f0301e1380500e940701605070000c0704000e1441803821040000300e0309004050081403480c0f113010b00481c0900c00d000c1050308402c00788108582d81c034a07100502904d4819150000d2000d48075041150100e50f40b08682c06059401c040c240f0310120300c001d4185006841452000e4041c407802140204000b0802c1c4080011440840004903910148400086400c4a600c2d8070004400e08a01404000740010341c01044c1c903c88224140c032161100c0110401007200108020f42c440c0c03810a503007019a80108070541200c8486c2d124014082c800482910141300d00300b07841d1050303d010030000d80b0520040c48500c1d000f0b250b15082400e055241c3c6200383c2d102d151a04103550302c40012004004624005010601601078041d02041c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 330117221 1250 330115971 330115997
    0x6080c13060e070c080d060305031201211b050901080601030b07050c03030601031d1f1104081c020a12090305070902090d0f020f040227090c070b0907030f03110607 72
    0x41c140d0000341c0a0f000304034040b0700090500504100b80d545010304214200182c80e60391400c0707a41c0f0f40c405060241ca845010000041351400c0b00c0300d801440c0403da41d00c90b40c0e02000c0da14030160203582d11401c40600030242001c00c00b41c59106020b8081c010003001401c082d411820301c2403800c180100038a04000041249000e00c104c003005507038200708282000f0600c036031861250340000c000b005039520350744a036994510341d80c5039400640c800b160600c981000b11b8440b42100780200c3c803030790084408a90001c52083d02c407181010b21f6404c0c4d51000c0c03041d02e0303601510b80e40304001d11406140e40000a5030700d0074144288001840080d000384400d000c11032034030785480e000c40ca15101d44040a0700c4040b46c2942c1400b591240056070910400c0100304660f039041d440000080014100c985460900e000c18144a26040081449000345200075104c2c0c01e181d050760304e000740300c000103005204a01801c140000004e95410804000e03501c81c1d21049844a0050b800924007180108203904101900300b03680 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 330118471 1250 330117221 330117239
    0x15120b0604150303091802040b0a0203070c0801060f03020909011413030806030d08040f031e020724053f1e0408040612110408010207020a140303191206080c1306 71
    0x8122090103406c42c860b0f001c1c084248009000e00c3c0d0140c06400c10000703501e01040d5021005000c0c20f44190421322900d41c65407402402c80e0a5400f0301d600c4102c891a041c80503240295042c1e074000c810400100c0c40d806009012035401c134065039040e400100301d80581c010550880d020b150b00c00000c0c0d00030100c000d80684d0007425401d010b840070703201c40854000641450310841c5a013040e80b110700306243c10710841d09002592403204d0f00c90a40000b03501c3c0b803000c24960103500e90f40f045402031780c1c0d007a0a021001c010350a00318024075549220710414640107002200400303032040b0700d10501080381028644a01c030b05103046c0301d00c00165917231000e0104100000e64228250b4050f620540390151480394003001c0900104551800d2990000c0c000c00c001603840340540040c420303e8802e40d44802d01980d603120070141e02c03860071204d642c150000c0c400741e4a507110603170150641981a2802030008511079480c5400c80390503030845180340c4c021405090007424194591003404d9901c070000c029862501501b8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 330119721 1250 330118471 330118487
    0x412061d0303130609080721020d030e060a0c020a1e020a14220b190303090e040c0506030604020912060106080912030604150f0f050a0506070506060415120b0604150303 74
    0x401c0c16917100240d6061100c40d030180c50185901c0000203241480708032505020b503441400c54001071080c0e8116247e02c4e40319000d603840a46242e002000310340c95040044001d0400283d001c07046200ea003002c04c02117400c0010720100640c03c1500030b01c080b0300ea4010312201d01c07075030b420201d041c145010900c5000e0300c5401c0c030a18908054042c16210300044402c1002170103007007800980c000c100d03124010001c0d81e80d04890741242e10079107488828690300c12045028440031500503003214000740013008582854001154890303002400103292062200010fa000c200662104081c1c3e030220005000729030304085500c0c0c015040f00c008112803122407489008510004165a025035118420344402d0909500c0d03e002a15405410354003980d110040b03401e40550501c20319100c1d101038800042c0505101d01102ca00c00c1e00500603200b956209070500c4007a00c11280141c2c07500d491000e00084901545000740c00207485074400e041607050600c01c1109440c3e4540d01c1c07007401258000300700002500700d444 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 330120971 1250 330119721 330119723
    0x1403010c03020c2d0a05100c082203030204210303060b040b09040e01060b07120f170406020a1116180203060a0312050708070c06260105060705030412061d030313 71
    0x11130300c05aa1140156400c5010b041101c40e0a1103480554010420003054042078030645c10030403c09015510811519004181d400b110001c031807076003500002d0144090f640c060350180c1005844c141c0e64081103442d2090001811f02500c03c44203c10342059030600840c0c00400a0355843c50410303040a50005292281c803041521030340e90790040102540b000c0d00490010001c2c0c7d0402038841019060038071503010500b50450028200a4840c420b0354003a070000c2e1903400d903581046009588580e03960000350f1042c4071032001d10404075403111148030108410805890380a1106c1101440d1014400d40e05d4079000a01c07080c640140104001074a551280700110790300309400c688001c0d80ca0340180d44a12a001c406800c100000a661003031114400c10002141d8442d51808000c03060320920034560b000244c0b200f00b10a04540041000380f8004e005410003e014500f86c03032506991710300003400c13103800e40011104161503c0c5c5160703035000c1c0202c8031484a0b0301d6401452440c0f4100d000e520002842105c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 330122221 1250 330120971 330121003
    0x120910080903041e09050a06030b090307050a03030b0409021504061b12081b12100501180501140f12100f06020c040c0e0d0b0910090f1115041403010c03020c 69
    0x503603000c005128540b13240051014000812103420308850a034081d01950000342c449101c1500840d0b1040800011600842e03007082c00b40c180f20f5101e82d0201d0280c10007112081d801070300c401d411000360360303010066801454080b04060f42c81e40f402401410102c40c0c0700401b440d00c0b8070388645401143c034002114103004842d15141e03500b603880080c400f0b03805410748026101407102282d055440c110744000c0034081d00768940318a18a503541c0e00119224850b02c2e10279010015007000c10015075000d020340200d05030314829050f0401c0d8000d0010b001a401070003c40040c2000d403000e1004080d2602e00c2907001d0204030007015009420160301070756642500111034003460b13803040005401d42c0f00342d8408a100341c00501840c401d000c14102103c041c9800e031680c403a14020725131010902c0c0359038860019183c1d030120209051042584a0401860030320441642081c0215450381026006000900251a80031100d81e0303242d08107018942151211800c400c2814410081c1003140440042d8081140983c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 330123471 1250 330122221 330122249
    0x30513050a06050c120406020a0237020a0b071a0c13231c061a030d030506040b0303160b0c040f0b090f12150f0403090e13020312091008090304 63
    0x1c1c624031801c0c0314002044404116917000c0c402000441d40050040211542c00ca03245514030354116440d000c1a0584c0d64241c1e201c1c902d05152000b07146200c90344c4a400140303401e54240e036500c10f0100961158404a8005442c4010360082084092449400c9590040d6003070a10164006801d040d00c1c16008241c0349290304001c800e2043ca07444180a843c0390041c02c041d407030705c2544ca1042000c0e2a0140c08032080c50030b02d610300f031104429550400b9803180080040803005190001a401400050045c036081341e00c070008101940c070200000c004018981418001d0520300e4100360322040e02c0036010300c049174010007080003104100014002030382d01084225544001c101c0014603094000180765801c1600b404010b0f501340c00204020b10703000683d514110150351003600100b54080304440c010301050380140c0078000d14041a10043e400444020200d00c20602500041c4c640302d55020200145140016070503414100341c0100008040306041405050411121503a1240928002c21004200038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 330124721 1250 330123471 330123481
    0x20102060c07061b0c113304030f08030711010c05030f070215090c030d0c050303040b040c1d07030f02090f15041706070906080f010302090606070b1501030513050a0605 74
    0x941c89054a80031a580340d0031080c1c3c080601030451000345c2c1003558050490340c009a03946c1000707546290f0381e00b081244400b4415004221000d0047c80c6851020444030a00000c80010b0040383e0300c0441c20301a8404c0c54581c42d05110007030040003c511150410b9050800d91510282c00500352508401034081c081c0e4240d079400c40407071034501d061a020503c01c1e01e0301c062100c60800412907000c000e801754182d41c460b41741038006a405800d402ca0042076580200006004604000780068016104502440085550b9800e070102c521101d41e800c50030121601c203015100c0c0e01841030044011341d004041d810301e80783d02c0005042419003c1c4081c041c40701d1103c100352110b80c002c1103c000e400d0001151541084e1000e040d60f56890403901231001c40c491110208085004448161003003103107000d81002e503829a4280030070484003900c0541c000c00140920340c0011100001584602e2403c1000c1d07540010f41c0000600f502c02c0505183c43ca003e088101201050001c162454229007050022500341c0b10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 330125971 1250 330124721 330124733
    0xb011523070f0c1703040602070306020c2a010f09080309010c17130e0105040905030a11070f03060b0a0f06090501110703060c1e0311040603150504020d0e0609010504020102060c07 79
    0x705080103045144401d0701504000031402d000041e1881804400c2c04810800b0046907244607070b005141c00340e4040300d800c03c002900fa8006000003001d0b001a10681d000d030105189003440d85e1596026103114002c1140d0a03540e2000303008001c506140792060505203000421901c920982c4c480a04214100703400e0002e2000d94010f209580740c503902e1281d515110070841c44d144140c6809500d0343e642c45030000146901d040e0255103031081e040f034095884c01c000103806480500303ea055800042c014500c0009000c650560750900540c003694010032020340c3c0b84100303d030060103500200d00c260018901842515030280185040e40d800307003404400031b04c0e0742c1d15891810b82d80c1d5000034050382c02e0812141145601200d51344035182d0304017006640b502c901c0b07002d074103441014030040e40d0010144400c014051098000918881d01c514052014030b45440200d1706903808020700120003520303a40c0480c4011010094107900010200081200e8100750303000035100c000140c10b00c440305130301188200910607 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 330127221 1250 330125971 330125977
    0x3010f1d060a150320040302120606030c0d0c050405010603060603050718090b0402040302060c0c01020f031801080a0905010c031b2307080d05010e06100e03070b0c011d03070b011523 80
    0x485c000311515800aa6514000a03a0041c0012405000000c240341d00034100000c5107070060f1001005045601e51321010b01a45299080c8182d4181d0640800000c191300c03a841240e010741502c1c0c3d070218103141890005001e6480184c601410000322500c03100240d000c1b40c1d810070a07180c00c80b00210b21002ca07000010068004e0760806584040c0008151100440002e91021344c00e0081c0c0030740300d0501141c140b01d03459008101000d4a5001c04215490040d80b1603140150300c03244403000020000e0168030349a084a8111014001082e80c9581c034203c040a048403800a16810b0b252111203d860300da0f981250402c50b2060701c6c90104046403010410a608040d9119040e0160080100b582d540901c2f400f401400d945050113064800849035002e80700390741d4404d0800340a0300821030940741c0b01000080d80c4c05800c150720310707540c1ca4070b0f540c0007000300a0340e44000b0900b580095031200b0081c2400c075082d05060740080080d0209521010500b038000200b00c0340804005040038a94281c03040d068403501c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 330128471 1250 330127221 330127241
    0x60c030601120e0705150c0304030305030a0e01050f1b0418020a050c06040b10050d020616050f0a0311010f020301080a080c030f0d0525120209031203010f1d060a1503 73
    0x6060030340c01020f40800148900440c0c80c101c64014090802d503990380024032441203441c400e500100303c1800880e0107800119000000c542d40000d2805c8009815403c6420648000540503c46c1d010322610220840c02d49503004040f0041034070746490032405d00e0580640486003400950081003031410180944103507144201810180c0e4441d14003460306121a07001143c07908402c4504401c08161410101400c04049502a0030a4a8640a59149041c00122450888041c03044000ba8400031006025441c0190b2180d120800c1603901d1f9800710382502d840c0c150301c0c007c041c8140010803043c0c1c000078044400b241c00030409039440700e034160710302e08500c2048030300300640074001940e101d01002d0750301c01489060241c581300c203402d680601840c0e24500650004000404074150b800c10150643e008240c8903000030b00b01e8a9a05103208030f0440d58000768094816142c5038103040081c0708a85490701042042c5110821003441c00500081420381c103801ba00340000c01108a01c0d0f003541c060f921080d002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 330129721 1250 330128471 330128507
    0x8060d0323041701060b1201050f0f060c0d030516020c0d052b0f02060c090616120503100f05030706080a18140f0105041104020306010507060e0106030c0e060102060c030601 76
    0x1103445080c841c0b0f98005640445469610780400020400c1300e40040e90021082c1070486440d036480c0008204d900070441c40c001da0b10a584414880f82581c520780141228210800900a0b03840e5880c0040e0484030000e0568400410980c658142550f000c01c20041e4010103c030300286880003403e190740707007064190201051000380044400000c0340701e01d054800d03801947e41c104260486c480100c1c0c5030300054602412280342030015420328500f9601920000f00c5c41c1403040010045902c64942e00703000ca104240205500100740f042c04003195013450050440e0744164010741c0c0c43c10b00400d03070703c564a10400307080004060101d42010410340101610700c001c4540c0000042c91400e201000802250f020f15541c07040001c0ca4942101c18014039111381d422003c2041740c500e40c2024031020f0740c801003a4a04024082210500013000c0e881100d880007042400011001e00358582103580c20341c15005640c01c48401c00070444160390014955074020b242d0705c0130a403281c650600603140c69100d60043c01c24 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 330130971 1250 330129721 330129727
    0xd06150e150409091703010e0f010602030a08060f010e04090b040b2406030711011d071d1f18090c05061912110a0525031e0e0a03060902010f08060d0323 67
    0x10442d062343da041c0c0944080e0303c8034140359a071084240d23524400c034040c11000c56483c10014603d4507001e1841c42c1c1a14040c10040541000c04002500700c27081c50301d00312000002c0303a0030f10061101e008005944400c10007500b404804c201c0e01e140709011444440c140c42200c0020019507a18410640c005001860100a008004900203044111204d024176516584140000012444683e81018208140c18504201c81c0d446a0304c8044400151840b40340d4800c40508c0002507100503a4840d24408031070210001e5020800c0c50a40314584060344a50702c60b4100f0b020a001482d4100d6581040700a9801c0106440d4480281c00c0c01400c00c0000d41d840c2142d01180481041d50030200030801804898038640e81d4a06202c02590030004495000d00000d0802e02010786220000300c00e020000e4544c203000b1400000d4a000500304146508110f59441d1550301a8045507004411000ea0860368200382165141001c04a55a0a0000800390810040041407607558030132000b4012140002028595 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 330132221 1250 330130971 330130979
    0x60a0308070b0406050f1519030c150f051809060301090602041d0105030706090b0a030b130b010f03060501050d09080708070b04140705010807050a050d06150e15040909170301 77
    0x140a00d000c50341500c504e820400050a6403050054142c8070300700356160342810300550340c1030002022203902c003100c103d140c4280c04000302d00301d5940e2000400030310100c84018540240000e001c80c6040d100c40d8140300301408002220708004008440980e0140c0c1c0800c5d250f270b07030340000034090b00b02c40c0d00103440301c2d1000802054000d001003042682d0700c54820440c9060b40e0760710a040d600e058a00c6000c002803414401172042043d00d400620104003c3d14001c50710706c580300f0002e440100c0f8038018905280c1e5802d086011543c20245405101c521410b081182d6031411001a00620174034042130415541c4200e40e030104160364042d503c400350403100890f10755002d417615420103a415101500c10000014611400340300001302c83c81540e0042e03481400e0f68079565801d41d0030b41c001d0080300091000c240154501d2100c0351007107070024201c2d0301a010480d00c0c00c0c4400340c0481d01c65003995009804403046010a60001c0007100e0484d90174400000d45803680d810480d900c041440030715044032100000000e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 330133471 1250 330132221 330132233
    0x2010b040e01060914060306061c06110409230718030609060203011406160204051e09150606180607020a0509160e0612060103050705041508160e0108010905060a030807 74
    0xf015a1200c4800300301c80c2d0081c00c1c0001c0d4084c011612203500d44c0c4103c00291803420104245102d29003c44001e0101e1103250f902c1000b550000c0729142c240e0310001c41d0410419846005100e0b004243c0807041c8440c607030b00e0010310b80212004000d041484081d900407255158003100c0c1800940c2c0040701005002003070f01d42100170358400e04c07441c103080c139803031060481600d000390407500403141408036101001f1469091201910b001042c1c4014a45141c4e010119003d01e0704005100d9070b008000350004048034400c035503503074101401d024001c2c0c50034040400c081d507401014841520007200d01a440f50554030000b03104d8a80790704110740100c1120b080c460381608552000040c4241600e90340d41840390701c4244001c03405504c0c0a40080301c0c1810100c3c11031b500035804a84c10400c0c80c070300a85400d454600074507500d0901210b10f4000f5006004000001c400554228515042850180c18150660707000808a40040c0100110306540300003041641e92030415100040d640030158a80b6482c45003026 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 330134721 1250 330133471 330133481
    0x40918020406060905061611091608070905060706050c0d090f0b1b16060e061e0105030303060306040b09010b0d06230f012309041b090509030a05070302010b040e01 72
    0xc0780118146040071a065008210107000c1c1c9201610550034190400704107d289180c0907810b681d14807a111001ca5140c0390009202e104502d010452050a0900c10005000703610080ca800b003040031810050206030f540108464819410030008501c94a402c0c410f24001c4c4a1424002d410902d08010032080000501e0944c008031701400d0310000310350f1110f0f104103c62401402d03c00e403211007004a0001d031030041d406a5480d902030300e8001446c000c0c03203d0700c1c4d01d89007058a800c0b032201c01e043d50940d80b03400900d00380c5001d80800c0c1d016504504000c00420b40d80c907000b80000b41070303001c01000508981800d602c0801c0407500102821800165800c04500600b044501d19080302d100300c02c0c0f0582a60a0030140d0f01904202c00c042d02d1136807a00e840108442240c0e42e0296080540b005828803c2e80d620101500031801040020890358000b5040103802c8459806941d4050500c3c00308210300601009071602490f5034105143e6a002e10302e0101d00505c480c1d802d80340d229150101e120b2000005501c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 330135971 1250 330134721 330134723
    0x406030c05042c0f0106140c0c03070306060801180b04030c051f020a090b031b03090a020a08010c030b030f06010510110a200d0b1603020408071712190f05040918 71
    0x2020409031510310f030445134800700340251008200950740c6407680f01031000040c000441c411041d82c00c1c402032480002e08040742c81e403007175400d41c1d140d000600c00c0307140038415010700e8034060300040701c0b0024564a801c500500100081e0912240e00f4500050050a0003611322003a0308840e1102c240483d4807102c002034021000d0030000420098003c0340e00103900f0122805803a10640b04079484210f0045071800d0303031000300650841c0c000d10b004a0b00680310384d0380300b0740a022800004142030800c01001030407903041c25001d030f210361b100c44d5807414070840214445040d1002550030001a07c0000025900300e142403407009894880c1282010620100180300e02224241120501c241e11703110003040700000c5c043d10054010103100002c101d8421401c205a40882402d04016080c86c2e0341709060383c20561140c0c03040071245400d2022661406061204444100090041904204140e8208240000072006000c244144250b030862014010402e40300241750101c0c09001d03c03400300745800e600030b04010b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 330137221 1250 330135971 330136049
    0x92f0901060f08060d210e060412060e03090d0b071e0c06200d020306040b030106030b0f1e060f1f0f0e030601060e0112140c0a0e040b01050406030c0504 67
    0x4041000d902d070410a290440c1d401490000300b686c0360020900c1c1c41001c81e15401d00b07103d25401441e030551110b0000c1d10007402c1403440810700e264a810280161203005c0d028402a8000300100d03001030303544001d400c081c260044403280d081ea540e8102070340c1c1c11100224000001c40403003d00b204803580101c00c0650540725039010700403801c101100e5054050080b01c004007003038050144c800350210039405940e2245009102040011440005c01d003100c49030303041516032854103420400d0706290418180c2c1c00c4603d95642c3c2065036403a25050a00342c1003d001c2c5449400849940c403120380e00c04004840c0c58a400c41e5110b81002180c01c0070b00300007005110388002c03a4003100d05486034900450800d0480e4910b0315030210616054004452407104003030f00c00380c104c1e0341d24141040b00120250880c0306a10300b83e8641c3d6921009034015003007003446030b0315034840e030300b000b886499a9034403400303650445009050203c2c95042150099455000c1c6411075000b07a0400617a0782120031004400b407248041c010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 330138471 1250 330137221 330137237
    0x5010c020703020f040f11030103080a090803030919020303090a090e0111031e220b07030605030a110103020a0e09090a02090603280c0b0c0705040c0201092f0901060f 73
    0x1603848810302c0c80301035400030309400480a00d04041d000540110b4022000055940c410045644d0ba60000c0e001a42d8050020940c10295600f24a0300c1c0c01501c04140114191320300703c880c01ea44d03400e02c1a54541c00c00001d05510086440030425540740703610047c4621120782e2590f4108c4c00410781d851415910b90b0910801c0c4000c62000300442c2d016880082c40d4840300f034000d0103114034040c800b82ca40c65114500919607118682c07021202c00c0e0441c41114900240c0c10b001c0001819101980c008902c260854100500061007161481032030142c20301340562078034188071017a11150b0740a10416000501d035020000b804a01066080446108440c41c0c4800d46a130000c0c540d5401403038100f500502540845030500c1c030b0b500008010a18451074400c0341542c0c42c0c4140a07500e420500c1c8007085584200c80034002d40c0f40600580c480c00d0f483e80b0080010f1707487c58452a92170308043c4000000010f015900c00e80300d0514030440511034902400d81902960f480c3e84c0200382409042c03248e00080e00704 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 330139721 1250 330138471 330138491
    0xe2e0612200a0f050906010c0f03030501050901150f0819060803070b0a020403050307031202160b10060503090d0804020d05010207080319020432150c10110f070515040f0501 76
    0x4203805109684030224040f00c024140700902180e940050240350501000c0d2100e80c0008402d0284181068420780d03000c0b84d254508020302c20800010707040fa105000c0c001c88002e03621a800242600e03402d048d8078005034242c0317490b20701911806110340702d00209428020046440880003000b04011886964051195941c00301180200d026902005203aa08100f02d64401b20384501100c0c560190642401480c0003100c007252000403002c00e808403081e0f52080c0c1081200c81c070b010301b071340010072071410131a1031072400c10320303450b142c40d1100d4558090115800c046011364070b80207501d00b545c0b60f0010007196111110b0804e800540c004803a05280c42034800b03d03140201e016802954203d644482040c0c0440c1c0818070140644c6002a501e04200b05d200d444508480d0f0302d12000110901074103110302e588070b071002c44281c207101c2c4054000c0700f01814100d111307504400240440d0351030000030460a84440744c625041c0d080902035008441c0d8104400140024044142d400500c224400d42c0200400400c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 330140971 1250 330139721 330139729
    0xf0c1b260a020909010609050117060702010e19050f07030615080c01020c10030902090c1b031e0313080a0801060e041404062705060a0e2e061220 64
    0x5841000845822041e0003400604149a8883c1c20105050000c41c150352105602401c0341ca003680000c02d00d02504084462a050901810b40c00a5051000303104502148061650340c0300c1c0c0140410388040000204d6090102c01d020701c0500c51000420b0780c80711517607810854060400c0c050342c419491803008000076004000945003a925030180c000c1d08200ca480c00030072004550075070059092648a254034401aa140c40c0840c1c45084e11820441d1100707503240d01001d076803507107010f05900d0343d10400240300b0002a10503000003516421000c29903944c0e5482c0d496211641800004003458004550300440342e40005034181039840b1550703020800c0d2081c40403c0306682607640b02c5070081429001050120308190000d280e603069080c450201c080c0500040d119100301c0381419112504040c09000c00e00729580601c4e104801030400401900300160303a8414515a528207065108404100c04000c7c00c40a411100c01080081c01a107095100c505202034407440d174250103036040360030110240403450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 330142221 1250 330140971 330141029
    0x302030f030705070e0a0b0d0516050a0b070f03110312040b0f0106120e03090310090b090a1211071505030402010305010e090c01050702030715090306060f150f0c1b 72
    0x10f0004000e28209151074190700450401400c02e0804941341e204024594032040f9844511078440c00c001d045d000d0220071215100b00e8640c101502c6107011a4040040e141c0b00790a642c00640c00c4003070884121880c0c82e0a94403202e15105d188030500010481d00b020341c5007160080d110754020030141409568421004400013030900403140070a03000d1080107070302c1d00c06a011407481e40d000012a45006103140009240c0314100442c07031a0f20b40c540700301c00f080221884040381c00690308001003064100b03039510542d95400100d980700401100450810040e0310070031020b4020000c05510107154820310070000c0141d40100c40070381c04203090100004d40f40307480581e418071405e580409004000701e00401117503560f1003150143c1c0d01d40b081c54001b0800d2504440c5803044001d5030b465100c140340c910314003a41035803129800001070080283c006c1000100322800311010940c0351030441c8a1541000d41502d00e1403000c407000e401c0e0007149079102c00300c072102d942000943d204c62140449245500c3d6004034106 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 330143471 1250 330142221 330142223
    0x1020906030a1802060f09010311090d2603040303050f090a031e0302040308030906190203040201081315061e0909111017070e090a05240a0801020309070302030f0307 73
    0x4420000180d40b911a5848007080b43c2c003850801040500b1900000d0540c5c00480f0508040040050100003d60301446250ba002d03442d03800d81800c00030440c0000e00c01504040004d4030b0044000790920001c0150b00840315010b02c9400e0084d00c03400d01d13040040081c1422120001246899800701d00640800100a00b01076415515212140c1002c203149840c0d0500060702418117800380000300029904c1009035124a52036002080c2d94038000d066080040d10264441c04118410018440581da120303501d681d0002c5c4000c0e0010341d2582c0744c5807a08108120340001d01102e4600000442d242d100401020200300040b400c034018562140750000c202c1d41c80134401003004c45803501070300306410f0202008010b80882d0604046210380351072480e09288040303c0e28070005103084607201380340c681030b142c458100700c12840401c25445c0014a107c40c03488031b13030704a646002c640c1044030384a40e03a00050030003402e602c1000f5900e90514501d6195100c00c180001ca00c039004684407038106020010a5880e06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 330144721 1250 330143471 330143479
    0x30804060f1412010b0f0705060103200612010509061309062004050d0204050421020a022b3c02090a18060216080a0f0905120a020910050910060e03010209 68
    0xf691914a107010250b01000c1e02203035a010902001012981c2400b115000b14001d807080803a0200d1440c0d04051401034240702407042e0810b001c20365040202a80040c155070302a6180d0040c1e0b101d02d400030b8060010540c99088090420001d03004000c0b06804c07250040c00e15501040d118440c103600c0000c54080c030f0003000d4000140494010140c50960810350f0032600a00240c1c444010302c22200c3d17280301c1380700000b03400350f03004800c418114200603414480c00140282c008800d83c0c44076034204003503204074402414111040b060950007000d040d41c041050b075203240e07202e07090860b401e00046070740a4090040e0320450103200000d00d003202d14010702c80500c42090151440003115601c800084d000301890081c142110035080c1d00040e401801003c0c0b0900944400368040e8056800900341001c40d080140108800501d0700c201903800550303401080d904030780c841041d50764558902d40800c0c043d03100e142e121300071609104d20364910b40000410b842c11582c0d03018103046440c09243c203074807030700f0380365500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 330145971 1250 330144721 330144757
    0x201140907060512040f060510031a150d031713050c120c13061a09040e07030b0a02071a01151707051b0102070b0a152405030907030804060f14 63
    0x44d001410140c1c4e80c2c07042c810f138030400d07100030795449600c1240c1080300d20b42c00d402c1031044140148156401d8482c1c0b40c1090302c115020038900103851401040501c080b0074011524011500100743c02950381626083e4444400e41040c40c0c01c40844210f54061441070303071103018201034911581410711001c0409140c0030010480003044400384106810150300d200c0c03040b0368500020421031400154024801d02d42c80702551540c030880100300844000c1b01c9100c0095001c9074003080098100060320758840d201030401a100c26160522600c60b0002c00c8010304c80212181c00460170702030160b403800c070440c01a44c40b10b001900b60200c0040c41003080d60000c01040043c000d2402c07000c6030901c0134a0389400040090700b010216501e000a20b00d0075500c140c41c0a03100e03000c11a200c450802a9801414805000692400341c1071160031500c0c08516007000300400000018002c09080203100e004603480241e141e925565480002c1095111110007400548141b040600c4500d0850640e40303c60030303800312201 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 330147221 1250 330145971 330145987
    0x10f0506031b0705030d0c03020403140f12030c0702120a060c05161101120203041119060509040c090f0603090c0b070305160c180e060f090604110315010602011409070605 75
    0x441c1d000100c1c1280c06110400c40e035040d011b02800354640c004150348026031a241103142040031041401c03907640c41540100100c240e400703400200d8116a00d8000f41041d940e07110440815281d215040c80a504041010080d441c0000009601071510340901800c1010f0800c50b68102c0d1a0300c111810040c01821606560002c9030900051130b81c100014141401460901e5540000340d8004480566000170102d43c3e0072014240410400158160407420000003410b28502908070f010742c1c4040390245a550340706482d59805501c00c40041e11100e031000711125601c80d40140a00006041241c1800040d040080c08170f4140c0180c81c501540b6803106410203c6018071080001e000040c150f40078659249c00150001d560207654041403071415003c107010303d2b0468010300e0004050280109188450100403030804081403981d081540203043d0b007480e0481d10002490b00c481100c00001c0048944000600c0903015070010f441130541e15420319455880301d8100d82c81360981e11a090104400704180c0e5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 330148471 1250 330147221 330147271
    0x151b0305030a060e0705130e01060203180307030807120f0f050714100203010b07031701060c080d02041a090918120a110106031b12021e0d0614010f050603 68
    0x1640400c2c4918005803107599031110110720041038a00c1d13004500005642841e4410484488000e050360803015000c1e035241000095036403180c1414000f0764410441aa11565010f005200040d0380000b0f2464484150f400d10a100f40d00201022002c1058202a55481809a04c01c1c119614440e19540e090103201d03100c1e8040e1461410044034280110071200f0403503030f0184091070180500850241e2240d42502e40640844015602c2c0d5000c0140c100042280d0f962240c1c603c20200c3d0700031030140e1281001c020a402070b00454000d0783c0c0103407901e0f1404500300410005800c80c030380e0444011420b0345a4803034003035001544103810354194210510030300041d00c0c0744004022596162624052000c8000c070001c0c2140c07002c1d00b040311313081c00146502c1261080c0e17000c40e802404402c8400114903c031a03000881c030700b00894141d00c451286c850a004103a482980c0c0b000540e401c98000c0c04441a50100e441a0b40d509000c2c1c0040200a00008603583c2072800980b44a118401a000c20140c0c0d0701ca096 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 330149721 1250 330148471 330148477
    0xb04050d050a2307080f100207080d060e15040e0c06403f020405190513030c140705190603110c030703032c07151b0305 53
    0x6403158801e00591800190903400b54050b051515000e4040440a40e420f0908043c1550700c41c41e0191b10160000318001d002245000c2034030401280141d44000918181c500b600602081240051810360009503401e9000b403007912403072128945900c0c0c401c0d1071003000211a0301140c03880080e40300440500c0541052700c024450000102c0e0700352082c0c00c03610110450086842034000c06160404170707061013031881c000302101801104100a548413254202014035000107442c079102e500301d04000c8420444064012100250081d10610007880e001300724042100d28824480001860400024288041940401d8103a0350559840302c48011644401d5903001b1104544030180c025200b000440d43c1d58403030410b52240c513203501d402d490380c07130b1480c06002c642072103558081c480001c100300d20403120301000b110640c50341420001401c1000c400715003140114082103007050b2001c0100320700c0080000840701c0403660800340c003900342449440221886510402450800e0207030055140001e4040c00c00307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 330150971 1250 330149721 330149723
    0x150f030708100801020a03020d051006020a030f0509041a030607030606090902030c04090905060906061005030720030a020703110d020609090c0f340503030a090609050d0503010617010b04050d 84
    0x5030509036503e5880290072030b4028840200880d60006120103515010b015030341d4042c2d00a100c402a0381c0c503100c000394581c600554000c0070081202c031000c8000d03008000399545040b0250003000840d0300b003c19072012420203040b85109208100001e0880e81c8130307000700800d030360b40350b9074140f4000d250200844c065040504424400700042c000803980c0a442c0c4190007074039024600074013803400d00016407800c0a2001e000c1501611120050b01c4000340c000c4101c0b030b08091a072030a1850129055001148440f060400c0c0b0100e000c0002c200c10440d03400241801603d020b41d1a17040203e002504026a002220360001d40001d000c0c07044408615140c004140e000322440a668908032825903005000e91016079007104c845101031058030041c0a81402c0d040f050007181c400b040d20740064640d283e03240401004984425100d001001c00c00080b41c0201c0c0030903500400300c5108140000c005032041d0002d0181a001589004145412000d40c03078200303048400503c0042c0c901800c01c81888550030803498 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 330152221 1250 330150971 330150991
    0xa031508030a05090a0e0603060f0402041805030a0f030231030c030c06080618010e0601050f040314010e281703040b0103060e0a050c121c050702150f030708 69
    0x100006103450180010006000d503582d41076a601020010044440580e4021900c0000e44400b0072107543c030006180764102510031040c1b051551b8a100080c0035004031268a4020034074011402c04204002001d4524001140c940b80b0b03c40040240807801c9000f25555a401007160203906a01142007207040c4c00a1140541d01840c6162a51a090a1520242e10032030b4108013011040103055844600c07541c00c084c0c111007803407031030004904045a100c0d041c01103a00030440d20340854200ea011300100c0d281e6070394041c40551902d580703090004481c3d501002c80701180d420618006811320700410120100c0801c0344c5001c40441011008007010604100122450034000d04003501c1c60240c4805544504c1c410b84112210b581180b0701390341580e101003003c12079503100010040000e84045040d41070a031050711141d10f00300c00c0c060b14034906491241302c200300c1100c00c0403643e8681d50010080003203900950b07140c41c00c0740051f10b40d03521074400d1001c1c10300d140d01c041c0007003240343d40f1072216142c101340d0001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 330153471 1250 330152221 330152261
    0x1415070c0c1712030106020c041503030c02121e0606090f09070e06040b04020414040b190513020f1612140306010503040303150b0a0801050607020901050d030504082e0e030a03 77
    0x280c03d035205079100b80c00031400760380003002038802464140522100703c01e000c000091200d20710380d805089a030141400038071920414a4000c1000d8080040c0e0b20440b14040100c3c088100421816855100540364a8018964000045c11443d10400020b0141840500038101d05191080040002c076002c0c02c0c45034860385500200c0466990750000e40060305414105c004d8a046c01000c2104898034600035500540d0311800400c1d044241c0c200b1002140e006580705d81d0030307202c41d0144200910071800122500d65000c5940c40c83d154201011504442c40341d06180301a94801e5800e403807420490000d114501802c200141c400d52040c00030719003140c030a007004120f600c0c2003002c00032221400d4215240e0110081340d43c080c03450f4000ba00710b0040070162210340c5003981e55004540ca454050150b2800b0b510245800d5007054070a030219801000180d042d00c0c850341d00013002c040e00d1000e0300505840d103540c0d116140e00d00111313071040c0155500410003c40c901016072200380c01610650120351080c20080c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 330154721 1250 330153471 330153493
    0x140a02220e0307231209040c050d14060111011503020f0105070b070302031906141512010b0405120c0f01080622060302010f090605251415070c0c17 65
    0x400c0602540c41c800c0d071324071404000400c0c1c0f5055a0405401e044001e60045520245d86070100d8125181240c0642c0c0118a544c20360f8800e8070307207104103090714400d5850800911144c080308040c4501407842642d4a101da205101d0b21a402d07540d690300c180124448540040006142c04103c01c101c480043c18260f0034043c060f100c018070030b00200d030403002203500003040003440701264043d46011201c0d1f00c4e080140506001c10341d00000ca2201e012401826075006140511008000742d80c00c9800310444240325603114070300303101e01d43c01074400d990040c107803900c0c0c40301e141c407001c2481c5607c00c03009814000d5940c0c0000045528038800b5080c03503048140030034203d5540c0e51207001c4140c80701c52858042000c52852000610000040c0b08031410080d02250a1000e241d0103011242c5580f0304045201c4150342c25004013581d0744103a0002058050b0710307440e05404c0d00c4041140030055070000c1e10801c3c0c1e5079070090141c604c0c090b051802040c004c020482408504001005908113040c80411902e400d890 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 330155971 1250 330154721 330154723
    0x6100903080a02160b0408030d0b0301060312020d03050f0412031109040f0603020a080607090605070c0b0c150105030105090d050d020909040b010306061a0403020f150307050403140a02220e 83
    0xc02d54901005802410800c1c012290940900008159012513540303032902d400c072103a840f030241400e0040403544a0b04c0920495409400c02c0d03000d9a00003c440050343d5003008040e550b0005a0304400c00f19051000207448040c030a10681e01c82d0303400c812005400026007400314018240d115555440c00000e0180d0170aa07141ca12070451800c83e10100000c0480c103500404c400d1554a40c4030940da40e001d001042071196000d00503130100c032014203085895070501d250162040f420b0f42c0011124003004940d9000881d400100032071032506158041c0d6259803528180340c00c0c0c5000321004040c55010a60360034844e4850001031000909110b001410700c41201d002503600002620150f4000b0038100042c8244aa40e1061170005c184a4440380c0e6484000c480307030f0b03086000324400a4450b6011038101c0002e42c4541190820140c280c4440326500d151814014003c3d401901055a01c283c600c1c070500c813402000141b010005030001c1c003c2018640301000c440b118085100c0390308030700e629074141c041c07001c070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 330157221 1250 330155971 330155977
    0x1d0f01021005150a0b21070903050a03080a1b050405060912010c080405160e0126060f0a0c020606090c0c0304030501020a0206041208061807170c090906180610090308 73
    0x30040318082008070040e01003142c40e1040750021701d000e400820200588528804103000c0c0b444d03000140003c43d64407803400b614000682c2d80050110f0180920100805034030040c1d42e881084c2d1564200807214111b05900840f000c03600d40c01c1302007002040300b80050b1400d070002e4203000c80014114403101013010603550030341b40342195170404280030405105c10400d0a0102107225249032022251040c0f802c403035000f61240c10f00c40d0040620a205099a4602c2405d00b50212290f8030002c03105a42045d840100f101d80c01141c0c0030a910b4a01b120b146078007440450054000e0030002c4c410701070341d16202c0e5011b61952081e02d52108a01c010000040016821f0010b04003951440e000350441780303418202588404c070034070354920070060b00b5002c0100780d65540911034103d4008209001c1243d851440130b0b10203146056031000ca030740004042007000d4400d48018101401d0a45076000d007900da02d800c1c00302c007000034015100c1c4070800000080c114103214846443c0500c491609000302070307494484202681c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 330158471 1250 330157221 330157231
    0x91306030807030305061807030c0c0812010f0503030403030512090703050a05070906320105091c1209050d0f0606030b040f050105061507260a0518011d0f01021005 72
    0x24000300b06002070503094441c160703100c901a205411480c0d121000744070701d480c2c020401c000741580c5d00003409001d4401c1006100c85c0b907000f00080d645900c051340703900300624240b04131828207411040100b078a04000c000d80342102d070b245d2201810062504807141c85c42c1e000070282c0180b44600e0700000003141042207460a000e010700d0140202c1400d2803501400d64003c0d4020036070505400c1c6413080c200240381180c101e00101b08600300802001480100c580d840740d04000d0758130a200094404403040e0920f400e1140314030424450031008440310040c0d0722002c051041541c008203200f0781001107400680140307100392281c4d800040242c0c990751251000701041c1d506844403480ca500383e80800000744250342c0c00070002c80e2404000a00007040002510070524000c003d00280e03400600c0c4031841d002e8104008041c4444142c0f1080350b4400105140c0156a01c5490440c01e140ca00d4801e5000f0100c4010a000078042d6a50400e40c0b00c061151a20742d51208c0c0d8111b00c02c502c0e801140f10070f5486182d02076 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 330159721 1250 330158471 330158483
    0xc3001140703050106020a030906180302041b080907060206040b040302030c01020d0e0c09090601050118080102030c0c0d030e030412080c1b0310050609010909030207030b0a050f070e0a060509130603 87
    0xc0d0038450401021030350140c001c4820743d40440c0080001c2900034810000300c0d115480d11800301d480d00c1039600700c100d0703040e48001e4109080c07020310004010b454a110110304482c2d81c0e0b4107410303555400311542e6000d5512540015811034800b25021403c018010ba500600a0040700d05e0408801c001c5422a8069103603c410555203601e0224440c0c001d00a140342c24030200c89400300e80c10480f11050729904103100f9541400707281070600703021620082401000301a10340c021512803412594104460380403e4458000b801101c410302807140c000d06c11b5440307004000d8015828103007842052072119081c1d11065a01000c10710418200380ca0400a86204460100703821440003c090103151424070190a0030140c5418482004895150b125203d81100e03240320011411401a0a050b8200f85c02904082c0000398071104100c18004c154012034058074004102c540700355a071001c1145d6001042e0082c83d07028108010400002c0d2042c006071001410040034100c0240b0345500003412120503610444207 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 330160971 1250 330159721 330159761
    0x8070c050f06040c080105041502030601140706061a03040b0f0c070525170a150e060c0c12030613050604111621050d11040906030b060a080c3001 64
    0x1080620004c101c01000b0040c02488613041c9139480b5018200d11680401c42a81d02000203081c0380c2c07150408181801c82c414074641c0d42c226034149940640041d01030500922440702d120079404051038100d0744140e81000c3c1c160455152030031100381d941005071810024440502200c0c001c41e030244560141d003032100d29411030490074285a0102e040711540005c4c050f841c0d088402202460104101c1200c0741d00c04007150321108801000c8004001d00200581035102d5442000707010810640100070b0f00118904031a070510074500c1080c8a484100d802c581c000582d141b9016914a0307907005543c0000c80100042507035507101e02559401d41008028000310f0700c4455280050080b82c1070250703000602800d1001c18510b6003407026000b07200306d4480e007103810fa640c0b05002400710108280e40181c000c00c0303820300c080343e0b80f0708152003800b030103941c002e118454800c8000780440c400a407282c0610005403003480b44107500100b882e5030120b51007001045a1807100c076070fa078540707080c421074030094485084001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 330162221 1250 330160971 330160973
    0x1170627070f0801060e0f180907091104060e010305060310050702010902130501060f1107080709090302010c0804230705120a03180e0a02030c161101020c041b08070c050f0604 77
    0x50b01940c0801d00140a4000010312409521426042d1450016500c0b00107805040c00441c0050134048820780c0c0041c12a401c3c03040f007840c003041c90406c40c0c4c9180d0040c00f6407007001d0780c0f0346546c0c45a4880c51000c0b03880514080d107130b5406078010300d80c4180014107a1b14001518108141501c104448280045c0d41d548034510441c0b81c0201079004401000400700076660402802414048a0605070410300448440404d00348804000c4000070703005100a880703881d80c0d2000c44102520309207008402550a28400020407845905a14403940d003190719000340304001c128038121004a0a8030b0000c41c05051804503c0382c81e14010140200784605c010000d404950034014440b00140a105d41910a04402007241a001e0185145c1106074101c0c010303030724ac44410a1264074805c80303400c507d002c180c041035041808500e5001c6030f807021084c0c0079644001c00b60780400044829407000600305061030402450305a204901c0294000389606041290300c6081d100e00e490000c0ca0542100f0503800542004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 330163471 1250 330162221 330162227
    0x30903030b04090b010504140f040305090a080f060a0614010c0204020a02012004080c09092d16180e03040e04030507201f08160216031a090c0117062707 67
    0x803248184886000c80507040027881828480d00142000d0100400880c2c00d000b103582c0c28080c0c0000f00300480485d042c00c07400d481c000d9111501202c120582c2454500c0000d0720340052050800100c2c016503841c10102410303070801c0000d42001d903880085641e13441001214000056607284800084081030361a83e2608030594940b40c0c0507003215000d55407820906c51050000600c818148800e0302421008440c0d205a0340382d142c1e00742c0e0301a519407041001c8104644040309264090743c0b0754401951200c003210206105441c00c8004041c802d50041000304403c04030040000d0b0090305c0f80c940145032181c240c4418034180f8500900107407211703806000360902d00e80101103161154103091941d218007107614001d095982c00034400c0c0b00100035454080007540c403d0004425000c2703c0d034100c200300750300c03801c2160700804050301c0c000c01036518401040c0c61801c00103000d009104165242c000d000b420501a0406030006800190420002e60001c12a04850703040740703405030079400a1481d80d180c413030002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 330164721 1250 330163471 330163481
    0x8090102130602010f0c09050102102003040b1806010b0a1d09100f0e0c030402060309010e01110a022107030f09030c140f0d080405060a141206011101020301080d030903030b04090b010504 82
    0x240047c4000410200200e9801042810714030b21141400076408514280714661040141040031000700004100300821406400c81070140c0d40d2072514800003050301070265a941c2080c000d01d08009001d0042520b00e40c0b244881070048140300e060308406000d0340e4041440d115050701d20384c2085912541c00d110362603149140c0d900802410501c0201070074401200c0383d00c0e22025101a020ba08000000b804280007500300600c484c80020007004032511707460a00c0c0854004805003001402280205030300d445158880a001e500040041403900718a0b980c243c030000f0007200d021091002c50040000803441c0060901c0081c000c451680740380304490300c04c00c202c0d4440f00000510500201c0c0320390010440c04829501900c07400d8590036502d0b06104020f490340700c0701c0c21024080c6080000c02035030b800c0d02d50588a010340400c1e00d5008842c15001d0074203090340000d0060b00416403080b0110b51780c0c140310b038008240043c000d040c001511451800407405417611414151500340c500401004141011702c14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 330165971 1250 330164721 330164741
    0x140601120203121206010f0c0c060503011401031e020714060903030f071803060e0c120a050708060c0307030b0f10080708090102070308150f030d0207050f0a051008090102130602010f 80
    0x1d19260503070300c41c20904c03072510140031070b4104000c03290322118240c000ca443c6495150044c3d00f02c0201d6a49250041243d8024060500850b02e501208403265019000d00c0c00006007054032000301c2d10701580680001e406c136a00c1600c1c00110500b010034003040a00c0307258002d104042c0991390b24500160f04c0303403505001414800400c400600344c0c140e14045212a007050702d90148000c640e0103d041002da03e01132202c210241d02c1003810000602a01d4001000c55191317128006464256580d00032680e1540d04c201c403040b508140410001e00d03814403e601c40a10600d009280c80c007050400c0c4041a415080e58030714101040300b401c140106130b90414000d59001c00700a009500d003540f0340e43d00804060b40540307140403100d00c000b100081a6540c40481140c494064110341e450703030740c0d1180290baa01c0903118050240306c0803640850a42000f0100d8403d4820103030040c8030142010b503080311440001030000b03055542c2440202942e5000110800c0144110703400071400e06410f042500803101c580760 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 330167221 1250 330165971 330166003
    0xa0204060510020c0103090311120c0706020309130f06180507031407120e030706110406030b0a1d060f0907020f121806030c0f0304380112140601120203 67
    0x81d8a02510350b0000750300c0040300b02840d01080400451030180c51040462009e0240307070080144409950362020301401c4001880000c0300d01d0b0a42d80c090030303a100e104592a07185c000300d40d209a000c00c082e00b90400d10b600e80d8a5000080c80ca070342c403174150b00000d9207000040900d6444409000710280e150003030042039254011219032504003024054030034880c50001198042d141c2c032118901c01414020360765415003000d803e000c0c4500322000d17109168454050034000c81d20b401070602c410704101d46e0324402e54480003a81d5103c41e404136129502c00c0d000410896010a821400c0e21890305c034008000e0140c801d80c0c006102014041240f81d052120790030348040009000e1110b88106200f002c5c15010600080d541e45580703469800c46e215441c0700304003950a55980010500040006040c201000e070790400f050981d1000e22800b12041c20101b10544101111010006009281210307100d402042c0c408d04030050f01c2c8102045240c02c00381c00360b010f0fa82e03503114410b1080960038140300901304004050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 330168471 1250 330167221 330167239
    0xc0518090610110c15040f06030e1f1808040f120203060609060a1203080a050c130b0d090f080904110a0f050d140a0b10053f04050a02040605 62
    0x800403400502e4409610810001012000c1000c09014440303c4071a1101601500d8001c2c0d0109000300c030399100e4850910808109840080c90328030a01c80d29511341c03200b40181194401d0024124011540d400b100741c2c921b40d850500e0b0b0b090096900d00c03100034a00c140405501c0d1880c182c40785042419a501c4a010300c07501c8500800141c0e80031a031242e2000f8111109141516007001056001d8030541001d841140d5030141e0703009040c0c0004045100c1e50000c079092010381e4070181b05584500130105005120031040760184040b1281c2c0c0302810317040480e08800501e82126841e2000b214a51100c02c1e05c0460703002038400d146003858040c05030030360039651980b40303011411440104600300318004c0808000001c901c503511a071141d003000c01024040120300d0110704000034240020103c0e20303c91841050410010303442d032809641910070b1003150400d415041e0750340b1160100035030224000c610315910002410001745814a20311030040340180006c225100b52841440308440f800e40003184580b401c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 330169721 1250 330168471 330168481
    0x4030905090a060b0d0e0c030d181a0706050c130603090c05010e060f07150608010c080906010f120203100c05031008010915020c0703050f0a06140c041a07060c051809 73
    0x4a04545c40300e184501c0c001403a442040040b400e05958900c4c40350705000e00e0440340b07091540100c10f03201c0301c080320010849103030340e0702e808800403443d0350444543d0410602480d00800e69543c443c13580f049036034a1840c40e0801001e80141c0c4442907411940109545420f06000c0c0a54072540c28040c140a0920080504250002582c940204441800e2910700002c081d8200324510020211503804030a0500c001500d0b642e1060182a403030480f040007403841c03070019200e040005910382c100c50400000456442c00e1085800240d0380c151006d80c2c01d88a00303000d600c01c0304d10600c11101440259030703869807203040c590000364074501c1d50390210b003003607050250b40300108103030114980140c42c820300011307580d80b41e00101074203051417940080c001d4080c080b01071580d40030104a007200184520b404011001c9030000c48803510000340c800500d0039605000901c50510b800c810a1110081c101c103d500300700302c550340c03641540c8407100c8090000f8408140d4079035001c001400d145615000301c803d48514500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 330170971 1250 330169721 330169739
    0x120703080a0e190303180b090d0e0a05041805072603040503060705030711012a171b0d020307021b010e0108220204290109030b010e150904030905090a06 67
    0x403103a00f07220000e918400080815010390700a40031040039507100d088440d990f0400315402e0f6811600d8000d01e008500c5c95280e00d0744201c10903080000000c100d00300d4182410305000041c45e044020243c4840c1c14070300c5e1004a001005900000e01e14120780030110169607658400c5a5000540341c50164410312090013a40d4010807400d0784100f02c2c1c07900c0398403952509000c443c00c286014582c01c4651900c05400070054401840c01e100106003c60f990689840502c21035444500380710265001d54080d0108103c030b0961f981200aa4021405490911102c808807a08aa00c00e490350009a40030f020314001500c800d45a110f11a0f07024203000b8120703c0c200001030070b452401044810402008a0521340c240d440240b059000d82e00900200320191081030030030303044111035a108501d5110395036441015842103da51040d0380e400201d0314200c0e464840c08001d0710801070801c01031080216554038907a01c1d540001c500c82d80c026580c0c254030618090601c440801c0141c038103442d0900300300007070015543d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 330172221 1250 330170971 330170983
    0x1303120309020d061d03030c271906020c15030c07050307081308060106090602031c0e0a0b180a0203070e07020106031712100f0b07020312030c04091401050906010c060e120703080a0e 80
    0x7401c003002c2081d275000c0401d0010600c104e5a585540034040446a803407010054a045040c0c400540848000420031000c000f5108a800c200c074500720302c100700103518041e541001d0001a0b02c02c808032428210b01f0303541c413261600042c6103041614480542003282c0f0301b04000950040034241000b00c0c20505000b4001d481340300300110b45105000302000d80c1350f1603209500c1405990321a90541d020440285444258403105480015410710003812841403410040f40076400181c1c02002800a2481e051103040f0144000304540c003595a2504004045030340c250400740b14480d50084d1980c4d03441140742e646038072880a0070030110030320000310078001c02000401d400c0541d04481d04454945044e4400689410410104550001e00104c2444140c0301c05c3c81c0600141ca0000c0d4040c426886080c2c4200d030181c03c01d20440c0d034031090840c0400d480d9402031070000b611030300038071011850b515121319041c500f51409860350500000040e100c014154003800b80c5401c004589402d00c0b841c52460007807a5103c07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 330173471 1250 330172221 330172237
    0x20d0302070b0112050a050f151005030a030c080702090103120f0201050f0601050f190503041a06030a140313030308062d090705120702150c1303120309020d061d03030c 74
    0x4c0d80c3d8508060a0000c20408204c00d140d012086480054401c42c40c1c80d200d40510410110b0780c42400082145403d0101d1054182da10240003402c00f84820303141180c24410707804054030040c40402c03001c3c015880d000b00540c041d50068001c04010f00031140c00416140b030150701042103926110074491510398080f4410f80001003440c0954130b48540c1d502801d900d11030f058024075040300c001321034844250080c003d18402c2d400b42e803202d0f5149990031203052030070204450f801d61641001441130001008a820040100e041d082224149000034480406406007504103a010546a00800c03907903290002c440e03100d4452003110784400e10580c3d0382c850280c0300d46103411449124040000f90031a0301c500d00303540c50307601441c851072014100100040d403100702001800000c0c105e16400104203050103c1141e01400040201000a40c0b0b50703115a04184005a0814200354440244030050b0b652011091186802030b000041d07400c514007159500ca00c448203180380d160b0024420002103040040a41c1c2c085 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 330174721 1250 330173471 330173489
    0x503100b131815031a130507050d06020c011814010b0604050904050a0c0f0f2111040609020d0213060201090b070c0f080a03050a050105031903140405090c030403020d0302070b01 78
    0x40030000400303031440709540310f2a1008041e000041c00200d03040e40001e4a54031084103d142c070342181060f400302a075000a0304a42c00f841c400c0005007442c821402c4168000c0380010704080c038031903066094a0381061b440902000c4100741c2000e01c07080754207601a68141200030050317040200041091030140d88545071181406600003003e1200030f0100e4481e00e644040c041002c592601d00314080407205000e050100c66410030702040010ba4001c00c01f01b0820703441c8007501c0c160780d19524290030705e21200c00039800544840000aa038005c500241918200c1070001588402425031080f00b1540c40d0792100085a0504144c01e012030384030b15070182c1100e814a841c2070390880c103007421210000134020003419000f000942c0480c0940c998491401080e0420041c012660703100205a652160300c20002c40303070b02d0a100a000044d000d9203100d40c0841152801d40d0401e981c03100015100d980c122103001540c0781c000200410182d0511464041e00b0305400d0850400240f920f4206141c0c2050151000e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 330175971 1250 330174721 330174749
    0x10e0909210436060305070312030216020d030c060606050904110703090e151c020306060406050a06110f03070c030b0a0504030e0d080c060403180605072105040f03030503100b13 78
    0x701c00d54501400c0240b00c1d0b004140301d445e03034138a4480c0d0740300703003610051b500c0003c40844d01c4800ca2081c022240e06150700e038400c6a810078180c0030041a180320320421010310000c1d07003000c0002507c80c0141da0080c03d45840f030588440c50001071000761200c5410081d10b40c58100720201c0000d400855035000c1daa00035404540700da4810315040c5201003a4084550300a9a414180185101840c030b008001803096080e1080f03602c0342c3c0240403d549042c083c196200e0003500b002d100b04c41c40342c2421034000c1ca8400860301904244100e807030565111540940b030003a504c1906105110300d03025a02e0308407803040000c02c0589001e45006007400007615410748205107403100041885640000e9881c150700d100b0075107055041615000d01384604001000300c0046408000181c000d00410641d903456400c0076070710002461075256800440c16600704034052000c00e01000c0741010305412001c015603c29142c0a80d64100302070007502d80d42c2c181e813020902000c00c11584a0103035600f0050403c8030241030000c18 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 330177221 1250 330175971 330176039
    0x712080307030b1309050a0309090218060a0504030f050a0203060f01061e050c2a030309030307121413080c0a06050d111605070f1502061302010e09092104 68
    0xa50043d07000040b038070714108a40d14090082c0031a406801c123201e5156070303480300da441c42054160700a44160b00021410080170194030305040c001041c0d24070203850f00518068595a490814508440e410b8500b82d104035102e400f181400c0081a803c001c041445160a41c9800d1000f000d48e0007240068001c412556110051180140190380080407060141d034820f041d0ba0036142102a6074504213048400b08202c410107600700841200c0c07184a0140c0503500e80300084d26800b00640108001d4070400080248403405044008081c103078021a1401c82d04000e0300d41100ca51401250f00f820307500c240000401001400c0d0014110350030980800f6020400305819146c00f069409850403000d0180d6101501c5410090003040c104103581604100c19421034965000e050012501880c1401582c0104082030516051010a00da410300c140740002c4500d420320701060754942c1c2600d40c00c00303d912050007d01d200055480307075030300100b50f000c2081c01c05d0314010080c89010a01d05c2101c050800e00d8141c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 330178471 1250 330177221 330177229
    0xe010b070c03060e0619110906030916031a06010e0d02190b0c010f1109010e1e2e020c21010207140a17070b01090f090c0e07020712080307030b 63
    0x1c001c2d900328408202d0829070140480e29000c0c11510304280100714161402840118070900103003a0b6201d06031820709200d1028481c541e80044c010108520400c04003030301904d4081405c802071849008800070b00b103400d9905000c07000303010341030906010300d40d83d0100180d1220040e00d000c03641c040398501c4000c2c035403111400100c50180c00404803284001604030200d017054104500f01c03c0c40c074034100f01000a0000f4401103000f4003644500040a5030000c00395403600c075500c58481c254180586c03024901000019460000d5010001004441f0a21034407a4602da5044400d40d50306500141c01d106464800144025402c0395000d10001004a803c0010450960683d0b015540c0b0090407512601551034140c0e9441080f80c0441c0d80b09600d500a103010440c00d42540d8101d61710140d5004cc42c0d0a20406901400304000842883d0340d645400102042070308030200003d040d41008449142400c0d14000c0c02e00c1e000d41c0100700c2c2085128003120000342e001c0c00301d076400059440c0018a20030b00340005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 330179721 1250 330178471 330178493
    0xc0f08031e0f0702030a03050918100b090102100212010e0a0e101d0f01051b130b1e360105190c080408070e13050604021504080a0803090d090e010b07 66
    0x2c1c1d050b06c40c100c111420540c101d002480b2000b0119004181a01c120344100ba080400f10b0b101500d03050000300403c021030307110010305054001401a81d20b014400b1108038200e0f00002c10702c10540041d14010019251015142608000d42e80c4052041001840c03549a6510340d0010f4581441c1d41e90480e010014100521440404078050517120303a024141c24981c00f038102969040d811b000020558986040540100e4000704202c04005891500d03011041c4103903005032540d6807011009171041c0c0e2a070400d943c001d000040b4004410400f500240d00800c404d45074414014a20f651100507200030341c0e07040000c2d103a03803c810301144c05a0011140044071540049000144800c50120300071400f610040b44071401c3d18800b4008c41540e944400d0344074004003652801a10a4110740045009800c040d01000c0c000c2c14816400c3e0725060755001c24500e0102030030000c3c4c3d2401d10110130300c401041e060000c102e0207101460980045030800204052200c03040c401d107240741e4800181441006020501 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 330180971 1250 330179721 330179723
    0x90f0a080708010504150606091502010f050a0f050a0524040f02030c0d0c0801050a141914042a1d03031612030509190201030f0203040c0f08031e0f07 66
    0x2a540400c0d0b503001624003078407099904a42c3d100c0c1d0071001720803081c0144944011203130603035a022003291038103410341e0800303075215807080440d501c0d49180400200345000345802f4010801000910a0101040c1c1d400c640f800360003140702c00e05250900a84907245807a044030145140c1030020b0118008000400070112049913450080c0048104105900c0301d02c040c000a102890060003042c898880c11240c50b00240162640490a83d40c03c0c0031100e400031000c4131032440038020300c1003000c2c5403001001d0001d0315070200074000e04c5641c6400e11828603018140011917403442454807110070310020b2500081b040c00c0c581c2002a00d48210f034040414100e001080b50380034003900d0307813002d00e00c0d02d40e1014030001809490020700c044003100560321074070130a4403800781c24000d448540c00f0300c10003400701481d40c00140e04054880610300c88002082c4011401540710754080402a484d007400301a0118031640660203580060082c0c03401c20550362138240c000c8070509500c07565240c2000310b424082c080c200c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 330182221 1250 330180971 330180973
    0x1906030506011403060c0708030c031e0c13080105130f0f1a040605010506030402030606041805031803010c0207080d080a020c06090c210c0d0822090b1005090f0a08 72
    0x100429240e200c407801d010b013581910350300d6a0381303407054201e4402c0b6030b402002020304000180c11300c06664051600280325172603d8440460303052001075205c109950040b03c8682c000303400b5001301c8407256004010007a100091085107041d050803041c045106501900030f0344003d2034142041140c60b0070303590130f5a00c000c81070800c6202c000d211140c1c1000f00c504440d62440d0100110321440c4c800190380c401c0394004c00504107503455009110150004045140c03010366604550000030340d00380040c08090f4565031005207600e2100c42010300707440452000c0c1c42075400c034a1060000ca240800c1c005418030450070100ca16854012581c4002c1c800e02130030114a0055400f80680b80b000481d000e400000c0848440c40e00d50700c15084010181030445400f13000c0d0b840100386080e242842d0b854281c6040c05541c4c0e450410311854500c0d10311418000d91203901107030348601400056a2882144200c07001516004500010100090214465582c07903d12400250074800f405555401d80003000c0c004200c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 330183471 1250 330182221 330182233
    0x200a11030406030b0f01051204061e0c0309210f111006080a0201020d140d050402062818061b02190902091509032503051c110c0919060305 61
    0x410010001d1420500845c411600c450142105600c15416180d0001c1e04a50488240e10359944000c014a0b00c1c92842062000d910465071131100244a0341c0c19011041e200071400030410300d4a041c0f1b038a14021685845001c998000c040954408180040c400e42800c01211009150b80306520304210b4140c2c004046040036400320b00c108000c188029000c1c401c1c1c003160145584480300741c0314600040040003402c0d40c10b00181444000301d80225400c180041c04040ca0b000c404203282580340d039031000704c10090351140d20414150350b10602005030001641e4005500d21306200e0001c000300e101ca031a1440c410740048080003035680e10016884601b00c140c0408441e82e41e2080d03018042c1d0080760449108407041009011160004022140c0f00100180036249034201d071031140311011940c441d11a00d01081401c04000210300300100ca900c00b010840c01c00000c1101240144803084403818803406421a80b0f0712001515801a510b4202071024441c0d07918020348400d00004003996400903140348240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 330184721 1250 330183471 330183479
    0x90709030b04061a040501060e010302090609130e061303020307030815120c10170a0203190e03120c270301090b101a0309070306020d0219170109200a110304 69
    0x165000c080d44c1e48501954404511154080108664003481000040b0320417501c201402d43c425401040250701c0100980d0030f20504001140449400d1022200c032203a4544609030901c0c4208401c030341c485040540b038025509a40d500a460740540c100040600c20800080b880d4000e000c4841c00d2601001b80890b03808000885e200c9694505280c2c00b035010702d072501118a5940e00c00d10061000c3ca07040c3c01180791a0b01c49090460096200038943d0380820712242c1ca0000400705030280c0041ca0725168020b68890000103221b114101010b800c1d0500242c1c01c020a00c451164160094a0485595103c51270a0754003000720340503066504004100e403012004000c03c49401034040e000359a002003a9508410230305204071003d01c02504e203c0380d40da2020200304002140f40d002002c0c2480215809810001c1c0c11100010240e020201100400c010200c944664140501c0a50061078640d50a001359105004011503008000c074840c0410f040000360096902d0007002c0c20030a101c180c000316551503544d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 330185971 1250 330184721 330184733
    0x31e0d090b040c2d14010e030a0503090a050d02030d0809030910020f0d0903051e0703140a03031406010e06130f0303050a02010608070605030c1804060f08011803020309090709030b04 80
    0x102d00a1391144141401c90030304544400180703690801180048146031400d181402401e245107007840350400481d03460340310650b02c040c0910402244210021520345c0c1d07000741040410100d6421150141c074012500c480560b40018161010703000d9410912803a48507030810500314810203c18941028100c0d0b0104e05050340059400050f03907624040d0303002200100421104041c1910000e0441d9010030321031610100040166075291040000b1101c00552384d6489288a104407560808541c00c898030ba04181030701400340500c0c84400b22580035251400310700182002c5018681c40e406210b003c900a4501c1683d0740303100000e85140c5240041c0c0564a1500402c60391200b12000c1c015402d00c44002010700001408a059410b640c44250450f510041d007071f0860742090203c501c0701e0900340341b8140c00340c03990300c81d1901401019843c2541d05080c203c40a00b502d44d030740717244c5100c8182403e600c40801e42c0841034039052001140d18003903d0715101401c40f05484c503900060072610301c0209000030011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 330187221 1250 330185971 330185993
    0x30b15010305010b1315021c0807020d020f0601090c1709010b031009031707230d0b03070f05010305090f07090507170402150f130305010e0708031e0d090b04 69
    0x10240d0701804140e07290303122140d15000e2821500c001d43d102c0141400a16044016105038040902c11182c20b8189600c001c00c074000c00c800203001203200ea0052218165052042c07210400c902c8c0018141d082e9001021a5555414420b0028150f5241c200b508a140718202c1a0440405010f444405080489070179009212021489101c0d01c42e0740e1150200090b0740c0900d191540d05074443c0b10100f034188800c00b090b401e0040049003084901d03014002d0702c2038111602c0103842d40d803900b010b1b22032504038404400c907017083d00007901c00d41c041c1900f0001600f240400c6010f4030300a280c08241c0e5107070040190701c1d04500301c030b030f5114038019414041284289130b0720070380c030444042d03845c034440413001d02400340300c00820341e00a274000203e0800304803001c1c9008020320100c2c41c0d400300355141c03580b070440380101200980c01c212032a0b5124030f01000c07403403c10803d0034042d20752b000c0038510304007500f03100e903451118218856202c006d02140ca9481c0c00aa980720300801034210b01c041c505898a49482d800d41c035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 330188471 1250 330187221 330187261
    0x10091103070f170c031503060f041101031413020d140a060b090105090a05190e03190215040609020f150d06060f2001060518010911030c04120507030b 66
    0x14060404034060b0b18411040c0c03000f0a010f403004003c1c00d407140b0034108602d0740700a0503107407122411055404c568074100b04d010302c07841d500c124109040c11300d860140ba0ba028032170f070414105414190840b101200c50031011350400c04094030070b4502441480400d00004001201510501500c034031103040d203201051905415204000c01c011445140040002d04c1c0f000b0b00406030052642000121002100c0d405250891805032188180780c2c143d003070b5070043c0e90703011030342d040c160f00086035201d4080b0301500846850701d100e0028202c02046c00000941c1144018006080b440e03c40030880b096481c1c2d4042c500c8980c502400d540d0900c101d01c1c080c81ca00f0342c070006400880c540361100c00980184550310200558003a5a204644891109141401800d00d0000485255a14200055160b80d03070221546030400c071014510b41e561401c400041158948508146100010410000203446c418210b5040e03070401c41c03a484600106080041c81c0c00400e400c0106040c0c203540902042c0200d417100b0345d841e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 330189721 1250 330188471 330188477
    0x4050c030f0105060a1413030803010602010c080a1b0804080708030a020403051c05090d110d03180e0114060a03140103030e0a050a0f03110d080304060b040e06040c0605031009110307 80
    0x142e661907043c06054800c4600e124005841042854418004000100241c4202c113805441c01034030307a1a1300300785900a03480070015039034402c9181c100c6030f08071803155413161020350100100901c5011486500411000b003d0400a42000107010002d811007510300e12604460820307240d21b004005d980096000b40410b80b414881c403804110307003103400118419100300682c0d440341891091410704c4100000300c0e5049840c450b107810348290b191640032055010383e00a45d20610480480c1d5104200107400f40c10450401e05841d00512504c01c0b01c000141c54800190f8034181d95504d0034500f20004c0c0807000c103c14008100100000a05a1080000d240101c04440d0201820707550005c0010b002c90703510450074001101070041004c9900384054000300c480c0500503045003403c3d0785d10f031901c075801150200d40316075980c419403225041c00c0c41401105d210040c01040182040d4a81e0040d00e0180e1042a080090020003c0c00d100b009022078002005405000c1c0047c180700b601380f0b40103030802c952400c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 330190971 1250 330189721 330189751
    0x60c0313210c0501080c0c0102031003031b0c060e04020405040e0d0201050702031c0b0609030601090f0605060405011b031e0512060103020316050313020a031505180d0e0d0204050c03 80
    0x4581c0004007100e01107034410400824a8680401902c650b540107200740000401881484c02d0307124280000c0d441483c16201c4072540c3c500754030b4087e05103038a01d0541d95030344950503051130009003c565000155074250400810b9440c074080010083c0c031550700420b8129040120302c5211020000f01491002100c0e0001e01c40380d580d501080365a40a01e4901c0d134905a064080804001145d90003540150006481c841c941107485003c84e00d090b44c2a03102c504ca06a41d20f0911291801d64810b40700544002c840c460b1030f061030000000c180c80c1e04101010003c00f1594402d01c07c05000f110440d20903904507030701ca03460032426440a0300641010311031070644501c40d00002c0e607130361280c0300301c0e0312a000340004040a0b6517003600c02c4890fa040113020300580c00c008444440566103080c02c14006601c03580d05e80e44010b401d29110800e4540280100300c0e07155907426810301160340454420721074031803442e20301d40864150001420090012034040d4200b1f2510303040c840f079041e1041c029031180f010a076101f06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 330192221 1250 330190971 330191009
    0xe041103090c011107090e070305121905090d201206070206010312020304054516090b220608040b0103112116090506030604060209060c0313 62
    0x818481190248095040980e404050350f0180c85201c40b0020400215041760b6240c1d8040d80407200c160081d0000c5500c000b5042040103001c10a4200301000e40d00160f0600c5c0c4011040c0c603400d43c004102d1024000c1c0030803a1600c94951142175403940e900b080030140d810351400c7c00748130200c250155107405008007600180d800b207030010700d86000d1321965004142e581c3c69512441c404038140800a4118002008001566601d13240c815041502c5001000024000100d290640d140480060107541480340c444101c0e020f0035412142e40003c4d00c125111103542404401c660354052074003d201c00c5c50000c034003680880a00450075a214004c1c102c9100d4041d140d0301c041d14007580480e0002c03c004005001480040c52807050182d10b0840030303104020a10711214081c5100186102038582c0350301000b0a03080350340704501600000c080b1140108036034104400131a03218080100003401b000d80001740f030046600d4040c1241e80a055520569440d24821800299900041d1182504008a44070405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 330193471 1250 330192221 330192251
    0x803150303040305030d02220e060a060201140a0f18080306210307020d0f02090405010e0606010903030e0f011407060b090708060d1b12150608070506180607080403030e04 75
    0x5015250413000070350812121210410182d030164900f0b0a042c100c000e10303003010607a10418400500b900c0001504585401d0092007081c000c183d00c50300844e81400c14403500900781c04030054004000007004194884010003600c0a080d2040c0540f44d03c030030303117240002441015401303940203140444d5810002c19030648144005035101400012980017041000010716004145104c1c1e01c4c420180c1050107076480c0c00181c000e24013224183c81d241d4441d03c0410200400344183c0744d0180090810108040c1036486c0100802100b4a03002d02516400c5106000341c0c2c000c071030010b6584000841140d5882891a088018003008034495011791199800b049282e8040e00301a845000c0140c004201082c0a80b50880d010071001c0304021010348405022403264101c0000c00d40240c0200c201420040004030420201e0b1190703400740d4103640110106201da55141811034030a00a0341603215914000c0d000003070350307512404800801820b00090000200354020344240c00540342100c041000c3d10600d0121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 330194721 1250 330193471 330193477
    0x6050306030d1101090f050604060c18090203040c2103020c04060b090906040b090915100e01060503180106060e0301050609061c03030e0106270212070516050a0803150303 75
    0x14903850b40090140004291042101102d8040004004204070303080d900c994161001c002c10070340d45030b0440c20822003030100b58000d480c0700c40114a0b00a041ca8408880121041c1c442c1c0502c900c016000008a01404400290000545040c69642d404007a841d6440035610401c60401c0b13003d40104001e0f52080c0c689880741c982150f00c545111858000c0c1d19040041e020402441740fa4403555403040303015141c07200e1500c18801c2440700002c03c0c5908508544074114900144001c4965040d48030903c0100c848540c032604442081c10710640702d859a01c4072044499010440c5a65986410000540603502000d2000c9078142030b0000c2004e6181ca8042c04074698088603c41c1d04592000b080708034081d070082c451341d00a030280c038001030401006c00c0c0a13825107119074410003400940c990340358016011076030510822a0514030441c034021103d402511640c000802140c10300c80c010442072036035400321207101a200d1340141611301007041ea1a04110707507001a0b0301940c82c00700300058900a81800411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 330195971 1250 330194721 330194731
    0x50306010c020409031826070803090405070915050d110a0e060918010f030b09032827080709020405060403022407060509060c03040f030c0201090f1e060503 69
    0x8400c103078600780e001d210103404404001c17820007420f02c50340c000c4c10380b900fa00b142c083c003030801020b240e0f0780510720300600551210390034605c0341e08400420018100d00004413030404e04280c2c0d000c242d640c0d4140d03050300e24200990040740c510340642446281d0503030190062400405e44581001010680304050070385015807210321000c41c813080e030420003d181c501c001d840903481c002c10145010700721882c568808074003079218844681c007224051040151041b01c0907440050071008504103030052003907600c000d035280d500a640d03426a10414191901c80c9850241800c0d44841c02c4010b14a40c0142c0032000485100d43c0340940213101003c18245811f008980c11904000c1ca07450406085400f0403150303640d416096446041041182040030022801421046014000009a525221191500300b160050250700c0c501020400c01c0000340e41c404842c240b9036054506030440000601c0113a541b86501c2d0041d00d80740c10400c00000f18020f03510904d12111440310b00c6c0190007940c9240c156094081500c2c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 330197221 1250 330195971 330195977
    0x213050406140f1819050109060c020105221a0708060f010f050403060e030705150f150a06051b1009050c060403110603040303090804141207061409011e0c0b010605030601 75
    0x1020401c5620804e0311541c468902200381c400143c04242070014086501108440c0769440b5a016014032607030348103101d450340a50009200500d48524a01101098008040c1e9000050910b000c284804801160b03540d8038010641c05030303410500c8028100032000c45400d84260900c1e01080310552240092140e0741069441c0d4504190841e513560b0050021105d000d00188000d102060210300100961800c8140515001105041c03400308982d01d41401400c3c0d4810b0060140c01c950287c841ca07100c2000c0300c0c003e00d41342d41c8882140d684101c0e056403504415286118603500d142c440800340e0b201c0200d00c0e01c135204aa295855000c00c0c0203541c000c0e032001601b1407403086800401800d114000b142d00074801d14002503100c0c3e00f40d44070002a0010b0300003aa1401c0c0f01030242c150313420a0790000b03225103003100c01003081502d0000b004140b884210000003841d08007003885400769000340d16946000c0c2d403800c0b101c80c100321501401400d20040050640c0c3d080784080c0002a903a0180084900450045c2c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 330198471 1250 330197221 330197251
    0x70309020616060b030703080a110607090e04020303070b01080706200606190306090809120a020a060e120a080d0c05040311060307140d1e02090604091107021305040614 74
    0x1002c0054040c401e45080d20000e840e00c108210701c0e80e003844204041c4d441000b065480340c0303a52400a00da040c410300541c2c500e038810380c180b01d681d6400c601d01c44200c0f071840304410b80303d039554404241140102c541c01000a1146400411030501c003140703070401d494059071400c10200d201d4203568244142141072054503044900440c401d418070004401000794072620070442d07196203559600841e00261400c2d1440d000c0801c140015180a10b07110001034600d6000741400110ad40004290141d80c1c8207400900c110200024030a884981040c00031080c88415100544894240081c1c3e80d4071850011341e6403450304941e40c42007402070060301d003580d4000481c5410382d10103c1c1401407940c80940410244030380080445540c19440000340001440d2030b0005c0b800c001c2500130013130302c0c1e0010300e0005015401803203580040e4695105640480da071002000c10f0700c40b5032082008092042c4038001e9003103a043d030b02c4000c6c0c03080c1c680c10003070090b48038050410409900f0324445000300e000b6112000079440070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 330199721 1250 330198471 330198487
    0x40302101b092310021005060f090f1008070608041a040812071e1d0307290d060e07110105100306090c09180615050603011502070e0a05010302090703090206 69
    0x365101c50029020000800b200c01c1c1001c3c001011003003503600e1035005902034030100706044154041c0c1c41d0001e00907036a440c4800c407902e00007021110010308182c48038141400240c200001d00409400030410501a42e00454a030080100f000300c0440e03040d510310000c5207070303881803c0400c4900c41c815604509107500344450001c0d8220300300c801038050010480050054400c09240704c1400f0002d000703d480341d070b445800260008554480c03000b561882500110030401250b40c84032007a9801d02500c4400264218401100000c103005807904080c4441c82d0140209d01000b510030740274060036842c2c40b01c841924804220500380e900c2200e02000030f100264042000811541003092900e12648449e1000c07a00d070318000301101c8002e850881d074680740078000c205001c054456064000b0080807100e041c1c40c2004003155a510040c4908070300031450300581d8480a2081c41324030b02a010f11403142c0b003a800d040c42c0b4100a01820300042c3d10804000010440c8640230788102c071a641e5014200300c4c203000103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 330200971 1250 330199721 330199739
    0xb220e062203020705130203011d07050901030b0a08010504030206061c03050f0d02120a0c1b0b010614040b0301060201020a1205060904140109061d0607081515040905040302101b09 79
    0x98241202580b04503400170640395290482c101c40e20f07010010042e169858510b0f01d400d07501c0200012039005d5181400d000c00f0782e5010f03040303541054003800c010560070a00b4020805641240d030100469501e49414041010380c0445c1c038500078042140c8400e4042e203101440c503250160900d0080100b41c0802a20480050540180400c0f0000d803c005003420507900390b4003104402196003140041d9a8107540e40b450790460605904a045440355618650403661202c58070f90040c013441060140c0d441d00141080000303021a0003400f400d00805469503034824010307001c0d402041d40500030804000c0525034221041c4141071065078010560309064681e40c480112a06080a0011031035484014030700104255014010015030301003204038000611442450420a010b840c24007001008028003c40c010001c40034141c001c01110b4009140f6001c40054042d44120b0f840751408071b05040c2044141074002c41d418500c0c0070040803d0040000f1000840602d290b841000710219040761414016044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 330202221 1250 330200971 330201031
    0xc060f0207031e05180f0409050f071d150402070210030e07061e030507020f0322090e0601150c020d08070215040f1e0504060f0906080604030e0609040b220e06 70
    0x200a0001c404006c001004901a240d00c041c094583d548010403000f070000c42009500d00a000110208414606c00c88500f180c00c00c1c003a01c15540c044040c05040394940c1e03583c0c1190350384c17507000b0f10080c8140b6800d00701402600f512001a2164020000001740090141e1007041d50444c1c9000c1c001400c00e01040140c0041802a000c2000c40c415100c0b00d200440301080104040301801c2203190310b03501c80600903854031034145c0000d80e109081c0966020090700000c0c1240c156013642150101508070003008540d09009000040d5000510070081c20501000c1002006d5080c000c2e240b60006800e40507000389580310b50b05c04c610101d00c950324104003d14407102d00082e0000a0701d00d03e820305681700300003403d45042d500482030310311403088200122003003485904020052840580050325094a002d00303508c100140c0d4a02236800050b85100e550384a074440e02e18003000400304000241c0232160510100c01110760102c119240a501e903528000c00580f45104801449180c0030400101041c0c41e00e2700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 330203471 1250 330202221 330202267
    0xd02040513020303130503070b040509220501060306050f100321030e0106080309120a1208190e0c01030f050405061b120a1b0509010e040b010c060f0207031e05 70
    0xd10750010100141c0e01400288000c8625010541d4041d081c0010503081400560040c00b003100300700010000f0351540c40100f5481010394610148450b10344c0c10120200312005c200602c69440c18001008110241c5d00c42d90180c4211550804542d0b241500c8850300140c42c0405800c05030101c04103402642180040541000070341f0700030441c0200b1140340b03820344242c0d4000290030b03040440c0ca254141490f41104101d00440f100070413907440342c2d0f211505020352030185c410810100c0c0e800a0814070016010b0b4219001141d02084065440c4800507221003504016900203814211500c035003100e01d004450240303030404041e0010744c0f1403114003046002010711012140006000a51402200908045c4200d01754040452454580e2043d80d2041d14100c110f035040c8802030000ea0f400340d0b402450054941c400366400208201400c0042e02d0240e801040201828200310a9801340e51098021709207644c4a522280001d80b00d01d0060581e810401900724005036060000c81600c80740400800c0280c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 330204721 1250 330203471 330203491
    0x1b0d0f050630030c160e0f040c05091302030313140604030503090d0515010806160f0c02040b03070b070f050d090e16090b040b03100504050105031005060604050d0b0f06040b0d020405 80
    0x440d48401c481030401c0700ca02c409612941303005208202600c8100300246c0d05c0047d541c142440c41c54550b072110006207490140310b004200c440c0c0092020f00080e0610121150000e08803521a00c00d03104a44c44809240501c544400000720b43c07440780d0030300d282510181c95010024504003a43c0c80c00b8031480181d001002e80e0740e480703114070052050510b142c6c024080e00e041d5020300180d00d018580f102c2504000c880d581c04100410801d1000d0903880030440c40d4459040780e01142800780080001d1170107180d60000949581d0001e0030904014a240017045414480c40550b24200c20340801a0381d2440544a0f9040000700400040ca001080706014039143c0c42c90b081c60340c900764880180d0465a046074005598510000040c404108088510500140f02c05c42d414003442d07042c00c0200fa15411046006138480b43c90758046555035a8110943d00070704000f604110744180707103007010348480006580c901794005130f14020504a05080c010300d000180050300c2580080710641c2408001c20f00240b4428003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 330205971 1250 330204721 330204727
    0x90204060905090a0311160501120917090f040506030d08090304030f060903110718110f13031208150906010c021305011a070c0e1b0d0f05063003 64
    0xc2221807040500402d1900010416444ca500d0007034003803071850b003000017103078003da28920b495001c04400b44e064950a1a15846182c05800300501400d03841c3e00c001c0002840c000303c407100c8403443c000b070a0313407000496003505240d4900040c80111042521225003581280300c0f604882c40c05001d2494100c544e0404076460203903a521001d41101507034030101c0b0001c1c0c0b121382410a1690100548210345081000b410b111890011610414100c501c0e005130840d0703d134001c0c0f286e03c01107042900c00c0d4205071060207581d5500603000255207440c074041204c00812040b6000c03022840f400380903105010080340140c00340313039480801c1010790000305103a0400070214040300047e181c280402d20015042d21020034154100358100c005860340c01c0502a60010070b0025001007007440103c141110600c025290064880d0340908180104603424038241d02c02c00900d510a5a465601540910344034650801080d2030b04000c01c41d80f500320f440101e40c50001c441840c40d221120ba0604400d808041c2e00b1a0b203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 330207221 1250 330205971 330205979
    0x10e0612070b040e221421190203031b07060e0a11040f090201020c04020304060605120615040605030309090924090705010c0f0b07051b0c010905060c030a0309020406 73
    0x12900d074064009107941c00000ca0108100d4000c0440b00e5041000000611040d00b4190024071181d46800005072022480c50040d0411031014809150400c034040d6081035603608403289407a640d4402c0d1100c13920106601c1040c48018400300a4030b001d007401480c2c485803480b02004050640d040460180c8146c7c1e03a6004080c0c07950010003c5102091140c101c0380240700c048010041103c20f54804e25040c00d0800300743d000140ea0115072840b001d24120f40c0162a031712a402e0407001003090380c210381c0d0410044035045240364400505d580c8200b1095003401c040c12104418171098403484d104aa40541c07080c0007522951500001d1140c0c0850030408484048680440e5000c4516035854490001e0003903005210040740240f01c0080039060a0030070413404161681c800f0200b440084018000c1c200180105107444d04c10021a00c1601460000c041800c080d00324072525000748119840c0410a016000982802c112041c0c440d146480b401460030400c54030000da0181507505400c9a000c1e80d03c2401007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 330208471 1250 330207221 330207223
    0x8030912040603150501020613060216080a022b0806040911040213030510090c0b0a0c120f030b01090302011409030a06020a09050a0f08060103060c021005150307060306080303010e0612 81
    0x1000905055402195204c4004210060700c106500000e04540000c1c0401c00c0c0d160a940f41082c2003030b0f202c20300580e00c0042e03150461075a101d084006010f01c10000300000f9681d8002000c018808001c40e02084c41c4035000340100c3e003049407001d024041100c8030001111881c0c65484000803502802c9400040086080000c040303034007031440c400254000d03210502c2441003c03c035070b0030b194240c034404010a24550301c03a000d404000d8032801d0307081c200c00504a41c0c3c4512440c1c2590031240d20203800003400b482980b024222403c8a4101d1000034a03141c1d00b6015580318504171001c4a4040e140d5201c25480c030340003112251b2000c000c00f41c252007403034014000104244010100302400e0342d5500403103402c00b01000080c1c2001c2c0e00c03410380c01d075540f1000e20a0010119440341182d81c020740000301805807000c240d003482644600d55403054034100411240464000607140c01060481c260351301251604029421910325001c0c3e4038007544240010b0204001031901e44c3d8000c000284054822403c1d00320807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 330209721 1250 330208471 330208477
    0x40519060f0c30031d060a1805190b0f0f062106130b01060804080d05040303060306050a09020108060301111e040302090a0e010615021c120606080103170403030c08030912 75
    0x341080070302c8000310f4120a645481204200028600c1d56094815540030a540e6040054403620509070741c5e036401c51802c283e41511044480d030081c29102c200c011020303031040804004405a4190b20860000755044004444031813203250340240c0300e0450b0700c804090240c0070200c841440c0990310101d00c1049400d10402c11103105a055501308401c594240c0f42c50140100103900c0941402a40005c0c440010718200903034003d40902d080000b442d5803130307080c1107025088580c00542628a0a000c2c01941c0c0c0180d080f140b8194001e8a503400c407130725464249400c035480464520a0448280140780c3c0046100510209101600321240e0030941c8940001d1900c10064030401c8041d036985190ba4281d94080c080c420040440c1c90000c0840e140c4100e01a440d0700700300e100610501c0c4030310107100545006800340c048466090000300906130f04c4803000340c42c8000038002524a90310310b103030301040c102000049405403030b4036a840d2001907000743e841506603040584009002d00500c0c072461001c8030341c5005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 330210971 1250 330209721 330209783
    0x51f052a0102160510180f0303270204060b030709030f0501090204050c04060f02070302010504170106031211060c18130f0216120207080d0c050a050111040519060f0c 73
    0x1803d144500700d142003031404203070710b015004d22818880c03110f41071110800000c110326009120a00401c0320351900301c009000c05a56241e00701000034140d491841c145007900360300361003910304000a507201d807070314551400121340c0c40c0001029010240009a102404405080e200d1000030600f4409980000d017645d200700c1d086c2040c4040072030200f1055901040020b03001c0f1450002c0c2c00014115000244244250b006091484207a8543c041c00b00b07100754044001103070005110300b808000e4800040c02c045100d0305407071040c416600400c821000010071140403a82d10301c15882d07000c00010501081480c5001d41d59030250b6512480c07050481a80001c001111030f803401102c401d03800f40f40040c0501d442c44680821940f000c80c00303021070034000440104086581c1802d0316280c1c040c0c98900e1508401c010010320399420001c0c80000039802d00c016100b0f0b030f03004446001050400c40b126a0a603840740c400c0c1c200203001d07440e8000c0290f00500d4001110b40c06004d81b14940c40512150b4008001c900030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 330212221 1250 330210971 330210997
    0x50a170c0913020408030f1b0a0b0702160f03060e03070c030503040504062120030709050105030f030a14030606211b161b0e070504051f052a0102 64
    0x10408510b107000c0d44212240070140808604090070a01502c0e03403400341c1c1c00207076042c80380011741c040044d45e4034910105200b1101c0c1103c0340104507242100d00d00304181c1d10040907201d0b10703000c01d8002e01c080802c10141c4a0805019058920b1030311070402501c0076030031800c42400104462804074080c20821000307076014400644d80c40389458180400c842260b4440d03c0d00d80c108542003d1948060000c0c0380c1c9894110403030070028458420f040c0415044005038560501c118440001d036200c103500030b00c0c101c0e5001c1342681d4505862460443c0c6034410109600c001450924000e482010960082e58104c2c4c2c01400c6d50342400b400804000c90041b00c00842c4081442610810101020318000d0369100d10842d24250708118941808e68a5400b14000c020035055048001000400741c81e01420010b10010b04004041c0c200004050841e030301a008243c0104070203a0b61030840d5046070440c844d00101c0d65145d42c605882c2030755002200080d1851020580d09401e4501100e003400d00203001400f40c1c902d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 330213471 1250 330212221 330212227
    0x9030318030203341a0f0f1b04170a060617031b010b0a06030e0c01030608190501330816050f040e06011503051501020d080a020909040f030314090d050a170c 69
    0x5001780c8101d0b0341c010300300e00c05070b0690400c100b80c0e0988090380c2030f00040b00b00d8402d411041d14012140130360003250000120003542240d040007400001400c14440b078043c42d410400d40e516035140040611034251041800d40c0704100400b403504421400c0307210040b004000146c3c4040080008001d40040d910500000381c44a404010a040610075604080800d00b400c212440c138100c10b0540b5805c01c14850000c245040c001c0005100d029004030600d0004501204803010014940d450100c0301c0d4400716940100d00c4201050f5100c00181c4d0b44500d05413007013814010303807501003000500101c4120a54009444000110030124200043c5020b03041e91040014601d0784101e005013154401030103481c3d0171580c1d15a4581c8d50360045021110700700c092814601e02ea031008900c40c0640b0486440d6500503e041040101384016000c0055071107110b07a8061000418405003075005a1003500c0030415a04a19900c000342c078010b5004080c401040d080c40d40c01034940007046030622030200c6e4000380c828400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 330214721 1250 330213471 330213503
    0x1020331060f030515010e010f0c0804080115120506220f06051b090603010501050f04080a0c1508040c060503270a02100203030403050301050906120d030903031803020334 75
    0x180907040d4045d00c95059a00f8540340440000d203001d02a0300702c641800310540c80441c00500c517020300910240c006400a030764603a203800c0140207241081c40015030850102000c5554402c0306566103240341c216004000030b445c0d803096040d01140c50160400480e424001c0c0d80e00003000600607600a6001e5900042c0030b141200320320000c00c6021440c0441c80008000399100b82e03441d002940d0640f4001e00e0925150000040b501c141845140c000c421603201340c802030000c0007400304500042c2c6982d002d0f809002040e036081540c11800560780240140c1c0410707428440700b4490406140d01c004440315128207082d2068698408404090b5005480d4100c84a0032096080299921410b0070843c40103519519003914004e01500042c0607031441017075200c1c0811840d545070001000390348000000d641c4050420300c006401880551003c03000f10b03092028880494510102d4131070f8864240d00030310f15003004d0303020440c041d50402414990202c525081c007420141d00b0008401602e00c2030041101040c48 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 330215827 1106 330214721 330214727
    0x601031112070f03030f09030f0b070e06070c050312071a06030a0611070b0a0b010507061d1606090905010b0a030b010e0301050c120a02030601020331060f 68
    0x2d00000480c0c00c0304038103540012280700e40ca800703010600320802680e0b0b52245100107003003000356000c060045002e031018070381c0c0824185803902c6101c00e181c0000d0207541100307500b079075810b0082d04184000c0c1010400955500c900ea0f9046042c9002c65640c1c0300b100309117190405141c09034001280c4207840401032a9420b17544503a003400f0110389403a0324802d682224900352007a0213000e0124007160411701ca4076040e120706948541c80c0145c40e841d0000074021a005840c00d150340c40c1080544450140482c0c07560044000540003281c0c070b0007900811801e01c1f03801002e42e8900d001c00410584560078111610b614a50401040b2180854011b0f1801c001c0441156015404c040402a02c0c11130030004250f2520950400c101039103d08508804032b0000700c0b54a4050392040102d10b03424810041d072000c81e80c484000072079604142e0800307103006840310b500040c04980004266440742d50 = true := by decide +kernel

theorem cover : BRFrame.Cov 330035971 330215827 := by
  have h0 := BRFrame.cov_init 330035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 330035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 330035971 ≤ n) (h2 : n < 330215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
