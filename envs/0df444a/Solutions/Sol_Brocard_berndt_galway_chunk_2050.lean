-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2050
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:03.482895+00:00
-- url     : https://prove2.me/submissions/d3551fc4-87d3-4486-9121-cea869394da0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 368525179 ≤ n < 368705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 368526429 1250 368525179 368525189
    0x1209060e09070518120312010504021303020904030908120a081509190213030c0e0f0f04030e030c0d03350610091809030e040e07030b06010e190e010f 66
    0x1c1c4800100707520ba0b0242d000707810304189059881c0e0610085402062a5a50111401d24941d101140c5442c900c0400141140544015102103007844075807120502404e40c1440007a0088194401050a05201c2e2543e40c010309400e004881ca07135900060740040650045803808000341d120390106d0800081d1700c1000821210007000041c142e1282c03205a80710400c0100c0e8449032681c01c018003404072403205070040c020341c050004488542c0c076050400c421000c0c010003072070400308298104110300c00701d8554a03030496010b1034034482992042c400709240a0301241c116034045410280c0b10205548201e84505052804500c00d4004482c600400c00c0501c80c1010261040301d05000104181410210410061103510781034079190340d00c00c160f06c01101480000307506140c441d40e200b0207040d0001c001021400040d181044084800c03400035488041a01004228044260114407160301c103900140790154000c120190705c02000405220300100d511400103d40000300c00002c0c1d8001c0c0d20200e200b118 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 368527679 1250 368526429 368526439
    0x201050f041a2802060a0e07030c08030c0601050a03150c090e250507020603040b06150d0b04060f05032104090e03030a141b300402040e0d021207050709091209060e 72
    0x1407103106c880d2005c0c000d08500c031180d6209542d00040440c41c2000701d24020025800955591510300b68801e041c40c0c0140c110300d0103500c141c881000000e80c2c150001000011101c0c00060744d0040f0501198139600551120001e403102000703101400748440540c803603089104080803150003080e10306807228001c890020354015818400900401c1c03070500f0b040d42c0008000c1078802d40042c5c04984a0543e003081c520b4200c2607035540800c03580ca00b840d01c10701021f889022081c1009074903081c0042d9541510100c408206048069020040f10101003a44d0107000b0010062120030041d00700c1d00c0e503a8204407040c080d0103040025034070107111042016030246602d0720a001480c2440740203100d00342d00440d401240c1d01010303120700005030a800041011494410365a8406080078010001a590310740900c0c415504107a80c00084e1030340015a1420a100404000b503e88840c1c0c1407003030a01e98260f10003070040d4209401c0a0411140300e4400684808c541c940c03890041c0c42c1c0400b211000b0205070456000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 368528929 1250 368527679 368527681
    0x4080d060b0403212a080c01110c070e100605090102010e19030206060414010302101b030816020708060a11040e090a0233030405190506010f0b090604030201050f041a280206 76
    0xa20f14583d17034035a4050180074400c0ca0072411104180c215949082100420200030513210600381080c481807008103503034070a2034031608000031216010700441c4158805e0020005c2c505940f40d000f03401075143c14010304142e0380c603000c01070700c0036040c9101001e0840c0107025050015130149000e11401c0382c62007112245000d140e0845d404c0c1b008101c90410804180702c1400081194043c8030840056032510032340c1c0b0040241410703030710070a0500f55241d0b00415074100d9107092001d00ba00040c078070340c0024050004a003118040c0500142e921403500207200c0141d112081004060000580c1d0030b00c184262401100018460303940800d000d8032180c03640c0d0700d40541c07001d0307100300040320043d582090080094a803c4c2c603141188802c07400003050100c42581010f0b00400c074000780c0203840c05c001d0a9030404140380c41000c00018001c0c2c40303540402418003601180044840961f1020741c2c2c080c5c0384001089083c07034000d0728031201580011042c0881a0f842d884c02200c0c81844c40303192218801c2680040640d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 368530179 1250 368528929 368528987
    0x30809010c05071a0402010c06090804030b01050111060601031d06010914010b0c030414120a06051f0f050913240b010306080a060b040e0706030b09060d0b04080d060b040321 76
    0xb504c801820a0f0704000c2c080201f01e01190721480b45c166190712800c001a940c83c50751600b908a140141d2016050002c1543c0c0c02c1030b441004202035078000310074600000d001c81e81180341890412401e14203521445090f001040c1882c07507078020500b80c605450359081c20307070741c0346448012071140f548113030b82c117400c248400c00954040c0c2d4910114000020310810703018844400041c0740c620010019595542c6507000d010400c5100c058800012402d10200289141001c0010800354810f203d024085c41100d00041e100702c3c141481050400c0d03010300300300c070011401c0103010740f030b00b944000c03a108141c40d1042c110010740c000d02c2410308951900c00039280e41000b50b1110002040c0301d42c1520303005034642900512014081c403001e00500400d0310300081d250301c0c03001031160b4280000c10450181e51644071040200e0380001c211540158014001541c8411001501019106950101d0203081001c2004001c100381030200102803006030b0340384403520801900480d00c11500c03100300708907406283c0d88144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 368531429 1250 368530179 368530223
    0x60901020715050d0c0f08060f030a0b0408090303030403180b120c0901020f102003060108060d03031b080a0c020606091308090d080c193c030809010c0507 68
    0x2001c80c11802c190381464140c130907240c103072954500b01d00005000182c3d80008180c000400d190483ca043c4e50072204606035601090362010402d0b4060503610000d000901000329001c00c0782d2816030080c1c107a80c0c4134107040c0f034058601030111140108001c50f00001107031481700d8800b903c48901f8104a28411a10342205810f841d9005402450460242e0054181500303401c102d007100605408400240e51131405d075500d640f28202030394910404404106001443c0c2e800440305800920407507080c20110803526050f4010041c6a20040c00b007881242c89440303e40e0800d03003180c85007428107000d1041c0041e044040ba102c400480c0c0566200440c040440d4045119a03200c42c0207601c030b084407529040720000020303803848220004440084001036080140c2d10288401d0101e01c488100c140c590b007000b6500e00c90417160400d81d10304200150501284c030402e600001c140c80c500d50b88281c44149945017001040f40e00e0032145d03510158204913079019090f03ca8412501010f0304404c44181d0180304420340c00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 368532679 1250 368531429 368531459
    0x1602150f04090e0f06041211030c070603150f03062003040b070509130e012004060507060f090204020c0a0506160903080f120c09090601030203070e0d0611070506060f0609010207 78
    0x1640e0f43c841e2240c00160100c08110b01c50140c0e0046c41c90960110f03050070700030001001c403800c22546030414040d0f800c0d0000e00007016000d0311b0003400c0c0030031508098403a010100c0c1a035030080360070320040080081480720b0b540c0700240c200006200e48044588125184079648001c0e10011301e002010400201d00a11610140c0242d001c010080101450300c0010242600c40158218442781d644091083c9161001307c1d0b0b6200002c01006094107091900e04050b009003c0c0d488082c0c00b0b030342c9840c1c0a50300c0d000641c3c002c0c01683d600620454036052408242a69104044004c50303607403241030041014a5500245410b0303013021559240001c60450340c8002c10303500807044030b14440000303200c10610903110704034851054000740303040368484401004101811802411b224140744c41003043c01003840c0d010098006298041d00d1000ba401e0451401c0b8000309059101e6510300c0d04003042100030000c001c2526400bd0b4000c331400c04802824004200d1984034094040740560310419080140c507001c84150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 368533929 1250 368532679 368532701
    0x3240501180f15080f060109111206030a0b010806040b06041e11190203031b1206010c02030709180501060f05030c12070f030804060210050c0f0d0603081602150f0409 73
    0x1044a15203c1e0620803401c02d5500320203000c1e042140c0c80500f85400300000b60040828480901540a448158550510502221640d0b1008040018805032020080b00c080c00e640700071001565a5100c1019441d05000d40f0201c60a4190f0b9001c9039483c5813600a44880080c07803880102c1c030030440c070120b50051064600c1078491000c2409881d04104141d0307415000400a40c0103907660b45040b10601020381c540c2c001c9900a600244001d00080002a40a9501450038200504040d960303000180c58000c26601001c00d403801e15804040030783c00c41900300d240c984250000d00c0380f55250800312010070f81601802d0f0b01075110381c46011580c0350080300c100c01c50318a03000b91049181c03a4080e00406d5101c68205031485a00001c040141d0359042090050540703042c1c8080140e41005064061540308502040c80c804c440070920385101c800035031111009540c004002a503500e100c0c50305038288591a102a8410741c0d03800c04a0304807001410855100303000d000b9050740381a09082052000704454440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 368535179 1250 368533929 368533931
    0xc0307031e020f0607080306090c07032114010f15020a020f0d0f0503070627230c030109050115080a0c05060d0e2a060703090e071803240501180f 64
    0x1c0003003d07486003401040600d001c1c002040d501e2a2800601c1007507030010300141700101c010031000d00860343c0f101080200683c4507410389401080351907054003038980342102a06100c100400050520740300c0ca2024122070700054140d003440407110059031110f03030040380039401a01140a560030707441c243c038698a5413445000038040c00040c40c2c884900e1904404011070b03082d550b80c0d15000380c4084151540e003548000d0205248100195030341c881c03400010a000045200c10501d091401c00021f000040039484068002c029009035800c1c064040c003d55941b407142d80d4070780900410b000d0340216809000300d8002c44a111035a150909001160748950785007004150340700c4128545050501207008070300c211903d0000c014030725004909032000e50301c4115104900030020400002d03000582da1080b0703092099050728554442030103960001340c2ca03591031290180441c000c004c009101c07040c0b03041400c040d00101031940d9240d850354102c82d402c1c029580403202c80c0ea0075502418050300103114aa80b4400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 368536429 1250 368535179 368535199
    0x18100c0c0b01060f0912030512102d060e061602012f010b06160b04020d0807050a03080a020f120907090f0c020f031809070905030a140c0307031e02 65
    0x6810703090441c00e03000311000038150303440504003990115aa03809814550b5400c42103580390f58001d8407500c2000212410240c11000140e804451904468010100071232450100540000503102c0d150948800310408207030841c3c003181c0d00e4841c00329400e643e500545103a14007121944290007050044808078100414051080c0e5000c2e4110151a2011034801c090503900fa808910b441c01e440810030582d010b40b03418810351080800030802002d44980280d00402a52a680046076201001400240c1084000162501000740005d2030355501400f95462000e141c42e03403000316040e0300c10a91212108001070083c03441c500342c2c400c2e502c1e4210541604a840c0c3c281e542d8a004159100c220402407029655a401105650180100a450059403001d94504841c100a644244a00e5101d0501807000c1c0c030001007225002c0c00303c01d000b0740002130840e03c0341459450700321104182c054141295001c2c0500c81200350800046007030691b80e1213044030001d13002000181e141141d0744001a0781c0421b01003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 368537679 1250 368536429 368536433
    0x3140907051c05030a050703110105040804090e0a120e031513030f05120a02090406050d080f2110030c06021501060e010306090f0911010507050309042c1518100c0c 72
    0x1c00c840e85e05030700c501c0d845441900f00500441e0901c400c0c804141d040004010000d8040c1046500782c03040c1d05000120710241030501c81c540403801400501c0e005610b0920201c994100201d0704401100b281210800d20110b8446501100c00743c86079001108039a8141d03000034091030207500d1314511881c1860800c040b080c0c111040d008180c41802d1800c1e8000f031110324a0500e0b01412015140603034050040982e903a0f10407030030344140885080051008100803080a40726030a00d0b00d80720003e0300e004001d04103072142340300c006d03001e100c111814812032100003400c90020a880001301c0c1070800740b100a03882c1c82c2060740e4000a5248850400d0395070080482c4101a900c15059008103407900040c04a6941c07030110003030252102540d0521009001c080006003002044901e541070540d0045084c92050b0f00c2c1c0956406611010b055004500813841c41d41000051a103880c86c2c000d00d02d900c400d456500300c85840ea1096498041c0503004041e0200d8070300b000d50021503442d051450842103200c05030b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 368538929 1250 368537679 368537683
    0x3020609010e1908100b0102070320060f0405040510050105030a0b0102010e12040e070201090519112125050d080d06062d0e010c020d020306090d03140907051c05 71
    0x19070703c0c0c001d0a02001c01e0500010f00c04100081d2050424402001240c4001c00081d644e20740521004005204002c0300020f106121000c0002e0b455010381450f44460080c495041150014050280113038508400a0003600501d60107104a80040e1601031558507001c0d0b00101602c030b0407800505542d00c46006101c3d000b404c010145e5458003884c005a100e5050400d44601c20201902c40d0046a0501d901740c808200040303940d111100580840441c4010b1130301d46444088000d51a159005c6640c01c0c080c0482450350b075604413640e40d0502950303500f800036040002c149048040421004408200034481c03400c0c8107040118542c011001e181c10108000212001c4d00ca06400c80e80028680510300003822403000c1d105001041b50100604400d000541d004000454020401e8100b011008904055444924146061940260030340700d684c80c021685d15603c1c08168901e5000038034050030801d0681826a04901170034034000502150751400b41000480f010701da8410002d5140c0910f904006241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 368540179 1250 368538929 368538949
    0xb09010b031009032006010b03091f060602010b010c030503060d03050f161a010810051504060806070e09011203030b0102030f070f0311061911040504020c0a060e030f0403020609010e 80
    0x20700ca030228484600c1e04e002414003e420414410850360160340007103072440494010f05460f18400c403540c80e80e82d03141301350f441d01e650f0400d82d0740d9035103002d0700352032a03015250066026650241c0083c84007510b4840111024000130b60302400045050020844500c0d1882140f40b06030702a24103503040001010003401e9592000c01200e1071954a400302c2c5007000028a031814840902903130100496242019464491100706000b9681541d100b00056900800c090b50001203000134104100c01d54a4903900d90f03482d4030948071180814500e440c4a0000d02e02100d10905850182500038041d030001e5a09401410407042c2c2a4190b00090241c20a40c0d4078200c00740c42c0c0700b0b0140404807200e200504001d40b1070080c410b11004c1540241c001c000380418454507001070340c60f6900000178000d40c2440d007000300d405240c1200358014000104000030b00400200380102901424041184069020300640d503031161078002e001c180014081040035140050180100c208181002890008180300107131200720 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 368541429 1250 368540179 368540203
    0x1905031b040507090305030906070609080a030c120e0c0909210a030501091a010c1e0b0f06031903030f06090509010507020f0129061e0307031113030b09010b03 70
    0x446410300122600d02401850340000150a083c0400e50442d1541c039103070300c00e00030064003e00c80014201c08005c0d090b4000903140e90060ba41e1625280401d4000340a40555034030000000c14012f0320154045143c0700e40c07280000703d4401040383d00402418030449000090880020b07000311114180c120340205903144242c3d2100130340e1540caa1960401604491060308160700440c42c11044511140c0118007a6045000c24200500d00310a1071800d080e010b01c80c1404000c00c0c18910610404010300030b00d8450140018000320b051541c3c983d018180e5409000410584401d10421200040b034007036401801514500c80c1d001c00c160307072180710090a42d6410385940021f07a40d1041001501581132202041b400d031124002d200c0b00310400c11580803100e41809400c02400041e030218002e9072087c00711640303509a914000502d1341000c240d4007580d00100c03a042c000c242050030103418401034504541508480a100c07840c51403e540b940c65070b0300c400a000c0c001540d80c0b40013040150340e0410560b0b2100d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 368542679 1250 368541429 368541463
    0x6090e06370209060f130801060308070f050f1e01050c070302030f0c0a0c031101030b0411030601110f150105010807020f0303191e06091406060301060804081303030801090507020c0a05190503 84
    0x55040d24520b58406035038011007c591504100b48006204d1204441685400600000c1903e40c0c078103009040032902d80209105102c1c881d940302030a07408000080044042074002c2025035160100b4110303500c225500140140c00420126240c0701c42000580740d480d05070700032240518a9552203851419a0f6041601c0c0d09414110038078456a150003000c402c844191018425060104141036031804080c103818140820f603103000042c0402000f10304000c0d0710f107030f0445800d505103550031a8801400e01610340060305040003d001300e03000241d04014001e540004610719a241d0031b0030301d01d03414043c20b0400041e48859240803040d20710581910401c4c104103002039603138076040601040f110008240445a1001c204010055880b081070720f046500c2820241615540c13440c1980c101c0c0b14400140e1071851080741c0c040149644650307160305072402070004000544034442c050782d45055007035034181d101d4400710007486031f420301c502200750702c40386c00032041c40c0191250002410191031309010007417a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 368543929 1250 368542679 368542687
    0x9270901021305061806340b060306091c05160506010501030e010c09051c0b04110f0103020322050f01060e0402031213062106090e06370209060f 64
    0x1961800d204001081c04440c500c1ca4070307002e01c80004d182c0700020155442071b480071a00090003003011089401031414a0300601d02e507007460b40c1010284030742c45000c0d203c1e02c1d0101c0005405050009009018611481c002d041041459000c1003800d51a414150100442031180ea030103256100d40308031010348110040d18407507050000040072106440341c82031160307060407a44c081103900a4024010313a4400d41d00c120100034000f0328140c800c64000c81c018a500302800400082c400500d24404029804640700754000008130011010b9020540d04800300c0300c2c280212060f002d6424100c400540d228400b502c40045640c1282405c4454541c0030180a941c0001008210329040c069071000400da2091141000d4102000ca15100800d0048900748103074104420700014030500d48200a131400307003051018640f141c0300600500101038050a1a2060201040301d000d424003205040901c100c41005540183c001c10640810855900d0100c69600300084080d940341d0500400070700c1c1c076100143d507903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 368545179 1250 368543929 368543947
    0x90a0b180f093c120a02030a030b012604060f0507030902152d040e040c18062907020a080d0801140a1401120501180c02010b03030927090102 62
    0x501c800b0021016401106403508000da45068440b4aa0019103030545441c00d40a503003003503c1c104e042c08512410311000310b1010081580007000304400491580c05101c3d012520b401954515061881d1261105003001900c0e9283d42110b080c2da0700c5070144001240520501d85040c0c21520242d0366040020744480400003541864910107241500380e852440c5000c2c5855001799214030507088100785850840c810300c2842121106482c09004650041c90180c10f01e89462140403581e44188001d80680f5074801e0b0b04040b0a1003031354100e4841a18007168038010719001e41030000550038031146802d0602c68070740562a9806944090200c0400401c4840ea44034400780208605034420740c0d140c1c401d01c01400040d218444200b04440c030b240070070611001d2140058900043c09580d0b0614a40340600010381080200704002920b6441315040122203503101d0100e0a03240d400d0b180e10303050750040010304110300f000105c5100412828501484c500080d05042c1e484030340513261803000c1c1e9004102501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 368546429 1250 368545179 368545183
    0x308040f140a060305060a0810050a0e0a1203180507080d02280206030402040204030b1f08010c080f06030102070507090b0109050409031e0203130801090c0b09090a0b180f09 76
    0x40c10107001009920070700703400003820107a0300d8051003080640380c8000c00c8051b1134103140d1401030404807041d01c0800c4600d9146600a01013124840341e841d05200741c1c04070220011034429402a080302041d0942c40740ca0005402800546400b8010f1500022001020607014000e03a405040c44c840070b0300c0c0da4205084001e14040c0300d0035450394042101c012244141409419075142168191182d0361240d503507000042c020301460744081c0c00c40b29003c0411448441c1c1031002c040300382c0c07502451041903440706107447c00c9401162608d40410343e40000b240d40e0010007080d07960f1003000240058a01502692103500340803407980030101c440e403544060b010541c1c00c503214a010704401d990803c04600b4680b4020240200380394404c0c0d11440046000440901c2401121030003000381d841044466603079800c0500910403d08161034840c5000404684881c60030300b1035050080040c0513a040341c44683c034120051044e03400107035000c4008484240484805c2000a208441701a0400d6951a000c90320318 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 368547679 1250 368546429 368546459
    0xb0406020f1e070905040519060c0f0206100b0711100c0b06030d0906050711030f0c01030509010507141309090609060b0909030a2003030a05091213030809010c0c030804 74
    0xd4156107581541c0840c1202c002003a01c11a1141c10020072070f61140e0800c00c0c1800c1e0241c8042c02c0400d043d48400051142d2500424045222540c50700050035051100b00c5c1c8500301518120a03200c901901000004588005800e4181c01b4482450610180d5400140c840c04012480c1c408110051900c100340000000d1107a80300e0002c0d8040c0c60002c0c03100c00001d0a03040c41d400344000307014000c5150030a01c8001d0004c0034968001808841020340081d0b0701e80d03901e442e0010950b00282c10100010003504044c041c0c140141325540b070305034425101000c0140944c204503a408040a1401c40004082c170f614020107014500a000008508000d030801c1c40030795040e400090b0144a0800a125401d5000000c071600c81c0d01e280380c00c089851028540550781d20101c0c0b0804500c0c880441440075010a075030041d8003481c0c6001c03c440703240e0940d0b201070055018642c60500a940030703030010004a400070300103205400c0145402c01010380c0f00d6654003103000441e0819030301c1c00070214041c01507400048807a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 368548929 1250 368547679 368547703
    0xe0306070302070b1311040606021e0a05151f060f030c02030a080c0f04030501050c0c071e060f050c030313020a0602031219060803030f060108071718070b0406020f 72
    0x10b40c6800503030f4480c84030340314000e1714018030020321400ea4014440300c13030340082c000200288240075076a940c0300025541d0105594038007030201709040081c0030036000694a085a5401800740040240b45e0341215001c0d50010030302584c4202c03014045002c10010480d404c041c000c0b644600d40d40d4007030031100034111600440d1034019903004000301c90b190354001414551010b0328040c807660b200601a94205180125800180746d5801d00c0c0502903401092800381402040e400c0032100315a6a6000c1200180340c0480f125001ca00707034440030302109200c2c1900c1c0039641414104503150901d880302e00c0d032440c3d0089134203030071403000c850b0098218900f034023040008190b81d01c001d50510710f40c0a51449800b50140883e6403007201c00855000140f07090304014014842d242c25a5100d10b070a114281701d200044610b1170004501d000041d11a5005044064250103101d680c004240c1c0c1c5d07400795102c01d8030300d05080d40491250b81d400241110b00314008001405240e40070f40900e6005d0b20809140c00f141005c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 368550179 1250 368548929 368548931
    0x3031706010c260c07080c0f040b0a12020a03020d29071b0f020a06170a0203010315020d0b060a021f0b220212010e04030e09070219030207050607030e03060703 70
    0x700700041805081c6904a039801e4072003030000c840e0395542d05401e42c1300c0d072040350704180210440000c1601c00400d020440881c107850002c1c0748051041000200c901c4000225401410b510090012252440000798000d1014001d120019240d03000a1103880c1d00103011211076031000050102c010580c0080c0d4803054641c01b42020500f411034001d403c9612b6081c4c40f0703449014001040c001e120910440c0c1c043d00c0d8000e0419101561184002030034141040300c0e526a1041c1080403c2401c1c109200f00c3e412240c200c1d080b452403126600a40002c0c2d4040c09040c84080d4440c09010525502c800c020280080c0980090009001d24a101c1d01003031039402e6100c111a1a00000d118503807103003890784441101c5c8492845002c411034446100a000f030400d00008030070040c001040002c403451045004034000d4803624000102201000740008049a5550040c0c01092002c0c44c00344001078414a400e103c0c1c01a500116190000f00300d0a4202c00d4042c0c0000315071111200450a0912109400460030303d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 368551429 1250 368550179 368550197
    0xd02181c02100e01031103010b13061103070b04050f0d020d0314010305060c0703020f0706030b09010819060506060f0d23100e060109080115060905010306030203100209040e070303170601 82
    0x80700c5406042000080c0000f20421601680c400c2e0300191040482000c0700c0d031a941c40f00c104c1c00b0f1a401000b00a0f4400044000c04944540250122000304244000841c64540e055a500c9000d00004e41b04903010301c500885420000c80602c070a0001c480140c2c010805000e032190002d00383d41c05058800007121140300103101040c03010588651000710020860b5541c030003450102e20b02a05c078602404140900d003070120742c0304d074107400501d401501100c00280340c1c0d80354280542c89010650300050340112403110200020360a03040158070000080580d400c104580d0420400341d4841101c100580d03507140c18071b010111168481008030652944141d0941c64940750410200a40340220086020100c00142090384144a000050070051000384031a020885040000d59098000c241c04188102004140ca5110b4480c80b003c03a44c000f00101448140e00151000a6101c960416041620307840e8240d0309007410040600194440e84d51060000d850f01001c51000102a0019040203030041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 368552679 1250 368551429 368551433
    0xa122613150b0d0605091e24160f02010b190e010f0b030403121b050703140c03070f0609020d05030307021219031e0615020f010c051e0d02181c 63
    0x111000101d0384c0320760001035980300e0004030341c6484c3d600c1d903000d0007262407110685d84014001c02c0d07500c0030300c2840c90440314a151900c170821500204880c00380c1c0c02c503035040840c22007501c100c410b0303400517405000015004074500b001c10135040d040540a0142114450104121840c07a008a40100460700211800d50b0034224070446511005c0e0010701000b1208845981007070702507000c456952400d002800c0d50f00300d0f4000141803500000400d40115150f0310300118030715406400c0702c03403140b00780b00a149054120340d60314003000090382c0140e410381d0343c0310071182c0161190004480c03018003540041d45c0728900708400078640203540030100c003030000c240a54184031064081d1300f17140b0305417400c000c11a42c60948810042c40541203546811604180000a00546010720010502119400e90780001c86000800d801d8038102c000d2440081d100b001403000c18042c0c2076040c1c501c000824034440ca0000414440010780e04041154584113101d81d1483e000d0b40703000040321020b26034410000000400719 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 368553929 1250 368552679 368552689
    0xa06150f14191107090606030b0f09060109050d150f060e090c060403021203090d15060f030c030605090718020a1b12030b0d0204150302030d020a122613150b 69
    0x2850890b0300307110920802003080007040c004030014010b90541000900d42d03c10300100a0120b8120050041504501c1c140c0359091000c20b5510880301a190400014542401d00c00c0e04e0303040c0c09042d40c41c904400c070900103403140350007844900c13105000085105810700c8640310080308050170b070880700e03400f07000c01d45502d4075264140c42c00c6a030125850741d09041e00c41c0d0358a007180315500b490356103e01034812810401240030306003c00448108020030072142c40c2c618031481170078940400b80188580050400000b0425000142d1045001d000d861082d0b80c0c8921030740b00c400840100c1030f100e40e00410710300411a400301040c0e00b100080100520082c0c038070b894000510001020800406864428017030254541504904100764040c00c104150010700003c259241c01c1404124800d005031f074030745001035200065111000350090358070703503040f22220010f8840b401103108201c1e40701081070618400071400b00301c0910402210fa2003100c2d0322003910705a2010995280030b8171b11145043c015002940312 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 368555179 1250 368553929 368553967
    0x3240705161106220e1008061f1a0301060212091c021c15050a0213060305060d02040207060e0708071a37030c050306010e090a06150f14 60
    0x22115440868004000c40c4191281402d070001580d04650a07803040c03100342100c801140c485a817a03080c56100c01004201d410594461a51240e01c12000305000e80640f80710700c48040c0c902c5402e2070407566501f11100748022050b03135208031b8801c048010840d180d0140494500e0306001c0005614041d03500c000030f00401d19110261031240081d10105085440e0040c0d0703142008484d1903402e0000020307180c0700389070841c510034001c02c0509000105201d12654001d03604410560501d007000c090400800300d0060000920082d4400b84251a10000d42c40c2c2d48021301030380f401784c1004207000080c00e1a8903d410200c3d884500d00d036014503000c001c112001c40880d03500d165020116540c0b00f2800c01c80e1800ea0040c80b0009498011401c2e90303040650b040d03400d00d008804e9585080c86480701c41e01027912940011500a808a07800c0740b5490030303902c0d00d04e48480c0c2c44541c03200c00080e003d40350100140c500c0c0c0e2441420010644607041d00001a40214410040b00c0e0f91010041c0303081041a154000c400b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 368556429 1250 368555179 368555183
    0x22b0506150d23180f071202060a020a0605040b0402030d0f05040605090409050115050a09060305030f07060f0515010e060304200a12060b040b030d02070608150324070516 75
    0x1c1d54803003031007021440c2c0c086208407500c030b82e03590200d500709510000343c00345000b6600e112a05c030300d504400d460080800c40c80115180e6142c400041799031502405200c0c2d02002d00d40085000d011204000030f002031040f1406180506120f8041b4038081c03050501c0d0044241100c4248031000203040981d1380d1003021102070790441d01d8403680710a0400c0c0410007410f04644020481d500f03018902080300b0414000c0400c640d412038141c0f4071a0303620300ca42411620f20340000380158008006120003c0401001440b0030303449480002034099160050b0340c00c0b05c1081c0e075854500900842a007205690010000c407042d94111040d030301e9030510b962204489032030150040700040a01040407155606c10500400070103064580380c001114614006005040218015120750b1900c946241c0c1c6040c00106200f140007581c00034000241030500039202c05a009002c01100d040712005004070380c90a01070006100031081032840d000c030008400d4202d040c030040c01d01342008814003504d00c1100c8000c10040c1126 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 368557679 1250 368556429 368556431
    0x3030914030303161d0a030f06060f120b04030525020108010501170105040515060c152203030b1302070c0509070503070c030e030a0b070e040e0706020a080d022b0506150d 75
    0x44c0100386a100501a0000840d407006c410b0318001b050009203002d203c0902c0c4144000c03c0340940351081080c103207065004582d1607102c0500701500007038004500c01d420a0080c10001e0410300100314192044101010140e00b00700340f0781840b0115608202106c0c0500000d013402c11300c036141844079520740141442010310a68882001c80c00384001c8900751042401d0291990707540b50309200c0c140f5510403081c0141d40241a43c0c80c0054101c030502840a5001c0582190500d0b451240d907c0440c05045070740c4d00d1550050310a18007040c90092480101041842290510070203071800c401c016811000600c0001485810005c1100782940b10010b5602e00c2c2e03140c101604040f1040c03004c680381190340710009111007040000d100486810010740d0652603030480d0184241144507502d9034486485d03100756009031380480e1481c0300103066074003c1c00c0c0350b4050417001401c0c5481c070b030741a200c1e4040c200901d80c0c03490601d4130500040304441c0100740d80f001081d038908089040b44099241ea52090122248000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 368558929 1250 368557679 368557697
    0xd14070e04090c1d1e13030302030a0e1b011b0c0b0d020708040e180a120e03010f050408091c080f0a03020705010903050a0f0206010b030a0914070303091403030316 72
    0x2040300f0f10000500701e00340b03040c0301100401c555510044015605801c1c900514401c288919142100240c0f1a1400a0246105110980e016000381d00040c006882c400e03110b15074440750396420030501600603422104020008907102c0050a409552408040c070110040880b80118001c160084201e40554400036642e60b00c0245410007402030a40060682d00e00040020f2071401400c41036018951040a460310441c0186500d6504c04020300024445480346481e641e4450044000f003038080d0f00540040b510403085120301007100c0c821141240c3c1d4074004281c0da182c50030440c5004e4901c410101e40e450a503011922010054010f450440350075480020720341541ca03200e42c041d0366200303902600074408006145405800c942058001c0c0c4c000030401b0701c0710780304280f001440f00c0c103c90100868500c0c41d02da07021807070b000e042040f00540c4c5003042a2410811481c0c00c05c91030009601999034103441c2e40c1420041c0800102110385e0300e201e5071080c4144000d8046ca4118880c811074681010a02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 368560179 1250 368558929 368558933
    0xf0b030a0203031818090109060c0201021303030e0102070305030c0303092104030807150c020703020405061c080f040b0a031e02030f270d03090c0905100b070c0b040b0d14070e0409 79
    0x50000c0a0011700b13002c890110600046034015081442c1007403054006104075903124004900700d0160011021010100e1141003010034001c05154404d0581803041d04e45450700da07180c180c40d5903ca200d8040040d1b00c0003081040032041030107030110200c80c0040504880d040c06c410746140c3d0149000241c11a0703400200c003003c0000d401d24007240d60030030080038000b0b4100e034180651289120321080e0300460a040020301c6a1a0010b14250322080310b0240d00350448241c0c59915590300150050780c1031a208110200c0e10f01282805028445003e43d13010920803240040440b858058039042000c007801031061050101134a00c0140d8441c020742d10403a0781064440e1410310810540c10302c0403c0f4050b850080c01c1c1c0b40e0f41608000300150090000c0054603a4038000c0c9400c944c8100d07503152000c42003400600041544c18010300d0458021100c4122007a00d44148404603070103540030325041600016120420045805241c4c1805071038481402689802d034800380840c0102500700c0d12660b511640001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 368561429 1250 368560179 368560189
    0xe0606210115120204060603020c1e030f03010e0403092403150506040603020405150a0804171e090310110901050a030906090b04051608030a110a02030a03030f0b030a02030318 77
    0x580e6041c000c8040d12050380c0398240d081c810f11080f001c0e0300a600b4080041411030180c001c0b5401422980010047c000440440001500c0d150005440c1e80c0400c200440c1c1074004500607502a280c4035404142c01d0a0600d0040e02001c100d038044071842c1201d062a840030310f84480303102e019903482c0c240440d2000080c00000810017507500501c2d0300c40d9011501141c03803a03040d4084c2c03007a80c4041c1d0320107018890f503040484950080c0d000c172100044c101d000081c00154072600a60aa4084030841801c00710940202020a800c501c0381812040010480240c0d038982003140c6054140714000400c00c2d400000c3e401390031880f80340c0040d41400380001310081054032030351014034100c1c1c121004001400340ca00c3c017602c181c03102391400c0c0c07400e1169104007803203c4d9900d000501164961401180b800c1c0042405480320042c00320035283d1801030050307050140e1424440c0082445c40703603070700141091520004004580c0c0c40706840d03009500c40608076006072030020031200c0c1d051000b02402c40c07421a00d80050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 368562679 1250 368561429 368561441
    0x61b0311090d03051306090f1202060306240403151b1707020a0b0a0b040605010207060807140d0e150a0908030103060911130209040f0207020d0b0603120705100e06062101 75
    0x5404000514001407803d0b800310300c0405841c203442340c1c4800640c0d103480384402c14017131100195001c0c404002040d994944820400800c8100c0b00740711141d41c0b0040c00001c05900150b0003642d10781852080c8a91841c0c1c0c0b80310310304810400042102004582c00d0004110000c020300368080340c507440c80896602e81c000c103c13580e138296000031035081500c0c20f0034a0001902c4030424007070041d410640d01003080c0d030010500005075034481e5203941a503900c58a04451402103062050f00400003004800c0b00081e150141d8000c82200340002d003504140c540121086110062240305010303d4240ca0100140c405011241102e070040004140c130000f60501320490041e0b018402c2c1d125420303030350229101d11290050112300c032048504001054411424a007a4424554001e41c08000003034440f0000c0c001c411180d03084840503040f00c0c800c0714040c00320840c0354080607003038483d41c1c0428000d103580c4e100d42c0540714940c81c01c50050b040301c0c00c025003c120721a18800915000e40340e103101a41000340b01758010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 368563929 1250 368562679 368562697
    0xe01020c040e010e060604020307050d2301030f0c080c01050d020d06080703120210150302060c0f03040f0e0c040302030d1b05070303080906100b1602150304061b0311090d0305 77
    0x700001501d41240500034600c138010001135028000010b501c1d0329142c800d0741c0c800c0307849803199460724010925140040840c0000c01c001c00c5900524140704507800c030706140c084c600c500b440440c0e008043c104038850003003540c00407038161301c081034802290340d000c4165031100e51505005600c0345101ca250348043e1070a60003818844c07060840c00000d0000301074900035000760640903a212104030f80401c0d002e44040041100c00051881030130001400d00300010a004218081a24102c2079102c0101cac1c1103034000d603c5940e1644056100303204c1d600c0796002041d00503007000180c0d460a80340d80d0100b9218103400603030310203010750b5400164410f000c5031b0103486601d9202c1c050301c4c44140c4918000d402001e0a0b143d010162140740006813001c0510074111003900c404811a41c1008100b02040c0803920340c0d014100d800800740c0042032078401004016501882c071a82011500c01030040c1d50310703082030300c01c0383c003c0806007080040640568081c04450b65820b00781c0e0340d8020044281001e8503144640240 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 368565179 1250 368563929 368563931
    0x150302070213092102061501021501090c0f0309050c0904141f141017030409020705010603033f1e0f0e07030b0f1003120302040501200303070e01020c04 67
    0x203104104141030340301200103442001600121130038014041016200f9030800700260380400041070349101000c15494202505104450014030720300002000c1000a80c044083d0b15125034403903c15540255008102c1c144610302040300b0021510b0b0107a4581090b5821070003002d040c401b0030203100041c241c1d94500b0700510f0454000303140c201c803240a0300030042c80c40244d1030300d80a60942c0c429036130134449019801400c80910b0103406c02c003d42c0c9600820785d400b18017078401004009030040310382c00034005207070007400001290b41c594100588202c02e031074000aa04000000c0001215201000a450f54021800e60f010b0700c5160070400001004021514440070710816001c1c032282030070b60000c101c410600f040501100b0f42000100e5a52401030200606120000c00003548103079002168603480310402c03e50300f20150743d03a02c0d000360342104c40400400003900000c091000796007110062111008032200d44440317031007202d1142d0301d9020260030f0b0401c001940e8070480c05a8400c00c00e003102d0480c0104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 368566429 1250 368565179 368565199
    0x30909040323070b010f0e160504081b121f0c03150b0c100b060f07170403080d0b01090f0302010e0103090212010204031106070317101a0a02251503020702 68
    0xa442220340000300b048803981c0a14001180184100a0880880700011f00031503040d140c81050208004004c00080c0c20080e040c00700140c2c841c030130803009101c004800c900e1070a42c640c2909001d00341c403000c03900c80c040b036110014102913035260b04a4452603841c8a800082d062003850400c602424a0302600c07500f0180390400414101c1c0304400070100d08001c00125625036a100d01c00c24107641c140a4405c1c0e011105200c0d110250390000001c103000c5200b540340d0a1030b079001d15002e4000b07801c00c0e0010340d01c01d01c0105a41c0340c010042d07c43d0602407142401c1400c038803880c2100000d896012400000e040150744000121940d000740c1000103030302e5000b8008170356000f103140046c0c007d4100d4802a5a070300710440c66045d9906200c81140e100c1030b09581d50f1902d2601041c102d854600000e8003070740c80b1403510310340007401c0340d2110040c5c075180f032100c3d42566031060700b080c0003071034070000905a80c0140c01d0340c08002002c0307101c501081c0468005c02010340040d1550301e001e078024026910080d41280c0c1d6a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 368567679 1250 368566429 368566487
    0x9010e090a1209052106060f030309030106080d0f020705090103020105180d060c09060521090304031514012103030f020d0609050a0c051303060902040e011508120a020309090403 78
    0x30062005964080d180e0715030750421510102c00881d941e2900c44d04941180c0c3c00708680d41400404802941409400c8928040344c0c000032908603007540d031020703f082e085889004c00c02940107880460302c0c02c803031004080c0c0d18100310020303a003a06c061100070705001c0b0005205088401c044810410303000000d00000b40c5174001d00f4604003402d2074880420001e6802040468518050310075500001d08040401030b010800e280001403d10000d083d264441c03109100020020340d10381240c2c5a032a00940020694010030f490402e56070300181c0000c0c21408900e1115074801d0092409582c4c0da07a01480d01150318190080d8400c001e11614200d40b01c0d01e81051400700c1c680003217070041402054810002c1001039022001200e40c1d004141e50074800e0701c2c10803003c00100d48940c000c00c0180b80001e000282c0341d122203140608490407801030401c0054200410007454000b84503101149828583d0b0520f40b64403010b00a490b4030860502034070401c200000326083c10b10400d03200c0c03030340200703c8031400f82d00c2c05c02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 368568929 1250 368567679 368567687
    0x902100c02041d0705060901030207020307120204110309030703030c180306140a0504020a120302030d061d16050a0c1403071407051008040803041a10080c060909010e090a12 76
    0x192405901403030603c61140c64520265404071406440b61000d8480315003401c080100680c04000c0c928101034003480385001503a014403451005003071a600e102c01110151040c802a5100744000343c18150b02070007084032036580030040700d240700d80c149400204618024401d80302000300011907100240614004403c1100541c0125900c4100c041010701a564500501e4103641080f50000c8d008240b0000401a42c0f900303240c2030514038424010741e07042c900e0f11340b0b0b404112403082d402428a03844260160b0110000e00f078099801040c0080402400c91402c2c2003e04584155051030080040c141002002c1c012078804000381001c0031745c1500d50f01c10040c1400e0030496548040484180242c9100040302e00c0c0c4150940074001d02a04c8100a5079107603142d03107005400041003910029545400c02c0c811016001c0242d101d92401e0810400e01c600342070760240350808092005000d43d03410401312015607607100d1261704660350390326920034565400040900740480f1031001001020742c001d481d0b00f5113800c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 368570179 1250 368568929 368568947
    0xa170901060906181404031b0302010605041a010f0305101215050c0721121a0d0302061906080604060e0a0503040906030311063105060a05072006070f03090210 70
    0x5134000602c4444603170b0000405041082c2e4004002c2000e8222480303002400105001c9468028000000c01c00d5072440420296008182c10070207001324032a10703195541c1c110005006d0341003540760401480c9030059168038416040d000303503042000c11903035031010402c640c922070090464214051096003003800000041d500080c40849105844402800040026640c2100f103d101c0342da440a4010344620800020300400306404020007003040e08a100c0c0d00c50f00900d40406203e940104014506180c03d406180c0e45400900c1a5a0412804102035a0300003401900590000000640e21070000c6003285030812031040100f8500012a00203071083c05940688200c0307000c1e48403090b0103c580d4610343d40300c503803c60b1060300c9d95110b6a2100b00f20040d14488510b40e511041c0030403404412a00e0f00361404000b03e403078a94240d10303002004000e40c1e0081c84001c0c3e50110303100c1d81d618961545007a03a102c01005201500f0010b82880000c4c05601ca90040502c1e19006003255440c02441940149503000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 368571429 1250 368570179 368570219
    0x6010c41060903031504020313080a0917030c100c170a02120f2716081605010c0803070302030c040e131b050a060809070306020c0303011a0a170901060906 68
    0x88000144400c0710100c11a41700c0d149950550044501001c200002034001400d0312000c0c5a80104a50009141030001c026041150310740c914a80d160030408c03801c8940b10185141c158006100b201d06c60900043c15110f10150000e01050314805403104681c2c00144d4030343e00d0a500c030380318140107100380c03541e00034905060712031419405552840d000001d030a0342a81c81c3c040ea41626a030210714006440c2d010306804950800791400c80e207050914801100311a0030821981d0001d00100000720982d605460082c80b0a003040014007440f43c940803034a000c0101940107254001000502d078980c00000c56000c0d00f032034640041c0c0303410030340401c07481225140383c100e484449003203141c003240402058800840e40020400d8002d541000412148500007521000151080700300100026005002800040084200954681d03240224002d031180314818981403104042241d00403850303008121110358010112071042c152565050309004250135032200310311510b400b901183c400501c92403210302d85 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 368572679 1250 368571429 368571433
    0x4110a080c130e01111b0106050d060b130218030613080714030403080403060207060b09060a120317040b09104803060501200c09060303040e07080106090e06010c41 72
    0x4001b040c052801c071a224005e29520406030100080051440e4101c1030341c800020340b84401c011000c2c0c110134241d030003061000341d00142080c524141c605040005561200204030300410b000c0b2691124030f400d2080c0000580090388030b86800da0402e0041007100c009681c4100c981c1c1d0b49a41c1c070f05069000703400c9550704443c01030400315052a18a008503030203000d56001002c210856240019075000c40314050000c5047c0703c082144200006202500d141c801d502541343d8400034504111964109200d00700c16a821515010126000115140040c19000701c3c0188000004400100e1004d0122501400f1100e8800d1201820710851341a0066030440f0800c1c0c07245a40c040d515140c805201d403513051a5065984894400300507032400c003610350340210000c1c00b940d140c540c443c1e0001404080c2259004081035400340100241ca80c4211104014460000c4a40d0070b4244500000c10001d0b02c2040030f001d003030f6886c00b158242180030400c144240ba01402c90f880c440404000390400c8140d0b451014024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 368573929 1250 368572679 368572717
    0x70305160302091e0312031602010c0c200d05030705010c0807020705091609030b160e06030906070f121503060605010206010303020a0b040602040306020304050604110a080c130e0111 80
    0x49000c2d00a482e03d4003c020b0035491120400710654034440861810564144036030f880162003c0b8800c4019800752001c1b03131400d503011404e40400b0f801d442040c43e066003040b54030400c110100d4040e40d01320102140295400100d404000c0000341c28144210018006002c0042c010040000c1540f005071204110703150650155252401a40c803402180303d8280c01030383c0100003400d0000840c84a24482e00207007803100086840b0303204d40d00300c05006c0700c82c0071078a030a0110810365260050320400030501d04a901034554074060500380d4880c480a42048188030f4215490004030340258079041c000d00202404120140003e041d00002c2e4682d0b00c001d075601403400304c001c50903500c003040b0310741640c0d09500280312590844e96403800018005005885982e0b0030301010000480500041d401140103000500e4142080e09066039220902e940607480b4448080040086103008581040d200c0c400300d5900d81c0e507030b0a04403d0000307044900ca014015510384200504007545044c0a001c04c0caa519042d1303600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 368575179 1250 368573929 368573971
    0x20f09150f0a060906030b060f16050105060405010b04090f0b0301230604020705070e180616180f1e030f12020d0302090603062b0303051f05100804020a030b070305 72
    0x145452401048006464130100740040c1d8029080a60702c0600601018030341840f03200440c0da01e0b0002140c18500c0303007040c81082c050140034000e240c3c00c44000c031002c0010b9458004800000d1103144142840b194803031159803017656540d13100003140c030000b0300244000991101005074901054040c80400710324200402e05600b07103407003130b6125a988200101300340d43c01d003800108042d00041030707100320ba180d030805504e00c3c50003881400c3c0617410100214500709003004018011517601000900071641500e0100002c2031a0b0792150101e490346645800b0004643c1080914090a90005001d080000700100c04000d8012004000e81106600340d80c0d024503014000c40c00d0388a0080d95a0b4814028004681c003450105000c8010341501d00c4400345160240007002e080110040b011780200e0740c0c4004108945401c6120310041c1385054210300700d00784c100400214645000240001007020420000c0d0454442e8030f04880551b4100d030a20072141340401008024050403105d1442da00447c241c500340c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 368576429 1250 368575179 368575189
    0xb010c0c300b04020103150906060504090506010f09090f020904020708030103050f190b0a0f0e100f0e1f1103041103010f0b03031e1314040c0207120609020f09150f 72
    0x400940c407101c81d8200b903d998004501500c111050070f080c0640e0441c0c000f4008083c1c0c4903079401440c0e240c071441c0c0c540d4548070402c01280c10080c0038a05000524009200c4164406044010f80d081c84a00007050a10751000e40c0007401040011a009403000030880103000c00742c1e000d14100c9202d00c088031a0901740341c010030344030080d0f005280c525044031050300c00021114541a50300004402d000030340220b0040c03000041c0c40b0108085245030700b003e442c20300e011034103005040f0b8000c2000c500b031052000001c42c07660b079442d030a90201d02c9909840701010100d542c540003111840d507140003070354403070800f41001000b444484001134031a610b0140c90714180f800324011a0048080100650f0810301e10450104044c00c1b510a0070f0b003101c070104600c0c1c074014000502c0030041c0800154820441110700280b1040b5030f5403001c1c0d1800c3d035020020410802e00c410700e4241d00143d2001c0c020030008024800701e1314400022400035030100c0740b08200410542044e5912009010880302074242043d4441402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 368577679 1250 368576429 368576519
    0x1101030b13091e03031e151a040506210906040f03110a06110706060e0105150706090803010b030402040f090305090d0309050306010b19030b10030b010c0c 68
    0x1904100d00303018821050070941d009802c0036020b0010400c0b5800704407903104a152803140202c01007075644010305004032103464005184140700c0c108000040324205180c07400c681d584034003211094900900401c0c018001f05941c01030801070911900c502892440c2c0c848150180d804c159005220703000194220800500705001e540c000103030b022400e240f42c400311082c41811005244511400c00d070300300010454410902095a01112540c48005d50324100080c0c42e410307481004030308902d07030040c0055504d0081032554240c081505590b60804c603c0d201003e03100030130010b0450b6501000004640c0c010f100210700c5644211400c101340201307060103000702c4101c5a00503000460501115000d4100b0f5102d903c5801e00174100b10304070344e0383ca41c000ba1618100b600600130781200410300a09a11003400302c880008000c0c1004d100071684c0310081074042840c91072410415441c0c411316140c41c0d020740325031864681c000520b80303a180d45900c1101c40540c058400c607002c3c0110805c44182020904c0c80315 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 368578929 1250 368577679 368577701
    0x3010308091c083103030e0f0f1c02121009031b03081f0902270102070803090907050904090f050606031609051b030a05090c010c05032a0a0f110103 65
    0x4141001000c410010aa4410a040d070340e00804c1a24483d504084a4000a0055211b6510040815100c1041c0600305c440d410301c00380a50081d03451110f003592081c0458000d03c1c00784101900350070080c00000c40c0d520401c040c4c0d551302d0252071103410741030080c0c0e00300c14401806500d03420111403051030750600b0200342090140020702d000c004122007480c501c0350000104003145401030b0302915a000c0400300d0b4040020307103092080d00b00800c41c0c3c51080e000c000301660300900162051518110b480d540b0b80c41040066403081c40d10368000388050b8019400e980031444c000d00300b00800c14043c50701803a0408a0b013019102c510030000010605d1074005920448007140c00c00000d901c0b4644007401000d0700300500750303444103106c40500c40001d2070000091445007131441001b081c9400c1c00d646290070200c0c145034440c10410740e06582004120000100c0d200ca1641200b10400345d40440760034500d1441e00107c640b140c0c000e0b040c1003000e1002d0401840d481c40d004000744c10103480044019400ca403012111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 368580179 1250 368578929 368578943
    0x5150903030a05042402180a0503060414070e070f02011a0a0302010e0a0819060b0105030c0912010b12160806090a03110102040e0f04030f0c0302030324040203010308091c 75
    0x34440c4915401458100303100b00c0d0102d4034040b08042050307280d5514131740c080f84903030b0215044801000000d151440200d0959003200782c6414030000c661600002030001d090031140d0340c4e40407150a400c02c0540006d002d280c44500050404040041804013070b10a902c0c015030901c04100c440609c0100c0c42000c00c0c40c000e1a40c0e410b1071468ec0103440301003403c46055404244400002000001442905040310b090740003041741e01a1454000d08443d03e800c0c55504010041c0108024a000a41210b42c8a841202e501d40100d026286250140980032003c54000c00500c030030200c0800005800040c40a001c050854030a07100c00030540d0b180c9003122401c0c1d1650054030075a01090241054003260040c00f4005860030b610b43c460040034200a40d141c44040114074200014107600142101940142c0d24080403480c040d038600a54070300000c3d19909080b40e68442d800140f80c6203000c048003054000d80207640b80d40e52401e200340150844422140100501000d00380041180b1424038251544604 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 368581429 1250 368580179 368580181
    0x9030306090f1401060f030e030d051e10060c05030702030706020102030a1d0d050705070b19030f090b061c02030a051005070801030c0e06040204180b0301110708040515090603040308040515090303 86
    0x3c081b56880784951740034040c103503524a00b54400d0000d000234440700320714110104050520401d410715060341c0c1d032110f000b48100001802a1407422a0301e11085031028907281d408000036080c802d00b10711034460025818800c4401c0010044d4040d006148910081d11040000f80f40c02c0381c81240c0c441004000d213000f80c003d114800040c60180014103103085c00b038421240702c0e0380c880b4104500d65014590003c0101032242600416903814061849014603400040c0410142950b9041c02c00c04040c05861080c00110190325024000002d841010758008040f00c5401849080c041e45540c0072407422100c45d810900010003942c02800e40314101d0f031340304074105d10300341c605201013409141c05051164456020880000c4030008041e104034040c03030740300d4002031071156002014219180d036169007a88140a0103010041091103003a50101c0740c041c1c41914007500720380580c5656100c1c01d070815500c448013106102c14103601c60800792050f8840c030102c0f03103038003450260142035440842d40c100d62540300300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 368582679 1250 368581429 368581439
    0xa060f1505090c04080d0503090601060e030a11190b0d05010b1c0903021c0206070221071e02121c02030f16021201050a0b040f14040b0c070609030306090f1401 70
    0x9a0b60a50041504400d0343c1001e456400190030079410844c91130009501006010001a091103c00d00408403800c1c42c0504a6451010175210606044068210710340210082c04540301c4c045004584001144988801c070346550446486422080441101c02e11305070002c107100241030203d1303500095071008009003161401e00d42d80030b000102d000714114051000d030b075130400c1c4208201001505890b005006507251601009150150b01e641020301e14144024004101c020281181e40164120303080781d00c00300d040c0c8100502444c0040300250015801c0c40d0000003003034003161160101055080150b407031018110201d82c1c0c0e00615418800c4c1c40000c0188000b03112240321501c090501c00340808003101181110f0a00311030703007280c0c0728040d80e88601c014556864a07210300001202400380801580e02100404609641e0040006100d1000c41d4003258048503078009032040780758403400500c5205158900180074056505c1030300d8105080002001c14600d8a0048111a020302c0750101041e0f840c0c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 368583929 1250 368582679 368582689
    0x3110405060a12140303070e0913030f110f03070f02011d150d0905010e010507020d1106041403071205120105040b0306070e0f0306240603070503070302070c0806090a060f1505 77
    0x850f5007120300b0a0b091141e003008490500c00345100b1385070350301d4256001081e841440103020000b409000c2c150300207580000003d8200d03101c06c410b00c4103403070010201070040c8000c5107440440b41440c4518400450b1000400420780c5907400064800c1c1e841c28903e00c0440d0911904282114009900803522450304c2c91040301c01001d00748150002101040310000c03a2903040c00c5407031001c800c525a9464500304032106804002c090310151440c502100c1500007402a140c0b0b40d031000c1c0c4020f03c2c0141241040311400e100308142c807076044d005907903080150402803010b80546e011415040c6050082d8000003010300d4540305031100c82001401409913507445280031104100c90000d91076105030200323295101c2e17480400200380700d0001208107029082011300040c00050045c44c0d9648a80001c0040000d420b60010990b070b0881c0d15802c01688812151810000c5c201c2c19421a07151440381c6820400c004400040c4481c2d654040e000400441d82e00c80019410b5401c862166004504070850411842c140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 368585179 1250 368583929 368583959
    0xa030c051810050d0f02041e0e0d0c060203060d140307050d08010602210d09081e1303060e0703140d110106060e061308070b07030314071407020a0305030a030603110405060a 76
    0x105d0b248100865005500080441e501c1007042c2000400c01d0319050038800052080c0a40341d05100c008200381c40254500400080042c0401003040b600072000c99641d0311441d015a245e103a200e41410000c050780425196a5000003005495602c6075048646005000760901c6040e20019405040915402004000b068207400d801c06030030031081280042910480c450303451424420380c4865a5800025403100c1008007907505400d901800300301009840d0910200441240d501c64000300b408510601041e0074901140e0010700b6805440c04400e14403800440c2560440c0710940380e094010b0324280c0082d007201c2450040c5d6000c600310a003000c1e101d103000c0000d0b1150300c403400140c01c44c0c55100c207882d9040c0703242a48240305515000c01d2075030816415009690781e4031500c4019541030300d0000c400400f1501c03030100070400080002150030a640b80c504458000e990031804a07650b5080c04d0000800409440c40700792501211b0b50a20704031880d00f8041c060003420010301071010a0300306401d00c0e100c05a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 368586429 1250 368585179 368585183
    0x4080c010c172707120b011a1204030903060c1707020a0312020c010b0607030203070201090b1303020409061407021b04111806070c060e0109091503140c0a030c051810050d 75
    0xc0404030f072401d10010400b02002d00072240c41e5101c560710901c1c1088180308187c00c08890302400e501170091068840c000e4468140c1e401111500c240c8480c14290749c1217549130805400c45091100f03020381d49800060542c0001035040c1c102189940d000e030120380343d418035440140020380500da02010a040354015003200360042c0d000091642074440000c409903c8600201c0150708081940c030199030704400004010311503800124a04000d02070300402d00c9600d8003009105036620324489050250340d07440040710b521120758000c4103041464019545205000142c000c0382a45402d000040c01e15015030244880b100b89003d0900c08040c0502c20040708410801760080c0e000e000e03203808240c1e4000010b00800e01621843c1b2080b210000041660030720740c001c4220a81050b0324030100d00b11f012420030841c1d40001c540344130502046090303410402a2001c0542c0100809008428041008440e04c2180c5044580c000198135a0343d80001c101022103120310941d00c00c031810486810004170500001d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 368587679 1250 368586429 368586481
    0x9060402090a0b0c0601060215070212130302060c0f0705030a02030c1014180a050a08100c090504021201080f0c01021e10020a050a090504021c09110904080c010c17 72
    0x56280c0b040300c1c03c0c50300100100500c3d5030084004102181c0c05104c400d02100c1461140d0034246441d0030041d40d01c1d00560b0000c0046400000c070000340b0140708104c68040e680c010071060307a90400f90807050791824006010841d034080c1400000c1e103840c000032682c140035400b801038083c03500804104200081a160300c003090100750910948110507610003001154030100d840a118070003942804600c20140d08214001e80da03046041c84031040014182407000728014003c6004124500200c5441c42c066000e96000f900116400c140004010849410780702c042040360002c01e61780581c16900c1a402000c103003d600542009540e003c00d980704840003001c80310440d40c4081c0c0d101c007004200d03403011102000080300445c24508440e0f120b1100c0340141000c64080d428096038440d80851604111484203005945000308810003081240e0782e00211402070203091140307040c0c105941e0652001200c0c07041e03940380140d10070440d40222078282000d242201803044560301c10711641c80074000c11034030300044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 368588929 1250 368587679 368587699
    0x50603030d110a030c08102108040801020c19080702010f0c0503130e0a15050d03110706080f10120f0510090c060f1d19181e09020906040209 62
    0x20750828040c104400c0210303815a680e64503410f40c0201100e0040d244c55042102c92001d00860b07c400710380303020a4075260142c0504145035444c03032503200c0c42d0b10340d0020811030021800203013011065014111075030031542541e001b00443c01c25010550201e800080c01880d00388000409544284000c1d100c4240c242041c20340846581c60301d40c9990800c550b11000049480c409106a605e400605d64100c7c400100510030710040000c1449002124007078a0b01540300c070040c0c90b05240c890201202581109415900400d031619002070000004891000c02401c9031008030f00c488a4100f181006c5a21256103802111083d1396040d00070580d440d419195031081021080d92203200d446040002c5100c2c2110000c0c3c04d1074a1009841d803003111080206124101104d22450300c0b11130652411030900704c4074400e092045c0241c4501607c40340d003190b180b034081006407600640c001e920040b00410452081415a45050500303010340707a840f05e000350441c0400e030124003039061a40141c501400010704050715 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 368590179 1250 368588929 368588947
    0xe04020a030f050c0f33070f11010801080d0f080a140a0b011e020c09070201020f0a0306050a0e060d020111031e120906010e01120602040902210604051905060303 71
    0xc0c1c22150344107a81d80c0c1c000c2c2ea00b514583c688500d4030a000d21090316001c451b0b040c01200640e0a00d00100c241c000c124115a255a03111b400b00110360046900800c20748101c54542895001d100d14400c0f003d0100d01104004611921f0005040c07c5211482d44c41c510b004e007030b070300c0100c4806802908a0126946503c000181d90703e8801d10349120f02c041c20380001e01502060f0004002e40403058016248004480c240305500f580441c0e4601448007d0300d954502e80c80e2503804a0080c450200c00e410510804500c003c807c41e0b142d0480c004546088034003e02454845210a44040091340e40940c0a03a440c466a001035000720f01400d071808101d07080ea0f01f42100181001e81841c009032900e008204000341040003441000c3c031403500032003e01c00410044d0304203451816503040600072035148200302e408190030054280c0441d4003910b03600d0825510740d04902005130141c00030340b030700000900c400c40020f0020f080034440d03107200c1e10059901c035001c2082070500c2002048080c3c4266014001004943c907 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 368591429 1250 368590179 368590193
    0xa23010b040606050a0f050c120708070515070e03073c0602031b01020702010e190801090b07030e010b13020706110a0c0b100506030f0601170a0203180708070e04020a03 74
    0x20040100d910307040d0b0340368034170301c40140340c21403a008940c2404000c0c401442007200000b03103c0c0d81e120031100d50700c0c1d464030340d814490028080c8280c001c2492240300301c020740042030442b000d4000d003156240c942c9280b11110030541c68007854041c10b0840104c0403102c01c1d01140b4440b14406c02d86501606440c01140708c1c00304030306034400d5004500580c0c000200b002d4003580040d0808000e240741c400031801c0c03290036400246030903d0001c40703a1050006c440c0e40700100c1e8071201881c0c028005500200b05d285402d2074402c080710030844905011900d0003407a01c8101d0410300601c0c4024400401da291005030107003190009411895003aa5541d41d54050f0003040d200c4800100001207854481400c03c00716032030905c05a2000810341200d0324006d034020000b070b4807007009407500300400d040801d80c81c0d03070303401d0040306c03000d440014040c824059001071101c4d03d1803c0d8000c501414010203580c03003000707a0955071030382c41e0344510600b00143d003c00d10411940740600ca1b59a00144014a00d802240e980e45070f100c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 368592679 1250 368591429 368591441
    0x30f0c11031b0307050a0308040e1024080c090d0308100e0a1a0a060207061407060c030506120d0509041a0d03020f060106030902010815060d020705060a0e0a23010b04 73
    0x40614120191540b07014541040480002c0c50700b00c940f801c00301d0440d83e4580d17650046205000000c0d4184001c100085000c10304038000c0d0100500000c0c4440121b00180d1401d40100d0042d004503603800d0120b01003814000c00c841140e90003416a00300e183c80d640d03003286c01c044020000380e020241540040750b00100c0408480c00f80340d400c00c010503169450389a0801840c0d102c2d40c2103100303a0100d0300c100b00a03a000300340407040300e50504050200c801c403a1503a000d40d12507200300821091526076501c01c0d194050307000324050041654182c002c01078001150f940c030305030041c174a004520141701403490303480d0641050015014072442a142c482c000c0000c200c04040b0035400300c0142c0c0003468100c00ba15002c01c00ca6004200c5407a0a00082c100b6800181031b5100c00b41c440842513074201000441a01c3e0f4004942100842039811036444000d0f00740140c560206a40d142442d6003002c1c1c142c41404030008103001e2854104031001403c02e003000082180d0452400320460554880301c8000c41650b40f07103e80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 368593929 1250 368592679 368592703
    0x1602010f0f061805010e01060c02060714101125050a050d020d03051f0603020705070f0909060518030a1121030f1311010509030328110a030f0c1103 65
    0x200d00da03410003000280880305010000f081c42e18100040007000004650035044540700d080105000c0300da400452101d03c82d101001d0917120813048240002040004e11040d0106115001c0041040910b01241c25204402c13001110b100c5204100d04501115442c1c80e40f450306c544115022110340355281030a12142207441d00258000800e0902296050b014881d488003108082400c100d6074050005110100f0340980340c109036000c1058010007404010820107413200130721500c5890341e00c0b007401020380a01c0030220744160801000c00d5034007005420a0898081a101440c28801c80d81011100031424419000300c1c3c0c403645070b03d00c1003080c4046a4000c5c4550f242460b6940e45000c81c3c1c0400d0b16035001d05100c01000800d080d071030210307417180b04071442078402740383c07445d501c0c407005000a2850103a48031007003040750082601c5d00c40c0000920b09001d4a042e07515540300003140303800d040f505c0f043c0b8072001070081804000d242c104280b1038183c06a4042c81581a40390885802001c285000751344004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 368595179 1250 368593929 368593931
    0x140f0105010f03090f32010203070314010503030904021323040606020c0f040c030f060f080105010e0705070219030623102904080f03031e0c031602010f0f 68
    0x5000950b404001c1d4220304409040902200c12079640f0241070801c40700000d0312121544402449240d0040c2c2402030303010009001000854a010b0b019000307510540d203020200b481c100e502048444805000f41c1210350043c055401d001d078100a000195010206048004030300d070700701140c00e254944140010240700d0f00510354542001d004d03c0221502798200c1015940318211920036507580c4e149640e4004001c0c0c030041400a04e426003600a05403a10018032050b041c02c03400f00c0d0384801205040202e0307074580028403031642e903117045440c0260141c0d1440001034081183d8000750824054850780f000d054045c000145036a1744980d8202c03482500b40d81081991502010302e009010301c1415084942040c03c800301500d0405640345061a5006000184404064000e8603480c25030a0760b0062401d4020344040c200d041c00d055840b540100c0d00200e142c0d502203e05101d06d51030a080c0f500c07581030080c0817895038807508074280c4d0f00b240902288046649400340701240038401c1c0507a4032150a0080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 368596429 1250 368595179 368595181
    0x20c0d020a030e0409120e060d0c02030c010516120c05211b0a05070209061f020a061514010305060a0306020f09090109051003020d050705040c050301150f1d04140f 72
    0x18000f01250354921401c0e11440c141500c1e940442c0300c50b0144624143c150910f004004100008990580500c40780781e840b4615002084110503008401082000c08840c020489640c845040244400c400d08180c4000350416140c3c416403000f0303610131108602141003103402c0c11030081520f0402d45150f0b41d0325005a024505000180500d00300c42034403070f804480c00f2070a01c581c0e4407004003207008400d0060300c82e511240c0400c00c07648650307101914041440d1003021241651103000f0f580d42008a100b142c0d031a14040c04200303000220320350b2909445810900c3c4d1140b51102e4011005882c000d0f00d803903482042d13400000005903041c4000d00c0e00c40800e441c1030352900c018004020381c1c0201680480841410301d420451003000d494900410780380e040314840c00c21070150a002e86881c3d650307000300340c10600e0042056406600500594101d5408120454242000c441c0440710000c240c019840410081d01903801402c2148403032088a80303000d4000181c441c025401202d41510640b850a001000c4030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 368597679 1250 368596429 368596433
    0x3240f06061b11011d06030a02030601090602060c04060c14100e0c061e0c150a06030b01241d0402070b01080c1905060702060c0307030305010503070f1d0a020c0d020a 73
    0x8140703110002d0790180e240c00e000c611a12400c005403151640b01d0b040105032114108414424032a0300c485013809094992a4a0f10180d840025482680c43c03a000c0b07500719200142d458800240320344103c400310043e504013494400c0545103d140c0c04011103060b1904002601030200800c11041c03d1044040040345042c184141a41040b62040d6071034002c24080001c6440c108510150380b40650349101441c1d650380c00c42e045a4204080e02d084c001c0800083e10600403000041e420840c20ba134007d101496059a82e18a080c03140c4c4406d000c2d001c6000e02d00c040900e0003900a00010b0090345195495058070307403280c40050704a900c0010b007100c50000d450014400d100080112500c03070101914a0300542c010706d0740f00030103945d051180d1780c851030f4005241001c5403105020740700026410004c8076150040c3c0e14014002e4a024060540644980c01c00090158443c040c1c40f4200d440c1840c20a035807000b411804080340400903c201c1d8600e400f0021030031070303000800181e58080466806000780708028 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 368598929 1250 368597679 368597687
    0x50403170c0903061801060e10091a01020d08060a2705010f03020a090207020d0b010305010c020f010b280e0c28140d0e06010f03020f031603240f0606 66
    0x39041d80d80303401e014492020141c400003240790308030002503800c04141020b43c070140c0c0504904d4111000c071200d01c00501c880380c03061401500070341b9080f1030280301c1c0000803a107100c1c2c2400441402070059020b4144c0c548035030300851101d50007480c00361502d000b1030f40b210a044682e000d4403c44410f0b0000b01c403102090f481d241c0c172034903025005100c481c400342451600003414085040c018001400d0340025008115075543c648514a1a800400b034142582c0d64280300d4003c1148140c00e2b0054000c1e401083e440380303418400c0101c9034000512007503100c081080011220114102112035004400c0c002080c1c18044009444c851440c1012055503111801c00340d64401e98000c2d035180c1440c1a03148013100950708800001b201c420400c00e26a20780d0300c500c0f0400c0141003621084a03d07805188000f0481408811850b000c0e24000e407081e4071007800240a150340c030041c0700240c646010140c041400082ca10329103014949200c00d07c4800140c072450319210440c4d1022203200d02031581d0300ca04012880e04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 368600179 1250 368598929 368598931
    0x1e030c0f0601050108070f0513030606080c0a0b0414011211030403090f0e0a020309190b01080c0603060603010512030d0614151801050d0f0f050f090d0c030c031205040317 75
    0x10800607080740e51501e4006050300c070010b450b15040c001d80b00c903003c40862040058a60b216082c03c44542d0117030343c900b850700003014140202161400f0351000000c0324180540041c00700c8400141084c5440c3c03900500001144410301ca01c3e042080b10140b041d81007070f080c0034100d1103818004080d96241440c2c40d01801014541c2d200c0c0782130141480040190166401100c0d078401042e18015035280c0c1c6018580e401c00002004054010004c1d5460000740031000003024140c880c04411a80303801d62100030824076000440b9219881001080140506c1c204011288000078144045030f0410214a01540a4a040e508001412049084883c215142000180410706842082240f914150304d454a2042c1c200c507040307070b0500000042d0707a00d4012003544034608c07083c40200200300000c240703c5480c01030702c0b0030f88a03414a1818071011469060b00818880c1070410f00d41c9800b141c18640703980907a15910341c6802581844485d04483d605500c1034081d59200d0b0b442581c41508c003071100240940080c030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 368601429 1250 368600179 368600203
    0x2030a06021b0a2126040b1b04050f0103021c0f0b090c030402040b01020705040f0b0f030102120f040201050f040602011e052703070503040e0403020c06070201050d09051e030c 77
    0xb003c081003002042400318501039180620442411603140381c64180c1d40005018061050406410030341c1c0e50000780400e44600840c801c2c00d000c80e01e82c440c001c074420208000c0c92039103d10041000108010314119a17506407982c018100542401d20021050305140d141010115429803038031203e0410110510503520060301c103c0e01c43c40b090505068268940c08001c10082c0169a5030b1a4030792140e0007040240c0050500601c01d2141c1b00c44c2100c1c103409003040c0c031803082c05480b10741d26201e02d500e01130090750080021003a030622183d99680d81d0b054298005042641400b41c1007001442c2c2c40702034401000a00503507000440c546058551a941c500d0f4800c00840032107103001d043c000255002e00b007401040c44981c22703609414a0800700c050030342c0300d0004003d149100018001800b158400c1400d072040b070181c1c003500c600300c1030700051002c1880ba0600090025100f00401e2a4148069024010041c003c40072550783e003080305110782403c1c6001c801c0e03081c00ea201044021000d20100641c01c4003070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 368602679 1250 368601429 368601433
    0x91e0902071b06020613020f0a0305060903091906021c111e210f210f0601080a1a04180203010c08060a05031204062d0906080c09130b0d02030a06021b 66
    0x4070309241c1450341072906c000028460121105820310507600c894100000e07580190036600e0600b03040c10743c550390340d210b1828603019810f050014001244844041030441d4420740280c428407500c000035800d80e5408000f07500c1804120311105034910420000c0c80301e100c900781008070385041440c00c45460302da6500e003400c140150701072400040031401e0098403c007d84014010b522008044480d601101ca0005000c94510030311003040320803035401c009c41e40168001c0c6c80d003d509843c0c0c00d01c00d1007564601c0c03540022142c41100c42c130708141029440141c201c4c040c0f440d46288050300c0e5002900f9601c0c0c412142000400600c2440380606e003c01c0c4d036000500c3c04600030101014010020315150107244207140500c001205d0b1100c4140095a1000c03108121031201c07620501c00c0c0801071701103801030152078009000000006e00030382842c421144103410017007101070703a07068803603180000d04206000c00b46c0000c1000202001a10b040001610b06c52160b44096128126641a59000c1c00d480001084a07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 368603929 1250 368602679 368602681
    0x3070903031409010f050c100e01020a08010506120403140f1318020a0804060203040c0f0b030f06010c050a02090606130906090c0302030705070816120c05060108070501091e0902071b060206 83
    0x303030317030480b44011011500f0706000e0f485001031440d05050809000f8401c802d10b05041c82d2598009040d40103103a0340300d040d03c6000540e40c8600500c0114080e01c000802c8450302c10000c200070a0251808650fa41640345c0300a02e003c0c40c40d070b01030103d90414504a008900e805d401400f03800b0144201c1e040300079849908604099404000508064024002a01455002000c1010310a800c5689000b0302541c202c05a1041c0c2d132240300400d65802214400590034000d00400c00c0f662043c4040248960018000e140f01c40244c0c0811041c108080c0c1880d500c031004004416917043c408201c0c01c01010342c1e000c00242280751079600d0064407000c4540d08101481041040305c0a030704103082d41c000350f40090f180741d2a00d007405e80d4100105c565440103090840d1511000c102c90b507203c54900c40c01403140040c1e40041e640c400070940da9070704500445012a010213414801180100741c03035159030500920008100d80d4410640301280e100c040c0c1500c854041c8080c444d42101c41d41d2450006090610091600b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 368605179 1250 368603929 368603947
    0x50105091003020d0b0303040b1201050103200a020a060f0614030105012d050d060603060b04060803180301020405122409030f0901030b0316090e0f0606010f14030709030314 76
    0x829000c108001c05141d03021036121407111159004d84a88000507045aa540751114031400868016018403884014510300201d40c40d48039004403241030a110107080246084000a042250000300c000c00843c4145081440424540d0003641800040d007000050818181042941c5094103215600c0c043c0c0c0c10310004101d41e031740060301c0e034450580b07030301d00c055883e200e601c204035112036030340d018a612410294500d418000c0070303030101d402c0307030b100300401c0008084000038041524506d100340007080e0170500442041e121076a90703000c00c40317100800062401c0e4403000040c4003042c2c0c001c0c030307443e10341d0040581000213000c1840080309080820018443d91812854090742c0703110b40c480c0c0344880c81006c01d85108a9000e90003034803104c0001002c5d5103458a007118608465003d40c03080c01d1000341841c00c0468510008600702e1010b210350310140a050b504c16005460841d6101c00301010410380c02c0000e1100e918440245010305802c3d0345000800f032441c00c000303000030300070421142c04034000c0201d912 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 368606429 1250 368605179 368605189
    0xa0812030a0b01111213270f0608062a0301030b04020d060f0f0b03120c03090906030a1e03020601050f010c0b04062d060e0c121321020705010509 64
    0x540812408000701c1c84121540040741c1d149001386006990748580540421420844000303000c0d407501406155010603038609000e521a2201d446040340c140200303c1185180e81241c01400ca1001e2055001c02d07455502d51042d0f25001d021038125030724000e1000c011000ea0b8990700003411002e0145903103400d550542e210703040800c0c00540000c1c403e2001051920030450160040c0325042c8004004000c0e481c0d0360082207010302015001c0511900542111800400080050f5004102100c000f14140b0f295081440008240a41020703030611681005000059064451112080d85400900d80304d40f05032402920b050810b0b00424440c201403100412540d13440252125a41d402c500440e2054645082050060541c9850000b9654240b4100201802c40040204200e0000c1e941001502da650300000690f003010381d08550107036810000000a4809a821540c10901a803001c503003142c1a0756591500c10703081c00c1488400224428060041e80d014818100202028209140341560640000b5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 368607679 1250 368606429 368606431
    0x902100c05030a0e0d08180102070f0602100203090c12071a040311040518012409051303110c030109111809101d0a030201140c0a0903031412150a081203 67
    0x3d08002e01010400095602d0300c0701c0c55140b9400c00d514a5880340144501244e1845c3c1f95200f5026204e01003000600c08000c1000c0703022105940d002d441110302035015040a580f0151134500d50b845540302000b020b903502000318200003820001460140d243c07019009141340c060b24110040c1405104c10400310b00c40886d100b900c030808807400203240d924450065809240000c3c680b000750719212021584801800003850109802c100075122640e5030700750801a00d40c11680c01075880d03945c1410038000b90059589052640e014000e548502c400070b00460b0844000100a8500685125071078040b414080b00c01415060340400110451030b0514019641c2c90840e444000300a0b91010441a0085900c40545440200c0d206a8980b007126080003406045401007203004250b040c07000c0f5425028100459114044035124130301c1103807464030141c444d13100e20080c195482408221117540080f00e00090b510507600c83d450f41540c800ca070401d1141c0c4441d207800c181c0b070301e50181c600035a035000300509803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 368608929 1250 368607679 368607697
    0xf09070f0f2d17010602071427040215030f0118090c06140f1611010807020a12032a03151202040f0e100603021e06030a051b0a030902100c0503 63
    0x4200c2c22402c2c1000c44400c42250f041c01100207403400041269036000c200320b0200c503860000c4003070321480001000500303400004c200c1441684d01d44030030104000200c0c000d52242c00207095003c007042000381e20401d684101c1d4604001d69501e0b005100b070740700710040130b408402141c400b000b0180300caa071080c9000415008220500025034000039008a010003200d201d1103203051400d480e880522601811440305135001c54015a41481151055100e40122442020668028090003407103071142094054260490b038209501d40f84a00f13042101141c40ba0740d100c1c0007441c0319120486010008007200c138001e010555105403128100505400c0ba218501c0d07503501105c000414000340b2465070024412100310701d00c2070240d8079141d07000c48000e0340710400720f034003c0d2003c00c0c00010441811a420418485d01a4411810b101082030412a40c2c000d0317500003500a01c40b101450940108040c98001c0e4169400083d1540300000450610075445101e03a400d84c148203901c0c440036510a0f03241d000b04071178 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 368610179 1250 368608929 368608997
    0x71a18010309081603031509150b0901021606051b010515150c0d0507050c010509060a121d010c030e03090a030816170706050f0906060409020f09070f0f 67
    0x900b418040c112044506080303a03101c2510700c048603841e021b03000c0c00544180044144014070000350a9006020301010031070b020080c0c0750f0003414940540b00d41d03046104054114895802c0c01d6030210020400380c0042c28030f6480303640d00c8050320840c07001e123403055803203c503800c1c0d05180501c41c12400281e41c1d08442d10b412100802100300c442c103c0c1490b4012a4130042940c03080410340e1032520741200007084500e000c0d900b511058640c07003006407646d2280240c0f003038010f075042100500440c42031442c0b804084244801065030000100205031002c1c1e80c02074045075940d40c1c440300700740301c0d0107200f0885028401405075042005080000d540411544006084d0300c1c2c0020b141c000e801520486140b00070341c04188100c0e220b810110140403070304109000c80d4880d282c4400328400180c605001c61080c1c001c117004040350b0340d4110a020240c001824100e80003210140e035050b80c1c0d9a40c041461003604260340e0050310008100000f808014800f0344482880f03e440300c0141e9540b44044103120310501101c3c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 368611429 1250 368610179 368610191
    0x31e092306071211190f030c050309090103060c0201060e0112060203090f0d12060506031009020a03110708070b0105060a08160905060c060702060c0c0a06090f050f071a180103 77
    0x1011588520895030001c05412000c9071010b680c40e0006040d009905494089610031420000d212000556400b80502044142d001b8400046c2c81040718083c494414010b8a0034280d0301c101240e850704080c0c00c01c480058403642440c03201d9509101e000002c0556414076101945001441404420541ca01401d90f07030700040024007a9008110240c0024007000c11610030b5403520000511220040c280d404c070303250500b500012180f4100d81500c1c01a40a001c0500040340740051207030082d4440d11642c02810b480d1002e80d114000404041d2106502603e00c0ca5900d00c1640b0b814620041b058102c284a07a50502941700d645901111890380820180c40d01d840b0907509450507122015941c0c41640d2001001600d5030004801250950003202c4640894080d5140c1031100541d500940110712007a07403240d04100d0114105801080d6210b018180d44000d44c03030720382c41c0c540c00d02c00e40c0741c40314406500203442040447c038450501d080c5e810380c8604003401d0160100321516202c0c41c0c0d540c0241050b4031a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 368612679 1250 368611429 368611499
    0x91212040206040302031618020f0a1d22050c1e03060a0f0b0d05010f0506090616020a08030c120306090117070b030702070602120c06010e040f0503030103031e09 71
    0x40c220f40103990001d0844c0c8036450401c8000f05e400120780a025403200d60070801c0b511003403160003a5001546003029003404c1c6018900d08a0b1101c00f084042c1c05240e00402821001d51a004800c0040350406540c0340010200c0130751280507110060015a681c6408000f02e580d1030000d0360b01001c500c50848441d40da41d8440070000350400146810805c200700003c80c0004540c440d80c40208031012030032000344010b030ba0360411414404051711032250000000c004040c45880c01c4402480002090712600030036852030303004101904080e4200b00c003c5e1388006402c0303a0050003000301081c5804208465441c3d40342a01c041a0a2041845032060b800e040580074442c0d17140900c0f064002e050b50540c0305480345030544000b50b40310000e204440244c020a2041194110598121151420800300400c5030b03034680611a44a808024019140e072404040e0368400070300244010340c000c50107540d03103241c8149136a44068100321316020010034810307901c20230086000325031001e40851010b05040e0050003045 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 368613929 1250 368612679 368612689
    0x21504060f0c080903070b09010f0c02060a03020c01141f0b0403230114100f0501080105030312070207031a0f0604021303030e0312040e07091d060d0606030b0a140912120402 76
    0x32031005500d0300521ba4003280c0b2440f448040d01100f103090380d8030040c1403c404c1094500c611120303800394102030100058244107009070001c1050708400c0c1e00000b17104600b45100d25580006032110f42d140d0a00d5040404406e080d02110005080c0e5100300601c0c052841c0e0360703011200d0400c036085c6600480d8000020007100294401160100e110b91810341d20329100c083e01c05a07030240e02072204054060400441c2039482100001e042e9000900114035241056000c0b142d0300721f00030074400c1103200c0c40c0c0c0e011002452800b1181a00d13040348042040d1420901c092102e4080c0080803030740030702e20600c140c1820083c02d4440e0011a901410401d0550014001081c10040031f1420092207110024000414180d04108a44514140d546034a03000e6150741c58000350800a4111b030881603009030104038540b034486c0d0028001031007041c002800b06e0b500d65a0000d0503c084032400030640e901c424030f5000d8144240880c0c0e0201d65000900301c0101c2440703c64003a0301a0f110a4036080101800003801c54540c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 368615179 1250 368613929 368613937
    0x4090f0b10090e07050913052401031a1303030b01030b0a0b09090601030203090307030f2d02070f0602070306050c0f0f030a1824090c12021504060f0c08 67
    0x8424094041d00e01200030300d11940441c807941c828035203054160600c034807000c500c0310140c03100100105d0940e02c034031421360000d20604500b96a11301840c02800e55580c215040c00840c1b1744030041865881d0714604180002640d200084448001c54204100910518071001c0c0000341c0d00d0700700003c1540d40240120b0003409079020340b58204803030b0343d030214009046201400310068200e0f0b28803143d5035400011002d80c0000e030307007140d5640d01c01d02c074041c0003a000b1411034a120466250401e10380301300140544003c031000c50282e05286064252245c070315410301050018041045c0244440c0345403541c0250f0b901c155200103040c03a0741c0d13840400e4600900390308580a0140000032241c0f582418041c078411680250345400e1007900d000c2824403031500b0141034920641e0040482d4000d1030301d111149544103400101010456611b4411030005000009a20302030700680e101d9000c0c0d46035910512042e07100403401c0400c0c04d9070a200c02c114066000781e1405000300149048200042c80303150160316805 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 368616429 1250 368615179 368615183
    0x90112110307020109060e030a0c150e100515011e050a0201060f080718140c1602120715030509030f0703020703080408100b1e0f0319050c180108070504090f 69
    0x300000c2401415941508650a11406106d0400c451801c2d40f50701c42d501c0c03280314441804182610088004035181001402c1041c01015000c00d01240d0440c24a040a050810081005a0351020300103600c0d030302000381c002180207080c80c42c4221030800d180c0c04202c00c0720006030304102c00007515144e541c1c03007900103030001e100740396072081820303111601103840e100c040c0201210660401032540b0116624000c80c01d243e9901e2002900c951101f801c15074499000d2104202c502c55200d50140058807214002d0040d90342110142c001d281c1002d03040c0103001c2c81d40300a50300300350500d4103004d844400070084484400e84000060f903204164074082e810410664005401c00c8804a000038001d48049040303585081198010080110488104500d40c640c0c0501c0d0003188004100d82c44983c00d10030400c3c0040880141115510b000e0004581100545011b08645a4000c600b02c080c0701d050084050f00d9140d450740943c1155030502a40e542e0390255485187c1c0f285449803003d1060080300c0303000c010460303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 368617679 1250 368616429 368616461
    0x8030a060b070c140307030f030f0c1e0b09031309091704030602040501200d0f030f0f1410060f0c0c09020a081b03240604090903270b090112 62
    0x45400d140c01209281d00c070b00004c41000d003103004194a000305442c02600e82c01400030321031a143e074404603102c4058440c884144418454074001041800001c034075910401d0050b4203050f021854138045545000d0214540369005000c0e00000c94030b07688030340c1e040d1520b9600008450425082c5400e800360fa08038404010701000801006010803500100103941003070b01d0b00e403150403024260800a0446054000440d00b04015000103140300721201748a2150514003c0ba80e261400d90002c12142c81c5d4001100050f07858048441c01910f0000341d651040240e51400340c900e103040030180c818140d00d03040e6801c2103130480c40182007021a12001c80070b483d42882c11503e602c00050042c0002d14103880c0a10100703043c03074441a10415610031644504a258800d21496801d405000503405561811541c032003070600021a0400c218426048018081e9440707400131941341403004080103402900c2022052102414045941d004046a000040c01c4c601100c0560400301380100510040280c180f1007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 368618929 1250 368617679 368617687
    0xd050910050708090f031204060b040e0f0a02090a1104061215030f02030609060c0d092a030201081302010f0f11120d2f0c150c03010e01080c090408030a060b 69
    0xd40c00f40545100d2001e12088925800c61050902d50300e00418007050303c49000c4000003030000b5040e42107031350305850290010443d0610403a0b09410070303178040c6080c1210f40c4144540003e610f42100919045000d00d1010040c22401d40c40e50003162086006000610180b400c845003c195a0352004850013a02103006260302d842c0d140860303844c0300ca000305a109102c1c0b0008611b1035000800c440d03026204901c000c501c0d09081943c4000a02100b000c1561074600c3c941140c1c0494400721039007074018a2a0120061480c111720002d04500b001a221500c810300341a001c20060744c0045200c50742c02220b0510101c0040381c2c440840343c0e5090003228094501441040c00d08e000300540281c40c80d080c2e442002e000642140c0c444003804040912008000004075101d11000d64030a0001d10100d50044291030761120f4846142840a174151059070807940d000004100026480420b18050042d48020300742d54007800c000941c0b05200070717002900d0008004007040301080f090340104000c0c07580b40d40d42515 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 368620179 1250 368618929 368618941
    0x5070c0f080610060512060909150903030603010c050c06010b070629130b180403020f152502030d05090c0a080610080c1030020a030f02030c0d05091005 67
    0x480c0380c2034504203c0300b4018500801c003540a1015104121503460300c004059880700c00304a5505c0c009404d480743d5000e4200c0c0c100b1840e81d140e0344c0da4824001d42004607501c0c10184141400c64a03c404103104011080c0b0002660540c00b01c2c1150444800106a541301c00c01801c0000042c4000c000c080b182c2500d803101d0541c0c10720700c40f16804010341d04442201645008520307040c00d9074606501c0552042c080c3d010b0b044850450307101c90381c0082c06841160315206c09a55190319040404098414104e0b0035020401d6143c10520300000d034218113654103158010b1040d0180da24091140901500b6489000094804d02c08206d460454000100102c2259a42c1c1c21042d40701e48050303490801d822100507010550781e4002580b8100700300c0c0601108124818290125000901c1e00c00c400e01c0150200c1c0012904010b025001e240c11120300001640da6005210160840d10880c440c1f860381d600600030000701108200903607001490802000c00c7d540d80e080c0c0c2d064240720000a48003483d51a00081c400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 368621429 1250 368620179 368620183
    0x7020c0a081506061303170705030a0818070e0c0306121002070b09060c0304021302190e010f09080309190906090504020a06030b0d0818030703150f05010803090105070c0f08 76
    0x74400003503403840d00068540f01e052006a11940048000b413426080d002c0002654000c0040701080c2c007044211304010b180d5880c1403d5901c560007050008108205001c800e054410301068103418150090011500d4224012846200280b00041e0f81c2000b100140603622080000b4182d549070206952441f0102980a0000e410522040d0b03108005000012221400040d8840c00348400a640c642075075660303801c0000850402070700c0400250207020070380d140072954101e00c591a501e80c8170be03030300349182c000010890119140081c003002507042e0304003c481000f100f19040701c1401d58605141c440c0c8042c0801d040491580608186840c02200080c0140036501050260340b0840b0310b4101556038400c100d050307414507498980d020700b00c01891400102120020400000f000c00c00d4400352111034000b9041c48419407054400703840306017000180e520980700d4420403071002c900800080d410301a801c3d5590060300141c0b0f041c00f034001490014040d0820125006140004801c2021501c90307822603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 368622679 1250 368621429 368621443
    0xd06090608070506130519030602070303050601030c1817030705030c010b030708030c06010e060a030b090105040b0702011a04020c01150609050a050a030305070f11062205060403020a0e07020c0a08 86
    0x5071107000340280880e00e45480b1003180c080b40005050600c4682c1003508016250703004030720500c6025148100000000c4240c00a030080a0003038034006154a0550b0016013030700c85e41c080c10303c00c001c1019401c0f0402c2d4002075040e810f0b210303043c0312002c410003d1000c0703e15520034001301620b41e100210f404c5201c0c04c0b054002d852101c1055050700c41030750381d03051032036580d0180903c044207503004800140440a07031801d040341e2084001b00704994280da2600c40035a03001081d60700849503512141040140060304281c141c01540d01d1000700001c0381c00d02e01d500360004440c0d0900c2c2c811500010b1340c014640e803d40102c001603140102d45442a596000c000d410582a4030a05004208082000540703180410014003166056100c1d18030304000d50741d80f801d13112001c00007281c0c01011039024039030b1515441d011f06160ba44803001511503c04000306d036419a480c0c2d0780f28078840d440800007880146c4408414201f00d59020104070110f80b2070080c140e007040507941e4420b400940e034003000252444006048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 368623929 1250 368622679 368622689
    0x5030d0b0312072a1d071205070203131715040606031205030403021b060301030206070f050d030623010f0f0e03122203021e0609090108010603030915091205030d060906 74
    0x80e0000403941c0c1d0718000020621701c50403140e803024540903000e02400d804a40e5200100d440d11903484500d00c0640011640241d64000059001080702c1c2e03003025000d844000902030205040c007030b5002418001d5502e4444d01d00c2008501e040d44041800c0203119003113600510f40c4030300000c8484240d0040203125820445058005100703968072200d44004514440b000b404019050a10303503800c60b02030044aa004110071564054207031399107008a001404240240e010030350b03000c036001d03160400900d4014015100d0000e1000529112030060307801100d0714240d103005040c070492004c04c804050b5419a0070711521600f40c004c104104010702c885030005d040916840181c110824580c8000c0d080c0c035611404000d402000244c0e241181c8825210044002c0c02c4c020301082c54a4051008604554001e0b4425a4140e440d120203004158000c243c132000b804049041c440310300030b00e110041c181c04042c031400b0320000d212290300c8288001441160440075030300c00180826540d8480c1600141001c0c820 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 368625179 1250 368623929 368623973
    0x50d0602031b030f060f060d14072d080603070906090902010801090507080c0310050d0f0b09160302040b0a0915030b0601020c01020a110111070303050c1905030d0b031207 75
    0x54080c51042c07001940d002c0c48900d2003082040e078409041c0b04d45070319404074065001000340045042c2a0322030042d4019210101140748071420494009007198600313002032200d920000451340d800103104031108098030011715100945840e4100803034100045a01300f480390074208100840c880130150061a5154402ea0380c41c04661303a40c0e24050125a81640c2200001d10b8200200300e0b00ba0146010310703008a80d24148240e0581d44800017810320003100401c88408107020f8030381040c4010541003590004024001e07058022803c00000da851005000c020300c41e50b5100c00040c15a01d841d91044043c11818504114200d40d8403000e2005101501c8101d480604050000b034076035102041c0481c2804041e002060320b100655100d18600d590704401e9410411041000c0036054400c11211000f10b000303840d0b20b580c407800c400555003040095154a0b4076017102c1f00e801800100000100c074105441404009000308520f03000908007154804020003101005c40c646083c0b15038078006107652984080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 368626429 1250 368625179 368625211
    0xf0c0d031b0c0302011814040902062b0e07050901150c06140a3c0b03030304080703080a0c0906050309010605061c050112110d030e0406180e0a020609060a09050d060203 74
    0x41b0484041070050b0606060140b00f000b00c5410143c01a00c1610f10041605060041069800304040e42d030460740d804110b94001503407840c1c080ca20403451400c000601030300b90682042d010410500c2c0600c10490100103106445030b55501c00c90b107402045503c1041070014035442d400e8100c860300140e400d43c1700d981c40d00111384a09400720b0480d80072041c031403540703001d5080b0956584010b90316103800d07c50400c0c5c840082c40c5c0315980600065200b00d04c900e00050b1209070a00b8003d100500c020000070b00c0078505101b180456030040301c88400c4410601c0c00a41d21760320000410f000d050150b000726007080000c10502d0784100016185260391080a004018680c0d80d050a088240070110303001d413644210503190380407403d000d84600c12007070003410000c0c0c000c4c51040101c0d04440c480e5200780d03c080e408004104003040d150081255803024103000748165082600040d80602c42c021003d0702c02c8000051804142d40142d440740010640142285020356039820301d0b0003e03610807112816030b034020382 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 368627679 1250 368626429 368626457
    0x60c08040201020c010f0e041d0601030b04051605010903020d08090d03271a25060f0b3c0a0306021e070507052103190906020f0c0d031b0c030201 64
    0x100d480020340d000d031f941045101200c01488010440d00050840f4207070390300300c4040480c0301080810300851003038030304182c1c900e442e051039400d1001c003000c030118060824004000b1381c3e900c072035a001035940444007070120104a00d4805200d00c1850401c640000c000600c403800d26030001c010b000d102ca40e0f0380c240c205100700c08021007100080c1d07001e10715804890a941000c480391038005000c03658245040911860318800781140200b107000070480d00140c850880e00030140090003554880c200a03540f469000300e80410222205407107011500c0c90025030412030300780e40010a43c0002810b4042c1040084507102e04205002e980951000c0b1001800300740c0c240c80400d40c4030100d4a45540000c00f03090714906090800c401141c0300a00e600700c40800c4c5259211120050000300315080303079a4065003071280d10b404081d050201e075a00c400c065400441c900c0a1503540440d40da0392080342200c018180d15401d20741035440c0c50802000050464030040140100031030100c1c603c2c00e89000740c03503584030300e2216 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 368628929 1250 368627679 368627687
    0x5031918060609060b07060209030c09100504290111120c030301140307060f0f020703150b090702060705120408040e070f021b0a0302090a110307090303031a01200109060c08040201020c01 82
    0x10302c12045d18107010044140407a2443c0c0c041c081c50000202035a41c000100400079500440580d03035903400c10b544030400c110a1809100b0030a48044030100700c144400358078004001c0d603642100a9040c0520241032070700310107041c00340800d040c02546806882d540380854465880e00f09003c1e1810940c6204502115840d00050b1030003200d460741e039000314541d8098021140c0c200b000024034254811000c0c00b00c0000e000042c404d16070f0303500010000302074031003c00300000108054000000c0d900310405218405030b010085420006040d410b59940fa201c1e40780c110b84c03510450b84240e40008509050281c002d070f00a01000040d82c10b85c0c222644140d4140d101d0451001d28070620780e0010034040200014200800c01c180e01a2040100284083d0f8009840d0b20710b520464501000640c850028020950984983d581501c135440e081910700405000183c071715507010046245160f10190301d000c1d1b164094105104a80e48498184007048c02943c015014420a0300c0407070150080c400003080c02d51007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 368630179 1250 368628929 368628941
    0x10207050d0203191509060b01080708010501091401090e100812040609061b050d0e0a0603020306090601081b04030f02010e090910020d1d060406060b03040b060105031918060609 78
    0x10050104e40ca01508503205800840600326218040d90030184090100b80c0709001c00355005050100320381e03400000041400400400d0a02404250070050040d40d038440301e17034401d0b41d08111480ca00c840380400140d031402c51903032124080d0322807002000f403403c2401d480d0b282142c4042049909900c018007400c2c07828000d50040d140090300f00b903030800582d48164030031203403026119507800100400c3d8a51a041c040e080c8014400703c3c0909010403503508243c0c4078607000f00842d240450450070301c20006803003610058260741c10000740324041002c070040214202d6107054113908072980c542d900e103006c0307a0011100c0f005a01140c081c020440d110b080c20b18a1134425a8000050b0590042e2000690025040040384024140d44c810304000240c4008548070b448002801c010405c40c81d0518100068031802d42002c60202014414000050030043c0d03c0e80c1c200c10242003491b101c0c0c1d2084031200d0b401e0480804110158181a24140c5005070200d44000440c0246410b00010f5100c900703660664034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 368631429 1250 368630179 368630183
    0x1207030203030609060d330b0d0803040611030f040501051302060304061a0a06030203090f3f040b0306100e0f0f131e0c020706120504052a010207050d 66
    0x70400010b40585001c0d001d2a90101c0000d228800c101c425450706511880d420150b080340c052003100d09410703649001d1036401d034980c4401042c030581407004040b03000801c06540c010700d04003020000c50200210740c0c100c00ca80d651007080103a140d207884030f01c940c0e09240c1594140c42e2541303003074003140d00002560481c1825940250203240345407503982d1540000e00d01190000d0403c03214034000340d80e42d541c150442c8007c00c220395002d612411b19003400713410800b81515520041c0d001c0b0307107500944851407410010121405c189002c0044004e500e00c03011002c1403624241c90b420000d80411400400d0300610b000f100291a5103142061038941604c2210900c0e644030b9001702c4a0031000c4051411400304820080054070b02da2000c03a80c0b8180030180c543d0303140c0c041c0759808644003109140c00e20703101f2800d0342c100501c011300c005850720301b0140c4403403502e4464010385900c4a0009052180400c0011440083d070f4801c08600300851900030940364202c40c43c0b80c01405440d030005642d141500210410035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 368632679 1250 368631429 368631433
    0x5270f070c021002071a090f0307030c06050c030d0903081f030510180501050108151e0c0c0307050d0509010e0a0807062604080904050a020c0a080d0908041712070302 73
    0x2507026020030203a891014441411480341d07134004140d540228000d5814440c500c0f90441e00d60002100700014a83c03907610041c000d91000c48100003203000002c02c1c10840d8442c1c280540d0750552a1441400c6100d0040003c00e03282c01c002c104001c0551100720700744280e00c03509101c0420301508255182041d40b44c440a04140d200c66610324580c20315520403e044482d0344540c01c00c8034090b035112400d5880036842511580c108019282e1051812024198030600b00d2882c1440d450603c0c001d00e0b0031141c0500000e99150300031520f90f591500c10000c0310991a000b500302c036403c200002008000d40d00088840c0c3c00140d20310f030340c0981c500b024605002500c1c103100c040c1c601c140c00d190040720101c5c800e002d5100111283c41181d0403030507e50524034001c50282401176543c101c05e83c01c2c08150790014003400741051042000200006000c41d0f2149034507880f9600c180e841404c2903400016021085019284441c0010009903900141c64040c01c00085071040e501250391144021800340900314024002d6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 368633929 1250 368632679 368632697
    0x10200610091a1302070b090307020f01050c0d1b050609010c0e0402070b13032604030314010501020a1b0b0c1f0b09010603090501140c1812100f020405270f07 69
    0x3460b12a03440003804402c6034005081017010744071129030f03510035a0000781d2a04000380c03ea0940c1000180000c0f0028282040d030b03e85983c0c20011170780c90180c21424002c00245c45c14034001c60790001300001c00c075500300003103c0d81800c003801450700800e02280194042003002d988500c2d282814003e40310322a07000ba041c2c0580c1e0b940c4440131002c1e098200310171410000c140508000500d100803407042d000c0840c184418140c41c140c907000c0c040340c42e004c509460002c48540100f01c1c2c0d1b030f40042e4039014694801501103c5420100100103406d44507001706007200c4001c500180d46100014000000700d8130107a032600381c0e200380b4500c40101d803102072005170802c0d02c4030010300681d40250480e5500c544036a000180d0944425204030b041e6a081c2c4000c0304601c0005007082c1a80800100204d000008a80100e55850b543c2c07030786d81e40c500c0481060312609440d40f448115003a51036050350f00600024140c034508216208a2400c0d200c0c04c0d812900c3c2c441a00740121340b070500520346440c440c1245807200c480f6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 368635179 1250 368633929 368633981
    0xc08060307060503060f0621010b1201090b0d141f0603030f180803120415050c1c0204030204050106020d02100209010906120b0a030818041a1020061009 67
    0x1290b10040c800e43c0c204218400c0d408250319481f00408031240400c244000708500c3d0041014840c03011f9000e100c96200c240000d01024070340483c442c0c1120007100700090940483e030041703065811004e0380540380015549036a41d110300042001860b100c0c84a0004c40321002e802c6000084804a000c040d001031000004085481d000340740402d00180c4410050070044c0c0d07106549031840d4003000d90380c0041d1010106020402c2404580541d40c6030f80a4018040c0e071810801040c40350091401443c40da0010450700c80b4154040c0c1d0466015540280080c0210341c1c680102968816245800600510981140e290814a0340c800d6611b011016540c0002c0280f4110702101c810914400181030185d4502c1d002c019965081e0005c00154490fa407803588a011a10000311501d448044560240c0c2c201081020100203100011500c1c0c0c0e011681d14061000b02c04045890180403200b0820b01783c8014118103440100184040c4600c50000410001d552a80034090585604803105100c20142080c1003003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 368636429 1250 368635179 368635187
    0x9061d01111b0f0a050705010305070f022802030a080403050606190b030601030e030a03090203070602071d1825050a061b030212130e06040207031d0d02040c020d030c0806030706 78
    0xc0382c111242101c10703012081c01c080b4107103e410340049a42c0d03400000c04000341c4d6014000c4903170208031401d02c0c1240403d81c0c14040c1d101c00301124400042c441c04041c00e0480340c0c50303201c40701c03203290090102e40c1813140d9842d10301c070309034440d01098840d4411040014074614003c031405000320810200a000b032072038000700c032850381c001400c401d0600d0748a85804251807410009091040503e42d004201003220340140b6080c5403180d0000c40454001890030b002e80d0201100c500c10220002c800d408190741d980c03c4903115504038003520441070181b40082840011070a510745004410542d044038035030303501d82c00c000500000e8492100803070fa9886602c07440092814810318400d0007401600d88800328007030740810907804040350f900c1c452002801802030152301440107a000d44241d404624100040d203002d0240b6a954540b80440c1c030301101c00045c48d440b803144507101603030302802c20f20a4100d520b03030281d00c40c44800700d41000280707441304000c413003481000c5640c003c81024015103135050510204803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 368637679 1250 368636429 368636467
    0x2001180512090a03200418120206151c06050708010e06030714010507030e09010810150b070f15020301091a04050114010f020703080c0303010e01081b01120b0409061d0111 75
    0x96000901c805c00c0702d1550300c07036000380350701000340b4040080e1103980303131130441044440e0003510005c42d030102c410070140030130380c420508242c5011281201909800710b140c43d14007400c02e800170301c041d04080a0254164001d103005058400c160a903034000c2da1b403402416900c41c070fa48907038035044d00c250000a0aa50040004056450203441e051400b04011404591030318401e038000101a441111840f420329424070880e10340350510002c00c0325451a01c91290140d0040d128080d02d2400c208880c070007000205400035144590148055480f90f80d1480040010300500560650001c0c0151020703200385032034461a816500c01600d052400454000112419903c130282c00042d4424940c010010030a10000741003100b003071200556503581494890481e80341c0680c000e144940c40051101d0001462284400c43c4e03900c00c0c601031408a09094150001c3c2c0b0042c0841c64105162602e6103060107030170340243c40205a030300d004240c150000c5030740e40c0c2241d0258490240181c818080707000490f680c00f07491 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 368638929 1250 368637679 368637713
    0xd050f1e090406060905040b0d0506011419121104090c030303150308041e0f0b030a0f0b0415030606060c020a0b0904140702060708010617072001180512090a03 70
    0x5824080c004010a00b01c2c2c0050300181301103100c42100b0030041c07415000d000200c100640e5002c1103a00e06654056170340106000c1c8420b2528105540c40c01911040e030446e22503018441c0e6201010303030b06d4a01c4101045280d00989881110040f141124105409003000a943c804a0003006a140d80c0301100200440900100d040e6044840000803c0a05020b400604101e9040a4039007032024050a00c40c041c07a400503881c00c034107560422843d00d000d0140c940c0801180c0010402107101c2085000400c0d01f40305950344a40307001c5003500701340000c150300e04c152486804101b180c03e07110035091b039003d0841c46000703500c90007113801448800840805803801107805030000c1002c5001c0d402009a5201c02c032905001a44410108000b06502c011b22500410950429409807154040c094a6410f002000c0105105102c0011404172052107600254010400001c015100c4181141248044041010ba4152140c90008002d1403055000c50f982010014140e0b6a0185540d6450000918211507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 368640179 1250 368638929 368638987
    0x60d051b1c0c030b03101401080708030307110106050d0308060301200d02070606260d051c0c090f0b0a08010503060105030a12020313030c080f0d1d0f030a03110d050f 73
    0x150002d9850402040200c6c00702c0d410082417608032104505400754059001d00c40c254000e8400b08500400801282e030040c5a40c54481030300d055030204035014104035800584c00009041221003815801110b0500a000490082c800c1ca503481400462003c9a40c14000c1c43d1041084461104402c039801010742c50300c114400300f5141d41e035008101c07042c2c0c022030f825411502020040300203808240080b548051031410a00e082801181084030100c68440361401c1c00740c3d4070080c1c501d001c2d00610140f4001c00d8402d6162003516102c0c012040d15800207481c80300860000d030000300b610b01d030125949050b1400500182a00245500e81840b000c0342c201443c401e50004020002e11214848403540255000340301102044c0c1c81c000d0142d10340762400000e080541c004c00084244240c1c00314451100307a0782002440300403052480010221210b05000c907915210320300d92801099004a02e405000c141901a41c248120090064034144503005062010380340070000e0b488807080e0f107220300d00d503181440c603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 368641429 1250 368640179 368640191
    0xe0613050f01050901230712093003060e04080d0903140309160504090f0206090103021c0b01091a0304300306030b1003020303180103020702060d051b1c0c03 69
    0x9a0182110002d440204103651105d906e484208001e040a44101085a180e19158602400010095981e44400d8140c80b03840b440344006110f01c0c0c004890b9501140311084140c00c90700da140340944840d00714100e0210b4105080054400701216206200382e4002501b41d1800000c030343c115002302000e0a08405000c01210104090003100c2d000d10300c901e01103401044050303903140c8980302400c3c5540c0030030b224600381039840c000a44a038902d041c007541d051707501907242c18249006a01038081e080c15003001750b840014400c02010701d0780007012008400c2c0c07200760781c00d900c0b00c10300300810003640d000c0604a41d0404c04034000031a400c581c100713400ca58120000700c03c180307c2205521103052910103800603031911030900c140100c41c450f00b90099030100681a9841ca598003207900c0c0d000344404c484104a050301c0c84003441e4000d40454086a0740201401c0d501c10908000d1401030109032658150791102d079040950074030404c0102c1d541c2650310804e05207550007080001c1c0191505141c1a81050344400d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 368642679 1250 368641429 368641453
    0x110d08160510060b0a020a0f08160605011a030103050303070e03070b070501050a050601050a0f081905090a05101404060506190602010b0924151207030b0907030e061305 74
    0x1404200e0380c5100d48090300b0480103800d6104207451050300903a420754000c010b001101c5400040146506602944e0640e1200c4181086900e60007454410b8083c3c11990200e46c0400c280fa80c0918180c40480040a02c0e056013042d0b0004280424000105140e20030004941410701808034055000001004c07240096142c45030008190818141210300769190b40a001511a03240910b5506c55400c1ca40719041400ea000020300340c0003000b0700e071000d00454102280c1c003401c1000c2508821452018280854140a40000d0340c410403200f0554040c0240c0c4900a1084c00c18001c290070304c1204031181d245603c4d65211040140806004c0315807103000600e24810202e00d1f0f65031030b070040000380c00028880c9070b10303400c0c014280e100800560681c1d400c48200c0c01c14441d1040c0b1a64010000d4603802d0340070294060814442c464040d0b206030548080d41001466a459001640301c82020303500c21806480c0c2580650035a10200710071056070300428000b0303901c098070780c4d0003194882c022811100d100030300d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 368643929 1250 368642679 368642707
    0x1081f0302060f0703022401090c1413031203200d02071209140105120406020319090813090b031b030c061204021005031e1306140f01090603110d08 65
    0x45414036980d00c001151002c24186c051003011129012060042181e44210414042042d014020040165990321142142d14440c4601d40e24004109080c00d54803600c03204000c20350940c0c0d00c400c90302c0050003038810001078440e010740c07016622556890813480240d035800700d40b21340000700c501c9180d0b542407281102041080c603030049640c0180c4c0fa0b000031541050310a03001a0f0310514410b042c003004000010100b403640d002c031640103401120058807511901308c8a0503164804000c41542c03401c04c910042030040e1003004121111003560486c0c8459503e207040404c0d00c2600f001d040d03140c3c028214604070703106030850300d0196800050a907082e460105d00060616002090b100c00300d64841c0c020841141810300c00c41540543c2400e006096103003900640140c03900c06035103000000d4001001c03825002400c0000c150150380101c0074010384801440c0c035040d0503800c40c0c02c0d082c0014080c000050844046c8143c0042d00d070096800e40400011b08244684004c0c420021140c1001c20801214a00e0301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 368645179 1250 368643929 368643937
    0x6150a050921060f011703070816020a0312050a0207050d022404050a03050303060f01050f160503040e0118050a020a0f030b0609040509100c050901091412030406120e070501081f030206 81
    0x280108008650500003840000440803140c006c066108009440220b117811083d12038131a01100d54507940c000f14804100c0e03000079035100a001b0f44404441940880c5c100002c1e01031402243d01720b64200395036608004406400001c0039400a10b04a112941c05090107460800f442c080c00c081c904e4156960040303240c07000300b540241d49070342010051180340d24020b41703c0c8000f140b00b4601103007001d000c10000145403041c0f06201c000c022098a08100300304041c41960300410780e038600d40c00341d907945440c40b10a501c1d1400400c803584d482e010010321581e81c0f038400d40c1d60051203980c3c2d03ca48020788903025401010300c1000a031344490144221203069461b801a82d2184054201800550080a0304101507a9680c5120401d0240511107441e40340da1010305d41003115542d281040c004815500807607075120a5118422450000150103d2040c0d0032840d440c80f40800802c0c10810548040d4000340c6030f03039690161900082c510804649108e40c0080c04026820f0940401c00b641d0340c1e83d0340001e5039684 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 368646429 1250 368645179 368645191
    0x90402010807050a210c0201050f061819021b010e07030b22020a080127080a050906130e100902040e011a0409020301030f020f19030b070c060e0606150a05092106 71
    0x180f01c1b0400380b000c550a000c1c081d08850b500d55003034400d09003800000e031102548a4070342c51202000740000e0802d03500e5000386c510140e06613011075564005d5400c0c2030460b404621003500541c00d0501c1c5044c44d079000240030f41100c0c0c0040b4000e0f46a01d4030f0622510b0320101c2c1d4501c841e07031490541c900000d41d4070000d0302c10040502d44000140f54161032010420b010380c0c00158900c5400c0c000160300070030605000c0ba4044055860140e685503a01800a1240e00483c0215034055035046408514440b51000960040511020030004075a80e003264605a11442c00b41404003084a00108921035008120301c003500410310001e0300b4582c44a040034101d030400d07441550000c01c0c1e40c40d20340c2507082550000c00502402d490f4940940403540c1c0c24540d03c00c0c5440001d101038010700c0090742d220711078060016031560000090040c032801640d405d640d141e0540d0101d11650045190308074a800260441d00c440300c580c0c4400781440074410400a500f482c0c0710900c1b08610603550032020016061103e0340c4516 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 368647679 1250 368646429 368646431
    0x3030b0414090a050c150901120609150f0816050409110607080a1e17060a0b0a031d01020702010804080c0a060203161e05070609060b0d0f050c090402010807050a21 72
    0x1001d0b41c00c1180c90030380c000100d1402041821b04004060306000201d6a00c00d03000c0c2032646008000000c40c0c0c00821003688000c81c8246030100a01560443d000c0c00400ca40301001800101340c0c8403500251591401c43e054052614140e0701005141000d0300b03c264101e0142c40b0300b103016031201e0040343c0250720185044030b00c080000341c029000742d00090004281e40710070744040c00c80c050b100e101821070b4a64407840103140c8110f20004850f5514000c13008081c00305c5e6005a40c49a01000c405400390005e050301d908002010240312186c0c000520a40e041642c05946200c101e40f42c9446074400360344040c0310038030365001b60107128006c620203000650042d45098085622903d210400038050144c04404184600000ca03070107400782d070301000350380000d074010b00c0004601c02903152400050041881140e000819403029000b8030000310001d028050107101614501e400344020050f0000301141d0090102c0c15075000300f13516921030b901800b5100740600b024013045081902c1c0b6a5030030000c40c200e511207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 368648929 1250 368647679 368647693
    0x122806020d0e100c08010b0a030b1f03020c060112050a0b090c030102160210020a0309090b01200c18071b0303020c07030506011d0f07112119021903030b041409 70
    0x1c400144220405984c541c98480c940c0e504210121149200e0001d247c41016140c84001045940e0060700000f181c40428bd0b1182d602803014005e8040e4005130401c00550140c60000688040070100040000790b00c00094501c4a05540c1d81c01c40705d007030242c40c8421500c1808848911a2800d00c0100200070039238000110b030000c64410400742c10004e800c50403c5401c00c401800029410ad00e000c810703a0000030002ca0707050306c49e0b80100c074a11032201182402c0105007141d0442000301241000c00d00e24269440a180008001e80184460301540e070100001e0603803804c00c043d40b00d400b03c05040390b8401d1901500d0040c20004c02481c040094000340c807e6040480104040d254041c450204401c00340080c0e0040d21b0421240c100008008082c0c07414042a18024174089405100b55420500501c04040303242031040d55000721034000b01c0c0728503500712202d050880384600000d000b9031000c521041c088603809440d50110050401c0e02c402c00d401c031b030f12400d00c1c0204200c541091032144010710014100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 368650179 1250 368648929 368648953
    0x18020405040606021515030309040501181515080402010509060a200a0f11061314031006050616061e0203040b0121060e120304080702122806020d0e 65
    0x1c56442d68815000e540c405600f40b4004a00c590249500040c403c801c1c060031103c50b004030341144140c201142d4007901d0500081110803001203529401d4502240401204900744c2d16954000241d000b140c550074100541103440300e02c01c80d406a406441807510500f084940300c085186904685040000b0807030316072441c0c1c507001a400e01c2c44076031050301000317089a100c192a03900e10519203920141042c4240e40b90000540c9076901215a18815010514009546c0b2512604048901c1808030701c64040c40e2411380c0c0b158454000d40d026075400802c2c00d890075902000100b1039410503c0c0c2151225218036000800e1000048c0102c0414842c001c056a00e1030945040b10741c0b000141c10504070b05030388080b041030b90080b06042080303003540600005090521084140e1070400c40b08003071000104000300b04002c0100a01c064941144245c600c1000c0003541c81d6280e85a2138080303a50741500380403201d040160070ba203240d0180d0944c0180001440e08501c540d0700c1c03080c2c40c02c4694545541d4026554010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 368651429 1250 368650179 368650181
    0x7080703030c18030204020c24090f06040c050d17031e0f041e11030706121401050105031b130f050306010e160e1f030507032706151802040504 63
    0x700c0c0c4515041c80caa0110500d0b000181d82c3c2400046c2c015540441d00d44404042003200388000c01d100c080140b030141458800c208291002c5800a03c07500030b800c0900c4441d0000034029010741d46c0903290340da085043c43d00303014003906196415110300283e054104840c0030b1303500086010746603441500141250110b4030000d040805050785020500c504100000304103010b01c51001c4044030020034100111a0401520200d00010707141d40c1401000c6001410b107030080e000403c0342440304001d0200c0e1a022000d148141001d102d000d001c9041000003400e510b00c0c041c0380401040500c49100d04190901600c10201d0b0010b8000300088840c0c0501400240340400c050f074010070003260050320501c0e20710200c211541c0070300c07076190030320142c20545182562a1a0003041d04a041d0354242e00020f1510402401340c2400c1d0b03000741c00309203040c0001ea9000d810284030224844074060441a2050781c0e5a00f00003089034043e242c3e0704441803030001c60700c518090801090444581d07405609c41d804d044c1080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 368652679 1250 368651429 368651441
    0x136030308160c080405100903080c060402040f051006050310030b15040e0703111e0409030206040606080f0a0f0311100f0b0a0e0f0702120a0908060105010809030d0c12020708070303 80
    0x1081c0281d0110f02000a40d960003110140c076402c0d1150404404260416255002130f41c20051071024007040404c8948000906c0e103100f58002c80f410b101c03038081c0074000e40403500141c0f0a408007a107900c0d01403021a000d0300040d030300041c03490611000190b4a0b00c2d80604218291804882e070f007500c1c200d48026103024042c0242401508000c1c0c04264a07540d03402c040212081c502a00529a002c21100440c01282c5081e0404030003500605c8014883d02e0000c0d200c500880e030495500c0d140c0034002c190803000089070165890000020081d1000c0ea0301c500b4107401d2884012801c003c0c40c00c0c450800102c0c14800842c00c1101014003240c10382010032204185c90114030428081d2010103006c1054901e8045101d411801d614000304090b1200381c0f08a05084954141c0500980300088070001b10f40d003c00341d10b00700c03681f5005030303045a40c030748004540104050781c2a03242544188100d0070b00e280701e640400e43e5115541080807503901c2414042041c1d8026031410348903643d0100e040030905030580507034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 368653929 1250 368652679 368652721
    0x21314090f120a030c12050403051e04050315090a1e0606090507090909020d06020f040302040506030102030405060f1302030d110d140a0c0c090e030702010f0e0136030308 75
    0x1d0300b80304001c00c0007495203001c0d0700c84500070103032683c40008030a0700405001e54061049142404149002e09000d0880c4c1c0c81114500424014002646070728035155068074142c0c0c0009024220181ca0007035030070408030f40501020880d028900c1c000b000120003080a02c50350b00b411510201d000e01505062003120701f203030301002a003170520042111466100d041d00060714640301000403c0c0c0390b280082507682240303800040660744006021807030300c0020405401103d1081b40e0074015603079403030141801c0c0d000647c0c00919917400302012555404000782c0301540004401c0004540100300d80000703103005400002100458081c00650b50444c006121075400c00d80c45007040025620b81050701c03500c40c07084004190800240d010594200f01e445c00109004000303104040c42804e511814881e00c82e80b03c04005c0b4040b07a8807031000000c0318010038441c4001c690507142d4100e070008a03e0b080c008820440c03407941111011a00c0d2880340b0020502000c0514003a83d1400000c0c0303011000e9604254035040d80d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 368655179 1250 368653929 368653933
    0x201209150103030e0105210f01051203040b0a050c10050a09060b0d02030601031506171509061003080d0f05040507080f12031603060b04030b151813021314090f 70
    0x500c0882d8204130954240c40342845c0c00380d661b01003410760348988036041d82c0b441012005841400404000085041d0590300202d543da441d409a90001c1640d9114501c12001d050500f800b0b25640d0314011070207005c80320b4030300c1d0039140d0500e01120413008882007101c2d20f49400c1ea5a100034418070400d07204110218505650002004a0540019907605814070005118903021025403503d501181c00c40310040c000a4250f0b03a42c5100c81c1302054a800b00c1e24001c690390000703080045c42c0749074002095401950034400c0700d024503045450380300503940070202c0e448546071100c00c508d040303015a2007001d00c40c6000703001800c0f001e0304001d41c85013442070304034007907200e503000701d0002c0d030500500c4040f01c1e000041c0300c41c2c0386000307070641400303502a20469021004902010600000303010107500030750703c504c114003010020301d801d032000c110141000d80c6422507240030940c00a544c860803a900c80480c940000d01070505040303103a00306000c1d940b80300c0107800448000c03c14804038241c104070f10403044441e500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 368656429 1250 368655179 368655181
    0xd060b09062208010c08040219050d1103010b090711160503030f0c070512070906090203010b09100905061611090403020a1205120123010311030a20120915 68
    0x101d1a001c0c806000304180c4604828100020404070158010a0190002d0003c2c40440381c020b40745d58022902030b40234000034404441e441c500515038100392800201015500b08081d210040e1141e020411150150740c0c40358019481d54032101c840384a210b1036918111010707050701145c3e0600d2107440805501460410080c04540d60200c15500e0018903138040a0b01c4403081440e0130b1800000d64403032a0801c0c40c041141071381020101d022410f807502d6440500519580381c49000807840300b4450984481e4040c0006d00b00391422180000c2250b4192504594a68940c0c00003001da070303c0f1089081401021070700310010440941409030210030202c0301d01e0b126240988011391107000450008050811405881c03c04c0d5000d0400d0b10509550b501c201760303a5607100d0504081403614a4807000d00315020046085c140e42c0b0a01600940701c01c840d07a144e0443d152900303900b002d041c004c08402011000500d8002c2085802d04c003801180d80c00030032840381d5081c00400361303041c03016507012400e1000542e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 368657679 1250 368656429 368656447
    0x14010f110c060904022512020d021504061e06140109051f0c05030a170f063f030403020405010f1202150d1d370c030c030302030d060b 59
    0x85400d10041c1010703601d00f65205030305030004000384244605c441020b80400110003800640b0509103140d203200318503000345003c0700c040a070381e100c00b44c0b020300700168003018107107603110105445035412901c06d09020510848004000b15031003c001040900e141d6101820002c1020b440c404c1d806000d03007030030a00030701400e00c404207091500038020b114103030390741342061941140300b00c80b40340410343c009003609d45a0341800710040010070110401c901030039184020030600e00326010f000740a04001800007921740440c8010442040201c007460803004280c002801010040410316030b2000d000c41c01440d52181140f042004171403060700060050703681000184419084030741c0000c81d8a8048410200c00d1119402040303ca1040c11102e4030b1031424404030b00c40e00121058122266440d40c025078568400b0003a4554110f081d03d801340a42c03143e000420b030300306603001e040c05520a005d50210300e0f146447c4e032640411201c00b83e10031070050b0700010f6001505100c0d4450320000c0e008104100345005004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 368658929 1250 368657679 368657683
    0xb1f03150602100c02030f0a0c0c050405010e13031803051606030b03120d020f0408030307090b030709090e03040302030609160902040506030a230106200303071e020703050714010f11 80
    0x4080304444403561000c240801324000c1081d80d44050380d03003512666072440004000c1008080c81401c07541d003542c0307040c00b00d81840d150040c01e0680304480314100c40c039a102040094800c00d004419803c0c4910a1b5807802c901c224185190090340c003842c01400c02d136900c04a080165962548007108143c6080e82c040708035030300840d082081250300084c50341c441004c02d030024001c4c41050803028003010001000075400d440403001d507200f1501602d8440d4101c0d82e84415042c10f1004880520010307610960134410f500555205015034010320003101d04094803075000c68030b070501c190781c10203480d40440880c95070900341007003400140000398001d6051514100c00701d079a41c08043e00c1c0141c095121050300501440c003600080e850f6404244010b440c0d692420058400c0388a5221045003101d1507042140c2d001c40081101d004412070399480402c2c010030150040d859080045141c2140965000040031a8040000c48040d1141e000c1c0c0c5800000c0030710000d000050316146402c144404518494a80c60b00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 368660179 1250 368658929 368658943
    0x10140a06030c0b0d020f0301180509070f0b0a2003070c06020706051c2408012004090507050c01090b0601172403010b030f1b030307050a12030b1f03150602 68
    0x41c0d100f40c1e6243c10756415150060301078001203030083c0c10007000000f42c0c8460700b810780e1441c8649081c01c1210780c90f1030030b2068803440c040c080c1b0710706400301241c02c100c1032400a009101c20340c860b1801031009101c101e081001980054800c855940c8085003440901140e1810000103003114001000c12070300c0c2c90009041170140c02d000c100680e206022000d03a0110603000140c0038880d800191500c187e00b402125044110350044c181d4641c82c046501c1901c88018400b1035614805214180c2130510780900700c80a800700518140421200f888242c66203e000d020b5412036900c80e4605500f235203400e60004080c2e45202c100c2140710b010303090500c100030004084445c14500d00103c40d0401c43e1894010902401d40c041d50542c241c4101d40801540c1d50001c2030f06504100c1d4040c41951804003501050b99a000f0b18502600980009207280000781d4a56039800b0140360718140407079072480d02c000150441e4024070503921000ca0f45620030805590611900584007405844000c8060904c00000e6075050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 368661429 1250 368660179 368660189
    0x510050307470703031406010201180f03020102040b030c030403030c03022505120a02060105031b1503070c1e060b0303040f062d0c050c030307080906091210140a06030c 74
    0x36010080440c4030000302d2a40e02c107502c071100d119550303000c80c603004000b0b00885980401c84115400843c1c0c040d071040c01608001c940c0802d5800b41c40310f075a2200000f21490110071019503608000c0010720a1602c00514810800d041c002926842c09040180544104900110405104120120484906131014182900840d9a80ca401c2e041c80c80c200e442c10740d0198408603041c0c4003184002c0031540c0041c419040c0e500507000c4d40c15110b40c070b40e24100d2441b402034515a0080440d00c90328104c02903200a1a4001d00d6403501c1204209d140d1a0101c000e4071030321445100031004050030060041600940c03141d004140e0040d450b00d0b2500b0010007600c07007107000c1e8804204d240c00364412003940e0084520750a00c500404102002e030030344000b40c403650030048101c4a038000c0d05102480c525000c020f4030f80c03054208030100c1c50640490100803040e40032041e20341e4403280c5108050140c0000300700500711030314031203000a0005031041c885000001c00401c001c1009007846418030018403000103205c2100c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 368662679 1250 368661429 368661509
    0x30d050a0203042001090918020109050d030203220909110102060f06030d0c020301020d14100614030a1d0105010b031009110409181709010801060503150f0f03010510050307 76
    0x11340e650040b644411980c1c41000064240114070720034170000301c40c44601500c04d8891000280e0b40c0c07400e20050509103d4090007580052004d004248101c00301c40c2101510000a10025070312940c0d04801c4a81006040d0f03005039408c6200803881d40c040094a41048451524039401c0c40c6c903500081c0d03145007655001c0300300002d900f074030411500c0c00d405450b2202c040d210184401c50f03409086203185542110a02200100a800081d00e180101c031030300e5210300c000301076511310f582d610074403005003590b42c121450302003002c41441d540300b400b031007464080d003c0100540e030740b400c10506900d028080c68009101207440c0030701d12104d03001400c04880407110018000700e901c4c200c0d2200704400400c1040081c2c2610000c6c4440b020005480b03000309001c110076241e0556076620384104a07140d02045840952503002d202181045191404103400901381c01000f1454901411012030300755081076851300007203070ba00c440606c81071a00780300c8040502001c001001c0801e840450f901500b01911034445540b07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 368663929 1250 368662679 368662733
    0x1030209060d0f02070614070203070b06210d09091a0405131704060f080403020a0f050f070602070f141003022101031b060906020304030b090c040e030d050a020304 72
    0x561075403002d0758021004424100103040e15070b428a4080e51015004480691910407031005051100490f2406100035600450074840c15607120030040134098403182c0c0c022000903891154215018103903001010900152908440000c0007401034203140d0030401d08203051211444407600a030030b50341d8104d44110350110315502d50407206040031500710700c081c3c0b2080038180300340c2d2030911090040007103d902c2c1c1d840c50b02490200601b03e4503800c094800600603044400d261010a2180c50881001405a41551820002050b44501d0101294011005a0449035040040f402c00c0c000b25801402000b40e0f40d8051410f02000504030305032090480281540030801005a0142d0000c1c242403500100b59070b44556100e0a0014607e00740040700340e007883d00d0036000300e003880c132400a44080360003c0c1c00550815045a8440d00362000c001c1ca4800c5c14840c07203107006483e40c2c441c0540b02c403400b5290091656083c00c59000c0007918070040400c00d00301e0040049c000050380c2c16110303203144204401c8600c12 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 368665179 1250 368663929 368663947
    0x60105041d0a0204030813060f0513061101110307030617060c090613050d0f1407030c0b0c010b0418020915030c040b0f030624040603020915012006070905031902010302 74
    0x240110740002d1b0003100007103904180824100d00c41001c0c0e80d11034481c11030f441d007084401c03203041c0b00c0e4640d05405a02032600802c0240d001e04204402c4840340d00021941c440384001c00c103190b03041103800c00d00003501d4580800140e0394a6800d50380100c10703140580020720b002c2ca0080450700c02d42200714003414001a00003070007030040030305001506006144128010550030002004d0782e40c0b10095900b01c009960440d040c54000500e1030407203601c40b44425005c2c0c41c04250303100395000340508030115501c0301e80748004d0795541e200e1500040130408281d1000e0846005000101d00000d0010b1203020700b6003031053341e0303603400038446402c40c1d01120040341e81d0400c1c4000c1008106a001c40903014407a12052001e40721032440170502504c1e022881721421180401000306681d0346210184d04030380341c1400f02d444151610845240d080c0d06040004012940b100c80807401003601c0d450600f9900004284480c041e8070040b1880140000c40040c00c0f10360048451714010b1207510b80003410305a00040e5818 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 368666429 1250 368665179 368665181
    0x40e07090b0403060b041118060918090d020c060c061b0d0c0e0f01030212130606030b010914010e090d0c170c0106080115030312051e1e060105041d0a 66
    0x20240c507410900320344943e0740780341600240028404040c0b0540c2404603d0011440c072800703551412403415030b1003c0f0200524107104141c4e00c107180d810780003401004c4842e095811124000e0040300c48c880200185d295902009060201111845118070b40c00c2120f07503403a500c001521030300131901410b500c2c01804080e1083c0b0b960301c40c0d035002c0003100741130286100a071508490082d46d442d00507540c1c03800804035000110202d01c62028214088040080480e9042c8041070882c0c803420f109080028406850b80c03140d45500c40f00f40d20035808662950700020201d96440c00050040090a4054a40e0b0601114503611800750b60115030400c260500e003034060055202005201e07400e24500b841c0d4030500e40e003081e800fa00c0e5900034103a0315030801c40071402f0345118100030011240c02d61344016030703421b060440c0000340070064440302000c0d0845020304000c0160802c0c40f806148821010889681c18028540f20484001c0c4290f0501c4401d203c2004030803c0f064800d2020610700b5001070040c0d0b03424203404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 368667679 1250 368666429 368666447
    0x3020a0c0f030c11150a180905040c17061506090d0215040806090c0a18110a090e13080d180c0e0f0112050304150210050901021902060606040e07 64
    0x54004601a1850000e042d04000010740b9035001d12190301e40845a0300134403105180c404181c03650158100455402e443c0b01c1d204071106603100114070a8416036a08d108029650103580c140c50009003104100234044003084911211a9084003a15107450714590749060418800f40f105d01503000001d001c061a968070340c0c000d980aa00400b81c100c0317110040114951340d00503029003030300e510412000c501502000200c0c1c03840c2c41b50061804202c0d504090001c074180d00b518040a40c3c181e01c03054444c0d10f04108201801d03001080d5074821284a1810303103429440380d006481005035005000c0444003140c01042103400510200001040241c00c44078585070200e01071801a0080307004e900007040c1141c3c400c6801c1d00a01c204600c1c1101a600c3d0b408802d500a41002c0040c2203a0003000200010324141c1104110a00c190054030512140210943e00307a9004450fa868280d5001600000120540030902c11030019480104050324064021614920880c010b0b4010030501074001801103105840b40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 368668929 1250 368667679 368667683
    0xd08060d06050c03060423070e0a0902030c0a030606030e06180712110f1009030321020a1205070513120c05100309051b01081902220504060e060d0303020a0c 69
    0x400541c9054105011144c0003516140d10550030003207100070000068010700701020f1005044982c0d51900325060b1241c1c102d1411140d0410311403040041c0a511502c0614855061b0212051352500c4d440d5004080300c0301d83c0c0003403060510b0003c840f0380380307240060700540c0507080d6444c000002ca09031100b01d00e00900c0b41d00c40013000604961110401c11010800700007503d090700c00020014001e010000d40350040c1c554100004c00c107440401c08030344141401041c2c00d40042d080c40b452000400c2030800d82c0d200e0744540f008a04164014803400d0391500c01c41d0361003207040c0307000d0f41008500b01c40c501e04002d40b849290341c0b207070f1049400400c0c841c1d0904080c005200c0100911103000c5480301c00342c0600904807050741d20340107001d0002e101c00c0000301028124001652580c0c110768505644515119111a0600c040380c0c0c280074008030340108400c0807405010901006c50414940400c020035160641c02100c1902071039030910850344c41f521030020440c1ea05040c056100c0252100c115020040a030340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 368670179 1250 368668929 368668931
    0x40212030c01021c0212070f090e010b070506090c1e040609020301030c0305210f0c0c030f0304140f01050910051303060504030809010504050d110a0b0f010e010f05030d08060d06 78
    0x1440449030158000c0180026103803681302d0100011224000324007426100c1c4864201d10400202058880d2030012080d060a0070482c1d1030355100c421102039904260072070a6040000500340007408410000140e004030711100030110b141c8074501044003120b840a80300040760b06202c0c014121754580e001030b80940107884045469603980d09089507041c21900c001e4031140610300b14540280d050041c0d01c4405c00281840a1502c0075807051111981d01007008035415000342000f042c03081d03500f48800d5201c4501600115207450800b000346100118414443e4810640c036007070602141d0b04030b4162030382290112000f02107a03034011016185480b8001d24148150581100030041200c030b9803045000d2030003036840a555580750f101c41d6089820540d0b015104e0703407240c024038a132584140b80d1001402c0345a01907072070208951741c400011720400d131a84403100d1400c10060041040c80e501d0b044c0100310714a80c0700c070031a10701800b00b6101d81a0000f64020001c05100280d40707920399050007814a070f40050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 368671429 1250 368670179 368670187
    0x22119061d0601061202030103080f0c030712020f070509040b0a0e07120c0306142403031c050f09160603021b0a060504020a050f06030f0403030e06010603091203060305031204021203 80
    0x30703240751521024001c260201e0240b040b491103092031842070724140e9a11016041c039003900c40000300c060b6000007090760664801084644c0010384e400c3c0090032040c400342c00519204290b00c40b040d0600c0041d400c41d07409034410302c08200104001c160f0041d086040928000758013085001075a0820b409500070070b410f00506000341b420000d04081e0760003140d005510070000c0d9410b8a03400341002000303035140140b05075481502e0302d1040b488c5c0071100b40c040c00202100d250102811403540030300b0300c0b07410464210b950b80c0100055900b04401d420f9010041e5400343c62006140e107001c200c044c0b40e500862042680c00b1510114180116004c01c5100380c4403421940c060341c0b1458040090b03c0201d508a00550303240d03000042c1824080c05440300c083c8003c110324103598038800c1142212000130070503400c0503121844004207000c01d2011902a145690340414407051600b0484070444100003000101841c01c541040400c0b408020b88064413aa504415031588072070001a03003d05008100e2601404005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 368672679 1250 368671429 368671481
    0x20f0907080f070f05090112020405030a0b04120507080703030c023a0906050a050c0109240501050f010f03090c03050d18080c010f050a1209080702211906 68
    0x1081548640546090040d00359100402103c02602c009804c1011030814004d0382034540c012003c035015160074440050905a8400000c1c0c0341005655040d641d2a004070240006e106001c6c41a03034a840302c41c14080c0ca425070a43d9102114441c010000e4101039641040c0001c440c401d110300d40b40440d01090b20306070810282c20b03c0d000403c0b200c1460042442c031141715400b06001d0340c003110403903140307488042c02c101d05038400b82d4090380081c500041a550300d140d40c50004004080b901402c0d410040064440f0280c4000c100442e041038008038800c154220702055140c0e0b04c400060003050761482c0208450700c092034180f0125a4541000300300b4010440413052556100d956583d07524811904a1080e40d5580001522801c0016419001400c1c54030000062805000141583d000700e16042100358000308174107048034182c00e01111100030000d4000b05529080c4c80f146403103203020f41b00320801e000c503984d0b46540391584080904030b00c0001d801d00c4240129640500c510b090041101c1441030418 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 368673929 1250 368672679 368672687
    0x909010f0c0806091302011e03060b030106050406020f07050915040b0907110c061309050612010e0307120e030c1201020c060f061005030f0f04290117011116020f0907 73
    0xf01c40103400745000f100017a00c8400710340110502143c068586000078074207070051240d42e1020007410811300d40c4440c0d00060652500c00118000d01082d42c0b4281c941e0b052000c02400c000101031085025803003801c0900c580d54600c400503030891041c10a0001c42e8000c00086806000c21710341e01c40c0c3c070405203410012480d030070030b62280308040c001041d01c62040004003000403d0040000710b10b174a07050002c041c8082c54042d40071a0300440000c000e0783d20f01e03c81c0101d8a0966001070642e00c8260008500c400410818001c003021502c00c500b801d1250b40892008a41e4603182ea19189220b81030702076124982d480294121001e1500700b0081d03549904c6c001d024511041e030150b40c4203004e110341c0d2001050081c0718609490044a13001d03034842c02a00c9000b108484500007602c10b4a4201c0342c00891909038400314582c1544916a02e0056099850003620500c110516221100164106503030446154000c2080320422000d21103004000c00c0c150020405402034103201d65040705150040c03007241a00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 368675179 1250 368673929 368673931
    0x141f090506281e02150a09060b211005071205061504080106050a0b0f030112030e101707020318150403060504050a0506130210113405030c09060909010f0c08 69
    0x980c600f07403407014140c1d8800c036518450f0104104490780500b01090640036680c00134180c0a00581011680d180303d0b02c001821010035090300ca0754854417a240e0564a0700500a41a0f10080303840d04001900e403107079002e00f2140d5070202420300e4940c0d4a0004405640304001c181120001c04900ca855a46807044d41c1d000705024021140300d15020300c000aa1700c0034501c202c40d90140c45c510b80c0c03070460f4032b88030780002e00d00c600e40401c605211007184010b00f140c0303030307201071120185456444443c180205107100c0f07a4800050004001c40d0420000042c482c4640e491400119406541c010304405224081042a00560b00001c24441c20703c0140010b0040028113540c3c1103014900360b031340030b4648071516540f0319403c41000390040c650708810032085000d82c1e950300810310014260303550b03078014100002c00610b4103141c0383c2c641e0b44040b00001540f03004003800c40141006070000c00905800300e0018001c140300030702c030038440c0c10740c1c0e40090b40801d020342203c1140b850742c540600074080b000c0c0b806828410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 368676429 1250 368675179 368675207
    0x2030901020702130902150a111606030b030d0228060912080708060f0906030f010905071409010b040b07051906050105010e06030403170a1401141f09050628 69
    0x411214100e500303131092041d104000d50003002000c07020104011005207821200010082c230040c42c1c1003c0a1010921a020781c0036081c004030144282041000340482d805444d64900035404100300d0715515800007003899228a40c2ca0803401d0024443c0b95004c0901c000c00c0000708102d00f4083e048003000f80031404d01c0088881c4d034a48071065a1040b000301c41c608806c07218980e000b2070020706001d090420343c55481d04000050103848000326000c0f446030075542804011295684840010851700403802c0b401c008000c401c843d810019450008491105c1c0118020703800c0340d850000d080400c210013000b802417048822061040324050324103040c03008042c24403809001c41d1100180e80c440d8074000f0100e9100341e6141c2c031000b844841e030b0010300c0ea0080c001048402041ea441c11404400d00508a41074001e0089403011003981c810281800815408514404c10b017800e990320302c0c6102a00f02c2c5210055034000e840a685404000346403480c86550003800c2c010685016207040c00c155031080540c00c0501d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 368677679 1250 368676429 368676439
    0x8040e09070e0408040902030615130905070c0b0103060e030c060a1e020a0f0c03110703061a0301020306030a1b03060203070503091506130e010f06060c05010f140f071202030901020702 81
    0x10307a1141d80c04603440040b0b43c000c020038030412051240c1801075024582004014109890388c54018440110541c41442441d00e1440d260208000c4020b59004041c2d000384c0fa481d02100d484003e9460001c104810b002c010701c8141c8500304041e02c9041002079400080c100c60403a44103040c54914400104408085004003800b84101c00e0380e41d0303085000322050820141d45035003c810421408590340303102d24034110300300038043d0550b1101c990104002e1010b0b6001c0c0c5800920040181d08001d040c8a110001e2030103030740140200011982d0100d8514103058003c010802686842680d4110050407504001c0c0260f01c04401d0046ca1a84200911720440c0c803602211030140c45200d2903117068104032042544880e1000c07010710307890041d07008482207440302b80022030440c400d47d100b074090380e40680104000074403051050050003800d0058580c030755102e207010000c0100700c40c159541413400600e5080e4281c120f10205100e544100401c070039101e48101c00315144d080100041e40030798851710042e80b0074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 368678929 1250 368677679 368677693
    0x210705060f040201050703110708030c0d03360302010209030a1a0901090803150604050a0b0921100e0a0605090c0102010f0e030904180f060207021c020f06130308040e09 74
    0x9680800075010719016150a810040c03184d0b401c41d40b81c940410069850b01401030001054042040980100c0a448000c1d20750f0b408503d400070111140012100d0b1944036009000e1003002c1082501c4402024842c07150070400794a003426800b80c0702d4000300715050300c18449050705202c480070740c0c00b0000c21144076010050315580801400e0f1001008060300941c0c042003c00d1040c4003d42c110107070110041c088505040c1e840b00041c0083c20b6641c4154645000060384c80d805103032540619210740300c01e8040e034561006c0b015005540f102d13007181d5402901d070380319100c01b100507041051024003944901c040c422840c0c0a50b0f456265003c5d2100e03180590b00384031600101000300d00174150850341e03400c0118203000369441000050161041840c00001d5030030604008a0406054000310700d000e0000582d0710391561050085e40c0300700d1301000382410404801c44c030043c0c3e01d02a444031460741c1140c542da154030382c9280c02100c0010642c80184044030004002486281880001d44030f41c0e01c6105441c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 368680179 1250 368678929 368678941
    0x3050606030f061e04050405070f080a030f030b010c02030f0714010e030c090a0905100605130908120a1107150f05010608010306050a110714062a030921070506 70
    0x20301e0109660700c21003840d290001404030b0801a1402c55002d07016403058403654125804030b411034000b078a003600c664009410078005038607a82c081c540209a40001060700790082d4400802003c8481007943c10182c82c1c0e42d001c05d941e80b0034410101c615400500396000b920303003034161541e80d0025224002c080260003070780440a6000d0005501c00b4803000d4090015907040c4c0c0c082042c0010010714075030085543c1d00c41400820b10400080402c508407000c0040c030103080104101e00407080850030940c060411310b011000650b03000c259142c0c02c4503200309084c0b68036290046805040c2c040f0001d240400f002c9081024800c6184682145414400c01000014007c00c42401a035100740101c00c0841c1c01781c0d00420024069a0005900000190700041c0c0c030107081041002d180c3c4040000c1d02d9072000c004420907402414001690081d4400c202d84141506c18400b644400c03040e4080e0803041600400020350203a000d20110800240b016070000b240c1600b400d0406580c0c11150060740e0902c55a000688 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 368681429 1250 368680179 368680189
    0x70201020717031e130602060f0a06140118150c0b010b04051507080c0d1e02010c02120901031107140610061403180604080d0f020f0d180b010312030506 67
    0x20441194001940c80d0001001402d03004c090858100a191481000100f50201d91443c42001410f0254080c0926081c4240303990140030004e820410110b142070030800c403c0c0200c40a001001500382844003041450041402c41c461250f40080a407103560054000603d078020a01000c05100320b81d10304091f6200c2007140f07000e0155000e010342000d8010240d9110076240c030046d2100c1c40c4600801e601c2d240803010003034101410141c10b030001c24260340b08440c0c00050f011100311041e403544000c11441460300e900135031b140a042c45008085000140600680e440790708804150300c50b00760f00b80c0c0d803540c8610b000b80a00c0e0300486064440d008a80100b80d120f1540c080c004205c1e512641e03030700d0f20300c004640c1c01c1c0b00d603a1018004101c60a031043e510741c00c024050104a20032401407070400d8031080b1040592042d1903810b02001c154510400c42c5d403160000b210180d0308011814030002550781031407140340b054400181c00150a9403118000041004107984070814510415601071186841e44c0040c08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 368682679 1250 368681429 368681459
    0x4121b02030c0103020f04080d0309030f030e120901170903070302070e04050c0915040f0504141204170106080f0d0306050a0e04021210090605041e05030706050a0b10050702010207 79
    0x3076242c0c0101c04140c910350f2294001e081c441760100c05491800d80e0300d5074418a0300115150304400700380c5600464052603004000101e81030054101403255090040c00031b611040c2800c918800320364086208106a40710f40c154807000300b016580152107081c0f810a150317484c2c01c9108101c0043c8034020012801540030341075540075661010040c038400400b403080203002000200400e8590036400c0303141c4c0301c030f60303c81c003900d118080020030004007420f041c280040b045c0c00103851059154000a082e45055200d5800c9904490101030705040c00c0d002c03c1c05680c0549416031014500b8810b0180f04042d80002188912100c00251820040f80b9600c90501110409610403e140780c0003800024001d410505020484106240c0c2550300980324a0448400c030303080d694003641c10700e9850080001700407a03688030910840d204042c580c030204203951801e61b20321682000402050300d60000c201c0d0018a81c00c00b01403440f00505140b05081151030040c0103400491050340148189000000d0b080c0f6454811 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 368683929 1250 368682679 368682683
    0x3050f03070804060507030302070605040809150f070b2a12012102060a1403071805060405060322020315070813020a141804060b1e030601060c03110604121b 69
    0x9401d1502c0d05106550613040303044291f05040d020801e100000d06144030b020300c550700c90040152a0f640c00c0e024030000c0009198880303089642000388011840d040c0069440e215030220050700c1542e07800c00c00c410503206402808105105051510454a01040142440b01e50343d0018005aa907102d214540c541860050300d81034110f05c0309041c01600305070009052081e0a0304040704200003c50711002c42c1d9100f1240d000021b070030038a064002c1000d584d651401070070229003d03800d02e0305020024000d03200c050720b244844120001c010050802c40ca04400380c003a001010f8801c40056103500307480418088943c40c0010f9203002c0000d941c2d5800c07000c02a40190060021454a070500300a508801c0d0a01e00807544861044000907200034400c0341c1c01d100300d200e000c002c00c6000c031800c2844040b0040c408418100a500300c0c00d004507441c002044c03030440d01c241c80e048490400508041d1000000e40c0f07000444c50003100100300502c40001d00c0b04103c1c41c49584da401d03000b0351410024244561201d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 368685179 1250 368683929 368683943
    0x7090e040305030408130b04050307050a180506150d020a0f020615060f160f11010f0815040e1b100e03031c0e07121104140f0a022203050f0307 63
    0xc90301191049010b1544640318001ca9403404400b074041c0c240c4103000d81d120210300303a000a802d01c25402c0c1030002c24010a4181e5540c02c5050038084081000b1820451000200e96901b001512070b41d20300490082010807400d41a90319034510042c040070350300045040f00030403801d4240d46102880011040e1140d41001041e6100c6045803082060580c413488403155408400d0020003c03800b038015951519074030130308240c0006510f501d802203104990082030b0781401025425903120a410448196000001c850005000c0036100005001024441c014903038030b1003084414030040003040050008407504503089203070031480400172074102440c1060315030944c005201114141c020403000c43d041800503c2c01080700300c010643d03185082d5030780e404a4400c2c108442140107104110480c1c1d0b01460303081d141400344d030300601064041d0b10b1000e071a112512604070001012688a6415214060341c190305075072001351402d00032542034105000c00c0e9010700940403e0f440e41d4400000b01d80406501c819 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 368686429 1250 368685179 368685181
    0xb120307060506061b070306050a0c02030304060c030f02041d16051204050c0306040b07030605060301120b04030e190509010902070b01061107050d0602040611011e0b01110d021507090e 81
    0xe12140070b01006401d89401000500c100d4031200c041c125400b201042c01001019564614207000054410191085c1a400e1500c2c081400316540402201c5e40f0541202011403503000d0414102c1c010400441c01c94030003440494041514156a45a00400c011031a84040503403a549591b03024070030142e046a001c00c0c0c04101c12411401d824490715441800781341500d540244a0001c079040400c1203038100c6a100c1007408200c42d00d5094130a500140409462003425581408005d2105a200010150981061800080c1014402d0756030042c0c0180141407d014251040d40801130303103940c0e0254034421501d20340041003041c0d0501c2030304e40b5650004d0704e618003039113011026562000c0300d00c01c00300940035030240890b0544560102c5820f0b207100745030040c1d48a2510364020700505150111600f9030b4101100d011a000d00701049001d8011a504009940418400107980310881400621014080e4030401840b00c2c0d004603c0d140804a4141401502e0303070b03034000440d0366400d2801480011300102c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 368687679 1250 368686429 368686433
    0x70b0f0a030b310608030304121205040302190819020c010f02060c0d02070c090905100b030a02030607030b0607061d01060509090a170d052404290609060403030903060b120307 77
    0x6a0161540b064200090313050784070092030303055030310454041c0c90402c42e201c940d000751a44030308020b00010150104004504050b54020f49541c0358100c1c5c8200c8490081d0141c040c0300e2140103e401900400300150300142c400c480103034980e80c000752aa03012074860001c5106807800070030340c00e1003510b689505501d0700100c080c854009400c10300f01070394041807440011411100e00e205869200d40554014002004500f4101060f24070140182c1c0c00f07900003400c07910041c0c4001412603088481e9090101d413201c610804640b0500601340c0240003141032004030f00c040d002d100d085044d0300c0f41440091203c1d544600030301204d013105030340001c8030740e000c00200c00101c3c0401ca1441000e542400c4030a1a00c5180e1190005640c41600d04100c0c0c0e0b600c428001d01c1540ca41d418005500c1310903101400f6080680103129039841000e105079084001900c10000c170f540d1110103c41d1041c20050620361100e8a1382001088091240801c4030120318100b481405441c25003001400300440000940c0b410000d030f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 368688929 1250 368687679 368687749
    0x1d07031403070c0608010305060a09030f030b040b210c0a060f050d1d03090a080606010e040e0f032805090901120c080102040b0a02060c0307021e070b0f0a030b 70
    0x80280e0400301d00080c80b12600140250044400505241d0b131504815419420240d0a000c0083c2c56001404d00d03242400000a400c10390f1000c10301030740c0c10b000600001000c0414094240c1c0c40c6020707404440500c640c0d0940268403020f41601581e441212402404142482400c42080c0035060100c3d0074011440c040c2882200205031101c072586000c154122440c001c941140c80318442c480d02a000803480d0115403c0540310340c4020300d410fa00508090a1100000e000c0c3c4601c40c0b041405152141d075489200c3d4410494800070011003003c0fa60b4130300d111041d140511141c01050703040101d202d0380c4a007a9500c10b4041c0c40841c03400a00c40000f03031b4038000e140b885100c0c4080c01100d440c82900000036000000384042d00041140085055a070515440b0081c100103000b070404902c1d072818801c4c020461350000c0e0006c8884a50410443d4002e019500117203814079a5020305803204000a1402c401903296020b05110b000380c0d281401030040d240c0800c48007a4100908841540c018114441030041d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 368690179 1250 368688929 368688953
    0xa0c082a030a06080604060207051b01080a020703050702030d170108060601050406030b01121a03070e0103080711210d20060703050c0903160609080703030e010c080405100c05011d0703 81
    0x28010000c1e00f10f0352005020306200c0100c805444481d40410a50309011042c003040170301010140440746400c0442e00003900c170b4500a004038403880e5000c0348040c01c040c0944222132000d40c004003250038003804510010103a45074014540344d0307040c7c041300009100e5000148240034020585441c1c1c201030400200302e0051401204150410984000c00720071602140314a5400880308030071241d2118048040c5854600a0b5001503070301e41004004001080c421401d482d00a613000010080c52050f0000140310300f0020002041800154030505122030000108a82060382c01e4441401c03600344c01d54010703084124008000001e8000b40c0024512a02c80d910170342d40640c0c00aa00f0307051805000c040703803414011100d0f0f00c0b0399044c280d005110a5800c200e0610040100030300600c0c0590441d130b0000d05041e00c60a00905200c40c0441e00340400c5241001e030303000b5140181000c8007900f00700300010a200751515064605520f000003100040110746041812011404010b04125140d030380c0d81500c0c01a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 368691429 1250 368690179 368690191
    0xa0b12060603041e0308040c050f130f02040b040b04140f100309051603030908010b06040b180a0b07062301080a2301060f0f06020a030c1e0203060a0c082a03 69
    0xc0011140740d41c0c8004542d602004ea010340e4a0048605d420b190944842070f03150000e91140840f452100c0301542c0e1a10b00380c001088560000c11400350101e2140c0280c0110f0704100010310022a0120b9040303650006082200c032841d851104880343c0205000072000400d101d030303811003180440d003003260380070741c10101c0e286204108449028003203890f403c100c4a0590012000960300042c02c002400c8240120440d114040b0f9465142500e4080d120303142c1d210750441a03071400140518100286d4486000200030f050380c1d4100e13a510443c610741000102008648024080d84104d500380204082d030080764140d5120400500301d45066480343c288116140c12500f8880490321603000c55005c0030300420004006441c0a0200c1a0820524000c000b041e82c0228046520845041e000700750300c00f5500c0c100a40108460359140c1340340c180c50300c0744446020087c0d007501c541400d100d682c80d400da120200404403561840c00130744444149a0310300603000c4c61a214a88000c0030400958661001560020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 368692679 1250 368691429 368691443
    0x70c06021c11070308010b030709030b0c040305010c05030f0f01031203180c0909020306070c03020d030506030a061514090108030a0f09030c08071815091e090803060a0b1206060304 79
    0x206840303070064140c600209604074a0380c00420b03203000b0550403850040c0940009a0710508514042ca8020680341451002600c1c52250001050120406908031030156030820020702921001030000b525543c01550700480c440442400920b50404449106060b40d9008240e00302e44041c10200b200a8031040d20142070710b40013096550b0019001d60050001000186070100304841c242c0101410410000e00c4e00d0140061f00f41001c000036070218026441d00200d040001d9541c443d8000310303190112713481c0020940c901d4554828055003041031450102d820001c1c603588c00402900910010b2182803040f0034141d8002e120a011180c0a100304240c070348890302c3e20003241c607a0794403000d00c03e01159200b102d25801c411000d00503400c180e00b40b08400f0030446410f000440c503103035108144e851a4070410403510303560580c5188a02c020030941c030b00115003c8007402148003e042c0004c1d282e005550842c4602ca800c00c00007010003c0300151a01c0e80070800c009009079a0b003034140842580000c3c021120301d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 368693929 1250 368692679 368692717
    0x17090313050103022803022b050714090108130503070c1403160e0c070b04030c170313034a0a0524040b0f030a060509100306020c1203130c0905070c0602 67
    0x80000c2c210320400d501c49a6102003600d0300e00c0141003007251404ac0c0018100302d04d0481e41002030204134115a003201f02880c01400556030400400a80184028003c0032408005080000e205000355410103a400b92000300d001c41041c1e0080560303528280c030b00c014002c0090401082050b01614103950710100e1100351381e00d0187c540e41c0300d041c2050200d404801003003540700c81c6414407500c020a0045841c1d07a010b05869402c002c0310710390107031013100401000c1026008500e001c050030750041a001c01d2080302c2541c026602c0a507400102001d01c14840110b02d02c00b0380401c00c616107a61a01c00b01c810140a42400310803000c81c0a0444c17090350b40c0c00c41a00001c02001803081d012170700400c01c1404000102d512402c04c03036618000d46a0903800680700d42d40c1c103000d00c4008103001001d0f00440340d00040040c1d940342c1011030b481c04c0ca44030800700300885d0f4000c810000008252211441d0703280c4101d6901c42400e132107409000071940f0560302c4500154604824500280381d40d401080a0001d0324003107940 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 368695179 1250 368693929 368693947
    0x40f030b0a0609060e010602060c030402181b03011203020f15011214030d0203060f040e030306010f020c100203030403020d020f1002090f0d111003050105030604121709031305010302280302 83
    0x958816078020a000c206205c01000010303814094290800c04041ca176915500701500000d040c540c0880d44414070040000c00300350001561000d000b071020200314102e4407503070365050045622035184170079070140c052410241c8140300040f0f03000ca030b61051001c6500d42c0ea401e01e41c241444104c1e01c1000c071079810040a0001c00810104041c100c03d207411040503950346032800500c041c444044d00514019800c1c140074040c11079020064a60041003803800364809524441c1c00c80c50000c50020554122504422000c500d60340400218443c2d40030703400b21003a1000004049958811074840d14000da004910301820f440341c1c0350018050301d200100603210200c010f4001a40c9201c4c1950f084580c4c907158180c0b40b0a90800300007400041c1c4503802e04129541c545004261940b400510040c2106120f60188010500414120b50780b40000050040585001c00002d51b0b40d40c019030012400c103a04c4800010380350700c24002c6a22441c1c540440b080543c8000b1205e07110000d5500102040c15000e02190ba4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 368696429 1250 368695179 368695181
    0x1060e1201060f17030702010f030c2001060812070b1b0408010507080a1505150903031b1b0a150f2703150c08040803270c04050c040f030b0a0609 64
    0x1020300b10f5985890a0240b030444180a0200460700441c1e1a8009003c50700150380c119101918241d014240401d640c020080d0441c0c03901209100c032200345504454028003884154032035000c0e280b68a04807403c3c10301c4004e036900c0b180070b14140184212103220019030040e4000381c01d441d5694001080c2d074189030700c0f60740b150700303440040b101400007031600c50400410b51054002c0396005550500344681d44e5042c8404075012207010303d010700180100107400d81594500b0003c440556001e02c000720280080c0300311554450340c5458100c10354003102c691111540c83c14003600401ca460800100420305002101900c00c40c0a200c249800d01c140d0364180401c8201c055601058003007402210000e2074154135003107070a002c6424860f00790a03c3d113451a04c1c1c0c5078101c800140c0050b0000c6826460307560302d40d49094412404001046501c008100100000b800040c0c1d0030b032140c1342100c0030b0105690b0585c5c4800c0c14001c510032846046211002080804c403a00700d80c0f504804440c401107009034450003040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 368697679 1250 368696429 368696441
    0x21201080d09062c0a0503030a05070c0504231f0b0406260106050717041d06010c050c0118080d08040506010602010504030210050702160e100803030f01060e1201 71
    0x1054540141075407a1000740d0140310340b4058009810400c0762126003040308848040c141c0000b00f204100400c85042960b60740600c00001e01005084a41d9144902c0004042d0380010344200c4a00d080d181700071615140502404402e00100c03148821912840702c00d034035400e80040d044108824084c203281080015003404070010340281c040c1240c0ea00d00e4034078014050141c803194122028104684003001052669010b8119800c0c2d2038a0f03521041e040c1002180d0381303a88c00902c0b48041d0006400038000d008061480310484140c82c0c50078180c0c0c3c8040041d00d41117444500141207400043daa0300c44e0350300506600b800c010142008102403511131005501d05200d0f43e803c4404100880200810000108085405401144020301031414107640103035543d07a442001d03140e025180c10009844a100304291031072803407150402c01602d559484143e0b0780070019503d90f8005041da038400f24101d03000004490050708581c043d086c1030703071908104484007004141c0d041e40c48a030f031510b00048200240100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 368698929 1250 368697679 368697689
    0x170a111219030204030c06050310081623010c140c0301090501021810021518010207060b0a09090312050405010e0a050f011505130b03030405030703061a04050105130b0103021201 78
    0x80d550300e003080386910005501079a144010940108801d1000034a4182c2640481d1000e081140e26034aa01030f004200c5859500103100f42d1062101c111411880c1701110002c8449103824808041601e1152540c841c61900102d8040b4076003901d01c034009003003440030806c041d240d4000d480c20a0f6150001074250342c110b000c00d407601da40106103a0180e014410580481c0142294030800c0341c041450040c1d26518225080b442050803400090300390007501c40805021100c1100842d80e90360345150803402040304040b032a0045400d4200442c00555074895800c080d500b50b204ca5207446449032504010b4170004000b100c95541b0f4022003842244200b155000032031080010340800d0003004a101d003181c00030340052450524400c01084140c6070701c0ba10262a000008001c0b51014880c40440d107184160740c030064151048110000920425612540c103141034418030007402083c3e0410002075981c00c0c0500b65014009041307004000d00a6409902c4100042c1005414030b1030035808246801826441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 368700179 1250 368698929 368698963
    0x10e0102040e06360c0d06030b250504051e040c050d0f050f0601030b01090314071d01050f01080a11030f180109050c100212070305190c170a11 63
    0x28803c0b58034140f140b010b079a807644181486003032403507030210b41d84d50f8143c2c00c55280c245100010403c45590101124000e01d0801030501541d9a6071a04031015007044540c680c42e048a1102d10011401c59000f849004220790b6900d400c083c100010048510001101d05a429034011404042522540594024540b8640b5059203171545450301c0c000fa2203d01c0c01c8105d206241c4410031040900700019503810401c28600003a07a00140070040c0c43c0e21050b504003800084030303803071000703031141000074620305803003080100741c0c0c1c0003100c00268207101c0000c2c000c0355440b450000c070b1a1115445006c1150b0b22040c50034006c10400d100c03401a42c10b9900a540d03030b070280383d40b6008128061402c45110504640f0580080202c018139840e060f1b1904041043c031489011210031894155200704000d5507038a448450b400d42c1da0746207182c0507019500c0030040380c122203064294400068010000358202c55003041080c0a070030b64580139602940d01c03128900c4c0074040a446511015134003004020410040d4801d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 368701429 1250 368700179 368700181
    0xa03150c180305060411030a0b0a0f0c02010b0a0302121c0e0405010806040b0609090a02060f1206330f07050a1727011707030b0f040c02150702010e0102040e 69
    0x18006200d004001c0720345004003200e52040001540015101d5441604040185080000e401c0001d051500da0040070b0302565500e014001b03011981d40c000c1850100c8048100140004020241e0a07105010030055022606170410005401c09203001c072541c0d05188143c503110b140c003060380e0750004031942801002580907010600c071424540b0810380900040700c018011850306940d03070200640010b00c441d01503191324002c40e00140303040002200c0a81d0003041c45031103078000349a5032810b411000180781281c590b10045505070401d520b007214010300c51002c440c1ca00386000c42c0c40d0f40c0720014a4620514400421a125400d014440503000291007200504182c0040382070800e13820b500c65a118040501c100060007a0306d1410784940741603031241c4101d100c0d00300b0070340040e02c1454100c0821204040756104000e68aa459404024038038130440d4162940b00c0e82c9070605c4203c42281c0c002c50050f80c0010011811468000134850340034586200100b112841202541c0c00e9070071903448024003a01b114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 368702679 1250 368701429 368701451
    0x1e030b090607120515040b031614030106210f0f020907081e0702030a08040c0909050604030306080d1b020a032307090b090c030a0f090c140103290a0315 67
    0xe0307848481000628040c131081c04e1000880d0950004171000318420340d56000d82e00c620307440070f0001203c01c031103140001694030343c0d40345240b28980018038070034465403078418082071520020b004440d1410f0a03880342d0007442c6150b510321604944040c000d4a0364107a8080d8400103903a074424241c4100c04c0d69403201a40e0415400900740561030302d4603031906140920070006c0341d660000c1910344014041c03401020f42d840b036040403000e2221079040550400c1c1880c44e00c03814010005011402240b080d40c003009031558500585840d0010301c0400c50000d8284810340301c42c007182c2140d40010a00040002428a60780c0da1441008130160a04801500030a504860b10100034030804008214106050160300e40d84c2002625644000706444e00000000c0041200c0b81071642c8890100100080c0c20080ea4003541011f54880c003940c03041070202400148408480d5209000d62412020614501d11400703000d481032040d00513214800541058481d000040070035155240601440302c1a01c002445250741 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 368703929 1250 368702679 368702687
    0x6040605071b030809100e060d06063b010e03060f01091404020904060c090305160513090506012102030a060c0806120705130f14060a05030d02071e030b090607 70
    0x202c0c0311001000802401040071954150454000301d800300d0f040078001049410590ba44042d002c111a0801c0c004541040480ba10380c2c03000d000e649650300d1310490101c494030410b000070703038848000c0c607000c592280035582a9413824014030868414107000e881c3da0f000b140403070314240c1c08503200305a040b00980100118540362190307020b03030b000b203111120760392510f034001c11490760000c0d000074407540e40d0303403002600c192042d451000655880810341e0f00f20320718041c1040303915815005483c0f00e201807006011141c4d074180b00d04072005620802030302250b840c04040e00d4581150841480801d2540c01c484401a80c0602810a500e1f101d500c0004400180e21002024a44020080d50241c00844070240220200160706021644200d030b0040b080c021506124026000c50200860540c0c28a8403810b080200c40c1d140350311a103001d4841d0080145d80d1f00030155940031000780740c0d01682210105000403015105c5800c040700b5070504c03034941c2c08d690344d03501c031a84030b23040701c40d4170481c0c01136018050042e81c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 368705035 1106 368703929 368703953
    0x6040c05030c0714101b08090d0309020f06040b04150c0803131106030a050a050603030f040b090d23010c020304051008060a1707090e160303081003020604060507 71
    0x10036a0080040c010b10700c4801b1032008200c0d6594005482a0b4920384600882c200030601183e549070150010700b010401681c00503d0980c04003015103940c0300602c001d007541c80081da80e0398941120107070011070744c1e4101d05c108907400304008003250080c402d5942007401a484010380d9206481c00741c40d09030700300100540001e008402c114001d41e09a00441c4250b04030b00c01401550355100c205510380c41030380ca0958541d07800703101c140100c41401001d01002034000c0c04402101986031203003880b0141c801d8038081c651206602805070480d00b8024180c200700744e400151308080c104000511b0003110002920100b1a01c2c400066081d0b440130240c90003801101d80f26200d880414148a0f07c4030480d0207851007542c208591040703a12000101c0c44812881025001c0c0e01508681d4101d401c860064040084550324290100141e0340c1c01004000525990711134030766070f200500d89080e900031 = true := by decide +kernel

theorem cover : BRFrame.Cov 368525179 368705035 := by
  have h0 := BRFrame.cov_init 368525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 368525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 368525179 ≤ n) (h2 : n < 368705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
