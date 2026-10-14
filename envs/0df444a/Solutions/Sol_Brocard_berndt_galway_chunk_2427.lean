-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2427
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:40:56.145238+00:00
-- url     : https://prove2.me/submissions/6c0a269f-ee26-42a3-bd2b-1dacd42a9b07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 436330935 ≤ n < 436510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 436332185 1250 436330935 436330949
    0x1e020d06050f06090c13030b25020d02120a0e09190e070f0801110f03130c0b0d1d120703020c060a090f150c02040e1c081602060906160504 61
    0x1007400c00c180181e0a80d1014407038901102c0300c183c165604500c80030a4041c80324051040001d12609200044032585c11582040710125050f0a010583c03281e1681c165201007282c005800403641c1e0402c482d0108201d0b00c5155884c0e60042c1007111ba140020080e10410003001c0c4a64011740220300726880f1080c40d41c0703450000c00d1090041004a0f580303195a01c03a5880365103050364410348002241ca0043c0301d2000c5011403010942d01d81459510f14440c0c5401c0507111600411030380c08040006421030074040c004204e5600196151405001040d044035440804000880e10011040700005008640b26100707004015180d81c03100140e0804034544003015001c181c0015000600240c07454016507014101c0741d8071525030341c441d40c46044c910803000e21640f441c40440c8984c2d21810052425401800c00c584800c422642000016041c204680b1002c0505074007154a00041c01409801c11462038000041070000f055242003403a03d450703036850018054460540003c0320b200c0403a2144049800400300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 436333435 1250 436332185 436332191
    0x9091e04031d031b01020c01020601030803010b031f0e06041d121c090c030b010b12221203060e09011107110a080f06010e10050105180604090609050f090303041e020d06 74
    0xb480e13601440c4500b03154606004d40b091020034540c030341c0b0005619061746c0e80418000d0850346041d9070301c121a00f014007140c03c24000412603c0c03001c20f1410a0700b00410540c89021602d0420b02d0a11049a050411900d2080350304000e09900f160005450002410300ca180981d41e40b507464010610640d002d0032040140b03050125a03014010103920660540340a40b069000b10790760707201800c0d05440707039062904040c41501c0c005071445420581c0d8104000000c0300a000800456aa811119104102c0400826602d05051040100920071607a00401d80c0c0000c000d160354a03a40d00e2540d000d4030000618040c40c8810665441d2078042c0300000500aa000300c8058042074080540c541600740210a00d0108000c001098910b4400c40c1204940040e1601403500b184442e034400007000c02020750360840c02c00c100002d80301c0740318460000180282000001c00e401d000c0c50b600c43c006c42c058001500c40e032041c81400003044404800082001d40a0180d024480c614030106108c401c040d480500f40e945 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 436334685 1250 436333435 436333453
    0xc09140f120f01050412080f130c09050c070c0e0105030714040204080a031101140c0304080307030b060a17010506070809130e0d121d10020a02101109091e04031d03 72
    0x30540100d40118403500000c48806c40445003140c11178011a00c0e40720100781741c40442c110005001d8900e602d18003e0030340400c07041d152019801544e80076501d410100f400001c200c814001d02005480141c000b50880c20101d5160000090396140c01d8010300440c094907080701c400c15500e0b03a040303400604030f6000391403600c0601d09016100c44140640300a0310350800d01c81c035100b03030078840c10b0920603441d421403941540c480c0d48a044580d04018502d400f030607030b2a510700600380e68040140c00c0c407507000d546030b441742c030003d105040656030103a0106000c0c060a1240400060b41442580c0a4050541d1034000c182e04010218018215040c1190a00c0c0512941680d082ea800b042c0c1018110b00c00005225034551500b22090030032082c1c03c1d000c06904442440010001c40c0e8005025090007481114581c200f40480329048510000311503900d42000224010b00e41010720140e9031000e07902844001c1c0d501c0c030311030240c0c4004000304014100710000e4907072041980240b0b101100700401408a440c441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 436335935 1250 436334685 436334713
    0x30703020f0d0c030b1507020d142103160504050a0b0a0c1502031501021b04020c120c0f0c0909190f08030a0903140f07020d051c09090c09140f12 64
    0x3061282c601c6000d50311100700c0c0350806c208202140c54031540074010b100d2401c2c0d40d88039041e50300194103200301706005244510a540b0443c5814003858801130b141581c0d00d08200ca02e11240c16603491020050200612003000720342c0e5409014411a080d0b55800c655510b500319003200c000a41e00c1e40100341c1590440742213034543d000d601640c8200d0951455503080e841050042e40e4420440303d0030011110032960740c00550030990060150545118120b612008425070090455002000600030715031040400e0320030030f5001c0000740034a00d82552100c0003401e02c49840c4e5140c80340480c0444503528090303492010001b0110701c1a00284c1c02c044000d03140c0c242424a64040c5c0b8002c01c0603070005003812070758044420b052040300d1a25802c50101480c00c22079900303024800e07504440a0b00c03240a00c5520f07a180024000340c501e0303101101d948901c0200d04001074001103509200da10000c00c0760300c80d41482500204c07203500c070166208660f8082030300d0140780081c6c00a086c0a8000d0b60b24000c0c909000303541 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 436337185 1250 436335935 436335941
    0x1051b0c03010f11030612160e150414012d03050c040e030427020409090f0501060b040510030e160b070c1212050708070203010204030f26030703020f0d0c03 69
    0x10a001c0700203004601c0c0c0329000ca020f480c40c81a060001c45030420102c0d040740342c810034450300071385500300307950940c2c2013040b1044600c0c032107031300004e110300c12501002111901d4061180300e4800442e01004880800034402d0407003d01401450702d9018201104000c22401000401c42c0e801440c4001180640300c0c68032079101c148001c1c40600a90a03c2d98042c0704120100a880540714400f040314113039901034611080892542d0740c1d0016596003000085180401c0b80650000d0501030024010401d00d00d180141c01c4845d03c0c2e000198004081c041840301e50358190580f00541003034500071aa060710703000300b94240f0004052061100c40711a10004101d0b0902020301090790096040e50b0409940b172040070540034807000010f1005d0313900c0c0720340d403c0e41e40543c000d0003046018258490030000c1e0303503010a0890b0b003d034105490301003d9960002c10803030694200b1a5925440c1c2c0d100e82035103899800c0d24110300000c0c00e404180754003c102400e10f03040c5281501c1d25254540310a0202aa40030005401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 436338435 1250 436337185 436337203
    0x50705061e07080c0d0b0f100509030706020318040b1c210e03070306020c0a0b0103050c0a050d031e11150108010506030d0f05030402120109030e0f0a061d01051b 71
    0x40c04000090403540070300003d030702c500c80d1400310900e0504080301100041c010105940c3d40200d9034240320f94692251007065200f428240c554980e0b0b000d030101058500740b07081d40320700304540c420056403940c45642034020b84e0300c0c40c0039603001c144411038000050301611403454441440350041c90b070b02d00388520303c52120105048030300c0051500000d00700407145004141105a01070b80404800c00000b034141d801420003420700826100203a5685d910000042020381c000c0c3c503d41d215026441c102c0ca02001c40d02c00a01c0d04031000d1880612503075003d4800252450310380020524a52520741090040307582d2020200c41d0303010345000c102e13040d00b840002c03803007030203401c1c5150720380000a0380c141400200b00e00800081d468010341880050310803103003580010400c0b40c10002d505034600023030303a0074004c0c0e00d00c2612030745803254a10920070034406148003101207584a070512920800143c1d4210301c0c82c15048918440074400300c10b00302d005076400e1144980340c0700311244100c41c0400c141808909410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 436339685 1250 436338435 436338481
    0x3091707051c0c020d170408100b09070305010e040f02010e060c030c0d080603060a0f0605040e03030601031121090a0c0e1603091a071101230603190f0305070506 71
    0x104100400340700f141e040215007002908842441c020602080d00c180409030710562400d011840d05880385a000c0c00e100320014040c10980c0c45848000c2d00d0300c1d041c45010f40c1302a4500e01000190708d41922094445c0e0301030000750030010340ca41d80000f564826416141c0010002e4600b036900d01e041071480f030b602d50100c07440e800280581000d07200e0151040d44d00600652005006107040d45800c1e400c00d00904402c1e44c3c1d4503060365510000500d42d01c4502070318070b6030064072000d56100d240c0200054280c0d050b80c250080440e600300300d140c0c0144811003401c410a1441300c1001078555445002070718083c02641e0192242080220000d4541c00741e186080c811241c14030781c2000203d10210075419950020002004501c40c05000e440c0780b400615051f80c4202c262500c1c001c03280d07071107026070308603031803112031455800504024003c01d400b02024141c200800342e0041104c401602500c421040e4100001006081784003502001c1c18132403000e41c0e00c015044402e44629080c0980d80e6034aa1b003001080360 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 436340935 1250 436339685 436339723
    0x40f0503060117062706070305091507050406230c03030912070b06121903020f210304030311120f1501020318060319020c0703050708060106020d0309170705 69
    0x125902d02d0403c10b0700c0c01d07071600c54014201601c401c00503841d500c0e035149a441c0d885c1c070455007043d11051300300310072405400b168074002184e0906045540c00c10f50220310070030011200c1000d1049403a800700c00c8070115040c41c03030305004154213110404880e500454a50341030b804045008442808080000c0d030007881102c0441c0c0007075407801e12070381180c000c030341d8040c1c031100307144000452900f0700600d21186d1494402c280d408035a0030503480c400d0891882c0082d00164000d03503c03019030b07180c104410690b024501200d00051403000302e0804041c400100007c042503162030099000c26100820380c1c0b4100c01402d031301d03446172604420030106954101c1d540b0409038001c1d21108500c0d4000300403140f40b60301c0198a854942000070501c28960f1000d06280c00300e00e040c000307c0040c125184090284444624060610f01d4a1030611510b4008075401501003600802c00410100703800084004013a05281030204882e806407c054071406c00e4040c6240154400141c003c1c100040400c00110303960511642c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 436342185 1250 436340935 436340939
    0x80106150f021f0b0f100809010c0903050a171e0901030f0e0a060e030903101d0127020a050d0b07030501150c03030203040c1a0301030c0803030c0a031a06040f05030601 74
    0x8a075920300d5681d42e0f2200c1030042401800c000310710b03040b03400c1c002d9010b001030766505060008600603100c00b450b0704000490a2003071001034074080c0203c405840840c42c007013091074159154652600c800c1c1d0002425480c0c03d135a55104e401100003650304a43c11600f4038007100c13100c011f00580c950b003e03a00f240e00103440c060341000c022803203203d03070606800c054005082c03140c0250345001c000c1c11107004411180c4810f02400e011598100310070900c0c42d802d114041000100741403181c0240c545a03204e000b040c1d0412211030344a080c0d0180880320900301c041e840381c00c4446030000c580ca5100300c1d0441a00300400418190a115008040380d016400c2a541000940e0361a0f80c014204c01d102d10900740003454038001c090209100f138018541003406005c032a03900d55030355101d20300c10300c680c0858000041d802000400910850690620040c003412020b0f520318134104407040d00700d100d900100700c140340d92460300039600300d484480f8801140c000340c03884d0b56482d101c001c488a024820701c41d66120348905000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 436343435 1250 436342185 436342187
    0x9210806011404060309020120030d1407020c090408220608070f020607180504050a05040b0a02130510050d06090e0c0303090a0501110f06040b0403031803020a030f030204080106150f 80
    0xc1e01e044040d10b0101c40c00c003410103d007100940f510b01000d904007c82c0d407100c07000400c0400c00324420039030007038011a661441d5040d40000d4514070715145007000d628104101c80607401144100c1450012180148180d50344d00d000c04c600d004141d6801185d0361a0300c441903000c2402d03418402604c0e000d40316506155124070040300c1c5080703082000380041e0049404115600c0c003076252a0700c05249521000340d503507182c201050407100b085510000031521941844140016000d0080c2c11001c4140103515241040e01c00035014035203072245502400400075038644e06071240c0309813422080d03410010711090359154214005060f041403103004034000c130701c074085c51031a000080714803001020b42040710007071901c401500c404503120041c4030340d0f00aa090521020200340005441544150391060141c107140c10002c0c1154512522825080403c0034440c000c00d0b00083d080300d00310740c103240120042c1800311007140a4000c540c00741c4020740c2031290125403095052a041c0060400d56030302840f420551034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 436344685 1250 436343435 436343447
    0x10515030601090605090321070b1f05091305010507021b04020a090b030a0b0a0303030c1e1706030c1e1201110406300f0b04200d0921080601 62
    0x4000b40452000c140c1000030501904c00381800010080075100d006420003075900f04100c03c100050306280c000203010082001c1d00c0c400c03582000100d15840000d0100c801c0b040020840303406024480c1101100203104c2c00c500ca18187c00d5140c0c008024071050501c1c010217540e8006401c0e1060407a40702e496140b40300e0425200303443e8400d81035511586c52a261488505080c1c0c0040c0200c988151600106800741e160f01d420030300250b1081e034001440c0c03252101c0040c484566098010a04040031102c4a01280c4c4072501c43c0420380c2950f0480100c2e211a00060710b0010a0709542e5007100301d2501c2e13141c03244402c10104004c100705a801c1d049815408000608071103039080c544d01511400e100601c1250301c215203155207a50501040c031711402c070344840040340102094000d4078264817031003013500c44441c0d8000d2002c401d10580c0e040c05501c03440c4001d902070f0300101c441404041c0020896500d482c4041d0000e80c84240c202241d44800340c60344061000d42d462040203840071074031031004a072140d48104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 436345935 1250 436344685 436344691
    0x7080702031204020a030f080d0b030d090323010615020609011512060207050328020a0c140f0a2d05012c030f101103040206040506030711031201051503 67
    0x290285241544041c02c00505000c05001642c10010301c03807006c00080c000079400350000f4040c0d09882d03251650314a4203000c1e509445001c901a4200f40d001108aa0b001021101030360340c00008201c1f80c0c42ca690403088000c8045464030480d41c01d0140014008071031990307040300c241381c0340c0c240d0300940d982040141c00c1e980c80c2e2002c1e10185003140010003c1d804544801c0e03684511580015280012940301c603442c64014041c81204040011701881441d40d907004400b00d804543d001601040c0c801d601c034600500528403031030203001896925020a40c3e40c62130051403243c0003d00d02e10203140c50344411000c080c4404292030b101441c2000c09039100780c005003081d0855605a68040b0250031a512440110f0000307482c501c0c40000d41e800c940031580c1c09024541c0b4046502c0020300e00070300c90300e2245042e039841418013083c09a0800510001d030700c0e05803c95017518030944a541d130301d80700c06500712103581343c500000a85010114100205001100d421f078125a806c6400400c1000d6284081d40380e88815 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 436347185 1250 436345935 436345937
    0x1f0f050a09090b0408031b070501060f090c1e0c0b0108060618090d031503140d0305150f12330105090903031f0f030803090d2f0a0f0f0605070807 64
    0x3400044d0005040c00000c59200e410071511014800c45420ba80c400c070740003510701329002e944071782060241491000030070009000e00b540030302c2180c562240103007580e030500180c003020a8040c03c1a111950040c0c28600c0340c1d6a01c09688000d643e551076440c2e07200c200540c0d03402d1107090039401a0020f05624000b0074003600c1400c0107488154410502079009008455060342c03038081808002001c03401d049005d582928440d00038000c0d45042d56001000c5810040990107402ca400400003495200c0804460000c04244c1e00b840420300e8204140d490854002d80701c1081d81c0412840104094a8410300d480090141a06520b20f90326a401c01070502d0084424020030b502c1400010000000c400740c114162101c0059400700d162551210045400c080d003040c1c0e9803030f400100780902450100074034070b6411800c0c5403034545010341619000c40c00011030031102401140001142960b41d0078041c512400f03038401d05075940a81185080000d61110301001e55000349031200007102603018070030480c46403a40d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 436348435 1250 436347185 436347203
    0xb06040e150a0b0d050a20130b0a0f09080303010e0f180106090e070812042319060e03060c090d03170703050412020c030d081f0f050a0909 61
    0x8000c00019003450003058100d200e40698440d51564640340211005811442c00c400da540030390904010540b10054044042d892400d02c1c1541416020304034a5110f640d8040c0c001c2c0d03508d1903074100007103410f956000542c24480010303658501c1b68000c003e40d482580544c5a115086544000990b16030009214100b40f120940d00011300031030090701d046500c404180340c42000f040d80c0940503421181c4a81048803d55a1000c1888070043d041102c031004226400003440c3d4101d1100c508140c0d8010f600c07078021280b494908503c44c655050f0040c000b0702c0409055080344c00b00c1c0103100340703020740148038103404920901c44000c01c905010450620130850500600e140c02d60320800d115940e055040e081e410011503006032640c1c0711140d0401130040c0080e580100700760500e130130300101c800443c0c070000d02594403000040e440b036100810b1880030048141810309044da00d80140c00817100c0605201540e00420308000703ea00c0c405441d80c40141d800a0b9420800704e926550890102d8211a00c040c0403044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 436349685 1250 436348435 436348439
    0x3030206010b0307030917040618140d0302190c0603060602010b0901150203071514010b1810090513060306110c0a0b0a14010306060e0f0c030406050403050405060c0606090a0b0604 79
    0x44440b00440d0080400c2c600043e4030206030b11030603403060320701844451104000900b000340a40c0074169101c1c1d050080c8404c4e1f2300c3c51800c0d08036805420007507441405021040c03809414103000348004040c41140180c130030502540f600d401000d0210703600030100820710f85407001c1b800300c1c41440f6054a008018061000c0c507400d141c030740024840402200d1045201c20849040020410080d12183c0400240301083c06421b154603ca50004142c100c0000441c0500031201d40f8910a03000b048588000e0719003c801078001802117503910318a8000365004010448a07041600e05503100c02c0031030b8001e10f400c001100e110b80c0f0a10703051081c81621442035100800c032401103601c00e00300540041403200002151462100c15440100d000d03401039504640d1f4486c10000d114407001c04913444000303060340c1d2001e80b41444412009000181c80030301030582d00e100090030140101c0894000d09402409a0307120401a0051a522101211541c2c01002640d01140380088240644504040000d001500740b078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 436350935 1250 436349685 436349699
    0x10f061d100906080c0a1a180301060b0307080402030d030e0a020118081e120403031704024204080706050307020a061a01020618100903031103150109080303010303020601 75
    0xc40080c1c00101c0c40c0552038030010300301005220704030051101c113010741000c107149010426884003d81c040306054001e04015613407244090110380d131084203a480c045401e4141da0100f801012103811044c070f8001c000041c02901c5070400145440369100318202c90719040b644200701c00f034030035031104e03243e917948508418001907008090080d0a40040721000c40c4050351b40b0600b034035180540e0582a0741c50b504c0ca41d0032a000c4c0090201d04244402c0100a1307281c00e02d0740d82c0c01031003400f58080c24040400b03050b010904540d01d403200c52154648410051411031484005200803290840d4188922500d000b00c090b0400013240a03201120350440250040c2803600c0d0060714168001031290045000d50b0a001300000c0643c800c0c50038001c80380071066114602c1c50300182c40c0810140001d600c00b41e03290400081020b00081074903d000a4100104030b0044a00d0107801030040825400c42603a0b000c02086600c3c2c084c03090b5201004d4090742c440381f03615629075009032a44070030b00000d00160007031300c0103001071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 436352185 1250 436350935 436350989
    0x90c090703020f160b070801060806010815130c18060c050a020d1b0f0f050303090a18110f2d040332010f0e010c02060f280905010f06 59
    0x801603c14010310b000c0010807810540303ca081c4080394118208400e100030250300c6000c0074090030f071a0a1940c15403e0102c00645080c038018071103880710180101d00c40982e10360340c050000360441000300344092401c212000d081c500591000e0155030001d114000f030554815006003034a181c21401420442c0340d15020302c01070301000360045d81c502204005e403190a6007800c01e00c2005240d0031f414465114142102d680c807016840d17004038420307842401218490b5444d01002e2089035558280d404583c042e01c103980300641402e58600080c00000310b040390b0000e80720001081c603200d41f04c0158240852046034103800c011170800b04180340a05001c140b0005a0588401d80340d9080445d40a5071413241c40f00c201018140c1041c40041651901c0c1005100c1280307000780540d6004241c028084020300010007560744500070032000a5041da64045018014001e0000c2030b0840100d0040840d240000b203000c0260500b010119031a40c83d144102e440180e2a1250009440b10076207240452402443d0320050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 436353435 1250 436352185 436352197
    0x30f010606080121020307060e0f0901051c111002030702151c150e04050c01030c02060714160503040b0c0d0302090a0e0403200a020f0d0809060c0718090b090c09070302 74
    0xc130707010043d401c50150741c040001c080209070320b90700c40c0068410138007406034544c5241d04143c02541d900005001d165540c4080c242e07080b20142220044800c1400c200144103214500c1da500a10f5200081001550100040071914020764219260808118440c800780c82144818015050003064140301c02c151900143e910300840b112880800d91656825100f58200707407401c40d0310340d00141d040c54180d605802000035244080c00a40048d20301100082c03d4101c4025410401c1040000c880006504140424445d150404120b94581c0c0d01c0c0c2c62400c81d40d1b40b00820745146441550503c0b46041e00c240200e0b01900f0f0080c1015484910b0443c841c0c3c40c0d0100070341b044050141c80351180c9122082e05a00d03800d070705402401001100c2803401844082201e0061950040046070280404240c4090032a0700d61b003c1510030781d5495141c150094240040b540000240301c2c1c90811080e894815078000c00b154500803914100d80341c0301c8040c0703156207461010195400151041c006a0b8040c00ba90103012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 436354685 1250 436353435 436353479
    0x10b041a0706051806090109020108070c0507030f06020c0613030f03020a17040605070e152a010c050d0b010e090109051b0f0c010e06011a03061f030506030f0106060801 74
    0x20912010365a92020f5480c110b440d1194050368400010300d0348020004140c02600c0c24000b0407803004550002484584002e01d4182071003444c000a8080000411140300110f8010803901c00c80383c002c1c5801d0002e54018039244525110700000304124814804814100301d500d40c480c640103c412000607400382d080046030405001651142440341c400700c210180c4160300c144400038131490180d00261a2144605606009250403445542c0765a0250201c1e0200b440c0c181d007018420030170080024020741502d01d0b42565500304010768094a80050181141880c070440500807502c20f03e004507a00648991a1903001e03841c0c03801009004501d9000d641c2040640780e046658070300c0104201003551040c910440c3c0e0540000d1403550001d802e10071031008004580c050301c065458080c601040c0440e01440782d0285000002040a0b40e80791000c0d03900c00e00c03540728200c80b01c80710102c01070000d020440d90a0b01034002c44c9009004498188256001d450f0b003501c1d8145d440c2d00304584454030843c00035104c1c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 436355935 1250 436354685 436354687
    0xf020f0706031e0c020708060a020f1804110a0206010e150d06110c0d0c060b0627041b03090c0807081504080702061615110304030f03060504060b04031406010b041a 72
    0x10010b20071502907000405130030b800500c1c1884c80c0460840c03a00c54018091510f0300e2050001226078135042c8100d401034030101204c00480b0502c00000360042202c1c0700c64105050b8002007140d556034010408a049403107aa002d030b4a40c1c4d03a0340c8000c00040103c503100071381c42107546164a000480351790100302890303241c000307460809040920031803a0803403050750302000c950120018402c02846000e0310348d1b404001d0fa101030901600d21280752100921800da01b0900311041031000e01500d855001048483c445404030707500320070600c4090001c01e141d201c152004103030313035034007060152000948038126035030b000007403000050030080c25004480103401101c4040d410016100942e4680c03001e010201c0c243d01754189400768501e40410700d05085032149101c03508100c0d608a1581000050341e600c00d4040c1070a20007104891811002010700c1d0300314941c00b42c0740a00c0850003001400c0600309580c820105000c085801c50320050f0307255030900c696404500c00b04010301c5003504000d04446032034051b40e282 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 436357185 1250 436355935 436355981
    0x60103030c080315060d1d030c03070f0312020706020a03140c04050d03050c071d09010608030703120b090a0507110307020a0b160b090109121d010e030a021806010f020f070603 77
    0x6039241e4040d801401940307466800a04100700c7e0886000030540c0080000e502c1c1020304950309451b8080c41394054401004404400c05050080c040085c40d5000040115035985451400c90001e40081800d0000039141006200001040f81215400f44141030006402e0a240c482000280c0119080c2101003107818403940040c03660820a0601070824000c241154401c0c4903042081450020904122a030400200f0040080c000c821601e141d9018070b400c1d0b104004844246002e4401034202c00e400c60744210401122170b005512190090411741d541d110305003c0102e00c61360300d0085420195014100c0c00041001d40d161000600e80c4110f030541003c00c80300140c0b40c0894680045844a080c0d9440799001420000c0640411034001518181010700100c1e242e52083c84c5d01e50259404c1c18081c4220407400c4640c0c003080025001c5500030400079a07094100c9041200b85000e45040e4041503003580c00180d2503001040441d0301c41c00324001440001d14115084000c0c0c4515100c0280e62030b8882030b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 436358435 1250 436357185 436357189
    0x1317032a0412080c0c060a0914120d0e0102010c2c03010b0d050c0306060406140405061311042c0a0203070504050a14090a0507020c0d2a090608060103030c080315 71
    0x741034540180411a00e500d29213012900302410303242c040740b05000400404400d01d410004a030252144480c1140d0030385007903004030313440680f014442c082510a2002c43c1d400a5440025585414000c1c1e0003400402c0540d04103590715141300d00743e12400344014020301c0c0b454440d00302e0402e68800080010030507030554004161080f03411441070b03400382c0100b007000480b130034100165500310000b51410030416180c0200c507030541400741c401c288202d0f1110041117103540c920f20340c02c914030120300081008280c0712a40094940c40780c070980117400300f03512038a0310700d85000d00c0f80d002c2c1c0300030f101c9485003035070302c41c10301b81c000303501c01800c40d8144071f018840881d0545504505001a0050301075001680c0c8407038080003001c220040503480742c2c0707040500b0010200e6011030340020000e002c0d01c2c5802c090503d031038092003080480041c9810088640d2125449090301100d070002c480088100f003007451b80b07880c0c2d506d894250900002d00812030312030802001074a4980110b6204910a030280080f280f1500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 436359685 1250 436358435 436358459
    0x20706111206091306051005030607092904030f0807080d0e0606121f021210180c020c010c05010b03060108101812080c0d051317032a04 60
    0x180440401030101d10501a40c1d4544502504240212407a02061809680a140701c51800b18020304880d103800c0810b40184030240c401000c0c2c48018241c0e00d543c901070100420345110b030301c0342c1c06015564100d00140d102e40300d40c809e0503d0000000c0b10340780600311f03258011000b520210489100d502003101c0c601040003403002d02183c0c40c6000002c5484c10003100c02c54035080c0c0103401c0c1031060303401c40100080380b0b1000481c058240c04d060716801d844082c5c00e0705800240614041004891014010443c2d4030000c104aa8140c903c0a880e02c0c102c1c01601c10400100c0b1009010100035a010025000b000cbd8000d0400400c5030b403081c0000328440314540301007420400e003130344180711680c08003056046c1c1106601070b1400c0200040b0890788040d1075500c4140002c000005582c05111400c4041581c4c01141d804440040c003c0704018040782c1086c620317210444043d00c405940408407041e480000794a0344003101d0140c0c501050703007681d001c494001c610070384034903010403152050700b007200148034480c4803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 436360935 1250 436359685 436359701
    0x1505060d0e030f0f040e15030a11010309080714160b090f04020403060911010e0301020c19050705030a1a10061d040f090b041406010b07030c0f150e0111090f0112020706 74
    0x601c2c0c6031036a10740200c6c0c00d0341c032101a2092181a1410800f4519614002a50b808554014a80110006150005900503e08818058030400b00050380c43c080c441c808a2046204840f24121407841d19500c1e0000c0301103000f4002c605a01008004036030541c600341e40388403082c100040c80182791666960355182241c1d09040203c03140c041e84203a864456800014005110b4070a8009514040d42d00d8002602c1c0c426004100803109101a072110511108000c03601c0600350150881d9140c480170300b004800601e1980c3c1c072040b1400c85000080c15070a01c03124200840c1c40544900300100c025107559040902142c9209070405c2c5c1d1840c1a010054981c0101095a4082e03103541c3e5060030941005501032500e01c4001c030003a4454801080180078107801c070351199815181028443c1302501d4280c451144811016100302d03520340b103c0c00246450783c08001d040e03071050020000300104050f1000c0304d005105890781d02151509031040154042c442182c00303503603210b500603c2e260b030795540c9808a80c601 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 436362185 1250 436360935 436360957
    0x1506010219060f0e01061a0313050a0807110d120e030a0c06120f0209180a0b2d01020c130e07090c030902010206070c0c170a0f05010f1505060d0e030f 66
    0xd424035080c070f24461007115203690902c0c00030b0140c0d81c2040d018100542d001c2104100c20940040003511200e10302c2d40b0380d02000d6000b03082d0b40e1101c03d01e042001158208020550700f04072840e030040c0300e500e00b040000310116440125421400009803041d956504c01c0c0c5140d603010b009102d803210016140c030321040007411882d03d980504401ca00f20300011200420b40e450724507481005031051964840062500c1600780101501d9181d5071030300103401a1402c06540f64000b070030f141b10000c03078440080d0b0004c2c8101540c4d80314403a03007807d0001241da07641001880c94003ca50b20a80d4026260150024460255144200d032102c0d9554070110702198406aa01c000090741c5d0800b900443d07905001c55a006001803501e030780d190440d9107528a00c0c04940c881c07200144640c8030114400c10080c84051551504a46c1c200d0038801c0f00d080c03190103080040915800503141c9040c0c45050302b00107c460707050710000380440b800d01a0786a0b0080090003400c21300c40ca1440306008020620020100030000c003204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 436363435 1250 436362185 436362191
    0x50d0e0d0f17010b1b0703140705040b090f0627040c05040501060503090303010b0901090b030f040c050d050c0402030a06030219060f0903081206210106030b010602060702150601021906 81
    0x70701c0790081251646140740030000070040c0040043c01e22880a441658410140c0801d0741c000c0b001c0d41c80d10304111a071005080300035190006406240204110088410035101030000d068410204a2404000c45103889503400740d0020030b10700d04188406035500e107442c5160094143c2e8503a600240001c1c101d8007212190158281408203003020300900b401410305091181c21802c020b490907032039020501841504850100340000300da032056803004001d000c882c62040c0c0d681051318003034a40b181c0449050f154984d070340b080001d0a08006525001043d0010060544c210141c81000b020b07520148c212086036440e4500400503956842c51400390700c11001b60718803200c2c0382840c090704034106864000f091007410042000403450740011504038094881106c40c180ea80c000000d28001c030307c4484030844400240030443c1c0710030154040320540340101030b048e26a0383d8400c012641c41200302c0321000140c2200c1200d42c00d00c01e4490060b03801000500680711910780c0c00e0002604649005d2007552a80c2e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 436364685 1250 436363435 436363457
    0x804031a0402010219030201090c081e0d09050609180c03151503040803250320070804180f02070804030212060f15060705010608010c1202090f01050d0e0d 68
    0x81200400404003030404003400382032030980c0020b0348607000e40c0742d9840301c8054058102d0416100390320903000781d6441082d80d6009c40d01c807144665181c802143e442d110703160b95504004081070005064008100340d60b1144100ca051200b4800c65800040c20345800c050980c000034400420034541c10300c40c050103420552a40381c4010810481a101d00e0214015400c40482c100068803039011650300c290040700703681d9651944010f070042484620a10300511700c03510b21450405138560030094440d06408400282c03d074454648660710b118104009002c4c80301000200109075000e413580c602c3c194070400028818078451240010703603010f20003c841e80e0400240900c114588202c2c0c55002200c050020710300c92404038148222150701418041c0700c12198808000c150343e4400031541d400340c3c064000e004241d034481856000e005041c0d03042000c950303580140980c80c0024070035500685002400b54682031100001581d07940d010b5150f640c0c41f19162000741108503801c00c00003001d180c0558840304045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 436365935 1250 436364685 436364693
    0x30201020909100303091a0c0109030e0102150f0412230d0608010513140705030703120206070203070510020306060f031503011109030a120203120405010209030c100c03030f0612080403 81
    0x5000810058505244071400d1000c80e603ca0900407e40e4007207006401c282c104c102103c90b060041001d4400d2540c2001c4506082682c002d0703071ba141c072200a800310342c00c5400711074102c50840f00c111604421010b000d000200031451619504069102c82d08180c112460b210b4400e20940181115207003804100003440195224240314850003001c8041c000c102c039041442041c0d0341d0250034503015029400c92410b5510104d41840b0080040900a04031218942e80303141c00012220001c0480000d40106000184424000300c1181c2e03001d54040080c0a18a01000400c00207400280c0075580151f01408034000c41202d01c030043d409414684000111541c9480c00c050035900c0050349104400c01c288100c41580d00c0c0003441361069640442e040d0b54080e24014200d255001c0c1108500301c0d504501c0500040c414194006c10751040207605039007000305601d0900c081ea101c105000f10014044080b1400401c0c03181c0e0002000c1900c4110200e2155a11a502c540110030040d041c0d44d000c0300060100204 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 436367185 1250 436365935 436365949
    0xb04091b0305040f0212100e0f010501052b0507090507051e0906070b0a02070813080d080106050409022817060d020a15032309100e03090103020a1103070302010209 72
    0x1000945002c2c4000d151035944e81c4000f40c040500240940401520704401c890140554000e404d4412420410709800b4141556242001144c55029500e0310340049840d0070b06e44003100400451241d251080c4440000c0100041c00a500039541802441400b080034040c0d40521805600356603030b02521040300c0f044c200404900f2140c00d43c045001000750000c240c41c0c0300d0039079183c1c40c1c0005414140d41d980c6206440648611040105680320005031299031181042290080d198810110350412600c0c1c5805d0b1055203081c021000415001d1204018006442d002820142c40e05440440103554400014422103c51030062000c500c0c0f20b03600407170604100c0c000c65032100b4200c82029011600745c010981200352400382c07002a8110103c81740801d802504010340611200c00141c0c1c0d54404130034040c0c0c00720400c0c1d405007141d0083c02c000c0c00402c0030900500b201d04c11160702651605520900541c0250f001e00c903800180325491a4030840000140050900c090080e0009039171400101c08210710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 436368435 1250 436367185 436367231
    0x15070c0b071b051c0309080703030c0b0a060b03040b06010e0306040302061b16141e030a0912200f03060405060a15060504050423270c030a020d020a0b0409 68
    0x1080c840c840c0401c45030f40c0304d240094150844100f0010742240c0c81c101204c1b4040240c22000c098850780000004050f4042ca10300700c034500401e1402e080703440b001500d400341e503072078030030084000401e0011a01103841780e44480d40102050400795081103505c0f01081c00c0100c201c030180d025070400d03400c00c800214502c2c1c4d00050f00e1010006e513407416440000100910040c030002603d1010b84082006164030100100400c07800444441005950251000356072548200c200744005444030800080350031008108001c0282e0104130286510756200214641c202420342d542d5001e0700d400640000ca032420f10400d402203004030090f10484c40d01a001c01c1c25940c0c102a00000b04450301c0c000c011842d4000c003136805a680840e030110308114401c0f00036071009288621440310074440b00510030f1a144075002503d20340d03008892210018045403000c0d45a0713403040b4102e6015000f403840000146028022091700360301c0200301c1e401e03c80d100c6a481388280c0080d080025100d940340d0041e504803021180d1555 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 436369685 1250 436368435 436368473
    0x20409140a060f0b070602070804050a030501060602070e192d02031b040609090203060a0f0602060a051f12050f0d020708210a18050907051308010b060915070c0b07 72
    0x302c903861300320507200520840d80e000e40825408600301040201200440b401031038000c1c01d4444164690174128000c1004d4442c501c00340c412190002074680c4a074480ca40300d4103040080000341760140116801900c10b004048184540710041c000440000088800d4007503d00707040103031246441d050804102a035071185490405040c0020040700798005140d0007610440300c00581c807a1a401c0100e0200a01a085090382d9012a00c002c1805980020164842d81c2c020700c040c0303c01c0d140c0070a01102126411144000300c00e500030240080418031b135600c1c0b6414419001c0303402e04290300100c5414201004240c400581080708200501300c0e040200324901421116030043d4440300c55000c201d54440d440000041c0141d441210080782c3c00503004000401029102d24824600420001c1040e40300c80d144903900c030100d200102c0c80040c144516641010040d1031240381c900040100100503145045044031b94100700701703180000343d01039401c1004045200c0802c0e1144014500541481c46812200b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 436370935 1250 436369685 436369709
    0x180a0902042103020a0b0118050f061003110405090108060f07050a051b0a15050a0c090302060d09140d02010f0e0d0f0e3d0c0f15020409140a06 63
    0x8030250700c5002d1280c50115001142c20b035190308a10703050b8145580c94a010306848262000000c000c107200880841c0404c05580400540d610410175441d0104250f0f2900c1d040010442e2000c00b0354040c2c0e104c540700703203407200d07580b418140d44800181035400c00340c01c80241504071a050100910850402c1600400c440c00c195045c00c44440005240c2d0003404c0031030705040c0c6d02d0003207000c180c4800e000508280340c02001441c2c49501c01039000015180540300c807105c01d03103403443c1d014600c0e105a02400a6176801030505140408c007207120000707000002d40c00d90303294052039071150350144100882820f001c129000070440407034100303440046910790000003000760450f40800c00c8041d4020f4682c0901c0e17209080c0218441c030207001041c0c07104906143c00500804401041c25036294040500240101c50a00800940c0001c00101c8400d900702500604c440701803a22000000d01010551000241280b00141040c0e0380c0e1075420203843c10f1140b03d0310800642018481c802c509802400003500f61000070b5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 436372185 1250 436370935 436370939
    0x203060115080c030a06080102030708010e060d1502030a0209060c0106031509050a0605090c0604030c0e090a03080f1f120c080f0714060405040606080702010e010c050319060b180a090204 82
    0xd0b1452034000c0c00c10020010000014610030f001d51710400181c034880000315120329080304d010303101c25004c0c000c0d91440710001c0001665480c2c2684110700d41c03070b8070800c802002070458055501a4001500c802101030f005e010b80d05864581740c0c040e14000b21002c0001c212545103050204079101ca0750341a051030703400c1180c0c400102e100002c0024545a00c5903000420b5942c1e8200c050400c80700c002495442140041c001051000381c5c5c001c0c0068940c0151303205000c2e00d90801d01c9a0320a140c06000f8003080e06800040c5951420031001c3c0d512044180c00360828030b50f0300700b0304070240887c0e401c04492148094802018802603071035460203001d00e1001406401144c030001956041c55110380c0c3c547c5035220562030142c0d114501900c2c0207010142045c41995143d01c00903007c1c10341211001e00540c41c11488051071a41402080d80071002625080d2071500c40d84601c00480501c2044100101c0d200c0d1000506080200000c0800031410704090464403088020001140303519407100010030300501c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 436373435 1250 436372185 436372187
    0x60201020a0e0904020102160b04080709020316081b1207020c0307033212070212010b0d080f0712020609100204031502210a020901110a11131e090203060115 69
    0x407034103003044a4030a80c1e41c2c4e0341d00c0100e180c5a0520344400030150440c10004000e44800c02500588030340c4e40582e0a0141c8a031181000c0340000c946075803160242d542c16002c00c6004a81c19600203800980e6a0321031047c1911544941d072003210300d03000d50281c0384200a80103605020b95121000b04402501c686803861715110070307031240030350450851000c0c1080010205c00202d00b640341160500309541d008081d0080084a540000d40243e010b400b4201302502007440610440520070700050504501e00c580351240d0030240c100840d103541d190010015400450002c440e11178414a46500a00041c5001810766061160f00c0050200560060005000040c0c2c04400407217851007003040140c48500c0c4c2651180741011602624090481c031505009554005070000c01003c0c070281ca469031201055865184d4819425a001d031010407a04091405441d211543c04180b24250202146c1890f80e010340ca102065001c012244899030384042d0303011030905010941c0104290070001c070182241d024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 436374685 1250 436373435 436373447
    0x171806090a06031a120f150c030705030703020d0509071707181802181b030609071107150e0307090b0901060c080409110702041a06160203010e1c030501060201020a 72
    0x48030103154640e5001c41e144480303194900ca000780300800c1c1c4042007184d80c584649405410700c00c6c030480d020b400b50104056080e04034503400f40b100ca40e0464516903c0c06821141a0000380c4a8010540c08000300c60041e21680122406400543c001d008800c1ca0801c00b102040494a00c0b0101c982044a0402000d20000c01000c84a160002c000c00c10f44e00600200b0540030604500940c8600201c3c03031800d02d011200c4160340329520f819007110310002000e0312603140e0301084541560100040000540315480781d0f0b005464001c44e402151501900c900c0b4044103804000f400750b000401e0110196a0b514042260030002e20024100f0416280c26001240b00e00030140568818002e9403490070040044107812600200b507030520402054003c080421030a600c001c90076031140d818403031a50011303004102c00700080320b0010107152510035414180701444010700403d0380d01d55642c980034071a040741817101002c010702c0214a5070031130703524130000340032214107030813800c110781c414440c0d41c50403a0812 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 436375935 1250 436374685 436374689
    0x702100c0c0f02060f030c1207020106030f02040b1201020a031a0a061707050c0706080402030c04050603030313060f020301150206070206010b073e15070c0b070c03171806090a 77
    0xa441e101181c1c50b2400400c000e03200c0e203c00980c0380d180000401600c40d200901500301300c0204d89021180c1c1e00c1d0114224240c5000f40401741c00d060310b401c9a5001482e165220659030310005c1d00b20000340040709086422078014801c11400310382c4800f211408540380341c1c4800008142158100500d07030502c00000c080500c0e1000c042009464000882c8400b40544103946501980c1000c9410307031500c40c500140507031010346040380a885103541c1d41c181d07490031b4061140304002c050010f50075603951203a8202010041082945c0540d030b42c4c01000004076a50000b0740c0a070803604500041141d80e00d40c0240344c504010304120464010383c00501410300720b8001c98031030940001c0840b400841035910110740710305208400a60034581c3c529410007510f60a00320b0b9941c4001c6800540d24190345030401014840c6ca2030040c40c0c2540c09074188942c180c60701c0038000c4640125a000101c5da02c9a8914070a040304058422003540c021640c00101c01700355a070188200804d4980d03e05112a070f0001c100c0b544214 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 436377185 1250 436375935 436375943
    0x302030c04060f17070f08011211060a0e0a121106130605070c09090b10060516120203090616060b0d11010309050c0d1a06010201022511090901050702100c0c 69
    0x8402d100f1445204c0c6100b5600002d460340114501d083c6800042d2070341030010300400114001c000000b549445910000c00c099810004030f965031910703041001007550011181a09001e900d0791030945648415441101030006c410306900900d2040c00c3c80884840006001341c400c50701002901440100550100102d1382c1c54200755448052520700040100c00c2034000c0b60460746044186024030840300070040c011400099000040c64644000701e8407031045028160201c0041d014060000308041001507040340c0502c140c0341000c248400160f600d81c041d0070340d0321a010b1802050405c2c80101c0c4520f41c0038410482c1c0d02501c1803041c4d0766800ea800000c0d482941403581c4d0300c3c840020f200f002d11520a400d600101a0440c540d2540341000155042c082018180203181c0b0001b4541c0d40140308a607100f65100008500314074903d0514034800303e519000716894000124401d2403900d42d03c1910303011328580400480e01d4541900028036040b01981c1c01c0d8000f03824151050760054012210504030385d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 436378435 1250 436377185 436377197
    0x13091a13051203070507060c02100c2618030a11100218040b0307080105090123100b0a03151805060a14040b030f0a05010c020f0303042001120903030614010302030c0406 74
    0x50300001d17142030041c4170014000310308100707500400303035400702e80d411700c1007020740c420404500b100030304031880014284561b405420300004c280d4248001d00c52294030020111000700c540b44405019400c2d0740000c0001d4010480d00c0c41000d0300200107201d144134030445035208505202e482c410307003548a10500781080c040e0f6503416030b06000da1402d20492000d05400300c024082400d04007941030082400c0304443c0e076082211451f080c00c0303c0d00308101600a842108200c41c0071418045024030a50100c94004181036540421040003100310b2000d030000e002611101c42c00d080340941d240155400101030a209540641040c805001c0d13901880c82c04a01c01e0341e00241240740040801d02d01348042c035030048644540bc0442d000c1110540000b0900d440a03400d40da038030b4115144803652130200b660001c0c00c524411101c00a480852698442612814503003d105038603c062070100321001e42d102580041d480e080d080c4615402c5001c400b440120030300c4c04514600c0d050380d114409002c0c03070082c6000c00007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 436379685 1250 436378435 436378441
    0x705010309020613060e1e06250b07022d07090f0608100501140307060807030218090a050f0601090303020316050c060c06010f061103071113091a13051203 68
    0x441805a44c0b5048404611342c41c0c0d1519030300c0c0500314000200d0014850119251200408900c0e01e0100c8201c0e5000380245050000b8194030201a03094074200c5231001001380700341400b040801154a01880640c0c024040c001150b442e2041e144c4451208007014805000c0d441c00103103400030b007032000c6400c6402d00003130040c0b00015a20107880242c1c490b1005124810721102c0c0554640d110390b04886420103c1c408402d1804240b5484450381c1c0300d0400810821b10002d5107990182d00100070319900c03080c00707103d003000d0000090511601907500c1c4400c00e540c1c400300311184255036155030f0410000d08001d03200515543e4001d6a9100301488013180da001c0e1000d04042010401910340f1040d0010720881d140c08070490466550303002445019014400400d001a1060041062070070100b003000240d40b80c81d00544606029030003034203c494000c1000740100c0c20810040c4070744219280302e600c00040100c0013403c89900e103034014041e2255061048081c000042d00022017403c00307a01c07540c01c552030b80c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 436380935 1250 436379685 436379689
    0x50705160305190206041a09100206060315060f0a080f101505060c031608070b01060e06040b09240703020f0607200c0301020406032316050d09021002010b0102070e09070501030902 79
    0x4040e647c883e140440f042d19054904101d018080c0195040030342e1010304600b540c00c41242d6a00050720800d400d50000740d5242c070b4007001600d02d2079220802130424007080d0100300c00702d003020460798010140c54000790035800700d0031018409140080d275959000d020140070702011310000d0209215861156800003407200018900b8403d440e4603802060001c0c0e0090061f0511001c150312134001103c090608200204140b070103820342200c00c1801400060a107420180a40a0399014450b05580409511a1904a4041c9101500c1c51503000d40ca0b003030300d804031854003038900110714815071b9203504810100055503500c00c0c801d4500e582d080e8070f003c181043d22005982400003001c03440790903500001d030100d01c081e003640048150f480484004180e0f43c0340703072081004807007058070102ca01c040e4020400003082d108001600c1e824000c40d000207000005a400507420041903402e076000f60351103c0d4170000030b60701441040010030300001c00d00403900d41100c400d901d03200c5038000c0034107056560204c24255 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 436382185 1250 436380935 436380937
    0x905120a020a030503191404051c020d110a09020c030a2a050a0b01050d05120307030f060f0e07050a0206040335010f06050c03040306111603050705160305190206 71
    0xd540241c4100049912818283e85039400003040071007103280310a844015520505141204a020b401d003641880d0501041202d0310100d0403c0480507101c0184c24005030741d400550040325441100c514a04480490500140b40d10940c0500038003441804114002c0d072020044a0304d02d4070907e000e2040040c80c210101d0306822003d095851250b2150031082001000502c46900f03e00030000c00c18160307600c004104546ca6041030090880d001400704d03500b40c1d214070300a950030665034180810500c000303111210403035049500030118014a0101041591035603031003c0e401c000545080b0303240218200c00690740c0c40000c2d200804200c2c0019004840400d810b20241006410f030354081d0010281f14158400d4030401e004101c111000c044000611501a500f11002c108060f400f860401e071850315035400905544044040c0c14a00700705190292104001c9111942d22031f032a06038483c28141061460902441c4003c0b1000c00ea0032014008203c00141e4500510300006100302900704070b101003069 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 436383435 1250 436382185 436382203
    0x9050903070807030e0405060d051903052b27081c020a0206151215060d06240909080403080307211406042003090102040e010306020307170106090512 66
    0x1541d607020912108055100517031398070641e01181d062105403100e10402aa0001c5128000e0140c0c0c09843c0075028175128007103440109000b81011400d08070210060f1008a0b90100b0b0440740d4910032801840e81300c503e200c0c90104080d0254645144c44074200d1720103040b5054400a4030325240441c07001d0400b60003641c0d440400f040d441c4199100c0d46190300180d602c6600340c0c0e90300c4140b4407454440c031190a003000051441c014000041c40c050030002020035000c1c401821141d0000e4000c80c1c04400302d020303030080040900d015070540d10085000c41c0e209400000303e811404165090051040110b0346074000e44003901d40120b0001d60341d8841c500180d43c0050f4240d0046440ca641000640301450705d0392011415a85540c0c01c08000c1c0d44840402c0708440d000440080000310340484e10f007080400b100a140d004403241c000614141c3c4030000038140e000b090340b04a88554000042020003540144407004002035081240d889505080b8041c00c1000301b809454000e055021515141100402c080e8507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 436384685 1250 436383435 436383443
    0x301020f0405041a090a15030b1e0703060b18010c0b010e060102010e010504020d03030902030307050a0b10050d051f1103130605060603040c031e0b070c02040e0102070b010905090307 80
    0x1584030080d0320314240d940c0041c8a010b200301e152816010f1809603480b141c2c08401c1d00144010902d41e0b481c80008010b10700100064000d0481010100003d881003080341d00400488540f100c071003411989820b000c1400514500030141010000c10013014483c0580b0381840760407400c0610004007000403140c0d00090b2038058800e00e207180c0002114030404075a01d0181d0000e1b402400071551112030382e07082e101c00703403030094101c0c1e8254591070201f48241d1000c541203200034140d83c034000e00c2e038640518041900100361001c2210b1800c1c00016140807807a04018002a1a0005110080d031901c5807500c480074442076100e0f8080c40c0b17918940641c1c0e8050440c103186081e88035202c0c240500b1202d401c0d16003400448000d403915011a409281030407e6910480e4440000b100c110b09664030303a040034100d171510500292204800100180c90429000d100701c0660790745d540140803900420082e07079885010310b6002d03481000001c0204454112103815075a050303001241ca17442b107100c000e16600c921301f0094 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 436385935 1250 436384685 436384687
    0xa23010309060b060d06050301061d040f03141b070e040b0f061c0b010504140f190b09040b0403080c040803160f08030c030709050f0a06030b040e2515051611030102 72
    0x1c1244400359100f01c080e80c2c0c055000700311080d10bd40000c2982d10000100c65408911100002c002500d00314400320654402d2503e03645c0c505803007c082c03001c0d40144140d140c2510702490754100c5c0510400c04407004101c01c001105103810aa203c1c003120702c2c8050403040c04182a074001600c1c0d9128010301c91403503c01e2101c49050401d0904154145500038090180300305d0600101459030702e070001c0c0607401451100384d60440d54440c501d0f002810074002d80208140c80c1c0390307003420740c450303840a88081c4201d0096045102500d4079160081014000034001c21018078140300078012100000203480b02c01e03580c1c1d003002c80c202240d4101441c01e0f01c1803480040c65418008108110100b030480a107004042d66154000240d40366000c009400950035640c07604140c508100b0440c0500ca80c000b03460000c0080c0000030a58541c44041b810550b64074184a03412900c90b031050b82205210016000030300c03214510443d031900e1100c00800622030081d00645d0840748580c1e26050100504c0400c2040100600071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 436387185 1250 436385935 436385947
    0xd170a0515090901091506061e0e060f030603010f0c050307141201080f0d0e030c0103180f03030e0c1e090601110706081e0f0103080c0a06020403110a23010309060b06 73
    0x3d107018180b404000c888020590308064614107540c007980081c0d460340e0703c41030b054100c0b0b00000800c00205002500411480280c1c004e41da4580c0b40042410707182c0a245980d5070f00d424403c3c182076a62203a0900c1d440c03490640c0c0b004086902c034055035040407003460180d4062000d50b0004210340a01503584100282c040000108581c1c000380ca150b1041c60300c425205c05058805d8180c41d03c480e448401078141e0800c40c1d800040b903210f680290a244c0c1c60318403810529189032580d5440820006046011981c0d032041c4417a0380d401001003030380940c42100ca1400f0f0356160001c0030225070407204924015041c2c03401241c0141c0c0203041031761100c5c00003c2100c42c0c3c0303650382c80010802d0009549600c1c40c0076406001084000c01030700482c0c420359007001a240107134696580c00c089907126001503801e07405030b03480c410300003195400144000c50085415005982c10340c010000181c00561014021300e010511800000d1481190100d48482c2403d00003011b46140c201030000d40032500819038041c5c000130710 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 436388435 1250 436387185 436387201
    0x303040317030703050112081813090b10091a040b0607021915140a080405012711090601080a0e0a020d081e0421060605090c04080d170a051509 63
    0x40c500c241c43e0b0f43d41c203010316642c410401c401c1203215a409000150b080080c001e01c4451140403d0181c400a0000c1900e540b15204040c01c6174108031046411007202000c0c03100d13018103a641c60b0040e0080b03c0c0c00300140300307504040f80c4c203004000c803029000742d40781d040a003099900d00003911904e41c0c019003507809420351a04001030703120150003000402030140da4600f11041c0304104129001c2403480b07034640340c000240c0c030588080d2030050045800e907484035202101c0081400c130b11002030800340075004007803100b0320300800300a440308007181c0103107111820003450b81c0e8801c84007500451000c030000707081c14080114130308014001d00c029410068035000c4204112a440c010500e100103036a002ca900011404040c150748076901c100381e901943c189281080700080500b5083c814400d190018240f9501e9010500001f422284100106000700c0c0410104105220031341d41c0340b40742d25011180400e0300d100340c1d240c2003025002000c250782e0744002550111403540d0039104002c00910f80e241a2900c014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 436389685 1250 436388435 436388437
    0x301030f0507060e0105160507030203070605090102060a0b1513150e030c0a06270911090102070b0703121d0618010b0d020306040813092412150b0303040317 69
    0xc01121a40700d0032900040b03407032240c1144142c60505030f60b0a817030070701441f4092070380c4070701c034841960680101680080166000c1004500829071620f8103074840088900180c1003010003041102101c0c104407040c011035488440035203003031110705086030310745040c1c1c01c0546560390650000207128084d42030541a164022010102c0020100c0845103422100014044020028414000824102c15002d400700903001c400035821800d000c1e0ba450041e988003503601c01c1c1c4802c40c46141a20100003090061940e06002c1c0c1c4018204080b8017070f00c2d00101c2d580c028202402d03e24034800403940c800075440509951000155044003c9040380c006080805800b101014803a00500d004d40c42e0100a9815003000200c1c114915001405004155940d03216400254000111414030000083c40803c2e260104e116030544120b0069101055000c0800c51001d010180e0704001020130302c40c2e0000000660503c1002440d1301c81c050003190f02e4441e03001103840d5008580009100040c2c180c4e8003461010564 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 436390935 1250 436389685 436389713
    0x612051c1b030e0a050616020105030c0c0102030f01051203040321090801092415030602071a040503040801051b07020f15072a0815090712121d100e040f02030103 71
    0x480c1901c41c4c2e070380e03034040003458403070900420303c2d044106501e100550b00070000380d50b021803003000391490170711088086401c9901c22207011554180420040c0032506000c661841305840020095141c9800c40e00c0e03081c0c91034009102965100c1c14204400300c101d1180742320300014250200280314903119407500d200d0310000701024104240301900d14180c100034074022480600c201da0404004107003075407181c2c000783d4403844040d504020310039040c000c7c105503035141a100724014405107885500f8000c10a00b0b40d9005070880030510307011000814000092001c4074a001c2c0e04603488280f501c0000003050f034008160070515500c010105070001408100d01ca0154150320303109402407222242a520191194076025142c50f940c80081c1881d4015003400303045410450f01c008440b01e0555039211964880303400706040750030079660404000d6503034100428066407580f01100201ca0030000c8007040020003280c90300307000c1222801c1321041c1511140e00c45030b0318a00749078040d59a903031242454040e1341c0c514 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 436392185 1250 436390935 436390939
    0x1020a030c020d0918061a030114030a0309050904060603050d020a0c0509010806041e241d1221010f1805040b1b1c0506040612051c1b030e 61
    0x1c03807184101c0e10105a4420f403640715100d00d2031250900d0b1000402042411025012940d00c410100b80c04d02c44060b904c0408140ca4806644c96042c0f20010154222408120b030295101c0051070f000641c01262040c1919003e544c1d000c03103a541c0e814180041c1005500141150041c0c0c2880e9030025400704669444030b0007414071400043c2d49909100300c02034244100207258002c000403800140304091841e211585580c03120080d910503450b820b4100c481d205002068110030342071220110054041d04500400c0881d800403500c200308110303512440c0202c0000f191860028440502d0333129141000364182600014000700e68650013030b840d600c0030314002d000300220314a4600003003d50303034000d0500c185e0380b00701801034a03291052440640100824641744440c420704c181e55800c40c1004801340c200184d1240070440e41010410300046039010380142c190300c0b41c201084400300314000341401d4032010098096003414030f580b5089903910010030000d0f030413004001c400018035500850701010300200b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 436393435 1250 436392185 436392191
    0x13020901120f05010519150e0a030501020d020702040b09090d03020a050c0105010f0512070609030245010803070b04020d020d021503070f030c3009050703050601171902061b01020a03 80
    0x800702c500c100c410b15100d020021f100e81e000703602c1500d00c40d2940401e1840094001c000041d03c80e9201c0342a0b800a4903d00b2916074040784401c1545000d0080d030480c40310540d5001e00b035090082030142ca0780c0c2149501070525030000380c518a2103114104070742004c40801d000304280e5071140600d00c4c01003c2813098a03c544400d103e04c6c000894007050300001c56049440385030b2120b19660034062186854070001c0075002d80b0483c00a04070307041a00040c290071041d44c0b10070b50440d4005d8814894030043e000801e5070351060000700e000a0b42e01c40401e800071b804031052004d101117440000c414801c101e000039002500e2030202101107842801460144000740c49030381603100075804c110100c880c40320061000403d00326010321000d020600c0c1041c0c040000b0181c11001d612001c100c800d030780c070440d02121a540490780c10420320006010342030141c001e1021070120b8164030b110340d5a9542021481c0345803410f1102402c8119a04c4e102100c18002101c0079002c905455441024000d4001414402c0070a003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 436394685 1250 436393435 436393459
    0x2070305040905181f060b03151005090a05150c07030b15030607050f0a1206080c0301060902040608010b1b100204061b0503030c090301021605030304020a09090213020901120f050105 80
    0x13102c881300f0340b8180c503143e005051841c4c004042031010035140c41c55568059940001080c0404810019842825400c0303400f4030b030404400078044460891404902003190a110381c0c051607031502240400c07241d044510188400d00343c0780800540c0704504200800e48942c2d0300001c20461031110540c030804030455007040f152000c00a050302c0b840b00300c1e200d1000600800a080400100038003922843c4118030700a20a00440d03040799040366a00e0b0003140c0d01c6c0d4851760002055190900403100138080313240c0c0650a1a00d840340207040c0d010180903034014680d005c18507150414481511545025001c03086078022018401804005d51040c040c03040014220300843e44011980d0401d50026540540203524561300d0030b50b44841900304c0c10b0342c01e0b8555020014520705020740d100a000c0d4901410140da0f590034688108a43e41c01281e02048005061411b454090307070315140071181d030400156000d41c0c1d8080b440f0040715401aa00c921004040c9048110156200c0c01c0e880181641c4e001c3e222405600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 436395935 1250 436394685 436394701
    0x9100c17030702060c0c0307020a03051c0e060d240b030a0e0d0f0f260a0b010804050d03020d02091e0120060a0c05040506040611010513050c090705090402070305040905 74
    0xc40116042d002503031018001c9100c84405c0002803801040000903241081d2007a0300141081d03401e94000e0f6a03986c000302c90a0103100507421155506820350400010204000020401e580035800d0103441041c0e46a540d0720707054003405802c5400c06401ea0000c1a4103851700d1700311a16420a89000d4141407030701500586009001490600340102d94440d2000305020340002c840500048103000200b100141c820041c0101130441006212040c10b003890b218a03049520310100d410880351103042095840c00c0c000410804a4a8030110f0543c3c80c008daa0750a0307410401c4064800e91100ca50440b111480107160b811059468002084090b0b0314040c91a01c050b01003c9014513a1540c0c0300340350003c00c049040f889440d4400c030418075290802904013030382d502c00030b985500240c3c0110b010898462090701c044100303226203640290490a980c088082da42c41e01540c03228858640e5000c3d003040404204200d010300d09580c9158401042076540701c2c11407900600e141c20512825408505000100b4548 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 436397185 1250 436395935 436395937
    0x4150e19060503101e020f03150f010906030e0c21010b060307050f090d050307050d08010f060801030809040623190302060906070f0c0e06010e01020d080105010f0509100c17 76
    0x1220014024079040e102440100f0051a188010b000101170301040a0511031103400901000b212605505440b850101d020101520500f480d0f54803d00b0041091401603800120341c3c4c0580e2882e00d40010341e04001c6444602e040c1810b03841990111060114003070090408040510300300c40c4500034007082184e0b001f409032a010640d90f01000c500144500d100800ea84009071500c401c0051415202e480c0a454045c03d40d8021801940e158000310155a4600d40050b00c0d1401098049404180710349801c1c40140408010b00006090060000300516556196003080001e0104414543e00d2700e9440940491702c07039480600c5d540918450b011811000c0c60b041406d50440c1d4018140f940f130407100070104945580584000c4840c650010722101c0840c1224201c48084d02c500069001d25003080f10024141e00c5680c07844038119400200b100e42c106502c40c1ca403504450082c00e080000760000c880a54035805498200c91300100001c80700701c92142c0c00b44030a0403a500404100c1250901a02c0a800c0303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 436398435 1250 436397185 436397189
    0x10201140c220306060603290102030906070317090304091103400f06050c031003121b080d0608030c0c0607030c1a0105040b06070302070b03040204150e1906 69
    0xc1c80806000510505201d030498001418401e901c00300030988aa69410440b8603a801c0140000d9a4180c40651a183c1c803900740e8004051016081000034183c0000355a031046032201800350310049100401c1600851100d01202039862a080140c909a044180da0b600b052252070211810011030025010207001168050440c1c8100980c01600000c468002e20200c00c0240d24001d0790010700c2050403512000c51006540f080d10440f00031802c50801c40b058500152880d120f03914100305200c1c0503d201403210085917480840b554800d44452015600d00841d00b070011401c2250600755801c001c0e51301c004244c0e80c900b4903420030000b40c98118a6039070b4024811841c2c020381c00005020402d242417405000224420310340402c60003490b40c1e491000312001864115410540c0c00103100c6032030203000e01c4032618800e0b54100e007004180d480003540d4110701c4c825540c2a401c00000704065455507000214040b40000070100405d80c0ea50b450a1200001c50b081800d0790b40e9003e50702800035407070140c001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 436399685 1250 436398435 436398451
    0x3030b0f01080f0405120301080a1109061c08091c06050f1003110f0a17060105040b060d0504050a06020a110d081b0d0b040e0304170f0a150b03060f040201020114 71
    0x1c070343e10800001c8200074050419105480340400d40f040f4884000001c50181c50842c002e003000002902d81003200a031003060151007070514a0420050380c88502c0c0185040033070800c2e8a1808003507007000b4403a4415404890707004221079850710503544115024900e011b100301810040c41d0740b240c4440f4021402520941c822043c081d10400101d803510790300703072010300b002040f81813208110400184040c096610810400b040e200c026040c0040600031340713004010a03503062000e0130000780050b20500c90302013058110303a510307070100301401030410010401c1035000c20119528204d10038003408000b6030401220180c03158010b25000c41c2d104030310407070240607a44100700084900d0041180640c2042c10000e03070191365650300000503603840c0580c1481100d02d00245644078103041c9040b58030180300802030308650000007035507000c40c80040c51103400d58101c0758104c44a800d00461402038004100c2442e0302d841213005010386000c182c68568080d5100342c008000260020b011510301c00d40807500c0d10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 436400935 1250 436399685 436399697
    0xc1203030619050a060c0b06030a02060d150e0a14130f06090206070203010f02031f03080a05030c0c060108010507170f1602120f030603070f0803041202210a03030b0f01 74
    0x780141c10180e09010240441d00150307002d00d80c03100046810000c0981c090000110b61114103802d01880d1000940c02c00c00c00e9000d0080d00b001c81e0041307401c03440b0b075001d1a48425075413560030010b44020480307407000c4e0441501c19119402c003600ca900c090a4520507000c045c90a1401051550096a0440300f245500c42403003040740d081900c038980100b00d40711f800e981005041283e2001aa0280324071102c914500000607113900b0111710412400c01c040340300d426039880100d000d00100d82c0c180180c070480002480e00c1650303551078040d0041e0900800b489503419102c0e10700003007488181900064843c0d40a56138400f491150001400300e411030550344e881d840030700080032541c00314031070107610146103150049a090602160010307860b580001c4034044090404411b000c0c82c0c2c070302071043c40020001110700b4040307a42400308440c4c41e48a10310440751007000901a5100315190341d411614002c2c603070002e0080090f02d0140680c1caa440300b14040f0000303454400080000e117410f20584031008010781d180303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 436402185 1250 436400935 436400941
    0x81e040f0609050f010617030a0c080d0e030d050a0b06071104050c0c0307050a0212030a140913020f180306010609090e0705030a08040801060f1206020a1205070504080c120303 77
    0x10000d000400505540807074541690001040d000c101210710035900740000143c0a15007021000e84901c080000c260302d82040100d04c2c1c02d20341c441c004120694000304900d6031901c4d48001d01e4000d1600c14040c0e851800040f402503004012503105d5031041140d04014821400c00d0300420403d0b01c1055801004403401c140004a141401da210035444110002542e10b0306940310b510710b156400031a02220036600044a5004504000c2022030a0000327004c004c605240921001410412207030b0305014003060080340040140d61113440b403903484456144119511000840142550b80c0080ccc01710302500102c59004c850b9040c0003418904035009a42c4003110b00d400e0951800103401103090b200064410b02c4808501650140105589540728441140d86c0741d02c2c1c201c5d0142035810701d500081c0303062000442003180c1c40034003502c207512540c44000140d035480320380015140d80a03000302c50303075041d4682000c2011031a00100100203596041003103440a500400070050780c400c800010b160160414404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 436403435 1250 436402185 436402193
    0x1020306010c330b040b19060f120203010f050405090a0264030308060d0305120106111515121911040509210a0207090f0c081e04 57
    0x31050040c0c0c40d8103c0d80c08080004899515403c01210520902541c60004c25028034251080b003441d184199050a408181110b0f1800b104800340301d03480a000700502d40a248a201c2c458800949480d0a803c64032561070b9203030340d800355600b070040d41e0040c0d281002040b8544000900d00c1c0d40254001c10090040b4014081201d040c0000106240180c10b051400b1010494145403107119891425044600300c20441c1c1704010207500003110740081340c03009420700c0417a511108003a0301503011b98140714804103502d411280c500c582c600051040148200116240303074085c1450340c800c80302c001214200e00f9100e071400d00746103050360300a010a81140c208a05818124100170f001803120090f110304958402013480c240d2400142201c0260062001c010350745464410b49030443c40d200000c100b0003094030201480d00740200d104c07985c85200400c040d0b006c84d200308101c00c06040d41500078040c40101130920300203000c0d2030784090b01103101c00380002c2e04141620211006003500041e00e1205851b1074035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 436404685 1250 436403435 436403453
    0xb1c091505221b090612020103111303260d0b12010c1e031b260c071b080a030c050607171504023711030a2604080706060801020306010c 60
    0x3d03001a540b40781da001031090442e204d044024812907140510503d014400102110107101c0d601a00c80b0083c045d1002d1140414038580a490380f0030001122a0070701c0741110191000c520f03403010a00c000281114081c501d1b5000449403440958000500d071103560542c03420385201c15010304c0040c8512203446a11040c9201c800704404440c2070020b543c0d11003440360165091203003d041c01041025000c141d20201d04513842d00203142c8200191a942070011182406105045c0003a00b03130082409001159540f01407500d000f042c0100484e42d03400850f207000342410905400540383c81c01030b0000900d0b101d018001300c4403820061005810b0b15a80c1e40c0c18407024200c020310150300700ea428041030007000c820070580a80881c0c607100030515540f10805140b070030f0341c01c04081410016046043e441d03484001041d01c2415520f42815200d443d01d09221a00c8052050a41e4110345011814807080c0882e00b401010140e00440c000d0060315198001d0b00e00340d110554a0340d00003041261601c010482e00f203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 436405935 1250 436404685 436404713
    0x90c091f2301033909052b061119020c0d02030606280e090c01030606020d050702030f030313050f150103080307020c0901080102040603240b1c09150522 67
    0x148461101d101d500704045010040703040c41542c1010341c0c641c8000700302c1d044a07031700d03005140440d85d000d031310905180401c414408200008070301045044006c010441590001300000d404800000c0d02c1e10303402d0340d4249851201144000150140071480c0c4440d00340030420300c60301d03030700a00140030071344690044c402d4a405010244010404221640c20507070440304d030582c002c01d03018041108070700785405564145402403041070306145c60502c08000e2540c0208010742c11802504006480f5020790002c03904001c1c0c800401000c0e40400020442c501c001a0b242c081c980c3d000307a0440d00541a407218440d03a49030510107084003111a5401000003c0084c0004d6031701c02c1c8144107581403040c1800100f0002242a0031900450750081814005990f2600c03551201d000d540a1450002502003100d680101c29401100e20302180026840c54180d40700c86000c0019041d000e0410044135075081c0311180c004c42072206240a41404003181c10000c44045100f2007001003000b0300c0a1580301d41d10313030012490b0f070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 436407185 1250 436405935 436405961
    0x804020d032601080105070906030920010c0209010b1b030a2a05010e0a1506120212070e0f010518040b07030b0111191704081005090c091f230103 64
    0x30800602c01001d50445680c001c2010000204450500314000f411a0906070040c50425192098940c040740030500400600300c2c044c2c1d0700310481030031400103c7d901010664007a4000741c8000001610480d20b00c020001c05002100c81d40c040386080c3c0e4116101d2103401000301c0042c04100c184200ca082c595820704000410000b030342e510011366035885d0f02b5101d00111100c220f42022001c0030a0020202c0400c41448076039100b081010704000340e40c00300d09800702000c3c0c050700609840018040d020030129000e000c040040ba9986c1c0f41c0f403a00c80ca2400424000e080c050b11204044004240fa1032039140e000e550301c201854103903903902c1c0c0200c004004c503070b0456041011280d04400b90340d00c00e005440340c10301500703410b08105481d818410400c2400000c0745000c02c1003040304000200c00072494052580712008085a241c40301c8001510346030322240d0040c1d0106880c03081c00140110b0302d2144640c0356000ca6102c0f03c460b40c98a4180e440032811460f8040c500c1e5810210700c42e907100c0c2c1d204510020072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 436408435 1250 436407185 436407227
    0x60723010c0906031107150b030105311b08100b0402130b18040203091b0f0a060809010608030412050606030c130902060c060708040209180d05030a020c0d1e0804020d03 74
    0x18a4942c08047e140c402020589607a6407042c84d105800c00780503243c0d200000c1825414254500000d00c80320206403101120781858848115080000200e00350312580044500030b403045880f10401c40e1921013591b1080102485e000e05a00c007818203000740d5003182e204503420303105e603483c289502403594011490068649100f20350003150760303a503101850048000800034452101036503500c03441039021700d400a2003241a07142c0428156580380c01d2800b03803051464800d90b035450300c030700403805002181c00070380c050302000c1404982c854005400501303850140080310060340360b030024181c541c660b4624107900f003040408070303103040c0b032203504103002d0284040e242c140360841d1010140e003081c03001d841d500001050700040c082176285c000b00d22508680c0248164100c14034482025035160341c2d894694007401004800921341c0d81982e0306480c03c180840003610100065000f0080030001d00d178104007a9980754214415a5030703c145c240b20320550380980702d03003c1c00e010307510195401c140c07103004180d070100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 436409685 1250 436408435 436408447
    0x1062c010f11010903260405030d0c050d0e030a0311090102060406020c0f060a0603060b060f030f070e0607030c060e07050607060908211005180601030515060723010c09060311 77
    0x8804d1091814841c060f94640d03109503c610181140910901045007010300c0ca00280408140c02204a917203085140100203880d110940003650a0300848000030782c0c0a29084504000030404001803400490a076010454440001004480d034021109a20700590098000400051f02c1c0d40c024501c1896039000c40b003010300405406803030a2011203008100d00e480e40d90030400c10400d40240c0100680c200c036810300b0b0100b60311141c40c481c00002c0020300781c560358402280e21180142e110010a40c40541130a54411507405d0150004d0018141200d00a00c2c0520000d00000007050f020700b6100001e0006181c031059481d044003804620000782c80c0042c01f000070341f070341c45508441100102e00d0040350265914040071014815900350b40100d020f1920450000b10036150700f00ca05030b2103030f42400c0c00145a22031360400c120a43d14110380f6034201c54001003201c107004010318021030085c0b18070400c07840c504441041c2d5003a16243c40d03c1401248601009000017800303504448640d4608611042c1001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 436410935 1250 436409685 436409717
    0x3030c0b04150c050d0e0f0a030e040605060f1210060909020f040e0103030210150f05040c110f03040305010e0a021813060614040f0b060901051c0f0501062c010f 71
    0x41c2d5036240e80010a100154400304070091740121b440944001c0050b14060301102d0002c0c5c0c0340c1c0703200b170310003020170400d14410071071583e45500c0720b03020300005040d1549070740700075012098031b5114405d01c640c01086030000a882c200922565001d0741d806640315400d0301d02d44070011020350020342d403901a0003800c2c800800ea841c200344003980294000d40c010018004560f0500c422148115110b6480c0011840d0500400171404081030440d04183c0e400200888690422154645034a80b020224000c207030041d01c019078000040c1c0244e0380124002c0203003030000d01c42c1564940741303404000e400c65403480400c400e8031800e17070090781d00c106070810030007000c603007640c90204486042c0c0000b002181c1c00c0d15041c07aa41003d00c651650300601c48010841d01c20390000040711805124085030401c00001504105048002044891040841350a000000c0c18403843c5015000074040d42001a2401d400c500c0380d00f81503040c50403c40160204694869500b200440b401c0da8407070341d002c05000701020114990 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 436412185 1250 436410935 436410941
    0x50d0602120405060414010b010905060703020c0a030b060a080604120c02120607050a08130515090c04020d050609130f1b030515101409061e152203030c0b0415 70
    0x40f031046024269900c0d040c41c014a42d0540c0340e01e00d820980c9081c6090006980144540d4103445040f6a040d440e2070075403504900c2c10640c504101d8115400c0303440002000781034000c283c0103141c00c070382d01c000c0d0359120003a0503661030044801a05150300c040c0321100752801072111110b454000742000c9102100899054500041594400005400080d2800c8865804120035400591a00e103168801c603054032080e5440b841c030030b00400c1e18010100881d003006020050711802c000c002d001036490380302804e8450000e0000310b40d4140501d10078400108030a20064180c61420740c0901c0c8146d20007201d80722950b0050001d1142d008504200d06c020000c00d90810070300c40001c05041000a061500a42c0311807640340c581d10420b4001140c070368140d62039850241440c0d01100c15618040c01803250014010506010019aa000f8840c40d0311401e2192020000700503c0300da807640344926281865000345111750b180720150006104003107941c001001c05025030b40140c001e542656100c4a01e004441c11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 436413435 1250 436412185 436412191
    0x90901030f0c0506120915040201020604032d0513060e06030a02030c090d0f020414011220360c0304020127060306030311070f0b07050f010504060203061903030207050d060212 77
    0x101705810400c010306450204401121102d04807a0455942001c0d40081d58840c0064802400c4c40b00100f8540a80798000b1015035111102c085200e40d08224076030007800c0e03584214a070858030840c440700030070329030300035618040300c8130001e0b000034a540d03038110800000350130140c02041004402c0000d507400d56545240c3c0461140540074048150003e8030402c01242c29900141003003c4d444001044113002c0b584120040942290341103c800c1d51500303044a2002643d03980a500c03401401805000403032031501c07540c00400c0e05002d5074291444039114101140c0440e00350124880810004006520030b0000381104d8001d4010a400c19030f0782080c14034019625004040020f550b05001c01c00d00d6407056403030001c0c4546d00040c0201038100001e0518101240c001c180721803400042010030402c0030800000303031b02050002080f240c00d0514185000e0341c03054030158070610040d41d1348596165022500401c5941c15001058820b24041c117200400b0300100e401d4420550070301c09906026414090148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 436414685 1250 436413435 436413457
    0x6012103020709090809130c14090a0308030106030c08071119030216030605070905061309050c1c1d0d0e091509100602062202150c01020c0a060b06090901030f0c0506 73
    0x11b03c803000c0505104c18a00c00c00d90480d200790801d42040c40b1240c0100c400d42c900e0458149060faa801410045101111103a000604030b0400000005e03015501d588842400e1410307075200503154960f0700b001c80d005400000c6100094012000c00d07034062b01980c80e234807102440b900544031204400c0044801d82c407284e174801da4240e40c5400801803203640c0810080017a0004540c0b650914082414605240e2528003c501601d03a40c0c201145840101c4000c4d6406a4240122080b1021908200c80081c20203480d441c585550304000c41d208041021881c948044d02950300c1c0c0c00d91031899030820594110144c049020b80b00071140d9050070b03480e40750340e4522801000c030b1140b40c01440c0030002071600740300420300c01c610031441e240800191091040c1c80c0080341c0403a104800c0e0789a102000c1641e02c0345c1d02022409620001d00e2050880011403417100460149400b0080241602d05110280c85000002544241000018800034031507545240383c80303000b11f00b081d1000351500041240c1b03620200c4011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 436415935 1250 436414685 436414687
    0x1403040f030810350a03030903090b04031a07030e12120c04030803070c1109010806071107080c1210050c0d1b0e060306010c1e050708060121030207090908 68
    0x9418141c1050071681c0081c10081e94128070f9203020341903140c2d20000c0783e5070b82152912001e40e940c8146246405110001d03860180c0300301d04d40514016004100004003200072861034640041e609450900707480449400220003110b089000101141c0184000c26000130303d5900d50080b50b40c000200025803030504c903262410398407040120302814008000740101e051150401042c0001980c1d10f0940b6000030b05420107010400e441d252a20715031540062054016007280c0c000942003000184550244066483e1140380c8200d1a4449445403640d001e001000da0122288508a0420300d003d2200740034082c098038045144100050207a90081e07032011101c0401046400468416210ba4007140d1006040c54004c1f68031404060305004140b02243c1c071030038001c40090784c1d0764010001c41e8040b503480f07071450720394030000b12221100c40180b00c0705998510a00c4004500e07004002003060503148080655600c2264846c0b011410b241c002c2c0341142140120b007000114140d09020314180b141c4550291 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 436417185 1250 436415935 436415963
    0xa050604150b0d0e030702031903021f0603061a09060d1103010c0f02070801090b04110418060e0d022a030f030309060613090c0b1303050601090b01081006050405090403140304 77
    0x110082d200c0700c0131544079075041002000010703031f40010000c4024802001384403000c40b01303040983c00d01d143e20600d042c0c0d1480c2003c01c00a0150740303601440030384c0d228030b00400c1050a01c840f0082d0076560300c42c0040c0c106180ba00414030381d01e041480ca442c0d10b880b4045015042883c1e17000702c0e0a442030300404c400030500c241c104901641d014480c0d440901000c178020440c40d4903644072003041040c0580041c08450000c0c0200326a030b00c1d81c7c2c0103018403003c01c0840074007018803450080300078040c00c00c4000e902c0c000c45400254207440440c0300c0e400d50900303000c102c12034070101c10310034010040403400552522545a0961180c2824000785101e01901c10150405107030083c20b00c443c1100c034a0702403004610702040c42c000124250b041005560105d150785441b484419481d400c00071030350308090020f01ca54000003c030706202e5004020b52540c01e030703074400d81d9403030380c001d07215100049005010209005220a0055013400208145e105001c0e10304400c3c804500c076070040c1581e200b62801c0e00c01800c00408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 436418435 1250 436417185 436417207
    0x605090f070804060b0f2e050403050a060e16080d021e0303070e1c0818091b03070306120f06060e1b0705010605040618180b0a050604150b 61
    0x101540c4280e200c03003a10a80e241c909402455000c1c003c0c001002ca698441580000c4d482e24090070780d81c1d06019000c0500c1c4070001403c4817401030b03046040b802c201c03a0380c1c104942c0d03180304509440c1241d600030020303d42c1a86c181d88a8010b4150900c041c009445400d1a60000c604da0756105401444083c0261000d8081000700a041c030092880d40c0c5171440900303001c20141341c2c00100712a40881c3c00c0c501131104030b04000020f02411800a528402c1c400c415190000b44140e00c130040c01200408412080104210014040041001c0341c0710640341210b00880d40030f070181f80c0011a800300c140d2800142a0f45c54a00c030b1403051031244001c0d503c00103040700d6541007150074400c02010701003841003110700f0f03d810151950b280c60304488400005e8004600101004400d4006030080c201c0200240705454480b98130340149450641044a518101807810066104051000c03820f10340140360b0449554801c044140034000240c8129041940d40c0071454401161401403405041195011a594482d40407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 436419685 1250 436418435 436418449
    0xe1006121e0c05040905120a0216121101050a0509130c03142a0d1d1501120303022203060515030f06040212070e010602010b1c030c060513080d0605 65
    0x16001241e501406004a084546444100d543c2214040380d200fa403860f143c0c0c00d182c2c6c984890786c0303154804a0a030704da258010032100072003040906803941c12075440b4801c1d002900a081d01078000c0c1d0385030f041000d140d4030030f80040200c0d1000d810b00318580040c6102160001e980d030300148c04900c0d0755111790048142c0c1801a440c41c80f0501d20000418104620480c007100710800107070300000c81e004403558050b803c207001d9402841080c807081081c1d440c66049134011845401c4150024000c3c12820b86102c80c1c000b004505848082440208074682650140d00030b62003d10303912095040350b69107544c0b0101c1809290b0203075114032404915030a04001c40d50900745854105881307a00702e403024084004001805561164040707504a030b42201900d002420958950061002c41c50120001715640e50150031140c05182c054459000880640b403030641d0f490a881002400100200b00c40d4000c1480e41c1c01103600000d1041400b1402c0007070356038919985d80008008004552035040400551034400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 436420935 1250 436419685 436419713
    0x10030807050303060109052e1106012c040c1505070209160305130510150e1006120e06060409060605030d1d0102030a0f0503040c030c240201021306030e100612 70
    0x41c56010230f01c4149009202c0b822040b550000c135a9402440e080d41c0140718014107480c143d15441070b10b0003540c54080448040c03521a0f01803164034180c45440e802d07a4000d0b0b80044c400c1e40c01101456246080c14214120034080b02e005008104041c0140300c056a1060445405019440e14808684020382c00160031385000419107041c0d40c00a00345e19010480c04141000c1e090702c07810002800c07500e0000383d81541c0c0c1d680e8104490351108401084000640d080d40740c0c098805036200d402004031100c0610b8159501600104c1041d0030000c00300e0107509064108081c01442110003180721916940402e103440405204040060384203000b0310000700d525070401e1242042072018501c0d02d0102d6401a00000040365450104100000010140300540c3c4000000e5036000b40008103166803880e81c6243c00481d0302c4001401d02c8112034051541d8014401c0740c00f030725804a010001680740090660050107200110700c194002c0500c4c1c04200c821500c6184060140f440c140492050b65040910010020b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 436422185 1250 436420935 436420939
    0x30103030e0d141c0f0c0201051c0c0507051501140d030309150204050a050a0e1f0b1207030f0902010e100201061203021609050105090c1c0c0906110307080409051003080705030306010905 82
    0x100020350390369005000c11b81d40b54083c01d1081d80e07440c0d4000900d402244440b04040c08500d801c090280c1154000020200380f8010b00c21100c2604044400c15914070080c0305c0c400f44640801100d006034140601da401c400e600908002540e0000c1d40c0704c5000306c800c000ca080044560001d0f084c000f5213000000c00c0085e060540351804418101180f40f43c0c40500507060f018131041074900252204070200703119018141c0260030b0b40d00d0308400080d1440412089d0764640110b410308100000550381c0748581261541c0580d580503005483c4002d201c5011040148031045540b92000840d0300041c0240d00c41c4224440e030300a01031403121028000c42480d00d5045511000d0500004005c150349610815800c00090101030ba80c0f4220301c1d0140f9011010341c200743c94207504202e11007100302d80012140d01107a03d1612091149402461642d4aa1007411001040000203020030f00c111401761f8000d42d4042c04140415440755181e07115410580c000441c00c41d00f0358000401c001040d680020820f00420702 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 436423435 1250 436422185 436422197
    0xa050f0715050f25050703030c0c0503010203100e100e0c031e01080c0103180f0c0509010b0a0c081e0f1e0c0c04050c0405130501031a0606030103030e0d141c 69
    0x100841940b624462849505213104814500840e220850158007259503404030454900d07641da4900685203080300300c402c0d1604800100300084509044c002c9922504110112030700c4117007810740c03000c04520082d00401c8800d007082d801140800b0038250f20360044100c001400e48910703100340c00000e02c60000242d0a100d03c1c41500401c00404001000b0002c0c20302420b01040c424072510f5440d59800722023070098161000c0d8141c07032080c0070031444c00d5815184166403180f0701d61380b01d04842000b4490389000a001506141d01040402c0301000680203c020101f0800112101c40003054026000544d078040344410010f101140040c8070a1181800a130b5002c0d0b49081c00800c0740e0391901c5950580c419400356844000184142c086001100e001d410028202c103445000303080000d0040070240412200014429401004803607000462845000f0082c4040e103103a0840e80e0803114140d100d2115500540c07036100303241c0011602c272181c500004c58100140031410342d03013030900a45407040c00440c0034441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 436424685 1250 436423435 436423447
    0xe0d08090330030703020d050c0703170903160503090301050103080d06050f0105031f05031c031104030c0519030204020a030207020f240f070606121214040905040201020a050f071505 80
    0xb00e0709031075403003100d0a11030543c2c403591510b02c1038020384220856050003501d44004c1100e00d80c02c02d4003400c280c0d8000d40e078001000003003003a06c404040c8280d031000e280342c2c420f0048440c2c01e5003540c0d125583c03d01c180e083d0703400c0c070348400d000c20b007550004c1c0c00844520f4408211501c655960b40300d048006c1a04844155070b44207000300107012440003a180841c5c0c003103c0140c4400d65040c1002c204000c00001d000c4443c00e1020500030003071686001c505c07500090a0070000c211041d0103509036015650010010460399186c00708010b090210400c0154100351f007140c000002d641c40c1e201600102441e51809030fa47c803981c0c410401342c00e081d2000c180c42948104000c21011007407420380419803800190355541c503100e8201940880c0100080101000e0400130046180e00c00c1d0b400c2c0e81c0762103228107107445408054032425500203800140010200c44180010001d01e401e41c0c02582c2c1003801801070740e09080b4161689404c0c100c640311801d0581d40712203000c0041000b00c0b45201040c111910b03103241025 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 436425935 1250 436424685 436424743
    0x15050705090607051c08011e14010509011103070c03021807080c030a1820120c04020a030b06030a05010503070603182a06030c0e040e100c0e0d080903 66
    0x701038480c0d03150107920041052410054200940040744010400d940c024900100004000d55024000c601e044e4180d1540d072100d000d200340584040c0c61400e60b5600042101c0303c01110b140d00705400c002d0400140d61030040309080c003800200225402070689003015401d500611604400b00401810943d0f107501c01c00c00015400035440c0c0c1c00222070b0000700d03a20b40b0f600c003506010b402364401d44c40c420072901740c0e840101b10050400c11b00c40c12a12801e40010143c0c00c04000401c507003035803000e003580c00000d03a061191400358004c159060180c00c000034070f07031584008190503030001c4410f130641554600040c4500e207404c1003040f005008078507040c00414110b508c08019882401d400420014080c40000071701114107060b44506250f00f00084101a40c41c83e004020f44180018407010500803440f058050400d4054204001d8801004000c1030015042c041d0092a0b40c8803d03a0070054096901c06595541c0e85460840a01034001107844083c43c00401d400c000c0042e0310460f01001e42441c1d8094a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 436427185 1250 436425935 436425937
    0x21020d090e1503070b180406050102060f04120201180f050609071d10090203240d021008130213230f0f0c070f0308090d0f0e120a02040903020102030415050705 70
    0x2400c03102c1051401080d040841d01d000f04541020481d000c1c08903440c00e20011040704021440402c96044c00066a56401aa110031003074900000c0510b9a0b000600130a0f240d42d8404182207562000188901c1ca081d2001d46059195400310b0303c18100c101000240601009920b40003c403000152042514007840e04000700680c040c06030240f600e00b0000dd04010011100000504620400795034903e0221784a6180038640e541c91100040424103079109800d014240c454543c3d4040c20812070762441e500d086e40c00b2000108a080040103090502c8010303101e50b1560a588003c1a8000c42c00c0c00040042e90003071a921606180f01e0244007080220b00b02156510503002440010030031000e07121a040d4031441e01c603030180580100781a80764001015803000d49103100d036101c0f02c2510810f0301425021a844400310f948034002030031703a41c40300b2402d00d090b4a040c0f007801a5013040300c11a01d616400b140036124458130036000f507580442044180442560b40e40d4541070000d20421061134502170207456 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 436428435 1250 436427185 436427191
    0x1107061d06060d08040b03100f060f0203030c030a2c0705030c060d090f0c0f15180306230109020a0306050604120605040311030c061902090306010e1321020d090e 71
    0x1041e2004540e034000c1c80040780c1113071701a1142e520001e40c0d0b0b1404184481c400300241c451080c141c2064000000d005225000c00a11100070340d019600c4e43d10340501e45009500050034061603284c0d110349616103469000e0082421007811121b0000c0068400fa07031504103d00f40d84954001e030840740c064142640c64500722281e00518100c0042d00d251a82003405588001d040002c00d0001002008504004001702d032800300c81f0410841022035070002c000701c41c801401c648500381501000001d00c00101541c02404160030f4500c041c1c0b40411000003034103219002a0310041c607607540001d1502c003056040c082c003800740400340c416030f28180ca041c201000090b030000307002c0c01c819601c8001c41c04041c82092112410500741d4110798603402c42c000059228807040e1800082c909224644142e80c0585000303071a61048024041d200030380c41c0010740e2080450003030a0114858880032a00c0000c2c54441000344542c9004200c0c040b490340c0f03400080d04e404402141d01040c000a10b0f420030955504d01d01d070a40c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 436429685 1250 436428435 436428439
    0x160e0a091406010609030209070c1a09030d290f03060c0a02010213031202060a110d0908090622090203100b0c0709051501030f090203060705030411041107061d0606 72
    0x1440c5811410704442114208404a406010742000000c03044d60004400c82034074000c8031000903d46800100380c500b4404100020b124010380c43d24514030000c4910b80035480414a803d8134a400c22280040d0200c0d246607100d45015401c0c080d208141103040000740d070391807030241c603e82c0503c0c168100090b42d4800081600014032400950055054400e40581d0201410a2031840300f407a140e103040c00c17419500c15084401071244d0070001e4100b8540c2c1c05412509052007005625040340015100c0140c0f04410042d10090010080b010b4203498020042440c07910309914490b0380c3c2008403890004480b168411130400d03005000303005d542c6a0752010718003241c81d80c1c20b1039a620000b81e171009003446d0701640601d64451400c410000480b0103401000842c240c260780c100992814910b80c90119540024080d4165100c2d030002540a80268029a0018014038410402816107000501900e175540c81d03c500e071800c0441d502c0100005e9010f05c40c400098109006240800c210000d03a9074007004080c2c40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 436430935 1250 436429685 436429691
    0x6180b040b042612060a061b0507050d050c030d080c0d0c0e03010903120e1204030b0c19020102071718060a140f03011403030a05160c090903020f160e0a 67
    0x150801588290704203c02d100070802031286402401d49048139001402103200c0c80c1d80000002e4407503d170401c9507400745c4825444504d0203200061159036002081802202d040c03182d44408a02907179030a4541c06958810380040540110744018141455000380c2c9030000d014000742881140c1da40a4151481c040b41c4510001d481c0700a00c1044409040700c44076145c240d41307407019000034958810380288020013804014404071580000751a0380d200308400c10744407800240014800160000d0712960011070412146042c008803e500102c049a030014000150b90f001542000704000c80c2c0d4403580d003211181c3e0b5035080418811022139007035400031025200c0d910000d012a54180100a0031555840c400121070716190007510040786a44280a10010380c0d03111808400c1500d0000b04543d540c5c0910f90366603003422101a0140010307040707128212080741d80500003082250407482514503080c0170768014410740440210088c00e1002201c2c0042d11217808580a0007000803c079103a9400c018420000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 436432185 1250 436430935 436430941
    0x10c170c0310030605070806010801081603060b0d020312091503041223071a0105040903051207031e05041502090604030312020403140a0506280e0705100302040306180b040b 76
    0x2080d2042c0d40382d00000c01e8545800c040c01600e6503c21040c81c814002a00c824449980303c1c600a90394800e5104605242a4151424000110b090f00a82c20382c1c0030280c10b07840c4515090b0700013820005085a8075003100008100036400c0c0c40c10860f800c81102d2a0111030b4a107051540740e10b0a0740c00c149180c4010b102d1010214403020f40218000d000644100c202c0319110354152402c01240c2c0341c00910b18111180350b200120309458a8420104420781c5a150b0354640001c03485000342c4c0e494000c0001c820f1591725044020070200c05503020300003250411000465103040d14002c0420490800c503010f040d031060003141100c0e10341c2c40846003603a0309400c0c40c01890550310b584c40040c0c40799410003454250346ca5100141c12400060580d20343e41316206603501c070ba40700c541044543da0b0b9a01d104160880891071006a921183c2c000450910381c902510345458503030001c11181c0c84035203110300000b54000f4040090060728030820600e400003110b910660403641e2140706800d0809040039001044017408 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 436433435 1250 436432185 436432201
    0x806150d05280c0210020307090515040e010e06030105090f2107140109050f010207051e160b130503150606130e01060806040c170c030c0d020c0c03010c170c03 70
    0x410690b01802181100c1c48080c0e400344406008402881c20140c0300d841e00303000da050b002d402601d205096940d034822500b4508020080100d41136105183c00c120300b007001281000c1070280c0c05010380000200500e040c02c028040c582101c900a110f4142a006040086078203500413a8610703d84010a0a0b40617004507484031404511604c08000d01c4450030002e110244c14042d001012854080e200743c0310f00220740040c007030a030721803464010002d8000403100950195501003008800f20440c04560302403061103038001141441303410207414414007042000207550a4070f00e41d8040d00701138024000103014840e504c8800800a041c4c3c40c46481d001c200c0d02d80581140140070300070025006d6890755540c1d07958001d01164000c0d22582e0149007030550380030049002d2013501508520051100060759629051803510303030400307086c646001108002c1400c22000c18005402000903180c00341544014060415086070f42d544030a0041c82a03100a508940d65007054141d44105c107040001c2d0f4990b02c2100c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 436434685 1250 436433435 436433461
    0x80c0a02071e0909141e10020f0906031003050c0a0f1401021203010e07031a090604050405010209032b0f050409090302011806050405280201110127030806150d05 71
    0xa0400e5864010f41c0e209100015600c0c5181d45c90007420b80321080e0780383c4501c035440d05e002e80010310b40b9440034000c401c000c000742d4024518010902c6106090000560003d00c0c203a1082d00c003001c582020b0141030061041c14000d00800e00411a03541405c0341c030b0107014503e002c215220790b07544502c8205100d004d903402400070740110402800c01d16520b40e12940186440802542c603840040d280142440081503030b4444018402070041101240d5070300c40c4104800752000070000c0751595002d04c011405034404102e52140c1002d0441c0d507040c800d00c50548110640103403804039042001c0342074501c1d042038126089800751001b101d004a0b1070308071402d080c2e004d000303070140010f212000b0720a018107102207940510b00542c4540c00b61103440c40880c0c0f03400c481c1401107050125000305d8012943c010340c000e2900580590408001040707029440400e41c1440c0301800c1522411442c4030704075402c05600c030207200d80c07000d8116021a043c250003480e09106002d010102c14040741c2e500c01140d10451009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 436435935 1250 436434685 436434689
    0x905010819020c0708060a15140a03050304090209012601290301060504050f0f030c040e0f1b030d03060e0604050403050c10020d0e01201303081306080c0a02071e 71
    0x2005664490790071483c1c6582c0d984a102d008214040c2001003410039215005801d0301880c080c16000110342004170307951180720301100f0741c2c1d44810000d2700040000d100380301800040060080c0182c84200440024005054510001c41582c4454025009010300000020b055a40c80702403d0504c0421118a2000c81c04100002c040b98030003100000e012070780900100103540b0700b9107201107a500c08100780003410781d034403078070a606030006204151582000d5003c0d440b8070001302c0132540d0b051141107201c3d04096501c14044492040c4c002045890b003001c0101041c81402c0d0300d000c010701c61420120780400364001c0c0105200b11346039400304007071620580503070b8030040b620815508440b00b02c041c0540254402100003001905003188950107000602c110304541090030004040e195042100140c203a0113042a401c5d00c420400b408004102e1500180c1032001100c0158001a030410b030f00540b0800c0d004150412804040250385a260313804500c0384215204035485244034100280300d03004d90380d003076 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 436437185 1250 436435935 436435981
    0x120c170304061a06120f07020703140a0b06060304120c11030f060403030e19060906060e010e100b0f192601030b011202100c030207050904050303060f06030709050108 73
    0x11052005026965201000071015444001c0754140c01c2d100344003035400744062172801e407405200000d40d40c002280000c2d41c816241c0c81614605a20385c0c0c1c1d070800c081040c045540081c0e10554040040001d14594140c100070126401403c628007980c0e030904081d07101150303104008002c5028010810011480704d545180282607920f40403070044c440b130307680200b19019070000b401c0001c44d03d9001004210804205a141e1900803c04031300c0c0c5031100540340b8040201d9000740e54104c0051401007600c022806410301c0c90000f40c441c1003440b8900414240d0340c03c00f40600344200101c5007151404000c8410707403101e4030100c01e1019144001903c52800841007042e400702124510380d034280c120420035050b03074031803461820b039641c0712409070a540152400c000c0d00000d040300240780c1c090190055820080c403d01c11520b1460300c40000c41c030084004d0f6000c8410b988040240300b0b00e490600c991810585007514020304624081c10000d03c403003128420181070202c0304000c9101c80101140e46804030369a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 436438435 1250 436437185 436437187
    0x110f040612031706030d080606040b03090d0f05091c0606030204050711010608010612032d0c0203060604090312020c030d09291306050a150b04050a050d120c17 70
    0x203102801803a000140c0ca040b40011401450070f06000c100410140c0591000703801000d40801020703003654640409072400e0f900c5074052000080c0700164500542c85080d80e40050140004001406044401d8071002001030040600411046481c0c2c0181100601c04045211103c05807500b0004018482504003039000b0742490308000c01c13907400408072804a440c90b002086a00e0355817000600b00d41550044583c41c0702541030280101e8031403044a078291401000381c1d440d02011002d1450a019100046408684040c51440540c5424004141e00600c1070354144a015910380d0300800c000d444c03e004c10403881d8003040c001000754007002030301d0b0340c0d40b6100390804c0b00b103e640c20083d01001140c540650200d00120b004000035503829003135406103004483e080450f00240d030340c00c00a8107000b01586407566071840e2480100d051000b001c0d0090103c034401654681c102014403c0140052b00b00ca0300801441c002500082e01e6120411905621843c10b042c2507046441c2c20780081000040ca20700d1544 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 436439685 1250 436438435 436438439
    0x61508061903110a0905061e011106070f0305070e01141e040b0903010b0a180930020c01020d120c03060506030103050601150804081602010e1305160203040b07110f0406 74
    0x760f404020026003000700d8900c3d036000d80d2900078500740c0d0701c03c468260b0045811018a1103680d003580344802c1440307050600441c3c1520300c14507545807003800c88807600000c850003640c40380c0640500c140b41c0c20020030301e03011800c000e02d0000030f091183c181d11012041c4000090016103000200071412800e003070b413051700303a03a2030ba0303a00205940d4100d041c1c201c1c840d51034955000d807540350090303c4204542d030500110b0300e40514410031000600c00550180c40300e40c803c00074a02c65207041c1000b42c403141860441c0c16204101200000d1030805220001ca0655001c413000c0000640c0000c050f18090b424240040703208105070a0481c082d01403a031081c3e401c0072b4040004004c1000c08a440c5041c0c400801c100e101c020f80d111001c030342402080c6da000c0c02c0d6140800841c4d800404041e400d00358a4010704140003a88101d0303002c00c881101003003414440e143e551051110302c4020401c1040c040c00244000c40c00c050405040203c1482007090048c19020030118600c400d403143d50140041d100002c0c010001e241d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 436440935 1250 436439685 436439693
    0x51b061909090605100903030c11040c050304150b0d060207060e010c1e0206040809060901200307060b15121302040603060504060c2c040f180201020601060201061508061903 76
    0x14050784403020704043c1d0104c0c081c1008001020142c0550790b070068541e141d41c80039914101c009509070b681004545802006807154000c00300003030039070742e2465a00c1ca41414110808031003030880c125480c1c200605c0d519245c0d1250309110201d60410300041c0e8031a55481c0000085c1090300c0e0b40002035080400843c40c840d001201c94041c4900104034841c101c002d820100e850b880c00311001032202a00303020b20b00243c20040c001e8048004181041421768404101284000c4002c95410300940d100151440c00c003d424003a40e4104082035481090300c4c405e948501c0c0140c000c0c00c155208c1c05821400003401c6440500034aa41d00350060010030169440f400c00401500c0111026100e90742040296861103114824652952100321980d42d180b41c004542c1d80c2403401490b410751760150b22110498180d05c1c0b188134040e40044003000e85200050030b44006414420305a2040c025645090300400201e08000b40400d40d00380c8610380420f0701c0c2c0c0d4850004891a00c1c00202c18421904000084200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 436442185 1250 436440935 436440947
    0xf0b030115021609020c0a0203120327060412090e091b01110a0303020a02031314030d0503070c0b060a03050d02010b03071509090c09081009031407051b0619 69
    0x2940e507000c908050800016000c1e42d030b825080700f6a800c00094100100708280f100e6000e481d004240000b42c2d0262091900040e1811407000909440c84400006005210180a11190860620801009000700500821030312042c00401c041c00d07210244512020031481141520090140520801c0c030604101d400241d0366821107203400703400c4010b0310500d800e0b50b004183e050556182e800007001d001d0600da80803406500149040d10135440103004041c401a41c000310000a0000d00f40b0141001c0300c82e208144c9459268050b400520000700244001254800d8008041d5508491500d030b20b5100c410100c0c181420702d0340301408900a80c1510b81c2425819040544000700441c120390003107440e0744040c0300740f0341c0030a41c44001c030300c46427420000041603801c5100c0020180c24400c105503515190710303061000e02594608841c5d500c02004d0201a00000070789610324a0321052400c041150781d800e40d4805035071001207210180ba280c418550b5650000320350501c5c8052829000c65240040701800d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 436443435 1250 436442185 436442189
    0x21030a020a0c05010c080d0c020309060a020a05060a0b09011509170102031014010c03081f0e040302100204030b01051e1c02030712080a1101090804120605060901060210150f0b0301 79
    0x40451070800020b441d45c82105200e0155400c034100e01d24041243c0d50076002000e8000c06002903001c24808685150303100d0b8042c050f0010745030090101401c0360f1802d2403c21078020000502d90f8504401c800031515211490303810b513000b1882a0040c00900c1405455a05a50307001c105240d14550101a001006401540c00b6140ea02a440c030303181e0705c41440c03038942c903218040180001d14050808010078440c509441d040329412905002180c0000e1602d078000403540c0048000110007000e0000300345e0704000841e14000882c0b42181482d0469480214100040c441c052043c0d20f8544050b40c21501c400a04441410040013003000d07803002c215000d080302100c01c045c0e02c00d014201c0700041c02030b000f0f0041000740c0d03881080d10780b5228400400750340e601d811000b8071202d90750310401c2d000040d01107001000509005030b5101080d1034a482e14800b618002042c1d14028808100108a541c2e000201c282072803c130120089803425a005100c075000d000f590217075542e103084400000d000c090a00013581 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 436444685 1250 436443435 436443443
    0x110712031e020a02100e121c080f060a0b09030102121005030f120415020f0a061a010f081513110309190f02010c060204150914010f0c0221030a020a 65
    0x8455900d6410ba88403030320320402940200c03400c0881d11388039200d000f40c038881440080181e0844d10310241c003541390030000541007035295000780c000300e021758200140715400350024032100c804e86007100c04250304e040e15224445038600d02003850780c000d58080d0140d41c0040380e006d410245d107141011301050310f0303d96845100e002c1d00490f01045c0c0701200c04103242100c01c0c00020164a4180360602480015210000c19002c50203200a640703002d00082c40030b209018000d038408640009008500000100c654001c40d060244a20503c1c04050304420a164020b000c14100401c032100000814025501d000701583c46610300485501c4104402c03010750f0244c080d441c1142c041108100001041544040c0040c1c20008200d0f0381a006610512342031321407510800d0050304141c1c5d05c810701ca0310b0710500f0f0340490116022001c1444103011440c3c0181140320700340b038003000c00458428058204102e1003401f0b4040d1460a000c4625400010440f104c1411140200c035900c0c000450300030f4135862803040482d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 436445935 1250 436444685 436444727
    0x12030d09210c020f100c080a090308030408070209070f12151a0d0c0305010803030a0b030a0f060b120615090a020f0403120305090619050403090e13030816020c0111071203 75
    0xf1040c1d04024140075004940c035242c101c188621b54880004d5600805075100800c0350050010000805050155024512403110552180d80e1481007029a4100904910422008112082c0349070340c480140e440b00300440100003040c0c3e81d01c0c0700d4011000f85030340040c0b03681d1602040d941034480c050f200810004148401c2003040035002c07c2c084081c0c9a00303205000f000d600a00c04200d18071030b03e41c003110018900400711f82c0c13060300c581d41d1082116007800c000d40c0d4880d85c800c0c404030142002a580219416070801030941450700020b070600480219500500400b8094001400401c0c140c0c11500c480e02085000c6031165907910340020340d81d102d03200d108002403e00780800c040040008015009a0304c66601003000706048c0310010003840010010383c204016148009800780d48040241e005501a83c1c002c8242c880606000d4403044000e460400c0300d5038084401061a5408035507040324803002d103400c40d141c100c0141c880303145c03801c0c60300010f0a0602c5d002280c002c00d600510120006002500780c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 436447185 1250 436445935 436445959
    0x60108030f0a11030d050a02031801091e0203030702060d1e1803080415060303030b031b1e0a0f060309020f091513090507081b12030d09210c02 63
    0x29103901482041e0303809903900380300e0722104500561102c00c042240c0e10440b400c00d245c2220a07000e41c0c3c13060f1070100f1280e50010a00c524842d141402400300c1c50408000d00000196a54881121420407007a2441280705281c5408540c0c0038805c0725203043d0000d0a1a482d0300b00c48a40000620201012410141c1c92500c2e0032100d00050107410340c04000c20200d0740020101d62015281c01301d00800032201c12040a042e0b48008001e441290043c50290b600040d00e410110141441c10030f5540044c04000220000200170b903541c2604054842c4000b0718901011b503034000416140449604a0012003540b140d01158582d031588c004d80c0b4040c02100e03920180c0c41c100341070160329441914401c049509844070f21641e8101100d00c59030881445400040794001034555605103610383d000320b103154105826510b1048025000383c05101c00403641e403468160864046952803054a03103c4030413a0300c0c0d00962040c01040031501c1044d043c03400801008151302040185280b041c244100e101d00142070003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 436448435 1250 436447185 436447199
    0x305010614270d0f061802060f0705031b010e0c0604060813110a060201050f09010618181707030822060b280311041e15170f0601 57
    0x46903840008005030502c0c00c03a030314001854101c140e42c0e0742920300c0300d9500d251041c0d440f00490b07102824015002049150241e03d003c80560326007003070350f0244958640500000d03035104012260742243c0d0806c0705076241c0d020318003242107015856840c071800c03030b0802c684000e50741e064002d042e00100d814141c42d0181c042a080003d103000310700805000075105000102c2c02c40741d0300d80c2108120b0044080842c2e01180c2c00003d41480ca085d0001801071351254284420022100540764001d04458002d104150a0603900d02000040c0050383c550180c0b40d5040c000110f0450700031800080d048600341c400d5614a038243e00150340280c01c11800200072800240803c0590b43d043c942c03208007212501040e007e42d0302d6640107004210b040f1a480001241d1036810f000c9203110b00c9940c0c01c0d084044e404003078514140070340e081016104042c06541410380311403036026084c80c0c100c0200c030f04400018415410b42d02c105c080208680001c0014401500d2808003030794001015076842071a002142e80a07038a0b084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 436449685 1250 436448435 436448447
    0x13050f010f0e0c1207090f0611070506160206030a020d1103060108070305040209070c050322031403030618180f03030901061e0501050f0c03210106030b0a0333060603050106 76
    0x25803020f0aa000b448440e03180c008030520f4541060517890200d4001c2d0b1200381030074505100e580b100c80800da90716219080c0003010701488000b08000c8803204e04010158107034802c00300c10200020b114020001c0001c1c444150366050341c3c1454400c1d41c041207941e000a41c0c0410b551301c02d80e0000d0104042e100020740703152080c001c0707610460307000e02005000d4444150070b48400f40c0104044075140002e0080b5140c815441643c00c0070810884100758406155041182660340c9100340400380381c00c10030800c4400e44409284940d4540d1400901c4010782c0d4141c48a66a141102e442c40018011107150280800d4004061b50080f1002030081017003580d00c0c520714400d410225461100c041c2c02c0c00c010081d9601030000b07802c800320714008061a14400d01c0c00282168407900a4904910704000f28140024000031418007404003400c0801c06242020300003116003209100082c089800d58601c8100f1013103903206c100e00742c120032080c0d6261400c170503e41c4d4013400e118054013000a18040000910700d201d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 436450935 1250 436449685 436449691
    0x504050604051b0c19060621050706080a0e150402120a03090506130e07080a0c05091c0809031509061510050309010605060f07110105030603070b070213050f010f0e 72
    0x32803515030310080300070f684081c0d400c145074900761402010840c5c0f0150600030707043c4c202244641c00000342c03182050f220014047c201074001420540c803100c010006200000c0130815038407030341014103c0c1c0d0344a03c41940940054010044140189604d4030301c0b080c210040b00f40640d20840301d0706074070032240072503681d290b49080001c2c000600c118020000c904001b001440c54042c1d1903801d1b14004d0b100c42c6280d0481c4c005840c01c4001a17036420400c02020f030517100d01d0070060283d140141ca0005d0300b500060f481c1d0788211980c22241c0d1071351040300803c007499080320bc01010241c144c0b40302e10602d03100070303140340001c407164241c41c040c500000c1c1c100c40880c840700210b090b00401038840032103000c100721060b0b000100800c8607503581d0140030403280e507041d01a0080d45020303508181e071005a440c114000f00b00700c450045c1441400c1c1b0030b2081039030300030030440240d42104180c1070316081107000043c880c0c2010b111044940c1e1a0038148a6540b0400040350305031644461007012031581c50844000c116412 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 436452185 1250 436450935 436450951
    0x705040c050a05090604050d050a060e0c010e010f0c0507090e100b010f1d04060306020d140105010207090c021609090c080d0503010b070501021b0106080d1407060b1216050405060405 80
    0x4010002c0c009020341e010f44208400a868603003843e46070404500700c0042e094090b0783c1d9500400c1c0103000c20400b401211700034405100549000280a000a42002040c0c120345040c01010704410035454802c41c008244c0359048403c0307541055840ea0001c2c014104e01c0945e512502402e02036104506042c040c1612642040e900c0c900502c517850f00c1201d0803c01000c01c280b00c108421440585541c0f24024940914000d0134016951811511041d0813580c180300810341c4103114400400075070780c011490104807002c030013011a182c00084800c9080a01c2400e0100c0d94001c201c8000c21507a9055011400440c031600501318455290f0340e00a5441d03800e80000c600040c400c1006001050060029000c0180308038000340c1440d01000f0780404280021840d026580c0d91400c0800240408004040c450b00003070600d0850303a802d41c0c0121406104201c0064000c64a55850f0301c440d4403036103014080c03040c031802074a00902c4680c2d4106a038078081d1041034803c604203400f250440c5064802c02e0702407409 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 436453435 1250 436452185 436452187
    0x8060a050901080303010b07082b0b03010504051c0c061b09060809030a030b010c0218100506090d02060714031606110a0e0112110c030c010606030209060d091104110c0705040c05 78
    0x2e40190460b403903204144c1111551414096080d048c10032031204218190030300c14240030041c4500d880021a24040103007440dc0e0f0514060201064001c502c80302210f445141d0a10318402d505015250b001d001c01c4001c3c5850302d4012220700c9003204070b00e1071101d000d055642c008101d545035000c0b01c003c0000d80d4407145e1394004003d500710060080d0300c0744032080c106041c000701c0c40300c40d60001400c1080440c102807a11010108100d10a900c0390902000303040215220303824103e40c0c00c049a010109500020b02900700052014140051804e00b6960341815204032039844c1c9100518512020030740900302d40040c18000c1210319903420100340c4034000c2da00e42c1e9004920607201c004584070210360380c100c20300310303640c401640d4514940001004940040d4008541c5d60040e94540c03801c51306260f111004051040c854403100303a48031422a4020b240034400407803101c6090502094046c000c2600c6540980b80400c9501e4641d1103001410580c02d000c01558141940d070001e110988042540980000e04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 436454685 1250 436453435 436453439
    0x80a15031a060126090f071a09042a02010c020a0201051c0f020f071a0708010302192102190f061b08220b090d080d150608060a05090108030301 63
    0x69612295202ca4140740400104030f1131070701241031184054503000e03c04454402c0004c0b820080140c0c00841c034810000b4480d4601c3c1540110083c210b01c840c050b44003100081c1d401403540c440d08120600101d41c0c52991161408e0034081ca0301c01c1f2056080b4001d5402c101000c000300c2d001142d00c40c801d0741c041c0c542c2071400303001d0a400c040d4000c82108079801c641e07a6561482019109101510b0010821f501d2a076031500d07241040b421030042c2c0303412045a5540e1008211003c1d52003018141100e82c181c9190307817a05800d9402400c0001e00b034000c0d00c440042c15809c040c40d5000000e10700300307540c026900c1c0594145803555001c000300c180d00402c0c3e100c034030f007070740802100b4411803401e040c00c0003054001e008403500c1d554138081c035881003221142c45548203811400104003e210303000189401c80300e461038806210f01040112f141100050506071020504000c0b034251038005201f02441940d0400441d5111030001c0c0c030041c02555103034040c2107030450200b070900b0202d00302416104600011401d581c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 436455935 1250 436454685 436454723
    0x801181b030807060c1107060f12060503280b040f060f0903020a1101020c0a090f0b0901151206050d0b070206011e05090705090a141c0f0204090303110a080a1503 71
    0x5c0b10421110042020056500f041e150040c012000903081c4c956440008035503090000b018007011902402040341f0f401c0703040285a6000030b000032100040c205508c80210341c0300a0681c60802c4000180001d80d1b40390420040012044d19598941d00c580300820100d54403142e081d040700e92101d4006e0240e0b00c0482204082507540c2140300c400f45051040350080e81c000d202190750074200790320003403502e82c80c1c1348600208040350180341c0258005841031b400790340c034001681440e40d000306168070900100000388005c0500315000f10005c1c040103030850120514616000450905c1180c607007005001d402c0010406001030740b980d590581c25199191034040c01c100400187c03850203009e50050100401071000e064032015951001012010241a501000a01070045001e0780c2c1001200000003031080301c000400b1040038a80c2181c041e41c00084d904040e1900fa0000c03c0755030904841c014001c905241c44a6001070310341d03c60284c0030b03c1403103a034280d200030701302c036884500008054840088000c1004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 436457185 1250 436455935 436455941
    0x160e0114041b0207050310050919110402040617090d080a02030411060a050d0f061a0c030d0c05040e0106050f0a0509010905120106061205060d02130f140f100e01090b04060801181b03080706 83
    0x2b00d0f009516082d200c540000001e41240e20a6001801040001c40c208007450755542d2083d5210401401801c4024541c080003031041c20020b224041032135022001c1400c0c441d14482400c0b07548005410070f580d8400740715010f442500710401c1c00c101c0f00e080a8600041d6038003030003001c048400d04004603501001003484d0304234030340125068541d0b620007844145910b0410b40100002a1855103903030f5900c034180340c5058007640e0140c0001081c0300c820010700314904070200441c0d0401c505441d00708c0e102d031049001210301220b40c3d40312683c803004520143c00c5011065120b070040350707913a0b00d44001e0901c0c580042800d6803002c44185602503400880103002d0305004140010000020000060060321600c02c2c000303d403031102030420301008031402c00c411103d500c030005030404400145080c82c01d01e0030130b101c80116014001d00040d41c0d00d42c4207540b2580c0365904100050282300000b80141303d907400105c0010f49041d08169423206096078040d40701614680c1c404256600000403510f4140580c4585010b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 436458435 1250 436457185 436457233
    0x31615030c020309061201050310140601082a0d150f0b07020310020408030d0f0e0703060c1418030c100e0613030605090f160e0114041b02070503100509 67
    0x150f0100b0061301d05280d554400070080d0007014160112294184803e0624200300541010803040c54009000d031841042c0002c00e900c106c0034a4007503040d60300c0c3c0e00411414041030800c00e03214002c04a00b401d0040b101c4c40031b801b0804821303804018841d80803444681c0d40401c0d2180540c10040341e01300780031300703802030340180013590014088036262100303407000c08100e90069022030203940002c40c00e07a42c0c0b41464001d0321401d00720900b00348a0300b28100840f40d01c07004a80301c01800f0700e0350b07101000300d05409083d0103c490070b80c3c2d4654a490b00440340d01c40c0b2604956150040c424040d9020314405458900c9003503100c0b8106684014103090303d0014440540c1c450649605d02c461005400400078042d801241d20034000780340601030100d80880ba152030555004070b1640d40b2900340c00240401010030803041d045034980ea0082c0070000c146000b2030010540407915446141d078446d0070055198002030b09501f01c40741079084030481c801001c502001c03200280d070345005035000201e01003076400c4c1981100e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 436459685 1250 436458435 436458437
    0xd1a01021b12070819200609090402011b0302070f0e0c040e0907181b0e1003110d140103050f0a120503060f0a080c040b0303120402011d04050411031615030c 69
    0x10686840d0b40c0b42e5458140ca0760317065060400014034010401103480e9501c1e85250212418401c0f2205500000321180107480459001c5c001020019065a2040000c0c919403002035848009003462170400a40700c0c00366000c0c840d14000180c40000d22010700340010352242000090f01c6090a0410001414945010b0308200c4180b040d00c5020964114a04160b4034410040800203008d032030442c0c640420711410301e00340050008000100469171900009420480030303d140c009000c5401c04100c0d4181d01440d000c8000c07a82c6011140390741c490000d20302505170b074003c000f00d03003007891a012960b0360341d0351801c4018100d040d01101004d00c580544090358101c180140508110503514000c5461182540d00620f0580e05c00c0144000d2414540720308000b0980960180d41b9000100c6040c204a06014100030304009200c01c0040a448010400d4826050020010f200c076040508040c0240c802d1407285034868081d485a200b410080c03512903004450841e0089003203800c2a42d01a0700501017015848 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 436460935 1250 436459685 436459693
    0x24030f07091517090a02060910031e020703020f0f0307121b0b180307020901120807080309030414042c030d0e16050108010e011a0c030d1a01021b12 65
    0x70600107640841e1114000d1259903881140681203e8880501d034090402120b075045050200c3c0940c840c01c0c21540c0c0808161034031000c071800030314220002c0442c09040f010208016098203440c1c5030503001400d03610300030782c200c039410362400c40701c140c40f54071609001c00c4940c41000014005481000454100001424a512249070030030303080e600010f0039034007110f40380c0105080213244403048400317030021a0030b10011410a545030707010a20064060003800030f200100000705041000b81811500c0e485d510810083d201c2c01d244205a50326085406100760000031b00c0300901c2242050310036013810b003c071802910641040c1c0e025911007070820b10380303407c1207001c2080f00c908045180e0090b01114140c51004004100181c2c161049030045604524104600040104020901100c803141510381c0001d14043c00b17006060840080e1040a284074140e00000c18041800e00e01c5a0100c0e242c90140c0c2000d40b8584000d60049031903a08040360903191030031082580b1803a06042521402c94100c04d0200c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 436462185 1250 436460935 436460939
    0x71d07030e0102030702070e101d061f0302070c05121c0219030207030b1602150a06030f0b071202040602100509010f06031b081603020103021606021824030f0709 71
    0x11803d9a2048400e80301591080c802004848640034495501105001d03030b00c40601d0502000d10008440c06584920f980500c20110765207542d0000441050316003e10000740e0460807032000b90180d0003410040d42d007280038010024142c00c02c100070801340c104810280854401e01000e4002860040c1e511004501c40e42801f000304400000721980410b02a8005000312440c40c5000d6842580c020080395038005590555800341c2d0f00014105640b81446000b202c080c0d68144040d0010b00047c0d001901e4400b0308521a82403007922100c00d405042ea03036542620820f402c0c200d020580c81a80b0070000107a0010345c0a01c0c183c2c2c110351141c6e0f00198074000114509c10072414800079034125402c152568000c09910310380001801da00c1d03600800782c40000c0d25140320740b6245403000704039500c4003a043c150001002ea0b450410140700703000c0c0e01c0e80003078215103c00151062000300c2003d40e040c030b0b001d110a444150f0107400c04d2480c03102c4c000c0031181d031790b8030355034840940e55005c2c0005490b10701846503400c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 436463435 1250 436462185 436462211
    0x3021c06020c01020d110702030a02090711031c0509120a120212070203041503053c01080706031103040c270504080304110904151113031101020f071d0703 68
    0x42c80c410a4200c000340e02d403146180d840b003c94002142407122524108000c00058801142120722385030119224085a50f43c0c040c01d4628101d640340360000380c00005140c0c15a14103959500b450300901200412644ea00c00b0b40190790341b011552007900d11308050001c40c002601c14001c4500301c0351502c201600b029000c060140c801c0c401655610056000070509001e10140c00707100340703410862850305010078100307181c900ca0840081c462004000755071510a040c034102e406896030040f05001e040307900710740c0d4960042e52108880e0140b1000039003804540a140807242d01a60300a5410640c0001820320302004580c1c01101c95206410a00114402c14001c030071a110300340c030450148030a280c1cac03440c242ca005443d0000d008074040c403c141520078000400c01000302d03c2c0d4103039045140041d5180c84800e1110b0940600c804514009035a5a00481000308055080010390801c0c2c08443e00b003030300b414010f0b80741c1c05140600c64821500d6100007130504074200105400c0798942c200001c1e00842106 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 436464685 1250 436463435 436463437
    0x231f060506043c030605040305090907020105180a030212070f0c1e0f0602030d05061311130902030c2203020607030509130605010e09090124060306080102040f03021c0602 75
    0x102228900391054842e02c50b90200c103150600f4a032a0030840c3e10240034480403d40140e240d40030241c641a41c4400140825016401b11018070703d0050041003140781000340240070f0501240c1116001c800b150741380e003180381c0020308540c4040e4140c003d8030208900d20340c0d038861600854826603848800c0800c407c003140407043c282020b0800d196403106001440f0452003c503000030760000102d000740e40300070441582e0200030b880d482d001c150f50200b03041d08c13040c1c0044d0b00d0903492417034030f640d03145845004480340d814030008016030043c0d05001400310341e5a80303d40c01280000c8070007034040c100402c40803411000307203244154a08040350110542d2034881c5c010622039044440210046000000c44003503e04c2c0191107041110340d503100c20f024150428000920720441d50940b24012245ca0340400d61703a61081d00004402440c12074843c4800700e50101c801544541480b070f00012902d0f089021940b01010700894040c0d070400d40304030944030324540c28407441e52814141110500e214581100014078240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 436465935 1250 436464685 436464689
    0x30d09030f1107060f0c020d1509150b01080f1f0f0305010f090305040b160611191701030f0809090709080c030106031a130b0403030504231f06050604 66
    0xd80d42141d85490340c10003404288004108200c1d540c00710000700035640d8000300c0c130f02140f24203103801541031500d407011031041090110001c1094a144040411000e503c0d44600c10a50144984440f80c0c11b41c1003481e8103c61a024106001036802c900003416503500c2c0d03c036103030080c0002c1602c442d0305040413860043c1c030314160416640078910040c2001884824003942c1341180344013504008030074941d900135009c1e02c1503200c0d40500d0f1b000450709a4a8044500c40a81d100c0e801810910005640b601110b405500c0064260003184109504108551080c5c00ca035880c03042400c070070901c0d44d0031354070741036088030303200c68200c0380a00100092001902c4100b0024043d004d01d031200c2180e24101240c1900707140e510101180261b1501c00104042540c1040d200a8100070603903140168585105030626408802406013070b4000f40300c2030100701603056101c0c07849607001d080d040c1141400c0c1258417407080310f1441e400c09103034030212007040c0003401c0031020700080d00803801c0050441d54034008108260015 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 436467185 1250 436465935 436465937
    0x313050304080c010801090212071107050a080105010905011d0f190c080f0a020c030301051002010e0a0f1a06101812050106090f05040c03080903010618020a09080606030c010e03030d0903 82
    0x4050091003030358128101c5809086030030002e50900a468270201e1250f038004010904200703084400d01e84c00e41c0d007441000042c2c10080c00031411a500c400300940606000e02c1142101e5103071100000e2011036108211002c0c00d02c00751565420b80f100360040140c0040a081030551105441850500203180d1140007403501480d1980c000c18501094104400440281303298003ca00400c02c080740040d0103c1140d044d242c048858100540500078100d00600740b06070341003502e12500c1d0146090012560841075003134030078030701c803680b80403611144e45401c402907606d1038010101d841c0240c0001e014000b0442004c81000564002e65620302803810402241141030794030380d5480d00e051041c0b44140c014800c0c0c0301480b202c14040c0e0300b00f1759038030010a40e044c88041c0c1800c1010880c00b006650a4004000800c400c00031460080040310100d4001d50203e1046170114080d804001209a00031a00c140b2440c0000d0241c286010721070300554035022103000144c2e240c0401c0044003400b05061040c91182406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 436468435 1250 436467185 436467193
    0x12010311030d082a12010f0306110a050d021c24121a10050301020a1d09060616020f03010c0c02030d08010b0a0f03020c010e240c030705031305030408 66
    0x4030414182800c540880301c0040010702d00030030410002039001c48160fa48071031103007003102c0c21007914119240918081204010384290000501e40d101e07000c240d003920700400003007019117a09054554107201d0042c0404c00319600340040305201209502405001d07044100301075a18806801000455401c2407a08940601456041910406240448001d0440b800720b0128000864485089410400c860020010700400002e400103003217404450007010007500079504c68015920183c840b44080c4020642004030348507146451038a00c0002c1d01822014046070305e00341c0601d000301003100401d601643c0201c1110003154444d1404d10580f200d608841c0d48030001000305204040c1000703c60022441001119001804480000402c44003c5482030906012840102c034094000c0c1c014502040c3d00ca51030b020180000d10000302c0c69400c1c40c9851648100006601c40800380b40c2c02003a03802040050040c400111a076000f2070085410541f003c0d618010131841e03a42d01843c42d40705421010590f00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 436469685 1250 436468435 436468463
    0x516050a1d0d05101a060c070b0a0216031a090303060a09020a0c051015050a060e0904030306030503070309170a08040b160b13110411031b0409090308090c12030d0f02120103 76
    0x701c5c0355002440010102d032040c0c94841840f9555071758aa2074026040f2051340080c0e4808094020840384030400204040007003001e82d641070128101104c4054210034000c143c00099101e04040116442454000e040034403150a2072103031002500800a11401d100075040760102254081140740794003c0889008600300464280414110030240e0100b0b0086035445028480c0c07e07041942001a680c00740da10030030550350760404401505141e40042c04900000a66509240e4480000025180c1c4032080404595401031003aa8405004002400601c2d09120a0001001c000001c04411161415418408109441c2c02c00e0561003940c440c0d45210040420384100280013240070820101120100941ca0301c042c075034441440010400e0003492225600c2c003c010351300b242a100a0803151104120f250f009140c05080d006064450412074450304040188a180c400352841c110100c40c00039605000e0100030900143c418444c2c45c0002e16024044000a01036010b180c5000314007550031990102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 436470935 1250 436469685 436469711
    0x324160909150503070503010603050318031f0506010e090c040302190504060b0414030a020607021002010905010c0c050622080a110a0602070b07080c0f0c030f07060516050a1d0d0510 80
    0x285900c06c40c000c3c0d051420810100c4c001005032000c944501945070082c44040300040e044c81c545005100c0e41d400c2d0440e60049800b025881103205510a0701d5400611101e8401c00c620305004503001060701c00104001d100600340a004100d18203440300740080010344480000701910392075082400d24840c08141004100607280c804603440c2000e40140001c0100341c0c0228010344910b1030040d01422454081c0429107100b50700c40a900e40e0094020000880e0441005101c18140c03030080e00e4a00c940000300341d00d104440a0880442c0c2140804400da00140e907500000f50003901205061001000240c5048441400203c40c0345208440040e900c501c1e92408849580024006008111414041290613040a001c1f40d458000c40d8204949802280f0703499032861190f000b514840280205280d02040082c2d04154000c103506040c906060303040c0c00741200c4e1800f4128101c0c000509a580041d410780c41c181c4030b8000600c015281119020594440038a8441380030304100c103280d61020003403042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 436472185 1250 436470935 436470943
    0x905100509160605040510200105011e081504120c0b091c0e0a030201051305060403080d06170307030c11030a110a060201060509040b10030f0c03020324160909150503 73
    0x20b8061130030690300f00303420400466100040c1048010a2014a44156089640040c139612014070840024046507846c0d00003030280d1600310484400d103022a520100c1c40030030102d801c02101101c042e100d0003542c5c07aa1114100310004510345818070620190340008181e900406070320883e1000b0080c5024010440030001c13400d8000b00b20010042e90402030700d00c0c0d41d54020f131501100d4091800750344ac3e038030044010030a44055401a648035200103400001c0201020103080301c1520300c0410004142c0d22086094000e00406107041c940e0010412400064020b280ea602d1003401400c20003d11916440801d242244561085d034041000c0e41c0c0c80e084520702020040054500ca20007400760f6131912002c120354510141c00105130030300c40c0c1c000941d007d4078200101d00949d00722040300c00d040b8003418002d50395042408268024080d00c00d82000101d50307062180e4844004102180c0e281d42c0385004032038000f151a2294081001e45000015440c4c405c0c0502407921003803414841d031980c50301e020903140c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 436473435 1250 436472185 436472189
    0xb0417060105040c0c021002030405060715050a0c0c0803071209030305090705060a090b0903120f07030e0901050a0306091b062d020d140705071404050a090506010603090510050916 79
    0x3c00c81c2086502d4080960202c5e40d03440c503035810780c1c1d100700300500404207a0850161b500304035041300b07001c10703d94140601102182d400c084001400c00c01741c0c035105140400e0740d50001032203010440d44108000040d11100065502c10b9042ca04110740c9a901d1032600c0c140c414003401078001940f01e4050207006a024451200103103021543c45103007041c03031140900090032a00c00e01c1360265001c103000042d84c40c01d100e0010b0310354030020071607a00c1d0b0911046442e41c0c2c0059600340d001800a280c803d500b4200015854182d540040001030365600d145d40b02406800c20400803103030703042c00804400d1481c40c4600c48001520054840d50300200f0700407481500d10020143d035849500481d40c440c4403054001ca01d10062803271700d184c2030300e144030440e0180102d4817030420010907511481d0b500044141c2000c00040e20010300310340500658032010022340507031b0b0742d51801030801d805c842c004100881c00b82d8007682d1064070950564040d03c002940010803514129182109038101c41c4008803c0b03c941040640 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 436474685 1250 436473435 436473439
    0x1606020f0309100c08130c0b0a1808010501031505090c12100b0d0b040201180b0a030507031107151805100f0c02060115050a0908060a090501150e0a11040b0417060105 73
    0x1094003440004100317440c040c00928101401c0742440e82801800d00342c0001030100300d150a50340340324140000b000801074030702c10745d4151504600454000010f01403a4102c0c1d030811003600e184012002c44100400b0b0142181c0300c54403642021641c0c6445055410440c0c2d00d1400c00780415107501c9501c01d0a403a24060369903c01c240d070150003000102ca104074a07402076020310b08000203c550b6541001d251000d60071500b00e8441c0410450201640342d00902e01c100d0640e5030071b000c022100070007603c5034000d680b00240041c2c4030346680c8400106613803203210902c007400705014810304a80c03078160400d6089103008110549420006400c45035a001d02e400590320f41c80280304ca50b2510010540d0202d412600d8400c12500041c6500c486104100e4480901400310030799465042c000c3c101e20080c582c01c0011110b95080c2005c0b07114180d036021424003200c03001d008d40d11030f80c0e480030107102c01402000d1041c20300c4c203410721012480001910242015084c10995218254111080d04c4c1c90404140d2040b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 436475935 1250 436474685 436474691
    0x70f020606010c0b0109050901060e04080405030d05120a1e0c02010e060f06060d05060f06040602061005100219060603080c030406090b180d020f100f031a0609061606020f030910 78
    0x2400120f801304201e046070250600080c9a444040125014260f01d62240120524880901c800d0007030802c01030048440031801c54955685070041a41da0b800b501070900107809145001510440e407a412110a1380f4081343e00e9600d101c04127510a0031034083d50b1b21200180e43d80d0680501c0302c0d004000140d0000c001c021034a00d985402400203203030b032150018101d10691104045605600d03980c00c40100004010318040c1c0b140e84445000390f540c60308a41014400c502d01500040505160b1098440e49140740e001e40501c849000e10011300c540101011983c0d540d4445000002c42d90b942e01900000b101d40001d95651450480d00030001c0e140354109050000b01041310b010883c03045008007162070002c0c2d8401500c1d5055000087c0b600b008004416040384403401c001400c298041d00c100c24454642d18104007895101410700031600282c04040d8001c207040042081515081004c0c00c0c1b4514200e5201c2803008031a030b1540140d0700000c0004905460101c14840c044409115141400007001020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 436477185 1250 436475935 436475957
    0xd06051002072607063504050d08162a08040806010f3b0c37080414010c030203060103060b0712181205030a0801080a0302030a081509070f02060601 65
    0x1c2d884d040140301d10028007144031920f141e0884400c00310200e100c181071032a0046120076440f2001e00e04201c404491038000c00c0f01f25002c00f806a08407501070300b40c5001c50b55030008140b40a0b240c0400c541c81ca87c0308140480080e0038500d48205d40c904000c2c1c0314240341030b1101d01d4280e5191800c601a00038103004908001c0074801994140600700200c2d2030364000300d080500ca90707102c10702040e014668a00b4034180c00300708a030b001e101030000d00b18101600c0d02c001428520049041000001c90740368000c058040c0150b20443e807080c40700c160858040c2003d00c41e040000b032105070842d1401500c03140480e401004114003980c041c4a03001c001c0c10021001f03441d01c011540d80d0041304e84040214014014402d14188030141c0c08190540501a5a064030b803c0704550f0801e01d035a40c100134941d400180780400041a200c1c0c0c081007920304103504d50019810500e000105039221600103101074050341c010345000c81075640f048100d90013099961140c82059210240082c20700700e000703100300d043c4007440b100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 436478435 1250 436477185 436477259
    0x7030302030d020901110d0305090c151207020c0a06090806060a270209030703050601050a050609060313030e211b030d21021c1413080d0605100207 65
    0x200c034000d82d01404010b0b80c03001c011005130b66907441c4044801c002d01c140c00100110941540c0700500600702a02103403088034280b0100280508010030008042200340000d9401425141c1d00300d03000b59480c01666186104000414810495540401c1c0050724034001005071100c1406041d800c030b0419200405198104214808401206201c098102c400020085102d030069411b4030140003000302943c2c103160745d0b81409541c0d40028040c4a1207050031480004031883c0070401c8a5035064040c01c61030440d0f84036048011005103500c01903062090207000b0300c4241d9580300141408806080c60b00c0302d220410340009181006d076152100820b20008400110360382e0002d64248042201e00d407031510081c040040710880350500303256200284c008625042c045c00d641c2e80c2003004a0030391804000f00104c010030340850180c2961803280a0000c00980008145414001c004041c1800004245950b541c0c0104d81503440708164a80140c00c064814094005940d09003800380c0e490030781c1314049143c0158 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 436479685 1250 436478435 436478437
    0x312140103031b02041a13021801080a0b04050a0501031b2607080613020118051302070609050f060a0f0e1005190f0b04051e01290c0109060c020703030203 68
    0x10203028030200d9103070380782802c1c0b10240f038000059010748280b040f0038400250701d5a000f00316a040e0700c2424003030f01c5032003e00c0e214801d40340301004842400211404006c019554260050031440f4426114074104140d5111801041c1c000c00c9880c90000d025071460901c0d45000e00b040c0418102c40100754030401500307800e1116050f421204500c0100038070701500145240503d5540460028001c20040280b15419030319a240e2090003a00c1b146202d4a00c0f8030100403292041c0100c60b80044003011001d5000001d9014203c10740c440d040c00500d01c141a102c0c4d03844e14035a10301005055102504011802c112800340c02c62501000e2428030101c8c040811725500c1d035082c1420035081a41d036100040e4445400a408854a80b002404205120812480001624280d040240224203000c00700344c2e09074880701488260a03580d1032040c450790a06e085c2a03441003c403201420031540e03900e80c040004c5100c5001b0514580f08400009943c01c552401c0010780300c25903144019508024020000300390040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 436480935 1250 436479685 436479689
    0xf09030f16020411071a071b06200a1b0206090616151e0f140c0c1506031e011112010906050d020310020c011e1401081902010c020307090e0a03121401 66
    0xc4608009540b1480215503809064523105030200c407005112003407294983c0980000310201e0f1707120041c0e020481c00301c02e291003120006000038030b802c0403141c102c072a07000d00120074a01c01095103140215990004140344c0080c0103002d410100000903c04201c0780c0000d50030441c00d5020240a0000340300f00c0f244200c0004002d4050700ca4a90b208104103007025480100e071071640312a0720b001c5003000080c1c0c2c60140c100c034030504030900c034107401e0aa03081040504148074000040052480c8083c100307640070030740002e40003d921756403030ba50103068804030580903010319103220f0502c41c500e41c500191881510b52030f074401809041000c0e141809031320081101030f02051204009a51180304403040c500501c810201214002006030710000380c14065000760b52030b04120f06c00080907036210700724940c40d0000c9491103400503c0402075800107500a0070b5402c41c8a000401343c85078540d490301d0100a454180c2661015a0003413800034081542103801c5039041040e00354104802c3e0f1042004550119047c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 436482185 1250 436480935 436480973
    0x51e0115030b0612010207142401120311011a0f060c1e0a0503070305070b06010801152102030c1903090c05130b030f060a0c05030402090f09030f1602041107 69
    0x1110000d41c49480c4e8640985598910000840d610350071420f01106c0c00c0c1c1009020807040c0100442d08518200350309541c104450041d101008503440c10340e00180f00c0d844007030220107000054148e03241e51002885810b40e10303003521280e110759405a6041102c112a02002148140014003c05803609000a11081c0c1d04101d01420800d2500c410141c504d05080484001c0040c400010302000301940300024150381845160050700350741b501d1005503031064090042c41e8030710050140e05401c0c07030701c2083e440030103c41a41442c1401c03140305085000b82d0307000320b0300320140302070002ea05120800c44104a40c014416031030208401d503101d50b070744400d40c1c00d85d00c6000d1040050340307817400c242102c940c407088480c27000800b120a1305219414540c0c80c3c400448003c10103034030301410040c1c60340c0100c080300e200f2070b402009000c1503501c200c01201e200201600450091100748036840b07030b41c0315400083c0701c2c03142c0002d6041d49040c900d03c100004d949000e1086a07101005004003c00030b14002c10903c1c1140d2a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 436483435 1250 436482185 436482203
    0x7211a0d020319060603031403040302060a050c04080a0b07020609061005190915030204050a060b1b0703150509060a0c0c1104110d02091e180c070204020304051e011503 74
    0x1007400020703c0e110740074103034800051001680b40c2c1007100c0c2d944071004481c844d8840c024142030000c90011180011940a80941c011400151302401c00c0d5102944c001c040c006c015081c0b6885485a070328080140c0802c44007000190140071550b5010810940c0c001404c2c7d004000340d10700504012105a010700c2024001c0f07984400d2011002c036802842c40250000380020000070350024907000c84a4540e100580c0680e10301004a5040700e9640920002d4855400700c461900744d90002c5c60303440c1e080140c10080c0500840501000007084892000545507404070007084500300030140904049010700000a40c81c906a900c020707550b080601e4a00c40e582004a1088907032458011801820b110050343c004ca000008404288042d954040c00545800743e44542c5007002c00e40280e40103003549034000b41c0c08808042c016a40b40d4103209a180d01680040140e42050707400e0340441e05982055404841a820440031030070300c41030116405001c1c20480c2c0007440441018404000c099019000c050b2142803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 436484685 1250 436483435 436483459
    0x1c090801020417194202090a0801050c0703080a1b120e07120b09010b09161d0105030c030901090b04030f02060603070b0f09060f04150801120b0703050414010507211a 73
    0xd003903034200070b17445561103010300c600300d5143d070b00035484140302c140b03c0c0704031550100d07415405229240c031904803203010520305045502c054031111001852a00c0d00740e01c41c40035001c1504000540d4280c60100c0c0c5130040d40081400c220016501f00b01402c03000c640c0700304410040d64000410400b0602d40203804a242d946551541034090200c0030031064111042c0d0b420302282d143d0040200306401e803070b41d071641840848000703140c40040118200d103001550070300c046103101e20740c2c6000b145c111507075a0000903010400d039070320f0407107001c1224207a0214110611101c550340d01441119440101200a0301038242070440250250068844128000002045814050f00c0740d608860b044c901c0080901d40b00e55a5541c809013501303d4109442c002a821b0000191124640703203500c50440e80305040160341d079034010342100203100c010029220600c0790f60150000071000e00c100340c000c0034150764034510440300440d0007001e0a1507060340300b6014506403094040201518245000d900115540301d0854 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 436485935 1250 436484685 436484753
    0x302160b040309060207060305060607030e1210090215032518180606080c1c02041706070e060703020a0b0402061e09010905060c1c09080102041719 65
    0x114504500400d4a00300900340030605400c41ca0340c40840d100c036401c8504240d151202102a610140c800d640c001c10180314035400603001d228618034928014003140c14180c1c1500c0103d1078589404078400c1c3d4160b54440036815418500c41c01d030b040a20030380c0d01d2445c0d1b042181c0d40400b2070909041840d069440a0511200e03a40b2858062030200c0342c18070113680880e29641400d40394916213112107507071441c1c460001210b9005640b007d01c0703951804861420000c40006583d03c0004c00e2011207030309a402c00010071400c91800721503601c085144014021880c2c0407101804000c44424010703c503000900600c40025400250a9542507103e01c101000791100e2020404c05e006d071001002c0c02e4000151240b0300042c40001512615600741c1e101008242c0e51030a00919104103a20f10308190020074201814140c2a40c48202220b0645400080c0e80c0c0d0302e07000d450881e0440d4110b4044c000e12810780316180e000c10071885800605609001c885002b07503698100180e01c8103150182c42440c0158011410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 436487185 1250 436485935 436485967
    0x3030f0c050c0a0902090906030606090f040303020913021801020111071b050d08071a040c0618030c080f010617070314030d020403060617010e030d021c0f0501030b13120302 76
    0x20460252182c3d54003500c80d8032290180d0407401c080f902414140b40000c0e0395140000f0b40360b0103114054891192500d48501c00408504024016410305408100e500d08648030044104103082e20b000005855420700118121060340d041070650442e8103006803002000c41c0c0c00202c64003281c0c407440c3c040da0f40c245204400d070214100d50005038403404480b6102d00f441020002810a24410508909015802200c00b03542050554010380940303840801030082c1800f41d407403807054844024261007910b60382d81e40c45c02004107076040001180c104a840d441c0c20740003402a0f80c0a410000009003080154135122540c0e03060382e11010f00354415801e400402c540080c0104c541c4500c080070155a51a00ca04046024080600c0f4a01c07a401000e03d20300d806200c1032107402c41d1511000b01440c0740c42c07515400c02019410641000101528000100e03084500078482c00c10080394188010440d585142088540040300a055120790540c44030404001070a02803074040b031880c14100140c0b511444a00d9100c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 436488435 1250 436487185 436487203
    0x6070309080607050c060f1303030c0e19090b0607020f0d0f062d0b010807030b0303040509100501020f0f100518032a0c1c02060f030f04020f060403030f0c05 69
    0x81d0700889040c0714986074043c0081c88680c9880c0d084901c69200e4005030001800c0440da85460200d4610007500082e01c640c218580103140e51402c9521044a100050410405203030304031440b45030740c00c08000301480c134090480340c000d04541c0e0700e040442c6a00071803446040000ea0600c20750315401508104016003d050b85800d821400070000d40e01102040740340341080144110b400044aa00012750010a0140124500c0306a40f2442c0a4803503040c207801a1101007102507044c00280320104803512020442807040d44003204400c1180c1c030348000a800c0401550365840d86800c4000e050909240000e1802440c0082c0170000406a1b00e030682c1c00000700130410001454000003507850780400011001001142d003950140c502e00009506842c0e0342c030750050421f50041c2c030f640704403212030f040100a401c207a40003524032850308226610311203e540c011951001c90851103000e1000f50704008100c00541201501d80529041c11074401401115000c600c81c0d080042d55220442000300900070184 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 436489685 1250 436488435 436488449
    0x715090e1e0a0e1009030e041512050709060e09060115090902070501050601020601050405090a0206071b1509051503010b07030c060e0309090c0f0f07030207082b030b03030906070309 80
    0x10082c10103081c200040c01c00314040484600c41c1515501c5070b5451071041c50341056241d00d0703100354128402d007800044c1145103a0f0711310500c05c0132400036216030306035582401c0070702c204068540c460620840b1002c80c0c507145c0000006046242c20081383c00b01c00558a819100081e1402c103140d08402411a502501500a661114000b1900e00300704070054001320700070b1000b40c0030354100f60b0f00ca0703081c80101c4008a07010b40090748016205070141c10407800800e4098040c0b91510042d021104410005c0030307645c1c0c4103c2c07140c0740c0c0c03149540720254002c810501800089030001d81e01c803010380740c002c1c0901040c007030640700701400209503007003600510780d4201440e440b203424050507a05507003e50b01ca0f000003486901030f0000c4000901201c2c603403821500c7c040320704131040e4140115900c003060302c1c1c2c00002d011810340c4140600801c0c90b079000c1000c070a96a040910107064100118901820509a1801c070320074517040c200c0710101542d001c426036001050568185880c2c245d1410304a8940202e40c0c0800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 436490935 1250 436489685 436489741
    0x2150c010b060f0a030b010825050708130e0a0203131e020301060b090a05190e061903121101020909070509190b0403110111070605090a0305030a030e0715090e 70
    0x241080f078403203010b000848410344041150950490054445507822191810045100250740e0044c0301c2d15040c1da4030800d00c0c0e14040d41006c41a40da8000982d02030210009001c00012081050401020080f41c3c000841c1c0f5041d0308606144070100e000d1104c0500090094502c8040c00ac06903900ca800309a03c150024002d21800e41c3c0c0c0c501d0030100358003009103240155900c1c8000b240307505281c00c0e05448d12001c104c0c02d425540c507081e200c0c5c29a1502502455004a0b42c42d01c10364408101d4280710051030081a10703007083c03502c0280281014000c07032100b607016401070140c03070015a00c62500da40d00040b01d091250340d4103800c01c00a0070b980440146074880c18080b100100700011002c1c09841a00d1080c69101c2851b00604015a10043c00394104da885c4c3c1c0c00f1000506c0082d11460207060401c401610015910382c40703984050441d0048200000042d5884a180711400c02c1040340c5401401c440300c211044944161004001c500340e40140c0d8900705501010440b500d0325036070080d8004180d1018a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 436492185 1250 436490935 436490947
    0x1110110610030201030b030c060f0c010b0a150206150f040b03010b03030c0c0906030a20040902060f090a0b0901200f0610090c03021204060e0c0604060908010f060302150c010b06 78
    0x600714004540400d03400a468074207407084da800c000641c1204400021f0445080100c1031000154541c40f4041c2460701d9503d64004040030b40f25441014082e01004100b5182ca40400100030f20b007503c01852481c101c0d114491906458540e42c3c865808210140c5011070200034401c0440e014000d02c2c00707103940520001816140b000f101041210340b00703904442e00c00036038a61400f01943e400d0f00c164043d08241c1140c0f2005d44030302d07441c06c42100e0340b50081c2c400b080c11074039a0005020354000d9465610f00d079070f000072185050300d03028150300007600c0449502414807810000007041081e001c0d90260038034803184141c03010b64034200000924580b12504661003460312000c40e04401c0700f503214045406081000a501e20783c068001e941c2a4081e05e0b5902082d03613610349450380600307600c1000084500030030307100500540300e400082003e0042a100c030140c140c944088103086030512208001c20350b103410703810302c0180d41d03031250411260020042c00d612101501c004900628501d0300b82d9030300c00400628 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 436493435 1250 436492185 436492201
    0x1302011d0a030b10170a0317091009060608192a0509070f11010506010813021f080910020705061f08030a0206101d060103110903031c05010803040311101106 69
    0x140d04140c40311242d9420256400c080a65038500002c400140480c40e00752540c0c4c1031a402c0010540e0200c040340c00c5910b600e081d0b4654008444bd0b4150a40e042d07a21800c0610892b07030104410206180001000f00546400d51034065201c90642d101402c444ca0b44003654108200c1c0003500c2e00503140007041400c481c10b0010002c1d040322010000900418013024090306140010710a0510511041c0c464a020b40c1c2e40c911905a28400100201e13840020411001b181007070141d415901b15060383c440a5880c282160824900803021a4442e6400c3c0100b0484000400c0401c80e15040010300d5400d0034443c0c000040c240d14240e464003c44818070020441c3d490003540025118000d80c4525445001d060b290311000031100f8640d59030000222140012403925403280c0e0100c5090310b501c102d49400c0c6984e442c0020705652054250b40e2003660408070407000d00e041486190b0060001c900214902031455941c103940074015815288207451100f4401407141c064003841081c1507400080e500d6074035041b25 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 436494685 1250 436493435 436493461
    0x30c050d020d092315040201050c03070302010b09091f0209031c030903030f09110907020106080f0703170309190804050d03110f0304050d1e1e06051302011d0a030b 72
    0x2054a0030300e81305180a08003004043d03c075680030701c500c000d002210f807904480c03000c00c032025204a0402c2000c00c1301d941d07500018000303403450500c250700101d002e41c11481003015185006d0481400341c0c00c00b000e410501c0c074162007107c0b495079541c2c02c0540ca403026100081e0401d190a8400815900d110299501e026410b52101c08450b11031749007084900c00c00c4a40c40211031961000814589034681e40750581e141c0881003c1e400b407c0c42c400400c0b82d03521010001e00308610041d203401c20703a200703807014420420341001c101501d1058000e042c2c1140f50102040741e41d0b0703212800e4040102a8440b41d401889002c40c1100c01404010b4001c42c200c407501d1600401c8182400340d0b140340360041c0d91040c112001c01000300c4044580042c995101301e0080d45500c13403810101c0340140031a11021000390009544100c140e6000e040199507003c0d044218280300003607aa00620b6251101e001e03008160050381c000d10400c0625441c01e148003500c080d00c1002c07419450709a003000d03000e62400700c1017242e200f401c24 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 436495935 1250 436494685 436494701
    0x50406030b09100c05030708040f02120d0806040e19050102070803180f0a0201050d0f020712030923030406050f13080c0a050a0b04090203042a0608090d020d030c050d020d 75
    0x200e60080140f081608120f9410942d038500040c3c0c01c0020400c0c85204e900c9050f04113004e00340080c054002e0381e001610b204600da02c2036030b40d0b8004084e003a041e02d030410380055100c01d00355030521040c04011102ca84030546652154034407002200d501003070150035815520882c2d44990303490f6a80c1400010000c80f04001c90644290f4407802c102e2840400380818850503082d81a11b40e04c0c2811000e80380080135209481e41242074941c00e02450b00490b40c51200010511342c9501d00250340d1219060071203000b280311035004d40303038240110000b05070701c00001101d003100c1c4185426900c0d04400303600043d5030f20543c4044000801c070000082402d041c049604900400308079291481c96a440080c040d55104a02c03c6280181050004001c02480c940045600c030f4480c1c060211008441404041c00c044a201400d40c107e50103901401600d4000a9064001a00c0d6005004600d4000d800075940c41a08000c941007503102c0a09403060340c0079070240c4448150312101903440384010440b80c401070003c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 436497185 1250 436495935 436495951
    0x130303021c17010603050601022109010905090f04110d020909070e100605041511031b01050a0506060a0e12031b1605031b060d06080313060234050406030b 68
    0x18141d04220a070080c030040c0a0310296214032a140c2e880c1001c01d900805004007090f041d0b0140f00c0d9214005039040414031045480403542c00d4a885103840010000d610b10303080b45000e42881c0b003d004c0601c0215030700a03807040d4403610f403c60343c0d10392001040750310b011044000d400509032001e100045c0c8001c0340e045c2c190345000004440c6541d5404103286261098850b26012030710801c401d000b0420003401145100c080ca091405644201030304c0103203960712a03030700060040d03400c904401d08840c0a0152a4011035241420b0000d800d04200080452050800307050610507154084001601c3d1401503051008450701541c0e15003440c00d0300308442e4040744052041c01c0c001c04030b0322031062044d50100026030f9400f4000300180000038048001421800b101550b00681c2402498030700f004038003521007c2c00548c0091611501186100e8102d00c440c1d41000042d03400030040c050340c11512035060343c1c100b503842c00160340103034070707031404100a410319004290030605064022040c0501e1fa80c04502503402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 436498435 1250 436497185 436497223
    0x30f0408092e0513050609060721120c0e0d02040e060c0a09051219151b12060e130215070b1f080604110102030c0703050c030c01090315090813030302 66
    0x100d0041201d044c4504400740e0401c0003a03003010320050429130094111494064002c0d458984251500c0f18403c000702d0301c8600c5420505501203da80c0e01001405104024110a0201c43c0101c034010306400700b240c20b06409a6000c40741c030800c0d036407140c100c603c032142c210081d81c1680c101005d50101c5688041c1703150011031201c0c040001c2c0e50402440318500c03003070910701401080066041034482060b41d10000c1c0c403c901129245004209548120003184c95080641c2d00100ca4035200036050302210b8034940025071400b10304120b100c200c041d00f00d070300c081000c0340c9000e165801d1000400a0000d220301d05e9a02d1804640301c03040091802c6840d0058007892442101d0000c113003020074040d4820f01400c68542c020700b010500282500e505078081c1181401a0fa041c08105041c2500d840d1a9900a41d03050303100c00380c03480c0d039030509225005558100f8a030260810741907484a0913500c294841568850359201c9040060000c9142643d0800c148280342181081e92820029661f240d0f89030b0b0a41c03400c078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 436499685 1250 436498435 436498519
    0x405030a1710050409051e07030201030e0d2003070506100f0b180103090c0806091018051b0303121303200a030807050f04030c0806011a030f040809 65
    0x44a1841c007440740b814408a680d103281050244006440c40d94402ca030144a4082000020b11000707440758010718048005100051a42c000101501c0703502000d000c60b50002c030f0109513219070100e034040d0741d004c80f803a007ea51005408061451840303000006041400380070f0500640d041a40303842c404841448c00308203400e07501d900d0074199511031144500c60041d19a55407000c0c55006c0e4016444c13207030103060b50084950b5074101042c00c0107421200c04190303030414070201c041646d40d8851011043c01902e508800d144880c1d0300c8a0340c9000a00203e044009401024800740d035080045401154000050554a0401003a144109002e42d43c00302d01041c15209c40c22460450380c040d161000020000030006140261004d441c103100180c69a400c200080052284041700200204002e5202d40003040060b4078100010f402d1410603000300740c00000003e400c484030105001038903002a03855031a80b03115201c80c5054030440c814680c0003500581c11402c1c0d480781140902007200018100075460348a01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 436500935 1250 436499685 436499717
    0xd0302040605180a0f090509100c140d0e0304120b010503010c080109020304030c24060b04030f080309100f0501080d11070b09010315030b0714070c05040207080904050405030a 77
    0x1008078058180010300911a0424400500d110803a0900d40600009441c07902c40d00042ca0042c2c031034000369000f035203a07000e108440f082040540b1418031070313a908025005d07180000500200036a03814005400000c9102c0c2d4006165a00100c0c104001008890b0740c2ca0f0b8418040b1302c0c0c002040d030700b550348608400000030103090600402c1d0f40c4009660b00c041960303084c501a23500940025000b5800c110900389050002000c10445c10034221095807d04603410683c50320500307481e07290300460303500300081c042000003503120782008018540c0003403403680b29641c803d0028a02402e0311400c10400e8208500c6403030f204d15640c89541038616400a40c5c7c2c605803080307015621100d20003c2c00340c0e81c2d03020b140d08010200c080d5000d030440410524001c12001c8005400701d00c0c1c080719030020b5801152000074816843e800c4088150b04505045030a42880d14907100c0d80100b440f5442098082c5800050745410803200e1400c581044c8002001041a41403c0c00c14a6407030308810603000100d802850a68603030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 436502185 1250 436500935 436500937
    0xc0b0a020406120207060e06010f080118170c1501061d0303090a1527240804020103090201110609070906120804031509020d1412192d0509030d0302 65
    0x1444643d15070040181e8403d40e90f400039800100252a46661101c540341c0c00f0a06200c40380c020318003400040c11460070158090300b111044400856403886400d81d03440000c01c030030950350702d140b40c442180d6158200c2c0d442e2641080300304958406a03203540400425a50b4018542d018000020700c00448a0000302040c90303a20710448100582c02240c0c0b481c00c0180d084250784101a0958600c0c0030a9020340740c000e03011008080c045076a404a03002c0c501403160b005282d611002003004c20300d070508190a02c7d80080d1045101810290401d0344070550842903901030030109078140c209200b110485c1c500320703000399103a00c401d01583d0356050500c14001815040c01d00c0801071302e5001002c207480c061071076440c5810b4001104149074060303125003d810140e501c00100380c1e0103502810351240b40d0395581c460076082960071461841c000000348101c800310382da1a080c1000d0456141880740b6088849900c80308281500301d683d88000300184c080705240369020018020740801a4101d84514200c0081581a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 436503435 1250 436502185 436502189
    0x4120c09090b061005160302010b100504030b160201090206030f0702060c0301080d030e0705181006030513080a0311041e05030a03021915020a03061d0108121b060103030c0b0a0204 79
    0x780c80b030a40b02103025468807451064481040d0b0402a16140042940210524030900140d0140c0d65400c901c40907410b04180c0c001c402281c900e045468141140e440305107920010b010124902c20100c02402c043c0d000350301c400080343d0000d00c00c6890303141c000104e154904040700c11000501900340419580803c54094905840441000e040d40d222026811402005007041c2900d15108524000a40d501e8281d9002c902c0c410081184100d8a08001c0b0a0a017003810f90110042500d0302c020800c1401601c6c0503c0040b5038403a1030305655043d2600100e0140284101a03588000002000103822040c400e403807029210741907400904640c1d031420513480740c81110000d00075810250361311185411030844a06120720513040462072440302d40d841e8003260000005200825518482400414006501e4000c483c0d2406180f800560414500340c0e102c50401030384601c142c101180020a007030350700c440d040b820701e800e400f10f0300b00d981c0d6410000d141c0211048151800058900400c0c0c220000c0c0c021a41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 436504685 1250 436503435 436503443
    0x70b06040f0504080a0c03211b0e0307090203130209090c0109121101030b01090f080d08090d12110417031e0307080415020d020c06061f020c060d0b0604120c0909 71
    0x1050142d24081941d1351b240c40c100840070820a2154080c88800d403219181500c1090350000440091050b10031501c000c82003018020300841a13403500c055600050030806607200c6040c00758494560700c400300d1140d02a1040294401589000c101c01d44000145290301d1400903a00d0f401701941d5015044041101790341c001c0c01c40e8003225a500440e5000303400c0b0b02d21703046041c90100c0035140d8521421005141c1500035001076040f501105510550045400c0e8100050748050201d1f20b07041d40303000d440d80110031034070406180c5400c034608154101c08103440042880742410800d03141c0140229850340d10124840e640740e140c0b1918003600501d11010340b48a02d000c1d1b01e55950729143c0f915880c4030b50404a181c10410340c0c08200f0010b40c20600d0018100c048001c00050561342400b44c100030101c03002c003010341c00305070602c04070703040b03c0e9030000d400b0001500940e41165a4403800d1308d2440a0525a65800e030441e100060025401c840000246015130041d0281200c0304c2e00d608440003038410b480710142c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 436505935 1250 436504685 436504687
    0xc061d0a11010e0a09050603190c050a14010f030b1507030201050f01060305101a0d02041d010602011a0603060f0a0f09050f070c12020f120a02012301060f020a0602070b06040f050408 80
    0x7008503820b5506c0030750400d4004003221601d000440040200a02004007142d00185c0d4240070040c60801d05d103040040c141d1060b81c2404103c0e082c00081c51903400c100341504054070703040c00650030b440d0828039000048850903c01c0ea6900e1508001e8080d14003655800502c100b95800080d6052080c411035000359030064034222000d260060105507040a12400c3d0182c540c01c1003d542e20b00700300e2006100030300d5002007820f0400b0598003c400c04050581c05a02564100840150b40002d2064041034080c0c2c00c54420743c880e1205400b0803440c5020850454011400d09808540e01641400d8001280d84005080c8015950850940140c081c140e80300808110203440080014041091040c0041c000d071045a9404528001c007501d01010142d0250000c0320024020320940e03420b001c0c14600313407940c02c140d5410a032020100002c0001c141b24420401074018645003266200f0700c500500d4582090341551210060309000d42e90b0003054640034400c43c54200b00003011102c1d809514459a0400122 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 436507185 1250 436505935 436505939
    0x3120c0f120403030b060711100309020307050d03050403150b1e0f0d08070c23040504050c010e010c0602040f050f030115090f060305010513050618030301060c061d0a11010e0a 77
    0x403286690001c2d004406064903694811026184d14010b024610700a24008d0400ea401c0014071102540559403003007054145044800542c400040340802c80e8010b50302d08a808009040c00c542d5406030b500001d01c0e26030620201144007131190803074003108501300c49450704000301d483c0c16081c100d402445503400540810300e8400c02d2820a0340488014041c1c4622454510380ea0303140d90400d0201d401c40004400c0c091214020034004800e902400c40080d00c0c100450f0610361501360750362107082e010754108000200d4210481e40714903100700c400c50b4000c00940d196034503030392181c1c10b0b5916400b5a9024428280303080449140502506040010a0449800050400c580c5002500c148a90a0500740d02c1e1000040096002d2152520039507020b600444515a540750082c01c0c40e4010300003107240c20210a02804d008004003c42e4111036083c00c00d040a2851458814040c0c119501c0c41003400d00c00501c034180c0e045d408180411050701c11524000d450300703280010b40b1038444100c900d54100e0f20b10340741 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 436508435 1250 436507185 436507207
    0xe0a0b0f0606041203020601090501060c0b1b0c06090109021302070b0a150f06021605040605060a1809240e01081009050f0706120b04020304030f081e070203120c0f 72
    0x40c0a0704103202400c000e1503d625000c402d11100c800e14401c600581c0220010030003e2a03d03c1000c0c0508220700d00b01c0b9000034107071980c2c200e1100c040e012688242010129604000039030b403c9030000401d00003070724038501e0000e0742d29000300040181a4000d001034141001e03882c00c3c5108a031506980a22051115219210014014124200540503508c2c07000030106811402e110036a000300032a50041c180102c0080785000390b503030681d1000d4000d0381811f405002c0c03580c4200075146003502600e86030040d0007100305002d100301c800f41c2c0205042e5203451074000443d00c0380903080003083c0c0c0c01d032030700318004c0d0b074a150108401c1c0003403160010b030360040d0a18007403002003070700040f404074061000c5580320814a802c00e07050800a61114000c500750044440701d50580340202040d8181c2141c0440c10f52a154601030304000d50040d0754810400500000b0320b0109280b17079400000803645c11070144074504050081c3d5254003500200000074523400000321100e40e040111840303100360803029405d12840c850 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 436509685 1250 436508435 436508461
    0x1303030c0207050909010b010201060b0f0306010f090b0a0509031b300304091b051309050a0f061e0e0903070b04170d020405090f07200f030c0703060e0a0b 68
    0x40310440c05402c1c40059603503516814a800344001100006651805100284c06c581c5182e01640300020107100910a10704800c0940e0f40c8044c080c00c2614008105590454511180d60081e144001020a042816a80c000090801400240e0403900000243d549071107407412145451a405007130040382d00214040c06500d503d100040c44961082181c0500280b03080d41c01980260240e1903441089046000d40d1190416114030355003042850071040c5412002d02d240c16000341c1d1441a101c00110358412066880b4130b2101034804001c11185884030280c003045c1c1a510002055103800d02808181d10303122181190041241c50029481d03c071440c4d440541c0305100900a543c0d54400114140c0e0b4034152500401203075500c1400183e4917404d10040212010000c1c009004000140c0c0410a400c1e800c60714154281c141d03541179020101c04050603607e0301c81d040c049023503d030001080240700004002002010390f4480c0d001400511020240d184c0d61b0000100081c103440345240218115080c408 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 436510791 1106 436509685 436509701
    0x60906033c07081005060c0d0908071d0709120510110901051c110a2118120e090c0304031d0a090f0902120703120305130303 55
    0x3200000c041c110040c41c0200b4010360b4000f040503c01d02c440d006008020003482255030307a200032001e035100c0d10500011804035400c920003049056000c155402038540b4006500d070b0458080c100d000300900e0151041c410f101c01140007007040b07942d603a100903940380100020020b0f481c00644420072038031542850701c8a92800e10061149a0f4802c040f60704140c82c841c044c40703003a961690444010079030520500b40100001030f01c0c042154002e64503140e0852809034001002001c400e912080e5541c040101e000b443c1401b8a81e0700081d000d81c0d00c641d900c03805140c460107000c0408041054004240c40520060001000f00003c040c2d1184400c3c054003000000d20614010103130114181d03081a004544000e5125070074031240800c980c0c010461036800a003187c4120800c201d2407501c1e0045170000740c405034050030540400030700a018140c050580f00481c140e408800c0d44048004007004 = true := by decide +kernel

theorem cover : BRFrame.Cov 436330935 436510791 := by
  have h0 := BRFrame.cov_init 436330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 436330935 ≤ n) (h2 : n < 436510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
