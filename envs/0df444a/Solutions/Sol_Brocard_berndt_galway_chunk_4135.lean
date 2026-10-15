-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4135
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:40:30.827476+00:00
-- url     : https://prove2.me/submissions/68cddeea-7148-402f-847e-7b479a0fa5e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 743525179 ≤ n < 743705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 743526429 1250 743525179 743525219
    0x70305060301090b090c15121b041703070c0801020307020703020f0a0801090f020a1d0a05041a0403030603120e0312030c0f07060603030801050909030315032104090606020c0d06050601031104 84
    0x7040d481b8030580816805441c60040358074150231465450014024002011a032040c01c4440700344408182c0b00d0b0802e515240e9441000c004664515043c1401003604050fa448008641c3c01081003105040e0b0100d107600840f076041c1d40c10320300c0d07034203c00010701d0412154100340c2a41d80390091480030702620124448260f4000d07100502000d8980c0f0030703103040315041080050000f00e01004181c0c01c540c1588900d500c03070700070150130021344044001145040300585003900020b031a0701040c018006200303040c0c601685070382030460544940710b01083d19000d44000c5900c0c40b020210004524954480440b030b44402480403055803400c0518008000b41454002900001e036410f0000c189810200c84590045e51444021401e40e601d01002d0700b4605203420005806003d4a0b402d94000c00c447d44200c6030180103841c42c142ca85017001203002c11109254031a00840d07021110b1a501612190394070303011541c01903404a03250b40e482c1d0050740500415071b00f101c001180003070005150f591002c840a0000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 743527679 1250 743526429 743526439
    0x81515010903031b0f080f0c15060307030609110409140f0304060e0d050709020307030e1504030503010b0d0204080a0605060103230a0f090b0114010f0c0308070305060301090b090c 79
    0x60610401198003035000c1c00002c010400040d1015120412543c04c1c2c048180300c0c07403403d84120050340d500807040d005400d07082900700c404138042801c80400d10080081d10070200d1324610f5442c140001aa4648441c84082d109650710190310007805107100c490145210003504c1400102d46910b850800038404411150090003111107000e48208040201c0e41220b01641e55240d00c603035071030100001800600000c0715140f050440001d05c9100074005036104800796240007500e40424403100303041c100040004102e00741560100800079801209690650b03164064a83e01c0710310b4861032800a22540d048080584940c800c074808215281d00041e1041c0401e9030b090140c04054251015002c00002510034116840f8001440b10b0102ea80035401d441c000203408284002c8948680c040d00d43d0a0b00030302c0081c0f152540c0000c0b1541c004840d00d95040452500d060000029200241094809440101019113450228480e60350035001303100c840d500610540c0d0325043c00d4003074903600d94a111500c0d00070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 743528929 1250 743527679 743527711
    0xf02030d050c2101230117040309050414040210050a170f0a0e0307020d0210030b0a1701060509070c030c210e091e1915080f120c0a12090815 62
    0x11416040d5842d04039007a0030310805103444040e050a0b25040c10885c4141041350a10345005825842460180030754040e4039805541c5040409100c02d03503c22a1000e041c00303640c2414480140c42d44171000505050301d00e403150720341c0d0010900b102d20584070080400301484590900a10100c081c5c2002d004000121040042c00c1c443c07007001d9128012810080e61140301e0710019030160030282080341e802480ca14002526008403130004038800566041417044040c10301e02c1c55107103482441a40c01030704044940c06102d00d884407004046419441c001070800c102c1c05800001c100800d0714804502d002c08843c840001403154005101800101c0c04900ca501c115011400c0c90950108014030b00080c90612803c0c0d1b940c2e258651380004500702001d045643c1c0313840108000590a400344042c1c54800d01410450840c0c8840f9440c1210840a0201c0c0e584100b00039548200300184580c21a94812014811584a44415629545103511541c11401010310380505102e03220940d92060103200006d0b514 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 743530179 1250 743528929 743528977
    0x203150f010905090303130c05120318030102090607150212160306060516141c120b01090b03070c0f061a0306090f19061e0606030b04090309060f02030d050c 69
    0xd941c0184c070301c2c01c61500104049550355985010600c4018000c102003c00a951003001c1012915004595011038102060f2810200403c00700b5400d0001b04a00a50400e0480c00c0025800d116031080104111402c0903003103c001c0c22030b010340300c0020090100c0c150510340106c0c40d030b00700c009528007400080e213408004190107000e002550701c02801d118074100d0340740343c44ea02c40e040e40083d0803002009211b13044401b407460049500c3c189a00c4016a581d82d034000180030b02ca400d41e0b4021042505100600105000200c003144c203480e03009002e4130300144000308a003070250030740c01400d4000d480b190422200c9000d80c01c480b04540e060f12000d41c102c1e101036644200c081e44911045006500700d410002c07100c1304001501d8106191030f4040c038070000b55107600b0a43c0c41e40c2c0e0303552500103243c0380c2d48501e42003100703035054030078039040700002c3d1410710908001d550014503001c05401480c0900012401e4003650520800507565407958403142000070741003168004c2e0040d0400303c54186100b0011100c00c030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 743531429 1250 743530179 743530181
    0xf061201060602101d07030302010905060906040210030f0f14240603040303150801020d050a06080109030228080c0309030111070c0b21070810080c15070f0203150f0109 74
    0x1c200c0d01564058a41d4004c104240c00240454000788800d40f0000d03181031340c0d903000a12152004600c86c2d00005101d8403645861400c1031402410101241c000c08104005a2a17001186a40020900d80090143d1a8401c20001000341c41511194503103440006846419041210303405030461030355405030701e985003220001182c80002600d410403008d1001c2400a400313500000240440d14085440b800d443d500101d00b20f03042444005401da88800500003480316510910000e010100020b101550b541c1d01d01a54421030010032000f00341d00070880ba40e6500c000b2954109969100c61096500c620306050036590b508661a518132070752a240c3c805604400c81d004560905501a000c403c005160102c0302500e9040396005842d8141200c00102c000598600d0242c4103e500e6110100e40d400c0540c0003802c00152500101c0003540825042e5049a44901c0f500002c4000d04e0003a594400e01132034241c060900a81c0d0007901441050041440f98800d65444c91080e200800c0140090703030b980003c0301c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 743532679 1250 743531429 743531441
    0x3130305190c09020702120a0f120c02210c03030406030b0315060a06050a0309140a170f1c060f0303170a0203010f140a05120c180126070e0f061201 65
    0x1442e806401c08100108601a000303824064002010b2001e020400392190342051840e42c011902407100c10b228404005048180c44804031003403030150014510359000c60304000d504104001102c0110050700008401008050040072019040e00c3d19240c2d600c00c080c0161140e81242c5200340680e0002d4114041d420103194450a00140441020f52030030b181654280e11201d071001c105a111800e84000c501d6240d40c02d10384940840c008d082e03050840c18400c54400c0954500d941824082009035100022780003039450305680000c1541d520300b90034032414002d003816800145600c400d64400001d050301324580300d4400c07104901a10881d681c00c10580c0c103c0c4024060054030110722003081c0700c9600c1152601c60040340c040e2484442036180c90000361944143d01c000405e552120081d05081e0030302440d07003404000d25241141c0300f9410903503000c25255030711a0700c4480112074a54404d0005082203500300030003400341c40c24900c1c04c0180400c00803400880d60b00d40180c641030140e60030300c0c505100728 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 743533929 1250 743532679 743532683
    0x1c030e060c04050d15060b09041409031b150f2a042303100c031d1b010c0b07020c040b0102061e06040b0a080109020a0f0b0403081b0313030519 63
    0x301d4030782030600e41040103030b2100110948980e00d1500c41c2102d01da00c54420040942040a080f5032206c1004040005682603d084440c0e041d0307010f41400200391002050341c0c103a1440758030500d0306284054956150000804460410704012400d105401d905000c1c1103008a006200c03482c101e0104c4080c104041000c1004454084410001001059007160020003203c2c0741042c41c2008902210009240a420b1541d80b00899a03c058075241590144a0130300c175003409000310034030707402e40e002c2c8107803180150580348400c643c0c40d103c150340f00d038031690741e8841490344a0012842e40c205014000d58070b44107900e0450041d0f161031001d803200e40c00003400c00d10034002c00c61890f080d8440f03580301c14070080c00070b0616070700a80c48010010302a541e07246800d024003440000041d035a0700354010010700841035400059403071341c040704c140b002c0030f960320441e819241c100801e5680d0b0b483c8140c0a43c2e4618422500b45004d020110380010a0721490000d0303001c4034000d0048413448203040c84c4500c4855280200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 743535179 1250 743533929 743533951
    0x170318070303090b0d0f020706150504090512090d05070602011410081b01090b1606050105040219080405100c1809020a09051905030102032701020a2f1c030e06 70
    0x1007000e91030020017000202c005a201185183e8601c20701c40581e089a4422581e45848052500c0b00855540c144030003460116003e1020b11810349840340c43c0e4400c0c0464440c0c03040001550038098803031003100104168000100e892040e0f45c1d0344001d00800c20307004130420036145c850120318180b520034071801c10b071001c460141a084440c0c800d275441e89511310700c041c0c0c18001001c000290140d4000080c0030f06d0703403403a010402c0b210704501d0980100c420513008240f05030320512140b84214400541e1251400751410103d40c291540d041c8640b81a4428040240c5a414010b04004082e072003100c42c140020611034000d03c1684400e03042c01070f40605030a41001440c0580108103e1070454020b491800c2080600b50301700d511100401d003603078400c6802c2189620465072980b210f414481124150026a40c002c5040280c520f000400c144a8410051140a0b5002800502c0002c0360700403800e21b07505030100d420742c80180c51840000640e001e6110042403407c0c05007102d100c400310340d151190060000d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 743536429 1250 743535179 743535197
    0x60901090905070503030a0e0f03030a0f1b0b0a0212070906020c010c06021e09030d110a060e0c040617150f01090903140d021c02070309140607170318070303 69
    0x603000c0014050200180c905100390200020070303840034801082d41c0780b0035540c0c1424840d03443c02840364001d540c4800798041c0c0d1042044a14440e840816030303d00f000107103842280014480781107242c01c060014064504107481c0280420700c0e10907402020406542d441d40221543c1e251300c141d0b0310741c2442c4904000758221100e105060740c414100c3c002098442c000050419000d0891305801040014500d6240c40c000603084049260411000103400110702d0300d04240d848460001e80c8030424800b00810b800c1d2030f0480b05103c282d0078001d680c07007480b010b001088940c1d582d00d00765a104005254130483c5009403030040c0700821010700741c18131901c0e4003090340340c250f4600300d1038500400012034180c007000078024442a011803540003c040d80d0342070071005a10381c07000150100303120600f80418030310f16104001003800280c01a02c100105c0f50810740450085181001084151049400040c480015a104820070501703000145000e54102c0c40006005105184840c1c0c0e00c0ba407900010f008550440c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 743537679 1250 743536429 743536439
    0x3140609251107080c01021618090606170a0b13020f0d05190b040201030c030501141002011104061d010509010c0b15061215010e06090415030b0108030c07050603060901 74
    0x200d00d8607003692903241c070101400b00206035506001c0d4a400c41a121307004244e41c84515a8100302022040280420a100c058030701040f2a00d8200703a100c3c0c1000a540b41c0342c80400b4010f20740d11040090460202828052001c3d00c040354036050500800c42e840200071002ca40034201c40310200102036030152134180c07400b640c00c00300301803809130030300880340341c45201d00020030759000c1620403030424412014405c45050500c0090242e13202420380600309032401004201c000304055030036100c444180c54803455071038561012805880e066040f10030000300014005501603200806100094101c440c40f5241c0c140301004480034461900e4540c0024907000041300401c4080c4003903038100007008502002d01d030b0303020040b4495030010b00005c81d00400724410840340c0d41d99081040103008091800c1070b05254103000180142c01544030780c80c0150b6440e18519000c5120400e024007440d08002c03002030960f96452550783c1d80c0c0c0004c0d00700105019075103000441e0300308042035074000d6030004d0401d9600e0b0300345 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 743538929 1250 743537679 743537731
    0x28080901020f0a080c0903010c0c0b070c110108040501091b03030e042c010f0c051c06051c060b06070f0c0f03020609090a0b0409030201060906080304050612180d03140609 75
    0x40c05e07800c484030381080016041c2e9000d100c0c4090a1341c141e180c3c801580340c02c0c146038081c054005c207620240b005248003c00003a4090b0315200b00950242441c1b4a15220b03800c00347d00425008070010308006400482c801a402ea01460f10b084a10964454104098490a0209903400c510903601010480215030000e400c0785000410440321600002407106071074281041034a030032804e8040800c01c00180d4100b000051300d111380340d40342400002d003c2c1c81d281c079000c0b81e18014144410300280e0104450700017004602c0d046400f40f02002041103840381030509200307441500c840c1048901141d281c4c40022000c500541c03000c01c60741c00030083c40c03c244684040c0515042e0003007124801d82e03500c0d155106140d0312445400300590082e4000900c076400c118001d8110f0356640c000100c9a80144010480307540c4403011215014403a072800300d541c0d2248508a039042c00d5080907010302d401000b220180307203036045c2d01c4100c00300359a1a00314030315251041070202c0e001058440d104808103040f141c0c4801288 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 743540179 1250 743538929 743538931
    0x13030e040c1e050418091a0705040f05120706081e1602060717040609020406090c0315060e030c0f040b030618011d0d0e06130906031401140106031128080901020f0a08 73
    0x10347c0d4400031030f4101040c1002d070940440e1490040361003c034041c071651408200880117080165141464409581c00e103994030780480c410101080081740004041013a8006404481c1209182e101c82174144201c00d0914058045043c00041c8100000600010311071800c0040040d40c04e10742843c591601c0d2120400380c0f8074200c080c3c0c0c0050300c0341d0001500400920450840028560300090500c00060301d031515a06280c0c040c0c4100503140503c0300035690003082101c0c81d040100d03038504045030108041000380076031502d1181d06028220805c1000328015690104034110b02000700010a846449200018140b0307180d0502c0e94028075a4a074414010707884a41c401000811075400d06142a00018040300c081e0004011b0a072220b004104106a0500b00e5a409203004020310414100d40c1c40800303904414440c420406480b00c0c5407080600a4404444104441407400d4400a518861510300e1040c034414070f1f40083c4a180000e10040818820f07560f1031031401a600e0300c0d0941c0c0d2002150440c0c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 743541429 1250 743540179 743540183
    0x12010b0310022a07240201060e01060e060904061212031b050a050304150c0207030b0c0403170d0b1c0209070903081b010209040f05010f1d13030e040c1e05041809 71
    0x818518089011302d01e403502c6400c68010b0b00d201e5149088201780003420740d600b907030142602246550050100c26044445201d00941c152809510b9420300c0001501400b10341d40008529180030f40c2d50414409130b015101e4815005d502d0920183d028a406110380c1d10541b10800300054050080c00d003d544124000c0d41c00c2402400e45a00c001e40203000310044a8100c4000d4025034090382d820020040d0103041680d0064a0050250030581783d61603414900007030200300c220104c0300058845200526500800ca2440007030042c2e0038101d0b2030400c0200c0001c503107009900c66580f800c006011940f241d80070100b9070b507001c45079a00300940c4d0007090903154905802040c60795024010100e060b11a84a107840311100303000c1c0840d41754035010304c2203824001c642015172280c034985480c4c9000c02c1800b040c290007002200c2141c5030030704681400c86090510980c825407190418040122080e4080100c00c140303018003106a10130740a4420940d0b02d0b02c40d03449a0b011140904105110300071481d848410b070b6078 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 743542679 1250 743541429 743541433
    0x9140c10050306012d14040b031314060f06130203070c0816290105030703050d121e0b01110a0f021017090106210312050c0912010b0310022a 62
    0x14414060903c0c5094032030120a03d0008082c0c045c0072000c1d4811035100303014240018862405040ca504440144001084403442400740b03c2e0713040c00c0213002e5072011501d8580d2002e4a12504018030000c1c41c0740c2081d1440c921038255909503140310800c5e4403c6034011005e54903100d0100740190f8540004d600312984c010045101024040045613850114050b07044440c00e128082e102c0c210001e45101030103070081070295001a0781800000d800150301281a11103061250402e51386154040152204400c4c1c0a490304010700110700300c00240d040f0226001090702c4000e448900303d2000e66807085400c0300540b02220303035a107050140c204522900040340241c980300e035007040c0304001d2401440c0d090b0303844000d681d550b0b01c04200d6002510109003d516000c0da004501c06182d890080c11285020300c1001c0700b5a545001c2804012004102c66009001902040300d1a160500440c006d28000741c0b82402030190111100e4600300500c2121200d155261500f040c0b0710700112096030010030114903804038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 743543929 1250 743542679 743542697
    0x130f060203090118210501060e010515030a1503031107080d21180b011517010306240f050102120304080a051809040c140306150103110d090609140c1005030601 70
    0x10b150500b820130b005c440040b030001000c0340c86190581c212400c035031001001009150060151b40e03940c1245000f01408001d04070340ba500c0e4410707150024030a56003107841130510410b000041581040301e1410607252001602c00142d40d50480c2c6464141c0c2c080f00b040003824100000070b002040460311500c0307480c00d00d0000796803896002e41c01e40601c0da50070103070390b026144401045882c1d2044091000340105241c0391401380100350f48403440b0303001800014580740c0c948082e910f10414001c440c441101841e5030341d6100c11b54030316001041403264021140180107480c440c0d414840418100d07401180d100c240181341100b015021100d41c2c020180700c2c02040754841c0581007956880f029a40160b009500c081000384c9800300c0c200c40e9511b040388090003a0854400c0000e0280c0d0741403198403c81c4207013804280380d88902c0c1031582611807254101407962070203805006004c019400a00028412130030214125000b5401d80c0d03591604105241c2c1c0442c4400b118811244103c0141d5085281070420f13040d9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 743545179 1250 743543929 743543939
    0x10030c200c1302031f0312120b030604080c0d0206010b0409020a05070803010e1504050601320c0d0e0303070b0604090f02030a0b04020f010905011407141002130f060203090118 77
    0x114100801002c0316907004024026440714102030356202c0305210000103c220714660791414001003941c0b51509200e07010301c8218400c41207410800c030707114000341941c40500e01481c01402c0c5030006003030540548a1ba9211600c054000240700b0306a80a10f40d905082518122190029600c10780d00202001028021800001d0341c000156018100304403102c001450000a010181402d1849080c80344d4104010701800f640c1051114280d1006104441c055011a0050301415044c0e42240340c0039080004020040c4a00883c095003030f20900e0303650109a400030030805d40d0702d0041c0380c009021a6007010110304540ba1030707403050b1285841096420034400d00d5400190801c5542c0f18107868114000c0104011850800c9036161350041c01d00304950b0241c02c0000080c0741104918070080324010010f02601130019084401600040660440d140e040343c255020005c3e4111104544801782c90040c00324a040d00d0040a40c2a81d046a000758100041d000046810b0040b018855018940d0b408020031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 743546429 1250 743545179 743545189
    0x1e030203090a0312120b01080f0709080313080d0c0515190c2303090a0b09010f061d07030c211b090513050405030714010212100510030c200c 62
    0x65000ea401038504c24a0b81c9000742407000c11100720a02e5600e480e108040d140c4e009a00303a5000b0b00d4016203441c007582c820b001566401078680041c40540701c04251401845100003126099079040710a031002840350b40802d035900e0540c0b0310024a5904508840480c1018810030703c1d40c00840c040002005410500c1c520041b64a4004541e000a980d0464114854a10362000300175810b082180c0f451850032a4806450300d013071042c001c003451510800f040741502c00b50000300000c506048100f021954891601d040c0e8079400200d10000a084030008000e1402489440c07000c403010703103070005180c0035415840071141031040e61480d6251f42d1101b000c40400645020702400c2041c1d142d40f80f0641c00c0c5010060440c0144089054550400f006c220000c1d0b00031081c1d5804641c0b00c40c01c0e101072850034401d24064001c003514481c20346060700401000c500301d51243e60444000351500d00d1846c03078081c011020380b48076514060218540c8510342c20840a05800c0e2001410090305076002d185003040055 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 743547679 1250 743546429 743546449
    0xd060f0b040806060f0a1503112b020c030a0e031903031508030903070b09011713020f0d030804150221100e09070e04080c030705011401050109031e03020309 69
    0x119500881e0034020450200103640c3c010700d00721a40b0b051540c00a001605d6a00e031801800c0313001d04504c44201809010341c000071412054808580e443d00c0b2007090b185042d00f91500b10b5401605043c1000090175200c0c800c880b07621841401a501d00300342104251040d180b1103040a415104000300c55a03842c01d01c12a030010700340300b607501184016207a08812910186a0801d0740c581e0030030000d0070a035580005244003254000841c2544540c11000140e42d04143d03a92645e4402880c142082581c64050031418404d42c802c40d5240380d05800c1909005070b4200324080100444c80f8070000ca404101107452407404034281700b20142c5410000816507441030702c0712407111100300e1034100f4000c0e84505a07465402800c20000480c140b0300d00012503035a620060710401e801d1803a24004142031129040880e284c108480049075038644a034036105000f01070410341c40068101c09400868550310608503001100d40080400b140d448400070441c841d6000220110151f12041140e6100e5440306c0c0054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 743548929 1250 743547679 743547689
    0x91f141f0c02090601090609170a051006060f080606181f03090506010b130e0402010c060203161206080312090c030a12020115060c0f0204090c0f0302181b0d060f 71
    0x2001e1801c0407841801070090010b0515814000181d07410700400c0d5100c405130013140c0701c29000302c03c030f030b68801a001d083c145101b034090128040d140000240825680103002112000d50b0380b0400925205c004458503071050350481e03405141044000d50801007142c003445800401002c80d51008040c10947d8203803c446640302c2e000c651210300e14818480103001c56801051050390803881c0010345104240000c0c994003540c400c1d01000b50103c0c041d0391080d1425800b00f0341c030110440d0b490400c2c001102038482d4803074001c00042d0030301c2c242c2d8000307041300d0080900f110038000042d4200905551202609074009000700c555118109100c1c0c80340e5410800301040f80d010302e61550201da1010802400d480f100075821400b0310790120100200d43c1c0c06500081050f400c281d003002803201c144001000790003005070141604200180204031407101036103400c01c5078400c0b20700c0020420492419074500c0d00032140c080c2e1481c14110040c03c0e1507098001018841c0b420500003a030151500d261408a030510b4202e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 743550179 1250 743548929 743548937
    0xe0103110d090b1807030b090f0a0804140409030503220206040b03041e2105130f060230090307181d0c10030e011e0b091f141f 56
    0x80b007030105107014540c1040b1443c11031007401613038a84003503582c00e0510006190b16507500015000d039005111103004481060282e0316910a941041c50560b00140502c002081071088480e0301407400d407089501c02ca62503100c440c195038a501104009600100e402c584012040d400c6400581d82c0c0300c007c00c0646540646503440341482c3c101901403000050f000306800d80c07201c2020011030080c0c0c1002200303401620501d1540980d112086070140101116581c45401c4900d0214400e42c1201c51182940e510b9822510705c000d40c0140109044c403d0142c041005010310086032a10507040d0042882d84c1000d8211000309643d0f0401d0400076001007490007429580d144c035800700e26021010a032240803050001c0c8007007680000040c40224030144200305055540d8284600300000703411069400020194000c80719140c00780c10405402c40c4e0207603034419a81c607800260342c1001404031003045001e080c5080744071410448440b402c054a20b59060340600b083c406410110000818201d0990060f52 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 743551429 1250 743550179 743550191
    0x803090a021512010e0103080304110d14070e0606040b1b120c1f1118010905041a21120c011e1e020a0e011b021f080a050402010f0e0103110d 62
    0x48010000f041e08603004080e00303500100003284040c400e50390041d80003401c107905110300c40002031640102500023030074100021003030705000c0ca000c1400e1003100c40549049680c1e40e6003a040001510940c0502c00110406001c018500078101d07100b44660314661080751803c00c00200b800c0529000243d080d400c81d801018401d1490300d40003100d00700f000c036820040c0308002c1c0300c10700c84c9018060030740f070799161407001508903a642c0c3c03040201200401014108000804440c4800c2681c8c8109038002030107950f6200030072043c244441c10103601701d24101d0103401d4401c0034114100d501d511040e01e0317071440d40d02c07803024210810b282040381801d900c0c3c0280001c0c00b840e18a2101200003442644407010910500100d0081600540c40f4205070709d091070501c51a1740903242e1080000d00d1280042d41007001c204510200324410003c880e020100ca407101c401c59038030300b49030a040d00c40895000340000c002c07905006091b400395049040c007040504000c51036094481a598080d0014403000402c10345900d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 743552679 1250 743551429 743551447
    0x1407020f030a201c11011109010c2402120c0a020606010f02010f0f02031e0601050a0c0c031703070215040c0e07050c0a0302030a030b0102010b31090b0f09060601020a0803090a0215 79
    0x70380d10b5002000e85c03c001d10000e000d203032503010140078045d000c0e81400100b07a000c00412000c8408a41640741400c4202c008114035503a01c0000d404c03132412008985400303000f1030300a072004c03400d8130800f8032164000c000e941e540030011240c2d04d0907041c1410a540d01d0340074400360302c100c50040c6595058035034001a101c0c41d00666080e1079808502d0b04000d4049070740280040c90340d2090440303105c80c0d5281006590f41c40d69251038040300100d81e0001d08014154038190f6400c80314072004600800041c0d00702c07074004100c1c014a0004a50544c0c00130f1054244603010400589001d80036507110b500d038104242424849504181800d116800480040c4c000140006074540c043c860852101000e10080009403003540102e00b180000c4110588040c0c1c0007007001c0300100d83c201080f002e8566034a010b21448480d03142c0402d4508059a14200d0140300c900022445040024005e00c11441640244056019529034016603440070303044603014007901a40b2005a02c0d03494980b100c5100003404282c1e658948 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 743553929 1250 743552679 743552687
    0x905100615120e070501030515060408010906060f0f03030c1a04030806012705130e030a08090709090b071107170f10020f0a05090a0512011407020f030a201c 69
    0x9082502c00c000d2030000b400b1240c40c8001240c40c1a104203080004050311010340b01410045141480c590100000070042010b41041d0842210f0301d10411042c0400340d00c8a1102d07000030418042e078030405414240410100b8410005940c03020300908444101c000c0801403090307c610100c1d0182d01140842d0180186540d003c4050851808200101841c11080e203040c90716000b958410113125007542c425414442c01660310201e000140325003100d641c0d03c4400800b5004e0003003116030ba0201d008050300000ca508480c09081c8415600540c1d0000c80e9440344002e40e034030702201549480b01d1094402c082141e008450310022060030f604000c10031070340d03030303146062400c01604502401d40e401408403140091562007074610700005410001d44130000130000c622003034110307800254000380859080306001d5040d40520015100c090042d90603685081c3e00781e035a03100c41001c3c810030742c3c8208414900c961082d0400741c01101c0707040d1581c10180006030748500e42050108001034410082c054011001d0700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 743555179 1250 743553929 743553947
    0x12050c0d0c0809060c0301080a0305070804170a1a06010f051c1e0510030206090d082502040b041a06070203010e0d030b01020d090f0303050a022505031e030a030905100615 75
    0x411724000f031440d0304140b01540c031001403030401400c1c0000400e40108204924040d9800340c0ba54001d4804e80d020b00b2150140d81e01d0101c41c040d84d50002d03801c0001d0300c2603500c1355064402c50040c1c55480540031221030440d40e80d0f1000c3c07900802e0303000c01040480402003600034409540004007400c0424403401c42c0003001c131071006e8146551038848079001c10040e242d403c244c6481200407118015601170360b0410780c01c0b6100c3d0800d29090050104010082c0750024280c6104143c020784040110840d150280401c8805c21035903961110542e4100d60721601d0200c00410380c40b031000d0000311340c0c190300803803481c507002034103d116002c01d0f11601060b4131541d040000f44940d00d0749150684400f441d00c1059a10b5210900003e401c00000007688a1258000c000c070201e507840300c8403100082e100710708440d19201018002c1c207200f8054103495210002c195426010340c0d0100b407002e1481c01d825440c09030300600c41c0140845041c0225140703501c071070489110310f00080820200907003607210008070003008409 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 743556429 1250 743555179 743555191
    0xf0c0b030a0b06160201030b030a0f0308011721090f0324060d0f12111501091d190302010b121609021809060f03011e0e0a0312050c0d0c080906 63
    0xb00501c42060840a600c0b00131840c107070282000200c50300302c0c3e000300b81848940e240241100c04005010020590f2001c4e01c14102c800c5640c4800407203145003600e94580840168540c0344c032103051518030709100d0300307801003640c40c0005000c10380c040030145c00f080c03e10440c1669036080f040350121030200e54030f1401c8511342c010812155503144216669525100c02d9111001511041c1105003141849000341c1440036900d408100301c40d440b0b241d0021045144400340580100c03282089400c1d80391400246000c01c0301c0d5044d4015004c240c6142c1203902d14403001d99000c2c1d08640d2178095002c041c0d10380700352840d103a00c4500d0280c0350b01a046d41e0059004400c0d90b10514006104019001c00c403a01200400c3c142402207503c05841d44419000818580750f8400319581075103040c20016050844034445074241c06940d4003484100d204911a0381c0b00c103580e480141c0481d10000d0b082c0100c0f16103901890b40700c401c41c03803d00e0401d0141100e000c2124001c2000c00003090004044c40312024042041c40e50041c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 743557679 1250 743556429 743556439
    0x1306031a0103020a020d0507050a0f1112011e05042a06030b0a14040e0c0907020708061308120a06031b0302030c1906030218030607170f04030206130f0c0b030a0b 71
    0x1804548001c0d81c030151b0120390303000c000000c036000e0100602405100481038001082e0b0480b0111800c04c2c40059290700e01031481a45040c40e51742c0c0340c610601404c1041c403421002d0040c0700807a0303401e03d405054020011140040150a00c410b0f0340c3c03110000681000f805c6010707207089424640c001c0e044a5240d440c29102d01406001040045100310070038555080940d004540c1c0026001e4240c60f069022421940c002d40d034504101c10075500144680440344034000302c40294071500600919420a2180680910301c1000360f001e600d0b0907144941d0700b00018020008545a60781c03103d441005584000c41c083d15808001041540b5040046811596040740c21825002d4951214203201603640301d01c00525030089421081e80f606810104c0d00703c04040c09499107840c200358000c0c25a00b24445c44140c501100c00414882e154905e44144125419002840c0503202d11142a200380c003912400c803042c85000c0545030004440e0f8003158020441c2440f03507602d90402000110985c1c41c403010840c010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 743558929 1250 743557679 743557687
    0x120218100f080c0a050d06090c0303050306030d21090c031403031504020c0c010e041d010c0201270618080a030605030705010c021e0616050c03060c030f0f07051306031a010302 77
    0x16916a01380c04101d94044410049040040c03a04001038409044041c2a202c0f110380000b05142d040801184142c204605032410401c001805503002c0c102d001e03180d0170307605d204a0f4000e4042c09583c800c107034039400b501c0f10004042e507a0341e03120400400015520001d8102006004c040d01806a01944400040701d0035411301d42e0082d0001d60740c11100d2034590410081c4000030360a0f44030307688042c84820713594000300011980e020542d4041d04c40051148011742c42c08010707413030466a5520132a8108004806001c080f035081c1c0fa0900508000d43c011012200390711580400201034100a0070301107030035100802e803245400101410001e071503002d9418010f101101c1c200503511800e859000300c6107440700241c0c8080000208007a801b82d18209406c0700408035100007480000a00b43d100322004504883c41642c642e40041440e000942e005000001c140c0003154100c1041280150b1003009071030111b05001109042c0d034090b4008c2e500c010042584d56940306410200f00c07400c1702044500b03003001c1d868 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 743560179 1250 743558929 743558953
    0x1150f090501211805030702031b010c0627110a0807080a061a0d05070e1e010510020111030a0b01090812030c0a020f011a0f090f01120218100f08 64
    0x109201c00c3c8020300343e06001d00400c460140c40d41d0001c164031028583e800a00d0945140c00e5550780c2c006201a03200b03100d402d42d003035000c0300144401107414406940b00f021080c490b680302e00c051704140c041101040760f44840c2c82c00c0450001c5110301007602a00300c11200c0501d01040c840c0100341d40c3c00010701c580250340306000e801d03000210150003503404079001426a502c09040314a002d07140700310765840b144901544061120004140050303890715490301c059500c400b0800e0300e4540a1415014a48100c000104400d142c8008402e4611202c0d000101e50b080000014110540c812640315070020380e241441845540e002c00d5640280c801c2000800310710301400684120350000030180305c1e200c5000103006070310510911007060000f03d2400244410764840c08048580e55044107814003802007195800070364600080018050003054120780d8199007050340c00340460321480070503a0000d43c0c02280c10314940941c4450b520403034405203c01f80782404c20000c030761900b8803a4001d0b1540d600181d403541c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 743561429 1250 743560179 743560187
    0xc10140703060b0307110f0f07030c090b100c050a02130501090c020307330c05091e0d110d050a0f0b060604150509041d0a1202030c1002090d0b01150f090501 69
    0x10b0017a641703042a1407103000c26803841c0d150501c02140e0034030740d000d007800b418030500b8000b80100c146c0f44030b95540e0300e1650b01d03000101c04450380e210110fa444280743e0010741c201805003c400480034010382c16507041c400260042640175002c0141d00b0301040c0d42c0c40040101c7d100c0c40c41202210515171001d1444c1c80300d10745505200034a14501506111640102c404c4142a100309030740559260407000d002c00d40c40041c0c0a070094003c0c41800d8001c0d0350840840c000b00d0074036903420303503040d00040104084499580f04c02080d0011603a18682011400d081c450108608009484203148604060300302e24400b0b143c20030080d2005844caca80507000c1804240031620341c040000508040500c0c002e0307200c1034041d0008014221030800c040e800c4446c20301c40c0b1900c071808a1b003d14124000c6c60068201e90380c5610490f030300d02c20110155103980150741040e2050080350010260340300300406c003034100e50326034584072107148003070b80440d42c958520780080400d960080440c81c030244081c1800d01c2d0f014623200002c0c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 743562679 1250 743561429 743561431
    0x204050a150302040e0f04030906050405100f021024051503040602090f0d0f0b060603010b0f072d0b090a0b01050d0f120903030809010b0a0b0a02030c10140703060b03 73
    0x900406401c800c20264601c039034140d03401800c00380300c5040c1604084600180006040d01d040d0000f45d6191008158180554101c07011600b010701b600480b02180002242d4502d10000e00d442140516050000005028050304540c2c864030090242021101d20040c0c14003841c507030001e4020b10001500c0010221907905490b400b90708001d0141ea5440c084d0001045003d4000401c0d83c444e00070b501c0c100c01e00c6a0900d00b480401d2180300c4038101ca80b5202d041100301e0000744101904140100100318404801c0310190221600c10155600a100d041c0c404107980d80ba0800044c103000504140300040c001e0340d06c2c1142c1c101e40c0002c040d0030100c20b103031502c007100c803014041c840c014040014041c040080314500980707565041031040a040c541400000c0240409100075000a1204030100784e1000e010720808101c020010300c0c89040c503242c03080d5051150011001d18056020501c81d2284204d028041c2c0c0403204800c5800040c1806151903569940401400e01800c052500c04244250035002d0b08403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 743563929 1250 743562679 743562689
    0x50901120803040c123219050c04020403050f0601090605030606091e0a06061205060a0e061512061309050d120209030304031a011706040f030e0607030e030d030204050a 74
    0x1540d0b00d0366141449044000310394080d080840c6544c0000091005403501559800021008032040010111220210101c844550200364200c4003055916440449850102d14440c405450526025100180480c0c1040c2d2054a4a42103c281400000302c22b1002c24003500901c0010040c0c58200701c00b080c4c1c0c6120082055014401000200740c8041d510121045205641c60380706c801840d0411500001d46294030480020685d01074080d04050038138001d141c8940704c0030782500a039900c2c080c0c801c002c042e07005d410380d40c110140030340316000280c94800402d0300d80c1d2820700000082c14044180045421900c490791181343c40c0800d020005040030a0300c8540c0c04240c58940c000b10343d4003032060020300c621803500fa4180b00010f030000401401c41c5014600031b0507101e120348107a0740c0b2162140414180d9090f407825130002400240019074418103898218020f00e0902c0d40300410002140d420f0380810b000741c1c003291005500c0f950a2404010031a22190700d8902541480e1030074001c25040c9425020b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 743565179 1250 743563929 743563943
    0xc081303050a050f070f1203060e13060e030d140703050411120313060c1b05010917010b040518070b041404021c0504080301181404020607170d0609050105090112 71
    0x1402009a100700b0503100904c96030501c403a80c070505454000c0103040ca4800031031300c505842104881070fa02a2142ea800c4032503504140400c0d554110fa000c1490041220407103d81307070f980c96844407188081026044d9043e8110300011001103041b43c0c091894001005e800402d07040000704400a0041d4000c00c00f5030340e06461043c0d071000c0c1a40349500794060300700d510288440000d00015085d6101141204c1c1d10701403580000c1c0f56544d0000c0c1c2c484400035009a5020513040d1004105800e1170f04100001e0701d003018000036010b03505600040655509a4018022a540d000c581c83c80342d00900000c0000c046500c070302ca107030920340034240e00400044514148102d0780811801418040d881d00c12008504036a020045442c00d8545401290800c0c00303000391440c5800c0300b11070102054800c0380b19905e054200ca5101d56035907400c000c5d9562103042c04440e40d9504001145100711a100030340b064030545400070030214142a914000c98605a100910461080d00100418600b4540c2c0c59407068120b11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 743566429 1250 743565179 743565187
    0x21201060b1344150a0209011202120c0d0b0406060306060e090f010522060807061205060306040b13050601080d030b040b0603010302060a11031903110319050910021602040c08130305 80
    0x10385003130100c000c40b14000580c40004000d0311a01c942d0040c030745d03140e00f40c94020781d1030544042c0c2c1c0103d0050000c0d03c00c02041c454013041c08402c0d080090311000740c81842c0491010106000f16003a0741065101d180401c2d12039400344442a040a11402c013000107480d00203003440c2c001c1d4032825081061040c01d006005040c80e001d03201070900c0e4201d0103000c0c0b04005003c001c2c2c1c0c80310480e6484119209410010307550440540f0f07451308038000d0b94015075005004180c40d403207075243d01c83c00020240481c090580c1440c0b010001032006d0080c94000c0000e10007800a11300303207160103016102500e0708648101c1c90004c8240143d5030305000d0301c1c152601a41c103691075428103c0f041c1c0385528064044400c921000c10103034200b02e4030702e0f80e40b0b4500b00741e644c1c01d000181c4562401011400203590041c5060480804080444165800103500814090443e0740041c03605d000002242c0c0416240d588010303c465075201581020f0144440500702c40c40c010304545003051495007c070000715801010003600003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 743567679 1250 743566429 743566559
    0x30203180f0f0f15180a0b0309060610050d090c0501031b120213031a09100c020d0f022104030b07020a0305030c09180108030c160f03021201060b13 65
    0x1d40c001e050001301940741961a640c02004140303192030011010311504c02c455001c0b4000401e40c09590080f489840140078a460b90f40c00c02203006500c2405008005046c8444d07000c0005030300521000901920904413014103020004041c2c0701d4600082d4400c1c0c58003008001140da102511910441c41104016103ea080c4159611019410761010f400c009601002c1c07810980e000540d240501d00030f204669625014400c2c1c18280c40c03501e80f007100035070000740c3d900a44c24043c0220b40120309041c0306458020074034040c1c210980d000714034481c081240124081c010001400038a41c1c00c14041e000900170003060359001007a0b84002132607043c111501180021361511046419031844100d03d140000070341c1c44540c451350b00e4100d000f607170000340325100e800c18202840f00007410680b136110081648080c207580a110000d801020515170a650720000002c0002e0403601074842c604060040710403031307480c18201c28090340d800240d00c038030303039403180c4030b00502d10848511801c0301100d444401031011360703003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 743568929 1250 743567679 743567689
    0x1b0212091e040504080d050603071208030712060f03021302030f011208070503031e150120070503060126030a1b030e0d0302010c03110304121119030203180f0f0f 71
    0x71101d812a041409000810002030058001c0c80d08011041160fa510b480030150746011610500c6040022400c3d520041a004802554000e00740c0c20642e4840400c3d54520040300c80342c0c0d010304449040c5590074400c6103000411640384805200040d81507040038071142c04e901c2c10600c5910b8107241d880e4003820412800030140d0f5051030308602034035186e02d061461105101e0054a0000c04031202034009164017513900d4840f10380b500107035103008461b05000490312511001d512803643c640f04518001a42e60760401605000c0e1180c00144e4801001085200300c00702c0c101e0b1041071460f08244500500e0aa022502d610102540d007050359101c081ea0a00f41d6200380260003054100d0001a0030380103168054000414000c42e5035002c02800030084040c0c0058007003070350300910314503840b28901e0009200d00a46143c4005183c161401034492605220b203940c0b000c0400c5015030400700702d074888107015a03007080f06000196180000341b903490000a5800c1c82a0032214828040072000e05410744070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 743570179 1250 743568929 743568979
    0x21060f0d0c0b09010c05300a09061110050108030a020d05160f0204090f0f12021f020a020c0d0302212d040504022a0f1009080702040507031b021209 65
    0x4601aa01d03001388a00401f660042d02c5076042442d0590300901c101d50000345012a031002c086640c8900b001c41c02c2c45021114072203007007100c0d01c0d54425000d40402d221003501c5164001d0003042d0044d665001c01c004042d080004140708038003070041c2400920001182a510020529417010b070101c074008135440094014664500040c205142884014040000d1800680c510a011380e2134007454410079941241c0c0c514152031409104005980e076840d1080042e000f8025006140c019201c002c3c4611011681c84082d040d41a00184c4c840030403180003401c0540e010400c49500d1070030030700d0300c000b00081e807084101070f8141c10300c1a8140700f07202c1d8400601d00203036030180c400100155507a1900403c6c0d113000c00114000f003509000c0355000c0c183c034140700160400b400742c080d5002d170090f0400c0c40801d41c000e110603c0c06a803401000c001860040e07581e88101441503081d5100041e09102c40081e01c52900f400b802488250342c0035000382c06000d004642078949283c000c4a500c0d032920412615460b107800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 743571429 1250 743570179 743570183
    0x5100806010315091d070b04140607021c0c0819140f33060d020603130b0406090303182a170105061309020a0b030c21060f0d0c0b09010c 60
    0x40c60b0303c040303148007031a044842c0004c425010020001a030802854440c00a031040205038107040004201d0314064040120600c50001d282c242082c1c1c05401042101102824003841c003800c440891003040031741c407042005000741200420400801005618001d6090790f4050310b810391104402c0c1141c0e03020081d15a440c2c0825090f500c140c2d01003144003c104100c00c400e1410400da0121b0200c6000301d840d001c2e4840c00d001000c131604120b0640070304c000d95201030505018400800b03103040214204032032860140c2d00c108400207500100d400c0060494001d007611420280002c0030b280701180d00c8050b003a912000d01200091100800841c0d250791a420790311005540c11000e608071112241275102c503110310010f503101800c00080403032400c11190701c07081c006c0d44450300710303c180401d18112001d1980b05803003000042c517042d4013280c0340700e8900340c030030f0800d0b80b621002081050134104642418014003083c0c440d40b400300410b645500c212007990280d249142c10100714180640e01c02c82c0188203040e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 743572679 1250 743571429 743571461
    0xa150e190e032b0f0506030606010e010210090c17060402150c0a1401020705070e07120b0a0509040f170a0c060b010c0c0b030603010b010e030a060f020f13080d050301051008060103 79
    0x2c000c00e00c0d400100319800d240f00c4040d52400ba03003c40b02c00028020144980b000070082c200641c1c0305030040d5a0850075020484c11072113240281104519a4802c00108a00520700741d000c2d5483d04140000c3d400c8400750f80d030f9003504603a05000050300c4a007000080400712100080d00c50301e070002c44610b02004a90080c0904040304891480440c040d801010014021800d550550f500c45003030400900c0140e4482000482e0b44c1c480301c94981c03aa512001500c0f800411034903401c1da68100280185100780c030140c500501d03c0d402d56003088000304203108510128551181000501c0c00003600c0d8032400040a0f1441d030300e60580c0041a885064900e071b00c9030740000c0c0106c615072226181c8125802c00c0390340078042c0d0b2030448003a4656000b140381c000c1c00031000700102021901d80d69290050028400e40a031616001c0c440c2c1c00072081c10070b0141401ca101c1c203450022003842e0240c1c6070724040c203144010050140400c01800759845402c510307c41000c140c00c1551641e00d4100040b8000c10540c6460340074a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 743573929 1250 743572679 743572717
    0x40b150d031701050a120308040303020f0d230606070f170a0206040507051504031e080c10060f0308271903141b0d020103060b030a150e190e03 63
    0xd074210a803004400d000c040380410070780c4c0341c03402e000c0c14039070380d0182614036000207814200181c0300f210203aa12601c030b450090f09103104800c2c0051160410148030220588400b280340003e00588003040b1000c01410892120b42410f8002c50400d20501c440038040f005000f01c0c8009021070101c600c0d00f240e402c240f441e680c800d80440002c0d10340609903011101401442c500081508d848101c14051862030089649858650364420303205c01c44040d48090070806c940f2007000070810303a1000e01000050345024280c0403400b0f014072811100b840c5c01829003540000380500110300c01d070007500d1101170340c01c0d00385241040398110f50b035044100c0c90b0029407000c000045240303960400190700e400c5a01c2001d001e4085480c840d400d5449001110641100c4005926004200c0c50506208500e0a0060600140540d11224113403510f42c0300b00d5129540c0c41d150004078102c55100106c1100401c480b07000030340542440d840c05400080d1f00c4801103400d076260300c03240e2030781c032401c1c000c5400303103000f0203a02c14507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 743575179 1250 743573929 743573933
    0xb0105042309090606100e040b1305070306080313120f080c0304060311160b0709080a08040611070303050405010305101d0f06040c0e06030a0207080c0703150b0306040b150d 76
    0x400c05040e08120b000d000c0700b002040d5032140010b03a95020300401031030100d0303601d034589081303031000d1090031060390143d04d1341015a840e0b1101d80d4080d14014940038081500e140c1f000014003a614160f00052040e803082100e45d81d0644090040015603c0300002540d1060541c1030000c50804040301c082c1202d1000200d100e00300034004020812581c49031001e000c42d0005a06104c40e0780a42c0c518080445004050640061084c1050765444101070920041c0f10307444504444c074080a00307004030350124001a01b88400e940020105610610170001401c003c0d0966400402c94040e51081c6414141c43d03001054082810248400140505100d2110080c00b000c0c072025025100750b800307030070303984035100416030fa404c0a00400e6001e0f05140c40d1805103450010500034550710050400ca0b0541d82800b0802c00180703250010001c0400300300081030850f0850074003080c1030034238444440202d464149240c010392001302c2e440340c0c0180c002c1000012551407110040500000f0021a580a0154500b000c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 743576429 1250 743575179 743575229
    0xc03060a140606030f16030e030d0f060807181e0e060f0a020408070b0f0723060105010f08160201060b0d060f090207050703080d24030506091c030b010504 68
    0x64100070a1900403020303220301c0240f060b81d100c01c2c1c0b0840d40405260000554043d4614001c21403104545400a5101d0100c80143e056400004c070220049840d10943c000300da60f103000c0c8002030303d4088058488145010402041c04080382c0d0701108542d20307072521003400003107075a100e413813094641018088007007030000058807200300b103072521044801c080110300e0742038280c070990b010342c0d05080003851968100111400d04c3d410841464180315010400100001d911881001480002c1c0088103403400c9180d1004c1e0900b0301c160041030410103c00800d12a655021100541124200e00002c001c8007018904034098411a000300302c0340301c40000d009502c81c00a5100c2001c98041500b400c0c04a9150f001c00000da108405026200f903000304024404a446d900060800e044200000200c500402900742e6684002c482290b415170000e03081001800000d220456022080e0406404030340a28442c92500180000c40303a01016540c1c80c0c0340e009071b400744089030041c0181112001c010042d1b500d2060b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 743577679 1250 743576429 743576441
    0x11b08030c2502060919051903050706030b06040302151306020706090812070201050a180e180d1d060705010212060f01050c03250209070e030c0307030209040b07020c03060a 76
    0x307880101e00c200303600c802c2e03010302d02d03040409030b00804a6251502e000c1c108143d1550750415541103145035800000c40d81d480c058400310ba800808090503407280703941030007400d0642a500183c00d15080111031101641c0300e004581c103580e811100390584490380180c5017141c0c09000301004000302c4c201030109a440c1c0000398941113408640e50740d408541c544100544801410992041d080e00c24000c002c0158054409031010400c2840c100d0410260280811034010301c540c000240300352054144910310016050102c00303403103407000410040f8008200106500812040e41603a0300c90b00c1c010740b0850340c40348111010a0b4104000350b4540070741d0103140b101141d050742c1040c802c0203800046080765006d01c0c15590b01020103006142050303180100c516100707103031082c1d0400c3c4109071038039940165111035140c0e0203104140e03140500805d05006140c60b0610100800748650b010241c2007005984959146a0055000c40c017034005e911b90140c240d10345a0b540080c69454022071040160042403a4408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 743578929 1250 743577679 743577697
    0xc0309050d02031c05060609030d0e01020d17070c11060c0c031c0909110403150f06051504030807081612144609050301060807050f011b08030c 63
    0x91140d2245140099a407407241c94540f04d400041d81d0421001c000ca01d60110703a005101501c0d5520306214180001c3c20040e04a06a0300070841044440c0a00d5a0400c81202c4144480c2050941c0d001000039001d00704100620310010442924546400c00031600740c20a943d0001030403064480011240080e210341000c000180030b0304c211036200b40c000403503020060011043d51a940100d034142280b20001c3d04070208039922080c0d04200c0000040c10280b406540d034000100f000603080107001d424800e650341940400d10030301c500880584001074030411a070071a03030301c1b00f041540d802d1107240c290654000c02001c10a444980c69941d01886454000c0300b90b061035560b1507214094044107941440c0c010501205c402001d4038504804681e94102c0907410014100e004c001406840400c00201901061000c0000303003d051003049203050034018000600400c5d00070f408440c0c02d0901280050f00b240800070304115401100c4034a5401803080f5141d15508014180da0381c1c5803189002810b58000d40710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 743580179 1250 743578929 743578933
    0xa0519090f0b092706013507180302150a0c0501051e09030711130e101e06080d230f120708070206010b030912040f050a050d1e03030204090c030905 65
    0x403000d004007403901c0c404070744000e029412202d171256401103a28100302580c04000054183c1080741c044880422840110342d1414440d410b480c25910041c50034108500b110195400d2800610040c2e03a0f82003094401111082182d44401c015402120100006400038216500c1d040521080c409400e442110496804400c9041c5890b00020a581e034800e00402074070b0f50385030144030f615900d002a00442d03421240c510115503065070690301750800f04010240c03050f00d03649216000b0240d58202d2a040c0c3c0d241b1807141080201e141404068070b6503070514402c820072030009401200400c1c1c204a2018a40740a070b03900e03441c1c03604100e600c0010343c0168441100d600100c80041d102c02d12802000380305a18943c058021a440e10401d0340c01c42d00040c000c204940a441500d20b4402502000f400051081190740c5030040d2400090007e042100e4001e20300401291101c607000c01c6204604100d4229400c09045071020b2604046000380100d80100d940c1c94144031040f0405941500440301650003601 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 743581429 1250 743580179 743580199
    0x12010902040b0111150a110d05060102210d0902041103010e0105150a0f14040512240112030f0c020a030b04060e0601120206030a06030807030801080d050a0519090f0b09 74
    0x10044d01c03601044d00900265502c07880a0240c080004d03221590401c4010b02d0115218060000c10441c42e009403050700001603603001000041e42c0d04000404020708042101c081c1d43c424801510740d28401c8405d03010a054a4049003011920380344d2000a001c21003000780ba45a507107440a02140031300c2032240c01e200b52000101c10b00c00d119010119291128079880e01d64044d5a242d0050710034036003449051690000a200001e07607a2100031590241c8007510f0060a1881d21b007074144a040d4104001000d03030300100c1c500502510360743e081100e802c0c90b00343c2401008007014842c22205220748440003500620701c0c900000801242c0c0354618043e920400b006d101000082c4a107944d90340c8244500031007102c60341d01103005410490300464000720010b1011030025100d88031116543e0000300120006503095004010000040c000e00740c1c00c2e10646020ba103031070081c0380010b005014400e504280a1210211400f45c54028104d100041c11444c191100c01b035656000102c45801c1800c115004848a40c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 743582679 1250 743581429 743581451
    0xc06020105070e01120504111c03080903040530070b091e150c01110c0307050f0a081b0319260f130828110a030206041b051201090204 59
    0x8665143c0c4100d040e56200d900241d0718031070304040c000140040d251a03502096002c1c06482d21030010452060010801140c0b640e2480c0080045500404500c1d050b081840240729a5581041c960080d030000d4a01418403540516120100704034441001141c1c40b83c3c1c80001110102c400141c001d446d0100e6024810b5040c41c900344242441004c200c43c0c7c00280000719038401c500d000b01601c400010030000040d0aa51000c58014551007900c00090395400807401c60304100041050440241526024058600301503507030410500400201100680c0b000071002c0300e143d0104241e81c0c0038110090250808100c40c0d00c00f80c0a1020040460b80c07001c502c210b4815040c00780d901d40350251803960001403040e520004005032041480c0005c07101c0d15020003404803213400c1342c1d100b40301452004840600c0700c140480302420039040400303100e03607540161422001003a004188207900c60342046003000d05600342e05a0300200300c0c4640002c0da1042d0380020030740400704158407242059109a0701000910805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 743583929 1250 743582679 743582687
    0x501050a091e02160519020f0a03050c040915091a0703020c19020609060406030203010e0f010302031c0e0d0305030f01171905030906030405030a090b090607060b120601030c0602010507 81
    0xe0780100c080c2c0114100c050030500d225402008101c030208207501c03002c05190b45083c20200010032048028a02d10043c10552801c40c0308201c010b40300f02c0d8040e824618580d00c19881c1c0403464901c92003643d0340d04462040c0021207032184101000c901007048404424a40f4196140303103036940c1c20315444100c000420080c0244201c0d120f00c0144002850b09c141c1d0003500d10403046040c6401c0f60070840600c980030b81916000302034800b030300e825100542c4940c1050400a46144001c10304190002030700c0042000d030300c001c41c0c1320f80c085d0b040f00702107980824500019604e800070700840ca904010b0444502c024568000080c5004403940c0030440d0080c0d90360080c44102603400100d2521f980c121a080b8810100300d0414402118851030030b0f01e06091134000003908640088509407290f170000101110095440a050000340591000c65410700403800049801c5000d146030003010b40c0e1f070348d0182c6d603001d68a085d502c1100d09603100444609684034540004090580c2c800d02e00558207201c00300c0d0889000f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 743585179 1250 743583929 743583941
    0xe0112030f0e1c0c0b0a0c1401020f180432160f05030a0b03010216060506090403050405040b060405030105040615080c033a0e0109090b0310020307140a030501050a09 73
    0x4019103d90350020703207191001e402003c4111000c448211340010321100c031030050840f004142d22004c1104845051040b903031008150340e094103910400090030040106401c6e038095440402c0d03c03052007009003000c1401001c1800100310341201c103115100710846442203c0e24178855140040c929503c801220380700740c111480e65880480d0840c421007800600c110050340d803080649101003814a0000c01080c220b03070003d4104650308840540348014069103008650300200306454040f4140f800d41c5005109004602440e0701c80c81d2524540712a0707070354000940d406000300800030021401c003454140c005203040c0b2912000fa50518000045109001c9070800d01d88c140a030150155141389000f0401c0c0d2544240c50142c60000344e41400c10803406040561200e80882c1c0325007520600340c4001400710041c540c409141c07241004100e00c05030b1400300e032103104a46280300260716900c40b544103032841705103460003400740500030910311060340d8550800e50488078291542c120742a210075001c000d881d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 743586429 1250 743585179 743585207
    0xe0f06030f070c140d0f1b030e1212030103020f010207060c02040209120f07060201061719060b13020d11030402010c02010f050c160e0601050403120305060a0e0112030f 74
    0x50900c005081000d0301c1c41c606900054a103841004249035903290211991040c010750003a40c0900801260640c000b0100480848281040c6400100305c0020342120780700140b004041190b85880d00245440705e0030255207250241050343d403801c0c05040211655042440180d114201c1c03a010480c80c0d5001007010004c0c0d40491f42c801780d4001140d001e00020354050440c4613000310703551145011041c401d22180711804d940c00064103400e03152407002400e40d80300760483d4000c04219621401d0003d4005482210481c3c00038808100c41343c541405001007000c80c1c01240c1001c61010012100c0200364003c08074070440680402c034420b03d09000300100d01088074001e010500c407180b4100035601550b58540800d6841c0750140c905000078440c1c45c200070803010031640c054500c40007407001c0031600242590001003031825506252540e152890030340b0009500206040c0d580c00030031025158104907030084c14019414004550b9200c15510109002c0341040d00064989450702200034811804101d02d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 743587679 1250 743586429 743586439
    0xc1403030304060519020703050d0608010515011d04050709030c1a0f0c07080318010908060403081f2105150c03150f040507082205030d051302041104060e0f 69
    0x591039903241c000138040600103c0a04c190b500c44002c9421071800104070f03d82c4241d85080e10341d0001e400300002c1e83c170036410054090341042e00304000380310007604088000c07000b440e111158001c076000a05048140b1008103800c1420300d0700704807645412844801c112031081200d0300b500c41e50f4131645d070280035202c6d0a1382410f9904100221201e140440a03001c00040c00090301c1c2140d640d003400600c4e5a0000001103e00c2c4084120407503a076812071307074110042c110b030340140095103019070300100081002031250161a440c0403800c035907150760f08c10603c06803038440864150480400c0c03406010382d1010004803090320075015480d1044c10a01c4800b40201e04070040c1c542503031240301ca55529510480542504840c000e4000c03c038550320f90042c240210711031b4561003020b0030680700b551311103500b880604800e010b0041d45403000401c00000c841010440710400201511914400c1100c00060600650302a0a1140d824045041d200080080316800d0300e480301346915010a0103000c030580c484450b800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 743588929 1250 743587679 743587681
    0x1b020f070b07121107060908010c0503043c030804150b130209150d02030114150d050408070b0a060503011b020304030b04020f030f010e0607110a021908030c06040c14030303 76
    0x1444424607080300403580c0c2000809141000341c26454030645da03000300006070a040040003032074420b200f10358400c01d4070328046143d4034141c1c88408000c3c416000c21803c510002007200300d1024143c250407403841e503144000798010080d046c01001c1c20000c0e10b0659150994100401c0000c01910880c0c2000c01e024001c005003c005003024402500a0030b101900940390800300d407030100750750000b0802c55451140050716075042030060140c155084218501034075101000d0700500e14124140c2e56100d40400f008201591245010002406000c0d001030580c5050820b01c034a2001e01d410260961f4025030007045250a8004030b44102c1d1418640c06002d0f810411080c07010410740901d6a40c01800a007942c1030603c04403010924107920501005c1599545400e81c0314001d100b444142d4208545123000c1c4c010701410504d883e01e50545030402031042c0c0c030301203281750410801c134000340090260006980c1c0f01c5403d010300c1601d40c0012201281d823240e03400c40205001103007245c509040f11000c1c00440c11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 743590179 1250 743588929 743588933
    0xa050406030b1f05040903180e06010503011748010f080604090c030308070e0f0f100e0a1409010509090607140f040b0a030e071404020d020403061b020f070b07 70
    0xc3c08034518008014040da44010526444038003402410b68400d41d41e5400c03202040b5070202404d0000c0d04a42d841c0081002030041e0390781e001c4140e0f030542e14803e80c4280801e00d00b03036042c0d1404901e60480b0325521075640343e0812428105c9407504002a06502c1d1560b14194102070310555410040160702140e00c00440c40c6081c0d100c2c909055108002900004601400d40c0380c0c02d41109043c1c0c0101c0009000300100b00030203502c4240c1c0c41496034203a80d200010042600000d80901d109110140030300001030008045070b00c202c100c40c41c54640508542c580c542c60380442500d50303d52881d114080c0c07040000000781c0c0e04101c590b00344114840805880140c03904103080b210000c0d4007501c1e0801c1130081c414103020401c1400104020200500c045550740d030101005025500000705151450700480401c02504c000311300c907508650303421100165101400e5200707030001c2c000c07908040c1c00c00340782c030500c1441e013110310340000e42042a540031201d4100c01120b46a9031100e090080c40724a020500c41440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 743591429 1250 743590179 743590201
    0x607090e15011b0b10060905010c0602030c0d09080904180b16170114090601110c15160602070204180f030e01050c25090605090105130e0d020105060a050406030b 71
    0x20a2001c145414142410600f0341c0b1080e100f0280310960f806107420b01403000481c0c80c0c5460000400c220b003082c07040c880c94030300080c0c4840340c0c5400c080e00d4070342c0020025403200d1a04c070885200012001040001001c1820003440c55008100903500507450010003030340b01c90700501c0b003580e801c2d80003c88640ca582c0d020038410800d80000d00c040d00784603105c0d04442145081400042c06000005440340315441040e04200c1d540c08041c14440c144424a411004400404941904a02c0054901010f0300c4011050f0503124403402c41020324420545030400e040100d00c0c0c0050251500888051202c180c0d400c550040c00565080024401c005400500c0006402102d20808050b01410040d003407100458205050a60061100d12481080842c0040c50090300000348090840c1900030080c09040c8408140b01100c18084c041c0b184031041c002580c030407001d4110f40b8500e0300b5013095074003411086c1c40c040c2c06814161101807207014402e0000c40e440c2042c2c0320f0380f070031241c01001b00c035804c0d01e581c48001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 743592679 1250 743591429 743591461
    0x70f02060a0c050d020d030c0c121805040c12050c0f12091501080d180632070c0e0a05040309030b0403020f0601060c0c170307021c020a0e01080607090e 67
    0xc00e000c142e812040100b28144081050f0f08100d40281c07001104c685001411907019007058014088180300c0c8c500030034102e40380c0b964000c80c0d0342041c0b0ba0340c03ca181080c00300c002c0ea95005582c01420304110340c0009502c107010a40c0500c19000910168407000c207090400c0c0035a11f02107580e03032801c0c451080545d9480d036100e50810f580030141c41c1c900d100c40c8042490001c09070801c0343c29500420301c400d011903100d800c545141c0809002d85001500f0041e000340300d0041004114184059002c506140d1f01c10441021280c801554031590740e103100d843c00c3e00d0001141d2150800ba80c9032000000e90100301e500070341d803040c0d5043d5900030481e419039030303203114180307004c2c0050703086100c1e82c1c80039141444100b0405020300059107414414540030b0be00984c3d488100e400ca00f8082e00907000b078942400c0d000043d69880c5038120303048014101c0300c0c034070281c0324010300c070010b5404190300000150400041e11600d069840c0e4a0907142c46669000c401e49202c4030070302c101101401041e0000780110201c1c0801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 743593929 1250 743592679 743592697
    0x160b06030d1b1703270105090c0120251502030a0c030e0d151d07171c0302030105012a06020c0304090603080c060f162003030702010f060803070f0206 66
    0x4004624641c02801c01d16400c111600425001750302a4041100780680501014442c014002d01842c40e142c2d0002d81c072070b0320005480d070500102c40342140700041c640444031860080241101c00304808a00c0032040711107003440d90140e080045101044040d041e103402415143d042d0019403030070b060302600700c40006004030f00b0f504004030302081004d03550304d200450301071354001c2150384452884404020101c4d01d0250100800d5a00018051051b08001c101c4a0865800c4070440d445421441c000c1d038140b40d83c2641e000800032950f980111103d8055011f14141c8000780d032011a07445c20340910b010000019810036000f91111000140020950340041911034054000d603801d00740e0f19124002624400e0704120b402c60004032b20840c001800b0002e5540c09005020210b403142040c103001c0601540a100020401084a076420400c4140f00c40842c40c6581d6101225500d10308200005e00a0aa10090b40f0303182d810728000040c0303c0000400d2320105074000f80085d1104d50766a00300040d43d402407241e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 743595179 1250 743593929 743593943
    0xa050d020c1f02040302030c0d020f030a03030e0c010804031704110a0306020301031502040501050d050a020714030a030c03020405011d04090204180b0604091509020d020303160b06030d1b 82
    0x10014145040c006048409245030007010081540742101d00950044448030b8581841480100050303075001540462200c020b48071040583c00f90b00109e10005051112140c042c4164100c403400c040e07040c0e000c0301501500005449000c80c0783c000440300341c0c0064030040d000480c1d00000703464000455051a42042c42198101d00001d1040b010407281d140030390090f6030340c40e0f003c0010020311030f00c00014109000c0b0704800f11324050030640081c0030b03400f0700a00206059540c0000403090b03d03840e8121400e054010390600c80034140d100036141c1c2e0b588600250b000003070520070941b0f81d4034080d009880c2503481c140c40e10080d003c802d40c40c1c422401020007240354060f40f5890094050b880341d10900903803143d08182c800040c1c07038a05214400500c0904003a000700c0c900202880842d013104411150014160004a10040940009003030014030701c901039814040014600130031a2441c1d00448841c3c071800520b1403990740c00007055102d001460017000441c1080c0d6002095082410b0498103030361280741 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 743596429 1250 743595179 743595187
    0xc0309030321150918080f0f160605090d090e061909151a0a050711061207020d1b0c0e09030f1909050f0a0b18090a021e03040c0b0a05 59
    0x20044155080d5002c038229a041903801805120035902400078806038051071741d1441d0f0100c0e900c82200340f09101140c003440401007082009240c05c0e008441100e60802c84d0907a040c901d506100c801040160750000447c480e0882c800c28260090701e0306c4c0b0849080c104054025541c040031300c03584044043c48140b200b001e448000c51041d00714407c840325051211402d104007403e244040312622101d1900311101c2000f4082d9080c1070754002c084403e100d900c0711980005000e0359001c509940070300c504440c0d450700c00700100014258005001110709106548140d640b068601f140480390300c200801410507844c0301400c3c0080441c02d155079412016942c1200d24003480c0d5040e0245d160040400e0440c07a080c040c0c0710090307103540825448068070702100d081d0700e151001000214010500c0c0f04020500402040910a0600380c45201c405000080c00e010010300d0030459150096000a4107122510820626007101000090580780721f16070100b070140c50f40741000448109034002c21011020020208 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 743597679 1250 743596429 743596487
    0xc0f0103020d14070e12060604090606031217180309090402010e030f03090910060c060b2805040e0d0503041103010b10120b1f121d060a0c0c03090303 66
    0x8400e0700d00315282e142d8991004d00340582d0091480428081c11481150b51759644d0f421741340040703400d030b40051044a00003030801d0545409000307044103610282603115140f08144909402c110350981d0b000120440c9035250743c0d5104142c440e907601c94058003490380140000341560511140c0da580041c01410320040340741c404000689410220940420180c0010480841d18201a010309410461040c1d40100d01e07400c02000070122001396401800c0c1340d44420302441a43c4800d0155001450700c200401220102c0102400e40d201e006d200b05801107141108400030442e020684c80040b8100d5510b852031521356489420070702c0d481040d1142d25568800c1c0c1e0207265565441d460380312000f0f580704c3d44005010513020800300c811200c1c0e42801003e0f0000c08240420403070395800d403440700ca8103000321100c107100d840500501c1448540c112440070402d0812441d28006031701071094072400400d0240c5082c0e801b003103c6a5891150060200e04030400030710000703020304069074881e04a4501064241411 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 743598929 1250 743597679 743597681
    0x8070506070c0e04050a050d170c031f060905011b0201050a08040606050303070f050c030a02090109090305120a021b0a02010504090f14040809190b070308090f10140a0b030c0f0103020d 81
    0x13554200c92542c8407000c1403003001000e105c01c64050b070003814165640918000c40b0304010b50300034460003c032040000001c0c03410189101400741540c036070100301031140c0c540704040c1c4541c1c52800ba00b4003041c1c0100441402e014106900061035606948141c00c00300d00c6c50b02920f800c04094800c59030a0b451704004162500c01700058000303540034036000a01e405260070624245001c229000740650000203500026856207a103150440b000c0c250b00050b071080a050132111030141c0e0315801c0c0c540b51201c0510000e6415074000d07001404054050f140e142c4e203818281c070365038658004003d01050050004103d0041aa0b104d54416150301c800424850031041403904c0f4003c0c2100d040b51040404212a001810800a80d1444030a111030203040141001214007843c06002c000408004420300040d034241000c1c4001191b4032154412548182c1c0030021500c050040112142070415490001508544d0213006100021300c2c0600500f090b43c2c107032014400b681d0441084981416005c0190ba0322011b21 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 743600179 1250 743598929 743598931
    0x1c09050106031a06031506030c09150108010f0e0606090d050d12110a023d060602060c09010f1206120609020306011d3c09100608070506070c0e 63
    0x4500000107006003185488004024104003100158000204004440d10005505504014960030111aa603a40700019207043c0100c88660342040400701400f00e4511506030280c020715098a0301c1555a80f50000c0b0719080a8501c240d00540040340f01041c101c0c00e201000f4182c054006c3c2510f600c03440c19407241440c02003c140003600007603245001300c49215807031060902180c885101d452034080c41e0b1600030b43e181c040501c500642569184140420134006480c118020600c1c940038082603000314a00b0300424041c13207020094000c80002403286020101180c0c0070010584880c20104002041286c01d1020210070300341c07144d40c80c90042034a0750840c0c10042c4240c883c07040492001e00d94810f142c1440410b03408404001165103200c691140407001e020342c00010a0060600b5032000c01c400010161100203031901c40810001e688504015200a1032182c1c1035501150201302039407204000f250010708c2441d0301c540003240184110b20b07068000382155030180c1d554640c029111601c040307071240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 743601429 1250 743600179 743600183
    0x804050a0c0b0702100e0a0b0f040504060602030a0306050a050108040b04060605092706100e04030c120c0b060114190c05030a0c0b15060708091c06062105030f1c09 72
    0x142c0410a141103241c09a145d000d50704c214607101d15184001004682e407043c0034040c00b1450031001c604090050002025a00100401841805496a600340180d1241c0c03100d0302580c001303414420085401d0811964142c01c44106943c1c1c15925a113545541c0c40c4410090011174595880b200009800e80d5200007240c05200f281d0390002c02c0042c1c0307240c08404030b03520201e081c8107a08164100278949042440b108125a00d0707c48903411580c1e189022118038250110080414400300803c0341c10340d42c400c10036401284140e003034050b181c403041d00540e255a0301e1898441203d00412409540d02210b0540c5030004d807440c1020718000307102e40d440b0f50440c0c02025260f400120240814400c0c4020130480e1a001061004402610350aa0000c9090b40c41140c10242c400c807000240e9031456143c50340307150202c1d10100705032038041e2070900e801400f505131362090180982914014200c4e0142d50020b030302c006a4410004c51400000544e810340c95000242240351000c81c0c41c46004074190107000b4104094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 743602679 1250 743601429 743601449
    0xc0f0a0f0309051b100201050c0d02071502070b0f01270e0109351908060109120b04020f010f080105040b0f06071202070f082a04061d0708040b070804050a0c 69
    0x84c06014030480c044031a81800440e0b0508040c00135030788400701169201c0b0303000e60015a460615007801d20000a20303803203201400e440080c09000b03102c050700e9a2070051886054034500e42e60380780c0707aa49003201c0b0361719941daa107426201c1c148509081c40d0b1107058250702000012922400075101c504000503403041018502d034404440d45030241c000980c3e41500954003200c00e040142103120020709404440612091007544008035050307a001d00420300041461942c08103021107540340030124490b054030128002e5094031000d644e03d60040400380911042035071000b41503841d003c20080a4105960200d411030500d98202403140c60780b00c010000c240c0202411550803020640017440c1405903800500e600758840320601c007002000c00c81ca18003023588118540a85804404008910b0142c90680da0280c60004005a040403803144100f000d2140000c20b9299030b1142003e0b6040d4404507001852107880b840000c0c88a1b0051f0901e6410a00400844000c94240e0f038400d00310101b10341006140e2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 743603929 1250 743602679 743602723
    0xc1d1207080d0309111002030d0f02130305030d11030717150301110c1b1e041b030b0a0e040c0e090a05010c030e210301090e0c0411070b0c0f0a0f030905 67
    0x1c003d1054411030400c1d804c2c1c0d40310b2060398021b08000e44038046d5040c810303c4242c0301c00c1450030f501481e4058400452810440d00205692454078035901da00c250032150300b29040188403130441000100f6240b0540c12030b100c00000d001004203030f00c0c1c03000e002008941512400c2e0f49404031501c1c244620402e03500c07150021940c45030074202440c079003580701e04148800301d0744020300350013501c428000440c04480694907241c0881c200000802400d1900744818000d24020b94020750316a01d90021820428180e88904845403600510b1710b440104035030143c030202c2c1c48081080711100b29a201a40300700b69a080c0e0345094915078802e400e48180c03501209c0000e4588070803045c0c2490500146480b0345001e03101240946161000b41e08038003052041c12041c641d110040030756100e0034001446e200078018400c001c203a01e8103552100580101c402600e11282a1000840008040c011562560f6001805901f4070381c100702c040ba6042c03010303032100040548034401400090700800c2021002c1c00300d086100f0036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 743605179 1250 743603929 743603933
    0x708031008060f0411014d010515190b0301180509030a1e05040305010207060609051b040e10350304120b0711031305040c1d1207080d0309 61
    0x1809034064410b420b080d0341c1c01c00b440002043c00220400c04038082c24044041045641500da40c08200c021f5640061a408100080103082e0720411032110249545202e000c0c025107075090880e04203c854031b080803a816102c0e500362400c81c82c041001c811010745c06001c29203600520840360000c1c3d000c0d61110b603a1451011020030340c0d0154680c80310f000c000550510480640081440301c0341082c0161124600304c85036116403007801124003860f040747c004d65035101c03a8508a0002e04c410301c5507000386407600000c40d48102c00d81c65103a03582644103022038101400d04a10004085015003c061203114801b40040c0895010003035a00229403105030740900c80510380c00301c01108154450218582040205100075050396418a8029420050407103888c1e0f80c842c4140c0300c00800e0000140359100201d44020713180d500310611000d40784103803000e21185440c00c0d410f5510002c102c41c002da0300c80000c2034240850510414180036401800c0807504521303541c5100c2418070701c1741031440000940320032040701 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 743606429 1250 743605179 743605183
    0x7051507030206070e13050601030608010e03120906010b0304060f060f03060506150c070b0705010e01020310062c0f030a20041b351312082701020708031008 69
    0x80c0c03100090030640c910428000024108404c061b00400708280c0d110046112031b44240d000300c2c05081690001c00800000c0394005507242c10904013441c0768170000d40010191140892414101c03600100214195281c0d40d48031400740881c40ca078003017a02d543d010300007030700100690207600035030082c28001218201107080c840c0010a103151101c241000700000c07a0a00000140e100c216011103208989030070307142c5010b501514006c0448041580040b0500c00e2208104414508907100c5480d41d1119098900090382540c400c2014241d0b000c1382459629042d040c1802042501c000c000c040c2c03516440340d680e610301c0c490759440040d49408c0d07503400c0d600b0740c03402c2501c81d10078481459070024440c0070403100c0087c560b11003402d0100e40794248040c400c0c00780510203050030300c100c0942c520188518100f84401c3c0c05034003c02040c1c0d12205051454070815002e082c259008004402980210710320016074943c1800b281035007034080359400c003c0700300410100c4000d18020b5000c5010f16483c50714240d00340b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 743607679 1250 743606429 743606431
    0xa0f0c29090109210306030819021504021008060102100f0c0e030304120f0816060203071b0b160908120c070509070e19080d120e010e03071407051507030206 69
    0x407040340c0c5400d003854045905103900c2e401c41c20560081c050400a8648101d011340540d90001780303070701c0000c55548038140124641c042656907a40c21100703654140c40e420161440306660113500320b0014074101440511a104155101c20180100c0700c0703503402c2003070074421141e404a040760116555183c101c01d6540c020007044680004400030341c20300382000d0780203202500407000142038154101d0742c042000705ca001980c01210000c2c480750142c2525081c075078013a51084403184c1c00105d0700b110304002c404002e09070398441a04410023550903961401d114034076516100446090010300000044c4130a8108007046010380142c43c107503201d82c2c4410146241c05601d4100c02e01c50080c00c0e08100e141940100401e0340300c0400c560301e2078080c4825009442804003500b00704103d002e800c200030180f83d08078168060407103a0f40c100700300703241131101c040c0c0c00c8a9040e01458500d400812004000c1400325020300c0003200c5003019200c0680d0b45000040d40d00c0303520080c4160450700480d030b5805045d01070043c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 743608929 1250 743607679 743607691
    0x30c010c110d060227032104210c0b040807051e04050601050906070c140d0308070318210e0a050a12021314041203060e040303150302040f15050a05060a0f0c29 70
    0x40000002e1f102500045d0300841c002c1805841081e0241440408403030500c01e40c0e41d40045078800056114003201100740e020707000fa00c0c0c0c1407044403400185800c20488406460a2108a91201c11010720810001d808068412410418180824185035480c0c0300202a010b104040550410707180403114603d481d100c410645c03003082550038403800320741c000011a5020465145c0002c0c461044c40c015170000003800c03c080c002e400790b42500448458007402c02e010031b280380c0d118440b405024100f000803a06441c007450390011103420040240c42a1091070785102d83c8000c200c0030714000f45031800811070b41d44504038209040000c0611041c07100c6512103800c0e04485107070902c00c11b81030000e030001d1403102074001002c250740c800c405401c0c4c08100700c507000035640c014000d0281001703242c5a1000b0b031a1101c10540300e4800d05000060500c1c21800c074a04848018213081d0a0020810381075031800700b030380d40d0b07402440304145510f000942d5112007149252070001c0c00c580c241d0030444100c00d1140e001810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 743610179 1250 743608929 743608963
    0x2040e0c0108150105030624030c04060818071404021608040e0703050f011203110105240f090f0c1c050a050a140105060307021e0c030c010c110d06022703 68
    0x143c0340c00d990040c00c4030703403002041c0e5100d00781c24000c40c8600c40c00ca80c0f019403070f842c1d0400481804407000382c08000308112605a47d5995203604c4201d8018807400ea00016103082d5801840b040107402d1008010340103903a0002c00050030400260b210810074103030303e4011034030050001014888000c0841034160040b029190400062504100c983c44800060060306008205801d114040510500d01500004c0d52030000f803146007404003c1c003090380c0891031312111042c181003d00200d07080640641c05c0740e0308020103441c00c40c0c80300040b205504070054001c0032109020002c0e403084ac0e05030000301d400e401100e1000910b600c0c000418004980001d030103001c101d8103059900b10350301d000c01e44580c15a501241ca5a40e80e4850030740513854150b104810390801c0c01110b6800010301004103e0b4004400107800b56414204420011983e0490504004011074044601120b6138200ba00706013084c148289001843c028481d440350016a100c11342640c0c08a1140600c80c48074202800101403103170300186 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 743611429 1250 743610179 743610211
    0xe010c0503090a080f0702031c0905010f080109021305030a0c0f050f01021b011b0308040209010b03060d031b0209040b091002030105011209060612050703030f0f0f0c0f02040e0c0108 80
    0x240080d1101c0c0e000f03030040c00750100030814040711200ca00841e1000c6074014110369403147d4002c0b400c01803440310303d410004654007010014040d401744006e005a20b8003036480d40741903801c00004000075000f074010007188002c101004103c5840401c80c0c55000c80c06840d00801702031801c00c9900c50442d80e40c021b00e018100c030700c030703244a583d800084165105814000c28140002110012902040000051104800c151440c80305040e04008900c1c060ae000782c03885c5a4030b80e00c0e41000c0381c2e240b00540741540c010b07008081142c0800c1c0300d0b05407695440c030704410038001e81c0c181d6000552443c200792030584d041d080c803e00740f088840f000c0168a180c0c801e50003056003503615110018142c440358012800c1d480b40c0343d441d042c041091940c0408064003501400040c00000da00701607a50384800d01088001c40c500307500ba0307030995009101c40b640c4014a81c0c0c0e10b034041c0c02d02c82c50440d000104188110703014180079428400580d202d0040c80780e82c9406000800c400c03810080010316441018000c00c0c13005101c80d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 743612679 1250 743611429 743611441
    0x20102031003022b1a22120309020613051e030d051c1b030e0f03031311030307240506090c180301050c19090b090f181003020a05090f011406070204020d0e010c0503 72
    0x100b00001840c0c0040000c7d48882032240246c02402c1e003040002e5211100140368102084046c0441040c0c030010b48480d21244055501d0200509400e10310a60583c090a41703a80028130440007010300320f40c469540b000103001e504001c010b032100d1840700cd10034404280b001e10320507418440ca504549030358000740340e40c1d0032501c0069180d1002411402c0c1d8007801001a00600441403284451268040c0449a503441903007020a80321001c091000c03000b5010010030900c2c0c5c203041c028039000d4a0000d10b60b0246840b040782c11400d591014507844407200c0281c120700b80541d000c0c400c45205844101180d503403008145040f442c850484100301c001d00445420a0207046461420341e003410070b00f0340d40c14a510459800040d00444803420341050301030400100201c0310003215401d402c0f0381c4242c1c0c3c210703041c603100c000300560003100321642c403017021054004021345030111100b4071036888007810484c50200c850b0082004e99011848910000380c6a10020344580070034851565044042c0c905117045040031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 743613929 1250 743612679 743612731
    0x40b070f09140303040e0a0204030204051f06120f0507020a060608210c16030305131a0901180518150111031902100203011502010c020102031003022b1a 67
    0x150042c80031040d40441507500585080044501412080c1c08000f1149010201d49000e0350050000b2405581441c000c241454259008000c1004080d42c818025a042a004949242c164005007540c80d8440b6204441074881e84181c83c02404164050302d5102510305001050f69800d52003600280e00a8100d038030982d1100a920540009203010b040d034400040411603c0c00140460440301c0d6103691000108054001c00148100b04a44028084d45582e84200c500c0100c146005000c400c0320800c1401d079a5803090100000c001c00800403401c609464001040c07103110ba0184903001c03d07000d2400e10290052010005a89030400d1a003201414144003c540c0c9a008031041859000c00396803031000564000c0c041e0300d91f850010070085449603510314401264890f0200424095441d100381e20f0540c40c418002c503441641c3d100010341200c2c1c0395909200780b076042041d601c0c103154075040790100da81005602c1001c049005001107100b240301c00d0400000844050014042c204541010303d8080c0c0d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 743615179 1250 743613929 743613947
    0x15010e0f0a03080f0f0c1b03030a05030103060902040e0706020a02090a0c0e010c03050904050a020d0e010b0a1401030e0102030c120702031c0509010e1213050607020f04020703050d090308040b070f 86
    0x804003203d6100c02c080c1d0003001581c003072024100200300c004100903034218000501c03030b02107802d01c13290015840c1c3d0301c0c024951a84100301040000410400040c00426107980007021054400b0b800002c0859004141a0410400d9045500140c0154030a0008e614004c4082e44d00180301c25410080c50001d80c00291400300c210b42c4050612240448840500d400340c8140d80c221240508180b0081c54050480002940040380b990941d5142c106011a20788051007400810700014007a5141c075414103604031000301002d11038504241c0c0f07032010184540001e002030f5009a0f80506080d80315258500b645501003801415030301150b0050064030882e507002c805444160007500b80000d0350740c0781c481c0c559014000b01084060b2074820f072103004c88500d80007401410084015400700c0c16070341d110400c100711031041c071501952101d201820307501c1514040c1d000300b4610303100e400d1103460702803590102c0381030316076600040d00032400e408200010300040c8014213a00001e0b0346044640604031903006403000703617 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 743616429 1250 743615179 743615183
    0xa0e0f1909050615032e081f05090d020c060d0e010f090203010c02030309060703050403030603050d0207060311040308090f031e070509060d02011209080c070f080106120c120c050915010e0f0a03 85
    0xc40610120080e001252940001d000070740d080e544548e40412030841c9a011a003004592149050005000b0840c0030400c500502840d40c00360004030220780c200042500300307480d0070481513901c450b02c1c0034807042442021046118840d02080008040c0101400c4905d920907180964004000304008060042512a4440954200090103445c1ca003001c030010501f580005080d403141891100d4290380009100c0104e03412580d0074410302540c40701008041c044e9200040620200b4044d04030581fa1030000085810005400c0360440c600d200044001d0303014503840908950001c034400d000c00d00b8550141d962101041d0340030303500342e05158002070510003092900a2a559541103000422407a50708407400540503500329440282c03140c00c0440360962a1040503007944c03800e0000540001c1580360003107599000180e00e0f0140d450036061150450450004071015000e4910100b4030741e6901441c0c50160303104650071321448540b98005400c2c2ca0703c4038641ca00c203851450100b486541d0b04101242076070707 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 743617679 1250 743616429 743616481
    0x20708030103260c06040c06020f0709051e07050c1015140d061d07050a080312070c0c090c120911150705010903030e10020a0e0f190905061503 63
    0xd0b10318125548005111103c0000da010002002c4450704c8002440c58003850103050f0f9072140c0c50703031542c1c266a01c42680340c07a20314030740090b0020000c116040e40600d61158240e808152804011450a000c02c1030032241800840e1020501206040c402c200603140390088402c100003549802958000d074081500c640c1c603260015100700400390b01c030f00036000451580030200b032001c07202441500d094044419a0403080c4e01c2a030b1400506860f0140c02e141c03c4983c5000035624012050019000d5100020940c0341804100c0b03010303500054001c1c0c41180141068a40040c8183c0280750003004003503070360f02400c401810b200403000400d0880b9166204810200e8280190140c0185400440c0c068424081e1555190950960506400d50050745107020120155640b2110745004003040703004007518400014480c0d040d140346401c140801404004004001e061440105401421004e009400c28440c09484009000040c00e00550b886210550300e01d2160039881c1c00c0484400a200d0002008088 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 743618929 1250 743617679 743617703
    0x61e03010e010c1112030c07060c0c050d0903030f03230601020111070b04020307060c03050405041505030615011202071e06060e01080d0f05040501230c0f07050f0301020708030103 79
    0x1660250311030800700e09084024003030448520b2020705180d00e4820700c1c1540d070003020b50b076150341041d0b102182d114213541c9042608019103034980070000c1c03602400c4030381803080c500114400718004001800d00c859080e43e42c0309145055103402041201c4a008807414142055000c1d8085409011604c0d00c1d22141c01e000001030343c0740d00040380900040d240c42000404001542c41c20b01c1003e12031244254003d03011070b41a16a281c0c030440d503500e0206c4016001400911040c000340c0f5203504480c1490030b492040001a80d203400002c0d081c10000d66500c0c1c043c240100480305035503082006500000a0704070218182031468072028441611a0307003100e02d500000c2040000c000700740e0311031005090003456020040da1903030310450381d58200641100100700300600c16400b16114070121410390314181d40f0503000000450100542821078111036000310024030a405140380100b2446011401c8dd900601740705162009019004426441d07060003030b40104580d40c0441c00480c110b90459a00c99540160 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 743620179 1250 743618929 743618989
    0x60e040f060e030d1d0d05090d140c060a170121081303060e0d0e06030114242209020a140307020703020303040f0302011106010501021903052101030b010e06 69
    0x10f501c07a607081510b005150001d00d11018800c80c5090050f030b8810003c69603d4404c1d01000e4616000301500643d218401c110b40c1c0f00000ca881c2e81c21424000194110313443c1040030f000003455078100990500010b031840c0c0c02540d04610801d241401444808a200340d801400c41071450055480c840c0034020703d030b00003140d0340c0a0b00451107074002150400e50030000e01c804007000070b44032a4407a0300301c80065031070031000d8a140781c00c004980c100e401c4a0f10440d808250300f000e101c100660500c600417000300404034101c026184000074070b883c101d41d0a03034410f8203480d0200c80d0641d00d119005254080d00c180300309204541c20508021410f030700d640041d034880c0d40b0400200d281c4001034100940501000c5000190b0b40000c1d41c4040c00d482c800d80b02c1070b25025500b1b180700e54038042442100d00580c002580d9048140c1d41c40144c2c0f2a046c003074030b00070f03151000b54034460340700d903006003600b0348030f080d46074010024852081c51403409042c14510000080c01d02800082001c08003e075421840025503412100d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 743621429 1250 743620179 743620183
    0x601050a0e1203030907140a060804020f040e1c21050603030418021b031206090a060e010b07020910030f1211010f0507180302090f0a021c020706060e040f060e 70
    0x40800d100824030200c076800b003040300e52a504251382c014428803070060041032060121186a60102000e4000e006031450002d00300c403060000303031041e80c00450101141d2a580c0b254081c891403c04c200c001400043c2c040b02d01308075400820040e8804003d07400480c1004141f101908030449441d900010a081d140d80001908520071a404100814401154081c0411071600604211511891061403100003000a1500d074814040044100341c648800540145010707080300da04201080f00018210f500e4452124058500ba041700c20062000300c0c08208510b0310302034050303100c0c00801c03481c001c40303146640701c128800f00320344020a60004006403238603040c03242212640101c15a07000b8044081d1109401000f8042550b260300003400e003c0009000f90402e801c1d640449501030001405a40d07200613030a041503002e040d08441c1d40c0c0810002c41401c4880d88207609140441d600141e480381e1510302541200c0c4194010195214000c04100224100d8011760100e2500700102280c00009810124 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 743622679 1250 743621429 743621447
    0xe0105120604110f0c07080d05040e041502041e05150c07230904200103020f0d0207060209060c28020a0e060406240305090705030c010f11030414270601050a 69
    0x81000e04c3c0115400d4804000080c0020071107041c00140d403407190204608903134610803402140045d1110760003007000201020700c010400c49201c6401401c0c5501c4034449880780c9030840300c0c031b00c0300c840041302844689014004840d40c5001404007924000c2c2c000d010b0b98440c001886600380e00492100009209580b224140c407107c000106500021300d001c2c5004034656207003406089030140103944502955001c0e100311103441900050250402c204090148065032040204444590702441484d000c1d894940c058005c6040100140040240d9143c4500070311500789800d11f4950100c1c14124007603100c000b0810103540d2001108403150b6250008600904910340c81140c040342c10321100600040c118092060002c41c0b47c0d401d100c00c1d01e86010303881c1d840c0628080d242d410380000d0588103507580201c514404121035800d250301610515200e890640c4c0155005280352100c0c20003804141c900040b40a904000500c4981004040030000b00d0407040c005088506120b000503481c020700d401200b02c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 743623929 1250 743622679 743622697
    0x210709061206092313051c090b040602072c0609130c030b090d180e18030d0504060b091605180607050c090f22230106060e010512060411 60
    0x10700444c940c0380c550b00d40c085090340044510f07072030807404240250300030200307000c13100d400070010300741402111715a401c0318844041c2003041c484030340b40c009030b0090000003400080c00706802401c40c441c43d10700c1c06555041d82d00e00051069121201201c0402c40700d820040c0c11641c241ea5555440da25014030400d0145120000741114415050000030030a4040c4072500c41c69207801030365540240c10b2000c1e241100c69580a12101c10f03004014801c03c00b1880b2038a44c4040f119071a6507030800040101030444d4404010540c1c51034880781000305010f642c0c00303180d40c1514141e9880b0f000b49020003100b000c01c3d94850818003002000601d003050050707a50b000c0c0007201070080149a4440d40c0d45800b41c4d07134104620ba0203001d5101d60001a81000040021a10030b800505c4001202c00c10b4490100041440120490700141040410b812151440003c0814610708100000740e072400c1c8030019150404262100c0e04012040002d42030000460000da030300502c0c2540d0104400c00c1140c40b1346001d021341860 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 743625179 1250 743623929 743623931
    0x1b1a0d0b0a091820030a02240a03050426030712110c030702040b040e0a030e4e0a031206330e060a0503060301060b0d0221070906120609 60
    0x30341403943d1940001c0400c1e24455501810100e24103e41c0141e602819580c0550640040c06d00401600748000d1041c404400004440c48d28205c00813000d40542000b00d0640020f680d9200300030801c8600e0701d801041030420700301e89a041000b50074180d85844018002c40800045160401031030640360071281381c012082d200540c0f0340f030600c06000e076250407103142a8843c0b4146054900c6900782403080040d946808000703270607200745584017640e801050f032909903017000780782e4100c000c802a180d07940d04011030445a8483d5440c04582c2103c03403012211240907802c02da02401200040d000108040700e241d250800f4900c030780142c0d034040000c107416408414040008024025080c030304031548035034110070342070400300d0240c100c60845071720b90f540f10980c1c0c00020411216032081e000710091075210b5001000400c0c10780e2280441600c5401c909904610260040340040300c15032002d41208001010301d501c043c46180c41c070401170910440380329000030f02c1908002040c100200d90000d101030440b0301c0c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 743626429 1250 743625179 743625191
    0x90d0f0506090115121e11031507020d2a030210020a0804140f07060c080d0603031206050f0904030c081b1609140103060c0309020d1b1a0d0b0a09 64
    0x2c8035003e0410030307900c40d1100701d603140003203039070b034102e00303610104980007203e601c211380e02081c010700c03a034800d220151105440d1210400b080e03617040042807603030340d1030301100c0d00e86060040010b031a02004c0b148000034442050050428a02c082d190403a210f580c10050a07581a2070b810240c1c1007841c11412020503600002d1001c440e00c0e00f281202e03000740d1040c1c0e060055055514980d540b101e142c28400755094001c00341c100009803140c010801e10b140508403d918100800c011a402c440940c0c0c801c8011880d00019030003200c0c281d108000c01040d050302d040340180c4a03039002620911005200a05000300c2e07000b2041030000c80e0080d0758004101d0165081c40d101400030160751034141b5071071042c41581d48003011400c020340740542052480880003500d070756403c65540b840a044e801c070302d41c0e040640d140203480c0560356004401003024024541c02c003c030711f4182132a20740c1ca072182d003040c1d140300075611101842400c101c040303a68040010074005601c0c0814000226000c003164046c01d680c5040103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 743627679 1250 743626429 743626441
    0x311060c0c1c0c0e09070503060c030c07060638040806040f050a02030d0905040c050a1e120c030509010501090209011b020414010602100b090705040e0c040b030405030a0f03050c090d0f0506 83
    0x100c8464085d40d964001c4403211a6110105995440200c1e1123038205030003400412840900d079006450300e940b0455000c1561078840c8049005000d02145070603450290741c01c140342c0503c83c0c201c115884550300c0610707072405007040089595414060802415000900815400d0003410b102448003690300806480543d08004001004945140034403886107242c4080d061860380144212450b00515031219000d201c0702107910020491490405801c4c00900940c01c1c5403c05ca910503645041000d48001806040607901700d8212281604000b2506104100070180c0d43e800c0043d05480c0c20031180028400026880418044c0c100302c1c0011a400702850008100d40743c01298882d4003007078220302040945c09900401c180302c05d054411401042040100f4001100100b0032582e0000000041c10b14095032400e5005c2a40e20071201554590408140c505455501042c264400310552400f07101608049103d07240c580f25200c042c92048410300b822108000c543c09440c1c0b51a5002415034070649001c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 743628929 1250 743627679 743627699
    0x60f031a060306040f030807020f0706050c0f0d20030f04033e1203040b070f1b030c140d170306010e03030f0f0319150311060c0c1c0c 59
    0x50018218012020340015034a080c000f503994402e0f6001040b0039103020003620f0030303280c4101c00b8041c04110700404803041e2000c5000c103d4403008062030364848d0b0ba01c500041085080201c2040b109002c1e4202406a0f5a1f0940c8135075030305401c3d002040000c04404c03411030050311754031a21112485120011a0001c10300c10305802001150300c905110b523007440d07150350488030044c5168042030600402a2140301d01410070f03000f2905400301d21401c507407400b612442c035030001d40c201c0750086031103428038030b4070b1420800860076841c0909141d011088585085580b06248507203980512218500028210f654643e15544d49085450f048900d00c0700700109003000740b180d64421a9102d021480e031400712011030400008031400e5881d204092410310700d200303a11040a03800a000307910b000080c010106004040c0d4403030f4002c0e150310b50503101c1030145036180240000b12450701d514070568090201482c40752002c240f008480d202151082c44851201d0766041a1442c1110081e0000415030804034441c003013 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 743630179 1250 743628929 743628953
    0xd0501060507020f0402120f060102012a09080d0507020103110708160b01060c0203100c022509060605040506090d030311360612090309090a0b120d0c02090a060f03 72
    0xe950070004c81c000801800164451042c6a18502040c000003640c01140c64400c6900290140300101d50320134901d0568409041c41c95030800511203800d000112507408c0512036005101400103010004001e190141c194043d0b07403006410b1580710000000c10307680ca4001c076104141e0002203503403180c00742c440c000c920783c00080f030496181000000118115018990b0000b840364010010960307900c490205102400c5045544d500b588200915003400071139000d9440314000e903101140400c64074000002050741c01d030782c0c003090a20200f04001d200c05c1e180c1204503a024070059444016426241c81e04070002c050b0122201e51840d40480ca00c007240310503d4018040702540245086031520340200946034140505c226035008400b0002c52000e401c441c1c1d86161b005042e14140c03410310f144100418203924080382e0038003c15a40b41030391034840c6001030340a50f410340d01000911300300b200c50340c0151401c00c10f50806403003250100300080c000c40e45900b12601a21220724010406075880ca40072104421b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 743631429 1250 743630179 743630183
    0x320c041d120d1b1d030f0a02041d01110304110d08041509080d052709040f03030f32040302070b1e0a0302030708070309050c0d0f0c140f03120405150d0501060507 71
    0x84500c4044c6840c00140c88090488030f48060141101143c0c01c103c001d00031403156004d06000c403a00c01c2c400e0314080c0b2070b4003610000a10095640c0c60071b80b402c55401d480703004110b40b00301c0006507a2408201940161019a05d104800301071140c86124140e411900590040380c1c1c501c103694800e40841d60050103030000c0180e81c00d2111291a8440300d241e2100c0c113809080742c00c40611380008001c1141c2940300b041c030902a050005001e100e0354400c0301a54201030304c0d00c2c90380038400c126140302c240001840800b00850900025641070541e4000d40f201c0b1588105018030001103803980c0b280d00320480490400100310f0640f81d58003900d41014001c0d41044400d2004520240d0001d00346500a00131004601d6000004c0d181c06203041e0200400c00d901c02800703860000c00140060001605400f015014042003600b5624000c3c1c1503042107e1680340f048000e0084d0014881d20b40c8442c1141e068400b070b5141151007202061000c803130800580034070102a51441e04080000890326004001413091034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 743632679 1250 743631429 743631467
    0x7050a09020c0a060b01050f1204210c020405070e0d050d0e0a03030903020d0807060914070515070b041e03110706030e0a320c041d120d1b 61
    0x240e65400100490203000c070741c040903801081c007600004405a0201c0d03e03030f0005050a50800480000e081c2054105122024114032108144014840d03000e0410041c40d00d14580b4001080000000a010802c0007000030302503a1a01c0104d000c1074010b003001d03c07000c03c020300b456160710110305200b80c3d2007040211903808201c048000040d14140000c0389800e69800d6241c0c3e1751418910b500380050010001000e44940c00c060040100040e028010940c400d4011005000404c0e02140d103282807140130b0f444684590800303001c90001d101d40c60140e801107500b149504240d84e490f403c040c00d0009a41884401044910001c4010160050800907c1807095400c448840c4d466000a0342215000d1549801035480480c5d00c0001580d01f0252103e82410b45a42141400e1b0445620841011054500c4616007014010f440c09052a205405a409000840a12024850440c6502c1e540c48525142150200240da0044008a50044040d40e40312641c5000c800d081c045c0f0041a4101000c150340404d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 743633929 1250 743632679 743632699
    0x20a05031501080615180a031104050a2706020d0212040c050102070621110f0d0f0204120f1109100e070801030803061903060c0e01080f010602060106050702010e030f0705 75
    0x81d40704203c1d81d481500050510040804452041d0a032504031040c1c0b102c0d50742110380d4600ca80d450381d9031031100651150b50302d2500f039410b4900304401e0720401040d011503546003100b000c00300070604112061041864074034000f044d1460601c40c0203803140d0700e40c881c1e1081c0002904080c500340030405030b100d54010806685441c0c4c584004a03218452407144c41c00284c00540c484580420315002050a4180e01d03030300181c105d4822500080c075030050038041d01c0340c03480030550340782480303950003000c0700d001161008500e043d081100c0814140d0100750b02070078034024141118100941e0602ca4048080028001d01603441c1030800e003231415046010b601110040c080c00305241c1c50185d00e1403810f032640030b240942941d40f100280540c80c0b50a014420805003880c0700000032a029200d03405100c240e566034040030580e068005400c048020713020342080c0d814100100300c065400310711203054030001d00d00300d60b80e8205800100c0da014035200c501a4076000e40390000e044030600083e0a811500c06651659213 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 743635179 1250 743633929 743633971
    0xc02030405100519030c080408160215040807080304030c031101090b03010312091203091e0308073009050103050a02040513050702190507150c0c0b0304031d2d04020a0503 75
    0x161b170000240c8002050b02e040201700010141005006000014495402c0307101440c0c0008105000e50b41c04061480c10004052101c8a000d1128401800540c0c00541c60076145650b21003240c44d130b03880007800e0450f1594810880da031054507001d0050409030080c40d00c0396101d08003a80c1e25074008145d400458442c900c0000d00600b010444140b664040c0c0340c00340e149103410011180c2903002c03144001500e01415010002030b80400181449a02580e002c40c01401ca041192020300c0d41a42d0101c14041b400c07071010740c0c041e032200007a01900e03400c0c40c2c04111a140c4010b60b1010303001c0c2c1c1c0c00003540450b240c0a8a40c00e032a043e03000a02c180c6541c2d0840d000d00d03e003009101d446d0003041d84094000d81003070b68140520b000c2c5185030102d50403035150100603900903455200c0700c803200d0b401145400c01d0000510003415030001c1402103008541e520380907016900f000140c0d800f08a1004041683c480d003400c03440e54284044500003006000e04150b5a800e00000010090b910445003540c003405402c01080c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 743636429 1250 743635179 743635181
    0x11090708011d0405011d0109060e0303040c090216020406060302030907140307140f03030a080106140a0e0405040302010e01020c0a0b011d010b030a090f0804360c0203040510051903 79
    0x104a90841c68060400390ba00c55140c0a000402003081c3e61941d200c11080011005040c6404445062600009034141c058601482920508248250aa0310602c14800030407002d529500c11611711010040e950024071507007282e9180c807260041d610902c1c0000005820381c064008504c501016002e40e110a6161440300541030240075040350158001c103030900500200d181018801340005200021145100740082d182d540080d510b000003d170305200400c00c03250807000303130b060503c10807405504121034210010000b40960003503501c19900c0e440802c007031600039488001c1ca065100e000751341e60030a03c90982e41e6000140e000b00e030030795815000010540004a900e5200074100702c00511240d00c0d00c02b200c8085e800c0a00460714056030340a003100003803104009041051b128541d01c0d500e80d803074001442d138000000c407490082d0f45400300a15550402c240000c5000a0002c04002107003800e2120072850340c001c94100f55000800b10380341050094201d0060100561001031044002013100c030114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 743637679 1250 743636429 743636431
    0x71e060c020607030c021c0e060409020406110f0c0d0f0b16120b0f15040902031303031b0e060a02100f090611270f09040b09010c0201111c150311090708 67
    0x40d006800c030302c42403125500c2a070400424447d2a1030008007030368660000a92950055115100d05c5900180810049070807a030101c0090744014081c0ca00000c054000c65145e07840c0a088510401c0c01c0c12205d420840300340d003090320041e00044804203074907100920b80b00c1d4070341c0a203562001c10301c00c8440780610140b42c083e032241c58002802e000d44a4541170180030030500992074410048000388401707c0e13a0b030003174405180310750500e080009035540e06040140455000088404081606a404d5821150440b2a00e601c000d01520150350364a1400c608a05017800e03040c0c000c91031805c291203400c405c5440d4006901850083d0070070811800862640925485005804810355110349604420404151604400c2e1701024100b9212911040009916940d00700c5048171214562020300c402c0000034810020704c40c403180002c0101c909868800b0707502c3d0150301007138221a5241840209014a07641100c000080319411044215450b460046900701400000c14040c1000000007440988900041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 743638929 1250 743637679 743637701
    0x20c0609010b150d111c0507120b0303181513051003140705031314010c0e032e0b0405070c151404030c031806050c0601080d14071e060c02060703 64
    0x1070728101d01c0c0c446680c080c0c12504403008120300240704100b4071b220145409060046c14039000038041c500440b01411000c0c10007050a00e061404580603d50745001088603100d51140c00300c680b440000c0000a0030124500d0100e8488010106190a801070074252242c140c89007241d8a4680d258041000c404869a21076a0700c42c42c6042c0c0c1c00b080f900c902900046800540141308007140040782d0b00d401c1190080e82c1d5180d10203a540300c4c4c541c000113502010070211903000310090015001d400740c81e0810700c24052411100c41200c102810035906095020341191407000c0d006100f640f80400000c1d01c000b0071490141c41c5901c84c9090002d01d402c09100d2002180c005800304091500d035510101c4400300c0c0084101d007401a5000c2c20b0352400f4101d800c2800070f115035a105a07407030354102c03056030400406a1000303c55030300c100301070100281c201b00c900c40c1c00d0003003028194071204542410413141c003d50312611001501c10343c52100744010394118206641098003150000d0311280d00890841d1300716050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 743640179 1250 743638929 743638969
    0x60604060c050a02040501181b120b04091406042306011820040501020706081e04081b0c100809070902180406170f030703050d1e020c0609010b 63
    0x20300086029400704a1100d001d40c04031211019240e010404490080c2c01c010400616100c80502925482c050814000e100ca13008011640710307150098138015407003403507804160300c408424140d0f469660244210940084502804d44601e002d500d89402c41581e0640c0c911405003203480603082006035078204c02c040741008001d183e281000000302c2001030944040002c3c0c0b14646504004988180e840c40b005542910036139451600001a10f003070300990000d0140001c0744100611401c0c03508000d081d0100d0905240d4142c2d449203454202449500008120300071480a0b040d4032000c0003030501c00701801901e039550320b12100c0e0000e0b20000f004546000d15544007010602c09410603030081c182c5142400c6031044021511400641070310391580040341e0102c00c071012650002401c00480c141c4446140c051442c101558400500d5440344a82044001d80c80d0b406603590800e0101010304941d850940840d12544000390541e2983c40c1036441556941c02d024181181e031074401d80c00c400f80f10603204 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 743641429 1250 743640179 743640187
    0x5010617010b0a0807032a09060306031104091b0603020301051908061b040504180203060109050c0f09151c060b0415200312090609030403080405010e040f0e030a020609060606 77
    0x303804c81d208031008110ba020151510406d110798440200c05403a5401c1c8520280c901e0082d000700104400300a5000d50101410420108040f421125002c0c0003818162000304000e540750504a200070130941c0107405407184507100040d404d5041d0b01640c180c0c1e004465016403a071455540321000c40301030141141d680c11082c08240a0140303405003000070000b0034003039814665a040040c044405048500340003025980914046290074000e09025100d141c10400a60400540380f03e01809403000030413100c0030000340001e05646041400c046d80c0311a80034035a48041003040207100030414500c175400f95041001c041400707007104080d14255200080c2c0d11409900c0700c1401c944861502c076410108080352551480d210b44180000e0140c0604030501e030150341401042903150500040103669680c10901003070000802d81011941294024680204a00e0049c40000c0003420215200b8922074030b040d004a451305004009026084842e40941d0354682c0e44064441d01d45000f00c80c3c299100b08100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 743642679 1250 743641429 743641447
    0x11010b090a0f0608070605040905091605220f060513060311060f040510030912021516050d0608071503061a030408070f080d110903150a1e05010617010b 67
    0x98000503030540110b60105101e5a5164210706001c0541c0000c0001040090b0600c003a507550f02885800c8481c40780182681c070700f51890b075409003100d40280c610170026090215822040590701c40d180d07040c22a0f080240c2451103070714400070041031040500481d01c0358070a280d1441c0c507200718000c4030f400c03005140b401c540310347c100840c552003060b40e030440700014000402c0317940303c5c0728540190407182d440000e24031600c0e0820000b4062049284001c5610043d0000d8000150f404682c1c0c10001c609086d55240c200d4000c01d803807602508a903c41c0381c5107030000004a0940000724041219200600480e8020070380c1400c60503600743d80596801d00880c03159003e480c021520080d40d0090054640703134201142c5c0c1d51802d00034180400155140000801c854118203a03a104a0310212100108140b07085208070200b9122408802e40341c5135160402c0009441640715001545000e814551440c82d41915160b080000c000a000f00400280f01d4580b01d00c01d900e5650029050f1340d5003994085c1000030203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 743643929 1250 743642679 743642681
    0x303070806120f010e01090605061f05032518090e19080f0a032003060904060506011e09090c02030f040e0601020304050409080d1407120902030f0307080a11010b090a 73
    0x701d01c040c07280e0b00c5802107032030b2111001c2c461708680e120071000106400b00a82083c005a4030090700344c07072080c1103500400540c2c1801c0361440c13040740b01d5410040e8607907032104003050000c100000200d0007001c00c1b2040090550f03000010f84040e01100c051001000c3d190f10f404c50884500d8007080e082c9034021800c0b1091035020031142402e0350f01c00c00038a031522021405600641e0042100080442d031903904a045100000030f1012150843c4556603080d8a00500095601d010140025140960712004239000c0c2e40700c0c0401615000a48940414224078100010000c03202c0e4498120746606e0100c158150030702c08011250a040042c40c42c90030721382042a01050028050f000c40d040d03210800c80003885071100d01542841c0c0b4000d007416610b4905480211042d00c2812114139a4405e40344100414507800c921007103401c40d40584001410300f402d1010a16000c40d8082c030955a1001103414400c000106c0001d201c50310b0ba990311240311502443c2500d099500c030b1115a94003040d40e00000342d96000b2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 743645179 1250 743643929 743643949
    0x702030111092b06020c070f0e040210050702210f010b0307030807171204032604020a0915081617030301030308042d0c1a0f0a140d02040e0114030303070806 69
    0x548000b000140030307155a03460880e48032206c0703003d0981011804101114184070440014810f580f810700e901d1070280d00141c601d480300031820041c4600440e02d0030a5458800040082c62003213a4071054118544503c240d44925000d052442d545c01c19542d86908e040c082100d5088a900c0300103a0309201456546504040341103003003082680c0180484810300b100c0d4071400f80514040c0e21030940351a001d140707074800210895002c2152101c2113040c4001621002889021503401d52030004c1c1c2148222826084801c403640a0800c0d840b520400400742c0c0103214100303003190740f80840d40700310004012a2507200e010910001d804140a031000a0205103064203410703001c0c4a444243c84e11624100c3d4041f01c005c1969416a6441c4507030b081031001540044403032194070303111104c1600740f00b8071b00905841c1d88140b800e5007080200b0b000310709401e040317224191400c00c10011070554030b50b61106650a42880244500c2910365001c034034003120741c1004000c5901411080d0b071a8145036942406100e074880d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 743646429 1250 743645179 743645239
    0xf0803090a0c0f06141218010f1a040e120a0804212a0c05120a080309030a0e04020c0d08061306030c05130c0c06050c040f030503070203011109 63
    0x5104050300000341101941d030003030f043d18251400c00314140f43d0002d0224000d80505101a4410018588181403060781241e01200c03c13450480c407403070b0084000c2e016050075100c4080d918200f0042409062039050306080300002a02c0c10001c82d1003502646949011280c020080e5540c10490400e42a208800c20341d4094010180e03441c9140da0140301c104489154044440026490701c5007001c0710405040c00b0008510903001c40000d001d068955004030380042c46028401c8540c0c10f402c0b51a0303107052003c195a541c00c11040c54591800c0c800c141d40f031346e1013a1600c01c0011f5000c80c1c0408249400d00c02d4580d450b01c0341e0010031034404401015030301b8610140096074131800800040620030ba040c0212809140304601590f115440d0005002c0e201a200c1e02074164603084c80b001481203980014511051904070501003810f03210250b40c0d0f89544180c0c0c111101d2080460400b04c01e1000010092000358425802008240d100121804690245528080d44941003100a007140c00e40420a660001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 743647679 1250 743646429 743646433
    0x302010c030e0a1d0702010b0a050a05120705101809050f0c0c0a060f0e06010e01051f05090607060e061b041a281101020307090608041e05031e070f080309 68
    0x68030745400b4808040e40054411365680f46000b0005069070a02500e05034080070b41341f106185050400041c43c40320140a00f9014241c04204201e054400f041b564000707000141c800200421418002809001501040000d101000318001500099481103510840d03c40002030041e440d00c07900d0021950005071140101c2c810481480042910303444bc1894484000030001840e100c4041c4d00c03400c001c41603001c121040703603880c010031031030312a001424070b4074150250118070085284004d0f18240a4070345001d8104202040350410003a180d480386080401041c2100c105654016245200e034a460b00c1c0307010f210380240020050356071081d090300140c21111f10583c0c02c0100612582c00400805040003c3c14109214600d45154101005540082990000b03516520b440f00d000742000e034040c401e040402c10383c400090180000d0400c030103514078802e003401040402c54181181c0c0c0b47c110030100c800c1840781d042c600c442000e10301e080742c20f0383d07500907030b4683d000280e40c50f244560f4100600c1c0145074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 743648929 1250 743647679 743647699
    0x6160305120106030f060905040f0206030403090e07090905090a02010c0b0a0f02070f060518070509040c0b0a02100c020a0201140d060e010b0a0311090d1202012409150302010c030e 79
    0x1901e100390046002e400306075030024040402c11401030580d0107951080c3e02c1640307400184400f186400e03c480c220203405803101c5030b0b0b98640e85030841e40442d4542c088000b00c00d8140a21010980c84541d4000b1606410401e100704e8843c411100e44540041c200240400c141c0c06859001034009560590b00810035a400500030020041090690307100341c600310340405501440700208442c51040c940c0001818413a4600060b40340c42440d0344503007034001c8910901c4054009000c0214600c064805429201d10031a26840f9240d4065070f9504205007071011281040c003003030b040070f1000503e403c070190140d5800d2070154039016070840580c05007080400254881a020601d0b80d0042c0030ba6000303003011428180e42e16501400201200c2054686e5514104100a103802c1541c41d5001c0c030019680051180d0303d9914660700513801480d40a0080192507101d00b0018031028181903804101c80034501d0138081083c2c4609040707075948160000a000c1604043c5503804288140c844e18080480a0402462 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 743650179 1250 743648929 743648947
    0xd0903110109140d02060402010c060e031c021305030d0c110a0305010e250308090f121b1c081c140a050114030f0d030209010926060702060606160305 66
    0x9440714500d040e540181c2007103c20a001d20108401189880c451004d070025041c2030f80003d0034882d010b1005403005444450540c1280d80038800c444821400107001031451882444c038901a402c2940c0082c0440e100f05000207090a000c81e07002d48644040d175480011480303595444c4c206104850080b5040b03621402c01000040c4244142903406113548010200c840400101b240030382c52030501c00f1144007441104000240384101901c46400302242c0340002820600e000c500b09644040f0649924490403940e0b00c61341c130070301000000c003440c19542c4044181003600c0c0510220800c0c04028828801000714010081c08540300c00070920b448000420031810303040007507402410548440070306d160740c2c0004001d00c8174010040043e00710180c01500030014500d20481d01e41c20745003011410b150700010358890b240e2003580c20f00301600b8827049021500000f0800c480030740030003d0342d805d01841060082400d07a400002c241d48210f0004140515049800c2040c5c40b45c5151f011044062003c14800840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 743651429 1250 743650179 743650181
    0x40221010e071e0b040f030312091a1504020306030303040609020612150922032003160201030c051611040e150402040f110909100515090406060e03030d09031101 71
    0x50401200f842ca604005242e1000d20b40c000350310158060104100c204118022889040201c03034040c00c24644d6005000c4030303e8041c000801d0010800501c001e03120071000c1559440a01860600301c20b9043c8007134480500c422880140c0302e043e855882440081d00250841c0c100e51240d0b0310141030182051f8440d03143d8000ca190a84513442c0324001e8800141003400d05e144210307406031081d140d1008a00d442c0305040402e08869201030100880c1910f038030361000068101c03402121401c0c048070350710400c1102c3d01d2101e2a009000702e00003810404d0341082c542c0710320207845070580ca510940340740c08101c2da40c00c00c02e00300c032404d080d07001922000c21017031360344050082c10407208000000420f10301d0184100401c0b117840e03000c28010140380070301c07202c3c0d08200c84c4143c40e071f80a800d45001d01076440d03a00e520311140095601441d400f01e21186c0f1440451655005403070308001c01d0360203000380c540740e8005035000000901d62a4055100b400143c2e041102600700e05a901d000c2d0402201c480e210660080c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 743652679 1250 743651429 743651443
    0x120516050102071101080105010f110c0a030b0405010507230306010c020a030302010e120301060215150d03180902030c0d0207021f2304050a0b0a03020f070c030218040221010e 77
    0x2454a950109480d010b00078440910b0221305400d00e8402c081c0d605100000c0d1040c4c000100c80000c02c031600102d2110028100217103180c040c40142a013041c50398034508106640c0c0112821586c0d54200404110b0150188401c101000442500c618005181c1d4500c0001500f004000342e04200d00c4c02503900140c1c45030000c65014600a40c008262403002e43c9050745014400d03140510403440400041003855800b142c0d090342c11003240d400070a1512007180b283c58854400c6000c69218946442000030541c100601886600f0f014006207203d179a80c60091080340000c50b5207104940b42000b4050300130717807103500030a030702d510052001216204180a0000328190744d802507010403955141010038501b03a5400c4885c0110b10300d0810714240c100310108000c0e0340b161080d036040324000305070350341994000c0d01a078003020309189441c0d07282c90b514140070301d6120a62000740d0150114015807650754000d050107e22890b00504148031220242c100c84036142c0442c600041255660304a20b80c0411042c0268 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 743653929 1250 743652679 743652683
    0x1b0803010f0501021902030c010e180a0c080702030c150a0905010606091a1e030405071e03020a06020303160e06040e090606010f09121b170106080601081207120516 72
    0x1114070796040100280c94041c4499820700350b0b001d000d8481d0016a4005000c5540c1da44c00e10f0042001d0114001044041048084014000b2191401c002c3d00328090780c009105090381d551140465164004d050f40c4a00c1100c004031002e400011010f9010075440c079000707802c148800400114491203845441c2104c409810280010f000600100603803252020400300007070342c10201902c0e010700c0413081540700300c1004075190404401710001c0c5c140b1101f404043c006110781c4554890500501000d80884c03500c40c0401c038440c480c40e44010448a100005a0380300d0b02c600c10070000112441407003900c402c2d2421b5811175009000304004179031004c2c3d4607099070007190300c1401007805050450014110f2006031324610208000d200c002c0240030a0190801c0200b41c1003044400c04060b0080c09085e07040007504014202c5202070b01309101ca400550010080311003aa051722841e0341c8030071203a034890035400c90b214118203051107444041400b040c400108418241081460b0030110105110303808071107542 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 743655179 1250 743653929 743653949
    0xa020a121503020f04110d0b010c0507031220100e010219020709050a0207080d230903070302011a13020f0c072601020a083601091e0f031b080301 64
    0x410460400c1411381031011401c50f41449525000880000a4000d20310111602600c030034400e0140e0f40220302c6000a550000c0076035103000d840703040c20201e442c0c04003003280c0000e04410f9103038400e0441841c40300551511701c011380100b042d8020420080e015080b541d500655007049003031100d40145115038843c40385500909100c41c038107036040d001c403400103003503100c441e004004010006000e041110300c800c01c40359001590f4075400c160295210107214044801e03800c013005010507000d00001908175144254020302800104c0c241c0d600b0400007560381d140d044010296035509040e201d0300034290a40c44020500c0c10551080c94892505a00e64440100c0002c2480c4802040a900810b02000f440c00e2001f0351901141e240c000301010380081c0345084002c420f044680451900d40705109040501c2d98030700007554000c282d094028605034108944c200301201d04111303030350381e00110300a13141c0c2c010040c81c2c540d004a44003991011b50109103946103124441d10f1000081040300910301030185121 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 743656429 1250 743655179 743655221
    0x20a0e19051801050901061505130902280e090714270a0b04060207030f15050a050901060f0806061228030f0c0b16090b0d0b010917060a020a12 63
    0x148035030869801a000c0c604590403c0c1052123959143c004404c15200c540c60a2955000c040c446602c0800300d6800440100e80001003801c2032019611520a4030300459010890a040ca048117031800340c040400c4d26005110a40000c4c8010b0050801122183c00100d8070f51030120f14088045030341312050400400344410601154050610b6800100508000c1c0c5416280038207083d8040d42d00c84403803200410901c4070040100802001009055070900c109030140640c1c106444017102606045905410540c0380085c0081c407843c0c03450000f001c5400e084080c0855445190a200b04112640c51341c0b44148200c100c00700d08030082c1d20004018090084129018400c1490010040c8903520b10400401c03904e00101ca0114446201c0035030412507420050001d08000003090302c202450f9801158008030105040d001c0d0105030f00601403006c0c0903602d100c0241d071129459441c00c880e42030040e486500140014010100c242d000705241c20013400c2401140043d54006004d0f280d21243c3c100d1140c040312 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 743657679 1250 743656429 743656471
    0x2060d060f061403061e04050f0103030e0a18021803070b09040614030d0c060e03121905070c030809010b1507060e0607050702010c0822170307020a0e1905 68
    0x504007501c42494403d12040b00101801564007000e080340c2e00c42c0540100e04011a00c0e102070300c2e81030a002903c140414507107080035800c440360912003600800c264040020381741c5808a9040240c80c0074004110752001c032042c8500003504182003e0b10b0740802c4680207805564100901c1d001480c0120003250b64002e040d0502064603101d03400720140d195600c80004443d40c000c200501d4035903180c64030340106102410004c01420746588440740310b010000782ea001c20302ca1000745522503040342e00050b046104042c00d03e0300b15030b02192050005101c003104407001074490105150170505032800841c4c40c00c10b1500142c4c0c401c08415800000d00000607c400401081d4054200074104d0300d009441036180000000d440c51241640003030400200000600030030074102e090310880743c00140101440140c5043d0001d150441e0b00441c1c20600071802d80d902c24034000000c0b5001d542d40500040241860725405104044028019690554000c40007000440c082c0c81030500c80c404a6008254540e228 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 743658929 1250 743657679 743657699
    0x14062803231f090c0906110a050d05030a06030206041d070f140c010f060807241d0301020d050a020316050f04031119091a09090706031802060d06 64
    0x100d000d074101003800e01410310103469101d8481e40c400d0700400090424408582031040d0340308140c010744011031410511000c0e45a10000d18030544426441d8551280b0302c0e45e4202e680ca610782880140642d2064240f03101c1c1d0f900c110003564000d800c100340400c1d601d450f030340050000c1e00a504250096070303440740315030440e0030200d4401c2d800000724204001e60344e0000c10b0046c040d0f41030002d0100540000180f00c2c818680c00d603c2100c1007101104200b00b15503c2e07030301c142e80b102e00368496020017103051301540044191401403840c403000d0a495001201e004658805100b00180000c83c0d8907540c24000c2560300300b034a0141500c5200c0710304005031b4034036062985030f0800000b12911010840144082084103207010308460a1f6500300c0182c1f20100c1d1418002402d80646496400901c083c0c4140094040e0300d98200703904041c0e088442192400002e41801a200022141b082c00c130b81c00020f003004101e009504c4101d0480d03083d009825030400d04d401140700e59002d18a001702481d038a040810081c070301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 743660179 1250 743658929 743658941
    0x60901051e040f08130e0f062815030e01090f0b010f050603061315031401050f06030c0409020a05190e01150206011509320103021314062803 62
    0x140071419168140790702c40e003100100541c401400242c00041406082c0b410000190080c00c04030740540c2c2d24640382000818019003512264003403110030000e4942c828041e480c8421412010b240901058079101c0d8001c586000008504107040e035841500e242280203000d03485c60320b40917191501401030986000c50f1541c505a108178884150604103020603542c40d011250000401c40324184010708030800791009218100c00f13042c81c1c00a000c2b0000c1001402d580360020803100400800180d681c41c2c1c0c0704e0b200000125002a0326422a2420700e440d46020340c00303240c40e036001500042300b0546550120b8580884010003041400c68900308000c20603c4101c894003520710160081c1100c40c445401075602d1606028607a00c0100e56100c44c44664070505c01880145880607407449850a825411600c9030340980040750329039011003088809500a00846506111410b401c00000c0d00c0c0c403868620b040c1e0001483e42e8460310410000148440c11410680e010081c540c80348249642d4800140403a01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 743661429 1250 743660179 743660221
    0x411041202100503010b0406030207051501170c010c020f090a0b03030f040e0a0b01050f03090c090705030414070602120d0e0f01020909010909080d0b030a060e0615010305040c06050f0c06090105 85
    0x43c040005110500c07124064408440041c03d01503111007240c90032900344640f5959a5054a800f940005501c0301d203080e80e0108030622400b5961103110070401120451400d40c8060742002d0f4040c002102820580c00341c9a20060028000442911403800a419a0302031440904c50440104041c010081c0c80701d40160090422801004081100c1d800a402405400c1005101030400704c00200340c082c0501040c070019000800c4c420702403800c1100507005801c240c0e01660300c0d0400e4208160800400544201078070302d41c5c1c0003400d48031032509000b03016074451040911a40d4540c0303403e004413002002081c10500c0004005602c40d181c550900c1103c2405a0140c8001400c1c084500c020525800449400350050f910219150740d2120100703280c0940b040c030040500d407800a500c07a80c2c3c9001700e41940104510a41c44084044407401182034410595002e000310425100c00c12003140914002c0c02c0c0c5038180b02616080c0b080b0f01c0907160030301108480420680c1d45a00070440d901d00c200c0903c0440036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 743662679 1250 743661429 743661437
    0x140a03110111250f060207060518030702030c1324080d02074509021e21070305070b04150c0803060925120c03020c06040b06041104120210 61
    0x1c0b44081c0d10100302400d01e20b160346280920203c2d06102c54810055452034000f0003c4d9551510307807038640c00600c0c08481001035401e06008180d901c80c4048222030a0b150010024056100100300f0405044c01640325200c5050750343c03403000c4003403080d0400e01c201d509031030b417244810600e4140301d14108807a00041d00115004460280715449608a602c91034402c00001c08000f005c1e8800a0900d031078100d00002002d0b007500b6240050b00c2090b030054000e1034801e580d007614040c1040714170040c80715048151a8000e0031207217529481250154106c203180d50300c408851180e640c94880d941400030302c1c0c000c2e0300c030403400003001e2240107254104035548107511300d81100c04c2d400791780780c5405e0fa0001824951140030014045100d44030502a103a001c1403d207030507140080341140010b401c0c4030081c2503280300142429841c00c1c00c2406403090390501844a005404c0d1656140ea41c480c541c40010640c503030003aa9505008055650300010b4800b4000e1841048001d2a407401040380d4030940010b80d80800c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 743663929 1250 743662679 743662687
    0x1f0806100501030c020a0b042d02150a1b050304090908070c0f06080114010903050d0906020c190e0403020f0706030b09061504140a030f03050913050403020303010b07140a03110111 79
    0x51741d000883e5900c49802050880642d00c1c0c6181450401c1c00004010750302c02d520215400540380342c4814140e14620031076180c084100c0030980840540680802c40c400719090364900b00c9844210340109520511400949241544568115044451101c029554840041070183c20001c2c0c8146031030240c4030406456490341d25081004101c10307c140034100e03d4101104a129903a4003440750000515070100541e041501c0a61b002410141548100380c010300c59144107002e40e06002c8130700d12400314000c0356542c0c510305001c602d400e000406041181184a100d800310903504041c86420040c0207599004074070101c2c10400c000d5114000b170325440c801c40200300c07900220b508010440e8100d40e1200a0f040c61100d9010000d0700c0c0c400320703620181081e065008c68504050f8070000501c007800b400c44030005002c851040450490340c04440007805070b8000c04c01480340b4002d05024001d19031082c0d10302d1641501211125050030f81e0030504401080340d070101201c14040030302607540c503103e80030307505420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 743665179 1250 743663929 743663951
    0x2040810050f151809010c0f03060513090515011e17061b04050d11030f0a0c05040f110c1005070c030918110a0c1106041503051f080610050103 63
    0x2c0403010b454900c02c202e1601c5a010140c8840c1030400c0b207100c80241c420014500f4100c064040c0030354070004000205d050099104040c001d00c149000e90702d001c0c095213880101c00d0604801007985c0344007a11644500907044070f240c1c001c05106406402900c051203514003c4d0603640074581901d80024040e00910040d0142c0c44500151040c0e00010540b141500c11140001c04503052050b60403c540200040003408144403442d48002c0310f41c0c40130f508032840078010401264a0b0144250010407800e0148020401494030350482c041040f0380050000342c480c80e001e100e0485900880408201c1e03000340c1c0a40c4103c2c0143d209541d4419035904008001c00040e079002400f014042c003440062141c0c44540c00780110055000400644e024540705070798054060020b03004914070381c0300b00c4058941103100005c60a102c0c0544003211400ca4600c408400011070650250078010404c102c0312012542c50364034840c03c1c1d1600c600800b00313900504000d00f031607400106100610b8128506041c140007003007072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 743666429 1250 743665179 743665201
    0x515060315010905031002071112100b01200a060605010905061b03090a08070e010b040e070e0409051f1401030209042307180c090b0405010f140d0204081005 69
    0x40d124018203120a1400e0700301c0e0041e50f0240254000d0f60b0548150000030030b10000c540d00610195000c0ca040645081c045000c004000c04110f01c1c2d0109508a103000d04d446044a03048920500e00504102a031400440c0c6444a042089080000746511502c6980203120341071062001401081c6400c001c05030400d4080b50a600c141d40c6a80c24143c240034404020090030300c03e0b1020350780020f00b811030071562043c2c03450342c4600a008010780700c0e81c0c00c030002070b84001d100102d408443e2240208003041e507030240d040d140e051501180c1038007c0e80365101b02c00080e5043c4040e0426074012111a42e490910b101c490086900803096030f5410200c078001030000d0382e0bc6c0d60019500a40c85040320710070000050441c0c1000582281911492250f84000f16000010650200c2e460750114820040160006012100d2003058802c1d0a41e10074100001d01240d40720b50721a05044c001800c048070580415551800c4680c0003000c0030300c01580c0820184202c045c1030000066440180e003061041d41440707980c2031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 743667679 1250 743666429 743666431
    0x8301509070905060c07090603050a140118020409021c12120b0f060f07060903050d0513021807050f0d0504020117040c06030209040f050405010504150e0309090703020c1204050405150603 82
    0x1034401c41020034040c82c0000c01b0440134015241140d0103128440d5213203403166844200341c4c022603070300c4070741c0440c054031000510031180c2e180d8dc29a0f510503110320603000d00000303084600046e40c03c05607481584c601700d410000e2244140740b207003904440c0380b90901c500420309016003002c4000c00d800c102c26044143e0f180c3c0700c1d0364483c04e01212aa555022310640100013071081d03003130003000d41d400c2c10610300c10f241d040009030030a608a060284401ea1310300700c16540310711142000a5200c850940f40383c692a0304a8a03456028005003856883d04041e040003542680000300300c649103c0d203038810030045583c00351401406034003031080d04243e418560b495440c1c800c024041c0c1c2040541c042802c18041d41c0380c1d00148a04100030800b0032041c00e0904082d4007a040441c1d054271b0a0341240f002d4140c040c880e104150007003460320055410b02d0218020080400700103801a0101070702480b15444022082c4024010b5559448055540f1464081404243c402c02402c285003a404100c4201054907090308a03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 743668929 1250 743667679 743667689
    0xf06020c032116050607080106090305031c0b0604030609020a0f1d0903091206040209090f0316020a21140714040c091a04051f020a083015090709 64
    0x1c503200d050b84074082c0e900c9004804442079000b800d00ca00c8018840c0110f101805801036907101e500a81e290f0205403001800762000500c2d0354420883c1d8841c0031806100c100e191a0a00c401042e0701c1000300c0080c80c40e8000b60002c1e0350b0340d039a8000520440c900100c40130018000014440520343c64454a1102024600103a100c0d1200e51400216040018400c03602503040017040801040c0e480701e4200e03a603900884040303000c0c18040d0003207042e881c0c0020741c1ea211600717110300071031a10b0304010814007011a5403034120b8005941400200e400c8401210070680310703107506000030b425241401e110b442900301400006841d007108006100d546450310000c20040c0080d030340454080308000701101d03504055800202c0d4010001b0442040d4101c00c802802100c000300d034a4881607000031a402015491500d5001c0035902029030b2400046009001c4d0207951644030b0202900590300385d0345207800712075070614400484680b04000b401c0100f100304100f080000e540140c010718000b00f004d0031a10306d070300403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 743670179 1250 743668929 743668963
    0xe0a17031312031b0302100501060503070f030605092706040f03021b0a121a09030a0201060603021804051b0309060a0501122622090b0105180f1503100f06020c03 71
    0x4c0c540c2450300810901401000c0907204002c150f030360740002881d0ba0025144403000605910541c82124030a010308001c0d500c005000d41c2060b1504440121401c84070310151f62a5401f4003104100c100003400f6152041c1d001c1c2c4d000c1c1d0f25000d1702c0c0c98000d04090141c510b81e601080300e1441020680c075200070104c280d8182000242c00d10046041902450b840345550592100c2c600c0d040107c0710f000407015150444080d0000e0048684404d0140d003a030050848407020303080e036014450341a2420390001a04403100c24001e41c2003c036440c203400fa40758400c03512509941d0180e820301024003154401c1da4010461545500090515641c0d0700e044410020080c40303240e180f000d40d03625658248411190700c0d1344405042c0302001014403401032a03455038810f074003d8170f00c2e21401c5c4d200795000c1d40440e81485002c441c0003100744050300820000100700c4046a82200359403601d000c030034900500450041e40105812401285041a600303200201ea80004045401410082c0d0064070001500d04601d91075140b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 743671429 1250 743670179 743670227
    0x1401050708070c0501020f01061d070e18060117450c0405161b0c050607060b04060b16020103021b191202070f05010e0a1703131203 58
    0x4848900604030040c10400000500104020510700d00b08110740c000e0b002d5400c000d01c00d4030042e003210030314481c0360401c01c0030081c00d8411000304080d1a40c404440d0078100011000c003804102c5401d0902c0d08134080c016817600307020466812110048030380c0c9022006120928101418800c0401201da0500701607005400440e107040d074012040e41c1c0f04050a004411210701610a15500d00840b240d0780e018070314200120360650358991030320f2014240c540301d0515082410191180c0104081010f40313108000040c0414155a017800515840d40603031004141116120100000c583e12948082d00008007040700d182080303d02401c0012182d024200140c82e84580040f18580c180089024206401910121000b000d0074440c2c0401c1c05000c2d8082c071040610990059913944d0781400791074051040174800b0084c662003008030b01420000035016482d041da80b56076a00011320500d607844003a41001c1009020700d05154401c40c010054080c1005012202da1000785c505071550554641654a485e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 743672679 1250 743671429 743671469
    0xc0f080106061b0212030313110906100f050f03071d010c120c0515070c200a0e090c100909140c0306062b020304020a0e0402030d050c34061701 63
    0x4022101700d0240180c1382d13a490b002c00e588141e07031640201164180211500180c6c2810724060f4203100c1c1401400b200c034001b1800300c0c16142e8200500d52641045400c00146945049040c050b6000d403010781c440072302042102440799002d0444200e03290400c6002e54802010a40d12114030000445600700750b4200f2030f170360412501300000702034400c02003264035042c8018654131100a195282c012005040c0301c0d112908200c04141305201220780c03040300c5102c18040d1100c0c002d08150041884012a28400807000216010386c06c150713928004a402c0090401c90501140940000e120440b000300c01780d4649031912104901001d021030380141070100300809100c4002d000342c20780c443c1141100d2554440c40926101030351080700c0c01c9015240c0300100194440451921a005550040240890324900300c0c0450300c43d0084862100c903407040d41135035210703015100d50503c52102c19400e1541b40139074240000000c042e5030381c84201007100211000c0c21250010b0a902d0650320f489035030ba98440d03201303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 743673929 1250 743672679 743672689
    0x30816090803070b060f060a090b0f0415020c030708011413170d0b04200904050a150b0705070e0603100504050a080313030e01080613090f0c030c0f080106061b02 71
    0x1074101540c64440000c5600c02e2143d00c0240512481c0700301e60f00724400c51594288041401405054404543c00110a100394030662000d07200001c200d0004504140d602d8201d0704d10010044110030150708081c00100490406000c1500078104200080c829072141e05044085501300401c1c241c2508002041c050030805801e01100d1b041d00031014840e01e035940036076140002d0201291680c4030301d24010a100444541010300d004480036a400c030343c10708032004c003032002a02c8000e0040c6185540c0700007101444a00c0400344c8050700441e040c2940300c4400313182082c5046466040507141c81d010b070741080f10941d00069114681c00010202052a440f9803928515000c5142d1008022900100811000510104600d03419030300a0341e400208082500042d2815501034a1403074200b01d400e0103401108800c1d8020030302030b622410f040148104d9503140d9034180740c8183c1044400d001039080070040e00e5560078032480034209901c0204001441c11001404002e003c40c0006100d41082469070203554503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 743675179 1250 743673929 743673947
    0x60f0611011b050301080f0d0c061a0301021903050906010b030402060703030b0d140606180105100509030d02010603050609030f030a050a0f062405120a020f070c031109060d030816 79
    0x2102d100403542008695024100350824004e001d1684134041c60001c1e4407600107841c1204007a03544405603165026110107029200c2003014207c0c21910407014103503600c0901c001c00010340c2c0c0e041e8200c05000300082c020243c8d0800b0300f11100301c0d8810b00050122000d05004c4a030000e60444000d0b03a280d450b890141c0c06003c00303101c501d5002c0c08511003d8140811001c0744002e4580010598404c0e0790b40724108180c0600014044034400200c000501607814282c82901d20000c040c01c2c8141000c0c0351b800020300e44001165104010b03511140100202b0000304900c43e00065014090760820b01900d10b810414040100444a00d41d11000821400f1002d40d0007000c0200c0c2a030800c0c07000a0f20381003076405402c40f00b180c0d080a85034608002042511800070b5510300000580c001645484800d01400650807000521040050070441d4800061302c040b05200150322401035180864101410001441c00082007a80144225141400020381c1720410780d911440300c1d0100082c003c8032a070100e9584131 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 743676429 1250 743675179 743675201
    0x10b18011b05150a140106120605040f0f05060913030c02010c0813080c031b040203102c0a1b030903090b0a020f010b0d0305040e06010c0210170604060f061101 70
    0x500c200c5448107000b40441d00d8544010203640d220a2500d5911181040340c0ca51074103820038001e00030052081c40d1040c0d0300703007039480b401c0000031650030749850000d800c85003020040841c05a89030619000101a03002d010b612807011126603089180011044402c20380002d80141048031601905086a001c1d10306950041c1d0071015864030780350403040c10f0b0400313034250041c0b540324410880d440b1541d2800103000e0303082000d00e07007849031514102d0080c00080c1d0005041d0480c060003a080200d02140001e0607132048141d194090002d4581c0700103000f04a00010704610071141c1000710300881e09000d13011001ca4070040e840c0000300c403002414121502462508912030210001800b086129400207040030410f21f05130007040410720710810851802c0707a10310001e0100303000380410019188c0b80707070140303038000410704111a803000554000b0b0900c00c41c8015035030103d602c1040c044500c0d82c1040d40140c0c48142a5010440d09040000b40d40401c6020310a650070401034140d450003012080d000102408 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 743677679 1250 743676429 743676467
    0x2091b0f07030f090801060501020c010c050f190b0a0c08041509081b070803190503090f07091a0114030c160804080d2c0d2603010f0e010b1801 63
    0xc1e0740749002400000ca00d107018002801c0124080780c001e03c10b1281c00d04450058005140c07102c02d9070010754602003002c20641c4c1a02039141c1c00482c00d5020300080d00030780703030311040707400304440130710300543d0044020380000d100318500b1518001160700580c1440e0400c2d0040030041030842c0401940700508880031006041a401284090060601c0b00a0404000c4444280c0d04d8030340d1200c41d500d603030307000f910350509100a04404201070345005600541d008261041034a4196415403030140ca00541640b140030115520f403003054a55a00e07140e001038807442442c0c40001e00c802c230110803400d808003030b1100c2c60000f0006801008185102205804158071900090316542c0d2101010f8607125021292408030304590904d08800405100d445540b100800c0c100d00000005014051781c140031003812100740c014030340100d20119508213100380400c1e680c000c2c41c3d03883d8140130164840031900c4c0c0c03107107001e022540010300c251038000e07040d00e4104040349441a0000901300040f20710805840707c0090311 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 743678929 1250 743677679 743677687
    0xb0c1e1605070b091c0203100c091d0a0509030306241e090909061009051519090b120c100c0b01090c030b0a06270f06111902091b0f 58
    0x641d44890251610131411101c841816940c0040c81403141e5420724001d6154015901c000c4007514581c0c0450003002651400c030952070344502c29803044105030f108050311010301200708103904986014048d170140041010310b08504000c004030f0031180548040c1050303a0320380240050791140b4142601c10000b1301c69401d1b05080e036040c049810680c010461a03000340d24040000c0e00d090340000e00079014000c02608000058130300061031000f030002500300050303120702940084a56482208200c24585000c00c000e05203440c1084110442c2c84010540340140b00034104408046000300d06e040c00300308280d4510400060050f4200c841a105000003441e0311403401c000b0a9540e541e07401602f845905490402c03840c4010307030800403510b00324841e0700d0024100b018903c00725038141000c030340d44684d040c4042c20b4050b101c0540804007082500420005070750390082601000041080c07481130490350f0080c41e071002e42900801d00749000108107040c007003100240051018503001c1241d55002103041401d440d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 743680179 1250 743678929 743678939
    0xe100e19170703093605060102030f030f07110d2010021303050c0906060301062001052409040809190906180b220e0114130b0c1e160507 60
    0x400f490a005481c5c80781d0415030040d103001e040800a50101c5140952501440d112089900140100900f02c0341140414007413201c48034041e402560107048045004c4005140008000b001d82c04205140349203030f4440d026921030a40c00900440e24034894114a0b4000300385440c2c4a8070341040700460203055840050050341048014140c001640e10840c1518103082502007005443c0e581610303060703800340c010001044503500805024150a10003d076154030724205459150841e4000c6030700d06894039460102640c450003103402500303881012240030354141490381b207198090040c0c01c03150380502852110107403003505108580000b0300e500001801481c2d00c502800a400381d0703921250b134100e428001c400c000e07890324010380420a00c1d00702c80342c55404904401c10700074020340e201060080d50b070344162314490044264110b20a00f58010b2407901195146401c1c1445000100440545841403020b00041250580002c4204411401030b40c0c880a100d50310965030200c05a006000341720342040010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 743681429 1250 743680179 743680187
    0x6210c150a090602010b03070608072001060810051005010e060c0d02010605041b0f08060d0f05030a020f0a11090a110c0f0d050a0509041a06040305010e100e19170703 73
    0x1c0320603040d6a15020655a03650907803c1c2c54002c2c80301c540c950010001400180d2140d19640d034880d540d850b1483c468000b842c0349005400288100c00c246035101d001c188150f80b000c120800c0d004201c15410044c0d494400c0034401c100400303000e01030402990f04500b00031a81c8030416070300c4c544280401c0d5200f40d889004041e0003846c072881110b005505084a0980030001405a1107005040340c0314001100c1c10b42c82d04480c0040010316107540b00c403074049850085203d00e01c60101c00c0e4402d000560f0390311100352020745812500c4603440000d92000f64110001485481010700701c00090f14101401e0b1100040307a0041c10b81c49201ca1401240810b45d003400e02c1002400880b40c41c2d80c00190b480c0150b280f001200c440c841d0103030200118000300300304c0c0d00e1410280e1240c40407015400203c11300506510002c4e0302c1d07501c10741c0309607250f03910780005c40e0704c02c03406000b0300342450b0b00488104110fa035200640380e1140390202d0005070102d0003960b910f082c050002c0d15440c60003c0206d030190f40306120300e0081c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 743682679 1250 743681429 743681437
    0x40615020708060c0702010c030305180106030303060e0c0c120304020117151002030421020d0f03020d11030412032d260106020a0215040f03060e0f0606210c15 70
    0xb41c00b481000c0100b60090075540403035400e103406a550040650880c0c070150701900000e050034200e001c40d040306510800e4284100805141300303560102da51441e002c2c61120701c1c0e0019120180300d40c41002082210440000c20304240c510060026440c0d035568001a6109403191004401d542030300410080c048a1000b1350002d85541128507030482e0041d54012640da0282c0c2c040c134a2003110f084010f51150b1401c10088038210300c010b100b102e0b00030741da0b501d452500d101c000d4110003580c082054242c4c00c6070045c00386800092080c00450600303203040e895422802802d840a001c0c0040000000002c100f89906070000740c68070710119418400000d8024991040c806031840d001048400803075054641d020500d040707946e1640181000340700d5800f0011100e000c0c81c01104005010040020840c4941c0000c200842c0102e0300040c800b100d0015260070010f10302d043d42d038143c00030780400c16a0390729044410780f162100f01d4000c802800700e8104615081000046650020015400d00b9081e0b41f000010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 743683929 1250 743682679 743682689
    0x80307020d09050306090a2910033315090908030609070509030312181219020118080c0a05100507120504050a031d1503070e1c120e060c07081b01080a0b0406150207 72
    0x5003242680021005000c51020304000003441d5036011480180c1883340c00501d90030300d00f4030722a01e0503661100010111844050221000d60001c01000b6281c82c2908485902482d0750400d64038007020100001c2c4c8a129100c00121030071044004910300040036110140420603000481c3c4045040e4101c03a521904800d00c000040030b46c0210b404d104510602400c03641c608100708100d500e103d00d94812855400811000800344a101d980201042e41080301007030140400b080000d41c0d003007900c4002c0ca035083c031905100b0461b0828081c007000400004004103c01c0d090324110024800c0a84101120081580c015611a001034008035001d0a036800850040c1c5c8a51110001c03041c50905201a944540426001111076030310400c0c04035104204600040d01c4901e07050bd40c82909030001180c94100307280c001ca13542d02800050040780b20030841e03003c0318404a89107604101110000822a00c0c0c0106007000d001e403144110b44450311035410000140401d203035001c2c0140010341c002940c0b03081d81c0c1b0403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 743685179 1250 743683929 743683943
    0x1030c06350105270c07050a080310080c040903170613020403111c030f120207020d03050903070906080a03030e0705030607080f1005010c0b070c080307020d09050306090a291003 78
    0x1201402201440d10012541404e00701d0312155a07030782c0c0f00701c000c0e030004082540d06002c2c1aa4131b500140d8070200540c414081740828101240c103242c011413401c2010720000d809289000b0700640420340114251207224005c0701c20341180d035180d0001c2444000c04041020305140081004020064010301290780c0720b400359082e4100300400800300303c0034040c40c0c20113404241500d000c15002c5105445003071300e030001c2d9071000d4900341b90360340803807040c18036941c040e000a03501040c0c0a070310740b50901502c40140520f020501c00e0f14148000142c50784003500000f02410740d202c11085082e1004e1215000401c001810364070903261044024002d0042211400d1405d01c030840000c58210051152500365541070b540c17040305100c0e50380d8000740b0980c05810310050122501ca403400007250384008600c03982e00355020303003484030350000040c002c0890340d0815442500000304100c661100003d1688255800c442c28001c1c2008900e40f4003e003241c0c101c180d501154414040000f001d41c0e000007a8100c130712a070b030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 743686429 1250 743685179 743685199
    0x420150910090512010c14040f060f0e090112060e0f0c0d031107120c060815120102280f020606033004080a0b090604231e060604060e01030c06350105 66
    0x7e101c0e016201d0b81c06080c0c85094151030600c01031784200f15800119420f4101710710141901000a04402400d900607100c0460000e111001c0122500481e5041040e00c001070084407003540c40346842e841114002c60060340040b5038401032601ca101c905a1406500003600e44080e100d00140561100800c8242c9030390100c042c0005180c0d101c2e004080c480c1c110ba03001c1c200d1112108041010844004608126640d000e02c807070080b49013110f140142e42491006000410030800b280684103d801c8455070055400000c1080b0355a100440c4c091214840030141600042c0744400768004000c141c90701e0200201c001c034002c281208000358420301d480c055081c1d2800da40c2d9268089680d50741c1114003c04590504e00284040b4100c402c800102c1c440d948160b640414250307401049001501242c2e0200360700031028080c1c241054070a0030050b00c180207031001c1c558115181c000444500348181c9080201c145500113032896a088008a40040200c0c280d940d4a04e07003940c11101002130243e00d10619000c0c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 743687679 1250 743686429 743686457
    0xb130c0212030c030f04030302450f06031003120f03151203030f0f020d0609050c0405030d0f02070f080102270f1201060504050420150910090512010c 66
    0x1000380c030f1080108402d0035243d44e4480e10f000f405028090821014113409106003a01040c20074402a1002100044041c04014405000340b01d00410303450400482c10400ba101041d840f00074400340c0c4107105840d04c6549071103061410005501d0b07540301908040304d02d0f0203c4031581d8040750500d00c0f0070981d9000d12008007010641c0d071458459210700103c440b41001035030002402a080480c03680080c000015840650700480e40590b841110522100c6075a080240910112440b54540000040b281e4505103070400d80400c1e9100c200c8010310303003884140c4400c80d107903610070405203000e4881c882403501c50380c0e0744014580c044c0d00854040030380d110b4a103072518884c0010030750070941c180008040c0990030404105220304c071100141014119502c42c080465a51170b140103580c01240b08814014100f078040000c5840f810b11003c60078032851080b0f400f100110303060002d851500d0000c4074200b1a40c080b03031600b179509038010b900054001c120a01c10480065040d40002000c0b011500c40742d600c14081c1c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 743688929 1250 743687679 743687713
    0xa06031e110301180c080f10031b170307032007031e020f19090c030e010e07060815060f09030a0b1801180203060c031008070305010507030c0e0307060e040b130c02 72
    0x2d000302001a1b14400002c4c4c40c8442018403c0d003140380030604c2c680481e280e440e02d01e210000b208440601500040301080480742ca0384045004002c01c0b409941009003a6500030421040704614101200c11000303001c0310140103005580055601c0b0020a502404091400315443c03a4060280c2c8201118080142e0070709004108406021804000911560901404100422a1108040070541c0d00e40c00021000c40903c0b90303505030943c1d20700820f1264a042c500400d4260003c25201e8403140410071501039403180c030150381e05034044401040d11081c0ba036010030701d00402a0405042000060107020f01c1e0041101407181c0000c13410300074001c10000c186d07081720009071404000e41590080b40004c40307055000010b150040b50800032111016902c022980c070705807554000380c3c3c007079644000b03001c2004e81510030100090814240040c82c411401c0009403515505c1c414030050142020b010b00541c1da41d540f08121222008000c40d1080001b880010700800700344001c00c0161184111454a620301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 743690179 1250 743688929 743688941
    0x90b0d09171207050c010b030a140f030f0a03020f0c150603060a0209030307020d0606030f0813050a03020105161b080309210604061a060301060f0201060906050a06031e11030118 78
    0xd0100c1c40c503003503e859504a03841d911a8403800c2c0c0759543c9440a0845540c1800091110790080c040031000c8905160441c1c01c01c00c0170032500040358010040385903160005026101e03811501c1c100180ca42d401554604c40b1441014480da006d40550701d10104c1c158911a95140241400e8044811559a5415010484c414900070550550007440003400604d041d00c04401d82e02d124980c04a80303e540d030b50700c114403001c2d80d00c0101c64ce880c0c0441c00f0080d05a0411403000240380031034000604a00d5500060710510611102c043c404680181d20401d00c081c021024907140e5042e860f0300324043c0e940c42542e031031381c100041d03640c8110b0020b1010f0109080c802e40c0c03080140190806013000303484942e500001070807580300c41d80300040c04045025643d5030355030280d8020a01c6849680c0841c04101c7c0c02400c40340741d504450b1410380342c64414015625804032171010fa84890030009200b81c5a507100c3c8400556081c0c102d900300d030400c10004880b0000d000554100d6011074010360800021528483c20344079 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 743691429 1250 743690179 743690197
    0x1c05060303040e1003050d0206070f2a11060a050c0c0301020a0503010e10120305030702061312111608010c0f0305150d060e0d02071802130501030903090b0d0917 71
    0x40705210902690350703400041c9810010910301103086641d20380d1040d0801601c03074900310141c2c11401c20820003036040803000c030301c0340024038002d62140002d50286151500c083d140342500e200901443c801c00c00201400c0300740c01d5000346219212290540020030907401554004001e001b083d0f51a001c42c2014025141d62202c503443c0d4070b0540e828540c00d9039a6010050003c14444800ca60010f0b140307485d85450801240645d481940d60321b06110b01915041001d0070010000d0f4442c40c42d00080350040e02d05840071000c5140070415405040b200e1031608095040d0b03070708128003e01d8000347c0544154010003490080741c80d0718100c180c0103401982120780c121010400080b2201d4100517902e020001d64600e2807140c080003460f006000144c91418aa00805c0c40140c0e014503002d01c039a440110280100714a0110190700d03100d11700c0382c1c49802001031301c1014140f54440c1340c14820140507003003c6014041021046071610303201480280035007820081900c440c00e84003100c46940c5490012504225 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 743692679 1250 743691429 743691433
    0x60b12010b0f0d020d0b0f030a030210020a0903050610060305060d050d03090206120415110f04030611070803160e120a1101030605060a030b0906040606091203050403080c031c050603 80
    0x680380011070300e2264040d07404000c00c02c408202c41d452101440c07001d410607076800a00000c809103c50144000c2c1c1000200d801d1181d80700e50910340010341d00140116402107000d001680355040001c05079141402600000c1881c0038513400c000f400081d800201301190203d1341d003400741d6101d031010720086410070300c0b000e0800d401040c0000328081c003c0e086020803070302c0602403900d88004450300741d000c020281c0702200c2400310706500c0001c800c10741c0240c400ea03480f0102c2e0f20b803926a0b02011030046210700d110050615442d07103041040e05450b503007662082074006000c0c0b9503c0c03901e029030301441c1d9446040c410103c0c0100040d00740f18109840c04095030801400203180ea0703003c98035110740000258240d14101030320f418000c1090340752440601007a10b4a134070045655085d8204005102400410b001e00841c5400c0080100d984d01c074200c50110307103600c4d603000040301080c181111107124681020f40510b1000401c0ca076091400001041e110442a40204910b107401c1c41c5e01e01074503001d03a0115415 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 743693929 1250 743692679 743692681
    0x110c180924071d0d03020d08090c0d140c030123010e060109030b090c130603030318020307180207080310060f030e2517012702100503041109040b010801060b12 70
    0x1c2e5008160a0b20010148650300c9401c01c880c2c1c0000351000c994110403801600b0074042d5030b942c641c0001e40349030040702c0c4034080c2031110300c0c1c0030105d101070b800511702800e10315610304071000c211814083d6840e0144050001d00241200c0c000822414410701d03040000f079038283d0000100d81c914040c5540c090754059541c40c0446245803204100503101030030811041c0150340350021a640e035400c0a036030000c3c00d4400411003528500307014086a100302040d945031a1103640140041e40c0200b4550161031604a00300d038a072070780940580c001d004201c0001c002010020511248041d04c1e1040d00c1200c0d0b103130782c4020004110040403010b483c1c03120206400c540c00b8450074401040440c01000043c080113145060003603896800341c502028801c2465900e0350340b103c0c400301007550000080c507581c100d80c024078000302150b0f010420f107450604000d0100a804408a03080229010100ca01014010700f00d05c01400c15080c0100c1100003803082a040d50300c3e240d80010120a08815182100365642c2070142c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 743695179 1250 743693929 743693941
    0x20901230910080415050402041b0305070207080604020307290408031e0705072d0f0f060c11060a120516030c02010c0c02060d020c03031015090510110c180924 70
    0x1404003c3c004030391054032501c8608092b00070600c81612903a550750042400e007080b02c0c01a040c0142c0d50000b48060b000381e8200405030700c00040400844a80c035442c81c0c00c050180158402018400e40342c00c0310742e07000041c002203002c000005005084640000179900131a0180c10040c20f114aa40040c2603030402d05003004400384146188003051580800030f040e10317410001111030a07403a0b420603034065000c1a814040d00811003c844060015070070103c0403011180c989403107103c00d0300c01c81c0b441907000041741c220080c8039441c0b600700c104500e181480141043d090809007071031620342110000f03203031400c201021032050003070b200c07480b08a4546d942d0321007845e02445550340c0309076200c500d555020425528450f9040004600c00c0080c03414003a980ca0a0000389007880700801c2004017040300d0b444081c0040d607145a18507603910000d092500e622220300328514141500380722300b698000801d45101300f4070402d00210a21500c1d101c0107a9905a003402445c6003c9082d54218182404000300041e00d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 743696429 1250 743695179 743695181
    0xc13180536030c030705060109140402010801030803071e08040614011a0906070c062607090e060d02060c010204031104020703050702010f230405090a051504020901230910080415 78
    0x20700400c016685403e010014092456110517001c40d103d5100da401082158000e1007034004410b602c1c2012080f608007500003c164880602015041d00400404600c01c1d500460074150103000741d80301303010540042440a041e1001c00c6401759034440c10400400c3c24613808861190599541101d040f0390700020185003010340d044029200c0c1c01807400c00070382010030b80f50040d160040416607200c0c80d4869101c07520440001c200220386000d060f01c0005d0180140d0401d0384030040d5410001c01380b82558640c8000380c200240f13190003a4105800080000603e141034004000340d074040d5140851040c80001130000f00e214000000c0d000401c280906d2005620415895440300a00e180071412080c4da02c4074851080940011801c0802c0e001900700070742c3c100842c5143d40880541800c01c0140340404c0b80b0340c11103500360000c51085600140d9842c41c1da0007040480040014554601c24411020401c8030150b40301180c030030700c5100d480e50f84c0c2c694284921411803060343c2c052040c0500b010041081c0c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 743697679 1250 743696429 743696521
    0x15031e0e03040b03091c0201050f010909031b0b18030705030d02030c0f28020123130b0108010e01061203140d0f020703120e07060e090c131805 63
    0x10050100b0040001d41400c004090350003905850b0103030226a141401c900c070302140000a50083d039041a0402c50420302c44640e070b50450310710020100303a00032149412100000d2303205c1c0c4000d140f512a0102014002d6070000b0a01c1303200205d462086070400d08512603076900480000502e0b0b0341c000c006d800d55100241d009581c1200c01034025a040648a1107400602e400c00c4052840031070310402c8a4145d000b410003c414282e140340020050302004c031a640c090070a0041e002411001c00c0340100d6481058030707103030758061a00a80c80ca4003658560001a0283c401508005020341c200341d4081941c09500f0410a083c990688500008848850000c3c0250704039450515800c0d41e9095100010a103074002008003c1c030070741d1140b29a5255882c070100320303181d92a0000c000c0c1e0003030030207205c015000701c0c400100b0b54088480241e10307910240003210910400f03041142c0ba8244140000b07000c0018000314000450708d0105101c0c81d80d42c907041e07038100c4a0003030421140100945e280402030030078203800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 743698929 1250 743697679 743697701
    0xf0d092001020f1c210b0f060f090d02030c060a020115150801061d060406080402120d0504140a0305070b1308010b0609060a09031e0c0911090613050a090615031e 71
    0x40301080e05055800060071007002d058016071078980c032180c0c0c0c041c503124140107901303003048038249d0410301000701c1145030b4080d020b0050700540250a425055560404c4102e00900d401440c042d916460040c0003800307020303104501c00c1090012078010401c489441416804001c1e107584046003030b881d200c0c0c111040c50801341140f890410482d1802480e450f644020805410709480d81d06003418144148100700c08500c0a410305a00203079100f07070300c0c281c6c080200c0e411141d03560020440300d02e0070b10000344459401d5000510300c0c1301d84000000c540c461440604808042c0104400820b9a1041418242c5e001250742e1940300600b000b590003a45002e402034500798030707545001c10b045600e9a9444c82c05101c1402050400c1141440e08410009681c0b070030009422121400d000441c42c03950012514045d864000b4407a01011800c642610000840c1a00410700105040301c0203640385a100020400e50045919650318405520b1119029001c2d4034038015000b181c00d842180700304280001003401d01c01c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 743700179 1250 743698929 743698937
    0x151823060a023901110c0d09050307060309030509030d091703130b03040326011806030f020d050316320c041e09121b0b06060f0d092001020f1c 63
    0x1d0f0384a20074444c0c0310002c0f4009006a40d905104808685401089040e58040004c8e5480c203009945021a0041c1155228100451078201130b240603602806032860503901b6110b002e810315804d90b8800c00c0c8204482107210f4800c1d0481101500d03a03141d200302445076503010f1180004001c200c4042d00150ba10900034035080c5c5401c01007091042c00a415140f842620828000c010300c003080350301d0304054140e000490204507151a60740d400052290206000e8071904c1d82000403000d2140c00c1c0100c0e402840300d403040b9101510030f480d01e1910312141441602c034807040c00d0b4440da0610706a0600351450182400200316010116003000040d04195023541e17401d98066500000340b140d01c1c008d20804920405075640c903410501e00082100d00c2c100c0b2541c0c00340000302c2000001c208036034002a001202034810554800780900c0310342061003884500c2c61003030304d450351410a0101d24500070300541560808806900d600c0b07001240c4d202c611441d0030301240c002c00f16001d000c02c80404401c04089550074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 743701429 1250 743700179 743700277
    0x2010f030f090606172d0102090612190504021810090c021c020601120305132105060115170402030c060a09031e151823060a02 56
    0x351907080d100428011208552922024804902e12080c40d85203001400700a110700525a0b500e00c82c10050000080c100200c3c00200301d0b01c8120039012540400c10103402c4980d64088400242c8e059102180c0018804441701c1d401c038040c2d80c260087d00d0003a9002001220514011103050300c3c4c110000e0903200018815000002d611031950040c10804c90945d0050003600724141000400c03c10b0065884085420080040c00700303e0403601180e1b009034051808903242d5414244006824203503070800b03081c951905411040c08400d1441d00c0100501c50001e590080e680d4100040346c1c1d40c0ba509003903000c01c2100c60350380340462002030765a81c0280010111148540003030045291907215611201c001658118180240041e080c0341d005035070443d04020721441201d84441c42030b01c4101003498040c03611076100b40700b2086064800e03903c554218903001d803c01c10000720a181903401070400c110030f0007400d00041d0f0f040c3c0746100360f40070760502071a200c0901d07250744108190848401000421949091 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 743702679 1250 743701429 743701451
    0x4090908130524130e2d061804030c05010204090f0c080c0315030a0b0915130b062101060803090406050604050609150408030304030801050109050d02101d040905030a0f0908030702010f03 82
    0x204d00c850103010b901b080061410040301148695240941d4030b08524102442031003800d49a8007042845800141c0c40000c06407114a0200da042c140100003404542c000b040119200305141d0250088003409403040100d191119030075286560110b030b86070540081800060a4480380e000001d0001e6001403d03035134904881d980b56000c075041035502e00f20340d80c030155074448900814004650003904940201c0211480c9945814641600806144c0240301409134140c1114041409a01034041034000b8044280c0720070125641e03420040c1c0040c812801c000d000142c03420711070115402d840010b801c852030004014240b0039840c5c0594910780c40c01204200014a0920038005140168880c1e1758004240d4506400101114010780003544100207809103500165a0701701d0700114540f507800c00f010800d40780220300c3c4550240c000c009801c6810702c894042041008001800d429155440304d50700511103500c00c95091406009000703441c2d00c01c00a142c05580500f4007510608460f00d400300342c4011030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 743703929 1250 743702679 743702699
    0x60e03120301180e120f0d06050405130b070f0c06090311150f0a020a080402040e071509090c030219080405070504061206050a02031311060409090813052413 69
    0x3d90050307041c1030500380d444404882900590f0920f4002100408088000c0c0b03103908414400d4040d4580d0503400001d10441680d81d030b402a000400d1300920030445072400007250b2050b030141c107500300d80f6000340d80000f420701c134095000004564043ea59240821a5172798920004200c0c04005809010400f580c2c50011001048940d025482c1c890354503035a8104410746c940040005050781d1541c50041c030400000071b030300c08049940650100c40c00b24a150300604818202507160304100035110b41144544c6000d504403101c1000c0752040d43c8104000100340e0781c200c040340135550300007001c40b02c404851b000b4180700d03134105900280240c094915644c0d680000604a5889512000c0038074100c01203441404886d00c00c2d640c0c024602d010641c0b0b5450460880343d441081440000e145040002000c0055122181900e015058200302000131050a003403900c180e0700000c1004100d52441000440c16007400301c141c000c001c0f550303841070008081c0f5444050081d001036161050a4010083c0002c15580d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 743705035 1106 743703929 743703931
    0xa0c111e01050d0905030408010b13090b18010204051c03030c0c0309170307050102030a0902030f0c0a0b0307121d010c03020301080604061130090d09060e031203 71
    0x1000f0301d40002803030960400381c0540b10100c0c0119550105510030350b0503d800310307202c0b01c644a040034484141c1d805042c0041003c451003001ca81c1c5c10362498000176140c2e900768000f6042c552121301203810032101d61a4840a989010902e80034550180f152a48100c42031070034280340341d09600d0190441c041071088026030380503809008502c0006200b0f035105540d00800035552401c20b2096a0050711458005034441e00404080c03000100c400601c0080c8004050201040d1625284a14003560002046c8105100c42451707010002d1280384030700c1c0c60180802c1e01c5a10043c540e5602582164044291a4141481000180300300d101c00640c10f035100350b005070003090300c0000000c009401c0c002d0504403020080480e0951314001000e0f80020000e521501461020360380312410319a488021000700c1011400c411001d0001e940329401b8000b400b0409001c6500c0c40540da0991003103640 = true := by decide +kernel

theorem cover : BRFrame.Cov 743525179 743705035 := by
  have h0 := BRFrame.cov_init 743525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 743525179 ≤ n) (h2 : n < 743705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
