-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2921
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:08:40.343465+00:00
-- url     : https://prove2.me/submissions/291ecbf2-e2d3-428a-8894-49376e6d5e2f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 525179856 ≤ n < 525359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 525181106 1250 525179856 525179867
    0x4090506132f01080a0f020d0f050906060105190c050a0b18031801050714010507050c010b030a080711010221040e0702060403090b0309010207060509010225120f12020a020607030f09110f01 83
    0x6c000c0e819204640310300401410340042c2c584680b545e00000d20f81008568000c502081c0079119010685443d880c00c410710b141c00d1034689006484600300a00c0c0404c860014405001514000d0300590710011941000301c0c0c1c0c82c1e800400c10300b05480940c010018120064a044118440f50409092940e1102014101440c0211070111640100e511b0201001510340d04440034086c3c0041c180020001d4510500900d0742e1800f0744440508071241c2030000900186600306110403944041c41514041d195000c1c1c4450b00c02842c0c51260081400801d091007000001103043d5480400c2d13100418043c01e190310040c00c640518000c228208600100144901100b501168034081d480101000549007807400b250003904000e0900c10421403102001540c0c900c41d0f10300c1c0c44141d400000108241d500f00e903058138244018406101440307514000d00d01d04401030f07c080c040c4c841c00d50300506010302d030086000b4101c5040c14118003c080c6010300c80c80103d400150700b00c00000b81612803451460811005948 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 525182356 1250 525181106 525181121
    0xb191b031b0c090f1a011805150909070c03120507050904050406060b07080c060705120a09020a2103090530010605060a050a02070509150f04090506132f01080a 70
    0x8828101254103050303c0c00c950042064820179101101c10030604401110391004544110101c151800300c140f205152070720f0103107403144500c0880da29190b0200040707261580125000ea0101e503140c4080380c140340e0000d2610200c0f641c07102040119240104010341a4090020030500607681c84000a04000c03690b031001c2c01600e00032001c5525035800f440c24405981c40102070280c540250404220528042c4043da041014101c0745804c0720380d21031060b000244034044069a0004056200080b4158144020104900c9520010107896140d05014100e8481680228000d0300c040718030b910507820300b9035907000b0200ea54005c0203c81c045054001d02600300f6070010369002c0700024030f0038100c2d0b411000030007080740a50203841c0d10680e290b04010500f041119017813021071050b041c006403450302041040d0154402040000c4100c141d40f42c0914285085880c10840400025841e0611044d0b06040d00d07161442105000c4800800c41599010f00036601d00721b040c01022000f0811003080c5800150 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 525183606 1250 525182356 525182369
    0x40603020d090c0f030204110a14180d0303050f1003021309050a0b0115090603090812060d0c0f080f16050d080d0908120c12011e0b191b031b0c 63
    0x3810f55403502d4000c0140f965610040b481545419802402d83c207410041c1c0c0c88588540c3c48211108040c40303030004840e441036541200000302011240c000741d0b18001c488803035078082e9038006064642002d07455003030400030301001c40c0240381c044100b0060b52000610380007400d0320f004c041484115441c04d50b2070500070020080420342c201d0001710706180324010340c04402c911541c03240501c59440e403041d001c80e000103102804c2120200b006008200b0741d4407001303400c25000b034607203015a0b005898042c23403203c85400030441e908100c1c40400044c1400c00100f507402751020040c0200c0100050307070390502d25513445000e004008102c0e01c102030214000584401405240b41405040c0da03c1c40e011400764031103000c10040100c54404181e4000d111419295681c4424030400394507424868407011a115a00c0d00707500710409582d000c0341008280c0c01500d85840c0180314500130030003046001c1e140c0074415a42c6c00417045049840301c0460362044006a6504030450b4110400c041e0382030901c10359101e600f00a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 525184856 1250 525183606 525183623
    0x5030a06050603061305151008010c0c032a0605090a12030b0108010b071214190801050f061606050c13030b0f06060c0d0806040b0411121b040603020d09 67
    0x22003402056000244039a1085041e11400d58510f000c00700c140901c44e40c043c2c03465214410940b81605020b203104c0c3c20410102c0c1e100e00381a90b0328580c0f800d4400d0504100c000403c3c030312100041603000310070021345005004000c540449003a03001450702c881c149003c0e2480383c03a030f00883d503207100920550a2007504010203080384a002c0b00081d0240690381c203080d0010f1a054000507101444d081660800c50703200c1c0e010062320798441c1c0115008420381c240c0403040042003104c04024141514401d10001143d00c50028540c5800200600d81e02d802c20110700580d0100804103104520302c1011390b075554064400692038442446411103802210300484425150310804003e00000c0202a442041c1c0074920840c42da450100384143e900400360340718000d620000840d031600c1d01445140350301c4503018100064114512000405865020010102001000900d038043e440c280e1b007455445000d61800891603880560300090354841c45c4146010960b021885a170b118640d50010650942c002c1001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 525186106 1250 525184856 525184873
    0xc1a010314060109050f0612010605031009060e0304140919060e240603061014070b06120a0302030307080408130f060e030106050906010f1404060507032d11070503 72
    0x1031103004008140c0e00c6152042e6400001e2016050143c58812544542c1c0c1c2885a1910307024441c007a9141000c0420035500c4004c041405d86080060752002402a403010a03504407500f014401c07200120445502500104030a100c1845003000e411406002680e03c040550766031484031a48008240c85684218100040002d04482840c0010b004141c8500441281c01c51a6041c1e1980310039191520341040b0140002401e9241414500112801605126401d5400ca1361110300b02c0c2d1201700110380c41c0d018a018081c90b42020080c101e90346841900400203c1e40c0f9881c00380d0340c3d00000707000700d04000c507000004040082d10810380d03980010b4200110320719901d440090101c0c800d03600802000a6400707030000d18918050186c541200d00c0905a559207884110045541c2c103010004c28090000c1140d18680480d594001080207181c40c5d86c03031a4940901d0b1800a015200c130008006021802654001d20038031a0b0f00351401501940c202110994203400c0341a0624982d5441a039042c09500c11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 525187356 1250 525186106 525186113
    0x4030c0c0b07020f040b01050408120a030605060c060a15170105090d05090d14120d05040b07050426100c03021201080105220503040f0311100e030a030c1a0103 70
    0x2280841510422003101016110012031016020314000a5030042681040440b0f9080562000c201400103140c0a8603054403082d090b444e00c90b5600c0680f08000c0001412030741198035100c4d880c0079000032205613160016101000341d807680e01030b10100d95160b5030058100303040f64000322030000300507440100380321140300c3d40c0b400d009000c2107840004902800201c040520f20600c12200740035001044000901c02e581c031901c803e003200c0705124446109002428000c460742034041c002d00c3d40844408562840c0c04d01d0705204035207010304002c0500100780024820205c2c50105445000e4020380200114800c039898985044800a15100c80e40d01e020b044841c0158540c00500c5540304103406008140d80e40d4000c00d00303ca0007110001d203071120515085035003050b1030b82d016002c40d008804481c24242ca5a1000762884a40da004480800c0d6991610344a41800c03664a040c103400b5007404007460600001103911400111801030410946214607410072030305070049100c04218000071100c0750785a28 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 525188606 1250 525187356 525187367
    0x1e020307081b180a05060c1b0405150108040f021315211709031c020d03140c0918070c030212030601020705042d02130501090806010302010c14060403 66
    0x903400400181100e0028061440e144088240481410b1880745403d000c44043e814440603501441d50044e80404006413641d502000741c101814140d01070701c3e0817040c21145c8507418404040040c0110b0504007082003d40b20b04c40c23101c40465003803c10b0f00c0d19039141c1c03510b600f0041110700025402550b103400e890b4205c1c41136100d85c031403400c0c09160318901da48403805055004001180a6803192011020100040b01400d01c2070b03400c07120384415414030100c0c4000a041c005e881502609c2d80e94903c03019005144e0400111241a0040c1401c201605420244c045c010000030500014000b000030140340c15220306550102040e00c1c0b09000c42c4900f8500b44c024043d040080007a001445548131811681105008a134040c02c070507002421410310b05010700c03010300451051100d2103c01d98003111343d11034428501400021040f40f0040c4c1c2d41043d030041204401031a08454104135a0f020140052107000900710305607a02401c00144643c2c1518007620300f50440c42072402580034031000e1004058106 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 525189856 1250 525188606 525188611
    0x206071401050603070501230a021e01050a06120f02010e0111070306051501112d0a0c0f0b0901051b21090915090604151a090f030f0319031e0203 64
    0x118242c505d110307a46e03001100d0300820100000d000b00c04964448248900850040000b1441e6005540b94400340103c0004038054008911209075112400c016007007200748640800b0b00112030100802007850346411225041c1c80400905010041c90501e80c56030068100244104400003124603550301ca150020140c1819a020340b040e018015124245600906052070307251084001014074401800c3c283c0100743c001c0c3c3c02c3d0b1552107160010004055814007442040d5800f494440351828502008942c2130256580801c1094201b40484040c583c1c2c4101110104160340c00303c030380274640b43c2c10028144101064244c124074018040e0444111500004c0c00041c0402c50700c004050755030542000074800d80c0d0082c9648054030350001401031506502108680759404010400680c132107422141c8114581445d10350f009002c60702224920b017030000d000f001d00302a4080c04540710204101c039642d01034500c03c0c010740c05104c1c030382c114514400d0380003451001101ea424140514003507501002076005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 525191106 1250 525189856 525189859
    0x3050a060e0a0f11130c031508070f050613050414070206060a06090b0703170106050d0e0c010219151419411f140105041202060714010506 61
    0x1014030040c03005401098401000d508442c40e011180c603183d546040030407585401a50090a0317004410038005144112456213403a0340300014101c1e2030244517509141c00b6400100c03503522412040c02032081e1103144004a400a4032441e03200d2f101d03c020f003e11091590042c40c2c110b0300d40101058440301c5000000d005615503002d41d1070903140c9a080c00082c0c02c00f401040e0110300320213010088900903200805a031402460100340301e10a20700c546034010001c2e400a400200b0106601c1001d0301e1511514407085455401003140030141c000103915110340f03030b00c140301d9003403a052228103021410106840141070032074200301701d46446501c03484a02c410b403210000366285421107400019284103c40d0b00810a91900440516a80302c09010207039030a0101d12850703d0f180f115004c0d901d440394681c02035001c0c0c2000d01e6403075001d04004202900b40d90050555541c40e0300c0300441d51740c20000b21003e49a0b22440d84540044600104515101d03a110080200c0520071107604800019400103015840 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 525192356 1250 525191106 525191111
    0x80f03010515030408041202130609051f030c06081803070b040605060306041a06190314060708010e010909060b0616060c0212030c071403030f09072304050a020f0403050a06 76
    0x70328802c41ca00d00d0000315002400203200300f0040c04000c10800000c4900ca10041201200a10000070300003524041d50000000b507444e001806020759510401424050b4002c1c50494403a2440c0c44070070700609a4880c42e4180300c100000700d40002c020304250000c01c1c003c403003100d13074445661400105480007118103441325807400c000f1607100c0c80c01040c0d003801a50084001040b80780c60f160301c08503031038000e4201c80c0c1c80705000c2e607611110364420b20020011400750b01c011408178982c0d4041e03414810010200750400016030700500ca0170050800d460b0645020780d0740040ca15142c0e20b045e60081a0085580d80c0c00030340416410303d8445901e1441d01d819101e09000d00c00040110780690740c42c1c0400030101110901440010901d400410103407a0050191122111a44e02815601d046501c10340741808410806001c01140c1d0004000354401003804158000050004041c0d04100c04180c020705841140c035100440c0380584c0c03980558440151484a155441d5a03929205030b0b21081520100c400c0760 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 525193606 1250 525192356 525192379
    0x10090f06020c100c120f0504051203030103050c040e120c0312180d0e01050406110109020901080607090602060c030c0a2703060f020f03010e09070b031519061d040603080f030105 78
    0x24800d84c60481c0480d0302a20159910b00c0c40003060725200820104a020014207110009580d41c03084004054180c0c2d0700c014503525419828002d00344000d54032201e015078105000140d4400d400110b2141c01c1e101200502d8503520030001c600d056210b503a940d000c64244e0001401504c840004650051141c42c60448040c050380b40b1b400d44080340380301c025a0200f2800d00042010a000c2c0e80101400e104c400000110070126500060840801780c005481d15444a01005803c540001500000e01210b00062842d032501c40a070041500c0300400d0030418030000b0880e410494040c105030346000f051072a00e10f1440441c50420755142c100c40c8800e4900030705020f20414905200d01c225204c044604800034516030920747d940d10700b9a0081e180c0c5550344240c08000803003a28802c051070207055104c0e0412503001d41d05040001071000910802c103003010041d0100001d0307422104940e45c291005d054001c2c6400344100050081000d40d00150180c1c2c1c0019000c0a00c1c091a00103505a400440c0c200c0c0010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 525194856 1250 525193606 525193639
    0x1a121b0a030c020f0f0d050c0c04090309031a04020307030807153e0406030905031e0403110402030f060108130c030807052b030f091a0405010b1e10090f06020c 70
    0x2005c0d02c01c04140e00d84c02c0b2081c4402d0b460301c10340040c00f005414400300c078000d600c020003240442c0c2c0020301c10703070005401040610070400080e501003c0c03500002102101414650000b07501ea05113440018200c010004016081207140c1c0d9402850180d89001023003000286203210201c1c100c035540c280c1c181d800200800c5607105003080d4600070a002c4045a03410139040040580c0142051041500d407440144600c804241d81c0288081c030403054030000d152507602e14900320001402c541000e42c440d60041c01000440805041481d82c411404d21705031415440705000c4c10705050b500750740548500c012000100a0010640060480d50701c284100e80000d20604900c0305c0840274601e0404041c07042c0e503950700d0101e1003038105201100d5020400034441c071041c1c0d24503140307200c0e13042441080310074541003001b480000c0c82143c0c00a40d065908081400401050242c425982100d09208005226000c0003031485000401d000c0c0041d8082d078003003203803030741d102a60b40c0109480c034a120711910401603154 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 525196106 1250 525194856 525194863
    0x71109191b140a0c0b010906090c0809031c06170a0b090d1b06020904020a020f1006050607060f0608031611010e10030c020a080a0908071a121b0a030c020f 68
    0x2000240d0703101c510440151540d0354141d40a6800f500400c03404a490b00c012400c1c601280d8020000400c1c0080d403103140100c102c0a070340710074804500340030f0104200403100d4408012030300d10304a807611b0001507034145005c000042550b80c01100c086011700f8110120100d0016402e80703428096400342c1103599030051a19525145404400e0000d00b96076404100d9000200c0072420040c8101c0002d070414032410041400c9801c005c0a400041e401900341004010043c030409480380030080c400c0c440241003002203200c1e0302c0b4001c80144113645d00d0303804011080481c2d2141e005808118190b995410b030349103485081061480064505032034502406a41e50300600d0201661000036109016402c26001c003034000700180280501940604007801000583c600002c103190f000588800d502581400031591410340309802a042008128100e18070100516041d15a02c003140380c0f984070f199036040e0345440d5100681983c041c5003503000ca5000c00a030f03015080034880b0392183c1c0c05c0b20000d880318042c2c50364 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 525197356 1250 525196106 525196151
    0x4060306030b0c071208192d050723070203070605130b030114040507170106020f100203060325030c080105150102150a15030b040c051c0302070b07110919 68
    0x10514038080f42c0d80c0c1d40e020301010740d40540d0320784403580d00103007181c7e803101076480c5c1d61411450811600d58449010b8103440d08031202148504040042c2c2c9030003003003c0e048042c544d000f00a880c00d52841c3d66500001c040c202c5840701d5014050301d9880e982c07030101400d0381d04143da40300c484070540a0003107912a11101524101ca6030100308045400418042c040200400b4003074004002c03944180700d820b00f4030703018802d00030b056070740c020300310046001da078141000c40c1005400c01e1240100b06105507640c00041c01001c4120044e028018910317101c1c000380301a269540014411202d0080010b14560190320440c41f404241056002c0240034500481c2ca8940c2032912004181c120000b150201c0e8603540102c020603520002880496200d0f01c404940160480d03085402007c480800d000c28180000307883e2000081854031102c0403d590ba0207925204140200c800004003c8ac011007030020003091101d401d5005000c0c202241080b004014980141c40321060600e410090010880d41f4103400740b10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 525198606 1250 525197356 525197363
    0x40633140d090f060504140f07060903080a030b090c0403110d031d01141605071a070303021c02070b0f1008120903032116021204050f03070b04060306030b0c07 70
    0x78903281038800418002c015020094401a5811602c2000a0103920909000e9070007104980740341e001c030024082c50040148065a00d5800c2008100107a036003000031082581d5020078155100c8202c030070304030010100c0017016503012040e5814030440b030340b01c04010010b580c0108501070290702c0300400c0c04081e10305444010300003040044c40481e0310581c030054007401e240524002c504200f013418081050b41007a046803100510740f172030035800c000707080000f080202004540c11107880c1030510b10b09c4450080a84c081c081c149c001900d1104204bc0401189a40c110360a00315214a131504001c5a02001280c003610204440703c04a29a1191000844200c4651100910585655004107101900030170801c5416110a104101c45a00416040d140403142080354144071b01d410700c0702072032641c000c1d1461001e54001c94190040c0301c407442c048605850702540c101c1c0103c41c80f180464509440360703001181801d4042000315080742c0c03541181d000c803802203540f00810b0b1a540403d8019108440c4000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 525199856 1250 525198606 525198647
    0x1050601090504020a0e09070504170a0f020909011401030b160e0f130f0509010c1706010203091012091b080705090a0507140a030c030e0309010804030e040633 70
    0x802c1a45401c0d001040000750514050040a082c840800e450440c21b580c1d51020883c041024082c900c85100c0da0200444180002c191000050f00d0301a5240345c1c0c03050290181d0b4201d00000d00ba00401d4014008001c1e05540c1000690383d01d091014088a06aa10050ba62503002401070f03010321401107100c460704010714031350700c6030350401c1000901048001d10f040755039242d854408560301d89120300c901c100b0f0307480c00100318401c240000a15402d085468035a891b03010070184103559a0000903508121401d5603240c07008040044290307008101d42044c11800b5042c04461030421a5150680510401c8007032103090b41c40d03c0b50710143c1ca8104c03c0c014980c03c1140c0c50f000951f4108030b070b0071071500b0410f281498510780e4004140d01425900401e000d030082034a54119119003541403103100301d02c602c91005141009600070000b4070300c0f107001d0f1001e0100050002c0c0600c8959840c0c1c000e20041c1162011011455082c0d9020142040408250500380c910006510703a40c5000d002c49207515009081d45 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 525201106 1250 525199856 525199859
    0x50a05040b010e1905091606051e0a090e070c0506060f49020a05010e210102160b16030c02030f180d03051b07080c04180209160f020105060109 63
    0x150f41d40c80b2000700b000981110315100c44020380700e03078030489025a403101c1c05000c000020181d0440040203a40c010400c000741004600d0399017031801c40d5403000b512110b0340242da5034000901114009080d4000e0001d8070101e034288901c141e000011402000d10a00598020f40d035004204030350290b0b4418496003000c0181e1078800c040005080d000904200a0840c40e4143e0006c9882c0324805114418809a0341d2203c090070190316000c071800d0b004010910349400c800d01c3c204003140c20140c41c4065040b803100b00030401d4015042c2074040c1c03032132039000420460320380102d070410b0b1900010a40300e00c0701c8140c5202c651820207209000d0750380c01c0c401e41d8005624040e009030b54500c0d90381c04112003400ca1025480f070003140b941c84003006103c4501075030310241c07240d0002a000c20500d80e90b415016480d0301c0381204004698003c5407060501104a8000501ca1844220308801d2016044000d42c00b070300c803104008000f40d041c8050544040d503643e0750510040f41c144140e0803202c066981c180461050b200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 525202356 1250 525201106 525201119
    0x1d0c09070f0309021203030405160e130305130e0a0b01080a0e070302120c0d06020a020118051009060902040507050a110d0806060306040e01060623030c03070c050a0c120303050a05040b01 82
    0x203d0350405201030702d50300790021549105410f50300705480c12540354100c0154140040c100c804404050011038a8428a50801d083c590000000c500c0000302484404100c07040d00101504090006141188442115150402c030701d0004100d0215414041801344c0b000c501240003e01c01d88403d240303a0002009038030f00f15002c10654103101c01d982e0700e01c0d10801000d000c080d100d40c80100e450314400c0c1000f50f00c51410090190a58107600000005441c1c80c5242ea40031500004030b20700700c1d40181c0000507519060781444409402c080c40040c0d0428107150500900e20340c050000d0510f14416903a0030400300001c1e034140c0d140c04180f00e000d0002150345000c10454507044c0c00850b00440d00810000b00c0101200041d0b082d076070a540040003091034408034040744140395052848241e90141ca403855450291190301c0c40c0e02000d170004040040c03098101041020400c440c100c2140c0000c91048269511850000c12990360317541100000c1c20440492021041d500605006a038401c00e05032043e801c044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 525203606 1250 525202356 525202361
    0x615210206070213020d09020f090f0106030e1e0a0c05060408030304060b042306010e030a2a0506040f140406180903030b04090b090708060603190302030d1d0c09070f03 74
    0x44281da000d241940441c0455030148002c1c140107415030070100f40c7c2d50190040103503030110b089856001d020040c04001d0b004250080290644900f0304000800500300320b00c0c9451310442d080034040c81a001c02090124850000b103407140640300c1c2004411aa81f1001840514001c078403d2506950060001c40c00191981c0c000d142000c2000c0d0000a00c0c0c0110700340c01440c4149007000301100e41440e4240562941c0c00480c1c02c4010200b600100b40542169646500e10150f01451030440c1c9074030b10030284581c0c070285143c402404010049a2510f8a50340a080c5c00074052046170002034503403140264908060040f90101d0b0040701c80e400c141e59076618110b004d00303440c0c081203081580d20310030700d10117030740354860340c031079540076034102c4a0502c1c24500c031502c4c006454010312032650010b000c220130303560001400a41c0807051409601035043c0f13490244d185000c2e40c4c0b4041c0c4210b08042d12014401c0301074101c003007030b080710a08581281c210707417060008045056030020300140c0d00d0303161160218081d8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 525204856 1250 525203606 525203617
    0xa080408070209010909030e1c0f05030d110406020d020106030201051c14010f0303081e06060a0302041a0304260a050c15040605071d01050a0c0317040615210206 71
    0x141995454000c07160b000809104098000c800703125170355007103001031580c442007501d203500045d81d201000c03560803401c0c41010b4442c070300024121a50a12000c041000900036250261710000c010302c901d41c5002c81c0f000d800d4010b405003400501c500b10446004901c14003070501281e0b0180c40f981e2802d40940200d086464400c00361800742ca4480c10035106415001001c40d0003464011400c1500e40d0841c1b0300185070f040c1c040d2915000d00c5004400c90f40c480c014501c81500300f00221a00c660340c004400d410b401a0240d5409140b54101e041d04050b45c03d540b0100443c81588100e21502d692040c0215480540c1c000448203451494103103c02818540110b00071300c002d10501d0112441d400074a805c14074901c100f1a0304844143d10345061165080e0031141c010400440c81c0d0070015100103000c002042e0703000305034000c0e00304405000c0400626003d4a200c05404090b554040d2882c0f80c242001c1000c0d108204c844841e0301c120001c0002c0c0c8240c00040c6101d0021070070009a4907000c03070303001c2141d5038005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 525206106 1250 525204856 525204863
    0x503061e0607020a0f060f0503101719061a03010e150c0d05011805250f0e03010c020708060c0c06010504020d140406151a0304020d05011d070f06140a0804 68
    0x800c0000056a186004040140207680500c51317000d0602600410046400f4203802c180401031040c40a8500d0b0700000d0f10907124000c4402240c507450005813891f00c0550703150010385005500d040e4080c04099002514091700c1c11031104003c01041062600b00d40b00c10903580625003064034400503405020300040d0708122820881410300c0005190b95084800030f03030050b41041024144d14040a03520f000e9a580705800b4414100302205668070080035181c40080b10703081024107100c0c0000f01d4095107045d116200c024008002c1000c44150103962410b0f103005200313940c0f003114002140001041e00b280c1d402c0800e000030304156440d050a00029400141031a507113252101404120345451043c81807095015400110380761480a0b01028500701e2a0004118840d0500010049800040480345c115905442408241005003401c60041c03030b40d51240880201182d10f8078401c1d040c000b40b02c0041d01c150035118040d8940d107220070b8484152400420316403001c1409801181c2d4010b89002d0340c401d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 525207356 1250 525206106 525206119
    0x70206060904141e060601030b1e040f0203040b040201020f0f1905100e100f020a0f1d03070b070201030f180f1a07030204060e0d0201091202060c030304030801030b070503061e 77
    0x400b4a086400c2940400c20a00d00400d21040136401d040c0420003241c000400b824100140c5602c40045062031040600b03036602191b1244c0401429221640409100400c56508648070300b01464200810345055600f070f401403003170192101d07255030081101c02d480355401c0010014516540d0080c1c54020382c0101c00c0d10389000701d903081c0c0456402030056401c0400c104000e0803c008000d041c000803150010281c001c4140306000c165843c1c1d810841400140082e402d00c02c840d04180758039030b8861048050815014007400d0800680b200d43d0364050500503200342c9040c814a04584103500c111000050a0380c1135102c906d50b0000400d0141c0c07001c10159000b540030300320401c115036410840304000c2d03424800180d80000d040103841d500041c0b92003003003001c4600340750740031a580008041c140540079507a41840703042c010340e085680b640100c0e0307010141c0c2029280c980c5014200a00b4416003403009851003c00b0304005580a0b00c60ba080ba4819180104049031010031802143c2c3d0600203850403030342144 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 525208606 1250 525207356 525207383
    0xc0609021002160f0e0c031510020106140402030c03060d0206040312080103022b14070f09060302100801080307150e030c0f1e0a120e09090601091103070206060904 72
    0x1c80310a1942881903560b0010103aa01800f00040500c042c15800004202116001032050700c1c8010b604a8021704a4003c0c2c9880c0e0721040c60400010003110842d41d41301103c0c3d000da040075031f01034004200301c50229942100020140d002c1c8030a0740f00817190716540300d40400010318a45000d03c107443c8407174000f41025041c1504d036502e0b040c181e25040c602c0d4005c14044001001146000d100218124921411125544191190740001c590f0300c0c00f401031052140d160752400f590810004007005000091804011603030701c000c254020202070005034000c0b52180030084005024086190403245404001c41c600b40740d43d00c40f001c15035800703074004107040e445a1503525941002c00140007400c0300280030304000d0314580c0800d0720301011585403210350105d42815151507040454194910341d00303ca8141028012900111180d42100700200d90120001c0140210044000340042c1640d400c41802c001400303665405e072115000c101c03403d00050307000800140560404280301600240709400307064855 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 525209856 1250 525208606 525208609
    0x606090a0e1207020f0109030b150105190c0218060a090209150406030c08010504051b0310080a0f1209030807020d1106030910060f050102060103140f031306021005010509070c060902 80
    0x8001c2c890008004403000c103010083d841d015020942d915000d00b8002006840c5659441c22070000070100600d03400001004456a40104101c0700e1030540d2200704071080f6500007016081e64a0104242d002d000e040821003c070005059010303004039002071032402c58130724150361b04010358410300071180c001401043c0208000d152070f020f403025088039100032840c084003040c010250300050f4446c0b481b880c01c200501503103801da122011070a0103140941540c0b0b580300001201026040c0e4410312040c0314115040d82444800700340341031007910800c01098480400403003140c20200341c5c003024040500070002640140b41203588412031a20030002ca4442e9844000000c086401c101c405039210b420100c47c9100058180c858000a44807110340382440608020000750745130414080142054540e08502108002c20010f0581890744141140c5d601d5810701c08000408049100e150054425404540605d411b14041e6a050b6070010300031b01d0b0650f030703122812034100c02e8030302090b2480c03980d803041400076 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 525211106 1250 525209856 525209863
    0x60c0a020a0602040312030509070303081f1502060708010602060105011409040f09080d060605031e100b03041217070c02010e0420040f0510122c1c020d020606090a0e 73
    0xc500840402c446d0992035040541600c2e8000c1041000d074011150903c0081c0d00501400e170041c44d0080d40e408903943c543d20442d91084140c0019a41c1002d9584614105500069980c41055070755274a00c42079a035a281aa03840c20280510340c00b280302e00c2044035810342440041d101c036000040001c514400c201c2c001200702c50110b28280e070940d00025004040c0c12440c007501e002045c051a01a10b5861318800304411a0b402c51049000c0d2a0b0400203d101c2d1509880312402a000b11040d03140c0d030341050f2520098556104003c0d6001c1004800006080000260060b11602e400c0e12150b031007801c1c07903004640c92038a404002c0d0f405962100350b004024511044032898100b100d002c01da40e01e050804e100c103030020a511003882040034141d40c0043e40d40c840c01d03022007e03403e002d022480c2c0b402d05000c0c0740004803841e140a81c50401240031050003400103884c0107010345640e000c41d40c40b5803402c0c00301d0701c604c20265444051b9005002250030b40c00d001c0121070f400610440c00207092510b1100d42802c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 525212356 1250 525211106 525211109
    0x2a0602030907060306080d0e0609030c1c02040b010827070f090621170309100905060709051507140109080f041e051302030618180c040c02060c0a020a060204 69
    0x75641c84114240b0a240e00752041501078000d0078000c0507002d40d0032000030445010440000d001d82000310b00342c6250303101048404503443c0c00904498060780240040070390600055016440b650410030604510f5015042840c000c03044004a40d25000700701d807503040d0480307048a82c550346105480000035a110b00c011108084c100740c02010a006141c001540320341e0f40d045075000c80c0400461132000014081078003107480400c000702000d84990f10200300a08255030b500700602e219040030301e010100580415918070642040d113449020540b40c40910400880c2d110840000503010003039540031550582074100714540342c00012400b85030907618400300340c0052040001e0020301007001d10050841c0c0c00c00056900c100c800802c80507103080d000402206400f07101d03448580e400408103009440301e40c100180210303102d01000c6282805001d50a031840a01d451400f18007892845580c0e520b803601411344140504e034000d01c015100c8051030405a031060201c0815449412001c50014400b40003410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 525213606 1250 525212356 525212371
    0xf070c0f06020a03080901050f01120510110c0609210919060930110102010b1e120f03072a03060203150102010b030a0602030c04081506010f020d2a060203 68
    0x1003c0001890082d2040002a1483c240c50b4104010031030020391f000d01b003504540148182294200090034a2828008a106449880c80c2080210004605648000c12804a468080760001e54903e2a80d079110300308444070305e008482c3c00c0500c000c001541c0b000351603584d4004203104402e0404e0105c010191303e1a9000d080807c00c4454200154820b03031aa445007a1034080c840112600c0c1c0008010705144040b038000d00c2c0c00b8002c0c6014500745d10035848446101000b0308001c44140d441ca83ea0004601030101c0340d40b1904001480d1606060041000450031605ca0000d50600c4415a41c06010a80d0a10b4040440c20000e04403c04c0c0c02403001c1030001140100300c01a501d00b4100c3c82d40c10301401c1460807070306583c1030100d60003840e100000e20648081d00030030010707103076260030701a21114412035011000354451500041411948009918040d1400342c88510b610b19000c1810381e1030341003076046180803a0038400e00c0d8142c40070103a050000749078100801c028908070765440781e080b038109941c2174 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 525214856 1250 525213606 525213613
    0x100902070b0a060f18110f0d06051203070b01032013052203020615040b0409050c0f090c0a080a1112090609070b0a050904020d020301030503121b0f070c0f0602 70
    0x42d040058402c0700f02601010503180501c0d0305055900300d2041d900042c10f6220b0340d4070340c140c2c000c0302e0420f000c1e44d030740c0400704074411303a03c0d64010f0141e00680902d015152107540e40210030014580000201c519255108a1a0070640c0c0380d40c65010000c54080304811b000415050301542d41e50302d141c0a100010b1a61000007401c1c1852040c205400709200c0300b8010701100402441c01190b00069110351010040240e40000c03a411400724001e001c440c02c0c8607030070905211a540070800007150341d4440c03e80541d004212818400101300720480280c50400d681c0074108240590b4500c01c0c644107502c0161900d000c03074a8825200b01782c0455001003902c2e00c008900d00144600405c0c01e20a0503004103e010040c05034900700b4503100f00c0d6210b116603400902c08000b922440c0340e201d0f45c05440399020700c01d4045449696030b0802c10f80301d601854428400701e03c1000020840c1110305a8002c1100302c01754150f050482c40d052440d1198040074042c2c6d4108480d0100040a0080309608405825694080c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 525216106 1250 525214856 525214861
    0x1e0e0a08150a1a011409030c130f0b190611032107030e0604030f0e0d1704080d0215151c1424040b330109080604020a030b100902070b 59
    0x404442aa0a44200301c3c0122615080c8507030307103d0345402480a068803000d1b5a1400c40c400a0b141c014003507009600862140111261303424980c2c001e0410906140043c001401d80740204400d505080900500c0301d111541c09101d1a4400c03940e10201c07001c410112407810540406500c90b91441072000382c4404c003500304100206034035000c0c0b0014049110002c0c200c1b800e040d6405451149070041c060100f10a200d2190b01a40c0c4038000b0010040c0c010a030054001000010a03032964004d0050092921441d00c1400e541c910000e00e54406c0030b0000400070450f1910b41c0300c03101d02c400e4101d425a100070540074440c0b00039000000d40480300c1c854034044181040514085e820909040021014104074856500b03425040800d181e0384140d1040f600f034815038908003c0b440114440d80e01100405032100210ba0180303402c02d044500d05c4013601d401c0d10543c0c1d501510707507603404102c90003500b0003108942000003541c0640381a420102811202e83e1060312140410202e800006042e940f80e8602020f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 525217356 1250 525216106 525216121
    0x219050706090e040323250c06021507031107060f0c0f170f041406040f05060a051e04020f100806091302220f060b1201061e0e0a0815 59
    0x20100010f10080c1c100c8503a40c5044d84000d4400c2403024810808940c400071051142500c910450f29411040c0011039500f007441101d030301b0f400c4164802252280d0180ca004100a030001840c0b56007480a681c1401d240d6840080803006010181510003041c0710074040c03400000c90502911111000c424400188840c8600c0c0003807200d403041c0300c10b1041c842c1607002084038213485810281c0c85aa5800628410f0300c0d90301d440210744841100600042c05200300740010030408c04028007000f800385007200c280e45c079031820040172101c003640ca40c070030328404010620003040d85911241c1d102d4001009160f80b130104101192800c071001003d200060292020440c0034a001f810300c98020030064080c201c500400d034007240f00b1040f903004150f4800c0500104a24034039183d040080c044000e00024400e41b503407030001001c960000612850188401800460040d203e00e14102601120500703041200104400076144180b0b0100007540103407042e180851920300070071421042006484002441d89000d48 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 525218606 1250 525217356 525217367
    0x1090b0301060c23150603031b15060f0901050d140304081005011203020604021c081602030d03050601080c0904110c06010f1403150a02070c06050309010b0307050904120219050706 79
    0x80d070035103048540a103040184c21001400704240c4410000041613900d4000c0000d1079801801d103180b800c031500c04203503450702c0c0011985d03a082e14003080b4120086d40390030080100506101210b070f0f40110b00c0100401051074141c012068507402990701003042c0c0c420388140350442c2e0060f041a90987d00c040d648103803035440c51064030f0040200c244410301800c09a07030300a407902030242010740318402840d070302c003450b05c0780c60342c080046a03015208035a204205d81481e50810700404050b84207025032480b000030306000340155032240205035602d140542e2501e0740c0c03882603000030700311941040c1d079900450507800d01d4000414800d0035600081c04290b14028814000054540200545d082c004041501540f800101c4000131b00c0c108408003ca56200d0540000031301070901d02600e0010311000014440390010700440c0176607821002400843c600d075041c10342c3c600c281c1c440c803a00100301400142c003089440a0348101d200584c0b0555940c186664170402c191302c012403080e505a009048108416600b01e0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 525219856 1250 525218606 525218633
    0x80d021612031b09030503040e100819030e010e33030a0e0c15090405040f0f032f0304031407030f0c05100e010210111e19020109120e01090b0301060c 66
    0x745030441d032241c219507480303480e40518890984009c80d2040400c428407030400d015000b03880a0800c81d02c118001c0445070100b05207980080c0d0100f2440d04900300b01d5441004981d4040c034000c4c1a4503554400e442c004241c074451988540c82d42c24010150491a60341503000f18060468843c000c40d65042c0d00071070038142240b41074542d105442481c04e0623007005101056a0517100c00b101c2c009059645e60902070400e10700d0b904000c10702d01c140300d604c604068010240e0609181008405020303c143c42f00000c01c0c180210350302201d107501c01d02c0100009001003508510940808094809a60b90303a0b556030099095902c00322448c000d41c8805204906101c0130990300c42c01c1c0351070455080d41e08180083d40728207062704420303a072076101c15511101c003602c00e0072590200310041928604280c080b801807c0da0f080104850030264403d83d2080c6500c0c414014220100d8000740303080403104064800750f41e44480c000c249414062880310011f41e62110030061402450075898a050703203041444c00c141d18043c2c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 525221106 1250 525219856 525219911
    0x5010e06060d12050d0203190f021804020706060e07050301090f02090a0302010f0306170106060e030106050f0d1a0703091101020f030f220305011d0a080d02161203 72
    0x104007004115aa240b450036115608040b036900105240207045038030b441000500308159000000b40142801c8554040142c1c0c640c0039010020805110030307030001d0388103100304010710701504102045185800d03030080c50348910800300013651698600c101984000d00f1202d54010074000700040104c04040d0080e55180b06c0030388011031415064a0001301c92040034040681000700b04524014094081d601c10360180014a00318174040c0100c442c00742c080c010500818000072082940c81501e4141401900140c482c001e0141c11810341c001e0a001c040c5006440550b00b0030104071010b8194642c0d600c0e1136014900d9540d02140326800703030400080d6401600a002d045501410484048680101c00d4640d01c4061214060303a136954100180f030b0a51080c44c0c82d00c50800d80520005c10804154005042c40c03039454800c40440d0791710705c2c100340c48801c44000070b49120f1040050000501d03955000b8030a04503c0801800c80c8a45602e07010000050101d1403000719a551510303032011071808620400d107104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 525222356 1250 525221106 525221113
    0x2070b011212111509010b12120d02070312050f0a1b0c020603150a08030405090915070e011e1d0301061d040f12024c0b0d05030705010e 60
    0x550760b5070107146001c2c0420700010002898070392000c0700d07414004075480c3c100740401d41049090030542c042c001e00d003107084607210b13816106000364884000706280c10950400e000140c200302c0003a420324040d60100204070200142c00308040032401c1c0382d12603280500591203001e02c039460000080c4080354005204044030450700d4842402080d8800800400c0c07540c10b54820b038903a1915407801c11b5015800e0007980d400a84200d000c40d4402000000e0400c4a07401c5070581c81c0764881e0700340c554444070603110f10782c1720082c60800207031a90b02807100c10300101010301d0f181900e0303800c5100c2505015014a100000140c000d50071164180c9503c45d41c10b8150b0040717008201c00e52038040c4003000301e040100210b501c00402000101804a41540c807030b00b6035004400581203120f9440e0003912814003480082c003011150040c01418002c008048500b41c0200040118403154504000c4950b64600c9038125081d890720072003001500c03864500d842c81445100255150300007442c16074251840541907002d82e0b030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 525223606 1250 525222356 525222389
    0x150507020622150e010204030f11060a0c290a1b0819050a0e01051f0f06090308070501060b04150809060403140c101d010513030503011e03020d050102070b01 69
    0x801074280c051145501c070f14200f4900400910150252804001004280d44042400030a0010048840301003500c40e03000c8420601c00032081100c5400342030304440018040e003c0d600c0018012480c0000d4148400100003c0010100c00a00810710100d55400c620b6844142c0074020700e0030305800004013440c0c1c1c00d1010061400107003061000440c800212142e84e2100c0114100600c0d43d4015402c0030310a2000b400305182c204d1022907202134407414100301c2e001c44940051030310b800000c44816107856550381401203140d0b4440840d540c00040003590a5507a9800010b02942e40d08000c00c020030650b08500050301500300081e200803001040005075404c414200400039511002200b00d400e03800c04a10f40f1000032011a80c80c10203070080440b41030303203000d907400384070801800b60030403600c41d0000038407056440f80b140c9440c4103501311000340813401c2800144001e103109440400a018480107a404d1142d4a0300000e90140e00780c581a00c49960000c0c0003400d020036054402e01412415688441b4003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 525224856 1250 525223606 525223651
    0x210030504080a03020703050f0301080d090906120b15031c180503030f0a0c120314070507050606010e0114120103060509161e05041b0206151e010c1505070206 70
    0x43c402c072089034040640c0044c1304010540200d080d81e500702c06a01e862030b10383d81c60303145941c0c0d1020111041320100340e000c01c0004031586140030301c005803203081543c800d06031101c2e038a51002030400341220080124602980c851034404110765030080c0740440302c20b41420741d00c45010f410181103901c40c5d18820304910080c412502c0000844e0703880c0410b40c143c00c1c1d45161181c8200c52001c80024010620140c40e4034101e5441d9054100e980e4079880c4121326407007600c510b10180c402d4440c41e00001c1440c1c12076000a49150300580310b89840480c10b05040c41e550104006202440c3e01443c20522504000e070014003c0c80078901c900e82e0701854a030010004c0d00ca030f03141c0c0e00b010300700144540d400940c648203501c0c9100501d600d642004007070107041404802d40c1c080995031044182442c600c0184120300000d00c407500450382c911006a0050f1a8000503808c40551041c813403c41618075060080c40c00c947d000207010300c003401903421035a202c0000e10b402e044400034241817001c1c01c9070b07020821403c25014030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 525226106 1250 525224856 525224873
    0x20a030305070c020a0302152b0f1a010e1201060b0c07050d02093412140c040e0a020415020d08090c01080c180a060320163c0210030504 60
    0x15242c0490324104281e0b00032440d01c9061103410401083e00d00307000c400031030f9082103016a100c1d0310060827040c80601c00c580c4402d0110741d2748264002c1c903d009250342000310f500407035401d9030842d00a08071042c40c464140c41300d403c2d00c507254003c0b8140a0b000030321244520040c4180405040d0882d442c0b096600349400090256201500d090700c1300101d04a10010320f00c80d182c40368103583d03800010b428132000c040c0c03015000c0c0c0680071103446100d05160801d8511031103010880d00c18050f0b00012400c06041480c04000385500502d15181c09500300300103d40000031041c1c2e0043c100c410345c0100125140010010128039000e0118200c40d4802c0d42403c080313a80144400750312243e860007003510f58001440107a90040100c400d541c02500000d000710300c071649500143c240d141681c050b0151a4034100000b0003034420f96181a8540940025400004000c8003c50f12104182d600c141c1d40a00c1c416491038a01c8841001480300300780c00c4068000b103081503042d543d06c1518a0500300301e10718041e22000765 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 525227356 1250 525226106 525226109
    0x906180b120d05210f0108010516050a12090501110c070b0c0c04052806080708030c0a0b040201210b0a09230c070602040801020c2a041505030a03020a030305070c020a 73
    0x500030b021804001c9044c0f075686400c00c1c40c510310609840d03800c040c0c0d1130b0f040d030120a0190760059402d04000400c806c46600442e01d013854a03a41d4207251078002d140448500404003461081903460b5148400481c0c402d02401024903010005a69120b801d0300c4c02614000d199405519000d0040c4003450030140c4c04506400070700c0c0d0a480100e905da882c404054503c5001c030314400740041d1207140342e5108001e603502c10001e8032078810031100c0c1680c840f0081035490281707500e048525448402120300160142c8000e503001031060605d1b02d401c140000011640210746803560301503030b41d10701070b11105180400354000101126541000b18a0382240040c0701c140b080141190b0030105200843c0040f00354408075914982c100e81c0c11500c5075159184c00c0d001c0d50042c4500d40b039034800c1841001d000c0d01d160049495504080f8a140484501113050001800b405141881e019080c203400003030a131002e10200000602c02e901501010f8904d00c0c02030222280607049900b0041e1240b22000181c0b9000c02240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 525228606 1250 525227356 525227383
    0xf0709080f120711120c0102070501090e0a09030216080c0f2e05090d0b0402100207060c141c120507110a02010e06190906091208030106050d060906180b12 68
    0x2070343c440740c9040001c130300c01c5040c51241d089440a154503034140c202141d0190303030350400d03400e940d64643c0e42e1004655200382401516042030400e40421401c8a596214081272072103801900e5070810610401c0c41060f516a01a9105811007500d107802c91911817044041c04030201e0b9994a6464050b10402680d105800044005000040040b107024080c4040d40c80e2420014480d81c0c140000c1d2622504042007910704a0240d4180c1d444a00b509001150700d0060f80d40c180d80c0c003410440f03182c4949000710000503c00407280211443c040e13180420148038040d02c0c0d9a51154403641070555404811079000038401810401c0d014501103070035001040c0c00d161303c2c2c0c0900e0a50000300010001821030f1181c0902000b4813001c0500c41c2002c240c01850160880d00c142c2c582884159131900c2c5e0140180903400c00030325000c001c1005010b002e001d2006008a070b42d003403c001550726180c1000c0e42c11103844e40c018900c501c4440780404841e00b036a01803405251010340c0c0c0e070343d40d05c1c4c501104c03140d640c000315414070b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 525229856 1250 525228606 525228643
    0x1090207050a02040f0608010b06090303090616020d030c1103010603030f030c03140a050405100b030303131b1e1202060d240312110607090e1b030f0709080f 69
    0xd8091010412103112140d40091007002009250300e9920000d022501c1250f00b19400d0140200c65490201d05480110707901901075464000c00c142080010f0340302003294903080150079512005604c0341070821405501c44e80b9601341c014141c4c02d110001454034007031075110b60305000e02440080d60080c802c00045030181000304d0b1002c1c40b03440550150940d611410940c2450701c041200c01d078055007100740514064819503501121980800059565000c1c04640692003040481c10041c0c0700045840614000d05c4002c0008a0394100c2403244601907014405048540c00c02030f5003512500d900c3c400400c500c428040c41412550b003c9141405003071000c2051a0342c0ba002d02d8031068080c0512144084c50070140421071b51a4a0f141c01d52481220036800040c520780300c070501ca1030000540310b004107810340399444040c0c50a07001d40018500200007600c1c044504e4038041140440101035070294001001106007480c00c0d00c4000c2100700706900c5100300740e10400a282c103513800459080096854500351 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 525231106 1250 525229856 525229867
    0x121a010503090f010509030a171e040201030e030a020106170a0203061b070206040303080a15290c030c0106081203041203020c01020f0c15060303131809060926030c03010902 76
    0x401c3d007041603444102c0100e5091400f00041c0702004070080c060003043d615000201640203814810020045628a0400c803030f004890a041e0110500355a12a20501d000706104c480f1105090442d0440c42403500540e440e20401e00480100d111380d2001000c039240102030310280e980000b65241800303001859007602c01c10070b01c5029900b20f41151822900075004565696491500812042c01119260350701c6107044e2000459905900c41481200d161030f8501c0c402c070200c0b4a10a0704403600071104102824208031500044200f0300c040e0181c940103c000003103051410b40b400782001d1420b40c0d000d09c204410410400040c404450080400d14940f400588031560001654020302c902102d80b05294404981c00a5807080001c20824030540301c00046003507211202030650b1f9008025000f1900c255407441444500311a60901e0701c0b0346018800031580c007009842d0b6102f280c8903031074140c40302c04640c0141e080700301002007248051001841464554500381404146a0006002c0e9041c5079800156 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 525232356 1250 525231106 525231121
    0x50d0501090b030a290112032a1e0b0a0914030f041509230112200f0909160f090302030a0816060c020105191b030504150516121a010503 60
    0x900d400105e00c20038541c10b507542c445400c0e11851f020114100c00003012610190b500340c00319407210100c0d400b4031b0146400d14503996a0f080e003051040030b41071410000d441c4a034002c075161007191402400c0c042c1c00010403c22138100800003001c0303006101c800303910412540105500610403607007283c200600b11265a5a500d00841d412030940e802403078200e030380b00c044210200d622080501952026211205001d0703d100c00301050b141c10041c1902d03410040c1d01c002d40d01c0a5003800800702140810b1460345030140840001e046044c050754003020001408180c0710603550003800b211010305007818075560a03469030340082d50700d101c0c8450041c901080072403440b01c800600300500342c1e010352120041c0708e20101640c00a000b0001182d0745c402d0141c10ba2058400c6c0c40c41071003500d00f0408074020304130100d0134041c0203801500002c0c0c021100341c844204c80601042680c4034203030050f0250070304034001584102c0c0c01802c801c581128070f40254900b55640d01c240c100e880341c40c000340800382402520f1342e55451 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 525233606 1250 525232356 525232403
    0x9090307050a080904051f060509060d0e0a0308180a15021b0114100602060114060f160c051c03080c090a0608311b090606050d0501090b030a 62
    0xd000821610030008140e00304410388010b4082810151001c02c21035480300901c02400c4c1461040b4134401200d03a40c203000703007403081c4018840300401422031450b08208a03c00310844542640d6004140c03c8051113400300342e40714a00c0c0780c000101da03100b4500300458115139516400d01d03400040c07841c4d4040c02800030380503050301a50040420254030030160128901441c1c080c00c2e11001d00051041100700150f0312640d000088400e440250780182500c0c1c2c01c0c2071035002e10403103035a0060382c4003400f800212900f900a074020907001d20890450010000c03c0d240c8118150415004244a050100361018200400706551080c258142c500669a604c91119182d030500c2031509482d08480c005d80041180c41e0407030b120368092030240045100038130041294103c0022418001c2d002003082c071840402241c0c0101d000c1d40030300c00d80c0006000035641c415014048a05030f07400390b000702e900410007a5100d1594032429006100c0c1180a010352048040000d44414507040014090071940400c50081403084 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 525234856 1250 525233606 525233617
    0x321040203010f09060e0c030105090c0d0c030210050a080702150406020304020a050901080d17060f0d061e060302030c01110c0d060b03010606270819151b020111090f090903 76
    0x3100101300340c02640c00c001015100030900302c821413040b0b03c42d05240e0f00f4144100c5110301c1c0410080c2500a8640c002c00803006c80c410070582e4203014003100800540c1da00c41d8981c181224607102c0e0f40c0c0d614503001019001c000024850302c2550000f4400b4001e070340040c410359501560003000180d60750b8803880014221b0180c2e8011980095030640041580c0380002041c034103010480d2507541001103400003542501d5000c0700c03030307a03082480300c2c44017546404c05050149003e0300c00c3e400801c1512845049510594410924103a000d03101e1400f081581014090624107103004e103090003030003c070a41080d503030b0550880c600780a800710300946000d100d9198804190404024000c3c0318069440000401246103840b600c100300200600d90040002c803605000c0489181d040039000706c01c0101c051f00402c440455081d0307460b140746415041c540c01d10740306040c09296034418010340c00620210082c2150074410005081d600100044d841c5540c6882d2a90110307001150810340c160b66a045090460084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 525236106 1250 525234856 525234881
    0x170a091401031d030310090204081b030a06020c06180d1418030708010f140f0610050c0a03020a030f110a02040f091502031509150f190b0309010608032104020301 71
    0x1100c01143c030015021000b50300400018001054058584000ca001c0b07220341c5c41000100d52140394591280b14200d0680d540000c4024103440a800407601d42e08141d0744060042103440e0454010420b1030000400c1c8400b10038010f0004203000441c4460250410115210302c0b2442c1d03401082c41c503410582c820216100c010040c0035214030030740c1ca10712607001c0c1480b9045020200c0c00c100da450004100c46403400d00c10a82c1110718030007034075820b090088041071041d107003081041c10000c0c850301420400219002c20b01c80ea00034080301c500c034100140280c113190701d1641001800096120b188800140044c2140e4040f00c0c0060420072030075541d070091410320710046c00040e03203d0104040741619130107944600060a15104101044010044c401c041140c000c2651010b024003642e030b030306115515014a0034060a19108401e9808034201e030011142d000d4450f000e400020400804d10a0141c1001042020020b5040c0000700341c804074404045d07401591000c01d4000000c1c1555025080075400c24407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 525237356 1250 525236106 525236141
    0x1030504110a0b1209010209010c240c0c050d02010606020d080c0c0d05030103140a15240801020c010623060f0d05070c200f060c0703020405090a170a09140103 70
    0x7980c00380010f0341d82100044415990000000032030141040c0200c650400c2e05039105040a05199140e9181441c3c4800c8949003c0042d101420b12144c07510600300d40c6616511141c04254041c6030245c681200c0d04001411a4140f11003041040e4000920150b10010340c20310100a82c1d48034890710040c05030035031888151017803e002411302030700800214180c0340100001c040d48904072807119a1007040b1800100040400e03d05a2181c5955600c540142e4101c007200000c11901c0f403880c0144540300e60071881d00b40c4d42c0010250700b0100244240e02c01000040c011500101071031001210144059070094050b040000f0310030b0303207641c1144c11140907201e0200300b00a5403c090100428682814804640c05070f6208980c0700203080b031000d0440709100080000031360b2800d000034444a070300030f84d4280241d4400d201004c4016602e80c0511403160340c0c000020b0912102900700350b01080c5100c10b441032210010032402003031a6100f402d150684500b00203501c080034519004800401480c2200b105824 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 525238606 1250 525237356 525237359
    0x903030d23131a07020c030a0b0a180816150507020c040e03090d03030c0e0a03060e19110907090302060304061406060f04050927030307020111090f01030504110a 71
    0x70032001c00c0240300a00040300c018140d0b40c04107141c2821010301da001d00003034a4038400000341c3c20a40c03c5590301403142e105403014100e0f020042840d213190001d084030031600c86420840740c4081882071f10800046c1c1c58020b01b0001254458980c0b034819145403440d01402e21603900d050001d00803c480c10300c4d00c64007040000c1e24001100039101c0038111065441681031a00d82c12a684000098480c00d0000a106840c00139032030390241c005003410324842003844400301182d0034a1f95600c204000075401102c01084007520145080c0c202807100510703407040800b00540c41e01003444141200e4084006480030f08007519050000da074803a00f0381d8402540014008108010041190003e0340380c01130500102000303403548820030443c0e0042d40d000412801c2d050200700080d29180300440c0c1c011140300080c88140020b00f480d075600b03030140400041d49500000a001c04581d09102c1c8540122119445070b0901704581300207002203040380546030405450f00040303024007548010001058000078640340406 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 525239856 1250 525238606 525238631
    0x10c0b090a060b040509150402031f020c010606080103050a0312090602030a1a0a06051c0b0303030403210207020616051510050102010b0d0f150e010213151e050903030d 74
    0x40e030441c8011640760741400782d86001401d00e0b00805000302c0100d0b01a065800a01d1581c402101001780140d03450b2003802c602d480ea020300c00c070590215620200000da6070f24041c41c0d8031800d481d000d9006900700260300c001000415404242c81c429240e15103417540328861020050800b4143d0050301402491001007401400e0020340d014a82221780c03582240408440307101000100302007846400045032082000302c1e5141201c41e46440070708000300e000107149940102180c6076820880d400c070041491000340c42031212110003c2800c0740e80c0e02805526102003540407441600848a90074103804201d621a400c202d403d01c07212058440c0d554840244d880c1040410800345020702c9503074095413801000346003d003031080400e5002500701d00242e08040c01035030b07100c04440c00e010440104664855042c0241d100c2030005165a9a1030800b580c40c0d1424114103020740065013403c0070034420032100a4103c0103a280c2085240ba540303007400d540310b9081d030002c40c0c00e51041580c081c03409489d043c400b51a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 525241106 1250 525239856 525239863
    0x30c0403031d0a05010f0210060b070b0906070c030c2619020f030f0c160b07122f0c13020c0127170705010c17090106050d11010c0b09 59
    0x440c1d00030350320000d0088980309122225602079050580184844406000550282e00c0e02c180350401481113869a401c0038480714100c8840e1740000144c3d0000103420814400c4a40710b540d0029110400707412141001400508203c650040081c2401394500c454014040c581c4088410b1969904e41132a050f4014007085085a0104541070b2100390348600340070045100040808000740303820010345c0380240403038200005800c030030080011803103441e541841108008410f0001401101b05003a11890580350003201190709207020410454046280034042100040081c13515081c091001c9901100c40c0c20103050441014200d9042031040c019074507074050a070300600c43c0481c000020010700d09002c1c9004e902d558032112000300c80c507240c407000c8089400d81003c0781c032250444803424540411540c42c10f09544070040385901180c20088400807a5044681e00c590150b1048001c105150805000510007261680040c0c00e951845070413040c1350340078101607840c00350040341c0700c5000c1c54039079583ca54 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 525242356 1250 525241106 525241109
    0x702120328260403092702090f0315040507120b041722080114010b07120207030f05030a03200a050d060f080a17030f0708070c12170c0322080f030c04 66
    0x10103440c0000391ba40e6142c082e03604002c0402c0c2d0541c035802a51500d81004c0d410060b0059449030000661070b08541e030410552440c01c0c1440586861485c0a0500c030382843c070243c0c801940c0b410005238034400201000c0d801540968080703135121042011300c0c1c042c01240120303802e0680124004c3d070700610f28104014004215403c56009024204e80c664102040860a125010080c1428810900000c1c00520360000b81c4041b88100c0b584150b903074484240e07101005109a1f5185c00026182945036858000c0a00c01c4a02c40c4401406182541340000389200744180329080120204908000c01010340019009010000d5032490b840e4132903550320388500c09910111220b01ea580809070309403403441c00381c9101e040d540d0700c050500c0d40e0301c810545151000600080400c450b110b01a070000d1408807101011000350703511202c081c06d900500090445000d070981000307090502c01c00c00d400780e060b1085a21060b5850112504c2e07211403414100f14040c0c01d082030400c040c08000c2000301aa008041c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 525243606 1250 525242356 525242363
    0x20106031202030c1e21070507030303050a0f06060509010c1a0a050f010618060f020129040b0f0f15040315050a0c050a1e050d050c07021203282604 65
    0x800000302c80000d42c196444c40c0c0005d000e00c2e00450091042c0c0f8103410b00e140307a102a030621031882d2411664801e4281302c46608220040fa40d18400d100540c0c1d01485440d01014904604004c082e05026015005000d419000c60400102440010412000200c11840c0b0000840140703810306000149a01601c8100c41088200030740e80c0000400a01c03808480521506100507101c1c945e0500008890840d170b0300f140b100c15076407581c038030000c0d08150116045940c003082c2d00c000c0c10807900001308803e172402d005105105544804112900f691401c840c02e0007c0001c8070700218820720401d80c00d08034001c5600141c01c1d910005c00c0c40515500d1500000d11401801c0c008124000c044038056600b030007544400c0c03001840540c40000d00440e0000c030411100c1d1542400d500b010200c5007139030141c032401c4840074044007021444c80c0c21030404041c200c401160190246080401d000c02c032888210410205449940310f854a0303414850152008082c0c4404008061000510b04000b20b400880140c41c200e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 525244856 1250 525243606 525243613
    0x50a0b01080601090b0f0d060506160c0506040f1203021c0503040219061e02030904091b0605120f0705070f1412030c0a081b04030b07030510061e020106031202030c 72
    0xc490791300c030f60658000d0b02c689001d81824441086003e034815080a003150500d41d544d0350340030500380c2c3e84038041c100100d40d4540b00307690050709103003910303850407a07a00c000c9c01444248400d0201c0c40301704403201c0617124800510f00012245007022450201e864070085184032142c41030080090340080158440e9000384e4198040c2001544108150a4544540b20005013040e034448180d8101150400101c036803881100e0902604100003030880300c0c818000ca070341c000300c032400e8010740c0c11a80a4200406480c240281000d034104071020282000502c0c81d08a441e4400026003d180198150783d681078028034140904001413901070303003d42c08003451060718498800280d440801d51002c4030310038592001c0441c18028440b0302030302d0042e406480b6000100482d180c0e0290b10048401510066000d984d07403050300c2c206800054200c03071014004550310b0440460600503250001d03040c10301c00d07040150200c013110400804030300510250f00002e216545003030100032503a0340003001d4a520700d0300e002074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 525246106 1250 525244856 525244861
    0x6120108070501050307051914030a06030606080613030507260c0609010b062203150b0108010902040506040e04060e0601030302010605010f170f090a1202010606110303060d1e06050a0b0108 83
    0x644d410300003203c40c039000503010408110488021122041140b0172414182c034a05080400000c03075402c00c84640480a588110810602c0b05030300a000041203007101a02c043d040001c1c086082e00441d0001500303110000901c082040503600c1c0300782c104403a0080a4540b0308820f16126803d84c441035400320300d84a0302001c20f40d0494184a101081e50009200c2886c00e45e41001c50581c40c010602c00f1400c2442c2400300001283d6681407507816444004400520b0302c07180800940341c004181c0090090500c103100c18841c03511a0703011035065a0305c001c4042c265503901e1400c5005030140c592a84401e00542000004040c0c05400c0303c42501c8098982402c1b400c1300348401c94922910a0711391710b5a803044004078011003003042c449900034620030156010000780d6200c14142d01c800031000c40050b03548200c100121940701010710580001407000c0c5281d4101100012a10712610002030007100d1050440503e0181800032501c129a00604c18010f600e05005c40000510242400351b0114403034200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 525247356 1250 525246106 525246109
    0x9092f1201021201170a050f070e0f041a0a06170a050601120510090f08070b160f08060f0310060303030b040b030309150304031209050c0a0e070e0409060209061201080705 75
    0x3d54503035852101c4aa40b160f0702c1c2c0001c0702c941085a907034241c828000c2c54094800702d0018010040c20040910041401030300d04810064100f60040002d59401800b030140400100380390b40c2604610603140d03840b03200d9160581c03203600501027a445010580340c6a00320800340100030480f641d186002d023042d114142e0b40c46414108041c41c0100003403084d040840d17000c0e8261400d510440060740510070144228400707541d0704400d40d02080040d01c503040004108010b46001009620101d8103a2400d41c13004031030440c1c042c000500192055208070905507045ca00d40e00c007000040e2440300607840a11002e40e4900307018008001da0340000b801682003101c0d41d5103900300003088400d0008040d094000e041c0c00c0914a03401c1d40c001600841c10025075602855402c00d44d4003072410828000d030050000030041000708403a511095015035406107010040003109504100040a4034000351008203d504241c41c01c54024030401021340e502540201c0e60481a440c0c6410703c80c10ba8415004403000c4680303410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 525248606 1250 525247356 525247361
    0x5040c171b06090d0f0503130e010e090c010f0c0215040b04062d050d0207060f331403120d0c021501080d031109040905010e190c09092f1201 62
    0x1090035000036800801303400040303c0c54415900346000390700b43c03410b04540e407215143c8a111584140d030354031445401444082040500c198101c1d903484000d1003011101400038007010300c4201e4540c1401080d02c02d902c15915002034455030680f071100250744d900d131034030b101150f1a0007500030100061040c0c904140300307401c4000b00302ca0403401e6802c0c15154080f141c0301280e1a0f4080303101022929021b0001100081d004d004881c01c40f204c00501049003240c406080e810001815400d1001150711f11410841d0315841c1100d000392015800714603100e0034188046864a2042d40c003c1c030f0460800035203079640b2007140d841031014180c980d00703480c80000109600e0380e0404007800307520f207a50802d440485459010303074002400f400815402604112002c00000c013140c40124080d038899446000d032845501061052405585030315a409111907625100c14008907480e024131414196250f20303000038001c5002000c014088941c0d60b840700d011070311040b0707012802c0d0165031500a160fa0030701202c1071383c41030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 525249856 1250 525248606 525248617
    0x206071208091e060a150b0f030106030b180a0c0507020d11010e030d090b07060b04050703091e030c06090f14150f06060d09080f1305092805040c171b06 67
    0x90f00501c2c0c00d840d1192074000038407044a48140c103610524000842d1003000000d08404182100d038243c0f00d42c500003001e801e441860180d50711035480c03d40480b00d400d82d41010b080d0400c4c428072001070700b03680240d000c2d1420301c10980060b40c0080340010110030003122030074041788440e080c0d0390111840000003c1c19903c010743c60b003000221300d0104050002c0910400030b040701350f00034200492201590707000f0900b10380003503c0500010340c0383c3c20701c4824400484200314041e481400035030b4105003d9200101041c0282a00915064a0798203190034040502c0c1d0444445400101c102042c0c011101c05954075000903a5862841c0d15000001d0110341c18800c04520841000d8400351400da402c1fa001c000070080e4034411a4014018044503401000360809060021840076507804024102410480d030520018035080d0307001c0b011060b007410203c0000002d0b011880117200400c01c1e840d1458129040242908944000150001182d0a003100050780e2407030a64000144103904043e4030a111152184 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 525251106 1250 525249856 525249913
    0x14041a06060d111b0c041b021209150a020607020606010c0b0402010f0c05070b071e02010c1716030e040f0c2f030403080a0207090b010c0f020607120809 67
    0x1403040071089040c58000070f00b0704185011041c5806844a01078000f030003c0443c1191a40c041a0800a030f802c0c00c0c8030f6413918035a52030700c1c0404070006100c025a01c080303203441c4050032040816000841d131500c600c901c5012540003181621561800c400035592001102c40100521480011400300e500a4203180c9034142c000700148501d035169001500c0628001031800c0130455a01c166401140f000e21034900901081850a50391b0811814403806010700c0fa01480e406821101c010300040c0c0e00078821110450b8400002c2e0f00762201031580c0c0f8600d000e0807124000180110590070304165215041c2c0240036000c580810624160721428000c49004042d9900450f8500c20701302c0c0c4507001d442d0503103028902c1e81c1c50820030f1054100c2060031508280e0003107518807000702d0b1100b2150f40500c60a40502965001003050614000000344a4501400c0241c03605122148090541d00e500782154a0103030446c4aa000e100072200c0c00511128007103903418801d00600405480444481c02c1c01800180d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 525252356 1250 525251106 525251119
    0x60314250806010c020a06110d030e0c0904080f04031506090c020a060218121c051201030623070c0b0907031703071b030801150906020a060c1214041a06 67
    0x4190015940c064000c0c0c0400e0600c4012158940160f58442e000c201600081e521221440956034a580c0f078030020340a00002e00d414101521607504bc009001141a40c0448070140c05442c1e908101056110714000341d518414001004018400b0406841c04d130611100c80400500d0b0b078860741441140c00c07440341d220050f0440d00c03040340424945d0300a0610325030032030405041002c8020010b8070f040300007100b024654100d42240e42c416407810f601041142050305100d880c2c04003880b014080c0368030500009020680c0c1c0e09005010381900002c1c0d82d860000c0c4401300e001410218005080c07482c0d440c6044808449040008000450100300c0e8000c40780d100000502d96441c1090490068000a02003403c100890f0ba000000d00e01d503103014541d01d030003500c0d901c00d5941880c94590a80e00034249950030301c90a01400c01c4242c0d40040c00c3c50b500740d0040c0c000038100960260440320000ca00748109602401d200b002101c2e55901060f00d4020303880b48503118030007c1c00070703481c6c640989d088078055030084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 525253606 1250 525252356 525252421
    0x40b03060f0604080a05011d0d08010b030c1b030702190506120402130504081206010207060507061a030102040603021201052b050c09070c050c030609030a03020903011104060314 78
    0x5040040c54803004005000710f00b004c2e101c1e05031034505500c0040c140c0c1c05039141d111101140c0100030410446030700c5ca074040c040e405410900a400c1d50410302c580707048001c0000c00180098614810385414441d0140004a0a01c0c040c5200381d4a80000c2c100303a01c200d03030740003114442c4240721b0302c08412500301500c1581000406111000483c10003882030b40c0010b4148480d000301c031080c0c03241900c901d10444045481701c506910783c240e1082d008151505560200c17406126040c1c21106032850716901071000b1486c201d0a1260f64a008181000780342c041d070003c20302007030b03268168001d441c015100f0004900113a0ba240104160031010b1603a402c062140e000d092070a8901001150814a0042044940f0303841c0100100f07116800484403200001c035881d0380042005014404004003401c00c800800060a055616540760700c03801a01d5014141e002983c0426610300303421503100300c02c01000540e120781d542c1c01c2c00350180c11500070042014100d000002c001c81400e45075115070103c800303207170110700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 525254856 1250 525253606 525253609
    0xa0501060e090d111b01020c0a060f140909190212040b0115031503030e030304150815240a0201060e0c03090705061c020d0605190f0603020a02030910090512010c020d0302040b0306 79
    0x3031740e0300654581180103200942c2c0281e19203d03c50001400a40d40341036aa500a29004100f0800b01250311201002003110000d281d40e080c0d40707180c0004008900340464080d10100c2c100a12411007440741c0f030200781c4100428050020215412110900407280b40203040032011811541d920a400b442c0d031030342200520100344070300400c1040100c0901141d02e03080d12400035082d00702c5130700b80d590300064a50040109100d10242c2c421148a82030381c0201d00551061070310a1661440249001003100125005080e680f00750000f40c01440b49441c0c18807076040a402c1d402c803d5008880b400068828008006004d080200403610910064034204c65101c0c45c0090a10180d8031114404038820384070000071540381c0d149080545807410848690b0b40c602e2034948001d98906140e0b11003801c0c148144240c290058002c012107000c5001100c1c036611045207268103a594520a402064100d4000c1c85a0001044150b01a040484031074086424110a42c1e208400b40e101e036014000b00c280c4244081540f5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 525256106 1250 525254856 525254893
    0x70305150603030408030d0b040c050c15060616032610030f050c1314060105031509040611031303030e0d09060e0102011d031c0612080c0a0501060e090d11 68
    0x1e500141a0307407405580d040400c0c40c54002210011817566a400d00020300c1c0b0b444d102d01c10000403a428036a00384070705001c552f40c40b040c0d000d91102c900300380d2200140031b0342c0c1c031181141c000a860b03002007168070495083c007d100304006910042550215400500129a1926040c0c8280c4450000c40589419941d40d9625400d0840040b04c151040c1c402d90110350fa11604040300807159070100044607000d001d44826907000241046051210410074015500400300c1c44201007101a90301030b80c15211031900e13400401480c401d21032004400b00a200c44490003502100c01d1034001d5038184104030004105903180d101408039000800c0d41c101e41008814040d0904699086050000080c41e4040c007a4004c10704140304402c0d2a245c1002400105011052200c2840c5000802d000c205240c1005a4a68511442134020340600c0300801c084154003001c10444001a034007070000d108080d924804000e51020945c2c105129000301101032540920030610543c030f80421200610760340c5141c0968003030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 525257356 1250 525256106 525256111
    0xd030507060e0105042f131e0207060b0a0f0806070c03022e0c030614060c0304211202010e060105010e061315080612100f09061d010c0207030515 64
    0x15402c0d02c9032101c0360a00020b00c6a140f065001e02d440d14244081c0781c002c03103601d683c2034503a500d0103400400200203503212101154051644210005102d01d101250105800c4205ca5440549800011000104580c641060064040a540c1d4a01c2141c40300d00d40c2d001d1904d24040c604d070725884100000c8003e48076422940c49940640162480c070400c041c91091000ca0314070b00c0c0742282000c51110303215011a8410245502c056180c00c015560402c0c2000b403e12000f005c00e244550004120414408810300c2280c00429000e80c1034030300b00c01b4840c0c10040d0200146030aa82d650b025520040d8130034010f000d40001940010302900b0b080c3e013810015a408295090416001801805480b55000406075104003a0130b104c2d02c58804c180c240900242184001452a402042000b2039086420700c0080c0b000c400070300310207001c5404c4031205950380040442c0315000d42001e04015220340d0f00d1815810100b0b2840f1743c54000e00030191131040503070342c1d94503d200051595015481c412620290500c00ea034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 525258606 1250 525257356 525257363
    0xf15040618050a200d0804090e03190e010206060a03231f020408070b07050a0b06190902090907080907091a0402040305160f0303090608041401111b07050d030507 71
    0x2010400c140c4615142c00854401111058040744410551041c0b0341c0ca0100c4e40c2404a071121101e550740d07030741c41040b4066031103160b0340103440c1c030846044100c2c2801502c01d50501c006031540718085044d0001c2c10102442145030140c081d1300042030240c1400891101135070341040781178039a03c5902c0030b1030141c070070b2380c0c1e0380d080042c001c11003000c1c42010524800e0400784103011000d40c566080221032401d051103644094294101080100c000403c0802c228003500c0d0419650901c0ba91a5004030f6901040f440c1d11440c251882c3c41c0c080f5004c0c08c2603000d4000031100307030b4100d070803542c4a58080e900d00c6d2098031007c40e0355210b1b41041207100a00c0d04002d04403c9010303800700340d00304078201180c1680c01640086481d5041506007100700490108114000d245040300320601c58134680f406040d0070064011201000782d4100064240280259209101034a220007003100001d0840303002d0498001d14514201c07101c6910304500030980004009083c4c4034014201c102c0f46405550a43d5541e000390000c070b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 525259856 1250 525258606 525258641
    0xe0f040603060c030905060a060e0718030c120b0709050a090b01020304030c03050a03120c080403030504020102150a0c0201180507050603060a09061404180c030809150c0f0f150406 79
    0x1c80020594020034440c811944c6001c2006a4180f5041c3c0c204000182a100c07c0c43c98040304200300b85e940380000d500402541840d203403904000703590204d10007461f00080d040c0140c141d80010726801c0c04114a0f051f0307000d5020700c01603884011084030555414401e8640c05040b910003030044001613030010700000d8050040307a180c25540c1e51054111841907006480c00d401c00040c100515400100c01c04020354015000c02c420b4030340100c050180280904040c04056039200010116402000101c0303c0044c1e080c0351849c40d160012400003d0030f14851103e0065080c060381114074082c200d41075010175480700180c81c466040105101d6282c0000304040d80c000032043c400200c4800903c201c0d00544602d0a4180a2a91000c20301059841802c172a2000d0700803081100d0104400456284c141d03580051b00c9030341e07144032100080c0c0c0c00f50f01502c549001a0002038802a11800007503040002400f84151040021f40001441d00d0b404c1c004000b0400100d40400500090200d07404807a1080032003400c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 525261106 1250 525259856 525259859
    0xf030e07080604120305010812030f191b030e0307020112180f050303011406191d180412030e060c0c010204090e150a0501060e060c1507051b030a0e0f0406 68
    0x201c516010707080c0d90544c0c2ca481507408608030316916015280c00340140d40b0080622860809494100e8030008094101c070301c210601040207400358100d407045500c6503c1c1c080c840c110b0b041301807a1490a1440c107001c0802c0c070b070403000b610b084030100565114a80584441040407130000d0414003074050002c15558100d0004a5074001410104507800b0340e41c001d1000311780b04e60421600342c5e01500c0f0302c7c0d20300d48244414007500c030111621154481c604415882c14060b0ba044060f1031007411041442e44a80c082640d055030921b400c1121000d030b200307070f01078a152007844416207020707000c48a0340301145c038a9401c4000056454200000144548254100011f141540d1000c0020440380c420102c0d03001c0b40c00843d011400c881003058020f41010042208010300e5140850140203040d0242c805c80c0a41004111644074000c180036108541d5403035158802c60303103030032000108154440406000d603101c40d580d82c48442500001a280000b001d615400f22940ca80000c116880c0b0010142a60003a10f8400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 525262356 1250 525261106 525261119
    0x17090a0c08030301030c0803040308070201050a090b0f0c070902031003020d14072d0e010612060302090c0403031b1121010e01020307090e0f0705090a121b05040c0f030e07 75
    0xd900c010040040695140d50444c58240041141a032051110390700030301c400c6c40460003400807103402d160709003000b075a110007007141035440c03541507406010b0800e03001c10810076101c01b40c0000c0c0340045a400644d8640ca0300c03100203001720301040d180392000e51031204042c030040c00c15071004080319014003410810a065100d40e0b40c60a039080e003100342300803103e404900b030f403600000800d072500d00140384154241c1d042c1a0070000750001440784208220326105010030800c000d80c03107200690380140c80380410703203130609908005034002e01c000c900007049602c2501071040720300c0003070314843c3c0e011501c41d96220244041142c0142e00e014042c0001c0d684040400300b00d4001d1081c602121282d100241e01e92414604c007501071180c42d408181202491002c002e051416141210391140107420800d17218182034000c02e1040314203070004580800300c00c01c0c140910031940f0550200002146015651944a4003031000351030313600c1c1d1944082072035007009440c80da0103908100c0e9032154a0040740c0d9190354804 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 525263606 1250 525262356 525262373
    0xb2403040813171c05030402220608030d09030207050a0e01031115030a060315110313031403100f1406030f041e26031006050906120109020310080d17090a 68
    0x3c580d8011640104144d25400009a040d4001c05a803400c01d5801e40c601600403903050360808040a5a014240301e1460b1442c25503440480600b4580003100e4846492824507001000000e500340d0251003010400030302c5140c103540e09000d90b15820811481139181d50355040e1480506101242e121103010307054001613404030f01039481500f6a40c0040744461440c10f01c002c06d200000c250f07010b014188a10701c2d4100b09010201c0c2d404c009044401028883c150508071f400681c0c48988684003000081408201581c2d00900400e9903c011608000329940e1000700b02044481d4030403607005203013803000410480d0021155980140503045620001421291042808910013800c503802000104040c1d180f80701c0480080021030b9100070b207840e600781011100b541c421113115407401c000b000240541c1030780b550820340d1400500c00188200365619049100043c0d042216034000030800c02c100055a088001102103017240a91640c0e03d50038a40810020171a50050480790903125841c01140020f0301c08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 525264856 1250 525263606 525263639
    0x7180f09050a020906090601020304031e050d050301090e0a0b040b1b030a1a030c011b03180f0503010b01020703030912061b0206040b07020c010e091504050103060b2403040813 77
    0x901c0030b01150320030361041100b840e03c05009a405000d55070b04101e65642c00104440a90742c00c650507030214410758048030780b50b4510b040c00800354058001000c114980140103141a0b0302c6210041c03011400d01c0c001c450303481603400c0c400380141c071500d40440c0104005031103890300040340313003070010340d258440e400c8a0743e82c0c0c400e03134080d0071a0365035039101a00125010a051584401200504010700381040002c040003c102022082c0b0300d0000404010103000391440814811400000c00005945002048600d0010300c1011b00075401c0c001c00c0c04d01503101113940c0f803e59506444001a20742021841000c000ca8403d0848075907603101c1c061840c124051411540025150b4020a12441d1501e0400309199014180c0c0c1c0555104143e0041d080c4c0e042003003018208016030350b985013541d44498042c03896280020300f5030003034a840004003c1c080d03280c000a00006c0140c503c04103401c0c0c00c2140000b040c2e907180c3c040021752418004100020320000c02083c3c0900880340d034420079900d403822094a501034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 525266106 1250 525264856 525264863
    0x71202100c05041d060d062408011e0203070906080912070f030e0a240516050a050f0c010e040f06151107090606020c010e04110430020307180f09 64
    0xc24108007912151384402000d03c0182c44884042c2054800b0070400038040030010080303911000050000700d1100070f0b40c0c032081002c4500740c0364680c2d40c4a450780240980c0b07400c444982e9958901583c5003200303008990244855a071110112854200201c400c1e26001e02440c216010351050000c412038010081e05885e400f481c00c90140100e00d150140c989801e50030403a00079900080308000981180d001501001c03903c20b04264406944031044a0318401d69108080d615020a0f4010a2040000f000400c49129404492480b403a080210b1390b1000040e4609000a50303543d108002401c00780c104003480740300c941340424108d485a8601d004044c0d60102880025640400013044413001c208400050094800400529041901c025152080b2803803003814440b00c0100c01d0080c2e1207540c070002c00c502c095905c40383c80355120502080c091181410720b0441d46810381ea01940e41c07020041d40401d050380100200b02003881d240111002d03021020800b40b10310b03601d50308540610040d010300070000340b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 525267356 1250 525266106 525266117
    0x40c140c01150f05030a031206092306060c0c0d050f010e0d020106050d0b0a1505061801080a0b010c12020312011401170403050318101b08010b070305071202100c 71
    0x440314141e48100c0c0d03c40904840da140c01000396803070100b0410b88203a090b02d4100c0d481800c10702c0401c0544600d501c00101249030500041c043c0620360400008203a02c030400c2c080c50b4850108001c450700401c1d01c02c0000d600801c000010b00e141400e064490540310340181c4090401c0d04080c2800c640b84d480340f100c0241c002e1135034401e2265081c07045402904040307402e00f40038074031501e80e144084e60092809040558804611841903c1c804828005200c001c101e2a5104140f00e1008014208908160b02040f00100400c000240e00c0c043d00c40ca241040c0d40750f0349200043e444a80c009040c140040065000c108a1651070070b07004104075010b051203844903003100c05000300041c02c800000740d0104101184a05010000e58003404507038220041b45000745203030002031002401e00311041c5201032100d1070010a01c00c29601ca9041c9800365165031210022a07a030345100242621132000001e0002c2c1c010032022001910048607017066451610449800e9000b410616048501703250440d00440d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 525268606 1250 525267356 525267371
    0x2a010b030d02070b0406030519050106031a180703050402130501062114010b0a18030b0604060f080a06020a0e030d0207031b0503030f07050102130e040302010b100e040c140c01 77
    0x508104400da0703510948020b04407140744c107402402c24020303409003e08050712a404a107208000002800001141d48000c0109594a140240040004458001600072800d02e001560700d0004102590a1000e1071600720f651f0301c1c10303c02c5008200081c400ca80c02010305110010b4410580700c2c081c0603080e03a03200c0200c0002c60f91003038071045c241c0038515030441d400e10103580f0342a00540800782c111100c81420b80d40740d02052100752a039030791110803201603003500240001070151034601700d07006401c02d4900f0002184c580070310407084102401000c41c242d1003140303407800150303050f4000c0100341c41e1490a6a41d40d0800000a07080c000d01c0e511041c01030b030200d0707814418017007000032608030b0444c0c200700254001e282a020135280d009186c580a640c201c045481420300c0300c2901214603454045450341c40f0180c40d155550f08003601a50103500644c0b0303003081c40303c080c03c001101c0003040d41203844410202c004803042001508e40400d4240c1000f0413041c07041c18108200d00540904c504600002c588031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 525269856 1250 525268606 525268609
    0x3071704080403031b021008040309090e071403151305011805010e0c0307181505060a020708060a02030f010512150c2104080703080a180809010f090b030c2a010b 71
    0x71710000d104162241400c03819000141e50748181d00401e00c6203420071617055510390400359074000d0140e000300e89450400c0c03021030306008041544c0c0c0c06d9a07044419400010909010305070f580d0a5851411034405070070010a900000c507010285c2294440c1c00041184040000000440426440100c403140e45880500c54011020700274218010000d030010720f00070b0314158031903180c0e40d00c0ca5101a0515958000c044c0b01c241d0090484028040c054003880d42d0785a0f50300020b5491146109500160140c400810b035140110b0003180d02808410f000c0450a03428942041074480218150303820500c40e41d181d4150ba0300010031141e1041c00241007081d2619583c8041264004031911907050010001c01004006401c1d2003d40703c0c0c0542501e45030140c0d42c0c5805031907004000904a501180c03814440603800c02c4070350002440b01c0780c030a0303848625640c1c54040c00c1c0c1c0c400084d40a0040b49540a0001440d602d01c0c078030182031525a00681001500405003040c40c40c4401d10031050903c0c0d444010700c1c0c130765 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 525271106 1250 525269856 525269867
    0xc03010623070308010617040308060402090d0c0305030307080903032502100c1107060921020321030403140c0d0e0102100e07060908030c06041b05030f060106030501050103020c0c060307170408040303 88
    0x30140387c0c0020720961405640040a050000b44642c0c81703241c0c08151422151a03907813950701081c1d84000300c0003010362a814116903e0b00100c41080c001038110380003885400c1c012017030360b0103900c2d8614002c6540c40e42c00480c2c041402640516070440c0304004e40d07083d00418600500424000d962960030140071b0f01d00c1c10508168640d0408401c0c40f0401400b00300440b0074490011103904452403126080d14144002070501c100304d188a80001e042c519030042d08200c1070015401540320b40c46081000c918955005168040c40548107555080070641515560181c408031014500501c144c5402401c561542c05c12071755140f50f980c0c4254007006040c00a0b540148000c0080c162600c0118100140c3c51146a034440d00104010004124400c0100104244079440c0303000d001c0c0201640c0707101d440d103140d0a640d58400d214100c00681071400005144d4060f2003110264070250014244812072203041c07084030792000c1e000a042001071004003032071b03c2c000c01c4501d00461080e000c040d510f5281d810700030b24 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 525272356 1250 525271106 525271127
    0x7050409051209040204170105091504050a020d150903020106030510090206041e0b030925060c0b0910320c070609060b060309010915050c030106230703080106 70
    0x91031906030000042840001d2210000d6000b5400c55658090349000c9000390007143c1c00200710424070040404000c2040d08018070509415044035800d405070001301c4486013003610040c0168001410300000f6045c04010800c509004642c44136101402d401d803401183c40d0380c101500181d5480b4814010041e0611100e10714854200c8107000c4464580c00084680c46035208819104485c2c515800014907001c20020083c0070b0700c8291910b034034041036240e495601250308644001b14426002400546980198080da004c40e542c80404d550269580c100e030100c0079000701441e124030700c201848090b00740203102c03024104030b82448800c914242c00d20380300d185070210042d40f48000c0e0300b00000a42240c09949001303400c0b80c401304440c6064107180000f002c4410f40c094200b04000f040010f52340303054010a2000b071003560005980c984801902040b100159202c0c9500c00081004200701071280303440003503003a082d0001c0c4e580bc40f00d00040000d42d9121f850110045040c00d00104280c03900001c1119 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 525273606 1250 525272356 525272359
    0x3020f0c060f07052802090f01150e04060e09030c0d0e010f14220f051504090902121b0a060c03080f1008190203060619030305030402180a06080705 65
    0x192101240e0008140d0701030040c40601c0a00d0209825090100c10015404c40e16891440311700e5188180700c99012120805005a00601303542000ca0a0302c24403400b000e0481d807801150061810700031008841c604910321070168450346803040403450485410300d0300e0081881c440110354545810701903e0500341e03600d90707070020722000d15503a0a0380d0740c0017411008145440e10f402c520050041440351840c2c0110308440451260503060040581c500c0b94100040c0e5251403140e24440f555607040140d44501a900004224800d000401c88a6a15040350043d284001c02c0c032888071480982184c600401030602a8590200f02800110740c2810105100607100c10b180000d4888141c1e02c01a040240140801c800096010000707000300c90b174030b501c1e18050310301076003a00c5a404420705005207611b554101a4400d00956010170380ac1d00d131a01c0040c414503203400c030100081c0c0c80e64030141d036660001801a07800205480226107114150b4100f00d11074a0040030005007203051001041c074003074868200a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 525274856 1250 525273606 525273613
    0x90c0b0703110703080d020d020f0a0f12061202090606120c0a0f080405300a05030114040605030a141009050a0b0a110927010b120f0105060409020d0b0a0f0303020f 72
    0x3800400d2907070044601146c494140565a0300d82106140024440e0b9007441c4512100802c580c121594000d449000310035040d0f680a440d03085900e1001c0840e002441510807024201c1141001403d00c060545e51204004010900784003e2030002e0390050b038100c03500318080d88001035007140c1940085c0d4030b8084404e94a0040300501d8503541c3c1c1a41c80043d410f00e04650843d00030650344d000907645001c80080070880642d0345849003401c01400301d4101b800740000c1c01400799100005401c191142d081103640040c002c20300072105894140701d510540003d041d0074020313521104600180b83c0203100c0713240d125000800018855090501020502a1248a12a007001100004800c1071b60aa5070003035030849116500508011290380a056004181421440759100004001d54000b024102580814690200541c0d5080244411603c24060340780d2090051209000191040e409030401d050280c40000b0304990704d400142d003046403580080400c140300201401010390600540411144145c0107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 525276106 1250 525274856 525274859
    0x51c0b0c070b041b0b391e12040f060e0924010903060507050301080d090503060115121505100305090c1002120a03020304020a05090f010b0d090c0b07031107 69
    0x5081c003400380039101512081036407100340201c0100102c0031004106180c0300d50360b9140240281110081c4110704403011074240740b9801c03d03107150226040c401c21b00c0b1001412045200d115881e4060b4503143e5548840e205086040c141d503805032000300080d00001a0360503045203000c00c020030a42c4008550340c0160650300c103100d070844192541091445400445035810701c142c40c0100c0d814441640b0141c5000c0c100800d125800b5001001541625007401c00d9491041e80c1d21019140c040c62441043e0f00b690020004000100804d41d50351100d20192070001c2080030380205003401d4801238030395100d40210031031b070410552030a10410f0030b054100342004d110510b40040c072103440f00f1098210501400c006610680841c0c400c0c807210451410040c400c0c1e8079203a5003030005001350402c0310102e01880384074001058901e09110020f00c1135075a0301d803040b900c2e03017040545045508100761400c850b54a0f5036080001494800700c0401070035603400100d0715581541001062340070301d02240c0700207400c01c080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 525277356 1250 525276106 525276113
    0x6060801140a05092514030d0503010303182606060111030403021003110706050f0f010e06150903150f1302060304030309030c0210021e1f0e07051c0b0c07 68
    0x340d9078001c604860000f410b581d8404071600301118900010258600c004c507900c11a0b0404030080c0c2074032401008041150080d07001c1c1036443c600540d100300802c00c00c0c001000082d10801c0c0900025441d9841024015510b410b00f980d580c03002d11030640001c000d4540d184055004100d29a8002c5091900100304200d81100b01c0d01e03442980000303406103002507128801c640c0a034201c5001000e010511654503070143c28248000e0105880e01c10404821300e01107000d042130f0341c0c030311410381e41c401c2c111a0040c0c40d94410081121030f648031140310f4050510404405a800380040c00a0008440d00e0400d10310f0702c40e00319005080c008003c002e9a4070528800c0015841d0181560361140d810b050004250a0320b003070645e010b854510b0000c1d44915840044d0704070b03550115031507d0550020041c19000c40820040715159a03440c519100010b02d0b10307a482d21041580c0e00410100030f00601614040e9803103102040c1641c3d40c2107641d10503140700c0d50b0040100f102c07040009074031074407032203000381000301565 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 525278606 1250 525277356 525277391
    0x7050f120315060d023717010e10080610050a120525091509050702012702060705030a0f0f0504030305090103050a0209031e19050c0d0302030d110706060801 69
    0x514841c0680741c045104c10000d94241c0c1150070607103100c81440c20000d040e48030601c0c24500c2ea8002c1c4900b004042c41d003040e076401841d096040c10000402110280e003000b403403096130003000744503404003100900b00041041d01032100d240034103074941c03807007905501f854180b01860455034807000d01942c42d131050401086000c01c4101c4000400700352030511800700c100640f0940d00f60b80200c12610300c1c0c103682d140781d84900f0b03210004482c0c80d9007040c00031340d48102040c0c1c2280c990000c01c90740416030604041c81c1001c41140f401102d840148000d0800005449aa01e190041d0490401188211601c44001a0031241c050055062440c2051401d030440d41c00421324004d12401c5410f06840300081005001030340c0580e03003810f4010701110035003500d5a081103e05070318010019114080d00c0c440301035010b8a8052040d4058020000f8052001c1680600104114950003a002c40c0801c1c0000c50394503c0c40d0003511030318084211520748031513480c24590112802d9503c1003625a06d012030319000c900610 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 525279856 1250 525278606 525278641
    0x80307080a050c1005070305150f040b03031312111f120905030706062603030c090d050a05030c100e0d030b040609060315060b25051207050f1203 64
    0x30500303500c440c080c01d000e0301c8601519221420700c0c09403805110003480b07254491071041e0b4843d541400700d07403603002d46844076a4410401c2501320140300e2202e031442c02c1035009041224005411030703180c1b0441841402c0140391680102c05541a50706508080c0100d040c81c10010b014115401c80080c9440c8415a050300394006040040c0805a4140340d070000309075200000a6070020b0503699034400c64902200104014015a44482c8502c032020300f480e5800b07005110060b5070708000790b00c0c645510340ba548150304084c041545c444c03480c03070f201c2000440900c40040350a00c607000558903003000140b9207003010700f8402c450700000c0c0703891a9480c55003400540d4810504541c100054115080790200300504410342048481e50b040c500000100a454180c1c401400c00c0e075030040081c96191505006144100040014080f4507805200c3d411681205140c0145120307800b29190442d45c0503a6103c107810108007540d140d00410401e0481d00c0c01800300c12019400380d62000d00e186815120b110150005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 525281106 1250 525279856 525279863
    0x36060c031c020306281511060901110a1b0507061e05120f0403030e0313050414060a05011809050109090b06092203031107060209180709181805060a110301080307 71
    0x700300d8040c40c810f00c2c3c2d044180151000c2c14486d810f00010900140040c04950b01e01d4009200750740014040c880103110f11041c41a92008042c64030f46d04250403100c803607450319510154100e0359143c10010344208100d800500c581d1f04d50300010b1051920a803c01d040c141c5056060207401c010603050065070a1503664001346001d200308142d1280d04003240180b071a01c000c2840c03480000713659600f0803503500e02c03101280c3d400c4505202203880d0150505050303505945c0c0c0398103c030048505102640c0110b0903541c1c6040816a00c4c1c039070554500c420f07001e03114285d0000210503910310b030543c20b0000440d552a0f001c0b90076905c007452030034240c003600ac40d440648280f4040c181c0081e40d41e030425209030070800210100d4075643d07403582801d08011307000398400304101d845600e4581601000740e40d6640d120784146003039250140c0c12441c11426001d5400c3c920b00140046a0390900c0000c44210304851380403c1d401500280014908000d20b40200c0d9110004c0d024001c1003800100f184031303000011a01440d50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 525282356 1250 525281106 525281149
    0x70b09030723280803071e0311070906050a05090f0f100801051602061008031801090e040b1614031302030a051e0601050636060c031c020306 62
    0x100d01c008100c0b107541c0c0401c960f90103656a0b02c003258000c0c460300c50300a18a109000803d18540d12090300f9680e1158420040c0410441d0210810706210b400b81120300c0c50280c105808011700d8003041a050401e141c020500542c1d8413034082c00541402141306016000c03d441c3c070b071140c0c00d045041c0028041d0060004140300202c070000f94141c4012076540c1d0007002c0f20302c024032003418070035003020341a840320181700010300c14400010074038111401001c0480c2e018130702542c42c0c80a50b05c064411202e0300f503504c605100070410006400003182100030b00c1a0b005094041c0c05040c5a40d540310400106c0054404100c1080101d0310034a03850030031241c012900590129045000b0310200c0c1c01c100281001405901131502d0540344c0f64401300c000d800008000043d10010307030b02e5804210890140d0641c520341002d120411841c140640c0e5009000001d4541c00e0382c0010800741c1c00982c079070303006410303000d00c0b6080442c5040081001d0180303840300c90342c49881035003546042d8012071040080c0e403528200000d07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 525283606 1250 525282356 525282389
    0x11090406020405030d020304030b0906010609030b0702070312020105060f030c06040501050309010603060212070e01140f030a0e16030b0108010c080408160204020a080121020120012a02070b090307 86
    0x4590760480d0020107001c0d0544150315008503002e9207070780041c803041e5860803000c40000c040c60004030300f59060314010344500c6491800c50322002682a0001d082d001076102e00359000c00440c2d40040c1c1050340a85940c004100351030603600b80881030181e2040f040c020742c081c00b800c1016a644070161001e0700c0c0c080c0b900c251a640c50403440c1d405010264005811181b0000c0c500455103000c048141c416003c54852824890b2801d004685a4140d0340040c620104240b1000d03030407080e99001582c03c00c22124011550500b004d4030541019100900c0030170b00e0ba4401d0042080000d40155140181034540003000112100c203000344c030448000708020600c100001d1200010051401d481e007003190054011502d90250680145c8800000e028102d0100c041003040c000e82020710500d18403507581a9100703a00c2c41c54030310682c41e680300120301801c41c0d55203510f10100300f480c4003c01e00040b0188003141401c1c0da1015803000c2e04000940c0c01071030f8021020001c1c9142031304c0c005801c00845001e24200700c0e004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 525284856 1250 525283606 525283613
    0x2223010306080d2d0215010e06060403120c23012d020c0a0b0a09110405190b03010b090a05010e181b18040605040b340e0d060507020118110904 63
    0x310910398a4140f0713240c0c1d0f41c0304590403603000030300080d1040c2640040c05582d80341e0005000001d82124481d500c8103003008140001070031402080c54010740c500740f620208103c2e036202102e1004101d01003103010015008804003131024024203100241408030200d0003240c2000d07981c8001c040003e00c1c96060340015483c22096801c018a03d665034214204a81d035003400072031034020b01651142511260031001e03564100b0305e0301d4450107005004500f1482c3c10b00c0714011001e400351a00d00c03001e5915542c0c03000c0787c0c0d040e80c54107c4081c0c813a41a49000080c20f60400110a00d400405401d282a101300102198200340000403044040e05206804809406100f400680c2400710301c040b42d01440c0342d29050004001c01500450b006522881d11012035660304800d40f8603200d080da1442a42c2d01400d00c844000041c801008120800989000c103804280c160100c2c0004089110494040307544404001c50258280301d1030214500410002c81741c4040ba40b04d203403c0200080c00544106070400228041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 525286106 1250 525284856 525284897
    0x180f03070b0408030409110f0a18081002190f05031f0506040b0703030f1a060c07031e171c0f0f06080a020901090b152223010306080d 59
    0x400c0c5007604141d840b40c6034400d09860b40c2045c4105200702c2d060040003600d08a065058804007030000400900b015804042102c1852200d01f21040c0003c0144010074480780030300141c1282c800e424005a030319010342100780c1884d95007400540800c040680324040496200c8100c1b80c020354810b10340300f003000185010802c1350349603a2006521480000b4005101281c0070041d14895000b510100840903562302828192610303102244000d050a034401c81e29072070b10b00c0151452500b450211050075460303a45030502d400d14014004038050b103e2100e041040482086046013144140d100e41c10700510000b80c800c2016910310401106845405099940c2d00d40d9120341040404508144115a60f440c00c103616160001d00a0740210032000011882d81e8640c09503820362079000d0f0000e409000c4e406158a000d4015448928082002c5045241040d0072960f0340005461806008080015041607038003500380e450410505142c10300b01c0401c94600e021509454580d06030a004c5040b40814560780d40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 525287356 1250 525286106 525286109
    0x20102090409030f111b04020d090204020a03050412030216060902030a052a030c0f04110f040b03010e01140d030806030709050408040e0117070b0a051209061902180f0307 75
    0x70000c0c5010007940500d58000641074108103035444004211141c0e00e015900e409101c2e80c0d05441c1d000080070b211042c01d00754010409001e0424000600500b40e40c0001c0c20385c0c0c0400421400039171110148018803410899200e004845400c003141b03480c44400820504400e40c150150249650b45130b580195103051100244070350b4804c05960b110503200c211107160070107880f4180070b8119100318090340350170300040013101540002c0429000140e190204009070000e841c906e1b14449050201c4000d60b503400c0b01400c00341040300c00300d51302c0751b04008845042e150141d2103020b4031410700c5500c3c5116100c0312402411160140760008cd299911408070b840e05041e0b60020003594a000b04210a002212026009503128501280340c241d83c0d80c6140c0d04c2c98480401c160343d4582103240b003000309110003401010f2541007420414181580245982c9201030704964502c184e41080040008403607c045c40900d070070400300700071070034107410724490400c44210405c49030040741032417030305803a0b66800c205040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 525288606 1250 525287356 525287359
    0x40e070c11030d0c05060615040e04061d0f1006050f0f01200f240c0a03110d0e01050612150603010905030a1e0c21090806100609050306070905060a02010209 69
    0x40e079010020f80c004101000c3d505080e80c090280e140440c0d4a4900395209400c60300f107003805a0701341801c0034004860002c0140c0122030555950304450050340841c548284220040f00142510010310843d0500b13046418840c80c80080c40d010007402203584080c00d20341d04500546107048101c14803001a540c2e0a0184550084100c200316040400c1400049601044022506903511079203400784511040f00001c200041207023000000800c11310012000d004641240e16011a1702800c50001482607803100745088511030320360b0000d80101409015154204001f40c82818140000207d120f40390100e5075400b2100011a034003050181d41e094120302c4c0c1140d004425680d0780c40542d00042e00b480070340c540245021072280fa1101c2c0f0b0030b009960903110240c02c001441024241c0d00410072015852040c103406028075a100841c1a00c01040b101e032041e15240c41034000c150416501404043d92039000038443e0380550100304174143d2218084044400c1980c45948660044106a0281c0030300790006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 525289856 1250 525288606 525288613
    0x315030804090609060e060603040206131802030106110a0528021215010b0901091418010308040515090a0b03130b04050a0b06060c06071b0c091a0105040e070c1103 72
    0x2c510007070140c1c860402c6400c5002c0400041e541c807000d500d6041000c80d520382c2d00c0081400020058101803004140c0c010080e81c1801ca040c0c0c81c1c50301045105083d00000031800c3d03011006201c0c0580085c964403003c01c0f401e000740480c403801e0ba500340d5520204680090b5210383d00d0f800b4a40c0020000181c58074030b81c02413850100048054030540d0f169041c00d00c4040d1049842c00014541c145e820403100800300c1a510b040701d032410f0130015240c1505000141ea04800160480d40031402254142d034040c0d0b03c121622a540d901e800e0070445891050342c014030041801b0064401942d407540003041c101d0300c0604640f0340b01d039180300400d5540100500068000c20703194080004021010803100001d5200d4545040281c40b0784040c40228050707050300881e2640a0004274540500030450002c1081d4084a800d41c0c2204650b200c00e03918030503512584401c0c0c7c8032019200c1004040080c145400c0b001e180032820940b41041c985440c600152100d424402100840c0007804200510041e1428010b03044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 525291106 1250 525289856 525289859
    0x1120608010e030909010b031302100c08030415151d060d080a050a0909020304051b030c040c1d12150402030703080c0a200102072d03030c0b09060f01060315030804 72
    0x920f80c581d4000420b940c03080710b0340000412201020300c02e8900031a461003100d80001526424860341e000429010010b110040703400b01700280315100118419813199051300f00004100c9d25540544034110380c0c0310b520040c180c80c14820303040380809625050902410010041c1c03184000708103258860000a403c11000040394200c0e0394105000301044404c03507441d0030322a5900c9a49200702e00095030010a80e80010744034503034107100d2112218003004002c0a840d07050248034001303022170b003400802c9004142003002c5400c810004260000e00d4100580d00d070702c44100100300a03521182440780f0a103188e40c0c440c001c1030035501d04101c0c40e0055640803031401c0e0f035031074907221080d540d000c41c1e403040b2401c029035502c42c909121006080700d45e40b00180c00424070f490401003440d01144000905454203504041c800010000170350700040210f0203620703402c1100005041141480400910207080b651200341801022042c60396090304441082c0b0380002c00ba020f6a000c4140d2921130f90010f004034401050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 525292356 1250 525291106 525291131
    0xb09210708070f14010c022416060b060a0519020a200f031f020919060f0f0905030718150e0114120c091f140a05040b0a050112060801 59
    0x2802d0302a950908022009141d686281e08220088020400c1c0000d0300d41c2603c0005090103501104104260b42001803003003001183c00c1e4840e0004114007401404810015007030106c5803042050724072040d520b40e840c020055202074040c0c814a81e0b00f60b5500c0d040d26240c03640c9442130102c0038006900140132011490f59040c07540e01c2c00004600544109407002400d4072038a400907403d15018020311f5104452086a0310f510000d41107803038800d40240c410500c4018074505110050003609207a202c6614a8a440790020b200c020360156440501080723107421300507a9400680c01e4105c0d00c803110070080001420980c5400f8100e81c2600340c081c02c4800d000031030100116108103051352050307178100e8840241c2c0710802c1020b4201e031014a00a810078203605202c0d00740361903081d03844840b6059901806030b810b40c25520503031695000300141e0040a02c0c00c03840e46011001c0034001c24045034184400380c49600014001e0007280305245c180300c0d4081e1901540b01035504054010010b4038000c2102503403040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 525293606 1250 525292356 525292363
    0x70b07020709150e060f03060705130513020c070e13120302070204141f1a090315150103060518060f1f02060109061d1303050421140105010b09210708 66
    0x3640c03e5800d1380d200058101d05110011a41d03000000b0010a001e40340c0e00c0e0155040e41c0142070410040c17103820404a511340701d0802240e00d402c600d42c030060f51501a10111030418096402900080210304280101801d6030b0030381d095220381182c2c8400416100e480180c0080c803401078001d402c50300b41490010240030f40c43c002c0d0700c80d120f080c030508503460101d1009900300c0c50380c1c021010003020340c0c034400650500f0311010f001c081001608807801100301105004013083d08541c0d00110318080c90701c861465901d800345500504060f2540d007800410b5048000c603940c40217160324018500220469160764480304c1041c0c0e924000a0101405a140c880003902c900b4240104004542130a0000070300c04141031600c0e8007200540100350f900e8803203403001c26104840c2c020a03800c00c001800702088081040e0302c04041050481440c8140c1520740c80c00c041903200e44d004900c03450f40350400400c030b4201464203d890a80044405503000d0341000c45c0d05a02081c8640490041d1159032400b041c90400003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 525294856 1250 525293606 525293609
    0x151302010f02030c0a0f080c1c09050307050f04020703120f0204060314070c03080705040305070603020a030e060106050f0705030409050403030b01120e070b250804051014070b0702070915 82
    0x780e81e0400034103080101603903a44a5100b0402856000390200c0002c82d0035001200c103664820a4054a4039170314482542c82c1580140c01a00d4020003145d00d44001030304440510010401503018042d014500350016010510030b58445001d41e80001708601018460941c0810134108400704004803210182c100c8001d41080c010140030030329040c410b0240b00461014144220203950b26640c112180c0e640c2280c5400000e00000240102030001100041c818001d000c081e040c540d130f0042e159982800002c050701d141e0f408290094001100510819512608403000e124138801c2141e41c424072440c00c1c074914440c2d6400300041d18900f406000806a05400110310150240e803010451000007810300110350610058280c0c941c40203000300580641c0c40701510b980302d2040540c41e00030400d44d1010420480d00d5000b219500310001d010701c62843c129000d03040703003140c0d07142c0340380c00300547c800c0d070400c0c0c0c899500d000d8148090f81c40042c0350b040c4200700c80c0c4d0180040702024084103101900e60018455103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 525296106 1250 525294856 525294859
    0x3050c0a050103110a0f0512040f17030415020a090801051e06061602040c0c0f123e0f1009050106060509090712060506070b040c0b0a050a0302030603151302 69
    0x103440001e156200303002d0070391300b444c403212040e1402005420694207030610300300324014420240b210440c05030007181c4961169018400c00394104006103401c094401e04d1401172807170517409000b40004910007503c0300c40300d000d0000c00140d4074440c04005844402c03056102c1c4120390700700001c100329019414813030f5480a000020741d40c09602c96100b00300544c003d034100428409220030300c031005031800e500305416841840c01c1000b010400364442c4082e01c0ca2070340058450b82000d4008400490b4800004900c40c0404410903021402c600c49140c24003800485005234a0000718a100a0304030a100030021240520120350380940d41079136200140c02080b41c2076500c1d52034640c0c00a003070b0780100c040b40c40745030008000350501d03612101701307846140001d002085056030315400410f16403544401442c0103400351850b08410314281c5049000d452a0b5040441d8202c0284405210190400309030b6071810014100941c0b00d65818011900d17200d0350030307019442e0003d04824082c1c0341c02d140042c00d018500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 525297356 1250 525296106 525296119
    0x50d2f031b0109030807030b15030103080304120e010903021311040f031208010b070b130222050a06051f110a030c03020c0301090b06040c0e0301020a020f16061713060603050c 77
    0x100080303031800c0b02d00800014012517107450000b69186e00c2980300001603400186041404a04107221240a801c00d0700119900c140000500050000d1740c8a4104e420304145440a450624000000c7c10702c2158172009000d051403c0000c012009a0b1b00110301d0428003001480e20307103a949004401c000010300c01603030003141080030700f4016886900d1080c183c6241040541c588a100c0e0b81b07150390007100400c0344a44444441c040e50040e07803a140525481c00003c0f40070810001905000800c54001130141451030b0300d41942000a5200d91261141d01c210182d5920340d91000d0507802c2d600704044e501034880f50f0003400d1181c0101508418100340b094026822140803142180a05080300d0307031070802a0103100e510000491902e01070704925526070603460850032418a01001c20f0a81e000070901074090f81010003114074071102081030340740304821031410070041807801c0780207040c00d08945511048140c0f41782c00074508940d80d03001c0089940d4408410403505070342c1d0030300a40702c0c0c9008162921645 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 525298606 1250 525297356 525297397
    0x60604170c18100b1e030414060103080406090801150308030405030d05010b0406140c0a08210109050603011407050d020d0b180106110d050d05060a0512010203010918050d2f03 77
    0x3c01c0e41e00359100e0404450000524500e503174032100f41600010070880b210684031900801c0c401080c40018000d6208021743c68565081140103402520340c0d401c9202c050785081d4040d0811228030b18a001200d40080e450342d60703030300c403070600a043d480350403013800c021820321000091700c1c071510000708111541c0c1e989a0010444024404030a8800c0e41c280b0f40d410f80c004410100882c4040008000601c03074880c0548850341015110700d5100000d0780300a289030760f280704101182c1002e02490814903400f102340c0810385850003002c2c255028086d615000180c1c04180380310010125808000070780c60013001103882040d0003599060300d2109019210001e040d0081c902090b60300012460150340068483c581044d010008142c0204001040300313038808200799000078180c441c030f40d503e0507201d00f00c40003503036941c14440342a00381c605100c03416050594040241c00411004070b00b180ca00b00e10362401c081c035403000c6d0030340458040c0074081d59a1a4812040e202c0c1d041031002004084030390084002200e80d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 525299856 1250 525298606 525298619
    0xf0c0a0510080a06091a0f06030402030a080306040f020d050717090706030e031e0c010b06030c0304020906030f190b060a030b0103140f01180209060405060604170c1810 74
    0xa1a034400c05400891000500c0200c42c01034410b9680011074060025003280c0d039907030090030750340c40030010351203416041150742c036508101d59443c01500303054840500c1c41c105980425030720844c955000d4201c0070b000c00403501ca40e50b03503002014043c2d542101035480b41e5010031820010007033034403201c000c01d5000c3c1220b400d84c000c9400c0b0030f210b44031500c0030380845d070300d0880c069000d0006148031860f68041041703507420007c03070480100848003100c10025110200440c0550031511900c8215224680c00c0c000c2055400300c04c0300712a0b1059040d80c1d0582c0545a10001c6840c220200391445031034003420702d94421417406c03031610b2003a40d03000702c00040c0940c80e40c00c28007100c0601400081c054454410060021a90011468400d01090000c03602040758030825142160804011b04165240e2120b0840962500800540c0c1200c1e00312820805401c4c0800012103600c214172804422a00d802d41154140100740682041200050501e21400383c4000324211890421603108038004034546021030b40c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 525301106 1250 525299856 525299869
    0x50f06030105040c05010c0503040504050702070e01140a03060c0201140703230c121e04060f0c180e0709050613172a0a1205060711011103010e15090403020f0c 70
    0x500c4d0400361800755030f42404011142520740020558451104000006030740d12a840303030318400c41a650181c12401d05221a1110b01c59042c1d20140480c55411403090741c03540c1c0c1059207802c482e0321000c000b076103502146d010303405800d406160807803d500d40b204202141d9015046000c800c00d002c0c00700c140b4a0321611080f00e5000041c0c07020701d214081408540000e26944201e40e81110141c4201a0030301c040141c990102d0741c080b10212615074a41e00440c13060101c81c000d00c0401c0c0b8050410b40700180d0b066200c00880d12072842007ca04240e5100416a110300982d80701010f405d0190120380d949901040e802c82103412480382c00107000281c2440c42c02018003248003602d8404110003005146181d001c0e4290014074050066840f82d580d800004000072090364405101d03224502038a502e1418041c00340c811541c24181d1003a0340d0602c0295001a900441100e0644154180c0400700740c681c801072505c04000e4451164100d080315090200307240d0001907000300c0e02840d07410bc0b50100c4845090201c2d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 525302356 1250 525301106 525301111
    0x6050102031c11040803160519020d0f150609090b01060c0c0e040c0b0307030f060807053a0804030606050609090105060d151707080a0b010b030c0c10050f06030105 72
    0x900040b0440c80060030090341c2c0020885820600402c0d062540b02d0390381509540c446402c01701c5081080a0500400c84140f1107683c0740d00e606100b16440203159004074407040c1607080024040c0301702c0400300d401c00c411103a103c0781c00681803400f0040b00e6151000c05000b00404101030300c01801a0000199492203a0b942d280c0040c0e01c01ca420445600d40304881c54516409001118032901011001ca20500d05001452107007560b90350204501e02e41100c1300080310400e40184880e604101d0040c000e5880700840c24055440d1400800048110018070004084185044140009060782c1c50410310010601a0059902171041003158950760410410304d4800e00d2441e0b03821440e0b00c001040f081c50200003132700d0601b8403140085200611000c18608030007260304502852121000f1441c038000040011502a01c2284020030410050f9145d1440d03100b014400c11100c3c4c4000070028203800004c50603031f080300c5041411501c0e4070340800ca41002a010440703510381d0b00500640001d0341403905000345130 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 525303606 1250 525302356 525302377
    0x60c020c1203040515070606030f081b0604083f07090905060d02010806030a1b06030c0e060417030d0e071703090109030b0c07150e010b0603041e14030d09060605010203 74
    0x16007804909440390806c1e000788000f83c3d1030f04c2d42d80030004049200c0d80b10b900c0002d88207805c166910401d5501e40650341c034130459154500d0703200c0c03030030407002451030422500030312058003030f400f41e640901ca8172650142d11030011424201200740d408181c1d007990729009000b0340c0c1e00d441d1054060f44616402040703c00c02c841c41c590252441e2105000340d401030509076003192000d410303109203014980340d02c80b4007403070901c3c1240e034141481350030401e60340c5c98494006044150719148600962890000c3d105020394000c42980d400c0003021000c003e1000c0085031181541e00f0414070000031403e200ca515401c10b0300c20300c3c803282c90780e0f01098207162010040f140d8144058650080580c1162214030031580c0041c030700100c60200700319040c0031a61051100320030b80f004030800710340306628503a11820746072990061402107105100303002c002540c41d01d4070804c140700544074107803208850503c801041090b4103091298000060410700c200c1c8950008a0494000c00c014880035a80300f004907901e229011818 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 525304856 1250 525303606 525303619
    0xc0601081b010c08270f040903050d050901140f06040c1103030a050a060b16020f0f18040f0204050109091101090609050603091c12060909110f040603060c020c12030405 74
    0x7840d0380d40c011544204003502910482c2d050180d030003103000742044000030381c4101001c02c01030b1070003901c1c1c40414018284400d83c1c09025407040c035500a4400d016801d03108000c1929080001c0c4807000075440021450b505072261009802c04541503191980243c0d01c460060303050018484846014082d1080070f500c824004511710b5031480d00440c000d06024100a40d400e4a13103000040c0b007021000506032041d141c10600d80308181c0d503c10020035095001d44580184d9003d41d5140c1d103503446446000416000c40c042001c2662146407181d10003001c2352000350321515000c00442e17020f625601092125216a801d580b42407417400041d10b000ca458418180010b0001d1801d21003410300c40f026507000503070070b0304031a810114040080c1c0c0800b03aa0907440001011300c1040052007100e800341c0001450030b090b08000080e59a103580ba00d14000c031030054021628610310351300544417070740810020764100b00e040204202e01c2c50000c2d21400c1e010702080c8200c9000f0b59100d400c0c0c0d80402228202d40b00101103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 525306106 1250 525304856 525304903
    0x6010b04051003020915030a06240c0f03090e0f0106021b0603060f0a0b18031912031113080606030d17040b1305060109200a0e011d06040801020c060108 67
    0x40f000b13544000030681d0802018003240c0074080059014500580403504041348280c18011142080c02d1030006582400c240ca0310010300c0180c001051008458106200140602c41402c4c16110003255500c07a030702881c141002c12800d9030f80902c0300c3c0d060381d1a40d402d8031903258000e07800c1c031360310650700d040d0981c018401c00100740207103006c8a602d10044005000c091101c0e44e5074107204010b03009a44100c03004940d12600c0da0041c0f03014015800d0030500003a045489000b9a00c81b03101c40350942180d5402e065607144803000b162622030650300c0c16000c1d0443d1201c0c0c152a48646a100c08007640d81034000e100e281072146c140d40c06696440f082006d044141249551281c80d032402400020b01041c610405c001030300c40100e1014070000f4040c00c0c40280c04600c00581443c0e11000300303200590b44194031010b10046550b541d00102c980c0c0789420918101210306040d0442101c096444d0300110703030004000600290714038044d0050450703884d140c0c0c1a903181c0e07a6100782c6280c54030101101e04a030345141c040c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 525307356 1250 525306106 525306139
    0x40b1b0f01232e0806091b011701030605190c0e01020d090308090402030408070f0309080705220506030f0a1505090303071e05210907090c09060c080f031806010b0405 73
    0x4103c0900b1038a8a4505480e03903204002802e000c000d075040e0a00390040c140940c12081c6008059104035020328014425842080d1402d0b220401800003c00c4681c82d040842d07440c0d90010402c041078003801c2010444001c48840c040e00c0341325a8140c09025005a2142002c000c3c003d140302c80440b6004000700d807420f00d0601c20080258001002113844280c10301105002c50b083d104040e81e2144291a0032032154205040c480c41c0c0251680000d105501070381c2c0790006c070449008512802066440b01040e592030342000241820750b0600c8402d414070402d90080180b140d00500f628280010b120204500d89840311266140e2004a403001c1c041010100311a060000c64031240721320a950b49052420b20605040301a90006403400284029022406015201609002c5c8000a06030b090082100ca0400d40d40584040c0a91080505110100713101c6414071010400301d4204100500303001d5a24905020b030200310b0001c1844400d5148076020010400b0b80c12041110150742c8002e2104160014548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 525308606 1250 525307356 525307411
    0x50d030804050304240305060402030411012d09170703082203170306030d0903170f1c02070c08010507020723040c021b0d08040b1b0f0123 61
    0x20000c40e21403008000c001510920300138000151844c07082c0c171440c9030442030401003c2d904003801d09845948104184070014003151134252204c3d00030b08098108000c040f804403003103c00c0c0d8000c2030036880d00790704240c106540081041c00b9103c030f08030041c46c154956101d003913a807422030200a2031484100400c025035101108d0031610031700d5028062072242e40320740c0d42e601000d41121006c2400e00c3d01106010451030180030124890110f480c04809041c516211030105844400b01c51000d0a0000f4a1043d440c03040b40456241c02000c400b20224600b03011061002903000000650b0003051541d4085440b00042c0101406611140c0c010300c049828041c0b07403a20b0b80b42e9465060b081580c100a80074058036240105d05090340150003401d080e50045900c00b0240d820400c1083c0701d004d008110800080700f1100355000d603044000c6c1c00d81c42c0d58440000e041124500080c103584d43c401e00006060340c0380c054000c01081200c0420b068230240e000c15400c0390b456425202c9410811280f00f0103024013640c070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 525309856 1250 525308606 525308611
    0x310150e0613110706090507090501090b03060f0c1b07060f11070612060815190207020a0909030309051603050d0f050714120d020d0b030a0f111f030504150204050d0308 74
    0x2c1003c2407800c02c107a60303010216090004101c416401061081040300014842c1500400d110355090000782d000e800060f4840c031004100340340501c0e8410100780c0e1680d200044c0e07841c000c440000c5160300c10710300d500d40d44e640c000c038461705000605a45404bc031440c41500c07105510125400140800e9007800829103010b0300d041200448595113010010382840c08000440504003d01200585400e10b6504800040443c2550004441c010003d01c0c00603201c04c6074103001c4407070f0f8850001d01044545000c6010744801c41019080e403140843d502e695101070b420610440748158121211080701320790a42d034401d00c030241017002c604240009000310b4000050325140501e01800e60700100d421300740e07007076564201000444900c3d6020841c24140301e000c0c8034100760341c0012002031507149142d0b40c0300305104c00c601130018841405a0349401f12501c8402c1503001c01000074030540000070703480c180200181011030301a04c44540c0458241242c1d4107034400c403810f0318800340c00980d600307840b900d0640d07160202 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 525311106 1250 525309856 525309881
    0x6051501180e060d0f0b061005040605070b060a0905010e0f060108060a03121e020f0114010f051512010b190c0201021e0313080312011e120503090310150e0613 70
    0x10042e0a44c00940d550f816125a6807003a1340a41d12414404103000d0844403000019090000411090150540107015140090742c40079241720706540d40340126640c5890740c0c1c068000d050400c00041000d102c4904100d104010008091559650749001141c1c01e400540380d6980101d5070160910220300c070120304102c152030609000b03001048a40300851070440c00d000c0b02c0d005070090641800c003c0710030701170004840c81000c0c3d6183ca07541004c0040342d90000300d114591040c0c001c410030700c01c05207501040e5007023010b200c56120346641c0e46124500c01540400c0c170300e1840351484602c00101e240074402404401780c0603402008801040d8004901c2c0b941c00500b804020303c024092605203101c0310003094041c0007000040c54407503d18004c4000040f0045e0000903518060225818040c00040f201070200e1700004e100e240390919a0411a0a52041043c619007500230755030545ea07514840c0c1c01001c15000340b0354130f692030740d40c0d12003040c0c140200584459a0002001c424041e480712950000c6420218 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 525312356 1250 525311106 525311119
    0x209040209090f06010219150c091701060906080f0c120a1b03170313030509040221010e0601020703080d0c0306080d021b0906060712140706051501180e06 68
    0x180c0001005664120341a0803010083d100308203d40d40c0c1031040c00e4143e00c0c0d03040b4449a03200d03161b407040d1861021640d0689440c1c1e0720b181d4100194414123a2a008080e072407400710055080c02e003000d005e0032040c0282c00541d420281e0006d902100050410300e81c1c1c820740e000d029003519250400070142e2924114842621a6900361000303d40c2c041042c0b882041d10004201c000c0e4510700e446c500e9408802031f0740d0039038941881001108240d041ba401d001503803500e062542c40c00e016001400134064004001c00907040e060001501c11062144181070f1f640441e80341d1425a5101c3c01265100094000181200001e1240041d8407a40b600036503425949810301081c51521b690440746030100703001c20307180181e002038072600b40c2980d00500c0650001040c0c0343d04001d49041004501c051003540c0c2c1c000c012881010301a10194803680c400601c0c3c400004045a0340c0140b03041400c090300f815110319a04405070310a24a4540c011036031113803051161800000c3c03c51401e00d41c44498100109225004003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 525313606 1250 525312356 525312367
    0x403032004080a140d08010e07030212070819050c0702090c07020603130308060102121b010b0604120506130308040212240f07020604021f0e0a0303080f250302090402 73
    0x440602600182c40b410000f403d0000e01800c0c040701c000c441e4000400e154000d84600318940b0b921001d041c0c150790840040ca8040d440b18103040b0000e11440887c0d5124089040c01c2c0003c0a5014400d10700a024110703600c82d41100c1518000c0c12a14140e80004034020b042040300c0040c200140c0542e48030705040e02060030134420780c0108078194000c45c1d100a071456003500c00401c16401001d10341d0412001e10003040f0048031519100b903507100e0100c0c10f0b2810681c0810190641009400000040002804064580f550341c00d070780d440d280010030111994020308000500002c1c007040300a01c85900b55855840c103444076002e010712040e8002482103503000e0609442c0c08264030300107404184180303417004240340c502200c1d21213140c0c02c090541c00440d0091010301003d60359280319030b001c0000d05104103a2101440302c044e10888401c1c02c1d00ea80201e103c2d600001410340141c07020748240a8002281c0a81c1e650215402c58100824410510008a0720300d00700024440c0e40680a2804040d10051604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 525314856 1250 525313606 525313661
    0x306030f0f0b0a060806131103010c0e0102120c06070c030908061f0608040b150f1309062d09150518010608030a120b0f060f190c0b040303 61
    0xc0c0d001100750340c40c2044804040400c14803100309a4410f4004004110450900d20f903251508005001540b9524680788610b0601014240521082000070001c016824a058010704440094804030b805800b80c000170704001e0b50801c0c00c640c241115403010b01865600c004041d14520052541501009a24540030031616807c0200902400c8240d0014904221810001040000780e4220350200011802030200203000324865503003010244030785290458040b40031810424900240983c44200d00601840c2070a00c3d0307203c1c4209a018960600807076990030b007128800301000c00300f62107000040807074820440c1507030300141d50180f04003880719180600405074070507104207a8035082120b6000501c1510050f0034407400c0014200e0b50041c5042040012024240d00710103001698140d48820a2113002c0e5a0030802c0303c032000008000c2d6440b01d801c04481c55254100b0001d000e005100c03008503003452405040c0b800022503114041d05055580c0f660110003404030292600b40e40325480d20899583d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 525316106 1250 525314856 525314873
    0x50324090a02281503021905120403080603011b08060f03070b0a030c05040b0705011b02060712091e030206090607050405090a02180406060e03070506040e07081b120103120809100b01030603 83
    0x301c02c2583e80150300c6005501f4110b074000302100e024814040100541119440d01451403607010340c01d41409210b5075a10780101c0d024240080803000071002c40012001220341260390365004230000c0e90004c0d140e028000a159444606000e01d295110f000d02c80d0030350309803082c1c201c40130500031440c05c1d50600d43e0743c1205542036003190808507040d944a4554142d010104000642410401d03c01440c40d030500030000340c005540c0f150841481504c0b44680ca05002d4440e00503620010250428152030189080080d00c800090320018224010f200228181902c00d805440a4442c001c4c200540da0310346181c80b40007980300a03500a40c040f5000c10902c07007940c03a4411400203060540b01c14031030300460020035050a00d40d030071191199500784014040d0009412861340d01038582c1c02d0907103080e107801c14442e0100c1d109000b07108041c0c50000e01084e1600c2084002812248600f01c1c01ca81c02490210984210310115000c1000b54440c01d6503400b40030301c40d00203010700708044c100010300c0c54903a22001c1070f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 525317356 1250 525316106 525316139
    0x10f1a031003020301090f0b090d0503060d0507030507090203011802190309052d0f011104030b0c070602040321020102030f040b1806160e061305041104050324090a0228 74
    0x40802c03d0315038020502c5220101c00381d0080722702014160290710054098440c0c000079001074003c1034280d40e424204001008000061038005007140c41d041d40c2c3d10070b0301010792310074040d800390b200c14044400042c42d100d0091701c0e41c007100d1800c00426000c0c07190084005000c6038a090340d20f80714002d20201c0d60f102010741e0039080403002480480c1e00d02c4440311a490151751003044401685000c1082c0341040715107090300c05490b40f20748244056103880180038442d00bd4828040c01452001800004000ccc440c5070507103a214000c0c1502c03c504610343c0302a0301703c2c041141d880b59100304040c005000610102200ca031301c088140e851084100d10724021030b1814404461507200001f808400d0071001e0380000d0003c104c4d0008640103442c207841c0340c1100602441d10f20030350380902d0301c1d00d0900c11289681010785018200241c11a0800f01042c2100134900c5102180040c0400303204001c9240d4076404200c018826801900e59003408111080c080721584000440310500031500380080b4003030404402650 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 525318606 1250 525317356 525317363
    0xb061603030e060603160306050a06080d0e090f010b16080c0102070605270307080c120703020109150203091203130209070c0515010f0608040501151d010f1a03100302030109 76
    0xa101d2402c034112038030346032014043e10b00c00d0b40f0aa0306802c102001c400340702c0640b80e1003500030a458441036509005003140f41c10080c958016003a80c030031240e0340002203d00340e000803904e800140d00c0303408040000c2c000c20f018045c0c101c038041060300f4030a15101c2d4041d244c07602c5a0f0b6120300d490900d5001608903004240101c4801e5140c03014803450b41d0840036004118035083c0b214906840d501b41059650340300312103000f00420700100e600c0540712018000a00301c09880c1300706a56881003446c000b070007040100d008903002d54001c8040b40c882001c07031003545c0c45440c149008080300e0442500c00c56041d08010240304280d4050b140c1e610068444408150051445450f0403a20301018601141401c21107842151802442801000101e800026041c1280d1180c00d107600c0c65100c50410a02600001c04803a8410400d0b0f2030008125640740c00d0b494090000013841038107a602d421042410b03c895100394804444030f81440028241c481d002550424449507441c20140d5495020900b50303240100e040c1d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 525319856 1250 525318606 525318611
    0x60406031508010e1f0e03030703060305011a10050708070c0e101d01030209060d02040c0807020c0118060e120a0303090b0c0c06012c090303010306150f090b06160303 73
    0x400d009075108015001a11508000b0300c01d982c000e60b4815a1802c050403000b400c441d20b10004511501d00d5800b11840a440c481580c0e0b41e460083e5018000c0c120070711007210158038100c08000030302007030074a60351100402486041c03039480c0040c048807a038000301030517900408100803a0780018690346522004042c4040594081c0c40c20790003000e001e002640c042d5000070f0030041c01402040c1503012950640340c0c11035400d0540d0f21080049004100107050080d0800c2c41c3c14180b14905800481c1c040c4540180c0c0c1c01c6410340c41000f001143e04918010b06070814805011044c41801c0c0111910708481c03401800080c210001025003520b000340112003500460f5440d04281d0902c01400c1d01d99910a80b0403021030b1501c43e0b0311408a03500d0704140b142d4200461180c0300140e450f055240751075000d21100144010505004103001d46031f074400e100032030300945000c01107801541b4502c1e9501c1180c40342d250300f07211649000c0140c009480004140703944400c00b000707070105032008114041c0d0340c603010390b0b0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 525321106 1250 525319856 525319871
    0x40b0a051009180b100303050723010e0c09070c02091602210a031d0c011103091915020a150b0310052701061214190f030305070f0906050702030c06040603 68
    0x380c580392001600140b24118a2507081c030100350840102c41c001130344000041c510303880f0410212060ae2500e40403210550034030102040b8a040010750142000e001c64184141e5102d420003541c1d014040d0034029000410080050321804440501d17a0b0442000d00654000e205080d898041544004140060802012415450042e0305101e40301e002e4841008072080444104140c5540d610020310302d03810821404000d48007100e0a001b07550300880c0280c05106027424184402d12604414024550443c1040c941504403610000304002d4041c1c00100050311107a0340d00c00725000d018000a00c0390540305400724440e694865201d2244100c1c0c0c03007181120001902d1649107180c884001d0701e090240c1c1021814060406401a0b501040d40d00070300c000d4071084400c0f50741d41070025040742c4003c11002090390380e05108510603e43c01c41442a5030401940e550306806548071400d1040000004507a81d2040c003101d0301401c001c0c031a00b80014212020b4105480004102c1c0c3d0080d04001d0019444051 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 525322356 1250 525321106 525321113
    0x9030a1713090638030a020405090f070c0f0c0f03110405071706100903050d050a1e0804121709011a030f06060d0f060c08070f08040b0a05100918 64
    0x40c20015100c4020140603407450b107440c180a840c400c11a1003011344000744e4000450b002e5004880903081440c284a417030b0710308000e03a0310094106200e560f008003a4100003862508003d03118a1148040d5100d54034805c14a446440140c1a0b00c0c500301c0385640300303890101d042450620710b10300a40c032404010b042070610905000640710054116014030082d070803060750b101d40000d0981e034095800c1c0da50381140386203880c0c11a1841200c4d440031300740d07009200c8a194a254004020214040607440d00d00045c0141031440440c01c0e0901c100300d000840c400c1c00f0030002102c40380da254400045151905183d510747c4c80500c0040800d413001e840c02d0395a6804180c011031800300303103400c54004801600881c50741824584e19400d0040c0b0441c444c00d152000d00040110f00020b13a240242c0028040004100d18100a09070071003c0e100c44c40402c0401c840c0c900080e1044952a00ca250321008c17002d034075259000e40e1b00142401a2041c4d110880040c004200c5000500c41e4118401b0207248140108910b0704 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 525323606 1250 525322356 525322387
    0x160c03060e0604050a0303020c030f0f07031b0503040b03070e041a0a060504061b03141201050901120f0b06060d180c08010c02061b09130b0f0f130209030a17 69
    0x48081d055030304108100404500041007084800380c160402594071240e482036a41180301d0420951201000070031005141e00c86900a4250750b4840d441b2149034000450300d90207071b006180e41c001c10940c401c01c824800858600003039600305101382070222a01028100080640b0070007074107c07690290070358400c0002d140220b800d0b40100b90310f00340f01d40341a0809000030704c0102d41900000223081d070f50404504240c4a40003c42c0b034807441401850300c0781021184003903241021300ca9a84118106000425007100c02c6119403819540410340c2869150a551401d0004800410507644480709000e0161072075000e01a40580b204070100b000707040143c900d4240c046e20500c0c4c00c40c8501da890082000703651030300043c00d1900b107002103c554613242c2007002814214400d015900c1e42111110280c961041e02039003140074021021903903078040f2058001848064481050056480840700c219201352602c29401002c400d0009020b07600b80805644880c5c190b6403041404080500d00019102d03042140131 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 525324856 1250 525323606 525323621
    0x10209010201060b132912101d0703090c0506040b0405120a050601170a15060303030c0c020f0d0c0e151305040f080d1401060e03010b010203040f030b0903160c0306 72
    0x104802ca007012401700ca40055041e0340e024490390f868186541d2180f03145030b2030010312800b5400c1c0d40550b4400d03101e980260b6a42050710b565070b80c0300f050b48011850110350000e02d81018154400340c00740d692108411005000d14100c259125441d0000100d0315480c2c100003440904484c50308903a44500c0c2c18184a076800a841d2681c0e2241c02801045000172000306006045600440780d80307004896000301e041c100b010701c80c00207000034080600080356079415044501260b00039281002042c078111004c0d00c10131494403000394410b0b5090343c50040d03880d00c0c05122101c035000d880c1c0b4015090703e0b009500702c10f8900340d44c50205030008002407995460f00e0009035500c41010202031000d81469130364030b040d084003840001d0644402040441c003805440d8403c6001d62242400381450703580d0b82401820240d905081140203500385482182554000002c46045807802c07003201c44a1845c41c1c44403e864100601601a40e0004100c0e00340aa80804404140540202d01580c103083c0340d4a481070459108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 525326106 1250 525324856 525324869
    0xb1f0b03090c06040b04062706080103020a080114060603071803051608160612090605040c08070f180903020c130b130504020108070e040b0303070f0c060503040c03080d140901020901020106 83
    0x4202c14012050094140c0c0d0840f281400c22024600c040440382a07155031004002310902078080001400030781c4000d1060499000b42ca01021040e1030300756071400d032144982140d11001d1003101141003414590000c0d607118443e49030082d030111007a4070054407003503c2e038400d490303036448455144944840342000c680100780540080240594940030001c0c89003041c0318217018400c1c1510420032010b0a900196201940600100a01d00d46131070314054000c0c850041c450944505200801c0e40d524003080441a2070181c0040b00c01140c0e0031040c08017500f40484200c045019070480a1000e8981c81d090b40b4448850010115080808100344502c202e04c1180c1014078a04050a020150340c01c001020f800001031700d00108025405404640681100e01c071803030b010f1000203100e03014003d80c4011901c0c894401d5990181c86030741d440007101c490109480180403086030100030070005100380000c0c40c4000030600e001c0b401284110f0380c4070b01d039a01290200f070340f030750005500d110640e820311502c0058a40c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 525327356 1250 525326106 525326119
    0x150807050a08060103030e040204030803090a03030c020303060a14240a031802010c0308060315010602030903010b0a0521100606090e06030601141905040911011803050a0b1f0b03090c 80
    0x10b022680c0d503954a0621016080c80317480403000c626526140c04581c05150000c81d038907505d003030901000e541c6400c4907106400180c9404500c106691020003128020703c4001c0c0040032460402030480800e105103440315a000c10f000c0d0020100c1141d0308042d50768982804a400c0d11241d1605026003541c650458401c44512401c80c414010f0303810038510000140c25213003240d030703030b40d10640400e20348250010782010301c3c2c0740c0400014401c1d44c000003c01840301c054009001b484416003d000d8580760034002c0b9640315904820784034000013280e0110918003044800c60b0100034440030a01c0c204d46094000e6030000310401428090b03143c0303d44c4040d03003005040d4002e040562424240c41e804524824100b032098100800d1190399102a61060015000c020410040003070580782001100115200c00c5000c5083c01408411541800055108803904080508260042951444044c20004000345e4402c01c10440d55038150105410b683d006d0700702d840c00e05569052001e80756140041090b02c079803040c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 525328606 1250 525327356 525327359
    0xf0a210f020730050d090f030b010506070503040317070201030e0d0e06091503010b0409052a1e0a0201062d140402280f050c0607080910150807050a 65
    0x19030000c2c0c4070302281c44003c8001441c0e498031520001034440e60791840c2c40303280c1c10201075040c05404507a00200390041d032166685150744d13040c00042c0c131601d44805403480304850010400340c2454001003e41c1d610540c10b42c2d00d4a074036951096120155040344010344400410300000b1542c01d8801c1e1148644041c0c01003100d4401d1030401065901c8540080380240004aa0030229031a90f501c4035484442010030151030750385441c6040b400345c010f48240c8402074108400b01c5c01c2d0141030030100d483c0401c0b110503284800302e042d04880707081c0e00070f8411102d020403c02d456104880c0000190002d414254008140070f403030900242811030000340c031496400802d1400c09240940d0402000403130704000024140340c103101000078002d00800c5240340500b00061503040c6101e18290b802c2103003c1d140d84130f120030452017072001c0702c0d540110601e000441d84180040303501c45029511140c3d004060308211604c91240c01c40740b400366000c3c0028100c20405504060184101c14082c900161800390750038440795 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 525329856 1250 525328606 525328637
    0x30103030318053d09020301110a02060408031308040308030601080a110d0e15130c06021f0203040c0306020a0c0515040201050f0c010608030f0c1015170f0a21 70
    0x1d040c0281d1540402d8402020908003200c0c541032001e5982071200070384c203542e8010311803901030701002000700d00c070394a000d506260700e4603a4015144010015070050200d50b599648034060381d48042d1a0810b1450030024410001d0885c07801040075600c00e84002d40c4030b0a0440014000c41c1010b0075071b4543c0c0d41000015003504c01035205541801a40003000f290b4100720803201d60811604044013101080b02c00200a5038280341012603070018496055420000e9030b940049854500c00d542d0707640c452000b0504644100703021b401958215014400601d5040c0c0e89664050499020f04035540101c2c441c60510014070000744030380f04901c402a0791241c400d04d01913000900b90710400706400382007807010802d9030070b501d000d60109002e03020140449949140c440004034281c0c00030400c0c600e240c030803071103040040d415038014004210600404c1e1a0100e06141442026200040e40184244101c80c0311001c8100100312100c41315021b40040344615030708040d045085c0c24842d8500c001d020300b0b40701600f000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 525331106 1250 525329856 525329863
    0x11041d060c0a0e03010c090501020706030e12070326060f090f0a200f03010f0503160603020f160b0a0b0303120a18060f0f0e0a020d080702010e0d0803010303031805 72
    0x203040d205669541e402e02c0b44060b2400000608040c0e015807034482c0d0215229044200750081d28000d0702150f8500b907031810101c003a681080149500e41e0440600300d010020503a0150031014030a0411030011216101c10708505c0c2c0700046152440756106046c0545170908801c91102990250342120040c80c3c81301caa80400000a00200502d40d82d41d4111204100860b4001c0205904074194666400920000035941d801c00c4c0287d02440c0c0c6403120000b1580340011b00b00001604405001c04281c2c64040103400035044842000e1612100700005500c60074400d00c100700711407041e900071400742022083d00c41140c0c0001c0b1554080e5100b0404604610b01000501da40032000241c0801da1b4004010700003038182e441c05004100f5400c081081a00d002d00d40c01c040c1c1000410350f4100305d44051480250b60b80c0d000200e0103904000402041c50102d4803000040241c540103042200a04003084045120420780180c1039030000c0001c4010300030035501d409200364a04040d0103140b07200c0d400f40c07200f907207 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 525332356 1250 525331106 525331111
    0x3161407020618150307020610170a151104030c09060b030106080c07110607200102060606120606090a122603072d03060602150106021e010b03060411041d06 69
    0x8204107100d00502144e60b80ba04c0020800101680c064403800c0140003e56140f500303441e20b007015516079401140c295183c0f040075029920105c014001d0075a9a200c0042c0c014202c980f0303241030b03500c0d00200e111a08d2660020310045100d4032400c8840b0f0314092080048412942006032456001c1004100d80e60f07004072901c0e0031030135172800140d44018070310308000c40d8102184002e40014002c2002d0042c07088640742401d149183c0c41c0260380d50303040c2c800120b0b207842c3c04580c001d500c01018400502d031006440700b040d0340698007905440c80c001c4c5403400124141e076103500082c4880c0b103405a61040110398114211b44c01000c7c0701c10459480c0c4543c88011901004110781c041110368200304c6d00c1c070747e080d40c21003401010411560329a1501c5800040c081c00d0103004480151052040b580c110f25240b0305818121030030342d1b024014480306c0c030b14000f818406c007445c40007a039906c0704c09a880c96a03040c480d00f03010354070443d40011101f43e44818801564118600c204900c0010205076072aa04045085e59 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 525333606 1250 525332356 525332377
    0x240a05060901051005040302041e0506150f0a02070f0b0c0d051305010e031906061712030703050c070818010e040b010806010e0d0609060b0f100c0b0406020708031614070206 76
    0x100d0000514800c1728680126030000c0d500c01d0410006103541c00356890544401c0d585800180503580d10b200c00c2c17125203000d540980c06074040c204816008041a4000340160158a00c19564613554a1020401200c03054214030751407580000c00c1070f41c5110400900c500c0d5450740c10320302d00340314007803221400c0ea00c0b892069a0512200171060700c600d6805001c044100c03d030709204001c2c62030490a00d10014811402a41280000204409403120b4000350081000a81144803443c542c0c5407402100a1324000e4080c03505044188200c000143c0740c80c0280841da2a901c40d102c540040b21000105140e011740651801149020800162664401c0d946c079442082030230b100e180a2000710101c1c02e0a0b429140280c1518507109008041000581090040e00d504560907a000c0340603008110fa11965071170182c010503c84c04142c4001049110419402030280c1001418006c06445040d0150b00031240748500c454000d2072030b000300d50810080000c440b444200319081c0b081a6000c56818800c800788203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 525334856 1250 525333606 525333619
    0xe0106020d0f1205160e031204091d0d02010e011a010f08070212070303060e1e180a0f1101021507021e010b0d080d05130f020f01030e240a0506090105 66
    0x1103010314098000c0740c1004410036420402c17071418940707080000c2c1861180300c3c001501013011600c0b0b442c00241104040082807121450240307840340382030051101c940c40c40b002e02d210304a1340500c900d040c01340040a014a400216866403100c00d600c1c2101c4440803001c807072a03105261405a45d0b880f0440c0b5440000c01d080190744d940b0381c0082070f8a0302c031014441c1c081030741d00000e0002c10107030f040e004002120324114603141543c9502101208508108500001c0307000310030700103481d0120100758100000b0b001310541e5412207058503600b500f649102001e451205210a100c8000e5a040090303052070203281110403568140340000079129071a468030100d01942044421680039401c0d80180c04480300101034148041c1d06203422503c94000b4440c4d25991440c01000070304191f60300f2007606074140e101f551000034050b0741c2e003040b615985c243c030703114101552280c011706040305c100f0010320800c60460002290036052007040500c3c4d0401460009194140418407129442d10a03c0a064400840b0388 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 525336106 1250 525334856 525334877
    0x112210c082a160b1602060d0f0203010e220507091509060e0910020c2109030a150b03030403050d081e0c040f15020a020f032103070201060e0106020d 66
    0x1044665403404856180001070030144055603400020026110300f4440c03442012184d8a0201543ea4001c000d1890311080c01da021100051800a008054030f8100c8100007544450702d1107800203c0e0000d030020580608410180500303c00f4240400d01201417004e1101107005644d61019100e903803901c1044140b98441c416035076080c22001d42c0201404030040104183c039569140000c05110680b07070344150340281841084c0d00031640c0201c0b544225800010300d40302290307009031891680020001034840a0038030000c4072039507043c0300c0301c4502e41c000d86403c130042ca0194a850122681460b4140c400e40c010001040001c0011170001c00712102c9042000c1d20343d132003085402c45894031452446910500c030042020072569034001d04181c0711510410403e190300c501221540711110200840940e102c812114010300e010000c0032202e000280596450054140032400004100c206006424802000b01320000c0c2d030920452008017000240c100042d403502d40042e44070350150340b00707600300001c5911 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 525337356 1250 525336106 525336127
    0xe061c1e0f020a08060612010b0f04170604021003060e04020904020d02030a12021006030b310507090e01020a09031707140a02030d11120d0908030112210c08 69
    0x3000040d1400090000c81e12100a4030025800300c000300010600040100e000c6042c840280c0c0c5c00d0518000e11217885900780351215985800000c007650861004000101e2070048003070003145030411030300090502d0b041c984100501000308102c41d200301850007000300300003a98002d243c2d8001e50107440d10b20554403940017094070310303120a0000e5018440c2c02c0d9848108a8116140010407500b076017600e0380440c0401104003034585a10014060900900120720345003500c07c2031085030500f00c086042c0e0240045c1240311248902402944c464000070002c00007001c460159024104040000b10b2400700e40d144041d24004042c00090b240560824806c8480d2407083d0031200010307000340c060501a0304607591203907104403030304003280a8020340b4941d00005000384100003241c0b000c2c8014041e03450400c418440103403c034000341600d450700c0d00c0c01c03303021940e03420055001e0040350b900510405500c3c20403030801c511003440705400741d00300c403031198003294002107040781c00741d0141e00103540b40403034003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 525338606 1250 525337356 525337391
    0x306020904092a06030209010f0f0908010f02040e09120307051321020111010e0d1116060206071b020d1509021e1003051005190f090605010e061c 64
    0x5008010326072820704060701c0c2c0c00c1081411042c0500344515843c5903202e100440613030054010103408508100c0c04014540c2c0550794408521485e8a0a021015a900c1e025400d607850b1035016070185a000405003d404018030034194045041e070010659141101100190b611008141c84100007020513200ca100308a22410402405418219003454000070820428041c4008003203010a002c12a88142201d040c05040840030400b8064a000f0310605002c0d00d009865403007843c4030340103112070b00c0e804611640d5954041c0503140d00070072036444c090b00e0103000302c489884102d4018090720b03d0b840040c0d41e18140c409015921603221480c1c0300710407544e031018013031522000f940702002654948400112843c1c54541c084104d0e0b18030500580348800fa0f00b01d600c103584007003d2000f091814405400d12612482e50030240c04542001540d40b4549140450036a4000304070040e25034608020319a4404000461524100d80380741c601805a904d103202a4000d0300c1d2141c03c42e450b40c05407800c100248 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 525339856 1250 525338606 525338621
    0x9060212071713060503060913120e1507121b051902040b03060403030f0b060405030c060f090306040c050112060602060a0c0212070b06090c04120308100308161115040306020904 78
    0x1000a950944e100c00c000b502036002154098050145800083d148002c40c0c1030320a141c81d040010a40a001c881804940e21300a18400c95082102000c1000504074902c00130132156001d102d101140c1001c0000007410307185003000b51441d04110401c0000070400c049162140c41d40101c01448201c0381910100e0094100c2103040d40d41405510104010b042d015003003940c101c25039120800403a50543d081211900850198940650007100e04041d103003403030390040040144143c213140c1054800c0700040c5c584607040350300302c0d80c1c1c00d1110810000795130400c413180c4600052000600155080040003540d600005000c858010740f250501e01500d0b000f0702610408043c0c84c040d45640f144107041c000e00200e0180c6066016210202c0012800e01044003036505503540905158900b03501514102c400e41e1014001c960302c04c40101380000001c000e440104504c4a1380100364a252038075041c0380d01ca049068000c40e00a141e403031758403175400c28030304210b80130360303a001e03000617150080400458010485c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 525341106 1250 525339856 525339877
    0xd0c0e19060305010c080705040f0b0306060d09080c010e010204140d03030906060b04060905190605030c04050d11090f10180b0a06110f010603030806090a200406090602120717 77
    0x2001c0d408400d010040d00081c0211103140c0301d002d940e49503900222568400c600c40c0142410500c0e1041c40b003822040011a0082c4000381054209002405a40e04640c81034500321411400011035203a0307403e003801459100c003404d00085003131500d00240c0e5090320000701c91441c4509100300b81c0b5000c040c0654007018040e46c008604020035034413084d420041d43d200340150008192800c5001406241000450b001d8849012491040918100c1c041e0b90940024003040303550032051001083c00d460b100002d0b49100e0080c9411140e40e40d1140610400c02c0c0c1c05048400303403e0140b4201301c0300f13220400c40001222652880e0b00300421107982c0f100024003001500341c0d840303260304000192043d44000c581c88150350013804d58001d05107801c4a24200c40c01848020042000300001643d02e16000c0b180f00e900042070840031806200c41e081c81188000b0f10a04020380d0364002c68107010b41a0f11840443c0a0b04131400203001c1d401012107181c40d1400341410050609400110580d8015a20344c1500c980c02003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 525342356 1250 525341106 525341111
    0x14070e0102010e10050105122b020a060f050103060b1c1b0e04050606091f06050d06260d0f020a080c0a0c0e04150219031a1302090a050d0c0e19 63
    0x1311003050014060a204440c482d10419100860414000c00e00c40d044110a800700d42c0000f00001035450700180070a1808158000d40080c00b000c62010700a4210140004000180c60340c1140b9022040303540c0c07040345c40e0003412316481e001a5003108030b1150f050690000d0403802200307030448004900424036040500420b0040c0140700c2044000a402d0b8065803085607401031603907901c040110000c0c41d00c1d40c0c650b070b5107002c01d80c100683d6008070000e05641c0c2062801040440e161248111134141c460369450f0402010380e00c0241e420800e000d445101040c0d40b503d0440c088050340c009540c0d80c136003103002d00f8010001030054900d120820000084a50201ca07a40c40a0307545d40300711100704000c840a4901d182c01c0502814020101d10031500c18190100c0014a0f041c0810000c230001c0001c640c1e40d02e1149401700002c400c503640c1900400d000c460b030311380c09a915156802807201c8155640e01490003049a80a1580041d0701d043c082015626030f0b1604800300d41d52100d0072400400c598510380704051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 525343606 1250 525342356 525342373
    0x61805060423090c0102060403140702060d02041e05012f010608010504030210150605070308070314090a1a06010503011a0f03160215010303021f06091410060314070e0102010e 77
    0x2c1082818820b0002000340da86001d42c0303030700698541000b240c0c001c0000b101d0302e4141000500c0d0f84040c000603400544131500300200c0c0c0b4003e1040760f00940080316440b8001c907030785807411040d0307441c500608801c0c80e16103005616a01329010207040542141c00e030b152606e10100c03900000f5404000100b01141c005d01c1541040c0c02c01075290510784e14264003083c00c0074402689401e2005035801255039542e5007601d0401541c80c112038000014001000305521141803081e5040062a03544c041c2c030740c00014140e0310b031041c075000250403510806411906450300420905a81000c280e9045aa0319095202da500b40c01c21f44820920890304144c1c602000402408080d0f00b9080b0714803104220342d001c8070031107012040d5908241c01e0900c00140164080c1d1651034500300c0202650680503400c00300454029200c51030305007500c00304481908002c0482c0c08005117003032500b94030320080c82c3d142410029a4842c10b1440c03d070040c02884070007404800884801c00383d2003507204025180007082541c0c0c144 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 525344856 1250 525343606 525343661
    0x40e060a021201140d030305040614010311100206010e04290a0b0406090506100f030b0604090507020c010903030f050a200d031d030702090402030304030c0b030105130618050604 78
    0x2074000400400511180b5000030980d1804150300004100005107410300b0714a0517981100038081c000c004a81140d2600c20340d052030080191840e020710300c141640401d0102c410b06010410032064200e0046510940040100b0f01d00f0452041c0c100c2d4100e2680031410940048500181c02000031400140f81108104406070810781d00c070a4860808540a000d1107a85415103420b41c3c00640c0c0140e841900c0c1c610b016822400381d512201d0018840c140440c0c090a00c1c400682c3e03941044d40300c01881a01e88081040d03895040c482d082d0060030900341040481d007183c0b0020718804001030600c090140005100c00300c240210500304100040c0210780da0111504044a91210b45840a45022a090807246010005001801c00c12060742000441c00c1060702d070200441e1440103041682c05000070000072020944400390900981002907406a8951410043c0900140440034001c040c2d494080c00340004d0203110100e401c000081000456561120030018008080d10203040c551540b0062071006030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 525346106 1250 525344856 525344861
    0x2318012c031207050405011b031b02030c06270103140a0c050d110a030f0b0609040b0a05040518061f0905070216090c1205060607031d03060106030603290a0b040e060a 73
    0x50b12802e0740d0340e0304031034900b0422180c0403080350340c009d01007403601a2400c0300d21804120001d9990008040b0b58440d002c0d04041075082c0c1c008803016030956a4500c1e50507201e5503c40c0181c08980c0207103410000000419544220504064002481e00741c603003d0072038034a4420402d4a45103c020441000f030300710001c82c80d1003154861052107010a08004254090390042d2244900200003d000e452501c010300382008003c220f64242c0c16404012074401007442c0e150740c414144128054010440c4010700c0b12a41d40c80c0402c0200603d0301850940304459240b0745040d03000089071a544808111500ca446050b402d021514483e280110201a03000541070368540000c40e051519854020b00980c0d40460181603840495140b43c02c00350401030b080000b446031724040c003014200442a03212080c81c1000a081002c01e038442400a621118203100f407000010f9210b818400c100800c088000342c1303d0b603000b52044000d2502c1c1c54140e031019a07050030303140c60700039660703441d0390605940d41803400c590003100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 525347356 1250 525346106 525346109
    0x607080d060f03050d023712090f0e0106171810050a0c081501110a200901080a050a330f060b070c030609062318012c0312070504 57
    0xb000c0c8600d401009415001051203140b28041c1030b1f2410340c0c698480c0000901e54140c02d9130300b00e4244001c520002190540440900b501403a40d2901841071904a603154403d01541003840c50181c03200041010750b4214913207103948002e180e102d40c0d0540d24051140507094549201d041c450007480e06102c00d10b8040d038041403107a10301e80e00400895100490455540d00700b1079012121042c2544a129190301945140301a501060100c9000788510790b01c0c50108201480c0c00b9414244510020451340f074400090b078054038102e401400009055160560fa502c007030300c0b014180403100380b141700301c05401c8540030694546100581c0042c0100d480140700030902c2c9900d403640315241c1000420b500c0041002c480110f500407405882c2241140c4400000780100c000403240380b0381d00c011028044030011082506c10003e8004880d00c0d1503d003004a040000d100305000340390b45000198800c0540900c1505800110721a03240203040d6030104140c514883c0880c007200003a80682042481c44d4404010310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 525348606 1250 525347356 525347363
    0x40902100f1d060f071e03030f05061c2613080106050a12031d22060f0f0303050304080702030f06041b03080d1802120706170106020c0607080d060f03 66
    0x1a03610003000c00c0091054a1007545510a03010884044c0300441c1e40c000e06403550042c125024902c46600902481d211400c00c100c010a071260702e040301c00c10491045a90016007a28035070306c510244488044c003503801c03042c002c1202081c02255a5085a102004905200000740040d175554100040114181c001d11401e90150b0810303101250301d0801d024448100e03204043d281c04000c072641c0d010b0300c04403e641301841400320500ca420724181e03075802c140f004101c0c52054600c00d00e03045a01c0c0c101561410340090f049085040010408600d03035401c4181201d406107019512030325285003468a51048000207940340c072404070012540ca00c0411654006c5110b501001806d40312280d41d10152544c1d4800600496000d002c0c0980039906600569403658642803000ca482e11240d000070004030711103e060700c9035030000383c09018903600300402e2031144990009644d120362411000031345c2d6040724402c40c0d00802c80810a030f000c0042c0302058855041800c00140f00c02c0761251962020306d022440700f40e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 525349856 1250 525348606 525348617
    0x50403060605030d080708130c06080f0a0b1003020901031d070f1202010f11030702041e0c0512130c150c0b0604020306090c0c070305010e07260a11040902100f 70
    0x28041c60006001c04000055407144465540c984034107a407140402400d04c07144440182300200021114115500a01003d4803041598144030000d10b8016000802c040c441500e0004030300c1041da07a80b841506c08100d20300d00580d4481803480100c01801c040f21800c80f01c0c1d2040084503041074404214401a1a04102488040c640e100d2004e0b0010f56100c10282c08100c0c0325181c0c01e041c903c10700c40051a0b032100e1080364503008495000c50700700d034180990044440c0102c0e4003465455130b6401800220764882c034041e41096604054040c2c000f0b0081c00340426801316103003040800401c2c4480c0801059804100c0348001d805450180080484407800c90341d000390340c1d001070480c0c0341c188243d80c02107001411412080c1d5502511900942c086d00300c0b24135a02c10704900000060090103000f5441c000000903110180c0ba080c40b1102600842d8184902201405090360b12080d0000f00c2001c000d4001d0109860103840b94041001880b56100103034100d04090a1a0f01d0f482e0030003418000c2513584d6851 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 525351106 1250 525349856 525349859
    0xc0405030c0604060504030618020d03080f0c0403081b0106030503160209011215050705090402041d01060c0b0a050a0204121101080f0903070b0405070e0103050a06050c03010501050702060d1b0504030606 89
    0x4200d0380388564050800032170300c20303c41030020600d00c4d48008180c2a44152665140c10075800142455072100c4007100040c145800f000b4501c80c1103180c0342d81004000840710704060441e80c48420a00a04444980d80000120480c040900940201d0000c58122068985e02c603030704e03100451400f807400303130a0340200340340c1000148080600e14551a00c603000b0000d00143c3c1521a0440040c15010b800442005814820780f00d4640d0f0300d2000b13000502d01d0580c8500c104c070714403641c0e040c5464143e007c04240264245090007191200c006207030710112100c80042c42d40d07100f250070030090286030042d201e60940b82c0d5140e0308114044041000b04502621070000981d92400070742110030088455109a0b003090000d940000d900d0081c20703400a2160050302c068a84130202944c14000076402524654010140c14040c000e142c03040d5600014010421441c560503c40064142d00c144e0394024088e59000070811050f400c2c560280c5180c010868842c100144005001401c3c3d4005000560701d29207003240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 525352356 1250 525351106 525351109
    0x206040312090b0f16020307051c020102011a0f10020709050c03060108090703200a091121040c0b0a180602070612140106050f0c12030a0b030d0c02040c0905090c0405030c 75
    0x162242d04e901c0419851030101d540c41350540c0c0403a5080c3c03c9030141f00307540020405541f030425503070b041181203403629507483d1035000083c20741d880c2c494010440310361035021922944131300001d0044038030141c1e0780c007a028202010892038884694040e910403443d10090141c40f030079810042d401154242d036948a5a11a6403465848509a2000400c0000081702c108a01e113566500d98000c2c076802405030000b191b5644000017556010301c054140d0031070000301006d207125050110890141d1516450485181980c1c03031291005840c05003d02c06980801c1d900a110301c00c0003110200810740e0100100343c0e0361a04003030b6845286018010208150410f00081e9680ca80b0030041d250090006203000d6918158054810b03502c20070010070710810030406200d10315810440d9804900111784e00690b04c0c035050b10352004032010342c006148660050740194813410f40c000e00e9282002d4048800065049001e40255110f1a003903010700d4222480500f00410908a13034064401c455058080d100940070000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 525353606 1250 525352356 525352379
    0x1c080a0f050a020601030b15130504020a120b06040f09210806030d0e1c050610050f0a0b1b0106090c02100f0501470d270201051303020604031209 64
    0xc502c0060b40700400400100f0740c01c0b0003450300f01100b0440034403005184400305051860640ca000411525881880304600345401100300500c480c2c9039200102802e035441c07106a44018041d68404c640301d1401902003801a03000c0609141c0c400100e02401490b05e41d6245501951012440490501c0d40025004d08011034920740d110340941e02d94540c00c41d413000704240030700000108440511414448000540104015801201e000f00d16030170541c5000c04110f0318408070003119001d500c0c032210404c100300a40c000d561401b440000b0b001c0040c6903c0c01e1450040c41682e000107040e5082101403107000360081400440041c0c031b01c10031302600740e028841d0825070f0700c01c0c882c80c1c403180000380070888103103440040e014100546880c00071190b4882c401e402a8540320390800001000300082040c0c1d0416a4070408406980d00c00384444510a0000000608100c800c4041c1c144000042d40180d0140d604543c04040d650041841c0d07120b0f82c036400d00040500ca0941c4880c0480d4203024040785444080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 525354856 1250 525353606 525353617
    0x120d030b0907051204081209030d2016061104170c06040806010303180b04060f0f0908061305070503030307030b21030316020c03070303023304111c080a0f05 69
    0x103850303c0b45800c125070714000007a48000d0054490040620072401b03800c1000c01000e005a042c50300950310b8009a401401c01c0b196070341b003a406030701040c00154a200c241c07181510881d0300759080309040500f060038403101802080147c079480d5240001c01044609006512414071000d00c0100c2c0c49082016080c0195440303240074109683d4004c1004100080c0b14241c0d91604500c07088909100560320411920140c0041e0000750219000c00e21103c0c0d0300380c0c84881c0503800442850500502440d040e18283c07650f00141000541c41200c0f294041407202c03c00a000c010400901203941c0e900c1c4c0128006c0080c028162524400c01da8045c00390210b02c1c038401c25918451810024601d55101c0841c0405402c002600c0003055001c0c00c070f15100341d03943c00d22540c0c0086000c1d0300a09011074040104400f0541d101d050482c2c141c01c0300c00091b80c00d0780c2ca0300d030b01c0d0761255005030110080448200095040001d50b4000c135203200442203640304011168025150090703454803100c500901d00030041d1841e028a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 525356106 1250 525354856 525354871
    0x5010c050c090403050706020a030b13020a080114040b06040e0402090c1e250c1802040b041202040608070303030603050c010c050c101806200105011211040605120d030b09 75
    0x3460401c0315141c1a0030003a0014400e0800381d26028240c0e440000b40c1c4c2141c50340d100404d5480c4041592400c1440c0741d4140325211034000c47c9042541c5402400e0082c041c000c0440ca05000740b812601900c980d400f024038580000e12507600d441d5969194050035004540c1240204000350201d000140c000c0e0a45400314800c00d000322132840703480320105054001c060039517142c04803440300c004500350103405010458000d20a07210028100403840c90f0181e03100b504108214410170040091888040680d01a50744607440c03030302045c4850001030040e0059411005840c0500c2d00000101034165200d1011644074405403007000c44480c5c01510410410b5034040c226400c800341c00d0401d803909101941c0e01d0091801d00954460b003490f03080c0d545800907001000407074000003000c44006c4581c1c0e20018460601e00003031010750b040a031282068041085d00034213804035889c030080180d903981c0144c000b8010203060385c680d4079074107130500780e4a19151203a100400d2402039100c1243c00e11001c0706114400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 525357356 1250 525356106 525356113
    0xa0909020105030f1504090b041b05011b02120d050a020709050708010620010216030206010f0506090d03020f06101701090308060d080705030a05070b07020a12030e0c030d0206090705010c05 83
    0x451134050416031100a20700410055155400c0d03065681d0b903c6607802a6010740e48001071843c06160114401e03012040c2c0e1107004410003401c00481c2ea0000c9000b042e0f402c1144085128115480410b060000900c03541c40c00713004103031014089580c000007070003001d0302950848001590b222201d03022154143c41080028441c0c9005204560094128160400364480034002c141000c890181c220b800c00a5a20b808000710700050f0141a4100b01d89805841584500282c01d45460002049071103000c1c134142c0103414207000c0d00241360081c01440c03c441c252a094502c589010071908040048902880c00c407104c507042c070418103c20511400e003034294541c69020117034031281c08119a0386225141104c100c9402c0001c90b0000e00140041d140261480e01c5842d00c0d00c074a0316041070b44100c014040c00443d4016848600410709038440c90360f01800344c0c200003501e1400d8560a90802c2076400328290180304140c803840741d6560008400d8801d032051026620041e1306c0c1c10045405005042000d000c170761 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 525358606 1250 525357356 525357361
    0x11506170a0507053a020d0f0510060c02031501060c020108070305070c0327030b04050708030c06041203060b0c060925050402030618010801060e011205211303110a090902010503 78
    0xb01c00c3c414003251140024403081e00c5c02402c28004442c5060b80c0c1e41c4620392500400e40c1e90702c0c0ca219010700d100b0004024000d0041d454603106030131881080b40715807810040707842c041a056407414820720117005c8103840d42c00b54039a11244041c0089101140403400900034100240d107003403080c4500c6004000951710510a00c049403401c0b201c900c0d038001d2403000300230860f15040c8010080b14020005510402001410340b4082c00e01c175041c0040c6921062080d041000700d222200004660154403641c0318000c1d10840b6070541085004002c80d4110384103098000072840c04140d800074519100783c10340c10440d50340072800681310b02007200c1103c6104e4240e04414092040d0301d0250003a40d4070002c090030390740122482c03d100366542002070340544050b0f5500c2205006003a0200c000074050700f0140d1400101d10f41540d2640d41d11504041007140c1c240b55803108003000600345044800380c0d0035817100b910109482c3d060100b07100314148100c603c01d60780040009410030141c019510b1081d0140c40d010b0655 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 525359712 1106 525358606 525358627
    0x50406060e040c0902160606180c031e1d03040f14031b060304050c040f02090f030606030312420108060907030e011506170a050705 58
    0x52800e4020030020643c482040400c40d28100401655900c02c443e20752004098070341c000700084e051040000e4240d0441041c3c01d68100030303a070108203d0071540410707821910407000a100c40d030107410000704031074810341c880c840c1c2c0207600c40b90141010589125a0443e4065001b220600300d45000500c42440e100c6544490001c0a4004102003014092421000005801c1c420300c40d85000000500b0000c040c408104010f00141052002c8001990350b5000394000070200d5025030310310101346090f0700c1e001032100c2c014130010f030140d03140104083c50307500ba46500030401d2410803143c80141540000700c082c042d01290100c5000d080400c03110140300c000b04048445c03681001107070028080d10342e41d0241076907004030103418001103079600b8103403490150441b048000125841c280002a12503040340c1c118401241d903150103c61644e03640d40c4141100c2c4144c4801d030003e0010301500511 = true := by decide +kernel

theorem cover : BRFrame.Cov 525179856 525359712 := by
  have h0 := BRFrame.cov_init 525179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 525179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 525179856 ≤ n) (h2 : n < 525359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
