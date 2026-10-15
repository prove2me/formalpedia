-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5163
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:57:16.058833+00:00
-- url     : https://prove2.me/submissions/194ac8bc-5656-48df-b1f6-96805357a663

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 928417266 ≤ n < 928597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 928418516 1250 928417266 928417319
    0xc0706080a051005091f0e01060e09010b030403030216020d030824030a060e030c0d0804020a0e0c090915150d050a0501030c140d02040e06092b110f0105040b091204 72
    0x2142e00806c00c84007856040134400e4010500d000840c00c0b19501081e04903101c0c2d4849014001450041c0190407000340160303640d900041011a0000344294011300d1100810707210710410700c04a9000440c600201441500024000020f225810900b10040c1d96200d82800c0780c00702d5403200c0000310362101c40000015080356a200317050242210240200c1c1c0c8045030003400e49080428000c0090800c1c0d50944050b8003034489100d011448808c000043c9004000c40f24a01c0c1c1489402400c02c40c00c94002444220130000c040b0082d40c058403080d60380e002d404a41ea00860b05c800a40c4903000494000a210390070381804c1200400214040300880b4043d65071520508401030f20150208900380780c4598000d40080c81c040c400d5000c52004a041800b401180040d2517070604040820303a00440c2d001d00491085844000400000b0b00070031407a21403250810a449040e0318483c207990031144125804e9a1484c001010402026800e00081802401c01188541803600740194504141c54410790b003044002c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 928419766 1250 928418516 928418521
    0x215030f0601171612020c01110a1205060105180d080301120627080a0e030319030b0a03021507150c08041b06080a0c200705030c1c0321020c0706080a05100509 70
    0x1c4030340484401c17003861f00007800103e09142c004000340c0e004582000001c0c8002c0b01c00c40c1203c000d801417500848059659078281400fa410404180913104070069001685203100000502d0a80240d802007002c4007008070100c032035007800c1090b11030720301214100c82840080da12101038220124000c8030381050300651100c100400c1555100000c8120562604c03001c43e01d50b1003d443c060f40d403502c40c440c5070b4050200705024400d128030310301113000003503210b8810150700c00d14002c5c600113860031030300614440818010200ca250221010718801c1000110240b00304418401c1a81012a0031061031101c640c5007482c0003001080c0040c007400d540c41640d2240d9444007080d1244401d800c000310740001303000007079200303242042e900d02d90f61081c4c034081d000d140e007120f01e58905011001c81a02c9180108000d400e142d030781c210b420480380b41c010310050414a42894582d100c51002d010704d42c05240080c112a41841005003130749200425114100e82814200f0031034030010b00c21041151820769812200d41c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 928421016 1250 928419766 928419797
    0x150e030a08060f03062a0309062214030d0f15090c030f02070804090b09070819111b01050a18020f010c0c030804050901051e0d02060913050f010b0406020a0b040215030f06011716 78
    0x1030591500c003910038480d03c0c2503418500003300007411000d040383c0c0b0800c4404a04071110064541d1084c44000310402e030783c0100000b5505420840e01003c2d0303443d0014422a2520304031080360480c160940300307007802003805e108058051041d04100303541242d208445141c00d02000f415441d0080041a8000002c050809050002d4002c5455a40400501504c43d030441096034890002c00200352110f6003004007058801e800c511a04a42907888445201c03000120703002d10000c0b42c4650314850422600e60306250120b0a09012600614401e10f04159100e2405040091203001a042144200c42c034032501e2280d0b160750181c08855081c00d9550010540300c900005000c0e0090040031a0000c2c50220808130141565106500c21090101d154000d640c913000750b00000e004a014141c0507900054111012a1180d13003100d5201c0d1004109508524078003501094681041d0741050136070f032455040c0300c240c0d80c0102071220441a0b014a0360500d24000700518000c08144080c6c9051240c40d89203980003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 928422266 1250 928421016 928421071
    0x31a10060f21060608012d09090615030303022d071b052d0406050108040f06061814090d0804150906090c180912050c030903060405060103150e030a08060f03062a030906 74
    0x52f43c0c2c0b8244401080c03540c0b8100030380a0740c00b040b41c1c0144050b400035100f510342d400c896490780000000c1045400d01c0c480755500002c40c040308980030790142c0809000100c903a1a140c4c624000002806001c000d01c02c0145501c81c0e2008070012240300d542000c40511081c0d9000d8802d652103a04a040360700d8480540c10600002d0205401031691a03c1d524001c662507403250b0010403480c1507181c4000380f83c0d0381750419907449800122258000910310000b10b0013043c00d4035600c1c0301d41094060002080d0000b559990125400c0d100219a4628000820481c0300e01d01004201ca0114610050003c0704040c2d4420108254180c7d01005015010501c0449114100103031030704a5400703401c40e4203d06090429690324007003480120380c01940f2410300a15003086000c0c00e40d0035480b66004508107884c407c03080d60381e0f03800141007a410449a200710034482d82d040199601414101c80e9500074040300d0002c040440e01200804121003030100107104000b080014030942c04518040d144007074a10781c0303030071804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 928423516 1250 928422266 928422281
    0xf0d140306130209030a11030f070311010c03090806331f0e0a080c03010e1b040b1201020706150b0f07060b120601031a10060f21060608012d090906 65
    0x4040c80341b0001c03042009002402a800240100c1c200c580740c407406d84401d07035550242d010040c407021418050601d82c0d401010560a0144207051007800369444181040c40c10a04079142e903003003180206a10366601540b2040004080300800b40350316240301101150813031f425001c54081d80d00400b90034522040c4200321284c0030b104018490446241c0e1803e40540d40c805414a0b14480c1d443c01c41c1c10f80c04948000b03100000b0035041c0c600310705400408010000108907196040750448a42c2c901c1442407030080c0700500e142445010006884e41803040000000c02c80b58002c0c0655460802030603503101811016904d406620240108a01400d01d0120b81301036030f11661021035100c1c003800801000800c0181074999100c2c050000c3c031968440d4083e0b446d82c102803090074041303052420441c40380d40c40b41d0b800345200512030304030b545c10340741c00e0000808a440c144c0c0408001004140180a50200c00340c2d442c0d10b01c55201e11601100490107007804000c140352142c141c09a6540c0103210400c507560700041c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 928424766 1250 928423516 928423519
    0x6030b2418130c120311011107020a0308071e05061b1303080306040b0a031217010e0703050a091b05090c07030f1d0a1203080a060609091109030f0f0d140306130209 72
    0x1420245c0c074001c0c10030300c05500781c0000c65091040008490000f141550912a0001c084100083c0765488580303040d4010181a51041c5c1c42c0950074000031342c590a00c00d501842100180094980078034100a012076101c031520380391a04200800c84619249110360907690085d00065030b13134803000f0005c0c0041130188003003500f0400020307000082c0100100c819900c2d100648852a0f62075420004100221090180f43d11208082d8040b176100340c4243c0c000d6910200d150400070b0702243d01e454a940160480d4081415601d40f04400d00803418101c0005c0d4000300300c441c455080090cc0d0b680508480035120588040001c002010101d1f0b07000000401c0c001880500850704040d00c90801001403c0d0784d55094001c100c0003400b00d601c0f40c1041c4200d03001c48581d603650303444035800c0c41d02c030314003500b82d000d880407161405104680d42d698041c0601a05441d824005003030300107119828504212901904100380064036503440201d0075500d007103030350000f400c54640c00c4840d82c600c1040000c1c0074512045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 928426016 1250 928424766 928424789
    0xc0b2d010b03040506010f05100305061903060203090c0d0807170d0509010204050f030a050a110a1e03030e030f060f0c0403050f06100f08030f090406030b2418130c 72
    0x900c016190700540c061805141500c03200e0313880302c0c11240301400d1031299170703041010007210740419446a40010303003201000b40039030001e16485c1d1020740e2105240d0415104194000b00b400b40c201c0080000303080000741500c0e8600121130316241c1c43c4030f60250300e1018040f40709c4035925041840c050405c848064054445c100914208102ca160003134002e801514064001c05014440510f8005000002c803544030b8010014464590f07100c0300c15050b45107005800c00101c081c0891544600d00000710706412030118101d4052840c00d005001e0101c26100038000c0d0003000e2070300c900e1540401d0043c0e114207003154078102e0b030b299917900410b107126641c00504603000320032581043c003001045003801022943c207114500340d1541010342c20101c59100d5608607620400c0006942d040760400390542050040000400380d03075076140e000141c1c81c111407a02c00380c7d40c0241e041e0014019111825000902628000403500c62001514003402c0090080190b02404002120030011140315080181807107800c2c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 928427266 1250 928426016 928426019
    0x150f030c18022506201b01061d1902090a060302280c050706050c10050606040e09161418190615090806090c1002071a040509070c0b2d01 60
    0x200c20f00001c0e1a00100d44080c01c0040316084904942140c4642a0654809510300742c807695800c140b41090200e0541c45540707a00340018042801041c900100c0c50360981c1180b42c1c0b81201d0390881c0d22111a00c1c1042451043c0060070032a01e07888400400d5516900b401607803104056030f07a0100041101d5451a030380e064401da58001d542c8051460302c4180314404a409854840c442a0390314000c0c803e603240340e5400302c0682c01ca0941d0907000103070820000780c000c500e459100d1500d140c14034001c1b607040c070007a40802c40b0510340f580001015002070100e802c2414061840303d0000c6c2c06e041d16004000702e2101c105d030108280b0890b1500b95441000303e4041040499924000b86110b80070700d01d04000400c1218100003031000f03010035501d101d14580e0020b48091402481009210200d0364000070031071203000c1d404241c0036203c070300c07415007118503000d01a101c3d45484104488060b0092401040040e007058a02c000744e440d5420580000c220540c6000c8201001070300041c9016160413896401100f500 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 928428516 1250 928427266 928427317
    0x7030b0112050c010804020303030615090628030204050d020f270601110c0a36050411030102070201140d3b0a050d030915020706150f030c1802 63
    0x2040040140300b00282c0c1c80700030540005445401d002c480213034164008000040d201d2030075450041640109000982c1001255000f20ba015001a001c0c803408d102400780c2403480040691051030b000f01d16150540c40c0c9402d0402098880c0704400e8002e005281110002a07140e03541c2d082c040c0c0508405201c940464130146407034080c8007080d50280e02090b40190350040004020500c101d6600019145082092805001c0c1604281980e040554402c80300d820700002e1002c8a8100a680a540307808200b6003410b007400000410881d501900c41c2e8410001e02c0010707604452420940c1968a80054a07804461034140c00380100940085050601d00c51105245855030707090f074426210f500143c2070500b00400c00750354882d03141303130050410340c0980041d100181c403d03040610054070030508c2c07200013040c42d0f00c01c2c82a6007042d401240d540f03448041d402c013141801d802e0310f0010801622541c0c0b03510310b9603c03680308151480c001d41c0c200d440b80c482208080b00c0782e50101c030001d401040601900e000c1b84074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 928429766 1250 928428516 928428539
    0x909021201050a0506040f150e0303040e0f010e011410020118030c0b0906090304030809010203130806165705010e0d080609094b0304120507030b01 65
    0x5014464010240d000c9410f00b070080545041e50085c0d8000d24846041548c0e0241016800f0844000c002640c00d043d130040d1406d01c094001007034070504003100c1d401c000c842c1e640040d1058000d120390002c04001000030040c0e900d80303030515102c241c070f0940411001c40c004034090059050300740c01400c1c0c2c84030400c0c10194041c0c0b0222000d409405012041c0e100c0003002602c401040d0f6141c1d201344e00900050001c55041c60040c040081d0500480b443e101000d008900aa0050b5000d8100c03508482e0411440700d520071040340340d85085152040c11444007004d00207040182c0518200310040300d80f5295603c404041c84040104403020201e024180502013200c60324031a150102c40035404c000640300100400030700491400300e2500e4030b0005681d0101844150309004105190510805400c50300e07a8000b42140c40d1024944850201080e034441655421a00e0314010f4580548600c0c0340d070040f41c000841590140c503c800c40c0c0700055801c5040c450302c0d00b58150405480e0402e0701000160210100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 928431016 1250 928429766 928429769
    0x1b110306190f09030c030f0302090a0e040506070c0507120f0506151302090307030b0402040906090302030a09240f05121302010806010302030f0604110c010216020405060d08190909021201 82
    0x14440141001c582000f500c03002d903c014042400400300c000020300540d002c00490205d0314006080c03959a500144030740c001d0758401030010790030209200910200380056036118801c3d00f06039000843c0399841c0b5945600c0da105110144c82c1c250103800400400c0030710701035219040300884502c0d05002c29601f00101c07030000442c2c410a1580449000b200c15802682e10109005002d84a280d142da1603600d4814401403040f81c0c4155184402e80018555100e00783c0f190b40a81e0003180c030340e510b209011700500b4140d0070a4600451803c0800d0101e4451201c1c007454200504d018110f40b00c0300c0400399014003076902d0740f010a00d1094108078010300340c2050b000804d4004d90311030900f030310f540e030041d03040307110665000380014140d41c0050040c2c00c0c960821103011120301c002a242031280845c1d5401c80e0003d5800010813012161007200354501402b031a80c002c5800c03105404100e200d0b90300e50100d44110729000c407030000c80c0d4102081d01c900030a5a0001040307096419555a034070a441014103507801d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 928432266 1250 928431016 928431061
    0x40507032009031f0c1b240f02270604120609050a02090403020606011715012a080909090f03070b0a141f09060515030901061d0901060602030a1b110306 67
    0x68480340d141c1c0b45052400401c80d1b40d0030241c03400c241044e4428610f52400c1d000329400e00184c030761464018503441031009000e003110310034140c103000206a280d07886914440752014030a00d4280030a00001e0b1280300880c05182e4404e10020304603c1c9841c0143c04c0c07021080300650300c0140d500400060603000f1034203030300c241003d0ba41c1120003002d04082c44144034096a54003862010025200d1040d400341c0e080c0808503074081d00c42c6c5d0407051400030440321a000c0000485400030081401d2806007032005103a60003642100161007040b8445d205c040c0e4a000d0300802420780c81503280030800900342d6900c01c6400c28003006c54000c85103056441241140701d4000a903007050700070400058030761860311031a010781d0001400955206603900030160743d50000ba186200555075030310f00040c2509844801071924a020900c50030924000440b40d007103400590010040d90030810007034250a6200f8140070b83c800700c28100032192015420074418080c0405823054043c80741109001d001107003401e0188409a070f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 928433516 1250 928432266 928432277
    0x32109330c0c0105181201110d0e010b03070e04020915100804030206060d02090606180301020403050f160b092211180a03050601060e0303160c05040507032009031f0c 73
    0x507020b004644500c50781031603286510034010003c00300d250a031000444031109100100d000240200120310903801446085025030751032283d5004d1510030f019640a90030200c026207449840c00a480c01018802807000748030354925400600015080001ea00d044503014201b044425407a40010f003c3c0482960b00b68054403035400096448e10f002074007050003d0303010b4a000103540b2840c1c00d0020710f4000c2c44440a202c5070035181480e40c0e40f024030240005500410040c2610400c203075180c1d0402c030590385908009000c0c0c0005010201c3e421088407507440c1c0a0b030b4180d007014142030703d4401c3c008440c83d419a40500300408500103a040c00e01400d8000b400e40700c968106c103d004200720628005100081ca540c0102c001046640d001c1c0043c1a00c10f400981500d1524606840191030140412421114204142020300c400c1c1858845c05500c0507060504200c042c1003410200c81d2840b1a40805000080008506400d61024410007010b50700040803010200c407025000303400b17880b6000c0c0c00c2c00041d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 928434766 1250 928433516 928433533
    0x5070b0315090403020a03050333041103010e0426210123040903020a0f030903050d08060f0411130b0d0e0d05070303180c090b032109330c 61
    0x42d1040000303009641c103400078213641c075660350301782c0f0690001071980300c0940010359000c0000d40d014001100311255400000d6040b0018010042190040d4502c1a1503400600050000821401039290040d030801800e441d00c8240c405e01c081980410190810649800300d00c041123000000f4541417916078500843c001c580e00c03082d88400c0c60502c01251004400083c0010940d03050a600c10003100b80a40f044e1002c030802515003007000700b4002c008034006042c8090401c20b2002c140300e02d000702e900a140040b25414441c000034442d000800d42d291240341d84000400c01d00441500f00c030b100303003142da640700e01142e030310082c118541e00540c03404d4800c1402c0100d80140e80710085074943e064626503e41c40d04000458500310003c01843c1174030f4407060703450381041e801700f10a10500c800800e08a00085561400941818141026000303004014000c0e0031001a103c007402e000d4030030001043da1010f0402c0000e000c000c40410b001104440e803191240c9480404000c1d40300100030361500c9104030740d00c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 928436016 1250 928434766 928434769
    0x81005030f0d03240303020303191119120e03040513090201050415050c0114010816050918280201090605040509060d060e01060e06150708030f0c040305070b0315 71
    0x74501010495466001554010300b0540268000c0700303a21583d42e03040303402d1161160411201c4a9580081e0090717070000c401c0045911130754103021015030003004180706d4440540d0303440c105409608c0525200c0411320760b0b040d00c0d05204e03189a4017155840b80081c003450720002d6503281c90354031a0288901908039a0918013040002c2d000c1c0b20105641a5112843d1030f14100709981c0c0c4880407444041045002c01405928000901803800308075240da07542e241039450300102c00d20340000840c501e0030484203031000b00900d40d9043d00c4580d110300303000075041440c51002c1656042040c81d400f0380c00400c2503203c111021104040103000c0551017a01c030b041c0c0403034407800e090b00c0b01c2c0100e00c900f40e800305103840065164101402080903042c4240d0700418040c04c811005402d40d0305c00e402c0201c00700016010042203150004100b0503503400320b0f050b2458041e0702e40b6040480d00c4000e0512604200072404100d0290b03481044400454010301555011925014080b055a0042c1c03503c1c070652040d1071510205 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 928437266 1250 928436016 928436023
    0xb01090f020f0904180f0303020409061401021f0b0603100314030c0a06020703030b060712030b040c12090c0b0f0301080d03020f0702040506060d0c0905100f1d04090c0608100503 78
    0x4011044140d0700b040f8045007004003400301105c0308007000b40380c00c000300d0008070003090304200d2a109840c00b6881e9070030b01010b00d08171b5055a1003901d17540102556084a80d8011400b1000c40305030302c0340000a144a000d0810142424036241e039006000042007000c4400b100561005a80c071580032680703e0500c1d501d02d150b5034091010204260b0300010104400600640e004040b02e6100b401d021841346203100004485030031111050b074030b043c2c42c1180001c03001e074184a180e08100c41124204a8000c19140082c01d01480c00c0d03400064640e0b40c060841400103a1808600030004412525039810300c103001101c654100b803013144001d206040280802c28060b0080c0c1c0c0c200c0900c041d510307042801c5d0303408100103410302501681c2c10400030004568049014003822602a0058440d0900c440c43d243c140030304100110103240410031101c000314500c903071081240301e20402d2241c0d03202d0800c40c0034000800400c25040002c1510203030b10800114a40c200e00d5051207034614080f0a00201c1e0707118140350300c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 928438516 1250 928437266 928437277
    0x9040605090f071d041b0e091b07080c1617120a030b0f060c010614090103080a0819020a0306081e0c010f050702031209211f020c06040b01090f02 64
    0x32103182c14000101460303c02c04d41c00050607080e1342802d6030601d40b01c2c04501280c4c80b40100015200244540107006a004a21b40381c504000b07645c0001c1a181a40c40c241c202c4a603c5004156840001004420302007036405440b105640c0b0425901c101c8800c201d20000ca1149205044500c481450180010301022401c0c0d0302c1991001100c0c1e15081c05804110001c00c1e05419403a4044d40300d03180300e0225242e02000d48000072180d800010400d00740704080b18440280740c0d00c9440340149400600010b80309034142c855030012401e02442d42d840d034110700241c8441070894810154400b199002c0e4060b85070700000111110003003960802151201d02c001140c0b0a21140c1d6890750010f11034040c02c2d446251130910485251800324102444c56000034100200c299100b211804003240e03580741403402c10b407000c04081562409081003250b003486591901d107800440c4c0c1c9400220032104100b6030581e011034812050800a640f90b901c0c1914018007591000c3c01610340c0701d0310b0118005540c2406108840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 928439766 1250 928438516 928438531
    0x27050a0203061206073e0607090503030705070302150409050a0902100807020a03080702240a0b19060f0e0909151501090b090102070b0301300b040f06020405060a050904060509 77
    0x40c05000c1074a0359960f11300410251200518088800f00300c422042d910321b44400104d2009030a407820032141c0102030081030740109109030810018240001d0300000c50100312941582c41e000c0883c1c4100c23041d81503000701d1b48000009414841004990103260f804241c169200b00d03030201035041c807110201c40c0030700300304c1c1c041000d030340000e914801190240380190307030040c0c49104070f0707003070f0000d02d40c0858000c580318401c907075030300703054070034881f083e81d980c0030340315500c40c043e80d12801c000710303820700ca40304c02c01d03103200e88410301050318210002d05109207040d00c2c0c05140608000782c103007403911304103070ba951600035001403070701c0c0510100344c0c00405070b1070a640c4120141c0d28404203d042c5607030540298001c66466055110780440024022907001c0070754002d00309541d5000c2c1c0d000fa40030006240142c40e100100601c0110810b04000400c00c4140a030010380142e55038414000f90700d0190000e10450b048141e2101e80400d200780810381c40310007031894480c1500c062214035680c0c424410741690503110320 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 928441016 1250 928439766 928439777
    0x31c0311090d1401021c05040614070503010605090301060b160318150806031009030f0f090f1421010204050f0f0108010b0a030605040603030c0605180727050a020306120607 76
    0x105002030079a588006030200014949106c4680301820460500380d1455030648650403c001c0c01002d1080c031604542c25802c040350b40c0b03826000180340d444140124000e0020110b0302e60183d0710250f1040b4060f0200004031583ca12121f100d80c0b203080b011704000c80000e5141b15a81642e503980440c180b003252176808060034440c1c20510b0a40392400004c00960309441001c2d40500304101901403800c5950180e11070b07841d01d0a907444000d0955a0284a036000d1103089a810406035281402540c11035040360b40503054940b0481c001546040110380c0c07221407512443d6400340c0c0c000194001c0040b100d040711190326441d030110a00c80d0401d28940014086100440100254078508000b0070140500d0329000074020b486100003411580383ea00305600140321032144c00304200c0f040c4a041d8024070700d041c4c028000c0f8102c00ca40340d074406543c0580104210400e00d558070308401036a44160304005460306001c10729024441034000d402c107c1d5820703c80c117682c1c64140145000411207a00400e81613945 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 928442266 1250 928441016 928441039
    0x601030905330f010f0e0f06010f050c2506020a08090d02130603050606010807050c071401031d0616050c030d150b0d050402010201050928050c031c031109 68
    0x40703580c0c011203070300c0702015005240031080540707403070b524128824040c048031050f00f5410314011180440b9540c1004184150400070304c1300903400404120b0f4804824a4051182102c0329421913070340c0503ca0f00c1d1007581c070413407456000d510700300722010403030300680200f0113141c1d640e642c0c00300e0741c4540f055030260038080e0400165500f420320070416144a8000750088682480301503950007181c000c1d61054906801a006005c01d641c3e01ca0300e8aa040805840c01504002c400250f40d07480c0d140910815940048001c4002150b074000d4101685181030b48900800800800e0040303074450340115030350390000084424020115020740d00b030b01d4040c0c0380a0b0003142011105031541000304050046d0b0b17407000104c4800012101008401049039400c1e2107800f08a03818244006400d40c0e001404d00303403250700108069004e05440500c000c00400101141901c85107850030302d181891003040000740c0600550301458007007200c01c0070440c040003e69074104840c1c901500c0186841c045d620704039900100f03950a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 928443516 1250 928442266 928442293
    0x60c30120c031302030a05030a0f030b101d060705010603350a03180303020703111b04051003060c0809061f030318080717070803070308040b070c05060c0d050601030905 74
    0x2550b4002c2d0312a100060300c2c00f080d00004e14000c3c142000b140c84e5840014401d8410303620441040301070517a82410320140c90707050005114024403284900820280114404004200040782e40078460050300c0f0640d20704107030510501034005404280c1300c0000c540b05411f80c9079a0117095002c600400c070001540c01141c00c440315610381c0400000340825854900d92052414140d107006900340c440d4500595442d018500685984100c81c40e0029542040780c00c2c554005175803030f01aa400f41e08a034001615542c1414800281c0243d4001501641c40c1500000c1141c1c1c000903440d0054210a04684260362500c0c040001e0341541c4050614042c402407080000a002e103880918010392101d5803000b070740c0c803600220700e441c2c1309500601107021400a02c946610301807041101078031041c8041d40c5001200c0d1406008140c001e03000400011045001a000500c2500c00c1c9813820380c08402d0340c50b907080c10414181a034102072005100240740c1000f254196000340f045030f14165000029010180c81c569 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 928444766 1250 928443516 928443541
    0xf0403020d1a0c0424140f121008100203101203021c0f030e0102090a05060913020304060b01031a01090611030d1503030905030a0c090b060c3012 64
    0x440441d9070900d0404005000c400007141d10340303d02c5031094000d840790300d80a1144c40e42e900081841c0c1c0c0302002da000e0500d44550041001c1c0400c030304804800c1d41d502c1c8a02001420b8468403a441c8044084079040c07010b049a00710421302181c07420000c44010b040d200c9400c80c1240b01c1942c0002100200203800c11510441e50b1219a500307000c0d005543c1d000b408400e07095000c0000041d00000105003464a15006405128008102c80750388000c60510003100d003c520240e202e8028144591004036410a403030703a6044150b514006000019902c900303141c030b440f0700584414008140400d040500301010031071070119900260b0816035580100070700d00075003992000d032043c800d2000d030300003000150440a41c41c002c2c2003c1282044039190218034500b80140710100c0394224501c42d800910340f140224003846030141c01d44040b60400034018070281c001900358420b0f188030384818010703246460075400014600801d05440d07030a40220800c1a41c00703001146c8169501c801c1c00c0368044d0f02150108107045c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 928446016 1250 928444766 928444789
    0x2b0501060215010e0103230d1e020a11191d0a110a080f040804080106120c0906050d140307020d061409010501180e0a0503120907270509010b0402160501060b0f040302 73
    0xf000345200c5c030500c514040d41003240c0c00300c1c1c88012818420b40c02803200c03010084d400e002795452000c1e203403049160303441d41c4081e024410118400e078034149400c0a00c1d5201e000e01c0000303011095804c07a80d015241c000301d14200044640317a00e0945400c42c0744815a04250440d003114100e95030340c0010381d44e24001e02c0b1400e20080c2050701c060b0400c0c4004104101c0920481000c0e101501c121041c1a0f400d180c81840d030b802030f4201d1600c20f81005020041078030741560a205485d40321003a140708021008004d8918040c280029521103040c2c4c407040700b80040c40e40800d00284052a000182e5a40d910205090307030300a200d49000180124401842d01040d070b8400060b0802d428107482e90404141c803907910f55001100fa0f4103405041405200d25a80c040045c00c008000328150000c5202c6003910000019030315000041c0d0440d2070358006581002c00791f1201e04440c400a04c110340b90200c101d406d48007078204100c102d51542c0b90180110f0003084800070344800c0c5840d20304207864107080d5424002c0c0c42850 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 928447266 1250 928446016 928446053
    0x201150509060402181c020f030a0506010605031f140f031c11030f0a0513060309020102070512030c1c0215041e0302150717070e01020a06022b0501060215010e0103 72
    0x151540c071720007a950f000002019031040100c0d540645800e004100201802d900498420b82c05149207600282c5d010900504551035800c01d0358480d82d5441207225441218000e20f01001c1c1d0403200829030500250b004902154291884e08560443c60300f03050351000a071b118416500600d9840409440c490010f0042038400041030b0fa040079001103e21340f440d00f05420000215502060540303280c007505103900002c06243c40d003840010003d0300042d455403c0d074000c9600031040c5902c5000c5140d410021212031864041c12078007200b902440350801d690758041100b00600460110f10501c0d1101c0108600881d0092a0010811004004407550f03030b05140d021811b40c022181a815850b0028501c07034400d842c5515541100401031043c803003284d01c000d003202c1c01c1c4801e0322940182c1d6680060742e03401c4594419001662500310244041115100c42c005012500c1d6070341071400103c8094004504840b1241c080365036003110340418a10f407110034015520303c0b104410040010403445456403040c0c0d041d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 928448516 1250 928447266 928447297
    0x3151503060911030604150b0d020708091221040501081f030c090615031404030e012f0f0a1205070204021608030f010b0307020a0215280201150509060402 68
    0x2e4440201081da00d0340344030019450008010424142094020402900c1500d622114101d0815200a805024194120064075401b20fa034804111451040703034540c6000404482400840441c01a500d11501c2c02800061546a1840d03005244100c155019500161903031b000c9541d460851300b0036203100c0148040c5500c0141400404100f0040308100900004400440c036141071591410030500001c90070000c141c50049101e00d103503c034112030764000340e25281802c0d003031460300012681020411030400c10402110702d608001c10711300603941c100300b0555041e50009802500060388884103840d001d070407030644440105069110341d006004a610091006060145141c00071800e0b40300c001c030840307045100006100016170900103990052212403110741c6103140500b0002d450b4154a81d00a0040b448680341d21030000101c82600c45d1103070011010700820985091542030350b460030208401552030b2404141803000e150788d0f040306803900a080c2c514561541d806100c020b610480050b0046030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 928449766 1250 928448516 928448519
    0xf080402180c1308030f0307050c010603020306010b070209010f03030504050603180a11120c010e040f0f1416020a0f03110a0c0b04090c050c0c060a020f06090d0801060315150306 78
    0x565081c0e4001d240d091080ca88070b114034590281c2d010526044105154805d22903812000781510450358020298a0b005803240000d014641c054009604000c0d450b01842001007146c01c482e0b0b0107812514001c0360361f000c041e640c54000c40c0c1040800d01001c3c00250f02040140441c0c10604015600110f002e00248150600980443e0400c0b070850380460b80701c0111402c00b215840c01c0d601c82800130449070007901004d000e020010301078500c4c182e8010300558450700c4c4020300c8542d50b84041911180c1100c1070080c0400c01b9400c000b407aa08545404049000403a00c0060500c000341100c1d0240d4072010b6081c4810302e64034280c88d00d0a1504071402181b00d07000c2c0d03502c0050801c861440040a11a00300c2b62030f0707403c2c0b0440c071050f51516000e106c10890b00b400326043c00e1f40002a004401ca4017500c1c0e6907035940001c1c2080381803040780010070140f88104d41c20700c040404c0c001210302d4514031550f242c94059803694412425131b0928036204204200802c020311541c56000c4400c21a0b045500300018040d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 928451016 1250 928449766 928449799
    0x60607060e16090b0901090b0a1e1a07050c01200d0c0506060409030203161b0f1a120604151701140601030b0604120f0204021b010f0c0f080402 63
    0x32501400c8041c0c15800036121440c40080c400c200300b000d00030f6464184076009000c004078070505030500ca960a010b46801c0032040c075441e900760060181c002c02c42e140b0092115080d80220030706603489076402505410512038010b290342e800b40c1d01c2195001001c0c15041000c00011100c103040303c103803c204a0301e00c40861000440030455518540e0340340d101d80300048924182207061400040c10305002d0360030081103c0000c0e501200711009141c2d02d0544512160540c104200010f41c041005081c10388038400104224065007400030444000c2d07514230380400c08034514440c8074091030010321020030510010503402d18050f00a224040b0341c0d410f03020034480d0740e98072281070031409185443c2d041e55148181151140d00034011540904d0030b0070148084080900841c03018410761003001204407220a40d04100005035900e6040250028015034550320740100e60003451200d802030450715840c0c04111a44d0044501603010601c2c060b807185540c00c20074480545054030000c200b01c0e4401c40d0f034081180c48 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 928452266 1250 928451016 928451021
    0x20a0f06110c0f070e09070e0405010e010507050c0f0313090203060d020915120d0c080d0608100605010e010c0b0c07020105120a09020109091e0e0c030f0c0a0f03020f060306060706 79
    0xe000b18004103003181c0d40c07940c858103000c4690003e0180c0740c1104100413061100140b454110380300303a0310140c000c0c0c0c0c990500d14014004d11040158950806090010466000c000b0f0071a800450059500000d03580102035039074421960140c11a5615100c20002c569065014550250b00505520540b0500343e00042c82080304a1341d000d46850719019000803400c122015041003c01c60009041c3c1405400c405411301070b1040004100307074400100d61315403a2482d0084402400c40d00112440103544041c0100a0306540c0150b600284031a0f4071070649d5031040300ca0700140f035041007100019440e40c6400c440c440d0b00442c0b0580c180710702040041000c1c406000c507140708012184d40015500250b100040c110356003035002d002d00340c0c1086110314904001c40c00c89903c1808100e400100115510210b270704012449203401e9150080420b907080040000c607080c10b03001001c8585640107a01d5249585001d5614000030750072001200c2e000070f150520100440d088840184071908200e22962000103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 928453516 1250 928452266 928452277
    0x1090c0905160518061324110c01140c01110c01050a0c110601090b0a09021b0c01090f0e07030b031603020103050f090627011103061005040303020a0f0611 68
    0x445940c41c0c00700241c400446004040c1da40300d03840c0c03031480c10602005a91607050607243c0e9a120760400a40b040c06500e602106000501c3d40e00b0748013881f041603042060840d10440050404214910480481044089201585014140c41d141401c558500035030b40c0a421000f1500010740d81d81851604c6d40003410081e020513415100042200d1621580c998203942840b1840410300210500a18001d2004103065054960300e02000402000400c001404419150b1100081910024203503884000c400c5041c3c401c4c4480404403110314844000440351065070b44074001391203480300020f00c1072200c81100d10f904581146004284000190300283c00c118600c05044041190110200119601809140e601c003071b00b8000c0014514281242c19200c1c00700030404102880d480004545503040071684103030740142580204407031021102940860b0740103881e064425000ca905180c0ba6a22900489081d07990541c068010302141e07070780d000700c0d90414000840d40107441e208018410880d40d0050b02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 928454766 1250 928453516 928453529
    0x5101a041a0304030804060203130f060b011815030b060706020c03030109051e040221160501080906150603090c090c0d051b0a27060e09070f0206011701090c 69
    0x6640d00c0c0380c18640e800145007203a05a25200040c0100400f00383c1180303076164003c0c0c000300b01507641d5803100400d01070804614401000103a00c81030040078081240d1100038120700c00e032240d0700301c110f0315601560401401c3c410b800d1000c0b103078071092004500c070350014283e004000c1c02150500300d591740c3d00300030303030304800c1204030558400b00c010400340b100d034040c0300d41104619685103004980d51188454010300240040e00904060b0303814252640c045076a0400001c94809482c210001418910305d03504ca00e10505d4001403812000ca09100300124216004035510090402d010840030103000e4180c00c0284494403034090482d95141a4442d501d0841c8980703403421140341c1c1c500307000021718100d81010340383c2d030300020980c4440a401100d0074103c1d0803150060822848081066280142600c3c0c141983d00b0040c14805000504640100744011000c400715400a081e507102002141c034030410003140c0c00142c0c040f5004100071030210340928030010151001044015680e1291f4541c0030880d800384 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 928456016 1250 928454766 928454819
    0xa020307090c090611031b03070b01090510050402121f0905040305030105150c070905180a05010606140c071202040905160302010906030b0108010b09030f0703030e0103050f0c0d0510 80
    0x5080702d541c031141c101c0107400942802ca41d01810b42070420780d00d0080d801c3d030a04018102c03ca00e46d428030100162904580d2100100c1020741c2c4031090040940020786074054143c1c003041000c101480c19000365213411001102900f02c650b90001c01650244481d900040c0100c0608008110201c250203128491402600d803155654903040c1807184444085107610007642c0c003031000f8022840d010418904a4200714008100d58403a400b100962003480010b81c4058855911100b041040c190049001c0302c2c01500d405038190340003107043c4200c0c4030314464088550080303078042c4041e11524048a00690029100166040c625a5540c1c64580c00a450508020840100300210f42c1c1c07244400e80a000545800d2208842c500000707058000d040c0900040c60601091103030b000d46007045600314041c40c40302162241c980d030f400c020f003200c1d20119440d40020308210016240c05850080030740240c286000c100d2a013401c1c00c4240c0c1c01001c001c0d2038105d9074038070b2120014170b0054800031f00b51a40c030100d0720b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 928457266 1250 928456016 928456031
    0x20f0906360906010c020306160509030307060f0605190b0315090414210f07140307080a030605090421030603060c180807060e1504091a0306070201052203020a02030709 74
    0x100600b081009261904104160110000584001c07403000d42000162494410540b074032001507446000b0341c1c121640511002c01d410b028410741d45c001c08810008040f003000300684403010f015503030321442c09044058902010801003044c44030029940480019180c22400c1c0c4070800007030b0300c60360944c0d0a442c40c02542c003030703e0045d0b1010b000c3e24005100c80d501e4034050310031400b10f0a03003900401c081c07810340f00c1e004504070050201e5200d000c0b00c0e5040d084141c99032070b03845190240240d0009000e40f00000d2070a4400700303090508000e0540540d81200b09043c8404800c00e001980c41c45c80c504107000c03d078603011300000040030390203014070240700e82c3c4401b421800202c0d1500718513440e03a4010840380d40611400c0080ca0b8215161103550310342900d0b840820030100d007440b007852085a0220070400d103231141d1b00b40345115540c80e12b1004241202601e0a907101c80300704078240d03001a2050290b0340c014a90010400c1c540507110f8180611900613568460801d400090030f20f0703c0c46c1d016491081e1105071 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 928458516 1250 928457266 928457269
    0x212131a0702040b011e031a0a060302030708130b0c0d1407021f0b1c0c0b12060112140a05060d0c17160305070623070f050606010201020f090636 64
    0x82c00806141c2883c3c5550301c564442961300f2094034a50686082c590b403081c4407000840e007100c23110402000500300ba080c42d599800010000d500c201d0f20840010181700c0422005800340051228441c7c0252a40542c1c0e11003040340c0b2825840b0a021280c0c5558919001e800c00003540c00e914803410b2941c000d0142005401200c082108480c6407000c001803a1118a10f815070301d4a0502000f104c4d114064406004d01d407406c2c003002c21594000382c1c80329001180511344275803a684040c0c483d030400e90b43d40020414022030042601e003880c1400444141348000122002d146902155002400404140785408652108140600302d031300301c3c4268001c0c4400c00d11486108000c9902c88400c540d00d4102c0492030340e00c0d02610307855103028100400c140110701e0915003052110108442e0748201d241c5555050f103240ae441181c0d0a41000c40eaa409044c3c0012242d600601c00d440401510100b481e26001c421020000503500580c4c0382070100a284061541003030103944181320061800d036104940307090080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 928459766 1250 928458516 928458521
    0xc1b1c02011503051009080c0730050628020f031e071b02061e0309010c02071503090615170606030105061f171e09030306010212131a070204 62
    0x191510840580800d0030030000320300250025005883e010001b4581a1601d0701034441d1007105500103240c894640d0218018400b140f0b11040c044030600003040503071202000e000000710b03443c0701510030f40056000a00800741d114480341c481d0385a200c0f034542d01c1030340348400080760800380e00910405808003c0258130415207206034942d1542040380301c501c1c640400000d0883c0185003140c100e01704c100c0050000c64940c2000d959100c03407010ba03054120503882d48607902d141c00c2112418070a42c240030a80103081d002050490683d0304100c85406282c5000000fa009450b13610300031220a80e0390030140280c02c889a0320390340a00012007d4a24000000103070520b00800503104902c240d01d402c007441003640c0c031051048184824412040e04206180101b9221800610328508101101c001003081e000300c030100800c8200007085000300540c0b034030646c096807400125192409070340400c00500440750114094801d00c0401f5050703060303080e1500700d070701035235154050101d507200f001146200842c0343c40d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 928461016 1250 928459766 928459781
    0x60e0c0402041e0f05100f0504030507090e0d09060801050f03150906160f0f110a1a070306170309092205031b0c0904060203070e0415090c0c0b0c1b1c0201 68
    0x1034120741c9517030400000518000d081108001072104240c3d01000c454024001d0394000e40e0050151110346a440e030700c0d400a0328080080ca0040e005000000b4400c1d1302902c7c040007a11403d9407447c8a40e805c01050005009402070a07a91520030940302107010010540d44921031140703080506140e00706922104d880241d400142c80500c23800b07140092003158801000c0715401c0700ca281c40c1c0300d0400094070070b07030410311100e00242500d01d01000700b003069501c0da024035000d6800c5607020400b040d80c9406e04055889a0201403200d60000c214071040b03071811031641a0052150030040068031401c0821203001c0308050001ca8294001142c41d0b41d00d1503005d003201054100c1c1030050540c4900c204000392041c10700400c024400c2d036010002c5103941c0d01c0340718840003000e800380040010320038102405905601a11841105504040c509040303a485003258104142d4440e0f85102280ca4080c000180340d0000408003603104014040c000c10004200440c0030082002c43c49440100d071495002405d4500d40b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 928462266 1250 928461016 928461029
    0x30c010b0f060a050d15030209040f0c050f0a030b04060209090106021005010608160c06110708120c0f030f0a111b060703020a020304140303040504090b0a0c030513060e0c0402041e 79
    0x244583c40d01960041c1c00c495002c0015107001030464080e00c03e02250070201e0b000650080d003441c042008001e02d190381001c2140c00b0f1140e20525655400804c000c0340e1004000703a402001b104e90400001c4c0c120440140c01521a2001504088650010500c803002c00d80c000780040c0d00072203852084034014070130350380500b0f401c0c0b030024468036000c09040d80350301c50134410104000c1d0382c050304024840982d021010f4a450702590039540d00c0a420705007120381202c2130086c07030164000b02044154800303000311485040701c10042400e55a5604c050029150010074540003142c607149101c08000342d0400810f2902c0900d580c40ba28040c0c805040d6252001c000c00c2581030601c10041d0310100c0340c0010580301224903440079290080d00200100c3e04500407030340881d4105003060301c600200104441618403441103004100540c00310001c0071000d480003644d40307d03140f5480c514480c000c80e415401c12002419020201e88400c072881c0042030803070f0710560003c0d407858028403120007414034001125004140707 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 928463516 1250 928462266 928462279
    0xd0825030801142707110105090c040e03180d14010609050a05060a0b040b0c030d0c02010c0f030221090c1e030c03061b1b0d02010207060f0509060a0f0e030c010b0f 72
    0x43c80540b24180803011080c4d42a203600403c00102c1d20b502c207212960030003c90300020b10060900803130481d42c2d10317011070304c1911503420000454a0400004152800940139184150200081c035050200182e42088181c0305c1c440300600340390380c64009014030001841c01a000040d941751001c64401110300140c2124030905c45c405d41080000c2c0104190b5058404d1941d00e6075035405100e04062540c483c05101c1c885807401e280c3c08105c00c94041d0300011a0100740c4c2c649601d02c80301d04100724100c0c803c00710b142059114030902d25400d21100440f031a4021155012540d03060500030000702034401d41503028084592105448030141410f02c92400c202100b50010021401d0540710340003003c44a08180d282c111020a035842403060b104406c482185c080001c0c2c664100945030002d020b90f02921080d504a401c0800341c440040041c450f1034400d000c1ca80c05800d598461203080030141c03d4502c04807007480d88400366401b00301810f000406a0f13882d41c40000a0070b00008050140000207088402d00c00c60 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 928464766 1250 928463516 928463539
    0xa05060403020c1215060f03070302090f07141e0904141302030c120604080304050c060a0503010801051503101109150318010b0102031204030c06050a0b0306090c0d082503080114 78
    0x40a001c2015089601154146480403d06001c49d15010541d403010b5070051068040c0300e60b4540b083c141e07071300840b081e039100710550110026000c5940305045615803181c5603074502d42117900011010303003801400248003007001414a000c00110748000e440351480c0030a44050002140360411002201140550b080481e440c2002d01750358031500014006401c0010000008007000014000701d10f00a90007440d0301d8481d0070302c01e001041c540007409240110341c40c0001040c0d4804c000100710480040080080181070801729030b80340a01039008003031041c5c400510145450f5500e10b840c400c1c00000c4050752545900d040e80000386c0c18019100c082809900d40200c4644a981c0881241c1c0c400c0d05002c140b0306140c407145030481c3c0c0141341a030f018107003030700d0107003803003125082600a00303000c1c64200d0071241c180e1a00c011b2143c440c1140000c056003d0b698004100020780002c018104880c0802a18001c2007040c0c0030341440d041e0100c4046000031500801800406084980100c40360b0040d04d8002040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 928466016 1250 928464766 928464793
    0xf0c0e030703151416020705031203190f0c03090203121809040507050409030c140705031c020a060f270b0c07020d2a050105071110020a05060403020c12 67
    0x240d940d400050b002d0f80f008240038460541d150000002c04282042c410035a250403022081142c049803107480050103502000034035031a0008481c1e108852049455144d51581f898150b5a03030050301e88507880940300d21403040400741510841090040c55240822420220b00c101f5040c410845018421110140008a140c010802444040b0101600e401f641900d650800d0f5240008a91200c0d40c0b2905041e441001c1507400000083e120f80301e500c1111141c070018601c6621081c0c540a019019400800e0051a01700b194002800314166401519840241901c0f00d4082c0c4001183d11a03035592501424219400440005005014680e0100200c09200c0d030702c035803030808050054a040f150110b103941c150f6460342c0b528001294040b9003c0004616202482030310140300d0f00d08140140700c102c000440d940554201c0c3d04466110300c0161109034440c00301b15204840c41c6d00a0110b10440c42d0401c0003c0003000241c0c0198065002000c1000d139400070000c2210141c05103220a41091840ca5500e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 928467266 1250 928466016 928466023
    0x2c030d030e1c0c061104090614034204260f0a200601030b010b090f190806010f0e010609150f0e0d060623091323010f0c0e03 55
    0x2500b100802521002d104403808441d01401d0703110152001d0f15141c104081001a44020400ca450a076024418550b4442d2080e041c00016041c040e0140c01848500840204003281034001690b0180303c14170f00d4800c104d914940c0200001f0321081481884180402d210310b01c0000f007035902d00803402c15000c402605030319110740260410b4944a840105041c1c00c1d40313004405d01c81c8084100758050945c0001e020405641d85030a100540d60303200c01c00004a03400c4c10150856102d0322002e09404034000d0f140741030081040700c0004001c00300c01c904402050380c560030311a25009062960000300558105a2198203a0006a02034001d10010302c00c00c000009071082502c641c0005810018040985002c0541d040100360403c10707403049502400404001141c1d00003003e40d800b410840a0008040e040c05031012092606654400c0f806000101b004015118060101c1d100f01c403818040c3d0141c0007a04521403040c44120003036512099841c103403006034811088000c01c1ea14002224403002400b0907103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 928468516 1250 928467266 928467283
    0x2041407050d0c120504051c0503061507060b04021308010b0a0f0303030c03270c0e010b03042303300705030604020c0705030703050105100801020304020307152c030d030e 75
    0x122251100f03041041140900c4844440511040c0107014510780751422544649403a042c14801048031001746100318811000d592054a014250382d0310701d42100c401c000c403138214941c2210610f1710342c0852400c0707841d140060a0f0a80c6000040b051050130980c20f40c1c255a030002b2664010003a0540c104256004403040000b02e079010b040001d818fd1380c051041b00906003c02d00e00c0c0340e0500d9050541740c10b58414500700c52040c01050300e18041510f030040c40401210a208001a07039100f400414041621704181480d5a0109400242c88003206e40300c0c64119080781e505558106e032551000c09180460076040340d5151034042010b1003901e40220003400900001e081036010350341c0490818013200d03080114802a090040803108125a04d140940c041d04007182e8032880704503481c80000d240003050003a07900a0f40d00501400303040d81041400c1f211862015030403810040b0170301c0d032141d04200d448a2124440403141c074841b1034608200a01d803030311035100c090000b050300d03008106040103000b151946 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 928469766 1250 928468516 928468537
    0x9090803060d1a0405030c01060515070305031e0405150f1303080601020c031c0e01020d050d0b041b09030b090d02211306050315060f070204050613090b040204140705 73
    0x4070b414603141401c2068202d118036140c80448404240b2050040c00005000001e400000910007541c41c1e006000301c4101000030260803100901c800f8000900a202441c1e000340707403099802c05140c00344010102250290b4040e105a0444110080d81828440c1002d5208039654445d84041c1001100880c0030756907040f01604000820000ca0070582c0f0034443c00081d03610041c1110b0b00143d21517070789109842c81c00b1081e00030030300401d0840840d50020a00210703860321b50711480d092000101d455009042d8440c00750b0380c4507581c1c1c800f40d0318100030300c09203001051081e614401402c9c154a412000e000d809424800c4940c008001d52883c2c940c00159061192500e0b403100340505541d00541e501c81c042c101c84074889000d1a08082480340d48075025522444d0000711404040043c04103121803071044c0408a01840010071441c0050b09213a00b0498200030050301c0001c10700704000e0312004541ca9420100d0760104c280d0240070a501e445c0c007401d480c0d4540c0c903c845907941003001c000380c0107100e4042c184 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 928471016 1250 928469766 928469779
    0x6030c0e120c210105060a0b12060d02150915190507110616030e180f09251e080c10020304051503160e0a12060609020d06030203070909080306 63
    0x7004140440c11034103401a01c01c014102d541402611240d9400180d40003542c85d0a0020f801460b00d030341000d0889100300540342c90300100200d42e000b1914000c142031382020b00c031452030f0b0050f00d0b200c040303a6008031190441d41e224030004082000401850200b809800000d01c040700d407a007001d9004040168507800e2455441a091810f45841111244140d03840180800c4406645a481a41200b01031099952048000d001800c00c402003d442b9a01c1002ca040722000410409820f1002d980044c080780031036021a08500e103c0805035041c5032100301210010608001000011030340030314024030b9461007510360341009680c03a91015401325082c030603514298800da01500910454001c1c05014050148200341200c40200d80d90090702c00481102ca03100f000b80c031403480b0b0440c0d00748482c0028540741e1000d1a002815044000c0a4025178065603a41c02c002504032140c4000c0841c1405620f010408518500401d070402080b0360210490504043d06800061111000c40f44d2014084458 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 928472266 1250 928471016 928471039
    0x5040c0c020d080c25090b0102150c1c0207020d030c0c0308130512010c0212090102010e01060909021206040f08130e0a09050d11100e16090605030706030c0e 69
    0x895030035500c0301001e500503820110071824000d4100c01090110351040440b0402c1c40540060010110103400d00300600181c1a0244a0044c403030304240105c810510440b0580304601040190720701c0203850f40d80380340000081d0214030316031556480c82da440d1480d03800c40c02d01c2c0e41c039000700f410f001d80f89000a0811000940324420440700080780310156800c0030308681c64000b03905c40002414524000d03070388600d0103500341c01c400c50b00501428141e42215800342000403c500f0345c8408680000d0f0700344c0e0555480d590104c40c02c52003485900000c015094011800030f40034018015108800030b4400c0c1160003040402001c56906894004000c1d84190643e030354003040c01000b940111b003500002808244074051210442c1d09800c441c075001d0182040c0c41c26a507840600307130b6400030040c5880213543c11480030304170b100d51140d002c00100101c900a40c0c0e00313821a50142100d52525070402d094440d41c840041c0494101001003102918542c2030801140d200324502411030b40520700c0c801e00c1210107909 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 928473516 1250 928472266 928472291
    0x180f0a050726030c0c031605130c02010209031b130e06010b030a0204030b0405100e030a020c13090f141507050d020d0605060f12060a15120905061303080f060a0504 72
    0x2110307000710b5040107907a21385022641950315640c80c4180075102e803103108000441e96240c07031042021688024581030510400c20034580160a0484491055540c240b24503c110345041c0200e02031059032510312011820f00808100411108100800619213040c00004000c8000039882d8107481c2c40b00b81c00ca44030340e203d00044000c1e1240d03400c02012822948280f20400000160300c400309441800300f40840c40c0102d601555a004141c029801640700004003042d40c10002c1090b1031480b00741d4404160550b035a16410140100e0140444150f030003540d2074a09604144503203142d5a01c0442030045134280300000901314081c2c034240c0600d15030300244a80320f5000a90003800101006004151664034505118095411403c29070f809502c40c1c100003002441e1503504501500c14142d0780c24250300c01540c00702c5150f810f80707000b440880e564501c048049142004072a2148424207a119010004d5140c001c14503003020344000b01c031007002c40030701a45648001042058800907100090018407060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 928474766 1250 928473516 928473569
    0xa0209010c022e080118112d0304080a0807020613020f0d0506090106060906080f07032004121a090a03120209190905130b130c0905180f0a0507 63
    0x107020980c070f2820714800700c0140390410201c07812150210394100842590301400d200b5a020704450103840d00c01003013402c80702c41c15406003800c9581c001c02401c4a1810a02d03100f42203a01c00d0303405072032681e0082901c0c00090b50009103554814817030702c041c00303260403c550b60510340071f54124028031460a040441010781c80310b080c1b603c2010b400008589060070070070412402400c4a0065a000681c00040414410b00400c00c441c0125005148103a050361080707012802407400000744480155408070121483c034000c0094405084041400c0385190064038001d448220813181a418691200c010840700e00d81c04945018256014100b0194420a031540e140c028071400e22100d82c4040c000307204510501000102318182c83c2e404404014075201c813400c21a508004030001403044e200e6100160040c01d82d1402c00c0050b500c6030284961664454201c00300b552022230b41c06541000c61309285800e101c041200c1c10600744240c0180ca007165007519241c0e00c507134160094601c0c1c0340603000c14032505003101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 928476016 1250 928474766 928474819
    0x11b1b12030e011409060a150e131b060e04330f03030804050f0f12091504061206170c0402160b010b03100f06120509210d050a0209010c02 61
    0x1c101e07001c1e10794003003013030440180c6184000707208a030700250b0210a94420035043c039440a4041c0405442c3c43c0c503440c9a40c00007000700c1c5205072401d80380310004040d100c203079000b000c5020280100e6801c0c010700030f00850128400074466400c0c070518541c100e41c83c860f070845d9031b00599008070120092009603100521250702000c1c804003003e000006065002c441c0c1030080744168250340d030300fa000d551002ea94112002c0900003d4200468007142c2e100503030000d01c10644090034002c00d90f03d0701480c451554100341d00182c0440c0e50101d400035070300c61503c107210140c031610076260310004d1100c2c02266180c00100145d4007460340012032604002032402c0001c0352135402107010700c3c0341d81c40b03180c1380d0002d82046d50191000c040703144002c0b80950f103601e101c00946907156682480300350f21000c0e2001421001e00041e19034050355080c41c1d9008005030070030f0b42d040282d001d030507940ca140c2100b03c01142e00c000c2c961002984140040400c1d41e902c04414500150121810721990140d1001114802050b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 928477266 1250 928476016 928476041
    0x905090304063f0e0f0a0b01050913120903120908070909020301090c080c01020f0601080604080a0e19080c09042001050f0307170f0415021308010e011b1b1203 70
    0x1c034403400f2108032407034201032003001e820815522010058120940c0d507043c50f00c1d000b0320100ca0703103005001c14245901160381c003200f50324105285c1c40b03080e00c8ac01e02c80e941d2a14110000341c11182d080c805e121009050682e404643d1a0440c0a1031501c070840c0d8450b0181e008518919494412040070b66409400400d82d0540215800c2099550307017401c181d403114901c011502500030305003541c5241001280e480e040b550060003810303041d601c664030300b8140c3e07001c20000702c1842100110755403a511060b00d44a404915104081030640c00c10f0350b121f01d0104050310706480b030000707a02004000350141b0790003c001120320807038880070310115005858500590b421110452404420055001d42c0480404050805000d0154490319649110082a1070441c1c003d040c400e88508110710622641d80146440b1051b2112460826200c031415425030b8082c18080003540c3d1610422201890440c00c4901040040d00305081079080141456419031075810f03000d003150440e410300705001d60090f0084100502e4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 928478516 1250 928477266 928477367
    0x2070905130b1e06180703230910112b320c0f090d031e08090f010c1b0314030f10050114070b13060e0304090509030406 53
    0x60081641d4614039021100d2140100b2040c0400c44c5414800422602c1609046107000301d591307907540075406008034107461041c8080003a14000e502a03203900b074a0141c65004050b00d10b42c1a92514101a1003007985c0304a5582030403c0038010704044454034840b83c0c040c901000b0484046030380e9180041c9450340442030b0f4200807208040d19490303104070302100464110900d104a484541c40c0c00b001c0d0094146130302011104009840715442d1440b02ea1411604c03078501051110b41204c07802c800301c580207030803202098624003071001c08001800545140788200340200844501d09000170f01207500c0140040042c3d509102c1ca00505200d2100d100c1c0c0b050060480664a04201e00c0c0c0d140d51441c2120488803609001c0da012a00d580300340201a590320028815a0034150241c8072007200300c2d000350404038440100b0ba119000602c841c000e950551007442c0c099034a03203140020300000c0e580000d01010080d002080180051900b14a24580200f44100c03645101c030440c00c1d0401c0e8070030403c41d00307048818 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 928479766 1250 928478516 928478521
    0x15060c170c060403030e06060a05120c04060611061302150304080c071410090608160210090b091209060d050a0b04091b0f1202150d0e010510080a0302070905130b 71
    0x100c00050b5640620322a5404200c141c0c81e04042d0390b181c0005507903159100c0c80d651001c0100349444000c403441d480402081e12907040c200710006c0d003100c103554000c002180c003040680006480034411145d04c8001101040d2210b5040e500241800031002d000351085440400480c091041400070380f0b0b00282041c04a49000340c1f110300c444845001aa440d510647d4444071150005200d00c1500d02221240d48481e10b05481d01000511803a000000d00d17400c6208032104102c0c0080700d805050303a040e01500e100074103030030440368042c140480f03c0d034005044941001803091940300ca00856188034810308000400e80c40b50074030300c00580960142c182c1c0c81030034404480184041044111603051f011403c040d045a55520240c00101b190320440d0603482070f03904038801504101160144086c0440112898900500742e10b02c22506071101c04402690364404100c40c5a0074845a00702400300303000204190007296400961340c074002c0c0a1591034503100d1001c1280c5134015151103170703442d511030b04203000303031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 928481016 1250 928479766 928479787
    0x1507050604083a06060f09031e05150a0e06190906230109150803040302060322050d0305070e03032212060f050a090302121309090807051015060c17 65
    0x781444a003c54964940140068501c0c00750715450340204190325580d00051554841ca000c4608071007035928040c0c0075146140000383c0038000244000c41c641640040750070300300e40400446900c2819100c860b0300200170320420f411004d0705800340d80428440451070b40c072a854560050000d05c0140d00030303004044c600500d40c0400e0403095068400302401000200504d026440880d03a0354030446056410800c01480035040c0880116400460340c0c5080d841001d0020904480c809034060070f6940e600301144401c0c825a05008194000026140046806810f00006034a9104419055074911041c420400403080181c410200a00345c03440303400180c14403402d100019108802080b49224070303020024418044900c203450328503406500800e081c1d210410004025070001c1429003410810800c00a174401c824003425a159100e03903411070b250b00351440e01e5454045400d40084125044c1000c000350029a040c00070304031403942c948580c0b90b11140c1030a495502110b000110302480c0014180d410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 928482266 1250 928481016 928481107
    0x901090803070c14010b01091e0b040617010b04050604170a140f070e04050307150b060f0a03050601030501030803150d050106060e12120405040218100e150705060408 73
    0x84c051803c1c1d01e210080100c07494222480c3e0f494131030110b1840f12040c04010100307000b24030300307400380d50384180500c2c0c89418910464005510500008120341040401031046041c00e500411606100904041c03c000000e00d582c042d60160188003451440e0f040c0005d0780c10400004000d400138000c44c10a105040d0107503c403441128000040e108030100001e9108454014602c01c680000165040071a240d4802003030480c2d50108100309501c2c0c0a202586690f050001c1c40701103806011261f4a00c040385018082e074500400300d6041c9460a0010000b2402e0f10040b0b0b540029900000d01659601a00240384c405981102130942c1d864444d01003050b60308056420906203003111085d01c40c503c80144c0c1ca5942c2600180307040e00741310510041250341000d8000d40204170301c0d00820084002c4000108800080101d40c2c2c0d000210301d401d080300170b42014900800311024414815150600d1030700d415070746046c0500f0060440c103001a648101c48110511800412001c80c10f0458080002e103a5100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 928483516 1250 928482266 928482287
    0xf03030c07060f15061d090405100c1103040f03210903060b15130302040e1209150912100506100503041b0e070309150204080a14100e0f0c0402040f0e090109080307 72
    0x60030034030722146e800d14001e040705104560040041040103040c1c1030410107041c0c05251881404901d500010f241c00e814005400070f0105042e090480c5440c42c200015030f20030450089071440c1880102c00b640580c00000361095a42183e00440c00070340f8507021509002070014a0b001e00303100410150380600b010195802241d00855051120404080c019a103414942d0201403000004002c4038250b810014034241c6007417401c1304064280b01540001c10b041c40e844156044103900314440c00400110244540750b00448181c03503a00968460704009802840045c00c041c1004440f41d24060b03100c000041b102000c2c20f0841000089030908040140160030380b100100c41215925059600124261080e14200d6000350020000038150b61078000c1c01050442c821440d500822100c1a03001c04280a2000b2044a92000b05040d503514060a414902000726062060340108010004100b01602100a45503919843c1d80a5107a01000b1030041c8070380440201070603004000c000300190040210358 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 928484766 1250 928483516 928483547
    0x3090411071a061e030c1c1a07093f06060914062e0e0a05120c090a060f090b01030f0e0d05160506010806090f03030c07060f1506 57
    0x1030030207010740440c034010100c580c3c6400c070900c5240444030b005000c840e002800006404e6405c50030407000840c01e521000320224a04410148400c03003007010510b1510250001c0c0d02e64004c9500f00400010001c280c280300d10010107840b802a072011081c1c00e4400b8044040c0c2a000ca84000042c00c8604005071880c8000d950a520342640040c41b14488d0043c0c81d1500082908026166590303c01c01c00b4040c1c0b1540030010b00441c602c0078032017541c9102c0304c0210300740464451481b00c0a10b1010014003542c1a0080d40c040d90740c00401e40e080a0000440440ea081c0c11541c0000741ea0b640301c40c0742c0040600b0750011464101e80c0c0d4000440b0200c5612a070007010007030742c0600003906036014100c15038503d201c0707080d0940d00c10a032008045110b0b03c003821050107040c0380415010308580b80c2900c0d202080e04589083d800060501034020010000312400d002580007441c214980118030030441e018201001d46141e484080c2c1c50402420380d440000d400345203d2503241142c0d2503a1005001a08903040e44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 928486016 1250 928484766 928484783
    0x1030f060b0412120302041a0a022d10111b102f07050d0f03020403050111031f03050d120f050f090c0d05030919081c02010b120312090309041107 64
    0x1500040c0c4170303008035810380b407480100c40751021040c0307002642d507840101c022045020740440e00c82da8445403000c550490384205002d6140f001c011a4050a000301034643c0d5415601d01100c15001e041c0110030340704661a51040302c4603441c80d850400b070a080f50b0048840142d40b0f400b41c803814620f000c100201158101c0c103d020b50010450310004201d104400d400340465100740059500c20b4410a10034500c48076900c0d0140c1016520780d40d00382034407180d9000040d02400401040b40d440c0c081c40d2812030201c1c0034282e400034645561102502d6882d079100680801c00c030004000c07c07001c40e642000c440390400346030812051034a200c1c0325080e894140c1d124401c0d4040c68080b1095403400c0400b51440680103800b85292820080070441d010700c42582d00c0951400500c8000f600c1c036000e008050158408001010041c021a00f0090031110b07100c101e244520361900800170012000800d445c03030b2500030011040262280c3e0079003817940c0a0880042d5102d4105080e60b01c10f2003031032001d808107520941d2007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 928487266 1250 928486016 928486043
    0x209040b010f1a12150a03060f180812040219061d100905010503060d0c0e0117030708040302040207050f0106080f10050c07120c0f0825050c01030f060b0412 69
    0x24025020103800f54014010140410040e000000524a40210703402c1c0f0900f1607130301440040341240745254401e079a9075581d01498001c0faa007600071142d50180c000c48120402045a440001d680600015481000c0f01480001d0441d290101c03000c49250000c2120300c0100c0e45c6401c010440e419007040000303140c841140810540c141404000030740704d010f448041400c5e08217001102d103500000c0c8910380c40310600100d400402d0760324400e440504403182400f0300c550b0400d125490383c00350f80c0300101103613441046002c02003401c0c0c1c003e403001e0380c1e0704407000350b41c8000d58109145041e01050303160b041c075440e00800148070b041c005400300c4001012415a0081c078150010304040300c10445070407054030410080180042c0d00c0c3d00e850116140b0754240196001d82d96128840070286468049a413142d00080380311394101c1000119039903010000310040b10200c0d6699054a581c0d6103420709061540b04d100d85410114241c010001400d9a204595101e036541d001000803d0180c26099410303142031040d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 928488516 1250 928487266 928487279
    0x1d07020c0f0906120a0b070503180706020319050933160f02031006060302040306180f171606091a0f19020904020a020a060606050901090909020103090209040b010f 72
    0x1c0c0c2480380c0c40000c0c5142e000795110000d022500b40c4008405881d40504a14000021140440700340030b10ba45580e07441e100d1134480003001110b000303541e82410302d60007407200300301d403640c000308131642c10807101500c030744d0000038034810780b154000d200f40594440d217890f09404030f81d00350600101807456003800d52000b0100d00b200d611514030070036440800c00e40d5480ca5480200d40065079510909201508a52501c9018100c45003120300795000032000a400140410074000c0601a080d8904203110340122400e070251740d08406481c007010028604140310070004020059001030b00c44800fa00703c03041713080504a1a00c94014559072204407040e91024100d0000a181c80200900c07039507200c0e02424558030303999604007500d4101ca002d00b550325001c02020b2220786890010385001e041720f03001003039143c400d4174040d800d0f140716801080802c030301800b03e85440c2e030340715102034122500300200003001c26490004030054602040c0180d0880d50a1050000304503243c1030080c1210644c1c651510704940303944 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 928489766 1250 928488516 928488529
    0x1b080709030203120c030f0309060405060618060108060a09020d1e060602030d020903010f0c020c041b0c0f020604050409030512090d0c0201050a0c05060a0e01060902090105040308070c1d07020c 85
    0x400394059201c480c41c000d10b005020000d04c1d0810b005c104890804074520780403243c950048038910181d07042304c0248002c101c010420190454011901e1620240c0541c50080144400410842c10070080a010590913150890201e01500c56100150740d600c12080b001006002107400c0100c60318000031b02100d1000c003521960003030724101e03800340d4584519142a0b80207504a0300e903199055603a80c03080900d003100c5108040c4000b00d41e03005400018010b904200840d40d007142d8200040380c034003604051070b5074044040001c10350f0040007510580301c1c1d8004203101c3e0040e9040035400514000042080c1034100300644424501824107240581c0c800c0401030b242c05224801c00d01142944c00d01da801580204058070004d101440c10044d4034009484041c070700b16050326038117981036841d43c100c0002102801002c000e0180080d0940ca031000e500002030062155120180c01d9040c04a152000c1080055107400140300d136002041074a0700740800e22103000825104080584034081c2100c40c070b8109903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 928491016 1250 928489766 928489769
    0x3030a061410050f03150901060f0206160e0d060f18020a1a0702041116120908061009051801060801060f09050402010806060307021e03070b0f160f0c061b080709 71
    0x1a030342c0e14104004e4200600c280d80010307000000a4512454440094461003005802080c0ca9070303c47c2c80e82c20072141c0180c1440c202030044a900c1840540002e09140c1068403c803138040c00783c43d11201d0056038100307507006114150303400840d03d0074006400000e07100c2585216400d4021291441c0c416a11015001c604002440a120b501002e07c00c420151415074040003041801c00082031404c05445100d100c003031034400d0210f40b0782d1121800200829880010b900c0641507140082100c0d0421152021003e8444c3c4500107001e0b072210001a01e044c89487c1140e880c401c1d51009000341516040124041c115a002d4072020028113600000d4402141c02450701490701a11401601c1e110f0005018155000618410651003a4a0318100d00741e185d0114110503880c40c4e0146850302c0b00c41c608180d44a0024205801c008682001c3c004101000c01030910450002d003405a808902c0ca40e00f0f441001c528038016245c64a841e0801d90300710551200040038811540e03401c00c650b62213210588940525 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 928492266 1250 928491016 928491049
    0x160b060303030f0112020f060a03051f030213050705070210050304030f21090809031015050406050913020301062c071b02010815122404021f0e0303030a0614 69
    0x3c4004001c02940710100701c0d1210300141040c101007060f0700129015510982c0b0303040c0001c1c2c1e5401000407850b082c5690a00c0f80000002c2d0134517481c42d640001e44a94100701d19100c100c0d0703459000ca91130728002c0c42110a55036015015051098030b038140030303015800c00c44042e80411014440c0010903446140400102c410030401c011200003624030702e2000f080c48120403100c0c2141000b14818603035080003081174400308007001080000d8500d020310243c03011980051300960404005000302e81c3d85c000b00607070144c503d03804230000039003d00000b40034212035030042601204001d81070307400200100ca40386805000d44070210940e21019000c07507421852205202103941c10168080056108980341d580088449107450840e0205400182016440d0620616690b1000c081d07045007400070081040e8240180f19200a907290640105020045200e001c41603002501c5031081741ea07010744d0040500140240c00c50381c40c0c0c5802d05082c2c00800f80d0340905990150628101c0304903140c80c41c00030b4008488c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 928493516 1250 928492266 928492291
    0x4060f0e1f03030c1b180b040e0309010f111615030c0905060d020f220e0f0c030a0e0a050d020708151303180b07060b21062a160b06030303 61
    0xc2c9511074800b500100c0c20780f40c030045e0700e006000075072250b21054421b113014910030025441085200300000c450003880c40c001d00f80c00501100100da0b03013103050180b01010b0360501c0c60f40820009911414004c120002c0c0305401e84820b0085100c1401c60302d04000210365807420001e86180070015594400701c0e214959201000b046001d0076607549402500011144c800440d0521a5443c0034800d0f01c074820192041002c91500c04211164110b42601e8010402c40d40c40b80003402d0a4004a0700c1d840001c001400c107a840d181e100118600c200a1030380142c0c1c021040d50200540100000e4840340d0301d1040c071342103210b00c02d00da070580941c0301d4100740942d0075540c5910903040702d6035050300c224080800348108541d88000008020500340700030821700784106c50001da5405214100030701090002c04081e003004640180704031841d00001d035075400040310743c841007422650603041c406030203614400000780c40f004188920310307801d000800c000c214465550400316035139040c140755590100311070203040b044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 928494766 1250 928493516 928493537
    0x60a0b01091a31031205070b1e0f0903181c060e2a0405150303030a1b0f05070213060f030501020714061023100203030a0b03010c051804060f0e1f0303 66
    0x10039104081c0d044401c5e0f410300702c0c00c0c1511510340341c00b03640045849854041060020b268241c580f041c8084e8003401034803005e00141801da03000e503a00e01404106e412800800c4140345555614005050303c031200d180041c88080010f40f070554060700d902c10306008184100d45004c401c402c60b85a5480480e4058100da5030b54500c40c3d410080581360240400720031880b05c8a22013401d0314240021031150b02140390101c2c800e280f00e00d1a41c030740350f403111b0070104000070100b20104142d030040440303080036011140c2d05600004c0b03901c2c03407004001039400b80002000c0c02c0b000108000301900580001170056070081c04107118042450b0b159007044500100c2c60788600014400c0031001058103c0c88003941401111340110030300441c05030010404281f015a0001c0200802c4010310702a9040c2440113030002d200391b220f144c2029140c2c1c010402c00c0b044003c4201610019500c07583d000e00c00400d9095500e00119554045011140c0029916194060440f50f0358500341d180c80030001045070b034190344507501c07803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 928496016 1250 928494766 928494773
    0x130807081b1306031406011505030a021b03041403070b030c09060c070e0c0702030c1203030a0f020c030d02120a050420190f17070305060a0b01091a3103 67
    0x3005a40d50000000e2102c0b0458880c92040b08041e41c0b0602d12200300b102c06940151400304140c0c0300f144084d20356048905416880401d5981003c0781070005600e46103141340700c0c140035071000c94030710b034a01c0041030010f0004072800c28204595015800d0b41c0b5a02e0302e882e81c0018902c002c03507007407000400030002c004150030104020071005030361500391021980c486104440f00c40b025100400a450041486001c0d840c00b0b1004072001502155070000d004c078000904c940303c1c0802400c07015020350b00c0c10200900102d0b601191620403986050340c1e40c500da10b1035408000d4115421480c03040c13000000007a54082c07170f40700d001d010b1600004406207010980c0f50300344c00201c0c200001501700c10300d00c1c1b00c44c0c5203200043c10203000d010014201c208650401c05500904409059241840d60240c881000410350105826401c842c1c0020085143c81100005032020905c82c2d01c2805807100c40180c0e003070000c1000c0042c000c0001c10345034804030390320342c21900105c17100c6907024a125010341c09001c0001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 928497266 1250 928496016 928496053
    0x80f070f0804023124141207060e040b100215130c0e0403030b06042304020d14041103010b010903122303090d090303050a081008010606080115050426010f0c02010213080708 76
    0x1b0f0f100c001c00c550502240c4c14640c0f400c1c40d41c41e9001c4404105103820003c02841c0500403800d07280001d6551002620382600000d5071440c00f40402d81c0e51000300d0000c01c1c0020740000e5550b040d280c100d180180259514407240d10403000403a003d4000a01d840351001c000d140c100c0407941203511118040000c2140404a0000c0c8500b5a400c00d030321a508001c0c0008400359405050a0590102c01c0c48840c0c0c0b1742418a208085200424148641d141904004044c1c1e00884420162070300303e110780c80c0313009840c0d900307481c0d003074210340401000b9800030729850ba008000c00081d8402e150080c1514400c040d41042550040c00314040180418400d0022040306441041c00310340c41202c40004003c803ea445140500f116802c0d0801c000103080c80f0018001440c900354007041443c1180f420514241c0341c10344004669480c402c03510048008104d038207100d4482508a501d00b806140803c003c0c0c1d0385401c1c03002e4001c1d4400010403000e4009494001105070000c5035174400c580300c050180c42500c8152106a02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 928498516 1250 928497266 928497299
    0x110f1f201203191e0b0108010e0606070605060f0d08180f060d0203132109050d0f030f020a081204030206060a080d030905070b0304080901080f070f0804023124 70
    0x24030507500e55103102d501551204c445203415019100155841c03160000605a1300144c001c42c041e07005407804e0150310b440703a03000c8840c82170300b0206c0064591501c00020b040441001800341e40107910f0f541070000c2c842c59030000c0490080c03001220b100000c3c100184a45003050629499000030300788a51850741100e900219403115906035a101c9101440d52100c4815921100b89540c140441070030034507041c0c0046500000d0f180c100e58145020540d550b0320455a00c9140e8010104107001012103035003402080716010155114191a8494809901c8642c454030101c8054005104e15400305030b0302c1c10103051f500280d500301e00107040c211034641000d5000d41b100e04c00840d410f10503404001001c1b42c140010718000c5209003400c61755014020300041c400000500103114441001c81032110311074010302110900b080b40d04000c00c45079520700004030440603000701c2c14541201c0050f22050451940640d02400b102080204480840342001c0c900340786220707a4010760700140c000c042c001d10b80c0700c241006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 928499766 1250 928498516 928498561
    0x10c030305180a080309010f180206130e190f1404021504050d12090b040f18090b0f01030615210206040305070e1b0304110f1f201203 59
    0x7442490b544269924091400e54241e950780c40100c140030034443e0a008203480b012400f0320600c01e030200210f980d0712400105000070721500340080d00981c070380d403030700d40c01402002e02100f20a9940350420000000030780c0d10b52100c000c245414a150300d0030000b031088004520070030004040310364a17a130130b100f00701040600001940304244400501a900c08180002c21072251058030321240b20350b00007520207a0241c1204003040700501081c0f2a112118010f0011160122100209820400c0c0707420000c00316540c0140c01c0c3c10107001002005000651094100d0b441403008100e42d416000c0c0184082616016900c0208400140c0012104d004008400d50600090005181c140e0300d9469900d000034a40c02110914080070401c01c1190000d111070300000c0000c9200e91a602d0142c1d24481010075004a0318885c2d8810215031805481d41c2c51903003480025542940c1c0b030048090000b510b5a40405160400304d02007030b114903484c90000c901e08900e105002081811030300c9a0b020000994071211118 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 928501016 1250 928499766 928499791
    0x1171909031211040f0e04120807120204170c0415030b1e0412180b090402070510050907050f060c060c030c221d16110a080f0309150402010c030305 65
    0x45403119291040200e21001c008591340e80d24a005003000c0312070a40c3e0300c100f00c21003010080201048912040d242c10041c00d14002c141503580450982e0441c0c00c0c03110307981402d8408980840d201d601008020f02c554801422a000b1100e20030410060300c4c000f40003482c0c2c1060082080000805403003003150408000b54203001d0104440d800c542007400210707010390b1107002c910b000b41030a54100c41c2e0354007031900320311802021908200e48903426214000e8014046d960001c0c1e51000c0c09000c0c002aa50300c00380160074481c030f051a5044c1030b540e50290040354415118440c200045140c80000c44080c80020009411942d44407035090503550401025550b83c2032003003160106400110041c050b80d1030124032840221410069800b8483e400c1c0c8480e02a06100c100600040381480b24181d08080503a20f001c0010090b811044d0303017007042100c001000d269003c22781040b10400f94001d188103400c00c404071103070202d140d0b019400e4206d0503100a03021170484109500071a100b0b41200d60b000144904c00e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 928502266 1250 928501016 928501037
    0x903020d031a040e03042102061222030503061c050c010f0c0b0c19080f0f09070f08010f0b010216030314072405090708100203070e030f0c0117190903 66
    0x3140130b44400a520052036000040d0911403413007024405094500c40c403c00a03040a407682c0843d2540c071a400d106d85031607140c1000504104148002074005410001c1160130b40c20b05c030301d4040c1c01c507007096507524420440d50f88041d10b19048401ca06489940103802005080940c400554103498900300a00410800840303450100d0f800c1c10b9418095218240c0f1155200020b410001075001c414103500300f0054070205110039000b01c200304a4000f4a0301e82c40d4070164680e104214a0701c1e1560344500080c0c1d000f40d90004081106501c250942c0d1034442003402440d14040049840d07089840b600401254000341c06d1001c60310030a0000025a041000b0038900081c503110714521140e194210645643c0e1091071406125507401910b401c025a040107054450a110846841d0441c80e801003410580c0400010b2941d8451150394161031400b4080d074810310300391318241d616a904103170301070301054101141c0500f69010301c014512070b0006941941c1e101041142100150000303040c160304101c02000c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 928503516 1250 928502266 928502269
    0xa1104020f21060402030606030a0506040b0a06111204080d0503070c0c090c0909020f12191107050708060c04060c0606051c05190b0402010c0501060b070f03080a0903020d031a 77
    0x420400c0c0428250400d6651480c100d41100e26000f08118000c500500c02c0c4000f81d02c840c010307660006600c2074081103956818000c100200003202e10760b584100801d4000032141d41007003559448600420981e00d0a014020004c5180d22480c0324a003903a502c8010305203206841400a9508030b44180307440c1c40b080a86071104d000c00102e54102c8400c160780e031210000f889810440c40b10041c02403a1055041003001c3ca014000d42c043c01c1e0741d4940110070100050844890480c2000f58400c080c80d04110300c15a01c440c4c410540c0001c2c0d01200c41d44203699002c50807010000d0744a02c603560680001d4680750500400300c07088181c003001202c05680b00c41012070250b8800440400305045501409080303015801c29034586800c5d184010804040c404000d00032501045038160700079020308120b2801030080c9052030041c0010ba0240110741c102042c110104050304d0b004803c5580a669048819140e0410b0b03002118403000e80100540e10603040320b01304a01940000885948290709041001690f90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 928504766 1250 928503516 928503547
    0xe0d0c0320030d1d0f0f0103090f020d060902090a02070b0105010e03010227031006030503030c030606040807060815100c032601090c02010608070e0a0209060c031305011b02030a110402 81
    0x500400120714001c0c01c4c0302e182c030a002464006040229241d4010031000d80105484a158860283c10191507060031001d020030074038074420041d400780c4000201151070502c90010a0b03860000c9100e5071404000c5a5003e8507402900c0f2226000313080b41140d64a09001035a4902c0703508901d6415540901c00481d5800742040060006480e403c11417000007045010035040194205800070141d18203501440413560001c156940081065060703540ea442d0900041c0403405113900010061180c0000424510741c0038281d81e000f01e80303a601c8100882583c40070420380348002c0c40b02d880015420094640440d1007410b00c1c100c50ba14150a40200b5844d100011070300e00c40c03d0700800411030700c88a0144030141d0900c00c8400501c2400e001e00101c50070084c40803803015019000c1c04802d600810b0048103681e1703980032a4070303c0001c041101e5032001c0c1c0d219854818107980c0300d550b01182e03001c08580e402040750040102282ea00a0203411111490b5070307040e0b503a00c4541c0c15240c019600380617442d038210094 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 928506016 1250 928504766 928504783
    0x2304051e04050606010906021203011e050a12030e0a060e09040206090409081b0118030c020f0907170c0406120f060f080709050603012d0b19060e0d0c032003 69
    0x31005881c3c00e2500c0b50024040380c22a50143d01194801c50342c0641038815541503905403142800b580c82200305803420b0781c0c1100700341d8000c1c0f40c2c0503218000000310300031941043d0610074400d031204003005508401300f0070034a03178a110700340100d80c2d820218004c85c50804540c581c4244000c0c540c034204000640420100d58440c08216000100040d1280308102030700d0741c5000f10324000307009010388280a580e58500d80c1080b41f0007010302c00c05815240441d07460180104c00302201401544580c6400e40d0020481c1c001c5a0071350010f9045080440c050151410440c1c09403985615401d5000510700641c42c020428003015852183d0344031004038800064034410303801403402200610031282089107003800c0303513009041c103803107170780342030702c032000f501c07601c2c091090710050106d01e50070f84040c6d4107081d1000d006c80c040415800240c00c1034820212001c0500c0405407051592021801d01080060040720442110054200a0b80c81410000030302d244e4810703949680780e581c0e0b040710021208086460302440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 928507266 1250 928506016 928506023
    0x20011806030c02101803140706050a05012c0118060305010c0201020a08070e18270f0d080411150d0906060302040e030a080117010b0607050303102304051e04 69
    0x452880b2450700d0350401826408281c94482041407520030000070f410300d641d41c00000c040c802d10548001941800c201510443c64010909100b90310384080d407023004203800d0242403009040100c900c10300d401b0302940e50701c01c2c6521a0b03089a02d81d00707041c03614055100150b40c08c9200b40d11404080300155007801a082c00307a00907000962281c0319114040e00440004040e1010010400f40c01344c140c0e502d02c209141548100023a035842600e50401d030b411b92400c02400e038070b4081d88820520341411000140c0c042c0c06540c000654005028041d011180584c068a020b4602c040240c1c00d00024608003c150607080401c01505103800e42c00c0c00e803035050361008042924501d0b07a8490400a6080501613802d910b03c87c400034500e04004a60050040e44043c0601c1d00307a6000d640c2d040310612130960068480502c0102100d8a5000c1780c07130895501e61086481007030229180600041074079080380d8618010070030551008001c03030542c05100040000614150030210302c9100001500c0029203078900480c00b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 928508516 1250 928507266 928507271
    0x1e0e090c031f200d0f0e010c090828060b1f081f06080a050405011517010e030301080a030f05130e07020606030303060a051509042a0201092001180603 66
    0x1042c0b0510080b03404401012003102c030216502c0c590011648201c078a03894498070006403a462501d80d08004164050a01d4529807800c0300190310190084090421104105d048413100381040e42c241c000401c030614904041c0d149620328a00003480c6402641101c4000780c003030748080c1c4500340100a00e42d0b2003142140820b80040c103018140520801103d2041c2051000881c1c20b460300500400250004149406032a0b684021404002d000e42200700481d018034400e00b20b0b1512804410501120050301a02a40c6003000650210b00c0110603030b412528941c014021010081d201900d42e41c41e10003081302005000c000304218129400e50280c041c208540414509260001e40a403070004054001480b030b40c0b0510800156035285001201598001c0d102100315030030b41403001c96a8080c26002a61140c01c2c41d502c81018540c0c8120b10002011068118807442c50408082e822607090a00240c04441c0118100e0ac03103044c8140d40018001e0180740004058000c84098100210705410400c0001e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 928509766 1250 928508516 928508563
    0x130506070c0c0f140f0312040b13150c080a02010e01020a0306090e01290a030803090616050c060708091903050a140301290f041e1e0e090c03 62
    0x344092951003c2d1045202000d403490420310014a484070711040304d8131501603965449400c3d201030155080c02585490050348a58850712110020340065a0b80d000b260080980003031021024442100302013901d0b04c03440300c114155224200c007544003802c0017055640b151190b41041d00244018000b00286075000502c907400c01e078000059610003c51401703540e040a940c0075101d00d0401440740ca04408450141d24240b190000c203400c040c0d254030150140d4004400c200e08080701241040c451020626900d0204180d10015901c900689402c16429400130002400d00b0b8001c5d440d4603081040d01080b82c4c84ea0f41440461541441c0210741100007940200e841c171489a00b0102c80350000d618101e8a5041d036051503402c0e030f1b140c0c1c130303c0106040c202c001420752848254002c04951581c01c12501f0140c0d20350b16194000209021486080740744032100000044100d021122101803403849072000390800d00c1d010000e08015405485c015441c0a52100d40c203896408000803000b1071811381c0f00360f40a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 928511016 1250 928509766 928509773
    0x4031707020114270d0c0b0c06011a030403030c031b0306240e040504021801140a091b0804020310020a0206060406060c05060c250303050402040c02030c0c09130506070c 74
    0x140c0c1420742580143e82801004420198015901003008a048043d0b49091003140050418140740b0000740c000c460301007000c95100a00c2004082c0c0c150824115245070340e9824800a100c0e407403005200b4007140c2480070500007842038111400d000c82510b0301040e1903046540180f600030815500d50040b030307681c520030058140340004601c02c9040c5030340040007920b2207040203424a4035581250f0b10503079071200050704569036000280c0d400303620070300d00181c55038454001102c035219032054940f08190a03000001d8440720760144464242d441040190055202d41c415141c0c0440134004903811b00170b5000c150b001240701e101418020002d0740c0201321605020045c4022a81c01d5041001001a410910310200f04001034554105e4030240d4034a54a46213425084041c00c1d14a040501503d5004501c0041c076a06030005401207000300e40401060303840410a90340c80c40b03000d955018a420207551500e5034a00040d1056003c1800341c280c42c07007840c43da50b4040c1429011140c1d500495040c03510182030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 928512266 1250 928511016 928511027
    0x7021908060609060301051b0c100c05120c0a0c06050a0e250807050102060c0f16060501061b0b0114010e03011503030206010e07080c07020d1a01052b03050906040317070201 76
    0x8803200380d00800c05810180c660b0010300c2a02303c20700ca008240003032000c800340000c1001020030742d05504104100b040030400203240398410020007140f80499004141e4842c002c4040f41c1d154100c43d200d101030800d0307650792440501001800b00c020300350303241c0024685900501a8403036143c0c0c0e6421700403004800d0500b0b880250100d4000d804242c6c81004c0500007640c0020b0003980240003002c03003545034541c00004540e14461110741c0c6211076024031a100c20000030f0340016050b20015110f0542c6804050b0803410010351a50b40540300307841d82401000292907401d10f1610941043c9840290311002101080c00d58078001c22028003402d680301c0800c1410f42c1802114050b101f800c0f035020003402c03c840000c10b0414050b0441e4810000080c40b18110b60761100700d01140c41e44946410404840600c4165521209100d02c60003285a5084903407919440c46415000500c4050054100d8943d5101110103801011289170880d008100102c0030a40c05011080b02c501ca000043c0d40d01c007a00c0c4001040b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 928513516 1250 928512266 928512271
    0x6070c20040f020409180b3d0306180201020c0418060204030c06080c0304050616051b0105011e03020916050c12041d27100e0c1906090b07021908060609 67
    0x6c052803000c0781500042d8140b01ca15048415208071511200e81c80c0382540c0214141141120801e944a48503420015281c0c0314000312400b61108011061001d40300c0b0002850500c230007401030b080100d101c52146855486110803980503241040b241c06203035a0030049a126400079107a00b20008406c109003030380301180303075407115502300c1440c11410907075035290381e4130b4001d807586049100000070b5100180c4503a099801c400f07907507240302000c0d50802c007615008003820701803040402c20700302c0611560299482c02d00100c0c2d50141020320b83c2d40d650320780301c0c100d01003a01d440e804110301040381c4100c054040200220640b1102c218541e07aa14000805292694455110040c0c00300c00f0100301c6c10100b02203038151040f0760310500c0400540c40706141400c2101c1440c00003103240c544020004c40f1400020b1000c0000ba05580a003c1c05130810060301d503004440c480d403400154580001d1040c2080c45010b00345151014000719020600c0141519100c10305d81c00451169002034104819442c1c00b05280d41c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 928514766 1250 928513516 928513541
    0x1e121009050c241c020d1a0108070e01050d05060d063e070609021201060f030b0f010806010510090b030f0a051015050901111e060906070c20040f020409 67
    0x3210758071983e11954007801a100e8280c01d000c80b19a0201580c001601200e00900d81c1c1c50b010000c8070f000003507088000300c0da00d1700326001400b2000004d228902540e00850030070416140c45042c8407602410b40c1c090b0500401c004e8000002410380800280305008002240081a00a031a0701a04112200c021521041c2d05141d5a6690301441d400403694412a55610b4000d01d02090724010b50000c14144601e041c05103545600c4c0510000c3c080c42d07541e02c81d0099901c00d10f4804102d46502203110751225081c0500100c0c0c0d0081c8004000c5441c00412204442c0914100702c40c48070f507101004d81031500100d91070070202c004103042280d0705080c0d100340c40d802825441940b121504280701e40320b211113401c0d68a0140b01300000c1041c1141c2c010410046c02c5008a01140c010200303035030507440c1c051071505080c41c0c648210710105110f158082240d911070329207540d40710300403200385d00c4100d80c1484104003003c4502850358041020340b6280a81031101c0312414015036a00d2070800584100c07107500c3c6184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 928516016 1250 928514766 928514809
    0x302120703151502192004090816051906060e060301020c0a11010509060d0c02280201050706020c030a2a0f1b0f12111e121009050c 58
    0x18201000071200301007561090801d401c00d82c054000264980703c00d0a408141c4c001c0ca21000c2410000c6c103141100c0401d4500851007603140b140000c3c041500d000c460005c00d046414071007000c0c00c01402c043c101140e170180341150240e01c9541504c4004805401c4143e80041e1070f0a001e00c141200c0b5076180350898400d400840c9015810681c1c00d4484448440040c00985c8811340c02c1c19680c811415030304480f00081c201a0380d507402840140080000761a03081c0980070364603084020403c0c03403491900803408503000104489482d030045505a006140440703a0725400e00c140c40c85007508101905001700709454080f0039103200915a44220f1b5400c0703059003c4154010100e0000c0c889854807815145d200d550020391511051030260710459035003000c0001008204006034500305c4000f2810340ca805031241042e00458641842000b141c01c1c2190082c510342d4480b40c0c0e10f107040c95039030190001034040030340b940f181c0d103441c50009a802c2c1d214290f034140d00030114011580303480d900424481a816030b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 928517266 1250 928516016 928516031
    0x102130e0601120506010e0a0602010e01150f1712030f0702160b0d0906110309030a14161b030203120409110c060105010c0512031306140408030a09170a0302120703 72
    0x2c2000b4060b0303140660303d0b0b4440c00030400300d0340100c644620750000285900d18041e1034040c028024480800403c1c419800d114207441030014807003000d400c1d00c400c0c40040e102d95050544404409803202e902480922804d00845820100035000e5401400407154840c1c013810310100091030001d405110802c1c49030004420005400501c045810203c0c511102003000b80c03050600b40000d0425102c541c008890001c1000031001000c001000c001490742c03030b80c504900c0000d19900b264080e450310f00000e40400c01103140819544110f514140c6547c0c241c180410b5225804a4140305031100da0700c02c4c1c0d10b03010a0902111207140a034940350003240b00d00600f03029207483c041d0b81d1100b044c03041c14140b000024181d005e100d0144040008010001c0e040b036a28102445203414a0705282c0d01a103400c0c3c501a03000c00c400c002198410300441e00505000d0540d2034540750714006000c514411104201840650708108501c03101410307502c405510016160074441014500000006021001b01441c0801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 928518516 1250 928517266 928517269
    0x60e040e0712020a05090403050901020d02030c190602071a070f020a0209010b03130c0b251218080f0604020a051203030403050f0d1b0320040b0c011407020102130e06 73
    0x1441c030100c84801c038070002a95541c2c00400c1d01c40506401c0150001c2d6804200414190040f0043c008401c081c0c0c205e07000310828030800ca0300d0380502c4d00d414405822540805001d140000e1600c21301a0280740010301e452840e5403107100c015045c01b0110f40303441e400d400f00184560002940c0b100c1092500107440c441c1515800100d02c41c005000710205042c021010503201d0400e00545207140341e0060b85c44000d20b03241d1400c03500c02d0308000001e078002801c0c04c1a030140061001d40c54a01c582e03000c070006046d03848012003903596101001550301e468a00740c4000a80d00b40410106032080c2d0308402400c1541000e0050250480858000c1801541c1100c00e8030110325002045a51282d010f00d0040d4841e07549000740310b0075106403007440302d00070300348a460b02d441c140010b819030b00032030592820402248a0500983c1d00f95a104840f1001300d0284010081c000042004040410888000241407070007d903401d20b01e43c3c82906c2000045c3c0d804501e00b00003041017201203000d00a000d82c60055440c1c05070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 928519766 1250 928518516 928518523
    0x204080604060e0a0f050a050c040e0d0c02030309030d09140301020a0c030309030509090c09011719021e13171b0402090d0210180905150d0f0f0c060e040e 68
    0x200010a226a500d50342e0b0200030f4140180b5400d20351204030119a22003d0a00760303980c801c2d840f410f60b00c80c00380051007810391030540301c1e0f1190510800d01903d19480505815181c1e40c1c0c08010990b00360000700b00ba180d0581d810312001c0e04070300f1a6100c030280d4506114020188100d20031400f8001e0b8070402c80c0c5880c04d904003d000700c40561618012461291500e42110140207006000c3e8001015a00b4401032041010207008007031030aa94401d8908011424092007204c00e6a49208070a0200000700c0c107204603030003c00c503100d04260a440002100343d04841c469000d500b0440c2c080b21140f0092102800030b401003003c01241200400d108245107400800315507030309810900c10740d40042e284c10b642d01c54000952545400a14920000a2402c80a4800d0200f0b20f0404003180c0301483c00f162480881c407405024201e6100c2a003e4405040706000240044000a031400e000481444c00007417103000c0f020b03069074440e07507204150345c2c81c01c00080e0180e500c24144502c140e040c40c3c402d848048000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 928521016 1250 928519766 928519771
    0x36030903080a03110d0e06090a0201080c09011e0c05070b0a050405011d1210060504180f051e0d0905061222080d1d0a03080a1125020f0402040806 64
    0x10403081e0b982c0202c800250010805000003501100c8082840844a01a03622000b04074954a05550300c6030790b48402c054036507100450080c0829045c3c00402d80c82c40740607000e402000f006051640000b6000072021404000c680c0320680003c4140000e001001400c1c0b280d44010610601c5081c02e2100500001e4001d004500032181080000b907072010f4040b1003078810104558015141103500d000209605445a84204200300800d0a00c5c500103401c4c1064400c100030400010104507011045541d400034020303034608183c2d071500c504a15810510080301c60151150b07c3c0c08000c01c04100740364000341c03c1c5000740d41f01511400c8140715004070703610126103d41d4030505200807403650003441c0c04400d100d08a000406006508045038107002da0071640c0c03000e902d00766003031081d41d280b03da1050444c5d50780e00740c4440200000c21000200f0f40100a940143d20102009502c032401c1c082d2500000c0c0e00111030344681d0707544680b01d412030301c154244181c03910843c8209072002c0d86400d0400a000c1e0303480001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 928522266 1250 928521016 928521023
    0x7111512130f14010b120d0c0f0302030c19030311030c0703111f05010905010906030215253e06030c040902070507032d03200136030903 60
    0x49049820070000200803241e80903601c15002c0f00c45180381c2410074000d040c3d0f2400f081c0104402c9424a1034010000f800c081e541742c5544e203003800c1d684103540d40c030346560000714100c0541c80180400e502c06602844041c2030a189040030007040b000c1800c0040648044540324800440d041082c0500704609800301c5840d65014200001081e040048103440c040d0000303820441002c82c11844054082c581d0032103412902414800d00090740c03074505180440368948802984144080e07a10300080041c2005041c10740145030300d080a10740318080e41002c1034650001100c03d50940411540d40300c541c1206088001903200d001005559103281d50302c07504601ca00228800d40010001441d8000c42c0300458000d003400c1c040c207549503403c519100e41d40f41101e02003126102c0218150b2003a0722000011442070007007500703100750325000c03e45003520903d007965100c3c84d02c0d02e04400c1091003100c0074015103a410440268200480c159411500c480c9864041c06c406507030141d50080340460340c005011000e4a40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 928523516 1250 928522266 928522291
    0xe091c09050d0203210d1a10120e03040603020a022e0207080412060b0a060e1c02040216110a0f050a092f180607020306010b180607111512 61
    0xb114000245414003a03010729044030f01c00c14009628101c0240074103134105440b0030600c00711350301954101070b0040c68008541c0041c03032541103a2280b48034070201c64240c00c074500000303521915541c402e130a550164001c880401d4001a108003401e604004241962800d2200030102103540400300803006580c0e281032030480d4012a511041c810340c00102c0300108020125050350024034500740d40a0040c2c213603602d01c55a041d440004005000b40c3c24209201c80c000c104800c0c24022046a40802800c0ea005a81040d030900c540c00803907285c100108011070042c0107010051141c40300300f0154082580106241160388402007006440d8a0911310940391903010104249000006825160218940c8141e4110000360b40800b410760002c01004d018030203011251144c00003400780a1148120007009405510050040004100250203080d03104a1152454040710340e143c0011901d030005002521240d0300d81140c2140f501d00310160410041c1004950307803c00709061300411070050014440c07c203943c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 928524766 1250 928523516 928523539
    0xa020306030f06010e01062a020613050405070309022409100c0c0329220302010b0607081312030807030510050a09141008070b070804050306010e091c0905 68
    0x180c0c2800318002c0710300b41208441e915a514010384495107401c0c4076803004250b0303072482a818000041100020f91030b1040902c01001e4055084c4100c540c03013105507030010041040041050f99590150324010146941d0120b1030394443d004005900c5400a40c00c0f078956451304080500d001c1c410f007030b610140b00071a500762042c4c043c40c4c41900c103401e90705002001c12500842c088204006664000c02c81140326005441074a01240c15560302d0a0070740c2c0b01000c103448100c2a40d13086160220304106684244004038a0030880780109a1541040d0701c1141c0d43c100210f42c007040d00202c0c549610041000740000b500c085143d44000d0001080601604101502e87d40058030191900c42d01200404016001707101e070310f035035505080007040105503440e8022103200114903221104555023080d02c600c880034010b05440c0c0600801554022042240c040a05000024103594140680c5000304800311410006140900030700d82040c0001c2403110010b4501d40311100a00d910101d200d0607100251040500e06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 928526016 1250 928524766 928524769
    0x30106090e04051204080609010e06130f140706050c1020032806060206071829070620070507030303020306121e370c0801020309280b0a020306 63
    0x2075100c0a040310401300010300010203000028446200303070700210081050021034460b054650340c05076640314251103002c0555002c1100a49140306461080e19591807040c05205071905050f031603481200030920201300352a4100090042101112441e142003040d483c0c1604d0400d403c19240180d50130140c004000112140f0100d0715903201c03a01004440c100c0f0300220b41c80080501024001ca031300502a410119090038051152a91100c00c1c40310032820701030402912000d4610048c0d5035001040405030010302001654000b41003050003000082281024004038011702681200302d41d0302180100b2103071002c2070001c036000003603aa042c078015070381340c40741000106103032022610801140966107000500c000300c0e0300c03400c00305900c1905503801c00700c1c2041c0952541955590714803003054004803d114031002c5141048100c0d1007400301609058807400601d08a80007110074044c1b07a031140304144600080001c0440a485180f00740100c01100340d80c540c1000e036800740aa100094005c00802c025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 928527266 1250 928526016 928526023
    0x3050f011a04030b131401051603051e09030c0d0513091a041e050601030c080a0c02031308150a0209030c04050a0f090f1704051f1806030b040c05030106090e0405 71
    0x31600411007804d41c1c1020703040c8640a428611003102d0b45816003403007204054040c01218880c0196840340d0241641c0d41d041135000e410018190709582075903840748083d2441c03042c895030140d008900103607102d03250780c10f003036181c4041045000180f0100744100d014440c40c01c0310403016035100785d1001c281d042d2440d0303112590644458403e0303803041c10b2591103003000c070440030309003010308036a07601307011315100d0000640c21030b80341d954844005041407001603c00101500304100c02002c4d803040342d150061404034066800ba0503081311846400205c5600c0c2d60500c0b03040c4158018150360390861504001e1300000e981c461034025554007603900d44002030024945130b405407105000d10801800004407a10340340d08603004c01c04d012a500b41449003184a48030000d42620700b42d600284c04101525145460012544460300c1d04004000c42c11965201c4282044030075402800503031804120412800300300026110b4580240041000c2413004101d4151f2010340d030811500340c0c4820f0300854845080c046d04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 928528516 1250 928527266 928527269
    0xe1c02070905150f2d121203070311130e06030106030501060803090109140906060f0d020d0c0221040603180204061e0f0e0a0e01020d060f1503050f011a04 68
    0x40d02d03000030403a50b4460400031480b140c40841d10303212104018000c10514441e9a000080c1020000361058100c44181000c480920f0000b40701d400d4444014400d60318003441000c42200030540482800490b0f901406540942c0280c9107066090098440c00e2044660091140b544030703481290100d080d5480c203500680107582c000c0024850151510b544039a40e50028043c0382c0000c03105400001c6030907801403450a681070003800da04191325404200080d82e04000c14850494070104026600001c10f407000340340265480c000469172125060300641045200c0251511b818041900c5801c0384c0b141104072801c0c0d5005040c0040e5640384120000108111640e00a40041c0b0782800810242002260303050f151034a91840000c403038441d51040844040c5108102d5903001140104c0c040b40c4c1d058020a03e42c0e00820001810240250826811707104203502c9079429003004001441540031003400380c03000105a0505121604007003590440c0c000301482543c2000803003884081401c3c004004a07030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 928529766 1250 928528516 928528529
    0x17030f0702010e13051e13120516054e0c030705030c06160905090c0904090c080c0f181f06021c1407110418050307150e1c0207 56
    0x10300f10607040801c4d800070030041c0c5414510902d03500c1441c0c001186156058890083d0b8124900c03001d03141c2c6d841d000442c0c038a5403003205110381480002c9080440d4440e240320b03640900c00600c07088032200500021002401d02c0107074100321400b000240002034656880302e01c0306e44807918504005215044c603803402510300580c4d003804002280824800004054105000c5138015070b0656200c0c00000803010348040214400b29070a424200304e42d14043c0005030384240703005541031400401364005011240d000a0458070700b5a0f5a000744850403041104c20701d9000246c8103000c0e81c07031120300040c080154012000f00b007034500800050900035110800448103410750175110440c0e4489801a46076156111f01c59a402411903460701d4180c80740c2110901641005002460040d0f1920f8804a0301418200b03e500300e40c584080c42c0108107644403606549005002071b40d1505003516000d001070003640000020281070411240844001207a04400782810242e04802e8081d40ea5040c1e04146465000383e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 928531016 1250 928529766 928529779
    0xd020a080316170a0f030c020a1505040501060501083112020607021203010e0604050406090b010b040f090203090316050a0f0b0604051e061005040e0c04030c17030f0702010e 76
    0x41003008001c10410a0b56114101920402d2150b41181680380202050040041c80c19001425264001d07484600054142c1c41074406606803030b181c08101028030059900903643d070380300704800e0000a11032480544030034a07050045007050900c2e505102c05207178158218aa019540051410044030361114045c3c0c07104030f580c000030396810080e48521044800300b0150103030001000e0341c1e00c03010302120305945203010b0444c000e0302c61406100003408010700840e883c0303664181d44008507803c4288540281850185613030b44508241000201404076070103050214014000e20903120804000e4449000005d400441c2060040c00d00340d250140000020302486c0512250005016601c1c914601c209000e50701885103446038081c0c140c200e004003100402d0b00c0d07c0b05010511615180d82144031a42c031615010b414030f0b4458000c002410004d9070442d83d8864000b504000b0018480c8092009244a42040c401c04240900755920785c411808460740380f070800140b6001f1a070046080c94091000907149 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 928532266 1250 928531016 928531027
    0x5040f0f090506271e0c12010e010605190e130b10050108130b04080a02070801140718060801141f0309020f030109170a031b0909050a020f090d020a0803 67
    0x2c1d074840324141c0c3c1540d00208020a1040e0041d104060040340072140402448103010448000c3c20340c4645140000c064040d448a800341c0b1381da0f035011042a05840d500016282084501c52421100154450303402000898034110386510340d000c0c41c5003140c0d18184820b000c0d599080c070031610034440360401001e076071440c000d00c81c840100c0c030010010b07500c0a0306c0360005511a4003014035840d42040009140c02c040b8000540040c2a0401400c1c000560380100e404054903002e5460940c0c00c40031004180c903c9050800072240c1d0311030f0000c050b1082c184d02d2000c015043c09401809460140503e6085101c02041c0090580b100492614004082400e00300000c440d00801400780c0150581a4440c446030300000103903240c1071040303060803680300382d6603100741400014a0005800070080041850b6665400ac00081078188040040900d42d5503000c000c28140480700c0221100a00540b601d03d1052045040300007048044404010085511114094180c0f0000f40588107540004000d0301000c1038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 928533516 1250 928532266 928532273
    0xa200325050a06110a02010e010e060d051b0403030f0503090a020d0f061b0507020d060b04060303050a09060914061c18060b041107030813120914011805040f0f09 71
    0x2184007552011242000301039580c0004440c0707102c2c000180501c030307000140b42c5e50040d0301904044c03500c0318041c100221040101c400003290f94000c017005240032500c5404020580c210307088105040e607000500182080d003940c4000b0b0010400440003001e0140020100740d001c503041040e0107085078020880303e8000b0300340c58000320140c0070503800c0f102c06003005100c64106403802c8010148141c41c3e96607508001640d02004820139030140252000b0f541d03050706020076100d40c0100c1c805503000b070b1a00355462280a500800c0202c02d0ba02890030445480c42c10300600303d00001030b60f211300c000c480007502c0300b1108203411101780005114445040c40c28460001c1c0ba00e15040c1034000031301601c400c1140e0340d09002440142d071621120340213440401c10011000038040d0007819045401046c1454200e0040e41e60900d48400340300c401d101081d0700100400c6104040743c02600603660a10381002040c7e680000c03840b0350800d50040030312854885401e0500444280d1154010002c0f20342d080c042c41200b8107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 928534766 1250 928533516 928533583
    0xc14010516020c010f1b0204020d0912110604050604030e0619030609060e0907060c0503121306050a0902150a051c020c0708070f09020d110c0c09090a2003 68
    0x140782001501566181a19541c000c040107134801149845084c03d994152102000091280c2c1c8126030041d030a1100841e541c0302d900ca6400f45a1240d228401005c98480c0003400c0f00601c50f01c6446c10b50b20002c02c020000b0004a480b94200d0360505102030174002c0040040c2883c0160101a0342485000c8046072520340c1c150040c81c102c0f43c04801c200b16403031302d5120a9881400c00c46944a09070f200c81c00800285200e010140c60301d034052000c3e40d0601d035034014040300340481605c0407221030031030421030300c240800307072041c03541011280c0002c10030b03d8219408250462080c11080520000204420000501030400c66695030340c440000403460300307081c07002c2000750000c1c410341c4103501c68444040740c0340d20005188011354441c030040301d00a51030100c07044003940c40362040910b61074076454110700e03c582c04405042101b9170032001c1c00c00780300718206005900b072004003103540720b5210001480120728020a41c59568041180d141505112000071904d06240484100e129002c0507440c0c0c45c180c4e5842 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 928536016 1250 928534766 928534801
    0x6110a0e0108010f1d090304031703011d040323041703130e0615070201141804050903030c0702131803020a060c090f12060605090c090a05060a020303070c140105 71
    0xb601c60a01503602d410001810201d580640800d9103414811100d00d01020701e82039031b0100c2c9800480e407400362250b507118860744050a03d161084c0300030005014010705917110b000d1003008030301d902d00071303141a8a0040c2003010325007480c0390502044041040c0d90400000700c1e0f01074006000702c84001d0648810007940c03035018050845039888115004501c1f1401505414020a8000c0020010b0806100019425400203200300e05005001100071200d00e40c0c90003600e0080f00324001d1601e098221418041660001444804940c008000f0000c03422040820364000c107405407074031041c000d00c080358400280080034400c0210401584100c0c100f50b80020666490b134801c13241030040f00541074040d181c2d0402d48c0030316681480392160606c262a81004490005800f0f1031001c0340d01070361030b0085100c6200580d0789404440300041c081c8240d0411808010040c9802c0d1622850203074400300c029124007004d4144010029401507603018446107038005c0c41400c100c3c50080140b41400c054002e00d003042e0b03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 928537266 1250 928536016 928536019
    0x31b12090815041a090703240c020c03030a05090307080715170103120f030b0d0804050307080c060f0a2109020406060c05070303181a030a1d030d0906110a0e 69
    0x2c41da0b240341080b202031500c90007158407031441c000c910201c0780301c800c00c503000600103030342446140030000c003003075034a4400f49419103086070000600000300050016140c40f1407012013550300c211a407480d681c6000040b40c01c00544c0d07180035a00c4501c510000b0b41410096400b81210344101c40010801c100c0c212420020000c60f512002c180c200040c0c40c40812032424030000d0034100340c02c0b200c2804240031b150140e00c920702501e0000748004900d4009001900c3e1b00d401900c3e503c03004103040c02181002c01c8403c010304a847c0c0106080100d00b4001f4219100c0c0701d02c454840d4001098070b0b40094040c54500101074011024521051070420185c1c0c02481c448906911507401c00900003a01c0307000390790300d01c000c5401c00080c0041c90305589080c3d607a001c4a803100e6018020405002540740400160700e4000340042003071035aa400c0030b04401013980c108900c1005001d601140c0c000304154000b0444a500c0882c400108000d4201c0c01c0581c0101910a01500c4400300051000c0f4a80d03805041d18285540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 928538516 1250 928537266 928537273
    0x3010905010204050f09010b160812090c09010819060c03150b03040b06060a0813050f030a090e010801020c21040306050903030a0c02190209040c030c2612030103031b120908 76
    0x640411401150070b100b04242003000300900c009586040403000441070240ac3c0851400d6151080c0041c519000c54100282d5008581d80005500c1c1411102d801080b03200014505034201802e003848803c11150000c11090381c035240c1041030750181d04044091980d081e9802251991060070807150f81c0116001ca441050070f03000681d503860000c0c19540500420760b0b0341a11a640c404000f540b40303010301e01c1030728617120b40d85070861141810401050b61040035511403220601d008281c5007200c1041e0084402b83e40184101100b6110015458602040554071660740ca81580c0d64a0329602c2182c0020748030ba41040100301c5100c6000000b50700600c01d0800c10096015107140481e11070301b142500f0015600e81035250740151400103003151b0024001d9400542080d500e5036490341c0002e40e81d200401c80e210044000b1401503005a00b02104080d807c003030015181c0101c00e15544e8030050000400b03111206407822003008034610103001495011142e01592100c214000d0010702d1184140140d510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 928539766 1250 928538516 928538539
    0x1409010c5d0204060c0b13020901170609010b220f02030a060e070c080301050d080405030102030f0405120c060403032c06160509030303010605160507091a37050301090501020405 78
    0x440e44203c4084648a40d92407510300300300d030f444441d0b0880103000b0003201e20300c0102010150b903c4c412941d00a082542c0030512500c0004071083c1008001480620180d1410a034004903442e00700c44401e0f44a640320a4481386d00c2c2c4441c8000081400812210a1a1000c02004030100440d4416030590310107040034601959108011100010000310050a9002c04c1c070042102d030030301540080740703541b1503e10503013007079100c101003400c80e081143c82000031003000c03040c0400c1c84000d105c1c00c1074450007907003030514101d5000c0795076940e0302000d440102007581d10744540c1c1500c00c0441c07852200c060090a2010780c0318010440703a03034540066418811180d030341142072082074011801c80f6003001001e005141143e19007070702a41c194206450301d18028205442742c5000481c107122070b1014141c8042c0c0041c40c0c01040c2c1c49500c50b90403003024140140c140d65456004c2241e1407081c040e45840020702d100000394460315001c2803803829400640c143d8240044141000419000750040e5802550360b2031030003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 928541016 1250 928539766 928539947
    0x20f06011401142a070803031e060337080304061505030d09030807020301110d02041401080f0f180d2d08130807080c011409010c 57
    0x1486440101154503044000f07403d0034a408403110203c0051860664400a07900e000362821f5600c103d6411001700b452000c0341c111041e10f014655008401a40104541041120940f42c403100410360f0440b15043c490000f613000c1001c0003030b103841544c0040c4003600e03414a4a8600081d052445546020800b120000f160b58100021540c0c0186415038a40c02e00a1450b1202c0c44243c2c06038170300780e0301552914120072000c0354003c02001070700d00071540165a24901000c25003403403241c801d802d04000111091090959002801c6a0050044050020303d500c542607100b4a445011112082501403a40b0070800560005038003134003110500c080001860407a081c046864180102070ad0100320f1040c0418440c3e40003604490049108103842481c10a41d611200d00c117801c81e0600c100b0b1a9164002189403440c42604940c110214800a00540b035204001507c0d5038240201d00444842da052285200d1425032040e02c50519150200107000702120902a4264070225804c0440d07111a00c024008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 928542266 1250 928541016 928541057
    0x1d0604090c030f02040b1002030702130b0907090f0b090a152a0c0e01030f080c030c030d020a031401050603071215060c031b0317060d1403031017120901020f06011401 73
    0x1100b81f69002c2c6140c0881d42d400c100c415400703050400101a59018003a45541320340000c50701a41460712440200e518000400003042403603041b040800307200b8409002c2035102c40124400b82c4519049901e91000104411610340c246051507400815010f54070080f80440080a1400c09009030803480c6546c2e15040121505442888000c3c00307801d299842101041d0003d003e0005800b01005032483d180800c005c0354690f81141ca000c2c0302059000651031341041c0c0610403e181b07603040700c48407407096145c003001811a01008007000140305000d51981c890648503840482d0300e400700c02d0541c01140d01c64070000d01d40c540c1c0c44000c80c0171032010074270300c61400080c611140942d40d1603640c01c15030590b2401c0f106590340e005001150400b0704422000c00241c03681a41800c0e0a084000940c1c0760710305030480c2a088001c0d580b01808542c07001c048803001090100b2490360f81702c410242540c3e43c070201c40c0101d14003c030007540740901c0d000d00e00011070b450480035100c04965070242d90f42c0c6072000d440041c4061 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 928543516 1250 928542266 928542289
    0x50603090316020a0f180b04051918060203040b04050f0a0b0105010315090f050708010504110412031701030f050d03050f04030f0909060b221d0604090c030f02040b 72
    0xd450703005010a4400c0d906818140346424805043c0700101951180c408184c2c00142e003089051800128072042d09400500c2003032041c1741e08550a0255051014001d40300e480b030740b01390104003629903e4005003690b0003800211816440a0215a42e01d01424680c51f8081c0c260b40072100c0e40546c88080b58010b00000304c5e840104d4000300085030a0346441c00650007805060140040200c40034400148509948507850b1101e00045c8046010300d0111002000c0c050160007103031081e0300e001c043c00e2180c00068265415115100b04100d1142c0d000d0900b5602c152400c50200d01110b8200c00100402041610944403a80b10380101c07540095107010035000c5e81c40c2142d806801091190000d000309100d00e440da0302c5001e040c24080300306030f16010303000141c40040d00a04902c0c10005600104e07900c0c0007030220382c22415404c1c0080d40e9420b00c0445500300008500c178101d41080c0c4d80c0800d40554660b400000764030340c45102c21100030b559140462222a20710030580c400d51411a065450342005821110b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 928544766 1250 928543516 928543531
    0x90b0a0e5b0905070306020d09030e1005070b060f06070c08010513080901050a17100815250e0d030f08060904110d05012408060c040f12020609040603030e030106050603 74
    0x1c04a903001000c0780141554042910b076803041302800000300392a4401043d80e4012903101080c80c00b00d600780030706944d41000c840340c06891b2804001220607406000e9500c841c2e400041c001081e11600001760f0001c824840c52540322000044071800c001001e0841000c54038840000d0102d40e0300c51802344840d0186402c081d2120804002c182861343c441c000038201c4641904008011413001c80210b580b40d0000c9480b0405200802c034284000d0008200c162400024500102c400c0d2800414040d48110342969241c0240101070f14290028000d030100d41a803800078085800858860800030302c0201002030702c0010a840d40e01250321400c103600703036a201347e03081030240c1c20702e42c00d04e814003401c224200741c20380703040d5138840901c21007030007941301003404540480200840350f040400306814010040c2c180c150603041000b0404c40000b564a6010840e0311602180070401c00e58000b0854502c11503407004c1d031062030440c02000305500101803000d005004d030300800c8959255018003c5d82e100554548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 928546016 1250 928544766 928544923
    0x1b02070b09090703140114010909020702130504021f020106091b020c011b211e0c0b06010302072a090e0a020618090a0519090b0a0e 58
    0x1542c00c28401c2e030b039000411490000f400c0c014103109170700a02403c1c0c01421414803042c0c0c1081656a02414030005000e1400b005c500d004001c2d40015500040141240b81d000d071924001401d568840189503500c1a500c140d030902d40300c011000034000c00c002c1c001d0710102c601e00b0320606094502d00b5003c420b554a00e800403c64101c20800569400a10002c01407800b80c02110580016621002030744401600400c3d112200c80f00742c00152240c030154440710110410720f0740000445a001181300192500041c0b201c407941c98110040700a842400c0001e0821304503162a1048030001e1407404502d14000340c03600c0700082d00d840c8140c095030803001f0703040c0c0e60764800200c99026240000050440544c111405591a02d070034002c68680c0d03004031501c01600d81d0351010890304020f51180c00e0700d0401e2580d41000107003000d940e0407512520250038180d0543c0d4850203541c910320100050f080803410b14662041c466040005130480019194144081c03083c46460300420300c1c5040d46050415001d140302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 928547266 1250 928546016 928546027
    0x414011a060d0b1c081e030c0f0304020d290a0627020702040905030a0e1009060e01020a1b1707121e02060307170601080403020303180c030f011b02070b 67
    0x7010301401909004031307800084103000001c00c0c4460013501000902c209881500c0b0b200f000d008020501c40030300446101c040c10420006085401d40480b040042003402d0161aa00c2c0d5001094841550300d6000700450500220819400000c0e112008404034483c000714603030351041d0795003080c3d504ca4440c680400d018a201905118806c1001c2c1c0030401001300c00500388078a580004095030030329042038501c1c2e0400900041600c1d03100c40710058885c000d0300d15280e0684c1406000f0304a8480307200345410044101e2061483d43c0c401d01106120541000f000700010700c0f42584a034152610344500410140800f4a14082d854041200740c101c0c3d0380c0070400d90b2040045c0d110b640003000074852046140204d03206100059a840001c0e50242c0c10b141d40d1b24400510450070900d48110150030141407000d41350401c40029400000c580e440040c0c560956090a40009000d02c0d004555255643c18010307403500881004e0705500c10660204016458200e00890344002d0740c071500113000300c003143c040c00c010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 928548516 1250 928547266 928547287
    0x10323031611031510090b0901060e1305070e12160b03100b0a0e101d061e030c0904060510020d050a0512041101020f0309010e1003140414011a06 64
    0x1c1100752540150366094841d569040002d0a000c42da80c600050004030782c091060104050980d00c01401d8a9501004000c60003400907000300d1052142100b0002c040034402c20680302c81d00c00b80a02d072200c1c3c40074005800c1c61007018020b04003040d406405090101220003c00c0c40000c2c8208118140c1711044040c603041c07100f820a030f43d000070302842c1011220750300081c446042c4001000303280d0740390340c4024891142c28200700901c23450041141c20421007641c1c07921052050042140c1d1950122403180d84d8400e0300d400404041e4043c488201100c070044100081c0c1c842000040101c560300b103504201407511107042003581c80030030b041400140e015014a001080c0100001c02c3c1a00c00303030410b00c0c2800c0e42660f201024250454044610900b0942e0301a52135804000c1c103180c024541018505004100b00000c110085008807544112203581014461500036440b41742c01043c040e5107002c0d18a01805c1c10016038800300184801503181c021511038a5421116522029000406480c9031039417081d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 928549766 1250 928548516 928548547
    0x5060d150b010c05060109050937050c0a0602341a070b250306050f1302220317040e070807140301150e0609060403080705010906050a0501032303 64
    0xa2681030101006400020030713801c1250724000e00c00040040340c545404954542402c20750030008110502494640c40303440540400fa140010509042d06061085030034424030f03000c0880c1001d89c1082500001158041d408151080804410314180c1d1001800103803400c8003407480c41d42144024000401031020b0041041c480b03484140c0700010f6420315109450b00c061110090311940340703103c11800032050318422008000f8000300d903400c0c100046450140840c0f4500c1140e00c0c2140302d2401407140c07801c100c625505403129803214010b0340e0301c00ca2511078080d031000c550303000544a1246807161001e980e44018100c6068501800540d20162a040000d88110001600c91030502005500d036080030003d01e8050350007408025036144440c01001c101424008880e49060b014030820002c2c042d8544968080b2000c8a500c040150703640c102e682802c078011b00c0552030080c00a8100301c140103114610390816410b80b4000c44002d0140d40c200b0040120401d895502c4096540051010703410707817041d12 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 928551016 1250 928549766 928549781
    0x702090106050f0903030d0207060b100e010509010c05012c19020d1e211707210e031b0c0906100318080703091514030a020405030f0703050105060d15 66
    0x1a18484d04080c41d680029080d60455213990725900d030302249003414003c890040303240550050b1150006920030f4000105095801104941800000900b2090507413044803c5842142c106000700a003142620f07880030321403545030501d0351684080d8024802100c021131101500443c5903ea141002825401d106130741c5a0031409503044200304150340060203104004110180c894180354149640c0c210986d890f82c00a0604d0400300044c4400e600c8050b40c90208168110b00300d030401c41005900c02c0e0740c100c4c040041c0001c4042c600c2c24070680d0181007a0000281081022101c00248081b803541c00c0a40d8881c90050aa9401101311011405a043c0203c002ca2491480d240c045110220545078003204c2c0001c0c2e40c02c8812440000c0c10900303242d0f10680e0900034040300c0280d0701000d440ca0030003c10410b80d084002808580000108074064082c2e41110300070400a4181c85100d140c1c910f501d500c84c9002c2c030055943c0e5086c00009101458030000700200380b94444005100132544410041c02820782 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 928552266 1250 928551016 928551037
    0x1b0307140c0114010f09021c0525090501140325270f05031c08092407080901020a051c0b1908010f1a0108151e03070b070209010605 58
    0x10014002650301c2801a96007001012498041c0d65250814040507180303e03a20441d00d061050280c140d040c208000c2c1200319285c0c440000c100c40d103603010504103189410b920103981041d00d18400e06901d40001d55034084403400d8a40360204a450325640c03003e0301c030131103045030748a6008101e800100c20304960040865401d18000301d07446100d9001e03c684000300c16201038641d100c04410841907002c02400c002600301900580050180114404d2201d00e000c00014140403081001601281c4100311400c0b2504800f142c0d01341030701c112840c241c80c0d514103a5560001602c036000080460740705000b00c079042c0c00c0030740d074542ca80701340304030003910315408103d8208040e80c03034546000d100da8034030702c8152000740d85480c010b0103c0d2a10418030700f100c2d0b620141e03003401402c5c031840780e902d8040d03c28200c007412401e081501c0300356140303203801880009500e505680682c61400c2d200c074404804281c2e440a03071080c2c084840050b2103105140441c040c84600960001c0341e20010300442c0d2081010b070503401e42 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 928553516 1250 928552266 928552307
    0x70309030c06020102090406051509060d1503031e08010302060405120705120d110a080f09040207050a030305073e030d1a0103060603231308030f01030b1b0307 70
    0x44039034607504190060340c0200c005030740204203d903c1c0d2516200300c0d002030000312044885000d13030741100400c900902c0c17280d42c814900071035440f042c04195041035400305041010681c6d81da80702d1801030001d4990f440c08240304070340318a2601885001351042d9068030340041c1020b0915240904001000b0700c501400c4500d4043c2302c00004540c2c40301903845a00e4015078020381407180801034001c103c103030301501e2031209602545400e0089413402c021501c10380c1d040b1400582c0d03101e11b440400c000c2e11400c0c100604034410340c0030900516a040c0d00850040b422580d036404501200380f8800a00411491006031040354103202c03100c9424400000c1500e030080f403040e070b03083c8802c210080c02250400e090a201d081ca00c402c00d00741d0b543e8107100304005030105080400106500b40344244114003240700c0000c0401210700421400c00c0320203d0200002c1e80198925a2494009003a2210060a102c1214280e40d240701048401308d21000c1c003411a080710f80010700b560343c0c0c1c10080f1082111904000c15004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 928554766 1250 928553516 928553519
    0x32d0f0f05090606180114010f0e100c0b0c310b0d06030b010b0f0717131d0a0e0a0605040f080d0b090a020f0409021e04080a0b061e06070309 62
    0x40d8980a00c1d0321404000780030b00160f140c0300043c03203101006610702c9a054154140103101501078924210125042071034800340300d2070700b01402c0d03d03041c2103d4022644120190400c1078102c1d4004e022001e064480c1900304403d0322403e00c3da83d014007480e1600da6116201c407105d0048240720003050b004407900503120f03420749540e079030b0040d42c540c0c4103950b13200a00b91124000d0042c0121040624010720802243c1c074685110290f00c3c45550142140040503c0c2c0b0405030424005480800e032111950300380000510b9543d50720303071600072a0201e28011400d446034000140640120300c10220f4142e9460702404410a00741e4072240204802042215041040b03204070002c04c4d0440040c060103c4e9503080022041d465030100301020074000c5c030310013403680108a10b013901207400c4150790403521406170141c6c0340c0e800c5140a044040e1140003800d4420305c0800d0026004600060301c60146004402400d8651a44014400310144010454052410b00d084c9540c1c6070901800400d50280030b86804e1903000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 928556016 1250 928554766 928554791
    0x25020604050a0816060804150911100c050106150507290c04080f0609070b0904061e030c09050903041208090a03050c01020d05120c0a1202030c030106032d0f 69
    0x542030304070309644e40c007000c0d0010940b810290b5030009012a414100c80c40d05c2c180d542c6142e00005604920707105920b92034400c04000019030f020740e1448009002410084c81c0000040c1072400c000003e072850340c2001e80000d000010f413000c204182090340d80d9a032920540b070f198100c41e1054964145e04240304003200180400d01c50705254040c0c07051080707240d42c032440d1102c010b00d17001d40002010005e030005414405070160000f02a01111000e590321070719003c2e0900042c00803e40c3ea031002c0e503204c01642c9030f0b19100c1d4031051100140ea03c107020b03002c422501d071603aaa084980841d81448a540104018414580301c003503a0f9075802d1085001526103101030300842c0d0551642e40c000c4600ba803024403003504c80c0d0380511001c0b01000c0b09180460800c415240b00110048000e071000d240243e0000d20840c3c40c3d4460707445e440d10110000702c11365aa08241c44a50790ba40c1c401d101e8840000e01d07054a002c0c002030540d42d403e0b4045040d195201103600c0010805000f0002c180c0500380a56841c080c41410307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 928557266 1250 928556016 928556029
    0x610021f021201060e1305060d1a0108010c2303060406270606141b0c0603042a0602060402040f1e020c0d090e0c07060917070204112502060405 63
    0x2030082040d409030300c40d80d21110144038100180c004900b40640c00003004440e49800014403c0040410008610341c0c030385102144086a00b64005048084000e1400403408001083c40b4101c403c0d81c0700030000188801c0d01100c05240d007a040b88003400503421181158040b040140d60884002040020346554581844ca555050410381040580c510780040c7c049041074426a002000c01c1e0503c6090290038100000c058410a000d1f5520f03480f001e00071003061401000f08034030680707028040503500d0920342080c001450310f9521011403100907020030408011101c6e0a641200c0e0150003e1501d51196401c11000c3c20030110308000c1e46070380340100010564004030010110900d00d00041e9150001416113041034800c54200741440819002040400082c0d10500e0380664580b02c9591100d17460300c0c241010b44803203000035203030032040f5800d241500d040d4001085c0041c800c990070041d10111003021540b42c09040082041c80060810103410990144080f000151000b007100f40340070b403104002943d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 928558516 1250 928557266 928557313
    0xc070b21060405011a07060605030f1b060703121802061602150f0a05220306060501020c031c1b0b0109060302090a1b031e050103081c14061002 63
    0x18400105011503080010040240c00580503034080c002981011200441c10960441c41854004c000801a051002a51008020f007900405444105030b41c0722086555100c0140030400701c0a003824049880d01c0d00e0750440d90600e51584400ea01800c00f40d600d00020907080c1030170b0311010f203994204801a5070f0903005050445c03c20010b50398040c1070340144218200034249400c10940108030b002c0050007480141d50001d00705e41b501c0d07682d90326140d107905220b456101080c500503010300404802c002c46a040b43c1300341c410a03070803156021103040805540d491025882010303e2441041020818401d102c030110003114105050f03989034099403100900c4000741d0100114030346c1e500051003146004042e01d0f801000c041c0f828044010740b071280c60000e1000c030802c102459990b003030300da41c50900c040881c0d1011240860030007166030740c0d040141483d44000e90403010740c0080007402c0c441e84842e1050003207140c400c03006240c481d074501080c01010703000546041c055103d45498510100201039031060b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 928559766 1250 928558516 928558537
    0xf080a1401150e010924120f0b1e130b24031515091c06020a020708060c0c1c0306030b0c07030f0f1b020a0f0801090b06011707050c070b 60
    0xb403100d2a06001408000690440d90400003002000c00484084040118000c007041409900c0303001e09201c00e440308509505070290450071301018800e6004c01e07500c01d488141c42038610311507204040c0c4a034015200c0703140d81c09601c410781948480c01c0b521035511020320743c0005071400108980c400c0c4868250b07241106252001c02c1d0000c10410075a44001c12880c0201c0700350b500070f210300c4020444d800a40181c100c1e0310b01070f04604411021a029546100b09034982143c0115629204084020340f070322001c3c060306180d885038802141c6c10714074000445000d032039424050000d00711b00849181c0d0003412909a001050703140c090202c00324500c00d6009010b19811603840b65507100c0c916000d4100d00022502400303107c0301c07035101e140081e004008041455210303d500901080d10f0310005a150407a81c000910914000f900418424015400080c07000c0c041e9040002659840d0011101803050020b0a41059101400b08560340e0151014004801c840d2040d510384079220140c0e625290882e882c4c0c00b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 928561016 1250 928559766 928559789
    0x901051c0b0d060f0c110636030c06010609050d080705010f020301080a1203060605040b030612010e0d09120c0b032a0a111b06280509130506010f080a1401 68
    0x14141d104c0b03200b40e9034030f1101030420100a0400d4221145c54040082521291002c04520400004105221050050700c2100512500c9200303403000c95a0f07401c0485041250310900c800418164000c00e4054102d6900814800c01100e2030340d542d8086400c03002c0c2c1140d844d034943d641c0010070212400a503020308522401807240c2c4a9505014100415400000c0141494031030306014150340441124150380d0301d00e28841d40d0740c0726840860600b12144500088079480d10018411040010808107184c000c3c80d501c120815032a8421700400b201c14a00041c0507074100d400c04c12005c0c01080180d540a542042c1d8020048034448403c40740c542121201461300c1c0c000a240030f007094104124549503404e0030014449003100c00d00344c00b0003400704241d0b28800c0d00003003800f40300d2114451115005480810030040c680f009000c0c003408541156024911403d0120480038600c4c0f018882d0b140300e81416075030200c0e040c199503016154409c0140207101c1c0700344c49541c0108000d000020441c0280b050003c034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 928562266 1250 928561016 928561031
    0x7110604090c1d010203070311160b0a0306051509210d02010203010501031103090718110c0c030c09070c030c0c12050d02190b0103200d0c03060506060901051c0b0d06 73
    0x20f00703150800c0c0544250610100010b0b0459a0000545041c1a8142080c58080c08420429071410070030600c050003028402e0720224042e0041409050070304c00580301444415155400c0101103051680b070130340e01040910012460b442d1844041001804817a003034000003000c510203c0c184180341080101603074000004000d1944d0603c1840c3e810a80000c080781107041201040b5107914151003004e10000c1c8680b420749604203682c1c0700b07003401c0d005042b0313065465100300203d40c1c46810a1080c98420300074584003460780d00304103225510a1076541d50b002056140c0307076014ac5201e002984140c80c0a24856404240090003540075074100e0f0042c40140b80c03403190840020300d8000403840f80074410103540c50300303400240c80d0000541925805a10f0518400d5403619010b5100004c0041c13641c40503680d001c2006000401d002d044c20b89000e0b010510080e0386040600000d48550103506001a60400038031000100b14000c502c0d041d1340034170002c50400d00850014141d020326041c02e8485a554210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 928563516 1250 928562266 928562291
    0x307030b010815042f0d0b06030607020102072d150b0a090606090308220b0307030c022803020f0111120109050f0c0a090e0c0703082a0711060409 64
    0x2c20041e103003d04041d26043c50655906401085e030400d04c8461004404136030315420091661402c4485400390040d09541e070141004107442c1c905640b0745d4003038011200443e4887e0701c18000c0f0340340241c005000c81541c2c00044600c10b0071441c01020582d0071000c036084040040c1c030034003002c100c0780030840c2c010500040000400140070348652003103001c03e00d0503000700042c6800132003410407640c0101c000780c0c0342ca13480600901c00600b0705190228a0402c0d110100b20300201c1d401540c0240b40554041140043c640010303691a008403003043c1c44101c1402d85007200310501880c070b440c000e210b032040c2da00c00c000d500702c403d09650030038081240024002c9a003002e84c4500a41c1180100034200d41402941450038605111030005451815140c5000400d10480c81c0140a208002d0a00d52001c15403480e0a00b0386510940100c0c004500062000e070105003560440c4011020b00402161002d039048002d0040c9049a4041c5408840f502c0300866418000c0d6a0308002c7c00c000d0544090201d144804040e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 928564766 1250 928563516 928563523
    0x50c061008070b160b04240605010c150e0f0d020c0406030b07140c0a0b06040609090510050718094b0b03010507030e061e150f0307030b0108 62
    0x1400058000c0c09240100950301d00020b41000b12142000b10301d540e04008440440410010030703010304881d60010a100c1041000c1c2c6030303103181103001020035202c2000c540c105c400380c440d03902c29240043c10b000e42400c046480304500d0a1900464030000074001685100141028070300c1420070201c2c0c0000c076599000030f030148198944160102d80c20010541036640b20340120310081d1075002044609400c6c40700c070072001740c112064128a8002c0b58001202454140a06a402c45405004501748680064095810b008903420242d20401800e0f01424a61800700245801030010301000300d141510000582c1450462002c0c094108000c41c41d05510b041c41c8030900102103500e00d80c1590070810090a8400b060411b4020b810b10b000003075a100d00d4540100a80408980c0603419407030b01045c004005e415a0021143c900f000007950500d503120103022007000da04200c1c000d249130015001030551401e2008403e07440c0c3d00240990720b83d80d540303030109151049541048846524010061015040c03c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 928566016 1250 928564766 928564771
    0x11010807050a0203120405150115030b12340f0321050d02070303141911041203050306030a0c06020f01050609010501090b0c010b1306030209090d1b0809040c050c06 72
    0x341002454000b800d80d009540c1d100d240d65002c2c2403104072010604014040c091841000020384030442a561541c9490b45099034807071007200072914001d0710740128245960040c13007443c100000342240703045540410641c889d000a03103e5419840e134070026003081c51950010060b084490300a082c0c03500b10315003440d036420082c601c400340d0400b442101203c0303644401112302001c98500b02507160822450164041d1600e0a981c0c2002d600540402098040c02c0b4440040d080c400041449091031008040240b44114040d24120200000c095070100340660001e581203100030701201c084420603211200000c0040c2c021000513085070f50742c908624800d002c0c094010608449607a15035141c4800644095054802d00040740e0b80491a000f401d8020342c080100080054010804202107485074030040caa5408201d105460100100d600342d80001901a0050078603241c003920381030b47d418808903110f54010122006d2108000101c131a4440d401001d003000001d0701e5598444007100384090a10000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 928567266 1250 928566016 928566031
    0x9020103180f02150d02190f0305040b061207030605090c101e03090602090d060b130b060f2d18030d02070614070609081201050d05100b0105070b04110108 68
    0x4000760300105501c0c031000c90752560b04480307442428042c102e080310a4080d08840601840c4013180100e46495481b0400041b01695601d8611300d610403001942201c8050700c026000c0c002000000d041402c144c0c8403c056118490210749110360780fa0f54182c10380300221841007444d00180080105401d180803920320700801703401c00c1906c802c00800c0c00750380140740108400c20103440f00400c0307003404501da044503400c00003d8440005d5920b9824050083d10100d5a0140180311101c1c40141c0001d0343c0c800d89218850040c0709614003c4440b096a03155000070308001d034803000b0240d0a9a62b101d4818102c0c0d50310392208045921882d03540e80c0200620b89540486019400212441c00365543c04074003102a280c1c00d0801c5031604010b42040f505a000700c0c10001d0182745040740340d10a00c0094009402c141400b000700c0012a80c0311824030003110300600b07004040c0d901c60340e40d484000e4496001f0720301a403010b2514604002d915147c0c4109060155410b4a00c1c0754ac01424291070759222003074a510048 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 928568516 1250 928567266 928567301
    0xb0307020307081602040c020d26012d061e0309020603161803060501080c0307050a0308071502030a1a010f0f0c0206040905090304090e161e0504020a0309020103 71
    0x8248001035160701c95840002c10070301000031241841c001040c108100f1580150003040950b12801019540c2c0b040b40e8003071130100394907a081030501c401940060300e5250b0400840703801c991030070002052400d120800513810413469031030804544914a5182c00038055a9039041055040e02d07035000100383e812860104040c00c0c0070098003d41c4484003202c0d001880700d90310b581c000c9070b0340781c0031507020a0704950044100102c000020a0011a4210905a581c00c4050360311400400b03041680e22040c501c913070ba808c000001c604001107498240544043d030b01440241c00c2d020400c1005504990040320072022403a50380280c091034421080010f84510300070b0804401d800c10f00c000290200884411100070423914104070070840d110a015a402016981828406401d00050440c0c0b42d81041c01000303c49807801d0b200c05000c11000980b007100194a60b402d80c506420302980350010a40703969420744050034590005695220b600c0106008962a9400101e2503410f03c001802c4e00d01d914030102e080ba2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 928569766 1250 928568516 928568521
    0x30103080304022106090309031b0d1202070f06090303020c030607050315010e0607030302031605090114030601021c08070e0a15050901021002040326030708150f040e010606090b03 79
    0x815560481c2d40050f0111000404001c0707440d004240111407102009890055800b40036690070000003900c0000003c03815121800b91310490107040122031601350f640540034406030b20103c1c0421250804d06100740c07054802440d115200d0296a21441e0300c0070000482d000703c20014107034140849065600103d0180c400f43c1481c43e001072a40c000a0040d920b4a80481a9052103a003c1c80c132006501e40007924854980940d420301a0007500103c409000500800c5101724941e40316008484070264144c4407247c10390303038041c40900315030001040941076214000400c041084a440f054000d85402d40da054280d182c1104010025041048058041c1d02e51100030b00c0980c002e5485007820b0f040510700240c440100b180100c0c501084d181c1040802c1d880001c002c01407111503041030b0124440c144034a04042201c0911641a00c422100c00c0c00103031201d00417485002950342d107111144001454441400034040016007140d5643d0071030714050f03541d50000c014254010240d8030043c8101c1e08024110b2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 928571016 1250 928569766 928569773
    0x903121e041506030b0a02090f01260a0e060412020c042c010908040f1409090c010e030309030f01061a04080d0309031707050a1107050d0209040f140a031202030103 72
    0x48018100810b24680c0d1910510035110660051008641121000ea442e003040145040254020340441e030003208441002901035006000c1062190f00c0b54032000c0049955411340d5000980250603010032075212107103286510401c011032802030740196030102c85031051803000f0345014040c1403124003840c24840090140302844124009202015611103290b861320a5103500600c107020f001010708001003404078040c42882c0903d03098031a040f5401084181360020020030000c03c1300c00d9401a40100f0781d40045511408004501c1d80010742103900742a0074200003410030b22521001d8455030345d00d1004015a001c0951202801030151500620b0300c0c0c2862510b60703d40c01800218401d050300d842016003098441c2c1c00c0d002d0134500c280e01810050811083c0280503522040d5100d0000d01c80046034490810301046500480c0d03801414811605119401d0060b8110300400c15691007080f90701da5400300b0302c151203000d01d8032202d50103440c20403c1440c0103441110461600c0c8019441440140b000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 928572266 1250 928571016 928571071
    0x60e060f07120213080d32030402121e0c041805071a040906060903020f041517030c0d0207060813030503010501030209121204180525090905090312 65
    0x11985001c101503501c003005010000100000c3d13000e840c26114440d00341781c5030fa1f03012211864150411401071403d00e440000c100f00c0d40600e41c01d00101c5242040807800514040080303503e14810300080c1c0390444007420100882c000b104c0a85a207907040b05030b2a0b030303ca00e4a4801e0307006090590700c00501c02c12103900d46503030b160807501030a42822a44907491401c3d14000c1c0560b0000c1542034000d1201035100c8500401e85021803000b240980040010014540380034003490240e00d01442c040c02c801e901d440c99290046078102108501404208010090464113020030703204648584c0040500920f0f2040c014460349005104025188140580f5400264424100d03811540b0919001d6140d010030300c009010981140745080183c0728041c6c0d50000c401c01c0c20043c3c4200e4903403180b0440540c540380c4012003620801c4441d0340520700d194110818a0807808900d02c1000002d00d00f56408948070016001120700039070300d4007402e60002c2030007500079030541c180c0e82e409181c05500d000d9640007011f000c5078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 928573516 1250 928572266 928572287
    0x1d123c0f100e0715030c03060504021806090402070c120c060519080c0f0a030501090c020a02090a050406020c060f09010c0507110d03050c1b0307050a050d08070519060e060f07 77
    0x2a5107403a00302c2d010040c41c04000302e4014040700c440c824120503182c0d070050b00a02c00b068190002c0f0b81401c400044030314191080c1c5040005401008200070003400410090758030810138142d00c180e0900c06900032540491124000d84001441c024102101e42800c1079030300d80320340c081006c01c2001c00c201c0310540400300200011840604020f03000d40c0f1002142c02d0313a0300801280b4141e550020840302c080691540086048030481201000f282c1c528401c1240c6403c80b2400280d041034811000c18503c0405a01059015000c0c04e80141021946114581049802ea0301c9103c100010401c0c042a20001c3c826a4800c40880c28003e290001c5591100c036403580100ba02d61155100344184001e26008004980444440e40103440390a00c0c41c40350485a03c019000190081c0704002000c20141428002d2805556006041060040c000c0c2e5494130b890344041021505805280c0541d000a451038810442091248201140140e40030200d58a0408000e01c6103034590801c00500c01c82c0d070b822501030503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 928574766 1250 928573516 928573543
    0x7080d050a0204091406150f0703200d052713090f140f07050604060203120c0f1305131e1104030b0103211d123c0f 51
    0x3655a00c60011500074000d6a200710310050034200038070106018442074a00c0303240125481c0620b00300307581405801c0c0c06002c642e401c80c59020043e51020a010b2880e020401c00041041c021070504002124100440841a2004130b04081030540c4d68110f462921028034110004044200d0350300e03000140d070360418014815290390307900b4a035420700c00000590000150440c0c5986016508006c01940d241024a0100031b2801103072008906031410301c0480c0d00300c850f194025810055880e40f100c10b120000351071001e54100030080070004c0b207183c901400b202090111012501440c0c00b05000c00070324410600750010f89020a2505400c015005071750030105d900c070f030000c4e80018411b0007031868070440e040544162a280000802c01400d000703261010045141e059045000c0098151803221000d42000540402d00d60f1100ca0350400c0e61401e0200703004142140d408400e413030072410410300074804000c2000e0075203030b14102c41c801802c0ca10883d0300a40e8024101d40024810443e01c494002400b00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 928576016 1250 928574766 928574771
    0x4051b0105090411040f0902190e0607060f0212090a0b04080307050d06080618070303090302010c2307030204060b0702010c1506030b0106050c15070c03081810021e07080d 75
    0x12129900c244103a503407000029204010300d0040d0308003110b8a8010b482034040400030050b021070440014025905110913003d420040c41030a03c805455030607400c00d11980110081c003041001c6007141c06002e030700e8500f2507070041c1c0d5000c100070503980d40d00e4014684030895122010200015540140003584071350490151601c0c3c0d01c401e001150180301d044134010010341803d0b0f0100309060041056170007880350041d81c0038500c911480b1951601803912000c0d02246001100b0005940107404203445184201495541a26002611300c400807419407a90a290b100110a1045081c40c0c410300e8007820b0070501050800c00c0341d500080a2441c2800000d1420320041c2d03802c0600c083d140c02910107540e002e020602c1940e1203410040050b040000c02042600c1211071160610b175544400b580181c0c41955a080070020300d4074160355011000e40103817556041c030b04150030a49414405900c1c22035540d140540ea6102508800c40c1e810304002c4c010b00d001c07a0070000600060b5614040b900b1602021601 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 928577266 1250 928576016 928576063
    0x1104030b1605040906060201061401030e07090b01030f09060b01080601051c0b040b0307120317060d061505101214060a05130b04320c1b070807030302150106080405 72
    0x80310b00d80100c0e4407032082a414504086404e94043d005503060b00e2450096880c6d011060004505549418140c07144907000400240050000c50f0090501054107040102d000009694a20210b49004005607200344d9a5a911000c642e4000901d82e00314101346030060a00c070178060b085046408848448100340d6079001d9012485d02c8a0b0096420624010300765000ca641e01e651490301c05030060000c500040d00c030612000144d02d1511074600454000c4c10031122100590303688001480e0030380c08820294940040037a071541d8920008030860030594415814441c4e0a603124203481e10500c40034000c490b1801040388944135607501c4004c0350f0b011160a840e49400a030000024024000d010341c010707040c2101c00000000c1c04091200c3c0b1440350030b030100888070010642c0c540510903107030900746070380c200034050b5130349819900b4600c020f40210641d003013155901c10482c44c2c65042e500440c09a084802000c0303642a4020706a030041030f4600b4099560314181d5210b42d1114003a00203001c000190b20301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 928578516 1250 928577266 928577311
    0xc09120c080106090b0a0914060402250c0914150108060d080c01020a0e10121a120f0f06090709050403111f0b2205041e0b0a1104030b 59
    0x2030341001400014000c00c002c68407500c851000e41031421005000365007111001400507031a200c0c460080401a2854100781c035803400f044080d600061500e01c240350004040b1400c2e030100121040840e114060700c5542c640390244020950754003e4a14400340e0741c1130100038110114075100d0300440401d28080c0318941da5500001c0d0881649440a01442008111981c41c0c00c0154002d1141440c03940f00e00c081846514100f0028003d00c001920008111b41c1040788200c406070031403041d2844040380348000414020104100300c15422403450154040d4032040507100082c0440f0441c4012500600b0940c500803a00302c3c1e43e61014840c4185039035a59000805040c400c61404082011080950315840380555507907111141c808024480300b0b2601c1d0803203140b45428001c0c00c200d42d2400044014900401b801d14008001c024004c1c0c8030f603905041d280c0f1f09410060040203410344501c81924403424145030440031110403a285d0b9000100030070003800031441e907803002c9a00800342c10004254150300c09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 928579766 1250 928578516 928578533
    0xa18060f0e030a11070f08102c060103060506090f15040b0a0303110609010203090c2b0803010312020705010e09130b1303020c06040521010207170705060a0c0912 71
    0x1c101c025000200f0100030700c942c001508040100070400302c40c0455212001c180e0a008203102e151120390045400201448030354200c1104800c41c0d400500e03480f005200c0034010750142900c1a900c5401a02c010301c01c100031481015044181a034001000b840d09500890407008098080500e4164000d0b5598056986412554080d00d0140030101d41c00d6403442c01800c2504980c10850302d41c014480059030b0240148240c03482041000001c2103103403061414450328036202802000d02c090412142208088185100c0351011302c00c00003140d03a5071560920b012a10300201030781c0110f411954003000103a0348604894069142250254001c1e101d643e2140c2e400c8045010091020100c40100440900242c0700c01080c1340c000d4090b503401102100800040307210310701405611191010a01010003a0071052081c2d03006035100040c5805c00c070b611046046156011445c40035a070008a100810200f40b2075260402402e000900500e03400700c02c041c0610601e806404140d04c40c400e50b4605100a41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 928581016 1250 928579766 928579781
    0x3051605030d0614090907151103030c0301031419140f0f030c0d09151115090a0317250c0b040b012103080103060b0d051c080a18060f 59
    0x1011240c0d504502c241000150203a44030301081c5180142400b50a41800c4440c680300300c403110040c00c03001e0708003480c203c400100320300020304201c040d503080d03d01d60004000031030003030f03035920a11900c80d85145040c016100300c1240c4241c1c181c02101240100c1c041048502c010180c1c032050b618140800032640c0d07451f2200d407643c10b501d0351081c1000480c5106010004010094244040e0369940100c000f0940b0342c29030038844c010403c9800307440c1c04a0300c0d00c01c20803551030714039450988403911822187c1141120303068608001319001806000101508941080154030190044030024502030300588804c060b10007204001c1d0a0083d004001c00d4421810300c105541d100184907020f080c075082141160b44240505100031005040136083c015107245496565a4582e4560750942e0849e9a500050700d5100700e0b0715003000010850100142d02403084281c041c003074035135800034054031100007411000041e000347e41070b61500b02404000c07040481400c1c0300a802540201d45410f08004080c0100000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 928582266 1250 928581016 928581023
    0x70602030a121e0216110d0b0105040b0f09010e1911030610090810051807121b051002010c020d0305070c0807170c0a050111030f0708190c091a0702010c030516 70
    0x81300380e030540801d07005128060055191441d9020311401f1310800c40030226024200d61508401080245800e4009a2103210081c01c03a0740005c1c10400894039894003038200c001c2440c1e6180c10000490b80320100c521201c1d20340c00b81489030104000203c140d910020b07120034020350031225842d0940703002e0554030008060080849410f4024200000010007050301e541d0484da80e50f120018541c0d6001840b1800d0301e080c540511074a070030343d0303440203504c0042c40e002c22440645030b04006102d95502c0e0300d00c82d007000a600085030300340e41400007c0c141501070780d042c418589040b0178058040c0d44040c088840a60215149595010302c0c00c1401901401ca0501802103e0004e0a183d0490000c991551942d00c00c0009006041c001214040700d070004492000e420003403040014100340c450030215401c0178081c40d4665910f0041080c010641da140ca0a0724080342c80180b003009040140300310800c14581c00c0c1140c908001e81c590000300614100710000d01001070104203070001d200c106141d0038a42e070b403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 928583516 1250 928582266 928582271
    0xb07051c03020717030103112701030609230706031d100b090c030105130203060f12060114010c2006190c0b06010302070b0406020c032505070602030a121e 68
    0x188030005000e540201011500310340182040c0c03061011010541e070682c2e9100d201d0880790600030090010301c2d2900102d4a045036805140340075507210540040340a94040d800c04220001942080e00f21401100300440070706244011588814074040b52640c1659990320340840c1c000f480845842c001d403c007100c001c8041c040d0f00900101c0441e26032060001d20416202800140e030f90a0000b40307607010911449070403c00640c01c22100c01d001d58011a804140106070b41640300700c100100710700f4803009208460781e50150006000d030428a002110300d1103003d203810810200b031070b07031002d00381130103070080c002c085050104a10082e690344040e03030201651041e40500054011074001c10440210f142038600c1c07554480031403c594031074002c0341d2a1030f03084039a40c0c801ea1102c2d03951038020b40c80200c40310241d00080c041840d041c040329810f40c3c9004020b818803441f01000d4140241045010b03805041590300400806010541010740051050322083d000140303598542821001e40208680b450040361 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 928584766 1250 928583516 928583563
    0x110a0e121e0703060c050f0d02130803121b0a1409030f0303090105160305130b100902070b06031506031905030405060f180a06171f03030903030f0507020a0b0705 71
    0x15000980b44040324002c1c036051110912182066130240716800340c1581e1604104160741003502290002c1002c440c801c01682d4100790780f60707119030070354020311032860104586c90f050040f011a8507680502807075059075038914004c161107010b07258400035100c035007801c5404603c000f419501442104440c01076082034940d07900c6d02c01101ca00900c81101c1500c100c00030800d840b000c03e84240309940c03150314000d05480704180203841e078100003003000708050303c02e940100011644075594005807500a00c41c8581c2c202c1ea0401c4400c03d8100307186403c808030107640e40010005650380024403c03510720035401503500842d142d410036a003148076540209802c00700010342c00382c1c4410000f00801210180100c201e007449040c2c4100035030020705101d030314001124120020117401e00401d42680080440c42000f00782c002d01042c0c0c000d960300d154020350109040b003508000b8180c0100c100c002555162034501e26119240e0b001498481443c020040300e00701c046103150401c80204910104074445107580d0b003024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 928586016 1250 928584766 928584823
    0x20a0b04052e06080a0308040320160303120504020a030f060603230c010f1d01050d0c030b0108010e040c17010b04050406270c0b0a090e09060604110a0e12 68
    0x1c810038050b6541d041c0381410015241c64085114040d031941a40c0d50080c44e1219202160000d01d60010030f80003050007504100b6100003004800c0500d000700d40d49240c40d07491800c02502005182c10642c80880c1400e0400c00180c1c1c0c5c42802000fa2540960120f0403a070303081c10048002d1a05410007041d04804080104590081d038614600a4092400300c07402c6200440045414000c2a100c1d03502143d14060321a0310210107074a41c014900d018513110782060340d11124202a1a004070740e220111f41d4801c070380507041d68089089400b41c0701e0035166180c103080c5039030f500c0c4051026124000280511800c4241410300a4200700143c00c4024010300c0981440d04000008208502c4d0f100d601c141c50181c40c0980c5d000544d0400c40440d00500312203601c0b8034025a401065211174000710802c1000c43e40071444101040c0c00c1030180122000504a0b803520300240021560b0040086207080d03800c2c4122140309500070021f0411003400c2c0c480f14414086004014580082007900b03a0700f4001850b510318a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 928587266 1250 928586016 928586083
    0x30d09020a080d0f031a060d0207060e062e0e0a0c032301051e030607030e070f0e13110411070b0c03041a0c070b070201090510020406020a0b0405 64
    0x428001c950032a4071568030640c180d920711124a043d404103440001c3da0f02d03210b020f94090005414000c0802c1a4052200c00068103a40038134600202268086903074028480756104071240c1c510400000d007503504001e2a000c0047d914441d0030344200d010420f650f00f4a81ca031241810092031080300941103401c20041d5007015002000141001910301000c2d51a000e90b0010044103007814141650f405900704400d200350720074580d181c2c1111141c1000c5510681c0c404000441c450801507a0000d550100f10800301d092031907a502004c0d0315404400705000051200c0310481d001907400100190b40320480c40c0c480c940884003080c0da0361040ca000710560003d41b8144c01070480038860080100c456580c034109600341d02050301c0140c07134030aa111031400001c800d20080c541040d0708892042c101030382e80e9940d101c01d95044610000503510360100e1350401c117040107814000044040b095050504041000f552003000e8000584044c8100c1c000c20248030050201c250180090504500315402c00785030400e8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 928588516 1250 928587266 928587281
    0x103030507060b01082e0e070810060f0518120f030403170f04030f050a020301151805070e0f01090b0f0702121c0e030c030d0e0111010203010806011e08030d 69
    0xc520303080c0007483c00d40e91320550340306118903040307040001411100501607014071086541440300c44010200451955007040c03980340b29031415595104c42c0d1a001c07811012443c03c0707900901c00e0011000c00c0c4401c03150084241e0308007419080b180c1c80d109409070300090320209802c5120400380251a01884401000300040040e01c2c003c030403410201d20b058070030800c50700c54403a9a080e8083c2c140000c2c40010985040000c10381d000380f08458528440d03400103170842c1c944542c00080d0196042d410000031b030b00300d021708408020b405000c02061500c00005001c1100460f4824801c0d003604149100f1680104a400b020b041e412480e961214000c03070034000c15500c0004242d108103624111050016000500b00f9040c040480040b22100d090315000d070b0f040300710398045a600d03004100d201c00c45501c0410040088600c2a85c4425605040b40c0016000e1850b8046918960340100014451410f00098507411110018011000c4201c0c0c881400b40b411480d8002d0380e45404006503104410380e10750010710 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 928589766 1250 928588516 928588523
    0x30e150405060117030702030a0b041a190506030a050d08070c0b010f0608130305091003230615161211030a0f02010f02030f15150a03020c0c01090b030109020307050904050103030507 80
    0x103503031341c140b903056a0b01c0c003c1c00002941903200d50406030028400d180450b4001d0b1113964111105848540301d40041c0d070080f1075210340c1d4003118140c03001c020709900400360000c00030380182c1000c0c201030721800e8440455108440a00c89004086072081c2e108071114040305401501d564510b503120224019200024480c080c00940d00d100032824000a00ca091003d03141e15445540c900312300c0000384021816840c0c80142810754031401080c22280c200d0a000038941424152003603490240200805410407207601048000b0034040300000200782480b0002e400e4000310445003029414074200c4601c40103102614440c040410410708840d0000310304640181c0a8000744103a07111128488205e0000303c62000d143d2000c80c002c550701d020080b0002c60341510250072a08014140e0702e0040c459030143e080d40300001e40c001500c1308040340602081c2004442417078100344040c0751228508a6001c107000e0808810fa00001180145018604986d18080040e005100f19070f0f4030b0078003800e650080c0d0800e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 928591016 1250 928589766 928589789
    0x30509100e03030d0e1207060507120b06160f020d0f051203040c1503060e0106020a03090f0501020703150b090709080f1f0b060906040e10080601060e01030e1504050601 74
    0x44000c14003441204184200250042d8148000b40000310080c201588400c40c0ca4002c41c051001e034881a03c00074210107001e8100031a05e41002840105000040142401d409241c01024401030350f40c0c208464550149003403410b02c486030750030046425003074940020341c8440452809800c102c201580c0d65907a5018100352801300319040104601c600c811240181211a901e6051000e00d4500c161036001403514030303001400d1a01c9003100001e0a80030b8006a025a109003401c60815030300105500140c40d8114a080c662807034200084d5035420380e404006c1071151900c6050b00c035881d0f9648030546000b001025462981011a8083d01c0c400c107a00449003036001c1c03000c002c81e04960001e805902c040b4078420250380081005c103040c009003100c10300c12754800740400035689035a50360300240c0050b16812803001c07034509041c0071068450711350340e11040443c0c00000040100d560400c0300c1803003110f428200801c500c694600c00c5420400c1280417080c112040318240404d100713000422606881050700c07031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 928592266 1250 928591016 928591039
    0x905040203042405040305070609032601170c0609090c19122906210f01060306120305071709060a12050a060b0304170f030406090209060409080702041109030307030509 74
    0x160f001d564048501501240d020003034030000239015400724014600900d03110013416044150369406081e00960b1090541611006001114000125000c804410b00003400000021004600580946404903118401c01800640032811201c200c803410304107050102115103641001510604410f1060f10700b0615040c3c0070402d69054400414681100407040d000741400542040700c540d0190a41c0d2001c3c0d070f65040305a248482c0c4d00c0c44039000d1003241d51017441960501c0b03c000c003215003a51110034401e40f00824500803a4000d02145c140c00c1d0003507622032016540d5a5159036902ca142901c64100c50001054400f5a601c042c3d1050410030240341401162540f00000080d600340b4000d442503c0400c00100d40051192038681c141924003a00c1142064900029828290022101520400d0f244c801c8a000c520384081c069500c51021107040140070b5240d00e40170703000e0091003070080c00b03690381e05480c030441d41d0041c7c280d52807100d0050403a13a4407a502d18000700182c00150710301c0c3c0140c013000c1d036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 928593516 1250 928592266 928592333
    0xa0602030414010306083a020703050607141b0109020d08030406061a091c140d080a0c050d0f0b063105060f070c1a04081006080715090504020304 64
    0x101c80c1200e56010040c031800407000c500d070417001d86118110b8120707c2e852245400882484c03c1c511601c20b0140c0160407818650305010b414900300411a10410100210715000b011344e40c3c1c00e54691504402d1080d040c00010080d0070300420700c0607400385d03108812942180810a00700021403142d0b200718410f0060594442000a030310b025210b2009c86020284000d0595041119881d44c42001c00c03926840e40201799103445d2805420f8881480d056040888068106a0880e0303849030443d000000420640050b19401080ca010300b8050100071074a5544408016002d0740002644000080c2450750f81e1440c0700e44500d41803c448401c644011003442080d015407240e001e407104444025001c07518141611044060942c02501c044074174071500381000c140000c60060121407140064982ea56990070304481914000790b800901c400c29040c90010b011000002c51180c04a4410348081c1030510007401090314606059048650402c0c40031003008107120340707914603075040c1d101006001070701e00020703a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 928594766 1250 928593516 928593521
    0x606090e07051e0d141e06070807050307051911071d01060e0d0f0f0b09010506010c02090a0b090405030403060c020a2103110309070f05033004050a06020304140103 72
    0x8610340d0700201181428090701480c0c030f03443c0010200200b600d4008003950b075440b84c1c04a0300a15440305a0310000580440348019800010007041100040407181b510741001840c0c0c0c00700401540030840007001250801d4002d606441e0b16812600050084241014005061210742c500c0f041c0c8501c650a00052a18401c2c1414501492103c6440314980c1c20300c0c078142c401d801400c81c000c1c0c001c041d500310440400c00c0407542c054003610503178824150101d5400c0c028a10900580a40380a03450902030207040d0b0f800004c51400d8030347c161043e441595404001d60b00819041d003036240c000c00c0345810070040220100081042d02d100d69020803000c070460f241240c0c1c60710304800040c40a0101841c0c0d64043c0c401503141d03011302c0b84524012622203800000095607030420380d501105d80e80101420b10280703d641700c4410180c4015001000401803114017441c0000300549100700011500d40e9024914240b00c080f100035107005884914825a500002940d03540b0a101d2204101000300681382190310a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 928596016 1250 928594766 928594769
    0x414120307110102251202011b0501020909010906062c03070e091510090e2d01110901021e12030f07080a0c0e01052a03040801050a140412020c0603040606090e07 71
    0x1401700d102c8604152007000b44843c2082e050b03040c40700445440d840c110140c2000f40c0054400c0c0005a00c4004403403d00a4808041c0c004220701360606000703101e640da20200001c0720031856111862213002400050001c003800220503a0140170fa03000100306800210840e07070061808200320f85142101d03085079002140140c80c9141d5114084ca1708100c0d25405402c8503100c480003a09403171503d0116109400c14900082860020a10007014240810401e01c00c00b05003c20318801e10b45000c0620000070340742c51742d00010745a011200030581d5019a0100030700b021075030f28509116501c0c14070030302c188031910701115482c0020321a8000982c1d401c605000700e82c54201181c455000910b5072000540f40c58026002c25181c00c0f1000c00d65050345d1944c401078488515900001c0d56889050098035400e582004002014843c1000c20003500d9001e0714510030340c23042d0000102450403103052012400d216110302c1555000b4008024441442240d900039001c03661a400c1c1003000090100402703842c2e0265 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 928597122 1106 928596016 928596073
    0xf05210603010b03010e100e0a0507030506090f0706140705030d0912140909060603090a050d0201150501080f01140d14060108061b0414120307110102 66
    0x83c402c0c540020030590080c031000c8417600c0015501d0901ca0318008540d5a107021001c2c0c1013405000c0d00c5c1c605a4010190340c003d60781d90905c10740e2041e058661100b60300501c050103e4848000488808403042921903c1038940300101403403880e04071440688050004100900350400940704181c84144580040c18010400910007805000041010986140308000480740c0340e580b28813450340240c088881c00e64960740d85d88100d06015082d40e00820504c1084000d0b10020f806400c0200c82074217075201980d0a544d00d41c011903141c182031301c044c00e40b1040c1e000180031000054134460080d80c40a031008040010035035929800c50710005028290382c10a4005008120041c0015500160055400030000c1820f000c0708040788503520071211200b0b850101707070341c550b115000c0540f03004500c1c4050700d890b05d90500f0301450070741101c1000d5006015020b00f42c0040344440d0041c4003030402 = true := by decide +kernel

theorem cover : BRFrame.Cov 928417266 928597122 := by
  have h0 := BRFrame.cov_init 928417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 928417266 ≤ n) (h2 : n < 928597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
