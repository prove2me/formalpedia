-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4869
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:00:15.515662+00:00
-- url     : https://prove2.me/submissions/7476a2af-f4ed-447a-9d21-af1b15615d0d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 875539568 ≤ n < 875719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 875540818 1250 875539568 875539573
    0x11040e0c0d0c15050406140714100501080d03140a05310b15150a0201060518010501030c110a0f0206090303030406141005010e09041119060e01090806070e031006090905 74
    0xa8070f40c644c0b003041218203c40303003542d4075500403100109408503035100c81c9080310a080c1104103002c0b41c00052100b00c4540c40250800640c4d585040c480c1030030701151422403000c1500d0100c5120f072407828810790381c1d0007104080c00091140c0c1e900305c0580405d0105514030305102881d072242c001034490100c48400c214412240d0520548070700d100c200c0302e4a04184891352090401c9801000180c40340090300411100d40300114501d42d98001043c40c101c0d0180d441040306d5410001841196018003422801007414a004800420740300403140d03ea20070640024440d010b905280d4040d940c1d00c40030344940400040507a0342d00e080c01d00d0160000c4c107a0844c011140207480700081c42c0c19900e10034010803205c040e10f0300f03080c02c80030108000c0c00e02030043c41101e04500e000d00c258229110100740040340030080d1101150349042c03501c0500104078040b1503a0400400384414403070b1080115140c1e130456501e0400c016640c4d81c0700300203820480504c40031b080103850158002031000058011803540c6005405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 875542068 1250 875540818 875540849
    0x60a0203190504080702131b020a060c020d09180b1f0f02061b09040228090f12200310060e0a09030806090a020421061811040e0c0d0c 59
    0x120803040e42e004840280180b1400d000e00c0004d824821080f84800c184084009062482c20740d80c070020200b90f41225005a01141d007490420585200e10742c046d080c240010220011144002031101250340100d00c40a40c882c10700d0322200107140c1294050010050032400310303011600c003140c00840c1c0300b110f010019500003641c10a20b4008960741e40203101c0103403180303010340d0001903103040c540c8030044143d0010740c00c104044006c1440a1840024542c89000b0207240c01c112034000c1851001e5084107039407140c0d00400b004022416030805203480e9008551004030034a01301000808011400440c0d09401080d00d400d5480200d94009000d481c65545404a5915103410744000c58030910001004100c000e00403071f500340740c46001c0c503030300c04403d11780540743c652903201c9041141c0c24800c41e404c0700710b00c0e082060100812400b60040d111365020000d201251070384c036034882c00c18080040b98001d9030741e014420072028040c400c49403140c030301921440f500529480d0412050000c1e102c1c000c020140c0e0300c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 875543318 1250 875542068 875542111
    0x903031b2b0b0f0909060726010f0806070305070c0204090204141501090801020705030306331201291303061103040605070c21050d140108120403030914040608060a0203 74
    0x4c40d001d020051700900d401c1d503402006441601c410300c0051001c2c6004c0040c04051001e28401a018208800344030b850140782c000d1030b030702d001c40140101c3c09050800d07003009151548001c0c84a0702680484020440f0006400481c004000c9901141900140c0c2403c00c203280c50000404010303003030203070384030030549a40d941e80314200c0c01000f0740200560001c00c086902c034136140e0300102c2200d6504049400d00c4103441d60296070202e01c520501c2080e000070460118608806503035600409054039405030301c17100448001e904208030070304c000007040e02060180d420b4a11465800c051a48800d08008805041001c07142a810444007140d0b00e03424000010103140c070031802c07800e40540c0440b10950142d568000d00104005801640c82000024003031288601340c9800780b10841d0012100c210140d5040c0a80941400f800080100031800c041004100003503011903041c0c225604000c0c1c82628248904c0014082e05041d40000c96034401c0c001030119103100c80e030082d400344418902c80c1d0b401100c2e64 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 875544568 1250 875543318 875543329
    0x60b0d0c0e0f060304060207020102190302070806010b090306161b0b040c05010507080a031a06030411150406020c040e03040b030f01090b030c01120b042a02060903031b2b0b0f 77
    0x85181504400f0600100700098120340180140c648140181d500440c118160f11200c841010400d5005910041c5c1c100034050042c4400d50140502c098031510f0056010046507880704060800d02444604103012030fa005e102d410300480302e200c08503000040e41214181050b1400301542c05499071080c03441700140341e6009004a0307141c507501c840e0351410188240300a800800752014003090900600b0003440b001c0c4c1d10000210f00c524820041d031144064598117201c019660700090700c8822004204c14422250000b5404016034070846012401204044919045015541c4048020034001c014050075428000d20a810703100607c1c03003048641c644a04055a03210160320050101c0c1d140030980d00110700b50740ac2031a210001810110300310015405141c15603d410550030409448825000c80d03540d0306108903604415031800441c114200406044004480810840304c424070014498158602400d01c08000586807206481c6003006170214002820f880c15085200740c4a14402d000742e49020b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 875545818 1250 875544568 875544589
    0x81c170601020a0209090a0b01150e090601091a07050d02030a02120909010909060e060c040501030b040221070207031a0402042715020715020a0f082503060b0d0c0e 72
    0x5038010072980009400b40000c2c05c001402c2d49225006403444000400c610880c0940204416000881e1000380c10a0080c0582035952480384504404010702c026aa44551100b050b100a52414804003544a4643e885803040c1b000060050140e100440c425980200c06030400058540958016803008600055284a610001a406402c0000510109505607c40e1082900c00e600001d0880e40074542c9030715080007245e0380c4040c54070014040c030030755901d8001c845803480251401d50800c100c51800001045c00003d1155200042e00000354049200b000302100840d00604824114804044212006181154140c2c016804c002d0300c2d2002d51500904401d001021648180c000e000e256225807a010350310440e41e07010390702030200c440400e4041f0f207040702038030206c0f00050b900c1a46080180603440f8044242060140d81000c01c0342d11018900104111040703420184501c1860f140c0903401040c554000c0f101182021500c00c11009207644104079480d0030f0b2b00c0e5040841610401c000441c0074 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 875547068 1250 875545818 875545831
    0xa0f02040b0613031106070203191104270f120f08100b030f091015170f031206030a0b09030703021e0a110f090408070c062c0406081c17 60
    0x34404040002c58410f8a034080d0360170740100400c0c50991950002840c0800300b00c1c01400411094000c400ac0003500340d48254402801c7c0d601f807208441a110490350b180250720149600c550740c01c100010070400e45590345080d50b00c80500f901d50600c0b950014042c0d54804108401301d030802000c20180c0e214001c516007101d038025145851642c2c0d5100b110062030001d2300c02003291180e20038016010180c0e0081d200c02c1182e0031445032503c0d141611216988403100051010358100c181c1c000e0000002004450243c1c0e80403200c0241a03c403500482d14020340d40e00d001e40f662070300b1b0050041b503000102c0104201d0780039608480505009001c4c41c1214029510002c1840d4040c41c101d4000500d184483c81798418000d203100b40e950200c0000c1501c0a008440440341080c0c001501360030401e008400d00060541480c1c0000e160790100c6010609009112220001c596030500c224066581c03504810003034005003069410300041487c1080e03891041800c0c8502203045402d05400381c42140c24094400c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 875548318 1250 875547068 875547097
    0x80a08210903030a05060448050a02060c0c060f1003020405040602220608070e04060320120a12120f0c0815031605040c090b04031a22021e030a0f02040b06 68
    0x2000d42118462061002003181070007885d900d00c10655111a000348c4100044a07181d1903038508001c04d0003030030a00003d01100b40380006200452038101d00150031a4000542034112401c3c0d240d844820205014a5000035400341c281400c11081007500d8001c0c0c8414030400001ca2032010101c090580001604d01076070002540aa002944d0180700705507040210002800006200d5180d4a03409003040500d01900140300c0414070f0310b800c1e4107248041030032920b103031006455403405507920031f081c104032550024100441c0b000c0c840000030456100345c20740d2003450801c00c0800c0c84281c0181015004407908000c41c40c84080201d904e050204d00080c030072000c54489078040c0d044c0b004000040c0b154042c0302042000322800131450500e440e0080c0040c6002c3c401000c60195540403007000900005c0081c031a44241303110764034500c03140460142c151581114a20203403074900b101c104e00395210141d142d0303041c800d051a82c000e1041040300b1a0950340281d030240318100c814800c1c045148a458201014407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 875549568 1250 875548318 875548361
    0xf0c0a0507140313062127060b0307080607171503010e01091502070b0412110607050403050706030608210c0304060e0306060402070f0f0c050d060f05070801080a08210903030a050604 80
    0x48640794800703040c0507c84240c076601141c0b07500d410600030346000710407540250780fa440d118082c9010414480241140782c020411480e240000400c20300240840602e500300300d00204003204517502002e40c500e54040d008015213204041074601178055002c0c161a950101201c0d0241c01c2c81500880d4922600100003800313a448555640008507980d06949041014a54080d142004107001c0c080c0140c11b0b03541c900d9100d5046007001d41c1402042e0f4400c000b40b600e4450200042d91011510040c2d0313000214490140e610100052183d5114005103620340b80400140400d00315004402205100130a034202c402130f58412051204a115151010b811030041c80c408000098010a81d814468810140540d4407941c0308046850040709850891300d0381d840791500912034000f07129140d4003e5032031501c41110351500343d01175103501145002500c40c5030700150008071000094219800501c8503102308a0524224200d6070700c94005071030203e162410040400d040303240c03601891002d089200e0352914130 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 875550818 1250 875549568 875549627
    0x50c1305060331050609070e0705070201030609020d090302010605030d022e05130201021005150d0503090a14120a0c05062a0c180f0c0a050714031306 66
    0xa541004022564211920f81640c070346144070302d129600c41d44000312030080d10600346041802d12400420700700040c2e0041d8004c112002c5280c0a0a03002000350070035640d6800e1b41d0004a000c1c2c1915000018614000034045003801859408540980d0083c1e008000e115111b0302011b4840499001050040e800a034803d03d585614040b42d4440c0d010003070280302c640082400300015114100da681c1c5000004122004c11748d40c0601c02162131903100c00c010000c6151981e12005188000700c55103014200701a00c1c4c0307081001c1001114901b5030300411400540f0b5a0300030904111425080c094001c802c0228207055103a4009550460310741c0c0040b91000c4d2500380000d1007010781103003503400100c20450490980e07200d0850b10035607004100002070020a0401002c0c0312011240c2c070806030000c480c0c401009088040c0c80c02154108425184003680c40b40c0d02102210b05003c1c1000280c80e15a00c0782803079400440c000700604036040081c0c5c4110840f0350300c01c42501c044039100301424003903014000403a80c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 875552068 1250 875550818 875550829
    0x1060302090109030c0e07080c032a0c06130c0803041a09010c0f030c050f0d12020901030e0d02070807050d03020a020108092e1a0307060c021f080a050c1305 69
    0x10301c100c1032400c89101541d17900d44585100700da43c040160400d1100a019255502500317081d404100601c0180c611308124031310a00030f00012045590031560b40c4181744095040c401101c04c0705074114101c907564144401d900d04881c074640022a00e2141480e8001504900401610220b98210000442c5600808072410141d4084048a8100700e04840300e100011040266032030014087d984900c03210242d4135040d49400100d0040c50300303d600840902a003a070340008410034121034908090384030020307240140e0244ca0184400980c0c0e000c0c0c01d4102543c40d90001d8111b00311200c400840f0081a610801d0080c001d92805020300140c02c00c0c003501015501600c42d2030341000703581045a080b0300300e52400c88156000000d05006a0003240880c5e0325800040c00307088030481440000902c0700c001c201c0060b035501000d00c1040c0c24844030b0f40e5540e013995641c5400300501e414280300d0b01000c140014008000070811103904041615010115102c582842c060781c5403280705c0004001135904000070400c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 875553318 1250 875552068 875552077
    0x20f0d111207171b0706140d0209031912270b03090705060d15090513150204083903100e10060f061409030c0607060e0106081b09040b01060302 63
    0x203a19000582460354203440340c900804c60040d9101d1400b513929000d103810703418521503030301000c100007a20901c07c5c0a110048202d989964040740f0069981c0742800c01300e401d0240d00c6403001ca03540c00462000d004e014101511600f0200302d55620071244501550004603d14807461302602c0c034100e45018000042500e00440c0c00545c00c100f207441135956040065040d60242803448081600c1c2c021200d840140e012b648800350500300b10601152600c0f0301001c50a80f038611010b00040d54a0052024800d13107507040b40c0c0a002900141c0d030342c3e0302800062001a03400606281c103003041742030000780013260b00050388082c002c000f4083c1c070200d90f1212060000c0e0074038500c11500c078000c880b49000540c0780d43c80b620b4018210444038509c80381c641040507116034190507079000c2c280c3c1c003044400603d680c0400c1107100400c0031a220382e181c070068107096004002442d00080d542d868500041140724000940c004807103c07509441c051200c113070080c0207200074280c5001302005068001409028065000760 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 875554568 1250 875553318 875553323
    0x9020a09021804020304020111060c0919081207170403030e1206160f0318140c030d0e062b0f0e010212040f11090a0e010501120206120c19020f0d111207 67
    0x16608520b01e1b003205d410200252f4001c0fa050340000740071519414443c400182440d103029136947c0382490512450340b01c056440640c00c0003100000d500c400c002c807003015802c00e81a0940480d8480d41c0701e00d0b02a080d083e8008840b80b1541e8059240b4551030b00005025100310040f44100707801a07401e85082d0b444043c1c000d800d00c02c1c10f444420a11480c0600041c108000d8040c0c141c002c580d030700c0c034142541440100782803103029401034a046080b158000d4040c81c0049400c1c1c0c2c84650312168a059441c200c0c0c1e0b89418482d100074092048240166076812021000007030074000c205104020301154200d05c10404045500200e040c00100030030740801e0007900940c007494180840306040800944002c40c00c503000702c8040d503100b0030312250600901c2164054410114600c3d103005690f00091000d0140c0741d5001054200000011040d001020981d4400900540a141e42500150019456234070320031020115210b4036940340202846441e9550004400704050729900c0d01c0a40c1000056000e0f0109 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 875555818 1250 875554568 875554577
    0x5060102150415020c06060f1503011512180b0c03190b040908030903070515010b03042004021803011a06190201020906070320010903350a09020a090218040203040201 73
    0x154451960300042440000a0011b841546040070400001c0702844490902480002c2043d412902010701200d040d03070b614200b4180f00a00060040703901c4500d00c1080000b03035040001079410f023040002c180e885e1718421003512a1a640e0020060241c0c00100d0f802841c0e0380c501c5230400403404040d401140400c5000e030020400f602a5110b40d0340300c0d40141c81d0121294000203419050150178401c201204003443c5c0ba004455150881d440da05000c040c0000e480030902c401c480308401c09540d80c004201401500035510381c480c1000c3c02c0c20441d02c1c00e0290740254284410b50a504402d039003480140d000003803415003040e40304961104040d0140e462a0190b40d4208103001036940c5200c054010584255210540105804504007007402e120803038068981c14001d06000003a00709a00c0e041c90f030401e4005c8014002c000b04c1d90200d54110000080d10b40702a40140b0402003c240c000003d19070090351000e44107591003000800304c1c407841106031254803692100480d40d14290700115000780c0140340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 875557068 1250 875555818 875555843
    0xd031d0601030318060c03080c0a031e0509100203130807032d030e010510170a0b0903031506040b0f0901030e0102030f012607050d080c070609030510050601021504 72
    0x15280d19084080e00181c0100c1d081c1c041c08080043d401c030310b4202520240c584200340c040a5034002e0202c05001d01005014000802d151a016200ea401224030305002e0004000c2c001680c249030009081c00d60700c0d55603900540c5d42090080225000b02c80c000c942d05001504100e03002e4550300003070742000b58200d0801c010740344c4269802c24900b01c2e40340c140b400300c8803181300c001c01c420018081350201d54120083d07034144020003100e626a0b864500c100c40381d020102485410400115003001c8180d0f100902d85494002442841c0000102462240c9801208080300414202c100a028011072045000001040025401407d45a8042c102501c0103041c041465241000d001e0300fa40c1080300e8000c805c55a880040080d102c00c0382c1c48111201a00141895402c22640e1554640c02e19019030b5004503880c00b004020014040102d81c08484d517582900c60705500d5040c020309401c1c8a200944061040f500135000e2661a441405e0280070705070000d0901a205060075480c9610040040c0d482c240c0307410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 875558318 1250 875557068 875557121
    0x90f0a140705130e01180f0f1713090510050a1802090406030b060f04020301140909100603051c08220c03050d090501110f07211a010806070f020d03 65
    0x1c4681101025019011540e00018131800d400c60320036101c2407110440d13415114000c20001031800c6040d030740100c0c0e48000682076040404510381e0724401200b031706074001202c0501505200d4540140c6020030b005100503190031000c443c0a445900525900500440082011021414000e04003800000700581080340311f02c0014200c0fa000d600c240d820034082001c0000b6031805000c180c1c2d1841e81140c00310306650502c03150301c3c0042c02030464103000d01ea03460041240040c04112511003824010000e11181e83c580c54901c0e102c0d41400c074000d2040e03a42d030074115890781c0681741d50380c41400002e400071605c1d0841203503214400e01102c42910140302d4510084080384050101d42c00081c840e88404501c1c0786010001840030307190310a00705650300310502c0340b1208900410008102ca22540f001e81045c0c00254010a034101031582c001c0002d541100e41141e80c80b041c101c03032030494400718196a050343e10390000707131416090266600010b0300309000400b00c0300d000703030b0080703144001e90b01c14031070440a0039 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 875559568 1250 875558318 875558329
    0x1a09071e120507030606140a0c06060b0703140c03031b1c0614030c0a0303030c1205070c030e030a0b0c03070504030c1e1e091a0603071205090f0a140705 67
    0x5034a4000091809400a1101e030041c05500e80003012440d080107250300d0243c0c000d000103000c411442d80ba5500003000084039100b44a0340188a1708140d042110740d6a40b11891029817212404501081c020440701e83c034111020240c6201d0440e000c090362075a80e54101d0010032080300440f0302103072101405829000100c0481e1074230190700040001400c18200101541e01e00ca404021900c690b00030155205c0d00d440750407543c007c0743e83c142000300e0402520102982d0f40c0680f80701c0c101038146003404002002e50300a105030300c654040d4032201000786a250070315894114a04024000d030304084046400500850015644980c040c83c00500381602c0f07a840740000e02840c2d2010440b5140c00716002c14a01c10208600014030803011000c003520b102d60416011100544996223500e690390f4140c503541004400e811400c95002400360b540c82c644100d010f00a2449081c17602c1010349082c0001e5020000040d0306113640c54400000c0c282821542d0300c08803442103000e0300310724a0255a0000405071100e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 875560818 1250 875559568 875559617
    0x30c111c030206091e1b150d06051c0503031b0c07030606050f12100903090914070306080c0f09100806071e05090d080a0c022808011a0907 61
    0xb90701410540c02e040070058500200500301e130031070365071008500c0b045c0403001480c070080c40d64951804191808100028901258202464404250000315540c080301c1a0b030165065910440f500181600303507180303180119010000c0100160700400100b43d001d42c2c5810680d8400300000c040340d01e0b00b507150406900305860769000310f8000b5202c20003480306141044800040d02c000f650241444816103034110395690300010b00c002e80e665582c441000f41481007807520041c003241401409840e216039840265088c00311040c800003442c11101140100300850708580170500100f01040440691341000b40440001d0300090400d000c03824006000707601801010301c2041140c98110901d01c441c441440c140320300100703c0382000001c00002d11160356480000a0482d0441c1d049900d03194801d400380d078007100c8503001075840070482100855008051b03600a07000000c980e40c1c42d60040c2e540080704c0c04d85440d012003c1d09500e50000d001d1aa040003848240e0002c4a4500010340002502801c0d00c507000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 875562068 1250 875560818 875560823
    0x90e041b09090c050d111908070f08010c020109050304090b18010905090d0801031a070507061e140c03010501081b0c010c031803021e0f0f1e030403030c111c 69
    0x440765000d0b0b042c0004a000c0100074007080d10708608412071659004458840641c86900c01c5d607540c414403107061700c0c0ca001000a4104082101e40040d1245160703484030706071384103880c0d083d8202180b00700424410301420740c5003a40301d0011410f160510082102078519680150b0700300b00c2054181c41d03000c40301b0b48002d000f0907641d10001654101000c0042c1000c6480451400384030824004000080306030751a25045c40d2881008112078441c07030011222071007440b1018140d01d041c00c1805803c040095242c25807910f041030b041040001c0040c0203400000110342000800205200401c0311f540070380c1904d0783c004040c1080b0302e0f150350100c0407044544c10449011055a41d40d00e1600d04a030380611600c640d62040c407290050000807554001d42d0380c01d48078503c00d41c02c01034101c2d103031340c0c10400c02003501030581c41001c1d00d50140e09980150b07540c0030b40d1400b84494000c401d80000b1ba029001c8100c4080d40d8041e80c50000d00f1503192a010491364240354460f400c01c1d003019a20501c41145090303280c6592 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 875563318 1250 875562068 875562071
    0xd0f020f0306180c031918120f032912032b020711280b0c1005130f0c150e10021c0305040c03140f0601060201020406090e041b09 57
    0x309001409004a0440074400803081c580050103006858101517a51000c0b070a20740b070004030f9802060700050440e00003091454028540010104441d02c04001e62505196032403007124412444102e051f1442380d075940c1d040e01091070340c03411820030b4901c034a180074601030190200c07601c440041c50700e1644000054440c515061442c070121030310000c161a04080f24600560030905241c4803079001c030b10010042403003250040c5c800d420180c3c041e440c923941c1d9000750805181e5a0307652950301c1c4465024100c2491103001e0203c60024a41da14448d1901074902030a481000030826520301c5032584e01d580007911304100715400002e2004205054094a40b501e82d42c00c03451070800703400c0c0003245540d1740c000000e54024900d150b2440b80d201801000e80383c460315000c1007540b0b441c2048030501307440303030009081c0060800b40203046000c0010990304281c03d11040320907036171f601e03d0308a08074000c0340a8200010070000040151001600300541c00a004003402c0d0a400c01075241d00e07000342c2e40c0d40e00c01020789 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 875564568 1250 875563318 875563321
    0x613051504080d110c0307060f2d0201020a020c0406030308041b1a04051e100c020a0918150902010807050c34140a0b0c071701050604050114090406020d0f020f03 71
    0x30b00511400440030002c6c0d0041080c681010005880900151082410014a0907050314140c200c100500498101070702090388031500c00d80300074040d40c480d400c2d00001d8483c4a00d0841d0b40e081511411048a405a8a100345034071a0390324064420700030307040740d000c40c02c0c0e040c0081410200d40510040110995a01541d19494001413100d502426020b1121804000310607211907290086441c000603d1482d1000b0185018400180c1c150303419084130089900d4850384804086844002a1216006613520403566603408005c00035101c0d401002130001f100140804c4400b40104040c08250417a14140c8003100e42411198140d141d0718003120300c3ca0b070f01030700c45210448011800100a410b1102204c0c0d4a00004000324400f10894810500f002e2800110810446030500c64140948905640e0b500c684940e81c00050103000c1c01d4074214850b0380f52500010740380790404111502038901030460343c020756554841d20f00a401005010902513221141d0b02180040d905c02481880510400c250300c9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 875565818 1250 875564568 875564597
    0x30909070c080a030606110f07060503100810050f1605070206031306090f060c110318010e030a0605040b07090311040b03160b040f050306012916050f0c0613051504080d 74
    0xa41e840c01c7c2800c00c182c100c1d00d0006811800455445e00b51140b5040c51580c948420704c141d0f603640719950201c0c3c0d6a00030188030940c18441a04828040c140002c1d02d010baa40b1008400050340c0000000a00490000c010410060614501440e84a00c41c04417034900201143c0703070141516031031001107070343e0040003640c40d01708645407060449600c1640307031104000086907010356581c811071407218000303008842a040240e00c00c1c0c03141c0940c8003003d404d564043e4060314150300505016030341101d40f4600b420009a185200340b59a404491700051100c9005c5552001d03c8000c0040c4820650180110314540c4a601d82101d00c0c04c00a10f00c0e4040c91f9680c0389080d400528003030395604420b00c6500000c00420181c040030310541041701040e107981e44516111041000d10b44214108000641a001c084005000380400c68045222003102034902c07c0c00c1003810003400d48940b08030804d10b000403202c14490b81c00c1800094132800c42c480f0402d40350036101c1c0d482601d40f400c281403800024034501e100044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 875567068 1250 875565818 875565827
    0x50f3715030f1a060102070e041412040906090902090619080609030d051506031b12010f05010f080f130602041832012714010801060501050c030909070c080a030606 72
    0xf50720301c000d95540c095081242c0003d44072101c1d40f040310010920180410b00348401312a215050381a05811542910076622410641c1d801500c94004110300c2d2800006201d40540036003c4003030b500900203c0d00b030740c8540c01c20600582180301c0c06c85120301038a010517644402c018690080f1000c81c001d54440c41d1110185003501d4004180d0b080001086400221940395101540d8000c0c1c80010410024811040c014855000d11002c03102e24030f00c01c00001410705541c1c080001560740c280c0e500070821210b01c0c0e0544041100b91800403056280e400014550101861030085541c8a0303000545490340d500d03621144201c100c07540c4d190107039640c68100a03591101c1d03401c0402c954038016106e02c030045648a910035080c1445001c0d400504005141d01a500140314210003000311001007015100c0341280e03246c60310090090460350b40c0303040d40c0400c0760b40c050700690388030b52041d41c000c6160540c0c107814070118039005482c0d8401c1c0010a540d40c000107213118043c1144400036030b000101c89103400d40081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 875568318 1250 875567068 875567093
    0x15060406080712060b01021c0507030809011a151c0b03060112050303040809042a23040b09010e0a030f02100f05031305070b040603050f3715030f 64
    0x11507035402408104090900c20241d0403400707400c03603000107042c0700c1080181c1c202030728030000f460054848502c1115041c0c0040181041c01d000741d40381d03290f943e280c8090600722501200b000146032003140040300039103005184503414082c0843d005040c90102d8121f107420303503102540301301999100e030007010342828104086401007001c1c03440c0e44000a125100c0c91380740c0c4400352015000b514001442036503903e80e504940c504000601c0c8040e940050304992048201e484004180010125200000b4440e81d4140784c0d8400da01070207410703141c5407612500c42015401000668184400346055500c9a502c01b40e0810086000d8240d161a08800e84104801e42d09600401001d1106ea03a96695038517074003900b540c4d40030780d0504100d04d01c03100b40c1c240103150108540c094003004c000050b000c140698180c0000b80114400c11400340325413205502a00c0c3c4055031541c5c1e46034a121405800c0d0201945407507001c2035110043d0001d41c0c4507187ca9080040c0c1069042510500d666003c1ba00070040d41d01000c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 875569568 1250 875568318 875568329
    0x2031c02071e1a040e0103060b04060509150307090501051503101205150a05040b040221120705060603190b1504090c06271401030f05070e030708070f121415060406 72
    0x1189005c0c18055198055a0b041c00050300350740da07812202c111902c0d1540804043c0c0402480043d051600030580c60554441481c0caa0003030040c0400058400c165000d5181622001000d0002003a9984034607081030300024509901ea141007440050110000100b2180160044000c0c0c80e85c001091242c030300c801e40c060212070101d03144c00d0421000c100340900094006d54101c80c040080c0c0140c840603140d060450081c0c1445000b4203250101505d01c110050400134800d20a80700a03580e420101515994203650225246440c500540f0002c0c3c4c80300041c51b40001003a40d40014081100301180c101d81004004440c071446a6000b0301050342c025a00380003001c1c200c200070074070b142402d0f101c01d84800c8920928000d900807103c0c0c0c0303a490307000b9005038a03030704807101d400c000c01e1410b40030050003410252511400f1f801743c1d8001260710080803800b2030603074441c901010103003441c3c490f40d07172090403840c0400e0341c05500b685007640b0141c0080c4010402080c4400283c411801c11404001c01c81d441d65004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 875570818 1250 875569568 875569619
    0x115030819051e0c0a020310021824031f090515100e01050c01060b0c0606120d020628090501150b0a12020a030204080f010507140702031c02071e 64
    0x40c50140901d003c00c40c40000d54206015440b0030304c622206280105c8008000d6041c000d045076011010200e501402d1414120041c405459800000340039104d80c1107202c40c20381600140c1208003010b404c02c020358004811400c50b1400480800b948121902c09030046031441d622102445a0206e01000c4c10310b03d024100c0b5100c40c1da102040380606202a00c0d417800341407100c003040144880c5000c1d4810030041c01521011a6600090103145480c2d1070100c0c1c085100310400c00309820140c20008107000c00142c103070020025030301d07510b865240c070303000d06444540c2c100850428608100198004c45882034400c1001140c480c54030498500260110b400041d02c0503400d201035084598060034205201801081c01603407020020011000b03841a0340000c4820f00c1405a094610314056100d6441030085680303103490001030603503500c46880307403203806135240e4403e800c4043c20710184d100c2141c0d4a0220b004442d01c80e03942d4202e6003c590b850055503000c5202d1804100700005e100a5500c2d0b040031142c12 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 875572068 1250 875570818 875570827
    0xd260910180e0f041209150e03010609090b0c131706070e0609060a18091113050a030206040b0a030921020f01200f0705030d0207200901140102011503081905 69
    0xc02c3c42200d001000034001e600340c40300c002403a6004404082c05400b14002410b1090460f00e03019059007007590143e4065032902400088003485803040d00c401303590000040980b500c0d240c4450841c0c0c0c120100c03280000d01d407407600090b9841003005549a02d0044005801c0c1032504c10000b40111010340b28030317405404100b003d11041e9581c0d004403108050300d800c00e05208801d9400c4035103401221703000382d200c180c5041d28810007101d104015040040000070311034051900c0e44d003800403552240c40003e40014080c441070211064100140c21101c0c040c0c0740020701c80700a61950020500e2102e1000060700e10440402030240d4184030a080a0311000000d020781c1000108480da400200c42c5050501080407401300e00c241020000c0300d0700d86800008507904e500c09000300c10000d510000f07048800810190005240b180e010b5074040b440c0000604110503686040b90030b118540403010711358110355a07547c010303a4940ca0341c41802c0196000e444801e49070496103140301a08a140d00e00c1f0301c103001e014032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 875573318 1250 875572068 875572081
    0x100501050906011101090803040515130c0e0403022506020106060302090a030b1f0e250915050904020d060806060328031103030906070e0d260910180e 66
    0x2261550400d600780b03441003101304030301c914500500100300024098400042171100707118002446007140751221a286110303454503801c41032101c0700080010030b5048400700402000e2180b810056003e8042d0068038070528013045246a1120b80c2c1c0185030226031014014885182d091044501500240c10704618100d40240020001042884014107031a96480000c5000b0402c05106808801d10412400d019481d1413030310320464030480fa43c0c64060051004908402c078140d11000c00500151030344641c80c1d0410404100e8800a038030210180002003040268039140c41c8000c100d0340180f61400640c01d420051000c0c24540c0c0603141a00c241c0c82456101d03410180d403c043c3c2c2281d20011a07450390300c03007540b0f008d64010020360b440c2d03501404003000701f02c0402008210300c0e02c14402952030203110ba280c1010014030311a001c5020741744100c0c05180c2e45c4022002c140704c00d850003155541500742400c5000281c101c140d0b20060000080801d000703149003c85649501001d4072412040c00d40780c0c41d141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 875574568 1250 875573318 875573329
    0xb13020a12051e0c040c080106050a0806010e0a0b19052113080a0e0f06041d13050106061706061903091b1226030105060d02090a09050910050105 64
    0x107016020940c0320581200c030401004100342c0c00c20300040000912440c00316040c4640701d40e48001c4842c012414064a9508244a84101416202248c941505042060788121034410004188030705201c2420b0b0903580030741c0d480c05102c0003802c0d046005030740c030828004c40f14000403030450071805000d428804805421001c000400c06018500125107041d541d001440c00f038000b00b0f40c8003400c0c07002c00003140203060b544007040a0402d5000d55141031201da4203003e01503d44680d10402443d0343c4025003401360a000107102a0300301c5e011030314030140703071034a511384500b150f00c0c581c0200c001c00c41c82c1074184c6130810310301030540d80458211000d90078030100c0004451125440300001042682d2050054100b100c414000100c4168110840403000d40b103c03d01621074601c2841071303c050010081da040703070025112981ca1407450342c520543c2164070302810b00155410284000540980910125249403198031100c1e00420300c1c88070110380d80c06d1802e11750b0b0500c441c041000b4046411f000051050740c9a9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 875575818 1250 875574568 875574589
    0x221060307050d080f1206040b191202010903170c0715080c0a0c0c080105071106060d080c0723040e0a02010e010e210604030e19061d0d0c030b1302 65
    0xfa107101d810812546850740d01072040c488550301d407071804600c5440700ca0100a07528460b110503141008100d10020400109101d040350088080c1c4182c3d0b410700007941e1400f0220f240d284181031407020b940d129510341024041201e103044200101182c41c0904da2410081a8000e00c2488000c040ae00440384004041c00c20003803100401c10b0b40091144681486902128003490304039080c0c00c034842d142c804487c082c01c401d81e281000500741c00303898440740501088460003800010100c505030f07081c55407042029040059128018041d400000a100b4030070f5030030001c007180c41c4044001c280f6032542040304035400c10f80b00309a181c0c02005e01c040140d80090001c86481c4003420007103886d2083d88002a07000811400c203a1446414903016000500c0005249005e14860380702e80032460800803d0005040320f44a403c00b03c206842c00411030280644400c10240c03200707940c0e0603083d000c54804515040205072046a88501e02401001800104405c182e00304001070b00740181104550001b4030640c02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 875577068 1250 875575818 875575829
    0x2f030f0103060b0d06020c0706032706052d0108160311011d030a030512010801110a030207020303190206040204051501050702011115010b0301150302031b090a0f090221060307 77
    0x180c94080780384560304c050b510342c1e540354003240543d135075a500c0a0072030303c407266845210040ba01701001001c0d614a205114000001c0f1082c910ba085030180d12890040c1002504001102032403003075842d8200380b00101e04c040e0a030056030740440d6515002510381390a6000700420340b0722110f10340070710000701002c0d03020260000910f00b08500c00154011648001905103810754988580c1c40c00d0020160080080c1664940a4042c40b00c140e0703a0300d01880c04c2e44c20f21904c240144800b0005030702810300a5000d05000c40c00a802c90341403003800c07944096030004d01c3c040d09002d03034454800c000071450720b4024268040d0800d5081002000010006002c07400f406100031b040c090510104202c41004004001c41c43c80e100280c0503c03969104c40c6030080e40d00030300403082003101051000b04024024003c032030060101d007140c1803001d582031800b0800398100c606910340c0b0124000001510302000c800c080e014011185005070361701003025510403c40391070091403280001c3d65080000356500441d54004540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 875578318 1250 875577068 875577071
    0x100f03090515090c041d06060607060b04150816080d1b061a010f02030a080105040506120601081c020a020f061c110a03110909040212102f030f010306 66
    0x8445240080c10820800c41c0c110b5400b4818080002948001a0000e100b2000f903c042100c8440f491104049103071400c0201410740c880000b0030320342d09040c40109038250142d0000038080f000b00300050242c0303100b10015840c1040411041c0b00e00d013010b001c042c0e4030f0703200e40d10301048481c604001940c440f10400709280038401c20203800e0b9031000395040c40462030340e803102041114480070058507032070180034120075000406500703102d04000d000000710faa0000e4240c540c44160380c13821b402c11014050081c419604001904551604d4400400c909800790900e038001e4003082683d0f01c860b410109030807031a642150b06c29413a1501686a00c01107d14035001610210343e2610720b040861071701325034a24201400e516000a0304000c03104080a06959044c960b01441451000c40400556001d280c440c1944095074a0104006140801c1206120540c0c2d40903038015020398003500040700c0307018102c40e218000980300104d601141c0341008024009940c030302401c40c28000c000804d14a0305000051489 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 875579568 1250 875578318 875578331
    0x30c100911120c36090c0306072109020303070303141b03040803040618050c030114070e1018060302180904050d050304050c060304201c110a1707080c100f03 69
    0x21302c405841c0c0c007092440351041c80750400c0c0081c0c60b00a01041140ca405103802290a50303501464042145400740c40a0b031341390403070701c500054403035000756414408658183d5030303180310801600c060026001d860b00a841c002203014a164104d004000020002c40612002010721360405040070190b07070304142c000c04a030b5101d40c0e542ca0075500912017000510000d050004541c000c11100240408004006500070711070001d5201e020591568107445007404103a0300b40c0000003609080341500f64203001842c03c000120603c00c0307106d580d61480d401107000260000b03824001411070321048040c481040d1101422460f20740c40b96030312022022807000070414000085801e00c08200902000000d0040910f0350300c5c02e040c87c0241507404464144802c000c1d040020070102e02d80700c03145494049410381c00d00c0381210541d6841c1940080d994030603501109207a40440d10140310b4000303401b0700b0042e8009000c00c40c2441d041600d002900c41346144121030708021802ca00c0c2c3e004812403102c0803142404100b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 875580818 1250 875579568 875579599
    0x1021005100909080307110a0f08220f030c0f1d1801020316110106030b06041512080702130c120c0c02090906100e2502030c100911120c 60
    0x1d0071816400900102e04008032030040c0034204000358011403c984030503590044110803d600ca40c290103010300b42d12041030f043d10106141d0001084000400c1e011590004484000560a20425001101580801d85084c420841602e50b414081c040d140350341041c0611f45007081c00c86440d5558100c0340425440040b13070840d000809144074201003071b00259121300d06055403062150602c40c06c0000541c0300689008a80c406214410681b40c0241c00d03000940d58504c00d10028160640c08139031920554080010f202d40200c5a81c49050301c0b4020043d51454180100030800c0c00040402204601d0010507003e07451b04201800c290fa41101e00124104c00c0c0c8040540d120303411310380e010790008000310130804600e1001c2600f503c142d1219078850303800d82d102c51410004850071680301d4005040405954a0700d01c421407003101c410315030720440c0d180c0904e1130703a203508040c0d100f00b1502c511500d0b05111010002d82525803400344205546003602500d090b10410795528600c0d048600a45000540555 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 875582068 1250 875580818 875580841
    0x309011110050c21040c0302060a020a0b101d090705101e09080d050c03090607060b0a0303050d110903031207090b1308190201051207180b0c0106060e01021005 70
    0xa440d035554070400c924907200c0081001070303000d803003001c0342440110354641900e001c01c078510f401290808028201c90b030465017400034580c00000c1c08000d510070b60b40c050001510b4440c605104030030140015040610b8800c1c40200d81564412400841c00071108200b068070001036201d088400444020624038820a8169407a0603d164840c510040c0801c401e405590081c54007001c8038030181c00c80c0d01c2c2c0c0f91445802c451a028804441030b40b038104018000031071408801a0036000d004900000b13001500350001100044c440c1c0c42100824030100c0c03245211401d0b442803801e40680c0081b054605044200000e44902c501c2203440741e0a41028003180301507104906441c0a0400000040e55585007244421342140d5144030721020b40c404d410f8032010702090401c0c034840d01c681c1038584908103217200c0054204041c00403d4041000b404948101030540003084110060042c20078440d40c484a440c0c0d00c500752205500000188000c11003031840744c0e6800115481d0494002d207002803980c031181420700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 875583318 1250 875582068 875582083
    0xf09071e180b0304020307050102010b010c0b0402041401031203050709051c030210111209030702060403140f0316020913170f040312020d0f031404021c061d0f0f03090111 75
    0xc282141c421004a0182805001580600d000b1821901030b07503559001203080c1e0f54925070840c001800d42c10b000e00001d86501031107402a10051000c20303203e04800d401903400e2803d82c0141c03403840c2c0604c0d03140502c41e014801c45410082c2840c1c40386601d0f0403d00814907810116070541040a010040c01051502c24424880c00840c040c03000d204c039050001e1a041700e41c11501e442d89400f0049000b084040100004072040503601404481c100b13403858940c41c83c041c0d20008212074600030340c030112141d000c080c002000a800325620400407020580140840070800610140c0d40c410b8125100c0e010450000030b0201c081610260301e81d5440011414440a000d150701c02004554403c1c01c058100343c0100c1c807108030a0440d0788000c0c42101400b0118142c4061103030040d5160784030008503016080c483e185230341411307845048451410f01507032400c0c221801c0d4080003400314090b183c0c401002c0d00510841c04400400e41c002d00104e440c80c004c00384c40e880f910703100b07a040c020b1100321800c01d00300c18131102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 875584568 1250 875583318 875583347
    0x207121d0f10031b050415020c151b101e05040b04120e0a0b0c0f0604120305070903020607060c0219080d0903210212060103021c0504020f1e0f09071e 66
    0x19a031011310400c3c00b83c072941087c020030080d1079003c680c9150f41480019808000c0c0002030481000262500515400f5031044001044860860700085024241046620071801c0100400aa030000301c50400709c82e4000b940c0c0c0300c4072690404062101082c0441603268015800c20408541c8800c8020180c3c1d81881c10200745801508001001551f116440041c2c51592803550540f86000c10b0900b080741c6a01381240c00800c2850440f003030309000d6100e0740c801a4804600d0501005550306e03a00004c6564004440840e84a41c4541e50380c80c18070b0b03040c400e51503200a01c1d0b000314810745856496401d28042c8044108010fa59000c0000605101d100110603014809400c0c50704201d4242c1c03010080c2d80a24034a403004c41d05000480c405504c40d2080b40c20352240360f20b42d50001090b0021030b4000d03240c01791059a01c0031200d8420141683c0d070840040700001032a980b6103191025105000f50107150000f5248142c202908100200f9000581412910f0b0100d034144040343d2a143c050710307800a0020750 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 875585818 1250 875584568 875584601
    0xe0103110412110405090d0207030311030d02030a0207030e15040b07081e04140a120813050415050312070b041203090c1202180405030415090305010207121d0f1003 72
    0x20030090000f4a0001d9a0200080e00c2c10711140d82c07844000ca540f986099650030042e07000b68005c0010038030854841300443c400e0010b581c0b9251140301d84d0400e81e0030076035a0742d040070b41c0010307100c080541107207481c1c4c0307041416141808000b2403010111942d001d2442292444c043c006108410001d441e001c90f00b103d001d8500c2c0c0c90580c110704030b070030704140c11601130100e113240d081942c0c21040c034007800000211141881055411807442e40c90b90000e412169030074040001c0c1074804600c0d540c41d030240f01c44007000c070050142e1003460002050325100e203607800c0300180001001054042001c000d612a8450b4000342c4c04e1542101015080b0f00074003c0007400b901e0900d110901280500e404020700a005000300c805c180401b040303000c01c41c2401420381d80100307542c1c010041004900c0c0c242038401035200c2d0340d042c0b104034103036262031b41420780c0d21860040707464003507030340b4003850030794000b04103420401a012010301c0b0700c08240089194407000000c814801c0008482000e0268429045401d0505582c0306 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 875587068 1250 875585818 875585849
    0x1606020d030e033a151d043315060504120303050702190b01061713060e0c09010e01050405132f04020d0b090604090f0809031e0601090c0509010e01031104 68
    0xaa07400100012035400418100175040001c044010101d41501c0329118480030f0301e50b4480fa5140c4d112880c106103010315029060316103c002d17118030040403481c81a0440b01080c502d0400700c110713001046a030420b00a10106110034051800b512150360200303a4107090004282d1603e1070280d19105403000b07a10740f20500841440c04000082d052581240d00a44039071b81d54002c03024016866010469203e01d40440c1c50038084007241c0035800203807003080c0c401c0c16a0400031800c0d01041c0601e1090304401004181400108118241442940c0e4030054400c84280d40300c0c032030369540c005981d40e21080d8a102e59030031003000003141901481001d40000070f000715a903002924442000c2e081c4903041601c1041d02000050309401d280c000c140650303a104202481d07440c8a6581d00314550080e100c5141c1520898086881082c000b50003201240c2c281c1c801010f140d0b261103130000540d0300321790302e01c410490f00b400301e015566001103807020003c2c0242408249115040041665800340e81d008483d881c079140f2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 875588318 1250 875587068 875587177
    0x7170309010603020f0d03080604270506010f15020a060b15070b0601031401050a060c0813121511120a0902041e05010f0e0402100509031606020d030e03 67
    0x18400302c21a4402e0f529904400c11480400c42255101700010700070556035030010f01e6501d072550154426801014409440000c10305c0c45104540d45040c04903186e510180040c8a401c00142c020001040c1142c002403001c407030b01c03000035105c5a1251009000039220300c11900e483d683c10711010540d421190216482ea2404e04201d01503640c1130342c12b6804a464412141481490344d00b01c2030507244040e081d900c240d4504582142c2002c8005001d036180c41d028400000d041c025819004010f180c45000c45802c1013860901494401c10609000d401918241000c1d00d126016801d44103400d040402c80b110550311040c0d00405412680c10080d03005280584400c000b502490030700d510020b290b00100a40da88441180e105030300c41d4000d00354a010194005070041c5840116402072006600d802414070f081c60000c40d20b004c599589008414003030107006d12001e0750400c4241c5200742c962401b0701012840c80d10032a01c9104074a43c441c003001800104071600c0313207120f42e42441103107000d000113040784224 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 875589568 1250 875588318 875588321
    0xc0b07050d05060306061e0f040207060617030a02060a0518011d070501112d12070b0a0504020f090703020408070b04090c08090d051b0303130b090109050604080717030901 75
    0x41e01005160380c54000420810306000a13594494000038015616030038000281c00108022135046540c001c1c00d100441c501c51b122400a03001c4c25204041c041815800c02601a414080d844010f4000303030700c148404207029500085240d00008400c00c005819210381482000f102480c910401341e5608009241281a51240c08040100c0d5081c00392252107858070300440391240284004000d540c802102002c10111800f00e0480e038650f20344c1845500400000da141c144540103540a10406c008101030041c080410007855002030700680c200f00d02c1c07600b40e0019024042e4508040d010311103040000340c3c01030180e41154041c02031036049985003a5141c9101105510034006d0500d00703400c00a48003007150040c240701d4003031910200642006c459032041211543c01c12408940d4004c902c1c1100c0b00700c5ca80500055020f1010807113a4440700005007020126544064818a201d030315101c1c1c140c011603400328090f908180c1c403c6440d540d4094504000d100142a000440070742c20000050001d0380005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 875590818 1250 875589568 875589577
    0x1f051302060a0f1e200f0d0c1523070315090603050f010923150408090103060506030115080a15081011041a16080a1d1215070c0b0705 59
    0x2d41d450301580d0301c0c680b102c00e82810b000d510600c003103281017841400110000c0300c82d82002d03e0410403a4001000314900c14a070984030300c0324002150300f800400081c0315950910140a01c9110300c03c0c081c04002c6d0b10030f49070350015444841004600ca4001c80c001a01c40c0d00040040030095000341c002a484000d504010300301c0744822034181c8940d0300040b454510602490038196040b01c910718000c0c000d41c03841c4000c0e03002006180f11a0190800c8000302c8191101098050340c095a00b140c2c4840d034400c00034007260340503002980f0459082c0010040390703540c28210210291071b46040c40080d201d80c03641c100544245201c011a6904220010a14540008541d05200480380f0148503e4801880003440b81c031650040c0b15030841c2a001e00240e050000c0000c000f1000c9070441c8400e0303900070f51100000c50b00441110b000040c04140091000c906007900e040d41030004403001d00401004184072a0b0700e050703a4041910406800340020340041c0904181c901f813a400402c0178a07103103807034040184503501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 875592068 1250 875590818 875590847
    0x32601080d0e030c010e09040314030106050c010e0a0c0b07060e120c160501080f06061b1c08060a05010309080d0c02160e06030d031e0e1e1f051302060a 67
    0xd90b45201009240c0022804108072068403403550159011040c4504808020010350a01c54070300b00040390000b84000660092a00d0303901c168448442114443c00d480c8454405104d03a8042e603041400b0550441c1484101e401288040b60b4450701e624107a400340c0020020881d00b8081c1e00d12111402c00000014000c868079902500c128401100c0024205122401242e000403090300000b0700c0c0d021085584d0f600040c00400c007070b040c40304604040407003c0b02c0000400454104031000c0c605a410f24201490388c520505042c0281d25100001c07072f030002e80c50310410f810582c44c1c02114040c00019022503007800c03002c0c1401d00290828102c003039651308081e88031011264402400041304801440d103d801408020081c21003080e121030110301800a440410389050100528142e01108510510342158803107000b60540740f40004520280c008000d0b000c100640250302040e410502c80307100000040c001d81000100b50303e8618040380c0a03d2000802034001d440040c09440701c50f0052501e451110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 875593318 1250 875592068 875592077
    0x2a0a18030b011a0c1207140d030b10090b0d11070c0e01050a050a050607021201062c0907080a14010209090f04060c031b0e12030a080121030903032601080d 68
    0x4240a03c150f041c0c400c030b0001318855044111154041c0103c41c004085480c050783c15040e040d50003201086c14503e2802c08070001c6941e1390203803171490074000030615003610241130104006113000e841c0406482410303880380d00c0b90750300c90300d543e80b400c40d18041c0c8040a41284104a01a40740c0191082c50360f028041e11344608001040000c40b464407030000c1c820f440d170241400b07007001c0706582030200c00112070400881554031504c0c01306089400071a2014400c1807121002c40e03d55400565030401d0070040c0014070190003540050082802c0050303203203441544039900140d40442e800450b4024041c11404643c006024424801c1990307070146440e000f40d004180030030080824460a07000c80e04510300c920004079040000281103800340f900086410806012101880c2c04c45c0701242c21903100c4141c0c0030100b907103d001403158a5040d48840800301c03148858060030002510003510400c5503200c0101009041c00c01c403c0010b00d07008841004000c00d05240c3d4035541c48410194940f5110048040002c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 875594568 1250 875593318 875593349
    0x90303150303090a03110f10051b0f1504030903080a031b021606050903100204030311060108010501081c020f0105010609062604080c24010603052a0a18030b01 70
    0xd14000c0125074409600406541380285103586296103c24501d0b44254803100700c004100d02d944900450004811160392140e03a507034180d51442003c00d2000d2524035960b032000c050107080c2d0800182141c00701d2203030f0300b50502c1c0d0703a12440e00b100c4108403900b0003041c07981d010880c030300141d41541141d4140c2480c040700c4801c103001d2078012a980d8401142805140c00105000c200e6540148020003100c43c010741038806003180e2911500070703a481940100d000900d0142c011007614000c1c081d003405802d0030402800194949154959100d07801254847c080100c42150309009000f0030002c044a11984d00034071196a59190203400400d02d40f0802c00400c0b419102c404440034000c50a1203208201e20301d41c61581c54644440c074581d000107102c1c04c9144a40c40c04202410740400311100c1c0004004160075141d810406e004003603034409000500c0040d134202980741c000107000d0444030800d07042b800d0241c9820046404a4900c2d044140003060404100c00c0842400203000030765041c2d03440c84074805481c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 875595818 1250 875594568 875594611
    0x60c0f061006020a0c06110f07030b0a060506040609090216021c0c0605040b0f071e08030402130606080a09020a05190e0606070203300c01021b01180b100e090303 71
    0x25001c03c0b440c0100412030500c000d0040a0142950011f000128400c0f90320f2a841800c6807440e0801a800688940d000343e03040103604d6405028036006030106071800790038103190200181c60513002d40030300d22040350041440a051003214803103201c203540080081e006140c10403510b000034132145509880d07001511202156060143c01154201d800b002c00040c600040d803108000d1035008040c003116400181036150081c03422014800d1000307030041c03d2a95983c10a8410070070412410754226500504280c41040305a802c10450396001c0303401030020650850520000e600d80e881c5810890b44a001990442c000c1c14110f0208810b40310030100e80309a5803101c4081142c05d000311b0304025410f90001040001000024038443c070608141c020f41c0c0c44840304c03a2902c00944e000b9a504a00c141c0d80441c080038000c1d528441540e0444000c1c00800559400107800e0401030b49024015003188941c5e00441c1101880c60303407641c020702411961003040d0074002c840a45913801074444913501c008520315410f6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 875597068 1250 875595818 875595823
    0x13020f030f0a180b0c07140f010605030a030509210d210501080c1306091a03010b0f01091502030409050c070308090f0d111606121d0615060c0f06100602 67
    0x91040350350b107000392207001c50380c2d40100e13201c00130440c2c42c00c07941c00c1c8840c0d030006040b03032100c001c0c00350040c0180c00c3da0a0005459402c440c0c01c2e50003c0d1081e0300615918002c2500078040301d0700e60b8820f58550143d03400c0c0b000f1100702d44220b44c909141038441c03510004900d0b41e009091141c0c2804504200701c80c1005c0100d103205a4a00303008802854000a400381e100e4540055800c0d40182c1803c400f1a0255681c46802d0840d5005c040b1401116090b0508180500d028401e49e0090b0f8000c440c0d03041001c07140c0340001d0050800d4056554581101107034815054003c10956000300400e0405000c58600360302e130082142c1000314218042003041000c1201030301d002c500081c040c80c0a500501140f40b240b0710480e449451030741c00c00c0c0c00f400f41c4c65600d081d00c43c1c50790101c1e001c0c192607115038030403da100070000c0407900456404924600069210180d0103408110b46420083c3c00b020003900401402c00980c4601c02c4e0514001c1d140300c1d411080380b213540d02049240c400d07408070022044899441358240d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 875598318 1250 875597068 875597081
    0x50307080312060a031205090406061814010302070c0f1d0106050d0209010c0249060e010222030b0705070218070905210c0612010603090213020f030f0a 67
    0xe82600148403004061400c600c249034400c1c0c1c0200303e90b9009a072070310340c0e09090481e145141d0000d1030000307202195003003d0055000a2800740750503103512202080800d815104c0b8012035084034903041c005e401c9603120350140e03240700b0b03000031564002594440c54190b443c09540320300c1460114070b14401e0b00d01c002122a0350b0403a402c5031185454103890030007080007544038032400c1c0d0603c100ca0041401507120340004000741c081301101c641004411a0300746089491003090442d4601d0917020310040745000001c03e202c82d5504c8080840c40d491541c200030301a0280240c10514011180e2100e10301580200c000001c89024043e40b0310780380c507600001c070b54034410341074003039081084081e42141110820f0402d580c800410f01d03203403a03030399203d100140e8421210803007500201c401c038a06082159052002c00440001158103525141c0216840d0005881c1441110185a5501c40310815501d404070002c1580c0ca200004641e03030200071050b5182c0e80c00070759000944850400c005a00200c1d90710030b04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 875599568 1250 875598318 875598329
    0x1020d112710032a050307090e06062b0203041208090a0206030f060d02100e01020705030601030b010e0903210f0a0614100302120f0714040b0d1802150d06050307 71
    0x20035110005840a4004c0c0c444900c440691003900b195460740c50280800c81018101c40d555019900e06203504010541040b40c0c20500301400b007501800402d503540001c9903e0400e14032105600000c503030001d581c152012041c0240c10300c3c0008200800c00507218070030780c00034010303449070452602c40f180e41e00c2d511014500004e40141080000ca0754422856102c2ca40c08407004022107074211455011440c2c00010304c00c0c00e0041070b80988a42407545e010301c11b5002500050300202400d6245454080c110041840780b0f10030807440d000815607020050045860021918001d014120f061240ba01000e0004a40c25400070fa034043c0450030400341400b80400b180d03502c104140d4052040c0f401c01080c503c00485500615500700405030340c04c49864801880740050030100d407001e19210001400c5903010040b070301100c2c070301000140444940e06058562030300c0d0721080040c4400d01d0091581c1c1e6412000c80c0607600c814003c0701c2c6016085a42c000740740040540c5010710040b07640d403061640d2505a4000c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 875600818 1250 875599568 875599579
    0x311090709080a06090503190513081f090f0c030819030c02100b03032106120f060a1109060d0501061b02010c1e12022a0d02011101020d1127 62
    0x1000c0124299030171044801c0c0c0100306492800020340300c00c007a028001d00d60781c00030400114000c1c0d4035030710080c1035a0003803800002404a03c0300c003614814000c0203051800c45035a80d100110000d00005d6a00f10902030362124855450a4407420044490703004042c0803048214281c452070751b0503210307003d00c0a2144071a001003542c01c41d15540380d000707400300c0c52000303405102c00d019584554007000007420404580c04400713545400d00d0f405100c0704202d80c401d820712543c0300301400812011f00103005a803210504200150303800d841102071299104207400c0c0c41e80003070017041c002c40b09441c4d60301c41c0c0c1c12246981c41e84071960010304c501c11215155818040d011034034044d82c01c4046050301d402d0324041030342000690b403010003903503940020003d62007003c001a480f1541d5030100c2e4a010800c5890134110030f081c90090661b110020701014032a50000b03041000c0360010b400200c41c01d4043c0e490001c12480d0034861007404620340c042941001c441c2c0c1c0000030030705080042105003180c50b0000120090700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 875602068 1250 875600818 875600833
    0x82d06060d15020f1806040b12060d120806040510050307140d0804060507030201060b120a09030309081909170705100221031f1404091b031109070908 66
    0x1085070039800d0400541e0461440e000007007001c2410b100038804280d600c440c1030388421000d05800d5094405901650081600b0070041c00681d0080d015036011b00e202004154150b41c509010601c2002841802441198203070301d104001c580104000348200da0036502041a80e031080d003914a60320492181c0d5415804c900340902001b6402645e206c4200ca01404100f04103885a40700746840d40903600907800180b010407075104050342801020014a4004080d5042c56a6200e4172481004003402c0c1d81c801c41c2c0c1d912020070402d80030350429030505e07030000300c003079228150384124401021000c605800001c1c81c04038046441c6460b848a003020a4000000301038290400e01030000054181c03140d001540308a008142200b000d82c03950281c3c06e000301001ca0b44905009141c3d64a216201d403c052907021501c10034000718591008028040104031000b15030b4030228240042c403034105c08000290804c1d000404810300601e00c02c2d51a20712400d83e01e01c03003070b56204007088620904a004480701c87d0440300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 875603318 1250 875602068 875602081
    0x111008060d03030917030108120301270b13060503010f0e030306010c020d06050a15080102090d0b10050a0e0105030d050415050d1103161803151113082d06 68
    0x580c0d00d000907120f820001100c0ea03d42d111034045000c072a04181c000d0100000501c041d100a000d14a10b110081400781d041d035044c4201e02c880d00e00160155001104690254199081a500b041e003c049001d44800002d02e8205650400391800c1e008040c00b035800e000381c01900d04124403a0080d00d400b0344015509580b118001102c4000d0300103400e0343d10502c00d07000000410710910901d03000701c1d48400f00144c501400d940320010103466500001003a40b060014066540301d41804503c0703070350f01c100680d42980e82d0000d000341101d12508259000302034000c020908508241515040c0da00417011104c0380800710100300c4161141d8042c0c03462000d4611240c0c0e03840d074029030140c5000b813510346002c42c1a008086255006130001c80d84900b030b40700b00038400c1d10355540009402c90000703105030031b4142030340c25500c441d2a03407035120109006850781d0b80b41c99107801824400750b03042c0c8184034200d1001f043d42d44440660700c0c101c04105c00540c101040d141c0c03a50080101090b840c0803a0030010708495901c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 875604568 1250 875603318 875603329
    0x5030a0312090c0510030911010e09310b040c0f03021509220b0f062508041e171609050415061205011a150f040f1211100806 55
    0x2001c84610882c0c00f4042540d59441d42c0e40e140d12101e0b45e6001801590504000c03000318084a4800c7c103104a506043c2c0e41c6454003000c0c0b65129844e03a80d42400300392411500c52400341d84885400440003a80035510800c100d412040340a640030f603c0c90001c045e01c0e04800d00060200344802544503106182d001c550500010185c40b03a0300004140d0054440b861280b8110702d03040428000722559591040400c07440c2200c40814818015914503040107800c00a884406030012007008812101803441000c001083c2e0032074000d4080340e42c04036000b01c0c0134451014002814000c11400400450509402440000321400304080b10400e0701011890078a4200c001c1001800c280d42507406a040c032103031200c00d8007440c4c0080042c2d840741c1c0b00464003420203900311400e2800101ca451040200001180d80c0e04503450041d032441c2c450a60742d0080300350840f406101c0c0f40d00c81d00d0240c2041c180014074038012034910700c8450054207100f9103928040c0400c02c03403050744913820010418010104d551030901 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 875605818 1250 875604568 875604581
    0x1f11010207020a12260405040b060f04090212010b09030a0b06060c0625050903060609190c0207140f21070803071b080a050604020d030306150f02060105030a0312 71
    0x100006140110a401003100070003150031003802c01540a03d4201008031240586280f1994200769829444400c000c0c41660722481c46103910564071809988040e6491b4411a203010720100b00c1d0559440c1d481c50b018002e0340001e00f15004c690f2220b4000648080d00d00221146040028042c0088044036550114200005044540c028505015903900c1040400900703014183d0b00300385203d0181000300c0e80b406000402880310400c54140b00701d00458900090441d0002400c80304a0510741c1c81c52040300ca14040303000018000e6003080c545400070b6030040742c0e001c02d894241ca51740c0065840281400070074184282d00d59080440ca00c2041918a403c0c80419038102400090b102619600c00050346180c10203003065490071901e04542d80e450280a085000428015000e02255805c54031000d40700e0310001c00190084104803400c41c20588070782d1101c00503041031051000320701c1c01e250b0028000d100582c00c40025100b0310001141620b0300090240085906a64500c0d0303200301d104e94080a082c0303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 875607068 1250 875605818 875605847
    0x14062b0b0a0222150309020a17030715050f010b0a2102091009180506030d050d0609050712051515070f120507120f0816020f120c0c1f 59
    0x5090140c110b41140010780f004641d400001090700315418040c6a1464440d4000d042003854940900b02c030058881c0780b1208200d840c120b2000b1061a41c0c44085400d52003210001070028170400120b00c0b01480640c0818040c04d0020040000d607a00c034080d000c020311900180e50045140c05c508001d20b291000c1311401c0c800c0c44124090304203401d03075011070800100c840a03030000c110401c0c1c0621481c0f02c01915006103ea03440e0041c000c3e418454086030701c840c00e02d0000010400700041580000c4135503046413005001d089000c01251808040c0202048100740b181003140d81010301180015000320329440c030781d03d4000c1c54200002030304100314034507502603401110020a03c400c2407010440441950710800440c2e1512540c0d0300491501d420300556010700c14003070214081420302d2040c0d100d9110741e4080780300a9055580510b018040e80b61009070900f01030319114800f0212207080e0080f01800c546000e10f0201c030f000d11002410003864040c690b0804903804210840e10380314500c03a0580c20510304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 875608318 1250 875607068 875607071
    0x220f0f050c100e010201151203140903060c070302010507110c011209050f010b1903080304022211090a0f1d0712050403020a030806040c1d03030d14062b0b0a 69
    0x21a680410003503107420000c2c03004070304000c2a07118035580a0040e500d0518020390142c440e1810280d118084400b402800b4080050880c81e00c00c4544c00d0104913500b4001c024100c840c0e41c602140101d815901c074000440c01542001d000c1440380303000321480c564042d030a002504d40398400038011075584d0141030400000944400840d4045402480104100450b020001c68018004000d001000040011407400c200c01c191040001c1000642500e0304a41d04459030010441c0c9802110840f46900486c5a0814034280e88060385042c1a40200101c1a0985850003002d80e00c2481240c4007a10744140d4801880000c041c07007000080901c01a444489030138600c07090359010103001c046030402c981c00c4025a000c150200e040c10b400403001035225000300d40034003d0540300a801040303410000106c441641304142010301a65003803081e03400d545100c0e80f023040000c40300300f03142c2c1002030103603017850180b0849083c0741003070784418401c41112080c0c5030464819046580d90340c522444000c15045086 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 875609568 1250 875608318 875608333
    0x2c04240e0c0d0912021905190f0b0a0614150f0901091d09102c01060801090b1b0f191404090c030501080d0f0507061112220f0f05 57
    0x80c2e845a411254064440c1c0c4051008a5002030300d840e0030134030300140c903070101e004040008100040d04100448150b00711a0100d00d98986000a60801c00f00142841d03025000c0080c81a9968480390450700c3c0890240c0c44180e042d0700740690b0141c82c804000c0c24035820403c041e01c5c4010170005004120040c904103014039915001030461403200700d08004864248014072240000c108074191803007015410812240444000f4141c1c0c1f048600c56003100300d0071120040ca050082907004200400d001c00080c482044a40352160204508840e00d16040d07201c070420044924011050384d1010f080740517214503041400010240c8615030905a0080004402e10003540c00c02400141009000400011075880501c1001a00383c0304160001505036021640340c101c03255001d48401e282100c103041856071004035040c0301010f01a50004c0700903283c000070745e0440f120300401180c1d100d1914104044105003a031403401d0003c02d00d4880281c6203544e8007428801050451b050410010310038011907100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 875610818 1250 875609568 875609587
    0xc0d030204080d0309110d080a030c0302181011030d020a200607080417040e04330e1617070914041203200c0708031c05072c04240e0c 59
    0x100d4800f030007201c1103140449e4601100c0d0301406103820707003a407500303081d810960459407040d00c80c0750010b4040c3c4224400c0b54101d0925019054900039610400f0035a44d0314039000d2030350000b0b5844102d5140028481d1f41c00c03050828880102c00070349440013401341180c1c3d2504c040441f644080074000399085207aa0840a020300c914070020b0006040800d41c4410614050500802d40b5420f01498401036000c11507401d54522207804d00082c20a0000000504c80c405070301461030036981d154400c03c10341c0a24404611100059048448088108210303102c0c03d48444030f070002e580300501140340c00014900030900241c402c0000f003000d10085d203800a408090003000c1844681c580d40a502d1584001031900b481c1c01c02806544003406120004500c1c0c91b0f09400f201c9080110109504505035584001c98050703880303080d03028246504a1890500352400039218000d046904040d603104500d05100005140c442203040e0f001c081c040c80c6030500052071b01ea0001c9040000a103040b40c401c030200655082c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 875612068 1250 875610818 875610829
    0x1706012318150a050609101202040915080f030c0a150b060304060b040524040903020f070303110106050913020d0c0506070b01050312070b070e0a0315020c0d030204080d030911 77
    0x7051419504030782c03502207540c00f4401148504c0d08020302900d01088500381607240c50b5080324490a2900e8158085d2114510000082c015504400700442c00c103801600448401c1c448003050320003190a59080040d04a243d558900ca490104882a0804500ca10110b540100d043e000c5040546000c2081c81c0100001440740d03000b2a41141c0d040e40e04c45d5265001d040070302c1a56031041c0d0809a4007600c14031692000e100300f080d21f540fa842680c81d10f001e0800c05109000b1004c24400810031140555243d02d409004242c4400545400750300c0c003640040c032807600001990058891200d00c1c0111292502440780520900006403402070340f00000007030a4650900604c240d5001c1c0b1801d4083c0c0d414142014101711b10311052208000061144202185413141401d4110903035081c02d00c0082401400701c0c1020b2406d0740042e210960b440018040c3d10201d400901d908003200d000e503403200902400607002c0b8021401340d1000756020700800c1c40168040d502041c07503607001700d0303140c00c961812500180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 875613318 1250 875612068 875612071
    0xc0a17040314030a031d030d0e0a0203010c0f030b150901050a090b04180b091b07050703020310020a110a030210150816050a0b0903061605120901061706012318 70
    0x89881c3d000141803400310394184100040301c425002017015000400e081d09550303006030140c442e815665801c1006011038204481d240150b4040e00a101000b09540301402c00c0c0224264240072030300f008401a140c1c03410116508801180307000240c141601d10300112403a4000045000030b003c290714012890843e0b00c0094001004951b20b170300a422156280d21040e602042010390044200780144041c0340700d8404003800032480c000712607440d8a03103820300c1884e1190541c030294142c0a403d500c8040c01c0c0c0550014001d0104ac0e440e00006640725038059a03807060000030180040e00001c04e40080d48501c0e411100d140c01c0d201003003800355520307080503e0030b1000c1c1c2582001e0392030340d0410810180c00e0031a1080002c000d2a50454149420a0042602d99030b000745441410300781054134800090044040d075041103e0212040517920388501d00c14000d1889000319900c9070196020613501c1040000c0c004c2c103840c0c1d0307031303400c107400e0104c60000018032000900c0580d844030f40d40030b408030582010103480d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 875614568 1250 875613318 875613353
    0x80304031d0a18110903030912030d060e15030f060627090f07081b13090602070506011a0703024207080c040308072d050307170c0a170403 61
    0x107003d0300030100c800088400001c02c140284009120034a1103503001b1003940c40e42c0710107031401d04804800a4800b815032140d01c018244403840c01d00d010840351522803500c1d00c1104d94160419010204004040c0d84800c070480e00724241c5e115100140c4142042000b00340301c008190b0140091100e845c0d2145041001190720420a80c0600030311200031404104a00080c90b4901c0500041088825100c44003403030182d0f02c0e4000d24440c400c0140a54580e403002c807045030040801c5446d505640381c003075201c1c1c81c00e22031240316828440210204086c800b084a28580c0c1c140c00416403150508000000396103c10381400142c5980c3c07550303541c82c20002c01c0180c03040007008a2401280790034017018081d04400382201d8042c10b41800280001441ca104440011b6040008a00341f01c0755020f0396011002040601901000102d10b40410004004068608148104116081c426100310100e4840c0034400040c091944003038014804a0107640e0b260340c11940040c8694a041e40300c1d1108a50f80d60340300801c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 875615818 1250 875614568 875614589
    0x20f1320070c0e07050409020322051005070f2340030f030302030910020a03062607170a06023025020a1202010c120603080304031d0a 59
    0x100e020802030301103400240c091201d000c0030505155000030000d00640c00786809688c7d0000215506058401d1121b1225541c01c802c0314003204140340540d2519541662030b503036642080c021554403405070b1400d1860340d00740c0d0380f0404004860030000e201d80d80d5802d6108210a000c00410b0041213078000101901c160b0301046582d80d502a4800b800c500f450803100490b40c1400881c10320005400c47d607161510b0f50503140158490b1104002941403c10300040680040d200150008506405412020442e0504040450100c1159854404c51400540c40c1e500581040209000103400700b80080800103034003003160042501c0b584c480003240d00150000d501141c0c90504a203000d1810824080e05211003070385114641010360b030005610445610795601c0960540007640401c2c030800a02505940114a802a5034070405000c0e0003088401c1520b0700050031400c0c0b41c0382820480c001c9500300c035807001d0450b00d103507180e850403211410070115841a4902ca40c44c098004e0361103004860107003000d5000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 875617068 1250 875615818 875615827
    0x22080d0b0306100302090c0702040e0715030f061805100914060a150e010f0e0a031b1d070507080405030105070206090c0a0e011e0e0901050403031107020f1320 70
    0x3094503005000381050044143c09000b4001a12a110515041070402c0c1105071124554070000b005028503c2d08200d851181c503400080034840721030b00c0160f5141c90380b0304020003025440440140d035400e0181e00d4614403042c40603400e000301984500e900150303032440005002e469a2080c0c0a5071002c908411844404a040c0304940c41c003001000014003200c01400400280960301900760130702011114140007603032126910060080c1007841c0d841d1401000b04245035280d14081c1485002c003065400d02c031403c650301003182008841c40c0803d865031107503412002c0d9915a802c8805501100c4200d508201c1030000061a807024001c050059010385c01401d090320700384568915000914007054410030318030ba010003840d03801140d501c1c1916005c0c45080548080a4070841c1c60f05210791001c00d03012034030307002c1008111040d84130f9400f0394480e9406006921100302101214020f6032001380d844407070741441c00e0345403908140b00ca441410360036001c2800f03080982502c180582401048448c0c070f10005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 875618318 1250 875617068 875617091
    0x90b22270c06030903120905070909030c060c05120f09071a1c110a0e040e030304200102070e0606030601031b020304091107030804030c150c051b0c010822080d 70
    0x4000d10064410b51504024655142d2401018020703041d081000c9030307a444544405004040c41b40e68007031f000909003800a07410500c0c00810311030b800241a01c500b440c0454203010700c0d01c120112000e0404180209078136882e002c144142107c8094407100e81840f40040c00160807084014000415241102d465210041c0100443e5544402e486010b9100d01e0304660388140303d40c0700251812102d0501d407080c0c44030410b10104006040c0040c20700e400d40b0001c000c00c01008820410350b08405c4021140601c0101050011b82c2d6402d0540070b111032140345040042c241e81005000741d540010145804030346844110103c11142c41021520070060b04009001d02540d070300380c05080d00742c030b0049007454074000854600030007a0704040c000030204140a080001848519104500c03130000110703040090114100b000f034019406805c540000c0d004000e1040c10b40c0c131001c100074030b030504103071180413495441e00ea800040311200090400e1042200f814040451030307510107072601181c490400940c101d10781 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 875619568 1250 875618318 875618333
    0x130905060a140702010b100c05030d0608010b1201020a0f0f2708240606070c0f090b18130213110c0c210c0d140a050606040501090b2227 60
    0x3c0502055a04240105416072100711104000201a160856100059140480c10f40c403d011100c1c82180c280341e8045050340701948009003c2c0412910702803c408d0b80c00c2c90509030701030000c907070000ca424080139040441c007550030490880081d28080190f0450589204418058505030f980602c0038103100b800014410409204807015240342a0039102a040d060310103010001c0549008100220301d120030055061001e4026028001350800c0e1592a072104a00800315400000d204500d401030043d001891241c0700d0b4003030b14407018030085c401610303001d0180c46c41c58100c0326400c40356144101c03031110100d0405040c40c01288805058041501020002c070704404545940e1084995213410f8101d400c0043c14080d0f0b14000d80c0c007102c05208a041c00da013500b4103008205039600441072034600b0004081040e902c50a4120f40c104180c0c1d07200d03801070301158070900c2e41d80d8003c8003100d003001118817080304c01000462100300110300341d20140e80c0e2402c0d540021903c03842c8000404007050402036039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 875620818 1250 875619568 875619571
    0xf0a110a030905271f030c0602010e0c0402070515071b03080115020601082806020406120e03180105070501020903010e0a060c0e010e061e22090606080402130905060a14 74
    0x6510b4400200e040310700c00b1010190080d28010900300d4075202000e001d171240c4840390045812181c1401002e541e202d029028010201011001d0b0007000c9960296107403503c26100707040c0d0024000c00c8010b400d03011a0114801c050860f030280152208010341d40b00c0c000356503140361482070742e840044c0d5160140030150341c00325188a00c155040200140240a00019002c070545544480000b480401251080e0025007014010300803500006002c100035400081d4503400d01e50318001004038980348007109440e40a240f10004640781d05040c0510150310030805410800c3c05000014075056998000908445402c0d02036005900007010040c1070100b80d20a5100811a43c01d04240190500000038410246041181e2003140e002c60428203580010005000702138002001035a00c1403040e2000c1c44d0042d100f8004c464100c41c01201080d820080e0044204480b00ca480344c0c0c40a440716401c00402222441c07904865640d00c0c0b4004021650400c07943d401902041400281c200d104051002500380 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 875622068 1250 875620818 875620849
    0x12020c10230f0c03132427030509010e010e040606021c050c0613081c02030108010b0a0b0a050c0a050601030818010f0906030f0605032506080c0f0a110a030905 70
    0x16001c100161001c4860440e9800b0301200410800c201840c98842c421000d440b144400b4030807601000c10749400e0a602108070241e15400314207107004500f82d1401f000180e04c0004001420900203942254025240d0310001c403814144000f61b130700c9149c00316041315003070741c03120006034400341811070a80d0f411042800d0703942d21482c1c020318100c880c407803403540da500242541c001244145c500c003081c40306440c02e54603105c2e4500000b55250750700e810000060340080c050269154038205000405286c013500d0441110303560442c140c20a2900503041c0c070640c021590440250090f082c903440010024040d9078040c610483d141501c03a40400c032007010698540c030545050000041a204402d90008108400c0341caa626011034001c00c1d04c2d100001522440e4480c07034040c1705440c07a40c20320780102c4140548415007101107146c0d09568810446051100313460144182c00b041105103840d0b100c40c0700800c01a6401d04280740000e042c0b07113101c3d141081d500401c2d0005084481c081c0681c0c41e200141c1d251128 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 875623318 1250 875622068 875622091
    0x15121107120804110913051e0709060f0b0706020903030c010f1b0c0b07110d0806090901020f030403032301030602030405010e0f0c0103051005060c06090609070612020c1023 76
    0x64203503a010b044043c0c148801c5d02c00d820800008096542ca00b0110b003001d42e00c0000d0b100710003441c0621030314490055607080d00500a480011988102d9131054074102c46108241100c10351802c4603110040c2c3c0048425503625808016a4030262810002060b0000c038100000488c00c100701000011998160040000e202d0120121600c4541c48a01111100c0d081482521140c0b5591000d680201c001000e0354514000e0194001c1d1194102484610900d420741360790000b9513035800744038205d01c55000d803080003610910103d0b010078480e40c06440101414411350440117040741c003c41011809070300c21101e00c0e070004100000c12a080c0106002801c440c0c0c010521948800c40040d11900043d00c0141003540c2c6200051a000c051000070f0010180030f00141c0c0d8411040c400d46842d030808941c111468442c48001c589034410004400003220302c103035030780d0030900f804980311000303940512100b007094450101c00c90325014aa100ea110021074030703042071494200d0311000c940f500000929907040b1b0b4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 875624568 1250 875623318 875623321
    0x42061903050634030b01090305010c0f110a0f230330010803030a020904060504090302031b0c011707051b160b070206090609060408010213240207151211071208 70
    0x41c4420a8040059280742000b00703440409000417102c007d400c0e031014020b5801c1c01840c600107034110810b1000c40c5d0442d034402913841540010155144642c10000386880c076036005100c007084104203c2d16204883c02c80c100710741194004044d18542101c6511000d03104000c0aa80904142508040c581a0500700301c008035850a4421520382c04006d0103103c119800052500e12a580c513800100a0100180100a405903a08000396217070060142050710082403030761807982200000b03110301c1c1c074201607555100d01780500c51124001c10707021b000700080c02400e000401204c1e0074820031400f82520b0000806240d22200c2c2c0c64840707051a40e00400700c01c07408111138000340c3c642d84116105070b4003e4851554808080000c282140714640c0a8036aa52000c107654408c412401044000c80e2040701c552099841007001c4a6000510001c07c0005079010480821014441440182d1800041c0c14413824040709840c0d00d0b0183c0d0341c44580d01600c54400103ca03004c016080b2031034003100001d454114541e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 875625818 1250 875624568 875624641
    0x20607021f090c03050d0e06030f1902040302181f060915050702090c09040b01030c0c1103010b060c0102030a060b090a0308090d14420619030506 64
    0x44885451050540348401090611110680d4010891183c0c1c003480c1200c05681d41d08029499844004042c000240c00c8020300c3d8513890000160b03805041d214440d038015403100c030100c1d907040f9034a032040f40903d80c0034440007002da40c0d028010302041c1043e0562401d545402d00e168118400443c41030004003040210a1000b0f50b80700c0581c00607511803a00b0039a14201029050320f1a02501000030340c0300c0f02c480200300c0c1605d0454003a048201081d5001e0041ca0305c590700540641c0c02001c6a40c001070125541440800d0003113408540b9044050000501440c050000c1580c80d0b0100c08101b201d43e400005000010200d842210300920140811500300500c64001440c014035521025181c401c021448451540c0e038403442e0420315922084c0b04615900d81c1d0801d81d19501026407019482454501e01c0c00d90301200b0b00300f030318891159181503030b01c00705410048003548405441d06030480310f0300782181c04146200c5c10010296000f00014503580c60140160300d40c101114500035060010004d11070751 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 875627068 1250 875625818 875625823
    0x80d050612190312240602070501080f0f04232401050604031202030c0304090606170c0d1808030703140106020d0507060c0302091521040507050105030414030301091b02060702 77
    0x4903903d49455101c0501081c0124068000011150b4103140320784002d4441400145640c0c1c01c40c3e076181c00b564981d0340d0320350042d50700010440785000d804109400150800308440d141c47d40c002e10500f91000345c01c1c04100b5100c52652600b9000754180e0120030000d008051003c030900a00c01b044039020259030603c40807030102d00070380c40020640d491880300030701e00300d00a10980c1c282044a10440b0303150342d0740d91600c001031710a601c500000b240c0c2d600a810640700200110314841e007158a82e123807520a1851550000342a0300c001c3e2010701c05401e07140d100280c5002c0085010356100e54010504911400105041100692101c01558051a60041015081000e952013070307070003040c006500811040d0070380192203045081540010941d800c03401c1c00385983c1c00b07801034401c0d011115100c1e00c0b0490802014040946010703020340c7c4000c0041065610481c01554441c0c03248205802c1d044c02070546e81e1443d00203030005080c150711800c590003201c0e490b40b00c83d50414118401080d5900b041310010b034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 875628318 1250 875627068 875627113
    0x9140307030f11060c06100e1806040201050f120c090a061706010503070c0b0a0f05090d0e090606041e091a060d15050a06050d0c02010219081003080d050612 69
    0x10800115940030f0907080e690041582c034400721a605a8015150088150400d14420300500c4a6000701e40c020a202c20420f0402001c0500240010051034485400558481e00014030503524400100001507049810840c2c0718045d8070880b282c60340f20311038101084500d400e1504203d0820031940050016080c0089040703030000000c1c241582d5075103c60300b04842e520520390024201044030001c1c010540042d500c00c00c05c600e070890003040035884820805441c7c4200c00d50110020705088a2000d03d0301c0d01e602c54542000e001030810b031405659400b805100260460003840c9000070359810450301201e4018a0807191070100480a542225000a1200d018600040c681036680d54506502a440d0792800b1024110050152a0882d031740c40d801405035201c460b0303802d281401c03c0740c50385840d4014001c0c0d4040306090132038421b04080c00f240c11225030000a21800c2c0411500ca00000801c5c0b000c00146032004a0301c40c003040740c0c9001e4041c40707508104080840c0e01e60748100d0f40300114144807450074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 875629568 1250 875628318 875628323
    0xc020d0309020a120f050d0e10051b06010b0a030609060b030c030901060504110a030b0d08042706030c21080405040e01110d06050a0b0703020607030e010f090309140307030f 76
    0x7442400d50000c507020702095041400840040303001c0c4c4043c07000c900d4000000c14800d2084601c0031803100d00482e51304031118200c0d5044500800e9402e4501d003d2000b40420710308003005c005080048440c85481c1c030400303034020102c6180020304240341581c940030b00b0020f42001c01d0244402ea1034581c100c00c90f44001005076542030310202c00f03da080350003908604020500180f007880a0881c0e00048101e07a0300c040f00e08000310385025a40b200c141000d0482e89005a040014581064030300110602c1e03a000d90040c02300345c81c3c03040c5400d611004407071048901450181c46140340103410280e06040303840020f03c035100c03482d0000720b060780002c480d0400c94040da8000e41d030200306030510700561409050415945000355a0206408150184c2075104100700c544c04ca03990107030280d544500c10124451b4885c042c0040e000f8100040300300d8002d4000c02c4441841000005001c0101320038a8110303030039a0411030005440e22010002403403000a1840034000840107402d00c1441d5943e5840e1142c0d840100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 875630818 1250 875629568 875629571
    0x40516020d0e1c050f060f0610080402100f091505040e060402030402030a060f061d06010206011d0a090321061505131a0c030301031a0705210c1324030c020d03 70
    0x2001042010300c1581a901c5d04c4000716059800c3c0300703203c210b21004c100d59240c0601c80c03421007150200d1040500d180241e401404e4400e40300c1c90b80714100e03281a86c0c070440d503003400600c401c0000d20481300c5804580703480a0b69502038480b0b0a0401c00c66002c240a80072070b10450061051002580d1301040d0382d00140d0b4403400014603064a030244201800056000100ba400c001c11149182000d044046100c0d0034260300751490b5030380700c0c0000028000340c02d090000f1b021002000030f112811750340c01089494004c2c140042014418403130017242c41ca0017401d1503e181d4944104021862040c410700180700c0c0b0905101e03080c00060540c10010181307038421481c000c9412000c4000c1d81c80700100322296181181c0603a036a941c2c4038103012508109041080c100c0075040000603c09034400c0c13041d180b071031041030f136084039455091601d070500c0540940074080b0b440b8204a880d28180c040c420b800010b04001c1d0740f824100c6601501840f034203100304100c1041c10300300300c18032140710390101c6c02484405a03801d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 875632068 1250 875630818 875630869
    0x60a0c05031807090624080705070f060609020d0b0a0f12060b1c12080c071205070203010b040c0201090201182d030210030b0f04060302010e01110c040516020d0e 71
    0x18032440c2c45003507488144000e183c500041550b5044100028140c2010480035800c00d8181b102185c03500f10880c0c003000002e0041c440c55001811100482d10a0380c0280c00204110b40c40b241c04c04100c8c2d010000404030240c0c0c82034189458200010400010988076140c1c1e901e051a00030381000c003145101008084a07615903001c5040c0d982c42c1d108030a001701d4100c0001c0140f90610f40a940c98070211010700109911000041c0142c081030b04803000c1c5980400049480c1d021030a09885640241c0f10803a450b5482e80e060003101d803611310410400440c0340c0d0021070382040c240009000c10072054402a140c201c1c050f020300003100103824205100000070003000c500404071114010b1300085400007941300000381d000d501079903415004000c0c400801c0741d2030a030f42c003107180400c400c58400c0e01c0001d02040195000040b80d60050100105084021060703801c0401c0900010301114000c86114184074a02103001030004e43c100040c6943e00c41c02d003422000d01d000b907030006060480c08024041061031034031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 875633318 1250 875632068 875632111
    0x106090923220b07030c18080a0227040501051b16121b1a150f091003021203180d0f020603041419021203091804170403030206040203060a0c0503 64
    0xb07054040c160085211100c1c0e04000d40028003520043c025400014200700e03074022941102d0304030760111007039a401006545070301d500384610494005070309017490b8084000044481c8120b48614441c911032070000900b03141644006440b2040f000c0c0382d00035036400703014881d11a0050113042e0040c03500050303c41480e6044801c11518501b03041d4108801918031800802041401c1d0309c0508036055403c54411603a4801ca80910004100040194070500d0985240c0441c10840700c41074200c2e000f0b081201d842c1e5129008645140c1c06981c034961103600010306070700890640e0364040a078030003c44082c200e0744c545031141c0880030320310840070f48145130001c00b04040044c08040c1c4c074142135201040d541070541e51000c9148041845c402640225130f0505203900c89500441128041800140b071007800e16284004209001c2004100b2030300305801100c00d103107420000000d0030081d44251b000b41040e250501c185400c0603c0903103282c0d002800e140c1d5075510185c000003900da0029050904000000592 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 875634568 1250 875633318 875633371
    0x904050705031e0114090d080703020f0f090a050103140406020a050d0509010e06090303091b0d0209090709060f0f0303050a17070c14060f2202090106090923 69
    0x250701142d03142c4118141c0602404903418100182c90314007000f007000c0313604405100c400000490302542a500003c15030740302c0901650010707400440c5d510700181844181d06d40e112207030f40120120310b0000380108202c2624608418650f010300003c0c80c091100302c00c00300c0340d44082c2d080504001c11554011031600500c9106000740c402d0300103092010701a03810480d4105008009003640d811250081c000042d544050000450340101d82c09002414120b40e20545030b001800c41031111544055151302100140c2c2d92100700500030f074600000762407001d241500007400c07100c1305d41c03140d04070802c80c4208100c05541c0c1c0480d60202c0b5014140f03142c1d6801c0142084554a11035107c50f8490201401072018135a4442000d4821a201d048000418103034620b180382c1d5010104c0b02c11001850000019000890f2400300e9042c82d0030360b0040c091101c860b90f0000e50303400401d0b040140081e1007401c0070044190f540c05600042000481d243c1703a20141e514280034440030040c01d420300d05443e00c0340c000c03061899 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 875635818 1250 875634568 875634583
    0x30a0b041a01030c15020c03060a0b030307050a300e010e040b0409111806211501080610090e07170a06020c030d0c02150103150f090501060504060b040f05090405 71
    0x1811140c490b982c407803134842c0ba00401401360760003103c11004a0b205007800041c1c4a040c04000030001c043c0d555030a0740c0607024041c40b0045507003500003448a1000102d04100e40c00c100c3c1d100f07500040e107054882009141030001a52601b030501a1080c0d000041508031030343e0580f0700802e1030001000d51800e40458007400391400550341140c5096211420301201d28114841d800003103680500d030704000c42000c8a041000d850869114145602c0d10704208550a04194140022002c1d0340030003825401000f6448805d901c840403a4202c0c0c0308000c1d09a52000104001c0d040c0c1110800408a410054650320f603514060701c1d224412491100c1c4a0f60010020002c28079400b050543d544c0d00555071550701c4c3d401c2600180811400c11b000c0f081124008070394495060034071080d900740c03a0b181d92548804c01c8600304940c1d14103a690600c8060b400c205000709910300c0d0085001003400e600e0314060208444496000c500d4044040c80144070305418140b404003100c8085501c214151070f1801c00c103060004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 875637068 1250 875635818 875635853
    0x4091515080402040b040905070e060117130b010b0721141305040612030c030503150409080702090a0c121a030d1110060b03040204020c070f082a030a0b04 68
    0x5003005030a8515030301c0a00184120b109903814401a1580c009020030386912410041450b00010824408119100c40a990064051412020720b44400c140741c000103000390762160715030650000040074001f14607606401841c40030340c181d01e0400241c5580303132540d0020841c00000001d81c420781512074801c031010310000070b2245529a84002009285048911070701c513036070245003030080c0090110041e040c1603580c96090346070043340d001c5954003180d0070781c030081c92101c00c80da140c03036246855100d40c422a51032901c60200e0551746c450a004014906070003c00000c2064240503140811940c4400d0f42c150001c403501000c03544001d00c01c1c0c0100141c609071310094041c4030311038101400d2036004480d9401141400709440803030114000100a40b0150301504014000c200041001070529600030850b0308001e01c20380780701607118003180c003c54540398011030f601c2d80a40d244045100c503001a14044d00d4101c2c03c0500d0021000d004652650160342e07016210540c800d002174184520603400030020030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 875638318 1250 875637068 875637089
    0x181109070e0310150f05010f08071e05030703050609041127090102070c21111f1214040c050121020304051606020c0a090b0111033c040915 61
    0x40740f508000040100702d403540000e5400c0e4000003840040c07440501c0543d801030b034070701c18900c1d00120140c841302c001510760030070000c0d020084205044052240b400c0898266500c07030fa04d051003903004040c5c80001d400180300341d0946003808005220035003984955401a2603181c0703089480d015034015040030740511222084014101700b071180d010b50003030106030304c074000c52a80e00e52510801e03034002c030f81d9081400304445e040744110f0104541c6820451003410040c1820f030014003645003034004042038220000810038642c1c020000f040b4034000c4051000c0c904125852503c0c254448405c110b106115840c18069024100d40728a03072440a0f80414004040040d550f80c1030500d042d40e41e414046800070300c0c0f8002490007281d100e101107103074115014024580c0c4421402c0121b50001800c080b50709a0510010450701c00e800039091000c1d20071000d00f03607019103298542003224400041901d44074601d8007060900c40c501e0844003000d07a01a181816000103010b8522003410507102940d8200c0d00084 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 875639568 1250 875638318 875638333
    0x10b27030a051e0f070311040f02070f241503120521040309060e0603040215160309030203060c040b0316020c0d061d030a14070611031603181109070e03 67
    0x1a51196442c040140c0c03c0102c0304080c010a80c03064546850b800010b1550030171301840300e82450580c00844a520700120010f02d4406550340300c1c90651003410040303500c2c3c0d40948083c801c00b0031341c0390b410517982c05900050101c0c80c240010792500510500001744103850500c41f201d4035900c0354064801400340b03071746003800d910300101141d001004125822000200e03000700c04901d081c0308045082030040003a10481c1541c990740d0820085042401402c01001d0041c002d459000307601d546a4480c0c24003e8480b12142411801410b007001c0004000c0328010400f04420440c500e581411294000002446c200c0c0803070011104038205201c0c0f101c0b0550103480985e90704203102d800d078800c44001c0015554804001d01002543c1d440b4085c03200f04801242c0081290100110094003d001c0144109000140308080341c4417901039410a130f8013450b201c41e98184a144d900c3e010301c11003d4081d010401e00225108640d0703050f00c9248260f2100d03001c0d01480c3c0104080ca805880790b500001c0e0018291006d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 875640818 1250 875639568 875639593
    0xb120a14010f030b0907060c0f061104060e0f03030a08010e1005040218040f05070516031107030302071e050f060729150f060307030b150703090e010b27030a05 70
    0x70100d550000344d82440280021a407842d50004408040380c095480700342e41c1d1401038950b56004030f1003c1050350032035220051600b5074194040100058845916a441005004024001c503070310146400c40c0a42c0c01000601e0000da049a0554112090203414072580d0752407020380030704054141c2c401504940080380c210445424040740290080c0159020800e003000c00071004191030055641501041013007114000800c000742e00100c889010741465603a03d0f64100c0650f107428803a40c010703001608090700600403800c2501080000c0c10300ca100210b0b5035400c000000b40041741c0c148140e0320400000a18004000e6140d500c2000038400b410b294049040440c0d03d80042d1030304989030100d480308000d1821881c5854140561982c070094001411a07803202d605070014004070080583c405c0c04d50f03a440454007100b40c01441c2191203590b42c8001146007448400413010180c12514041c2c0d010b000c448220501a07491080c0000707c504841300541c1c01d000400c0c10121075a001074030501966400c0843c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 875642068 1250 875640818 875640839
    0x4120308060409030c0210170c03040203070605030709090f06091a120d0c0f030207030209090d03060e060d0f02040b04020f0315010206100303080907170610050a0b120a1401 76
    0x540a034a554046a80705800c000841e106448020003180d18411000701504040301c0703444040440b07090640c1002c0d5101c00e40314200d04102d841e1211081d00004120440c00c0500044000f4200307424124214188100f01a09160190062066241d03440130459038500040d00408000c00003c081000712417031405954048804000320780303000c0c520040200000740c0002909805240342540d500850542a0b5942c92000e42041429411449405000710240c5da500c0d090b14080d1514100815500703059002c06415a6090b500940030441902d003002529145d2101540819a212184240c0710b0300c0c3c0d10009008104807800725410a2000c60b41c0c45580500a0055008031404180c0c5088034241900480ea40c0404580c47c58070241000c1d0100002809440381e6600029801e0940b2201e41c2c640003120140c0e407040254102d6540000c0c1031040c4e44102c42c100302c1c0504010b680040781c040c10030300040640d200e20207103d01c101c0c1000380003510040d12940f02c00d5086070702e004645040d50355a0740485 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 875643318 1250 875642068 875642099
    0x130e060406050a0605040b1b0114040b1018050a061701090308010b0a09031403160303020910080f07050d09021905151204020f03030912010e0d030515060c1204 70
    0x40c000c92908202003107510700300c480d440483e078295a5407860507041160340300d00754214804032080944e001c54901134410302030003201100c0b001c6952005280c54141442000c090000d03008014800c8540002d000c0c0d0107800022803284500d184000c40d06441308540f04009040c00d0344085019404401604403008040d00610042170207a076462610f40d1f03d03202c0209240c46114013110204072405010400100290003080c50380f00000260703418080c050101805614401c8811800030390300140c03040c000d01d404112566030102d00c3c903080c640c0303103001c80c00c8005600f40680980e081c4000030840c141c1481a0f40c0209400d0741e07028155410f42c0c4001c41c41d0300c61602e071a00542d03108403c500d1043d08400d0040f0103441c40c4005240404640b03071110b0b003e015218686c2c041c03103074050000308084003050300d50300c16074100c0b003901000001301031a100104a00701085d0060303245c2054141001e1150708402116040c042074002c0710025560b40340300b034070649800b00c112040302444501240004030401c0c001c03400c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 875644568 1250 875643318 875643331
    0xc030f0304050901030303091a010303031d0309010f051303020307090c090b0f2b020313030206060301020f0403111f0807030c26040816050106090e010b01170601020102130e 76
    0x9a050480182a0503100d00840c0101da400c02201d90040000c00c0c403c0c8c02a40c0c05500031440600900c06014025088070380980050740400c1d1244508815110010f2119041c52034030800b443c18100301e81d000070b0825007000400810014042602c00109011001c2c1030010f41c0d004040b9281d40e50b48003516400340100042d440e01103980300000040c2101401c0440b031615400c24901c81c58091004805800d441416508441d10580750740244010360241c801180078540f4000e50300d00290032850300130f1400760000c00d658001e03401801220100002d00040c1d8099a6110310610944414030012032226072015000c101030071600c509403050207030031192641c094501523405010046030540261340483d0a4a031044056040c0e042081a041c1503503122900b0030b00c5031200e180703003030100081a80d08000081e405d0301c6c0d995441c03030200001c001c01d00c910184801c0083c000e01c425000719001802144441c40d41070b402140c40313000910a07a04c01e60483c0d0300039075000303802191203440320412401500b040782d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 875645818 1250 875644568 875644573
    0x31f0b0703020c031506031f1401061706010f05071e0b16090509010e01060318080a022a03120c12180f09100b0c01272303090d020d12020c03 62
    0x10000c1d0344c5e181407000d01c2204090018201c0c0200300540d0301d0b20301140d281400003241c0d0741c0e090001303d030052a075407402812039645071a00030610035203090703941c2e4000c3c0209050105240800c501703684c01106480e072060700400101c0c3c047c828190b401e51a4801000005d2203003512004105411030310741c1c601c0c0c1e50240b8964401c0500d079101c07000d2010002003030141c0107026001000400c40c0d580711380c00502030200c500c0c070b01860352165552941782d1078101064910258000c0346001d00442c0f06103411040000c16410740600fa04515404641c5036858002c2402480c0000104406200020407030210200c0c1500142560742d21444000f4031601405c401140c4108e0507550762001ca45061806140205c3e02e1310304e81d803501458075000241a600a0304c10741d4882d52074541407107081806204c0005912054014289001031501c0c24400091800541080c07080d000c80495540580c000300343c4002180c02d69007008241c07401e000103601c060b507001c4000e245aa0801caa45400f503030109204503903010039001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 875647068 1250 875645818 875645833
    0x5010b04020d140a05060618120a051b09040c0e060105070b01090618020a09051c1a09072c1e07020c03061303020a1e0c080102041a0a05031f0b0703020c03 68
    0x4204c8240c070010740350580d0028040c0401049243c500d651a6540c020042c0003403449031119440601302000004191902d400505030349900c5416100d0801d095141101c856002c3d162681d42c03035144201078000c0c1001ca01c0f0745000111035034020001c480d900354100318000e05c950303035070f0301c1c2c440207042c4900505961603e5a102c03102921540e00a595a8007100d13200e03110f1040c1080c1c1031040150104050b820748909400480300811403030140a8581901100c1c1c0d0000c502d41105001e1611601d50b005011800003c406c001c2c43c21104148405041200069031400c0d8813010a11200e041d406456108501c004005000740700741c0005030207041e120b058042e07a0840d80d900342d0402070500c4948029025800c65509040042d088492500e5910002507958282042980390380301c0c0d580d5a078200045a130360028003400081000f10b0246140c4d550445420314140c2040c10050090002400c0071a4051007840801c0c001a82031102e600600208440e00740c44161a06009660b00c4071480c0c1031340203000c1c078803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 875648318 1250 875647068 875647081
    0x210302071e08120301050108041103100c050301080c1503070518120c0102010605060c03070b0408130f0e160905011d060d090201030f0c021906020c060124021b0d05010b04020d14 78
    0x106885c100c0c1c005840b00910b40d504da49440e080c14004d4403600360705004a0703602160385603180c483c018058a80340d4505803258101940b180c9407407000200c00348981d0003101034900030880803046035404841c915009032078401d010003602081c15a240c026a1081c0e0041c04d42c40b2186000800841106090b402405182c0e501d20038031840744612501c501041e0000c111000105041c940032030b030014480c0e80b0686c13400034110442c4042c40703400e130011204804120820448245c1244a9a0b080b4082c0da07098141640e5100014100511500c00d5905204503c0e540490302040c1d21001d10389900081d200307650f00c17902410703440d0081020050490121b0301d440c0c84091030101501c9225070b0324500360002c052544401c1c0c0c0c01d0307200b41c180b000105e4545408200b03120030501e040c00340724024400c802882030105600040d04080c8007801e0f03d00011507000b528032101c88000001c503000c0035001540c2084400c01c0a0510354017400341201280d812500004194010510380c5c1d01c02081c0061290402c0070945812 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 875649568 1250 875648318 875648353
    0x7080c1518100e0304090b061c050708220f050a0f051006080c090c1e070803011d070f140f03090d02070803121b0d0e0c0118210302071e08 61
    0x1e98201040da04c20301c024002c0f10000e602403001404c0c002c103a40d082201ca8811684042e4204400510017600c031400c3c00030940d000407201d41c1004107240c050f1410040d40b801480700480c0c110001d4400703003c0751707210001c2c403d00b404a2038200340c1040d01010034010742d0074805c0d0380344100354089403014a4684c002981c0400480e442080788001011030001e84c883e14a03d500540004440340d2042d0b4410301040c40c6017406038002c003043d603c1804615225850700101000118040c03444092100c1ca400c1040401680700503801a002070310f041280440d000f4410344400c5014038080581c07d400c0000074009189000600d0000c00c100640c201c5070030dc0c3c3c136000d41c1500c0340a119400c080c401e258001003003010021405090b520a4051906410714400e0a01101030750403010070840b164000e91300d48507840d68481e13445e81c0948000340e1f03420501c1740707000c1c0940501340e0010f15900c088091034085a00701442408030100074421034440a0058240080524220300c0d68891030a0500c80c1112046403110503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 875650818 1250 875649568 875649581
    0x15061e03030806010e1807031806050f0c070b06120115030606080d031506030207030203120f0403030e0c15070204140702070e1b0301031104060803040b0918090307080c151810 77
    0x1b03480c804050b5424042d405004201824103403d042e102c507010341890011051801115001e42c134041001d0030a104c0002042c41c01500c0f5a13401c00040210101185c05200400e41003441039030403005105c5505051b50050070700309450054507801100000500603c0d8000c0000d9034000b1082e6100070b1074000c4241c0450b20311042540288c1c075028000c016190081d4040c204480c00303401a649000d800030200940174078211081904d0340e04000c140700c10715500d031180c1c01c41405100c008107a42c600c0200014034504d0b904200f1600d08038001410011912660090b1803000503c1c080030081d0300341040b001c0d4480005028005003003a0301c000050002c00b025048081c00140885510b2450342503407600881049000300c5150407640311000002d411004200510007458400c1905880311840f100301319943c50901118002d40c0990000c1c04155540881281c004550142c7c0c8540c1e01c40d5000001030900c414400707444000c80d12101041000041104407a82030302c1c1942c15207986c5008842e140007150361 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 875652068 1250 875650818 875650847
    0x20a060608070e01120f021e063408030a0902010509030a0804080f0a020a0e06010203071b1406040e011707030c03050105070807030504030e06032206060f06081315061e0303080601 79
    0x30901644000d802d0981304030300100301000661440201440200d071003030303200c0803202e03110b2603264032110702e00780141112b4044003c5200c2003040c40d1178192501f458500010b4540301186941e041800c0840e0b006d00111103d4a4010b0251500c4035030f2418400c2658005125a0166015905040c40c01560115079404510381c0205040314060912031440200d2030f00030300d585e042d48010403401c0007041410340c24424014103a101c0c4280d140c00c2000341e4405140300c0b4003450182409100c00e00c40b5074034000382d090540f40d90920440155100f00e0b100e601d030072995400a4044d40c03a04401005018041d0417243c0706903529111035103240c840c0d00c400ca0071102c0465000d0005040b00020404600d03281000b95000304444800107480f00a000100100c650058401c0300c800f0742e86c0b10100104281c0f50803000080c8000e003000450f5141c0001c0e000e5004810240c0200650740d200600c2240784000c8e44070750b01424564550303134043d1103000e9000c1e074042c00a000550114003100c001650342e40c890803000c0e01248 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 875653318 1250 875652068 875652083
    0x21031515030705030a0207052517030d0522030e04150302090402090a0608070e090f06190903030207330606020c040e010e0a1505010602121603020a060608070e0112 72
    0xa03208001103c0f250005000d10001c643c0800154021030002c0050130020300d400c21042460b1525480f8810940007141c0c440040410356000000e02a2000310644007960803002021959540b04203001c41a80d4201c500c0103650719183d032809042c107a20130314031001d070042510204001c000701200088040e125100007540a4071110004005041c68080c1940001c40080d000c28900c2d15524610b0400440d9002001c8a11440d0200a2042070402520119141640150a05080c0a91102c140820b07010001d0b0395640c0300c1003184100351181c1c0c102c8040a403c2020310501c101c0343c1c0b0300410708420300d260611103d1184d0704030041c100041d01c200e41c2140d110345c00074620701c503032141404047c0c4050001c49013255a43c0b1035060040b0400d008a400e1140709022128025118803290001c070b4006070010401c5500c429140031224031401e00b15011040103d4038440b481a407442c0072441d218091030000c0c40d83d410b1200008658600041072800d940b440b00300742d5420382c0c03a881841007a0710342c10303c05040c12 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 875654568 1250 875653318 875653321
    0x5011d040f060810020703173c0705030601030b03070e151f0503090607080c0702011d03010903090810180b1009090f03030c0c031d032103151503 64
    0x61409038403401d0080000038020440680c2e407610541004c11692440500c0c917000603031541095400520404840441c80b0700c5242c1e0b08103005001d40401801c1e0400b0000910800c882c0c0b808001341d101d9440100210118981d2840c02e5840100300350429604507012030704201c042c80b814a4081740760010749546004141556491804004032400007101150f084405900d6084807020705145030070344001d1549425940c0d041100f040c0d460500f004150200300200c0344144990069291f04503080540c0928155004d14446029241c00310744061a0f20307459840d00d5203040c10103401403e0700040b1803446050321307a80350303c00d40340c2425288650140d480c070903a440c03110070025980d035049c0307900511142c0300c0c114483d445244820454030f1a0100759482002070080404044e030500949414020a01e000d0312100035665001c2c01800c00707654842e00c010420f420041070b544040000b101400d6066034422100c40c05004407484960041d1650080301046520314501810710f01b80d40c04007480c2246866145 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 875655818 1250 875654568 875654627
    0x3030e010c150b2106010e01080d080604110c0f0d09090c0210090c120305071101031103060f1c0f0c0801020a05071716110102070603051006031a0901030812010501 72
    0x409429020541c801a0320342400804c004a40403040071000d6440105000d505101d608007101c40141c1c0480202d9000c210810180e55201d003030282c00480941b004140d44092560b03000e82801031003005559403140c6049590b0340d080016001460504544651006645411240c0180c650b548032120140e0302141001803100740a910001c4c0060103031814180454913802c020b2860403031900c00b5000500041514401d101c0903d04001a4143c03d003000c001158040c00002182d0000803c4a07115042120100703a1a4176260b615030214044080410b0000003c1c0c900005140040941a18160880c10001c200e4400500c2221091040b07030311020b041c02c2e242d60360402c1074004040603841a110501009280e11020f0030300003d950310845200702c444101d1400280303032611a42c07090003014201070501266840801d5039009641c014a400304801c8108100603002c0b00a0481a54000a01a000109010804025201d800c0e00ba400c0844240d0340d03000112842452400e030740b01080040c0380c06255 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 875657068 1250 875655818 875655821
    0x1030e0313050108100e101d0411010c051006181a010207030f03030b031006080d0305060a05190b0a050306100507020603160c060e070801150b1e0c01020a020703030e010c15 76
    0x244840416100080c0f6900c420a1b20000030381940c01d01d01091890000340800b5506940ca4070034442411483c1026241c16182e452200198503100f6040c88552110300052040501035100c6000e4130704070a0010a940350404e101c0c080c0309000d880009071415244128904000245045401c4164014803071030f070864448010600910b0011004c0c5544c6918901c00c40d102404100105480c8000015541d840c00c104241400c2c0d541e41c80c0c5080614203030800c843c950364050f054003581c43c184c81000300041b20401d10020300308213400807041440b020403200c8490360301600840c42040c1c10b82ea880c1000c001c2450584d0140156030001b548403109100140310b080021099115465291500d80b02c580d0700d5072208021600b034089142803c2e0007000d81444410424040c83d2002d07100303240c1d0414040d2a02000c3e0b0084c1c05a00300c504140c01c807220884560542800a4440200c0b10a0086613100003500c0003a58401e041e21049001c80c40d84035946400358060102c1c50002e83c1c000240601d0460307074604880 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 875658318 1250 875657068 875657071
    0x1606030b030708010c0503180f0a030f09050604031103242a070506011e0b040e060301270201030b09040302150403020f0d09090b1903080702040605040f0b01030e0313050108 76
    0x141c162146030300000301c001007401003030035420041d154999682842503103c801580981c103010f40546c032001241440768000101e20154030380500d0a0050300d401c00004803034031001607000991100e00810080148a4810143c00785498100d08a502c40004030207401071074071000c4040c4080700031810001e990b000402c0b507082c1c41803082d4556202d048981d034180c010306402c200f80903680f035130021005229424500050310700d09003105056248862511980c4032844c490340c0187c03c0490308540115807280c509402401c600011042c09003044401c1418119240c100d0b903c00b03034006806c20109500324140600c000b4040c0b078050b800340401210304820394480e11030181040b402c6104102c05200d44840c240441c41c40d080300350f40c42d8803006c0c6c5003400303a0050303c3c61006094480ea90540c4182d230280c81d211035160031644d11026043c2c80302043d0001034024500b0781d20240d00103081c444001c1c40380d10141e000303a4445000741c90070041040803c003829600c0c00764040c1c03d51040c10341071040c4000d601403c05603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 875659568 1250 875658318 875658341
    0x40b0c2712011104230a14030c0f1c05010b0d0f030e0603040206040510020f06070207080f03040b0a080a020c010c05091011060117010902040c030c0807080f070825090f08160603 78
    0x5003c103801d07200450781e0261b107584400a0074240c5c0c6884c2ea61031500f032003241102101104c1024040701d070400002d5607407942c9601d0a02c002c00d034104060030040c0a401141641d080102081096039081c2440c01c10200800b008800040c0120442700303280c54400c090364003682d006814141003e00303242c240036061009030b054805501c51590f00d42041700e01000440c0c811112903010380711503841e01500d0b91812140b06400c6049030000e001c18402000c03140d05480001c1c500e4540042540c803000d081c0b9000348600c501c0003003039508090800380c00640107801040c03403400c16100401e02c607c446c0f500301c42d041c0c5940c80420090300300070b004004c000c44215800800b44104000010a0003171540080c0407503141034004004291151f988203d950740152116a010001d800c01107460329004d074481c0210280140441c00344500c490100d0316904915049c0b140204c41d2800d01804496070050252031303079010740b081c0714078045d00c0c4c20f001c40e1080011036440e184d102900300c400c00319402c0603015000b511098811 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 875660818 1250 875659568 875659619
    0xf0906080c0f1327060b0d0b19030606141e1002030f040909060501120b0f07050702030d020708121821070308030405060f0708040b0c2712011104 64
    0x100c40202c81c0782200c0720051000e03040c607030440300050001001c002c141e000c0620710036150440c100311044000048072000138688400042402602d03000580e801a1800c43c0c03401809c00706400b00c20401a0380c009402d960280083c1084200c000b000c000e6096002d1466024100802c83c1c00501800d15000004000d41d203401901c0c18190b815080040300d40140d401240b220762100c44207003e20000b40300700e130301400d01c145503203003400801d86032080320800c09001103628115150001c0e2002348240251a8035981c020159a0000c5003060029034030300141c020010a80500800c072196008408216072018403111441c440580300d0208002e01940c040568034038542484480309280c040030700c110000743d80705038417454880c206801d026113820b070700400404040005801b440703c0180c0080d8801e501c19804615645a030350703945100c400398065084080e03410342002c15280a144480004584414000c0d141500804000b03001c0500b0b071400803011202c040020441417104034103c01c40c1315286a801c814 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 875662068 1250 875660818 875660827
    0x41406010f031a0616060b0904230c100315050a0614092803062315040b0402160b091209010c05071505030114100f0e0d210f0906080c0f 60
    0x100341a070b03000422226005d083d0406a50070000d0300e118031054440d0640b020741141c80d00340c0d151100b5070050055251400c401c45a0703101e00752010400300410034400380c11088041d91904001d0050000c1a03601400e81803144000720b110300f052071015049074030303a6a0340c109080c4500c0a030b1240b5400440303240e4200c408110a2000c108152445c49030f0010805142070b209460f50030a00d044541c081803404d4207160300301d03090928502c020000c68004900403100310004600c80d000030014807501e250140c000340003040b910117400c1c0e0060b5013903103c0c2c05900000010350b20107000780c2e1030b00243e000d401d0811005100b0540e035035100b039040b203007620300c194211800c068445401d05c000340499200c0340e000400020040c0b15803692040c842c0320404080d40c03d806050404030000c0d101400c0302054008002031780340c001446564105021000c9030308000c1142020184681640d5400010308101021030040380141c0050f41c8074a40e80021036546030b440360203580b82c103d112034090b4004001e59401600034071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 875663318 1250 875662068 875662121
    0x30b06092b0813060903020a05100c061410060804120c0807080304081c020a02280618060e070807120f0b0708041115040b03060d0818041406010f03 65
    0x61088603580140b042c01c0c1c0f904120a100254480d09030480c40400c40058070800048c3c4981c40c0a600340c1e2001c68100d4802d20128400300c039542ca0340d01e009000a82070504440c0a00400600ca40c082c0d21321a50204100383c0780c030000d598600060b80c0042c88501d07203801408916100f825040451441620468070b00080c60321102c02d6500306480544005400142803455010040725128643d070a900055003040c0152802a443d920480805c8080d10b0a254441094075a86105000040e91100b0700300942012072000726050403030154100c1c1c03601c6ca80903002c1051000080d000080702c900c840109605403d14408087e00001d0040491f2205020503002e0b0000301d420700101c3c42503405982c2c0c040c0310b140c54200354040141d140d003014010404681c0c0317084c100040c001114280c45c07207003240399601d4980c00701159125000740400b030107404020035500300b520154010100c400074101c5060206284208551500080694429002c2141d01d00303c00b0311036000b40c01145c810400b40744143c10404488 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 875664568 1250 875663318 875663389
    0x1812030e101d01090513053309070905060a0f05120f0402011701061d03120a02030d051e0402040b0103061e090f111b010b1309060c030b0609 62
    0x30305100700030401c0820002038502d8011841d289500d001d18040070800d141c400071072400f0032242800010142c4440004041d07d8051104201c0122140c0c040c18a1058030382c0341c5086404407401caa4487c0c0d22407800720301604d2040f4022010341d28003c01d81880d2188082d402e40740052013030b102c40705201080c0301000740c59060b03143c018800c0010001040302e510309031000400c00b08000070a003580d03004910040c480240d00c101c44411070103070340302c0a0f8098182100060f1610070b4801c081000c04000091071802c1070350102c00b0302140503207211706100755180c0c581c2c042100c4000441100b20310105400107000f61a254000040e031aa06040014500c0c2e1165400c11440b42441030703451060308001010011030302d883c459080400c04072602080100c621103120101e81c407a42114080c80d8008400d000700c2c1413802e40c82802c203084024000400046405200001381101c1c410940e10a460109900160360083c0508241100024082403419100504003d03100040001100c0a510484d0071200001e814 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 875665818 1250 875664568 875664589
    0x10f170a06031202010e0706030e120318100c02060628061e08040f24020c061503030c10020c0109080d091b030c030b181c0305071812030e 61
    0x101038000c103105007142099400005400040701c1103a140c0521352100d6080400d8400a44d002840c003c01c046290710301d89031030301d1003980301c4201c40c00002043c03040c006407501446c0644182241a00c4c0d00306040c005070400c88000c01c0d0b400300540c01c20b00024019103424519400041c00480c014107088241c111422080c046c10b40107507001c0703030800340300802000301c4614400034000e181c5001e900760300d0695600044071910040061160030000451010010344103880550111015421515100440851513a69806031000c03400c0c415698060070302800d01104481c2c1a030b40d550000c01480103080c2c0c42c000250b21030030808025550350b5100000192070305000340240508603201140ea40805d0810001d03071840c0114800380700703144090030400942c2c00b5006000300e94121000b4091a520022440f07101c044040d00c0043c1c074041c1200000e04d400070049125038008660744c0030490390756605425204039100306040302c04880f81c4c00d020090080e0003c54010494424a40400701d44c1f01030001c07030b008005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 875667068 1250 875665818 875665831
    0x120f0d060902072a0819020d05030307020d09120816060f020f070b0c03060d2d120923040e030d0c05040305010506180402010309020f150c10060311010f17 68
    0x40260061400403003032080a680c2d200703407400c48044174a40ba04882c2e44145668041480315040d0420206564075079030a24003203500442569075914122000a4440401c0300d0004007080b200e890220f1020b80544545080541c05108645000c001d081035551510310340c00105c402d15200d0034000e40c1c0071058000307420307850304a02855440312030a2412842951005100008003402402002843d03585c2948607114180c001846642c1800c40b0021400c0c6151214030b610b0300d20b8580b600b610104280101e001c80c0d000c8090f5165054192201050723501d8191003101140c1a001c0484414218981544024240301001c0c040720f240c0310407015038109403803400017143c02080011030100180002809180c0e401042199003c00b03629000c040b4078507440d030181c4081d0406903149490f400319200c04001c41d4032070000801075000010244038521190b0704c04880300803503001d0341440900155080c00b4940036a07034003041a0070690303640001191625000003006040142103942c1d031b030203007112106260090b03d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 875668318 1250 875667068 875667083
    0x140715030b120d0c080a120507090518010f052205010803030702070815011404090b0a02031006090f0515040b030a06030c0b12010b0d0605030f010209040c02120f0d06090207 76
    0x40050307082122811040d020b80c9401c0d04125246445207078010034090f0102e03840f00e01651180100c401c03c5408510200002c8009490103040c000c0198000d46900101c0d0300440700105041c00001003000502c40030310550380c4240c000b42092240c0d1070250620102000000c0c0309840355084104801c00342c50b401e03802990290400001c0c01040381e41070001401411300b1000030f00e0508250140b40d140d002051180b0022624906200801507403290014405203401404030155400c180030001c000354020390300b113907102078464000194580100b280c0703001c550034660b800720702a00d00001d001002c2c15000e44822881410440030a00000e1007020314003811850300006222415440c0150144401d0741162528a900380f1540b902060400314040c152102280b9140e1201c0001e10071001501d090781003554503014070b00302502c40e444150b001d403c1240044609000caa08500743c2680c407030f1480c0202c10000301003004110102d40428008048038000e85800103a41c41d50390350b45004a0300413500c116140c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 875669568 1250 875668318 875668331
    0x621070e03030309030a0f030b04092f060403060213080706090303030609271110030e010605040b061602150f03100e06030c09150a030b0a06080a020d14071503 70
    0x196122510000008041c0d0007540b071402c0c0702e12071960b079006040824080209041c0001c1d4042d100703030403c2d1100c840142c000d021072041843c10000303401e88500d1480c0340500511480600020b0101400c803ea000602401c1c5440e00315240e00d0003941c0b0441e011002c0285000001882d606d0421101c00100f00690700c1044860540c41c00800307860241d80416111030614080f26282c4070000103100c25080d07090032401c02c0f44401c5ca030804155444804064bc402c0f0100241c0c07120035055005451212954002041703807503121000c01040f120701404042e00010180440c2104000401048503011b0005040c6400c41c0310104104000740d10881c461541424007000b8081c0c6803800319280c5001d04110892001903213003000110b41c3d0355081943c01c4d8401c040301c20200c2d400650740d5018048142001e481015100c1d01e0341080e0300c0b00306084d10361103000c078540b050004c0c83d50000718180c079081da4000e06c82c0c1c44420301c0381c8607206109030800c0441c41c1401074802c0040c1e4040460524500e80400c3d86022609 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 875670818 1250 875669568 875669581
    0xb0108100524011b05190c0b07030819060302130b01020f01060803031f0e090706231b010f05090601060f08010e1602120a0302030411010e0f0f0621 65
    0x150398026011a006510b0b030500503a1070311109105110030142880c10015602503558020b10b000b007100f202034a1030003444500880c5004000e884400c03180284060f81c90f0960b16071803c4254840ca12001d000140c103800031441c007106040070b080241c00d14100104041c1d840740c0009194444d4081d40f11031340d990325541240d003940c040c04000c504100d074500801c81c140c40c2103101d5884c2e11000f0300d00c130842140240c140004802c8492050003034182e8420715805481c0621350309644078010f0088201140000c0344028054100c41007440c02c1c0c00186940d24140104000b04c0303110f80f00440c800d20102e5483c1d4034000e040408a00c101c80c400c20010000742941d502d0514050002d00030302031207104000c002c8006002e05031200b009603030070a00201803020408400c3c1400c0b0306060361031828440f111000210400c44a030305402450295000b5160b02e24072804400c01507442c820300c010004d8014103a83c02060444c0f410944800c1d510303d0240c0400d180500c00440140184420b41081c00580e1207c4180300b030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 875672068 1250 875670818 875670821
    0x3020a0c0b040302090109150603020d1d0705240403020409080d090f14070b0708030912130305070909110108062106040b06191205030d0204060503150126040c030b010810 75
    0x525031441c0801c006454448c84100d210a070380124001d241d00001d1170100101c05601015040f4001c055843c10300741403c0000303444080740d00c038640c855501640e039640c0254034603940005114200580902d064a140d0034040640b45840c0c0c02d503000718007440421800724a038059003911074820703001c80350641440d2400452000710b4401010b240d030f01c0007105000d81a00d02c811180c80c03542200c601e6032659100254680f60003403d60281c00380e60800304480124180c2d030207a0320282d034411025114900d40f01c10302e0004451814001030488100840620b05550154080941095002c0c003290310405841010906221280e40d14000c0c990114040100f40a44080c100e03800403003c80b0441c00880e01240000c6001255000c0e4814114a400c8803c0801c44100112851600031072004d6403250b9803000007502e80d420441300c6030b14441c14400401d900e0342c4242c00c8648034107003007a01c102041641c880e00101c17204004000310342c0f0412180b000b001003a06040441c1c001e04a000081c070748a003181c4035100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 875673318 1250 875672068 875672071
    0xd050112030215090d030b12030a020d090608190504051e0706030605150f0f160c031101080709180207050717070905090a030305072105090705010c050d080403020a0c0b04030209 78
    0xc59107200424800c4504000c10340b00d170003001c03524000c911841d818001419011500408103942e20001810b0703404950086018550b102e1161644240702d40d41c0c140684284804656031145c001c0e8004035040f110301250b00c4179030030038010000c4604440c5569102c980c50f00d52110084c400f54000b8408104450741070144001900045d100d80120320700c4070060014900071103940e459a0f01010884a6000c105541915052a0401245440a03070070382005486204035010a440f0013110f0b81c6180000e5008007030003406542d05e0754490507458500300303511000103034204900074071940800040e004078104018803005050400460f0b81c0c25000140b8007031800e84541e2000403a10f04003000c000c0100c80201d112a00e454243c20040b90580d03600d501142e5a8946d10700c03042c500519440c44820062190307204500c12001c81c021180e06036140e50042d80e00300c20420004006034031170400c01c00300c00e100b007c017160041d1003030045806044441d503030040744aa003074001c4240000301023000c0041d40341068015 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 875674568 1250 875673318 875673343
    0xc0312031b040b0409021e040b040e07110a020108070c050709020c06060a06020a02040221040606060e2b1e03021513030210200c0705090a05160f050d0501120302 71
    0x1c0c1d103040d24210315404103001d20301c2100042c540c0032980c0d82584a801d0000400c519640145030b079241e072100d0003041203400a00900085000900000d08101e000d0f41d51300000c558213000a1040700f600b075004441d4400020401c104200d94603c0b080b0004004101010242850b01805070f294541e03c3d80261a003035005002c2d520607801d0b030104022454000c9209000180c0540d03000d82e5582401300c18172036803c4104600c810701412442040248403450740100299041650350705c010007100c6040010f43c0a842011501d0003a000d00080321304040a0f080b00c030f16512402c005200004074844107410a01031903415800b603008008a50096941004180e82c02024810000c14120854800a40ea0001c440040c11000d69402600d065910284903030b11a420000c20041c0c1c8c4e6003a00e4600c203072120b81c00e1040070f00440d61140846e0701020b19000743d42c0b00b105040c2c0585140480101e003140d0078a0104c0042007409010881e1071011000743c01024042c2c03d10142d0168260048c1c90004d142c0038044419 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 875675818 1250 875674568 875674621
    0xb010e0901060305070e0907020f010f0507390804030507050607150203100305100b03010506040b150d021215011107080c060903031207090f09050105010f030507020c031203 76
    0x2510340e9220000c0d4191201464005155600c096081e01c2031803551000b90f03401100c641c10001d900b90300040503000907400c0d00090045c0c0d040c164511041e500142da401000c10102460910001c44003001d400d100215030b01c0e40c6000106040c20301070f0130030025005962440e400941030044c000d041027000000c1c20705623001841c2c00e0240d104d0039541340001d188000020340020114076031400081c2035801868000c42a20b50000708a8180b40082c4044a82640603508100006100749000c0c810010094009401b0592000f402807075841140e004254144015909012004402401d050520703c55070002425400d9003038110005800b10b00e40800202603030384104420300a05801181c0305112840a440060301c0b504807400013810340c0521741030949484126000c03c101c95601c4442c80003241d0b5007110103111607441d46c0c0c00c0d02c141d078400d00645020403494405132401c0340c400c1e80603603445204d610544040300700e640c00090600d4071007014150288008003c1c00914102c500307540300491810f410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 875677068 1250 875675818 875675837
    0x2402060910020a110f010204090c090f061b170702040e010510050415030212030a091e120309080a0b070201050603031608070c0f09050a1d19080d020a120b01 69
    0x5129600c0240d6014040490303000304400a0b814000c40d811300100b803081003662914801489098000e400520802c91054180038408600900402088040c1e80500b002c60b4405030034010155115010b03980e04540d41c4100e80e450201255444038060004a03488071002e550303100c075004000907651204c0b03080b442030b49090188441ca05504020100301d940544010441001e40c0d100e0281d4078a95600194200041c2c0032100038404002c00107084030b0a05440c0c1005c02902c6460103a103051019074041c00383c104040080c0400c85d40225145801407203480c004180503120300a40d818903c0e420800c803030020782e00c0280090582c0a0007031030751000060f030085041450507201034820700e070800c038080c5c40e503007000400c4000d0100042910380a002050181103109640d90300040040c0401ca80e00d00d00c4d1441d0240705c0a2414688003c4d0b110546503000501008038012010600100c00b4201254800310030060441d1600303050001d003c020466840740c03c818683c04001100f0f40d45242032280c1007214210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 875678318 1250 875677068 875677081
    0x30703061503110315060f0d150e07140c010603020402120601020d08090a2301061d0a050c0d0507111c030b03030717030403020a0c1814251404240206 66
    0xf082e130358000c070401115200440d40c200454110720411000b4a181740c0002540d480c181015042001140019440c07100141e40d103c1c5000d08071507041c2c4041000a80580da000c110b00804005072030001001c8000081c207554a600150803a401100d180c3c410440c2d80080048540c2c05104240410310103003800c3c40946032041499464a020400c010002c100d4116161003041c0500d100c4e041c840c2d88000200802501e07140c8110404011248128001c510390001407201c1a040c000d003805514007112550512460b210004050900101000201b000500385130b09190000c000c1180300d40681c0043c85c0003811095001800d456400d481c143c083c0d0b20401c0300b074000402103040000d40d480c40c1081c0307907200e45691504a003000d45004000d8030540344003801164000900c41c284a00400c03a9000700700c1440000c9120b180b0001c2205c07a4100300c02e02c0300c404240a204a140180d911030146014004013586547c0d20308182c1040d0003601c2000049060300314040f082e01c0000324210f0640c00201102d21300350b13 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 875679568 1250 875678318 875678351
    0x11090117250501030c021014010302030f03121803070f060209030111070b0c2512080f090714061e250f02010e0d060e01050703150b030a02030c040b030703061503 71
    0xb4461141059034071180070201510902000ea07080d12400c4041c40072000b200f00d05211000f0a001c00c0e4868040e040b416500e0305000422070301c2010381240b8410099a410142c0d40b03101c03040110090890004005040000341031095940f8600d1180000603112103420040c5030848404290346030b0014810040724021400c219103841d07100c0c03041047c1d0780c0c3e00c40700024020702031001442c07410310b001d00e640384180401061a07044110b080040e5115100d41d03694100e501c041100036200008140c000e1401400540d40c4480610300c1c046001e4481450030000c180c0b000003032400c500c1c0001940c600802c0358100f0031041d10780c00201c0c1442c0017001d00c19100c55111800041416100241070010310303a070600003034403003030b81c0d9500c81030300040c040100184181c0c0c010b0103010108e900300002440d0411907110a403c00c0d600006030ba120784100c80c155030760140520000d42c0050071545580000340000107281d00444000c620440b690703640841c3c11450070070f540300c1c10145440000141800e0841d617140442d400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 875680818 1250 875679568 875679643
    0x302071a071b08151603090f02040c031d011a01030507080106230703050d05060303270310061701050f220c1503060e2202060711090117 60
    0x81c00050305011206070b5103040c0300d0341d401488103008400c40d9070101480b1400c801d118640d003070210701c010b4000d24070403402c031244d811004082c10700b00a038620150038640c1c4a01c0346a0198200002c0c54030040a40201d80000301c014802907a45074841052038241c00300414144013401e0074144810b0808500107070040005018101c00c101c9002e86030724a0a514050001e20341d0f684c0c0010b1551410107040040440c0e102c0040e21400f01d0410010918074240002140c1c4902614840c450a01541007010b120021043c01441d0f03140c80341c03981c0341c01300d524948181c0000381014204024008010048035094031001003100c12420312001c00c02428181104940340801000d168180c4612480d01d02404026100c0e00700c0c107804510b07030352001c500a4059100506079040c01e04e1030f14580d9100010340c121050790005204c4902e0511404c000141041c41c00380204a01c0f561072041091841004100940001d91060100c1e541210741004501400d00c0b00c18014040e01070024403030105104902e008000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 875682068 1250 875680818 875680823
    0xc110a030f11030f0a031a10090b07080f161b050d11041e0606022a09100b1210063b040504060e2a0405040c05120a0302071a07 56
    0x2c4441c1c1501c1140070900445141d40d50810129840d2004074000030024800d08400c1d031405070407a40c0d00314003460700c4800000b040d41d559817020069814100791034400d40080c0402c4510480c18050108259402c50217845a01001c2040101502060800f101c00c01c0300781c9001d00d03c05141e1842803241c0d4485c030000d5075240f90400c8810a4101c2c1241c085402020391686001900b040c0a151508244403600700900f02d510036400c1302d0703c2909115000501d04030303956022980002400c60b401e01400c00c04003103039000c3d04003019a180c007541c9040c0c02249030300c4030024001e10300483e070401030008074081c099000b4089900d002c034100000b40000540d003d03c8280741070680c00c01c07210988220010140400300c4a60b00bd002440302d0b082510f03109000e07043c085030a2016000d030f110144805040c0d090080480d90809488a4070301c1500f105120080030040c206582d5850001c0c8049440e07283d403800c0101c3c40880c0802010381000b1810003d0601c003254100b1a0510070400e0142c514a20000c1641e400e40d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 875683318 1250 875682068 875682077
    0x8010b0c06070f050d0c03150506041d04050f0303010e22021c020f04060b09030f0c0603040f060b0a031b0503371202030711060328090c090c110a030f 66
    0x5905084d100b41c05103140c42008a0f00f4424184036495060300800300c0806480050f485d8241ca900030442c40c1e0046008210b080c00c00032080c20103800403052402d81040c017031810ba50b50440c000503020709641c002d0b00300516550703602050050b080485843d01551a40c036944010a200c42036000856100341210055084030711a12210159981d4000308140200d00074010803d41d43e0341c00d210400343c1c00c1003400612074060007030240401d0310003040e0b04111000080402c4d2850b0b44650f1030000c901140c10b001c2d03031030b9a5107503405040c68a03850b007458091400f58003150031030b038078202440c440180149c014500903044424a01c060402d80d0008508602d40601c10769007100048110601c160f10482c80503140c100010044140d00e81c000c402019402e018001c480c4241e81d010b802c1c4a001e01c01078840e0580d200f10780149014080e031150144501121250012507402815280c514880036950400d44195681310f083c0829a0b0b00000c840740d60f148420080c05900c0f02d9500d014100c0312503a0106400e01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 875684568 1250 875683318 875683337
    0xc060510031b060e013f150501030b1e09040638040b0a0b1e0d05071d030c10120f0b032404080f0403080c0109020a0e100618030203070e0708010b0c0607 67
    0x141c2040500e0300d00303c401e21b004101c0052403020405c403d4446200d02400302c3c1c980070031f0f003000d0300300240882007140c9582643c51340d03040c11805010003840700400507142540e032104145c000f40c04c040d00f05c20040c1c1c40b406841003152103000c2000300040118400512275841d15900c4084c40e107403188518100c0d154025000e841d001840f100c906c84099000b120024501d0005100104102c1e5510a0b8000c1c1e036940e49115007503400c3c404110000d031055011329807640c0000d2480000c2e20b8103012104468400d442c5c845041244500b003030342550015040400920386070115024a41003c000c1c008902d52407480c8040008044407940c2900e002c00f0700003505503a00014800d541042510440303008550041c11703d503031108406211030003000c000034101d110301c0340c02c940010002840c2c01c1d900e0003007420040d400c1c85c0300d01e0040291400c00c2810742d0314000713161100000000d60350a1092000900c041e0400e0341803882c18030402008180140c1100c0e100240500601001510001da00c81e8040411304107440d40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 875685818 1250 875684568 875684657
    0x3200615060403140303041b1419030b0906240109090902030f0703080d0513020f01080411100909200f090f06030405030c0d0503070c060510031b060e01 67
    0x1c500c241d410152201d24502d00c0c1c440d09240c000011840307030340145251404448007078070b44020f507046d074450340302000e0125084100d14030f844442d10b07100442c0d40c24090b10107542c0765610480c0e0300084900100b10b800120400440d062000018102240e21403c8414203001010000e000c04ca018040d01424641d00e19041007151405c00910101e805200103c4004568900d8420001d621002c6101c2e405800c02d80801c00d071452525001495540c010002e98180c01105c0045a5600004109964000c800340e40322400b43c0325240310a0b800d8400b90b03501440b50782442041020f480030181c00c0142e0384080550b8107071240f41e15041c0d071f030003011900c0c101c3c0d5100e1000000602c0e100c5841009944044000107100c20040008020068601c0810980340031041c43d01003900c0c00c0c00100c3d4a4000b10300ca44040400040640d84410b0303000c506007180c011210384907200e46080800320718198144100d4030800f4852560000300c012030541007481c01c060380390030390550014a140d88032680c2c0805074404080012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 875687068 1250 875685818 875685829
    0x2030307140604110103090803010e04110405070e030c1c1410020f0a030c0e0a0b0c030714010207023d050d1b030b01230c1906060303200615 62
    0x5035140c0081e4811194418540116120a01500c045841103400c21400a441d4000d02030040c03803a8011b40380600356031074a4a144901d60006104032000001c10b5803010840d43c40b4420b0901800b5107644000306100c107402810300d000d22200340b091003501d0407000300b00394124100610401c0c5070701030303035600c02c1040380301c411491302560110240e5403a001080078540440204003074002c0815586d803d000c103095480d0b007915044203c0c4c0105070880c261400600025100d100242941c1c001c41040f2481e1541541710000c800014281402d11b0342d40004044095140c00f90072a1050814464082c09241c10024600e64208011510800050b0000330040169004034280d4122000742c04050110001c80c3c03010b180355102d48030b0100d0211349800f071040e100e54843d2084900c903000020b07822401080c5050491003d421210360354000340b20310807004c2030200c2d01c000740305aa40c1c4641c00110b0620f0075480c01078005035880b070300c5403615401904802403050700010303640e8001c035039580318011034041940881e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 875688318 1250 875687068 875687077
    0x6090c0e01140a14032d190c230d061812030e0d1b0606050a080d0914130c050f0f09030f0f120a18030807060e01180f020303 55
    0x4540c5809400000340500c40007644059808103d070389000060310744822190041c00d001ca0700e501540071048075412812044101d15203130081005801e000d0803541d106a2a00401700300100b0301984c5003214008020105014102520002041d119000d1a65400503100349010500320301c54004611420180a0140d2000241c491a8110300d502c0d4181070030040c405182d1000d0404c0002d25245007100030000c089032816040c0015603440c4030302c8114050b0b0b58241503d00e0000d59210b03603500e01c002030359a9264410760040005602070f120710120824090607400795a4403201c1c070340c218541c111589903207291010101d6505d20400003819404920100d031b46000d0910b044011050000c0d0030070100f801000a007042c160201c049542003e41b0329501030300d4800b5034450300155849541500041d014a0000c0d002c6021a881d041c604180010740c0d044410642c3c0d4002d880ca10000901c0105004440c02010390180030600288110201c0d0394080341160100f1102a2001c041c40310014119541070080380c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 875689568 1250 875688318 875688329
    0x1020c0d050a021005130b160f0e100305150406241419020715051b0c01080c2803020c06130209011517070807090f0608130212010905030901030b03010207020a0306090c 74
    0x1147c10740340c2419032298021100004801042542d0304144040e80f05440701ca082c100b001c0c0c03019070a4040007000394058003001d001105c3c59007038100c01c00c103640c032030b4440d500051200c2100040d16040703c0c150900e100c08118104001c02c401c0c10110302ca40b040380d000f11009000d1110484d142e081958804906003c00c45d040007480c81683c00c0c84850b0b41c1c0d8072a014200551001f081c0d291200c0e400000b0036504c0c200002c80030b01013001100003500150300c11018000407220f102003102c4d039441012030780340c0848200340d9020100c0c0e8080741101101000300121507100025811800d107580080e0005420400140b152404003000751200c8007a4031301c00c00045c511322402c60080d902178140504080c00600c070464010002480d130f00000034402d840c41d0030440850709a910741c008552a480e42d0281c40c0501c890083e81c004601c41e900c1540040f00348103846030742d0b01031805152510440300006083e100c050066910030380c01030103503801517a079009188040b245c1c000340c002404442c42c98030346400c0034070381d021 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 875690818 1250 875689568 875689583
    0x7020f03180f040f0204052b061805030c16080105040f02041a0d060225110d0309081506030d0f1d15030405010b011e0818030c030c01020c0d050a02100513 68
    0x4e14440d0911038000e0402c1e10000c0314185610342d854101c17244035503c140d0501c0304030451074406402080940d4001c481e5440842c01011424031951291899640b001c00115802c0c4c2c040701c00a81d141c00004050005030030308100031700c5181400c0d1200c2d001c1424004010344035682c0d420741c111558180c48034640c0e01c0040900a100c041e03525007881d4000303400207943c8200301d031861150a01c09820100740541c8030350313020800c50324a4642400b44040d8040800c030407028080b00e950040b5445408000c001e00ca6480c0d4422815185818002d05090103410606101404000c404d0349281781e03005603690402124050391007186001e0100015000014483c012860748000010b1106201d0b06400c010300f05e480a80307465500c44405000b10f01007a19900464000072085404904074030f40244400f0012007040040700d00744000c0e84401c0b400c5d03922184d10140c0e035a50000e12500291018816550355007102d0030701c0e03418070616203000703500d034010440e000460641e244d0000d2a112850104900d5103500b0044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 875692068 1250 875690818 875690831
    0x9070e1f1b031706030102030601050d23040605180c03100f020918040506071d010e0103090501150321091505040e0c03070810031509030e040903090e07020f03180f04 73
    0x4000d803da5141c091180c841e80550400960541030500071a40106010f03560b652411684443c15801040407594592030130910850b80c821041c2100212406a4010000000c0b2410048000007420500f0308074026030f03420401e00001941d40110740491303001c00740980819412041ca6800c0020310454001ca58003525a001510000a968042c10b119901c941d0032140d05456114054580740c121217001004500201e050790300740e5228a860540e0940103040201303803011540d45890070345000482e0419000e41c0c0e081d040061002200d00d034034405081d50500040c0034124034001300320454034042c1072510072840c59041002880340040301c00808520700f00714090f090500e8400c03101c0e8410380305800007640b12000304a0010341407401d001200c1d07100c40f0701003045052000c00000380c20b6241058007409542c04441c5c441d41c9a6000c2e4a886d10321a5a1b004078990800d241508200c0300034020b4000c56000001c0892006800000c48906954802c540c40100243c400003481000d07400c0d5095401c01d041c0390 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 875693318 1250 875692068 875692073
    0x130c0806120c03120307230901030e100f0c1715011b1505060a050616260315031509120d0f0f060810090309140a1d0609070e1f1b 57
    0x1401745000340704a0b40c80902e0300060760800391024110a2240d0958101004550f007550f00980c80801509001001e8900902a401070f000c202c4407030f1849402902e84074051075190b1070b4095450714010302c2881c44030381d09040c9103417030b654151100c0b103d80e81440ba022020080d0401c911141080c160351280700002c14140803840c08001d4541561513a004030400640031803075240860689100d48882640f0700c0303554001d80c83c1d0f03503d01207100800c007011008040ea040151030091f0010342c841c00c00e80212002c1c0d00e55400600d4a88004855554011507900051144050001c5803d01002400008280c2c40311094502500100748007030407100041e00c1c04001243c41d00081c4c001c80c080707038161403e440301940180030b0305065440d0040000e00089001c0c030103100400200c010902da411000c0d00302c0d80c003151a5040c02c2c48141e0317211030006051185008000791442c051505a07400750813882c000d0002400040801d101c081c20103005a401c0320035000031100c051103034400380c13034070180c0c031020b294000c1c1c450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 875694568 1250 875693318 875693353
    0x50d11061306030b0a050607170405100201141819080f030f07110616260721020421020f0901170610080a03051c0207060506130c0806120c03 62
    0x501c02d68012904200c2643c1e8280341c1480c2010440b44050142c0d480c2aa49035215540c40c0c031400103809c0c07040390030320020900343c403071100d4401070640d55000064800f54080301402c40319402082004004002034440c6c3c10b55901003640540814101c041450480c01032800340c82c0c40c010000d126481c42c901108200e18540030a01d024011202901c901c060341840420700c42e00c525080760402003504014515200c0d8510804861290552401003480c020a07400c903180f00e01c0009490410004125100d002002010491030f041c01e02d011541c1145411300e0091462005500002d40762118004502c40c90f0030340d102e4403040c0412200050101c0316568403030406481100c0200b00c024041e204800004500e400c0000c0c000050391800402803160240941d0121032039072050700b590744881981c444048a40e076150010340345180c8504008502c91600f0410712111140390080b810801c1d081080e42c0542d55040b0140d19000310b07045d160024240600c45c90546000c00e40c0c01102d030541f00300e0b0550504400341 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 875695818 1250 875694568 875694607
    0x926090d082808011e050405010e180c03060f06040209090103050f0d0306081e07090c02030d0c0201021204062c010212011a040504021b0f16050406030b01050d1106 72
    0x4091403003a0344640d42c910002c050400d400d00011402c01001440158029000701c014480c115103070407002074a40000c1002d40f0000e0b80304a03024003410081c00b011102088080391170400300002440041c100d040001d03920b42026003600d121140ca0004a0320640f034980469160b040c0c0a03009194650f528030302143d03105c00405101711180144806101030350310a0142d4404c9605100080c05d486007801c40052800000c3d510244051040c480e00103107035145402070074150f111580142d92148101946602906c10324201ca40441e40b04021240c06035151603440b680107a00054006080d00480c2d440005a04414072140b040c110051600080e1003015001044416040d801e00180741e40c2e1000062a2152030340b00c0e1036001c690501c0103120a0500c3d9024100440304080c2489000c5d18507007005d8140118844011403581000c002001d00091200e15400180303010b03138080129510b55211840504018019a031294002010b54000e001010900305800417009169640e96455640200b070034540307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 875697068 1250 875695818 875695837
    0x7050708010609020f04090507110f0a0203062d04050f151e0402130e0703020a030323040513180501230106030618020714030417010f0926090d08 64
    0x80c142d011825040d140241c401244c4400f01c0d03d401c140c102008034001d018020700504c03c1044130341f465035107040c0402000c2020040803001c0e10100d5407074010b02d418030f5401021303081380324075603107241d108009546601b03d4558442500141c20352035510308a82480c808802c444400d20503410704038044240c2c414124003030466021305080c102d580e01045e241040e0111000396105090b280503050380040342e042050290140c00c247c0b1003003901c9074005024404580c00690002e2510b01920640e0003000c810b03406010ba4010703031241010314010001d0b11150111140515a82d00c501102140c158000c9400e070351154010000d00c1448034100004903058401440c2d403800c03c0304a800082c11030300a200c0d030f800361140c040d41c0c0480291560350380c4003c2d61091008441d050f103502c0c0c841012540900103000501713400c81420f481e50401c00c01003400e540000440503805131402250f1000240c003400140c0d10480055030a07942101c4940c07294581e03006c0c0e80100754110552104074010051224000c0c402c40d00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 875698318 1250 875697068 875697071
    0xf0507080d20010902030304060807142106010c0b072105070e190b0f0306060903060420010305100510020708070609030201030f18020f0f150c01180b010306020f07080705070801 78
    0x501090b0003a0a9031a15034010750541c00c100300a00181d4410010a54003040e541440608181400029980ca90103030b001c9404100c0c213400c0442100c0c0840304042d410040920301040b81e031502d03031140080c0700d201504640500c000c0c00c5c4a020406404400e0f010301e100c0901c0308000500c2c00b468060f2104080d0244540701ea40e088452061140d450700241c0d0655140301200b500f0945030044c488030035480500404d600140a020740d014a5404010b00343c8a1446400340c0092010452220f02040750b010111034145801c040c1000013107a600710800e01110b40031581c59551500884040c1d01300a0650030001031409030b1080800d45681100e101d0303049902c02ea8081001c468007044400440e035210700d144006d0001010f00d00c0140c9081e0f60880045031008241c2c0c1c2a0300201000507a00803882c0e021a0101c0c00c001c90f24840f044001e00c501e8400c500c645040c5030000c159680d4503425075005020007402141d007c504d61003910700300401e403007820740e0002c0c0180c1c1d1119941882c555a4800d481520303001c1d07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 875699568 1250 875698318 875698367
    0xc130b0a091b17060114123102010203120402010306080607020f1002030f060f06221514030c0309013902030c0a030e0402070602160b090102160f0507080d 68
    0x1548210800c02e080a0f040d03000b8686a200c41004454031511741c0642800400140455040c1a10341d074400d034040c0306411030602d0792024251011260154520301088003240011b007860150740c010040304c200e14508803000105588500c0140c000782040d401c1580c03a0701c02c2800b040b100c9500054032200c20015001181c602074030004c640000d83c801152146100c00b11200850120b08102c0e0f1600030b0303401d00520060502c40003882c07001e4a5605241400304070385042d6070800c4041c20f03400344421300d200c0078a45210720500045045086100241000080c5100040003445820080d80300e03000d4800ca4116804407040e098a41c0400c660558880c45c28071100080a843d18a00000440f01607001c003501620044ca29520f051b6030480180d0b01183e00940c082181c000000c00d10701c0240300c0c0c03c109415100b42050ba0342051005000010120203440c1c2c4108901c0003007c09608200f001c07a0b40c04411415402000d1500508040c5160300103034282c0300340c5600701120742d00701c002519403658056218040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 875700818 1250 875699568 875699621
    0x20d0815011e110607050d1107030c0f06110a080708090f0d032f07200616021815041802060f090a1203020a020a05120c130b0a09 57
    0x42500385203049010551950202c8070300c402c600c441540300142e500741040c1d02400841003a0038090125094400120001400c40c1e0041d16485140f1701311090044c82400d00f0030307a40e0080d1103041d040f00c018100d0703010801050204081600800c01440728001c0d541d458015103c0003070f1030704074280e41c00c401241030040010000f110000d06d1b0081c0003105001040003500d80101607008111101000054113005a00e8160404071800c10044410340c2419130350703940013641482225101042600440b00e05c0128000c0704980d59082601e00c0d500c17160740c0c0b040754a0701510006078480c607180701d0034640300442c10410800410340060840e011400740d50034084c03074101544c105158560700c94000c1d407014041c010780d10002c500c00c000e0180c0c004050040e004186d00c61000540e2804016403c800603440801c80208504100d40000014502038428110062140001548503d41c84020798003c0c40d03e0708100c0c01d1200140c0000c00c20f500040c01c1e07000e200d40c46004c1000507083d600c004510580c00360301055803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 875702068 1250 875700818 875700841
    0xa300f05060904021e0d020406080a0303050106020d0c02010e0406081e071202060f13171f02030112060903140d090606080a022409090106030f11090303070204020310090507020d08 79
    0x22503a8005c100e42c0024a4198080388810b03c424000303074000a03c14045001030301c562180702c01410504005082c0441c4928008041d01c46c140c02170350441d0040d01d5584041504100641d0b091982420051140c8120300c000c203005260315800021079100c2c034030b06002c00240780019500c0c1c0043c210162440c550302c54401c4642100030500094000380c0403c451000e10350800f01800c8c250034000078082c46290b90742007c2001c2030142d2400c910325004080986050001101400403825400805508542c504910103258004105014041c50788503080c0c0010981f2440c1c04400200500d2602d41d1580c40d2885039000414140d003084820ba0319081c07010600000002e1200c10040e4001e01008480f084808540c4e03c503600383c0018080100d05206030300a5943e01d040d0a40a041c8541d0002050a00c1c907044105031400382014201c0c42d0700410100c01180c80100403030f070116805840c0035903240c442d120100904401603102c10303103075403414050240056000c50340e6410809182e0390615192500007080d41d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 875703318 1250 875702068 875702071
    0x1b17190906200f120c2503080c0705090106270e1305070305010c030902011707022a03070306061503060b03070309140615010f140a300f050609 63
    0x890398810103104055484500c0002481141d420307030b4924040321801e5032604805103d85600d440c00452880711540c01003150020440d00ba8110965180e509503103406e4400660101801d22440010121403034041040300600402015141040d40c0d82c4d1344400811043d0080c090201c45030180c150501c07100405c141c1981030780d80020100986840740c2c2e004900085280d001200d090042c0d90000012410a20543d0102007003900c0c080307440b90031880010027240c0360000760380c040d4044100703001d02030b680000c0e0402c0c02007501504000ca203488103040480c40700600c104130341c180314440001c001c00401d42c0001080700e0b03c01800d00c1d00380130012029030a8810358020002591820b10024001174401d4000d2082d86004124000081d440030300201c0c10200c0440e1045e101d24000d000d24034184d64000043c085444041c9080b0f61141c0071142860020b20a01c40107a0402017080300100300700846200e2000c419198001c5151010a40c88005c40540310303000050b00d9042c40c0000040f40750805030401c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 875704568 1250 875703318 875703329
    0x12010506030709020c07090f0b0414070804120c0b01030606060e032802271b0a05030604111606050601020c04020703080417040504020c03120901060303020a031b171909 74
    0x9101c90790400034610f00a41040c01c041c109403040700c80024803a50780e40f152410301d044640020801d01007000074041518110b5180788102040002003102075030b4040d0b1174030341090307110402e107880728500300d011110380c2e4070b50501620300740c8444000010000700d544403070304036501c603121040d0320b480c588109074685a280500d803c82154500c50260300c0e01d006882d04180300c4c4001c182154000d0b07020002522042c3c8240162000c6100d40c080c44120442110280902c0c10480441351910301300c070700014500e01001d800980141c1e100e1030002c00c882d4410342540e014811040b8021880ea040e030034420f0103041c09413001c5016014000112901d82054021103080507010380703513a170325629507030b607020700b4034809228201c04144c0600012880755103e00007801c020740e052009541b85c003a03403d02207805200c0030300815000c0e85002d008100103500410f8517100c080e01810814010380c001c107402c80007200d1041000704142200728034580383d10700040140c5000700303145030134580380c4000076010303140039109001c0c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 875705818 1250 875704568 875704573
    0xb0702070b03190f050103061a060901140c010204030203010e0a06110f19021c030212061e010815040204030c15090807090914030307090e16050702010c0503070b0c091201050603 78
    0x1407a99441c62658054912101d0b4001034110b44c0100114111802a001140d04585a4540382c800c91018422821081c00440c0e900f45041d8042c40007038000143d0060ba216440000f282050321683c0039030584000315000b40007804040220134080780c44005105007204c401d0f02e0114030050305542e080554013000c0030502c180b881c06e11803049030640c0c14206406102148501e50714206100203214005410886a480168035203200b22142d1000c1d610040ca01d0340108070a29450000480c406100c0611201c00c0c2080e2000f0f46034a1105201d060703940790159002800010300104000c0a2208001190754400b45864891030140b412903c18146210b1001e6941c841c5801703002800745680030034140fa01c070300005800c20f50408119401c64100321042c0011401c2c40c0d00401c20306052400c52540b018040030388034045080d05001a209014940000e8100540c00102c082000000c00c1220019500701c03403042c483d4504443c040110b5030020305082d00072807100b00540f034100c6050242c43d000c0c0703500402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 875707068 1250 875705818 875705821
    0x1e091e0904060b19031b0602060411011809051003060605060a0206160e03100609150335030a0903020c0102190b06150301090903030c080411090a060504060806040b0702070b03 77
    0x644001401c044062150b004900c03451041280c60b001080d040214407a6080484461194040d88840440b1f540f1000c1035400000030000001c0103440c14004005090a0841c009000d46280e0781000041d40c100101c00b41c50b09052050000092060b0411244161018000c49450760180806809003002d2803025a01c880d01040e850903aa016003180d0324451b02e00300d41030b8a80080028174180e1000b0380c5030a030a0381c40f9414000541540192004a5001c1c401404032a11355a640c0d00d58003548c054103d03610742145a451070107078401040b1601c100800401a0326424081c100c4030040080c100f04074098426506404210f50010401e400307081d82e1000380c01d0b0012002c2d101d10050f141d0041c5140c4d07002407462019900c1c5021107020310b020701511034000511076a0307460040c0440380140c040c10240006041000001861081440c1c68290144c0d00e450168440c407143c440503000a030042940b29040980210b030070300c4000b40d4a44164001c4140007041c4d100d24500341d803110382502480122010810 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 875708318 1250 875707068 875707073
    0xb04050c180918030d050417030403090303030e190b0703060e15011112160525060f09050312071a070c0807031101050c030406051506040504090204021e091e0904 71
    0x8002c19800540501140c2c1c041c0d0201049a0039a40600c1d0480000b13983c503020b20003070003503041c03a880310700d559a07640310f1031400c0c60b031400340121045200040030592502d104074050403007400343c59003503005100c0010f81713001c05160482e5003101c2190904006494501c000420303511003d0358030b000d00c810340c0d01070044110090044a9030120b42015200621800c16001e0031600f441c0700510b06904d0201a40102c000c2c24904542480ba0743d08040c0d0070703503254001d2030100074401021142102e0340e50404600384801e0903c2a00c00000e035a004a03814001c45003262218240c0d540146000341c800c0c02d21500d0302c280c0718507000b07030004d00390f6030040011642c2d030b1080001001a0b0003001796a0081c2030200288180041840c00d5510444802200d000042f00b0f010402150f0301407640c124117041c11310100170845d2030210349117003c0e600c980c5201d40c1d1030302203400954980b03904440d012800030141ea4450b0501c020300f6a0240e00c2012079500505000a600642c9a070b001012861500d005109001503103454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 875709568 1250 875708318 875708329
    0x2417011a15040b0414010f0302071505041b091b022a2e0f08060d0b1902030f0402010905061204020d083a0c050327030d0b04050c18 58
    0x709020401d0550400020030740e020301001520081c40880e0868007a0700a40d4001440c03200b40325004000c1c54010300c102400030761b506038080070719440d007100069036603039504040030200703001038503c0c82201c50b240010590182c5600102c01d00c0c0c3c0c05400e07411035007000a9040340c0d10054049040302d90450200e041c2d81c043e075600b060310140c0200034a8580c0c01d19a820341e020f91056610028042203031030107062109950828410b03244800300d41090491440c3c01b0700840e40b2001c580c00b0091000c111900003803445140d80c110f2600a07501e00c41c0840d01c900c0c00c40502c21034000291f4043e4081040d0a07000510303490010f0440321100c603601d403021f1950b01c1e00e50900101408220048503021014031004107d848143c5c03d40001c0400a5039040c60031898440c803030406c400948204000d24100300d40e001119410400302c0340c101042c21256074140c46c0072403914103880141d59015842e4040081e1140b44a0400c2d0404088040116020886034448009400407440303062186003a030018400c800b502494070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 875710818 1250 875709568 875709589
    0x7050a170c040f06020c090a0b0f040c0323271504050c0d0501051e01080d080907030605011d0106030501210302070504061d0f15060d2417011a 63
    0xa500e555414030740c49030f65082c08203100b0f811a10042c1d012000c811034918210080a4106003e034404120401022012612108502c20721602441c0c5489030940c05038031985c081046010503d1161104a441102028111105451816003119980c10000c00d440d60310781e610300495000d8005141c802031408021003119002030081d627940c0104119130074107440e08100c45000510030800003c107440e15504011603004c21b40000e111121003200140308014000a2240e403100e5142840c148598031400348138500441600024101d9080400000c0d10b4500781140020a000d8541075019582c1c0302d4404900700d0381c2c00d100b031034101501420401c02070b40b035a09042070690302a06c150769107a0f459901080568640d5802205020320f00d41c4101d0841d880801c3c402d4000e415520b403c0c4640c05e010baa07803c41c82c000320540c0d81c031540c400103460445002942c4902c003861900a200348034195070b00d0b01c03015024024401c91001e13103650201c0710b05a80c0c0610405010080820000141080d10b105000a0605 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 875712068 1250 875710818 875710831
    0x6070308090304051009091a030d200316171314040f0e1015050d140a051b040b19170f0109080a030c021203010e06060d09030c0b07050a17 61
    0xb080001090b02d031240c0043c0007076080b03d504d507078101c00d262055030011248043e180c0b451442d80d10881d12051382e00403907803020060181c503120103800f4100c0003003180d40440001c0f50681d88000504104068546010b026040703010b0058039181c20030380003c041c42845404007101ca1401803010920441150003002400000060000a40415181c9094040722480c07101d000c265480080388142c040755a0017600303440d1122102400c1490701d40008203480e000511401408444404090403440700c0811440545a07000300442d4418200f48440c01e0584681d075095038050340c01d0511a00c1a410a50b2117442005c00d10f81502940d2480c254000e000810346400c200c0d094021500030107071049090182e070f089103010700011a69118040d201500b2030758040d802da820f40d0010740805144018840a80c5e044600c44000c04040e6506e1100040f5148200d080c0c00c80d20914012529003415802900c103503200b88214051600c46d12460000c1c2c0d6a400344d5080c80001590084110b20203d02846003d90804c6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 875713318 1250 875712068 875712073
    0x311090703110a0c0c0803040e31081305090606030402100306120b0604151203110a121d040218120c061207090f0321170115020106140607030809 64
    0x405600007a8035922440c8583d0005842e40d000701e0a0080d546503200c000c1c84520700075131030310f4038104200100d09001042640c0c0b03400c00f00708c3c00103140708001c0010110401d41c892180d1802c11494207a0850304101c91288041e40c1c03424020905061540000d07015440c000d00043c115600ea40c204004000786801c80c400705034031080d00003000d4034540d9403454424030440041e40140b0348901404200d035014101d45e454003440901c2041680b403d4440300c07075841d8251418030350a03e506030184d0726143e850072009010780c03045205402c080d0b070320060300e00c4011460b800c280c07454545d4004000683c02078494003032a164508410040510f821851700d5013406109050b6020000310741c0004107103400c08085074803001d2841c010020000d504c404500094515024461112420342c2c581c481c0d04030407902c58500f01c5400c2d5042c6101c16000f5000362000140506c3c50304134540e100c00f580031505c00e00400c0800990708000000c110007044815420041001624040c1440e0b100d40301107400e004040c02800450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 875714568 1250 875713318 875713331
    0x70609020d0b1501030e03180105030c0f19030b03120405011b05010c0c02030706031a0405070e15041401090b0f1b0d0306210309031b211208010311090703 68
    0x9415501030b50310030140c4140c42042c00043c000054151020004040901d400402201084800c0c40800005801e000e01e841610380d0384100154105200302c503480d070341c00c0300301041040d0410804800d03421182415901030143e219103205241d525070400940e455440802d0000f03010f1540328101d0401000c1100382107424403d01c0d6158582152101041440043da90854000541c1410401d100080066180401c00c20740540104903041c0000b011041c03040391100041070300144610410300c20100010f0030340a89006007c10b070010341d48940308800c00844000f10445c034560082c0c0461044594100c61380344ad044885c0b001103000d070700c4003410903034100c040004a04d480c60304002c841000c4441d92000181c0324281003441d032286480056054084040381c2c610300000758804000402c032648500d0040d01465440041040140303182c01c40240f1303500882031420307010320700014400ca282c020441102d0212070042e0407941e0036000d010103891204c0c09003192040c0d040100304c696000b43c0030710307000401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 875715818 1250 875714568 875714573
    0x302090102070f0902040e091606030c031416080c270105070c1805100303050a0327050102130f1a0307021203091e010c17180106170606040908070609020d 68
    0x14481a0401c0b4034181c1d0206c0d050040c0341c042d564403034010599100804e0030314211040811480c0c02c41c0201d908054071000c014440d140aa0802e10038500004c05841c40c92401440000f41940c150a14600003a00e08000c6880d210b24002200d44c02d600506940006042c030006d200034040f01410058100041003001d180400c04965a0b40040c052800d0741e812140d04020480302600c0d0050075000706202c80450420000c0d1b0840201e03843d0b1601400c2c082442494a500b04490006201140e082d28440d80291390401c1019401401406000c650569045884072281040040c980c01346401c464600b000c00c0d80002100c1000c1d40e81304906104a0b42c2001c800d400b050701c2c507041900c00d2052544203090028001080700c1c0c4180700041d0300c03002040040340c46113000380792442caa18411480728102020410128010f5290005c99820800a004084e61914070f008007103168082e4401c107004103004100301d8902400f91001d5a60000f170018200036071910b4500c001d0041000499000c082c1c159000e00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 875717068 1250 875715818 875715839
    0x2c0d1b080d0807020f031c090f060e0102280509010809012a0f031a150f071b0b0306010818011b0513140a0e060112050901060330030209010207 63
    0x6415110307034032102ca0342400360000c0e107009200001148075030424041c0841f00401908086171078180710401081c410418100300c15079548142e0003a100034200800504403c005400400c00c28510326120407501046500c4201480450760740c0a0000d0f00410500c0400d6200f070804603040300744d10f000080c50004d52000007900606908501c6e4107841800d03841e08460390403071400030b03901c0d07000d0406000000848424515003071205051034400d140c085040f81d4048103038815203003981d48100d10303182d54440d40d0800788150000c0110701c4002c1d281c080c3e0081081c81072803082c0c03409420183c40e450815111500d04d184072003102001e98441d5980c0700c8003030601515920181d4071901054035850780c0e85441c00c2400d081c0f200f040d0080068841ea524105c0440d8036000f02c0c0c202124415101140d26444610048480285100c072100c81581000144541000b042d48136004981c0300d828240c0220605007540c1c140040b0410b4a00d080403020481050703810302980040000410501c1550a8036455981011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 875718318 1250 875717068 875717083
    0x141305040c0203041d0612010e0c01050f040911040519150c060b061303060f0e0304030b0a290916020307060e0c040212010911040806040f0f0807032c0d1b08 69
    0x5d1119039450144032403401d01240914050992500030301000f00901c0c880c56880300d0b442806c40c1000400a0324000c0c6d0588034060360003402a00724140406c010800c4854600e030041c1c00b905108000c40400e40210031254210b040131114003a0807401c0c40c0c0c0000c0300a5860070700ba1101516050b88032030f4080d1299a4440040041c419025492621941141408401c4a01001080509a141540000d1019000415102100e50140481e0504d540384076240b4040e017a5a90710303d0040180a000500b140c450b4502c80300600801c0d11492030990340c10180550380c0c0084e00817034016800402041002c40d081e6080490400800c9049500c1c1d000440c3c0803d04a0780241040302c43c0201410050200d00360754010013031035500c2c001c242401c040c18000c80c1916904090300c010401c055040008080107005100300300403d4220403015183d02c903905019114030b101e1480300008a00300c1c0c01140071560002d0034104071100161001c2c10341c4181e9030740d041c46060302c0030201070b40c50b58811001403154020440b52 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 875719424 1106 875718318 875718359
    0xc0115140d0501020d02040b0a02010b0301110417010603210e1005030c032805010509060a03260c010501060f110a03021504080d05070f141305040c020304 68
    0xb580248640941911954004100090300641c0e00005d8510004c064000717000250b85041050708a410001e1442e00040d42804180700008418451038102104200000740440c0c80e51036140c41800510200e2020700b820522109070f071607104c103010102c8101612845440c0c41d8011002e4080d0000070000003e900006c03001881a1445442c040c0b0400088440e040f450102002402d000cbd20b02401494000c1d8641400305840d4205507808500710307604001c40d00030b41c1e100c0400d9442200303210b40316080407000602c03803011002020701c1703018001c0005480300c0f03040ca070307601e980a0714002102c03180c2481c540001c5440e1000c660080b4403c1c00c8024041e03600c18040d5240d2400e510103010740303550580c0c00392611f400c004546070010024400d00925485180200416250860603032160703c60450a40d8480039042256003000d410190708100d513401501e0801ea10741c08043e14203480040d04 = true := by decide +kernel

theorem cover : BRFrame.Cov 875539568 875719424 := by
  have h0 := BRFrame.cov_init 875539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 875539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 875539568 ≤ n) (h2 : n < 875719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
