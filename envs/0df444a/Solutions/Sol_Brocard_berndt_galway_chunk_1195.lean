-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1195
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:42:15.835593+00:00
-- url     : https://prove2.me/submissions/c95b907f-e8b1-403c-a918-665f723b3524

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 214748201 ≤ n < 214928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 214749451 1250 214748201 214748213
    0x20c060d0e0d0302030403030c0e0114130e09030405310504050c0409050d140702090718081009031202120c1608030c0304030336020a05030d0206061002121204 70
    0x2003110405842c041d5408082e031643e030590145100d24082c1d607080c42402491030040d204400002613842c0024942c1d05e503040944041ea0040107038840d0030282c1d9490070341d950765040760500143c442036a03a4100003002c0005151034056519034100b124608e400142c0d0a80910324003103001c0400c4000e070b6131510009010b0190a201c00c074403141001d042400f00a06900c1d14035120340382ca2155030049082c0c10400d5900c000054203a501c815800f0b800c9181d1901d4005056074034102040034920f001c3d03503280010400326020311615103140b06a0001080240003444e024200080201d002200303144103002401c00c0380500e6016035001811542c00c65500d03002c450718030040304250307000030f00608800418001c4070061100154821800b0b65402c112282e042c023104079403560314016501000c0f032008421008041900354240c1c80c02c1c07004200803615550f0700042070a2200f508840009a00410304000260404901c0c030310034101d10344040c11801041040a20070741c0505c2401c0c07046894048009030070052 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 214750701 1250 214749451 214749461
    0xa0212031005130e030a0e031603051e0304120302030304020405070c110904020303090415050a050d05100b1309060c080612070b070204150e1e13203c01020c060d 71
    0x80101d0030345e55610f0414402170080450702c40658044d104128894080d10f031000e0040b4241c941c0f11001d00034881a1401404001c030110350462101c1c0010040000d10040103003070f0080ca94420b4001c0c41c0c0300d1509004002c200c0b42c000300301d202030164441c0590005242c00307981202c0c208007103640400c3c40c0c5503400881e00e180100c010844c0c00518107600301c0004e5801d010041e04640c812200902d0950300e500c03e01442d40750000009200e0751140100c0103440d4100d4020700d07841ca5010308016060f0813001d03001010703120401400da46481c1d0b295000010141d09c8010030b03901c000140e803082c2c0081c840d00384840c1e0762103540c80b074002c5000020810f0403c540d01c50f0000c1440070000c0b0f50700807409494100002c3c510100341d8035140d4014036210201c150f80f006441c0717284510040680048400300d25150510b0018a907004c1c20306010000d180d80c4000e60f59640300798013000310f1407140b50502c109604c011001202c6c080f80501015050141c0c00405c0ea4002130f01900b80206980c01c2d45c990802c2c04003000030708 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 214751951 1250 214750701 214750721
    0x702010603140f0c0d0503041a07050a03030b01080703140106030b1206101d06091b1215030106050306040503092b0302030a0e09100603020a110a080a021203100513 72
    0x4003680c10041c02e140001c640380f0300642c2200f5a110401c1e01c00400200c0c400b4018020402c0d013040c001008800c84102c013035040f554414022501d41075003075a030103082c140c5941c0c1c1140820f43d00c01c614131141d40c0c03002e8919800002800c00b00400c4800c8020700c5131400e01407041d0003c15440c1c0c00820b9540e110501490390b000104412151582045122103000c01c100c0d0042941d102041f000002820380d03078183c0d06000e0308000c1c040744515250051003082e44414040d08a010f21070030401d80030f0034031a0740e103090320911301c03001020382c0c2c0390f07030901011300b034400350780c0458072a034421014000819404030884021860444640c031004031030320007450400b00c952040d440700341c07a524108c100349500480145081c0b5180d5403584410b440703078030400404407000e843c00c5003c901c0c15141409003900035802000030103020709007001e01404109505240c101c4910b001c84103a4400728a100321207404101080300004003035400390842c0350001c6a00720320003451041c00c4c800d610850029074003114980c40b03103804c1c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 214753201 1250 214751951 214751963
    0x309010617030c16030803041e0210030b1302040305060114040b1e010e060403031e090510090807150f03020f0d020d0515011103070206090a050603010e040b010602070b0406080702010603 82
    0x8080078540c0d440b500070b208408107601903400503250241c03507081c120042e640c1c84906103096455070703203440010850310941030030b0b171504540740000513a0ba4901031201d503041da6940414009030300010b0146941081418010080c010703c01800000c901180c0075042d1191140003640340780003400028041c0840400b090b400020340f00104081c1d0352601d8000000e01d50030b0300c072000204059000d00c081c030301c01d0784400740c0003454034404140301c00fa025031043e03501c600d1031802d4951103840344002400c400c6128a03c070085203169404004084042c0003500c020320102101009450040310060100500340031117404140c0c0c001003100c00048500140c4101c603c03c103808540740c0d016025450300501e401c0c0d81d0141e10311205190f501c0c10750301c61004801041021000b40d0f007010320550900c8902e4000380c202d50350241c20b907940030035079480340d101441c003c140030f00d0300c0c2d6003d05250608042c44c0d0b106800c160219000b003101409020083d00441d0129409860600b65950f41c1110407801020107030001424 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 214754451 1250 214753201 214753229
    0xb19020a0504060905240702040e070b0405030609010513081b010f0506030f07030804170a0f0b10150c0210110f0c120c0d0f020d0803070903060b09040309030803090106 74
    0x1401d91040142c419a01241c68010403d40c40d0380402000c95081c2107200901c520101032107840542a401400d1460301c0580046004d60405083d10308200791b6800c026000c44000c10104002d1900300046900b02c0c0402c0004c01050030010079581420a030a14041c00400b000070f46c0170304a003e010001040b149501c00200309032480e80c1c101e88003908081e0342c1c01e80b09100d000000040810b000c5040380840784e11854591030545404040307243d49140410000300c2d07010b591070740404a04502010b0050522405400c0030903d401075002d04450a540c01440c460700b0032540001c10f25411080543c42c064040700c402c86c0d900100340c400c681c00b10011410b00528040d01c0031000c450800050725910542045902004a2044010507030751544c081d0140e580c402007045803100810611075445000500117044024032449549444c0c42651003610301d0f800040030f1103420020f005551050340364001007182c0d44090760170b00d900c000300b080c2d840340000341c54460000041400703128250f000400800700c42c903403421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 214755701 1250 214754451 214754467
    0x318060612030f03150e060103020702130501030c0f0f1a07141c020f1e0309090708012309060108090f0a0b16020613060207060609060905041a070c0b1902 68
    0x7280010740400c402003840c200d0002da440c0d019004040e103c4044000102030689456002c010380075019120b241415400c011039005a01d6040c00132024003140c80010809514602d402d0005204903402a0840d46449400f4000c42002010302c60859214200741001540d0220004030103108a8000030149003032400c2407001e640c000320700c1f40c0c240c406010701100d003034038000c0044e40c548510b0030a48007660081030940c510504441d0703000603440082e000322810802200e0206038002020b481e2200422020b00c01044640d1800c1114801280b40000700040059200e02082d02c0c81d1005d4a424144200c40c1c0c00249822030400082d4650380d001004c40b0140c10f405d003410030071b801d0191503000702d500b65041407030384807400055051301843c07581c3d01c101c01465207500d5a0000390084c803422900140c8070b001c006120b001d0b038051400070308020100084d840c1813510b0203c41089419a0443c000c0c0c00c1c1c0300c100041140c1100c044407295030843c1268003280c1c2d4a920a050f134505642801d01c4562010800344 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 214756951 1250 214755701 214755719
    0x30305160801050a0302011b06020a1107120201050301141210020a080f040507120c09020403031d09040309050d0f140309010f0509030318061c0c0e0a0f0603180606 72
    0xa000312005405810000320000003120304080901030160444115001000154842c0c0700041c04090104545c00700c0607003d98900040c1d90104440703000149400c0007000000348280808002409a04054a441c000541c006045800305204d540c0080c12104424680f80d100e60000a0000055800781c42c02650030400000080d04000820000a107002001500746400c0780000c5005503004002040385900d0030381005800c500303200040381c0080c28680006420907040c00584043c51198803610700c80b108000107140020150040188141c124605001c082904039800d001520010340d4012b28401c0385082134201b1a0003214018480b04807480100307480040400a0f15804500341c0e01e9070302201c04003000311114010410380c9549a0010072103007500e01445d0071490a1403201400b0b550904210011041d404150030000c0d1118603264920488010791148140742036035011140381c04038904080455814901c9402420145035607081d08801a40001c00c0d0041081d6004409120301c0d44c03503030940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 214758201 1250 214756951 214756961
    0xe0307080d0f080a1d1014060a030b09160311090a050f011406040506070803040b100b12100e0a0c020f01020f04050906030a0209180c010f020a060c14040e0f0a1503060b0a050a030303 80
    0x400c6c0c005141100550002183c00101409244c00400c0e80a8a07400c5440b40030040da0b01402a4081d8859000d964555410320a00b5900440c019400544d00c0341340481402010003004044a0b680e91420003001400c001102d1410305580d03c440c0d03e2240c4030b00c01c0380420304074841e0750026940607402003021020002c07408000c500c2188070705241e00b6207403a508a003036901c60040c0550003c406003800a00c14240103032007580e60141d0840200042c040d62134000c238500440580c3d2807035202c0d40318601200701079010080e14681d12407000003140f03001444900303200305003d140078952254608102280c0e05903420441407071002d0300104002142d0501c5940c282d1400704c1c81c04090f103140294240344202c0e40c010074903458400c5154015015034549956807030010070810000d441400380b01c549811000c01c0c203a010304054416090a103600d0700381013140c0144c07a0380080c11007a5050a02c241f1254a07003400c86a00105d961002c00030403003100340000245c50044540000c1d030824108003001040c950300d6044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 214759451 1250 214758201 214758223
    0x30c110102011d03130602190f05030403060507020d03051f12080c190c0e1b07170f1e09062208152a0306010c020105190e0307080d0f080a1d 62
    0x40044117980d1010240d0f128044501001d159071001d0030300700045003140c5012610280724401f928030341603c0f0f64400c01207540c02e58031f60005034008003000e03482a416125450f04040038180c104244174654500200ca10100d0003200c40002c02240400b0410982005443d1021090402d9500711042d5aa08040054030010f083e40c030309104020016041c070740d62000b1802080d80d030a41040220b4001c07180c1c0c175030f0340c0540011103c50551564030480710040c003018080f520031130501d140c0c1d0ba070400d140c0103520701803c0c0100111880704000c807410b20750302c0c44e0443d51008080d041021140f0990740d10071640003266404600300e40a0000c164481d0705070010820710610503140320348180c2c0c00304c1c00c051021403519094844081d0003040420b1481d8005e110b00000c89105142c0540303448080744040c0c034041c2d25000c210001c650300940b0415280f400b40305a1010b404880010032451802043c0105420312100308481440080004507000080b540c00848561101106074425003078800b540540d51401050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 214760701 1250 214759451 214759477
    0x30b0f15060a0c110a0609050f090f181e070f0b0a0f05130302060c060610080f0f0606070f0b06040b060a020705040510030c0b0c0606010302030103030c110102011d03 73
    0x24040300385411030003081020140031281000b60600065a0044620400b990340007102d00b0034000680d0f521002001030401c3d640c808030340d41d01e0841848042502401c5440c0710790884801c010302c01000c1281c82d6807125408032408502d0002c450a9800d140100c41d0800010b1a641112901c40100140100498122500d441c0980f517407900b0707940d41805501e1000e80007421030480b2024882c400c0010b440b006982e41c461001c256541d80c0024803903841140d00c51032980200c010040940791400c2c02490b1542107080c154094902581611148000281188484456074000c981c042c2c4410065035401c0d0b50002180c4ca00302c48030f062418003000101c402520542c01c01c80080c015003000d00940740c6600d00c9030010700c45541804100f00142034028000d6003944d0072028000041002e0502410040602d2264580c2e00e01c4010301c071070304100c4020805814540100010030000b684045e042001c1e40c1c00c0301c0d240c4002c94007800100d0140a1800c4000c1c0c10b019011100d42c91418080020829443d00700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 214761951 1250 214760701 214760731
    0x30506010311030610060f030903021c090905060f090c0a03091707050f07180216240b0d0b0601030b01020f0601080d1101091e060f0606030606120b10120207050601030b 74
    0xc0325030032045d101c1c040d41c00045c00d095810280e0602a8004807411031090040d01d01301013920803038013550b02c210602c0200184a40c102000340582314403403507420220a0303428490840046012450065019061108040d80040d000c03000d548294095041039602c0380702c0c1c43c55003600303101111182c1c12410082c0d40314010200075003403c1c02c000901e0011160740c00c141c0c110070300c5082d90800c0250030150300750b1400c04500030140001840d0610740300304170002c04100144181c01035100411110004025801410206840742c08a07894000381d9a01c400246400b01e002030b0400e00403030405010709032095680c46901e0021400b035001141081801d221a078421106640c010400c5003030700d04256028184501c0e1203034402c1d0101c1d03100102c4020a01548001c00e030300f8504246034044904591011f000a0b03550403040c0003aaa00107145040641800c100740030303006da1580011001c03001c40d550300c0c0620403800e10040c0c1903401c0780c05580c02c0d41d800101340c40481d03941c1e04240c400100201c49400841b4680 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 214763201 1250 214761951 214761961
    0x6120b06090106020606010f0c080d051603020a051605012c0f0114040303090305120a020d0c020c092202060301090606140c1b060c030a020c12030a0c1b0305060103110306 75
    0x104541c50b040700c11650041086859040040d03404400038400c1c607081107508401180850000d000828681c41c44100000302032910300c81001c4070b0b00f9002da601c0300f014010000c01904070341c4403043d5491002c840560f180806150b20b0403600400b401c005600480344a035240d105410016000305628002c42019121840c1e03044001c1401c8590901002c10004846404500802d10950103654074601c82c0c20001d260502003060401410380403180c0065850700007600b0fa00c0f40c20580510b0b03180c2c40d0280010039414143c4030002e80759010080803800d030007040c0c43c142e1f801c21000c0d49020b140c1d150041c1030b050380c950f1205158400b42029004042c08a414900c002700c03840400340c22203024070005006070524a00c1180445800107000d12001d601c201d0600c44107901110600060a0b000e006400501c418039040c014440461007849000149400070302007859410b4104402d503d456034007952811810101d8405194039020719000076005203e248004403c10030b8124541c0908103044045a1040c0d9407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 214764451 1250 214763201 214763209
    0x601060531031e21050f070c030210080405151005040204090203060922030f20060f09011a06090a080604080307080108010908070602032e05180606090d06060906120b06 74
    0xb20050051120005014038102002071985044e2810000c4c40c04d1403410740e60400c06a02a04107120607681588000030800441c540300e41c2001342c0c2c80440c1031032016031600d074660a440d10450001440361500040001700c422100340580c10107004002c20440d1102c1d1100181d200075007089035030340c0c0103c5514010483c0514259454240c103054684c1c1c2103010356441d5030864100c000891050148150104002c12140080b5600d030040d031401700c0200803628009e1b4411992107001b410944840e4907042050340d41c0c1141c103000700389069055401079603512014000c184030803216449a42c1501901081c8030400c4071407401903014505654030000c0c241d0f01c440d0003034221294014003c080c020100305010028241f03401035a4030189030703001e2148540c07184070f10402c00601c44040d080024016941885180380000400c03c1b69152401040d82601e080c00c041901071080d01509482408840740380d504200d02c9400400190040260a0255a6a5890580907402280c2c022a070080e60a000a100c86c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 214765701 1250 214764451 214764503
    0x30d020d030b190510120504140c04110d0b1f02030c06010b1206010c14060907050325120203030c01020406030f0b03011a0105030606123105060106053103 68
    0x610300d0f100354500e502d000c04000701581e003940d40d08244400c02c0b190740b988400a01c1501e00c80d50242100c140c0d803000c0089400c1c00e00c0408803481344900d1400d001e104005440400381c0351304032140f030b5000401e1205080000c00c03900d074100390640e1a181c41c40d1006080f80c0e002c4050f00601210404540081c1d8961a60468501801e4011581d5095400000703a40c0d40c0304d02d450074181409203040400c0441c5201c20b41e41001d50844040c00340c0c4c0e2004038100842d0a0400400c004040c1240844101044060301d0b00412001e52143e00c8110400702010401d556081c03044400200501d40215a210707038450000e4060312060310324803401441d2821115141c1018094224004640c3c400e1301e0921119900640b03c54001902d078982145052041126000c4820221406061100c9856540c02d20052540640314449055510802802c43d00071000940002c0d11a0541d80c15081460b180c140303480d03c244d5010151076007203580700c10083c5007102c07040741414440141c9000741515008072070007003501d4008031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 214766951 1250 214765701 214765729
    0x403111008070302030a111602100516060b060f0d090209181905011104061808010c05070f15050403080412020303090c01031d0601060915030c0507080a0e030d020d030b 74
    0xe03841c03900203011036101c0e90007954401c081140001d88a600c0700e0003510140c02c0300e580038041d229844122000c0d440c180d00490b0060340945000d603d4070a894000d440842004c1d24000c1800340c942c003078103801e951007005545614501c0204030f612866941741d00000b80240d00404e900600c021004039645c540c6c40c1041072400d80601c4000c02000c1109180c1010320007824005550a551b10403112800050760340c008c000403d055582c02d89050400e48410045d480d4603442004240c1c5003150a205d80b6401100b918030031a0042211516007909007405000241082a51240346281c401000209a000f0001c0c0e806076008820702c41c2800460302d01680d5030320003a19030345050343c42040d00c41e52641c030075040900300e403000c146c0035547c2d80303629103109181c00820f80103600420785150f410310840400140701d54094000d442c040c000c043c042c51001c1c0443c496880050301385200003503080d00c142d000d4400303c0410103000d0300b19400c1110040c8025110030b40c004200c0002410008000070500c2c182c0d8150601d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 214768201 1250 214766951 214766957
    0x15030b0c07020d02280f0515070c05011202070b0408030708102301090f240f0504171501240c02100c15060306020d060504020703080a27060204031110 66
    0x88441c90f003c05c030b400c815140600811341500410040300c5e95070030040c03800600c507101030031002904140c10040740710301c1c0050b0800214014003029003c50f0340092603000301c940c28209507020b500455a02e8000e841000c1018050030144014802041121002180310b42c059a880121985401a03140c2c05002c0e1b80c401c04952510807000101d54241c2194070308005070050408080241e552805540800d0965115155045610111460103220300a8000c8282e90514003001c035880118405803650059024075068141e410040c01c0116a040001c000010100f0300494100c0da942c0b040c1c03564601e4090058108541c480601c0c0c1c00890060034000e2311140c1c0286010080340c01c004040350ba50004020943d1070200035544441301c4d150744d05c903c0006d035019210260b03803811942c1d0100c043d01c42c2a400203004520401210010a90208001e9001041a140451480d4400307080d105a4240c2c445234000106521061500f00041c43d4014001c89106090002d5000ca10008001c003132444c070034101c0f000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 214769451 1250 214768201 214768219
    0x50a1101090b042309091c0c0f050d090b0307080a05040309081902011404051503040318060810170c1003110d021305040204051005091c0b0f0108031c0b0f0415030b0c0702 75
    0x2000300c11f807c150821880c18a020700784d920081c0c442d070441580d00c26095a081d00300b0090154029403100d2040040c1202501d0103156007040ea20088c06440002d020549080d41c9801180c01c251152140c2802450b80740b040390352000110040881651440c0822404204c10640c0001600d29a0307042d24200c0e4401404030101d8014201005001c1c1d0008000300d0400c04040790030340030311810781619406030445640700e043d10301e072000d12041c83c0b07032550300042c071000d0080d80081001d5000064103c21158242c401458050300e8039010f801a00689800c41a030304008101000e040341d05034040c290b0350686015800510307030369005002c100d100324060740c1e4212030303094508243d0b580100d0003071a01c07103c0070304003588454681140f01020406100200c492055840c01d01c000c03000108800d6015000400c05149080c4480d04440001c0c0700d11640002100c0e1034850b00c201d00d070b442c6a00000c5000c8007030030600250406400e1560352494902085400b080c190b00412000c6000c0c2c001d448001c6d60292000350 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 214770701 1250 214769451 214769473
    0x30403021e030106081c0e10050a030f18030315030b0711030705070b1c050910110f0307020a030f0203070201080a090f02100305070f050304050a1101090b04230909 72
    0x49144001031240d0704540600c54448194800b4070644005010701c00c05005800242c6d040c510240c5200e80150040004030380d041c685a40c3e40c000c20109420b00b90134010f584120700801a005440c1386101c6001c450702c0c10700200f1040b804042c603421401e00c0303550b0410040081c6540d050160b0001e000140410815000056500740608480c0621401c94804c81e41070903a1983d40f2498240e09801410b00c0c16808504031281c104000c0342c0c10b5011092007405c0c05580ba14040c11a42c2d01c1c00040410000754481700b181803001894011030f95503d01c0d0840c010b540749003000000c0c0d41c40110645c11000101c4540c2c02041d15480481503945d001d505071744070781d01034032a440c088014090740403068890780c1150000000690350300581d0b1400046a0700c021615150111014114510070038491090100410070400050004144400c0041e440880b00c001e400d42000103d50042e400c0c0c000d80c8080800060100c3c1e55640e104903076402c403034190030803440c141402013406000354003a01c1050007903000c1c0003500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 214771951 1250 214770701 214770709
    0xb040305031210080708100513030e1e1e030d02070e06220c0c020a06020a0807060222030c030519030f03090206160803010504051602030304030f0905090711010b030c0303040302 78
    0x3d03000b2104185014886484002080c10002c2c1a031143c00341d5480030b0f000360f410003001d0291540c000c0e0108241944a4403d484c003904400c3c25040c0c043c480e942071000c00140c0d1114440d01c1100c940c02520501c404140140c440052940c4510160301c00e10803004d0405c40030340700045003819140520819000c0751114014020f10b04040031003d07103000280049200c0031030f40b503c249181304045507203c00002d500c5005200221900ba0082c20443d0400c0c001040420411411107400550219005980301011051110310b141c120341d0102240030304440c00400d1055002c0b5a40907680224260385d81401403606003e640542404024007007030094040300b042501940c0500c60840c005417500d1b26210b82850801e44d83c418000b01100c1c8040e000c0014080c83c00d02c0d216a5034468546c041904c1c00002d81c0304084d60341d00000780300904108080804c030140c5407289203003070010100a0213200c82410244c00c0078100d0044820601540d40c03074161013403070500c1c000540404614002c0c028503e09400c0d17400b40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 214773201 1250 214771951 214771987
    0x611070224070605070f12150b0304080408031908091504030804030201110a030204060207090b0627030d03050105011106010510032d0b03060114131e0e010608070b04030503 76
    0x1d114116400e221040210310307a4001e152140507180e1303400301c41c403004410203400c000c0100c249144d8646000844a1144114404213060721034a010f00c2e17860b6030711443d2490143c0f15907000f10115010214050040b20501c2c50581d226009a0b15504981d5030303085006a0f40d4401c2c8040102800311010101e80424007a190f002d400c580030707100100300300f841405645170b2544200f0000c0300090380040c040140e103905010540c0601228a024842c407070381200000c1441c040d034121220403480c00141042110104078014114400c0a002d80c5d054074004040500201800d104480c0440c005001c032080342d03080861080e041e2000204200f000d40f0341080e00310003d01c1e601a024100f0f80040390110032100d45046401c080c0c0d404c113200800c4004a081c14542001c0040c1d0010304c80c400f42040c40720340c60782c44020404540110460000b2154a5407881c3e0032880c20201088070300c0352502c000552038107410f4100c1ca007952541d2045505031642d03000103060f24440d41c400540560028802400c20f042500c0782 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 214774451 1250 214773201 214773259
    0x18050f090d0f0806042a1101020f040302060a0507050a061d03030601021510030203060123010801030302030d0203060117090a03030501060c0201230403020a06050d0b0f0102060604090c091806110702 87
    0x42d0070b86030146c5240d1142c0b0040440c0640403120354044000650140221000c8a941d4009504080c81c001071015540501d01009108400124002003468410320a450071070f03400c90300701d0f1046503041c14410020b10f9030005400c040904035003110400480081121700511043c2c3c018059801a40724100f40248083d240460054bd03162000001d030360700300700250191481410b11510000703100d8092a00c41c68200030706042c0032001c00108086600401a101480050380380541d4030b41e103010049581003c00032800800617591820300a00d500005018500c543c0b003600c2c1000717281d880c3c0780d050750601410b00d0003d0000b100d2040100201d20788524003102c03c03403411050745c102070322076000408415154102100085000c520301241c5021400385007528902522002450540400005d407210002080c0c41e020300c0d12001514108410054480020f000441c0b00300094801c002000301001c1e000e40d8180c880700c0c24001401d00440701d900c120f400072603000704145007076001060f03285000c60707050382 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 214775701 1250 214774451 214774459
    0xf060103060902071e080903100e01060e040309121a0702010b030d03150302040b061902030c010510050607230708011a09060f0904061806051608042a18050f090d0f0806 74
    0x1144010380c44c08c11a840d80507540b27200c0031880344e017481c2845003111100c0c0c0c85000401c0103441800b011a80044080c002c3c0d03441410622001910f60400040300000c1c01000a4154040c00401480b141d040d4417603050000300710309603212418007a00803401e40e00e0072042d014040003041c00820051409a001e00c06030070000d01400d0500425800403400680782182c00d50150300009000c030501c0070203118166108611801040645003082c0101b00c1c240110840108180d040c030021481c00240c0815050190001000307c91000b600c0300440307070180c0007480d6260000051100106041d1402d030340f0301885004064821402000d40004006035104080c00075508035a4480c2e183c4c82030030341c03031001800050007000c000c40c0e2070411903404603010601081d0b03c4200b00d450018080042d00d40c0740c031444440540b008105254201d104c0010101d00705070311001940a650420340352240181e00700c6c1d0722801c684020504503643da0b4080a84800342c000300e4000144e0b40d901d280113100d0081c14456000748000e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 214776951 1250 214775701 214775707
    0x4090c0e0402070c1502012a0c020a180e010b030a0807030c080c0705090c07050706210f0b01030509030f07020108070509030d0206040519030804020d0f05060f060103060902071e08 79
    0x501240481c3d10551042e101d1240d203020030f00c000382c1d08034510150441030740f008100e0b104152441124841c01c0b0304030381c8804840f4940d00910380e40704214460314280c00600c1c400c68640e4651100c10907030b0010b41d48903115805c01e01500194013041c81031400d0140044c0c00750800e029690380d4045554410f840480500246213240c2003c08c80a0703018140c6490402c2c020304201c0d0600f82003025900d4000c041c000944410002c14001a0010400b482210000e0504e8030b000c0348800d040181200e4200440340d4843d1400d00403105042e59a00325120018081c3c80c20001c40c1c545410740c60f200d2140741d022443c0300720100400720041d4030400c0c519504c0281c074a000b81c2854202c200280c140f0302c1919100340103900c564240800e122080c01859003001c03801450310b44000040c4d030050030041c4c0c001c002900c0b48144d03044c00014000703c581c2100340036900100b43d820b5803034404001c1785842c505941460002e4502100400d5100b80d40c402c50b6070b541d8021103e40044503e2012060940481180485014500b8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 214778201 1250 214776951 214776977
    0x50603040302160801020d151410020705032b050309060c0307050702100518010e03150901090f0302160801050f0a1a0415030204050f01050603161107060512070306080304090c 77
    0x1400c0408054140d1340d00159071124010281c00c15039002c8003445802c403c0084007000345c0c00c00320400030050041550280c445a101c01402da06068840d0b02c100e0305406825821044c034000d0008403484400c03a4480c0d419003904c0070004592a000407030710020070f64003440202d81311030954009554802414a0030a180108550200702d001800480718008190049081828061052141c404220b820300c0c1100817003841000090755100390101c06506100c0d89000310391740007801e41051140642000e030031300b24480585002035540b0500d01ea107401020070b18501151411040c011203024103044400316005031a8440480c00a24000c580201006040740b422091504e49009503280b05c1e124201140c101403460040c041520802841c0e03000080787c040041c0200c0e6100303000d480c0c02580d042c2010040002d202001d45002c0d101d1030003440c2c20711440c1c10000d03002d07911034000d1441d010301c8000030740540c43d808415400e58803940031300c4895820600007407003e41a40c0d408007940d203c1e103261001c004116 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 214779451 1250 214778201 214778233
    0x804030c051213062d11100905030c120f030106030507180b09150c03030c0f040b0705030301090b040b031507030213090c090608041a040f060e0a020424050603040302 73
    0x2c00403034950401030f40411240b41c0103900482200d0002c0040100388040e403031400d120b038030310074085400e111130b034001e00307040d200100501010b10280100030000300f00981842a0380380c010f48254074032803003001b005d002007052104c02d40b080d1000c501020390039030342400000c4d00035200041118040122590b442c0b0300d4640a8040d29000b0180b01c407290b0744d110000d10600c284000009450440100100003031522500c0020480754805c40c6198501d40f20700c04104507010501c903950180c100144040303201000c2c424003100450480d041d08104004000110080c0300556040300e405540c59049040f44502c001d03540b1001c40d0f03120b01d841c41c0040c9400d400080c2c80e0040c2c4143e030406112039995907482c628880c1c1140c0080040c1025007041087c07803905940c0c00e040801990a080300c407074400004242000080d40754051a00d40c42001401050384042c0c4c00c0b40d481604071010780c8104d003403100804c0c44400350301004104016072010004458105000c3c4007160740060021030071881740504400280c1d00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 214780701 1250 214779451 214779457
    0xf070203010f050702060601020f15100503030d0203091e0d0e040b0a03031707080f010603021e0307020a0218090304050f030a1b0609081f0e010f060b09120606010804030c0512 77
    0x1824a0b001507141044a4000d142030001082141594003054101e614840700060011030030068600080c641c0d6900d04140700341d00020307889180c06120203d00c5503aa1406a0046c61081221500b2140390524075650041501d021005c142166003001c0c002a52040c030803080d84586100241c40420140503410206000c02c40310741c03003900052124086a0081c03c1c5060816401c001d0510f0b001d01c15080c00941d90820000611801c82490340c001140d030b21000554641650a28004840b59101d29000401035112005014228031415400e55005822101107035024001c00107900114102410a418001c03c990801459603240c880c0c101e242001808000407180741603480c040400c02c251501c80e019003441c8c0150041d901c6500060301c100340d201c800500c00c2d007000b40210404641c01007095502c07401441005801c0b08402d0030328501140c00c4002c3d800810b807004007940c11071001418135030010345820080d180540015a032001240c0440c1c865900070000078028019918a800c0d014060600c1c0c0e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 214781951 1250 214780701 214780721
    0xc090b03011d060925090803030703020a020d020a0803010506160b04030302071b140d02040912021c030908090402130918021f120203101802131e09020f07020301 71
    0x200d0b818280e0a01c0c0202e20415004041500c80082c10300304800c0101100c40300a41001c884461518084609442025810300800d210800c0da552800d20400007006580f06060143c0507116201d000580b20f0300c0084e10344001c41e00070f51b40341e05603401c19080250303541c002e074003421880301380701065004101804d40c0c00d13000b54400c2d2801641c4a059240c510030b1048034171008080e60341440410404109203503070b80c04a41d5801c6031414a602c1c0580300040050001d440c02070b0085020a01d0940c11b1078000912040382035224440090300c500c0e883c0214182c8114401c014018081030244a441b0300703054000c5d10035070f01104042c203285030701e6114203401c813450340903402901e00c091400b190541c10046540c208205151411811100780e40e07101030035285c80c094020448903800400241c0c03001c403000743c102c007130050207126182a1080c2c1600b10040d40280c04c0001c407883c0b01100000e4500200c60074982c000003c0c4c0d040145803131410410500a4000c9440140645000c20007500166002e03c1009a26 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 214783201 1250 214781951 214781969
    0xc0a08010e070e010e01030b0a0906020307020618010c140a030e0d0207090f0614010c0c0510020a1a0603060415090602030a020c0c0103020c1e21120601020a020a0302040c090b0301 79
    0x70403038032004929110107a8405035803640702d040180488402d100083c0d05403900b1002080740c0340c941e4030340078008004201001e0a164804018801660b50116842c0d00402c00060fa00c02c61300012482282210b8001d40c4210104291042c80c24a0b4403404020301140c420500340011603d040e2109241003d034603046000c0160809501032282e0980307441004030241c5600c9040194904100d200c0c03100805000c1d40c0e5043c0602c20401000308000c1501c400007805000c0c28041044807802800b070b5651220b44c000f240c0380440c07103035564102c02d402881140301d604000c0050a46441f1501c0e40c11a4800c968000351503540c5600d17941010551074002103000b4214074400607a150032840b0b006081c032500e2102c01e41018010011007100b0741340000c861001c404044001c840d061000c81c1d2070780c0b41090300b000102c2e64440c0c5003003869110003507074080c110000070b0308410311840d82c810004a071280711600000b540620034a506001504183c1d0050008a13941d04000004c0760b101d450a4071590000d178040400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 214784451 1250 214783201 214783211
    0xc03060c0a08160504120c090c02100b0414070c15020f1b0105010302061c02070c141009061b08090915030106051504330c02010e0f0117090c0a0801 65
    0x1080d8032105255010203c182185592108980010070314440e511503121201180004071060140a2a03610300034800210708206030004028060341316081d90a640301107600d8030100c040c0b00d081a00810915542c07125000401d030382d80e2201600d0a1a007a0801e4031640d400c007980b40c000780000e2000300004202e80410540310100d10341c0c288110103040ca08150143d041c24010801a114041613403c051000e1013108410652122140024005c2400c090401c000e402c60018506507440b81d29a8411819a600c541e400d107007503015035000415200300f00009141800c0c45880700b0071000c1d0311144500c80c1f01424540b01d80da2000401841e019036000e19610440030500490b032909110707500040505664a20b0a10f05005000030580520700c10301c0e16440c3c000100c000c1100b815144900d0003192600112002d0070081c01c001c00c61030100c041203010811010342d4036942d03d000441c0b04032800b416500c45c607600100d031038081c142e40170240015005100d1007011041d0390b526401d2510160004400010f2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 214785701 1250 214784451 214784467
    0xa0e100c1806021c030c020a05070f03020a0b0f090d0204240509100509130606080a0b0402030d09030b0a0f06050a0602060a0c0906020706140403020409080304020406050301020a1706030c03060c 85
    0xc1d514000d9072200c0c06540c0890000000c80c1c01d8403510203080510b45c10009907941c030068041c0c2c00d02c0c4070b41100800038001c038100130810180071004003054900035030710f044a8603151a0262010300c2031101810f135041c01401844031502d4070140018100d031010f0000703c0d011400888a03005050010700c048050707180c07c0c4003400541460b1043c00d5005850350b603030b14441c0b031400c0003051540b18050403500c2c082e55041c3c01c000c14459150803035001000c440c012100c11013500c0c200080d4418090310100e200b4000d00010004192198284000380c94202d002460a07441d804420780042142c05050580903495003000141c0d9903406141800030718031500500000e2508002c09004c0381d100e41007140034020f80f0b0f401440700c158009201c8090322240d08101008800d00f0b201000c050041c0d502c001e50181c01c1c10703541c10400c100d10740694090b40c42a90148480d549034003c043c242c0c040d14200c04009880c00101c4410040100f48898215101505540760030b08694046410031000f254841d8510400150040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 214786951 1250 214785701 214785737
    0x305190804151512060615110c03060115210204182f0c07090f021803010504170f0d0e06010305150c04061d0d1412040b030a0e100c 58
    0x2240881d50b0b208100a46681201ca5400544042c01400b800d0403000b41d0000c00c000450307005a019001d0070f2000111440c4654008040555041900f1818062003000c0541c60138001800c2e81684c42d02104482044d071424412200b86040e00710101c29681c500d4003049954610340700900c060070581c090480c24001c030714a000203a412900b02100d6200c54a800190340174200d0501051020318880040e554030001c504e26450800c840e004890214500502051054003a50013003804008420301040c24000000030103080b99821280900b04a03d814022620321b0303440300061022084800d166814a950100c6150440d41d01c000301c0b61069001c5801403040c44000c0000d51142d03480c041d444409480c04034096041760003640315520902202882f10440b0300300124030000d44042c041c140100b0200c0504101060a1540c4590358483c0100000c151814003100d0841d41039429503c1c5003407540d1216052000203103800c4040308041c1c018030440c42d488620a005081801c64185d0f200f002c0043d000c80b4003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 214788201 1250 214786951 214786973
    0xf12040305030612030f0f0919080c042901030b010522081e19030903050a060507030509160b0c03070209040606030b070302030610080603071716141c0305190804 71
    0x184800354014080341b02031100301e208035a00d0348903040700582c45060745000f140440e000341c1000c0c004504951800310358074600142c48070941000319014040f40804000c02441c10304815105032a015945079880c40a5002c1c0e0850b40c0b100c1d0b8103140c040c1c60300e00800704840d04d0321080c0428640f02c440c3c2c90b000f04030a07902040510b40c0030850300000f0b01807000c1c55521540e109030411640c0110400c0a0a00c81810b0143c54460010340d04181918021501864404000d0804544d0200801d24007408200d2000300000c182d40c014100802e0700e0305032800d2001800355a00202c010000398072080100400507124000c600d8000d92056201023085800c602d410410741000800d0081050310500400456070b0320943c0e50f1690304e055040428050320b85601090800b52242c120401c091001c480f8091034540015101c01c8502d40c4001c0000c040d03445040c11001c2d5000e030400e0542c00010802005074044114a40f113a0540c400e0800520741381070255008014003002d44060040780c0c0308001c00c0b040c003a650410b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 214789451 1250 214788201 214788229
    0x10603020a05030d050307081e040b07020d1b020d050304080a140c090c090609150c0f06010807050108071b0c0306050402010e04050415021b0a1415100603020f120403050306 76
    0x1d480c01c04d4101c4401880e81c0001000e0301c00700013032140440d8000d4022a00500031100f172a2440010303241c603040c1401d11940542d640c0c8014861028201e03100c61050388171850031410240702c0002c480103a02040380da48a564010b0312140020800000c00d8201084011240c510580c480380350001011040c500740100c071040c103802906858100022000700f04100d5581c10b904039401900c030300032400403c0d06a103202c0c07050340380c0400004031054070542c0005c60082e454164402c5902c2603032103003086a20380200380715040c0403c69032804510254003d42562640d070448d005010020b082c0e80d12480d1860569600a5800a40c0c442c140025035912500b00c1c9107296068400384900c1c182590ba40c5480d40c60f2810b2001003c1d0701041030402400b44100f805440840c5c01d084a19038515410b011084507224420b05801d84222544c0141444040c1710705403003034820000e802011464800160b01035400101c0010081800b005181186002c0000d82030281c1d009036200c64880c940384c0d0901c4008101c0d200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 214790701 1250 214789451 214789453
    0x110a0603020c060105060a0c06050a0e01180503070201030c140a170906040c0302130b15030105041b09060f140d0605091305070911040315140c0c0604260a02010603020a0503 76
    0xb052142019000980504441044d07a40a5a0315003522049862a480710304c020034090401040c4820110a41c11008100501d440204150b81d07107800280f02c0c5040c680c2005089400078444038001d9030003075000a9070f075845030501c4040b04480d6001c00009600101030240864107442901f403c010300f502d03909500141d200000c000c58240b40e1909450301e9844d1000900c9201c0d28440659482c08603003044024000c090554044101c0200040410350000d00075030380203510f802540510800300541e8259108000d80301c81c020141001030841d084c05a40c0b114406100c1108034101d400404a0f0040000d10210305000821905100401c10842c802801241003c400b420705080403c0010444c07004980e01c1d1400024482d0324180c1c4007010b402264006011000540602082460a80c02401421509045078481ca43d10790121980600840401861a41c40040001c0005440c100c0100c01d075510014250b0101c0c004240c001d0266102084030340050b5100d090400460410012030350240200f10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 214791951 1250 214790701 214790707
    0xd0f0b01081b0904020f121b1206031509060a050c0f1803160e07020c0418030c14010e0d140f19030e0703110915060a030f0216110a060302 61
    0x82580601400070071442042d41001d1a001070359004076401c2c010050030640d121443c00c00c4050198000012444803080f07142d0006940e280c2c0c40c00400d030102074000310b040c14614554071040b8200001005039416101b107404c82002c07000200691380c41092510000e2a0711310b0144030780c2084c0e46002c0d044081d419000e00c00680310f5107289068429a41001d0b0007403000c6622180001d1070700c040520000321446c4800004620150460b650350f110b10415002c0b22110180401804102c9880c03056907180c1c01000005034001911a520f81c10203180200c4040c807015541c83c0c1c14508507a03400031180c08075070280301c18034907582d04000e02c0340e044c0300051006030a010303000343d401100d0721030301b0800b008050616030224510340c005d42c4000304642144040714010758507440d0800c110360012518621891036000003c480d0000c0940c0098014400707000f090600312a404280c0140110702d80711078039a602840300152041c0c2074400c006030180150580385490b5051014001500c2d80394001d081014010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 214793201 1250 214791951 214791971
    0x4050c0907051b070308070f0c080d05040e060607060f060510021507031d0a08042301121109060309010b0103110703080103020621150114090d0f0212030d020d0f 71
    0x88003d55540905607510303007103090f20241c04282482d099070401032442d103010845805222541003061401c0f0311520b0807001c0a41c50b080000c0e40d038203895404000040f001c0106200444400001c103030030003c01b07068141844030b1640e8140a5402d00892030700540d6846204100d41e1900111100000505001820407003843d980106160a001040c81c02416203607071a000803180d4440080c010000502e050b983c400c4090316101140b680903116401d80c00d200010354010070424580e031b10111a030142c41e050b9200710200d038403802030803400405034801e042c00e2000c07085540fa05001584550443d80000072030f510301ca000074089440039a5100100c02d014403003040007907084580c042c1501e03011a0b84a80311103202900885141301d040301d000c102d40070382060203084249088001c48004003600e07034030440d103140f1401d8011030041c0b284903640000c1e1110041c01140b010038004445600107000641e00d6a90310044525540c8500700d070b00c000503400640c403004071003184541e641248404c0004c7c0710324440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 214794451 1250 214793201 214793207
    0xc010305102301020c0d060c03050117030a0e0102030405030307030e0907050304020a0303030b0621060f0306070912140303070503040b0c040b030103030503070309021905011206060c03180e0a0504050c0907 90
    0x80407100d51082d2044014125a00800c134401c00321a0091415080b07010500c0c004029000030f510328800300b82440b002140e0001181c411400008032a030095051605440c012074040c4041c070015419404100004901e6403028030042c054580079440d074889503400c013401e00c045603000800c0001041030070b1081c4401a0360310645d200c00c40303805180120f04880c00c80009030061148440a80c03d0300c5124555001c070b08581c210a92164074200c07103d00c50058620207064640204566100004030b02c070400f4466041e51301582c4010500038102c8404880c1070001003442c5034400d4506c00c001c0395000c4104400c103c0c401050301d91001040664074201460501d008003103010600000f024090080000b4946038031039800050740da0340082c100b11300004101c01c003684000e039a0240c0d9002580c24040c503c2c000d030849c042c54007211910f59608098042d00e40301100c0603181910640c0e4402c1c48460005198059450480c1c080c4140300000a0716003014034202e486c000c1380401e07a90007548094100580b140e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 214795701 1250 214794451 214794479
    0x14040f1203050421050f010c300203040506100b040501021519051005010e0405040b16170f010609050f01021e010902150901021e0c040906060e07020c01030510 70
    0x4880d80c051490107240a550a02954102004210b1080741c02d0101e00f890304102010140110107440d400603241c40041d00b0380720841511700115540785552200410a100c13034102d051b1700e0586070340340041c2c00550341040e80e206a4065446510003000d0180300c1078240e800d070004001115246144c01e1821001035110b511000d10200e101000d40009109100c00344402c410180100c0750130041e0b454500030245d19040c250203120700040b2055203551490905200303250080342c10502c903411036555480c612104c0c6c03104a00c03600030400001e1903101d00c081003200f403074050301549007541d0096040290003804110300764031040c41002c00b181e51481c03590700441e801a81540c000160351030b0b25442040349015003032916000390003285110015550440c108090401c0b69804d03800e8860001c1000591003400418620703001d16500200e015698600c0c099100301a454805e080114882d640d500902c0d42140c0210740d60409030308518510b0002c0e690500c039499000e0f06069110a850741800072905000e2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 214796951 1250 214795701 214795709
    0x9010503030a1403071e0f0216080a11040b100804020925030e160e0103020a0f03031d03010605040e060402030616091a120103150501060201020313080a030605090a0c14040f 76
    0x1007000011517105441095801a010410158200c542c90540c200500e076000c0400524014007a0b60099100707003c041c0501c1044511400081c8400da0860702d444101415040c0c45c607510940c0c0e0700c401ca1454990403030880b25030b05142c0360921180707020b00520a00c7c01d00103062018184169914484c03d100c280e41c0c46901c840a45000682c140c03130b28000c5440c044207103030030064001110a00040030107056018a05880c4203a48110f800f40c1d440940084581d8940001008100c508048000d40303428058956001c1200074000304601e0340c0ca001103011100035440740c00301600114108003d600f002c000c0310760441d844a6544a01250070800109441e405018100524086640d0250000d0341942170743c00409101e45c2c03080c41035a4034500405000854140300c641c00c1e092800004401e8018802d1f07a10507840040185002c10955882000a522402d10b81050680c0c0f0341c0301041d16250300c815140b081d047d2000010341c61440071800340c06401c200703101c2d0100000801c028040c502c0900c1d000303000c079 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 214798201 1250 214796951 214796987
    0x6120803041101020c031006080f071d1f090b01030b0d02150c0708010204060c03090807140d051009051b031603060e10050a0f1404021807091d0609010503030a 70
    0x2d0001040100d040080002069505205101600941801ca0b5000c81c0440d400c0c9000c5445029000304425110502441a00da003582c2e0710443d001c2e10320035100040c0d0b00003050084001c01a002d038824803100456501700c40034455445459883c00c0d605071103010140102252407030280395180d4005082c9821003180140c0840c00428443d424540410072140a0000400250745880d11141c00030b182c8240440264009040e421000030410404100f80081e19170010010460a0101c0306101150400360011030780c42c41000070300e10314000f00c0e1281d0800244600c2c0980700308000700c41e101001400c98031040b4071075007249030000d0b040301d41ea200b650103da61208002c01c0e561171030900241088014403a81075035908000c100100a041071f4080c0c2825050f60008020808104c04940b0b0b84500443e0025005401c03e0f01c41c2d00008901001c15a20106070725141010a48074201000c14402404100c0a0445072000f8401946030514449000d03000c00d4005504040516030000c203071520400c0c4032052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 214799451 1250 214798201 214798223
    0x17090108070e0f0f120105090115151202031005060a0c15020f16060e070303120f02090f040906060f120b06040209060f0901020717060702010605010813031409041407030612080304 79
    0x29101c600000c040040c1e07280c000c110708e01d050981c540c080c0c03200344221051040d407100c012810b090700e1000c90009424503656015080312903507041c0300a5102503c16500b070f10491900040340c1ea501401003080000c542d407030700c4298000d443c2408440f490005c0000034a8014420010302d1400c01c0240e50300f40d400185000b049503046d09116004091417910903840f40a450804014540c00103141780601f80a240204403280205010380100d020b26126103501c1605511000c5081ca0603230041901140182400108560b5400004800c000694041d9044c04880624a07040c440c02d00042d5900c4101500c05524104402002803554410700601041c80b0301c0220362003034503074420041e05002e001c01115000004090103070007555100215841c1d4019800c004000c1169441703030340c40070301404000e264005003010b030b0f540a0719021040380c1046070481062205130030302e84d120f004110300170700c0c40d5075124254184048c0050581d20543c112110040c0320081500003c0c90440403039900980121060117 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 214800701 1250 214799451 214799479
    0x9020c3f0c030a0c11011e0f0908010515030c04061511100204030605040b060d1104021c0203010f0302030708190b0c160b09012409020f0717090108070e0f 68
    0x60a008455a04007103200c082101509543c2107001342e050310f40200085005042800e00455281442410004000614080030390401e030040c1151042e014003410404181074a811489003110801c540d201243c040151190b03134030b400c050198000c05002034034148005410040e5130303038100384448050401c200410402965640c4c06021f8901e40510404003507503615a00d040c2200504016941541e1222060300412502e1800c1e816031114550302c02800c040e90105503080000030741040640300c1461144a03843c08191a4520085000e41141c580c41e0042d01e0450040c0341c03801d0540d40100c2c943d6403040d0324100e41910712008403251994032007150166aa12025000c01d05d0003003010b00b521441c103194451040241c03441c652440350b04804020007407104d002c1140d001694640c56482c0d14a020ba060500c40c030741450300240501540d10f9003451034040310740c0d00c880c000605c41c07514004000c8042a01840b96902070708007a0440603510b0018081880207002410b40f85646000ca84030381c42084500b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 214801951 1250 214800701 214800823
    0x160f12022103090312091507020d030b0f13020a11010e0d0215092a030307031d0609180907050312180d03020c010804032715020607080f0601020309040609020c 70
    0x140c003c07901f0b140504a24200200041d56801c1c83c1485080801d043c00b1700c03a401402c0000e0140c00c40d14005100c10003945401411800a500c6042e5420400015046c044405582401140300c071408050003014012542d10307009042c101ca503820403034602c1c41e00c818000c3d4018001400d030782c07500c4404403c03128a0709181100e00c00071096400c0b40c0e0540004a00c40c010305400000c1e00406000980112102100b000100004d0384214406d030399000f040c00442c03115000007005401d82c40030040d07088440854948002a03c0c00d10f6064502a9483c00000d00301e954010342d09080c0002035047d50380c0e008100640c0d4019440d041d1a00703240381041891000034041c036203e0051010001e05241502060752000e50300002e50f4599409000400844140d00800d01440054a0b6110b01120350341d1070100e44402040d2440030384080c0115046100034001800565200d1140c0c00003400ca500005a440682c00c0215082460076207aa800d4203001402e03800d130a21000303841050011000010450010074100c1310 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 214803201 1250 214801951 214801963
    0x8040312060f2903010b0a08041104060e1905010b030103151e0e07080a080f0a03060801021201031a07020d0f02010906020c06011d0903160f1202210309031209 70
    0xb861400350a118002004800c04400c840040400801a80b40c0b4850156014442c842031142e130724002001c21640c44114816801c00e1740041c81101000c0345686002d00043c142d03602504011a0024040244201c8082c000600c03402201d03101c2e0207001c07961408030305110f5400144005071041850303040e0300048076031542c4111081102e0000032090928516500307070080440b00c0308a0b0b80c0d441020404036640c0000209a640d131507000f6509454002c800c140c09005030018040c00c02495100d20020600000a002801d450f0001001c064600d43c50340c18052025030081000440c611094001d00482d81e501007507140c0c85412600b01031b002168410380480c0144a280b5002d0102480440d1a810415011590361704031006003900d11840d400711284400c2d001e9003641c0083d83d40d03200b00072607946603a0100915282c14080c080c0840a4039150f2a1b014120602d4a030303180c01600503900d803000103501070382000407000c1c0030100c19043d8a8003d10055580c4100384101c01c8068940c400a01406010080307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 214804451 1250 214803201 214803209
    0x20304020f090906060a09060e0c1b0d1d0d03020c01030209180405071d2e09050f040201031b020c040e0304030f06020c0d0309030507060c0311070503090913030804031206 75
    0x19402c042c944081003648564060f0380c110720071141c5000000b40242e05000310001d49003c000348400781c0e182c2c00030380d00c61948444001c580d11030030045480b0f03100d24280b012000009903611081c44621249840c01d62403456031000f10302c40c030700c60b109100100b0385c0022082e12811007070074010b80d100e00c0344c00050040c6040e01010251444035404000c20440049421821201f62008080784000210400c9207a00b0085910704035180549405d07003500001000c0001e5091803030001140216100c03001c2030292242140c1d140c140103400380500c030071542e151284aa0340d0b0013204001302181c018080003910340c044070040d40e00c80c0b034503034405e641c64034028030844d0019a0710030401401e0030300318901280607400c00c1310a24943d000c2d00e8020110305001e4000c01811a501d6a01c0720301e800240c1c0c1e6020020718001c8000000c0594031324498107003c02000c02400c401b802400116119907011b0200200740c83d004100111404a8100407000250081d2910f600107506050010803821a407071000c00806403584 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 214805701 1250 214804451 214804459
    0x20c030406110c09061c060b040203070c14071d06041103130c0b1306030e0a291f0b0a14070308060108060102060702070b070318030303052508010603020304020f 71
    0x20300048a03500018102c046801000c240d88031611a14108000010700b2550990001c0c8411700c010011b8208414550f000c034818140024028081c03400b04d8103d0300100c400d2004541c5820007031003848503c44c13014160310741d041c00510301d150070448c031b00383d080903d154080d00006c1c106000c904103079a29004500d056078000c1d4807944a04e000003821900315044141074480c8543c0c03107404100050340004581200c0c1c010800003100520307122040b40282121420006940070390700d600000120040514081c14691100c05d4400c0c116110f07098407416001b030543c0038800e8501c031190310000e1750190302c4801c0b5092804000c0d12086000e800380d4116072139004140103103900003050400c054104954a015000aa80d00012950703008016640c802040e07038800302503400744600f00080300b280710041c0b0044d44a80340c0100c80e960302c21456607410b40f25070000c6012039269002c0010a000c2c40b0680340100c81e000020300540b124144c1c0140021106000d04000c041d000000030b015515050381d1a1401c000c0030b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 214806951 1250 214805701 214805707
    0x60e03011407051309050103020312031315020a0210061a030403020a140312070201090f060b01140304080405040b060a170c09190806090c010e0f0111030316200a060906020c03 77
    0x40c50003803d40d440007848021984482c0030102d0480b000c1c4c030600c0d05030b0764050000d00b190b000c0c00a0f11800d0f07400c024002c1014030303141000000015080c10a5400e9101c410038003503160b001c17041010341480486e00c41048520720780102081030301b207004820a41460250310550307070381c3c850703003002c0f41460042d2101a180380d8000b81d560411000000c01041500304091032035105403107442c03049080e11000301019083c03000ca245640003050b040e40c03000e03440c4001414110104000c1695400058000f22003e0b5816500490304000701e09003030040f5000c0307840480d61949052445400506650103d902158500305038030005244a6070650407a058030305d00a108001e68031805d0703200341e042030060150a685000c1c16000c00c400b85400101c2600c00720058444900383e011240a000d41094140e45585c104a0b00303c0c102e40c50a08240004d41c045d18204910403060500e110000d000000c0d044000d84074840800070300620a400421200192035001c05d02140300c443d5420448045e002d822241c2d00c040c0000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 214808201 1250 214806951 214806961
    0x180604031109010b090117220b040c140a0303050a03110403140717030a14280e010206040804060e0a0b22050d230106030501050709031406010609060e030114 69
    0x80c201c001034241c811510103500ba0b0300e036032040d40c240c010f600010b8080f030f206d10071500441e1180d0525690005401c0c0364030342e1011018821417001c2c00c0f05001620354010318003d1006002e000303a00ca001070840703040a00c107051041004141102d001d0b21002e810044082804030100c3d2103034200d400c0310031864075940e88803512401c003022064540541448148144580000d41c03207090f115010001d5108400343d41484283d1340c094902c10086040c9070b00381c0d2020807000811081180d050704920041c85600c5511070304040004e0400710354030400c141554401c0341040f000520580894042e01c0440c60450118039550021a00814160300040d00c644008244140e160042485458500740c03c0010000740b03d540b2800d001d818254a00f0191038602030032142c44003115107001c20303071480e030884c0d0000840641d6070311003a0031200d0940740403000941d412010010300c4400c00c1c942e010701388020087c201c55450b010000d4025081441903405014000100b40001c0e6400c1d0b00a014000d407001c2e0313003204e030300d40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 214809451 1250 214808201 214808213
    0x9050601180e0c01050406030f1d0d120504110d02120d020607030b0402090d0206090a0305010606030f0e0d090e07050f043005030a05130503030d050a06050d05030403060218060403 79
    0x35852044007503841d0502c0101d080c00c00294501820b101a140c040c50300341006012009825107034400c07040c0c2601d0340041001080300c1102d58490b100980043c0c840c112103a1b00080000420001c0e58646604043c00d001c04184205110032440f50110341c82581c0071441d2003c00c05d8034681a0b4104418002c0051003903d40d44c010400e20321440b5641c1d010451115a54108012030180b1803075642c1040032440d850006041c4200242440100280004c1c52296a6a1420709450140d00078000081e21a9010000c100d054080ca00d206072400c00501701281821500804003003081c440c2916140e406404a400f05009030120f92408a01d031004982d00c40e1900349540540d0b400d881501441c0003a413410003880c002084030f0308207040d4440051803a241c04414103c40a8101c295000407aa4002a0001d21a80d0420007811b1480c0428400704d05840c09034000707422200d40d40e10507405442142241c00c0041c1d400300440f000e580e4007190043c5c503400342c1862a407030385440030a11074002400140200600c44 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 214810701 1250 214809451 214809479
    0x5092403040c03290a0c0c14030c0606040e030304020d02010e04060608100e04080a05130b070b0433020d020903011e0f060f06200618060f040f0803090109050601 71
    0xf00404041d032400c00060781e599048030b502442150304104410115500450542214859070000d240c00720001f800d540310280701c0200c20100c941150301c001146140340c0010300c46e2540c4400c0440f42000600d49002c0103030303102d102c010f000a2080c003a02800c07004680c0075040c01c0902c2100900700700100303a200c410103001d2410548141101110b0303a140003804201c09581c05200d2030740120210f0410103442800ea405c3d811012107105d00012015000c01d180d64698007610390705028040400355803c1c18204400680680300d1201d2100301905e00390f235889140020401031042000e94016910006921040e0080c020068a07542c5542413004003810740c821040b41c1ca00700d400382d8004200b04070302c00c82118210340940c441c030f001c4100741110070045213004044018403c6040c845201e010a4000c4600e801c01c00102c6c1e40703010a2000d4003a5260051041040300d034051312010902d4440e0415484051003842d8158004044900000025001820a41144d044a6070200845038a03507102c3c40b4241c0034038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 214811951 1250 214810701 214810703
    0xc0703080108010e070302150d050408040e101505070201030f230a06060905062a30030c07050709050a0f0c03090309170c06070807060b1005092403040c03 68
    0x14903258008a00b1020611600c00c4001001004100b03440c590303030034064503980d4481d90250080060000025402060041da4031540c41001c8003503a407801c00100140303009001c3c202d44003000343da540511411103070008060914456003401a05d6040d90f100481c003500700385020208882c01e005200c1c100d40001000d0740d8000c001c9904c00000d0b903442c00c0445003190300a00c252000500944410420382c2004001010184403003109a4140c1b000316405c68041032005290b0035031940200c0524500c040b0210b207485245100054250304507258501440c1e0fa03010107880b0341000c0d000060038070108001000302c807005001c031140038800c0c0e01c0c00240c0e280003000680d075510030150801c0f210440151203445004103080d41529206d03216814041c00c0d0001e140407104640c0c240c4030b0107854441d01da07550000b82803006c1c801c1c0000d83e525245864080c098440c60385e5101d0140d0314440038011182d4200064402c54001074444500749610034046003026164a440a081668000309100c14070910461000641e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 214813201 1250 214811951 214811957
    0x50303071101260606070303110c06190608103201140a030b0f07023c0705030a0f030e060d0e150105060a05070c05180103050616092702030c0703 64
    0x15203d00c803100d070241c5100b5003445840030305034000a00c0e5242c607a01404c4c1c00350091800203131600d090005da4540d41d101c44030b40d50300d41d4000020041840c0c00054202c06102200c4414083c9510b840c0c0550756807010018544c0302c0b20307103502441d446480b10440b914004030076003260302d0f007003c00382d100000440d1081c000c403c0301c00c0c800f0003008298144110b031a4102c9510600d40e80455a50002102d020f0101518078011400740720700880a8010040501a440044c0070301e903444001c00024004020107490584001c03a001407801300455600482c0d0000001e41041b02c05c0c0c40046203103421504401d40c04651544080046014081990954850003503909140211a03040c5025070408418200074480d00b5031101c81005911315081c8514050031000d80f00b1031542c501c0c1905d03600010b840340024400d54010480c03410040051110400c116a0011001d01203c0d10800300844000c0c9940c0450140140b03060f041ca41c150880310307410039004a8044400781c00c64407401c3c00543c801450741b04140070303000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 214814451 1250 214813201 214813217
    0x608090607030603020906012303011d090d0903020907020f0d0905040f0603022b0203010501080d1b330914070b040f0e071704060f06080d1403090106050303071101 72
    0x81c09000b072281409403030300106000c03001c0d40e41800460382c4a13010301800c9002e0008858000039011142d01440c003034400c6424020008410f010041a0280020190341c040ea105422184009821016a0050301c0d016030b44151560303103408099103040e45081000645109104d01e20314115030164242050f510111010f00100c0c00c9204000c003035408900010354051400581c2e404e40091a060710056040301c104400d09540c0e580c0c00090031924243d11019451300107180121a080e80315402004200c4410082c103400100c43d201c54030700301c568640011101c0480344c003011942c00504d18425002940d81d0302403107100c0082c80c0445000c0c4141e203412006100760361022401a010b54140c406075054040e1541c161460f2002400c03000401409181c14442200c2450840c44c0c1c107000c0c1c0512450040d2400305481180c1200c0e4400c0310800ea000700003d030410b102901040d40e1080409090b28104604a601c0c3d031540256540188480c0e8401c1d41d0500c40010f201003000074058040d40d8243c8241c0b03940756 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 214815701 1250 214814451 214814461
    0x2030f04090501050a091a0907020a050703060902120613030e18041101021b2b02030304090e0c0402040b07030f0e030d0210050f090307060504050703020d150f151406120106080906 79
    0x641f01402011451b82c0c05460015025007045072040d0340c000c05500c1101c0110700da80d00d400d428600a60000d41e692a11034a002055007891103081c403081c48403000903d82d40c900541400e2090508103c01010094a0708441007566640411085540c402e00824070250030b091034040322600c01c480c14240035000e4881c0e86c0010076201c00781401030750006003000ea480c2443e82c101e0150b103c1c406000d4060f510111034508003607102003003d40050100c00c00c0010703a032905c1850092a00810700411881580104401d025424ce2101918106070303240c10b00503060000040c09071152109020001e8042c400c002020f52f06550002d60700c000e02440500411864803030350141041441c00b181c3c40c2115074810048100060550751205a2240c01401a203803581e44035400110b44d030082c0541503402013480140e011403000203110f030740405454860300304118000700f071305503803a40c50314402d03040004a0b001c0803038500e4540a045a0401200c50703061201907864a5020b49551015030784d4000303030710039000011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 214816951 1250 214815701 214815719
    0x30c080f0d050306010e0d060204030501140709090501120803060409052a19150908010c0504031401090b0613020d0f02030907270b0d0f030e1e060a0f02030f04090501050a 75
    0xe40542c20694542403040011410b07c21000c1c0b01440884440c0c1e4208400404100e085c400c03009038140c0038840e21581e0500c07041c0104088110741051004900d40001001202070358003440c03511980c4041c1c15a140ea9525002600030300c0b19480190580c06004aa40460540026000c1c284c0d806c0382c0e50042c40c0801c031000e20a800d4581448034004d52140e4105005400e06500c500400c840e25180003030f8903907129450242951480d17207400000c1540400c007401009003511060360380c44a840000c10481e000381c2c9581d4942c0c580541500c1c095240540310130702c5200613404a0390340c5d00c0c10b01014040c08511030b01a030000d60044482401c903002d001d80101d10b15140c950b550340c2d04d00c0921001c02e511191a4050340c000c0420b504296803266a540804001444032805400303400d0080e264420300420741e10901000d070040c00114142c5402c214905081681e81806552203224186014003686c0200d80e4286d2862040d4244101c0484c008240004e034a41c03260003590580350103036035078020583d94800c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 214818201 1250 214816951 214816957
    0x504061106040c170703060c021c0e010905060901140711090702060108030901080a06172d1009060603020a0305010204051318020904172107050909010b0a0504030c080f0d05 76
    0x10f103501038402d0200071000450b018035489800b6601550855030742c0760b864100311000002407001581044010040200b5004405200e00c5170a091a6044000074000284001034501400348030b64000700d01311110b070b44607210410f1884040b46c0c107259600e10368141081c0d007102d0074038410f2081d007503071000884440c40841c2043c1280c00c220025800c2180403001903d1032000240303820001c41d03072008001800c098413040d03480c5142980c1c0c060512a880c09500184891b49501039100114a06c251503801040004003d0001040c0ca0390014060141c1d1903c0005805994000703035001d144000040140321040d07000b0b004594003110b100c2c541c801460250070075210341c400382e481810310088c0128050b05100f142564054030904031040100749081c1d100031203400a803015074540055842d8503003090f0041c4101c3d07421a9982c1449810420341900140c24854140500d4001c01350101e0102442ca0040043d14013955001f0001d00200c1d072030b041c41d03c0d611460f4141d2002903202d0f00401c044040c0c040c00c12 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 214819451 1250 214818201 214818203
    0x6090e210a0f05070614010e090601081216050c0603011d060102012705120a020304140d02100f030902130e010b150f1c150f0f0602030307030b0d0210050406110604 72
    0x30240400c002c144162015008000207840751034464103071500b0104c211040c18068001ca210355446405e003a2500b9141c00300582100c031184d4004c0100e040c903010a1002d4500e075000081d44100c10418a1615500304107500c80042c1c1c01407000700010034070000000503030803401c03c0320b82c1c864800c3e502d0000480c03d0b946a50024903071410755090060405001c601640c00c01e50017034086914905240c040d14210b541f0142c4017200503040031405100d131108010402215040c100e460380f41c50295900080c500b20914485142031206408140c00d0582c081c1c3c00100340380d900141402640c2d8600d0820102034450760050000c29444e050890a040c0703011450200c2540083c005141002d002c0b0010300d03120340c40740c1000402c0c00c080072003031403a80485019908000c0f13480c500c003010345841e0402c0101e00781c1c420381190717031002e0950b0340500c40503034000252907010289180215181d607900c804900f040c00d056030080d400c13040c0c0b110003503403c903048402041240d4081e0740c0d1000c0c800c0407000e01600c0305002d5070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 214820701 1250 214819451 214819457
    0xf0a0c0815010309020312031501020304051804031701120b061f050a030b04060902040527040201030c120e010c020709020906040e0a02040b0304110910030b160306090e210a 76
    0x401c1d603040031071205101c4014103041c0003074004507980020380b4003041182e0b000155a070010400c280c3c1048003034503500c140c100780000c0d0300b85414200080c0200303d0b0801d00e444006940d200280c289441030581c0d00c460001c0d5400d214807561200c0c998072a225841700c0a441b10880d143c08a5410304154070f94400f0a485140c111445c20140e42080b529544100204000c0603141c5201d90699a164450b220090045000050744c5601d4503060002c4248000e5182580c4034580c0c05501c01e40d20910707000c0c0c2e8072550900e00018800e0308600280d81c8082102001a10f0354681039504050840550081540782c40030b40844502d01d43c0d131035620050388102c1d84400e070807140c10302c01001040005d00d820f51700b040103031101504203900d66606c0111504211010b84120510801007006824120740c00c580105428800500207821034440c0c0b001d40b08068410800b6101040202030707494441e9004401074000f1060910080d5140907032180d89005041481c401072102116a44c8504243d400721080300c06261 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 214821951 1250 214820701 214820717
    0x1202012403030f140c0f0703120503010605030f04020a031e1407060f080901020f0c1b01090b070212010f15030c0b03040c0e040611310e0115020a060c02060f0a0c 71
    0x110b590200ca02c0070700784e14503424842c1000c01e040030b1105001d81500d810080c2202c03451820034441e5407440d007009005000e8100b00501001c1e5000081320340c442d14040940b09252683c0c40070a030840c04c181e001408000b00c00380c4500d000c0d140400d0020185000d60a02d0758150a0000b0749901c503011071199002042d000034070400c0b0306014142c0386903c0a51180011300b415002102c0740c94070340c00680c1d80222504900d0411045031180000101042d81c20700e4400c582508001043c4010f21a00d05e010340301e008074007125101490250460200c2e1089414103018840d00003403081c54140240c04100d07000304044030302140c4c0340c002c0016603100381d421074240807110745489050007400401810540d0260f031650283c049460703901c0000c1a11265592152205441c01c0302c101e0041c516041682c80580384c000800c00c004003800e02400d054680301c114040d45101200c8041e4944500f500c00207009904107040d41030866000711344070703204403070400c603c103401d075611440c2008a540c1ca841c1100410f0030781c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 214823201 1250 214821951 214821977
    0x301051008160c06090804030305041701020c0a0f0602130e06120a02090402040c180608010608070c0203070e0705091801170a030c1205072003010f090b04080702030109120201240303 80
    0x44420f660254003903440011505000c0d11284503650082c1c10503008030340001003c0001003891901200c4803242c1d44002c41c180030a449590380c0b80e05903054007a15084214410000b031001300c0e4100c503d99419501e100241d81d95030b80303000300c0c4d180c3e08542081c820041001c000704c446202041003145994000d0000165a0307484d82000010a0071210b180b00304070f00c42c6640080d025503851241e000d010140c450400075803400070000c0c00848001d0500741084928032241c4016100001c5070010354004001000319aa2541c000300c075207000d1030644c2c5500070b82500c0720401020407070b003480d4161507108070741302d405011015001d540c400c41c0e10300050000f2501950440441d41414100c002201c282c80c001f440e0081e81d45602e044546201c5031041c0401030320244100ca46400d124180c5c03102c000000c14400440c070f40c0c598481c3c016000704040e150183c001200411544e013948206e070b800d64402d030140710201701200002c2c02004030055541c1200e404403440c1d000c0856080118003200d40c140c0c0d134880c2080c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 214824451 1250 214823201 214823207
    0xe010221100614070c050303030c070203010612080334050d06090e070b071a040b0712051b0d020403050102040f140d0206090607050a1202160902030f010302120309030d05030105100816 81
    0x10083c0c0540d0000d4164101142030351f0700b440254040c4501128040c1c07100010700401d403c582c12a4024416030b10112a030200041c5003500741d9501071802c0c1c0c498002d0800048030002c4808480c03015000018000030020012900103014101d074a000c00c50400520f0340b2000000e08039495030741800c143c1d5220400800034176801c00c00401038140302e03159000c1040c082c40c0143c02990000d0b04c04407180c0700305000b000f0769142e0100c051241a1100b034000d2142d0704080c0071950001000d800500000c4200144a9020303140e0798040340c0c02940c1c0706008540e00d99135002190040c0007580100c0c802c0c0100c2101045282c42e003002034500e0150002c1041717250090000404c80b0940c04403004075014010700841e000031078411500281c1c4c0110940145c05080c61182078030745490080c1c0c010106480c4107000f40200b00c100c004045065079411303582d1074a01442ca2200c0d6185018400040d9032500c9606008007000f903201e0065412980141e4184403490300307074602681c80c3c2d10129100c280340c0c025402d2a510a81c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 214825701 1250 214824451 214824457
    0xf070206030709180507030c02060411100513080106081c1d1f020102030916080d11070e07021b030105060904021306050406030503090f0a120b07030e010221100614 72
    0x2904003c10020381e112541140b640210500c02182c565a004000580b03826000c1c4558000c468070142a0f11310301070ba155400000041145806003802d01d28072803406008800300c07400b0b0428210441001036079440030b64040e0405015211550069407504c60103c1180c0c400640c0c070902e1911100075085011041e034030016440300c0d425034008960f40c90803400441070f521100302d0182c2365001594070302e03020403494a403000740750a03200e541301342403001c00100a002c120010203101e14900701c03502c90105038020f80340103a2500311f9071010f140300c070030300004c150000340300420701188041c0012000c0b40c810406080700d40c100c8500e40c110802c2030000c3e0043c07900001034814041d01c0140040c1c56034442c1d010400311401030b00100c800da03000141034101803030000009010010704440c1c8074012420002c007820f0140c0c130b00f0802000e240071170011a9081e400394000d1600c01c50040021034072039070244a00050000d0816042c240302000c40040f0700e1202c0c0100001c415100c154548001004444401081e168 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 214826951 1250 214825701 214825711
    0x140a030b040b0607050105010e1003080714030903060a0e06010f2322060504050a090f0615030218061009210c0504061d13240912030e0c03030f07020603 67
    0x36903602100465555210f020742801c40c060000007503158102510501ca000700982541d54030303003414500304009410501222149603002c00c007052940d25001a0b2803031805400001a4580151420080401003603402155100c008034100e482030390380c0700342d003000419580c0280b0382c1c0c0104401c581c4403500768071811040b05203800f0f0800f54040c004840c440298070070002c0707141c540383d032214001c00c03440c9001d005c0c85400500f031000410101130596165551306800d501c0040140e51541081c0c032020301f00d038171408001d50300507201640d84010088141e81c101c4044400b035100b0b0100100400e0f01502c100c3c101c105440c80c3c1503510544030240d10320104c001424840480c1d40303401d55280030131140c489006035801840c000c00070040019505001c1203507007070000c082c4115508841214070104189481c520a000500502e0f0002c0401940d442c50180280c500090b00c1d903c000c0f42c558015a515905c030103107070403940f0140c91043c040401003545903c1a11001d908034102400380101528141c00219004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 214828201 1250 214826951 214826959
    0xc09060105190905030d0f11030a1b110a0303030e10060e01052101020412052506080411150306030106060915030c020f010f1b0201090201080a021b01020c0d0f140a030b 74
    0xf955a640080e2419005486000001d000d4000d40140140c00c07c885403034035035015000c1c501303002074410020300445100949141c840d5490191509001c00c0c100b0f121480707800070309400c0d2483d440e403c01401030404444200010310600c43c000c0001e18145c031948050340c0164030401256460301d010041c400790000500b0f409290400380c50103540800344028002011140311410794580c40d414068205805101068102c889060814521900f4400c0a2040d220981825080380e00c450a1a0101590320300320282c03c071658000c1050301d001900003540c800c000403802807100741d403a010104d031004014840e01c1020000e85074541d01c00d074007a07000803410b02003d204544050001001c0f117400c0d11804402450f160350748610052490544192080c543e4415000a001248550b40028038060b0300610103101c19a010600a5411241c80c040c43d844c010804020b41d101e0710558ae2154413500905003c202041d0011102c1a5860040402c00c0307445000d00000c0e42802004c010940150a0070100e66a03c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 214829451 1250 214828201 214828217
    0x50313200405010806090f03030c0301060f2106091107030203040b0f07050607050d05070503131403040f06111006180b0411030403050a0906112e06080f0c0906010519 73
    0x9a486038490a0f0003081180010001410140301c09070402508244000d119002082082011400344080324115490391800c959402c030441030445103107080f4999485140e184208204003842160041c5c001c1c0c1d0410581041000c0380100311055078814184001c02603001840208041d4102c540544a010103802c115450007803d40c0d1101e051070b030700701d8030000407410100d240124400389214a43c5e01005500b881b9245007014051600305104441c00144120700360840203031306c55401e00545e00240880c0c00c7c0f41c48185c2c3c403542d01030002058500865032520030902a1000c4046c00c2c081c0d901103031000c949401c00707414010310040141400224154105840b854044502d2540c800118817075402a0703107483d1101e001900042500d88035511802c1000303000e4000724883c00317000c6a14022929054201051030304054800503a800c06181061035941c070780040020060004205090b103141d00d00c084c0c9800c02d4592040240701e84081d906180083c105011080d1600e01c0d49210040d890250f04120031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 214830701 1250 214829451 214829513
    0x90d1502040f0e15091e1306050a0207020414040b040f0c0e040f02030d0305010b0f2101080c03060a02070314090f03161401020a151512051606050313 66
    0x402d04120b40c0c069a0000b00200400c100100070f001e403424051003c1302c0c590307500d0800d00032107440c4030f100014040f00344403c1e1004ca00c02d00e602034141e80c450f903800300040c04103142902c9030388020340010006030b01660501000341500886600090300c03669100c48043c2030340d151601c480315004900642212113030700c0703160302042c802021410980b04038440c0007441d0001045e0b206060070080d201c07103460141810035005000960007a01500c1160f001e80000640f42c05080c440345501c0348c2001c06d00c0307200716540000402d800c0070200b218841e043c010307001c449940d2200b04410040b48282100540000e0325031495102e400c1c090001802c003444014400015001d03100006070030410303008808189403d0a0408200440e11040c41040c0c500702400500340900c410b49800c444c04110b040e10301302403940c6031b001026001d03035894010013600c2030625180e214041032034a9943e0303810501850001c1c80c000e03c400190a4404c2c0100da02c00c0139440440c808900450f500e61a0f003400d102c0015148250f2840299 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 214831951 1250 214830701 214830719
    0x7080f0304051018030806060307030f110405030706020f0d0e01030608060a0b09060307030305030f0618010b0c070509160309050c040e03070b0112030c0f050a0b19060506090d150204 80
    0x5406540250054030310f10000614190456010780c01640c2c80e2980091041d02003600000703090742c480c03421f960841d40c90743c5a100403401130520800c12203460380750004514840c082900644150342e402d6088408054a555041e40d031945484c0c5c16200c581d021000480c038052084004007516072040c180440c0e11a01c5180e15810410212107070842c45a85443e840c20314a00324410070341004050f4040c02056096480c000c020744801401110402c070100f001c03078070a46a00d8044922452071070307240030303040d42c403003d105580d944160a0301149101d800000301c0c0c28503004001501030039403ca4111680d103d611403d402034590440c09640c01d010303040380c0d81450f8655001d01e1251807540809103948801c00d260a1401c2c0d08180c2200c3d440c0b94580d030081001a4009491401c05a006031008031048424604030f440d0002c0070100404810309002409090030030342c2800c00c411900603c0502800c0d032640b091041c00d0103070700360380c540c0100c1901114003c43c2403117240c001c0c8100c11100c0545017a03240d130403103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 214833201 1250 214831951 214831957
    0x2a1f0c02031b030a020609030f01090f050c1801030609051c0e040609060e0103021c02150702010e01080705040605090f0a14011b110103020f1b0d0e0d1707080f 70
    0x400822124600042107150030312000304501e0000486040c091050008255501d424010003405401c00141800712580d00b0040d215244900800a000358802850002c1d648071094004403407a2148111040d034902e005c0c440c40500d400503c442141071303071954940d000500a20724040e5054002c07003070321000c10b114116107844174910544807012188002c4040c00111100c82d4484082145030802c1480054141c0c8404c0d1b0440350100d0f050480941080c415207140c8a50b54030095001c1520741c0c2c84119040c1e04c00240036034034000d886000254110000540301100101c03500e10008600304000e2104501803405003441510180501074013107080c2000c42d25070309258000d00c031822404001360311550303842207451a020510b1100507440050f25170791041c040800450142c14143c01103100d002004510f0f040d1800050103490814080c10f8242c44961210050743c1414006982e03c004040c0c5070800100d042401980a00d165440085007419008282c110803400c5400e89130402207200441b2144000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 214834451 1250 214833201 214833259
    0x4021b011104150201060e070f12050a060306050a0c0206070807090b0c0102070b010b13031e0b0a0b211009031b120206060f030c040c050d02070303020d0b032a 70
    0xa616912818810f0b00c034031060100344040110381c181a070500c500310074000d55640001076810501d030b040c0b242410039994070b90040c00303c002161401e01002040b20b03030f0381c0012003180e0160500b04038036140e41c00351500740d40e0058038034400360b030100c0301091101e07114454095008200386032100546840d1104030301e16a0004c034441c00ca40c0c0d0080b5550301440000310759079005180c051441458100b02d2021204c0344160b038403001d08240c81038100c00307103a00e21640610748010f50221200005240c0001c5c3c00000784401c1480c2c42c007811034420300708000003400b840710015014441c020080001e1550102c0c001e402110400c5007000b44540020400751480300c15041076078132501030b100c811441520002d1501c0301c020401d80c42406031840c0121280c9021542c0c0c1c2d0501016107010030400d402500642e010300c607245041c482541300281040030301d940f5074060b01030b201003203405101e010802e02c101603075900700359010f81d4141ca40d82d0000407401145940841c400720007030020104a9082c02c42caa03092078686c84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 214835701 1250 214834451 214834481
    0x2a0b061903080702090a0b0a0e150a030f061109010509040510030501090b180303040b15030a020319060b060304020913031b0b01060f080f180304030c03030203041805090a0204021b01 80
    0xc3c0150451900350986a84064030301e00c1007100046100015240c4800c0f88500d0301c0a00050001c2260802e01c0200030a040101401e8101a42e81d6440e002240d01c4412030309440b164504404008018000e0007290341c00d640c140e48803401d000112080000914019101e20302104941000000042d42030040c00a010302403040c1c043c25140225920b441807000360354000050700304008020000c0d1204521039000000318031200303070118080001c20302e030621a4801a42c5442100b122000d0b030300c035a45414001c6885440180145400da006019441c041540c0095005002c07000080000c5948008a8116802803070001b00400c80401c200b40c2e51040ca03a001d0305c0b02e048600050000d140c000745001c904e8020b5142c01045840c059464a0410303030050030701c85a5010741c1c490340050000030011341e030103141c20087c60140244c2c0d91a0181d030f0703540280319214002c10958410304044e959440f444d03219264200240041c03e0360741c0d00f04030081d4405403401c461032490440f0117030050000d104040000c6610301d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 214836951 1250 214835701 214835707
    0x102070507240c0f110102012003090c010203160822030f060b061c0506031608070905090d080103020d1401090302100e0307020a21080c0705012a0b06190308 69
    0x110280c88000d40c00b010b1501032000d18000d0a0004070042d070121141074102c2d40c21500c5c0408070004134050005040d01c3c4200010280d9030001c92a44e030001540182d00c90821180c03524030b007000581e01d80c01186250444244402d02c803c001c0b94902004014040c54055945003000c021a50030000d0b40540e0000d8902d01e4048100f04100865840784d00100c680c200c40300c506004a4912a0442c0e0350558840a00203495a02086498400700800b211243c4450f40344038055441d01074243e6904a1481380b040c3d40d900300300c00f0070036014000c40d2001c80d090140c1d40c3c0340c0d031681c02d5400380501c241d0800c0f0125078441d800010760304400c8080c821078198134800d50180c80243c0c0c1c0130303440d5400d81d19200c200c00f280d034004100e8800103030744031900c0804231a08031090070a0404040a09408134100b480c0c0034002840001d1510030511000c03c01c8402e0369000d8807072600c40541c0c005455401c048003a410840694140013980100e1460003815602400044c207400760209902028000c83e4080e91080318120707404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 214838201 1250 214836951 214836989
    0xc1201080d1701121709060c21040303050f0a0e040f0c120b060901080a0b0301020a080f09070b1b07090c020705121c11010b100f02010c03050f0c09030102070507 71
    0x111014016801c1c540b18812020350408116860702613018000814031007181240c0d00603601d010003039030800f590003000b0300d459552104116484d010000f034010f41c1d41100340c3c1c003158034801c68010b036000e50f5059034901e0b0501d0404610201c465014004240521a1640d09240159128001c2d85881c84080384086100206840f0107400503c5148408e0142d60604068002c1e540790b020a850741c2507005d107800c4c50152a00b80500780103020894170f0503055400050790030250b0750044800c0d4020840d55802a409607074800c1c68a4a4001600400510a00c100240d212900c9501c1c07240304d98440300000e0311009941e612180b000c8904449841026805c102400c1200d8945041f02ca8021750450010b8018801c06188600070503600308a00014858414400221a0350950092411040c05881503240f10901b10000c0c0071a80a0350818005601303110340361141b0340c403a02039a801807c0031180c140041d141c0550010640e0064110300390150740c24401c160114604104400040a4001042c2c0c190400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 214839451 1250 214838201 214838207
    0x10051207020c13020a0c0c0321080601050301091e05010f0807121e0f15201905031b16110102161412010e0606010f0e010210050c1201080d 61
    0x80c406010354120b16a1030555880d0341003a400b08015070840141d50755100101501d2045801101500f6507625000110800c446806e180741c0084040451440980b50752104171984c40d070840b03d040c0069024401001320503e0303500140300030b4488800850001d06248030302400c13201700740d03c0384000d213044a508100c490000e1140501621074202140e91805081d2501d8403944030896901ca0006030955129003805071441c0c0608038503030b0003402c03000620106580e81028201485014003000c0c03090b8400c02c4000768185c1181e14582403120441d0f0b00e42c2c103117401600c10382c00c000c1060240d0b0200110b52024521120020290041a0441030941000d1400c0c2000714580500801e8103542c411911501d0790620481c0420490707507081c004264440c0300802180807094034001c01291507017401c481108880c0c0c00b050103481200b00382d0b110140150485011503d0444000c803042c0903800800c400341500800e0340000754004464550645001c4c1140d2110080900990048140342c00c1180c90304034140d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 214840701 1250 214839451 214839487
    0xf05010b0703090308030601090f0e01050405010504022811010603050105040c050a180b061603030c0e04051504050402240705210306060a12060b0d05131a090a021005 73
    0x250100308a07040607074580d80902007070054080a41a014080001041a0f1142d242c1070041c00003460904049540d6000300305a41d4001c0c050a4411401c000c0040350300d040c0ba1098500c000303842503281c0307500100c0d4a91a100c074a001d503042d00801140c82c0981881c0c3d02d090048000951007000001380e03e181c41d052250411201d900601e00c107480c92502000603d450400d045407000c005180010900d034080000351552294504e44034924800c0400c803400d2503010707480140001565100c290721b244c1c540e01008200c610842d428041e41031240200f40c803a00341030740210790041c4040c01004d01042c0c90f104003070a003007611a4007814070034001107503010072a051128001e00034051421041c2d1b40b813130a038000040d01004150350b020302d6020030014a024816540014001000d1404010340b030b40f1a10901103503446401c030031803818140001b069003d001220342900203034001524030140041e959075207404c0807018200b0925407061241c15005a502c0b005c9001c090501034441507503503c020b00c040d40000d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 214841951 1250 214840701 214840709
    0xd1709041404020a1a040f030c06080a06051c06090204060801051e010302031207020117012408060a140a0b0f03060f0409050705060f27030601050603070512180f010f0501 75
    0x3611902444010313241c007503c01c01074401440f0781001e48928108610b016000b1940001030b031070384400b0000244a142c0308528140c40c9640e44803a503540d01c05c2c0d403410590303085104041e08070b100c03440d940007016080015840801d204d0200401c1d14a0540c00017001d0b42c9540d0080c1049965807401c0c0100e03000c00c44201a417042102c4000f01080d89144c00003507e9400800c0c4091341e00500162880c11a84030380122450301c0c84240061001d541c440c8100d01e010000e2001da035544c1c003849004864001c2c014896507103c2c020080154200300e0400300c980407500261070500343c01810207403003c903500c1c0740003015000c010352502030f02d600d03881c0c008208641c0042103030185e8001e40c5400708810108002142d41070598900f0342c0d200f0307540d29601140c05134900c00c607602c0c1e2a0340383c141402d00241c03503000c00311507030014012000c80d4500d0b602c540400080e440300361400b4021490410120204109124449500007540c11802080b1034800103101d0402406605000e103607591a184501018003901c1000d000d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 214843201 1250 214841951 214841981
    0x51b011115040611030a090b01080307080301090c0215090607090f030201020a020d0c08120306030105010e0105030304120c0b041403060703050105181005060c1e030304031b020d170904 81
    0x1001141269500c8140040c0c100c404519100700180c180055038100d400380741400100d03a556843c00d081401c004110320031046500c2c0c00018000070300c00000000b920b018641041c0e405240d07900c1c183e50b640050161030110010341c0510402042d0f500c2031300a80612454550014006610b014900201404201d8121821050b2803410600150742d0006052900329030503122080a001f142c00c000401d001180d00003040c03445213581d0b004c005d0f880310000e5400360340168028041a621131554181d002424090140c040d40240000c01c0441d5500f0032404410303006d100043c80305a00c0e103c09030142d500941102021a405502d5110541020001d840d032007003051400f040f4035410080051403284030462660801c3e64820082000d46121600400c014000202115176855840070300756115800c610060640c00703645c42400041001c04000c40f40b090780e040d990600003440b00c0d0003100d90280d030b0305020b0741c00640d06c0050b540003400500350940d1407004070800351313204c201c1502004261071000e1583c1002c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 214844451 1250 214843201 214843217
    0x6030c0e010902160b04021906030905060906040210050a18090203160206070203090f040605041a0102070806040b06090406020909010906140307142b0b0a0507050310170c0d051b01 79
    0x401319240403800c2401d54001c00c410340035201d03800011005580722040801c0300410780e5000030f038030340c066103c052414410015220107035070b4a80a02d0302d800c81110040d42000d001040441c82d030380700303500800f090701d1a420100a29801c0c040f440040c0741c01d503004224155400014000381e146012113442c3e6003c4284001c2041c1c0c070b44504025101d01684500a020b08451952010296515040100505000740c0100841e50351203411484001c11050600c3c054060140080ba000001051080c81aa0001c00041a0342c5850080c400710400080090725403950a002110b810b03030707510320014020010624013041e4181009211103050a01c0481c0d0780c403aa00200017084040101c0c080781d03441c060200c903030503004d421509958444004220211415507040c04090040200c080c00c0c882c083c46800108004580e6004800e80f582e10003907a45425085000000f001213000c07055071803007007a80d80c0080c1c2d410042c4030404106a45410081161160003412242611000140c07400030798010034030746610 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 214845701 1250 214844451 214844467
    0x403030e132a0302090301020d09031701080304060503070905030a0c030611040e060f0312070b040c06031a0d03110d2001111206010e120c01030b0603150d02030c0406030c0e010902 79
    0x1001c4614078000140100300c2c03840d5003600360f0003581541c032001809402590b07544c140c0c1c0c2100b03006000d150011804101030042c0b40b4821005102c446040e07030a014003c40c941410000107031402d07000140708204214000c14042015107051060f0445907101d030281145041c118a00541942d1540781c0ca0b45d40b0800c240401c2014600703d0702c607281c0000301074a0006091002d50b0111f4200075801451216042c030000c5c3c0c80d400c01001c0c00d40c0500c254000c14030158a513031100411029110b00e10402003090340207420310a814500a4100100039229081442c907040044110710300300301162441030003046020340c4d5100540c0d401c0401e84065006032000f0040b28810f507e040040b405420701819000f100d080004116034020407159061181c010038409041d108080d0403035403803003682e403002d001904140c800c046c14100a01640c2c0110f402c1e990803903180340100c0601010285416050b641071084494004050321184164006140100f0245d0100f03030501d4610140c03200d040e130142e2015841006020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 214846951 1250 214845701 214845731
    0x40203160c0213051017030906070602031e0108010c090807080d050a2a03020c030619090f0602070305031b0301030803070f03020d110408190203030f0913020403030e13 74
    0x30551901504254000440c075001258044280b03201821a241c60942400410704040e0b103d6022143d2608056040e0300030000155103a0140051080d0171410500c004000184260080c1d544501300c8001e070072a0b080d50100802d01d54400303901012a0740d40d107542211010703611003800c0c0041d00a40d401003243c2c5241103002070351544980b01c01020810041580305a640c410314500b060810307581a440d0400600ba50420151442010700310050300c00c0801c0400141404a141440b801d44540c0d581c409150785040440a440541d1b0200e40d1407000e0a2a840080c00034400b40c2002802a619070341c6030303d0300116110141401d41a203245403001400100001400601200e0b4006501d150060450703201250a130080d020b00c1600540c550304008000a0300070001c070180007101c04203001c482c5039083d00000c442607a41b0751140a5016082000303010000705040700204244140505004041c1141c0000d80c8102d0300260400c130006a0701000c030000500c1c115990300c500e582801030402486803501020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 214848201 1250 214846951 214846981
    0x2090a03020f060408010507020304090e0105060307030816020d060504060c05030411010c17161709060f090303090d0501050702010c08060904060c020c06120907090c0903080d0b0a080a030e040203 86
    0x34412620900c2c07100c600c1e11840103603401000c0c614024802800c200d20080e4682d001070145807000c5141c44c18171550b82c0d005001d4507001c0c01c4041e01800d1154119100c4030841d038400c0800300050111210303084010b8849080d007800031400341d01c00041508052920b1780030380389014801c1041180c00d01c144000309400e0241e0403034040090a2008034040c941c41e01c03000c0303054010311483c184000440c00b4050046001031803c0114842d00811481c8031300c4400d4140c4900035144645d4001909201100302d000c80c9800034900040300404503420b04034843c002420000d410001140c0c1d07a5141c00610403030310b809001d800c0e0021524105040a80351890108071400c0c4010005001181c079030030a01c1e1014000e001107980041d01070304017955480303159610200d546095900b450544280030740000c481d003203413050940e00c02495849400151540c0c0341c0a03800e030009900b04c1000c0360b60300401006076440354060341c0148851b0000d00000c43c3c00e400c0203070143c5030a00100740114010000c02c040d15610f0010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 214849451 1250 214848201 214848203
    0x20606030312190606020c400e0109050a050c04020708031323071706010509180f03130612050415020705030c010617061006020304092307080105011202090a03 70
    0x40300342e1640c1e07440200000320029450303e01a8034944074000c01d045a0104103400450410b03070300c1c20001c40b03040500e145458a82030400840c0c141c240315a00c0140c07411418400c04e00d41211020408003c2e0b4400c0c01c0c02c440b0007410840b0320346d101100c100e003041400d0180406040c02113800710708080c69902c0e0a0014031005081c40407190100b182c0c8020001c500c0783c902d01c221030910608101c240851030305542c0342c0b468081c00e4480c00d10803050301d04080c80018207d058440c0038010003404e03240e52020141101c1d80c1c802000c201e0140c462180c10940f0108040c1c2001074210254080a03460488054003d49030011042e4041e070808082102007044842d40c400c03916405c120040e42d441c041d00342503045004804240b0311550030860300040340d121420f552103480c0c800c101075030440d03241d0344441000d092081c441c14025030014003040103030a44a51005441245a40800c000005031440c191032450085920502090380000140304d00d5910a00c480144a02100d0031850200c100c00007030580c1907a848 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 214850701 1250 214849451 214849477
    0x10809120f07060e070b132112090e09011a10020a14070509010803090a050315061c08070318090902030a150b0613050405060108011415040f0603060f060206060303 72
    0x10b0040c0410a00b43d00080340c40180200782d445441d203a9244041aa11035205103036644045d41c00414a2a840303481c0250641200c1d004260701c0195655210070f1121307860f912014892146030000720545503004a500c03c1031000c0002907011051a0079075044120109814014012101510203003900058a156500e40005a40070100021000d0303626002d8030f40c2009810120b800000030742000004050700000314100c5002060035250070515542d400d0308507821051003421380c08a04a400d02c42985103201c4e54411800c2c0c428a0603440340010381d0320118080b40050b4011a103020000362030240c02000c1d0032010024414000140c001039a58503816030003804403000c40105030300b8520554032035211918098895920303400001c0c03c40c0700c00c2d00c2c540b06040c022428440016169031080e15214140c5003005d8000b480990785500740036070600d80d45070304074034040b04000c04109119500164401403942e5580070814a040c1989502e8150301075018401350b5002c00c00b8401d440d5000720680381c0c0000402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 214851951 1250 214850701 214850707
    0x30f0417061b0a080c0d020d0e0105090303190c090306020708091e031216020307030506070201270b06040905030301170c09010b0a0c0813060e09060a030302070603090809091302010809120f 83
    0x40203a000e148a18090700101b02c0c4001140055401c01d030b0020020f40d0140390007049643d540c440c000351a48070496048a1041781100a000280b40e10b80c03005070b1064a42c507164005035141e03640c1e0b004a9018010658100da00480c8030292485c041040d02c002900e000c102d01240f0084d40b011a0f9995501041d03408c4c25040440c1464020b0450050301400540050860790005d0362414450b446500a40303640c1c005500b03043d69002103407001044d2901000303603041401e0044000d500d486040c80b0016001039481501c81c050400811020800b45000c1c140c1940c003400310320940348210780350003400042a40129403090041010800c0c0c1020345250303941c43d0030302401d070440d40d1401c07039254400c62803048440d1500550210310242d101e40966030594080e55101016180c140820002480a200c01001640310241c1805114800e8100c0040240320714130799401d0090380700c0050814001142d1240e00c00021141c220259030340590300f950410f03040c0014008180c0b042100c190a03102c0c00500c3c50002c4000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 214853201 1250 214851951 214851961
    0x1030b01080c0a030b1503010f0b070201090e0613110d0f050c040509130f03080105011b0b0703020a090f03080306040c080f070f170f180102090d0f0203030f0417061b0a08 75
    0x1031741102c0c085032001464003241283c15041650340790400e0180f680001035004002c100b0240860171240d0311034058485140961401f440041d001000a005580160b00040c03000d0800360140903041841c10301c150030039126000740600320201c5025001200c0d6a47c18038040c442031104410840d000d854050b2450811541c403400384160000308402d0040c0383e000d06008440c10306a10501a038140c8100344d94131201004609200d140c4e400702030001800d00d85080d8013080d0128000d0f8010030803c1ca007401d215942c3ca075100d440382440c4070180d00540c0c070100004100541490180b1902200603e50305180c03803039003041d40848214480080440c030900150302d030b00e602c82e14010308800400c3d40d0b40d541d604449103000780107045680016500d9020b041e0000e00c54551001c018001d507002e140b4060306110041403140c456001c0721007403c405a815000401c02c540c0310254500051015042014074000052a441c203420318260b8000d03e49898005480c0301000c800d20784804551135010145040c5050385c4036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 214854451 1250 214853201 214853207
    0x803070507050d0906020c090402010f1101060b0703120c090308040303050a17011410050c030d110d23060406060e09100e010f03031707020601030201051308070303050702030c01030b01080c0a 84
    0x8080c80a01584241e140e60600240e01004140c240d03001c0340c2c00d6544211b1007c0c1805500e45d02660001e003c10b000002c020b03000c510892171500e0600b00400081030256540344d81009a600284003a0005207c50b000f01d18250b00500400300062143c0c0f030a030a01d10f00c0c50300d9a88040c0110f000003000c2290006040c00700c0e9102c2c0d100880d000005462040886d40d54003000f171340401c0981c0c0c20b240101148481c0807001402403082c3c8201c21008d41c041c519045842c101303d0b000b81503140300543e0b00e100c00d10501c2c0d590200d500c501c3c0d40e80060345140c03540d0401280254148010000e0402d07200e141031030030a022441d800901d414000d8410343c0e41007801c0c3c03258440c041819400e60011000d040f06070000040c6030862030302c0c8404a9010380c90307015040d100c040a450300703910100c4290f0003681c0504010001544224000d10017018983d04841c0d000303458500385410699203238415000194082040400d519007884200f0040000742020080e0026a00019041030401448404044800303c0c0081c28140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 214855701 1250 214854451 214854457
    0x30c1e030f2409111203031f03140c03070803090d0605190e1c020f120306030f1c1d01020c040b060903010219030606020a0317042d02040e070e0408030705 68
    0x220058160252102c40c00c1c0890043c00d80e480b040c0d5445074140840245818400707042480b03000c1c0710b80a540381da51251280a101c1d060309022100707017911080c000011a8500c054400700841d8500603140300d0030368108052a00720280c00c003000e150410001c001e0301d5501ca0300720f0007156a10031b2003c14a9511804c4413681d56540074601d48185082a0302c49001c02004200c1d1800803c418044907243e82241d030301217a58110791389204a182e40040020840c184d6100040d5a00c2103004088032502d100e460280742c1050312240001014514a020f10404103401180c070751b603620010307401e04220240d0080000e50f14000d82015502441d07072509401c1440e10b9000464a140d18090025940d1300780002240341c0d442d058800120010f03240c1940030a106202040100003950113a45030155002d4008248070000c0c0040d10454134100e030000311016003d040c1b0b10441e0501c08401c502110010680140001d5540750354a0712500e03041403601380000a80381e0452500701d60000001505e07643d0340002515184 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 214856951 1250 214855701 214855733
    0x6140d0c020a150212130203011509060815040b0f06120109030507020906090708012c01030b06120705130e0c09190e0c0d03030506041410030c1e030f 66
    0x608011219540540000d804405a84070f00949490035880c441520120300400c454502c640c0804404035070b94880004461014a000400002d40301e0b03082e001e8041115071a6115952140c0c840c0d42c1042420790030b10009401903c4071000691078942552040b503201802812006420403403004207203070362950103000ca03003015203e00800010009090151083c0c00c04001244104500d10024010703080c0354080d24041c154a8a804501d6400d064251604a031086090302044070402c602c403a0740314803181d8090095008203041221410070f00f06101804442000300c40e1164000300d01000180c44e81c0e00d000c03105000c145400101c010182082e2400c0c4070180f00c07182e90040340f54041c050180446d104801e4088401d034400c100140d51001c07420388a0704580310180d800541d0b4180785001c03a000740c002962048000300700003040c031008121001155010764001c6a80c14100c00148100074031000e035040a0204259142e42081501000118440080c00028042c0003101c0101c01000303076049110703da41d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 214858201 1250 214856951 214856977
    0x91a040509120c01020903010608191203020c060403050c0f0601141c05010c0e12070803030406021b06010b0d0e07030506060d051006091506051c021e0d05010503060601090f0614 78
    0x90040070f0841c0b0f010b034000000d12803080d40f8021300041e0003100040e000c4004050030803001504440ba4a44904400103000d283c01450340070000c3d80d00703005060260903c640c0c441e440d003544032010442214074025801400c19181c0e0b02500050000e00702540c2040020340d42203450a01304451400c400e900c950840d800204250300342014000c81d00e412003486001201c06503000b11214020100341a924407061041c0080f80e003007000400e0205019800814210b00f0007810300510038a0b00e400140b400070245c0c00080030072004100c00c201c803070490241403c034000d02d2005065007070071034564984130403015101e24414071864010108002050008005c0c038074001d403080100c00c0d624490301c1e0150503000600040745c4804880810101c0c000d90279101c1c618a00700025000344600340500c4025800158141000c03d850178420110803c0030f0020700b0705000b05400410103514100500d4035000001d84030a042c020025000d200e00725849030403008998403880c0c2100d2008a00c2c4171090b851040301a01c0d014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 214859451 1250 214858201 214858207
    0x507020919020705060a23240604030b1f1706010509340f030e0a1101030f11070b06010201020c15100b031f080f0727140403020601091a04050912 64
    0x20341107040e400040b940c481d0030310780d81600801107901000d2480c00c54440d605000500300081004440c8d85484004c01c0000d0000c5251503280e031918040038604840942d089080c6040101c80e141c0003010314402003165403801707203e0407034011103203890740301c1402540e000e210350302d001428a502c0c1001d00e02d42c2000d249466600300b0f0307481d484000007560b84542c05c40410110300950004a200b0301c50b20380c50040c1740000d041703c149940da0f010b0041c238802d40f07550b040540380d1140c18440300051041404021030401c050356580b40c5d51902c144801d6000b0115815a44140300d0003982c01f4011580c904011401e0951448550740d500700204103e41c036130001d031690103000c41004050490580c40d2010269402c044000495684c040103544042c4011b00321150382121908010010080168401a1200d0802c890104604810040894100340b00192020200d201030009150301807000c640541105ca00501003c01900310440ca82c0d032691840b2070181e80c1e82d00025201107014800003152000ca0346034569 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 214860701 1250 214859451 214859461
    0x62901030e032b0c0f020607020c0109050d020102161404110306030a0f05030d020301151b020a050d140a060903080a0203060a03110f0310020406141c02030705040812030403030606050702091902070506 88
    0x8160507490303507508050f10511008c500140c0c0005038103140000140d6500341d07440d0030803050005c03170700a15004074158032601c04100d040e09800c1d0100d00c0078054040c2d142000329001301c01c1209903490280c408841c000200103020081d10040f40d03007810750341c110141c003206d00c0389450002c0c036611513104c14010b160b03c00b0002040d2030446010000c009401640c483c44018091102c641c041400088000d52000d2092000c12090030501e0300208040d00480820300380300708042c00f090402422803012201c0c6a9512052020560484000c0c0d401c810030700d40450a41c0360890125002014901002e0250001c046426284d6514150385110b1004007909a901d804a000c0a40002e904a400384e20003041040d103840e15550740d08030036500600c060410102d44840c0b0b040300d14000394006002003042110800010451072410050085c030b84202a008641e00d140504000b01100c0042d003007107040280800c1000003585d0380c1000fa5400018008500300717401e4801e4000c200070310401000030110b000e0102000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 214861951 1250 214860701 214860707
    0x12130501020a0e0901080102190e01020c190302010314090c1509040f0509192a0b040308030a06150c0b060f04090602070b0609161407062901030e032b0c 67
    0x2c0702c013034030b42c12010798880f503241e8280d0103103066050000f103a14070000c100c10f1042441611101060042c0c50b080400c81c4041014008c80095195a14810020400455070301d8032817a40703800c03e00120118141400c0e00040c0d12514401010b91140740c02c0c01c9545442c42100301141c6075410004c100f08001110b0b015503101070101224212000c5c0104003062059101e0828954003040e0301008002070982441808030090f8858010200d8203120400c01041101e000c500500155018400d420340744d241169402d03041d500142c2140c03c400c445118000501500b28180134805035102020220b0742e03981e90b01007140020764151160f401070414817580240000b59000388046401244088140d985207010300001000640302d50314640c8a401e02c070480b040c03162805d502048000000c01c0d19040040c3c84040560303420340301140406040c03907130015042d4001c9100c2e5080400a083c2030002440d01e00c480c80d00c80c0141b00c0a42c0460f4144501c0c556145044403140f40b4038440d601c030811010000103001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 214863201 1250 214861951 214861967
    0xf040606300c02060702100c0210050a0e07120b070c030e121006060c0b060a030f0b0703022a013806070804060521060904030507030309150b0f04020f12130501020a 72
    0x145c054003030204a020305403558002c000345501d103600109026554a510200106070080500d80e042781d40c0d240c05c0c01061014030641005001802100410f17203001e041c1808140400340c9100d060007508004800003981040148030400030031034500035500c1d200c40300f4a0508404003081c45240745440d40100340c00f03800008540e021b6000e6402d02006540741d800f07229001d94a13010207081d01c01d6170301480c1c001070b007003410043e44060646400340c10411091150817980d01110000c030940801d0380204400c5020074460305412592128034100035a10030941d1440c01c1c0c03545200c45901c602c1c0da900c4c204071f80d140e01d401c840c0c419610002c16079a6036513520300202550000c182013020078140400000b13032241c4d00036070b81d4050304008001070b041c1e888503030701034629a1007039070110245605c070705140303000c14403400319403a007240c14200205405501004010140c0351810a05100b07503c10b121244002020030181ea05015061800540326100d42107404540400c006d0010407940c000201d0f5042a0313032280c94 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 214864451 1250 214863201 214863211
    0x50402030109020d210e090408130b040f1d1504020901110f030c01110a0504050402090112090c080f030a0522080304090e0c010903080306040c0306120506060f040606300c0206 77
    0x42c281e1000e20007191586d21442c0c60b280c0c01610f00000c5000702d1b080b04020500e58404034940c1009965a0049400303503080750b803004a101d01440310030480302d4900c03e50102c2c801c0c010341c58803440e49058401203401a17000300000e400340394042010006a4007460031356090081c40401c03204140070b0940c5140e0380e40c3c81062820021350074001a1542071000809940b03240409480703442c20981000c0c1800003d400c1024842c1c10400344018505d41100f407445142c0069000d613a154500c6410034a020386407007416601c04103603520030040e40041c41c1d400803e0329066522070f1040c051520701089080344100b0b8941020103507010000c0e001480210503170080316005403040c241c0700c0c070665403070054690346110701c00501001030800003e4002e14080e0b11100035070409080003d0101c1e190820102c601c12003000846281c1c0c4050140001e501d0b0200c0e40a10780502220244502828890010305011594121100b44142070104030241118012600440e0034821410084500c803030000964a89090750 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 214865701 1250 214864451 214864493
    0x10b03100912180b0a02010b040c050703030605060a0e0d11060c100c05030609040b07020f010e010c02150c0f0307020f0d08060906090f13030903060608031209150406050402030109020d 81
    0xb0601c0d10714011018000482068000500d02e0303441d1240141d03076544820340345c50840d5038441c5401e40c981d440c2d01c070307030710210b5100d40e02c854480d001c3e464040c04076081a04440c2c0b141c84d042c482e1f0714100d5840300480c52142c006580201d508541803600d1403c2006c0740071503684c003150104040e04410300004071440304a50039a41070006541e0507000380d90364802500c000d0b4200501200003004601c02d0056503810460602c121030185000c182403900312107050030b00c2c10560b5140c501e80070485a0402c5044200070034940c61407020308160a040c1403512134000003003e800c5000c800103a50030b00034400215516440d20a071030741001c080704000c200f030340200d40c024861341c041e1001c60000d041800c80d891040d00600700034241619401040352041d05510b20442c1040300720800800000c1e4140100b01c0103242e10701c020341e1100549504c5c42d074140b2005005000700d600208900082200c0391100c80e4100e9048100000c540e103650011a000d001c001e4006904078400050620400c2101d0001200c6160640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 214866951 1250 214865701 214865723
    0xc1c020a2303100c020c0904050a1a0114060c030a0311040b0d0c03050c07200d050102120a06150206040303050a14090703020f03010608070b03091507050409110309100e010b031009 79
    0x4150b20044135030083d020300c0180d005001500710740c14100304c9990042d008404841c0d0b542c0c0103550721050a080c40a0035042640030f0310040000001c58141d102841e9812209982844e14426959a41e401070f081070108164540880c8071103e212501140e028042800b1842da480c511800c80794050840013a078040040d28ac140090608214070091f902043d91004241180c040440003001540070300701000d5610089401c90b032030005600b40300130010341c13582c0c01d071014981c50700340c1c15001100c090303a0161501ca4154410746502690100c0d10586c040d906060004d410f85400070680000d11095038201c00110b108020301030003010019590045910071960300c4d40311644181850b017611128418000c840e40140b00c2441b80d102d12101559100b0401c0007103840100103c0e9100941070b03415a40d00000c0f4000040505c100d085900401c44c08112001704149541440b001e03180d42d4400d503001c4007460660300c162000e0300202c29040f00d00400b1005089820001640407003c1c001d10250808030741561100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 214868201 1250 214866951 214866973
    0x201021612020d050c0613090501060e01050403260f0304050601060e210a020d0c030b07030908091c0b091005130201050f03040f02030a08030609090c1c020a2303 71
    0x3401001541d58100c0700e140900c01035400d1108100070454226441d02915400c000941c444401906002000b607075401e140601c0d1041c0c1e84211031040e0041c01c204040c0344407440c00e9980090403942201c0e80440b6174142c00081001100d2038016030300d1403160803039000850b807400e80b217160702641c0240d00840641f41c859a85000075945060078070305441d001140361400030058241c00d42d40103040c1d0604402d48640c0002640000c0e80c840240b1400c41c3d60640c0d200051040c404801c02d103541c4090039040c10031202c8441d44a9029030b01501105901c10340315506441100403807084e00740410390303105e0303600070b8141003600c05580c0340d81030a011305004c02d01d80000038141c0c280c940300c14241a034060719840d103441c4048100c2106680014001e54020b0a4948410010f0700c0400003040202e00030450a51203080c1981001108440a401c51300e055100c0d42012005a50f84103441e0300c3d020780c8050368601c41305c281c4040303907008405620003600d8244685084241c04070782401d0040141e421003e4480031014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 214869451 1250 214868201 214868233
    0x30809070f03080d0c09061d0f06030108010501080f060f04060506030f0105100602121e0306180114010806060309070b0901180801060801180f0303090f08190323040605250309020102 80
    0xc0c41c0716000020300348802c0041c880f0452091004e14501c060000032703c2c8043c49010a032980c0c02a8010225a903503480100301c0100207101011501e0708110141c045414003201162100b80f0240029001a50b5803000c2501541d04000310100846900000c0c007a61810141810804260b072188038054040d100c0c005a40120b07250072038248006072514104160794400860100380c00c0100310a400c0014503208441d5000ea010000380200600242880c2200700a40014004070014002a00905041c014004240b802180104c1aa10440398298591301008012580700e0b02042c6144038039030100340702158200064004006888000000b8030007510640d60580e0000d045141c06892000b200e42421300103440f80d04000d006900402507240c070440c058680900c198400009105004030480d4409015034050281e9560940141103181800c890711900340320300d03407005000030211a034810001d442c81500049810362040c1c0900354400c50308031224068000c0c0707610b1100307030b01500c00c0c508403441e1004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 214870701 1250 214869451 214869467
    0xa05060916020a060f15090902010207050a030206090103240e04020a1a0d02130f0b030402090f011a0d020705150108010e0d0c03030c0909151d0112030809070f03080d0c 74
    0xa603036000b400f24900a440d13680040480500103401152920909a98001c1070840c40000d0b05030498000380713400d60780c400689001115070040340240b40140b03007000503944900545020303040038200415410702103444460071f50070b01031018800f00c44441010450b45400e00d103d43c40303640300752000007a0340d44840b40201c181c1c0d03040d200c4480028080060034034107140d6030040d0942150f24210b03001040c5e00d58582076000c0380130f50000002044003108101c15440c11001650704040c00701010311865051500001c81241c90400340c100b03c40001410a0300305960358100c0c0d05498112041e100f500d120b421000000303017420322aa800642c24108800081000428680d11010040e1180d408698442e603064014260348103a03d014000c40c00800100c182c205d010721031600521500902000d4213006d070030703940c421a0300340380c82402800d100140402c60109034000c510680604000328156180d6920916194030f5420004141c0b0448000104014100d0041c10590110113400e1110900c548001c0369100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 214871951 1250 214870701 214870741
    0x204050901091110051315030515060d0b060702041802010807030b090106080703020c010c0503090721060522030c1e0b0f1012080d060803070f1104090203060a050609 73
    0x2d06050140740f00d07807a12040064100400b07041260500710142201451010309921150114000b122009501a81881415131110600c42151390050503440481c99034001c22007900c040b199500c1003aa042d80c0c0d280165008154020014441c00c01c2075101c4440044030b03d1004c07030204000c41c0203c2c40403030007401a514400030140010070a41c2c6052000c58400201401007001e0560070002c1041d507150a0254100d80c18260729025900d040400c08a072030320030103078085801d01035491060038450001407010555a50415030105041e2982403072000644440090b060b910350301000c205003050b4100d00c11111460050403850070004850340300d0200d0700b00c02c0b48001c2c4500802c100295000102000340c6400902c240f0602c1500750301d40e01c80000d1912120019600e40b840800c1030b80c517082d0140140005800140d0240d403c1c0b0072544d0b5542051484c012005040086007003000f035007900c66a2001c0380325a0018116545030421907810001441c040e503131240910b52030700c002095940502d030141100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 214873201 1250 214871951 214871963
    0x1020412060c0e011707030b0d1b03120906090e0702070b0a080402010905040c080402100908011103160203040503190201120f02120907080d0c110a030c060318030e280f03020405090109 81
    0x2640c072110118000d1448c1d0a5060b40030303076500180e07404141811107218803801c80c1981c164500d401c5040100b644000d5081e41c10400c015198180142a4400034240c125903056009034032540320290700380d05140080e04031503502d40707000c01c0e40f000490f800844d06010314001c2e203940c4105a03d0700b0600042d502d0f003203c0480400c2c40540450300600741501c11400c001034502d4150034481c2c803801c0715401d507800c0c800031948006011003800445a0b26040d101070001e0140021460a850800800d445580d0fa8080d09113000c0203007043c02c20f69001c5c0c01c0c0d0321520480c426040003108000b00070364000390019a86407180b81495070004200000000f1544103483c4400028050403d00c90411142007444100c100c403030703400780c85e040102074030352980705000b0710b105241001d2039a06200000341204c1c40c08a83c1c158441e03402d03082101090704040010b030804815115211b180c0240c2d44410310711034144105d202012501b410020b41c80c4550100082564400c980500c01c035280e40c0143c0b0300341c550800c406004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 214874451 1250 214873201 214873247
    0xd0c030614100309020301050702010f0f0903020c060f07150606032405130603060204240206010312050c0f07031104140103081b0f0609030a09150206010e0901020412060c0e01 77
    0x1180b500d2049580403000500d0080342c0210319601103420f5607001c3d0b4900015079100c0f02065040f0350b060107940603103040e4072401c0060420f161802581c44000d0880706000b0b400c00200b0b82c40a020030000c5519a80c0c00040c0c40c03480810308082c0600030261446407500080c50103400181c01200600c0e1104802d04080300c00824509100811507000031113660484450360300c0c04004001074550010707000a00c50802d03010350340520082d90785a07140140600100315009040140b0000d8010340040402a20b01d19000381c480491041c0c13075140c520343d04100c9090b48a12000042002100740d00f4911101e07040d1424020710000d41e844141055080c04010503c0d00c041c0400890010130482405166503140c0c101e900e11404c05403010308010702a6405102c070f40000440449690700031540d03c0082290602405951040d40700c0291514018003801040c3c8140c900420750140c07007501070781e0140001250f001584c000904e01400188004070090000c64008852204d4a43c000c1104581407110300300c280f06 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 214875701 1250 214874451 214874489
    0x3070806010302030603010204030203160509011719020607140f010c0302090d0206090301090c0f030b060607030c110a33020601080d0e04140a050f0f060109030308130b0c0d0c0306 79
    0x800f0b500020407041c0c0542d400c0c880003001d070340c04102d0380b00d400b18500607501c0c4081c1803d045c086101c2c0140c00040c1155078203202000340c00030001e00d400401c400ca2426a1180c8010300c0007801c0e610860388050506511a109600d8040011070300c400c881850300002c00541e0100340c016401d034000d10882982c000030661402c0058100302d0018941882c0040c0009040001c40d43da80320744c0d041e00c0c0c009480b4904445001d10800175011007103900f048045881604041307040e80c0080004036180700042810b1942034811b40142c81e0190b0460150501900f1003842c0100c80403a215031501c0d003086500364a40c2c00080d00c0070030b400800d816050340c00c198081c0442510f001310030354458403038030300a5420654a041103006051846010760041e01404004140c41c10011b008414080015040b0300071180b449052003004d0f078001901c4012a41c0c581407085c80b03513807115401c4019050545000d807602c10f90008001d07030362a490000b4103250591400030014400700107070071004c0310020301500016890b80031060b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 214876951 1250 214875701 214875707
    0xf05012102060d020a02030a020c060301050a050d11060c0c0f0a060915090b030a0b093103050d02030a020c06010b070503071502160309060306050d120507021518150307080601 77
    0xa1403103002030b0005203480041c035100002ca910180e04240107800100d4014022641440391603d02c07001122814203650400000800c600c00b94454184100680307480340c010070080001440300030308000c101d95121a00301c1035503626002e1007a403181c8148542d042c0c0451a260001e4000c05850541c1c0c1c2d415082da0a10922103103044100c0c03c941f0500040c110002044440306008503c5808003100214070003940070284031300088040e00030501500640c03030b00300180c00a1207003000b8114480d416201216114203041e035040c0328174a151440310380004200000d115294008000a2003400100c40085c1c1c7c0c2d40340d00e20303124015034030000e0280e0820407401000c20b2b4508507810103080555801450b00e410584c2141e0409601d071400c401146885104100954151080300e00400040e1400702110005075101429606258420b80c14010040307005000d54481894071102c1d030020400040d69075a001c2c00b408455403d480f03c1c2032203141d080c5000b81c080409070701500c0c010010750f240e0800c3c03600c601d4015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 214878201 1250 214876951 214877009
    0x803030604060f030f0201112112090d0f0f1803060207020f060313060b120a0302070303020c0406080c0904030c080c071406090306150102030c0a1b090c0206071d220f0501 75
    0xc8d0600c01c242c0d250020f017551079401c0d80d41e00107070320142d41d0b2207101c0c2d201040304e02da000b0403080c5260011101d00d0300c4160401280b060039502881d00000035140d0320410b4880c0011400c0040031262043c4011081105940c01041003600840341252040c45220401c1507a120031a56507004440802089001586540100032300010080034075144452a035059898020610b60603401640181020802d01da018003601da4881c01c140c605000c045d0801a446a40700f69001d030b81c60003000c08a00140915101d24490500d2590240c51603555100320703082c075a030351450782c00f0b408141c0b100703074200403050714000007241c44034034010740501038543d1050004101040d038000b6440c1136003c2000319283d00c40f07040c0304a0b030342d60784903c40c80800400d074000546d982c00066003010417514a00b0384180403503030300003c00075481052840c2404e51038034810018908980805c05d0300b42c0165202d51640c2e0414400e100c40f000340800341c1e03404c00c030341c8480d0002c00003906c2082c82440000e0034080f40405002101b4a08 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 214879451 1250 214878201 214878227
    0x605061c0e0c04050703050403090819140709020a0507211202030415111b060f04140c0a0905220206041728030801090905030d050915010803030604060f030f0201 71
    0x956982c400c441e8003050944000705d0300e010029944004020400d900b002c0083e020346054802403075400c0c0720601034605105000d0028009403007024401a403407408001180240503040c1c020354036560710284c0034000d074115100403500c0d18040207103800c40e840e151200e0651000a50b032144c07060102000ca030002540007802c2920302c10102018801c0c840700c240124400101140c960702d9a58040850340c400e0194030110103080358210100b0301040045000c3c1f10b0381c02c00d80003802040220702034406a464411942d52494112000010000342450030b644054892000f0702020309030031110080c3c5c0384144044c0b1100030b40c040320a100521141a0913050000020740d4803080354403040031190011110960000302c02c0c001200c22260504040d030100e9144c1c010f00100c2c8003440714914960303e1325140c1c01001040c00d01266203000080d500d20040009140d004020001c640ca9542c50700180d41d2031b0392088030340e0383c041c5080000000b40b40907a880213800700c075040070746246400c801d6070044401d9812000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 214880701 1250 214879451 214879453
    0xc0105160f171e0301030506040618050a060515010c050a030318020a080106030201170c031b090d03030c030b03030705030f130305150103060f020406170417040b0d0605061c0e 77
    0x1a2900141e40010b80381286001c0c00701c42c5840700452480d10003904264a1002050881400108009000001e0311900180d00c40000b051344102c084004000b942c01c0071018125100e074000040600140381c1c04a4022219039014002054451300103403614505204010103c2d8014501c400111f4426440400718440c26135410801c001d250300003401949441c1c0024a60341d6403008100b00b1503822184918010607500402e1045190102c0b05403100c1c08000c0c11440801c5e1000e10f02401610980300303c5d50b503201d00500150306441d06040003070003400207030a24800702c0e1400924030b43c1458000203072140154000c004510300100003220170201c0d0820300d20104102c20421001c40000c8052003003880c480020360140d659507265080c0141030303540740e0042c0300c0c1c80362041005014803940241100304411016102507420f4685103044804100d183d0854400e070a00850301150400e44040103221089900c001480b1154591080150511644606030300804000020b00c070001041d401440340411028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 214881951 1250 214880701 214880723
    0x303070c1b0305010e0c191a1209010e120309250918060c0905090f040f0203030c07080c090c04061d030d080415060806220c140a080c010516 62
    0x7018140200440d60402c075a5a51a0700c10750200340000c1225840d01303003041703e0400c0c2c8030f14610010440c0d18428040c0d00b003405c8206044010705900702c811900400d50301843c640711442d04c036071031078028540180c0e80324860140d410440000343c44e402c1903d0240c444500a090940070000c80004124008a03017501c0f58402c1010000b42c01c1010700c103100c81c180542060130504040ca1030301c0001c1b101818198000e000c2d11318000c1c001d40d185c4420496002c64030750310701071440d1601d08065640d003a607018025411300c07002858401c04000454440115695541194401030400d0304010900070110382848441d030046c4400c0181e140718085890030380624990340c000412120000c43c0c1000340309128917001c00d03003860a120030400701503401050f81c2480c210800c509402d1009294a515010305006540741d1140c851001520054841050841d80800030f082500d41d546050b1810882c04e403042c5109403024440040d0868020a07051981d2105031340b03c0d4030b40241542048043c0c002c029054904c00c20356 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 214883201 1250 214881951 214881983
    0x25080d1a0303070606080601121101030f1808040611011103070e060c07090b0f03011a04050c13030605041208160507080d050709080d0c0503030c030a021903020a120c020303070c 78
    0x5000070880c96001d2000072612a080040386d501c0e290041c0d006801c0c07144803101c0c1c00d0206a07c84801c5080080918000c20a200c2401c400c0b8050041c03e0074103078007c2003840100c5c04103c440070041c030840d4940d4a1f10030700e101040c40b14a00b00c0b5040508081080c80410020315404c0c890b01003003201c848020311503818440d0751101c4618045aa80020030303200c0d5591142251803a0428a061241c0401c9009200700312030794100350000c2903c0d9600c01c0c041d40c0c5490210300341c01031040681315031200705503162403103d1362400c0042c00781006940551340300e030960300b500c1b40e01842200f1540c03159903146000c0c0303800036200804403415840901c0c2036810fa4002e20581c0001e801c540a114010151596000c1c0010b0800009506200e507484100080c0500304d00b0322400503102100b90b079800100c030006980c80742e41b443c20400180c031901c034808007004e601d0361600781c0880c3c0503406010300004982d5100e200f40c4d1010501812076045000d800c02513032082c400901498410540d40000c24030500081c0c400f4465 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 214884451 1250 214883201 214883203
    0x130b010311070b0a1a01050711150a02030d06050f0307061101020f03090105070906110c01030b0a080105040507240c060b01020c0a0f0302041b0801060c03020304030b0c25080d1a03 79
    0x40c48088445030005000c1c1302031060240204200c030041a104141d50b62520320019040707100c0c600d40100604a9080012940d030fa60740c082200200500000595407004050001d403a42e210b41021109645091808215801d114074000c12440c40917000382a900e051000a89030a5a08120b042c0d0395034080084000c0550000083c4d4001c81843d40046114100345001034400e12850b00a00b0030890301c03080114a902c0c00040030181c00344282000106105480c001c41c0b440b002942040e0040e6090109100c20407800180c40d82c1181c1c074040c1c04030000300d440c6041d04246818581c1100004000441950103d250b607840103010134414012210020041404075941300c605038005c0922451400080040d810280102c410261840c0c5542c41d144144030400b03000d0308e106010309020054100070140403d40204110740207160000644c003102d150220030f0100c1a44580e90240c030300d1182407a40c82c00d49040348543d2056030781c400949420070f9a4039802c10300525031003116180d5011126800805910 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 214885701 1250 214884451 214884457
    0x403050c060c120403210c032307060606020609070b0403020a051005070204090633031e0512030a0b01080f01030b0c040b16060c080c0f0703030b030d020706020606030a02130b010311 80
    0x100c104004500c41029402032100041c41c981b04034244004501d006000a920200d10410001082c000c8042c100b510f0141c05c050b8080c00c4001809540780c5200402d076990001140c3d48281742e1442210f00d10343e25034041920030302591100a4011460400a0082e480c00307406410500351036191003414403006400080076200078500540b58aa078401c1c0301001131914000068042000340d2807035061460040d10641c0d140464071014000481004050303252140040000c03a0440c0c0000c119151442000b03250034640d802074909412080c078103440c5000b01d500800405102e040b409070194000ea1860300e92a412400c000c0003500325500421010031441070b0040071380401060301e0150b540940341c80c9404811940041d510000307114a81e0304015042c11b015003112010100201c06a440300c00c03134601a00901504088298140135444040d21041d80c0040c0c110201c0f45a079007102d04036141c41c410f05840d2034110902940003103441e101240c880040390440101d010042c03400140f9580900c09404090f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 214886951 1250 214885701 214885703
    0x31d01020d06180204050d11030316030206011409161d0d0503090f0402090901031203150e060102010c080106020307140a0b07170603010515310608010509030403050c060c120403 78
    0x1640e00c41d400d010f031a002d9440d00400000d4000304500c0c00f8249800a000302c5244100185606401103070b035415610207005580e4194665080001122003034035029480d001c003400f41d1100c29848071010740462402a0b00e441c090340341080d07403030140402284101d41d600051000c926060001d01400d00301921040102001240900061902d07081190100100710880340c00040c03180d0700610000700295104903105044a07840b1004498031b0100d590281c2c09404008458418007420040015000280800c10b5101e040300340e00801c2003807501001035071108028002e10005038805e1245400054000007191100e528140440b020100e41e59250002e442e021103003a00002c141c0f0035002c900e00441c426045d0403040840080c001807a100c400c2c55a0340310b11402c1c480c071130355000301c850000c25240e0031900c840700c42a001c26100c031a480943c00010304031910a00c7c040e5031800c0006120b04801000f80c4003620f900c1000b6140d0740c02801c003044190b03040360b40c45490a010b110b0300301d51a0f41b030010081c4015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 214888201 1250 214886951 214886977
    0x91c021006080a080910030e0105010b0a0f0c121209080f0712020609030d0504150e062208030a020c100f1407030212011701020705100525050a031d0102 67
    0x410500000000c1c1e401e076500a210076448021024001388180b01520007032030003a80c80201c40845908100c010341030102c0100703c20f5203008000700300071007080001d24420360720303480b9031845613580d131400c4955100d01d0201030105008401a0107400d44200e042d094a046044804112804541ca43e541c46a00c0a4000000c4190000e40032040217600c19243c0880001800a0402c41c80d1403c011a2240b0801c11480815075a42d00000c04200824402d080d20782601c200030002c0b2580610300b5640c58409945207000080840d18607180f600d09c4002e14010f50b076010b00039609548400c1124800f031340000600c006d050081d500745c2c1941181c20301c43c90315900310148010440e000340344103411402c13901070201d408042c0100f0002c0e5171606040d640d681111800c200e85507030a108120359500900610800512500441103411041c44990308490b000e034241c1c9850303040020000113100d81118008074000085103061041e900740a01a600031a081001d00d06442c020035440c842c0706007264040b80d540341103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 214889451 1250 214888201 214888213
    0x70212011506090e01060513080102030906250e0603090703020907021507030c050a11010608030a09050a09050f0c0d0b120d020f010b010c0f060204050d080c0d03090305030f091c02 79
    0x3001211441000c0142603c2c181411040d0605142c208a40300502460090180000e040550046c50300040030040a40c04002c54072800c001c103400380c80c0c040c151400c0d00d140c150001520300b03424403000800d011001c1600c8070f6035000711180070300c501500010039030a003074010620004003589a01c1803241c810f6050b50b0151030200414246045900006800c100070145441050a4510307004002c0302c0c0c0b20600390a04489024007001c040d0701500c802c1d08050550700001c60042c0782c181d00521244140d50003207410712001c0c3d450321150300803203c0440780612124551800704a80f0b41040c0010906d041b85d4000119154985101103582e01a030316041101e2a8000b009030140c81d03031705108020994131000024071902a01000091041034403910152000b800c201c41c0ca402c025542d41190010400504640141e44030390a0081054001d4030b1082214001d02c0d00c43d040240c480d11640d5400baa041d1650390035601d802607000b284c0040200220318600c02d88903c0358074403c0c94003401c002c85940341e00a142c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 214890701 1250 214889451 214889471
    0x70c030c0603050703050402011403040f0818040b0d120c060608010204060f0305072d1209050d1205040b0103110d02040f06080c120703110d0f05070302010f05030f01061407021201 79
    0x31910f00500d0708003050b241c4424000107070ba00c4140325100721803012a007512516070342005000c40525640080413124001155000e210000d6041015040222420444840f01c04148084a0500200240044680080c5c40b01c098042c031549c99010b03010300c2c0000781d055102c911450890b4019040100400c14660400a0303403645070062940c40385151038000005500f050128205e020041650301180320582001309415100d0016400005d50004c0203001c507154034140152604501444040000c072851103104412901d8083d16028a9201c940c01115a1845d103403001461400c0c20019403040b140030440c000760b0354a01640320200404a4000f90452030a401d1600e004400051a800341c82c5407125041b0030480852920222604050f01d460344038852000602c221210140051010742c03040501010b000000842c60305891003a03c0d0501c44000368a8240c80341c0c041114414402c200c41070061001500c241c00a110364004105010f040030015400a104e50108103c2d501d61030303664040400b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 214891951 1250 214890701 214890707
    0x80106030c12050d050d0e0a150608030f07020d020f030109060510061d1207150302031006090308090d0825170910030504020f06031602011505180c070c030c06 70
    0x2440001000c2c1601d0b03030955509a01c1d070140020302003e1040105502d585604a6005082c404c0c001d4425600c3c10161071420304500140e0404000880d494140c0100e00c0c41000021200024690b84d40309050502503400c010300c0fa0240c02d012a00803941c2840800b1946090007a030801510480740487c1c185040090b595003d603080e4007410400102d10f007542d070010b20082001d040c0504c19144254115500744a1610b44a250b9021025903100e1040440070340c2e0345a809180202500c01980520a5075100125291006800050400d1004011800207407030f000000f0180c6a00ca614400c0c101131808001c01040c0000003000300070500d842605008002c001449013184006107070b00d081c1416208404203a50ba9980e4402100741552100810b096680700510203a5250004241d2556854142c80c2640f00c0510610703850b001d036003440c00608158400500707103020380302c001d081807054140d28980d00d010900003400707484040c0030400480010825001040700a03500030341000030907501c0d2440007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 214893201 1250 214891951 214891973
    0x10e0c1e07060b0907050403020d020a0b0f0d05060d0b0a2c03040e090106030f0f05030423031c1e0509030106030308190b0306070f1e030b030c041a06210108010603 72
    0x403840b540b944c034200300341950440256804d59070107131446407c003546480490740a600d80c1d0400d14034990701103050351110040e02c005000400700c00324207001c1501c84405000c030170001d1038801464100170303200241030b1240c00d50000000c0000c4010098075841c00d142003418134501c1100c40c1c0c0b01034000041c00d0010314042c1040c0c3e60800400300080103800c1c40c5850304001c94000e00801030034101c0d100010710a002c0104255005000721416690343c08603401030341d020708000259180c3c024011800811049d108141108521110039160541c00503054040110980c105c00700f01d106000d0305000c5000651403d105081c01b5510a8481c42e40c641019100c034400112003031485284241040320001042c0c4010034040e800c11950308040800540440007510901403413400c1804846590589010303031980368000a40c100070590564084800300310a100544500f132398198800c140c40c2c0c10140780d90501c00c0081c1180d629601000d000a1481c1882e40320207034082c1d00504241c0e44404003402440041c00c06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 214894451 1250 214893201 214893221
    0x708100507051902030a14030f1305031c06051c030c020f0409080f070506010b041406030606041e0f150c021c02060315012604061e020d0e010507090e010e0c1e0706 72
    0x147c40c1145061a40440b54000090107440c41040d4586040100102041035944c0c000b9101041d40b008207442c1c00c070800501c810300c03406120f218030100714051501d020504007542c0340c156862843d4040503400b4002c0e8441002c5102d82c1060352030503600c3c046003d08000d000300c801061f410325a240c1241c1022413500b0310681003078841c000d0820007000410741c0075048690030b0310140ca2203a01e03a900c080006502e80a160301070910203140b40c0d914454811502001c2c01a503804066010703d05031560521040002c1c00300405010460103180e0b4005481c2031880e60f80c007010026141c0201c00720036030201d40c4039001603580c06c034a038044040c807040340c0d03030000e950703071107410601d21407403c905080e104080400c0d1001d00042d2401c1c0d5038000f480817544042c060f410200c0031a4009540e14021414090020039040c00e40d412035518080c041007000740700d9642c8070225041c444c8842400d07424840000e1350b41d607024240315003500e020818100000121703018241c1540300c00707955540302c0c1e20f503081c00000e480c0c10b481 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 214895701 1250 214894451 214894487
    0x706080106090315020d050a090302010c391703040b0f0c0720060c071a09030303040201210c1e090e2706090304030c080708100507051902030a 63
    0x5000d2103601c1282c6004494101860202e8240d00380801402880f0740c14800c034801e1709040400800640076080840300781c0c403036402044a076203050401c07143c00210780800340b100c3c4010380c8004c04001140781603c80c06680c505a10100c40100e81c0c40302c1b4003a05040088040c60750210400003404006501d143e403115064003170410910744403482020314480d02070000c02c10808070100242e58007850380c4a05440348058001eaa0380c0d084403100b9030b13444400d4400d01c00400c0074404075840503050b0405682d104000600214116165a401914290540308003c40541042e004c0c03d500c0321000d000e806500c8010303440b0039a14012407007101d8440c40b100c0b00d044051007111501080b04c0078618030718030350089211080201e42409642070855080d0f8244c0746032118490201485030759080440103100b04d0b44130701446984c40340d071030482c503032646424440d80485410410402003013000c55007145602190078034106203070005542c24803421050210141c401a4004a4400729140d0420015290300420345 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 214896951 1250 214895701 214895717
    0xd0309050a030309030215040b090f0106050a030206030402030307080f0d0b040e10151e0609080715050703120f050109110909011229090106060507020d0f02120a140706 74
    0x900d400da5110200c400003010141d0303940310f003001d051080c801c96014a515040b060750030b00701030810117200c19040e102040035010314006416120014030840d012100050502001940307103808005564100500680c0c06000801280c0006000c450060a82141214a0a88401c0044400d200f201c0c94021542e000314a401c24100644c03031b00040f07035a611007400c05d000c14560140c2c1d140103601449980840380c02035083d00c248402e195011102405e495030740d59130072401030340e849030140d0787d42141c4194007845260001700241c061080c40144082030103803d091411811101d064011901c03c000161290380d03542c0c00500192120b80a019500003411182900304a079903400110704c0481031184102c01c05030001314070100b102250015803410a149004694a4101290b10003802000c944282c401c0d4608070002c00c0c02d50154080d508030613005400c601620115548003001e0011052090340d004488503011808242d00304103d45c4882d00c144103100e002c82043e040c25281800c05e0304018103200443d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 214898201 1250 214896951 214896953
    0x705130e061b030a0504050319051917010605090a050a1d0a1b050c0c0406170d0513062007180b0604060c02091905010f0302030f0606010e060c0c041404050d0309 71
    0x30009903500319000e44da0018144e15030745459459031082820301002e25120300500452941c100d0040c141000b8000d0151654a18851044034141e01e0001c0181002c040d81f001449081e1060018040102010300300d0b800071038440000030a1989190700c144801c00031554100d45003046004207a0b08032500960500c03141200c0700e104001260b001240c081040303008a00702442e10301c00c0115850488028008210860301c51022003840c03200110701c14014820040101c902074800c10448071410800070019950509028048030111241d40801800060400b680ca56402c01404010024400c0004404111103c900701030300761014034181c00d200311800c0c08104002e5820401885046504903003548440d65072900308495100000401d419451a0100204020f8402002c61080d24006c50071240c0c0440068410b694550302110a940011125151207c1c00d05002c0050841038106000340c1b240d04c030220f000324040b15a28a25403080460b11020f00c002e214051168803015140d610701031100d2411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 214899451 1250 214898201 214898251
    0xa020105040501050c0a020d0b040201020607020a080706180209010b040819120318061506110c011d150c07060e0102072106060b030901090605010501020115050d03020705130e06 78
    0x160307101c2c1d03505000c1c00040030300400d1801d001c0c0009035a8001d025a800300442e041c10a240f910454003207025109031004240031358000074502c1c18882d80083c50070b00e006115aa004081d01c1075916030702001000103c8400107aa4240e5154041c00400000c1074540780741c01c6243d890120038900d1451100707030004002d000700e48280b031800c0c603610340342c100030440715584500008401c0401c04050300c0140b03400b082c4104c2d40301c4011280222696603503506680d071460701d1566140d080540b04c81e800305041065110005142421841003008005c15596a00c0003540d5142c60030340c0420035080544d0442402800250382081400400500a00c000c1032811304101e0b6410f44440700703140f91200e80c9902d03000b010401c40c0540010010b40b03104400141c407400e24805160180c42c3c1084201e40003800c0200105203544140310b05205104160385a04c0403624110a205400ba981a010740c114007401d640421181c58020504e00c9030741c1c584000140c40456610203e0806d00c0103402c070348a08118050702d00e14008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 214900701 1250 214899451 214899457
    0x50114010507111c03030b01030b063a06060c0b070c0b0a0222080d08011401020703080912060906040c06140702041a03100b04050a05071704050f07030804090c020a020105 75
    0xa806034000c0f01031808000014422003071a01806600c0302c40d455414200369240d004980c000401b038070203201108070301e01000041e0050b00394049405003401c003228070b20404203100b44000c010341d14900c0300040d9104440c1c030a41e505038010501103070240083ea4100100e00034460380c0b110242c94001e4200840d90340b5074080d00340181c182c030700d4150040386504504806008003034040181040001d4110f6a038460580c131422286028004139401600001c2c0c082c03032090b003007580d0751016805880d03070070308640d2408890b81100c0070307054214030541140752600c0e10070071a0034042c484802c010700c01803a0914251007032200b2a000b00f41085509550a01240c01e010f00340c4a8450381254042215125507140da00540300004030749030300d4403c0c252240903c13011a0720450304800306950030b0049a458201c1c0780144c6405603024070008261455101c0e40381e44049425070410710503406e913440c2d01c0604142503e03018072900301790f170011000101040845002d20a004c6072101e10f0021f8045500542c0000c0c0c00781c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 214901951 1250 214900701 214900703
    0x180c0b0a0e09220c051c050304050103180c030609290403050306010201090b0a0f0e12070602071403070b06040e010b101d03120403020901050a0311040c03020c0f0c0301050114010507 80
    0x3600c0b0701c011944010821054064250806129003c00400780c00c0c007000145035441014004c142488400c04410f003604084002550808015440d00e80390000440080041740000c480c01248400d204002407091010743e0011800342c0702c040b4031608035040c201c44040d2002e88180c80a07070002262401103d64442c102c0e40160141405600c0e5500c41e40140d02510840c08000c0420090f042041a101107640c410b04414826420811003101c0d01c4070030f00c5c1d66607542c80f1078920802e000c0c407001001541d5a00100401846103c01d800040f0804000f280795400c00c04086408849450411607a41424803802021014141c028070082c0d8802c800f08420000741c0c8240c40421a212103038000840c080c1040044400c4040c00303c45091409500880f00c42d00f140c00120300c610200d4000048500c0c200d010442030300d40001d01940c6070300c860002c11008042200c225014107409015031604580306020440c07071078094202070703c0d90100c1001058215001600081414000340c407401902d80d81c0102500c1c001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 214903201 1250 214901951 214901959
    0x315121b06070f0b06101d0f0f03010903200307030e06090a150302071a060f10030b03070303020c12010c120213030b181203090c040b0420070308061e1909180c0b0a0e 73
    0x148c6204040f0b0baa0001c02103020b50550b0820400e1400c0562100201003c2c0d4180c00c14006480c40210982d07450f0720503240041c0000e5032203080321445103003c030b0041c90b000c80020001e0380c540c3e968000308071000f200c14800b140800d501051480034400305081c86115003030056034a10042c07400c100007842000302984224007441010165040c001e00070b034090103860900a08444c070b140d0352850020340e17a0b00113015950090b0100e0a42c6881c48405000e801c0c01c40c201d45d2640c0c00d00b4500c04072007074000d412910000c0b905d0264141c0010120344009400790250164500290414540314122031804081d104550a820020401c000d040000410702000d41c450840d00824040300d8000000e010f047d820460a4100c0358030000801d050b50494010240c0f903109443e12300c0160760380e008001c0b030a2001024040d41b0a016010b0329020310f400c580e0b01c902d1840c01c4402a054540f02c10a900803034103080700828244804150032001e20291780c18040c010000840c4851401d031070000c2c001c00e0000858002401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 214904451 1250 214903201 214903219
    0x302060a060609150813083004021f09091103090c031203070c08040807080102070b1506040329010602030d15180c02120304080315121b06070f0b06101d 67
    0x1001651403040308668011841c80c2d211b48032490204100f0007441d490350f0461101d1042c016140200120307881c4140d0b002040e014401030345150001d2101c0c0d254041c00204140342801237651082441041610724000880d07686034138010400d5440c0032800103c40b0310a611220f044100b614035481200d0b80944185404000c4a94614242d2028003583c2c01410301400b0305400401c0300e01c015400f4224050040d5160030391615440303c02d100e0f06c540782303240b2600058200014400310381c40703881c0040c4164030002c042081b1822291200d200107420313004600180c000080d00041c40f80325001d00108280070307242d4004500c1c41c14601094401da80d9094240e610740716407103040701500901a40c0704186201990b03d549180615010070a58011219031406128070021101e1500301405182d2a401d488001090360503501c1c5904506101c0411100e80d10040401c4000001032280c980315424a108400c90b05150401104000d51107464140000400480c0e282880d8560000d520303006400c40d0903104900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 214905701 1250 214904451 214904461
    0x150203070b010815060904150515090f0405010c02120d09020406080718110307170421090e010504020304020a0b0a02030f0f07021206060a030b090f0a0302060a0606091508 75
    0x4214015408060a1404440000910101c000c00c03800681d884190aa5038580d51764010400c1c05042a070b40035003103050312062400072411540c031268004000200b140310000441000038201c00c812500307800c0700c0e0220001d0004000090056840104c0b42d03001406c40003140050b019018051090880061512100d50314155200e85c1e0040010b003595005648203a51107040621802c0c101034090a1110718000d40d0410311b2400313600350b07405041d40b0f5440828483c04004c0c42c028040014201780c0b20041c1a1103c42da20080e0440011516045d941350308040501e846240340036800140d2184ec040c900400400c40169113005a18058819a0201c0b40d11650140c1d41280385010303100710204808000111042259001e801504500d8070072505038824603089000c3c1c5858500a403595078002d10b09420030b2001640d0000c29a5000460310300700c03085108541030540c030b000680345050300036800150030b00c0300f084414028a8054011130600d914035030324240440683c02d2510344290b0401c401c5d600420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 214906951 1250 214905701 214905703
    0xe090a0204080105012d0e19110a030b090f04050a03050a030b13090b07020c09061023041706010302100318020d0309050301061715040512041e060201151502 69
    0x1c000d4140207000308060744c0c5403c2130252013103081511080504010154526030718101a0440a5907444030400a80da00c2c0c6030500a46040101074509240e6182d02c01120940186400742c00c6000c85a0f40100c0c00290704400c1c041030507806090000a80800c40c100701c0410301c000303501005150f06103403e07969200049000ca0051800a07540c603800802081ca104102d10786400c41950385004200583d00c0b83c54407001680d0310542907000c5600450080002140c515041400d400344860030b04085650104096075052402154202c83c881b003803000c10240440d8803914820088400d103000104410750560300000c2c269001c0300c04200406480b502c0103042c0b00845064440603982c0a0309504080c2c2d13061074007500c0f440080c0189400f940ca082000181c40c0c00101071082500c0c1102c02801c1c420100c1e402600d044a0014425038261160a00e45114540b04000820040c03240c1429a03d4081c42d842c07410341003600701da002d0342c11a0f0501001d600d002cac01d44a01d100881d00c03000b01518410310005816 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 214908201 1250 214906951 214906957
    0x31a0306042303120c070201080c090102101e02040308040e220605040204060b0706050a0e0703030e09131407080606040c021009020a0f0e0901180f03030b01051b0f0d0f0e090a02 78
    0xa6848040c4803002c1c0a100d030140c1d0b000d400d1040c1f007625080d030940d49a000c141c000317000702c1d0b90442c0140d000680e81100c054451f480050045151200c4190f41b00b1485c200c14180d038000c0c0d00840b0b06c1103000504001c104000300c0610b0300440c1d29090001d01a60380440440071043e4401c000c0c0c0503560716400305003150354540c040c40040210f02c10a030340360b07003140c2062801010308030f8038041c0460400580003131020003c5200070680e03926450305400c000c9414144400c064008240060508000e8500c078041810260705a0b111800203000b014802d00301003516085c4000074120030f0145090281211001d40c011440881c0040545000282000c40e80002007280803d54003500540d5164400856040101d20781c0c248a14001e100074011000e00d1a078001928404150107440503d068a2020009100b0740003141c10100514140f82030144801642c20080c3c440b612481030b40e807003c1c0000242c00700c2803203108840c50043c107044007041c080402c0540394000010b1703943e200f950200002014241c0d55419 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 214909451 1250 214908201 214908217
    0x8061203090312030a021309050f0136110c0d0e0109051f0207030602030a0204080c0f06030403050d2a0f090b04090b12070806070818071401120c031a0306042303 71
    0x40004c0c0344c0d40e2801315000278102034406402d1000c0351030020440802403220b102e054401070442c07a4070f08810721041d54a64081c079601c84025505c0e8802602603e07441d2014080c1c01c55854040c240c1403844060290002c05103c08450512440480030001650740d050410002c0c4143c110243c83d61050070070032030170410b0a82005245a1011040c1f1410320410b03401303401034076069001c442c9691248401c0000e541030500359103a1200f03041001a000a1140001d080c0d803201c1020046002e2000042501c0000d80360b5000c50600800c1d44100314502d5404410525586030505000032103038100100c603000c81c880c2c1c1c016000707030036100c81010940c3c0e11019804814030701910700b5242d509454017041c688800d01a0b400c1c00010b84090003140419004181c01c0c06440c841d45c004002a0385040898243c14a600b40c1440c140a903203079000d4003680041c0a03600240ba59a0b60001d00a46200450003030100d00c203210038081c0d4004000c000004803031081207203002c0e83c1da401c1100907505c0810514a94810050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 214910701 1250 214909451 214909477
    0x30a02011b0b0f1905090d2327010503100501030c09030b0a0c091a0a1d040c030c031b050f070204060503030a020328172508061203090312030a02 64
    0x108203d07040207910f41035400b031038510301000662940702020a0030f0b941e00b0740d6a011603400c8000030222482c040d00c0744804030012501c00c68031818101090240c0b03a000a0a0000b00310a540c1c410001c401400504070703401a42402c1c5507081d810003500001c03d400b000d0040605141c4e80e001c0314019140200301e844d00030f6510080300507041c5000302c0040c000d000702d5682e100104a98030000b007107420303c00c4c103550400002d800701c0c9401c1c034081c081c2c02c8500301d18003101e03280c1003410040d010000380c84c0c3c0c2c001c962070b88916440c081203043d21603800a040f1450141e8041648800c000041c1242e035203c1e086400c1003a00109050701c0d00d00720300019004105c02c1e44040d038181300001e11a142d481d004400b03000344d038146034944241c00c0d4068180564a403205c004030000541000000109402e01c558101d410a901602c900d20201303912403801d03a4031401888240124541d08100b0075245040ca000411241405018604245030800420b0751340d41c15610488580c400400098800c070241e40c140c41aa0820305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 214911951 1250 214910701 214910723
    0x10151a040f050102240c0904090302010903201f0e0f0d0e190506340b01050315241801050108130203030301120c03061b110c030a02011b 60
    0x10054485a125114182082807110800101980041565207240604441100c014030070ba40e000a5014401003104800180600000720b03151518850841018441d800000d40b00110b801d01a21a900c5c8004e00000c4205180702000240004280b41100d1001c075190346001d4812400201c019042c1149003002c41d200300e840070036180301c0008421201c010161249440f048800e01400722446180c0f1508081c41c29540d020081410010010001910920015801c5190f1150000c0040e85e0740401400243c240b140940c0c24001d0604215005040440040c4504c030900c280d08554a10005c020b9200301e42c5a0007a4070f841c4081d1010b070110504003d02e983c191404040e007414011100380103440c00680341100080b800441e45110310000c070f070000c0040d803c581c41c00017100041c211465044940760010940000082c55070f004007404002c0c0583e441040c141c07a1100102a600c44c0d10b20040958090312044c4000d0f2004180070b50b0540e0286481000c0302c80f00300245001180d1050010b01c010864 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 214913201 1250 214911951 214911989
    0x20306040302060106090603020901140304020f120c0411180111120406020303010e091501230d0b060f0307030f0308071103030a090303060503070806010e10080a0b06130e1015 77
    0x801e00d90b050b01c45e80d0700c80c3d02032251220f004900300d0203040d00c1a408202d07070210319400b808443d0040c40d807051000300010b00b80714002012600c446400d1244031510340c040d20441c01c4900c0e080c01641e01c0011300c1c103550780c00c3c0150400074200c014101100076060005690780440c1d0843d0500c01060f01e00c6c1016445503642d80d8404000359242e209201d21403141c1b031180c020642c41e50f000320304801131b51f12003400d4840c1d40e401d018056102d03c54240a04440a03120800200243c40c0c885580e94114001d12900100e0300e45031051004a4a0b03035542c0c00c0c0309420420040c4001401454201c22070754051401505d903580c1d100d0190350501c841109011180300c04810425200f515070081c82104e4031a50701032060690310810325649644500880038a40c1000005002120401400075440740d00d040858000355642e0086900300880b5a40c26a0504210402c010036170030030654400001c8800a4200301e41d4000d5642543c990f10344080c4c0c840f4640d00d6031900c80e040c50800701d000740580141c01c001e850701c2005c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 214914451 1250 214913201 214913203
    0x270e100e100303142a0f070605040f090612060902012f0c01051908091006030503030f0f0601050a08070e030105090a0b0a2d02070507092403020f040e0109020306040302 74
    0x250b840110b001403020075804802c03140400665803200c60100c0c055042c2c00c0c41940d10000174014015854240c41030700d54501d02c2c801c0420468008041c04c3e04c480d0b1f83c0f00e090045096542d0f01917004410070908261041161640d10322016a51030b820140c009903041291004848000c100940114203200f060b111344070285080303841000e61502d00d41194030804c0c20900540d001c3c003817001544140e0707076000d00c1c0501840c001d01e02e0343d40c8100c0e1982a65a0001009055011504150030036140c544c4040308000101074a0b19071035400010b407244080c268a04100000c2c010701c1a0b95125041080724404102200c0c041c05041942800040086c4124640140c80a030785e06d10451003583c0404000d408942c2d104500d102d0b22340120071011070202c500c810b000b6105c22100440084410950b8200000740108005200c008042d0a0001c8045040351054a054040d001c0703022041e2a00e00c1403080070030041c0c2d620b0040d80c081900c00c0c0c80c0400c02044002d02d040c0148900080603402d0b000d200104000c040d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 214915701 1250 214914451 214914481
    0x10061805061902100911041508060c030610030605060a03020f1306120b0d0c0303052b0501050a090c0f08060604080714010323010e0c09030d0e01270e100e 68
    0x40550031146480840007070b100c1503808840e400350031183e0011006c0618100340d08454910021b40010600d8070740c2e0382c0b84440c07400408642480314a400030050092520317142a9820004c00d4601d000d106045c10440050520720555070f020713062540c00518010784002034030076a40d1603618400c4940040756075101c00707401701d05924492480d4030300c0c1c0f40140c2818688100a02122500583d00c0b68105041d9a0300307840c5a40503d01c0764440d1040042269043c1d01d0031042c07030441c4d40f0031480c04076165140030103124070540a90000360005050111039034400340e1003450002c1d640c2840c40c000c5140d88644c0c0109a080c8a42c0e00020b5a500603034202180f00e8000c90b00d03001a08100380d8041243d000700840a0355039011030442c0011030f1029000402406550500c065001018400d0b541d2800107034000180c0b8040c1054081c80115050080302200b80d0f030030603041c54960b460340410b00030102580c200360350051002d00130f440704941c010300404c81484604d0b03000409045050195002d0341031500034001001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 214916951 1250 214915701 214915747
    0x10c030506040c0903110d0302031603020a03080f01030803130318030b061507021c060209041b0906050903030403060908160f140106050904110f060f18091006180506 73
    0x180c24100f0b0320388101d1280382950100ca800c070030841072608500040199894580c40e09404510081c080b085404d41c4000703848020610035001071091114501d4064608880100000c11050743e1130010804222000c0c1165442208440d400458000918080d00c5885000340000701c015030480000c01008141401e960045500311900046c01c0c9034081d25820703a22610100075000005107409a50304140344c0d010915203441a18003500b4559410041411a003408801c2c4648120341c0841100750b0360413100701800703003c80745000c510301001407000c25a2442075110040c45c031541d0304440030a011200042c0c0c0d10036440c09500003684c1080b0305010004130350440040c0c0b0300c040000303440071030068148124411660080c00c9030b003940c1d8654941942100d50003060540003640c0806003032181d5201001401c0c0300b00c1070900b058440294400300071814a01c400300d80c0c044c0b12420240b1114844103000c500440340385207451041000f818404180c400784541c001600300300041100601101003011103641c01d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 214918201 1250 214916951 214916959
    0x60a0605040e010e2104050603070302040e06041a060903030c010f0213150c1103010902040501090e0d080108070e1b0a020d081e0c0307020703081803010615090e060d05010c030506 79
    0x800c0b0400c0da5400c0340c0910440302c03c55484030680310710522003241e426140ca00e028001c941007039600c01c00304909a2080701c01c4800241d00007020f10426040485440d0000c100340e404021440b0409144e456080c000d641c4184140e001003100f43c0903039020402c40b0b03e8606840300903c04d21035181000380c00f0b904a403140c14680741140c140450040700c48400d5003070340c03201c81e9203018000c5a16154850044650044c6581554803039041d003016855038010b8034001e040c403d40010b4004c601c81140740c1000001d00d6007200300040c1d80010450380c1c90025015090354000307070410b42c0300e40f03458507840440c1002251803078451401140071880540c01056081b00705900d920703454001d545134190b00b0200348030300103400c07100d00c0043c3c08140c06000b6030016652241c0c0b030f030040f10346a6899488140b129000b085041100c861500c01c1404241070a0003803500a0440034291051070903000d80140c603000d00e0340500c0348444040c034000784041da03030465150101038200e4020019080840d0b4010b01800d000c440203409 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 214919451 1250 214918201 214918211
    0x60608070501110607031a0d0b0f150901170c0a0e0906010902040b16050c0d06020702040b0d0506191d0d0e0901120b0a09020612070f05190804030c05060a060504 71
    0x160b50140403260b50510602c400340c0155500d0710010340041540603e51081780455001444094903501c07442d031803450103a000707149140b0f01404209844100144200344071245400381010300e446070804c082c151100030b5400c450320368420300c1d40ea16042e201d503c42c40e8084590507000641020f8041c0941c002c070705007026901c03c2c3c0e0704c8181c506c081e407245204e040c40d1082e04210f0045c0d40c85070455482d80140c492800d03107600c0907210000414080d42c04030162070240d80082c02004528092003078443c540384c10745031031a03014001e860712515800020a555000b004500342d038442c1c041154402c00c085003000420101044a06102d01c0c0d0f42c400001c81c020100d8410940002203240c03544000d412201d190070542c0c00100305585d980c000203c003400340c102c02511540b00c00c0060b40d810014120940c404000d42c2498a0640b100403e20000007500c601480b2080060514111400608050500c141d04011030151280c1c60111102d4001d00e0300503000e4007901c0180099006242c0014049803070448040c42 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 214920701 1250 214919451 214919459
    0x50606040203040b010b070c0801020a051c09020906010c110301180b070918020703021230010b030c2a031b03030603280f080304020405180c1507080706060807 70
    0x4910040d2809002c001300900104400e25214005000c010f104664a4400640d9004820700b682c1103140e041002c1407000c54000300304110f840200c0182c0840c3c880074070031090b160f000308980d500040c02450400c5036001e003c5080c4456417451004115025001b00010084070b80ca2103200c242c1500d084420241480125000074400c0000c4020358100003140c4c546000302084070320003980154011001d50240e0340c02404008080da02520340154240380c8041d94400c505003001e103c401c05151111030703800f0a0300501100c04824166a4490600c8212580d81d56000f03080214a00a4214201e44020103007110300050380f0100180481042480901400001c018030f0242c50703010486009406501c299101c410700342a064026812506c21110f800c084040354442c0c40c02154000425200301400100380303c21030030680320f003503031040d0b001c0c81d104401e01074a070345c1545542550180d9407055582d08100000d2107200d00444066030b5202e2030b20b95580d40580ba003030700502031900c0380320740030301078bc03c2d00007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 214921951 1250 214920701 214920709
    0xb0604020309070501081801090f0b2206111218010c0f0806060a03150605071a01031a1b28030b0303030a050907150302120705040f0b16050703030c050606 68
    0x2070181d50b091014098071800c0a004440102c1c005003c44070150105c440320b507505c40c00303203d80280103001e04e034014035440950a00480500c07010304442d801c4442e201021002c282d819110100e500d90140c00460311703a002001650a50061607490300890f4070320740c00d104a5410030264020300901041c02404005645c81c42590400080389840002c43c0b68080010000e1a0190042c5031300d29190500044c3c0c02d041c0c000381840119107400040100f200041d911050001444111849000d800b06010107507040d569603035520784000c2840140f828400c404108220b0a070b40c2030031180014040071903120700308007210148020302004940d041c0c3c1005401da04460b8400c0c05034803c8103070007074011880c6413104041c0d01d00a2400824003075960180340404211107940e02d43d40c3c410125540e0b000b503160920409003561041016024805202040108002000c80425001c0440302c00707088480d00c0e420114040341e0680e5141c10010030710300480fa004000c041d0407003011840c1e035001300c0c103e07000b81d07540c1c200b48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 214923201 1250 214921951 214921957
    0x7030209040c14040303050912010216140105010b0d0906060b190e1c02120102070209070306030605180709020a09050d050304060f0c02090112030e0901061d2d03070b0706090b060402 80
    0x80a0f02d001c100014000f0902400c000d102201014000302c1d5240415401242240c010f40100184c0c07801300740000c800d11804044510003201814020041c5501d851510302e11403040d0382c402001c142c0c94070404c0041c0b003c07552000c80142829440142c1d03a10000111200b0298401468408a8201035030010182412410180740c124900b4452030600001d400b0003020311486071032980030359001c009420050700c410484502400d0302d030324081802c505602d480800e44038000c1c408a443c1d00201802ca504200c00a03d000454805540050b500e802010040f40d080c95a80c220940160144a040c0c04004001000b8000c0714115034866a01d4815100304480e5000d000c1c0c0302a500410a4005200c04403810021030320b001c0c882d0a00d10804000310b03001c644c0014003640247c01007040d10325180c182c075607010a888101c071b6040700c0400e643c5015440f40c94840300003c8416040d09882d20142c40a41c408008060260008401017904d031810741c07038a8400307007880c0c0b401100c40703c482c80003040d8681420300039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 214924451 1250 214923201 214923227
    0xa09020f04110a2c010e031006090b090906090a081b0f0325080d1e05090a02030139050705060a0c0306060906081902130f030b13020109151707030209040c 68
    0xd2448074945004c011210b00e6401c910803a41070150144403d40c040940c842c15006020500001c68110110410064407160051010388150003000400c03408000209510300926031103100795403500700d07141513500c140c0304206002c0c41510401100c002c04400010180043c0b03580d030030440802c2c00140a000340e4140c078240000700340f07040c2403105042c0400310b50450402c0007400464800c0f11b4500000f8181540c20948080040390011000801941000c1c080e011640c8818002c2c02d000c807101c080040600f881803004408010404a482602c0b244100100c41e07545412104881c01030178004040c900400003c03070303c0382c0813901c0c0200024110303000d24820790440d11180c8030145a03641e041744840303c8225141c00128401e6080000070301d40310704c4881c101d0140c848004e0400d50399003980360400c41000f01a140100748c800d80424280140e030f1041034034041d00c0d1500d59517500078003e440d0940c3d0243c40f01035641341c43c403170b840204804168564040c1c00f10a07801c0314140240c3c41041e505441554500807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 214925701 1250 214924451 214924517
    0x1902060a0320040303121b0c0b1504050906070f020a0c09021e0f2205030c0121020a27030b01090b06131d0f0f0a09020f04110a 56
    0x414052201c0c080d0b80104840d4101a00d0407203250080b820b440e025511540003240881c560001000c000040ca12074030400c07908025000c2100110326802405043c09448001e10010b000000503a415094081c00c0e0080340000c0c00c18401420016081c6843c0c00342201d0304400900401c5160400610007c0c00300d000383d802007803c0e0051820452040060350062411207a1521381c04410584401020700414605040d40300c031a40f900109840030030742404c40d0420918105001c0d81c10301180d134001c207006034480002d00f48000e00c0751005000b40103030f01d00720390318541c520f101041d03030b003070050304480340082c0da081a0004a00050b26402030403050841c034000600050407120040c400c1480592140c0760042000b0036041c1040241490103001072896005101c0d200c01004024542c0702421418980050030840c182c18146407000072413200610080071803811729110340010302507403282105800c1503100580240500f04c49028003401c20750081d0b07902d20000e504181d00b8200103041100c0807110f085100c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 214926951 1250 214925701 214925707
    0x702070302010c0b09191202070e090c0108071403040f0201030f140103121808010c020712051009030903060c080105010810030201202503110a080a030825020c03190206 74
    0x346803200c1d641303002800e1850900c03680e01160f1084901c42c00d000d007401d22030f00c40202c0340c0402640090070441c80760301c490000f40100d828001106400f04121204810038a41182c4598880c40d0454026a109112041000c0c2c00414070040c8a501c002e45c0d000d0354001e8809214030801c41110004035503c4590003075601d540305006000044c162007003083d4044951a11044200c2d03068a1442e480450398842c400603036449945021443d01400398000800411030b0110102030252951030301c80740804481101c1e255511034500c10540644030310409140c00600410591800c158094000350003802041d01003800a4001203660808503c1c540950383e0681d20001028500d60041101c280f14002d0f0142c180a00d50050391040c040381001c0c001142c2d41c0b080d00c940c240c0346091221900e00d461201c0380c00b83c0302e481c0080c05840b500058001d07800768189001407e035540d1846400b444113501c0d02c03103c01141403a0000100913400074069100c03030022404ea9048440908080c4200e046414009403c10024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 214928057 1106 214926951 214926953
    0x9080d0e28080406111212040501060b0f04030b040f050a050a0c0e07090b0705010605120d08090304150f050c0613060f06050109090902040603080a08010e0702070302010c 75
    0x8040c1c190151101601c1c0c00d1020301c540d0040c8400c0c040003140c0010b400004101e100101c1c103040c0805512241a460f01e40e1002c0010f40d41511258284000425204907031422610002100140940f90070720f16a03031b0138503483c0b000f041924a40c40ca4580302002c50011311101e10080e1044018080a00b590b241c41240c840c8290091000b031140d00c4100710016400203801ea003541c44c41e0825035200c02440c0f030708902401c1a50846034000144d025001d10603140020303c00d50100b90368440700202c0d030341d582c00c0c3d5070b91380624450802c40300103202d0306c031032031a004151790841c0ba60b20b443d10501c4e00448200c0c0d50f14281040c1c8081810300e036242c100f8024425075114600c40120007550a1061524000000b070040394103004440c1c00540d1b40303d91364115656a4000d1f8000c55101c04100e8070f0f80e4000101800d500c0c0c0c02d2081440725622100000c00e410310104103081076980c141c660b041720b00c02d5 = true := by decide +kernel

theorem cover : BRFrame.Cov 214748201 214928057 := by
  have h0 := BRFrame.cov_init 214748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 214748201 ≤ n) (h2 : n < 214928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
