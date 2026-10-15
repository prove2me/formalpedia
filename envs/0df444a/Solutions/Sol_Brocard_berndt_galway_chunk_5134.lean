-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5134
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:51:41.046053+00:00
-- url     : https://prove2.me/submissions/98dbd0f5-1da4-463f-a2a7-f5ad61719445

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 923201438 ≤ n < 923381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 923202688 1250 923201438 923201441
    0x90512160b13140a050d030510050904060b100f0e0613120c080705010e0604050f0a0e040b010306142503180c081002040503030403241404021201020c031c0906 70
    0x1c0e541e5010302d608240d500000d000a000620824000b480c0050190201d1602c90f01c0d03d0b003551140300030416071104045a0030046502448014100040055516007803a103003010042100903542d0740500341d403000c3c504042d030083e042c3c0038a000c00b9485800c1514000410065160b004110802c58160b0254001c00c074403e00c28000c86140e40f0926500002c9810304408c28a04992a0b10560401c0b54841030f031800c54845d0001d131400c43e04c065070701b0b1905240380700c00108407c19540240d003284404070104018814036411050481c2d00038502000780660700f0b070303500c009100215a410240300004010141301210040342c260190354a140004d040310404411400d8406844411b43c0c00c1d009000040c03004100038096401119503400e0218946843c03c80420788078061880302400400c00807041c4460039002c00c5e401440e544405808001d020900303200c5006e4404251416401104850503982d04003805100b25010032202d100110f0400750f200e0041010f84c498030a0b910b10590700d44030340c2400100c0e01d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 923203938 1250 923202688 923202691
    0xf03020d11120a020301080d1b02030303040c14090402060a0f140a0309150e0705090405240106030c11060117030c011b021902010e0607300f03090512160b 68
    0x101c03036542e0750b0021241d0041c10000a44800708240c410001082072000000c1c068146c0303581d504290f031000325480c00f01041c000400c080a9058080001000b0130003449500d4101074510040c01d0000000340d00c130078004032000c101c50003074108004110711040140246881100341480e85400c003054070201406a0107908040f407030f4800301e42c80350802d00030455155044181c10f003880e0000c000c0c8030450030095a449600384209402600168045010f000d0280007042c0031211002520300121001013080301300c81c0d024810030b0002860080c81030784640c03058062455114003000246001d900b02551301003401e0407030100f4a450700c03081280104104003070207103201c43d20f141c80403000c103502604000b0b81419040c052010303a0340c80c0c01003480d0040c0c5c0c00498800900300300381c0d00309882d0740c03140c80c0150101011440e00f05a1030030381d080000b9001e45010160802c1d00650740d0340000d55220010a4003a50300f072a0000380f1603007128000240c20390004020344540821051018404c80094442d9000b0590 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 923205188 1250 923203938 923203961
    0xe0d0203010f1508060402030709051803030115170403120e1e06100515030a0b0a0b16330b01020309060409090b010b0c060a0905010225020901050906100f03020d 71
    0x80b603e89107100162181c191000500d41d01c0d01910180ca01a400651241650701828101d01d07601d0000c9115458200203540d0b1004000080303969a5071680054440000301741c1b4402e001403004100410f162a4181745640226419141c0d030800d10018007a84004e050206c140d4103591243c02c100074130002d205441c11038182c1e100c01c09045e10717003094103d0084800f81a00054028280b0400b11402c4484d4242100c0d032021022200141090f54000043c68510b80380e482070344110f00115402099025070041003907000e03c903000041c80d003024a003205a81d0314400700002c500c0480807804000108158009403150441481502d04e41700c400c000148007500650050005280d03500d0b482010418045c19282c00b50030141076003421f101c04180b41c180d9583e4014000071802d0f40b42c0c0c0b180010420b094044d14100d540c540f0f40500c0c0841c510780ea03900410b6407804160f20078500c40340009405e080c0038600324014500908001c1d00004050320640e84010340c4c5c0711502c04c26908101b1004442540d100c1d02c07440e0903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 923206438 1250 923205188 923205191
    0xd06030309210f0308042303030a0b0f0a090906060302120a050d0203271201050c131a090d0f05070b09190e0610030608120915040609060e0d0203010f 66
    0x40c01c203000b00010b000c41094040c03016007030407842c0300460a011042c0031a0703945854918819511032a0400c0400710b111130104a107000680080e69148005c0f000e07500c58441c6203804c0000840d00c8040040c00c05a845420760044200c0d0414444060581c01111865001d440007065440d520742c040b03400d2010126200790290002d010440c2004014055005c500700144002e5040c400c0d94110038007003212003c034000307642100030f41d80406504c9090743c03000e1160f4907a0003000039141000c0b40e51025031020352001d007071444c0d110020602c03d40100c1101010640031100d10308003907006091220009100000381d0304d414805080300000748041014102400c03100c82b046032503214001c117110716a0f030350400540070394040030020301030520b1b0b031100258840401c0b0313203110b001040d21800381e000b00216004125603010368030100e01c45000d01002040d9001040d00c0b0301164512440400c00e45000d5802802e002450399034041007060700c01e950074214010010824240301965600007421214100401041c89 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 923207688 1250 923206438 923206457
    0x3160c0806061c1e051c02070f090e2e1404050d0e01170a05100510021c090b07050d1e0c080703110f0a170405010e0f04020d060303 58
    0x18480185500400c1500001c05203800c0c0ba40018400300fa03e42d240148000b143c02901c2c0074400103a45190a242d50900c0d45100c070034180c1003280d00c401e00502c21603904d205921803d0742c0c461000888008407052412107841039418856034a016007240c42100355640300e001100c1c41018003420f00609100d07080080c0f5209010034245400680341c40380201501a10424100804240c001c03500600076171007440c000c0c10324482c040041e540c204520090390341030380700c1c6000c0181020856101e60f018403034070b004402c1c84981c1e62023040940368140c1000c60040c3c000e500c810140008030040c18241d00100d040c50b8207100c1d25a0010110340e00410403e41e0f4561141e519a1405500308482100030034851841c0d450120502c13101602e08180101d000b0310010b070025214003458400c000444050000d002a10707050b070f0000300c507070381e071074803149010381d400750450240358032441554007200c08440041c2c50b10044010b0020400080d040302c00c038403a80040d02042152030210715486003201640c441e03211358030704 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 923208938 1250 923207688 923207693
    0xb0705122803150909050c01121d0a171c050c190e1504080706140c15070f021b1315090c120b0141070b07020a080301090e0705030316 59
    0xf100b015a0140c0c40d07803858880c011011503000f00b20104c40704401e003089580d100042d8000700040292a13001c1c4800c008416000d600120040360783c06402c2e002e1440c2554400209040d169244a805054401803004016841505000d504010780c40310032030410328184440085d159091076120442540000d903048038040d20f0749044564055031076031500041c0e00702802c1404a42e41c2c0d02c1d0714082c43e0140042400f000144041c9101110034100e4244240c4088841d00e4005030701e020000c0d2800800702e48a02400d0302d01520002e22182482a550003170381d05500c0c03101c1031040711151490741c241c10a45078400c0401b40364108030342000803e40d090000460741d4441070020810700fa1020100c50f8141000480d40903603900c2006032004240d444425540311429940100c940410b119028000a4681d4400100b04070b001010300021030040c1040000740d80e403583c1c1280c072840c6001009095007002d20041c0848941540201d0032041c00c402180c190a80ba1030020780b45400c241d690391080008440c24004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 923210188 1250 923208938 923208971
    0x311190501051005010822021e0a1a04170c03060f010501180803030a11040906080a0c120b0f091e0c01020d0206070c0609060902090712060b0705122803 67
    0x1e20142c5031020388401c130304000000b404000c0141c007450b030490a214201918075166280e0103ca50741c018030381c40041c40d0301012400c0010b5045101d51041480a00010f0842807002c108006500d012018524050520329060910300e10006428424456000c80e0076850301c04200340f601036540031141034050740c9804001454400172900c07640c501030742c2c40703010000d940002060326001108408041911810365030000f603103014990000502905010002880040108110340818000e6242e5030b865511486d0207403c480c0c59800c024040ba20290008603041401954190081040f100b0350b075543d07401e50081540d00c03468840301311300c0e500042c007082210741e010040c104514119002401142ca41028090070340509608081c0000ea15800840200051a0300a200a03540100b00030b0711400d003d04001d007024105c140340c0a00e980b420101244211607041502d2506500000800d0320100030720036290036030408101074075a040590341c0750b42560130040700070304850a26500002d042810400150 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 923211438 1250 923210188 923210191
    0x9060e06100603090809120319050c01060f03120e2d0f04050708070c030201021b01090302010b03030f04170c06070b0906010e04080724050108010617030412020d031119050105 77
    0x2014146084107070307000a1900810f403251075500b1100402207885551f04a41544502c1c000a0f10b02c02d092002c2e1640c00b80c008000d4008001f00200130400306845000b5030585260500005c1e01d010761100c40680410b01c198102c07022180003409402c101d50807040071503040400075500c07491584100c9040b1086040504190b040c3c000125024002400c00c41009002148040c2c2201c1c10005890113032070074035000750125482c51020560814860348840c50040c021b0940d501c0c120015400c0106441061800000341d650340d103000c0d020685014501920300c0c450b003140c500541400d0040b03104a0344203598810260000c2e5000e0100b10600e440c1c8000b2031824108140c00403240a1641024003011984200c1912856a4030081144200e80301034860980c2c100c584048010250402c4000318405506400c100d085625043c3c209051921014a0035142d002e00d002c3c0301e0401040340c1e410b0015182c0500c011000b0307400381c00e06284002112a5250429044581012a110101000c01c0c2080024491329 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 923212688 1250 923211438 923211449
    0x30e0d0c060b1905010f03090f0c1502011401181401030b0402330306190311180c0d09030909020304081206031f022a070f12050a030c0609060e0610 65
    0x1d43ca800c10034009460300c10240c0502c90401980000702807071140698820b40c6015004610700e10171300160302c3c000300340007018002c1e400340c0360301100ca0341c080300e0050007125240081580d4800351a805d0148070400e8a00107010407c509484441076998603203010000b41c0a5405100028850314081c01484041c2800031148003200085400b60f005051301c03191503005840301c1d031002e00c2d9030347c460000040701d0842c07a540e13983e90180700f0000001002007807005071100740c0003901d8007560034500b0f0a9980720288100e039201440f89041004082469450b4030a0064501c02d0904074102c41e140c8003440c08036081101e0442e8441000203501d440e54803451b511a80c415003c500030881d01c60f05c2d0144284d0852541c141e05040354010484256402048203141e80040034035011040003401800d040c0c1c0c1e504064454860612020080030032901101d0389046403060f0080c00800e0010f0780b0303940c110707a0b00f510110155022aa200c40c407000040342da001d0f45510a001074000d00050078280c0f00100501d6165201 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 923213938 1250 923212688 923212699
    0x30906060a06051c05070c02100806030105061c020f0d0c060f030f0c1209081605150a0902150304110a09150b131406212401080c0901030e0d0c060b 65
    0x8960404130702d449041486402160040760701c2c4ca60f19802d84801110803c020360102d29401c2035842d0781d60001100e0720400c000c032300900039601c4003001e0008201200e4055000300c101100034202506000202603401c5402030042000700100d80c0b201500c0305600d400640003cac1040e0f85143c42c19a140c0918142010440c00c201712100b007014010709001090004800d419481d03940310f01c01c2c07200300400d0f152003c4040c21a107040b031080b803400c552103420321080c4001c0c1070800404101c00c00000e00c920040c0d076030b020744141c2c044440c0d10055122900010f1044501e008100c0e02840d2603250b440510000780108800070856920503c0038002c05130080e08007820325102400440c00c0d0329003200340c410840303a404020072440030112005c10401c0c800d00310301e415085403c07041201140d0012200c240f25507a801100704058544011003141c0c401ca250b11a4005045800850b0701c1c445840000c181c62034050400040005440e00d100c0d041207403400c2d030b0002207540c4e05010b106004090080b006410803c480 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 923215188 1250 923213938 923213947
    0x1e0919051c02070f18152c06030a240c09032303180301090209040c0f1a0a0f1709060108010c081003060902131506030e03090d02010e060f030906060a0605 68
    0x444140c1058207101301c070003c1083e81807840001e00070b540302c0013003907029101ca0200c0c87c0d1500900c07111455049030710f2514101e00356403045104a060a00c0d400384400a018280300a0145c8418208042031501c0e140c28045620905070f58100310301c501c0f8060b43d81b544510f2050ba1071800c0c10005010b140c00780280c41074102054202e01e40020044034203443d200401c01c0750001700c0c000803900500b0302c010001e41210340f1200b40300602140c1d05008044410064008207626112503002c500080c550090b011010310034014090154004c00008035810aa0f14294005614580f810268000c0036030701c0d045c07980c1040005001140081c0103919001e2201c0c24580058100900030040d00402444044e1180760b4441113102113680341909580c001001503014451b031016103c816902842900c56131000c20705d091513140300c0440100940307007086801400a02d8401c10344d0015100080355504481d8001c1c0100100c41416184101440c02a40d817080103000929000d4144481d01c0540c0d001a000d00c1410301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 923216438 1250 923215188 923215199
    0x1120506010207052101151a071a04020d05010c030c081012020d0317090c030606100e0f061c09230d1b170a08010b031e0919051c0207 59
    0x1e5070404413030066840f150642c0007281c200000f2412003280052550920040c030b10a50503180d50941580c01d52580c0310030540c0d20303e407200039034420749000500c0e0f40018150340003110042450710740e009001506240e010006a520542103408400045011980c3d42403800d140da94000092039110f02e4000e04001c809040c0303800c404038401c050000030320500842040d501018450000c814405d4154a54403145003020149c1d40c0d00d91450040c080d001c3e1103410000780a51804810795060f0050a40f60011151b120206004d80111100740b296040f40d020800e01d45049600440b0300307501a02c8540c0013421066a242000020095480c650342031910a1030046085038041056911540242407103d16590103c0a40045005082010700420720040d041c8480842810080100460617503506c5e00d544e80b1a104c10005000607030740409007091594503901101c05400c6417039040000c00040743c2840b110700506082c1c40156510445171a0031040c000306500d010fa42d440d40c41880c1ca030001e808841d0601c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 923217688 1250 923216438 923216443
    0xf06020705040b03031e0717031b0c0a08040f08010608070e190b0a030605070206060307061d130609020a120203091902130903051b12031b1605010605011205060102 72
    0x90060600c40d65640304000c255030740800441c1c00d00e106c40d10700c84820815618028400b6001202c050310071300280c000d000c144000c910308403880788201c40c00681034441c055414081d540c1000075851042e2181c0c100b4030001c183ca250140008000342e044a070080780c10718540d9401d580303855000c3c0e80c8aa10200c0240440e1030085180381d07000c2048883e04218515208444019005906903682c0201050781d02205101c180c0e007080d481040d85800b1626241c0703a00c0181a60b030b1103544111030000760380740d06c50502410104584032107084002c000300e0703a1003500681502168000c1e44a4400544c0c000b178a101c15540001484d00301c5e0b003400313a08505506d0701c030500b65107076000c01054040440390280d00608540c0c807446001900040c00a042100311110303e8050415802403090700f5081c59010708000c580d0000041d0401030000d20401641551184d051b44074513a40010704120000105120001109407007503440b0031070340e000e2400403441d03626080002d80ba0342154140040e0103403c00003005080e9800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 923218938 1250 923217688 923217703
    0x80424090c0b0408010c0206131e0b0a0f0b1c080c03090a230d0309181404030f080c070c09020318030a03020406030506010806090f060316060c0c470316090f0602 71
    0x10901c0748803548504540400032b071304002c000700204400f1080c02041d190550000c855000741200801003101711800f003001180d15141038440c2150b01e00340e40310000310f451028000710461402143c0c01c02d840a0300065200780d49410982c0008105075040d5a009038145080c505c001081c0c55601402c0d50300c0c1c074000c20740d1000d400b03080a1041014400c00c001642070384418898801000c02141c1ca040078034000301061502148500024580000309440502400c1140c8825038800d2540d100249007410b0400a90002000094000d0440b2203a8010f070106100901d40b00c140d603640181c4d9242814030180c121100a4003c5040250f0303074080084540b00c0202d89500001e420540e02620364910300040e24009140326008a40d43d16603c00107400c58200e1150b41240e072203101804038640d200d810742d004400010003c4014104032030075074130031414024002e1450b01c2c1203201e00c0805013110000303502c1d294802d4403100c469035590203140101a5002400340c02421500078040320461070808001e680341103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 923220188 1250 923218938 923218943
    0xb07030c08150105161b05220905010e0601031b0b0a0e0d0f170a0909021201151205040812060406050a090c09081605010f080424090c0b0408010c020613 67
    0x60b0b4090106242c3c1c0140c003179500e0720404416481c0712884920b4009001c05401300c015002c000c000074007007802d20300400c2c2040c03c45813160450045804042584014080106050790655618841c10ba400601442420302a5005035108030403401044545208403010364855818448244004245e8591244c01c0da1050101201e02e010f041c0b07003e040440321071002042c01003502130102402114000b18001920040b46d40b61074003c6e41954901e5540281c0c410191291200b542c200b00600c0034202401c01e0880c201c440d0328007903070500f410341201002c403032090b50151800040410608805148006050b9119a007a1000e000d95482c000100f01c40c00d640b400703a98103054440c116044a04c0c400c03d1040c004007078007000c0399803c88031340410b051070311003602409e80080c0d030710360110004a0040005900656101c48103c180c900150f41d01401303a48800c1e40c981040352141c600c54040b40c002d44251019041034502c8907540d170300e00031696085030300904c0082c055401c8503040012142c40744015442864 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 923221438 1250 923220188 923220211
    0x108060402010c0b1f090f18020d02042f0405090603030c070b0a0e0a0b0918040b0c0913090302070f06020a0309050d0309030b0f060414040f0f05190b040b07030c08 72
    0x413120f50890300f001c1c2902c140740c0203011074200001100c50403504901c007c00440706040041c40f1500140402d64003000001070742008000010000605041d40041c40781a00e11041d900098000b804030b8000c00a000d100d407805e128003040501c003d180100c11b45800c04400c40040d890001001c00040d165500c9109040d02c2c008040341155070540529141c12130800e000745604409529248100956000700c19428003c814401c808001c0c00c8044011a002d2a00001c04c041d030b554581d5a41320313180e80700c40c0425030480c80c0b480301c5c481100c240d4081c0c006164800e4002d480c80f03c2c00c0500e05202a0032030344c405000c41d0301800d41140886d070003104000c16a2021f42c1c1d0481c1c0c2d2955404c0a840d1032103a80e00090000390101d00f00120350300f0103d601c600a5400720b50a000030f80b032540700c404000b81c0645002c0c025401183e0042e00007102c00c08002481403040c01034561031a0300700d84100710201e0142059030b2203a0b00000300405c01074a03000403588080142810411280074030030051403200010548540e15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 923222688 1250 923221438 923221441
    0x304050d050301030b460501290a05091305150105180d0516060f02010506030c01090608060d1b091104140d050a240f050910020d020408031b060108060402010c0b 71
    0x8504807503d80c8240c0c1078902804942091681800314981c003030000c0d06c64540c0707440c0000c990400c00820700e5040d620b50750001641c5944018030803d0300c3e80000c000e1400d100d410418820552074110403800b85010101c00003450f13140c40c84aa4a0f00b00c01c08503020b0400004001c0c0480709840318044183c14401a10309112050151801d140f07409558036001c03601c3d901110001940c2d40d40315156031201e0260f54000d1225458485c00d0540d681728445d0018080391941c481448583c0c80384000e00c0d0b01507001003144640803500d40705e413030480d54480751401c00c04011b240140300c01100c03801030311444241c08541c40d03d0186000b240007200e00101c050325100d4a0302030190001c0c480f04224000841da005a5986121141a011499400d070300402001c005405c0403407440ca0071f1a00c1c4161803003024800003a01c030380480c00407090020341c88010b510701c0c0241c5c21b001c0400c003041d00700090890244040c8040c0c4000040b0903819140c0705050340710302c450b580044100b00040c1d0f07010041e040165403045c0b103200e45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 923223938 1250 923222688 923222731
    0xf12030a0e101505120d08070e0325051908030a0e062101030b07030504170c120708091504210606050306070804020a09060506220e0406020304050d050301030b 70
    0x10102c1c40b058890000303042c821050316410960704001c0c2140c204a0f20300e42e9841320078a00c5500e41c030305032403050089041000001d45c414004c514500d40c95900500792520000c045c58082d000b211030f1220341000030210b132030074411410100040240c03403c20321a21200149000140c556a1150214007410400750110030a101d44070700d41514448040350f07aa00d6496a060301904010300000d200680c0c04018032408100018020f100301c9000d1500b005000810031011075081509902020010043d0f00c9004900c001c5500c241d03001c2d06216205000721907031035410300200410b4040051002c0e41800d0100010010840c4a480f0b020403a0010140b05500381c1840c14004028003650b84100d41501400c0100603405610100f9240704500c01c403030503120641c683d00003400f2580b841c0640360f04800c040144914284503101111107002c10100389011098035500c6900e00324030203440171540300d9004410b01003000b0081c4891014001d4900d040d81c11585142c482e20049a000b0300340f007411195820300c2911 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 923225188 1250 923223938 923223943
    0x501170a1205040f120b01091b11160b0c06092a150c030901083108130f0315090b04031803080f0c06060406060801060513050a06030b01020f12030a0e 66
    0x10116a4810310007207569074012414007842143c115007501c6c00100104424145210b0b0050386180c2d00d00c0801076942c0740170180c640303850005908081e88508000d02c1201004218420068842007150075181d440050703004d0328140f4050f0991842da0003150035110010700204d800f544101180320b03c450800c5200001c0b0b07035580b400600c0d403400d1820008040d98042400001004400c4080e030b0342c12856030b46c0d502c10350220703141ca2540c0e006201c0071400d08000103152184000c60310b030080321030903c1d24003c2c002c0300418080b254400c980408580b4410418000c20750300042c40d10b4241c1c0003d201a40c540d40d1064100900100020300388960300c0721890300c81c000d00c101400515403100c40d081d0346040310001071109070026000103143d0f00c1008002411800d10740904011110251602c0d061070742405000d49a40d003041c124400c54800c12200010103a480300c0c0d03403900810340e54400040d84040ba100080c10850038842401e001da12286840364a500560100c95100011036400501506880e1b1046d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 923226438 1250 923225188 923225197
    0xc030c09060121020412120e042c0102090a060c121e030515040501290c0604060b1201051330140f0f0315030601030503030a0c0c05031c0501170a1205 66
    0x12041403880a1102080940202c080854107c3e850741c002c1c1c8012a0204020f840c004500070001440c452004900509840d10858410700d5100000d070502101002248a040042d4040000035045c00c0402e41482038004024051450a00e402c09120300c01c98001402121007181480c10580c0e2940000d84410b507400303d502c5094001001482a9691502c070250200c10500c0b980ca1a000301c07044200c02c4440d00400c50301c0c0164414060300303560f03440381ca0740d0b0700510704480c029400801c820080c010094081c070903917100721909060b07000300040c01d00f08030348007002c0c0604d5040c541d201c1992414000303002540005926035607141c000500400d036405854640510402245c4c80c00021543c0c0c80341b800c2d10009107104203809070703d51240320043c90800d559400300703103c0a40a50404c00104400c010303940c100d82d24030525420b268161130300d250f403210314550122112b19030784810042040b146008501a960040c40c440800c0028404e4070210b0305d0311011020b00082680a2030150000c1550190041c1c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 923227688 1250 923226438 923226449
    0x10080c180609091015030c080109110f1c0515031507021f050117071203030f0b0a09090507050f060d050405192301090f0b100312020c030c090601210204 67
    0x44006007800c045107000c4e031030746001d40c80403004e58191000c1141d1081c8203085100b021580d91003110791818281c9030061070b80c0340c41e4003002d403c1040103000014107180104464140102100680d22640c2150401ca40015102441d80c200b09003468260340d9000840041c4061a8050310791241c440540070b82c074181110348034415680d211000c0d80455225603212a0480c0e20a8841d408a00031f40505e0710744175032040c007a281c4000881c00c0c0301804248a903000303400f003000d0744400085403c80d43c00025405152940058070313043d19150084c003004000e0040000034541034420409000500e40081e80703900400d6000203078690340d44001418420100b00d88070b604101b6040c0f030040990384d42414a88100456605078044580e514580d015810501c11032020f40e8000c0320110b0041841d9803094019080a030515200084440c00800821041111003000d2002030b001003240400354400d2508284600089074801d01e80c1d5030410280f42d0b00005001038048800355401851401c0702e145000070700898010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 923228938 1250 923227688 923227699
    0x20c09070905010809120406050d0612111c0305090f04020d0c05040f0f080d050a050d1508010e0708100b1206070503180d17101e0510080c180609 64
    0x18819030940014401c82503510aa90300032981e0343e98020b140d601d00c2c104008880c4c1c018104010040140f08d8230291000d0310900b1000706440f95035078000d00c81c02e0900442502c0c6084001c1c0c128141d4944031500d1001c400c03c049003080c034108a80c80c05050780c050310f10046c3c000e01c14400f81130b0540d541c1c0e80c115842c1d10498081017202c04103085008110340c01c40d008807100d1014203c0e020030340150044481040341e032980020a02c0c801d000d00700301c0c1c1c950802c0381c01c2c20600a013070091940c40440c1d400b840210319074110400010030b141103032003420f40d80e84001c00c4500c0c0d0404a024041c3c0a40441e81500c0c1d80f0710803030701007009a03815000c20410681d8101c4a1440e000c0c2c45d0611610907072140086005401f103c8000c9801488204869106c1010180c11408102d000907900840c2c01c402e44400c0e1f0101c0280038094906a03280514100414030591031a00180d11810a100a01d060f04608051852520b0164501d1401da041e4160612039080c51110703840705003007400015a0744c00704450400901800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 923230188 1250 923228938 923228941
    0x4050d0824130b03120c010b0303131505071406071404061202160b07050c0c01080105130903090803070c0f060c020915030709021903060501320706021201140103061d07020c09 77
    0x28151201d1b00030075003040165003484a2114035190000a072810001d003800c0c00c81410b0716002c400e00d40c0c01003000040c07050000c1444800302145401501c00e240051040c0a04214646040000c0120211840c0845800414002403104540c0000e0031000b002c4025001660780d202c07800729603c056840c1000038401171039002001462980840076020403119041190040c1284c02d0056800c04401d0090350303000740e070001c1c0002030481103402c40c2085a000e420444882070b111101c0c00d08651048000f0380d01c0c0034070b0090401824404500140c010b0040b86401e00829030258001401490050180682a40022440d8170140d40034045c0c076001b4000008110350303034500942140c918510f9070410001003440d10000042035401205640f4828400c2d500c4d89902c0e405000e0146052204490300002e41da80a01c081400940144000c01c02008541c50012080d0714007040d021711a802c03007103614101400d041017080140e407042c0c05020001e00424104c000781e80c2d2044124074142c070003005543e004090700d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 923231438 1250 923230188 923230213
    0x804020609041815060b0904090f050d0c03120b06041205070e01090902100e01122003090a05160303020a020904030e0919060e040206220b0304050d0824130b03 70
    0x3010224418440d460b01a0b8064070a11460201c0e00b0510844241b10010071004505241c03541c0321405091180c5201c69000849407106031a10001c0390410010500c0001c0003400d00d81c0002181f605402c00502c2840201c20b4140407480b01c0c01903111721003001c00640d585508020341400810085c000805002d00e040da99016014081c0044090581c003605041420000c0780d0f00c66140a0b401c070360180c5903603400e0001d000c02100241800311000b40c0c9408031810b100204a42c8100850281e03250714000e180d52100307400c20781d0030803524400d0302554043c640010000640c0205d880196241c0444452107181d1b51800c2c15902c6420070120707260703c80c5051040226804000c111a50b030750740d0b141010040c203a1582420403a528050303a01035402801800020503800104c2003810090711841350544601e55242800942a001620110b070395030011030351583c4195001000681c09480440300c0c00c4008d04c00c4419034030010800708000d00842d0001c00c29443d02c201c5410000c4040070250807201000e8092 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 923232688 1250 923231438 923231471
    0x16260307050d0c0203160803060406050409150606091d22050d0f0201020f1c0204030b07121107022103130303080912040302030d050319090f11030601060906080402060904 75
    0x40c2c02d405800b03281694441c68544000140d81e001d50959020348003501380c030b8440c8009500010708455000341c5071030003c601521a401261091881100303406901c496100221301030710750380d03048402040107007001089a4602c110b00240000c486620200840e02e6410500c01401d45c0504404001c80c4452802410010300103040f0200b044a556045c00b01400034004a00707074491241e564210a034180034000c00340d01c010391410f00740d50402c00e00510b89075407a42c4000302c40304202d40c0480890f0300d4103205801005580038105014038a000c000b0314018055001640714485085080320340300796503004d40012042001110050480c207041805c03016600d14000b000c015003212103000c5400b40355a50140903444609440c15039a00402a04100001800803103c0d42c0004003180b23000710803a5000304d044c6900d4490b03c1e0003940692040342c0402d0741402c0c00303421840c1d1001c529020b41d002e41c0040100d103034861034080030b8070114030380010503032501e00000320709006d0741015030790003460040300d9450b90020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 923233938 1250 923232688 923232697
    0xa03051e011403070603050c07080c0c150304110604180506040e0f0a03030f0204060e090c09150307020c010806010e010e151912060303050a1b0b090619021626030705 73
    0x49040f03130395650701c0301802c405803402541c000940000500041000404900c0580f082c030000504681c600c6e400e4800190f009601034005085540b000024001031044085d031180346404140c5009281a00c0c0c5003104440c032440c00400f40794195184041190b55031030ba0001c00c2a0b070104d1084410816081c60125143c500102007140841c1c035002c010500b4252500980e001c03684103450303140e44144064180100e00d00001e01d080740107072003008072607029581c4c681c507103142101d805d201e04e80f00c3c036000c00d02074903100c81c4011a82c1485184020807207103a03884100586003010a00e01840c0c02c20b20b090100c0d10422803006c10200d81180415411800079405282c10300c400710350343d10881007080c000d40c24412176203140009130014200f00210000a409a2070070103200c9503811011072549a01d481d60034070030409503400d010640080b4244a045070392250307440203420004a04520f00039400046503029980014010501c003a645481d0403508490400c10b181c1221740324515a680c07a103a071000308564003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 923235188 1250 923233938 923233979
    0x20d0c020d111513080c0904030c03020f070618061b120203040e0a051f06090e19140f0a11180303190c0317071b0212010e01050406050114060a03051e01 67
    0x100b130000303104000001d484440980140c8046225262501c0c102d510b82d01d9400c1c20741c1984503c001036009403000b0032182d002400565240c0e5001c40000c4203199084089a02100400c840040c10200d002c03140c80001d81c1c85c95001d02d0041110b0039008080e401d600407030303005220403038a8004016510741c10b900064403610040c0e80501080c0c2004110b07403074600d100c2c09200001002401c0c140480411003010319082403100b101047c01001e088080700940e181c1030007002c1060f992506011080c02c0450420b80c020380c024006100c0f0600000e480541b5004615000401c13450707001c481c0859480a100304d070f0311900803c03070320164040440009840703240a542c0441c001980000946682e000d400015030144001e07035a50301081180000038120321002403411790744018108050186201c0c2481250f041c00304280020800d40b6040c14001e040b29816404071064000084003124143c2e103900032524401c03d00c0c20f0000e004d0720f54203182150048605905206007a00740004a0301c001a040560020300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 923236438 1250 923235188 923235217
    0x3030922020f12180316030c0f06020c0105011a16021311070c06030b091501110607020c1c03080c0d06030f0c03060b0d03020c10170106030605010906020d0c020d1115 73
    0x4035140604d80c10b840f01007040381000c0c0c106018034010f2004060710a100540245403445100f6426214100e01220340082200c52960000d00d05080c54000e01a160041450768529110165290806040d621800c60803c2525406003482d40855803004400c01310400344100030003480ca904510800c01b0345c000102990b10305800c0a0001e500c80c402c2c02405819507014089841036280c82900340500b1026205003070501600000803c540308041000301e10410711940180501905402400381000d84402034807084d0107101540004a0781190382640c00030413815006507a014402c50007401403496401c02020800500d080c6010300100d488500103070381c0502c404101d414903080400680b4081803000074096005440e40390b015140030107244208000c10b040c12042c210031400304040703140e0241c00200110741c0d01c0e10148060750703101c184100501070b2400200496440940f001e460f600030054001d125600c40400441080f800c440200d030340000140601000300b1030b04210340e00c00c1d0000f07002c6c5e0725000e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 923237688 1250 923236438 923236441
    0x70e010b04030c120503070b04030f0908370c0303020c0f2e05090406030c031b031509080405040c0f030b0411160218013203030922020f12 61
    0x80d240c003421079040741d50001041010501d480c074400000540581e017640c85000502c051702c007041400f0340c0c4902c542e100e542c61000c22a20352601030550304954100e1201c41c2c2c0202800e00494510a9151a1810b0095000d80d4034068142c00703d0381800810360700030a440050880042016000288000b0b080c404030f45400c4100380301028003802038583d00108401c8608006680b01e5000e03a1948250052560700d401071401c480c00d030124003900c295500854108041034401c000303200400c1c0051103907845003451136028528544030301e031103901500e0105100e190b8840d07041041148001c1242e0043c04007030424409604508800f9000c000d4008039480130900341103442c0a40e00c1e0130b210f20143d0003a00c0140600740b4400c5070040c02811440d180c07c0703821040000e400d03082260240a800c2c000c000c0180c544d002c819805d45080280400010030406803c0310003100901644c0102c1610799211003900e07142000140c960481094580341c03102840058070014161034903421003002441c0114424080f103000e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 923238938 1250 923237688 923237699
    0x30c0a060f1b03020d0c0213090803180a0b1605040312020f01060801021608090d0b010e1e0402090106050c07030605010602300403021306091107050d09080304051012050702070e01 79
    0xd0410868008005803c10850700494500030000001050b0020323204190b2401030200c010304950741c005043c2c0c1e062202104112100c41018092040c503100701004d0420311440f90fa5001980382c0c0502001c0d060502c60703084840c40c0e44545c060701c00a41c3c0190442c07240c41e078040d00180d2074804000146c4203a5003080300209002c0c405000b200e410301201880045a8005a2114422a00907015807036010325900d2024000c5009061007c0c00b070006985120a00e08000d0901da400001105078290304200703000070007026036074a0042130b046554504101d5070301c90100e003081c1d0a10440e9040141054a0000049200356001540c031011082da80c60319142c0c4107445043c041c09000445440100e0442004144014100402d010344100d03454000030500c40d072901540c6050fa400b05aa517540b0321408600324040c8542000407010f1030455041506c04181044034040d00c030300c114045c203030042e2001049640040d105c0d0b014400031401c0142c00304807a00340b5030f4001b03481301658442c255845405c5800490b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 923240188 1250 923238938 923238977
    0x3040803150d03120b0103020706060e09150c07021005071506140405010b04060c051603050c04050f0f1b070c150306081b1903151d030c100b030c0a060f 67
    0x10540e403d600d03006280c0405510700005040720b01c07585410035400b440701000080c5280916400ba0440b82c0c40c8052500d8040c240701d1401c800140000d046000704d5040c80b003452032000444800a4050700c00e02200701e1030b02c0040d079186c031501c20000c2c201240c03001c0313002c0d00191940c04541918800000001c046401d80c0030081520b800f8021000045001c0000308001c5024034030140305103100311b0641d1b00d641170101c05145d084460354019166604403244e504058034080c45002c2d07020340f0b02002000c003410000355501c03000e8001086e4401c1641d00b1840c021201c3c0068056030241640310f070400424540360404010f00c8248106564003003828a200855452000704540b0f400803001140c001c1110a00800c01c40341e14003d140c01c0d8032590801c80048082151449d1068003080500c00c0458002007400400c1c2c07502036100091145038005110744502030f04040fa01018265035100c011480b0203843d8000390900041d03606956001c01101030002e50681c00c1000f00d0040710043d1a4030524042802075480d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 923241438 1250 923240188 923240209
    0x50706080601020a030806040b030f0a050c0406090e060402040510080703080c060c0325090314010207051c05090d02040e030c0a052401050424080304090509070506030c03070e060304080315 83
    0x80101b0030010010b80982407035403044080c4100241240d01103800c05c4202401c10001000c02da821380c001d0700e10b030401410140114802055580c108001440c0c040303000a1305c603440504020711642d00c41e0003040b0b003a00004018400b804000e000c0d10b221558034a000c00155216064620080c0550760008048491400a0b039208444000141c034000044031000d45005440500010901002300400300101e402c00c010000c0030741c01280010380ea05a1400c05914040c25130002c110f080102880d05102e07251b000060380c021a20030b80c1d10040040080c40014058000750040001c40d20020039000b0780c40c4000500d40c4211401103064404108141c41007a805800920000c24900e114030b004000b030341001d601c4402da250803c2c5030140300024040c2c6003012214968030214117584041020701060300e10b44100b0b50421800002081c201c3e20300380c0814030350300004001310f1900901100140003d4061402e030256480001d1010303540e4940f40c94a0b540c183c1040d1010200e1820302c0516000c02c4c2804070809 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 923242688 1250 923241438 923241443
    0x3080f0103050a15020c0d09030209060d050c0f06160c051f080402010e04091403131d070c050a050706080103200d080309010902091003050c010c03120507030204030f050706080601020a 81
    0xa144501007600d41000b00801300c004000f40a40c05c0011a200d0342c000d1002456034416541c440c14054518010080c8124010306028441c0c0f03541303401c0d000013800c001900051840c0980f0480035013094200060b130a40200b0411400c8803c030140c01204100c11a4081070a0303038011100324100e01302e00c0705e800800f46085086280810322900100d0090760050044041d9000000c10105034151070b40d4991940c4242500c5035152035002007140584803140c0c01855000d800d000450040303024500b00c03081892030020300080e0a000f003e081000038400c06015032000c01707401c0320480321004d90b10700c00203019880034401074841522080c5031010038440b071802040b498000030462408141039460b0754030f1a60018040c40b03220340d6074501100041c0c542c2018030388142c03400c0300e211620f6403031420864140070201e500c01e8108142c0048240010350031404142460b01d071003400192640d00c104080c0c1c000d1045400181002c51409404000c00400103031789015110b503076850103c1500c0f90401641d98040d002c1e0300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 923243938 1250 923242688 923242693
    0xe0a1d011a121b0d050105091338012301090308030604050c0c0d021b090f0403030906110301032022020f0906033102130506011e0c03080f010305 64
    0x41104001441e2241e030f40050100303044000240c1c8001140c649035000c0d40b2483d40c0c0c203071240010819460220f804a40c0700120428040612903603550300d81045011a03080d5000020b8010400b043c285041400400010a07a0100d061961100c80f54440031400c0a006c02c41c910800241207299440f44141004882c5d0040e07282d070454443c1010000138141c01054804104000d202000d0001000c01c40e1090691450300a001541403091100d460305081148141c0150200d03414000c03016401d0294990150701480c001035905450701d8040301500c01c1e500980c6a05038040008020310008045520081d0106074a0b0440010360350140112001e41100329401030000362201200304c801ea400500b00e41c503404c020350740b0380020400041c06541066643c80c00301004042075001e001d03140c6510780e0780000e01d640303818030a00385a80042c20007003551010a01141d281c2c408900c03140d004c1d80d0302131099090075a04919a0005040003415070081400c20b90014155402240000c007420a000c0d041c8c9800402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 923245188 1250 923243938 923243947
    0x70816030819020403200d05070f060912020603010320100e0415050f0d0507050a0906051002010e0d0f0e0d0302030310090207080d020a0909110901110d0f0f0e0a1d011a 74
    0x900f1981e6511b10021908505080c402400040044c000003029004618443c003440b41000702c02840c607103c0340c01144d4001803401001d409640d4441c00d4034112544404161021509854130001150a002d40b0607000200a041d80c0120f40c1c008001224640c03050302c040110809a09810120601a100781ea811005805a003c441d00385180300442d0b43d4002c00407259056600d40c08210100c0c01c80c0d0025810581c0c40c8420b00072403400c0c1c070b54100b4245061000303201c0c0440e91100c1544441c0c190b00c1c070b82c050000c09007881c204103001c1d0703501d020b5401008118040da40c4407420040e4581c0d201b16200403013112012008034041c030441c801d40b246550444903050401c014041164000e511040c1c260090040036140000c03125054043c010440618074501c941f6100044009452052482c00e2030106070004a401e42c1c4859000381e01440404061601d4490043c501d1010303926010424405500980031140100f000d07441900c10103580440700160451980c1e0f0b40200354500740088003e010307030440400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 923246438 1250 923245188 923245223
    0x50a1404120e041e051b03190b0f030609010e16030f0b041a16090906180c1e0302070c05060309070603050702190b060306100b040b070816030819020403 67
    0x1182001d005001070300000f10b1002d200401494105200d50101303c03070f51102c0030026485405003011003250b084006031415810501000d01c03200d04264520264295102000c01259407105d403110311401740541914038608019507018040c245512840202c0e110b16050b000c18007041134544000c072608a104680210000d0740c601c00c4580b0040c01c2942c01c0003540544201201d80c104d0b000380a080c20603903611000304c141c0c0e40607182c4002503000701c0c14549000010041d02c0040315600300c80d40c070503400c0025801030000d000d4501d41e01c0a1501c0b0f6900340c505042c07001c03045e0964001c1c0380340c1c0d00918031042d403145d41e0000c202e220300c4111681c607900e82080d2402c0225a009170000f40c0c200d40c0500645816210519812241d0f06500340b00381d52042d152003e02c021801c05000654100285081c1420b1460802840d580a44181c2c46403214048000480c4070a000030001a141c444034861000208105203050040c0b40060a564405c3c6410280390022200001403080760212644145820002c10004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 923247688 1250 923246438 923246447
    0x100f0302030c040e070908010c08060904020103090f0c0b090f03010911010f0e03060f19062409180501030b01091406101e032012041b030c060201050a140412 69
    0x9000802054420f00c0042449883c1407582840340c43d2941d0f8184c5a1440d040d000d0742500d510404080034450390806000e0310381ca0303000312994440d0b0282004511900da920f4006850443c40a000d0000f13011110042203000764a4010512106e0850385100c0c82c40013502050b088802110005181461054400c07009500405524000b01c1d828100410b140c5d1004c0c000c030b030500e2022100c182000014008010b403c0d40050580824101e65500030400f80c2d042800068801c08008180720201c50313080242e640300c500c10301c4804003400350315030040310307024030f400f1104040d0130280021900b00b401f0b0000411211118801d481154140352012461030711000140145207080e50b000700304010034545010080d0211112007111284540c1d0001494090281d0300c01d05814503480c40c0000c07090410040d428485c00600180c1c129030031488131074280c0d4400b090b1303201d1240940c0c4020f02d68407605000052941d0113501031849600c0031a0300340302c1840e1962082003400c400b10340003081c1e00d146808504143d4440c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 923248938 1250 923247688 923247691
    0x607030305061f050304061b20030f0c07080d0c110d03050f12040506070f020304091802130f1a180601030e0109050619020a050d020a1403040f0c05100f030203 70
    0x14140751680800d01c0d00043da20000d440c1c903800400e200000384410040e1511546030204103103415141e036a0082e08000345514000c10b8420800c3c802e5440101030540c1c14412035280c40d14001926036902e201c4032040d6202c1405110361440c601034400c03c804100d0299007820901031340301d80415010302c0a01c0030420110040b43c0d0650400601740b000380041070f603607002404080b200742209151840d017841d0285c071b002c0300100b800041019410043c05003603000025503080e910070603000f2450b100c0e21211035402000040300a0b6210741164200c28040300c1c9a44010f500c802c100c4c100380072009204042000c242c0802507415000384815403889003240c2030b007000d985c00010515000c15822105849903080d41d0040c40d09031440d030400000d04c2181400c20846490b0a801041306508002c24070002030014014203c441907950740006540c404a4410b861051a2546100310345441303003040d0070032000b0940494000c642c403096201c4c02181d146400a500c0141c0d40ca580e603256100c144141d02100030303400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 923250188 1250 923248938 923248951
    0x20a0210020f0d0c0302120403060e0d022103130b10030501200a050309121b013e0d06030c08160e150406121208070315140315181005060607030305 65
    0x1d28407e803034150b404400204003c1d401030300e020880b00c000030300140c101104a0202c50542d4010114400c8061250211940102d03958031425103d6444850030103240c41c11100080a5103412004c114003401c50200380d10549020b030008005501000f2604a0030b1580098110044141400744071882441a4019503002c0e81c28026103558001020070003481d60002180c0b00300000b4140c14110718800c01344241c2c1402980c0341e80d03d200641809080e960b4030101f40c4101e00c451112403840e449034000358800c48107406285001002143d60380d061031450f410a0740650207940c040c00c5003400b01406452401801d88411160b825002e07254460b41c2104105040c880c40e0b08951145000908100543c6400e80d80900891406180070542540141403c900400e40d006052401c1e84260380d2031240b01c0004180d4032001030b10015107080c64006031070188001483c010345404441001460720900c8004103d0b501600121108884122072640944400725003698020f03500303116850100b8440d4024940081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 923251438 1250 923250188 923250193
    0xc0b0a0c110111090f030a0b0c13170606010e030a050d1b02040f1b080f0601030209060f0a030c020c0109030b0f0a02040308030723180103052203020a0210020f0d0c0302 74
    0x5059004581c20340d01c081c0078000c000b039408904c554617400d190300c60f209122421030190000d0710031a6586402000e001e426441d00b59004143c030312a13104100c0070f4070041c0c1030790034004010203030081116030380f103200710345680c0043d9101251141904000a000d602e80340d0010143c170100700c1c0320310101c0301d040104225034041c0c0c1c2c582c400400913840754801c4000c12181d1000c04aa006444c0280d03000741041080e5801c01c020381d040812414084c49204a40c000009280c0581e40c0c0c444600040c28078050f10310305440154000880c01c07245501513110314240200e44d005d9611a0100c0b00066070b120580384800351506c1c00002c0000c10317180942d04003641c41507540340c005003016141e480381c840580044840d040486c44e46e85403200b014100040340300303045241e000000d01d4040180c450301401e03401c400f802d50505885201148a40945914660360405c04020403401c0c2411401c000317580d6920900c050740954074840000c12000d101041c00007156101800904070344404a10469951680710020340460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 923252688 1250 923251438 923251457
    0x81207050c1002370803010801050903030402010504090504110402030f0f0916030204050907031b0f1e0e040c0503010f0b0f0604060801170102070501052e030b011202030106030b0a0c08070c0b0a0c 86
    0x10b544006504c40a901403c2d1880d240c2d0b042c1410b050031220050400310143d44180100b10050ba400001c94054584078500031800d0f440314544107203900c84111040750f006001000708031403100c11002c41d07072150780d02505640d0151100d95809440710710b03880080410001408083c00907080940155401c02c19a004440b011070f070740d444105101d0303003001803126800c070645070400172406500100f034090721505c0e03a84c40d1508010407c10210116a1040d058180018030005051000203405540100409002032060b00301c000d040c88001c02c95020b449115441044500d100c5003049005c1c0d5040d03801e035440c0d040069003801005128140700040c41141507408100a000084d42070080900031f51916405071194a40801d010301503039180d12034a80905805001013010840d070141e580d044456401c142d42d021041400801e001d81090703000940161960018000b00b02035a6025116030300d01580c640f5525110340d841100c5031055000f010b80341c1e468290100705c54114541c411241d417001414800c921 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 923253938 1250 923252688 923252773
    0xc0e090a0c0c05030705070f0b041d090a150510060c0b04081b1c09091a040e0f01140609060a030309030303020d020c1501090609270804081207050c1002 67
    0x2150301c0303104106c4d81504040810040c14900603090400303010b904090b20304150500c45000c41c08190301d110324030701c000030300040b800c840b0080c4000d0308015004041c1c41402e5400100400c00381c0801c0e9030800300c0381003040e400503145200325030842959521801c0f604083d1681e40b40d413141d41d0801003106003403a000c45500d60a0102c10810311400466511011900c03805881000e0304035011544000389860402800703425070707020401040b4141c0c000711000985181406000b0f45082070040501d8125842e1031040e00e4203009040e01c00c1c0c482d5004684500c6243c7d201401c0c82681c0b8144e00c00100860711121003800000d019030040d011030303216650b0060500604204280c40e051614510b603000c00542e80061045030050301404014210030041070144480141441d40410407207041c5054140c0004002d100308040c45d004c0718011301c221000c075418082d403c2d41140c0d6a0340405011a80b0b44244515620300781449064500b2400079130300540704032411040d040b865661060810b8071000c001c80404000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 923255188 1250 923253938 923253943
    0x9100b0c0a0203060109050c070b10050a081015030201050a0c0809091608070807020c090603010609050906100503010507210e2d01061401121803120c0e090a0c0c05 72
    0x340100040c06020707081d00501d414807006801610b9294144801c00203c0355880c012940c1c0749034820020100790b03545180103000080c0540020340e100340d00c0d4034002010b110010324021100e420b01d8042003030102e045d108400e03403a90391100901250050001407041030042a0f0300c460240212001d918240c845030001341008802c503003658488289400c0c69140340d920000c426800190760a0402160400d450b000c1c3d40c81a18402d40c174820032032200090102c0d103081d04000001c0c815000113015a0410f00340d19a100c1d5011500502e0201e4804000146e925050155074010511a2500e00310f1a00e60030300b10142045808010b41c07040d13180c9010000c44c000402c2901c0c10411505031074070340c00c210075145071102c3c100049241007580c1041c0d8140002000019441208a42420031001200d041d00c1104080c160642070100a01101e000d040141a006015400c0251f4000030400c0064041401a650120741507407464200e08000d00140b01c8010301e901c08070380004c5d90304166208604907901c051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 923256438 1250 923255188 923255197
    0x1e0709050301140a150b090d0f050a060507180b0a0c051f1d0c09010510091d010e160206040224130e010f08030d05040614040b0f2409100b 61
    0x1451a042c40c810030131505083e00c40ca6200d0070240d100b0034052031500d40c0c5965603011f2621001d01c01c121544081d410800d15901404240c4da102d806c0d100301000038203005004113000c6504c03030041803580c900e0412005185085109541c0800461824a8080402204c07500440d02e0100c2d030511500bc080c4010300c030040c00381e800c1480c03071b100301040b44404540d2070b0079099180240302c0c800d6440301c6a044603940d59070b40164151b072001d450080c20a41044030031101c0c0421a8004040c011040444c8890514008811307410b0358161140c04005441e0f590144030002162454500140c012001160052034002d50303503918010f05030400e8840a051201080c402d13445080201c5ca1090300e2441042800307180c04c051401011002000c00c0958034140b01c2c4d079120311943c0c4822140c03903580c200007020401d0940c010300d4540c1d90662544a94585460030303c80300c10080d01c032802100710050004070101b0007a07801380c580c140c0300100307828618a84e60a200890308046c0260407401c0c03072881c000c180c905045c00a030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 923257688 1250 923256438 923256461
    0x30a0b01151d04111216080c04050d11031e0106080f011b03090f0b0403080901060e0709090221130606050a030b0105060c120c0106050411031e0709050301 68
    0x128a154903110451010070004480481404032990701642c81925040c0c40d4492004207071808a8030140c500c03031100e564424141021782030700b504003d01140f140e904e20359130301c5580141c942115503203800c0c0e499540c030f000324480d059100c1d0348034100000107401e9464030400e446000c0c04588660300d030010b050000701d00c83c10003c01c15a641342020000ca98081241d400c0e007a960030000c001070205041e40c1504042c1d280d0f200c4050607111405001000030b070340030308c0901d00d030000220995400d00f80342c007c040a84c180d40300d002a44c2450303008034202c00f410102501440c50398859054040c98694510040d4004504203144955001d1001d815444104c006504c40d03501142c07010109816071404034100c0f040340d0407460091200b400188001610b494099042d140121007464030303059421a254038009106144510091b00410031318440141500700307200761035003140c003480070501c500110300450000b120780350082c04071002c29864550300000540e8110f50f030f0345803448044d5100c102090940d04851520b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 923258938 1250 923257688 923257703
    0x703150f0213030623092407020c100e060423092809060606090807170d03020c0f07030311101e0905071a03040b0f060f04020d020909190b03030c0a0b060f030a 70
    0x150801441220b07128054070205034001c0f02d4072304010398002d6070303400440c041071301884440b980700f45c41c9401015032380360440c8020402c96035280c07103038008070200d2000e050194404013200290300c00e07403030040c40b0140b0400080082c60585403642c0c80d401aa21034070010712200742c0d5541c40c100042a114040c3d0405040e80340c940d164004e10b0a20742500c2c050b07031a4012901070039a0b101c07882c060b003400300d03043c107801c191403402589642d03c1c1f0a00a0a1070700c8002000064440e810001040540040342c04500c200310006544501000440b5281590607003881a08034042030b0700003600c5490154865a03d450060007111100c940f106218044000b603111510070070070b0f0110401080000300180507910200401d0060250300706400450310a004050000d0311498001c20805840c80c1c0c1030b4107680c29400020401d00440c02d102500740034003801100c0500340b0034109400309000742800403c440507680b010740103110203032207500c600c1107404026100c20303441150700003d03585a68040140c0c420090245a4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 923260188 1250 923258938 923258953
    0x2040803091c0b010b09040f0c270f032a080606100306120b090c0a1d0703060e0103110d0f0501020a0e03070f0b030907080703150f021303062309 64
    0x100141c284202400b4a80401d030800354000142092000d00c0c11075504914107a1a9480303480040c1c0540f0302c10701c0c05803e043ca050303000303411039510080d18402da50700e540790a0b001d11110000c84009001c0c2c1d004401c8043d42091040001400f4101142007201c4070000d041c190952100081c1050441c60303000914581c0400b040c00481c0c900702d07a00c201c0001c0b4500702084140d1400c580300e44203003c2100c0c0540800794230000035040b00000d024240390b81400916053340a40c41c0d05c0e0300c0c6161400c242c01d080d19820203c00003009680280314801c2a03d04c0054049980d03880c0d80e50321308864024400594006a094111400180d010080c001c0003902c5040007603218240d4000c0142081301071000248a0f0b480820704000310380005910209441c8400c030101c3e500d40d100789030503103082001e0307000980078411044000700340126841c4110b0f00d50b405d040b050111404451403101603000d02e00c41507030030106108007000000c2d0907500ca20768601002c02e03e1020705050603195040720310103ca4503016600100c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 923261438 1250 923260188 923260207
    0xb0408060411090103020d0b0709151101140f0c07030e060409090204050f011523070b040b0c03090309010c150911011103030c180112020c100516020c130b030102040803 74
    0x1040e0b40c00200c030564260b1501d6141d80c00044840002080240c00b01e1420720201e880d051246000341c01420350010305000104042100070038040c540105584030354070300440c50550322000a9801c3c012a00d5550b014101d0716001c040402079800b12100310300344040c0c00d5100181b80c0f5454084c00080040c0f5100281d441074900500040e81d070028103179003544010a00506c440d8041c035035618441c441724a040740b0200d4008103080400b601c04029910081c002003144004c20811400c094829885260a028252a82d8010b14028041920310801941051111007895441410303104c64403070090540300d43c01d4064108140848601c0030099441611060061000e560021400407140f003a01000b9403652400d040e03003d40780d0080490b950810a20903a401c8940da21440114070990740460b021903460300000c4940e40d50300c941c0811122000d04000010301120300716002503880d0311070b58000d44801820142006000c1031494101c60241c1c0d9211250245501c0900c05030002e02100c0b401159a448101d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 923262688 1250 923261438 923261453
    0x70305040215070f03080c040902032509060207030206030709050402070f0308090705010915050919091506080f09030c01020f07020307050418080c01090609050c0a0e07020c15040b04080604 83
    0x101c114a00d501c2c080088600148240404d0240d00b9014584500f85071964010b40d0080e126030307408858a5070003c0140211005607201c1d0b0404c80f0400e00c8580e031560031340b1505440d150726510491015812405d01040507040c21001194002120b243c420780c12a12034000808980044000b540c4102c1008101410181c0002400c6e42000403030f0010180d542c50500001c0440f143c9001e400818484c040700b01800c0e0b4020700c240ca00310b440007400c0080522810301c144175034054500c16810498109941920314280c01440d62099901e9540ca055044d0b0b20350707021114640c03003e0b02e6202c1e1844200b281c990307504001e101400a80a040052951301c10b500c2c010186845400d41106c1c0c843c03490704c03a8080040003005100000c05922100041d01e5440d00114140180340c00c44e000b0b8030b4203040c03813030360b07c104100401c411240160441e5004481c41d100c1880c409141011110400542d10441c50140c8615080107424604000407941d5454140c440071845095041684a403009910102c188810041341 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 923263938 1250 923262688 923262709
    0x10219080c0601060e101101020705010c080f010902090d0f02190602071403030337090804151403181903050903190f0624060207050f1e100203040e0703050402 70
    0x540c40c20601c0202158000b03045030340c2d0000301030300388001c040c2c7c2412400002e4040d9280190000001c000c4070070340303006c040c2803400d04440700683e446a040c00860805100d2003940c50003080605150b060b1011907423002e0000300303408400d0340d200b06881d034a010842c8c034000403034010740724035805031100500e4492902000c1490112040c801d400520801c03d010110300d030551040b0114484a000242842026446a422208007090300c14203182044c428081c0c0d0310010021584080658501c1580b6039001311605c10806445a400b03031803c02c0411a00da11441c0d41d1602d1095400c243c0e810844802c00304c08440940c510101d001c1035012a01c8405407806200030000001488132a6140361075507914031954030751180e40200403940d50311002162100c4440f045000302c950440101102da2030b030b00c002c0e549410500c900340c82101c0d4640d20910b14100600c11048183c1c0514242d0700c0c40350a1010480e05600600d0124118031080c000004c0015080403628040e00d415140010507040c01e00510403104007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 923265188 1250 923263938 923263949
    0x402370c0506131a0a020703090803070c03110a09021206010206014e1412090a0306050402270906010b0a02061605040810020417010e031602010219080c0601 69
    0x14000104010070000308410380e01c8074602004101c0f556071464507040d124140c82080703150803003460412075641c07440c1d4000c14200b80262178003e0300301d5590f0003c955910030301d0300c01081d14681d81d8040001540b000d200440110005200c0ba503400c0e00d071080c0008036040b9071180c038802c4052805000c181d50b01440710703d01600c864010312940c880e007041d00b10042c80c030002c401c030a00c6d110030440176450340c10311180100c0c003141c0070700420300e246003428a03015841028903140d021303004200b0624010301c540403c490442a0107052120290700d10b0303c402c03006000c000c2050340c021005009007000980d02811980d5100140400d008081c00e0400505243c680140c2040b22044820804200c081d5000a00e160307008040708081041c2c010a00c000b141c050159a0040e281403187e185505040c00755038000c0e005071440b0003000440c030714034074000909990101134101c2c4039401c20454a200c80801e080103a01c9280180104d0b181c4040c03101c4c10a015044202e025100780b80c000c5400306542c0000d1056600612 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 923266438 1250 923265188 923265197
    0x90b0703290a0308072402040807050d06060b04080f010e030a08341215050603061c1205090414061c060e0609070807090203070503060f040237 63
    0x9014840910010200700380a210707070714803010700d1951088041000b440e0b00c041d07000e81300c11052500603085400c610191000c1c900100c0507104804451003a43d040340c8022000789280c07440d08041c00518200050280c0d152602e580700480e440701400001c0005010712001013050300d000f0b01b00e45003110409500d070b480a80080010f00b0300d040c0d001c20b02580140940360011149000c06901c40d10b03600014085401203081a8bc070180140d411000b2811402038884c0c060200691011800041c1ea46030300541c1d0b4000f0050020441030f00340060701c032042e4202d40d44002c04014098940307034200a8001c0f00d07940003c10000e071110075800d103406400c1c2c9a001002002c0307100e06004d00051840300c052284041015420f40030036080c072405130008a010240720307003944c03000e003401c1441036105c402c94000c01003244900d50700082c5502191084a10038581582d48500390748a0300704100c0d500b2880d0b00500d50094081c810078400d01d071821800380e03607038180c17030400d5140e001c41c0f007501394602e00410012030510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 923267688 1250 923266438 923266451
    0x40e010e0c0d0237020d0516061e0906090c05180c0f0f161118010504051005130c0e040605010e09130c120501060b180f060d0906090b0703 61
    0x9035909054030401c2071160005a200c000a16a00c040b003018100108401c1c1e000c84007521005100700311000d01d004c0160b0070358180c0c180c0745200360b50300d01c690b480c030745460700810341d102c0023141d01907201c030006000f0549a2129010b01c00064400d42d401d54606581840d0350300700c280200300b48031203407000524081d2408035511805e480c0c2d43c48044002000e0020070000001c03086400a200000c843d80b1603403110b0815106c1e074115000030340b4481e018104407035500d111141c00800346801200000044c9244400103540d0303003028140300c00b420014101c0c1d42640920800400c0d984c4e51204c04001e01c001da80030001d640640c0b05002007021021450082c06175103071100501103640d01071009809140c0542d032641107500ea8100030904403113100c0c0c01403c18043c109000c03c8210584810600741d0703004e10000c1c4417075501c40c0b00414081c82403194404080e00c00c2c1c02c4244071400d11002507103070b241d40204440c1c18000c0a81642007600d0810000700d40403a91104100c0c10003c005280396004443c903d41005407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 923268938 1250 923267688 923267701
    0x1f05010203070b0912070b041a060607030c0819050a0807031811060d2c010212040b0a0e010e03220b0301171609091101080c0d02131a040e010e 63
    0x7a0700c5040c6024069080001c00180c000c00c0c200083c0c812a2110340400303030b840041d4201900712074411f442c01c490313101e81d02c0050a60103406010700750190a000304850325045a9640c19148001d035034038111b8a006c01403021418028040e1400f0407400e81c1501c3d02982ca92030741c40e00405d00f280050404051501c1c00a28a10740c1e891440e80883e003d900940d030460300c7c0c00c10400100f80703019903c0c103d5407460810070704691007051031084050f1818403051840100c0f907400d4009082c0e00070025004034882d44200040d01107140c005100d604004d100800044059a102196081d500e45080e1041540d0000645907e0048108108401c1e10b05100f0050041800d000d80c02c0d00300d2106105d01869480400c4628403034100c280548206403204000205500d83e960001d00040c4c4070030312051341c0e0245400c001000c80c0d4083e2540c68403801c4002c030791902d0511962a850025000300804c4010701c685444046191010b03108150714078003c000c80c1c5506d070740c074043d1f0b95a121038050f00701d0002e4003000000e1249 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 923270188 1250 923268938 923268943
    0x31a1f06081501050c010204030302150708010e06010309140a03021f4115041406010818100e0f07060512060f01030b0d0308090709200a090509010e1f050102 69
    0x811440d0940a80803002c1d0b40401242c5078001d03c110315400f54400600001016000529030b04200e43d548500141c507503e9140c02d2310108000d1040e4001c0d2003003c4000341c05c0c6e62080d4000c0c0c90880c85164465440d032000303e86c003481d21418100440142c2e0269903202d0300a140c00703035255903110006c00140460040c003181d11105800b6446c031010401400d200c040c003086038401c0c03010409054042c0c0d02c00507107070204581a000506246641c069850a204c001d08455410041d44c82480103840d5802c1035120b411800b9403050b001450307000d850054068500c030340b8200c0d000364007a100325003005100010415a02608011a69026100f80941042007645205c09100c000c0d50009084400c04200032400005802401c044854964400740f43c24000040540040640d4003807c030440031500d055444215403011030340d03400c1d15100020b0007011200c0e603d01403000200000c0b01d882c80e06040b000d6507030011800501086e00031130340154103a4100000c0c00707019500d0307000b030440c0301042401c42c92030b10300041d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 923271438 1250 923270188 923270191
    0x19120209010c200613050a0603090203030a080a0e030708040311030604020915031002040b03041109010605090904060b0a060c030e150306010f0905031207020411040627031a1f0608 79
    0x40500504541c29207000c00390380480f080c036900c0540015521030852034500b0440341e05006252054200303641c00b180541c800d200308207007258081d0040d4900321480006079000305008280325002c1d5210546070000d54020b0020740040c0788502c99168036141140390010380500c01144035401b9501c80c0d8100400b5958409955411141241c84c0c0030040b206800400d0422604040805219000007800160540d0b07003030040d8070490007050317512800d041d0402082984802071050200041c0140075103e03092804020f03482d000f9224803c00a0f42e80e0022010904814280d84010003180d003109900081c59084005011840c030126042c8810100803402501c080c00080c054a040080144031982d40600a07081c130400380000400719001c055003c660110158400074089005a0900c901d264980c0407105c1030b0780641c2c3c0c281d11110007041443e241510705480d050383d00b00d090079188034004040791401c03e00544000350004021418a07224500754007a201402c550007620040c50781c00c0100700da02c501080e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 923272688 1250 923271438 923271443
    0x18090706200114040201020c01030c1d0415030803041e021e060c06010b0a03061e053114010501020a02150a030b06130608010803040f0618030819120209010c 69
    0x950003250410180c44070501800c816590541c80c0c4034008607041207030014144180d01c00da0887d0a004460070046080d101800f150401190010760b00305000340f01c02040c410f2a00014000150308444c020040610381100da2040c0d405540c0001480144000d24509200ca00d0039244074142c880b001c0d50108256030340c4100e6101070107110b83c481c4011075070307074a080307510362103402045403095610341e030190700140d10002175035001c24a4004000340742c030103a100b0003030348115180d4100400c51500d07042c007a00c1e19850045500b0b80000c0100090b40210030074600074200c0c040c860003c0d2480d074101404459002c180c1006065502640000d00182e0f1a96008000000e0214284e61188100034081c0d000e4042102c81d1640702c80c000c1013074280310311080d0200d02115002c1e41c80c1e584c02c0e6078403492292079101e54002c2110203d0701010034803420303000b0141000b40c00001480301c0c40d070035900d84a88900c1d411016030003403508140043e800320968440c0550050082440b400c41c504030203500060403061484000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 923273938 1250 923272688 923272697
    0x6062b0c150914030f0703021009030b09030301061d0609010309050712030e04052a0f130315060608060f190b070b0a150501050d1a10050918090706 65
    0x10404000c80e0345206001414840444003110089a2020700a010907005409244000700100c2101d807800140e104032008100c406060703c00e04640074054040140c051900502189042c0040003079910327004a84942c0084003d1600ca50501100400c030800124030113140b00c4500d4a410312507502c10044801207002420006481c2d507451418a007043c406901503400c180c401d845020905030403030300c034074010001110208140d0303a03010401d80d9a20100c2d44200781100290102c034540207207007070040051a24070030a460502082034071040740427403250000c94000380c4111103003265440328015500075000d076003012081490228080f80701d516010450038410701400107500c900300c003043d030300001410b0114943e6580b0507060405281c10712003910310404485c0b40010f03144807000031545030300c00d585059465901c0c0000c05030011010304010581c041c843c0040c55101d0341c199491040b11b50680c581600c0d4541c40b640d00008012008001000002d02c0c0f810000400620740c070302080340c0b0140c5032039007803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 923275188 1250 923273938 923274019
    0x12181c090806161b02031006030213090f08030a02040e0c09040c1e031a041404021507030807110c1002012403021008070507150b130e0c04230103140606 67
    0x1303440600c410b12a4004c0d4150007210304541c15030019806c6074007034038000d40305072003108018840d004c01c4803002d48003d81419502010000010542001550040d41c1110003500b0300740c480d0b00a580f2010f003a2410f54510400060b00d20a40c01d042c000c0c41c181c001c10303082080900581000c420f03000b1030000464800c01d9a00c0462000c44a6840314040311810080e104005c2103110456550300c0031400d1310143c0c490490700e0211500840302c0c90440d4801ea91583c2e601c0e00b5074413035031011703a09580da200c0f94910500401801c0a410b480f000c107200c0303940100b40d0010a4881014040c120b26600c0e00d60496291902040b050015844850030840801038500d00751409a8901c841229a0b0086800c000c1003102d201c0c402c0c4500c07030b15035005007108207021560403600d8011500b4040845007603d488407011f40100340c44800034581940005011010b104c8802a1141d08400ca81c003044030981040701c8801e0034501d440c110910801c4a00e074080c0d403d45198151440303d03005c0600b8410208030204000407070342c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 923276438 1250 923275188 923275217
    0x2130b03130804080105090106080a12080a0b040207111f2106080714010f0f0834020a0506130312051009090302030a020d030b0612181c09080616 64
    0x100480756103030300110480c2d00c554072200014040c20060300e883e00d4541c2400c0c404070b0300f04404a20380d80c409501103000c51403100d8090050300d03c0000240b401000310340c0c460b85000951594001030034014481c480000032503841d03400700070106030800e910003441c0890700082007100da002100d000c0c0d071050403210402c03404415501d0001420b0a504070400d640a611400940501d44590740f01d10550243c0702d109401c8025441192140710615620700041e0f071240224800002641082c22014106070012111090b201c0558078403802d590f89200040c2d11140842c014007105121040d0409c06000e4242801b5005840003806040b81c0c07004445690b9461000c0313540d40e44089280c20041c5210007040c0009900790601a40741c0c2c00400c0c541e4094050030040c01103982c4684620b0702a910020301c5a420034074010305100115900800d070001c00c011050701c1480e61b85041059180402c18514103008207089000d006141c00a40e0380000500c1c0d018005000b0315024280551070f904102d0316104000502c0e24 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 923277688 1250 923276438 923276461
    0x207050d020f120307122c0301060e15120705010237030305091b130b0d02041802030d0813030f020a0b1602070f0b040b0a09080304060309060b0402130b03 68
    0x28445142d01041da0480245030f2100400034007940c600038400e420381c100082005441601d10a00a500f030385081c0c4000c41035014000ea00581220000780000816a0b22801e41903004001a5802082c0701d440c0b46204c0b0651502c0d25250090f02b8620011300100c51425001070b555944c618003075824070300b484c1a008000c000c0c5001a00310101c00078510940b1a2107030070301400404080c1d45801e8030340900a01c80c4002d4102d1040d00780d841c500039146602240e01150303c08000d002910034550702c44208280c40307015035594018289410704c03140000101035950300c10546400d0662902c001032080c008104203443d41c94641ca800f295416090010310600300480482c02c02c000140002d00c4403030180c05101c0405000c62149070000f10b81d4080300d41a82d00c6d0700c11051110424811040d2403001000148030466003a00605034203031030b6003400c070302e65a2100881411034105401c01e00019030380303400e07007000e0007100e0041d8806542c06030b404514055846060001924040c02a5001100000049082c0e6000d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 923278938 1250 923277688 923277709
    0x409050f010c1e080f180106051306090b0306070c0f0303020d1a0a051207030602090a0b1231020909030c01020c0601030c081f051009060602031c020a0207050d02 71
    0x5038001c01c11100300c0c8030054102039544407030644030494100c1c480da0b5240640700441c0034400800010f407103580d0b0b0708000680c070009100001c00c03554039190300013203644805003a0740310f00c42e02d80d0020616509001d1190100c41c842d02685100b684554280034145030058089511260030886540c440449801c00340d011348030b0808518011403509056400e201554810340e103880760226622814540e4034002c02201e114580c1c460070860700444820000075034641d004010382d0340090101080729940c0c0c220804e44d60015454501c09041c99810031001d06084a9076802c000c01040c21a91140c61403101c40b25008d416403c0240940e02250200d40740700710400a4442c400700b901e0081d5070380c2004140f01500c4020a00c81101e90040942c2c0c00314401c040407400c95512540f41981c4008800c0d03031454039014110103410041701c070703c51010204a00f6040c2c0900c001a040c95001540c0d5a200c841c0700888051407842030b160540c2c4144046208994041946001c03248210b403078144d01500b50000400403010f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 923280188 1250 923278938 923278963
    0x10e0604120b010503010e19020d0b0414010c02070605121b13030201140315011b05060115080a0b01020c101713120305010e1324061701021206040905 66
    0x1011500007408010a5014410144608550a400c0e6607900c107040c00d070748400500c002a40c12510b450300c40307058480c0311524100e00060003690030301519150754400d02c900b40c8003604d8040208125005101782406181d05040c0e00d44010400645400e0004000d07005544d5150010810840401c203000b06101e0015181002e0f0590a580c0e026224402c0115003058842240480c48481900300190703810025280b15444c0c14014440124800e801110401c1649940090303c100c868095004114200581c601034003d02000f5600c80c109840040e105480081050604c24141140b10b074059038046150410041c05482d1041e24002085080d07810100320808040c8003c96103080000405040019003078a9002d1004801b0026441070b088042c0d4000b4001c26462450440c042007042c0340f005400149640691601018484904469102c09051808424519850310414400000320200c889030320072110000b1481c1c40310686c004041264001c00f080c4c86a50754140740000e00505000102040310b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 923281438 1250 923280188 923280199
    0xc16050907121b050a0207060903080318030d0c090518040c030803060f060712200607081b0711090604140a020d0b06030a15050d0506040b0406020c0d021509010c09030f02010e 77
    0x1e060f03e001800fa41200c072001c001489030240000d511800fa0340718800396504030150524698441d82c885202d02c141a0620340d00344810001c000f21308505e881802241d8419546540c40b6906c1c0c402004128000e1801142c02044001c0900001030072a410380011283d03c948050380740c1e6110b40015407815085051560400000230351102040310030180d044641825444203901c094413442e110204d007800c402a08140e80c440300100d04200c0c090b40100794000003605204804042c0c0d591401c01d20b4211340c10446401c5402e00202d040c915003182c100740d101c074056600704803038005200c281d00c06010242c000c0030410ba00040c0f4002008203900309941060014200c5a075900b01546028000c2010899815000403425000b0039280b60900d010703107081e03800000030507040d04c503512042010b450262086418513400c001c60300c20043c040c0f15403001144160050150700e003100280c403510020081410a4a925148021f00c0300c1d40c0080030002500d400c407007070070420405c0e440141d440f204009001f07070f07114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 923282688 1250 923281438 923281481
    0x3021c02061008071a0309031e07140c01020307030e0f030618010509120301090b0109030204050c04081e0d0c060e01050a0b03010b0f0307092705030c1605090712 71
    0x280d800144541c0110221220b0990550350f0340c208540781c180d98000d0884d07520b03140760000803a070482c0002d15003203020001a249084640d01040c40000750210040305503090125507101840315900d0385600112428020740004011000002c1d01d030f1140d0034009051040030102103010751a040200c800b800c01c00350071100d05090400b0b488154030054003081c2c0d510b40c241000103003503000c04a1011900b5004140382d50459091510b03000c083d044c801c90050412402c07000c004090b035101d0180c24007030102d0b034043c1d039951030910365118101500d03d035802030402d044400c5070304240341c0000c0d041a4544d1030f03e0b102403400407a00c0c0c0700000d01000c8000c00c00c0da40c200018130006140720b038812955260308500030000000e200c070a008510038100300095154001402c10404164580c100860103130340800c0714400c6207040d40c2c038890005181001500c00740e0010442e501c0c0ea00e001c203c15909500c82090f6039000c640303030100056070044008d041c3d40030090304ca2540c09c1c0140c0d480e0080e01c42160071444c0240b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 923283938 1250 923282688 923282743
    0x332010c0302031006090501080403080a0b031c170c07020d08281b0506060927030403030e06040b03040807080c0f061f140f0d0203060112120f08060d0302 68
    0xe50400d507513010307000800c550300051160240e02014210b9806850b01030729561151401d4400003002040000fa09841e0850720b0b00503a0103100e00c0c050203a80f02020040d03001c0c4074000901048030787d40d10350113a200110603c041c101d175110964a131280d0440317450380529a989800501401008011441c1d0030031880840700d00d200d00e0088401c400c9041c0d8504540106500d1460007076403207800003501c0f41d00a0401f15600742040c8408079030015007450b0102e0f074000d0130014401035901541c01c26503140c02c00700b0280201644003000d0403427071100300c842c80d05150800c0e6450180d88030280c4010201310000071300d58200085002a41da0240301c40c070595801103020141f007515654100e620070030940020b403440c1c0d0780b200306090b03650039600c9180340c9001e000d00c040140401110f05041e0707103500c95044058103005076002c10034075011b09a5594006020303a541d00d401501c11394802c0051051060090035402010360104641d40d1024003200c4400c148103041c20264100410088100c01001c0c028004240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 923285188 1250 923283938 923283941
    0x90409150b1c021809121305100201021e0a18080a0203060a05010f030312060b0a09060201061211210d031508120901120e0a0f0510060332010c03 64
    0xc1600003035031100080094880b000d42d8010100c1c0300294810b2501103584103460ba254003942d4080f00b03c0f0300300e82205038109084061a0049071803074441c9007261805110900b09120b508000c4c01d814002582404840c0042c24050100c40b1078807011010007003000c040d020310a00d014000030348643c00300c0030410b4850319481c1c0c0702c3c0b400c80020b03070180c0b1800c00411000c440c148101c07030489401d031388503560071800c564040b280130f940b0000c0c02c01c0322501d0ba40003090154001004040c020f5007070301c645170100c1c6050701c0642590070301d80c040540c0c0e4034100d00c400c010908031200c00405900c120b608031002c0f42112003410b002e10109042c00c06c036200320300b0018111038040c0e1204c80d182800880c02c0c641c0a136909000c42c0d40e003200049269900178284207100d641d50207120451080700d48600040382e81c1d4003c080c0a03160070707840c0e04140c5032000044144014002e0510241c409a0303500b413028000700d03085071555040440250720040c404c8013942000b00c0c07a446522910500c00d0f10007002809a200d01100040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 923286438 1250 923285188 923285201
    0x2040608091908041403030f0d051936050d02030a1710031b0e090d0f030227010c02030102120919030f0302070606321002100209040915 60
    0x110510030040c6090386955440752445882d0360200c240e40c906820005038007092901103808070380602c810302c0030949400014010f8041a4034507c00003459160070022180c0316070000c4041d2180516001d501516204164255203c0701c4000001c1c403501d00b40d0140310803004409a20191880c0a02c1d883c03800201d0b8048010141d6103544d44c0c0d00b00007007101011030f00d401d0318103450b520989078102004000050300000c1781c40b01c6008040304200314980e11111420074a0003150b0000590b040704074002d402030f41009042c0c00000051504608048500320742c401030712515503d141c5803c9003450b184045a104e800680c010517800340c005c2d07481c1c00400072250004613064804034141c3c0140740a2866101d4601010b035071043d010b87ea10350340502c40542c00d41c02517102d402c054400325100c80c00807926800081d44040865911b54103031800221500801c10107a220021403032051010a06031141d0f90b40c00608180440b80c11000160386424450001d0018444548010308007004640711500c0c0340507591041c1e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 923287688 1250 923286438 923286451
    0x21512011a04050307300606081204082e0e010b0f0117130c0b0301080604060c08090312091501060207080708070e040609020103060e1302150f070311030d02040608 72
    0x1c11541e1000780c40c088841c051400b071035406034040e05c0104030888100c81207016985101b00510a00d0040e0a07802013180044582541c3e404d40769001000303101000c000480b841d55500c030040c2d0070141000f64441d118414940e03c0c01070f10380e007444510701c0c0c5034003002688c2c01e680e40000c0030080350199488181c043c0002c80d940c2d510a424100c0143c0440d40900948680010132a20030780041d51034808010a06c03201d150103442141d846400850303440c0303010b402540680b0000004281518113840d00078103440c01d0070404000c020248040c42132211000023900d006164003801c407949a6a29043c071850540e002c82c60424200a04000023010fa4012a20b0000d481e502410b45440e0b82d12440910b40d1208140f09021a00300d000d8005800310310351b40e10410000348145408180702d541c650f090441d9000659144035044444085441145080d510194155000b0780c0301c107007402da1011514500d40161706024051203182c405614815200388101c61312a0030040c0119210760700c690b03005000301800c8955 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 923288938 1250 923287688 923287709
    0x615031506210f0915070e040501090207020f04090308010501140d1503121805010309151d10090506043512071805040c12060b0c07150c060902151201 66
    0x403c0e100643c1150b040c2c4100c0d0103500901d141ca00402c2c4001205c18000c20010820110000f0401140d80e40e001c0e05008110080300561034180764010000c4605e40154568459481d04410f900082c1e0081c0c2c1140c1159800d0030544400551080740e11030303070b104031130700520503034a40051030b02e2101c8029a000c00b90307070044a40c10b0401c5102c2500fa19442c00c00d142c001c0507101150803c0240d584a074000000d164850300c0006280d2079428050000c3d00e8071071800b42044200d29090082e60b0204015481480c1e900c0c000074042c245258841a444910180c0041d1600c0d0645507408445640c00c0a9a14460b43d1035020300c00c03001d143e290102041e00080e29070090b007600c40003c10555071040c0b02c1f0348582c0c00806e802c1c000b9245008100401400129400400d1000c05000308490190b0343c441e0300000c215040e541a51940304112860030b2480a800c000e000c2a0b0001c6500d40031940004801c5503544d001e90001074030b4809000044090480d141010108203002880d0403864521030308007412218440c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 923290188 1250 923288938 923288941
    0xd0506092401120f0807140a03020c01051201030b060d15050412170f0703060b0d060810110d0b3105090d05120604020708220608061503150621 63
    0xa00070001c842032040100000c84451000007261400303440d03100803440b070b9500910b40b036055641d00d01c0782200300d6103003201a0070100c0c49406044d0180003155003400d092030414a0a030003010180e1703c0700c006000190044008034002080340d01c070301c9000400c0daa001060854001b5402101c0f0002d0718003154100d6070600a82c100c54015070003616900e44892015000c41310590b01e02c1d4440b5215400140b411b0f04140c0c0360400000d00601500080200c5a407004021a40c1402d0102c29480d1661280c400c1d110146001c011004200c5d4039001d5404004040101084501030040020070842c02c0c2c02c10006a003490162400308400c03054820524400c01d010140100da40c0c1c102819107400e0828022004100c0800070020100b10391b44104d50300580090005050216a8880071410b400c585401903890135034400580145c1300400b20319000b0020381c68003411070319005010584220210990184000000c008a128420421a680c808060140c0f0098548010110006107400b0350059119481700240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 923291438 1250 923290188 923290243
    0x812040303110d2109140a20031218060301170618060c07020d051c0810051804060917041a0f0307081803071506080a1208060d050609 59
    0x15a0090146454581600d0004402a02a05660f130104460042a904e480200000c1e0f001c1802000c001011001840007080070726005003c0406040c0d000141c240310680c0d05070302e540000d00e2031a810540d11046e40c07688070b00304201d020700c50007222495002001000100300252443d02e16904142c01c041110b01170307201c480e0074000034507000301040905d8115800007511000300c503008020880c405090f00015800d0b0ba11054100642520303042c44c0301c0d00103a00b00c03800540c04038945401103540c00714140014038000002d41000c440004030380d0b0071103080300001c00b0720072a90700034400507421030701aa0782c003a4007070041030450b800f43c02100c501d2100c0c8011600d42c036503441d06030340404481c0a0350b0352558a60607800c0d00d04031001444202c1c88560100c0008200b80d0030304c043c0594603c078a000302d070300700f0b18080e00c50155182500980000e51202081102280c00a4200545543c96040002d0765071100d01c08680612010440030708580309510620100000016010000f10541003042c0700249000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 923292688 1250 923291438 923291443
    0x140601091202010f03020c0c0d05060402010801080d0c170f1911150a020906041e0303091d1501020f0a0b09010b010306030c0b09130c0314100b040905090106081204030311 75
    0x7050080d00068402d143d101605009900624141d031031501242c0403a5076190020742c5015030107a08581e140c05c200c1c14801156003021500d4094100240604604244400002e003088906e01d009000da5190300c10043c8001600b03800c41c0c008407619a001680c4d41051810480d1401c0425030b03400015101c00e15658600700c1c04200e43c046032a41420380c811684841c403543c0040d4000d80455a031100741080000741c484c80f8440b210715100900038814009600c0c0d0308003c0e0200000741e01000702c242001c181c1c1c2d00c00c1201d03036440e9944210b0340b411084440d1041c40040b0328180a55a4440640c400d503007182062000f02d8074043e202c2c40f0071300c0003881142d034180011800e60310303944801031000300030400034042802100084d200140010b4082003041c0e503070b450000705440100c41503402080d9181d040c10b480c151211800d0381e220300700e00b81c6120780074600601c024041c8982e00c03c1c00c1d82641d0b44c40218004540030f400c1500205001d81c1221803500c00c0c44648082c5905c548811000718920300e00c0c1e1186042d01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 923293938 1250 923292688 923292719
    0xe0a03050a03110627073209130807050109021210150510080702240406050f040804120305040308040308300a09030c02031605030d0305091c020f0114060109 69
    0x600402080c400070001d00c907841c15142c020b4507a5035024561010071050750b0303d0704a403000c401c21841040340780c10128440101140c010807488c081e940e06c0b001c01c0f8604c0300034110380c0591a409090320355030313803442c0c00c0c124018034448034001c0d44006030749500701c41441c000888e188030712441401000000300c4100340030145800d034031680350000e00912180135802c2c05481181d50104440c019600f030358000100c52f6026400d580054400c03644440c0501092103981d12580317a00c8003c1c2c140b00081030500c3c0d101e0104a0003940300d00c1001224490041081511600c10341e4001c550110f1015101c9840e45007800e200d4000d6640500d640c0705148140d87c2031407110003080a06040030150740c946444d5040740b48083c1400c08410790900c09820070420061b10100103100b6100e00ac6101440303c80c0c105007c050802040c4014041054105801c1c40026900810004c2819444140001e104118582c0c207a080103240380c1c140540394642100b00109000c02d80c8144d205136008d07a00e1403192522804106901813030f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 923295188 1250 923293938 923293951
    0x6060a080a0f06020a021510060e0117010e15041503060b0d080a231206011202120c180307030311060105010311090f0604050a27060501020d050a0e0a03050a031106 72
    0x102440b403022030b4080e4014040b42d01540306450302c1c0940107038040424081520700394900d1030406420032085900558016021500340380840c007110139855445410407060040310511284c10020592a0010701103844007100081d106106607204080340940007480c510054038441d06100c2c00c400c8518201502002082d444140340d070400040200032030384125000f906681e0307403580d1074070510180041009040c180c1c080000030520381c9041400141840e10824001e00d000c6e00600c04c0b0b2a60316280c030300482c0d00145011040b07803500d06007002c2d0304800b0701c070801d002d070540510b841c080145540a0040e40c0b43c502503204541140c0d0703a0703070011011100380f4040030041030810b0050000500e0944002109003d00810301c0e410180c6032400140b0815107a1320172604600f142c041840d40410003107441401c0f00c26000100320aa00d0240040e407107624243d9000200003002904501540c003ea0b074032025400060301640179907840c1e01c1c22a80e00c4041c400190040f403203201030420407809c0010042c0c800c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 923296438 1250 923295188 923295203
    0x11030c1c1a07120f060e0109020a12021908040602090a0e01090509150601030e0c1201020c16060903031404090908040617042a0e090a14060c0703110a06090506060a080a 74
    0xf900101502d005119680902910b503445103400030303d501d00d13440c0c00360203010b40800050b40c0b010088805440140c07400c1800680c2030040c442c0e01008508481921480c1e80941480007882c1e5071860400020300c10010b0803944a40600804540070b03101200e600e0603a81980c0e004c000c00c0e02c0d8500190303660078094040082d904a00740002d8900d51081d040300048486110845550380301d158005098503c1c0b208030b0b6040b036903000c034600000c210100035030002d51f420741068444c0a4100640113018610f40d003c007905205025090a41713130200c07081204c004103918041003003c2e41081c1f40040355507205104104c001045541250b00280d900c144403406954860240324494640e07070359025032009283d8482d41207856040c40002c40312101c01105104064190152000d082c161503c20300c401d800d5809402c2590041007000700c0e802c02201100c0700141c0508158000d174000b0380c011881c0c0228403100400050034030441400704600052400e00131034041b2201c0071595242c94050307a5601c88000080d2140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 923297688 1250 923296438 923296457
    0xe060a0918050604030f1419140c0304030c1a1315020c06040801150602031201050d240b040b0f090f09071e06030f0b0d11030c1c1a07 59
    0x2222584040d915410754030505038010300c1e68070b466003412011242036001c60115003400c114550301000b90722114045008590074090807820a10b00000c03904490303014003d10101e1105143c5903001500d0180044000700d95580d500c0380b0708401c1245440c400c010f03040f03070300ca070050804d01617010655403400b0752420300140039403600c000c02d44002c140c0078913a000c0d40280700f140307011502c1c5e003001131000c1d08030040007142c4401c079000c44410342040d0360700807001c54000341b02c030000d8440e8001ba141d044070811900c4042d81d21050801d4022041d5080c11158226a580d541070810301e0740c0e80160701c00c08012101007103c0ac0c4681c00b8890115940c59410342d210810f07400090480c03000c0381d0300c0e6801c5100740080750440d07600e821813a654804004445a00d10b50540c030b082101940c1405640451442c03501e041c05036601350008900d200c07412407801030020b01500301d44c01080c4c078200b100e500d201000074026013400600031030344c054082e40100152035140180300240a40b809400c0054065000343c2c1d0780308c40b207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 923298938 1250 923297688 923297699
    0x60c230d1811190b0c0c0a121218170c09010609080309010813060903051e070c150c06020310180509060112050a0209010320010c0503090d0809150703090e060a 70
    0x8400c0002d0058140660a0b8080b8020801d00c02802c04501d021000301414842e020410010905a50003424800b01c9523080000042480303142c00d00d030515909100b0714660041d012580c6015240c1c008031601c0c001c059035000710ba40300003540805000c0a841d0041640d885407000c0741c0204403801502c25035801001104450b51065202c540d001c8240050300d0702c029825034891040e40c840e0a0107070001000816450140c942c1001c4100100c03420000312440c0546503903030310b40c000c001c43c4203901080b000e8041401409024040d02086240d01090847d641d180800c2000084080c0d4041d00380d9407609551808039001141c0b1825002e2030060004004680c605019105020b0b003940e001c8074140030b547d01580c010f0302c40c0c024a50181d44103001480b014030a044440d100903200d0b0425904024504284030b0208a002c001c036100711038180c83c03072061651681805031aa00c031700c4074410f030030558400541070100100c001401c52141b00743c3d0380c01071903541d80907003140e0350760103560507179103c3e0308001c00700003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 923300188 1250 923298938 923298949
    0xf10060f05040305160825090e0319030e070509011a03060114032403031c0509152a2701030b040915060512030304060c230d1811 57
    0x140c5050a103405468291640d072441d08200840c0d0f1007080ca520120740605c542c2409110400410130f03401c0000c08241c2c0600c0701000241d07094480e1484d01c070f03504d01c4010716604040c802c070f8518803c50950310702448213000008004240801f6120000c0c00341032000b0039a4074000e202181255048130741e07a000840b000c50900b126a00151820b410702c20120791810980c01b420010b180b00304c0c8405d06201c1c0c1110030300c3c00c800750140404080c038070075041082a0100c00c640001d0740300460044aa00042ca6513035058410319182c1030080c180546501c50003000000001c03c000440d40c0c2c1c003842c54080080d03002000c0d00030b6134010100070500344035801c9212884e002e01120b6420080d0014500030892020f0f56001c20200c0d10003041c16204e03081c0081c0c01e28440c8080d0b0003a040203003c1507500c00016141b15080b55140d000241008060540701c0418283c414440c543d020303000801031240070600d1191481c640316540c002c02c840c001507810102c041c03000c01900000003c219030408400200c07072444108001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 923301438 1250 923300188 923300207
    0x240609060a031b420e060f1b0309010c081c1a0a0f061209020d080a11011a060412030210020a0201060e0f061f05040302130b090f1006 59
    0xa030000d61000d000400316110181001010403c000000311003810308404e00071881d16905144041c01001e0b118501d58900040c0015840243c030095442c15012210103d600e07800c0c0200341e541c08040425540c01403401d45008003c01ca17804901100712641000290f6128007a400c14140410455050b810128400c200105040c3c0544100c0c641c00c100816005e00454040c07020110b40d04c4031010314604c990428102060140150b400340a01d55840c041004150300441301e16404900d4440c03000380e085403500c24001400b20703030180240d41c99041c10040101031080e409401d01681d82030041030446100c14050080040102506803890b00d8200056400f0342035010604a0440c0b003038891480181c0031600c0031701038500e00d507400031a11034689008600c590f207018000708051080c6400384200d0340e0f1035801042c58030098210001c080500c244080d03d05000b5540081c1d00101c148860002a0400d68000000f4010413900d0700c903661a40c410340818020b00f1a1003110603c085482072103039500484044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 923302688 1250 923301438 923301451
    0xd031821020c04050f160816180302090403051c06080330011403151312050f0307090338060301090f0b01080106080607020a08070201030f0e0609240609 67
    0x1c4100c490b06030045000c07a0411680b5042101c0c00800740f001c1d94410304100005025940b51100060034103256030034140366620040d03024002050000c903012040c00e11031200850300180754003050b00d40750030040e010b17500004100d5040b0f180c44000b4250b0101d107101d0802030302c80d110021170074410760010620002100c41410b43c0240c075818040c0c0c081d07100882d0b1941c00303056442180e520807030700c0c20f003494603046501a000d002c82c103512081004a215812958030350340e0300040e44003403407055640107a4442c1b0a5218060000c90004100010240c0240001e01103a100c0c00501e200e110364442c40110700510030b403400103c0044481075000c43e80075452202d030800e0340100000303055803180d41c402070420b80c0030f0b108440100e0204010031040300b0030301c242e10003070450301c01420f21803901d480000e455000b503240080034950003013206403c0d07900c030b0f5000c244010701504080119070340c0349807110381d030300b43c1180c0841140c407600c1c03441034200d081a01e4901020500d2818145c850306d40c40100081044002c0c47c0c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 923303938 1250 923302688 923302693
    0x409050c04030b0a0903020c0a350304060c110d020f040506300105090607050d0911090a09022817010908070305030f100312030209010e060c0d03182102 67
    0x11001c107900c0740f201030040c0a04400060403c00341c3c075001e4240381c240d901151080081c043c0400c104c03008020150100080384020800c1c1030700400070b1440c0410100700700c020324480464080b40d001d070004c00210b01d03940145400c015000c020020885d02003a074210080d0003a500840009040c01c084d0001a0001380c014100b01c10042229080070b1940403a069490aa101d07412441e00f10303d50a00c80c04d50013400c4100a070100f4541058081e1440c8034000384002503603560301200c030074400c1c200c481011081c0010107000c50b60514220f80c401602020720243c4c41024001800002c420b030500400898a5005503d07a480c00d140504000040ca01c88041d9151552035070181000100014010b0100c1031103a1034154880c1091042140210001851001c00424200050010400d03181c0c480b20f81000700e2402695406400004803404086c0307281007038200c50f0110307948501c4600070904048019044e5002c1000c561110741407508c00190309005800f4070996516100507420b01c62400f020b24005004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 923305188 1250 923303938 923303947
    0x170109111c05010c2007050319030315060503072607110a020a03030908120703080c0c0c09101a03040822031712012c091515090c040b0409050c 63
    0x102c460035120b0b0050500e00090030b070001a03642d00b1100c0900c80701848060010305006040c0804641e4a80c1042080005030000003035650805100343c10180d14100041103040b51a640c07444043e0103608180c40b080f0200302800701d150810b00c081d040b03d2072002c813079004160858841800a0314011a002d0b8151094020340712a000076032540bd4292006621950f100702c905440c1100c0e9031708201c0e41c8184500360340010460080400d91220020b40c0020115000c2951001000303000c510703140b07000c500a80c102111404011038001040c401c003044070018660381a29090030f5490f80301c248030803a00108465070a10a00d462140c0d814421414144000803c41e101916034aa0f1b1160000c0701c1e521105403000007480354540e000600c5210700401250400a888000002c12000900c100403029507644002000240d003200e01000418154440200d1009c010f08040410009203031100303200c5405595013074045082a002c06003210102c842e007a88050401e03040100082c007415001d003c542c1019424003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 923306438 1250 923305188 923305193
    0x40c0b130812190206070c020616020306070e090a090203031c14010801060602011503022101020d090506090c030706050307030c12021209060c03010812070f0615170109111c 76
    0x2038078220100c082e5500d03480d0001071200c50070f04243d095a62085410213414800c0700c903003040c13102030010350460b80d19441d10102d0300c44415448014901170f40c140b0500b0709211a0340e400c07030f10303580d001c0000703a500042d16078a105005054500102c402901903100b04040010001d1610198002100320500490310b09070081016034000020703007000165940d03901c03041040580901c5800405020b55200b40300081c0785400050015030200c0d52500c8071076102c0840d5980c1b520a60440b400391426005c10420010b050510303075902d42c4201d40d610b890780b0581301283c0d1980b82c0054884101c8000780e0740c0074619a100034040f409442216a041d0511101141890440c01c0034005080001c500c01c201e9510742c607010410600e05400605510ba003950100014040c00c0008079180410580031070b030321a030301d858524020b83d807510f10300c101408880c0341000000c0c000c8901031b202401c65801c00341490140400c41100307422603d106100410042c20f0f1548440542081610141d82800d01c080140742042c10340c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 923307688 1250 923306438 923306443
    0xa0516080c0609031207030b10052212020f0a08031605010b0d0605070806090606041a04120b0f1f060c0203030d051602010c0e030c01030b06070609050304140603040c0b1308 76
    0x340d0780305107142c101140da0b1024085c0c0c03003c0290b000541d03250074051592004040b8000a800c4801407040080008118035021000381520180002d180550b54160341e80c2c41d8028002c404d0020103d11503c1d082d402030201d883c145c42801c041d01d0072034010794506407450440c086001400d1004869554850140c01c036541e45196462019900074000810301d40f5140780005d1980000504461089420fa07040c802d80d40c1303a8006540c16144103038400d90003a0019a2500b9090245510107480888013090040c00c104458508a0041825502d0503c1c0da84904500403c0040c800148107045111250f0800c02c041c811401008101e0010781038900e0440c03d21100020345d00121402d420381025081c0310080b20780d091103440f42404052910311700700f4003404002030321224500b003042e0400d510b80b500484160349035421174044c02c0e40a00c0803c07180306240350441d00c030340092041222100452003801824280b0310b04070b0380310b40e90001c0c410350f000d810110f48011940000b00070f11a000e00030500420909000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 923308938 1250 923307688 923307691
    0x100c140105010b21040f0b180604050a060e19150b03010213030203071a030f1b040806010614040b0904091118010f120309060e0d0b0a02030415020a0516080c06 70
    0x202140b642c0d10800d42080d8104100080382c1640c4d00b0480c54104001700d4103906005800b160f000391400141e480e11100f0b20b2251941d00581e1304540610f40a1208110300000c400c043c031842058280b2200e111506000e071950072041054852401ea01007103400500d005e280c0c030480051720100003400b18090004282280c00580d90300e000e401c60840148290310307040081000a02120010302102e021402c90141d99000151a0a41c000050804036010900503480e0190000c020942e8a880c0c81e80c86122594416080c840c0102081c940200c1c42d80d10000e00c0c00702d4090754043c541c3c091805042ca0203110003001403820a407880c00c401c4017116416614182d114003030204c0700c0601c0e1029410058180070740d90203a88492202a8048075400029402c81040411190242403111148141101103505404180e100070185c491207410000c120180c2e82c09140924080e030a01d02c126404903d0741c004900c01c000b11071001c9070701406485143d152490603078484070b1140d2407490810709000c02a5141000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 923310188 1250 923308938 923308949
    0xb0411031806090105060f040905070503030a0f17160c02010c020a15120e0604020d110409150b0f13240f0e090c1e28051003050105100c14010501 64
    0x898119509001c104450f0060101002005642021700001d42030440e11140540540e480e007460405000c01032011031f00511000d41920359072444040000c041140e00054500455585906101f1902590055071b00c1a41c855217046910b9180307000503284079110720001c03070400c0000700c44c440058480500303110041c0701224003072007842d0344070b003020b41248480512918558a8094000b508500016541d9080750f010340e5400b04c05281c0703040240d01840220303120b80c0c100d420038145000700301c00210034445251800700b04000a0300c4010401800d083e484034a954001aa00c44040c1c14000c0d50f44075005031130310032610f2003a1621036025030703541030400da2003c004004900d03030400c00c82c181c060b185540040003001510f1180c040e00c00095490000c00c80c1518104c011072108038181c0c540c524500c1e0b85945d0350f103000707648a4501d10442569400c41c0120390041d01035129020105000340182d906a0700018899010396445e241c1c102d61000f4038010660f1080c141081100c1028020300c6824003805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 923311438 1250 923310188 923310211
    0x501050f09100306170102090d14031b0709050108060603070b0d06030203070801090b060a0b0307050313021e011b030e0f0303040e0c03010e01050a030503120405101509111306030b041103 82
    0x61502c0d8800285c1300e05025000308690040020380304a6440440c2e20042d07aa001410164403a20a0070361840d500450808031100c0143c0810a201c548002400b501140c00000c4184010f03a01d440caa90748504d400c0c0e80d0716415602841c070910241100310058410030b00240d00001c2c1059490300080e1414034a0b9211190036595100a0424480034010301984240c1c00c0c0d0300c000d030103464014040b0051200425035401c000d408404a2848070782080005910307600145805070a000002c400d9000481c00c030740007400b2804901c0e02c07903940c442c0f2400240340755030507480302d078914044903045c0032044405049465150104020105503210001d1605009484800b201512581408a4503a0804040c1c01c210312485911000f0400175000008403130100c6078000f41d1070000d4980f0b00d407651405403c48500d4601900744000c000f010004440d020080f00c036a54000c0c0003968007a0030305202d903c10701c0061004844260024040c0c14065000303c89403580251001400c0383c144402009541c01c25241100c820 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 923312688 1250 923311438 923311451
    0xd0c08061602030a0e0307051224090d08041e050619060b0f090d0204020c010e011b0e0d050703120c331802062a0a0503040501050f091003 61
    0x1410402440d036115414055101d076070303107a1240c0607603030b0301940c40319008102481d00d1490290724140408802080050080100701c901c8070711140d11f44984009102d20340081403d40703030200e8021a2110300030f04450340641a4901c2114007110080002401950010340d010781d4546103462528420000500401c003612142c180310f41c0c103940000c2901e10311045e2504000092080d00346500c02c641c0496080003c060742c910110703001c500f0075941400b000c0c0d40281701181e03500d04d030f280640202030803031b24070002048074448007148528128041080317000060b01d445030029890508801aa0361540200e044808256485c0d503140320404100c0c01210000300c21300208001c02c0841c108078007810062050340c4946006c440c12200b010309114a03c10102a10b0316803161280138010070100406801503c942c0c1d84000422446141c05000d0b60000e003004405078034045404404140741d400d403030340701001d94901487d0a00464003a0401c0c540712500340341c00c000d41141641c9030b0a103000544004c0d140421718 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 923313938 1250 923312688 923312699
    0x3051c0603140307030801260703050c131401030209072001060e0604020a02060a02030711070839131b08010f06050a020a1403070b0705130911031302010e0d0c 70
    0x480c0800b41e81d6900c0d0344140000d20000350080405070660300d40c6500c0e100e64030b41b400700c0307088010b295003042c00382d900030910084107000022412002c02c603420b81c0c0d080c1c0348001c1c0105840c2294880c0040083c1c109000300180300625000000740d4024056240540700030101000f60f42010320b103070105031030507036445a0820480484091061b0701c01c0c800c071070850600d00c5442010b92104030007451070a040e903000001a403205d002d4080c0c91080c00340881290001c0d03845142183c4e44040b981d0a600e4104140c06035004a01098268105170744a50300e06640884403a105100f400c1c0c200010005103503842e41e600d843c03491000b01131103400146640c0d4046940d4942450b00c101e016030b54002c0010440c0030040c2125080c0c002920f8210f20398040f400704060002010b0050850080d02c4004103403000d034a0030301010b241c1c01009458180c0c2c0c4141d100c0d05041e6289240c0048404000c0030b0a100d2400380005082440c103655400ca403180181428540001d424000500d001601072045521141d0003409105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 923315188 1250 923313938 923313953
    0x4020909240d030c021221030906150607030c020409080a020d030b03061315110a0513050a261c181203020703170409091208150a09020703051c0603 65
    0x101c40409640b41000d8100a0301c0050000308524400f0703000740680740a100080104214006042c011040c5104c42035001040c0707521071358001d40c0c6403040e038480d61010803c0c03030415607903450074a0f000a042c5032400101d079609488007455884140e074041d44c0c6112074004541100c0040c5882c0c070311139000d40702010523010060200c800e100c400500a502440c20092010380800291001c142c0084c5280c2c0b500040c0f4003007601a1000c04d126400320000420b01c120f5158000000d0100301101048a43d5001c0d200d07000d00c2541809ca114070283c04044d0398103820412602c59100c14041204400d030341d14030701844294503070038500b013a60400080000c0c150a20806810b1100302c0030703101c45801c000d00407415880080d5200c085001c050701110f880020710b908a004c800c01c490040840f081e060003d0591420000840200750901c0b1340411140e0002a007190789000500c0c0345110b0003041c0000440c10543d080d4000e41100e0f070b08400f8004100306405204a09220310102420402c00215106003503241014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 923316438 1250 923315188 923315251
    0x70606030b0f0906131b06021f0515060703020c180a06090e07152a030906020115090f02070203010501030809191401081b0c0d030501080a030c1104020909 68
    0x18042206101440040c06000c2102600700d07560090342c034a410700d80c0c201741c0708040c00b90b29444010640c51b0700c00143c1580118035102c00d6803031190075001c2c5800c0c401d20300d0b0580d0342c00c6400354101d4160a4801001e480d00b0009028081c0c00380c4100c5040314484804a903030004d009141a0b0b00300840420081c1d040c0c1180141405071001c2c020605c5455000b50740701e81c1e1900d0070700485120304503040010220511611207402400c40080c803580542081482c0c50240d030389002415400541d102c1008102c2c40d005002c0d00b01000f4000500032447c0386000207080c0100041011005150307000c0106201503602402018043c1d80036900b0a9036800400040120590010800c0418001300080400170119180c9216440c40003e0801003800c2da030300e007100c06076078014860b27900703800b0000b259101040c203000403582510b020b107072020070090762115041131340d640c0000c400500054400301c5240018201d14400c04101c1c00141001d030900c821310f80080d00c02d610441e05540c000b6414075490020300b1100c0f5045 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 923317688 1250 923316438 923316451
    0x9070306080c01140f0a0e190303080709050d030c05120408060a0f06060c08070615090b01110f120f040806070c170418021e1b070b0c0601260102070606030b 69
    0x6003180d1002c03084404d40658610304201a0021842000e22405500c01c5c070b500010080c448264400764004003010038505010540c00141d400d0002005240100b0114040d218000c4c0411015801e0740d508450104600f041110240078810103201c105480d200604040c20340c140c06010b5501d1b0082c1c25238112030782c0010f10250b45040c881e041001641081c4c07104149a00110410780d43c28803820550042c0c1805516207203501d242110004d0603e12640c00411008002d81c1c4074800c8041c0c000796a41d40b640c0701c0300d20b0f003000d40151146030340308000140145444850152901d041c15a00d081c200c0c10702004580b10000b0a1440245000700301142400304943c8880c0b03038015081500740142c5090745401180c0309284507a00051a400c5c0b442c0714140c03601c0c0f03020a803640755a20054244600d1805050404803c454411060081161a49a0241d03100c1c160090020045a860110200a182c83c004900c05505d01002c058079654807080c001005032600840c00400c210786103140070541b060004014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 923318938 1250 923317688 923317697
    0x9010f03030212040b1e07080f07140604030509040c030b100507050601060914100e0409110a080a08220f030302150901020c0d051e1b010c0816081509070306080c01 72
    0x510100b04460240d0710f460405884405a070844000c3d206c1030b502c12404003a01e050004110082e0410200c1c00410044c0d10070850700304072440345806a41d4501041d02c4c010003194050050810301e04055120078403c403401d18000c500781d141b050208416401018040000840006100d41408003c2092500426103071611034000d42c0303042c1d104e100150082c00180c1c411003a0007005119a03110328040e02c000d01004104001c020590b00c0c00819000c1c10f900041e010b00030400d03001480c29004a90140304a800558540c50084500310320260381e0070340d48484000c0b44843d038001c00d0342c008000460340a940702e500100f2800d118404000b00e07030000200b006105030300400c07141c0740003400802c0c029003d02841c2045a202e03000589064240c6a900e1403907440c018020a505224501049855082d850301d80c008010140203582c00700c69030346040f55148034140b4003503e40704183c2c1c407401d815070b40600d100f00000d4106090100003203d034036080c0c881c3d41c00aa1165003e00c4190000e011580c2261001d081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 923320188 1250 923318938 923318947
    0xc060c07030801210605090a02100f050315060c07140406090507050901110f01020a03021903020406081515070602130608010609090f0b03010c0503011508190c030b09010f03030212 79
    0x4004242c034505024944200a01c0340f00441040e065451040c030080d846901407103113280c00100c040c1c2d2400c1c2c030942030b84644000e00041503c140030766440910030142d43c0d101880c50b035494441545030100304040542292080040a0700480705000440103001e285050200740511241000183c44158010040f03440c68401071005207070b0050b0807500c98003001e003880720840449207103140c203002080185081c1940001029640250306a0081c905088020099603040108041c120102d020340d02552011540810100d0408454003d4216a0711001440c5413405083c007503814170345c0d0304094400c48807145c000c11070b081800314522400c80900101c0c50240030701d602d8440003c04018161068207911a0b8642047c443d2008581140c0d50101006c0c00a0104141d075020041040e48240b290500103011260a90b45292040b03007014007500d500c0107105001241c0d180004000c111031403540c0c5c107040e620345450701c0e03946802c040f1600a240e003114540e0802d103182800307410240750003105030b5240e40c20003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 923321438 1250 923320188 923320193
    0x3080105041418010f060f0f0b16141002040e01150f0e01110c030601121a07050f0c0a14010b030106080f1e1e031c020a091a07020405010b0c060c07 65
    0x8140d580480709003038103400c4950b00c0f4110b0340104000381e5580411401c0400202d000b00c1071b446014100e0b8400b1902095466a0b048004294014042801c03c0c3c0714910091030042804660220030581c0041c0558a42020052080b01285e00039030083c01d20910042c01041488220303011b0041d000001d0500d40c9000c220004024881c00784043e02c1418010300c0300e48214000006c1207402c0540e0805400c03245d0950719400e000d40e0194841e0307400c680255a4145103070503240c0c03101d0440e004040320b494560500f924a0040e85482d000780041003c5442000c0480001c5040000c03a111812102c800001e0381044ca4401d042c2544c07255000003140390310188010040750000a0703820001b804241030ba82303c1c0d000c5250610b0900c0e4946480c09041c100c440c041158186021000f08081c00c02c90b00d0f0702070100c1110300340c80140d004402810380404d240906c2080341c562100306072086c0c01e001801d0185041001c1c1e0004080b59400c4e000006081c8000c00d02c182040350400010b904016030280142c01c0440d02e5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 923322688 1250 923321438 923321471
    0xf010908011b0f03052a070c0b070606050102150708040611030a0b04050603010c121a030f0d0206070c081806090612150f1302090d0c090b1f0212130b03070c0308010504 74
    0x220307180d100f494905004075104035981c242c0311a00d9001d0b070110a800d2756001100c0c03954111040c203884452401c0030010303c941c0002032101e03040d8113030344242c24141e40340d00090f518124024000e80c1c0c200c2d1601d40c0c0340700100310000154820014070b40c1c00100344540400340421240c00400b9580a6850001444c0300c0769000061800e11810005002c51010030000070b20022101c040816901440f0301c6400850031100072455501c00b6010b80d0850380140d41c0c52804858000200e074001d0542c0c4e404201841c28030800e003024040000c0080d042c64684030310980400c170a5440504900500e405001c1848010740400c2c003c140a8441101c0f0400da100441c40014500c90f500084456003c4d40081d0f50419611500c2030f00801c0c0d0780040031058403907503c0c4000005043c15003c2144140d52003040302246101da520008280c8030380e6402001e01d0302d01c1003401c00c4241d20107003500042848003040010b00c900f4490045110388016590315004001c0751502a020b4501a00207600c101d0910204c03c0010910 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 923323938 1250 923322688 923322721
    0x1b06110c10061a0d06120312050a0c0c030806040621030801080c210a02060403060608100905030d0903120509370f03030b0d200105180f010908011b0f0305 68
    0x10f404079550380390400907040041880b0340c00804000d00804240d824140c00032410054290000e000340643d0342c4070380c4507804503400b1814517004561002e102ca004030b840b41c2520740d03000001920000310340781c48070b00106460800000e4034180c41078a9a03d0010160b02130183ca00521090008086171010800000c0c0f5042d2908007a002801d141c40e101c0c111400200003107845160087c0146075281c1d142c0c28200050881b0340180a154411842a14a2050544a802c46007074129010310b050810825649004e05007580090781000481e401c90382c02c3c3d00e0030340700c0c0c140940d0300c400051000c0702c25461446500da44220007410000d0b810080c5030140c03010300021554066002d40985105982c42c0f0b0182c009050203104103400c6200303c0b1541c41048031101c924607107064400d081c00c440441c40c000442d00c81c0310305040c1901c84041c00010100a04145440703006201050621801194807120203d00f1a0384c100541407000e51249800e0040680240003000315192a1a06000500d4000001e82c104840c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 923325188 1250 923323938 923323979
    0x190c020f0a0b071404080c1f080103060b01020a0213020702010f0503040f0b0c251106130504020d180605010e2d0709050d03020717010203090a031b06110c1006 70
    0x981c80003c0c1d0300314400c0c00c9000d0900081034540361110b4890aa0542c3c50b10341d401854001e817050380700c001070203c80710518601802150b0b501e52a03a0b0855036038501900d000e14840d8103510070650494016910340146440500e41254011303142c2074a030000625110015100c0c500b807010801c18400402c2606448042c4142c010002c5403594550360800303001842001e14a1940c130641c403c195081c80d51a40c584001d10340a1040e50381406810410054540b207005580c0e02450b078030f01820803260074150082e041c48900c40c10b000518481e0410005160300c017884089030250f0380c40c4014400c1605c401611904000204441c95440c40d06004404600c1c5a00d0451000038902c01e00090605104022030070140602030000401c030b0005180c040d544e503059004410300b04411441010120105109603481003091400403d8036a081d91070036200c001414902020120030350305035001041c414022200d00e01106988a650d070311a0000705030404c076000c1d0054610504140d03041200b010b400712810510321 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 923326438 1250 923325188 923325203
    0x7270f02070803240907030905071a1c23070206070503130b040c0b0c031206120316031214011e0e0105100306031202010504021018031118190c020f0a 66
    0x14130038041d0b10b401e1184150140d401002d2000f0401003503419040000300c0d51041045654007503c84802c0300441140780c0714030301c48500c1032011030300c800950200060b10428be0032000426505c21040031040303002030590a07066100728030922178069410096503038459104e140c00c5045040100c07030200c1e44010f03c440608111225001305040c0320380c041d809002000146403040e940c4403a4000d00780c407900440414114040a00b00140d030300d04014440e06c81d000c442d40c018601d41b03800d2a8903030038000c0007158150100500307042c00708107207180c903c01d40b003400360a030705944103541c503142041c4101c502200c5254401340d04182e041282d01b10b403104090540d14210b94004d103030749913818100e000302681d41c03020f021500c2c0c40000d6820950190b004600039070007583e400340d6002000c85e040c3c840c200258a010400660418208085030300d901001c40080e10080110301108040004624804000d840c40074140b40c800a40c580c042c0b00b41c0c031607075070078800728009460242c041d1102039880c0e501108000e08001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 923327688 1250 923326438 923326471
    0x329040c0b0c1f06060e0f2107030c060e0f010314010302010e0d0803041208010f21080c251e0302040f061706010504060f0b03060f0307270f02070803 66
    0x40b60203000c414040c00010740688010600d0102c05030180486120b00008101d0091380c030304007401c0a092894280d500601401b0011f080503c62510354086402001ca050107036040c084000380c00006240020080c0c0d42d0303840043c180910800c20614060042641414a4403010007059400c0714650350441e502420300c1041400342c0c9000c03544860700410002c180c03201c0001080108110101c8205800019130380d84199070381c80c0c0d003c042c151203d90081a543c00c0c244140b5804840450710007111543c814141c0c2420724240b01d1400c0d00e00681003070081001e038480c19030010140680c00d10b8100520005520130714000207031030f03a040b10440318080030303000f1911078035620300c4030240381c11001c0104040c6001c0c6000c4450040103580700d00c1c080c0580d920032428041e000582c21000040d82d01601c02450b0614a9a124041001603000c1c1e0b00409540502502400048498645144041c2081c07000c1144d00d104e08190100d000311040c1d01032118916106004075404290154181c0754003000803445090b86 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 923328938 1250 923327688 923327707
    0xa0204051f091a12010b03190b010512040b060102010e030a0f3204080606040917130b0a0201230f1801090506040602070b060f0f04020d0f060329040c0b 67
    0x200300c1034108038004122041d00c481010b02c1c100040050f2190700d094040541d0302c801b94036840f48015104101511200640d4008280c4681e00c605202c10050408074a0060b1006020020510403641611042d150030200a255602801a0311440d160f85005d10300e4582001000703007052001044d440c040280c0c1c003024070b200c821680105069684040c0c1030000481e8401c00b12a02c1d13500c24000d501d0140120004510503052a02078a50242c0d840b00801d0741520201402040542004e1003011003c8150403000a03141003c000030242605c3c13590011400d603030720200518000408a058084003c0074108214264412803080c58210040c4028070050700680c00906001d090021005451401890184420401640c2c0107048031881020049940d03522a0204903500b80c484800507001421960704400078a05a030050400d1080d249002403529440201a030440310150002c440c45031940c1c070f5480c08030041c1c1c9210881491056403180741460282e0740c012040308a03205400f011031021882948 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 923330188 1250 923328938 923328947
    0x603190c2615091006030b010506070f0f0506090f030705062e06020a0311150c03090709050c0d290103110c2b05090105070f020103090f03170a0204051f 67
    0x20010080407076071034900012036010108025244503c4a2003102c5050410b4280b81c019141201d400440e031291507031810341444003c2c0d0101100300c0f2040e04042c202800900c060f40d81d64040c5002c0c0740141510703d4440c00162a225040415220641c070601407000003520004400341d20600b144902c0c441190f081c8942c000301c40d0f118002c3c0c0c1150b440d6580104040e9800030307050381603e000b5a0b03070320300c414480e0a034680c9408202070448800c03130781c410009050001c0c1600558008072100212403506555012450440d507040da603081e9510400110301d01c0400c424026042448800b403025200e10280820707804900b0741000320725050540794108642141e4000f015508201030701e5003030381c3c9a02203803400291802c03515050002c20000c08071189222030322a03415102441c5040e10307964a0302005880d1015503c0d10b0b0a012030425031500114030008103255043d403400d40c07003070300d46191040b02e0500118040c10700070501424030b48107200802403a42c41c0c00c0c0d00417907a8000001603840c3c6501d407200300d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 923331438 1250 923330188 923330249
    0x2030a050d0315050103090503070b07210504060e072117041206151a0c0a060e0f070501030b0105120718080705090c030103030512131a0603190c 64
    0x30298001c940c01e00115a8040d00041d0381011040c20204581c1d840300019401c5601008000d40254420700c032070f800003403001040b190452020b081c030980486407114520700c09503e00302111212520741040c030003009500d001d081c4880b510b0b0405482c0140c00c064075030304102280824011300c043d50702e01c12400d010ac5950410030f200e0b8031b0840d0a555a4413000b03846860008400c08840103441c00d0807000400c0214103a403415200d0300012001155000110894280c01c0010030130014080d03410400002011840345852940d2084090138541010158445c103104c0540d0016040c941440f291910f140e030b101e81201c030040340c0784444550396100c0c3c0384219041000444d8030049820a04000b060704503000415074116481183e080c22a60384498050002d40820f201c01400300700d040c403444000305407102020364002d11180b03030700c0c898094035181c040010100b020030304180451102404410b0409001000300d85007090204042d1020507a5001e83c0500248621419503001a01000300b91900d0344012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 923332688 1250 923331438 923331443
    0x80c06070209071b0b10180e0c0f1306030c030b09030f0f0d0216050c0324150111031216030b011205060f030703060c020f060103031706040902060c010b01081e01030f02030a 76
    0x501700e0745000107891004e142140503030f9207115035105a07c0d004246a000f0841c2c8900f0540c0030380b0405180784180003080d440c0f860800e520004010200c00c221b1110b12911000f5401500c003101e4052450074003070210b9102070004000c81d0810440c4040035071503101140c0040303c8617442981e840c02e92140030030003401000c0d100256120010b07402000c1c0000000e1405807040c0c11401d41d040c001026105c000c0b0780030340c001543c084452440002e01c440102c20024001d00c203060421a000c0650500481d00b1070340807900444c01081e14000340316081c548003480b508507441a0604024002500b4000b0340b1100d02c0e107191850198031030001034000d4440c02c40c0c02100e01d030040c1c11281a5901c0e807601c507001c1c12170b000e003500051142c400c02258450000480504903501a101c2c1307282d29581000001e010980244140c1c0c0090b01c40d1039000058071031000810700d1603003290001400c070704c01c000014500f85000e40b500b40d44010031054410441d21000000741104e600c112242407002661010034201503401c03401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 923333938 1250 923332688 923332703
    0x6070215070b0a0c020c0916021c050c10020307080424020705010203090c0108010f0611030f0a021b010801050f0d05010609020c030d050c19051c0f06080c06070209071b 74
    0x2000420705429003d002c101209025010801c0c07404c0340d4030a010800c8980c82610a404122010602400c025503250141b05440c10340020035407842c50f50119005540024800141c2c42d15920000d2090070b81b075002070340c420341c5103091002c00141640c10261001d88804801c814070416036901c00103400215941c508150b48801e001d05145d03000f5001102c090b001c9000391a20000b203580315080c15810b030f41c500c4140401240c1014030840c0c100080690301030040c4003c02c10740b8160b107420350140c202c0f014503074014040fa00c0805014a0800320b1000780354103000f1500d0050001e075440d5441110141c1003a50b0301c20524180b810940c0c05404250b000c0c0c4e01c0d840c400140101c0e94140440180703101580420103000c6903c410300341142c2c40c8a09000c022610b103249042d5200300d0320406c010310311070305c0d0001042080381c0411240002c4800c089881c0070069900c1c50304010040c070900101505000032101c1d2420606150042600701c7c02c001d02c0c900030013588615441050544201d41007106811088 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 923335188 1250 923333938 923333947
    0x2d0c30032c031213030f08040c030507030b010305240121060515183312010f0b0a0803070b09150406020310080c0f0922051b1c0206070215 61
    0x1116501d81d480355070341d010036003c2000042d03201d00d0302410000100b0b602d655002d810241090f0100c0c1c01141c0a48200c40844001c100000468070070425000558040c001d81000d075451450000d01d01542904203501f10821003107220300000c4440402411103903907004c035105c40c641c1480400c04040100074001e12503403410082c803440da00e01071003900c89904213a85004004881c07042c07403c2002c50807290032000c10071007807010518000803542d010005503007035251240715540c4000651a58030180311074903660b65412110307400c0e2015004d00c0ba142d11040d245c51150f9418481e00079181e124480c8041c01d60507040001c0b8462410030001e051180d03e940242240e58101490814043c3d0b000791480360310102c995001240d8040e000c221041310300c0d0000c0006503403120400612250301c0d03008028209030401c00030a00c6514481101d0150141c1c4110080c2c01d80c0345040c1c0350b520424515100107801405002c0d500f0f802e5010307030549400c0c0260110780c5e05403651100d10000719111314015003c0700b880d00214 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 923336438 1250 923335188 923335271
    0x30f02101401060306080a050c0d02060c010509010905010c030e030301090c022e110906120703180f17071505100b0a030504020108010501050c0307032d0c3003 70
    0x40007038143d485540e801d00603281e175052032541d00e40d080c440181a0f600030780302005162602c4494400700350320150a0702d0401d140040c0720340c21a00210b0b4002c0080c1d444001c2502002400c0c4198104086103050030003883e11038242d2150f0303e0005024180d4130580e104d00d8403514034001c01607002c4290241c00031070301803421402c079030f040501079101c032501d66418246045000c1080c101071350b850b41d0001d0905814004103e924080150000d01448103040d5581c18074024a8440400d0380c0e64a4020801461480d0440ca030900b44036a0903449440c450100744a0380c0c0024241c1e02e40d8000351302068a02160030b40384c400c1007c43c032101e6a840342846020000358000e6041d055004248214003d0301c503550720340e80c2d0704010350b0f40c0d101d50f4840d200c1940041020000007400f0b8042210021202a03240c40300c070300c140f500304040300c003141440c4020545104843d0200310702000c1652940c00740800382108003007000782ca40c984010002a03c4149038484480810601100003041032030000c5c40c1d41d210080810340c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 923337688 1250 923336438 923336471
    0x106030b010f15050a0804030e0f031209090a0903051c140f0f0906010503100f02070c0803131d01060305071803030e040e071811040308030901290d030f0210 69
    0x503c01c401440011012141c18a070141c01543c0c0c0c000900c2c1c44e85251591583d82c04c89603000c2100d80c4e917511a0008140d55610346080291408000120703001c9580c400701942005540c607402030442c10752074208800800025408810344042c010032242009440401c0900000502a032110604e82d4052090030861001e44604070240a030908c41804440c41d1074061015840f00c20074020ba5816074411203071041d8446699010410300001c035500103041c45e449a44480d140f1880740e001964076070020072402ca680500070110001841b03100548040075000c203100d481c040d181485114145983c0b81c00040d4401c1c040c00f100101860f00c2044010441d0b143d14026003000d01109500f4000d901c1e00e421110840400160b0300181c540060b0040c500e503203601c100a01400e007560340d801d2020018080040001c2403080510702036890741001140e101c0b08202090940030051070303411b24803a0482c01c1145d69071680803440031419054a01641600e0080506a01c1e04802d801520502440c0c1039041240002c1e2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 923338938 1250 923337688 923337719
    0x303150905150a051513210b070e09040b1f080d11150f06010c0602070f05160b12060d0c09060305010507030203040f0b0c190905031c1d19081e061012050106030b01 72
    0x230309441102511054002c8910035203011851703030003451500128000c01e10002595a120003d041451280d0303000403c01d0103001032560000219500139110882030b15000141503181035010002004018044c0701c0d01320340e40c200504403061500d2a0404903030940d11030b20841604070f030081800d5540317009500d040100c1c91000c100c2034645004424201c81043c0c03462002900311b27221082c0b96800c1040e0008002040c07880030b00f98a5002e0a0b1486c128000b5003400502030040662420014a8030314505090b402d4850007002a004c0510410070031000850180080100642003546c0d00300c076907a07a40b90604144940c400d01c0d0207070001040b481c03680075480040c0710b05488040c0e0a8800d80184042d11103600080320b00800085020000291f007107404158159844d960020020303000c00e02403000c0c0c1c507141700d029000089140c0002001c21107035510b044442103680340320b070020480751810448400c1c900c8820f002c0d07821a40e142145e08800d000c400d41088001e140c111010301001e5030354944803415042e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 923340188 1250 923338938 923338943
    0x4030c08070b040f0b010b0301050f01110717150108010221060f040f0b0406051c140a081801020c01020c01080c070206040302030601080d0219030207120303150905150a05151321 78
    0xc45c90004180c4400e404180d81c122800901004000c0e44140011b40360700799100d010f4502c3c2d10502400003040b0200603d00b00203020b508001d412001c40c0d00020b003c150030160030205680c0c0c010030a40c9500303081880003001103d80280e40482941360300c17000a1521105948490b40030707007000b0042881303100503444080e05c03640c01c0340c081000ca5510310903c0160394900c2042e6428030300c1800782c2000702c1c80301d041c40d050801105082c0d03038446000d82c4e41c1c04080d401c080c00c42545411b05250700c001c9540c04101851820000b400208003140c99800001c1420750f0051042d4025000810f0759811511030b04160307005550f0080540f4055030f1075901c0349aa0b20140c1104900600c9002001040c4a407400c59110799a030300b5074040c0c04440d041c41c0d0000046055801c08608065071800d1500810429071011000780c0a0000d000c182c034141128124415a4031f1981e8030b02c9800d07010004c007c1995101c038441180070561151517241c0300c00c0343c205852000c4560104030444500030021003100e0160200681562 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 923341438 1250 923340188 923340203
    0x304060c210b03101122030f0c1a0c060c0c0703051005161704020f150a0305040b0a060f21020a09021c020724060f1706090606060304030c08070b040f 66
    0xc0744102c010030b68240400d01740d503d81c0208420717000b08800318080c81c10440c804501d010325aa1b00e07074030500b55581161007594594541c10082c019220244040240500c201981c0350410400d000500d450302c8002d00614289040010281d00c910b84c2480781700000d640090584c0c03010b013100c46207800509811070f070a0031054001001c02c00310301d0240c0c1481820b842d488280e007909030344075428080c0048203510401c0d401070402039100e0424141d18014603840180d650003080908003454041d1000070301910010b03c450510b1410302810b00120b40b02804c072001841009080e45052040d4a0f00c0d04800034065001440508041452004c54004100074a00010301017107400c140c3c07814000f00c0c01a840000c00d40d14000c1e103640d90864140c200049a1700c00c1d00000a806079a0f8030a01c1140d00899000c008070b580ca0341c0703041500310402d000d0710b9440112400a0125841c3c0b40b1300254045c072004000405001280d00400305108a0030300b690091680144401e080303041c13600700120081c0c4842300495840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 923342688 1250 923341438 923341453
    0x1b0b0301090b1c0611040902030c1e03070f141204080c07120c1815150806060a0c020607241a03070806190f050a0c02160b0304060c210b03 61
    0x341822400c50503515044507044103c042960b89000160042a0010048110074400070410105510086002d48200d80d00c007552405100350508040700251071807170240c2d00600401c4060f07904110304044481e403134640041419000b600380c10003402021076003030800051300100710400c1104401040c040485104490382140e0b581c00003924031108003c01000400300310000c00c5001e075444007005d60b44410340310200b0400300b561009c4c10215900e5014614040401c2010080c440c2c1103000580c110400355215803504a141034013900001c10030900034000c04001030220280000700c1c82060100d25100740303103e904120035208802411455580302d0341c90600c8641c3e2202c80c1780016988003111007150203400700d50303201d450f03204040300c01402039205503894050007410303074501d44101031080032002030005a00c6600d0b08024034001c8030001c040c2d4804030101d0301b480220105025641e22a40c0428081990807040303004681411405072810215900d54059044a2085420452040d4420350860b02304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 923343938 1250 923342688 923342711
    0x2030609070b0f0a0e1519090308031317161401020307080a0f0e0f07031a01080601050f04090209040507090c030b01050304060207060e0601060908010b04020c191b0b030109 76
    0x66859510a030003801a04202c0501050310040180403100030a06000100003000d002103000d0086440b03109204040002e607e04600c500c41705002e0355200c8a1518940c414211341e516481440082c11081d8200a00d2500e0802c115100d454600100d22480c039442d11210124854240d0184080f400c07a0480e4200d00907218031107052007030302c3c070401ca02e81e41c42c0d4042d106c00d02440c00800c0220144480a51281c4144400240401c8803000b4540c501c03004081951540c18810460400d5003000d07078003200510010030006000040302c506460003200c050300e51260b243c0009004000f150300c0250400301c808100814450301007041400c81c0da0027003040c0031400c1c111104070200c9500018a9010540034408100400c0e804e6001d040035900c141c800244a00408021514028099200c03a00081c3d641c2c0c800d00040e0801c1c0500700280400741d40640c1803c0b80d0b8103105484d92417844a007441583e00400e06000d0102c0d41e01c2e212032180d24200d500c1800c94440f5841841a4024000c2d80c2840f410094018103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 923345188 1250 923343938 923343943
    0x80c1c030902060315130c08060901050a0810020901030213090e100506030a0b1812040f0b07080412060b09010b0a09170309061804021810021b06070f080f0702030609 73
    0x1d0340c07540140300c07134507564490400c16040c4c90007504694204032a4888005031801c5480340085c4000365072104075641c0b030f100c010480c594405801160054084400c10401c0000001d54107050075009503000d600c03401d2002c0101d00900440500e0810b01400001c0000c010059a224541c500600b9055070326a881050610040c2c80091741c401d42c140c0c0c40b407015a008503850f403034000c3e00314503591210320202c44154000b80c0382c241580400c494030200020704200c2c1180c11b0300c0c00b030f00810440b60000d09060141c0c5490030240503c1c4a0100d40b80e80d074a641c8000c0004642c84041211002440c0c26802d5031181014982904102e096501040c50b840f004170f4080071759100c10000300c8160006528101444d0b09200507074010340105011048109803041240c0e5540c00503103581f1512441c03403401c4505803001c02c140e00c001218504199000700c0302450170383d000b0303620203c00010241e40c1b85585882070f1408510021001d42c01038404c40010400041c188035040043c200240200c0c211903054503040050794 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 923346438 1250 923345188 923345201
    0x5010506091605070203031903051608090d0e060c100b12060108060106050a05070c12061406090402100207031703090708070e060405130f030c060f09080904050c0403080c1c03 77
    0x110b410400b1201e10707080b00e208a008003001c038406001c0c2d0781862a0408414203c100b440008070200c0e48600c204407003600781c0110300114190030310f0f001c80c0c141080070205d500c030600703000341008112204803d40300c00c0d2561012104066801c101702c5002e0b6180700080c00c000d04c1c0d4616000d11520151122040100c070000d00903040e15180b001800340c5910300f030310070b546d80d9100c48a400c090080034044040880c80141e5178500812040444041840c045e01d014011900400807a2a101a03014140841600c0d090388041e4412342c140c511640101c070261060380b921540303a02c0106090b040c1003005000d941c05e00040c42c0500c00080440d0304168841c4001e58032458180201400c038034583d00080c8446c0f4003034102a03041910514042480e101603141d400d180401100280c5c0880c00c007162040c100000307841100c5030702001d00740401803910545e0f1030608034843c11601500c1540c440000c00c4071080480304440086500500441d81d07042040c00b65a2101c001040d91080c040081283e883c5507400b900520 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 923347688 1250 923346438 923346451
    0x60a0609200a1106090604030e120c090a02040b0c100b03030702030316020d08040b070b070f0207030f0c0e0717060f06040504020a170702010207060b0a0515030705160c030501050609 80
    0x10080300c210780030582000c1d08a0002d540800c21154070b200b070041400d12115002c0c8850401400341441c19040c003414440010004600882d80359000b101641c00200745401400002c030f03044007a0b9182d29509034064010798011a4030351100160750750320440f001900d4019204010014810a80141d08041c0c8034042d040d0040c1d0160005c100c003040c440042d103004840148014002c020300d0100c0e844040c07498009800900e201d400c0001d020086c03008010000d0360250b0245003480c11205a054000d4807403e50340f00c000c04903803040481004101134001d40c0c0000d08031441030300c0380c1c920f004200103151502d030140380310300d200110012861078103005115810300c1c00040c01040c581440c0c82d0500c40258044c03841030080149c1c00305690f503244100041d0500414142d0300240e1103180a05020007101c607015400c2c4c1c031825584130b003048282ca900e11800500703c400c00645460380d03200001030316580320351143c9944503140781c0c5d5150108091798180205403806a0000c10503a96150305018000606403440c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 923348938 1250 923347688 923347721
    0x20601180906050703020301050f04060807062a051f050c041a1c2007020d060506120d1e05070201090506180406080c0909371202060a0609 61
    0x14403215610841054460815440020310381c41c0c6a15207500b10764040d58030600103031b0000010082c40c500041c8558501004403030400101e8034041c03081c1d903600348510454080c010203070420b40e0300c1c080000302c503403d1840030f003c042c8103212a4a4901d86840ca0031701100080c0c80004000c0b07071058107610846100d010b02420041ca050304000300e4074010480c5c2d0b1003110000a00b08604002c401007500002c4090a6516000c04c0e0f503500e00100102d40001c507002d8071500d8130300b804003202585e5540000c0d14900d4000b00000707041c2e21088045610344a440441c0100c40c0300d8000900c84280c0d10640b418101340c5000c02010708a4405e9804461910800d24080d0000c0d80d00d00050000d40740000003441d00e00c100504c082014142100440c09030703a060fa10040d865042512013140d1402d1040c1e080f0750121000f0080c02d11a072080c80000390101d0443d45514926400c64140c032580e41d4008034108006801030660584d03940300c824001c1d50750200700c5401c0107841c1041d070001902c01c064041d1701c1d00021140071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 923350188 1250 923348938 923348941
    0x8150705031e0a06320102030c19140604200a03020f040507050c0d0201060f1e0b0904110c0d031505150c10110a1b1707020d051e0606100206 62
    0x200c040388501820580080366922000100100e4070000600130804001c0c1191070100785d902c0c4e03800e000d0500d00805041d0340080000210040f07000c03420b82050f24004010340044185801c00965100c503505041d407139032140310280f0090248005120140d04209010552114a00c4007030111648017840300035005101550003002074542a001194050190328005040c100200042d902e01441840300c600980d544d90b1080c040c000c110064400030748503400203410154210031031540310031a1846250441c40011a80250310399031a0800044c03101c4c103540703081e100c0351540d030348030b44171052110800042450f1446040080008c0e1001004a0350700070914600c0312865041c002459104039620410350040c05100600655507109505141151201040e03c0d4107416001614420003842c10758800040107880b6000200c0606070107042100b080d6441c0e4881c33401d44089001c04110b90f40040842c09030080018403803000280c41c00b01c1401e018200c81140e26180306200001c1d40201a40c1c005800110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 923351438 1250 923350188 923350231
    0x30305041211040510031a010503210c010606170f0f06210708011b0c080a110a0b0f07090909230a0f060219110a030f12060815070503 59
    0x2207814149500550118403020104400181211400c6450884000b00100c0c20300501420034042c00c000c0010316001000c3d54140740000780c0e40c441800c90b242c03405402d020ba1500e449030a078281d50426902d90024000241c42d00b80c0076010010100d8400e5283d43c6000c00120740c0020840e0260045803501d201d040e0584801d414403511002d60070703c00c0880c49011b010700c0c03c14081045810010320f0130000000d6a403000c0110102d20300b1500c1030349070420245600b520007154041048030405845400c104018280c0c0201c4036003024540200034250074080400c200310102134001842c0704521960f00c43e001e440c0c0341c81103101120f00c103441c054181e003d003c0e50310a14a00c0801074000c0e9410300d02c1140c1003a0055a03511110080c12202100c00c1d42e00070488901c241080c0f561030030341c0129414928500c210b5010543c0e520350391004007408010b26031041c6409140a84c10386d00ca21001c4000c140455500c070020941d030340c04102a21716000300c540380024101031051090b41c1c0682210710702c0c410315036400c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 923352688 1250 923351438 923351459
    0x30c19030516081618170c09130503040501030911090a06060915120225030203091008190c14070606030b0c070b07030b041514101e110114010e04170403030504 70
    0x940004603000310103400310752451100500d0500081078001040c07407100120a00c0320230701c0040c28407607100307001000f40d41c00540c000c41a46c0a6580038a4001485150341c1040f4400d110405000360300005058180032100d101504420203076074460301c603034690554602c1240c03030700c00d007808600300000d00c580341d950f07070221094005000e424a40428290101903601d0100290a051041203015a10006005c51582021542c2c00485150790500145074541041c1003010001c9100700352400c0c0b50340708100c5001034040c8260710b540c00c500c7c6e290b181c0c407940146131400c01001e080c00151000499070300007a004940703050132106481e900512a030525107400c0d609401400401070602c1d4010780ba00c00d0f126040c0b40e03280d09400100410021032024040c40c0c070501440b0f2001c40c0408003006100c405482d00c40c0d88503040368400e41d4080c6400f98584020003001401482809002c40c4040c04601c000500c0c0600c168030740b4061030044c0d15001600a06800074090b034403951200401240b401e00c010040f1041d41c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 923353938 1250 923352688 923352707
    0x60403031803020603190b0612040602030928032a03180b030f0f0a11090f011704031106011706040b041b080d02010b04140606030c190305160816 64
    0x9003503601078140d4903a400078005070030440d0002e907041e041c00c1d000c00c660f20990045900c2080203983c4a0b140102101c03090118002c010009890b054000012034034070380d0200001c40001d042c4038012421500c1e4a070304060121a01c8030700f5400515500004040d41c41d043c420408100c6e542d880211103074502d550300b5200b89500040030340c1084030000b0009601d0351102c0c0114412062108000b4041c03410840c0c5030411200542582061498403920601c015101800ca07040301408035202c2c0142144a00100d85003504401c1e04811505810180402c01d50058884a0802d04038001c0d60910b0380c8810040083ca000181600e003180c0c00039010802003800fa1510503040740c007592000591040284c0480c5956070346038045003155100551840c00154280710b0310303521107021a407d100c02d5030703144508041c1ca000a000325208103800004101e000644008813410008100c11100a420442030040c0040008903002034503481c0718603444552503c606500352054141303440100082c00040811190341b0300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 923355188 1250 923353938 923353967
    0x30a1706031c023f030613020d02091302030915040c0603050a060510020d02070501140306040b0105090d0605010f0e160c05161e091b0e04090b090a12090506040303 72
    0x600e254820a80e00b644a41c0c13a10f030b1440c202040120118004c0d40203035104804204513207107401d2051000c0d541e620b40c6410350342100d00c000541c030b40e2000318900e002441290541c0e580004890644c400100b1b098024600c1004040141d40c0c8006107642000c0d102ca00840e001001d044440d5801e1060703501960102c0d4104034a0b00d00040c1103070703c0ea004240c104040105a4002d0ba00c0071000d83d0001e541002481d01034031081c0b034246201c00100d841443c1b1400094002e9110341c2c1c4078070846990b6407041040c4c5946040003440c440010000e420514002e060a002c3c4040144407440e01041c540c4004c44d005010300b05940003101a41c2540c40c04480d840550501140c07540600121140d20b1142c0020040c042c02000440408a454683e1000340034001540440c1c0401d0910369429054100c148140c1400d003036905240104445204c0010002c2080d99401423407540380c0001d100f41020005804a50b49106682420f5103904403141907401c800540302e03042d4480c2c000c11041c0002071141c2c012841150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 923356438 1250 923355188 923355193
    0x60d270305070620040308030406110a0f0813060617010509030a08060103150504020c010209040614010f0513030609062301230607060507080915090705010507050c040e030a1706031c02 81
    0x180e8150340581e4080e1b4401c0e1007051001c800d0109020300c82c4034942800000e03010b40e40ca04280104080c00038000030b43d244080c4100c0f00d001800c01100c0c480740b11611035114900b04440360721a07111244558121001048540c680030004803007407000021107241c0c407103c0c0c581412541d2038400440180c00501860101082110b5000440351905c0c0007414110034000009a21245040240300483c1e40e01c2d4031007003107160483e200514a0f42c002c00305080c0e030032161a05540e143c80090714003041c201283c2c80207041c1848d00346c00c9403d022a43d0b0100c00100601d448031000d5100f0107041221582d401c0c0204880308141c209510403c7c070b11000c040001003405040c090a00d1070790340b51081100c208440c01c43c08681c6400800c03941d41001c5c4040f0100c5030000309130101c2820403001703541d034030300080c024181403000008411050040030440f810180f18010070070301005054041013901d81d040f1050080c0030410047d54004d43d1801c02114510518000c0c00420004602c02c44a19010641d00034410650 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 923357688 1250 923356438 923356481
    0x60905090603010b180912040b0304080c0a05300309070b0d09051614060705030316050d0207030905090c0715240b0909010f32060d2703050706 63
    0x1a207881c0c105c0e070b4600802210011461500984080c1440e010f02c4480b410b0103070410052160018210a0300d412075005107480c0c0d11000742c41c1c8040d19100c4501c0303000c0d120703100d84017010009014501c200c003207849040144030009001403a024219000688080c0410f802c281d100340a105142e00107010b6038a05a580071441115640300c00e4109014401c2e00310a9018049003804074400d00c943c00546000e0580d0b919107800826207520741c40e400060030200540310500f203515805c0b849142910811015590119a10400b9103006007009100707129032030042810100040107001e0790016110320b9034021070f01c0b510100d002e040003002094690306250300c0040c2078518001c280040c65004d0f01400071034507074a81e15800d160400c8421031050f4811603240c40b03245814401555000250244504440880080e406001d0413140c21103903a0b0403015004070000c5000b04400e005900045000d01c00d040300140720404ca0740b110404000d4480001c0d02081e0100448400214580e126001202000e4001601c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 923358938 1250 923357688 923357711
    0x6080c12030f0705031b0a0218070c14010b0915182502030d0f060f06080a060801050903091c11120a060f0507030e0d0e100e0306010603141006090509060301 69
    0x2c80d000190191816440803a0700003404c6110600503110f9030100e170051032804d403a42d0009103956000d800d00294010b4100200b00d4880c013880d04160416071180d03910041782e00d40740685d402040e011604601c00c010384004500b207035262030840f00070390390090843d01c0c650720180300001e00d000b030207807040715003035038422640c600158421100e1410f6926903000d075603201c0c0b50640000c2079031003881c0b40c8c801c0a40303403510812041040303040000031200c403814414000d607507109041009002c658407820341c86d42400d0800c0410312010005103841c00048030080070014a54200c3c15001c2c1071924004d00d5440902e003600500e2400c2106103550070140300490b103040e4001d540700000d0740c4100c140581e0080e202d0060102c05a014012403e80058440040c68240c00610303000300310009500219014500b000301c818400c0748211080c50b4180e0014080f144207594420000f002004070720541c0111403407030800b0801c01d50421002108551080e40c0f0401d8607400c0c1803c0024401001e0034142d40340d07698917806140e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 923360188 1250 923358938 923358967
    0x3f1501031d1b0f19030308010b1602130b13270519080705100203040303050a140601081005040e07060f050c0c010509060c25060e090f09011409030706060906080c1203 73
    0x130441c501d10940681902c3c5141c060129001a0040385010342d0900c070304241c9401c83c0b0242440580c0494462130314018108200d002000120010b0f904a09147c0400c0383c40d200030b820140a595072042d50070040041c040030190800054200101290882c5c4c200f004601b2524505014403400307400100d10b041c0c0c0c540d0720316140541b500000f90f10b00c0d03000300802090541620615038000e040c004188074410401081039161600145814184103040f030104204c50002010726010f00300181007049130300001280a5070700c482d54414940040c0704003040540f154481d200343d901c3e04507800020150705500c00c0040d6030a400c0008080e800410610555403444001c00c9a080340d1964000780614204801500003e40365554003c1c006000e450000f42c4416142d000c900d6602803040c04020b10907448140006014029101a84c2a26101a41400b03440000800180880d91203010104811307a52a12800f060340c61a11581c00640c1049551002d1810702d005041180d070361480c1a0f915080c403284d50ae56 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 923361438 1250 923360188 923360209
    0xf020304150e10020706080c0702130f290405060103060317070807120509041a0d0b041b031506080c010507060c02121b0c0301023f1501031d1b0f 64
    0x50040e40501002c00006d50450021071300225035240c118505401750300414000000001c88042441e83c0d8407180c0c02c51040c1d50b1000e269000780310782c22018641814000710014400001130380c403c43c0303080d01040031b641c024420a01140c0c1d00035000700f203078092041c10840c02d070842c150a68040c60300f049100005000002d0303240c481b85071a01c6203034440200700284405c0b1034400b180002440b49028002480340c0e11003034108010303540b1800070a40d035a01d0345040707511a50f130010041064a42902c0100401609070302200e405640c4072810080e042d0f440340f0465852240314003450210350100f01d6500404c5850b0032810341d840160040f141c0105070290b0443c1540c0c000e140c09400a1481d094488190005110203c400c0c6400c600179820400c400030002d00021200d0081402c031400c0502c1010450000c0380b0381d0400c015540aa02c0c81031803d4040d000200003410031150000c0e25113250264500401c40d01e001880750488000c11441070391058400148180e00d00c641c0e880f003241c1000410f6a680c03144400f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 923362688 1250 923361438 923361469
    0x50d080c03070606242109020109051002010203010e0f01030c0b03070219082208070902090d05030a120c02031207110f0a05030408070602030c030f0d09141b010f020304150e 76
    0x103800805017402a001e80000c50a00741c00c01212036282584203244040c080c6c440c440d043d40009864610f0b00c01622002500d60285800c209400701100c03040703406501541c103c4404583e00003090703882246850004c20240401003000102a2050128094240180da8481301ea401101d4488001c02100d5800710003114048030322080008485220140b0041904984010403c6c410703401070a080d03605031211202d0158050a0ba404501e103200b03599201000d01d03980e84c11030141c03952014410401846200100c001c05256404c0c810310005052001040314010003121085aa6580b00c4c02012640148200c40303139240b51003508108803514034240180b8120500c1100250350712458181114240590b0f030740007005541040c000c0c001c61150100071504daa460700b100050b07440c02880ba41074000e10240074040c0900e03a812401d00540c0400207400e18403200c20103004a0b0400003080115444150704d50900c0053300148010004031204000d11445042182402074682921001096015060202c4c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 923363938 1250 923362688 923362709
    0xf041806090b0604051804020402120117070e06013c1d0916080c1c021b0607210908160c080307080304032f010213050a050d080c03070606 61
    0x70001d42501d44100c00b0181815100c49080c14582000104d4031001c158464809006800014003195180e03812103c1030206544254100e5840382e1031081805c0c40c0001d606140d106408001c514050301208540c81048140e445d4202c0303012402032080d402130914040c48542c0b43c079140d04038208031000000c44040d12140c0d101074504414a01d10320580c2008048103024041c00010301c2101060080c440e00035000c28205406942c0b15413407107009034860b260a018030700003d1180c44095020f107030028000b20000fa0722003c10420710398401c613182c1400b0385204000c03480d410f15403032009000c500300004e0b071602c0070000141034285031030740059503208003074828545002094035010402c0ca03803071902c040c1c08048000c50400700c0564075420305d4400078001905002d100410f031321444282400c0b4081d00d555a0540f424005104400d0301e01030742000790522074588032420301140300d003054060350045480084c0105801c1301a03840d08074456200d15030502c0c0d0741c0000c000100228500780141b900500c006003d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 923365188 1250 923363938 923363951
    0x10090609050d0b060609150f34142e140907051509060a090e15030a1e02030a120905220209062106013b0105161a090d05040b0f0418 58
    0x710604a8411880c84107003940d40c2c555804a00c03440f42c018408181d4008021920220400ac0341489e2002216409813203581d00001018116a00d40c08140b01554002082c017044000482804003002c08032010f500c03503031001004000600e80000d43c4003d0001c0422030910b0040c141c03012030511752051020b4000702e98100000c05c1517403030a0003031781da201c0f144100e00803000c0d2040000a0300d50304e48510140c200d82c40b040200b008001040c41a00c60b00d036004044030f044d900d9a1a16540c141c0c840024600401c0c400500000d00d414409207041500040700c0c0d80d007190104c00d840c02402500003800b05600320f2f100b88174403481c21030101019400704540000c09102c62030920001016044180403082c4c0082d01d0342c2005410b104c40b500383c404008040103030f1106a842c5100125180d0207160003544001112000381c1c410b02846020030b020500030449010310a80c0c400c0e00c0c155a807400c568010001034000c200800c5890a8034000c2e0108803e00c45105183c5542c410202000f118008228580c5995031075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 923366438 1250 923365188 923365207
    0xd0603080c010b0f0a0609180f0911041a150d0e0601030606150323180a08120c0403020a03080d02090a0b0a09060905060d02071110090609050d0b060609150f 69
    0xc3e5504d8582080300c0c407120356401c0c160020036081003031299882c030981e8041030ba03e80352015003160b44901c9040310108540c201505000718482d400103400c0b80240c0c60641c0703400004403c482c03007590300721000c0d040385840342c6c0300042c12882e54010503002c603200741d07100341c112910300f024002640214090040070130340d14242851540e95200303504403802494a400c1321003206101d2030a840203950a2030000410960b00c1168880e084450507616100600039003408004000140003e800b0141074440d00500e01d9680c244440c2c0d061003280000703540450050000c1000901070340040c0300020482001500b40100500400c207442c0d45c036000920042070110780c0d48002503100034501c0003485c8910b4542c829600d48000f0071400d119004a0803640c680004401e0300340b148000e4a03928011020303180c0950b15071070350b030020031a103018003070803000542001001030b40b4030304468110f00c86034100160040c40c0d01c41d00c0c00c0280c96030000c00100c3d08005c04442030700c2154040d030098940d80c1c840d80b840c2c81e550348604 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 923367688 1250 923366438 923366449
    0xa020601060806010905061e04060c11090906180c0910170601031e03030209130c090b19032c01020d0f09050304050603280617010e0c060d0603080c010b 67
    0x58100004000c155010003c00e40c0e4030490703e0701140d00c01e595581d42c450604070300c44505049800080c03410100010b001a0560384031070f038580c042d13000796100b40c00c00d4180003c014041d6070603038904200e64055404103408080103520520212407542c02c940b5481031801c04955203820845500d0101d820340c40003005100011084c03070039680b400380082d2001d581117035180b91111004594602c0000d003030702c0304182094040e038121441101d0050484854000f40b94404001c2c10b8030b00140e4001406024001514400000a0f00c40400c0c44140e4203002c0c840700301d001c4005205000240b541e41c4e03d80350f81042c0110a114840080c0b002442c00540c0e51410710405005031030031a4030307040c00c05140040840100d00302106030360a442c01290700e90303569100c20032441e0780d242035542c0c04070366071490819039044c2800f25401030040300e0f1403a055001a1401f411180c1c00c0701e1407502ca2030a243c00c2101e51500340d01d408030040c604000c00c80000100e81d0b03125254540690400140d51b40036a55a515005107032800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 923368938 1250 923367688 923367691
    0xe1015020c09070807120507020304080102030408130b031003060209011e03090b06030a0206041401050405150c01060504110306040b13020c010b310e010204170105040b0619060e0d0203120a0206 85
    0x481c102070300300303007450303080101410100d041a00850b90b40b20b002c150300d22720a1040307d0041140354001d40d02c030b003805e09012405901000d54003100602d2040b001520b4000a029039100b18040c40444841740c0c0303585c4600e0041d52210318001d04219100c400c003100c0889100003440c13001d01a0794000746052040ca4800da001c0005840c5c14400e03404039040400590b6080e00716404d1711548029180f10740203075001a51300780100c0e00460383c0900d60010031384d04c0741d03804809070041081a1300203000440da03070030500c01100c0760b244007890303202c00400000c2c40508298101064818000d00721911842032000000c080340c004059580940e5120a018907c03494411250182d40c008200b605040e0804c0f21080c9084000e07480e0075905aa80b580711300f440d000030a40c1510700034003550510381c10142014001500920b012107088038004030b65000714055040c903901c3d1000c554901d4a41c454614286075040c0c0704002c18034161a84001c9040031130005031004d002d60351803880310549080c1ca82d804428060b0502e00c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 923370188 1250 923368938 923368951
    0x30c0c010f0f05060f01030b0303090f0409050f0607020c0a050a091503062306060a0c0308040317010f06030e010e070605090418032613240c020c0f0d05070e1015020c09 74
    0x282302ca40da48a40d008000c40c1c02e0f10f40c045884800c903c0e80c0703001140103444034540180150040e00c154601020021851a22030095542034401003d144820014044440c0c01030581004040d0f205108040050b4808a01d0b510400b040c003030b003250340f0b070740e00403e0b201d134003040c140840203a8a400483c005480a420380200044603402d0030b2440f01e080052210342d1040015041082030408681854001c03030056500541c003500002c1e0700d44c1c4403c03021507114518410680081c0c0703002d1040c2d44000061080744810448030000d400c1ca85c4c80c101c0211580e411540000e0340c0161748200c0480901851941c1074003d40c8a5258800b9074007141d82c1c20040101c0c000ca1441100800c1c108110f00d0001259460140c2a803100c4035107a54014410303480e07003207900c0e00880c07003040e8a407030712241119400141000c4c07042c8040b0b4501680074080010701101220f8081e0040580e0320001c0c05100610011441c25031244d0120b46800a182e4dc0d802c120403010460300030f40d005600031036403000701d82c1010290b01f940100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 923371438 1250 923370188 923370191
    0x151005120604021503191a0108090d36080a02010314040c12030e060a0806091311041d070609030303150e04020405060f042c12030c0c010f0f05060f0103 67
    0x42e00b80c010400710004401c0c0040c02c03050000019408190502c01c1084080350100108112188490945242021150840e010030310520005028200c00502410042800c0d914081c12403804141400d004c2d5114001c284900c102d900340621500f02c0d189041c0083c8855002404440d5050001504842c04460407604074110300c0200004207080c0038500c2c0c01c840c101d412440b050441c504048400120316560320340c0c030110004244c80c4080e801605e10340501c00032500944a5255034264040070010550020080c00402150b03132031900e815800714104025407090f0600b424040200d043c100780040e002003000c034010b0300301403051603410704ca4000c104244100e034030255424618500071811000704000c0c81103460304000b0b4801d4035000d402802e088000f400600c82c0815007481c8481c288480307045007860407106c0c9c980760012000003442d0303042e4014000c0310f503145407504e1507503882c1c0307038005441c1040d10340d02c0e803089a8a80a5901c80c2c06401c82d036400d0002801d092049c00c0000c0290050081410076 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 923372688 1250 923371438 923371441
    0x715060603020405150304050c040207050606030c09070c032708030301140d0209270102030a0905060f0601080103290a0e0d0c02060f13081e2407030903021510051206 73
    0x580300d6200c40100740d485d0392078080e1240d80d13600d8114507103141c00360002e80050000c13608908004000401e40c1c003465084003500e10031184807040c8400341008852140024120104500100f40164203071400b50080e2010085c0c90700040c6082d070541c16882e84886490fa00c00401003210078418900c2c0b000803203044505d4051910940c00044050001030410302200d441040d041d403981500030111200d01205c1e1009540313929010007600010413105400352028050f603000140a0450780e6144c0e80f15400c16162001241d003544c641d5070f0491128000940d60015110044400510030168540b013440c5945012a074144540742803820605054040170500401072140380c01a56100705031612007184056031512120220445d034800d09103944005064010385900080120010034840c540070841c2c030445000c0e04d9480d00f03080910303d2052444a44540030000718002e05d2080d008400918040e1048400300161000002d180c0101a13414585118180e607007004282040c1c184c02407400a1003000e820316 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 923373938 1250 923372688 923372699
    0xa051c14070b0a020904060801202d0c06010f1401110d080901061703070c050a06020303131a100f0f05030304210f0602090f0d0f0213060b07150606030204 68
    0x180c094004010602402c2c10001202030180b0b50594040d018024024400c04d0303587c8600f14001c100305154050415490090140b95507103210466040055032042c0c1c0d41c1c0c0f80540d0003a0480221100007914240a0810001010f44c000700b0803079000c2e20403440c1e203c1c0d880c1c3c6010036440e85642d035218aa41442020361100301c0c0d005010905030018200c0c2c0c146240c50b079444036000e13401400150008112a00040740e03004441400101034140280b0131028003d8050f151010001c3d008400d11030382005030310804c009000940c404043c0041240310f4500c25042244400c100c0d5102801240d445254138a018010090042489844801000700f0b00444426504181c0401e03100e200d40c1c002c14000c1d0100c0d0030701104034142451710f26481a04103100000714100c070700d4080083e60208540d54807681442041015501e007507010004c2d6250303c1004c01045180ba6400d002200059405401d1940c0c0d03107800008201c60844020460148144080c10284107440f80010850307115800204c201841800140704 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 923375188 1250 923373938 923373977
    0x80603030a080c19090e090a02060a03090c050916021203010503070b0318030301081b0109051c170406020102071506032406080d1e0c0c09020a0c02030a051c 69
    0x324078050380303428102a80d03004505603051140c811401c2d1040000300f0502c410036444440e042c141c0762450142d40c1c098940602640d030301e4a0031007019500c0002040311000050081d400b100f070091264115504003595440024a1108220307066000e6149409104440030741c14805003004034041c3d500641154141400300f0340d141c2a42c05481d0f4220400808119000d180c5032549827a401248102e07030341e0390f84414200c0d07103525090180d42402580c44503160501d41c007035440c0d042590800b60084801c20766110300c14800302034840080d6034400304c0c00c180600842407040140050040c0d6000903039a400e6620f08140a10b0356005040c036034034a0314009200080321068403000d51070f8050f054030320b040000346146000b850542e1107000035116404030040c0454003c036140500d0799614040b00701d188000c1105840006070381000821160204005000d19030342c03036006d40316106983c60580041c2600e540401c0c500f00c80c1d100183c0d0b081d0300ca40b15442c4209680e11100c2001c0e200c40c900108200c0b0f01414041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 923376438 1250 923375188 923375197
    0x1030b180c0d2c0d05070305160813030b100e06091305070e0405210c0705010f12140a0b010519030b010c0206030f07080105030f03120a09150204090c08060303 70
    0x41c05020001448010740940f9007112500140b01d103400b5660b04081822501d10407060403a0803040c0c064001407602550060701941d802d503805445032881c161301010700420042501c0c50898520308144000d091603000922000061807007205400f4140c105443c184e440c400c059442003100d503c00004110345511403e2803250090b524520740e2140c2050b51808a0800c0c03a10340143d8500d41c01e610402c028060001166060501d91001600980126900c0781c0301510403241c9d500c0c1654045030b030030171070355200349001c07440f20700c1c40d2814030951114400041c1c2603d0105030042c1425040e034090040c901281d00c500a1080402d080c46480c091102d44141c1c6403402109080050564840314030105074000e4010409981c3c1c002d02030b0390f5038682004070141304481640e0280015035802d00109243c2070000e004403580340c00318021801c05a0400c81407085c20382c01840c0f80b030000d486074200000104951401740c90450184005601d032820080194101c034406480d1000b0000100305004468802000700c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 923377688 1250 923376438 923376451
    0x5040824130f0f0317100311010302180f031018050c010306050d060e03160308040510060602100213052706010e010e0906041e0c08011205030322021c0201030b18 71
    0x1040f48030f814103042c0c4607007500c6030b800483c40d550101044141c5601440c4201542c0c070890b03001041041000044089001d0581028241491071040e40034914121348560201c1000a089a0460f48440d2000d001e488c258016843c00000302d18103101000000d124140c001c40c82840c0422015103800300180c8104051038000d00201e9452026000e548000e0044412400006a040380704d4289403070000c2040d0b0040f00e0503111405a10706002d1090443c2c0510302c12079500f580100450503c441c0144c0081d4041e14082d90b000d001c00200160a0b240c1800324144040c19085520701d09000d203455489140700148110b040244884168211340c2c3c100b4860b9070855000c4d101e1004c4c540c1c0e030030040307402001754010311100c085040341078800c00500c980011f1000c034100e60340e210540c1d80e2000843c65080c0b52550040c1180c00c03d00019100e540c0303140d4030828400b40122007003803500c41900403580e20004480341103040b603207544150042d560540900c03e41501e00340c1b1740c074481507039103078889008500182c5103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 923378938 1250 923377688 923377703
    0x140c031204050f0607051c1b0f031d0703021809030f0c210c0f0316080304032a0606060c12030b0d06060909020f031b090705040824130f 60
    0x11609100b01004280807a0181404654642c1007090001d0b05941051502c24a80c0301d558501a0f50011140580c4560b1100300380304008510140f00160f44504811300c01c00c08056580000160b0075620601044d540300010014014460440c01031110600100141003906c0d40682c0a01403600400003c8401c2180d80c0c40300a61950441d4400d9402d21600f4008260309002070070082d000d030300f030400041c40740e442d0f00e10446124214004145880b40903244190703207008006192000071a8101c1d00950b0b20074428901900001c0c40103105150f00a0032080380411000040d0030740c401c10200b032141c200038209a0030000c0750596980c0e5000340150029641c0d45c1010f03141d0000c002e55865034079008980070352200c000c0c01100d444e03014440041000a1090384901f114003d960442d050116400030304003441c1c411601500e2600051100590340586900704100c002c000024000a060041c01c00c200c181d13841004001e0801425403203103560180810400101c81d84203000081c03151a074170070072550312085 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 923380188 1250 923378938 923378941
    0x403020c1003060305152505040302090c0408070929030c040c0e0d0503180a030b0a090f1703060108010b0f04031112120c01110708041403010f1a01140c0312 69
    0x1d0440280c442648000c06921888103091a148100051907100d6180201000191000303240c071181c1801c0701c0e00594001c81d0b0200400c1c80541800e6a503c1c0c0d010301d032007510501e86a40e9040d01d91405080c0d6018460859072510404954560a801a000300d030b0f5411034036200c24a503000103034490b42d50140c1588107599441010900c207001d0700c1508810080103007070611f902da2909140d40c490744800e072180803241c2e4000c18a1910303d090340c02601602d4004e80540c030295681003000c001450b44a205840954551000c0c50002c1c0750792003620181504080ba00345c0324200394002621140042e084a44195024000610030408a00030b4500307c035004150035550401c0342000c0f03400714290201824441c0030300c130044103001e81641c0081410240950080080042c201c0c00e8a000d4090180020b14120b01003004101041001c2e071107031401c0000900010341108400444006c40300c205104560001038007d02d0b400540e0044802d40989a40305000d5280110402c102c5480380b00310302c005044001d1a60 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 923381294 1106 923380188 923380219
    0x71e03051c0c030f09150c050d0212030a02070204060f17070b0a090b0d0f050a1505030a0b070c05160b030f160c060c03140103080d0c080403020c 64
    0x35240002c1c4526980c086a010b030003180c1500802504201c0071503c0a070351507042e01d40d54603507150400d10b40c1080c9000c5007402d442c032004c10155085250b40d40b01c5507034150b080700da006010840040e0341301100e10004004181542102c031004292160200f145c15000c0d075944460140d05088500301503544444400a11078104c1070300001c0d40b02c000030402480382e64080c080d054900d00d00425104001e1800c0e000304c4408a600d020030759207454080344103914100c088000781034140d010307000681703107611241520000600860200940c5e0503407030003400000c0c000c1c03070350183d000e2180e1044c080d42e80000040702d40055034111060011704011502404240c44146d26503403081d03c0d400c0c00a05151a0040101403007407401c0b0606485d14441c000401c14000e1031400b07188a0304616856031280c041403030444580c00e142009101c032a4041c000030a800007080082803504841c00101c0c0e10564 = true := by decide +kernel

theorem cover : BRFrame.Cov 923201438 923381294 := by
  have h0 := BRFrame.cov_init 923201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 923201438 ≤ n) (h2 : n < 923381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
