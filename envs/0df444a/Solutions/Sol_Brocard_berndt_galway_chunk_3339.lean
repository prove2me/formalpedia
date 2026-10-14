-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3339
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:22:15.166814+00:00
-- url     : https://prove2.me/submissions/7bc74de7-9af0-49a6-9bbb-8a9ac176b6a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 600359712 ≤ n < 600539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 600360962 1250 600359712 600359719
    0xc010b012a02011103090a0303031a0f01200c060706020d0e070b0f07081911150115080613020a03020a0207450c030b030609060705040b07031709010203040c0f05 71
    0x24441c041d001190a1040c1c00c44c554014030080100c03900e039079903000395030009511950380032601e01d0068070801550005a0842802090f000305801452b03a0402442c55000d545000307070311070485444040c00d00d080000400c880e00f1020010748401030203840e030002d290803081010180305651010f12040e07512402c510031820390703070000d200780000440014018014103001300c5132241807101c00c01101c000c00000c00284804034000803601a00800c06014009010416580848442d031420190405006460900c201004003910000c3d003180c1d00c091014000700075004086407500e80c0d01801900940c020358008004d032007250000910411b030719650302400301440b60802280884031240750040708070319080854803025201c2c0402c4c2d0744124031030310040402554000c5181e02d689814141801c41c082c1407450b4a412060401203460b400408079411141d02c2d02500f503071000141000c48442c00101518003141ca20720b010f2020181e030540185000f140500700840707080d0399401c01e041c40c444e41445416003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 600362212 1250 600360962 600361037
    0x210f140a1b020d1d0402120405070905040209060f040e0d030e070506030411010806310501090213031407030b01140306091c1223241c0203030c030c010b01 68
    0x160b1034451038007903401c004900c89019507136244c5030001d001c1e42c0141d1613003800e04075010104000e200e0f0420800c0d0041c4207240e400c0146007060340101c1e0400c0e038010318250241c1d22104807201180c4440c0c0c0000364100000c0203680030750300e0b140001000352120340003000880c410591301041e20f141c0441101e000d203034428400c40c0c80d074042000652b01c0440c001c104960285801e401c05125100c001c0c0c036042c21403844488a4080b90219000004035401a040392201c184140329401594810790002001e40f9000748040e51450714650620740342492079017000341019616000082c1e4011071500304403501e07008405864266540c1c0d0310180d0b40d68101d07983d03a40d00c200380305095681e95000c4e002d00120350020210115406956244004000d4003c291008d040b101a904000c5a10030300211900041201c0c400d52404e00c8a0307400046d880444117100354040c5180c107800100715a420422a880300c50780e0307001c4e6a141c11450050a0080c001d070445280825850102000117402d0108181c21500f12440c00c01d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 600363462 1250 600362212 600362233
    0xc0a0b0418021c06150815040b0604050303120627010608092b030c03060b040b0d2406090603021c0c09030219051306030201210f140a1b02 61
    0x9144445501260100c90340c00c0080c2c80740f05070b09402e04411460035030000325030039240c89620038404455440e02c2c0100b04500c028010b442d521150712103e401c2c07003100e0101c1c0148042000a90074070aa17448264075100000780d40c2c0d81080a291041e1140400702c4040030a10543e800003411000e1070445080c00c40040c0c401400804e0050441c5a042082941103608030076071707055401c4044105400c404500d0110500620b1940d501d40507031080c0c5051490180505441c04c40e5a00d4a401240507d005542020441a01c0809158003a00c00c0b0218080240148012616a903d020005003d03800001d28907001c0443e4060080c002c0f0b41d03001c98000c00e1340b10f40c40c071009049002043d82c0a00c003000c0210540340000580d449035000c14851018110a9000034580010090300c008803071910f584050a0000420241c0e810441040369840f010485101c0099500150303030050404141e10012180341182c0d10245004483e001482000011001c0000b00c2e0b0f009044080300c0404806400140d00c07510445 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 600364712 1250 600363462 600363479
    0x5010806162d0c060b0307080c150f12040b0c190c020f040c05040603061d1b040e0f1e0f061507060609200c1b1807020c030c0a0b04 58
    0x4840c4552000046000240300140700203146050b07000c0000508000c0039a42806942d11a2003580c03501100240711461a00308040d8403100169041489000a080c0446402415008441c00c965000801a640d0030400b0072040305850191016584881c214001420360100d200841e01500d48540840548401c5098125041e068080c4c00301c1c0c1000282200068584171402145a50712180d1034080d119420114010300322040c1c5c3c1d0001111040c0144140a0286501074442c2c015140303910580302600b00e000c6034202849507601410846d00301004011642c0c0076a034885000d4503082040e0000c00c1043d08080e1000c01081c2d0f100394a5410150202c2c0c500d141a2210f1a00d11590700540c604040b03540e01c0c0d840c200c1d062980004806070b01e6501c0e8100482043c00c3c000c2e6420922403202d41080d00c008411030740c55840f113440c20070f00411901c2c8296240d980000d1138181a01d8500c030f031481c0c0d103442d0100a49400940700f170075001c0d218020314285545481d411000664058012503400c0901e441e406 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 600365962 1250 600364712 600364727
    0x10b03071413080a052b121d030c03030106080f0c0a0c030e1306080706020f1e030403150207061103070c0308060f030d09170c0108071206090510090501080616 70
    0x12040075000300000a6859014001040c4c2c00b4021070107000261306030701000704d42042c01c440d0354542c5041d40ba864200c868000107406058040c4034000154401c03039212804401000d00ca1441c128403000c240703000c0c8144000000d50680324031760f5075900c1540b00e5100d03840c1c00700001e60300c1d021074100a110528450380701e2006103a00314081d1a12030340d402840306c00f0030101420602450040e07a291001803004040401c0480f00410151001700706080c41101003544a010040a04a421261088200c80346004200340c5000c0e540240f00c0c8121000f110340003e00a500101c2c08039481814440d400d0842c000d01000c2d6441813407203072101c000000c082c5e54215800c120041c82264460b051815501d41d40d00c0070403843c0b441e0205c0b42c80c0c0c14001400c2010740000100441c549640d141c2c07255482d840c082c0d07448421290488801e062408080000c03800250140c1920f0f0080d0002518050070842c1000c2c009040e082280c901840411140e40c8035940c4548444044404a560181c1d83e2107a92459108011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 600367212 1250 600365962 600365977
    0x52407091e053d090509130201082508060f101b060e01020307080915070e0607022215080a0f0807021201020a0f030f0b100f11030c0f0105010b030714 66
    0x598501e580c0d000c40c0c1d94464030241220b42c090300c00f04000b0002100d50000e8203071010701400c5400c0b0400f854000700640c00042920002810810400085295095000340450020581082000600c840704034000c2480c0b5045820034820b038a4414004454280340d00340b00c1d100101ca903034000701c10300080141003e1a0340710008441e1581d5446110010300c4e000e05c065070140881c6d03594080c40c0c5c03d10509561801406805075034450b4185001d000950350400030010900006132821601d610366400040c2030b800f802c1111114420040680c403481054a0f40702405600605d00404506038079101c6641da6840740910040c0240c5c07400340780070f01140801c2c01402c0c20310702c002c0c142c0144003255958103003a80c004080107000710b000700b60318000303807901800b5030300d0000241401044035080c640c0000341c1a904418080c0c051084000c14200240d201e20381c0c05400f0603510080341c0c1d0301e80803240600d80d03600382c41100400c50b5190200128040d04091f0460380222240d130f4600400240c48201c0d08030750341c88401f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 600368462 1250 600367212 600367249
    0x1112041709030304030c0311060c1504021305130c23060c01090c0905041110050a0c080903010c020309030d080c04060e0625051002030105011704052407091e05 70
    0x8004002d980c10030040010310311907501000621f03e90301e0500b0300c180340c0d403a400e403160350300b404854201040051080550362002d28052107640741c900104030300030323542c1c00320000302c03820b21040100d0301031410b0182804520810382e10107000d64946050180440c0200d1201249210204107542c9181400217445513070a98000020b5030002ca50354000d00109650040001c1a191410441440410104803c0040d801d031110903802c401204001d126206031040341c018000d0300010030742409803e400f07586484101030000c100b0301444400181d0380b038000700c0c1000c2c032902c10410300121140c82002c69500807a04486401c1c03c00c0d00f040c20907121a502d08002d2a0006003d012503500e9070f44030b100804080c0c0034200e9864125205045c401d040a01c00c00e01100c0c46d03401040104040e0340c1c0150682c0d4549180c4140001c2c47d01c451900b142001c403005408021204420050343e00208100303074084c003031009034841c05116603466010740b940e01c034480c0380303808940b101c84800c00c000d04120280c814200b207a40f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 600369712 1250 600368462 600368467
    0x4020315190b0417060c090609090a0f05010b090910030b16020307050607050703030b0d240207120305060a091b080a1508010b041a090a09020d0b070c0611120417 71
    0x18081c50b40280c100b548007001940c0d9101c4180b41001050251580081c3d810700120b241c0640c0001054980c410f003841140280780003030024902414030f03808100c03402c56008090089582d9100c4400c01604550781c40351080116801240d528030103a00a6412030b0781c0407022842c1551100301c4004d0144c84000201c0a50100300000000642c040c02400c1c400c0d85940c0b195900e03406181401004c031080c00c24414010f421840340c0300c007c1490a4034800c42c8106811003c01c150351001c02c001c0203806098401408294803174901c054042c1c16400080c441c0b10182e0720521800c0da500030300030540b244803440311382030594813402070380c4288074107291544031501c0d0710041240320881e5903815554006e58002d45450350f440554182c18903041c056001d034440c0d000c0d1f5010f609071703102d8002550040064049442d160b61040040215101d800c1490031650b00140000703024504040043d00c0d00b00200780480d00645402151a03c0e050b509003619003c002c03600103400c3c0e42e0b84580d15420380e01052651600184010b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 600370962 1250 600369712 600369719
    0x705100e09040f02030a0b0403033804020a180b040e0f010b040b0a03020c0a1412040e010b09010207080a060209130608060412020c030d03200901120b0114070b0402030c0402031519 79
    0x147d95007a40502c1c86a500007500e01054100642407101c1007400d0b13403000c40c49060960745081c1c0c0280c10407000c0c40403030f00142c3d241074102040d98074540349048841500030a0000184c62080741016204a07180c041d80990595a06421031400740002d0060141520041c00b0074001c0c800240d0152107019000e0a0062030003441014803071820f00c2c4258200e80107003104103002c0c3c02c2d00003403220700140e12a203e80301d420181050309808011b44140248104840c0110b04000d99a00c2000000000c00482c01a101a002c00e402c001000c6d6100d841443d014000b44200f0032601c100d9440b540c412076410401400c1280c9550b0b03107011800894070951411481060030f040a1954184070031280030700c080d100019030010f4482a0b40030718036090210280d5000900040480c0c2c0d070001003040091040010015030a548080140e420b00c0c03000d900c0300100385000c1481c1c4d0411200000a50113103000300e08903400b0b2010705003048140e210403a441d109903020000c4142180c144110f0002d0003445500346480e24984 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 600372212 1250 600370962 600370973
    0x70206041202040f1a010e04020409061e0b031e0a0f0c1115040302120309030d0501140102060a0b0f060c070911041d0c030f13050a050705100e09040f02030a 69
    0x140c0100c110780007000c404104500d00b40c401e900c910104010188202d28014181c90000c00b02c605110307047c810707201d00300c0003155a158104c034058407a08000700142074030b900351292440114001f952802201240104000d5001026a440781c0003013030151004201c00d404030b07140482d0142c07a41d001d060b201c50421102e00c0041c001c5050482141d66103c041003e5503400382e00d05450441c5031610142180305000109602066040d40080c03c620743c03d5032911040007844c40c5201d5030004034800c61400001041c3c00204014202000000b603007105c54070307155010f181e01280d4080f50a5503000072031010061050510b040901489400d01099a884035076404240301034544044002000760400207040c00780c50320792203044c0040d4a00d6411803100303143c14113604182d440702400074000d00400341f00086034501241b2040032070a074090141d4203006402c2c80c005660b40240d004e5144110a24180000d0442c400e000440031180002c1c900c01e50398660303840ba4008184d1046081e40c00d402003441708400b140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 600373462 1250 600372212 600372217
    0xf0905060a0b041a0603070f02030c06010b0a080c03240301090f0812090f030a200f010905011803020304090c0311030f01030c0b070b0f0c09220501060302040e0a0f02070206 76
    0x702001c1c021a00d82500c40c208000c5074015040600f40b1103c815200480f922001d00b0f80f50f104542d82000107800b0705842c0281d01d140505d581a80440c81140004103044403907001500c0886101d8560a0803500c43c00070000860108549040326801e200140e0000c490310185074040c0c545020b800021141e4040e1a65980340741600002c5e01c001400103500101282044c0c0c501f540b108808003e0118845001d00740303500c81c81100c5c40041001403403a061000a0032401d040c2078041014000c942c071403540d541c5020b02900d60950700396003c0d4a407561600302101c41c00d500c0110381e40c2c1580514601810202c1c0031004012400340390041513622841c0d0010000380000450052003059044400d0390301d5403810114100c00d0782c01c219034035002800762100090100f44280c0c1c00011900c4195030650f00c2e0401c3c080c00e03014070b22100b40e024103d1400642c1b00c3c03c0780300300014010603820b420300203aa2141000d0b0168400c5104021454682c0700024802c4c0340a80c1c40300c46030140000015107000101d0b000662940c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 600374712 1250 600373462 600373471
    0x21f020304081b03070b0309120c0f06070f0906110f0d0c0506010603060b030f0612061305011a060307050a050903010603060509010f0b0a15030f06150f020a0809040f090506 76
    0x140c0c000602031150410421841a50f5411490900340340e000f2500402d44030340d0140b05a40c40090084080f40990f42c0c24400d20108500c1140d01c151a98140d4200380c0d551442440c062480340103950109207010f110b10f8040c0644852512070310001490004119042c0c68800c1d00b100e0217000301d00680c840c898080c022940d5860040c0d42d00c0711800e055050050130400180e004005043c40e1070350410100680500b565480700c0d40c803210801c00c0e510003011500000518007010700c03a000e510700304104110303e8922100382601a200800c80603241902d40110030020020241c3e1014041c00000d001902c0b540040c2004202403400f1810803a00001190960f1100e41003102c0e130540f14404c0014040d424410b0aa03106000c0400740501c0e4000c1c0c010403d41012030041458140b1203007224480c2500981142c1211050300d201001655a42c05054200748565507506000914250001d1302851000848604864000f81401e182007201c00401c0b008104040d5200520380c1c5900e00e403008558140a418800c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 600375962 1250 600374712 600374717
    0x8120408070b0a02040807060f05070c0f090b091905060d0b01090603110103090c0e07031107080d05061017061503040309181401090f0e030a030b01020606010c030c0f021f 75
    0x54507400d00d0010070784200181a406410300c1440704111019001504074100d405504000444100c840c0c0220350501c07c5503c094031000da1f0300300000e08100060152400c032600c048042004000d9801080038841054400c181001d07540c0b031410030031442070b80c00f00c2d0b0041ca0003803030031800b03c44540d0703082142b1500b41e01010105aa07079038100144007ca107003c0034140d0007440d0400c280b82644c6e50305031048255000311004461014001003085000ba80141c006141c940c40258440100c3d2503d080950f1040c8207006255081002085242c1010b5880382d10000a503100c81c0d0703038170f080d0034050030040d60700425413035102c0c81100400c2d12066400e4001c5024a00a50707502c180f9030700740015882c03400b24101c01c4042d80b518180340c646171050a908507906448880001040ca62078800300103002c3c1c40c811014860340c0c080061603017074139134140e4040c1184640070703002c0e14020340d2050019620307140070751005400300700d10107444800a0710b16000d02a1140c40100180b400c806e000360100704104460448801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 600377212 1250 600375962 600375967
    0x1b0a0b09010b03100603020108161407060b12120d02030c1b0c0108070206060105120a11040e1006090f0b1b0d1d0d0519030c15020a110c0303031308120408 68
    0x80b42e0806010382c180c2d841c00712000384100c620703560000f4180c010080128049248568840542a120391080300300c45038415401516000c180c2007107002403c06c000118480d000031510303803e0f4001c0206140d5100000b000c00e41d410228840c1008010f90310043c4215001d080411004420444002024509407036050041403040b00260015180110150900c81554008070400003140c0e0300404941306c2c0b0720240911001e0342c595116101c00b41151007807155107800e01080110300794007548400c1e841200210008040c071940d452007500d44a00324041d130308640c0b411610904c1656003050041c030910800000d0448415031040000e400c092026100c1c4c40050345040310750041120344103009015290032100320011f0801650340f55079800c000c1c2c140b4640c1c180a50b1120b001d040c01030251040c550780164400340d5605410340180000d50200034240c020070401e07884200181c20010b8080e005440250040d45551680b5a00d82c1406110503021110400100300d2104201c038065011030003648100385054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 600378462 1250 600377212 600377231
    0x5120301090b0901031718090a0903021c090b0304080d29180a20040602010501051c1203050a18080409180c05090c1218100905031b0a0b0901 62
    0x800e84420b40310b6280302e055144014404a03083c10b00600049280710141ea50718441a440b2405107401160400e6020240b0420020907240a07042414014465802d407a00308006003114442c0d984a6804400042d80c495424031040550b40019070b0010f004180c204d0038001b104000324103840d0b414070300e80c10340d81c070522415135a1550498240200b1804550b203041d40c00001c001d8004882008142c5d240c00368443d1603a402a1784124001e40c5003440711541256a103441d0f00019020b00001e204041c0074460f030252140c4000840b820b5210290b5100e101221403020b6200120041e11717019068141c1e45544a94100c000c11600d621070498501c140078081e100c070320b0110800111140e901400b03100c0800c110b115400140442548016a8021a000d2281f40c5528440e00207038000c407512080703030b07c0340002400b03a07001080c62501c000c000150220388c20722403442c8907030b8103884040d4070041c500c0e8002d02c21400311907040c2c82c0c1c036603503e207204003110502d07032136508c4090302e404e0252034000d01e503552461100e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 600379712 1250 600378462 600378479
    0xf090b031f05041a15070f0524010b070b070201060506070b011a0f030c0c0a0609141006060e01032307080717010f060c050a0b011e090c0507080c0a05120301 69
    0x8400805040340c0c20010030000d0100c84d4410041074840510400c0c501e0758901921a50340c0030b40390011781119031902d9000341440c0c09543d5403a1a0303480a00302c900303002c51181742d50910758080c0c142c40f1440002800c02407213030b41c4e109030890050403800540d5242e20b4045901c2d02d812024181690062001805a5160031292104102881c071095004002000b54505402003902101c1c0c22011080304107560b501c05440c0103040c20401513000b00f0080c10603805505000c640344141a100744040c058501240022044e001190000d00c20340c0080381c410822401c0c0d6600990007621844000c4401c00b82685918091644221084920301c002c240c000040c450510b40c070105d944002c221006641d4199414071034444812120b6103e200e0410268034190800c0003001e00080100c1540040c0050544d6114003000241d0040c03100485070100002e40009582c100a00800c0e000880544415180000d5a100e01c0c503607511200d5036101c240b1609130104005041041000c4a02400220303003500ca5050250b407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 600380962 1250 600379712 600379771
    0x200109051002010c1205040201200a08040b12070305091b0f04063c050d1b060503070f0806090714041d0105130c120e07050a0806070e01021c0f090b03 66
    0x400046500d1b0004000060360049641818001d891001c44003003001090003a1a10301410030041c20f12402150008000b1403900292804400c2c8100c0c441d4150390308101103040f50003c40d0500f81030307844005002ca400c50012003141c88040c000d00003140030300079180800d040d942c143d4000203062018148803a001041c4000d6007419191891059280356424929541c3c0441c05014151207003540c6441001005070384000070031089800c4c1c0d56041841e54442c1c0250040d042160014080b4201c5007006c85154401c05c2e40c54840c09c0c0003000c2a40e55242d0500855034060409461006203804110208810041c0700000b03004000c01d5950f24040d43c10281072004104803403c00c1d0030250300b0800030b141c0450300421700f0030819885050001e039205480c0d2600f4942051603000c079800c00c0b510070340450413100201d5083d00c0341c0c0b020345480210100328801242d480002c4e101465414091205000d00306106185065401025207050030140b07898150f03012080d030094a114940024a100605144410f11078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 600382212 1250 600380962 600380987
    0x120f010603110721110a060f05010504140c0a110604051c0f020c1e06070602370f050729010f05010210020702031005010314060a0504200109051002010c 67
    0x3000f803c1044603030391203400d04001e1480410b10301c410301c04407111912400d045003074000711800310340c00300c1404e080c4600100126aa0b1141150a00002050b00d0074140903803103014110228548050392000140a903680041c0f41800c104804000e04205000e000c001c00e40c0124040e401500c40e50001180541a02101c6070302201400425502c038481c640e000301c0c4414040c4415a00190b4200074080d0755442d15000d2200c16038440b40200d80301c42030060580c050120419604181c0040414281e0321609844e041d85c080100700d070104010000c10ba200b07c0391212032019500b402810039615a81c0c041140b2107240080c00742402035254803c54031900031445004040003850544468200320000303407941480b542d813880701a00040c044046440401c410402484455810046541c5924000d5005140c0340092405071041a000c81c0040b6070701e200c1c0303600490748003162401a160740c0030108403170400074414905004034440001940d03120741e18840720100b550b5000140d180129200541400358441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 600383462 1250 600382212 600382241
    0x10150206040804050f0102070b0d060923061903150f140f180f0f0109050d050a0509130e06010e0601030609060332031804060501050901170c120f010603 67
    0x244004503030b5201c00c640c2990030644001c8015041100140e1401c003070f81e4085004000009901440710006034004010f42e459108244400d01c55442301d000c03102c0c00004041c0f40c3c5d5800001007541071500810f8840603600d1541d012010542e603840d85a140d808404d50b41c01440c0d15086413001928140c070400200f02210204850541041d500c1a0340e0031000404070b4140044403100200d80ba07204002d01c00d0321044510803038851100c171000e494042c0440c0e04040360315204220345e81420768004c0040e125020071590300c041c20810a42d08002c203070024022101c044035503422444100c0340d4103000941c044e051600c00c00006003002000141103450540c0800c160714508141800041c60f514a20340c500c001d990082004030103000d440b0410000d06049820a43c070000071248001c0d0450132003140110030803201000501d580300015186445030002150014410441c00224002200d000b03d400c8056601d4040c10004508030000d1000c0d4140c45a400003035503c2c0c010003c80d541401911408021036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 600384712 1250 600383462 600383473
    0x70b0a02070f020103050c0d1b0807020d05120a0e0f161d010b0706060e15010f08190f0605040c0903050f010204230d0f24050105010f03020918101502 66
    0x42c0c40b401c2030400c40c07540082c10036498201152024540600340c448803c81007400308642945007041442d004e25080010001c11101c00c009540075001007042e004c0211991100c51a01c51081c80080c1207403402030410034019514100d584241e032040140300180c444a0000303164042d01406c3d04440c2c084182c1c010782c0c0d1a501d1300c0d09050f400c40240c5240b411102101c500d1502c4100516050300a00400e8103e00712014085040003000c14a60500006c8a603080c0c03103140c200008020201d07261207040b2100c108514010750005a440900d0317014584004290341d00041c110707104e50000c1c0035200300d0300409000500d20601401480300034000403051000b0350000310310b0a4030f0425408018000d0824600d00d0984001e285d00c1aa11911810003045078042a911400180c0749026912008118415401c03500061480e5414842c90720405050f01d20503182c920b09901c40b8403080b4069801440c3d2140c004002140e04800200c40c04482030013118050144840700d414149800e0805039800c69903000c65000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 600385962 1250 600384712 600384727
    0xb030114011404080d0309150c17060d032f0f010207050f0109030801030b0907090603080711101413240807030204030201050f0d140406051005030705031b0a08010207030203070b0a02 80
    0x17449640700d200c242408240490b0341e08210021b2481c500441d4405410602c2080c0780d9580012a0202184454202d02c0c0356105c0310240214110040c00040c0820090001c0413101e25101001440c5800d003140c10607000c441411641e03040c50b05d100300c000390b00c1c0c1d00401c9140400205011f4903059501c1c8034020440101b95841c010320448040c880641000c11403000300300662384c144800405044017110a200303065982c507218400d42e1000d02c003510801c3c007440c0d0203c41071819035021592001c2c550741c0d9030a0720001d400320031810380c030a50024503100c203400c1c400a0006441a448c04041022010b0009420031550f0080c0141c240100300800301403041209000503a00081540c1c83d0040c0c0000003611054200800c0d0000e0040d1a014a102d160301c03030030081009001d81102d481130f9000c1010340302c181d5442c0141076841801e8025168181c000d41e800321302c01248100209841d100c02840350a02e1a503445030182261300c225001e80c01604009842d005000700c0f0142950000d44001c01180f802c2c86 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 600387212 1250 600385962 600385979
    0x904240e0c18030f060f010611160311030c04050c090108180d03020a1116140612040b0907030c03031101050123090c0d1406130506010f0309020a0b030114011404 71
    0x50580d00d0034540d500c1d8001280d00b0f4808001c01c0114031090021940c603420a1103500000b68001d104480004907031400300903020802280c40e07010501c41618030b51005041d40d540e00d40c48101300c0d426503018442d03000b55095a0351503004d441d01941941c01c840380d5865105000412854004001c0000003c0c401c000c1d10b0347c079000081012440c550b9150041e11440f0403041250000e0030128150001d01c5102548621040f0300b020311002c8a160300072508000d840074081c411640074551048584101e81c01c0003c01045460045960001d0300005a4145648036070f120242d01c4c9940d0001e800156000754800c010510900c6000d015103103221040780c0140564050400700c03416020010b025a400c40045035142901d002503801e058500c4909202401c0703100f800b1211100c040300c801d0f124036400e01d21030900b14140d11440e4082c400c10380d01c854158040040590180c00300700c104036007141c1c111200050505200000d140030b08001c0b2390107611400d201000410207a81003048920701c1c0c0d410081000038a2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 600388462 1250 600387212 600387217
    0x140a060807051318020c070906050a121401020f0a020609010b06071202010b041a04110f0702060a090302040f0207051b0105221d07120501080a0303020c030904240e0c 73
    0x689481c070758454001c007200302002199441807584610240e00c28030440e600c5d8010b0310380c07221403a0407140c89964441042060b61300c540b2840d074222080c02c00c01d2061000400c1131240181c000d0180801d64000c0100c5203003240c0c0007003075120b00c014001c180c1e8504a035040c0255078002c18488028024001031000242e268410442c009007010b42817815031184034000e400010701200c005104100000e149030350680b05500c0c00c03008030302c118500503104281481c42d0041d15404240001c1081c1840a50703824070205500ca61803007000e00c86415000001650303240503010348291140409a210200c1b481c1c001d1809050042c83e03094070801d04042030f490b0346e01030140c900e402d081108062000103a5024890070304640c0d0401000030750603480d5140020300e1003504900421041c1c1d00d046040e201c1002c02000c45501b80682d50f5182c0051800c0b102092103074024140d00c0c040c103816245444400d0002900b01c1d404144504a45100d0b95071544400b0440b240480003000b0a5096617014500404c6190b22071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 600389712 1250 600388462 600388471
    0x2210c040501050a1707020d021e0a2303040914060d020f190f090e060603072409050409060501080c040c020601170309100e090105040b0d0b06010318030801140a0608 73
    0x108011800c4110740388034050052882150452403a061b05143e0f800a45603005030350002c1c05481078400d850f8440c8104400a4000322017180502826040d075552088945081c420f0f00d050070b2440c40c00da40400c24140010703c0141410440060b4002e80000b407009150300c028951762241d1001c821260142e105c56041c1c4070003103000c0780e41d00c9031045458141403400a550700314110070300c690f0f00e022803000100d030b01039032641c9000011500300303030345c0c560802d5aa4001401030041070050100409a0f90715100c000490f0702d95142465040983c0303c4001c6402c581031340038240c031a5038940d00100820b00c81846000403c100541d0140710204445070301a503145410300c50400715804410f4480a07004061090758028130005101c401501c440c92001070409100303124a034415031000000041e00d140c41c1c82940789010019000350802e102c16141c00440e8038001b08910705268a4041285c4460003c180d46000d480c0b0070346901c2e1b459414130316007544507440c1209503405000a208140440390300440070360742c0f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 600390962 1250 600389712 600389717
    0x108210a170a0e0111070209061c0f0c0905091506060f04031e050f031306020303130b0a0b0406090603061103090604080a0512010905180105071209030e0607030302210c040501 77
    0x40342c40700032840d0000c28001e15410450351800c1c41c90014622084000d00e000380c02140c2d40701c0c19482d001c0c1003119400311f801120501c4007040c4100b4001500940f003400d025030140718018150b664071001d00058680888951040d5041940f000c100f10700e15885050704940d068807150300300310b9407071209400c620030b40c0000342141c15801d94080f00070342030014000c0220f503c04103a80c0001a10700c4020f039a03030880080480c80444035500491520b2000054910410842c00850141c054a031918010228003802d80e1001545845032003030749881ea4050100148649480042c405d80746003804800c40d903050002c212600307010000d101812030b0000707100d9046030301b041e0126560041d0342815113403071003a84a01d03c026520b50000003403641071a0702080c41003000320121548256000c0b80d81c0e00301e0304111043c2011404925824008a07529070084103464841d0800b41440c041c9000024100d40060008500081e000115080d1402560824081031504042100201d00382402a071125003c3c034081c4504 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 600392212 1250 600390962 600391007
    0x81503120f040305030f210708040308070e0d0c320603060303070606081501060503042a0e0415110403080f18100c03021c02070b0a02150108210a 64
    0x511034204040350015135100e070850340c0d208013400d040b61031604030000000000c4008081c1e031801c14040c1c02a144280040e60720201156215907040d10030348000741c0300f00c04104c442842003501e03442c1c2c1e0099454490061407080c000358a031141e181180550481490b41492508801c0403083da00c1101d50340b0092012116152256210000b280c60340c000c3c4500581000d00b01480013800c50000302d104001d071801000c0c44c2d00140e0320b4032015070740c0d44001d850040c1500601c1c140320301e118000f201000310f094035291a070600c0581d15164440d110500b540c054503084a04041d440d40703820b0070300c1900140d4040b03a080e03908161031030b12892014040c00100c0f13040d8000005240c11500c0c10a02c2c0d00384a014010106542010341d8200105440f06a41d0210003600c20315086229102d490300c40300b10200f69941c000c0c070380310341041080000e54000800313500c1541f145407482c108040190b001c0c54043d082043c001c2a44075403012441110342014a0036881c0c0e1201000f00c1c040903a03018100d0b000e0400805900e10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 600393462 1250 600392212 600392227
    0x2060706110f030a020702030606040b01120c030f09051014040f0618020604060203120f19020c0f1e0c100e010c02130606050a0e03011b1206031205040608150312 71
    0x104248200b01074009031050000400405609541c042e008103030094007102d440b581da15050004039040304c0b02503808500c5d0315121000d502d44a41108015030500c0c42c02041d14455107140c4811f58070310f000119440d41098000d00949021445036420311804e00c0802c1e222403d09480b08080300c3c012110207880c00340c84170a0791042d400e6400021a50a03800f8210b41d070307603d5580308001d40303c2c0c1001c41c02040c2624200c000c10528400100a42c3c007500e8000d070402d4210542d00e10040c0250300042405100c4d024126607002c01503420700c01105d9021142510042c500e5820542500f06190038850078415450600908203c03640a00c01a420389000c1c01c3c010317060556400020410140c0c1602d486100341400d401040c1250320801600c0c2c42ca04985030f40004040c2d130f01c1003500780c800904280010309034107542c2c0312a09200c0d040c040c0c079880b020301c00003034603c0d284c0e165504080b56940f588004150009020824250f100310b00c0e075401000c2c82c003480b00d03c3c400400041c2d01c0f11054a8203400d50f12011a14a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 600394712 1250 600393462 600393491
    0xc0a03061a0720151303060207060b011103070309090c3b010314150105070f1a0609090a1202100203091b030d050406121103090c0a080a02060706 64
    0x1601425808811070340094991000d501e850344161021250041000c09204031600118144205000d004084100c416001c050350300e550b80109542540311000400f000020034801d200501005004a07400f142c90485040050100c01c19054507143d158020171540340400d90205580381502d0100001141d481405101181d81003001c6140c0100540b0501c0103070091040c1c81c50400d407409071526030300700c03010302c0200550444802926078a4185071040009042c00e1b00701c02d003a2406801414030904040d815158544e2110b0070b90070481c3d940000342407400b400028000e556522040c1103501d41094074202046580fa2201100d00074502c002060007074000b01d0090082c0e40024003030003011516480d08000c002e0759140c3c542c040c03440019200c9103404050902107030000b01c0d00010344942d45490318086040394044040803694805d0781c1d440e180070100c042400003c600401824009210034807582c420880302000513404a90b0641c002c1e1000001a01c2e10001e90303100076000b88000408a50b400c0e0031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 600395962 1250 600394712 600394721
    0x603060b0319061a130b0103050711031b0307080a0810050a0b07060e0c06161101030e0712051608032205030c0d0c080a030c12050f0306040c11060a020903010f02120c0a03 75
    0x40c1d80d40044d510040310840684c40e44006c1c0c040d0341c00d0b030f0f0a108039200c1e00016115802000c030004000e410802100c80382001e11601100040d4504c0304980c030f02551074489110344d811802d80c1d140081c4051050000381c10410080c14040c04040302e803c142241f811505041501c500840140f00300d0329002e900b041d520f0140401500309102502c002c3d900d0301c0080403d03c9242c104c1c1e0003200d141c0c90031035480855511238407490305880c64040c024540b0500741055400c98806a500c00c4501e031045200304049220050320074801401400000d64440f4000700f03002e20740039804185501400c000c60010000da80c1c0024101200c4401512100c1803903540d824010390b41181c0da0424078440c8115580314041582c0000344d00c2c8418012a0003034080b40050000f107859220301c1c1c3c021040314500b400410b500740b6040c2d00c2107252034114140602c2003d90303682030301e04001040310314904003940070605000c142404c0c099681c1c040383e00e0350214602040c04501e4082c03406e001e071802c1d070358500100b40441003901030b0f0312 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 600397212 1250 600395962 600396011
    0x9060c020f1c140a0b0103020d080d02130819030518040b090108030a08070905010e0108060103020705070602030a09080604020d0605101a180d0b16120f0603060b031906 74
    0x16400e00e004900c075181c1900503481d0801c0300c0c683c0c0000310384208001c0100f8800e00e1141d010051000c113074615002c20103603500c910301c01d890b144000c01c208100e20003136100030464801c10404000e0807518041031241011040307420301c2115000c031340e01400020b5011003102c10f2204141c1600c6000d034600008140140042c66100340c0211044002181828000010702481c04166644c40595038951400311030008283c03041e01e005c9280c0b00d81080d25580100300483d84254103140060800311192195171a040e4540e2003080940c00c00900444001d41c03103000c0c507001e4a02131004148604081d40421f21250744010040d120542c1c440210300c015000c0e20044009000c24103040103010f50002d08841240d001e081e40304419803d140e8030a099084c1580941d8410343c00852440745590b441058a0750b11204031002005c004403c00e841941045a100c0e0000c10342d64443d0004038103043d0f142400c112010b6405061080c0d0001d400c850f58800c40000181420740d0101001c41c40303640342018512403400340003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 600398462 1250 600397212 600397219
    0x3130b0c0903100e012d0f0f090b0405060a02040e1311030f03090108060d030c02010c110a080a06060806160e010e060a05030406050106091203051308031314010e0109060c020f 77
    0x3031440d01070455541041000700d0180b0001c114103a090032400c112224840405640c3c906c82052120082a85a00400030702c0403610000c1143e08002c03c0b08000c0390412001281d407003540e18203110500c45e040000c1e55020203405811803900e820306e42d01c440454002400100c009a207203c8407000c108550000030000d01d00a0b04556180501c588269140d0300064011030008810400042040c03808030600090305815440c0e140c0e10120640044904414a5a0075180f40000342d81e0f03110702da1102126103008000c40005480ba0341158507000d0162132103030740803603000c0d4401c1d0103002c00e003286c01030b410b110702116060041c000008080160b5444504076007240e407240020842c800d07031a81110007144240d105002c03c000070782c1c9400e016681c6400d203000e4040000800352622001034000ca00070203010184005100d055a0380b07294883c03465004500300c100441c0004000c000442d448900300d0490442420300040c80980b50340001c201d21854440c9104100801b00808195151500d0080007500b028 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 600399712 1250 600398462 600398473
    0x31e0522080624040b0f010e0a03151409070503060115020708010c0504260c0105071a04060e070e06030606090a1b11120f030414070e1906060503130b0c0903 69
    0x22503107030240044881000325059480f03110480a01c0e0600c22404202c40080022551004070740c01142d81c00040c00800703420056403070f0040082042685211003002c120240851004080d2003020580c42d006032000d0402c1d03006107818401c0c2d0350080345e15419602c0880321000030784480c1500306c1c900035490303001d0b070001c2d441c006846072150b40c050020000d880b8000002d41704242588290f8100b10b003000c908620603008402e90005c1e661240d1700809405002d0002d0074071007404000f9141ca00364003a281264420340e40c44182110305018890b550007030000c0c0e240500d480c549000842d03101d10340240750600c109050360014000c003842d540314071034041c2c9a080c5445038100c040c2d00585481d00440e52844a0300c14102c4e13003919005604101c65099800702c550342c0c00c40d100da5556035032800c0c61031042c4e131403800f51401c0810728034140000076114560409005a080040790054400c958640d0800f80800c0740400801c074090088804014005500a9080026954072040004240550100d460b41406503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 600400962 1250 600399712 600399721
    0x6050913020304110a240e04060305072903090c270f06190602071502031e120601050c0a030c050f0f0106080f010605100302070201020313030609031e05220806 70
    0x3024514005410344816501c546c562500d203408001507024158980d80100c505608503100b60b6038081d032503c01400c0401d146440e03070f41b55400c04406400008400943c52289402001c03061800d404041082d810b01d8914180368007100e0706e8540380085036000d40d064048140d02d0340c070b51600020100c5060104e085c451300b00241d030004060001c0d108244212a192081c880046081c03c01008031107040d00104490f51810040d030703003000c05090b80542540003d10000006c600b603400c2c030b1521400b5a00c126580d070048480d449040d0100a051141048810320071040d00302c20018860f4843c540500784180f0303c03540b0380741192400e041d40c0f100040c180500e0000792116070301504034009803000e81040d1511400f00019881c00c0351281e206041d807000300281c02c186e00301d001350b00070b02031340e801881a01d1130f200d89840c840f0b410310a580c2c0110b48541d80ea8000c0014564410804e0000d41c0c0a007030040400000d4000007407250003040c11818589410b0608150080c1045041d4001005982c06a6100340390 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 600402212 1250 600400962 600400973
    0x90b0d050a0515012304030501020c0303071404060509011d1224130326041a07030b09150109180608060108070e010e07050d14090d0504030c06050913020304 69
    0x50564401810390304110210348800c0011440c501c074200181c5d1140120400e6038006030350250800e0350340c90008410040400810802c2c0002d121000350700d0000d40c1c0d40d041c4000000c2041540310750b6410080400d02041c02401e07800401c440340da80c02403038246242100a0800c07203c0c42d51210b025a4441c107402c2c240c508032000030480203a04020352180812408810442e91019002200c0c0240180c0d0312038402000240136803506c000210b00160340002c9004640402480600159010ba6941c2080403100385400001100703d54400c40d00d140900041c414200810250080078082101b01d212212204015074800c00c2c801d401080315005014410340a01c465800400050044060780c1c02208008201c0100010b83d100440315415020300080e0720b48018062120b00c003a00180822200304030b19560b81050340220701c8021144504071150741400107a00c1c0c508079203100c9200501505000400101d29030304240c4084580c01d08000f036480305007000085085501c200300081036032012007807100f40304 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 600403462 1250 600402212 600402221
    0xe180106030c1e080c040203070c0605090a2001020703030e0d060603060f060b0a02030d0b011428031a04090f08071b0608060f1e041a030d1b080a090b0d 67
    0x6000ca40180c2c0c5409414101443d01401c40c040d62003981e01c056a6140141000e03402141d028245143c0201c601c40d16a8a010a8075015a02000740e903000c1f0888405200061700c0c6461a4400000120700c203d00120010391200c0d80b611029042c09000c0c250341096485000c00101040d50181041001c1030b16441c20f20014000421222162480c205002c103011800c84121603089180b034004508041400007144043c10201060504024030602d905e61480b44040141000c1c0c04624505c1c00d9031403661901110f140072000c0078000300f508041e59401c01c500466181c0207071460070380b000b00f1a41c4075400c0002e20f8003a15040184495000038030710043c0307c504d050f22202c0311081090390798502d680380b60444545500381c0716154400c0300081c2c03880c4146021710030301040d02850311380c0041d243c250100203400c4800203121a02101d03070750030300c580e0140f078140b00a0440c8905402c01040c400c00d20101400500d01c02c0c40c0003000c07440c2c0001d500005502400c2440c0c01071003400d024680d0f40c10711031191400780 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 600404712 1250 600403462 600403469
    0xd020d0609060609031a13080703050a0f0906050a030e0c060703021b03010b0906090709030206030a0603110a03081b010204090f0e15010e1302040b03030705160b0708040e180106030c 80
    0x1285003480102d0010701c1a004481165040100c548003c240b00c05500c1080e00081d00c00500c6c0c101c9a5500d1f00000c02c00000b40a41034020b895403922441c4603030000c0e103407120008402c02005100341e428000d05800500759140802c2515000906000c031102075403030a49030a8440350300c0f030800300e043c800301030f80020b00994a409256902c030000398600285401c0e9100c040103d0ba001901c0d40c00200a030422001c0c15500c0002403800c1c40840383e403900850110360054490340c54154a4030024024402c8003c28444d041c070045d0382e0200c08a141d500e40303400c10300030b1602210711000585800c404000094055801402c40390000300400504840108018001c01c001c40b00b59003c0c1c03a06510f80d010351810858101d51403205000d409548a41d007113403035240d2616080740c3c0165520098841ca884c03c0018200007445900108001155074042c140304030000d500110501408101c88000112000e068070700315071008401e00515241c2401c081110700c09000640c24546c41e1103c000280f044281c2c0c03140c01c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 600405962 1250 600404712 600404729
    0x31902030309090424110304080703031404081e030603060f1033031b051e030405030a0207081216150e1f02070b0c09040608160806060a06020c12030d020d06 69
    0xb03490740380d80c842c0140c8552400f148242c0700c041c1f0000d008035403050020040c2034130034a030004403071131138a283c0112003a0036101a1203480c808200f1810041c00a00101c260322404504a803c629280e070000f5a12000100120004552075011a0807000ea00b58000003404203010301181445107400c1c0c0c0301110b05c80f0b101031071080080100009100c1c2c003030321810001d000d42c0e004417008101d44010960746984000c80c1d015480360500e8100001e06044805503014a00c16005969034200300070000385000c800b50490203564005440502d916070182044400441510310084248022424603441c0e964002d50075051703140c200f21051821640101d50f076420704e00c207000e50103081c16482007000224081c41d0300040003404c681001c19a400031000c0503080a50780244040f4804d611065240d08224013000800c3c0461540c1c5002c3c44240b1081c0f248a0f8000004e8400c0c03080c032031414100075501c0e22440c840c680210030720311600800d51010300884805400300c1d0381c1555510300b891a030f03200504143c41503610 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 600407212 1250 600405962 600406013
    0xf05010501051e01080403020c150c07151d011e17070504050a1403070b12090c061e1c02040807060801050a14060c030712121503020319020303090904 66
    0x4203443e0540030351502d440d20700d03950561900d03058019140240c0c05402601940f050340b402156560720701102800281d44601a10380704c040c511212440c2c007400381c01007a50001d00305c00d070307850a542c00542e40880c000540c8030f04587c0b605180050f1a00030a94101030203c02c0d81642c2611095084106a2411103615810703074116030312000d08031080d00071401155072000e10f000d4100141503400900341c112440041c2076861080d03480f500f07040310764800303c1d91940e4100020100104518144441300d180311050321468070300b214864807814800740710543c1250a25010602003244180301c15045800504808215070391620b03802c2030769440c2421320418002446800c00403580d8100b00d900c0d0300884e1850031014518800c0c076420881d181e08041407101680c8024048000400d06050000840d502186c0301d1419030780d40001000c05860070414080035800b0861010001602c001401c10b00c0c1080032503841c100b05115100083c1944281e01240d6408244035041c0414019008149800d03a609075a0030721 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 600408462 1250 600407212 600407219
    0x102061b0c061e0708010302060a030903110d03050f0f10090207060213090e010e010b060712051c0b120f0606130b03060423070f0b0306010504180b0102010b030c030703060911030a0f05010501 84
    0x110305d08424007000b50413010a000094440b07009410188042d4032900303007840c00a1403010100d15100740b00c5038540009480c1c1d81400b80740074000c61000d030070500340032060600303207040e4100000f01e01c200d00c01c0f601d0b41980006c0d80c4051000c02d6050b42d120920440301180f1560b941c441c5807004e00b115151001c280e510f0403c4481c0c542505200e289000000540303a1420b108036604d071114420403860107001845810405000b074142c0c184005920100051400501d005155040c80346007004000c0d004c216902625428207400800640c19901131780440c0c50303403c010030085403007025140803034540d5010321801c82440100b04241c0c0072104502c0b900c103541b2544420500c060f981d00c600e01c0c0704400d60740741401014403020700e00d00000e6600800604107145069a11140360403240d411081e52000300381d0305e80c0804825030382030142d070b0b0007400e00714020310344841c000000903280d031076610008180c80e65a103d02820000a5924080f07030100050550724501890700780401c8003028441c046945518080010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 600409712 1250 600408462 600408467
    0x17010909110603072f010c0504050303190207080703050a0b06010e06030a0203220b04110603100e0901060b0f0301330305060d1704050406080303060102061b0c061e07 73
    0x115066411030304440c1102007400c10312031558400750511040144240c900e51101c072000c1c281e40101440004d0b00d80908101410680c01c440c2d200648200f0454204403c0015950000c182ca0000380c048001510041c951074060345000880c1c0c3c017038401409511340000a0000c04508000110302070000007106586090045600c5034000030f005500803018000b080060501e43e01450b4019034001403040d00d1281c4c03c006a803521654203048602c6020340d4100010007034085064140d60805488140c00c50611603900158416030b40141c0009540100001c0c500742000d4011400521102c00c110303aa511140b5480304e420350003406841030308042d01002c00d2000305c0d020000c42002854060564682000c4c00c0c0c12009400d000d80060340c071484d03200141010800d40c0c019800403a440c41c80c3e40c0d03551450701c010300080e547c06a1210381c990b04180104411640c010034a90381c0030703038204490622004d0031541c1024500a1502496013441000104003a03a17022162598022100415003486640c900008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 600410962 1250 600409712 600409721
    0xc04031a1003030c030c02090a09030e18150a1205061803070b060418050106090b153c03070504051201180303051b0706020703090812090d140d170109 66
    0xe00e0365203415401c00b000842d101d800d0346284c00c0e209140450803001d035500000c41040c01926011852a59a0425010990008500408802c007503c00100c16040c0c25802c561049008111900c10400c00341d080c43c1c10395070702149001038070b5a208000305600550410580e41c80301140c1e000d841d00c00c03c410000304060000280c400e0281d004002074038655811060201400d24100c003801c1d203408074082c64000410a02904004d00303411680003540c15087d41c10080c2508140e4402c94030326804101080100764180c0407040b00910035100c84221002d11140c40301d411154041c0e4510820010081c8003010380d0041c001e004071001203840d01152440340307034403d08840040c841e10325005003030128440001d0080d00038179445240c224461495089800303944181d980710715800c0b100d4a600051000030941c10103459006024024014080300305003615100261142d04040c41c1301d8105c3c089a1000c00c42d24a0316510f01036405015560240c251143c080e0407402850082c1109000410001ca142c40d0701e8800c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 600412212 1250 600410962 600410971
    0x1201200c030703050a120f140a09020f04050601020a0f05070e0a05010e270102130302150406020d0806040b0a060e03011103070207030809060c0304030f0b07082403070e0c04031a 78
    0x550302d410116942903940d0b41c8021007481c2400006210b041000c0c40c10710400d1152007603102c0101d40c1080c04c11210305001c40040c6240c000518249120001d070300d51603c1050300765416140000e26458000060346424140c2c0c0c001001021802c0c030610800c800850040212061052280244e8032055030035420340f80c0c240a400c82c00569800000d140e055000c5002030324250740036000910b002001c01c65400da0340180e20414403900c21201c1001142403100c060200c1c089a1403000b400c081c200100251070f50f62511501040000c0712021400075a280d601804054030000e10703401e9081e95950b809030044c1048005984654a0204111003c40401b005c0364414095640940101c504640d0f8a01c0b140d00889047c5410000c00d0000041c070650800041001d58005c103480c0c0c00ca0402890905c8980800409103410001d45100303000c0d0f142e5200190311150040d4804604580040d100441d00d0311142d6800700070940703c18018070444c5c0444000800c2a070380038200c01107144c5c1011050440c80103060380c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 600413462 1250 600412212 600412237
    0x603060207230114040219230f0f1804031803122c0d030c0b2701060602100b0d05120a090501090305150718030818030d0e1e120120 58
    0x8002800514086174501002e140d030340600c3ca051901c0b0b408561481090342080c540b24030680c0381c84900d600c0e2503981c1c04041101110ac440c1180e03179600101e000d01d82d44580c840c5100040c030f400301c3c0405006003600082107a1004101d1340d2950b90f814900c030740300e207445680c0780031407141c0c0104140c0640c2140d21500301840d008040f80d41c50040014024160710041c800e508000c110151280007800030300d01d10b03001c1c129803c2c02c40034809202140503400740b00c0e8a840c0354581e02d82a010060300350085810070400c60b44881c00945100c4c8140403c000e41d42441c80103007a030251808629a0304010805014018110b980b10022640c450005484541d401c0c040949603500c01060401e00900d00010194014642d00d0b25000d41040006419406580340e00704407441d081c0810703002d269401d59203004001ca40102c0061084800d042d1000c2c101307504117403d00d4011025080040f546520105028100001c007403d0b0149542c0c820a102e030080c10040200c010b81600a0880d840d0303018003200b03585c4440c030800d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 600414712 1250 600413462 600413501
    0x6020a030c050315121515010206131a040f02180708010504090b1611161508010e0a0905030c0d030608011104030203030f0c0718140901020c0c06030a06030602072301 73
    0x303010420000010045a00248151000600f80b46d0614882c41d0003604640d090350310a85141d400a42025001401c80d5012180c5620700d03c0440d05103a0f10140c1400042c00d41c82d001c0d200c2e030070103000070b00c80f0300c1020f50012600101e80c0d12001d07100200ca482030f1203507030340d008059880c0c00c104819101d68031005080d511924002c10085514015002e07030307514440c203090b50340d240319150003030030f0041c0074282d5103114424032000c204440400c40780c105644482d10b040d1451b0341c1014250078003520090300324070142d581d4083c0082040001c2040318401412041201c0e0b030700d0000c0304010081c02d850300908825508050518040f201541c0c00e88007900d9004000c0c504100c0307014050344081c1c11500001415100c0d0741800103a480f0f15403914000070b80805808525014002220f20101e1405040c00300103038410007200340c1c04d10010030039012880e000c403100303940c80e141c01d0400000703070480342c0000d008144001041010000ca0b038510703610030383c2c0070414100d10404290b1110300700ca66a00700300f000c20180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 600415962 1250 600414712 600414751
    0x2150c121501050d02091903051b0105070b0115121508011b020c19150c03030b01020601080601050103020f090a1721040b0d1e0f1a10050903120706020a030c0503 71
    0x1640142418000c043c1488054411f4010100502c0696078000e84907a0007031070602000380b80601c00301000c04000e00b031003407400c00720307642c2d6a898004c144121501c82400e60741c40d0302c1c1c2078440d94010140380c801c1d22040c00001040d0198090310b000070710485100d503213800030180d04412a41042420a41d413500a01504a28801800f00c5011a021403484140610380003050340c20162a10400c685000d13664540402c81c0351030084c0880c0c001703249040c10342d4083d40040140b411700042450548900f842c015840300514404641d6600654800e107500072140b01d00030a140e003440c54121090034058045548120b1410681020381c0c04001c134030710040d4010001480754200010007040b041082c402e000a8140489000310b41c40301d61140183c03d08d43c0c03118080d101c1301000d1b0282c0048d42c00c8190f010442d15010300009854880c0c00f441180500ca0080b0702d1a1655809000381c24101d000c44281c981ea0310003d1404800a501800c04840400e10b0441102c0d600c5101d401a03910540f0303100c4002400008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 600417212 1250 600415962 600415987
    0x4230603030c0f06040b132310090807050616090504150302061341010e030304180c05031302042403050f0d0503040c1502150c12150105 60
    0x100412a9415110402008030480020000028a8807518010b0f200d40d0405c1d25005d08010b9000d001c9458803804290b6030008a11601e103002001c9100c8203488072507000440c65182003d02c10010a03903280c0c0307043c50070300510921300000c00b4400e1103001500c0c02c1d680e4101440801ca4844144140060490501031016080175408052003456070b82c000c1c01d010350f50360300144042d40f0603203880b50484041c00b010005074041c003020402090303400000e40c1c5030040060201d01106404400118408240f800507038240c0d0296102902242014003038030ba4032910342c20485a1a48441c12031042a460242041c90281c812403c3e40e00408034000001001e1206801700001b03401000c0c0d8250b075005006905402030300c81c035143d010007944100040c203807406440441509000e4140301c0c480510908000700030010308034042210564108030010728400000800c200c4c80c005680060f240101810310910a442c40d51001402200503200d040d515607a480e500b6140340d00340000040c0340172581c1408207450340719 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 600418462 1250 600417212 600417281
    0x20a0f020307091a040b010206010612021305060712080108060712020a0e103504081803011109031905061b0d06090e100b060306040f0b0d060605030c04 67
    0x500003001c98400d243c80d011002c1c01c480c40e504040628180f0184200315609084c05000340803203090025140c6985040c038040c100d050160000c01400758005001c2000710070540e1818003401c4003421140d242c1d0407500c2e00007800d00d91800400007154080e0000241028002046481000785a40b8006c200b28860010000f03508101200c20500c103a4000d4492562903a581d500141102c0e81c3d00c01a00d480d103402200d1005c0b00d414a001f6a00070480341029200241841c035607009640551280d540d00c07462986018400c0700c0f009002d07410b500346151009134400c1400a0100350300c04404ad943e48408440c60314800c400c50640c000d210b0f40001002514180084d00c041340d400100403141c07440e100c40d412401040f00c0c0c035074000c0f9810f1642c9281c015446a4100302e81501b01501d4807040010180800c0003c0319404020705203403180d40c075040c0850414449070400300b03031941c001c1d01071011546185000d00142c100f50145074064407460408a410340b41ca8001e40b54100401140b040103621940e0b810341c00710 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 600419712 1250 600418462 600418493
    0x62c010e1504052119050301150f0203071a01031109090d051605150403090f080309040f062301030c1d040b0321040614040501051204031803260a020a 66
    0x6020301d10b0010030b44010440d00341102c4001425a44d0b6174070140c0d60b00580c1003c00d02891040100c14401442a60340300303a001074164442d4141103000b0382c0e140b00b04900c0e51103010001411410b403249040b40f03500c25800f086050b03901c540f1140e603d1079003940c00d1125007a4100e0700048a940410103003000c0a0003500204100700144490554000003902c905151030300d40b040d00041d071a415010401415070000510020f00310745180600390614008210f540c0703000d0072980f244641d0781c40f640301d10400d1083e4030032001800c6c20300d0b17110105040d0994000c2c4d2601c3d0041980d010078141071004000d9440760703084282c507418905020311240c0c843e0b400e000c002c214a03c251a0140326041205450103141070b042c281201201030040d580b5408e02c080181040e861481c2ca80c1030600500c014072150f070b049000c0d134000d00400360416481d030340c40c3e050131a11694001c01640f4010a00100030041c8018000c02c913600007454082c140902d9030017880d0040d28400d400e5400c2c0142c100050000010380100d9046441 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 600420962 1250 600419712 600419723
    0x70605091606110601050d0c09050a0f09030203070537020420040f05060301030201090e102c0c0309030405060d0e030d0507020c120c04020703030207062c010e1504 72
    0x3100141400c1049120700b41c220601090034900c3c20707454072908101843c00740c402520b0443e07280380300d0355440c0b103440f01900076840d0107900c901c0068070003030403513000200600468000f03100d94206030070080d40b01d50200030203940e10700401c0340701100b4141e0a500540210a01c3d0303019501f000f400749601a030610740400c00ca03806a02ea03003108501c0c0c0144e0310010020704503141c001e540e8070700e080c4000d01450120340c02280a00303814070040015030303001140c032022540c503400c1c1000c240d610102d00c0003841500750420300c401070b5501c4c4054911400850050b0002d42e06003990030641d1221010303110140003c031000300050303000b04410f0040c9c0c14000090b114510030502c0100e4440d00c13055006003160001b00780350b2140fa0389c1b0300030004503c0e41008006130a85058440650700480c1c8201503460b4001004654000c0d80c0000741076080612a0781229589904140c042028181c01000d200989070030142490819400340c482212541e0184186000c02625000610303144521480c00c2c0380d0201c004000b504c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 600422212 1250 600420962 600420973
    0x302070609300f0c0303060b070c0f060201090305033405030910020306060406180b1804110a0c0605190f0501061103040b04122904141b090c1306020318010e010507060509 75
    0x1001101923000e49603080c498140950424103160000180d03c1840d07010104681c1040407500120350080210707500101102c61508041c13406a886803240c0203009401d842c0c5820b9480000303400d56216014500815880041e5980001c504c5c141405a00003511840da000d45c080104000c040e0049495001032a8043e4030242c202d541d642d400c040641210511089034107001c006100c2614044c4191111054036071a402e06040d60fa0100602c1107941c0c4000a2010303549001042c3c00408842c042d1021200e15101070003152000c3c21407030081c203020701c94080402d0002c01034801507032001c410b0f0307810b891030180d0481c2003a203441c03c400002c400307944007a07481c10440f000c12008407880c6061200069031805840400f03040078a80002d0032601200c0a5406800020000c4120040c1c80102c0b055000304861100017612910b501c50064854684d51610b8070300c148000144154000c000382100e018905850742121004d0001500c2d50212003036400d00150701089400b00046e110b50000760402c40f0f1004407407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 600423462 1250 600422212 600422219
    0x50a0b090c060d15150201060503010f2a0905030d0c0b0606070302150a02070206121e09030406030b041121010f031a09010f020307050d150803040e070302070609300f0c030306 77
    0x107000d000581c007030301c0040c8d44424041c00784e410240a041d4440109800401c08807200001c1021800100c2006008002c03011441c041540c0c89a079564016000c001c0607106000c0e52441d014002685200e400c40f46403040400040c45450a40152049250140c01404005109540e03100f90302400500510321540e00f80310380801f40c1ca400001c2c045000c100136038507049040c0130504820901c6041240079100788803508003e02c007034011050b1000c9520a08000c94054524000140074164412a003400c82d44082060a80100341c072141004800c100e005a20440c0d8a401d10b040302020103000c0941707841c820a07840320f000c041c04052641c1c012400b00001441d5240003080d0420b036803040c1c61480014201051599000da081d2050094454100f0703a120400343c54450242e4a9000b03038429084103042c4a07000036010b0b80660100d4040d5644580c080020030158500407840048013001d0610b40c03003c640c10410a01801c801c80040116540c403a44429030541c2011111140582000c1f010581c6600000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 600424712 1250 600423462 600423479
    0x1109090c070f0f140d03091416050d050c04021615020f0a14130f060216150c0c0e010803070b0a1406090a020418021e0304080a0c0f0807050a0b090c060d15 68
    0x71744565086540206042c001814808032003030820030340701c480360040d00c1c8020780c010520b5002400c03520103a640c072a451107507040c483d09000c14004015001030001400c0240100e4040300d8980d01c0344240c5104011462500c2d10400f00d0117008540c5440d40c20400401010070b00401da00103078403070b148114500c2c20000300c040c07207050100742d44088128030701202e052100d00e805000702c002d00d9560329030081c0154034189142da09070241210b0f0000b4415284070304000d002c84e42c00640080e150004802d031195940300c0c4d40c56560b030f00c0b03a036080c0c0341140c80c040031601e21813040c0145407408050400c07107400c03515128100030302c4800c09490a03803000c0d0b0802c030000c1c69440c1001c0c2455562862840180c840540c0c9103020b50303441c114551141514010030400001401040903120f039045c0f98030701102e07048190729042c00c6600c0e50300400340c000d0384046400d800b045000103003050058032034845078031701d0b85807008102d90300c41c1440c0031143e006130140503030034004042d580040755506014900c98000350307840c400c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 600425962 1250 600424712 600424723
    0x70e1003062703021027080d02041d01061209120f03020c010903080906010803040b040b1309020408030304060e1b09090102071707030914010c02120c03011109090c070f0f14 76
    0x1240542c00c03420580e184c8491318480d00c9040d0490721108100c3e011b410481d041c0003004598001d00c40d44010a45400024407a81a20050003d180b90306140104410074140500c13024864400001d021644071501080300f40255041180d0095000c2ca0aa010b11000c1d10b01c64546541c0c0c204140c0d00344a6603110050034010300c031016001e9191844103007403603900035041c02c6058104252a5104010800503031800030125412150840401612014900300b46a250700181e40150b0b0300500104000c1030304a800310045000b03a00c102810480940106c28035500e4000040c00108555108030601c0b2050070001c1c007c0c8d5019001000041c0340c0740c0c172666120b01c60027029050401c64030003c114002016004201e0b10064201544450090913281000034180b29032031400070b018210040c1c040801700c100300814000b2a02c01802440160b4001088100c0394110f020300b640301c0e02003040801c0c0400b0141c02100c1d04160000040c01120002da1200c4520805a031022294020122503403164010309000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 600427212 1250 600425962 600426041
    0xd11040f0906060b13120f1704080c0111060115090801180201080c090913140609240405100914010f020d2a0f1202160302070e100306 59
    0x300040100141c140746088401c01d402440c3d00c0101002000030802c9019180000c4804040700b040b074402e024a03080d02e440040c410018454820f040e0024083c18205002c1c10a035010340d001c80d483c41e0359100045601c0040ea0400e40c1031034200300d00501162000e01c070b40c56280e21550904882c0c69640710021400c441040e20031028003002c181e03183d0110340e440851140c00c5540c0421841c02c008000c1c00080d4024005004020015170f5480c1120404c44104510b42c0d21007094001d40b0190715040c0b640c6030300d506044003200d10010301410075580300710150301030364051034015004100c40c140c0d0101030001060140b405482c411002c600040d070146003402090207440060745c0150303d81c1003140d804401d40e0f020640712181000c05100102c105840134260a0704413840c0d152247c0214100c0505580c03014500f011501080e0001490740701091b580c0018020700b505c80d90840322500d0391044844400007066031800d200d045441d0301003005c0344071034000b0711a440b54500904070f8044906020309964480c10b6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 600428462 1250 600427212 600427241
    0x30307050307120e011d01052505010e1002070b0c0d11040803070204060504060506191b21080f040807060f0609050603060c0408030a180e0702390d1104 67
    0x141d10303a0802c1e1310524081c0c03402800e007080b09070b10401401083c00c110300015014100308012139102e540303000d0810321669044800e10300e501244900c1c00c001d4043d0440880f46581d034490500001030f551614800c41e01c842d80c01c80b0401d171541d1100d51246504d548502454100c0540b00c5540c220340340d180e10000c6c40101080030045588519034070501082d647d096008611440c0741c0351081109481d144c0c01c03a88025455860320b003401c541c0da01c059460000e0440132120b82d6500705081e000300a44000c903d000c0c50000603005010b400e0001d0215602003003103600405940310300e00030400089990b409401154071541e004a2144443d900c41811a1032a80c4034104150b128401c0c001582824481203030400103043d0900d142c02c0c1007034003031035480c032400c5586400c1004450442c421130020101030405004641f140041c40d003000385000350745802151024500c1d51071403442d00c401c1d0700c00355011906600700c03040728160700300201c0400885030340b280d4041c0c4411044085101d0340d40c0e51441095a04a0402c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 600429712 1250 600428462 600428483
    0x100c081b1507050f030403030f0f1820030703081b061003031b0305031807050406030303091203051e09010e0a050715020606090402040509120310140d020a090b030307050307 76
    0x40958100c074000c0c0408050107003c2001d80b99280c0f40f070f400c407907010b40c05050205a48804840c40001444000c0c110342e1294600300c1005540703071210b5483c940c42030196000541201c070b10501d684a01c1c030000003555041d40f01041c01c0000500c400d0140145040301214240851003440300d20f4202a401c07074819410008640052040581158401544a9800980302403c45003960040e0441c400503040030f444019592111901080030050300d0041c000c040c005010541d502e24004d4040c1190a2040300c682ca401c2e2a420420313071192103007a00c2901d05500845032003840c034071983c0d50a10b000d48091700e07554170b40c42d901410540420440c04801e120b90001c8c6080c3d8540f0040020144500c001d00301150052401d00c0744554800e180103810580445000030540c603181d00035850059003214104403540d0210402022084014060049801540501100d041c500080111080801c03000070362100b54000d0034070004602d648100100540a8202c0f0728000307854803494a180c020340c00407903506000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 600430962 1250 600429712 600429733
    0x7020405071b122006060645090f0c09010c0b070906110309060910030216150506040c12050a11041e08030a1d03070b040b03090f0309100c081b 63
    0x8200016041c0b98603012400613003904c1c000c2500c861015008600c24440810138003840f1045500d0590114040c0c0b14900200040e003012090300e2900c1091002c804c1080b00300140d031400d0a0310300d540300d17080048910310b45540e0264171038610f4218903405810081c0b2498038400140c01d00c0c4105004001ca0744902d24a030b03140500040c4a120082509402c6070001d12011401c0d4a5401c241ca0100c00200c0300585000d2101001310024056101c84024114800021038140b000d2a240c071464040d50a00030703c100e036201c105000a40384007a0460300001c50624804003211a56441a40c005484520200314810384940b400c045400c1600450301c139070380101030030700c10480b1041001d004060510141d0300b0700350b0104001d0145c40001c09117480c40c840c1c0c0d05c0b9040c00360340c0501c000700280c030180c000b031500e403030b220745030101301750001c84c1e5800e924400d00c01070701c0c2100000001d452174404010a20b0b00a0070b4030200407581600303050011960600305009030039001000a01c1c6090184140f8000d00d035102c070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 600432212 1250 600430962 600430967
    0x3030405010b061608030402030109050312010303020c031207020d111f030b041b18050405010914091605040c09080109060506091008060403140c1f060e0c07020405071b12 75
    0x16214024420074082000030401036110000034a4581c0005d05203460390744500101c1c4c00751000000040c88c0d400000740300448601c1d07120fa0715060764040c2c0d085402c1c1d52440b105241d07130b07204110f036a01c075621f03130901c101001840d201c0c0c09080c070507116400e1401c036100e0720b9001c640381c2c0a0f0348440414030035141812900b0300d0b6041c071901c08842d03400c49040c44400882d48100d2a20031182e0349010400c090791034003043d081a00c680880092501610030401c669481304d40340000d10003010010a640310139400b288807030000203400e109174046031b13285565081ca031204210080803225040c00900c86401c1c400184c40700280318034254180120800309292509608101d0300500003400a4240c0d02a5502400030220010301c50364001d9150406c140c1c6440003601c030b000c1c80c0c05188440d2805224180011990b00c641000440c0040b412020600c04e1540355074a81c007201c0c3d401c89110007003d4061141601528040e0803542c0c01091343c0c04d00d005a41218110034210100d5030a060b1101310b00c20103038001c42c56 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 600433462 1250 600432212 600432221
    0x303020c0d12140f01050f060c16030204050a1e020c0a060609020c0123040303020a170a060303020705010c02011d04060506040b070b0a09021e060912070e090a030c120c02120303040501 81
    0x5008504a443e180b8145004914045040c00703982c1c0641c50554043c18a6240d00044030a000110000c0710301041c02c8990071008200e050000320701441c200b03c08078524040c1401040c150f075200d004958805584200090001d42280320440d0316842402d400c14082a00352180c1400381400441c007681c1d500b50725001500b510700c41d4214903110418454030300070900d40040b20540082d458900980c0cac07070307060800c1107400078444081c141c440b128010503c213401501e980700404030f0784039809580107107a881b0019a203502030143c01a0209000c00b65852161461868210a18800a000040a6880c1c5020564035006a04403800034400050701d9014803039010030103070380003074000801e00007441294040368019005c08941002c100c55581ca1040c00ea503030b501526402100545081950a000700e0510350f500e00500c02da400c1010704002141f0800d40c00708105a20035010b465050700d48500307079141000323112928050410010782c041d01c940183c0e90301d00e440d404800318070025038032030030300b03040290864 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 600434712 1250 600433462 600433481
    0x620120f0d18050307030804050307300305010b07020d0c08121201080604150213081006050406080307121d0a0303080a1a032d010212070f0203030f0c070303020c0d12 73
    0xc0909000b45001520000031110201d606140155464a40345007203032450245840042540c031000005034001d424404950a02180e404817244000b070621078150112031081c0038006e0344030320401c00300c801340c2050348406d2016442030300111071050303071540414100b0402c050354200d1040000344640d41265021394250240100c940a805035060a030b441000801b840c0d440701c03071055008900c1c500c240c103c03040e2460003041110240c0b000c20315045c031040000e050354080d0078440c5107008030204100d0310005c01da4103810fa00c00320721300340c6200c0c0480c103691002100c81c400620040b0f45004020ba03441c0d814041e00214425261030000b070405400d9002542c03554000e1a400e0300000404800b540d40005501e170000003050b0308004000c43c280e400c4010f00111402c8122a5800003c2900c1c00e00b00408001c1d200354059900d10740610745050040b81c49120a83e01070700340754541004222000d0380c4600901c8400c1c800d0500610300720504a44904103558440b82030003186103004c0311540d04100c0d00510b134a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 600435962 1250 600434712 600434741
    0x1080706081503100f090606030303052d0408090d050a0524070207050f0616050c010806100806041a040509010606020d0e090a051803040905060117010620120f0d 71
    0x142e0390700000c01e03680c4689680204402d17841e0341c844501503c046d0b00000e180b41d04007405001081d04c03403d02801400707003550107540b83c9402c3c0c9084150000c0c80703040e20054410451540c4515151f0341c580c1034480d0030005a43e41e000c041c00b904600000c901b040400c1074544118007424500e442c08070301c00000240001d031881c0761000c0c1c00030000d0880e404a0088140c41040310503da280a0880c04640c01d805900e0490501c001c403800c0301024403e000034030f081841800d86e120140c981d0b0702e0003405002078a01039040042350701000442c01c149810b4000c03181000c014000c142c8611095000a02901d0050f102103030182d54441e400c0c46080d074180300c2000510032030709002d4105110301d03021454001004081401550b035480c042a40039090007021170000ca00341c0e044030344030340e102c011840003000d0a40d080f80c0400c200910f4020642d0340350903210304a030060f41b511000e01c0e030740176220382c6800c0b0b02c20700c17004007070080701311403480e00141030702412032042c1f01c240d42e0343caa03041c058501c006c885181100488 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 600437212 1250 600435962 600435991
    0x906160516091a4b10170703020d0f0e0706051306030510120503120f16030c0314010f050f09041e0609241805100e030408060108070608 60
    0x940004258030341400c0442500e80741803901804000c0103003a004291070105000b081540d000c128601c2c034900b064591288000b5070591a03402d13040042100c05186402c0100e00241071081c0c110100c90f0906a00c22542c0c200075140c62a50582c2c41c08584a0690b1441400e564080d41070b00d0520400c0210080e040301e0912514040040c480400303d825148910401c05031650b0014009000074903200c5c0003000f660b4401641c40490780350840c0c40c0c0d04074405d40c803400101e20380014005542042d200703025441079072001d808221407410881c060700407890b00405050301d03205a0b21080300034104c894007d1213030201c2d83e5036040c00e060800c01414541c0711600d110703240c0c04051201040c8024503401040e200100e22040110042c9801400ba00402c500508080b0f0350f1107401404101549001a01038081780381000741c00702000300a1900f00700c0032006080c903441080605200703046540165400c04866044078141540c42c0000c3c2d14243c0e00346c00c05052a04012401c100c02078000c01501d8010003864031094 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 600438462 1250 600437212 600437231
    0x1803130b120a1413030c02060706063b0408070b040c0f060e062d0c030a030501081f0c120e01020711010203070506070f140c06060a06090806060402090616051609 71
    0x449403c05098000043c04942c00101014010710f022440c01c0e0740684601d494600508100009010610072030b00c0144001c282c1c0614106d07080905444038401d800c800c00d0f641500c48114840c0c80300200200c031404010014440400e40048640c0c0c4540d100307800e50420f150818040c8030714840c0c1c0742e014200340302c8aa1000742e10780d038420098034042e040806420010003040040c01c20184051700002c4c056010004100442480100003000440c0032a1414442a6602d010103540e8403c881013060946845044030075000c0000c0d00310101d20384007442d02c6804400300c5147d01e4115104200705042c03a80d80010b11404000c00c02c03070340240e514400d002941c2800d44503124140c03038000050000c01000389003408640c10701d00950504e81802070000380d25403942450781a2982c1c03000c0a175072031449061251400a02284034440280582d80d4880160483d40c948030184000303900b14058807648000280b1616008425510f4295101405000241889145071100a140c021940c001c058203030708020820 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 600439712 1250 600438462 600438491
    0x1b0c09060501051809070e27010b04063e01091a060907030b01050f0c0a0b0f070e150705012c010501060804080918090a05120408061803130b120a 64
    0x340d54843d415100c14401da580c050040782da038080141099071040740408070601c001440082110001b462142800f07235640c1323880c4106210f000f50b00c80c00c40041d280200d111450801c400c680c1c039019201c00b501e00d10310500c2d803a9402c4503e040150b000d44980d500c50b2840f051000d03003041228001800c2003000c4c91410a0800b2620100e0020007850500da102c0c0c50504c11340e4030a1080300c904e0000d007a040354640c101000070b641c55501000c42525004030070400310b004029240c401e10b00601164480e0b050400041c01441031800b03034682e00000307010090003000302081081c010841d840802e1a8613000724074061514081e030000c03400e20492940c4c0742a005025590f0498010b941254101d620285c841940f640091002c14026243d603000700100402d2107005000000d140103401d118506030b410103c4202c0d81000140a40c0c0300d0724055511907000302d0800c0c13403001e101442c0d80e141c000950b441c05130036103d5440ca203070301c42c3d0088006510000c0c0541340921000780c05a0030007800e410138030442e049820407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 600440962 1250 600439712 600439747
    0x50d062d0f12030f0509180f09060f010614070b01080d02060c0405010c0312020706090b0115020c0315100f0f1404021614072c010509040b04121b0c0906050105 70
    0x14144880500c140c0011800b0351705032450200014a182c0d03803564980f4140200d04e9081e601494041d54050218201c4d000100343e86104401c0d2040c01e040a0303192100494007045a030200d1a0ac00c0820024074012488642105001c0d001c10740c0140340032500d42200925200e0300410280c1c03480401e00050009a80c41100c1d18003c9815107052100c0100c10b0003500000c0c4100f02c0d004200c58a0701100c0b008110707005100700d040340c02240f40840940c404003801c0e41c032060144003082e41500401d0b05510003000d000700a98004461841811010b03441e0a01414a4103075600303c80d03040725200908000780f025030b0229400c5400e01791425810318081d2625400c240c0704040c4020103600801d5501a840e032020001507006281e0f51041c07010b90420500404030b03188a1441c811044a0071500104150415110f25170065520034004102ca40c0d6503104e01602c846003400034010403e241c1182010501e22104140403c0d0050307800740051498026010101d480c964055414020300780030808503018156030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 600442212 1250 600440962 600440999
    0x90717010311060f07111903080301090903021903020c150711012d0305011805040b0c070c0f030b070201050a0b060409021617180406050907050d062d0f 67
    0x314000c03020b00314006040c0c0d004414800101e2200441ea01d000d0000d015003004404109461481c5003a9130703d5003000250540340805090203d040004100c80c25207030b0700001005019205840c40c242c240611800604007000c800d0b00180c0c880032203600c5130b10381281900b031403400e0404001c0c0341c8074441c1e5411a02030080c1440724140088a03014001c8005c59000b024a081038810312068111010500600200001e0064091020341a060110005094403901e400f640d00400c0d01200740c0d848408000b660f038003204044540c843c006078002945448002d181000d58843c03421030341207141280303000382124030042c21024000e08050800b1240d8a60804841c10354000036005a40c40582d400302050800303030050020420880c010800022981c0807010300400c481c0900c080703801c0f807041c0b020070069401c0340c0129075100a1a802160030b15002e040104001802900c01203603da82c0c84d403410413014021210069581d46415900c84d89450382c1c2c191202401040740084d0041d4100060040c2c031030103200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 600443462 1250 600442212 600442223
    0x203070c0509060d06020d0e0111070503070f1e060207030219021c020102011104060503011d0c0a0503250f180b09010f020304090c0504150804030e13020f0c0c0907170103 75
    0x14045441c031380b6090010708003650421030a5650b2820309680c24014600c680441426500e072005406110524a08039095141c11100950130608030351a0402d0b508045d940488030b600d00c0390311220b0002c2281886015440c040c0700010385580e403a0401034141285960080010080346100100583d90488074083d101c01100c01c0700ca181401e84010303030040200315140740a141010900103a9150b2141c01141a00c0f00c1100d81c00d81c001c00005511a400f4003507403800d1004000b8085c0841d1148500e018551140582d04d10044c0032401c0348011854808500c2d00c0f0f80011030310503480801503040000500c00d40110440c0048451404003003440c41c1c01150380c02d904200100103040c2070a0310800588001d00b2081104109130710810502405a50092150740484410020304982c4180038039032140c851601500d480814120000c200311100c40d110f181c40000c1396080c861014815041c1f009440800940c2c40105002100c020400285200060064042101c074030140064892540005070450b076100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 600444712 1250 600443462 600443479
    0x70605041d1b031308030907140a0e06010e13020c010b04150302030307080a0306080d080a150b07020d02040f1103040b010801060308070305180d050307121107210b0405060f01060203070c05 83
    0x10050030015450070540170300340303034070101c01d0214000e00810588222031240302c0340484050803909200040b0001d104903005622001d002030780369405032648121000d40141000c207100382c154414002c980140710381c121300d80e544d070141814504083c0b1172110303d0590380212400c0245542d0000e9070382e11405000400c454000711b4080b030028001c0c0c2216010305440001e0314010640c081c030051003030f14100c60102610342408009050700040403082e4040c2e032076882c0d946151110940a00540d407a02c50000c98001b0703521810850705042520540642e001c00100840d03807420305003000b10040340103030081c04907039241600802c0019100380071126800d134181000c0e500c4582c2081e21001c820f21010b1110f8004d40c0c4c452480d0b082110101c02401c00f40d02c903c0d1814520034015200304c803118140b00303004c020f0340c0c03058800748411840c1d2445891049603d5404141c0c05145c0e5681c15011103007501c04a41590141043c84500f0b0f0843d1006130140145200450510380300342ca48000703801c15407244a00800f001d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 600445962 1250 600444712 600444721
    0xa06120f0c0902040b07030e060901092601050a0b03071e0509150406090509060f040203071205011e0606020d03110313030c050a030509010207050f0d0b18070605041d1b03 75
    0xd4121001c01005540780854499a4401c014840c0d60303c24402100040c50440803280f46c0d140c0b20007520b0340410183e46940181e030070300748001040301241c0c0d404220040300b010f40041800003401024801d54180401092005411040c146424840d42046056212001d10561456650f5141d002140c0040b0b40e8400c1c03948464410401810000441036003050400401280e14403003904094010403400c0200d80199488411820706040c003960000d40c19042401d041002c04100d500040c0818002c500000342200360710315044040c01035200c08290360351561801c005080e01846145075150450038144000c100b00700c4500c205110040600c24900c019440c1e0005040c41a03c29000d0103922804a41e01d800c0d80341806061900034949181c018800c2d060b000c2071a0600848030710218401038182d0051264584d24540e900100030284042c14801040040b49203c00704803450040c255174440380d03a120f0800fa00d09a0394000507900206480c03100050003881d0781c0366518000710303402c01c0d1314130354582d00e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 600447212 1250 600445962 600445973
    0x11060c03100e0106030504142406040f14011505030925080d08041217060603310c0e01050609090903040906030803150103180308090c041a01080a06120f 67
    0x41c2e03044045003020003400403400a4050348440e0043e405542c1414041c0f0028900c1e0f640e40d001c0c0346480a100b0040000c82d04000e00c81400c5d541c01000052001c01c41820103103100c0c040b68406040480302c065142e0042042003503883c0d0340910850035140040c0765140c6104415500d5182c0c120110b020401c1c03600100c5101c9690442401400e401d4050b100c03980d520000041c4102025241a103001d011101c0c1c0707102581c01806e03041d81024810040014030364400d400c1103d00d0300000c2074407036401480c0c2e0142107050780884002c14440c0440085428948560a040c5c1000c1001d41010388041d0314880103101c15030710901a44c04c108412581314805645118440c0e00714019940b1540303450b41012000f00c2080280005140300341407039441c50060701e20440045056841c52400361030304004001155010a01c100c0045620100c018115240c4118060100342241c0041408285881d0381c0d1307884200c40d6a011a0050300400300303060901c10030f801d0440b580140e042d2124020540c02007103548004101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 600448462 1250 600447212 600447241
    0xb0708040b0112061e0f0e010b011202030a0b03030307120f0b06190908070f06080f06060304140a12050a020f0703121218111003020414060904020712021c11060c03 72
    0x48150340142c400310300c2001c20307001801074803480341d07001814226442154001485913000c1210144e42f040c2e485c00706401110025840988601c0c040c17600c03105079078403d4404100035802580a9070380e041a01450712489411544640704c0480e1003418440210344070f95580c015200c400411644490b0100d8091030103075842a6241d22000c0c003402a40350006214400d0703050320084030480d0719a00d4090740c440105a82d0210202d2359142d000c031003440407801041001103000c6401d41d0800032105002402c1e102c55860214240c2d200b8001080000c0701c1c1c0710395506110490031b0007083c8008101841c00c0d80e442d01c1c903070403800c046001080041f10b9280c2503c466608440403507e0400329480004405040421220b41c03445051806174024001401403148030b8422901180c051011010360352071003004000050740a8041254080d4091282d003001c00c1072940c03510b1420754103800074160003510418803103006080b0051a01400007240c0c1803138070000c01141e6168004000d07000181d03659200c480d00342140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 600449712 1250 600448462 600448481
    0x121e0a0e0309090702102717130902090a060509030606060306190b0a020f0d02210403060e0105060f0f01051207051306081b04080c011808190b0708040b011206 70
    0x35020f401d10076065008980400c802038092014880d24120001e807160105141c40346a0080d10f00d50014004142c58400c0402c03401024112185081c1215800e9a042d8000e0381000098603070005207014240340c01d603050002082d5500304142026a020002910b4100080001e4003c0310000700040c001e950701e0540500c3c0e1b0011024400a5607128030401c11250401c0c1f05035800361150080d13031409244000b0702074080340c003154010190011b1610700d0300850b400090100c1e041000a0001100158443c000c40c0c81c180b030900d00014580c6030030b0003040b41101d15940c6490180329410306007812a41e000003260310980080c61605111703180c0d00011203162250f0b0307400f043c11500c118800b0549507840005c1c90300400810b90341c082654540c070120b0510b0310443c42600c10661000b01c080f0f0095003d540211800b92094090000c6076565484460600003a040d90200340c02c1070204490801010035035964000210f0300e0b01c0151482c007903803114014281130150b80204403100040400b04503050300002080c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 600450962 1250 600449712 600449719
    0x10c020109021908060c0d1404060c0806010f050906070c350607090e060a08010f060905010e090604020607050109080a090311181807050a0b121e0a0e0309 68
    0x51414500090003000100070482c481c038181e40344002400c007029450320035100100c000c1c0c46a91903005000c072656009a421a6180742c5510103009020740c17003104980324901400c408a410802e0450042002a00800315414042c003010312003070f00c503401410342c0c0c080301003501c1c010341d2482d00d41045103500180d0b5100e10070420011104007000301c0d1080400d81c0c05030615412444481d07082c00d81e03540f104411281f15002a003098420041311040710282600040081d00c040080c9031101005401c0d54000354528038010b4581c0400c0000348114400c25005000742030700822203080048049445070130240c0003070302ca62000300340c0d0024040c080d8000c5e22419804503a0300d6890ae802c1c0b0018103030b041c051000355103101d07800d4203030042401c18400308450401e59445840c000c3e62002036524003283c06040005842c402d0b444040341d91385820302540040c00f00c44201c90307140c000034442c001a080c0b00400c0100401242034134061888803007064150007500c21007000c00c2000310180b00311300c2e60181089a990 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 600452212 1250 600450962 600450971
    0x6100e072d0908250603050c03060402031f090203070908061e190510090b010c11010f05040b120105090c0c030a030c03090203190516030209060d02030109170301140a0305030702010e0a050301 84
    0x15006160351403113072000c01d1000c12103189907100300039411280116080d24495070204001095403501d5401190302240607448400c65403403c1100042c1d50f100ca82003d00e03519400000d010340343e078000001000814110000302810b2419490040000411140021418030300030085400c00140c014000622511404100200d260000d6140c0120031030340310f0010304503d40300c0d40400d2075114143c1c0b20221600161604a2400c0e04001103c412080581c80c0d02080000d00010a034400d81034010000d0320303800c501c1003000c4d5042008010f08a98098440c01a1340310030466201c40c00008030540c0c0e2212480c1c100080d810040311002da0107009030325002540341c0101012102129801d40c040701c611400f0350103c0d0303100000344680224408030b60202a510001c03072000900f40d0300d0200703186048617102500109103a040da0742d074007020450000c40108101004401030040c003d1000007552918800c13642c0c42e26040c0b13180c444035124410002d02a041103c880d200100790f4035807074030040040c10301800820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 600453462 1250 600452212 600452233
    0x20d0605031f0f050c031b09041503050f07051503090a1a101a0904050604180309061e1706040905190b0a060602030412060e06100e072d0908 62
    0x80340b140c6000650101c0d43d107400420303910b0785494400c40c1e10072903401a40d2451510740400b02000440d100c0c2c1501540082009184104d40b100d00800301902c98542c2819640e40c110728000b801c000812886545645c801d14040003681c2d6044038079041c00e04011403031641c98681030b079828109401088e014104910340c112800c00d080900c00000d100e084a40000300806807106140d500008151400c501001c40601040e07034186425440581c01c0072004000254051880c00303540c0e02040c1a1070190b003c0341ea1004104861900080760542c0060f1031000e0003c402415100030307003800b03407211a00c081041c42d04005002522245e004c949001c3c0c10404503210740030300816844000c2e85104c411642c4440210104941d5030385c0e80600f5040c0c038400c0d0082d600305030405031440c8000e030b0194025610b01d61180e020100e00b41c07051245900800d14007420341040c1c5e0411107080003041700500f013601040703202c002090b8100d940d22030007454803002a502d60f110000103803080b140c540c0143c10003402d5005204010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 600454712 1250 600453462 600453493
    0x30c0507080a0f05010c0804120e0103021314151201030f050307050f1b060c0c040c090b0d0501050f060910050a0908060109020c0c120705040209060d020c0a03020712080904020d060503 81
    0x940d0410b103e04c0c001c0c042041d1482c0201c8010b80f050350002c100320946405c000184c0e000d28124442c0c0036043c9401401d2042c40041c1710754602007940300c00541520440c54410505100c10103100412240300d0a91421f040403440d031101500501c40600f00e08501e41034a001c000060045076600354220084407890b054200c2559143e4500c5040c102c0d00d58200703020425203040c030000f9103000d4113220003c0d00a40f00b000381400003521012521008020a840010651964039400350000003003c00c0c0019030356040106000404000d19032480c0b140e0b1040c80b10010075034841d4100c0c6140c040718a0100c1d100d00c400ba105481604c090340141c180760181600220302ca1a46038082e1000b03500003c02c03196905025401e108641c0b80201603c100c64100d04070038407060a15400420240c840038020743e1519a0003c0140e003260000c1003070107001d070020309800d01815410401d031030240c07910b01d10307001d084281551080000e108000c44240115004110441c2c0544540c0c8140028030001e0140c826003d00c10203803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 600455962 1250 600454712 600454733
    0xd02070504050714190c1e12051828230a081e150103030f0e0303040b07170408062a040e190605040c030614030d020307030c0507080a 59
    0x4581c052403501c0b00081602e0f2144660040000d8002e15075880d00d05036000e01151070122065480c1406888091400090100361020f4040c40c244100030f21900c6180c0390030031807504e242e40c2c0d050410409110304d48681d8901e142d2030013214803c84a0820f00c0d104002081c0040f40045203030041a5014807002590a072404052061011f031500e9901d5501103200c104212035450f4000c00c00b080d4880340e4030008586418001880d071f000144116000c440076900031100066090b00100d00084101c20319160710780c6c2024049942c0325003140510b0078641070500d441010300030300c40040c0050340c814140341d4014030003400300d402400e82c040a8541e50b20f00200190300000d030019040000940c5d691b0110701084600050740c0a441d0101040f00da0364035180c0c0010901d80b0b8070103041f111141d8a00d00015107540750310a400d102c80361510007065103803074185510011500780f04514029003103400700c3e4900300d60100032103120503410700780120042e0450401031702d420440d420000117072186103990342c24028039481 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 600457212 1250 600455962 600455969
    0x901020406020730030e04061d090d0f1b0501050f01052707050d0f1a0a090204030503070201032003010801141f1703130b04080c0a180507030e0d0207 66
    0x884060b195120f420511544c4021012100340700311035200000504868245840240240740104c0088036031000a4201d034401c4c1e0244901c02d440c100d4485502c0784d6112080e44c0107282c0e0000e81243c1040d01e20107403041c450104850200030504c2e400c80100c4001c1da000f01d102c107400900070031040c41c090a00c00000a02030150310b208500c0320000b5014122540d042d031076a461140d507090003d81f2100ca00703440c903802001b000035000713417507581100314203006204001b03010f004203207036442c2010780d58140074200c04071f070304100b849600422041c0007107000041264071181d820310f80043c454058800c02102069120340c1e601903420b000000141140707054015000410341d02e034490035907031944459031101c0003100303c1c0c00c82d91019070681007107480e5440390401c01e049118005da07803518040c00858111031500e600000146d11001c2000e009080c4100500341c2004010354034520040c0c10100e101014a0100d041200040d49030000285914440e410160884581c5011951001038000000c0d403945814003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 600458462 1250 600457212 600457217
    0x41d09010b0a0311240a0306060905030f0613050a02090103121412040b0709050a061124130224070213020a050d0203060f0306040804170a02130915050901020406 71
    0x54410624040c0845022a41d108500149460007a418050421000c40e1168020701e032004e800172040440f40020015a00b141c0e0700000d101d800e19002411000290704402e0003540007030840c100a8400103181d0b0741241c0308224140740c10f1018949103242c110394840084d04160a60000000c10100d520240024801a1654003902d021105482951b01454002d81c0d90308400d100410042150030030115000041c51400a06298450003c2140320700c07150b000700d000540024040e0030410060002c0070030003044040420418041b1102003103500c0d0302402c0d503020050041080700440d50b41d0009241c804800b0600170586c00003280300100c143e00004030a034041d0542d10100c090b81d50691080314142c0959443d00340c207200741e0801d070800941004100320b802c1600c510700020f01c0d41d81045801e00c50b1b403069074183c0d65541403034120620224035100c2d2000b1703a070007002448010b90b1000c0030034021340c03016540082c003228a41007480a004002c18002446451f050900105080c19001401901c5071034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 600459712 1250 600458462 600458471
    0x3020f1c0804081608042d03030e0f04110d1406030717011401090506240d0f0612050a050d020d0206010510022104080706170406020901090e0c0304120e01080c0906041d0901 76
    0x4078901f683c0051012000c5244007802d4013480000c2c015139028480b00f50250603105082c0f0088049001c0b50703070103691109146008106644a1119400b4160006000e9803808066042050110366a014240a5911103011040c4000350300c2d0401d40c0024003504944800542659541506c03000401e000e80c0d040e4001c00e840c000a0b40101a40400ca4a02141450b5068a844000d02c2c04800034003902001042041c0c0301c900014044440d185880e90181c0030f038025000140301e528156203856140d4035803a09641142d0040324000340c000ca0024111182074072400002c8001000807030421340c06442c0e1003078003650b1a060000400d41c0201070000c0d14044000c070f403070301078540c0303c150344a80300c0582c0d40007201c48610020700014402c0d000340c4151101810720101442d11900c003500090000c0b10400f09601d4003004001c2071001071105032400c7c03400c508002070154407080008020b00340c028900f0701d00103000941c0811640311901114010259200c410110381d84001c2d04520100c4192082501903080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 600460962 1250 600459712 600459749
    0xd091208070f17060d08030c0322170f04170709060602030c0606040902060c0a0305030f0f0103110d0c120506091002091f03062103020f1c080408160804 67
    0x1c00d440c8a0007030b42c1d43c442c5040d0589803800d401c284000107100b01e8026840941c2000020142130185001c0c80503402c40b2034603464585e900d44280a1010390401c90141040c02c1c035030220304122850035001c02c4400c040341e40e8080100700900d03d482240e02100d003024501e041000140d00105100044e9404c14030180320302940c984040b40d0705c4c080c004400d610758002e40f010070f00078681644450302c901e1002c0d00700d500302940100780905105022006401044000042102c40c0c2005100b5035406004032584031069411522038941001d8480003050140d004440d41c101448035205103a40145041610800911041c1c03508031303100c2d81d091300d4144091080d0381710115256814001e8a21a000140520003d0f001814030104000b4000d9180800d256540c0c0010402c101051701c05c05204c4140c40c000c00c4800d1141c40c000307160010070409100a41c021301c0b2445460034106210701403208092801e01510f469500b840f85042c80340301b00500c48170a903400010b0800c000c0d04060f108940c071410740500d44441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 600462212 1250 600460962 600460967
    0x3040807023c062a07031b061b1505060d0501180302010b4204060507030f02121e19090e010608040804030b0703180c090b0f13110d09120807 62
    0xc1c144048455840200c40d013154403100102c0703c80702d5038504c000c6513000d9a0300e44a07039904c2c00c42106100c1a1041440c4140310340c03900110101c40da480703010b0b80d0000703100c40381d00c0d9074403402c400b2a400d155146e100d202080c125680e44450f6031906030048003c01c03112005180c00c514064420318110095401c4c00501c82d118038210081f40c1096130302ca102e03074120021810480c5521010154050882044600c0b1012401186809000540181d0b104e80c3c0d92905075060160100c013082c82064219885a0100c00000d07050409484020340084d541490074a0300d26540b088600a600821001c0c040188880b0b403150f81c01913004085400f4130311140b940780d0b00e5079002c031000c19080b10090001c040400c000c02c0068a00707075010758480340034580020390070310007003090007898100c41c07043d2500303001650b00f409a83c01c2d40c401c20098180845e0066000007640d80459a481c00300c0e422a4080360341c030501520001900d030212003861035992020410603401d46040b500030800700641000060207500003540c05c50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 600463462 1250 600462212 600462217
    0x118061821030305094b07050f060d020310090e03210402040605121b0102010b0a0308030a060302060c0a0c0504020322082703010b03070b03040807023c06 68
    0x18101c03992946406510b072416406441c01030180b01d000e01c2000c84202011000b280d4031030440d038404e201400c40140c040060416060940f07030400d807541e014001e8414206c0002490400c44506440649080113880c0c00940e640c0507a40e200526035000204004490080d000c492007070f40c100110411900440808407640e07401400199844e51040030312412082d0a01c050003603102d48010000308005403148081198014500c40181d11644410300b0341100480343e00d8444040c40c000e1000704000c2201c0c000103060090b85102c090680071001010640e881c5643c0c200d0b4001e1030b0064080741d0340e0000030480541d10040d840c0259107404484801195a1810380211b80c0180fa40b40401c034214501034500c4100c4c58020782d02148c00c45010401170020140008504100e500c1c902000c09420742503105041c251090442544d02c2908100e005005425000090301e40040d0000c2c03103240c64494500c0420240380c100b80618080e4040d4003c9410102400d00e070041d1a84003440912005082c040c040c040d060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 600464712 1250 600463462 600463499
    0xb010e0d0512311503050604020f040303030213170c12030d0c02030403060b041401170703140312060901032d021306081905030a050705010b040c0c02120f0303011401180618 76
    0x314078207550b03868205e110350000703904120010070042c504a118598612503500c55801200801e0300820240c0089050040c60001044008001c0c138a01314004542074030341e00c150f040c4603c190100302d42145c0c0ca4034100150380068141180c10000c5104a00c00a50b0b00d801521084520605007904c4244a05050040a0680700c5200c02440b0036424030066480681660000519512402d20b0020200c1c6005518551101c0c1d0580603546c1e038081901c3c9076140c00c10080c0300c7d078059004440100001060248440c0140305c1030410406441c0359030072002c16001d00301c080030f0341c040285c041913075118200d540504202c56080007184d00a400040280118455400b00905a500140318584e25940101d00813300b80c0d00c54800040c148003040002011101c00c01c8880300007504180182007181424500c962840124100510000320450310f02070340c1c0d11050040d10a0820701c0301031007026901a8801d11b012500d004000110a42c4508008061510b0a00c041c41c20601c5a0400a0350311019500301502 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 600465962 1250 600464712 600464729
    0x51504140c2b060908090f040b030a03032004090f0c0e0a03020f0f091603051305190f0f060c09090204051e0d0510050603100b010e0d051231 62
    0x9964001c401003039641e10318204200034000802d1a4000501c2c503204060285101d01400307904e60b100300c1c1c20b200e02e04c6201c0c0f24507405a883e01000050b01d58001945001c0d9070b0340b619011601051940e603d10a0b518290061254130401281c04a50a4180e4105410f0361100907020480c1d049102c0c4200da09409400c80c0343c3d0000510784007403015041c12160100009809080b22040001110200710800012170300030318556000d0a01c020304031741c18011079800040c00003c1e000b550056403121a100c500a6040c8031195880000540c204000c401c8100125500414a044444550f080c81030207400c028083d0782c0001d00c190008902600d803132090f01d0070703a10082d2582803050a040c0e480d0402043d030740c074901d82c48a900450031b00000c0c001c0004d500d05c0f588191010a25051100516192944c030514402e81d4500304000945240d9000c050070714041070865030500031450504216003048601d101403406041c00191074406080c05100c102400c0700c80c5980303040741e101901030602400496000c0c0020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 600467212 1250 600465962 600465979
    0x15090c040b0f0d2a091a090103021f09150302180108070c061508030a02031201061d0f13020406020f10020f120703020d0207060c2c010318051504140c 66
    0x440c0c460240340b8004040d0b2841d5071203082400c03003250908084d81d4841c03d400e40e226026007444460840010218000c25552220b03694151740c005120044c0b401003d1580101c0c1e031a071404aa03218880b40b41c000c0540f00180000103d09500080280d07000b10f81c20070a040d01626a060f45512641901c0c0c402c2e582d0703a9440610b080719658420180542001843340e42c0101c587c08100f401050004151010f4030790004d5a0300d5000c1c96000581490503880842031006500c900d1518460080c086110172608403080b90740d0100400000b031000d00c404101052080c070102e0301054881c4c00140c400c440e2040301b03084900741c8942d41140c1003680300c5c07a8108a41000103100d25035a1080e00303052182c1107140741c28098101021410548201d800000040e01c0c0607407503904010501d500301e1a00c0d001d80d180a08a440c5050b011840070140764024042c160401d551100203058600315207100303088155114094543c5010301002101c44540c0c01d40b002e03100c0ca0240072034460380c9240042c0c44040408040d00400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 600468462 1250 600467212 600467239
    0xc0a1b080304031d012a0201020c09010b04170304030c06080a1d0c04060e100909080f030a02251a0703020d09060501050f030303101a2b0c090303091715090c040b0f 72
    0x3201b0800101c000c90551140f8001170086950304182580038205102c0d1035a100e916085035003100429419140b1502d400421050000c0f0b0300b40c1c3d00744070a0b507840b414034044941b1903845940c02010400c01414591000300d00d01c0310004804211042201411034080c8022a00c500100321a010240c6280c01c034030511000800041102da0440c0318500d01030385141d41010004102c0e04502e60046400c0a000c41d40040c202c001204210805904904c0550320030014034459502c41e42840c1d010f1100d070a030107001d8000a02c11500c00d40454601c85000302d4140400c2c203d40c686000070741020301440e4807030204c0700c0c441c03401d0f4200041035074410480541944100c0d882c103221210540b4000c4032028070100700704400100c1c030a041a50400c4a145c41108071400090002528200c1d451050708030100200e0280070004682c2c041110001d980343c0c02a044140700203115494034100035600c0078034100a03400200306929501140340048201c0965003480007401a10400101d5400d402c0750a6118021003001c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 600469712 1250 600468462 600468527
    0x506121306021204031e0e06030403031e06030f020405010603111804020d02041e08030c1b0d0f03081503060c0a080402010c02030f030c070801050c0a1b080304031d01 73
    0x81565001e4400186480415250070f15001d004684c280c01042c4081407407200c211130f00c0412640c2c5002031501c10626021400069005e01c400340c005010551141400b4003040540e4240c4600202c4400300bc00505076645440342c226070400505a2081d0315040c00001d18078043c0c01100117407070310105030b80d280c0b140e900007940850034112141500a58241302c0e1540c0a0880c1c401403024104070212031180d95180310b00c16030824050b030071203841a00140480400c611001a00402d140c8001c2c16a40340791071444081240d00d403481d14050700640c1640800c00a164000c144a40140003c1c5490050705c00043e09142d5110000d58401541c400f04000c81c09181d071142040c26041441450501c0400c0c000d41c00103841c000181c030050203a034000050580441d2002c100e00c0e001085100c6c028051498580500f0981d400b40d518150148013401580b2101c400030032030721614865100303030760741c0d202c0c00c1c5403d00400320841086c1e0fa000301d104d07840400c00998002c0482c01c2c2e181301c40014045401110b01a80d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 600470962 1250 600469712 600469741
    0x6090302090c0702090f24030d300b01020d030903080103020103020307110f070914090a0809030f030c030306180912090307080703080705070e0c040b032e0302010207050612 76
    0x2c520038080c14018030005a40c0c44002501a01e0038030102d4045040200c00c521041282148480300c250040e46d8040c2517403800700f0403903012540d40c10403880000320703071034503901c0100c00365000540901c0030043c0c150285c1c540d600002e420002039007240c05403c0031450a904440c111840500807541c10401000190b100b0303001180c0c0041149400c020380300680301c20526110141e0580e2640e43c004180074401c010180c82007070111620407400c0c0d60641400141c440d102c3d046030101030300d8030360b001547c2441d54400b0002d0307072141001745049a903180403550906031039030002d0301d03800d01c0740c0c001e100310300c03204c5101c031002500640c4024003034520086202c6840ca43d5034080e550082d01409600400101860f040c06448021801400c420b035072401107140250a00901da084680c07595001014402b43c010803000791000c2c0c40b00000202d41e40e42380c0c07410160100c000d4030700c10b00080c003281a03c842115081000700301100c0c030030303021285c125490b503013009214000d8030000709441182c4c1d00003030126010001d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 600472212 1250 600470962 600470971
    0x4090f020405060c28150c0203120f0103020102060115050a0f03110418060f0f03200a2d060c1506050a03030c120206010b07061d061303180609030209 66
    0x10052401da9920b0200d5015044030000150b560480c411800403d03800c1003820242c010a2602c8080c0300102d90b55510381d0240710306010103056a51080c46007124004c00444007011248034190f51680f030314400c01c501444090104034018029100000390416080080141450440d02e07000c0c02d15440420880c1d8103554140c400042544070342903a2181c80e1150300a01c0074104551846003603048200c007038000d40d44d01c1c0e80f2150212240070070400c40f1141b204240da05680e403100c040b500c2d80503d0841015148928540e142d800303080442c00268040e5441d04100da0f150040c040d11401109500c44074254190b18442d00010565004e03030000000e84004500e104036a1410380000c3d00ca0301c820100701080c946030002ca010448190602c4113000c507412518a199809200410f421741c100038494020307003d400e8004001e01c0d00c41541100f0104800b010030b801e001801c046036080e2074400365406182522102c164082000310b403c807800041d030300d601407003950550340700e5244461a50707080c401001c10091 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 600473462 1250 600472212 600472241
    0x9080c0111090603010905130c260f0d05031504140a05150f010507060e07090903110d1b05150718080c0603040b040804152a0c1a070609081201050102120409 69
    0x1e02d40c000a50301000c3c0e5405000d486c10f0030320700c0b54151003048818ad5403810003200568803032682212107040014241c01825642e07d005c0391039440710120380c1058a1881c82950f0300505008000c00403981202c0c0c2903219881005050002e40c5840100c04604480500e003250410211504002a540200000c10409105450000e004800c440403542020041d8014160090b26556094140755100d01418602e6080001401c000e46032004041c102e8141c46d058240303419120400e00c0e041c020140045c103c00ca40c5a04000100d103041c240c0101040808113030f0040c41c920804d40403441200026403c2c200103000382c102882c5444035169011702c00c0004204980c1c0b2001080b01003030041c2c40420300c10040c80d003030301e4501d4039a00141030300750f4201854410300d455040200b1803201013504100584100d0710318034a804940944650320034081c0c851040081c010504043c1400c3c1008280070040030480301e50719a16610783d0302d8000498455506c9091855603a806000900032403030a980011148007242 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 600474712 1250 600473462 600473491
    0x1608070e120c010f081e0a110307020606130b09010e0901020403050d0f1d1e04020d09081c0605010c120207050a1706090105060d0f051009080c0111090603010905 71
    0x100059010084003940c192942205912805958011001c0014684c0e1030a001d170851401018480101449684922807550140f000c0384035a03000387d000504a80c000f0041135900d02d0000006550740c981600d440d4010700b00e0f00001c0303104084074440d4a142d070f00c00405802030f5919240b0509104da001501115265508000010008804000e0b440e0703c0c0781c9039194424400304e001d0300030f0200007203450b904a200100c94003142695a541d05502003028000c0d45500b10b22986c000464024040d84000081d040c0c0b034801d2210900240f00040c180b207990610b880103010441c4044002a90164032030180407503e400004000200c0c45012900c0c0f685140c411103a0b140d03511000079441521640c408203400c0501e214000340b2280a02c00554008410700081c803c1d0f0a20102149117400c503800007402c0304584c04000020040705010b1800843e030610420b2040075440d04000909501000e40618258688041d80d900c6140a4080d0f5030b070310400074809800c583c41c0c0385807000540300c02420200c81c1c2d00c40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 600475962 1250 600474712 600474737
    0x30c1905120421021b04090606150c1a071704030309080c0a1401021e2206110c01030903050a0f270e151f1101050c0c010b060702102307050a0606050108160807 70
    0x1030340340412458465514075085149604041416580c414408433000e021901081107440c1c1040c2001c8003a0000514040e45030381e00d0601310300409118000610001002806040c1080001404a0018040c00340d00383c032561528401800c0340b0942448000825044050071059900c0c1c1014044074500301440303e812540d101071204605100d07800c19400320b890707940d404a08000c1000074036001c0000b0b080130080014591805441c03409248144010000c5103a403102d8400c0c49028050024100300c1c40f5011007115404901e0780300f41890044211301c1c046240002c1da400d10301d0308070307480c0d0724005803225410114021380320b581042e01c00312440501481203800c4410810904c112482201e10034101c6403034100b20546142958240010644203440601c40b403805696900b0103c0303210401c500f441d600e40e000b0002420f09100101034030170654007003c151442404008180f840d00300d40704550400c505610b900064481503019900c038020111215041d41c400b500500c801d40d0403106900b030000c2000369 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 600477212 1250 600475962 600475979
    0x5070e04053301090b090a1e090f050f03030c03011208040510091404110f0304140a061509062303120c010204031205030c1905120421021b04090606 65
    0x4500681c18151502c2c0e070400700400d0b40c0e1000603024082084041c0100020f0314005010f049024044030082a0781e5441208040312400c1035004500074000e0600040110381005103e6006d80310080e80c89000d2559070b4804400e010084034460504c071101c0a0441e400c002c403007004025001421110100c0411003c1050396850f540789003004819510401d4060510b1141404442e179000b856008906246604150200c40002e4580050000154984917070391424142456640728201e000e45000700b179010414054560461080d40c4645140d89d0900c1d6a00c1082d44100e44142c800c5400b05140241d504018900052581c102c2e080010300702c3e0742c00e01840c01105803079404004240100d07940001c0400800c135080c030144520301d8143c1405801c0d490300f030b860003640d44112484180d8884440c01c0d02c40c41c650141080d81d559204d00700400b40036203410300d0031030003c2d04071801840314541c840001e10a06880000c0a98980d036951500076595860728007030102034512220102d814580b50303100401d0303140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 600478462 1250 600477212 600477253
    0x1b0e040f02040e09010b01051c11090a0611010b0306040f0209101e060305060a0303140a050c150403020f0c010518132a050909040b060103021314031905070e0405 71
    0x41503011003805800e013071909500b11080c0b041c486040c04001c0c0305440140325a02c90074818003107d43c00108003861991104401440382c4444d103a03210500110110300c0c1c40c0d00c07507425901150060001c22401444070b08042e0380d144100c500034030fa0324120500f100141000c56041703401c20f03600c000b03107181e2544070003805907800d0b00c43c964a1070070251800100304c11036150207a00d4000c0000d03206c2592107401d54400a140e07002c03c0c1c003001440c400000e006104140319804a4450f420b5060643c1c1041101200841010205640a400501c90200502c1b048140800c5004407020f05071142d924282401c510414500c05c605611a0301000b4420710400580e07180c011080413403c0240700301500c81c4079600c0c24001c100d40b00c074030008104040c080072a0310303224150600c6e00719422407a0301c03c4607582d92004070043d20583e4440d070700c40c43c44039000144200e54200400d80781007085007520460303880c100c481780c8008900d003000b41055000c00c00400001b5200f07240300d030b00103000340c06a4200e1003004c8009240e01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 600479712 1250 600478462 600478469
    0x302100903080a110f0414060c0d0509041b1205060a050a29070807031d13090303270b040219060806040617100515040e0604060b041b0e040f0204 64
    0x2600b041d08000803c680c0e40318030010710142089040c14922209844030302030050b4080c1107424086020342c40c00540d600d000351400d6010007011500c80c0d40f01410001c0c25504003608403406a400c03c850f01d5198a42d200700104101c4c410f0b8bc84804d2400342c066000080d000c0508070541000c421079010404d80c54489100000c0c00c06089103034907610551400c1e1005041510318641400001c0c810308002030a280c04691099415250000c00095040400058083c004507119030140c04c0031403400b004043c580003481d90740d010791000c2000e04a00c501c1d00c9480e401040c000b07801c0c0c650318207200300007071555404507404c03500290070000328003a548403e001c0c54140b0f401000124405d042045890302e000d005110151030080c2010840b58101ea2801c0d5a5105070754582078400e480310700003061504d0001c0c0300c4046250043c8144030104503c42c03041e440c0d0328207840603142542003130300b10b030311a01f400d0050940250b4252044c03268046603030703400c5910131004903440e640300751554880f440308002d90020380080e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 600480962 1250 600479712 600479717
    0xd0e090613021e090a0806040b010e07140301080a140303010501050f0f0d09030903110105040b04170c04061514030103080703050706020903060411010f02010e07090f0e030c010c2a0f0302100903 85
    0x90b200c00500b00a841025513010246071f42c855410040081c0c12001d60343e04403000396081f0302560711007070390584002c000c0c84454400340c0c41c0480002181d1100249120526000b200240200d00302c078803500d9100d03c401d005003408140308200700b001c3c140e01500144015151002a203062001300703481c1c50240d5145003019000104400c3c828018071001c014801c04000b801d0804c2481d05103850b40d040c0c86800349100340c4c0e0040648408204941e8410b01c80204a808002c000300030413501e442c85e117511681141100f1000404a05c3d4044030720002d0300c04c59041e00e40101040e4104051940d089030242c0c000c060860303109400f444081381030340f000c025103030069124034041c4141203640400104101448130054007168105009e04030440000728000e010341d032028102103010f01004402d10301806000c01c2c070800300c1c440001c1c11180c13040c045d480b8141d032040302c1d0b8940d24441c45005200f01044010319103401082016076085001807600020423907224401d0040c4c80c60101d00170052001c660b000d03e0150007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 600482212 1250 600480962 600480967
    0xd1b1b14071706010803210403110d0513050402031003060b010c1e17031303300203060901172806020c060f0a0e070b030a0204030507170d0e090613021e 67
    0x480c035000c0c403d00f40074080703001c019410410451404141054111400801d411040b4003041c00d1505c070325404002491444c04951410006c1100245039a2107004040c200810250740800d2902d428000c6a0084a281c0b41080001d0300b140c407030100400c4445800c40c1448444a070850000b0003800b046490814641c60079079100c0d00c0c80c2000f0700010082c103492100c68200f00104080707920040c550010301070700b6280c00300c682804400080c054404820300800906030881c440c01899540b90001c0d84205401d50340d01c030560740e0b15019072800300030064030301c04035070051100520101c680c1c90400c7c111252041d00510050a1600d17541c0803030388004680c01c003e070048010440000075444c90150009014001044101b840100881e1241c029000b441400840000811680d669580550300615003100944400f0703a0782d2200c07001601c7c030a0940303402c0e0703000c1c20f003903620881c0c02880c5440ca06003015001c0134182d40c070300082010240b07011121040041d0b09000c4100b602802a00303d0403036500c3c141c500c6a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 600483462 1250 600482212 600482249
    0xd0504080715120b0301180f020f0102060103021302030702010b0d050d03150f060c1109070f0225050d030c05101a0f060406080a0e120d1b1b1407 64
    0x500380740c1e8a03004021441c000b00c45840d0b520f40c1c49865402051502000000d400001c2d41c00a4090210528140c0c0005811014041800b00c0030b1410f00005108480c51a100c1c00990016a00c44909101c00795010000d03042c0201c10030307070076001183d10240500c00042c2d040704442c001024008801c0c0103075055072046004c0c1c5007694043c4583c040154030305000c00c0c0400d18200348500303441114020340c000c00c4244215101003109212050071400b00040a550320ba20300800c0003010180303c032844600500c508801141c4004040c002c0d903541029400030204514100400e01210b20300c503020850070080b0441c50312000c100c1c184207004402c3e202180105007903951348000c45450061502c0302c0d2244131092100c1d00c8990781c5030121400c44483e800d0016055a580001100030070300c940741c5401a0282070b458001a4200c5001015a41e1114008021250450451030f4000d8080d03803504010820f0a41e858409100500c1c5031003c19109a2030719010700c0241c0d80c80780c1005c4072035110b10011440d510200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 600484712 1250 600483462 600483479
    0x70e01031a06010c020a05040e0a1709090f04030806100e0d150b0102010b09130c030516030218090607110709150801272004020316110f0a20030d0504 66
    0x10b4100d030007481c050701c02c3d03441a0005940356015118880c45a40e8549071034118000511038411940c2d00003402c500d1600800c0820710590f4003813520203120b6402a00040c044c204540e04071070056406544114143d82e45c1c3c414403444200503004081803081c04115005580d0356007020f4200c56115800d000c2c410480c508a000a0390082c003a442d040d64186484854140c8842020700d500501105c8a407607455030328104016038007219000600240215040b135242001c180340a44200c920940314103524103140403001d02400030036200350305c19400c200b020030a0b84e071140401c20281e4030548161071080e0703512002001202d0b201c1c07800f0303d625040c8201c200b02500c02032041c408040e8500905c25440010703030103001813007241c110700180300075442c4015040f80304c8004c500d9513091001030811562030411800f81001c0581d061101c0000600001c4052040340c8045510905020428001c101001084d56503000b4800b0301c1405000c420342903141100d51360740c200040c070b01940e0385072265941c039410705944 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 600485962 1250 600484712 600484763
    0x303180907090e160507050d030204030b130b04060e0115030f0506161704030504180209211009050c09011d070e0f0f01020703052a0a120311070e0103 66
    0x40c24802d81c01810004950400c5003141d2069801e10380003680c0f1500b5901303039410300407582d01030410300c502c0f000c00211582550040003502c0c010707800c8025964440704820019a245070000740040b6a540c003007000241c0540000400c2e4240c2000402c11506110004550038010350080d204d0403144401e031001c0c004144001a08810f0404200600002d6210b0283c400e1504508110022440000043c20715128405842c00b030202070103814650503120240c04003941100b4005846851031040c1000358100041c0030304c1c8000c106802501d40c034140e60304110001c05556030261920700441c841c1d07821994550300007501900d00c6002c4040c024820300c041d040c007103c2c0100700006205100d142032030310350b03964503952454030021030b00d0301c985c4984800101e04000055000070003d100e401034081c2c00f08d0042c0e02640948081400c80f000800d9410208414800340b40714121188540c0d8840d60042481402e031300349511901012039854545da01c1d04098503804c240c2c400e0b2400340464509010f1120794880 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 600487212 1250 600485962 600485971
    0x1080a050c04150905030d030507020d210902060712021c0215010e27030c0d03050f0a0213031202060a0501090b090a020319061e212003031809 63
    0x20019490207a110001c1e520403030040100200011a000d48001d00c20704003607024103400303003e940f12039449650180103001c00781c9400015000744041d091100d8850300c0d0308086841c00b07403403450340d00c005482518001c00319034006a8200304200880000308080000100c1041450742c0144030308040070f80c41c04880003000d4600310841d046043c8030342c0d021109094103030548194031001e4032551643d219159114008611548800015050302030b001e42c0040003802d14051694141d440b0009104001c0302150002c4500ca1500302101c2c0215640d0880e036400b4110b400182008802d036a0303243c0e115441404503c444070b80042c2d1000b001c00441003841e025040c0108407046e0b0500c03c20381c05000085014600910b2016015070100c0018030070126009455642d540700d250130030040781c4581c0307400c40300c1ca5001c1c0000d030304a201400000c0c170140b4040c00300c0038403d502d0501c00d008950340ea0302d21020510341c1c1e00000f59811040350709811590300b400204820a042035210400214540500040400061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 600488462 1250 600487212 600487231
    0x3021801080d120216051b120303010e0403050f0c0709060b160b042303090405071103180f0a09021b03030702190f0f05060f06030102160b070c1b050108 67
    0x20041008160004a510600000e030800d921506858418140280107980b20b01d8034080900f06004180480813a688400074180c4045581c070082210600c11800141c40d41c506060f44100010001c80d0444011581c0080c4a031902034034112107000341c05816040300c004904180c21a11040100c6011842910000c0c04000343c040d0610039101e401c2da550449015002e852412140c0019040001880c1c0c80549006500e01c0c0c4a40c6c10403488580d41d076a0070070180701d805a0300e442e001c0b48100f03002d01103003030280300354000440c07515a05d800301250320f61800c80385030b40040340c1014400c440d0b40c2d00000c18001d001c0e8854016191030300031703807540c01080c008960a40d041d0001c2003449600c9074040f40c41c0004034a8152000b03a0250b10380f419820b0454542006480c5840040d206010040007141260055204803107108481c0c6418040600703c0c0f08403549558582c034142d00d40d200250b40802c415074000900d0420010300301980c8c0301c0040b1440800c1c110040c01780740400c140603542e0001c008903000003260 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 600489712 1250 600488462 600488509
    0x2132709120e030c011e1e02010b0114031302150f0412031806090b070c081005190606090509070e0306090c040f0b06090603060a0b070b041101020a02090a05100911040302 75
    0x2040060b061000106c104002a200da07050f460f440c5000c0c421443c2e100040444038891902003040080c02045842c4032540091103a010150030360b04800141c81c0194084400004407a0701d542c200004110082d6450b01c40030b42c00e1001420785210350020304010321045806005440440c60010236004041c0d0b4140500050300c042800900d038021400400c0c3c0310f080903c65078843c000e040405140ba51a80b01034914403d0b44622640d001c0340e82c000501403c4c20811f0850100ca00d40d00d920296201401900b0014400c28001c0006141000c9183d8006046090415080702c20f41d0219040c50400c58260402da484108510424141846a50600e40c52000d041080d0740c1c03410001403861040d0700281d07126441c007001060f00c1e03503148018a03000f403d000700a940e44003180c6c640031000c04c2d02100c007038030115906d0003000410350000c545041e050358014483c01d81ca91300d03a80c5100c000d01c0c1c060403034810409807000c0416800014030800003d40e500d052203603203542c554410410f000c40084502240c16005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 600490962 1250 600489712 600489733
    0x506010303110f0c12070b0d0c030605060a1409010306030515011505120109091e0b09010f0b180702011b021606030c02121e04031a01080102132709120e03 68
    0x30aa0b0000300e9400c984817503804506400c1c0c1031500800e0b0300b002c1d107002800552070361449030a0344005d01e40d1500303490500c007296079001006000d0141418a0f000b0854481220103120100e01c0107080c4118141400100031703449444062411843d114418444414100188000f610342d449a100d01d20700f9182c007d01e80005010022000407041c0306020030541c441001704104407141c0b5601e0244030303040080141c00090b60038841c941034020384000002c0d501e407003066040c0000034024060716080150280c001620074010462aa14004040d00210355035424003170075401d20742c1a070b1050350303c09a008000c0010a40344121046040340e22003001c1c54a0050701581454010441d13004141400d0861a181c100e501405c503c003810200b4403010701a4000b6001c820401c8041c8007000a0070b01c80c0416941c2c6c1e8035280114204c0c881e150920140b011020020000c80e0203150316440102c81040b440041d03c818041ca00d404c0d80d643d40c5007141e044051524440801d075011600f641c170150100d001782064400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 600492212 1250 600490962 600490993
    0xf030a09060e1b13020c031303110f0604032003010f0213050a030f081e03190507020106140f0a03080309030306030d05070f060209010c150605011b0c060c1a04050601030311 76
    0x107031410180501813440381c00c404000a6415201c0c4110440f043c3da950381c1a1030034009100151b400211403071002c81d00020014100300000702d1400f40054583d80c40c050840d203400c000b4654100c24505085482c104440c1a61000c0c05900222104910050b03141d01480d2443c2d0013410290308154014007070b9040410120f1f0030340352100b20389500240c04640e100f0403d00c0340010484d800d04100040311001040c02031403000741240300380b1994401000c000640302d414040b03098400324442c002c1c0d00002148964507500d440e04035142c01c00300080c00b00d80701c00da681c1d644805a400803140c00d021500007104008540c103041c0300e2186003808501c1c24034501400c030b644d40d8006c04100140900b60540c0455081c1c0c061340100490f088071a00810b121840c1c86403468a04013403c1c041c01458002080c140040082040b04603941290b0703640403045444403070070210211807450340d01406646c241d03200810204210390b00480c40703003d24010000b60402e5030460402400300400718a801c01d90354060750000400d00d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 600493462 1250 600492212 600492253
    0xe01050f0303030f01140117040c0609080d120c02190c08010c0f020607030903031e05090f19022404030507050a0512030304060e07052d0609060d110f030a09060e 71
    0x10106c50600c003250100780300486000c25103803510044c11440405000500429800880490f01542c0c1c0c0c90403a580c03035455580c0ca441e101b030b5001c800b080d0008002078520a990f082714103400e140f40f04645600c19010b4481c03a00700e2034408161b602c00c075000e0003440005002e004070182010103003408400001200402540d5400091040d8100360b5299080380805119400144e210021940300e9081801c01c2000c2c41c0c01401c00340c80031070251082000e0980030308800702e50103541c418620101d00f140c2c05c658080c8020200c0c07001030b0115042c203589001408010180192004e580a0001800c448e800e01c400d0000c0d01380190081c0d4800d04990102c65040c0e100001202e81c40390f0300c070002084203e031040034186030501c0d580105038061828030107003100020120f5109105c0b40880d0740c18800000c04410b200e828071990144942100c4100403030440340703203036030000345151a8120841d894850078000d6001d4980050b510800070a48490180c0140038a81c003803890600303140c001520302c1c91004101300d03840c007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 600494712 1250 600493462 600493469
    0x3060105030a0f09081809010608190933060e0114190510050d05100e010317091005091801180903051207030b0a0905070504090f150e01050f0303030f01 67
    0x2d03140d408007400b0620360341055035444d92050b03456494451b8082600050100341b0021070280000b40000942c141c441c061141c080c0440134101c04054514154a1000d0700065505541d113070344075403120394035000c20700c507090050754442100c1d0203041150601e0740a8070800e521070720607140600018803881403134040c0039412000441c0d03640300108000200300081041e603441a80d210040f851014551174118000300f031070f4010402c00304003d070344248407209080c1c1d19005d114060000d10006100081003920081b6050b103840078480e041440c620700081076480f088a0410000b0004140007680307040000c0c1c0c04c0d2604d0a1000c01c65595818140d8013048100424840950f0a46480080091500440031a0300e1030500040f110101d01c5e1408018016008100840c0d00179000004000344400581c4620380c0104040e0b540c4600d0240341038180c401405032080d001c1200c543c0c0e40e04042550f001c0c031b4a84c0000306603040d0300c0381c5258504010071100f01001044580a07400403c00c014502e030500003040e054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 600495962 1250 600494712 600494731
    0x1080c040209040f05070908240c09031204060504030b09010c0f1206050913020306010b031e0714070b0601080a0204030201050f0703030e0a0b1609030f0b0a2013050102030306010503 80
    0x840b11420000360150200c100803408a41c64403090007031140e441800e5505844203030046a6640080c0701400c0c80e034540c0001a091620001c00101d01c081c401c9100801e11590000c040340c0716050415040f4066500030f0703010001240d000102000ac0068440c1a00c0d8030148120080110811006019190302c0d030000520b42004044018400000040c0d4070200c0984009001401c45180680d9100004030142405074800c0c410700d0000150908000100d9100310400c40454901d03004d50003e20b440d85901800079014400c60700649008180e82e100903000f40d90242a00d03182c9410010009021a8405044618001e004110030700160b43c2203800c0318000700c2c140a9180ea200c002c0e0074100c0092080300d0f01805140144203980e02400001c034880340c05108200c841c0c00c59100048015681e540492100a010340464421900442d4250340b040c0da0104e070803074000c40e03c410040c200d007151000d942c824bc1025080030070710f0700c690807101483c513010308002e000540c03442c01c00d0300010b00b02d4000108032805 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 600497212 1250 600495962 600495967
    0x192006040f0516080109020f030c060f030a0219030b0a0e01060f0509040f02040f08060c190e0d05060a1401080a031e050d2904060312031a03070e011a0301080c0402 72
    0x100b02003000101d04003c400c03a21040210b4540301000c1c0030302013a040a80c403501241c10000c00500c0d01160403822890000c040c149003407110342ca04a90303500b00411078450590b081c0281002c02c10048610803120344150380000740028884200308240c40507810041e0190040f00c0148015604031b9500e1140b0b02c40c0b420001d0702c4000600004000c0c0203148240c200c000d0002c14001150050b1183c400140c903288400d031800b0342d603484120110b5009600003604903240c05407000c0960f03405051000c541c490007030076150440b41ea079143c4030316000c400d48841c1240c035034950a050449101481d860301401311003020f40020030460301e0040050811701100240c0109a28001d400d4034014400c440c1c2510f40404280100590342c2d04103013100d1211459000140b401c0b244d650118a070034819201905e9002c255401c2900d0751800440060018848500f00c40d01603c0c8a14420744e02008004010030002101001c55818803440501d0804035014001d0b595130248018440f4440114800c10034041c1900d0058 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 600498462 1250 600497212 600497243
    0x8060102030d151502061006050901020c1002210c070b0c10051009111c0902030703120c14100e060709030f03120e06390d06030819200604 61
    0x544803d0258420110b00004a42c1400c00c6600402c5540c458203140c1e00c21816156620300690b85885404903140c0141c020040e0000e541c80c1c8001d0f001d8100c1d10920441c0d0740c4010003070036240ca86400a0b0650032060300800c524100d88010404800600441401c65061115000d0301075502d103082160100c02d96200c07400180c03100d074100c0e401401804034036024072400602103010b816940c00001d44452812165661202c01c000c24041c00059590240c02804d0262854403003514500c14440000c04000f40c0d410b5110104513001005080906000058490000400101000c031940c0c3c403080c10340c0e078120b1020486940e800c0501c8100300d80e080000404010528903046481d42603208940b8840791402d140024010380000f078440c481d81460000441014000c0745140ca0a2820844900d003607101d030fa0081006400e19002d80080c0c50020300100d1304548a5a5480054004c2010001c80031140050f00c14a242e101c0301e802a80e40203007801220a2503007044c92a16070b0030084c4003030701072201c034130400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 600499712 1250 600498462 600498491
    0x11a0a12211b0c140d1208060402040b0a03050f07030605030d2a0308061003110901030b031203010e040c1e05010507020315010b0a020106090b09072a08090301050708060102030d 78
    0x1020008030b5005a03806450461a0003400320541d0301030130303a0351000000d40c0190303410b0070140b1500003504101c1e82103c1c1400520308854800b00100740c0380d04a0f409200000d0800341c0c81e405003400000c0d0342c80114070742c0f4100c1a014070002c001445c860416080c0141040b140d2008155800c88211500e440d0204980509055040d441088112038442460100490170326600014040c09081e00315801e0700000e001c41c4040303041d07600c504035122030444100700030561980254044d0401b01c030003a00369000d02a22080c038030f406070000d0f40304524078010441000b0400440a40d088040c051000642050124250340140e00c1070341801340a050110000f410015907a042003404102501000078280e01c0d80c440140c1181a004192640055030a080700814840b4042c0a2810041170141240c221a51190021151000d462286164034803054060b00b641c402c002248008143c010420240c6e558460401d060171034000914100403c00090140300341a0703800f00494113450a10350700894010911080c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 600500962 1250 600499712 600499727
    0xd1a09180c15040e0a1e0e0c0f01050a1d03030304121e0c080304080909040606052d010c03210501150804030801031401020903071508130c0e100503011a0a1221 70
    0x10301440014101b100e03224a041508806002d01600082d14404d20480e81484044000e100c0441d000c07172000c0c043d5060380c1380b080311b031000e02c0d0a405000c0e0b00e2490141c0d0210381143e000759815200400e2207521180d145412801d06843c0031034148619842d205400b00c000d200440218004104150010206050008080c01ea4404c51801052400c9600301307031920f08020910303445050b01456590f80d180c441d102c1080000381500c004001c06015000303410004444c00c00050300101c1c24000c142c9150301c580c1e21131052045a04281c0c000c00956541000e9010720000c1c0d60540c0071040001942c204030010341d01c0000c2c981101da0081c0d42002112904902d04d019003d4000400d8052140c142e000500b6800e500c0780c034000c0d8206488811a80e251015010041e06100c2009000c90040b040100290020210180e07400754080382c505035101e4a590000b8290703266010318100c024449016202949000b542c030100801003130404a042010302d0b580c9510740c452421900e0a20310000074110b411a0254030b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 600502212 1250 600500962 600500981
    0x3150603080c15060a1404021b0307030f140703170c0405100e09010902030105010c030e03100e0610061b08070602040b040b03010f080606060d1a09180c15040e0a 71
    0x566215103641c40402e5581c9800f100c1010b0700324000f408030b486400c25084200a66044013500328001940c3c1060001039401120303507000000d038041211150610500107808068440c0e82c51521602d2410300c020049240358030003600141c420001d0400080d040402c4c40e5500c060440818460354801030803520902075503022503005032490105a00d0241e0059000d15640b104a42a5a907a600e5442840c01ca000900606002ca03050900a0300440d01514410750034030801011100e90301c25205c039260070344008080f0741109074014402e21400705690340c10400588994641596020780c81c9401031030f242145807020f0400c613400103d031800d002280d011100903008900d491940c80c2d03602c8095202c02c4d0320920880f072036127043c100c01181c18440480c1c0e043c003414005204a0030101d11403606001025580151000b603c004e2148020540701c0c0440c0302d00c120010400c2c010071007459144542090036140741e05220701142e19070707528401c0011040d54252281080c01c5032aa5841028601c0245180301 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 600503462 1250 600502212 600502223
    0x3070305030d020909011a04062d03060e0a0b0102250b040b04082b050d0f0504060b010f0201050603031614030705010603021314010b0f0f03041101020d090e0103150603 74
    0x45110b480246a00200100c800582d00014540c0e40c0310b401c20b41c2014505984000c00780704000422000b84508a031a09c0324107215100c03440352028055401d841d01500a0359004244c4501c82040850840f004641c0d1100c2c0c003942c00e215201c02000000d4495a0940309807208400c5c06080c100b0400c010080d0f003002e0300d28000c0780c03940c643d1034074440c0c0c8080c0c1280c402c40d82c0e60b01c104034043d4050a0b030034481e000d56044d0030404281c2600711020503070b859040040c0300c4080035581c0e10404401c40c414094030380510700034400020034900e4070b40010480d0f003d128402095a040009212040d00d00004940ea2a0200840584241010319017258502403901c5032111911012400b401480b9043d0300100c12370344202c031440c5d0405c40c84a80302007520740c40d603c00307100320810400401c007052000c0300030148842c42100c41881d083e54944102c0302500f00356801d941c91026442e0010440d601000444c90490f41410502031240c03602482220035001400014181c06080b28501050713500c035044076014640c0300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 600504712 1250 600503462 600503467
    0x15170f0115020a02060d09110a03080301210204051303140f03010e040203010213081501061d01030c05090607030305040b01050904050a060b010207170109060c08090c0405090c0d0c03031e09050f0307030503 90
    0x1883c202021f000842c0f8143c850b004150480744061038200c5084084991140101d41903a18050200c030701814049400c000b011031800d03200b001030b0340320b02c40d140c03050507040c491884070701c07490034001e0403050160300c200b02011040242810440f0794409890460b400600a1151a1345910209001e40647c24040304c07000c00002d030114200c00c0108a2581c94001c00854000c1aa600d480844040c4000c01c010040c00f41c1072840aaa1075110750046a140942400c20a207803941103004203007a80e02c0b0607010340000760755109201c10402d80d01d44882c01060201c640c4070a03424a03444854a5005041c0010300e215541c5103801102d0b4001e10018000b003000c100d403c6614002011140d002c1c011340c0804072a09860442181103107030103a0f0b95070340102130300c0004245000010f0140001040d0242c5011a40c0c45880400b941e142c0d2a40004544203204400ca91410362645c500500700001c500240103190b1481d883c15070b055680010030808035803003102e00808051210011070305002d115040a403060100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 600505962 1250 600504712 600504727
    0xd0606030c0c1713031511040303171e09010902030f03040501080112170a0815010807020706260424110f0f0d09200102030403170a090f15170f0115020a0206 69
    0x1480d07006500ca00c0d42c508203001210707050507e401e003403149000043c0802c80341607030f500d240d04c81c005a682c2c1c4901124280c010300400151003089024003200c490030141e444071903030421030406205c5a040001c00310300450525041c00000707021100c0502030003035400c08409100061088040d8180281103074202c00650f80e0300b03c00c0c0b0040103401c0c211075400304007140004105295104503125445040c8643c0a0a21281041d000320b0341100840d046411901d03c2c86025810850405401c9015920545d0110414001d110161644076488104031404a190201018051000604031140300003000c0a50340d982c420b01101e070105002d4006100140c51500d9441000c202c0300d0301c0d25400039079800d407d540d4a4332015004a9a0348a00e00004088001c400f0b0608c88101441000d0302a4007581e003011059907807100c0c00d5405042c080d511144000e00d038109508481030f04075001e56620071035142c89051030324200407012500300061180488403050300f5008090345100340300115010354000c015541d038414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 600507212 1250 600505962 600505973
    0x504052206051b120408030c0919060906021b1c06050414300325020109060b01030207121101150e01080606040e070905040302120f0d0606030c0c171303 67
    0x4080307a02c068110f0000007150084061101a2208070a840d1842c03080360b615540c2e94042a00040c0880f038442070700380107181059681c100030894455074400880e801510b844001008421540e1099066401049401001c0040a040381081c10000e489038089005044084400c4140445010381718a242c84107000820003000491484103004c0e80440312100708403512400c01400c40e0b140958091420380102c010701c0042809994003c50840200350031070384c6900c12880040740041a880141d4ad544c0c3c1d14400c1011521441c1c00c000e0085c1303011802c080256a6824140020344000d2051207500d01808401b4070094201100c4401411103640c603003a55042d001e90031150a0088030114080c1000050250a0a1140c1c1c0c01111031000144a118541940c0c100100301c007034401d17000c6000300010048404800c2004004031680038002d690740c2c0d0050895075049642d640c000301c0416080440017185140d101c60301c0c601264003c032025400c0081c541c10b5076283c2c0b00700301d03c01d60b00408900c0000300f03000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 600508462 1250 600507212 600507221
    0x807080307360501030905150403050d06090902101101060f0b07050105012c0c071b0302040c0e0306070f02010f06090507080a05011505090102010e0709060515070c0504052206 77
    0x1c00200c1c018101d6690400410001c4501e8160720341d64904010040025601c2608520046d50060040c3c0b580c0c808503c7c0d8400400744121001d8020030400943c044000c1d40328807428009001498040040c1c400726030020380c2000c40160348508100030007401e0b2019030340030b42c8940d0062003803035105002107a686038150480c0d0811101582d00354a854000035220401c2c80d4641030031461030321b24222020800083d2044490b01505850300c080050001100041c65034600c188034109540a00b003040c0d00c0c0d441004182c8203081c0707411040210804600c40c00d6100040d9158004003142004000c4642aa01c22401490b00c9002145110b0400e02c0000d901c686a40c8003601918050b81e58518980d204280c55058031030030f10a9058038101005040c008a10540181210600510000c03841c040240401071030441550403404145944c1c3e0801c02c0700349084030400c200d06648100460500c1030079260718100c24414403620380181d480f100010b40c800301c007461102c60404294004184021281020b03001030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 600509712 1250 600508462 600508487
    0x4030807113610060302070c080106090203060a060309030c0221030d0f06080d050906092205060a05030a080301050409050307020d0308060406121e0206160602120609100b070807080307 81
    0xd050003140b030141903601c402c640b440390160700307010300780186002c000318001d5003e1001170f070f10181820400b090b04a400c3c0a030b0f01c000d00315000056180e05210702004000c541982c000d40902d8a07004074030f000242c002009204480e012901105482440045100300800300005500c41f8007001448074140902944149003988001c2020040d0035140e404290703480e6000491000400c401380b20041991070a00000c0441305400b800940b100304220700c2e036100454807100c28407a1141c84904028050502403030b484020003084008004442031911b6010300d030302c01800380c0e80c05a6101e0040e1414488100b08598a8030b50243c003450301100300d030400900030341c7c05840d2588600c2c2400400281c03d00b1910707048200c650004030f54001000006483d95644c0080d080498021000b441000607046801090500c5c60307010341d4002d41d4402061079441c1081b20003d10403403041e200e9900b0712114964907900c00d415100c055240c690313035000074109a0b8480c05a0745004084801c00020401c8495101c14011b115 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 600510962 1250 600509712 600509779
    0xb09012c0601120213021c020f0703030b0906060d090f02031203070201180c0608190606020a02040f02030f180307081803060604060627030506010f03030909110403080711 75
    0x26a42c8601c0c01558890400b000031798000c0d02075600003240501d139801440703240c0d02c00403101011b0b1102c0d10904160703040319400c2c101c034540100e41c3c2d0042c180c2500603040c0300382c41201c1c04091450007900003001ea02500c2c3c11914a2a5120608410050340070740b0602107507001070403110002006640e0700d1540d802100c40c0030040d424801c9144001e02c1123504040001d9010308007a11950400000300c4410301d00501d20721a62000e03030130039075260038203200e20400744c8400da0241003884500d005210a9a03400e1950010f00351040082260300c007a1055015080b8042c03260a00001403d080c0702413440c0506400034016140c0060601c021a801009148070058143c081c0c0c1c51a584800030031007110914800c600104810303030003620054081102600890707207580900d000e41c40d22034a45d103242c64401d8110018900070100e0030b00a1580005540d8014548000c05011410f40e10300b1603d503038011440020301104010a0140c2008244004d20b5198030001c1c10b11030100396000400c880b40b00700d04081148 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 600512212 1250 600510962 600510973
    0x270f0501210501090602071b09060608130f140708070803030c0d05130b1006030f0920150706060821040b2a071502010e0a020f0a080303070f0e010905010c0b09012c 72
    0x1841c0e03c032405503100b1210541c83321071807a5121102e00c21810389042040350035420143c480d00c00079000041c0c000c2c0199194008124690402e0350a130718040d940c0d0070204140d030040c03081044003102507044070805e10320a807000c44c0782d481d51007844d9608042588000c14108185e010450303d000105540e81c21140c1a540c107008000c0c414504508540c000d0201908035600c840a1409000000410010300e40c4040c0c41500500000c9404070450340000104507000d41c0c40d0a0200005001049a0000000400035241c41c02c05600107151041c4101e10584d20740804c0410400d540d0307a9035a1824481813054020f400460a242d600192102030700d010312030180080c0f10b40031401900c1403040c1d006a1004d8030007407038500c905800b0090f24220407004540e00c04000b441c007050704641400514010002903c0710b5844004020020b020016000017007410001e8045080110b41c3c2d011000303103040340e00942c01b9110f50f10f421440c1405422510700588080062515201e4080c012140d034440011740c807030a0b01e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 600513462 1250 600512212 600512219
    0x30f030b06090f12031308011103010f090e1926040803040512011812020c06120f040c170a0c0905040b011e270f0501210501090602071b 60
    0x2000c4503408581150044010301000c421400e00b245580b410303603401440c400321034a110780d2a501d1039204080403c04c000d441d0004005000c800d0240e28000351a00040c0e904640c1092000224018244107440308180c0343d0301620074404091061100107848018401d000b2561030a0004d03500d0f0038251102111440115406003204000d81a28296a00240918a06482c20080200311201d070310700700c4100d5503035407000c0c059403e0006194140e20300c244000c0025001c0b042c6e020303007030003440c1030102d000361001c111406500300c2409003103603c0440a01001c6580c1c5540c00c2c4000d404915400c0803540e42e41201d0f2a0100500002c0e240e0703011481003906440c0b0b1900c48000070160380090701c0003400444000010f00c030110a200042942715500b040200041eaa1852480700c141d480000300015106c1054003011007110328000d80ba1000707107020090010b5490840711071590400110088440002c5403041c40401c00c0c290003c03c01650403000a41d12013040e0b041c0703148180000c40300381004441401000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 600514712 1250 600513462 600513467
    0x619020d030c0906030b030111070f020307060c050d030c170405031806070803010e0c07050307060b040507020f151815070e10050a031e0f320a0e011413030f 69
    0x42003549010f0f52910207007454408140c01800115403103a42c1035481c0c608440308084808003070410303240600100c501000b114010f040c00c00405411210803ca2040640004070f00009800203d006c1107140005641410318001c491a10203d41e04000200d0000184824041e000000e815021005040038a10a5286040040c50700c02c3c0c40005007490010310041003480003460701d00d6484084c000106181c419180c0d1040d0035030780300c0d4400311100c543d688a01e100d18185840343c0c5074400030500041503000c6034110305a503165100030b03507450500b80c4240001c90560715074580b00d814249140884104881c4465501d46e030070411201000003c808150555003854040900340e80c0c044903403265803900100c0e00301100500714541303c210f108007a803109101c94100c144201c0e003c4480949000403442ca4070b50014200302c0304020701c900c0828050444880c550720300136900b600050100c0002039491202580e10f8050465084401c10b540080000c1100d40d40d00b2003110314050f803180d95a00082030003110207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 600515962 1250 600514712 600514721
    0x609060e0d1104060810050f070804020f0f04241e03120804060605060a05133f0209131505160f03090503030709170d05160c050619020d03 61
    0x111030384032411080d81c0001c00c0005803220080d150103440400e07013a440c3c1c44801d15000907000d846c0005540c8400300202c103000f41642c15001000c0b8a01440641807940000310300c074540310526031041a5000242413195900d0340844904035541030400713604030700e0304805c00084ca6144510141c071010406004150010350020a054a5000383d02807a2000c514004a0321041e006004445242d0f484d2004a429902d900141402c45259991260784940804803591a00c1b0107910814900d480e040a00c05070400001c1d854035000e100c2800d8240600550241c0400c4446104c400307500310041c4828011550000007640400c14003804403000c0b07954410402404848003103a0f00c6520b80d4108502c1c4d0302607840751201e5a48000b072031a001c240e002980d11081d0460380103581074004942a007030304000b03002803800c046981d80754100240c0b03022035841c0350103002845245003680909100613817803010400080720240140c800980900d845405900343c4010000b240d003000e43c0036129824801c066248607019 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 600517212 1250 600515962 600515987
    0x5180708030708071e060207062c120a0302040e0c07050d0509090609040516090219031103010302120a0501020304030f0e030a02030c090705090607230d050301290a09060906 76
    0x3c07094542502a1181c00c3c50303400c1c0050b08040c210100154070007155150026181650040d200002c4100c550550b11940c0c1280041d9210800044068030038403180c00301e5062100711600c801203684525801084000303200d56000680c3c0520b240b024400340c1800b0700050080c2c64814003c8440c60a4480b4041d5800d00030b102d401c2c0d40c000c6502c000551039062040303005030014400c0c01100c410440c1010f43c0d210008207030300250300c107a030301061a5135550f86940c868500000241010445c0790510010031685100500010780030345038110070b100340008100030210010790003000031502c90500c0c0c0350042000b4800403141c40001d411036240e160514012500404e800c0e4000c0080c03401c04980c00900030407010090090051100900c164460703901c50350003c0c00d82c6880340c4058204644000c40115804421035041d41c4241c0c048412001c40c02d03007002c01c89040d20308040038564130b40d0902a80e03148200002c1314072141e6a602050b6059226006542003003981e03040c1e114006601d88500c012103480b840400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 600518462 1250 600517212 600517223
    0xe0a0515041a0c04060e0103020d020318060a1e0209030c0a0b03070305060a051c1103010606051209030f0703031104050a09050f01081c05133201020a020a0b0310030204051807080307 80
    0xc07017000340c070340034450019407518181005818080a003108004a82003110302d603202071400618501c01c16010700203168405140f2500700088001c030681074103080300315020a03d1300d80d4009481c1406942c00c00c40051907440040034582d48640f18288201c2581082c0d90000101c0d003840c0124180386000c50030074017501c0e00502032002c0388a2181c201d00d031400d20400b0546040d02c0b401c071008050380b402e004041c0544007540b40d49544d821000d9441c140c140c8000c0c44030f01d0541050002031100c02492080f0b0701800c0e014600844c60040508400050303114a07800640d01441c58a00006c04440a030070444c810094111086081daa80e521a152100a200791040603241b00d12242d141d6140107402804144609440401205032a00c1c01100b1151060200380c850441e0b0081d40404840203140216070f051081c40500380b0900d260740072035004043e0b4041c0700c0c1584400320001d0f0002034406124802583c0080003400641080e0b4030410b2003109480b044001400340c03010110f01c0407400011902441e9114 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 600519712 1250 600518462 600518467
    0x302450703090609080c1f06030b0606030a020c010203010e0613051504020f0405180f0702010b010c03031a030604060204140a05090105060c070e04061505190303030e0a0515041a0c 79
    0x16504034002d01c10310780220340c019541e426200210300300801402c0c1110031400104a4075040380300c0b40d01103404440400001604290090001038440c1c602241c01c0f65054a425480307885000a00d40030f4003900418000a61012000107a03800d41658054000d680941c0da0361041c03010541080207440c0b040324010820b0481840306140d900b0180e004007098805a000141020b880344006080041901103603e1304250311070901c0202c1c2084080540c02c100c090000704080080140003901a4034000c1b409410705030f41c0c000d420118100107400790400035000b41500c1c00f910b400d240c2400250040d02074070348450b00043c880411814003002c2c2c8801e480c0300502d00600381e032802e0200301c004ea120450700030490040000006440c0300301311007180518801d10010030b00324140c0038080064103180c3d000501c64011094904a101501c04446090b69010701c0e003c22003003a20b840c030b145090340d00c04008010348645082c103000c6989094031680500e20942c0c8074080d1400101d414802c001003903601742c4210008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 600520962 1250 600519712 600519721
    0x7031b0c0e06100e132a093c0e041a0a0605150c190606031a01060807030b0301180c3807031809090308060402160615030245 55
    0x19016110180303038029404105c0d0158044c203000180f500541200d615456142540da4031904290040041c0c440090200d501941010715200010b080818003510381c3c0262341e41c00c10303a1010100304000342c0540a1402c500c0e0909141c90400c3c0540c0400c02c3d50700000306401301e03000c1c40460044408441e00140b8003017030026840c52600c0d1607031100b80c55001c0761007050300402420421404c129141401000001640da20714188500440c118403040720071150124014002d0681000702079170422540c3c40d00041c03521200002c6801056414a05d035100d81d041020481006018150a41034586051164400c81c020b82081d45d42050480406140c0503000500007042e1281ca40203800000c1c06450920500390712071058000e207210079040018175640341e200d500281508114005d07000310301543d0842c42c1c07404c017039040407440000da800281803644134640d814156002c000e01c90301843e0000c11110140d030a204640b101c520485031500c0f80001400c42e0300150307400d082481030303004045604080083d030310b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 600522212 1250 600520962 600520969
    0xb0603010c0c080d0228020d020303130f0212100902041b09060804031b080405040513031b0201020c03060a0903110c0a06050f0706060603050601030f091707031b0c0e06100e 76
    0x40701072030204c071960a011251180d00310b5a20341d00503411502529800c12090b41d0000d0603c2c8070400c20340d0640d030041003804988240d0748880b401d42604445445868006440015030062080c81218541c0c401e5980000c090319195010b0344409108641c20040b4415100c07112005044400c403800111f40c0a001c01c100c16409004d9465000e40300b4030304500c01140000304035100b07925248055580c030102007024091418240300b40343d000036118504900007641540c00034200c001501c1c05030048100d03001c0c0181103900030070044210b81802810f6a41500d40815030030010404c0c00000e800040502d1106001003001140300c40754400054090740a0b01e00740001681c0d254001c2e900054154420480c1c1800300348240320703400103040c4070381c0c01103441d0070500001415218000300302049249050880c40c0099282060f107007030003c075080c1103a19801903007010341e613015603208080440001c2100340c1c4100070103950020281c80002424400c0c0e52503001c180304002c0c0c6090303c0c440116800e020076560614 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 600523462 1250 600522212 600522217
    0x6030c0302220606120608030309120c03090a0e04020301050c120606030403140309011a12071211060d0504030f050a0804061505060c0106090c050c030a0e18130b0603010c0c08 77
    0x10b1507803040d0030b51081c8211030115810b981c08100000c1900c00d002c3d400c0120360141e03100501f00786e0015415410031309403e51f1102c1301c00c1c0054121400014a27003240c01400d00c10740e00c144100801e94810503039a01000c0052403000c640072071103540b90600060f18500e400d0706a4644280640149000d650352005016580c1c2c00600240c007408100059216000707050401988950784c01d0001145c41c607103c04d07513030304d18084540080d0301c6841002e01b0140800f100140820480381403107941c41c031080703142c104200340061800c50350750007110000d61070b403100c84503800c0640200c0c82503503408252002d104040718039005a0b00440c000a480d000450302040c5213070400605104810a0100316036550000501242d0184400e01e0499440703050070091200c85200e90120481c40d4101f00b0301d440d113030f00a007a46911810700b8003c144144100c0074240b03900c0385010810000d540c0780e034104250401c0300c2c41c0c2400200a580440d464200c0c2400101e0505044c02820140d210b2034840d0650312100740c0e1041e0f0580c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 600524712 1250 600523462 600523489
    0x10b03060a090c1106060a050f040f0f0612050601062d1101050a140105100203040605030a0e0d030501031104110a0c0203011416020d08250c060c2106030c0302 70
    0x84844800402c41c400d5a00c5100f062509030307201e41d41000102d1a03483c0c14040018001403003510030b42d00c108031540316080030600c0217a044900144442c11400000010041050000768113441c1c18008100501d07650700c2ca00085000700122211342e070361260100d0f201303241500010002c5009400d00c42c40c02080b0b040002d5041f10f582170860b4014111010300c0c4c00c60700c080303495400c11500c5a2066620402c13140c0701c14098030003a20000300c8280507120180d5a886144140e5042250010008400d00f11070703441039a200100e40155405c140081c0b0b4002e0103440c0c00c3c0015a0f0b1100b404161034214982031181d14102a000400d8a041c88020301090769810101b61003079801d5503c1e5401e4000040740e611356644100c8442c500b00c4c6035410030355030003450114038030750442c103010941c81031001891515043c0c00b4488100050301c1106500b280040702c0801e00303a10001c0181d03007082044000580c224003c00d80e20000c80b80c0383c400042414050905543c418800a8211a408641803026040c601e25001c0c5a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 600525962 1250 600524712 600524719
    0x3041e050a21020405400803040c0807080d03110a0903110103140f01030b1303171b0a020601060f09030c1511100c0806060702010e01080402040e0f0102031b12010b0306 74
    0x414994010031305036441140c01c801001034800000c0c04100700104510078100440e0006043e94804001c919468160203e0117040b2203804030000d4108102004808040d00d800001d5410450b40c88184903942c503070745844600407904108075902c00705409000c1d101031003c0d580d00c0c80320542ca90b848042c0d9801c0c0d800356060400d0344075103902c00c000c0b80342180c04d401940042c121403042d41c0741d0b00b44480070400c058044031280c4844010603022079844892494041031303140c0302500c9502c2c0e0342d10701010f8020052005e50501e1b40814424801500401ca07035040b6003c1e52946610041d0181c02243c07600d4403400002d020b01c2500d0707001e0160000c8484035624400d15400e0040031168009a52450644c4402039001c8054450306469059940070030050b4001a0680f011410b10f01d0540c0040c00c100d130b120381054100600900090309540d600c0d0002c0700075080502c280c0c0c0d034103003801c00018084e5100316420001c0c010b0101290001210f560308548020300860303603481441c0d003860031402c2542c0c40074041c240c2c0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 600527212 1250 600525962 600526019
    0x130218070e0307140f0f0a091a040906050714030921040503010e2406090f07030b132007080306150706051306051003110f06160503041e050a 62
    0x540b510304220040140620104800c1d62010341010828456200b40007240074034004609154641c494055400954160020110388618861030141d92071100030075555006c1d0030100304500348141036110a0251007280e850f403e092505c0d41d40e000251009032121119640070055905000010b807c00340d0905c50381b2046070f45802c0c0d0300c1c0d00113401c3d41c8010300d0001ea45e0b0048c00995000102c400e0740c01c2001c0410483c00fa41c00d150800028800040c0180300241c0c203d2008000386515101740c2c02400d0021380213013502d2180f82503840541c0201103400b80d0f142d0306009240090703c40c008030020f903809694017140c2c451655403600288806204c0c034206200c84000c0c10321032040020f4150254510411000040d030b0f000b4011400c12500b0342c1e0f0090b080d9480c2d20038894043c0045410b850390011031442c10346001000e40203800c0401c049200700f50341d80d031100791030161a004101d4040000c10444881042003040b016200248014080750744c410a907005a85840070410366a2008410454101c164681d04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 600528462 1250 600527212 600527237
    0x31812030c01060303030501030506240d170427050c1e0d0e0105010512120301030618140d0f0c050a12090801020c0d0e0a06080403080a02040b031911131a070f0809040513021807 78
    0x1c0d82c0141d040303100d0d49aa2242c80903208400074199042c800501c402c00e00c0642800c00348410248100e059032070481200c91760310449420383d28111000d11b01e545204210131540311403200c0c0285400c0c01841d101e0030b109404045982d4000586800c411403006003203155902c2c565508004101e128038802d40300040349034813000b20b4507840e04040f4144c10040a0300e0240d850300402042c070a0414810700610403e200850046040000c50300a059805003100802c44501d61080c2e03021540303a800b4021560001500d40e480640104e2807900a50542d2111600441d9601c10010000d015004400c0061400c400040202c0c3c42144113a40140d4260001880c280d1101c1c9072540d650301c1200e28803074465642c840201d0303004642c0b049404001c6035810b0700d4201216013030002c00640307043c41928114401001c40da822030071450200c44e0620b030b100740010052481440c15404a402c280f4000341f28a241000107404054140a01564643c1c0217100e14445081d42100035500c9a0251511041080d00c00a8a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 600529712 1250 600528462 600528503
    0x1140304050102030a060e191a03011a0901050f030a110409021e1201110406110f1f06080703030906052a1509031812030c01060303030501030506240d 66
    0x1580100d0141c8005641d82c54400c48403400d80e2036a90041045030b14000c2009024600002c80c000d02c40e86041c0d000c501d5003a0000021803494001c000c440c2e06510345080000e00564070014107160920541c0c0d4a9000ea076218100515409880319407609a001414184d000904041d240121284001c1c0000b40c001c64075008a003940300c002c40040301000003e004100c09162901768188044640c5009001c1052141100066401148140000e016030841c600d60395220510900c0039000046085a03000580030416031400c0401c2503a0100395803604801060402c0007091400a8913015101c1e0780c01c003403030104100c1d030950100250900b00c182d03a0100c0b41405001d049103100186401d40204040c3c40c2106004600304030240c0081c00c164020001146030b058064500c1d00d00a03c2101c10300c00706080b04d50300c1030643c410b034100401c81d035282c030b000441090b42540c44281664014012102c503035481c044452201910b140b48a0700a50744245c1c00703412441c003415850072661140c80e03000c0148070b00c960360317 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 600530962 1250 600529712 600529717
    0xa0c0606121a0906070e220f1e0c0206060906040b1e03190209070804050703060509031e07350706140603070608040f0c05191401050702090f060114 65
    0x100c60111024000c000e254180041c1d42d41c001d00c1200241c001c030b00304500050091070080c03040c07c2c0542eaa4202010810707100c403845460040c5180810701203041c4059a0a004040001002c11803a0814541710039000091148118041a41e0000c06054440d001081585c0c1402004264465180c81000d43e1a8803040c1c0d41d8902d81c2e0000c3c00c04143c628458040504005260140c0c8041d10040001403001d6500c2113400c54004255041c409643c1e29181400c90130700e0b00c0758001402040c1020300380100c80c0f100100402d4208082800b446868084801d003080b00e116225001d0f00c00003040e88454056242041d20340140704a0040110040104040c10b4042e6000b070181035912130b0381d92810641c000c43d0000340c9035000c44104e000c1c0c50403d0900d180500b1341c000140000c0c10160740300000f40200301e451810400907240042410f903060b0308004170824100c56500811a181c2d64012002d0b8855000c0c2d01620003242d40204a80c010740e50f080c100526400c4001c00d2a1704120420070303168030303403501d4400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 600532212 1250 600530962 600530999
    0x420030a0b01060e0621070201021605060106170f07030b12150a1b12021c11130801020c0304140301021317070e04110603060a050a0611060f09030a0c0606 68
    0x1c0c421080d61401c3e0019000300c2c04140d0003130040104101010001183c560300342d0003881c02c03488034411034035000710480c02030090705990401c04c016030840c042884400942c0c14100e461a580346400c0b854201441d4040480c25555103480000d0070b030110340d00d64025000f100d20f008000d03144801a0316940c010034070b4210600018005404420140000e003285800361814036004802641c0382010019001803d01c005043c0c4085d109a0214441b40300040043c410030418032050030074048001d0007051002c46900000e60102008410400000e140a040c001d44000c080014080d50400e4074101c03843c80a01c080c110300c81e0341950700300706d1a1402c552400416010307103100040740303c2040d80a001a490240740c0d420070a80c5071708007010000042d014924030b0b0842c84050b900c5a440340c07200004138540d2a86500b005510858020020404a038848038680b0076424000c1140c849842e42028481207076070607107222100c0d41081008500701d6004080000907207120380c60015000d5650126890103c85841 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 600533462 1250 600532212 600532223
    0x9080403110f150c0f0c01020723030102120a0f090b0114120105010b040f090227060c0a2d02060703031e020703030207150b0f2202030a02041a0406080420030a 70
    0x20f030302042e002d00300030381c444a19046004045144480780040d581e41004d104040d001d0ad030400601100b0400148116610b4070081c3c001e548840f032290700080100c00c102c42406e0118036100d02200c0401890048410040e000328210303a4990070314004040140d500c41d55a80c0085003020304a4014009101c0c442c000c2071a080025103960400700c000c3c07101c2c005644400401c80c018002008040c2145614010340d00b40811201103010b054004503c1c240120304c8a00031710301415a43d1004e012140c80590b5000c190780c0300d116001206203c6102241d41c0707a00000c0e400890034015040024080e60185075071200d5041d00d501403002c0c0202e2030003a640942d00880c0007035008a1300c00204801c0380d11a501002c00148140710000440020500964480700d0140c0300d0130740c4004507649400c0710013403141c429000701c10a541d240b5020345824080e40c006c0c400c08080245508c80e910040940c182510182d54003551000c20300d48072504d56507500364900b1171315511031164180418640e98100704d1030301441d108d40d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 600534712 1250 600533462 600533467
    0x1b0f0d08090f0d060e1501080d05091201020304030f030609090309032a0305030a08010b0301081b0112060303030e0c09041e17030f04060b0906010c03031a06030c031909080403110f15 80
    0x55203040c1010740c40701180304415846c43c01072004803404542280ca05c5044e00e08a62605d501c1d40c0081d030b00034a04002400315510000034032051580c40b80ea0741541a0301e54905000d02c03036072000c988045944020780030300010005141800001c0d0303d11000f501c42d204c000c1c0031510320242400d41045001482d44212001d84c00014603864007900000f88900408041041d107045614040e103542d220000803007160074024101c240140586c1c01005da0101039200c8400800600e926403070042c004120380111305801e441403141070381251510749a00c1d07207e80d51010042d450768502803a802466214100121142c020032141001402d0081026511808820740d035802c69007007608028088600c014246030160100b50100165a60428840440b043c0c1c14a00010520b624990105520010100d410f5006c0c03c00410b10804500c0340d00654041d81c080c1244500c82c4280c084428125080380000070050041400200080380c100c01406031440c8000c1c1105400448040015411100c2d20a110820f000f02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 600535962 1250 600534712 600534731
    0x30f02041d0a0e060f06010503042d02031504170d1b080703050a05090606010c24021e040302210c0409050601261506150c1b0f0d08090f0d06 62
    0x6000d100103014418010349030700d045c07010183c0b04003840108000c2c184400007004c2020084a00000b00e07907540c50384403181c0e41d100040644e883e01c076074009040e0321030310504164188030707483c00b121303070340a503510945814410401484001d102d0b0440341e003100316143c2c0d8060703044074407084407000500d0906981d10340c1010301d05924040d00311400500400040e500d020704100700c0d4600040c206420581c00d0030540c44210541c90400a41c0100d03200052164031002030080c91815140c000e040002002e100148001c05824510320130703402248406540305a0441004070714410650500700c498800344242c0316140c011101040c1600d1207204121000e0b4440c1004004401c4084882802140964800d142d880100152142d07524809146030813403403000e201044855a034410034000b4000201c000f50340340ca106a80b12a140d5900301d1100d17040500540b04030200d403800484d0b00c4200c2c500100704800c065016110195960030080407a50800d0310300c580d00003941e0321407904c000c205225001c0861410384 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 600537212 1250 600535962 600535981
    0x1502120c030411120f160f17030406030f0f0c08160302120c0901021501170c04060503030d0b03071809150b0616030e040603060c0e0a0503030a030f02041d 68
    0x4010840100414180140000100c4074a04000d84290440340c0030100111084e5507810840829420400c41c410340d03400d40000c0301d1400881003102c80044141c04099640c0400080e00d50074005000b00c3e40d0010081400f0b0030380250700c500000c1c4a0558001009103001c10000c0850f402e104000c00440c10b4074080000c200144488ac01c8011a0380ca800d608181900040c0c04141101030280c050031280031a1040090340300f040b04044044420544c0e02c05540d48128400d0b0b4210b021081d100300c4d0182da1070140560502d80149003c82c0c0002c1e008520788200c1024400080c401e0190103503250044c20030000c0d0407280e40207a22104104140001034072034031440d214401050420b544100d050520340c85036415903c0c44c0503110084c0f43c02122a2103c00145012034100e8164214580e0042ca8001d0101c1808200c0e4001c14164507103841d1001020520410820144111301c41c40741d00d42c1c42009100b42c1c461080d0441401190f507580003504040c0c51341048241c0d410070404c803401c4500d07200d0400c050000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 600538462 1250 600537212 600537247
    0xb1612031505010f1b05150408030907150504091509060b0417151305120712020d0e0310020901054003050705041a10020d0e1e1c1502 59
    0x2c000d007410b0095600100019210f41c0103800ea100c440291500641c06100302480f100200801c400e20424441c541494080c200350001d0714030303040a200d5080b011801e0091142004a0072030107454160805150860000c090012010603503241c010255001a54150a000d0407001e03081c00c0c581d6035100e60920803014040801801551150f070701001039100d404130903180c0c0c2504548851803120b0300b000b940c14818600080ba10b412100c41c540010710b802070180f20942500715150a6007501c86a0044c03803001c0302c100f03090504240e40b64100460240350303200658001d081a00c410f0408070306011812012003a031003a500c850809030341030480d48560030017200f0405060181c62403440b0b030503623007141c644550310000c6002d0710b07000c0c07559490308408d5140507002c0142c0440c0c00a007010034484c9200002525415880c1c1400301040099103000e4592804200490110200c0110010740d51400c0e0708001c01d0141e001000048030304009400d002040911038070840e800340c11180980c3c2c2d4500c00c03a10700f0046 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 600539568 1106 600538462 600538469
    0x40e04030302030f010506120c0d090503040f0e0609040c180b04020c0106031514060910050306010e160507050c0405040c0506070501050109110406090b16120315 71
    0xd81e0640040d0b11440c09a240b901c034590f41c0310107009079030041c0c100350302c010a6140b000905c43d144920151002040006010030001d0716516883c5c2154081c1c2c0180c80708280501041c4200c64446c100c80b0b0704a001992984401e1a090716294409048c40c0122424080031131136400540d2803a810818a400000b01301f1955039515081242c000c164030300c0101d60500a0000e0b4681d101c0c11489040e02d01c5608050700784269860400308100048002c140a107412030010020405071010044a406005102c44911041c1801d146034840c004004034034404200d4100720900020304041460030103410162408596500c4e50310304049160165040550001c2d008600384041c00815001281200c0040c4000c00102410701c4130182280705601a80011030900482040084048401402d030f00b039540d00a0042d510055440c2c0c1000000c031030700000007a0301c550784c07200350780154980382004 = true := by decide +kernel

theorem cover : BRFrame.Cov 600359712 600539568 := by
  have h0 := BRFrame.cov_init 600359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 600359712 ≤ n) (h2 : n < 600539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
