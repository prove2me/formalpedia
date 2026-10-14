-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3732
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:31:26.621801+00:00
-- url     : https://prove2.me/submissions/da369302-4dc4-4264-8dea-4ef9977eb6ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 671043165 ≤ n < 671223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 671044415 1250 671043165 671043181
    0x3050f0d05160204061a07060c052502040204030f05030a020f0309010c0f020d080307031401090c0e061e130303030e1c0e12100606090b031005060304060e0d03051914 73
    0x102c0980c100d801a40301c00000c20028103145101040d0001d038100c2e43d846d1907150820000b079558100110041c4039040001d2008031500d07581107080c10546d400026409011403010400034410740c1c0c806803000b4645180c403400c1200100083c41e02d00025803c940d4950082d02d13010352203114102c20720780405e00413050800058880d20280709010b0008118014140154a031402c181d4021107071840001da5500352841000301c0b00d0403407030141c072010500300010703407032410003820340c4001c0c000140c4550340104143c04180c1c0c0c50100040002d100800c180d4440443c5101a0b0740d00c044c1d40401c402280c1008120400030b0400510043d40700b9840c1040b02d0394660b485800d54030310207003184203500020545140c40340d1000410030411201b00c4040001a414038040009086a0b4940c01c610f003e480101300b0b100720004100c201500b52a070841c1c07103554070f03100c1c2c0c0f41001c0100030000c18400725000f854983c55101d40c141c1d01c600d11800102d00e0103c44406460f8101c000c589400c40403400e02100355012070404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 671045665 1250 671044415 671044447
    0x112050f03220b0f0313032616140f09030712030206160e030705040f090f1b050303030f0f180a030e040e0d0503040f0501020c0f0c010f0e010806010c020a090204060903050f0d05 78
    0x1601902300303268030340b20b0100c0030a42071800c106030030604052035052181103960303204042e40e1613440785880a100421130324030345070901c00c990260008120114441c0c01d90b56091103e500200b05021860200214030301d0b01941303410084a0280200c2408840c10042c0c41c0107091404000c035006016214841c00c00c010800100300c0107807008412541c802d016400a0720340456450680c0c0500018107054034100d075100c41ba0000c680159000c0e070010f1007484005a029200c00d5009820b10b4100c0c141c0e641ca90350700700c14000e80902403408500c5900f40c1d04050540100660b003c8240680d41404064804105a42c0c0c03041c1d681141d000080d4208000b0f0089001d0040c0c3c4400c1c0c521600c005480c05c16016076240c80c0031201101d020880d08680c121420f1980c00070700010003144141032440320300c5000c00c000b919030440141190305020b1019100da0440da20101444080e0285c02001c54840c0d85803c001021401c007404101c1f039074410004c0d0b485058000055010003040d40d030381d55510b40700810701d6840070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 671046915 1250 671045665 671045701
    0x260405060709030320100e060f061f081f03080c010510120b10050d140c0103050f01330207090605030a2d080a0503090c04050f0112050f03220b0f03 65
    0x2d1401401d125081b06200d602820400c03140700300041007a400d010b14a03503445a0042c1ca00c2e40b0860070451118040c0799213030921085c045039407c4c58812551010300e51401134100b80881b4045400da13a00c0030081084c1c41c0040d190303140c5150004c1105548041c50000441d9132400340701702707540c807544840001900350340781c0c140c0c09080c13190b11141c4107668102140a6410014049404035691481c0311984901041610b0803000c09107418841c034100a014070344c1c4200c042c018450902c81d800c4850643c4c4103412083c2c07600301d046440c181c00300c50804c0d40081d101c0c2424041c0c002120f0500c68009801d01d00040c2c0194880e8106400408461002c002260501a1092100340031002044180c0114084c0b0700508618951511425502e14020200307034101404020f00d18496481c0006000d03601050000450650314001d21003490207410b8185245040645051800d1034400011450040d212030b40f203084100801ca20080c00190b00c030303040034110303001d404031200c7e00c502c003030002602c1c001d91203050f070103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 671048165 1250 671046915 671046977
    0x71403030405180f13021f03020c0a0507150801030b0f0603070909052410090507030207051c0921120306030b0a060f06020c150306012604050607090303 67
    0x200d820b50b501d000c51500210f0070ba0300030410444104000e40d48204070b0030503900600c41440316405020030341c005900c1d00809121180404450405507412a000e941100c00d1480c680e411104140414030300b0036502e10b02da000c0c44902030400c1e040d01c070354980101c160505980e441039648130a40c2d01d0b6800c81502140c01403038968140300f800d6000429070814420018100d000300c0281c40c2510200e04400d03d4030750805040c2500b403400f1403c01882000341c0766400103403482c0c134502140075180c0480480103409281e4001d0114029040614205205072991030040223503503c40b56101660361501030703030400445000400e40c0400300d116900140c041441c03d04449070702e0400080054881d00c0d001e090030f81c22140700d910903584400c1070094507400c3c44804010855031009082c1c1010007401302e00149400c024601c4242404008100b15030b019011407095810071007200b211028120083c40c900ba4401d0b00c05075840d0184a011600c1244108000c1054940503141c03100d10381e4410904280052a842d0080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 671049415 1250 671048165 671048167
    0x180e0304050405090a0c09290f0409020f041a030f031e070c1505280e060906210a1a060406080a0f02031e0906010311060a0912060c030e0f07140303 65
    0x50000350300c2c590b140050451107e00040c0c04402030390034407585c50503109075400034590b14000c9405075643e5150a82e503190a68010a080c1054400710b00ea000020260560260401c9a003070f1003c102d03901072034007080d42281100e000451034120262640329240c41c1f07081082000311a80c01c00c5240340000c000c2d451040c0f90302d0403120360714009084403552400b620800030358001003600c0001d40007114010b601c0e2100c0364035003101e19401d00250003207240d0717241e0a0143c94040340c1404503644880507a12460000c615010003508452461440c1450440302e104226207080c96119074203619400d82c03003031004054400e6260608200780ad64039440018001d080d20307901e85842c081c0c8c105031030001e180602c1e43d00c07400035096001503082c6004800001c02030703100c1d0b500510040010401000f8500010a4151100b660703d016480d4100c5002c0c10b41e40216400314113103014841004240d500c018a440c00e40d0380c0c1000b0000882d00ca10382c0301ea2556280c044968060b03501400750100c04e05034030002e41801030450b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 671050665 1250 671049415 671049433
    0x11190203090306180c1e0f040e0a06060e0c0a1b02060c0a05030a021203092806051302040b01080601120f140a0f06060c03020307031206090213180e030405040509 71
    0x1a10f420000c4643c4111043c14074200d031400b0f1001c00030810313040d80803541c40b00140301c00803442c0d0f8407042c15641745124056101540341c2c00c2d200e9a01070414124068103960034442141009800b5080910415a00340100400a0401c42c49601a540548106d0b0340341102a045940360405906451400b40d038000c0c010800624804010040c0d1130a540c803a901864554900c018040d09180314202e2103501a00c0810402041035008190703a400b1000c1d81100841800c1d03c0c40c0d054450700420030004049910b41014000f0700c0ca020701500e4510381c4200e9003400001141801120408403d80d03481e4042503004803011100600764000b5580d0955900700003034540160310441640b07075000c0c0c8455503525600c580c83e140c181114040d02d0003500d0f840c10600c0c2d9031186964000d5403482840d030007504000e00e03e8072000c1c401e0340a4001000810b0070b030300190340b1404645410464000184100000c200d41d8001c5006403c0303180c0030b003100390074008002c5d40c00c161030315007440054800108509868040d00042d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 671051915 1250 671050665 671050669
    0x40807140a200109030201081906170708070f051035100801140705030406110301080c01020606012a0609020325060c12050903120418050a1119020309 66
    0x1890154001c0b84002c084002807944440d604400c82100c40c10481d44103000c0c00580d80150107940c200001144401c4526a0172402d01c005152a812001420600c0380158110b18000200542914124010340714042d50300c500c80c040d195101e2284a81180000500001c0b4900950150f440344404513004140c070611040966044903014000242030300240040c0240b0100c2c802c4940090451000200040b1a80810038001c0c0500189007900b00100000040c080001035002001428040d00c6110303147d5031a15042c0d6100c1d0f1508003414018400c01700026960b40c81110042d12030365281562047c40d042603001c01c51908c803025801d940d181d0701e40d90f007840161420001030890b41c0941c04c5c0b04001500034555502c1c50001076224500b0410384220346008180f0808a5500344490390600541d2a42c01c5c10101e4144489040c6a00000c40013007400144c0104180e03c00b2449403103030134208082d56500b80544121001a00020b204800902001c0d60745d0307003c402116402c1045004480c140b80413200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 671053165 1250 671051915 671051923
    0x30926030310170a08070f0302030c01110d051b09010509190324050f15010e030f0d090b04080709180602161e050d0318020901080f060105061204080714 67
    0x80050078039000c803104016900c001042290481400e00184c5000c2960351510b542c0c034052050003500c01920414401c041500030011903000794820b00003031141c1016050f82c882079070032040c0b103411101c2c1040300107440c0824441d03180c418118001038060500d9050001185d00c0d802c0818102c0e00b0280340842076002a246002046c006e6214040e05030a601740540100784c1c0c010b03000000f42409007000240280f458654000c154072940e64162000b0b2010f80c000100c2c0d2802002c503e01d80c0500440218140d44840802c158030403551688400342e80c1c607514900d5072420b11681c810b13440c40d50408078050090642a412080c43e00003803aa140e4040c00d80360716581c0403030f400841003080240c2840e000000300325075681d01c003c1349110701c5010100e000c4035440f030365102d05200201808040c0d840550700110707030805260044203a0054111441503031100d18040e0350383d00c0c490310300e203191080b1400001c05140c460210f6011803008800044180c03599a0340181c0346d044070707004071001c6458004071400140200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 671054415 1250 671053165 671053171
    0x1905030601144e060f06120403081f0909030e060d0603020109270b2b0204110309030730020d08150f0f040906060602060f060a030309260303 62
    0x8a01003007010360340c414070091001682101c82c140071140c40d01542846400c800c0006a503141c3c200a0400d544581c0041d0054503d80c42040c0d008102046503c8071405028009101c0c0e4425181d85d00962603800225180e1030b0301d04003010b000c08110b202071105100ca50403c424051180c24021075805a100004002e608030321003011a04e0754500c6c04200795a84400c0c400d00038541440000400030703102d840c03500041c01280308030364585c2d01e0300720300b90054603446580c80c100c883c10213800d15540303040c040c1e542d01e01c585410140d10440c28000340300507051010088900450005c002180340074aa42d0340c0e400600b603c058910190031050000150240c05020001c5449440794060300d07090581d03450141c540c05010b4449013000311029000b9210341c0b07502e404580c03245001c41d4a21800b0b04074030001000340002c1d8400900c1c003410100001040d94000070103500420201e200d550295982ca41880f80d9405d15100181c00652690001c110828144860400200b0354414082d100c16000f10507070700d164019 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 671055665 1250 671054415 671054437
    0x2040507020a120e010e04090f020a0b270904350c010f060f05040905070b1210060305130204181b080c0420131502100b06190503060114 60
    0x600001403c2201880c0311a2040c085810321034901800ca00c0005d00001503105c0450259a5440c5040b080c044505920555594001c02940001d500e0307500804440e00f0982d50b8000c04455115040103007880d0170000e0800c600042d203410340300d58a07926040c100409007982100004554800c0600c103400d40010030310342010018209503541a0300b5100c500b1591746445c00101e46184c07903403e010044036484568125181114041003030f010a080c120706040590b8031489890300700150111340a4501125184142051881c00301c5543d69a002542950801c4540703020018901d1043c2005150603404405d0450010124920b0b5100540c0d40701503522810300707004032424860345c041001c2001000b504050304000d90f01808a010062111800d0140080310200d82d0300c0702061480c1e03082e0900154034001d10000745c803101890302d04e000217512020ba014491014038207010502c1a2800c00404940c1d1304800140307001003800e07403210121002d400150100c0e04000d550031180007507940311070292014101c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 671056915 1250 671055665 671055673
    0x4020c19081b031206030a02100f0504120f02090f0705070b1015020f160b0d020a02030f0409050610030605030d20100506090a1e0203070c0803010b0703110c0f0103020f070204050702 80
    0x401282c05a5000700a04803482980200c2d41f0f080180c5a8042e505017004003814006003400080205480b00e0003590008103003130442e009480c050140425104c01214001c0e08d0060503a1030704824126045011280c40c008600f0401000000403c0200c1641c2d1085c07990070f203410840d850305032000c8d01d01e0109504e000141c0c440300c813002c0c00107407e2000140b4174803a8011029001d02d00824200c0d5801041d03500c40030309501143c0c08901c64020302c2107070011a4051100740ea50350b2900d40324001010141d0740c5030b00510302920f008803414007034428401903900040040c048500603510486070a4000000380489080100c44030071080010866019061a01031003c0303a54904001480840c103002402104141e0406000d00c14038006a0710917240c180c071880300076a81c0d0b81c40c5a000e64002d410103030024020503000000013042e010480150450502c00e03039400d07110485281c12a55910005441182d201f50f40c800602d01e158003030350044c40070010840380107080074503a8000400b141d00c1122000c4c00350300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 671058165 1250 671056915 671056927
    0x2030c0904031d0f01020c090a0b03030a1d0307061d130510051c02010c0311160b031f2412060f0e09190201050a170a0e0c04020c19081b03 61
    0x283d400204000702c08181d4481d00200c16210000b55100c92081d121030040c003a90380800c880c5451500b0220014078058122680d03400603030001042c0c9104030038040d08c4038600c220607034480e1901140c0c40c401c4851a90710513002094514020340c1c000742c2040d01a500140001c1013a400010501070710b845550f219030150740092a04080c00a8000640b62400749121800d804a0050f038001c14000b80d0300d50580341042d032401d00b50346858036000c03c503540804412070b0310800013031001f6044015880f40030002404020007003003003070841c4587c0c16070090020440d41800b186200c20076041840c1032414052a00201c2d824070400745004403031054204181500c107a01c014000e607108001d906400c01e080c00010b1006500047e18045034640b460070082c1007040018240748502c2c801c6010400e03c050410300d0f80440d0600e401c4500050854895615407400741d1640c504482c6810f20a40d40315010040151980f2442000c150305404038206041b515a078060059440c40058440e4401c041c2c005e681c0150395541d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 671059415 1250 671058165 671058197
    0x504092403111921050312040c05041805122a01231308090414090109050606040c0504050906180903070b0a11071203270b0a020408120702030c090403 66
    0x22030f40c0909641c00b404501000c1168004c040000d0710b11038003c0d403c02e40d0f01942480d1081c04c51003003420254910454405200c00c2c00343c034901340341c12210f0071035042020300c100195200010034a0600a091904242c850421a025040051101410003840c0320f22150721211881000e0f02e8490a0300d00e10307075540220620b008007580a1000116480302d103500289031080c006070001002c20002400043d000c61011260f44441c1c00c0f17407800725200e16640724146440c1d14520b0003082602000c4e1658440c91001ca03545041602c5600e0442d10a42d99262525003841d0034404040006070400b50800c0242000001811300d0426140c000c8285a010f90368500c2241040c4440002c05400f0101140c82d01d0185002514080c0071926025409030b40e085803921110410b40c02421240303841c0e200703405880607104192415040d020312003442041d10840b031741c40d114400400c902a60080443d80da000d0500361030a0502c55002d4072403a44028211103021b502000402c009003010b460440100e841d4a1103280e4407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 671060665 1250 671059415 671059429
    0x30331030306030510051b130509010e040203011b120510030c08060f1e061c02040501300b07050c03130f060f030b0303031f1a13120201050409240311 66
    0x104000c503200348a581410300e4180d44070347c400b00042003404000038001034803080100180303004000003000712904d503a56000003005100101c4049120b5441c003203410303e0a0705079040078945c40b0410307511740c4008418201e500c4020030002c2c04c00c1d95030618a90740003000030f40c4d0881807009008442d0103490306082c4011021291312018100310840030200310010b40641d00424542e6202500700d6505c90010703800d158000c4c08400b44e14000e0b4002c0e04200021030102d520310310034100c1c3c00c9803075218810b0b400200111950411155801001d00c4548000f190a29109001414180d0405409e4a1401101c1900007003035038810f034401006000c070000100000c13504450303503290019507800c0500c091000140025180d20009001808444000111142c1480c54100540c041d02c402e62040000e840c0b00c250000c019005041e461102e5655004082081160a400c60707906650603181c6a08190a08409001411000c00101c0d110010980440c0000c9940e0080000550251125a5400c40a0805d2101c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 671061915 1250 671060665 671060683
    0x703031404060c060203150d0302060603100b1011032203030806060c1e07050307080304050f2706130c082401120e0a0807030302030a0b0d050303310303060305 70
    0x10003681070104102040e0080c0e0042c043c80c0e400000140d9959520b100049481030320200250004588046581016000144603000d010700703d040715010584c0d0030b010001d442c054441c46400c0740000480c81d44c400c0c09103091140d600c003604c040d81d0410f0070724040c0c1000c010618102c001c01c4264540100185a0080111340c1c0010081e103904c1e2510074a403482ca82d4800d030000014088001d00c42e07600482070000d101c40c0018100003400d40e002c80e03641d03c08c6c1c95031307a030001d0040038890a07849181941c0c618000050900c5900b215001803921502d28001402e0901d00174843ca402c1000c101e06c442c102c010a110b60000001c451b00d807202641095440141000850304103203d0a1081b4000409246c1e0481e03800c031152488141c01080b1490042071240c01c1900300c1c01d0051507000c020900b5420903800d034001e144281c2c9080802c00030710f20010100500f016200342c000e03159030400c001003418481c0b0441d01c11031014160000301c8070b030f42d03480340b00c0790f00420b413403030f00342c0c0000d40d10038081c01000024498149 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 671063165 1250 671061915 671061947
    0x9030b0f0403120207110904080c16050a080a120507150501150809071d060402040306060b071202010c050405040e12030a1a0d0309120302011b030608210d09020a030212070303 77
    0x1042511702c0d5210840c1c20711103206035100d000507a00080c1004550011114400c0c844000e40d00c0910030740c1c0c04da03603190030b0714044d035481815001c50105854800043e845001e64200c03018004204405a00390307030660140d0000d441e001020000c504000c0014041c5600810303181c0e004170100c9a0b00c42c1d004110000c040c0c02086c0c550000b61081103228540000580200015480c3c003090740c0300c50000500a220b2070740010030281c00c0440c0000c045685001800409000b20389a02004408020881c203d811040c1660045501404144142d041641c0512002000d00080760907008150890380c410b0381044030641c59040c0c9410070005100510070003c0d50030001a250030340e0860f080d42d0046c01c04070b114001c20b0785c1052604804014180300b5003011004030b41c10401c40b0710302001e1070001800742145010f00e034214802c04143c0400c603642c03902c80301140030140f15a24109525060a0006042c0c0c0300c0003070740d2105a2a9010001d0f90b1000e1040c440c0b09110720041c54498a140741c00740160005989180f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 671064415 1250 671063165 671063167
    0x90f0603050304090b28060810031e050307060f02090406080102070b0411031603110108010815190b060d0b0901050604081504031b0506190e030708030709030b0f04031202 75
    0x24074000150340a8403000040450502e00d240041040f4865440001d2403041c460701440c01e6442c0390400700001d80740159580d0a4580d145004440c0f05012880000d0200c440310409400b0081e80c0c80d0400d940038465400d0b41c1c548140c1ea2184401d80700074070000c4085603400100035003d450305120f00c0008201e000000e60410806441c1c4241c090801000503005100d0903840211956043c401c5040300b0700e2103204501001e480e4103000c00c00c40b0750f01c6410303404a0b1b0310304000310b50100c00191090310440c4860945542e03660304601003601400d2511003c0e04584c842d1410402944c500003e0071460a000200064034040c010400c0b03420101a4480d03402440208014010050089035051244445800410043d100c610f01160211a858407902100e070051070400108079000c2a80d81c06840f110054400041920b5004012640055100c4038194000c00c4040c0009088802550b841a12410401d101c43e80d25110000042e00456211205942c0b0034104410590403003801c980c4000041021 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 671065665 1250 671064415 671064419
    0x2010b0f03030304020f0a0e04030e1005030621070803180a05041b030e03040f0603020315030601050105040e091e0706020111030103110f0f030d020703032307172101090f06 76
    0x3081e101d100140005c2d00440100d41c501e0070790b45407980b4180007840313681000c0300146000d05000380031080d11742d40540700c3c50080001207540340c4903405890062000a10320b6622900f0016041540d0340702c0c012441c5240130700d000004207010148040c0c0515046c0440710000c0d40d94103010800e80e0095a00314920441c545aa0504040e000000d050140e106c1414001101410401c1c0d0070710f10b02036a8820b0340f02041c1c551004c1a081c0d416000386005500000034012443c1d0324074205615030509019042c001902404100040040d0384060b540102c01d10040c0c1c1c2c50404c0c48040382c0100c20804181d800180e0241004122156092046104010095034100e00b5541075030b030384070003c00300f400001d40705000103c54a1015551003100c002d04060041c2150b4409100074400380d107488061006602107903801c0344c0c0521140c24034000d4005605c0e0f517985a032070642da40e40c603a08450144038010300c90400c103218000c58101c583c0020564003098211114144d0b241099500a54102c06000c060346800e025003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 671066915 1250 671065665 671065669
    0xe0d031401081b0126010308091f2a0c260c0a05011202090405071e021516090e1e01080a20010210060f0807061e08070c0f03030c02010b0f 61
    0x104a07081d00c004d1a01104250250324420490304d4880b5005c1000c40e1080000010403002c00002c19540c4403c3c9d51212115031038a611001c4021503103205008100308010000032054842809006050500809512220161201c4c810b4402c1a081400c01c5c1d001074500380842d100d80007007403010030704c01c0c00140280c603000800305482c100346202c1c2070b0500081203169140040c464064038500d000241c01040b0514180c2c4c1c2c01040d0110912444180c050b903480103441061010650582e50015480c100b81da94692403080810302d0740d0b544412040289820b00480d04003210a090b9015a0050b0411000c1041001c103018148406a002d401968004910340001071201006a00e00117030480d980340d1841004401070f400d1101582d203140100786011008560910088200410750301c1200484459540b01c56064885c00f400c581d0761829403c1c018a00d0034440c3c810b048841e44950945801c20000a841e0342e1007a00c80001402100401d45495804d4802070f824072403010342500031500c844641002d400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 671068165 1250 671066915 671066953
    0xb060118060f0507061d0105040314040b220503060f1501170703050408040b040306020415210b01032003070e0337020607030203030901051005130507030e0d03140108 73
    0x804a41403043c081108020b00c8011303444103500150324098036808140e41e040160007454111011004548030f0098000d50303001610581d0281d80750b10449914100380601b103038403030080e07610392101c11203980d5102180c251420711549005004001590885040100e0140c04441c000c440b03a504001104044c1c86c651400081c020303030020403900380001c02c0d0b1200d041500035445103410014040c500094004100841030f40100103c41d10082c00603a920a0508100c2d104400b042441c0d00d40c00c00300710030608450565110609a5a0504001444648400c03408810b040a10816040901d000c41000a915080003491030780580860103001011808034100d0302c43c0c80d200c18140c121095680c440d40441082041c2c1406440c0c004004903224802482c000390f40340e1003120604a9542041d01141b407103030070115040190b0340c0c000e082034000300c160507598008141c020a540304050719140740c1c03000301006002065180c42c07555004030b01e1890442c0036000c44181a8008403450b03010103180710200c840e0bd0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 671069415 1250 671068165 671068187
    0x304020105090904060e0f1501090212160207121401142202010c05061315020903070b0703021603061505060c0c010e120318090705090d030e0103180b06011806 70
    0x441d0031480d510b441c10800c2c01031402103004c120602c14039400d41420440040ca160800b0016200a4030984e283e00c40ad5090b40100b10291142c1101c5001103441e001c1c2c007943c22054101c60344119400140d540d6650b844985035030005031003060100850345100d0100303008030000c01c802d019003d001e5061007084041c03000740840c00c06075400650706070603003168400d01182e948660080100c3c1c44c942000c500d04c14000803108000c84000100b80d04800010180b402900c2c1c010400901a0004034940320f20207943e6807240104404600a80382242903880e401c299001c0658020b400000384032986001c0010030781102d0700301301d224070818008007000c22400160074007148004c0c07038a0141003041c540421500040c94101d8680381c00040f840400b10070038520030a80d00c0104541822860300e0740300c401d075140e11400540d075400c10103000c01c2d140440d004603d40c024441041c900003401c01c04424418030b440040420441d01c864500080c000c80d5030388001301020341941840f8500d2030614205c40030f0800c0e0418 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 671070665 1250 671069415 671069419
    0x150c020601050f0607020405090f011b0903120e04020304050f0609010902091308040b07030f0906080c12090313030f0c061b200904050c130204210503040312050d0501080102030402010509 82
    0x1c0743c4070703415601e40d80107a403c4140d006c1d00504c00d500704006055107543c240d0322240059840c0183c182c580051703030f0400e40014461916039a03007803411600c0f80c10f14600c41204a00501032070040741c250b5611248000c6100e54042c41c041c0402c0142a0001410701002800039007035607041817084405a910751121580000c8408032090014100f4904010345004580c4240d080e030034041442014141c01c0444660484125982d0101580c0c9541054500300c400f0741c2c44c038052034030611250308044164001c82d500080c1c02c5003282d04140c41807803d000d2110042c1c20840b40c8418010341030007004800f0041c04042c010a00340607002000e0354010f8a03d0044aa070301501c540c9a9910802c0c1c03c540107130720074a4003440507007540220b28247c1029961400d0072013a043c01241f44907004040c00c4031910a0710182d41d101806190980610007070620300b02d0702c07408241d495000402001000a00501108000e990356845154551482070030f05000c0710b0301680328014607401001000b0051307034400300329040d003401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 671071915 1250 671070665 671070679
    0x9020702030f0a030801030b060901030f0b100519031a090a0209041a0a02030402100f021905072c0919171e0c280f020d12030504150c02060105 63
    0x149000003840d090000a0150b1280103d400007002d16a010141a040e01c0c080c180c4001103440300e5050004481003444080c1461071107004907000289100d4075182c00c1140320522400860316540041e600e40b400c07a10000b4244160302041041013488200c00d0b02001e100c06000b48145040254551038000203c002841500500001810420010072105c00f10380c100301c0c20000c3d8a8030070280002540180e034103070b00c501c40caa407507007198520404403100e4010080e409000c3d4980d003030303205480e0840000c0e0112024095101c0100b60039001113582c55146540d040c01500020310712503011011388015141e05500d8001c81c155800e4501604c1c008103c460740b104062030788840790416005a4050407142108142045e042c0302034101c4000c0c050004024840161132502800c103000070b030781c1d141000750b40b81c0c04000d0943c0d801c0442e49401204040724009000040d56801035075542540128400c0702e140400d60728001e10043c01554201c000422030071030700c100300041c10b41740003a40d80c040500c295845030760 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 671073165 1250 671071915 671071927
    0x24050a05151308240609040c09050c070b0906040c050d081c06150f02071d0f0705090d03020d2c0f0102010f0f060302041503031d03280302010e160902 66
    0x1469401100100b1980c3c0a035945030060301101c08100342e0228501c0d0f24030b140c00d000302c2c116290100c13000f03002e20762065031000f14030316040c10000a40402400080007000910184010803064074103a407080c8c0200001e410540760601d801d800d41580340e00400e011f5410b050070f00c400210000c04071600d030101d0f082d2410580e00c05101d02406800c00f81c00500000400140d50b05003d500003100c05800c072455000daa698a85401010700c2d450000a4981010b85903400820320b4031840c050364a8011207103181c29071900b20ba0302c004c10080020408200c00584c0140308030a000d82d07021a0b00f0040d1000324104411b83e01004200200e54024004850301c2040740342c04501c2c56a000b58010403841e07803201000d00445d0300d1046400001c100511041c0e004904000c25000c00d050b0b520f0004c0242c0c1e9142d1a06803403000481c4031070020741614403085400d442000c051050b0301e403005801c0326038a0700d62880404d1040ca0740ca0001e00750b0380300c2518101e0b02c0c2d128501c002c0c2c0d0204115520026681d94000040c2c4a403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 671074415 1250 671073165 671073187
    0x20d0302130f0320010e13050c070206120106030612032007050a06030b030f0c01141803060c180d05060c0c2406011b0f02060d02070624050a0515 64
    0x12078076900950356907403002c200100b000030f07000b08401310b10440585000600303092001512101e6503110005c0c0e00141c50b0710b80030710003800340d40300981021001106d030b030a00615074007041046d8000c0041103070840b046401000250307814007840000e000f280000701a80c0d0300380e5901620090880300007803012045020f00c8440c0300003c0000c200140b0004082c00303151651f0f020090000d201039141c00740240186440b002c4104400203c240c02808180d4904000d842c001215092503004544402d42400900c000e00d003250350100030503406108107901c040d584052036440e0204808070305600c14001c90101800c24003069011a070594020003c030706980e42c8200e6050540c0c03e02c0d002c25003851003842180140310742032a00d0f26030a40705a10a803590210012206002c4050454482000f005120404c00b81d900504100014110514a010780542000626174030642a40d00c401c11900643c001c032658401d16007002c3c404a801002c081c0c80b018401418400850840100c4050400c10340740c00280350f004003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 671075665 1250 671074415 671074447
    0x601062f010e010c0906020d05070b040b061504150e041404080a030e2b020304030b070302070c03240f060b0313020307030f05031c060608071103130b070203060f0403020d0302 77
    0x50340c0c0c03400c0200684200810040c19180e028051b440040c0b1030040036400440c0500c0480d003500d03800c444e641520f5a19a40e640e031140c0401403d00307400c01c9200c0d44060304210404060401342c008140030322036029500c50300a20324001d030606284a1070400c0300350009000b2000995070042e404c41006607a074440d58100380c0160281450409052140a001400629200d05980c201040f03201020507041e030000000c0341e8a016501000d000130481c20003003003ca6019178010721080d489065081403a0f0b03665218865801041c41e809140c0b01d121039441800c0c030049101c2d4203451031070401c1c1040400d04003d01300c80680001002450111040d41300700c410355404102d41c1c40110340c0000c01c01c083d0420380c5049610b0b0b401034981c04807280c1403c90314025030305490007080c0580d50a60b444100320f54030464111783c030100301c82c0c55403d14082000201080745030140020040e104d8000402e03a100c159106051800c0402014044511044000d010002c1c0d401324114008110b246009a140c0503103030241510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 671076915 1250 671075665 671075681
    0x5010b0f06180f0a081005130816020a090e010c080109020c07090b1c050304180911061c020c0c03251206021207030504150908090d06020f0a0c02030601062f01 70
    0x4030103130034000000c070014005056040c524884200744015240c1d40a05c0840341680840180019014030000c00a9155441c608410030700052103195210b035101d4219045400c1c2450300d040c165180e0102094054004c14082d004260100007146007800b8007541689458150043c0e20f011500c440c010005a90354500b03a1414007030790524611313040006e240c41c0380d880c1e20900c50807411444509007403c58105038890030a200b038200c241a200c0e45191001c02030079074407070801e801c0c000001c1c90841500803281d2000d42440302c030145c002d2101505035001c240c60410141700520128040b1320300c0034240e04402c40380c00c040340d0b11b02041d407000d20710924200700070340148116038225070b00c803100300203d0701e501d5006170780114041c00d04560030036424022001510041c3c01c021740245410007a40d0302500b895400303074500764020755005090140b483c1900031140d02480b101000120030b080c05d40107501c1d043c84400e005242e5030802071160100104a815200d84407518909500d0b41d032a0340c18850f803001c0d000880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 671078165 1250 671076915 671076919
    0x180b010b1c0606180f05030c04022503081e0c0d0c020f010c020c1e010903030e0109082d0708060a0b0a051914040b33130305010b0f06180f 61
    0x4080d45900e402131094200300d5848580e4400c154000800788030004e401d13000c0d200090003400c0520056070502c0b0182d44901c025240d9038010076042468401c08000400510384641e44114890814520344000400d81c070340e40228003003544080c0075002500340300712015007088420103d44564501030990402162402880440d421325020941780c540c00f0440c0c00b1450000c035044441c0c2280c910041c00000340c042e6003580486c2034100c0034400b0074000c40c50102407040c145800c01c14640c5865800d400c1c49400d65881c200742c00406904c0d551000e02c031382147e0b58007125800401e040741c900f48000d541d9843c094854400203a0350005d002c280d03101e0040c104080e250140c8031085082c50445d00001750401c3c1d2040b0980b00b89800d4009040b4589405101c008020007000c80d04545c200400408599042d03908040c002102d81c035460100c4041040a040c1020180d03c04503e000d1450402909441c66200050310910a154110b81e441d038a070700549100c00200700e1407001e020607200100701d006034201c3c0115 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 671079415 1250 671078165 671078171
    0x9170a02180105100504150c11030a0501050117150f0c07140307110a060e010e06040306060303020a030f0306061e020f2d0c0a0b0c030405040504060f180b010b1c 71
    0x1654901c052020030304a5409071440343d12004030311400c980501031401546001640d400510301228452000042075601507034031004024420300c0024941120620112890794450f0010000b90b80d40b811200400074082000d480303e87c0841c03102440540e0b000f0101240c104c4520041780c4031441c180d00b59442c0e107600c01208400c09051700c43c2a41d907038200f44403c441c460501c1c60fa100c41c509152903024210b4a20b6168141505611401560502440e605403a0008014400000030411901070b4100850081c1c000d0b100310606c5040082405c0e411450b07000615040600170040940c4c03000110cc130010404032100c1541140e24000c80c1022640c2c091a14548244003507144840c52640e90b945400702d8101c0f0306040407044a28503604c41001c40c504960081c2040300070408070385420002c0220f035403c001902c4c50a51120001000c0303450941c1c1c15a8111f6450381d440e8082099440350507003a0f0031104403030340035203542e50382c40c400c040c070500584105030b10219140000302414681030a031440e60135030038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 671080665 1250 671079415 671079439
    0x240118020f21160e060a03141e090a0203071802121015020f0d030b0a030f06020711010507111c14010e07050603090703110f06030415060503010b0109170a02 69
    0x2c0c140401c1c840301400801006102044051009096140d100c12960b1288448040c01000300300c0583c121140390f0007850b03160210f91a00049102d04c00b4451210902c882e41200a8080700f031640020040000c402030f4009000c000c007684e03000803008200d0380303003152124080c003030310452001900509010003403c0c0c08140a02448a0010341c41078262081f01500c030003221202c3c402240e4598040c03046003081e801001c159500f00344690040361401c0c0019003103038402940d966a1100d030a11015041e03c10742c0c2c0c0410100104403810a107819014000d103802c40c02c01c0c882d0f1702c0d5144100c11410100380300d00b80c6010701c81070f40710481a070750554640200d130300000c50003d9482c15001e401d1100d085425400340343c4011031036240c22030a9034003c580d030500401241381140c0da903503040d2044074a91680071043c103110708170640c1c0e03e100541c4518030400c48500f011040d80c080c20207844064201a219034100729482c1002e0343e024503808110b92440141c2401e01101c03800035410210032113030180d00510b9030001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 671081915 1250 671080665 671080687
    0xb040c05180103030e010302120115170a0c0207050109181508030c030702090a0c080f040302010204050a18050a3b03031e010501020a020d060b19080d02240118020f 72
    0x24642c1201c1c06504e480d240c6044800044003244140b100d58903285100c0d20041c0824890f020541601326100c0c04c0c10444042244c42c142881c08040b991040195101c42c92070344082c1d030602450b0020203082c24000701c018206091103001558031444805a00c2d0b4a000300c12010b5408201c0c000108010310a8a680e841c483d0040c40d103a40c4111000e0717009444d460f001c01d409000611034030040d0001c9a071a55825210403801c00701b10100a4000d808641d028800880c00f60350b2030388103a00800680c41d258840028544a450581e40b00404444c4c1305858035080c504440c0b0380c06200724102c600112200440e8000c4009005120700c3d405880100d80300c044104401718400e907800c80d80c001030701d021060541c0c0ea02c600490381e440c000c1800a4024451003a41e00008200f0303000020700042c0141189040c041000800c50800119802071001c1d43c46090942750464061120a00f148a041d05204c18100e009158400c480e40603c51086400c200c03415855500740ca80d0b0650f0000341c0d0028500f0380e1440d010340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 671083165 1250 671081915 671081959
    0x513020616020a2103180f1710050910020702040f150806010f081e0114040c09060b1908370f15051011070815090a0309030b040c05 58
    0x41d0403401921518030105894409180940d14031416140000101401c1d41d0b085a80524842004203c001680c41c080b69500d801c101142c00380c1109600f031141c0030f1036000400e14102c281d5550540d0700c1d1801050050031100420001103580d50f1000160b500c5d802803000c103000b07003c14400b648000b450a00205074954500c0d041d0030880d02520204c41003645c9034050502c080c00340703101d0001642c0c001c0d9984444100c00c428a07581a00340c4800000344400d480705000741c200d00c00c850440b00c42c51141410301924109100341c40181402119043c1404034480d141c40d070072150000c190303060000b810300040c0d8981690100c24421002100400004141d41c02da800324000c4d040d440168a81c20302600040907506845136405c180404114258442d1620003800103054043d040241003240401c0c0c2d50700541000c20030100206400301c010721000e2030303500d81020f2400c000f03080c413002c5801640c075240205c1d034481d420038141c940041d0301800c80d88891500310640d0000340e1043c1c0d0084581c001301d41a800c5240 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 671084415 1250 671083165 671083207
    0x70c120c0c080105100618050409060e030c0c040e01060302010206130620070b0c070308060d06201201150203070b0901061a0c120c0d030b04020d181103150a05130206 73
    0x4030418085903180c0c0303020b4607c0c101c88a139012410b070945208100b1850300d500030003651030250b840050455010f1f44c4541c25640b00f003892a00d2903110700015a543d041c24440c1d5024842290020000b40d415680000c0d01c81001414071036180b6464541c00d01031140950006010a10800c07060070404230b4414155181e401050040d61045c118100250940388074204452000d0707403581c0d42040d1b42c0e482c2820800c24520004060780c2d42c9550742e410386044070344030a030b404000d0740c042c1007075482c2c61400c6e04156081d0340c140c0000c08000020702c00c42c030003a500003050b40c0c000b9030701c1600401d480d42c407203414030300500d100e82c40a40106d07517841080b0380704484035004100028040c0251103081c0d004880000301d034070440c00c002105034020406205c000c1d100781e104014040380280050700d000c0105d801d00d4255400800b0303100d1503841c4034292908204070700c8050440e94030181c019100055000c80b0362022604010f0040c1ca08035265000101a6405111080b001e03941c01884161502d80e0310200c921445810 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 671085665 1250 671084415 671084431
    0x8010c1211031501111204061d1c140f100501060e04050420010504050d0c050a0e06060d0903020a0506280b060405010c0c0902040b120609070c120c0c080105 69
    0x12464551500c110601264461110051110f942c05054001110006201c400250082c003c1c001007001020100d0f00a10041529540e00420f03241380311a15002c21025000c483d00c80e46d40740c03200c0c0118980d15a0350040c0c41b5000400b120304401500381e85800d0601d4070b50015110300800301d0882986900303a11650503903113039581d00e40889220034240300413644251009095240e215581006504082000600d04001131402c2d81c00c0c42d43e960b01048010003903d100f10740a042f184003d1200c1d0801c1650000180340c0e0b01e44000580c02c1234004034a05210314886081c0f81901c40c0d0290003410700070440419195031060072144103180180b104c003140b0480340c9030380382e1401400d1015a100080c40c010780c280038000400140c6010b01d03280054401001d039100031650f81030707041070000d041d460900c0a84010009408003a41d42e000d5180d4007c04800010240c9115101c000140590305a00900321811580c2c008900c01c50b00e002c1c0704040d504245103074002821307034000c03401c00b10700c0344c1040d04110700840f03903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 671086915 1250 671085665 671085671
    0x405030d06092307080f1b04030507090c230d020f120103110d080d0e0c120a021503040b06010809100c03272001050d0e0109021513060e0a08010c12 65
    0x621488a44803c80a88403c80003444040110b40c66901c00c143c100e41140b081c519500d403e030b04100710310840707810580c0b064409421040c800c0022110750b014410141e549490b040b0881e000d0020900541078001169103050300d40403d01000000050341152003440d85100315030b468204040c1d113030545107424001101c6002e180d41c0303c1205800c140802001d809e5004180c1c03800c020440d40701c80014070640290306082e2150140450035900c0c4c603081c9220b1403182d800941000304c818014000c00001218518103508010400c00000c100c03540b550035009442440c09080030380380d00b0020b603d49801c01c9801012245010321040c000d030340661054103d01c40c5d40c0010788150104540d1040710b0350400601030b2000d4520b9040300108010b6074100300082c1014101981084020412141100d41d4900401c0c0d40360343d81c60100040d85801c9110841c55040500501d16180c0120794080254520307104100901203c05850145c07543d801032407402400056008021543c2030100081c00c0d000003000680349945 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 671088165 1250 671086915 671086961
    0x204060e06121b0913210f2303070905041b020f0105060904021c081801180f090b06120705031e0906010509131a060a05010504080c090405030d0609 65
    0x10001c0f9041444000200400443d10083d1040c807016000c014031304112048807404910004080d600f280300d005201019011070f40406100c043c080152211541040c40401b811140842030703019240c034510040801026266201d60005482c0e0024580207240e000381814504000f04020b404041030f40965a170840d0300301403140721858201c8400703850a5401429560005000d414240300000b04020036602c0002d44c7c500c907854900e80b60700030240044102c200d540c02c2c6801c940c1d2045286c50782c41026503034145100c1c1340100346061081f4511a1001094540c40088402d43e2405c0540d0460341e25034404440c1c604e09100000c0903584121040c201e0001c20038000b50300303142017211a61113101500000c14040c1d007010b04010061900900d0004d160130451300d40000034008143c8100c122006407800151030401c682088001203194002c0b6040100500c4200000d4400085a4610340703420f032401c0005454a05201d07055120b07040c96407106500304840002e0500d9154018548100901c804180720a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 671089415 1250 671088165 671088199
    0x4020c160b13060309110427030f111609050903041e0302190b0d050606070f0c080f0f0303010b1305060f091c02031c0e030a03022a010c08090a030204060e06 69
    0x40805c0800b4021410b21090f140403170605501074000015416401d0403c008071300500c02581825000032400101c0940e5503081d000d8218043c480e210f425a009031180340944043c9014011403445003007495512140030542d2601c2c20300484020304040c24001d45002550b600300d41d2071140c24482240200c2009050b0341d00c142c0103c211000782d80d40b807421185001b00700480103000d8000980b1441c2c1c090320410407000000d494100182410b0321a0b0310410a2a151841032070a180941d00031180c02d030411424240b61710008002c40c2d054603a4401810b840707070006c0707440b465000100e4022942101c03000404002102c0080007400b071b5080d04032602c1803805220607103d80391400440c4000e4040c3d2051695010304441441d00721060b041c81c1c50040c14000080000ae8a0904044c00580142c0c101b400c0034019007030000a051900c000c040c2100c008401c0c0000001c0c212101180302a02070140803806102d1691401101001150002e00074844261284840341d0900300a45100d84501c15401030355a1407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 671090665 1250 671089415 671089421
    0x70b15010302031003030f0539060702070e100b0406020615010c030c020904030e040204060521010510050318100c02012306210d02030909010f03080904020c160b130603 74
    0x104546132801c80ca082c0743d0356056070300003081340e00c0b5010300205204c0d0318043e800310341c100841240c0c0000001001010482c09450492008840b155283c2104007001f0859400150402c11102c1e400840c000c150707144440c40c40d84240a80019052090008000521603030001d446406980a0480341c071191400000558880c1407082c80100825415a07071500546054202a58018041d06002203c80d000000040499000390003680120342c012603018800910041c0141d800380303c52a480815504003000102e0500511481d041000000000078101115401c40342100945940c211110200ca0100750700140a1840c00200190b280c011810304503040586003041c40303070403160500d200e1349401c8248541064400d590088915810031495650901003100305080d4205602a586550850301040703420f40c0183d12841d0100040c4000344040f4403000101c8140240886006075102d101a9009040c00807501c8010380c1805400d000048102c1220002c00000d4006142c40140f151140016011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 671091915 1250 671090665 671090671
    0xc050918070f120905070801051b07050613080d09030906171603180b0103050709050108120a18031b031428020406050303041707050103060b030703150b070b1501030203 74
    0x410491496030001d001c1c83c204103150003608400705a085881d21803030b00e0001268401075060799581c041000800301242080600001c181c106490301d41203446407580c1d01c0000d402c1e400c2d900c8403200d021080204036811222603403410a0184a50800c0b0b08003e010380b0210721404c1d0102d810070b0564460301c0304000d103d03445030300c42c410865003000c540e45048000b81040031140061a49500041001c00e0903084018004c501c1100100703501810046024259030041e800528a076100814402c4400002015a10406454505001503c0070031000d001d0860a540c4041c19140380010302201440100c4036030425203018030a150742080b40134121640e02c08403500350080c4a062081d100041a107084851411a07000030700c085480707600c6400203411036015600c10303181c207200300302004041e507030912000b03009203401d003010000c0c0c610700b00b00520207110041000081690342c0c1130012040401c941e40c14081c10618a2458a6000030301e070041550f40d00741c4214030320501d0208181600d600c2030089a00c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 671093165 1250 671091915 671091917
    0x90f1504182c0f0304090209030c01051201210f050c19050a03020f030312070c0507090b01080f06040e06070c0308090604081210050301020d02090f0d03140c0c040c05091807 76
    0x80c4201a0221000e8030511002c0803106000307607441c07030780c100d60100042c1c00585280000141d4424002c0101440c000084081c01e060285c2803000503c00762200d000c050440b2840400c649411074180d43c0030b06500d00301d4100400f03240740901d81a0510000080d01c090340007050b40c04510014648070f4103d0201014410951300110000c028001402d0241400202203400b9044a041000c0b01801d036058060031540c0000080c1100d078080d090007410080400101522074080200c42c180400007850944001e0850840034000d40108216403110303400f0061103224081039612905240800910981816070241c0000d000800071030100349011901c140100d5101c1000f03450b2a5105401500f07240009044240181c4510800521038800303000900c0071403c00700c001a07071104da2008011140481c0002d8500a460307001c5c0440000b40c100e054041d4100c80c03803501d10388450940321440e00c2c04d0154689a6000b0f4181055281d43e40d4122014080c90341c0c080b50b5010010a060903200074498080714510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 671094415 1250 671093165 671093201
    0x10815010f1b050d180308030c030705130801020d1d0307030f020a141c020f0a1509200301062102060306011103070b01080d020a1502090f150418 64
    0x6829802032841d03400021650a261190000c001c01505114903000e10603140c2d504840500822a07034001c08524507194103404a284460840d111441c0720700006102000340c44000012440d9130303001d5000d0340d818000b00c020061219031109100c80c080d40001c400d4401d45424225424420f201548460544c0802170000703604007d5aa20200c848038460103a0320194061110b403200498010102035001c900940c1c01002906481088420240021003c100c01c40d001810300006100c8046405056540c01444440e4080304282c41e4600414807040020100c0142a00b07503020301e0364000c00110202000c0b8001c110080d61000e04607400c219240894001c8042144803000514110340590f4000c00e0624180031101d04102d44249907500c206001d507080c40e1500c004214000c0100b1a1060340718084c40a030001d510b280d61000d1126401c420440c80040e0049101b1f0b0300381d1140c00c100c0c0e4031101c000342038552040103001c10f041668003034002e014090f00b590103001440e400a005101040c01e5071940e40d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 671095665 1250 671094415 671094451
    0x20705100c15113f0402030a24021c06080706050319090b0c0304050d030b06040506030c09030715080114091807090f0605040e060405120c0106050402120103060b0108 73
    0x56008000c080c0708401e484400f1300005143c0c0e14000030f4550030291450802c0310310aa00c04c14007001c25525034501400c01020410080180c41c086a149003c43e404a10941d0340ca9071101200e0714090400c1c64514902e1000c41c0c404400c040368401ca001c4060b0560080205940380c00030513456082500800d0041a402c10128400d1169040d004150400308100000c51004503a02d0740084d030340c1a0707003080c50398402005100900c5000d011054000142c0e050810035403202d0804102d19001d6407181c18403851020000500191103881100e125520041c1130340c28036070700c465018480f02d554504500018072010000b02d1282c03146403035800c08000c010244107895581c000b62041d59803c80382c1038003040c01141c10006a0481c14003541a14000703410005c11420300b40010b02c400c0f00c600c61030110b555072008040c04082000031800303280131450b404406549040300c00c010b03405416946e00540e001b501c0002c0f06044210900440e5060701e00c900030504c081d21051004403501001600d10300d4603503502c0400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 671096915 1250 671095665 671095703
    0x90302011b05061305160b040e0a090309050607020109050d0b09060a050c0706020901210e1902060a0522080d08070f092705011e151e0903060507020705100c 69
    0x1e004d0455104804569000c0c02400c2c0c02103d400c020b91100200040c0800c0a1042d030750549a025800207181c2010480ca20311070b00c0041c00c411aa118060145100040d0b00e0250b900c80d100e0708010b04070191001110042c20318142d8820308080f41c80311018043c48002c03a00c25503080c01154003820f003106c0e00714200201901e4410095101c0e061107414031684c0760020030f400001094144820820110010ba081c0381c8020030707400c19010246218114498011400050b0780385400c0d101c8404107890190344030601e001a0010006403121440c00940100c1c40010b0511000101c01040040c2e5030359082c06a01c4040007580c29035142c0b01c2010108080d01c4d001d101d42040c00080c450645194140703003056966820402084031000c0c0c1148a1015800200300e000282010640000300410400050300100b102401864600050049956501d29072410b0902510507102d00b4003640c1c00040c02c0000b030410210103996401c0510816005e02c110440c40c08029000d1684100e01c69001015200300d0000022 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 671098165 1250 671096915 671096941
    0x17010806070e0a0306050f0114510306030c1806011101060b130f050f0904153e03280609020a080108101e0506040b030d090302011b0506 60
    0x54000f03940200c000b000c25040d0107002d00618110710302ca441541080d40c2d030750b01400c0c0a140540a0301c02c40c2410401d0050f51003205940003180e0682020441101003103208840c0102500b004006111040800c1407090030000c2d4050503040f0101c0d04050994824000618081c100840ca03460300c020000d0000d500506644900d004d0750000082d01070344601003084150842120a21450800d8409022461070541a00c01400080360081900d03400c550024920900080004000c1601c400b40d000701c0f104550440d00003c450003205808250390202c0c4000b403990344503810b0301c44e200710380c0100d101c1748012400c0764090034880c50001183c1314440296155008141d407403102255441d1070001d144822840a081e00e95000c6d941e4091035458440494a04405000d01000301440c02c0440780e842d410840400103184041e00010440380d991500240c010600e045015030107004074640d0828296211044e041070f01c2c400d0700c5511001f50240400c015042c1648402409580720801007040ac0d40c10350 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 671099415 1250 671098165 671098187
    0x3c0a060912111e0a0b04082d06040b090607090b0a0e01020c130504120e0d0b0a0213080309010314040b060d0503130303020601170118021302090306090d1701080607 72
    0xa1a98000c0b008030101040c0c00c100d2010300094074010710301c0003040d1032900d21100c1c0d008048072a0780c00d0800b802c1c00c1440340c9800d40c00c842025090b6000442a145900040c501c01e1a80d03203900a480d560700c0d05062031607042030101d50440d414026140001c000c0340c00f1b08240303015240c040083d242003021800042d0381c00031070040840c2c15841542c0401c0b10956800007184280240684082900d04003480d1034484404012840d1040c4011000c0101080d1140a1000101a00014055210341700c104801009119020303019407020b4042401042c0440c00000501c03550703a0030ba03000c1100d01001c0003200f410443c01c0d10700a180104042c04a1035030700e450420401518040c0081d40e180c60310809101c21410026801100540c00010041101e0118480310340310004400000744490003440c0180300c2c0003114004024420b00041400716128285581070b20a11007000d07040b02e6550030050300c01550340200d0144000001c919109452071401400d003014120303180100204101c0d21105004e40c1c00b48840 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 671100665 1250 671099415 671099423
    0x21020405040203130501060e0f1314030307020d0206101a030a06050d050a050d26070509150315040615121407030516030e0c0105093c0a060912 63
    0x912012806548600c002d500900c01800742c0c5400c0001841c045080d82c0e4903500110f84d03001114104241c40744c0c14484150310080da0708248951092514107403031241c07040f80b9042280d00c804003c00903495000a51082060116000c5840070740e21031076403051010303a5000b94189112071160f480d0315103010304060750304000401c5010500a13160707400720f11009000d1200b03507425403041c60f02c101800010700c50101000c20398903110190441c03a900c001c1c0e000c0c8822642c07500b8042440d0000d1490341c49101560b0303140d90000c01d204500e031a007502c103159607081039920301100e20801002901901c0d0921462040312140341e6008106259041e050394030020b0101a260f120f520740300c8198641900b40c0d10715108920b641c0b07000500e41404030391004c1c08110000e03164107051400d20714450f06000007492542030907092030a15a2602c40801159500783c540381c40c40f000d00c28402600e034130034070b240203d02c1c1e0718640d0142114000350b056041260000092081d04045030b010303001803100c80302483c024407040b802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 671101915 1250 671100665 671100667
    0x807051509030307080f04030614010b0304031b120302071b030f15110313060509061005040c09030c061709010212010308070f050d0906020f032811070f05010e03010c2102 75
    0x90b1749854030181d20084a645440300005411303c10001c55101d00781d0740e140c00101c620b01e29070600034840001e100c05003015040c0319406415a184020811030002020f5100401101544403004080e02a4100000c00c44280d0084105401440442d510007400c40e03400407050001e00f07019455111403a03401e0422100d10035280c0c00644a900c1459005601548400c580448106001e0030700b141254000f80141c84650056401e0103c020210b0079a90151142202c000650410721003094900c160306500c0100a081800c0000503040e8014000c1e01d03090548500f10300d41551807400340c4d800c030300c50340c240540c0a2030070400500201d4960400f501d000b61041031004040141502d54601c0d01c214001d20400040d4040e000340050b90b030503c22660f12046000c02036052003480c4071001034030004942041d800024880c810071120784141c102d00c1c00d499074242610346481d2603480158200c0b56a00806002c1110a60000c200d8241407140d002c46125070380d195004100d001034024004511540ca00c034415030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 671103165 1250 671101915 671101927
    0x307121112090906040515040509070302040e030c0c090705030f06010302040504020c010b010f051602060d231609031511040503010e0a02040f110d1503060501061808070515090303 79
    0x8001c001000503007104030381c0c441d207600a09042140800005012500441c2884140050910f40401c003103400c2c0070488020400f9a51070203d02d1400308203600c003a600ca418100090b1010b131012004104401801d0240d80c590741c42e40c0103020010750305030f400b0800590104000b40c0200403210180360402014074000d03152130b6840d0009000d270380100c3c01c44405030f552800f0300b0400d0b41e040102d407402080241041418250301100e40b00c0280000c2070701a006200000e000c040b0488075a011039a03041c15600b80c500407007040810074040000031030b28020141059800c60344218042d45680040f030354041144522540c401c1d8861000d40400d100d50360504006020100382ca82d0280103520300700c1c1d0329074000d19100f82c0e2801000252402c02c01c080804604e000d0050814613260000c41c0c0303c3c141002030211b0801000a9070640c0704c50150700203070400c0e18100000c18403d070300108a000b0404105c1440345099142c08407251200010b00c5610303480010700c1101e0300300300d002c0d42c091310400500030181c3c2d003000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 671104415 1250 671103165 671103197
    0x6020303060114090a030821090d140f1e0a020f1c0318020307230f090105060703090305030703090503241513060902071502161103030d09121b05030712 67
    0x781000623003803080d0200040311030200d00c0f107080d019441040440101844044a0009042e40142402b0440700d108006010410600d2650444a07200e43c44000c0b6014450081c0da54241034024140c80710041c02540c10200c603807000018032450f509035a1440d000b803910b080b030080d0700414050a00748070003190f008441c00503075010f020150040c0004000c402d018806804e036040060000c1c8115482250034115018039500d40701840c40c159002a44d14680d552220b040a9410442d1980020200d2000098480c01c240e4002104c6040755016001c03146a8038600100d01016000c8205052012008800140818140c1c040c60900c403200a4800c528801020a06009440c983d400c01c20f4a00d40018440d010010402c101c000400c1c08405c086052501d0880210b0034002c070343c00003410444e08a14841e02540c3c09004076102250307010320800c102402072406601c0481c2148105022601d10080e80d04202540c9a9004001c0e42c8000698a82055513480c01041907041445030108071081d5503d40000b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 671105665 1250 671104415 671104417
    0x3010e030903070b030f0f100b0f070309050d0b04082b0606081e01091a030102030a09030e0a030c090c051b0343080903070311040606020303060114090a0308 69
    0x100046406141e84031012024145420032607400100d20765802c1040000c041c50202d40241c0102514642c0030140d103c4959040a08442d40c00c60102d0360000a0000e0744c1d00142001401a10320a80b034900d10142d03a9000c0210520482070060019105840001e0004011900800848407002c100c034901d06030002604090b50032603006507036000e5031010f09000c00c1e41c1000c2d10136846900c00c01c00c90944800c003420180b102c8010300c11142080d40b21321800554030b648849009544502030000c54407880c0c070080d6039018005011341030300450300000c1c0581e03da0600300794400c01e40c0e4010284121440c54002150001c2c0b50060345541004824401070410b080011142040b803e81d6000842d00e0700ca07607118034244501c1d100841c220400220300704107020406403100c00c1c080c140400342d04442d51103509281c8080d201d501c000d1a130502400c580841085601e15001c0e54042042c2c404014a684178501680e5900c0140c0c0c06602041d14100e40258001c00003004100e881c00143c1601c00141c1e880d911722180d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 671106915 1250 671105665 671105681
    0x2060a1215090621030210050c0d0c0e10020f0304140f060408071505211015020d030e030f090910030c0306020703030c1403060409140d0507140d05091e0301 69
    0x2d003645550080003030451504184982c000b65000703000a0300702d9940d001e55113181c02c802c0503003250f071117100142e03450000038242c0d000d48079985814003040560020060201d01d46440841c03103141411030f04041c2a2000402d10350441c640c000940c034240c201128007070343d800000121503001c444a82c070ba0910351101c201a1008010040042401c00e0420b4400f1440c0c41c814000e0008001007803081d151204100004940c8182d0740e1544003001d600c0c0d03410f8134600550103030080180f071410440901c1d07501c0d50010380e081b00d12565a504000c000081451103440344241c052040d2081d5050002c400c5514111076081d800c044031000f01003010b40d407940d4174a40081c03d5407042d0343c1c65601089200c18107401d030048003189a91403070400d00242003482241042d00010741441d0245640d90f105204214111407429906400c0c4001c031500c14030710301c20041107540016011075203c40c40e0b4514a0078800c00040490009005840d00f50511f18100148801d600f02e21080c0048100010316040d4039840078450210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 671108165 1250 671106915 671106929
    0x3110c09180c1807021902090f041406040b06120318041e06140a080307030804080c010227040e06160c0201120915060617220b010e070212030402060a1215 68
    0x619250130305000c0c0c1415905130085100000503000440107a45480c00c081d0b200051440351403054950381446590034201800c1c000b03035441410140414443c0e41006640f0400c0111180b00f82c0c042c480360615201e0182146040316000c44441c0e40c44d061405070000300000c04c00c0354580c6101c07100d06c141c100030349079642d00416018110803c54100c608280d0b1811014003a000c00840c5441100c2c3d40003490000c00410140000c0008644001182029011151740b03411040d41c805842921030605c0c1150710240c1000d91149250032021740c400d42c40820920310991070f2018030184814400401d4410000302d2a00700d041200718264001410345602c00d02c255540658800c40c4540c48803d103020440e146078009100340544491006458410b1502d042ea01030305240c11000c40c024140380d48040128114030040c03004080f0800800c2c020300f03080c0064401c9800da402c64205840b00b1b02c102c003d0380300980700030750024000c1150310f05850040c00d0300320200c280c0c04400102c5a5040007010ba1000b03441d00801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 671109415 1250 671108165 671108209
    0x1d03031b07200406120206030a150f030302100e06010e0f1003200f22020f0c0609030d14010b0405240a03092d1707050a0f03110c09180c 60
    0x85050f003894428040a8a49450744001c020029000a40c660000600f1000c00300e45600c142c1314122144c0c3d244000030100450000b01050f202c1c40e020b9250454540c03090350301450040b5001400c02c0c00038149040b02e59650090606403505a004111034000070044400b0140c1a000000090610161600308c1010034a010820301107040130000c0403c04800800e02c20502a0000b943c0300c1500b80103a1103110140340d00607684c01c0c0508a5203424018041030407014080c0b10200407141402000805010700e00c000100408510800240080c0394280580c8500280030300c02441142401d03203000c50000181b50000c5015810500501c02175030203000c000000a45030340b03085040200081405090a83c522003480c0d04046020f4024040001550701a041809400f042e10101c900c0808540c4490381003416a816500300d400c2ca46010340b01220304130300240309454581c00001003c00c10394240180203012001640318a00c1c191340742041000449020b00035503c00703c2003540d8141c401700500305112889 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 671110665 1250 671109415 671109473
    0x21906060501120c0e01050d110c07050a1a04060e12010e07150e030a0305090a0f1d01060512060103020c012a270308161e061d03031b07 60
    0x10407082919422903081802d00d100c0b02c1055800c40c02d170480114081c64540c0d180c414112100014043d900190201014001a426072518003c00c01c00181c0e1310907601c405400c1e0303036a1002003003801d00d604032800c0420140000d02070a4840c0d8400c23031040b003005001001800132008518216641504000c4441d80305800803c181002c1d0505d0781034800c00b500700f00640700c0d04140880e4455034050340090070003000250074a120b955000850000c1c00700320301c0381110745031102c4c205002011051040110021007400004010740304200729000485020001c03030260700c8502c0103401a4020814100e965500e40d08101e4641e44551511421a505030540c101c0e0000d00500103030248403161f94207140710507800804180c940d902180e4408580c2c2c01480d503565502801d9807001490001e41c0001d10742c00d502089101140100700043c106d050280004110821120302d14402404220852140e90b4109000040000c9a0503848107020616008064900801542c0b000c030002c41460401c04030b50526111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 671111915 1250 671110665 671110667
    0xc0103050901200c0a150b13020702060a0c0c081212071115220f020a050901050d140c09040503120c090a03150b1005071505040803060d03021906060501 67
    0x169a0004501d5008000340c081010800d1030842000c00903c0180c0c0001680303d0714440c0c01c00900ca0b42c5508a038489003000b420340442c1c0007401080315013501c50407903903a480201130780d03030702c21104201e500625a929005080784c0603074680c1c0040c4020703102904812000a1030202c00d10007a00b107a01400d081980e07031050102140c0b031085c1f01410301c104000e0010710903803044900050160f115405643d41c408265140748248548400c41d88140c607906000190850811461219a1005a200300c079460903050b1180c00340080c0100903c07401e580218040c0c00880400c01c0d16054000314603c500c107856402c2039001c04581e0040781a103045403e5400025604107550100446c186c00c510380752011850710300e07070000140c0054100d010103051400084d814004d01c2006620000c0c6202024003d642211415070000c2c00390b0304044015148618003440c995061021031182c01d00c50350f400300b405030940e240c2d503050000c0c0c0344566000700c0035846a80135403040003807a041c4943c1b920b44101c1000c100c076414200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 671113165 1250 671111915 671111921
    0x30a080a0605010206040b0408040f180e28030203040506032a1602010f020c0306040b070f050304080f0a0512092a0d20040e150105030f060604020a0314090c0103 71
    0x940300100749094400e0046a03808103202c0e40040e000514170009845070304041d4118407070b41d40440c29059a0190004589102014980340c401d10004100b0014002d0003215465003ca1200c00280c0174a403c007403065001c403d210b40c01e00340d0103441243d08154030b030804150f0581c01a9004c00b00542c100480c0c408600707654400c0c5414a5200700c0203400c100007801d0000e00324001a000030705020446003a203c403180300704100c01200000030304585180c00c01341086886403209440740c4001502e841030900300680550b04480c00f4980c03101c609450201e01d001a04680d0300080984020410200542d10144011250f91405004050054401d410020341d884443e00c07290107103080020b9140c01e1501c1160f6541903400c40c41c540280f400120360240840c1c1c950a00fa01c4404d986c1c1c410320b84030f5245183d61000525801001842c0402001c40e602c1e941010366030400054011904da00c0a40011002d084ca50090b040d078240c682000f2591510703091401407140c80859408400b9840010700103440d6034980 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 671114415 1250 671113165 671113171
    0x605090c031312021609090c230402090d050a1202010c0908061b09060703031a3001020c0312010825090e01110d020c0606040501050f0d08130e160305071704060b12030a08 75
    0x14100c600c40c6414004204427080d40d021346110300d80c0400d0040082e280d0394008403229522038140c070480b902c0e524007001d0007c43c0c0701c0c07094010743c80c0401e1652a00e000d52307182800d41b00303030300d0062000e940c2e031203500c132185102504c5008540c0e0080c40303110000d4031340c000600000c0380b10f0b0300d0100d03041c02e841c6524448204042c1109204a104042540603407006645004108001980f00ca1103109090180d50181c410303071304d00c1c4101d4131000503103510b10305986650b141030302c000d0819110350b000c0f50069580791545c1820b422503501c07062481008106e401c1da014060314500721001040c65041e0b090f40940c550480410303e80d401740c001900c1d1030289800d01c8203940c82501184d0421095041001040e140d26000803518090003c242082050280d0300e0281c91920011011031172501e0b0300c03800106c103201001c0e1100c4d4581175500a907250590700900500741305460b165100200c000010000ca54800c1020307000b540c2c0b06a0362076000800e5107030410140305485040000350b5a8441e9104020f000342d07401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 671115665 1250 671114415 671114429
    0x90f06041a031905060a0b0d06080303070c0c05030606010203191701060801091415100203040f030c05011716081512010c2d05091305040302010605090c031312021609090c 75
    0x1000401501e541c5111b400001c1d5400d035205039441d0107640303400c0d0f802003034160070000b00741c40040100b00310703150300c240544c0f0f410b0720802178128170345e585105140d50303407006555580c0541c1051210412071001e20705508409030b840e1414030b01984140f400203102c2402a0415000075051000511070b1480b54041c407201c0d060302c00c11054652410300440100c0c1182031011074441c01400aa00851500c01c00985e00581a00d40c1d129114a5581c607180040031514480c40c4d001c075282c500c146402b00b00c0b500034284030f10000e56070b0003003030301c0024400c4805d080c00a180c43c500d2140c032205440705845980001e001c41c0100300002031482c40103040500082d1800803c01c0b803240300c003d1544240c861982814011001a04201c2c3d16080164000b41c04003800c1080b002c03030545018100001c2c182d054110304103c038400d480d240d0203522090025116031104542e004088110300c42c440001a9072000110080740091064504181c00994509001e40d1141d000905054843c0c805005110f27000304208010300070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 671116915 1250 671115665 671115671
    0x240f050f01120c170c09090a06061203120908121003020a0b0a090b031005030d020c090106030b060304030f020c06070b10050d030f1206031e06050f0606090f06041a0319 74
    0x86070744041c00c2440d07034002da008500d480d02000701e98920030001005001030041004040c1d00c7c0071140f040e540c910714603042d42c0c000d051081c00540e0106409441202c50303010b40d0b070000c20036014010800034240780c00c0100d50740b0801300001c51840280c1c501c0c0f41d010f03400c8541c40d41101031445c010041600d01740e0304070320605801001041c4100b500414031100304c58205040380d0b1241e0341c410045041c002c4550109406000d1031148000040d40480c042440b100e00310350f41005641c03280000c1f01207802009000341c000381c040010801207400f880c1c503001001d00d648121111058085c01240c00380d040b0840c03c03544443d01d0310034450380400304080b0b08080c02082d1421104200640c80050074400500200c82c2480101c80d5008010300041d0040c0e03024582100c1c1f040303160680c1041342d0418154005007a03030b90390b01e002e0100f00021141c01041e4040c0f840105400d040203051420080d80e0710240107069408007042100250040b5a01d140f180380c6041603042d1a204c0c6054440a0b20314100c0c80c2d048154285 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 671118165 1250 671116915 671116949
    0x50f0f0105011b140d0206040b07020a0807020415170c040f0212130f02041103070e0114030109110705010504080301170d080c0306010203070c0b03090d1803240f050f01 74
    0x40d021205540100001040b41000070032410440314003002c401d071500c813601419454682e0720707070005607003030080f031242003e1501ca560f8050100d13240c1d400d41500410a42040008002515181c1c0008410a1160704800f1846070703100c180300e0005080d460000415040010780c0b54441c0761503c0b4042c1390118501c0103505d0200050024410280c0091002c0e00c848200c8500c0b1060101d102000d0100715400740040040d0b40311501814656042101e03070900040081d4440c00081d40300e680d442800c5071b00502c0031811039081c0b1440102504a0050503d804c03081030010720081402401140c0c00707139018550341a603a5040001a03800e00c039007004541032541c0a02e803000b02c401c0e0700902d202d5000e10b51400c680c3d01c070344441e07004034150b1003240000340c4105404840462210a0701e4010f6006203180d1040701c0c40b03002d4189081e074440390340450b0b400000418210403c0419103620040ea02d460580b15049000e41140511030f04480b440783c85090220340e1002007200c7c00040d60442c0c1d000d8440c1c4141d04a000d2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 671119415 1250 671118165 671118167
    0xd03032a1d0d210c0501020705070e0124110f0714010e150307030507030209100305090f010908120601020a0f110f0405010b1603120c05120c090a0303050a1b0303050f0f010501 77
    0x3c1103000400071a41002c9940480343d00ca0400c400c81654010002c0d981e030380e56424880e0341d80103140980c40b0440d2141000103124007241d10952540520407400c0320010300780740820b64400c0c601e04803c80090144031100c0c0b2085005201450141c080050105481d4910078001010700b4125103040b4014800d12a159012100620503207038404058600442d44c0d94070f03070364220003138007962500e20303000b448ac20312403840c264050b04058402c1d070b00c8070200e0790003000000300c0609841034803a024280103000c2203083c1940440d103034815880071040c01161203000c2e49a0310481080224801507400005000e0f4008091a141004003164001103a0a00076541808090b00711403007921408001600c0b8003407420201805840318081000c0803039010082804401c60240260703100c1804084440408000901c0703168203042a54030034032010313110f80250790a42d541929540c1c40042181d05008021901001c0c40407a40d0003461818401c0d0340104050409034804250000040c01c205d035207200340c5005110076 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 671120665 1250 671119415 671119433
    0x301030b1009090506070e1c03080a1401080a1106131413020a320a050307020d231303021201061701020414060c01200d0e0a02130b0409050105150a12020d03032a1d0d 73
    0xb43d0481042410354286800141c42803142804b2040621108007000441d8145442042c0c0e0380310082c1c640c2048565280a00001c80c820900001302040300e844050f10841c0c840598124100420450b100c0301810040101c038440e0020100394000460000400c4482e81d814040403481c202d1604005880b2040e00313201d4880c001080401c050000d801060307001c064168041319000441d005003403100f00c44000041580605054094001072280c80000c22003000301c14070071101200e4002e440100120408020050968000c00d4105045c2d0b403030b085201d0a6140444c3c3d8004448411054980d41c0c00640081d482170b04d003000e0302215541c001c00f0000001da1510404a060320110301f20016410740c3d0440050001d0101c010b0103490b561070202041480b00c012110390b0f217180710468820800350f0343d52140840c1030f4400c03400290019010440500082d000790041003006500380703911004c50329000b10320003510030160814000a00701d80d25251f0741e44844101484880300c00e40d52280c07490f9481d2a90550 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 671121915 1250 671120665 671120683
    0x30b01090506010c0606080f1b060403030305062803030813171c140711030f07170904092609090105190b0301030b1009090506070e1c03080a140108 65
    0x40a0740310000940e090b8400c4102c002138980c080c8003002459100c01c5029074034001c1d401d080110340b044200001c0080600f030314441d11200d004220f03900d00360450342c0440203402d000d00b205030444010b81c402c55503040d101044400035818515007500c8107141d810010034001014040c1d40078000401d0022001c0785040340f21f81012090880c50b45e6580001d035aa40c03d01449914071054580d10b0008120805843c044919000f130505903560f01c0200d81c4c080d00c0544911407400a40340c8942c0800c205d000082640c2801d003040b5401119440c03c00005001090039651083c13011104c0861090100d281d0340008503110156400c410302d050305203040130380425407240e01805854420481d660a01c9200745130f00120f00080c000c80e0350400e80b00d503503a250086e240c0780141d036100503442c0b500d03a001c00c40b2000741c8100000d198000e8010840d58a49a405981d4205260340494210303040c4c0981030098101c1c2007001320914800d41d0b0b40342003480c04008040454001d000180d2810000d500104500e80c00051040c0e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 671123165 1250 671121915 671121929
    0x6020d1802010e1908030d02040e0603011401090f021c020909150f060c031e07060b031507051303020a080a020307151e0908061503060f0712090c0803032a04030b01 72
    0x86007113251215001031005d0348101d084d840001194400781040d50081c0c41150403001442209448000815081c3d60598441079200541f02d00108500c18440d00710142d8207410420051510360302c2d18642d285250f1074009140b030740d500016071b154641041701400350f1000036210502e42d85e0b4100000a4446a2101041132040c031000c107a00b10f0f030b5101842201d4001044d000c41d8030451680801c02240da80246100f40c41c814a0580c40d1516418003041249000c240410b901800766070300c4106807142d80007182c103401d5241c2c0a950210068440300340c684040c124100042c240d8a110788101858103840e6004103090843c0d110f00c440d1165003003d403078981c11288181c1440c81c1c004803001140e104000c0d03807002d00207118100501601440082d070710201040d00f9800c1c2d1707103190b0750208185c141410682e40a40010800240c4a87c00c016642c0300701c0b1858411810080002c1e910303451246550401c3e101104075a48456580344010442022036205c01e1214081c02d05203851921030348031a1a0504c1400d0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 671124415 1250 671123165 671123179
    0x201230910030e06010f08100e10020d09170d11090306070c052a01121505041a0405010f1707062a05190c0504020405030a060b010c020d06020d1802010e 67
    0xc0c1010b8001c0d044226501100801c035150f56940b00240d4400811511400402e40140c45400821124074090040781809040080c000101c0a201240c000e60020b1134024041c0d07918111600001c4039028801c0499244192890b19840b003207a503882204d6004500c1001c00314100f043e081c00340c801241456008050f81060000d034119402e0250078050018074030803c007200d50540742650030398800d00b10028030b02a0b030b6041034080f00100c03c50480e50400b0103050300c07200300c4c6800c2015251a420214a8200c0e44030b4807a60404824007207000d0702c4080e04048100407005d1424440e0f40e1a24541d101500d50100c010b002e107514040c00900041082400e180903d8140c0301628094020703901e030050f030b45234440d003100c2140070b4140344584141d00e41202202c0c202c00d02c00f40095185054020380b400e854008028081410442d03944500400381000454184603000801501503a14013021035049400340d600969501c040120003001c481c440100f0511301d03146510301c4405030742c0c00b00140111850680c0c2003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 671125665 1250 671124415 671124439
    0x15110c150a1407030c03051005031507230702030f010b010503040b1b04090f0f1a0d0c1509180c08010902130b0c0106141f180f0b030402012309 63
    0x70005011402c0034070341290300c40014031003100e5159202200d1900c0a40e0100200e40f01c082c0441902d00042c850254560300034290088100541890150408014200503811011440300f48540d003260b011001508040842d01c2c1d02903003003d110100c802d0720064020400d00200c0000a001c500003e00081d015503513060000f4030020034001e140100002103008075407500d03950010740e000350400c40403000342d081c180400c1082003480c0303001c1d620b11490580cbd8105048200c0d00c09200204043c1c440030382c1c80e108003071000500030380c086003c4150801d055072000200750810900e840c2e00c943c031302c9519441603c0c11000c5207100d0350025042d0306540d00010b01503556101e62504010302001e9030003000c01030340c0014000c0c0e0407580c15406042140d80000c01980a01104020041e034031000c0c521a00e5440140b403004400c107440b541d00741010800300c5010741011074480d4001d445140304c9400c003081c2428000305000c15581c00c03049240044c02d1040010629003c0030827241c0e03070750107848000c80c050003400c604 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 671126915 1250 671125665 671125681
    0x80303130302030d060b180a080303070f020309040e06040528030c02010201230a0605030f0c040b0d050723120a031101020714011407020f1506010c06020715110c15 72
    0x101c0d4102031104c10709201c60307070f12031540c41d04a9108920900840c00844402c00c0075003001c158200403502c11300050b50855448001c165003940001702c0f42c1c0c2c2140002c00036141242d42e544070396003000c2c10250040a0301d140528016240200c9820000b40c8200d1045481c030070f00f16a0310051141c254185062030b540c0040d0300c0181e015104142c0b1040380d8001d0120485100441c1c594003501c540c5504c41c0521210781c2e01c2c402d064075640d00038041000342e0020060601a800d1903040b41401c0003000d05501c01c81055521110b0030414107810101d61101605010341418600e85e03118000c1c51001c0301c2c1d0303441c10160300c4c07891513550314050002002c0c051804502c0c0c096000039419030b00c409410111f09003418145200b024020885071400380054154a004074030380c6440041c5c00c0000c4015103008105040d540d00721907002403001001c0307e0410080a0401d0300099042c00a050704d030384105a0360a9102c41d44c030740e6006440b400340c065500d40300141710001054030006545400b111183c0d80e4940ca50700d070109 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 671128165 1250 671126915 671126917
    0x60f0504081506031608190f050f100b040b010e01120e010c170c030c031f0302040f0f061502070905181c0e040203041109072d021608030313030203 65
    0x12058056014003410300e40485640d007900c2c0e1140100b181690b030842d03881380280300403a01c180a808201c1c0e00102251405140e1546420140750140c80c1100c0c51943c41d50b2868a03029664189130b000f42c00c02a020303800800c0c00d004e5a190b00c00c0888040c041512143c000800ba048240b200764104289154408659986a802120745e014036034001d010042c0c08000c050100b541c2071441c100124030384400109450301c00000d6a0160203c2e000d02d51035a194150740a00c0c50707651607240c242400e051b0f4030000c01a6240c3c8207914031740381c0544010564000e541e12210880345140e015944600b0f03144841903e040d404a90076003507500a0707800040e151114a8040c0e000c8003150001c0c8480c2c07007102c8500302400e2462202040d2010103a40344182c0241148c188826408217030382c01080300c4e465400490607440c04160141c0e2003045842e0000c0c901000c01e008404d07410203085500e001c400c9880010f202c136035040c091402522070203d2203210080c40e10028130369a02c4001c00d04441d0660308400300b010548288 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 671129415 1250 671128165 671128169
    0x402160303150e01060c0512180607030905130f0c08090c06071b0f0f091503060902030309040912110a05030a20060a0515011803020105161e170c0601060f0504 70
    0x2001c5000c5941c1c580401420400191b141520244152031080300c9036040402159444005000345d0f5901404810500c649500501800c82c140500303000049000d484405804060340d079404408203c0c51204210001200c0d8036803040c004000c038540405c140c0c0702c00041c5a100c8501c0c180d660b66038411036820b00c4040e0b502450010b0411020094002a03c0f1000c0d49040f01520b406080c40780f1400d9942140c1001c40e8444c3c00441a10400440d04102003001a44180c01290014059a241c2960100002c0440d503424200312220f01c14095200d00302035022216081a5661400411803208aa01c4683d40c0b809a41020803c20074928041c4841c1d1000d084416200580c4504442007410f1110098000d424200c50301d0640d61131506024400303611a042c5c8118014811116804060070b43e00110b44c3c0303a01101c0200c603100c001c041d100c000245820340f048480c104100d066160b42c02c00e40f810785040303100c40040d0b082e110810700c40101490f5010500b00c0c112140c1d0300304864039510300002030316540540d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 671130665 1250 671129415 671129429
    0x50c0304090203010e04111c12110609010f0f0b010504090b180708251205060a12060204090501120206040b0a020c060d0c0908030322020307170d030605040216030315 73
    0x110000450b000d4801241b800f840c800c4421482d04010301043c005024410350b034a45041d4a560700d0103011652805241c09101d40600e40b45140c0c0c0003001c9003500c0d1050507030b0704401c50303035441500003068000303845100c101c0360030000e0030300a8005400000713085002da4017801030301c035541d000e2a11150f81d401104481d1a0828084c13485949001440500084400c0320042c03400c01c500c20b008442c1100d1000440c5440100317465013002c140c900440b04004042c0105200c0e0440440c0300007007880c080c905100041d980c481d4402580c1c881c100b000160586006038403000454841d007007040700590701d0f001960241e0b200100150388407210038208030f03e04410103010a40221002820040c411419005142c1307004441e01c070319490360b0351110919628031048400d08050300d000c444640f840c40d080324100c9034160006044558040e150190701c800b412180e8040411940000c6111070103e400d80501001080d0031a001c6051030300108122101c9040c0040040400d50f445410f02d0b009429245141c000d0040c0f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 671131915 1250 671130665 671130667
    0xa0203041716030305070b0603010b3609030c070f030309051e060d020c1506010207090b060903011515050703080112140f010b01030e0703050a08030402011403090115080c090601050c03040902 84
    0x900c0c103000c2c225900c11b650503642d4061510025500d820140103e4040c9540a840000b0315584800040100d81c80008848000184842c2030b032803001202e240c3d14080d1100340c000d555142c260301c095515180c103a0b4030813813807048940c10400110f41c000c0707a104210703041964000230030201034900181c2c0c1c080c0a07945036070140e00031400c06410641d60307001d4900f92001c40200d0784840c5070003e860000c0301d400c0715903a005a0044030f05000202d0160031424030300310054601d42c1003071a4003000900392a6889071040d131010824900f00107050481e5401440c1000508000c0c0c03034280d45440040c6424814091a03109660340c1900404200200400004e4081084280c0315012000c01c0c1d00d901a0211428850001c0c0c1008004c400149001c0307010800c482e0300c107000704000d001c260384400e00c80d040140242d050050283d21010308c04140d0006501c258001c0c00001601c40c00481c41c0fa90710007150708023204540c0201071280c0c55071520f05d1410b130091000d0074169180d00c1c0c481440d074034600c1070740c00020031640 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 671133165 1250 671131915 671131919
    0x50d1205041806050a0608060f190e040b060108101203050a110d0e010339020f030d0504020a0e1e10050a081005090a08041203050918040311030a0203041716 69
    0x1150300c500f06403802103038000d04141e85d4003811201d0200030365a26a00983d80380c001d8000c0e2404c5900c042203030905004101d4050b079a080e03680900a01240c040c0c41643c00c9000700f041543e80500301c682e00010944107140107d003803020144a1080280004082c800c0c0043c29403100e07805a044511220002011940d2a4025000c01011003050010981c0440d0038282041c10090100c84e9040d62141000108061618030002c15898881124482e40c19802080308103090100180000e040074540c500010405040a01c144120090682d1007007104469040c2842094840503189902c2038003d040721002c640c132918036211030b400c20340d80000d901c42006c202c00503040c040402d5a401a09400c44200020783e118052161205d42c5000300400d5601d0800090224050385026089450b00914043e41498407100104c0d040044d1140c81d030800c050020300304805c15a0001a5840c01c00c124070255043c42e060340c2c0040d5680c041da004442441050140002e40e50b20200301c800200782a0815004400d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 671134415 1250 671133165 671133209
    0x32040303050d0b040204052b020a0e0f0f07081311030601080d030e0705060304080d02070503032401030e06060d020409060216030f0504030206040603090602070b010803091801050d120504 82
    0x20303202c1c1451500d420b041240210013407800384240d40482d2005000d5261190b483c0d500c1656440c259038a12140c843c0005240015032620284000540ba01564000c05401c1013101c0b001075000041c4181880345000c810070644a601007030280c0c0141c54072150f40d08068240c900400d512448091843d0184286800010f4403000000e0000c0340c5541c9403070810814050b00007060711000c6078001c09030040001c1000c14006071541008103860b8203010780040c20000b00d80d0ba0103042d9881030320400e24458a040c40000140480c00769403d00c0700c0242002c0040d0013041105680b240d4000700901d21458444a28100b50744450300040303200e660154045544007510030a001d0b29000300e210680006070261540801d1900030022a02900e030014451420070b0b1410324110094440c50104542c1c80d80c0030f0040d80e0000d069486010302030042c11000e9074482d60080306000c0c4100c4c01d500a000281d400400402190301c0b480b103201005070b00031200c0071810b81c2e0300b0b0080e9000d100302d512902a903000303005010844 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 671135665 1250 671134415 671134417
    0x2070c12031b03051e03100e0c160302030a03050c0720030102070506090a0b160203040909060e030d060302040506040207020d02090a09020306090309190b03061207091404150207033204030305 84
    0xc07201445c10301040e000700d501e100f5180c0003c4654075003400712910140030030340307480c10711070307404850b9001d0185004255010081030100002c81140564804900c004455805008081e0700c08840b800450030f008290310341c280303620b400c640c4103024041d06c2c00310037040b51000e4040301c2d10b040d00803088403918149041d0043d0381d20b01002c0c081d1214491880032482c2c0e04803081401a001100740d004609150401c080380008042c0d9040031500355a0711035148000c0902440a40502c403030340140065150700c3c1d0b006000503641c00418a6215520400001005a488961101450350103544001d0107a0782c901101d0300510a00202a42c14403510040115148001008045200c0240c030100a645000c00302640c4c1c19101e4082c035603802000744000b41c800d0801c401000c00e449005421900107a5031440000c00f142e40d401c034400781009504040106000114084038000b04592004502d800d546480003012084030300d0f0780b00480400c880e00010100c040c00301c0c04c0c403070301c8e1035079401d603503880e5680303005005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 671136915 1250 671135665 671135677
    0x40b180405091614010e10030e101122081c030b010315030f061b02010905011508070e04050f060a090605100311010c050f07060e0a0902070c12031b0305 67
    0x8180e040c24005000c40c4030104000f04800c440e41c2240d400c8505080c014003065040805940c1000002407000889a803400a100209802905c00050075101110b56130700b0210a00c629100b9182000d07035480d59108148119208400b040c0419035001140c40b1068030508640c5e030208015102c1c0c01c4059160303a0a181020a401c0000d407420082c250403000150203413003003240062105042a107040010400910b110080700748100710014100748600f83c2900300708800ca048600503903645c41a2000c1050900c964040114102c0260074903c0c580711085039202c1183c05500711580542c0041001c0040801888950790000810f55031245000c000d40d100a0451010686010382008040b52841c0181200c0c2c86c107683e0050400003820a21400541301108524070464040c8600c101f0704864010900c00400500f916a5030100b20801000c1003090000b840e8022030740c120320401110000404214498045500c000080d181401d25810281c4d690300b90718050882e0581c4d502010810194420001c01d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 671138165 1250 671136915 671136919
    0xf031b030509060a0504050c040902011e0315050315070507140604032105190209010e0306040f023d0c081209070b041d060a03120302030106090608062103040b18 71
    0x1140d604e004640054420680e0080d1980c6c11200c404102d0741810781180054a006041c0b030349220550840400300300e0400e0702d40100003540e520007051265204524070f40101821002040c1002c45070920307540c41c030009040601803081c000307030010400040980070a0080c00c040300345d1f0010f1030141000b0f000181103510031103000c41002082e8200c2020f134031030a80100349502542d407032001880c0e020030095000458180c1404245020b40d40300b580c0c10002548121302c12031130380040c002144140a001010a0318082030f00c051050b0b00b600b8844d0b6801c9901e042c01d001e441c001c0d1825000041501d82007404007015007907020014691002c01c2c060b480e510302030040181111700c40c95640d10302d0f0352240968043d040e04150a40300e0440c0302c0176000d015a0704800c1c0240107584540c0c1d05d0f9a4901c1c10707803034030010202294000c00100803042d000301054000300b03410708103440c1c28903010001902140c000440d12125080b2035484102c5031004000751806801003049540d6605987c0c2c0804010081110200b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 671139415 1250 671138165 671138173
    0x40608060406140d0305091c02040c02032d040f0803031006030e07050405060a090212040b070305060603060907030b0a0909050c0d0c0515160b090d021c0f031b030509 73
    0x40c415080c944201c0c8100d45030048042070303182c034000c00c009540003020020344c04c03c102031103d68015036400c420010740c07103007854000108803840c3c03045c030080c0c0c2c00e14030788002550006d011a000e51043c0c0c00035440281078449914165110944040e00035000c0c41e000500c654001c40004200302d00d0000041d0f0181401d103104120281d9107401c11001e0728418115412141c100a0042142e41042d0b00001d0b04248002d010540c81c41e06d41c00100200d03003007060400e4403c032064007400309000032460f400390042d640703140a0025107071800202d0414440548010700414030500043e10315440f035440b00403462001000404907998903a2120701601f9010030549640c00346011042840c41d00d5007595100c40c0e40309118a819510301804c01c1805103084a41c0c81030840c0401c2241c00c542c0708952b40001c0d8070701c503000b0007000b070620301940c516052010383d811055600102d071051280782800140c0c40f00c00383c00d02d80503010038a20b10040300903003485441007a100c009100012103007a0180c000780d2050304004111 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 671140665 1250 671139415 671139421
    0x30a05071211040506070c0806041b090c090605160209100504111201090b0d0f0b0103151a040e0118120f0518130908070b010315150e100f060203040608 67
    0x1c008641d4428010481c604003000708000d642402000b410741e00d40100b1541540e559104d10807070626408640417035503e1500c2452005c50906800030b84090030115004001883c40204045e08404060061006100c40803402c01d11104083c903001202560140c0704080ca41010700d12150306103050300410f031041c2c0c100f000c80d000d5140500240c030022404c0210282a80c3d10f010306400013409800111504481c0d4800d409001c41c10b0a405100d405228203460402e41d85136090040c0228281c0ca0540c0919080c070740d8200d4284c0c0701c0c0341c0380c90250030211030000b8121403030300340680100010f5280f14804d48940c1d4199040c00152500500204101d440d645407281c06980101d9651003810906590f541c80f0825803000707820b112908111202801c0d0000990200e142c0340c402660f000701100710394070a440750050003088440000d207000e03049000b4084c003a09030404103682c0b0600340c60080305544200f200c0001c2c0040050080000100a503501080d10b03552181002501c9900030701610300825488404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 671141915 1250 671140665 671140697
    0xa060c082a03040204090804121104020a0206040204150801140402040c03110a0f17041101030b270408040314060f0709062a0c061d12030301170a0602030a0507 70
    0x11160445009002141250000d007080c1403a41d040900180e8100da641e00d8000b0000b10400001d10141c14011021420300e110340c07901400108601e800b00c2d01032801444105609900003508070740183e030403a0082601a121a075010141c503050348403110560a20200c0700ca1080c010314414000c3d4000e44003441b421501241c00d40642e28405950381900c0010040000301502c07801c400d00784442c0d6480c10441c0c00b0351a05e201d48044400ba05e0542c0d0008811001d10442c0da098032401e01119019190180c81014856403130844103090750041421101801c000f030200104e204c115400b4590180d07682d00e208881220340341c1d441008031340422000c203080000c074018600500b428401c90324079945a032091824201110701710b00c40c50403070303c035012456444200002c003c00d24600c054051a924501c2a0000c01140c11b00ca5507a4407003180961a00007100d03080301d4002c000c0381c2c1910f441403032880c8010022040146004040040541101c0c07000c03082c03048084003034000703a006040301c0d503448050f0541046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 671143165 1250 671141915 671141941
    0x90c040c05070312151e030f0c06030e011413150c08090607141b1c0203130b0712051e0d020304020f1c0b150405180d09060503041707050a060c08 64
    0x119100540154482000043c0c1c080d4070f40c04001c0f05801071024515035a035111404210240c4040f100c0308603009040c02b0050340340c45201d520020f040d000344041032002030882210344018000a40401109036a601406910720394084100e07100601004802030b140f038000d002440c140e507065514040da89c00300d180b20340300da080013500f200759018984c03402c1c501c10b223074424100c01e0445041e410300aa0840c100000d90000300301020324015000f0b9a9a1300c010140001c521900303800181c0f10341021320454001c92050290200000300d1414200d0b5603401008040f80d0032451881510001100000d02180b01003098019502981c03081e00d258018039600b1081107101c000d072182045011151032503400101e003c4503440e0b5040080c1400114204005101007810384030103c40c20031031121500100702e022002003156000c05402450701301149402d01400900505c0041c002819007000307040d84a2200c00300f5000c5070030855010b0202c0714906001e2a100c2c025008040031a800308030418001800150009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 671144415 1250 671143165 671143181
    0x12050a090918060203070c0c0f03110411090613031101141909151e0203070b04060203061c060905150c070611120103050f120403030f08090c040c05070312 68
    0xd100d8032600307420000100c00901107815050140ca954200320b0740440d500380700660041804c0c1c0c1d03401c04194203a0514010201c0e895004460340c4540e4602000851950861044105c4041f14080b600f080e140b1028006401500e103810b5000d00009014030b1a6541c00740100c2c12284240351521041309004015110780103061120345652800300710900b45000c660391990b07146000d0741000d0040700c1c1c40c0d14401400d2031000400c0d2000c11000020381d0b015945840c5d25442c242035a200031464003111381d45103994013102420060082d034001c00415480d81c2c41940102c1080c407211300300c0a40780d01d036041c4a00070f0805500c0c2aa11401a41c0c5e000144802100001d4481c01c00030075610301e01201c2d42c2d904401441c014040c41c4143c0800c6c8404c88240810a001600841c0910010044001203a41079400e0404034000b0101d010020807041000075040034001c0031800e03103400c00b81d070f26940740f0b21610b0a2580080340c156102e403400300000c0350103401801800c04103000360b84289098400e68141c10880d0080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 671145665 1250 671144415 671144417
    0x902150c1b0d1407080d0302130b03150907090b0304081c0501030203120a03110d020c0d050c07120302030c01060b04060908010618021309060b07030e09100303050a090b0c0303010312050a 82
    0x42d105000842d1091103928242c821030b00489032142d580e82101801c0100851500d00001d400142d580f944025584001d005001c184038851f245003000c420606521070700301d40741c5014150708030008004a000c0d003c107500801d05902c21568070314043c5010107030303a441505249040c01105000c6141c041c2e951081d00d058a5021300208040b46208080b90303c1c0d44c1001c2441b0081540307415a18044800d45070150100e580d9912000d6102c01c0c04800860a0450003561702040120600031a50403810000d030410440381100b0200d0b550381480d080072810741c40b41c03c2104500e9070910720005842c480c03400041c411940c485e540c000d045070311022142e0a80e40b0720b1084090f4242080003403020b02c8690b034014034454152040c907070314495580a801c4156442548084400b85001c03c140c400d01da00581740520840e8122100c030391703178a0b0281440d20030070340500000e010004003003142e102031030140d54030a000d008000a165103a81d1511070b142d9481d40240011108503801e114110b030218014402e036201040c5c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 671146915 1250 671145665 671145679
    0xc1704020f09090c0301060f05011e0804060908040306140f0702150c09030703020a0803030105030d03020301180e2404110402040f060f090f0306050f06030d020c01080603010902150c1b 81
    0x10407020030640100191207070046009540401809a40c02d11402c0300804428003000380c900e10f0b1900140409500c2241c00c10b124009040443c0d5081d841002c07103074402c0d4050700004900c05a401c001149002ea500700400c4145403000080b032030103104680d07903c5540c0c1e00021000302e1347d40a10480c1c865941e02d048119100e600004104207130210009016140005800c88000c2907490300018003942e900d6022a215070400070040c441400c080c000c200300724449050542c03555140100150340740811880440c54140c0d24000100141d0091001201c541603003d4001d803203a000301840025010701f80c0e82103600c0f495400500b41d0504150084d241240c0c0f911045001c0c1c50300e08482510900303440b03e000c004010712980080b5a102002c040740c00958000c000004280c079000d0009004054003501340d511a51000700c031126100c1d030000c0c40b00f940c1c000a203420f03c2c050b1904000300e0301410070544002d51114121060000640e00390003d0a000c01c0c0c1c0400300c0b1074040700200c4e0521810b9441e4102600044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 671148165 1250 671146915 671146939
    0x6120d0c08090d08120a0e2b0c14030a030b0f090708070c05060a020a18080d030207170408010b0108070305091b0105071713060e060706090516090c170402 68
    0x385810140c0031200b40034203a0300c00301203903560361501c03984428044507a84104005000b2041010b1280402c00c0480d00001c00900f02913101039250003041c104090711140c1240d4046100c0c62180040349002540111407403800c030585114a0346940204c003503c0c0c0020f15240c54400ea0785401e02c095041c140d4060245c6105e80c942103000c4a24841c01405c3c541440460701001002807030130410f43c2c3c466041c01c03200503200c1454030401070916840403100f5002e4040c0c0c4401340580100420750b40c6140103d800e0050740c038461031424035045030098416490002c400301d400200344d00c0c103411405804100b41d81c1e4400d903546805042d41210010b4803680926403003600d2104009601400f01010210141800e6050007400e40e076111550700807211051010401003a0665001e09000500c2c0290402d410811110258140401c81078004d03000041d054907219190313201481402d10803c44007503018050090031039229004c0300e0180000c580c9000c002104640d940703d80301096401c00d8040c80c0e0041c40c0d04207001e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 671149415 1250 671148165 671148173
    0xc010306030809120f030a0c112d03070506180108130b01060834090632070f0b1f030822080109050c03010608190f030905060304080306120d0c 63
    0x104c541c80900d040d1040820b2096000020005010100780d15515114107181600d80900c142510102c198011850341703640c1301c00b0008000f108800601000c90703a401d0311440e10002482c10410703034052504418005566a003103500841e00038003501081c3c079040c9064841c01c6002c0044610740f040603000d40c03000c4005120480c41048d6007604000c91201e5052182412045002120a030665992140480821214025030000f01200080440b42040f14466510301142000d00d180f250804010007040b140819208280340706850007107130490740714143c01486142400d40e407201a02c2805100706124400c1000d01030b1000d494003035030740c00b4002a06180101d003002c1c820103c105262401d038500c0d02000f00d6110b10900c52800014000c00080503100c0c942000e040c02c4598541043e03c064000760200d01c02207100034112881c299000c060b0403044100e81c00c0c02c0b64503020303d400450b8443e20000c180710a200350200070394081c1c241201c00c1030642d085030500c0c3da5034a0091010380040760190505501007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 671150665 1250 671149415 671149429
    0xa120b090705120a0605010e16260c180604030807020906121c110714010f0203041503290907050702060d06150914090c1c050907080c010306030809 65
    0x5102a0444840725151030000b02100402080442e00b0b91045109100307102d010f00a89004003060901500241052400010204214130b885801e02400c54004103092080b9001642c80303840c0320b1404c0002e810030005000180d4002c004410328000030300c01d0342d421494880c0444080300d500c450351070b142112690034000080c4d0010602603100b4500111815100700c14030480041405842c44032410504401000c1c04034120503403420500d81c840041031001d560030710340122540e43d00b4202904610303243c03a8101c0c650f10030398008004045618070302e04001ca406821246903452120030400001d001100603008400f80301d450700360702000300404585000e02a00040001c4e43c00071f030095140011100d00300341502d00c558001c0340c0d180c024240c05182c1c9039019075440050162904026550500c946c0001e10707141d40a881c00141000001d4a005425031821701c080325103600d040705104501e01041c00d603484101e14815500030380108241d2106943c031a1003a5001e4a511000140c2028600002c0c8104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 671151915 1250 671150665 671150671
    0x503060a0f09150f060b0f030103060e0a120315080a121805190f17060601030b060c06190608070f1205030702130b0a0905040807030f09050612150a120b 67
    0x9070642d00c4010701c020409904100b048104594401300c3e03c01241110300d4121595031388540d60829040c401a15590709500440b41165000031011502c0248a0780d1a401c6c80309400d4020440560008400211070700758101c0201001540c082a1045903962110f988a9040001c001c0c41c511a070135826a00c1401140100c11040c18009c3c150b40590312000490b14000b4000e070384e012000e940c58810040009100b0502d0003071f03d24803415040c500f240b1030009940d000090089414140c46030618022034175607105890414440e80110b40c0e5a003000804e0220359000400c441216074144000441d0050340040d00c003044400010000300007900d03101610200010301c04080725280400c11a01d00903aa07060002c2029078064080020105020004c00144160366801820014105000c11011840086c1611110f135014240a14011008042183c2e0789059802155004001213812114280100380f8180704201d060700c144a81034620040100c2030085204050003031070b0720f10301c0c41c001403802444250 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 671153165 1250 671151915 671151941
    0x1090c0f02102f040e07030902090118020d05010e09060c09010f0c050a0b0f0106110a0b1801110301060c1e0209010513020f0703120c03200f0405180601020708070503060a 75
    0x8851840b0b4031403000e802a50140c0d10f0408603090043d8011807045c1500403005040803c9440d1195007c10304c2d4450500c903100c5942582103010498882c6d070740413200342240e001c10800036980c6821703607a1001d40b810f640c2e07419544110303400101007241110440340103000c1610740349180f42155404650302d01c400441141d05018822000e4001254410498000c00c0381286a04156062007001003505c1203d2003d8099070b0f1020102e0000b050b0107025403508010350b48421905044010800750240001c0c8968801e440000000064038540c0300c511803100ca031040c2c546805d40c1d09140c40042601c401c40401070350002207038004004130b1400d030710000c010200b6898054244481e038500518240c00801c02540070030138041c0294500e40c1c440c880c1c6000190301382410860960203000307800d164007180009141c240c10004894041401c0e290070307900140402002c0c1044210b070541a0300c80003600b525814003510902c5004150301d14045280c90a07500c020740188110b0b610150760b0000742c81903ca00301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 671154415 1250 671153165 671153201
    0xf06360b070813030f17041d0702190606050411030103170a270f0e100501050903030702041a03210708070c241b020f0f04021201030b01090c0f0210 65
    0x1408083c8010f0301c00004d600850310001c08040a0403c1c00030310b50640401d42d01c0c07000410082c07000340d42c51045980b0b02010750180c000035580d51171003a40362140c3d40c281000c200c420b00034032408021307454110b1001c2d9441a601440801b00041c110790b4640402e0000400c2c500c0d86040043c0403a011502a00701480c2600c1d002038000c502c0c00d07107a90b48460400b0b008100c1d172001541881900c400c214480000c1080d8400381600e40303408804e0080e85202e42c0100d88c10010000384001103903400304143e61001c1d8005004100d07100410320001003118801c42d50b03d000b40542e0701c0c1400010750f100c1c4640110f100b01c0e221540f802040b0f17903480c407440d40456000c81d034035480000d0200e486488000e007c04448a01d0600e881000d00c0500040e007061025400608024214603c1500580700d0020b6080e104c1c2080e070300600b184a2020008000c0d006c0d814002281b40100f02c000814401201401412101c004008102d002041c1c81b085074040ca01401030000360780409040d00700405032b58000018500301c04c01078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 671155665 1250 671154415 671154427
    0x10b0406051302180d03020d1b030f2f07051905061b161e0f0f03030804230a0b01050d0804030f0501060305030f04060917150a060f06360b0708 63
    0x50303100c2071460f42030740148c1c010300d1004000ca400c40011072120011103c3d808401d1030701e40c0c0c01080510241c05c1d0b4001c015140c0940c10819040204420f003c1e81618034a0310141c92091403a0303503c2c4002e2003024802c48a41020448410640c00810161080641300741c0ca091071400c1240c98003a02481000d0035449000140c003c00100e40c100b9102800070400410301c0f84600d1001c2c0300e0100c00ea60400074024030350800030420078022079948422640e0509219616035903d04000d5004035005004e2242c0f20781c0c1c2d5124407407410700415a42c0507284100b400010a90b03c0c0c10500003144606180242031050800040c000b044c4016040580144101b00101d10710b626940d9940c150f0700203c0b8080e001d414007107014000e654100b640c40016101c03501c400e0044440300207032140e540f003e1a82d541840904040810100711158105a0140c03903261011002550740300801080301c45520000a841c66407008074422829401c000c0030f03488002680f418026030308088408080d035000741005c6030900e104002c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 671156915 1250 671155665 671155669
    0x23040c090b13030b0c03010626071407051b180106080c1b070905010503100902060904230c1903051003120e0901080607020c0d260403021809010b040605130218 70
    0x504c6100344218445140c0369450503c01600748414003540300901c0394103e141c030807050803c0c0c1c9060fa001c1583c0c42c0c0b841c1003c603002800b42e524402c00c80040c0860007001d000204011041240354080313a810ba40e0b40018841541c00d603410687c0a005000c0001c01500128191407042130117800d00080d40b03094a0300720700c0c1501440c0c0ca0481d890380702c074600b103445000400c41032500b80502c441000d1040d00900c101c504aa002451034410344903494491075489402d120601511081107000005412a802d41410000b90000e403e8200403140c50b0030740061440107000e680719003c0d141c0502a038200b00c82031241103565200c4034081d990007501c20401400900c65103030380c0e2060a02c0c000e107806000743ca01c5040440000703080a40705101180104044240140020003900d04504000700001301011070442c10300f98903141c0d11603176002a501015240c0241d441e031880710401c40c028000840200701c0a4603040600c01600e01034460650302c0381e507800d01613a54040640051400c54450a940d156a4543c0c0c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 671158165 1250 671156915 671156933
    0x605090a1508010801110a02150a021e0c06160c0212100f02071103031303062f0c1b0a060e1906020f060705270d0c23040c090b1303 58
    0x400c101c00611070400403c19004d00b8400c9592802c90402d0341ca2802d010700e0303000b9507aa0740700442c40907a100d03400d001075407082c6250305440f0300e48541466400c0c088800c1e2087d0015801c8943c1143c001e007d03d00c08180c101448074600e4500b0030540e11940c101040c540c00700001442100852402805400c1c642140c03a003151140344e9440e02c00010041e120501824280c05498000c041140030340d00402c038150704203800c000030300308490303004801041101041c6500041801290180d58107503182d036540100c00c48210300030700150060300044528a05e000481c002a01410304072064010030711803c2444261b00c143c48a0300c0703503040607058a044000000402d0640e00d031540c0070310016080280c8650b00d81030f06005554009820346050350030706400c40c0e40d000c0c4e64040416450603100c5403003241101c0b5190070121410b107942281c0d0782c214060792401550f171440c4207407d0480040041e070340100e1052600c1d101c0d514401030960f981c00045030801c209070045500060315413a44e50300c075142c0000019401d0b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 671159415 1250 671158165 671158199
    0x3060b0f0a060f09082d030c07180c0c020112021b030301030602040e09032503020a1a0a0609090b0414030409090503040513022b0e010203040804031b0f0605090a 71
    0x5aa003440c41d10f000c1e00014800c104503007180050b40c0208130450400a40c045a00c4908035040da25400380c807880c2042e142c510700c5802d0760210035000e4240300107609d1701066814900a107001400f44108003500b8021207804000000080c080390200740e940740d0590766039002d08029610030350300020f644400001c007031458009a0044440c3c45e0001018020000c82015054118422000940c107046a6040303080e440e0300c442a00008007802d2641c0391007807510070412510313003542112244080180c401c0c6542d500e45011180c5080c07060070300d94001160360192050034290fa4200c40c00d82c50f15203030fa030b441504400d098150314017a440184404201420284141030300c551260009544d074600d0181445010240e100300881814030512102c0101d81c4040e91004080010382c05584088841d279907404028220740146555561004c0100000c0241c108001c009a071b000766001c5c0c204001c00165004820280d02604020541481d01003010601520190840030001810b21841e41e031079640340c01d0700d08405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 671160665 1250 671159415 671159417
    0xc03110a050a080a050c0a0f05040f180f03030605030d08060603060105070812041a07021c1404080610050a0f060507150905010b2e0e0324071106010f03060b0f0a06 72
    0x1603565107080020410643c205c44006481513940d4524104805400c04094440e480c0199151201307200c1d0b0056951211a901100a2480c0c0c10b800cd1810601004500301e0b208901003454040042840d180c00031312290301610382e503100070076a642c100a00c00c65410141190341400700900003000081e040c3c3c0e015080c16101c0c1041ca01151420b8200861584900e86182c440c1c0c807948801e000045038041624104440310341116580280c0c090411500c0c002d000c2c1c0310160644001c2401f04104001082140c00b40e00350f43c400443d002d440d0307010000003420324850120740416402d020003041c1e02800140020901030302005494080c20f00110044e28105541101c0c243d40d1108210281c1c507060310740d03414103c400324100c2000c020815001056007400b00a800601c0300800d2800c0720b59804000107030346c205100d114180004205042c4d0038420f82c0c03c1e2090341c040f03850341d40e4600d580b0718002219412101581c0b07212800c00e2642e1500e900038074280fa11107804c81f032402215400c948600c06503030b00400302 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 671161915 1250 671160665 671160673
    0x1b24160e0409081b0105061c03050a02120316090504020a020706080403021009060f14040201020705010c02130e0d1412061c060606092d0303080c04031b0f050d0c03110a050a08 77
    0x103044c548508682006240521600404580030a41c0c0c039114440b690340340d89400c00301da03903101c0e6100036840d0800c14400114108000400c202900c0c140c10361405c056541e54454030702041d140e0342044181c2c007690722602d0050340945400c1104c144107100e411380145c040c0c01550321004422240e40243c1c1d08456041d1030560710390344030040c14880d031b20440751010600004088142000c3d40000d40b18519072107a24100412500c8210542d0389416402c841e11228000c10407000c1211409107844007400c101c41d00c089640210384a84411b07a02d81180c15100584060103815551070b001c11250243c03080070300c0079842190000a00041c4c040c41000041c00c46500c03254000ca01e070116800003126100c0c240c00900702c00382541200c02020740a08405ea0381d1600300921251b890100c501254000c0740d0003c0c1596416a5502251780c0c80020000300380c0c3c87c16640841215107600c2404403000c139002d00248400792045080011561513540c82042000007800303c080a9a20000507200582c260044422608 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 671163165 1250 671161915 671161957
    0x403050c12030915030a1103040605010504061a371d0a080303040f0222060608060109140d080d0c1709010603021003050703021b24160e040908 63
    0x60007441d61903020310600001c5203400154030200e4410941503070301d10003000001c0b0110f4080341c4660000030711000c512401c90f131a4602424100c0191600f8880d07140110700d803c00c04144100101701b9072075480603084c810343c6019401107000c903525030720f0780c4c20340c200c110702c544184c201d050608956224000309544a290b400e10901c0d03000354113103e90029070b00c40c44055400b080090004000d81e980250840c0388428011340c5800400e800396420344aa060701c40e0504204017401d41c01d64850025101d0aa0303070103046030340b0340d0019680147c15001d490b416003180e80c120005440c259000c400280d00c101c1030030b800c280e4034000000a4030043c420340030120300445c45680311200c01c0c604842e0b000c2c030a0f000a109a901e150007064050b0504800001015100c0b0b001603c07990082e0100c1e50071006c4511a80070000c1c0e2070102d0307601c50071402c200e50702d0a480100000d84400000900e035000c0e040601c9605100c0c1740804040e20720715004284180c009850b6251079000c6402803001e0a00c1c010300000342c0380010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 671164415 1250 671163165 671163169
    0x3f03040f0507120303023c0f0706050c03090d0302090612060a1806060212070206042c07030903020d0e0a1509090f05100611030d0b1c030201020c011a0906010c170403050c 75
    0x49401c04640320803044041c40247c4014542d104d040d511001060306640c2c1e0501800e03480350361241c084003030701356400c11080c4031a40e0820b400452042c00403c05417800552140d03411002c3e44111400710364881018090f90b4130310b074000320000d44c00c8540113028031520355441c4445e01c2201f15180d80c4820700303a96010b0803c18a44c060040c5000c810310400e5aa1400121f503002400d50b0103107020343c4161031410102030004881ea0000c1c5039040000b91012003143c5001c0f10000c0141050f5002240140541104048510300a5021403c1c076280181020562801c040049070350f002d000941c1c50401210140000311280b140c4a12100008025004030f940d1800c428000e0462000394040c0341000040a042000d0050105c00d031004000810707800f02c1e4400c0341c0800548020300d0402d004041c1c2c0f00c81d40400c0700f010380541c01008507220300301c001d00c104055074014843d80700c198a072044c3c00848403c0000c4056124212101b6903a1203800c4405001d030002400d620660041d4008851036400445112028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 671165665 1250 671164415 671164447
    0x10203060307080609030a030b150d020406030f0b0a030311120712080603030a090b030421081902270604080d091a0c0d0c030509033f03040f050712030302 68
    0x507103103c0c0020511402c00c000b00c15924031440002d0400c243d0341d0703001807942d903480c1c2424a0402d105d280c0480c0c1c450b10810000c00013580035100382d80c0800d1400c04101c80c039030214000c00302c010340000c003400320282c6992070640d803440c0220f0501d841405102c1000c40c40041000141c13000602485210030729100c84100901000b00c06084540b09500c00c2c018080d0700799204070048166a0202e0400b500c0f0703100c07464200c986010f240481e000030404440e01c03e05035a800a0f540307201e0000000c4800307150740103074540e0b0202e1007240707090300048907140500e02c1c1c0b1141044070b8500b000c501412051400703a803003090030f0803e00c0340040440000d010200400802c11940b48400d568007001c94802d25201c0042ea500c0ea0b1607514010746014005008254000e040c000d0040d00c80c66040502603e4490304048900c07082c100c10910003c081d044030555054240200c1d80400c10b910900107160352440d10740b6242c60b080032040001c116281c0c4102c2c000424180704480c40030030301911076240075841d0252240a8406 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 671166915 1250 671165665 671165669
    0xa060803070c0311010c0206040e06240f03040f0f0507060f0201270c08190c080a03140d230403080a05090c040207050c0a080d11070501051209010b040e010203060307 73
    0x99200340480000b0a03a05aa15412a54080440c85291303081100680b410300040902039032020010070f00041a43c5414401e1340328460460324180c429226040c0b090318051076420210b50349609000e00407408248400550b0000c2c01050100b01d00c0015070345903500d001c1c2408089a080c3c0085c1c50420900b0303005552500b05952034002440381c3c2d8040f0102620400e07920000d040c43d1000700604205000f256500c1c0740c042d0109500f0b0300d04000d40301c13804004451100b60101c17800d401c42000000d41e050301203028034240303505940d40310403920b4000103a080d64221241861440e95619040e0302c48610ba951a000c0002c00c6847e5440c9610307150030007400a9100a100d10480ca003028104a5a140042102140d2200c02c4800503201c440c1418018580f12040300003d400400e64032007c01d60380400591504034912650b145031a502c2403a036500c0d1030b6542e81c031480f8007198050194018207a5840c082591000414000050850010002400381c91480f08a03000507540007040c4080f03030a00b400a900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 671168165 1250 671166915 671166929
    0xe18070f120e0127080f03060d0c090c02250e180607080a0f050f041b1d0103050d050a2a0b0411030c0a0e04150b0d15050f06031905031309050a06 64
    0x410130710b543c0f81d040d024801c00c0100e404002c030000004d031850ba5945980010103411428080300070f80c55800314002040400101000752040074800c01201e10b0700c4502c00401110000d200b800da07441c04a080c21101405400004400400c0600089c204002c01c0403a205000343c1c3d98a0301641010034401d0100c801c285052170800d8100300401107a210340d00480c03600240c0c0114400c0311908031350325403c1d46004035084103506a038640015000c214407951181d058a0182c0143c403880c0405139030a0715136100b001141004070706280c00c4519a0041c01e8541e110311045500c092844103000e036600169810101c0341214407412001000b407440c1010051644a400d09442c9120003e04020312160369110040c4014a00318404880c00161006a0000700d400c207400361080407101a9403900c03070750200c0c1c80500800010718100c006101d00120b400182c0c014000500074140c0f040e0840400f0b440201c034181e0566547c44200011030035403040100b180b00819a0103c00612400c26100102c1942d029502c40340f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 671169415 1250 671168165 671168231
    0xa1b0311030a18090e0a0b060604120c08151e0405070b0a050a0311131701181505090604030801060503150907030b030105060303040b0f07051015060e18070f120e01 72
    0x4190076000041b08000241c0000e441c030350f90b59a5400181481c400c60300880240b145039441c4804000550418100b80e800c50000e4450800b244492459100d42c100c5107e007481115280d018000c002c2100065041030107141551200798950004a03483c0d0310000905002035400103d0302a420707031501c00e42d10744e180420241d0303140c126000c1d402e207040c175050301800c01d0035071271003010b500c0d0703030f08254084c16883c0b010709291039444100381000718445044500d4100e9a5080c140041d07441c21001c1101c5100d5981070312000b2169003048011989608003c2410401d201080042070725503031207100f1280f00e03814035580820120403240500d400e40e5406460356000740e1061100740900c00c0e100302907c0d0403c161014098680050303041c0940741c000302c650f0959050707250203034840e1101c007010801c1058401d03c0d207800c0d000843c03440c107100302091100f070550803244241001c07802040c0710b21030b1301c424000c9034902070501d010301c43c1d4468110341d100c801d0312503540e5640e902e082c0c1748081000c10101940e1700c03100c4e01d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 671170665 1250 671169415 671169431
    0x503041409100b0a0e0301060906060521040f030806240306030d092306071b14010804021f03090206030903190801120f020a09050f18030a1b0311030a1809 68
    0xd030300c035021342644402480000314031070800780c43c258000401040200e0082c400140e0f20b101c0038050b035200210211407900460516071425690f41a10703406540c0c0308844802c90025500c0c110768405028054070391000d4140c4429140c18400004034283c84112000c403545c0c0d04019040524000803003441405100e19441c0802540011450010303071494041000310b001000000065410b01c00c445005140c80409034241d8480c04034075440c40d0940f000080b0002d903a07103a000055172503800c200e4000707510090140d0401000071b442d112078110b0b0041410003080381c1d0196800140560802c68594405070300c0070820181c00c0d600540c09810009071800c2030100b035410b00301174251210ba03d101c003412403101800c2003000c54980302c0c407040003003d4000042200f0300700340030f503c40c40720410b460111030075001c0504140001e03404011510850082d8852003812051f004040a10b50b0740c8032000c0d000d1182c0040007204070301c41440202050689640c4200b08519a0901030101032419008084068504511 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 671171915 1250 671170665 671170679
    0x190f020708070b0921010b19051c0204060b07110a050108010602060f09032511040501050a051e0904080a030501080d052a0d11060f04110603040609050304140910 71
    0x10100c191125845041d65460134100407440c0440030802a413400c040d1034034035014000c4194800c0401800032204201420070700400291440200d008082e44020409000d09403080e1034000440075900c00340c40401d14596540c1d00d06015004420261078081c45241c1100d05445d0042144d0050310090902d4040e079410200700951b2500c0003041c00141c50300c902c0100d1400201042a140540c3e5413099084541048204580c0c00244022046a00904581c0403d84918050003a54107a40f005010700310603600d030104111071448201c040b0101b03208490244022034448000b018171882c0600f28896440940caa402400c0300c44c140c2c8603000c980c12011010441720f40c440200c0d02803081a13401a042d01c141e07120f60400e55484001c46000d40d10420041c00c024a0300240810601814001950895034804503d00341403603044074001c00400049030100c2c00c601d4108007458000d4001c1c04d0010f010090303039032140e1440d840364214441e21121000d81110034a056801c2c19401503064124a00862a002c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 671173165 1250 671171915 671171923
    0x2040e01060e0c0d2d232701051e09010b0616030e36090703030c08040b030114040b060702010e040c050f03010e011505040b090114040803190f020708 66
    0x400c907060000034100c00801194014200e0306517030700e40f082c0c500040442152602c90000c1203130b0744060f0070206a48518503110039038820100340000d208102e5941d8014403102d40350341504001617002044d51111540c0003d1207210b20802c42d81032041001c000352034075141e803500700a2038020b49030b05181030049140c8491064a01c0184120b0003c403c10000380307401e5450800b039803081ca400c4003c019041c1d00d010f4109004844c174070152175464840104d0705418441c0782d04102c03440000d50340040410230009204581a04490380184051410700751600c03010140e07a03200b030b4011000703010b2541d4900c42c1403034903115031005c0100c2100e0180c6008440c2c0d00180c40400b640800a124a94401c09006054050000c40d8008031600c56030707590700c0d03841d8410b90307481000a0080d040000f28802600621034000c4003100c3c290b500326005a4207200708000112030500c1c000781c000b0800e030800c0c4800036008034100b019020a01114075810300706601800b00611600032987d8110440d0312012041004080104d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 671174415 1250 671173165 671173171
    0x1d0c0a050d0f1104090506130c0501090303050702060f1303050c0301050a180f0606080a05030310060e01120b0409080706020c010f050115033209160b12060307030c1202040e01060e 79
    0x205a2907080f40e490001d4000d16207801d0142980c0035603020450300c030a1454188040c40d11404030784110035100c0c001100d100d82c882c0001404640200800701c00340c5440070103892110b01c0104001d16010301c21200c0d8900305603aa0045403960f00003104007145d49428001c855106a078907000f0490301140b1076060f5484030110300082c14600301c0b50011070a000d800d41004000d4080d00040302c3d41b5141910380907a032603004441c66240e01d04605804a6260300c070360b501c01030302e440c16500c11040c000c11106440040450701e011a40c410380c0d450418000420150281c600b15014440c01a200d40070080d03003a082d41e00c28040b23540d0051a0000602a290144980d840303e4a03c5180c0025000702d035035400003c03c00d00810001203001c0c0352450018a41e0702c5e03a45030748a002c50f94166614482040d15800c0214254000d50f009604180300050040710034240569011a0080441d4800c80e80c80c1c5640b60301e41c1c00c80d0030828440404206d200158109030085042a01030708000300038407440c00d06092040c0b8005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 671175665 1250 671174415 671174423
    0x218010c0303060b0f0c190203060402130b030d050c010e0703080d0b13020408010501061103070c09111c1b1d06090a09020a02070303350a1d0c0a050d0f 67
    0x6401a9040c903201e82c2c0840094a134014140395190b0b401d0842680e9034022501c0c3d6100c3d44696240d0511421201d031400b83c13401e0380036006144d9900ca5508110308030400e2021007151a58078034039a07141e40d90400a28609907050b864203a0b4030b070941c1e40441d094851500c0c40001c280d00009003080040c032642d00702c4000030603121001400c841c140c0001511081031900d000f0420340040b03408190901c046d800941212031070303240c01c0d50001e032500e81c1c503171030380038000e0080d000b40d079403207010007401802e50030400c140c034090060309180a40c458941004659600741c16044140d543e0f440040c10b03d0143e13128440b51200341040740c80541c1681d607001c50018021a41401154081200d100d140c0321004d54101030714452100359150190094000d503142c0c201d22080c1c0002c0e81c0202c0c141e000401c40c0c4844003540c0e182400d014070969555090050301e02c409001c1034540c55a0740540d1280480c41d0760060a0340c10818007400904100304204411660150041c9100c0c028034204d01c40040c0001503590181580 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 671176915 1250 671175665 671175677
    0x60501030924020904150e130b01150e0301150f050d020d110109050d060b0102010c030b10140c011503050d030203010602100c03020913200913020903030d11070510021801 75
    0x490102d00042d0144400c00ca81160402501040c0608044003ca040c1c0308070120035604e47d640c0d25002221084a4680500350340c400c440140140c5045009076254940036007003c0c00800c903080c02007030841d8003070840d91810000b5030300180036a0f003946078200000d1100302c603c0c402e6921160001901000c0c100402001324001481080c096402641010700038100208800d051010302e0502902070003a8204050040d4601041600010f019210b082c0075050080c0a051400e801c11030241d131611540e0b058400054030030301400324442e409000e50140705840c000c0b4031503014a103140c514039040201c00078600345030041c0f005208803039000a9908648249000202e00351050040940092184084841d0084020840e20302c1076400c48d00400307008584601019510f2000c4031202d900ca004481d00c01c2c2e4031001c03880305090494840d40107001c2e2448010140c4c1d10f0800c0900c0c4240c01c40f0303c03a07041c2c0c1805400100d82d50003030150500c030b441c8007045009415460b1040391340c0c20240d5a00c84001c4207041c0a1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 671178165 1250 671176915 671176973
    0x80d090210020f0d032027090103110603060109090510091a030303040b180601090203070f0e0303030c1c050702060f1503210c011e18020901330f030605010309 70
    0x20340311707103916041d02041d40c00d255103280598043c42d001c05445447c40b040160052901d01c1410320150076130407240c116001445003d510f10801c010f030b60021317087c1d03410490510300c0498180030314071949000380385000003290030728602100d80081da1078a801c16400e2503070820042019072000b00c11a84d2056115900c205030f40e4a0060005d100b8605845100351441000c002041c182e415a00941c0113241907100e1501e82d452140040300d40424a0403019050b0b0800e2000c43d12803202c0c640035001c00e515404820b0001c81a240107201251001c4526000584c040300c00c0c020400b9417000d5051704410b40c5280c2104e4080a980403035522003016016141c0302e06401410580e0400780741c2680c5020110400910440140396040321601c0484041007040c0d074034002c80e02024010b44c0c2450161950702402126281c0e2030000a411095241d81d00c1e0720362101c511380d840c203a09880440c0c0000392080341c1c64040454842c140d00400310344450b000306052521745582100496440c0301d10200e0b00700d030003405854070f070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 671179415 1250 671178165 671178191
    0x60302070206180307150c03082203080a0b031c0f0804050703020616080703020d09091e021e13140405130f05031303030e040f02030112150603080d090210020f0d03 72
    0x1101c6e40005001040041070100d50303507001d4a013a80050081d80c50003072039200c105480030691307008207450003919800303640c03000000d0040e120180c1c0910801400100a150980824241100800c60784411082c00c0703008240c40c0d8025803400b0808032035103001c5409192a035102a41c3d611503000182c03003080c003c01c408040298a41c104000c20b5848801d50307403105410701d0081d540388100903800d8042452400c02240c15007052103031000b2079400d644650b2000d140c08001600940c006088020b0180240e12401740919411000b00300540c070024468040e54a005003212040c1c0102e00420b02c5182060107105840c0710300d000d1404d146401c25800d46214005140140c038600c91803006169a03e120000082459000080d200c044101038a0506c02084a6010241244024060300010154245a11010038540310f01d4501004000310b000413940d450380c032100b02d40d8001d88845903640391540a11406c608001c40340c800c003034041d0300003406540340b81c40510ba15811041004020156500c603100082 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 671180665 1250 671179415 671179423
    0x2011407080f0c0c090604020c100b0a0e190b010f08060f0111010609020403061107050d0f020f15071107080303190914031b060c1c021b0c0a0603020702061803 70
    0xc8100b0640345a0f541044a5100391240c001c0c0b40e4840c460780300c00c40010340f2400d0078021682e00148a80181607000d1440140d200180340000030640c020101e6800490b002d140b2100301c0c0e001c0c1010340c0b454032420b00401d07100c0c41519141c0740700d1410880300d1201503c602e504080c00300e400c1030003100d81c2860b841c0d141d070040720021061840000d9070341c20b0180026030f4154980c010801e50707000303040c00c0c0310001c0109642c40f10b41c42055401011a40a900d80c40100c5125410048a804462040e01c001d040307014051850001c1383c1c0d210180c8040e40d20b00b07001040fa001802e40d41c540f00d06d48090704030f2a00e00800c0715101d00004010300c0310b4800c0c000b441c450651280e80300c08401c6901140c161800c0e08005d2001e07a5a8220310711607200c810141001007160500054800d1003150b40283c01490724201c2480740c02c1c074005900b181140c2303035024815141130b41301c00d026140d40c010085008060b601c51903000c000030728000c2d6015105240c4100036800151f00c0b00c8080310100408688060f0300c007940d031000301740341c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 671181915 1250 671180665 671180677
    0x8010611010906090b01061805060f0f1201030b0106090801051b090d0206070b0f0f090705100c12110714090115091a091305090606040c030605030d03020705100204030201140708 78
    0xd03844c40c1440c420b00300301c803040b1140d0603146603640740903500410b00c000746001d410b507000719540408244440301110003804010103611449001a9040c0020300c03403840081d19081c4c01c126a20032010005000c26948000d4207001800100000e00140c2013002e241e4101501d40c40c0149e26000f400648000380743c58014004003150b5028052956800da0ba0806907911700c42540d010f0303082c0b01c0000214004004d145991402048031501406d0054a0700e0100101d034503428a003a42440807131020301c4c0110f0101040c0300003600c1107454581000c0c012120755820941550464031840b80c2d01d408180140d100c0b850402d0566182e03946442c020340060909403102c0c003507503024076914070040820100500c900400f406c50003400b55500200b40007115a00c0781a2002156414141d901c04000158680391507000f0b517059070414100041e940d03856001290810030296646e60110750001060400c00500300251000e03511041d80440c2050b0a5a000800c1c0030114505811144004a07850090058070310484807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 671183165 1250 671181915 671181923
    0x160309051218130c0206131b180c08090c06030a11040b072001080406240b0a090515030c07060b1e100903151d0a030e030f0c01080106110109 62
    0x900c40d81102d420240450580c2c1c2d0340d07401000e081d01c1039049100b41d801482030b211443d8002d000c0c0c660303c4807181d07948091084800d075040651f542120002032800c0303101502400d54454084540c0000c80c00300405d440c480e0b5500e404104c10903003085003010700814804000142220410703034a407280c64100020b00b840c003d002c01c072a10700281c00500c0c5034440f801061a00d21400401e840d00115000200c0340d210911901404240440c00142c0020b4490b88504003a1080041001c04100d01035208180104190403c4510200002e204810160040c10800003800c00712418481101c0361001444075000c00381445c0026080425100200800c40c2c112152044020f401d003818a0441c1404c10030700b6000d0f601c03250042e80302c00750408910340b24241c0c080540750481402d51854140340e0042c4010001d0340c8039013402802141510402c0201400000165402652001245c4502808060504c0c0e25403594480c158064041610761740d820203415411070380203040c031f46180c616250b905405000700da84010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 671184415 1250 671183165 671183167
    0x18050f150c0d0c12030509060f1306050426070206070b04030207080114250e060c01060e0a02070c08030301180b0f0306090a03020c010203070512130f081b091603090512 74
    0x82c80155101407210b24039406aa1050002c4014001c1070742110426610b009080d0428000101c44041c50b40410307410506200c50203443c2000c0351185c1040f02e6003504e040320802c58042000b9003032002818180e0201401410f52803070900d080d800100b481c800c2c464003c044021090001e4140350080c0060740007801031100910081d06d01c0c8450b1001d1040440d4145034541c51617400d60100607208403050046101611180e45c108015000c2108942000c21220300325034941001043d00c41c028007a2500800d010100542c0300e4419281c000c4441c1080e4100030303020b610a1004018181e0611040741d59040000c074001450000701011030440c00e0303005200d03905440340d10107100f01c5681c0003d000310458000d0b0f0a9503003580f00f12004988a105041015045500ca480611030321100c040089c00581c01410083d0442d80d581e00311b82030307071001940c131040694000f040c5960a1010485000c5010f050840d94039405140800c00d150206c107003000390008050382c50140780201300c4204802001001007031949 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 671185665 1250 671184415 671184433
    0x80f04030513030f03030c0f020a0b04241a040e0d08100e040506161103040308030903160302160f05010801030809130f06051906050a0f0207030606030f0318050f150c 73
    0x1c4c80a0441084c21400a807502c1e100c40b003001c0c0b0412802a5a500c0c40d806400342d02910744820a2101001e40140d81001150340c990181000503800c441803004030305808140b030682d02c5045a03c000a2404041c0601c0c00c1caa500408400302041c0003d40000700d052901c526203410624220150700e50700b040304005600014042400800540c95100307426032000390404444901045845610441d540e1580c1d500600007440080c0e2001c010f542d0010240c4205c905002070400d810004036103440c0140d0142e00302c10002e01c01324403038024100107400c45942910140e0700c0d14000a1421005120190151344003081d40e04640d541c208012407c401404010300c401a203003581e00c40106a00e01c1894452101c103c00807100000081004080ba6910f481d114188100c211041e0b845061056011085000c1c441000c400140584038000c041c5025034a0108101d040340740152100c218440314401034410010200401d5039058200d09841c403003610a003032901024802d15145010b07050081186000b034031b0030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 671186915 1250 671185665 671185673
    0x40317040e060f0307150513060c12030507121a0a180c08010305250b0c0709050c03061311070c030b0628050405070c0203010e0f010b10080f0403051303 67
    0x1034030544480200c5203410b40c44060801800384042e410864051700130404c00c11a014058440c074568260310708100d0f14055044106840d8a241500443e002c195241140810b20160352141c941c0821141802c000900f007594001e0240070b0041a0748003200d03220380000e4002000b4504110401d2800b0f09000111500c0d03240d6110006100c48802c9031803442c0c40c8504032100d01c52682603040381d42250151070340f042d03201d59070b4010380c9048031101d1072000410f40c00111224079000a082c0c145509001c2c060300f42c2007515150541c0d20103841d80007040d40a0081c040181d0ba02c151454501c40342e000002000600c4149444c041e01a80714060000ca0000340004240040e041d0054801c480c00c58014909030140304c4015820642e501c43d0741e0031440948030502c4030341003680c0703c142c121000341000102d40f0f1499001a080d03400711106d0320b0582e0480d00725003480c00c0d004d0181141a0008a454482007440c44800600d4010300510000180007146d020a0a241c018001c50700c3e12202c1c1c000b1100143d44a081c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 671188165 1250 671186915 671186917
    0x1e090105061302040f03020f0d05030c0c01090f0b0a08090118081209070e0a0c021e030a0e0f0102032a030a0c031b080307030b12030a0215091b060a0302040317 70
    0x60700c00d02a0521040d0450b0100941c4229410b13117a0213030000c100241580c090210710200108a00e402c04600c041c150082001003014004c0c071182000100006001c4100043c000000c90b40142c0c04070f0081c0030148034a012035415605070340240d140c504603c9d03907800c80c0c0502404c1944a030089200403024500c0c2030200c004014011800c03080c0300a00341c0d845440000e943d0704072505c00c034040707602c10a020271401c070b81c2d07508407903c0c2d541544110344014200080d20005030303c4500d1202502d034000200a000720703030010a90301c030322082104c0d070024880c01c0c400003039245c0c4514075070704103000b0070306110000b031049101240085450001c00c50b5250485420081c2c0801daa1650580c04110080010104a0507070300c145010507500030f01c16403d61300c5000080d4003034018076140701c1e4420315a1060403601401000a03103000e007246e42c02044000d0030301c402403a0004d03002d032100b0700300c0d001904422251005802d003440a1801503400d560342e451160f10440081c0540d03000106030305c0f11451008042d15100b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 671189415 1250 671188165 671188171
    0x10909260406031b050702280609080c0301060e1906120506010816050a0515071704170c030703030e010c05030a120609140a0c1b050102120718030b1e090105 69
    0x14a003004800c00499450454404e40c103400350005004025030001420300025a140d0000000c1d0030482c401c02500c2980003040303a9400c4007000940c0003000b0050bc40041040140c5c02d04150002c000160034a07000e40f5050314000e081c0300301081c21440800e4843c6607580850010f100740e4104041c29205481d006441d05400e100b000702c1c03442000400750950300b0426038203003200d10050044010034948000c1c4030700e245040c0d06910400f40148203880c0822000710450070064201459242d559042c4844074940481d9204a08142d5002c07034140300d66600d00003412010343c1c0d014200540c001c440300c0c00403600d000c01c1c22002041804041405403200341c0149142c0c070a02620354040c04260349441c605001c840c21101c010740c0c01c001e44408100c4281d219480318603904524688100b627203441c50b00c107001c205040c02086030f04d80c2d400100d9064413003154681d60380059892620b0461b28400d0a0304101c0c446083c00b028194511a50220b00d0050040e035101442c18000c01025110303107814058507001303010031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 671190665 1250 671189415 671189417
    0x1b03070e0a151d040611120a09030f09060c0f050712031e08040201050a180b131806080d030506061605010911060406090b16020a030503030a0e01050708010909260406 73
    0x840103e182980701038800044501044001c0a907643c90b100e0740c001e03202c0c050182007200c400308681c66126410302c800703c2c410740d1b06400c085400c2c07000e803400500070462044503808204142000780030b51588a424440403a41040d01c0c0d014062060601d5401c4c0171751940724107041e11a04076210b0815070403007182c089422486040300082d0b03074001025103642400300c50080c00581d003000407c0095002d070041048911409a8402d58151220300e01d2800f81d010f1803401c20007039121740042041d10102c680300803510002140a2000da4a40700c2401d80d01c0d007000710314905041c3c07650000f903515100c0000b0f484054138a4100204189a5414014002c104241e015186500302e41103e04250905c0d400700d404036021a603d0704461440c0c05031284075500403445441078024401090700c056903d90700d03060050350080c005140e0b00d04180c20303c802280d10400c0302d0352441e410710080001c0c594101c3c02142c1124034400010030b904000d441c014110b00f011700b0800c030211003a4000d480b8140d1690014005440d21 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 671191915 1250 671190665 671190701
    0x100c05040501030b0307050d2d170a020a0c080115080a030c021c021306080d021501170a0b090d1d01020309150706050405030d0f150b0f0c030301060302030411040e1b03070e0a 77
    0x1910708a07509c0c140004d20058a1076002c0b1140c8513168602400a103400c943d83e10540325188669501c2c801d480009920401c3e1503034640008141d8000ca0250003002007040c00020040001c80385c0d005041001b10f1072020f4440c84021100c3c400c0c0c807030a8000300c408550300529aa21030741414501d04001c0c42301c2d00500c50544942181d0402d1140002004040b80555520806072a817810802500c2c0c00c1c108407140285001c1e02a052001420003031105010302103400c0940f89095040d07100802c41198582d030820b200c1014000c800c4940d80100440d00045429101c0e019000035010072030700035205900c00100303810301e45020081440b50200c0584900070041f030040c0890010258080241c5032055100c181180c0340603800c20034469254010183c0c13004000d502c50810004607203260458200340d00490100303070000700f080100725084403000581c2800b01c8040000d0520859110f554040e00a40c00b00005448000d5040943c1c0810140e0004c00e0000b9480c2c045180280e5444042c0038401c9046c100211 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 671193165 1250 671191915 671191973
    0x501062001021804020903032a010b09040f080f162607150207110d0c0e24190801180c0e06060d020a03150611100c05040501030b0307050d 61
    0x40e041c002c8a08035002c21905103c039501c1d54040100a40c02100c0c0b4590501c800c221995120044100000030000011500c0b00b1700b2600c04203260031360b042800158172921440341000002a1602212211580c221700d01c1e540b10444004500c00f58410944001001d04140010ba42000740001104682e4100303490424071b065607502e5041c4240c0031b8510000c1856031414400c9503074080590140c50301c24041c055083c040750034a0085840d20a0b060340c00e603500781448405102c0c0783d00442840303412080d4001c07540c01c0301c41140c640c00c0200e441c003900144144042d41a010400300c3c0c410480e0098040070008100001d51580442c00741c0000d840d04549010b020080010640103404229200307540191069151015041c8004c0003035010b502841c05166030b03021031450440a6000405c0500090f494000c02a05401c01c480d02c2e1030301141c480c000c110304104040003503962150a03502210420309010800140b007500180c24020680c0010b41c20a0303018005800b1312400c191100c40581c140e1051a051031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 671194415 1250 671193165 671193227
    0xf12061b03070504060c171209071a0901030b0a03050609010b01030f0b06070b0a0e030301090e0606090919030201062d0608010609050d1112030306030723040519050106 74
    0x10008031452000301c3c4003484204140d60080c0706000056100e08000103801014250340c0500741c01c40c0c42840ca0f009000010001c021600700034a0000d01142503c9003050018400210114803441101c0c50401d0b445182002d20b0352200342c0e290300910741c03001c1510441d242c180052402000078010f0140040d044c45000c0d20540200c0c80340320040b503405014607191031102d4864000700e420242980c600c0d00d96589090849505c180046c501070101d44401203a0345106580482c41c15101401d03040c850105001031140500340000d0010f04103000021110400b80316007801d0740100a140d010028401400203000c500000303600d20360380b890070150701c1185a40d4540b0383c00c07142145c0034001c40c40401c002c1c0805200c2d52904110011032184140f9840725468055400307c0e484c18842d543c500800ea10100601c0041c0c9024130404025003142104c01d1940c09040840850701545604100c0c011645d03440415407071005d20070000900628001c041c01296941c040c01818034020005401681c2c04245842002c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 671195665 1250 671194415 671194417
    0x32706020702030d0e1e0618120708011401140d111c060905070b1201050f0d050a0b0423190309031406010915180c0302091e040c0f1202090f12061b 65
    0x80c6e5030103000c0c40d081000000b207404000703500c240314642c49803605075101d20103642003245001400c0c4076070010074a100e0511040c0c0c00100d06030840708903103000c21040701003518ce0300c03030b13880d06103420441030405140c0b040041386042da40603103100b103c500905070358070038444140c0201d60501d00c50400c50b00d100b60b0300d09510199001c0c90042c10007000c03401004000710b19081c4040304400b140144240d0f500c400c1503407000d29010030144100c071001c528004010a06c90f91820420840700031046951008946541c40303612103000ca0300b40180d400e1001d607500185072144410002955008218010b00003802509668948003445075450761400d202c0d19002c1c03038002140800403640c1c807640d43c1e901c40703420340c2d00b41d0f001d44041000c1004040e803c1c0b2130703902603071307901c0d03a25155a241c0d0600000720902c5400c24401036515400114040c41300f2258008001039028078040a60f100300b500050b100c0716424005440d02e03045c070070000c2c0d00c5011500502d04070100841c242c0c0c0112082c3c8050014004001400015 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 671196915 1250 671195665 671195719
    0x3060307050306060109140102120a030507080903160f0c030c0608010e0901021603111c0c140606010c0305070c260115030305030703020c03250c06032706020702030d0e 74
    0x15040c4008009203a87c86c640e41d0701c0c4a50500550b04480a40e081c0080c1d43d0700b11092860010780c4034030174040c81d20b0300074001c43e400011910146140014105019112010840d002403029440c01c1c208000d01002500002c042d55000d050b400e2041d03550b2400501398002800741d4405581c200000c103410901c148204d40d50700103003070300d851f4000030f0645041e030b40c1200014040019000f214900d98401441222104200d4030300d0321391320440c00d0b00e03041000714901d940300c08143c103510034414444141c0e004602c0d040c00310303850302c0d0486d5070305042d1a0040021140f03038407600e80e0b420603010045800710303080d200704036003542c5070000c10030509072940341400c0c1c60051101501248040011807090741c444c0c1c00a00c03400c103000d000c803442c1c003501d00c0c4444501c141c901000c032043d04491107004c1c104440c0341c50304001400c0c24501841005105d40d0707944c2129045042041c000c0340401040010000b0f6034055411568008090b9940b01c1c00340070020700751030740450a0501c0f13451040804482000389001c81e5403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 671198165 1250 671196915 671196917
    0xe010905061b0702030a030e03150f16020601030c05040b01090810050711190201080c04050d080408150c0a050a0c05190b01090e1009050a0503040b0a14040501020a0f020109090e0102030603070503060601 89
    0x1c6c00e1081600c05403119034550350100d07058090311010300600100c00070380c40d01846440c510801d0300e2500b80c034203003100701031001c0400840d0007201c01040031070160030054084d0f030030464000621f025958010b030b0300003c45511104a60090039440d00c90440306901081c8204240e841e1701250400f003804051303d0300c05004606110060b58003610015501c02c0c15200c0e884091700d240a40b41a854400107208240c80032030480b43c01c44001014001003070103010454840342038002880c20b50805281568082c02041c00e5281000710214010211506c02c0c81310040c02c4d82c010068075007000d10381040341d140d230300c19039000d44c0d1403c1d285000241c2d00700280704510b0900c064001400414408004200103802c2083e0141c503103204e03600720200441c81c180001d00080034100c522503130b200f0f60090041c00342d98000800d05d007400000d100400869801040b900040d907408a0b59491042561005a079103600c44e4002c2d0f107405240100c803001d5010150300540c0500800c40858840d01d650310101a66030f40102d485038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 671199415 1250 671198165 671198173
    0x1101180305070e1e04060f0612050106030515010e010e0417030a0f06150c0b0a0e030c0a0302160321090f060924210f050f0f0f0c0318010e010905061b070203 69
    0x178080350081d84405d100c281d4403c404103032a540e0f04e5140250b10000001036425035510303101001003246c00c110103a040030802100c81903a40c940a95065441c05c1445140814194440010708012500450051000c810840c1d140c490070028813800007400e038559440120b174a001008194180d4114002102d5070280c0c0e12003070041a282d85044400c0e0f80900f4120140762642400355211000344040e18001102000034240030806040080c5440e100c545604050205c000040c0042018110360075032400540c4034031043d031601144200d480b101c1c2d5a10001c81c40d40c02000c0441d10300d0380400008203c80984e4001440d004107414401c0c0c0f80c00404101c08045255403541400c250844480c6800188008000203205241100300100751141141c0740b50070a06404208801d00e0f03c0760220640041c1d501d0782c010043d2a040c0c50200c1c45100203080401145842c040c14a9411001d411071a00701d160b41000344000c0f41540b512a50f0b0781c000341e801c5030486019400e001c220301045400c3c0e81c07005d50020020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 671200665 1250 671199415 671199421
    0x1d060708090d05130b0d02130e06010219020f03010c020601050109080102030f150a0902040b0909070203160602031f0e010e090307080a0305041509050c030706050f071101180305070e1e 81
    0x25030780d51340810891625003041c040300145108221010f031800c000440710240e41d94010841da4800c000c881e80068080200350000d0100790390740000e10408855891415004c00b10003400001e42c1d4449034161240c1c90741c00e2100c1048030360b2740420a00d04031042a00e414032a09d0310f47c62480d09030302084664000401c0c0190000d130454001001080d0401005044842010780b552403120980c1c0c0030f60840e005211000602e0159401c010311800c0c0d1280c0c25101444c03c02a540d0241c8801c803441010240002d500880030540d60040c0c0c10402865020300c020a082059845503000d8202809100324480c0a04000000b8088000442201c120b9030340408114a41007140e10203070028400580300766a60a07155201c44d4801500e0f00c103122000c3c1c011001401c402c80300b0004c040c54042c0903009417003041002c1c0f00200c1cac0102d0a00603104110703403000d0078525205054004330786d251045a20440d16540203d000424000701203900c800b6240103c681c9030055650760f42d00300c004200c903032010303c6540c040b03400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 671201915 1250 671200665 671200667
    0xb01140906070b090106030c17030a110c040c0201090c090516110c09071106071805041e0507050705010605060310031b050303041503050609040b06011b061d060708090d 74
    0x6148000d001091035040c1442030f1260600d90408445030340c65603545480900c00d0180b00c4141d04000c000358804e98442060500c02d2a881c3d001e250000c0c414040d405000e0043c000c0107101d82d9140c40ea01410402814038a004002c1c0a0100b00e5020b40d61755017400404904100140605440fa48003000002c18605034581c04a85030356500c228100c03d40076046515130180c0c1c80501660154056070f9642ea0041c489019003410800082c01d18810303c0030480411000880c0310200344102ca030308076000103000919040034080c0f560104050a0813514240c1004281d0790008050844140110001c2188a48980c14003000e44010340d540717400c5050380d0f04204006944000381e50341040d80d0028070b90500e80d9910200e4038503006038008100302e03446000c074000001c1e8136114060744120304031100001d50400380c691b042040c034054105410030000741080c070074502c4448850000b8039440a0100480059000001c0010490100070440c0340190008034850501c40c0300050b01509420020f03020b404640780d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 671203165 1250 671201915 671201917
    0x210603120a0f020a0501052d010e2706070504030c0e060f0d2a080d03060506190c170306120303041a10050303040e15030d0e100e12071403010b0114 65
    0x1601404510880b080b02000500c203021f501d0050070b00c0c0480e001005c0603035440103a907080c00072501d500d000911004101404a15112076001402c00e030550501140c0404101c5000442c0c440c0c4e0b1580744540000d00c54540e501000610449008103a11010307162103030f0f240010a102a034070994010005800700703060b464005280400c2d54130403101e1600170b00515a42d8042c0240300710404804a0070000104007260051045418102d9503240c100842ca00b00f500045450013018207800c1c00c002400101000e182c0a0082050600d801c402e2030042904075401e01c44c203c0e442103507031078001c3c03225195102031a240001564055548604c4003003203d03200a10b00e01510740010400c68642c000400d0005a83d2018001000500700c2441c00310100d2a09500b210160000c1c0c112050007940311071224003166a0144444048a0040b1028500f00e4100071b030884112800c0062036078080303401104400803540000e180f5007100d03004c00c060901c408030101050b080351000c6c1003841c049603103006d001c0000c441c550 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 671204415 1250 671203165 671203187
    0x100f0f032d060b1309030314060d08390a05070b040e0f04020f060c0f010605030309060a050a0302040906090507020d081003020904050f0a0c030b0901050423070b210603120a 76
    0x15113900780c3c10f402d8108560035038031401000d0300841c0c0c0c0d603526004065600d02e0346039806641520f031240d140e80e203036031050500d03c21241d104075494114690760f1108010f941c0c00e000d00e11200790400c542003640b042c52176110b1880701000c9495200e440d100085546100301a1000c881d40400700d03001c11b546100101004803070046c4106d0703002c90a8482e005841da10080136000820902c402045203151000a8078210f84440d0000d0f40300c0c0d401803103404100c2c0d560008031034101c0070510309030b030711140c00c04010350180c0141d4100700012800d007080070800e00c0c0036502041c8544801c1c0d08940e4420446601992010b000355400e1005204c0742e601440941042071559400512841c1243c51960b0500c91807801c0c503080034800c5850507040b00042040c402d10b032628540200c0910000c00c4241065507419007a40401c406802c40e1144030b5440301c2c149041441240000c0c904695010b659100340740d04615410000368040d20134542d418045030a504001034049400c000754031180b850240c0600040d03032462160 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 671205665 1250 671204415 671204419
    0x1141002071e0f08070b160302010b361b0c070306060b0705060c0f040302120a06090c060207060c11010c0f0f080d0b010503130308100f0f032d060b 65
    0x100c0018200000030b11040300d040d03007400401402d4100a501003003080d26901c41c50f22648104c8040c80131000d040700301c030041200c03103000c000390280501d01030303014100d11005686d00482d03181300791198182148440440081c070b803050a808c1404203420705851401911240620302890908188000c501c80003040d6051801080b22665076032a5200010b82d03040390400c1c0e4035480301007140ca0400c0b40400030f864000c1041c2d2486411701c1c21010342085d56005a20000e48140c003031350103c182012040c0046841140c11200c2403010341003e08014103e6001e500c141c0005114107880001c00c1031240314800721841d8400c00540c03025040200454100980c0d180640f600403002c1540c0c070005a00c160010300e00f03803003481c0c0c0c0394440302c0242001d41210b103000d0800f8140481081080303111010203541019042d81410448415142e50b061030f00564825001035040500030540426049004002c55045a104643e00700c0303101415003174182d0010622800c1700100442c110802c000980f00c0e08145018800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 671206915 1250 671205665 671205673
    0x5100501033b0106050d0f02061b0115080606122505211002180904080d06032102070303140c010f0906050a0b0a060c060213080d091d01141002 63
    0x14002184104407880480720a0061200c4110140100038040c4e440100f9080300c00c0b620800f0b0a071a4400c401e80800c40c024480d2000007560707015030525800c1001c410404c10002c00074100c1035056040501c6050080b007010388151400515503150010301006140c80050190070b0301415503200b50114a0200450700c108107403c280801c854640484071911030003262021000403201d01e14080c01c00d42c0d10a228100f0390300400841d040040d41510041c040d00c02543c0040d1959114101305549006282074014801d0030310310001f0512000030000741c15062608c501011191240c41c05aa654449110090109000036001c44500c0800c0002c0e0440e1513018001140041000c180102142d140410459a0941c1c1b01e0034812903290728410481d1500043e6004900e0070f052810142080c20b40c040020300554000030641c070024482c0b0b4075100140031401c00c544a4070b1820802900c81c0301c0c94000c0c05401d4420700383c010480800c0ca506203049440700310380801e031103001c0c00c03d10001b9107d0030080700079803107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 671208165 1250 671206915 671206961
    0x1c0507060207060b0d050d0314040c051201320105190e04050c100302190c0309090f020706050408041e050d020d080c070807060f080f06010e130905030703030b040510050103 76
    0x40f205c404008291007140500402c540d452009030840d010600450060045007040000040c2d4415a01045c0d03001110341c1d01c02240c0400e000c50151009044415102c020f006011392501e014a00c0d28550907120010510181c0e252014400686000e000c045410301800c0000c000034525541520341086c0604203490000d80b94401098015540c8201c05000a40c0014440c0c031061810f10301d204866814075010180341500c2c0c80c010000c9001380100b0300300310742c0c9806021100c84c1950403100030b40e500c50400d00003441c01c1c0c1003504058100d4400c11180e080001c04145125450b116003405680c001849184014401e80074066440b07410003049417844d508001085003440c1c1000a0002040701a00034584035051800042040f4960f1031224140000302080c080e00c1741516044d41e500c4402840c2c43c0c0c2d44881003d00280c05400c40f0340c2e0064000d8a85410302080c000084001c1c03100c50f000b40c50610411185000703200880c0d1b0221a000340d100170262040c0720561080d0000d01c801e40d500c10030709407100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 671209415 1250 671208165 671208169
    0x6140603270f0a060605060a120e0a0c1424030f071b0b01150309050615041b0507110906090f0403051b0f100506150d021e09031c0507060207060b 64
    0x2250441002c0e0f4042c4407420104140707402480c0162074265a480e041100c0250040d06071000405440c0101d601c511a610001c0b804200d4640b480384c101105620b003a42d640c005244004000c05614001c2c17003a0903506032001c420304018540303402d4180b00b00d89540d40fa0218401e50400c040d194000b0001c000303c40c680000c4000200c0f620303450044e40002800d516000304a8204050794460070141401c006c0703404081040418016840400031180040c90618840041d009100d20b64107405030005004001c81042e1b4800d019103011485001c5d03004244044208000800a04503038041d802400000000c1548030095030558000d882401c1060800180003014041da40c0844120342072a0700c141c014187c0e0100410041142c1e00c003a0908110509003030b4042609070b03561181c003d21103640021450744031581070707045076104411150340390a0720404082c035500740e03448400355a00c2441540c03100180784101c00d070760030724141091306c0b190b00d46012030380c460010f034020341c0e81629101d40c0c44480030031903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 671210665 1250 671209415 671209423
    0x50405090c12010b03030a030902030c04050705040e09150c0a0309060f09020315070c030810030b0a09020f0907081504090210021501170a24110901030614060327 71
    0x48a689000e46118803801c0240046280c04036100c40c0c06a040500f0720340c541e2004403c07920102070500c2c02141010b02400800c1c5081480030240c2e400074908800c00c03221b01d500101400c140c40c284110781ca91510b0b003040e516680ea81804124200d1044080816805d006400040a0000305800c0100f080742c550f499100c1114240e418034420030391208800300440c41c05005178070302015204501c0d085401e2602000b0003509101e40002c05024000f00401e1010400008210066501c80d04000451411000b0440a00f0803030100300d0054100c20b0b2400500e01d440580c0e14400c8080365500105696242010401155072640060308507a45100000c0982c4480d0040303450000d240d0020400003d411250348180d200503481444d207107819654400c074140c00030809082c41ea03007152800c0000e1b000d441c1a02c101d0040c0114805e5102d10380300f24503da078101003020307141c401d409032420040d0340d69030010030390300c5440011310561080040000620401804070f10385e008011015001c4a031942602c1203d2034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 671211915 1250 671210665 671210671
    0x605090f041d120c03040e090a290601080708071805030106030b011e08031c060504051303020d020312130f0506040c0f050409020117071b0308010305010b04020f0412020a050405 78
    0x50419881500070340e5042c10062940d80d16185010545803002550f0341d60703200d01640c0038110b101c10344600803540c158000c00c0b41c10b80d019040040240212a021609411118040c010302c2a01d011500021805d42c01118000d1082609840e40b90940d40c8204048078004070380303240491001c40030b840214107628248140405144200c2c01c000883d4149030400004008035046041d0307100744100140401e000c048140c41c10403c00c0d0448041c41d00c0400c102c603021305281c4d0000c580103840d180c2004052180c0580d0358008034065001d0340e000300c0292004a07260f1207401d1003d01c1094401c6c0c00b08400000c424500038500b8000c1d0302c02c2c0504c40445d900c2c00d00b05a000d0300c050f580d007107680c40d01b802066541400d000040c01c04a404000c04441317940040c00c1c2941c00000303881503065600000b1940b60180e503154140c0b4014070440503914410b8500075214040c280425100c079823800040050340d04140c400ca9000340b0302e200f104c5040c81e10740109013035242085841281c1101c90164001850340700c030b01503940 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 671213165 1250 671211915 671211941
    0x1b0102100c050c010e070302060f0d022b0e0c01020c090c04030c0b0a030b010207050d060504050f0106081e01150b1b06011706070e0a2310030203061005070c0605090f04 74
    0x3d41e50603458074072429214182000c034401c1d0001d01c402c20040e51007400300e4249141100081d6100c0280c070b00000020f00608070b4501d6551556801c4074004c0e03103074203155190b030b40440d5400c0003043c00340041d460380c80c0c410b8004180980c0c000c610071216858503070801036008002a0202d490241c8030303950f10303104490703580c00380c5c1b0458004030740d10711650341500039184084000e10003000d4003450080010031040300400c02034100d640d550081400c0c07003001c0c003250100c044400005d01a1942c0c55028598807142c0c0300918048612088003489256010700801030741000581403145d642d030905290b01c019607c44003078800c481e0109512081c07802424081c4900800246403414007020760002c1c4242007100081c1950204040701f4000c0304580c0e12604030340107071108145481a8420f4961515070048801c500c450340c8200340e86102041698182c0003144a40000d403145000112901d030152580d00540200034082004c00d5001e000f1903205602405552400500b20007654026401044c01c498150b0f04c011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 671214415 1250 671213165 671213167
    0x150f12010b060a0c1511040b09030c030a030503150d08120603030d0c020d030c2d05070506010308031005032a01090512010e0c0613051c0b0f01080d030c021b0102100c05 74
    0x3c041c441d202e902c0c0c0d031105c4c84070317a81030000704c00501c0900300610550150320320304400030a41d41141e440401c5440c500040103011541000c1d01410003a180c0e07003080b03c204c840751007640310040150400303036040f20301d165100002d20300342440c21441280d0250010305542d0144814480c940d00300c00b107802070003074030242500902895405c00d04002c0070748803030b0f41480042c0041000c4c106a010303610103201d040d014088070361a40e40301070310104950503c00e6001c00f60403031180c50004424440c0450055001e00c07000058855a10750b07a070180764640d0708000501440801504903400e010140c0e10810100620502d0800c03c0262602c0014912680380c609281e0281c0d52100c1c0025045001c02400400203c00c680160070042d50325100422103080340229405544000d2140648080b40e450505006600c070642c286c052504201420b60003200340704155562051a14095006004c1e00c188181d0380340c07aa01070b121400410422058400c1640d44490462044c038441d0001c0510506ca201c48a0109545003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 671215665 1250 671214415 671214437
    0x1e0c06040317130b070c030302130b2a120903010b10030902011d0303040501140d020319050109020301120b100e090d02071e15030e0115030b150f12010b060a 69
    0xc107000c07004000800b0700d0034680118000c80c0c004084c05901640301d141500361928649012000380c002c10302101c01a034280f9201103880100315018100080c0da4030840303200b00740c030038239595440b04a070f00340c40d40c20342c10a800821030b1903400c20040c4210200503002150080045022900c101038203808040060b954601480840d81e024405c0c0d41040000c5201030402d150307890001c2e45900c80c0d442901d0520040d10009034020701103800b41c614241c030300d50341191a031074042c26a9094410710141411070300e00d014008901a41075100742d90503522030032410600004155111079644d24090451421300d546000000703108401048035904c038401440c05001608211030780645001e000750040c4041e901e821a03c805840c40c020a400201d810150124654002004007036006201c01172819400d0b50800d2144440c0c41c2000705548100c84c8100c030301480e1566001060b6a030b40a8441e8001e5000c41c42016680c103524100e03000f030002d407800034000550404040c00094a5600c00c00010021032540401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 671216915 1250 671215665 671215697
    0x2130204060809011b050702040b0901030b2d2e17010b040b090a0903171f0801021612090902030f07090b0a0219030c06050a05010e010801111e0c060403 67
    0xd80b9803c6101e26009121500260040d07a640b80c0703500c8104400c104001c1030354001d40d60b03542c100d041d0591020700700c0011541c40741070230f550b80c1500301c1d080706000312402d800c202036411920201a0000c0442c00030003950300d40700220641c01580b040d090356454403e03c9003007041000391202c0b03001040400c603a0242000d090703419900f542c054040351481289404806007864407021101030340680c2e00e41300000c03140e030310b0316043d165244141c804541c0301d0010310030803c506017500c20000720787c4680c40b425034030940c1c0c80b80c0c6c0030300340d201d40b851480712042c1920004000030705c20b8020860710f0342d1a0078402c0119448021701030407070308101da031081510b243d20144204180c1110440e4098000750490603e0094107070f0300695118080140e00c1003051260ba00707041403610422159100540c007210030310242c104131083d040505400c0c0190840e61445100025030740714148603901460a00314502030501b44c810080302e0041c22034074002c0b0300303141d0100030840014038203009082c0b050780b20780c407004040d200c0940c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 671218165 1250 671216915 671216927
    0xa020c0d02060910090c14030f0a060b090a110703030515030a0f060507080103030503130f080c03090a0510120506030f030a020a0c060306350708070816210305070213020406 76
    0x990308404c1450401030714040342c8004410030980b052907103024800c1142c0d5011902c0e020400c40c4007400c0740034466065040000350380140d000c155003103c50b00c81a40f01e11505008440895000c00d5640b1401c00c03084001a0094204542c0009032051540d544c4420b103021a050144602e41210900b61151010341045003a00c195600180d031442c1001282d81180d402500c1440040c0020700c00f0f0b03041c02d410a08018071000240182588031407056201c680782c0b081560390782c02000c4d134244510020000400d550911451002000c0c40b29501c2c00007408402035810020800680000d800d8010b0403640ca548039401c00003031406001d554001c080f45080c0381030410070018190031079010981041c10802c01c20440c104407a81d02d80c0040c1400003114440101d1207070100f04099418030901620100040462000c600181258402001d8a110001d0884222800300f00d50181c02540d1010791900c001d840ca040701d498a2240c4030b801d10510313110312500000c6503941882c500c0079449400190501080794021 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 671219415 1250 671218165 671218183
    0x20d09090c02030702011d3c0f0f030a02090903040e15030a080c01020909090c240304111302041e0501030c14030a0b300d080c030a020c0d020609 64
    0x10030071141509510007500c034030403104040d0411565601345980008102c2e05620140d000800c80c000c000c0c500031404040c0740c0c2d1000078042021400d0a103440490500c66450480240100825451444001041042d064003100c65403d840341205440c0103071a000c0f000760007580707410000d42e05d80d880c0c100c481c511018000c00c004d81c50f00b0091b605004507100095841c1005502101494035074142020050090003140340301d6502444030014819071000109010580800a40c0c0d14003c0c0ca2030f01000f00c05c40580d40440341c0e20303050200005004900030824074130135104000c4c40ea41d043c1c00c3d10070400e170680c0c01980114818401c080d0300c000c080d40b07180c1003d00c024602801c040c0240c0061000103825850031850400d01010000001130441480340e0040f440e0f110010208440d60394924850020401c0c0d42c03020303405001c4c03500340001c0200f0001420300015080c0f86e40d13511f141d03960102c0070501c6800c05007540c149030b9000e001d4600c8940e800e101c0e6400320310343c0b5401031865107403000400b80380000307103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 671220665 1250 671219415 671219429
    0x30903100209030105130507030b1b070c050319031b030905030303070f090e04020102060a110c01061202100314010b0a021501030f211224030807140102030121110907020d09 76
    0xc88014000500120b403e07230450b50011126141a910051080000242c1c00c0d4501021300e03000400300100400e00c80301c04240d840c290122004001e0b0014240ca86480740315010b80810100781464102c01400c410418035103219281803a41342e980d4030046803544c0c1003030b510000403c040c80c0a40749110390228540d0003c0005e100100043c1c100707600042c0d1260001341191130b11035106c4540342c1450132080304482c20728003944020410950741c3c2d0041c1d5421200c040c2c089200d240007510f2040d8551107030044c0705d401d840c91100900564030340440c000d49540101140d001350b0050588920040342c2c070058180c0210b00502c01110100110300d85045411043c03980124242c10500700a15040e902000005200d2139105001440d4180300403225140b200e01c44c5640c00070154110007004104c03144014000442c800c151207004003100c2085903081c4d001c02d001c0d0803404001241034a0b00c021650314501d404600409540c0104040e0b5404100001812902c00c0056404014900307151544140c000c40201b2003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 671221915 1250 671220665 671220691
    0x3022b03110c22091a0c07030216060e060304050115090903200c3015070c0503070b1312200102090a050f0a150806181006050c030903100209030105 65
    0x30072404440440c8640004002260b0f1402c020040005e081420340c04545007501444152a0808194050350311074001180140a0310b8a220710f50000c0e11441401d542c81502c810312101c3d100b405001c0719400c0184241d625640340e0040d070302441e24145001010345602c80001c5940410ba040140c0040c0b0850302ea100b02009030014604226004102d540103488101c0340d03280b039500002000d90501c49480c0c01420640c549208a84100000154062004040039a89600d541e9141029904042c0c40c00d0050043e1b001005010002202407d105500c51040d000400000c0619111107450425807401d2002003103622000402c0e1a01c000b80702d039402c180e48002586441c4104002c03d0400c00a446900d0045040042000440da15070040d68040c6c001e420402415820145004040d101c0582c0d50074054088404515650307084040b49601c1900d4588078542c40c00d280180c200c402e584180b600b5a10b40c001401005041d5406005100140b81907000241c0ca0310350440c05c2508450000c0e00341c00d12414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 671223021 1106 671221915 671221939
    0x903030708060f030a060e011d03040f090c0516140c0415030803040204021b0d201902011e0903060f0207170a0e0d030c0b01090c050403022b03110c 65
    0x10709d0400b078881d000309014800e80328803407801104400c009554050201c24069000950858001d00d0418541594014140c5058004c0201201e40e034041d40e6550820610400000790680021502004440c14411440250340c03980d120060003074101200042c295901c540c1603c07581004817030a141c4a20641c9249501c0f48040004140420302001491180300001101c801d10040000e000b01141c0000101d1800d101d8490041241000b0700340c2803c0c103003203002c0303c04c82c20318180940f10903142d80c0c1149004000e60b282c1411401015205001d12400320319006004412400c6400b41540d4034a001001104c0c0c2070809146650030180c01c0c203202d4101940041c00c400c115000c2d034942400c60b42c8401d4488240c03504c004002002030000c1c002403015140103008107250381d00185044c424640003203949049080c0381c2c5400d80100d0000002c454010400b40700c00d00841e9021154201c01314 = true := by decide +kernel

theorem cover : BRFrame.Cov 671043165 671223021 := by
  have h0 := BRFrame.cov_init 671043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 671043165 ≤ n) (h2 : n < 671223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
