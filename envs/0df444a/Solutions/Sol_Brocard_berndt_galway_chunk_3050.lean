-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3050
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:36.077369+00:00
-- url     : https://prove2.me/submissions/b15ac093-e13b-4302-ba45-d4b1f6a2e7a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 548381294 ≤ n < 548561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 548382544 1250 548381294 548381299
    0x11404120f0813050306013219080606131401030b180102340309050111031308011b02060f060f040906050702010504140a0201230c03070302250b0711 66
    0x40720079000041940c0000c2400b1050242c21554882c945000c26150160580200d044021a0f81903c0c143c83c082801b4607410b660900036520b03055409101040441d12030441c0a060404e200d6000188004041100340c01140c0a0300c0000c400b0f0741040c1e0032029214840c1303881c00110101801000864132800c501c40d0444903801000242041505225003039030044502c034100403803503c611501c04a08003195040c001c4409100b0a0030310001c0d1070182600010f4410030703043c40031703540700f03a0350b880d42c107004072800c0903490100100c10716145c4095074020b0a04107039002d14000030340c000b100000d000098041c8100e0f00049100c015a40c0e0340c1c280038084030745c800d82a4200d0307200c001040004d05603000741e034852121540002440e14050410072192481c41c00c03807000705c0c2c00103105800540d9000c602982701c030031400543d1100e40c0b4140f0207180350707210b510500700b03c07808040303a040704150740800c5c0650074081854800100390707400b405510034080030b4400c500c00036004008500010320064000d0f00c03000c000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 548383794 1250 548382544 548382563
    0x209040c091d032712010507020606150d05060f040603031d0927010f0c0804020109050f01200307050a05030a0f02010621030e06040618140612250f0e01140412 70
    0x203010214645901704070241020ba51191b040010080d410054950300c0a022200e08032800f81c8640440018401d00a44010150312039000500030348030840482d01e40e400240007040080c0d03990170020f200d020411044c5014018084070114540b0f07103c041d1500034130840000e07074120304489413000188501c6819402c00b6541311a000c4c05040389038400c040214840351a1103455188c248001007081d079039600841d01c00c3c001484e02d0764003172b6400b080c07903041c45401c200c40c005c100007000d500070314501980f480201b8034400d00c20079008112002c0084c200449040d01c0c0c1c098913181d00c482c00e07401e07500107003d4a01c200c246e501e0300000c003241d0051300130241d601a05081003c03902c2100407401c0c41d48031b82c01c02c3c408a00c8500758566103041012000c1c3c01002155514403903602c16400262091185400d6810044a0f003004110300003040311205070503024081080d041c2c14030034000504210408107812001ca45e088941d9140d0354021903080711400d041d50795940c580b50424840041c40d031412403042d01e44204 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 548385044 1250 548383794 548383867
    0x7020a140a0512190b070e0a06020601140a0306090c1d010317031e01170c010e03121c060801051e040c1811040f05091609030209040f0209040c091d03 66
    0x202c4480d030b41c44a40680c5d954000c902d08500701415011500c8800e50003074610950422040d03a021400d01d0560f11518070314100d04c411140001c0710b000d00c40e080504141e103400b1100003000035413a184011500168501c00c804200c1c4405002e000409100151882800d803110003d654841002160301c016401981d5030001030740a8030140c020403d030821415594829418403100364100240c8850007024600b0b80e01000e465000320351100c07107140c802c2035040300c04240c044400f443e03c0300c4032010801c0c01d4010410740d80d41e02880c601810081c0ca001c2805001d070303010f500a00d2031183c4a0ba1050780c001042a0455180101c645800c0380c0e0310020344440c541d60505210394142030001040203001c107048241500e03040500300032031000068444518110a215207441d441d401c8032080d0101c80e011540b9683c503035201d0803d4065850b202c200298800452000c001c1049103c500b40d1050310800d40041240710842504100c2000e03a800403900964001d000150101038501c1c2034602e0410501d500d00074121 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 548386294 1250 548385044 548385073
    0x609010b0a14210916140904050304030506070e0406140123040503070f17030c21070602040902030f0106050405010c020402071406010605030a0c080601120b0d080d0207020a140a0512 80
    0xc2c401c12400c0c0314220220f0074044820030800043e610685503401716419540f41024409801d01c154008902601640000a092003418000e9900460b00709043e62101d00c2c2601000741091300000b0b4281c85036140c11008141440b0301c00b401c048011040e1141c2182845100c440c0008102c200143d1074007000c02c200118807030320280406001080c10008014000d41040c1c00c03045e01c001d21f02c01f210740540c414000740c00362a400150015021103402c040e52103040b58204001c10130310075440003404080c00001d0004141046900a612400c00101c2c40221642c948a08032064031461042600003481e4003081d9000d0310707055004188261042c010010003000306900355042203002d82c0301c1d001180000c0104440d072201030280400591003481c0646280c44c003c00080d01607100540013180d06541c40c004814a42c0b1a014100c1100e5001070513a51190b072030501403000381d44082e1040f405041107400000e845007191000c5280044002c01c01d021450030601481b1051020034030b41c08440c45007900114a00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 548387544 1250 548386294 548386327
    0x101202060301120c05121513030807080a0603060c08090d02010908030c0d06170a0203071202100f11060405100e1516140c060402040e0a02090106120b03030c010c03050609010b0a14 79
    0x7502c1b0f402800310039860780144d001c0424010319040e00310f04115160320000b680844a5a8041046d0520f45040d44402514400405407504000d1a076031501e0401e01d120b64005202c6882203000390102c450241c0310840407404c0c2d680f1183c0050840c1418404500303100c0d06000038200c281c0060400182c901d50701c00740c0781d02c804811382503d926500081d0700103080d0b044c288504409002c54080a900314001d90340490944e00b00700149608001a07607400c440000d226800500c446580031048400606180c1040c60311040308160b41d0905e1450b00c000005404d0340410b0b040f00340101c000043c001c6507614000110100c800c02d010f6030410103110b02c0f09a05910040140a040c0b500780e00429191a051052000b21455020760724441c2d4015101e40380148e0702e85014906603403c2c3c0c40c01c0e248000d001110344000c0c1c00c039840d00d19414000840d000032102415032043c04600c0311607406000d592075000902c80154028000c1303204045041010303d088a0085041007560b07404000c84a18140d5016410080e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 548388794 1250 548387544 548387569
    0x50d031d040b18010e01080a210c02030115261b0f0a0311030111040e04061a0a0b134719081605090f0f090f101202060301120c05 57
    0x114110f001404032800440555016100e104020004008e0945448410801e030f01c0d410311541c8541c00310200d05510030703004d1402142d809130003801341d1801e9040d0b41d00c031a20f1500400b5041c0524544c040c0110710091044e003860f0001c0e0b006054480306462840c41d0010814003420740241a1880c081807988900720520b00950061046040034440c400c20542514440340d078820005506000c1480128903c40800d0380040d801a00001c04940b001111980000c4107924258080c024040000d090f600810050400304415460707641c14944480c4080015039542c81c003040302c07a51131101c21407034000e402e09112003e000c41d502c001800040b4850030b1100c0c0d0010b914545a914441240c4100e66088500150080792100d0303820201480700c1c00040c2503014491060744503051580c0c0314041612820103d140c40d13400074152031a14a01110355080601055561403010412880009044009241d02c0c1d080700d60f005207079a10b140d1802107040030b8800881c00580306900d600100140c15503070129001c5c107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 548390044 1250 548388794 548388829
    0x2010c02192403053903131109011505070507050a0306020a021606120903050f030a152103030509010f2406030203010308070b041a040c0f050d031d040b 67
    0x801c0408020b5841c24a46868085040c541008140411080e048903a08100c803800d140c1c2e611510044c0000c400c12842c032644003140d9041c00000c0c4448075100d00c4400d508036000742c5010242040b910244544c5103024440e1100345000034284030041c3c0e128800a0002a0055080311100c6440d60001102c411041c0e0045518036800030307040a1060f0103000c00b81c400360254002400680c50100064000d503800d020702001503070345541e5081054014070a9031106840c03200b0a680320303d030881c44030380100b80781c003003201070171104850001d04860310b500404000001540220100c4102d91780682c050880a0724920080d5210504201c0d070804c144510201c400010040b1980448a04a102051180c03a00050105801000103201042c2c030350084520860b4480c824880507500c908064a00940e10b1410b000e05550090a01c001d1042c07060201c8181c2e80a000f812a1483e40e0f001000390900407098001d02050b2403800950420751452652010100c0280c0041803103580d82002810200c0140ca0000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 548391294 1250 548390044 548390069
    0x90f0c080304180506010c0201051b100f290d020d02121b0301020c1903030209060d0605180603190318170115080604060908070803041101080703060f0302010c0219 72
    0x3490f070303640d8016441c0070580031040105040010000703021000702200641803040c005000c51580c03914005105905a003001a10a00000392010030040c0c150798950200c00c60610103218441c09a20b1042054010015501d90420300703c81c0c1130003010070807034809980c0000d900e050800507848002c000700520b02c1c4403001c0e24105076131200c4d48007107805448000d4003da10510602c452040d0000e078050300c0902c50581158004424a822806482111101c94003c480480d001c5000300d0140c00040684201312141d8104551180204a503081c08a881d40d915911524000201112400180c0005070003480c0004620035107a05103208480103a20400000714890340b40d41d0041400e200b084180000d804d0451146454620466560880600040d0003c3c2e80d03031b0800130400094404454480c0c0c3c4c03200805031240b0b01418000c500011f0551450f010600090010710368a22030300c40d000c00d9600c0742e11140c401e2400c0d80c004490035441c207a07003281c0044c00c0c00c1200268501481e0740000070407541c078104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 548392544 1250 548391294 548391299
    0x2402031302040509210f09210f0102130b0d0608030a020d020708030a0203040636061205010b160f0804080a050d0311090f0d0c090b011d0a0306090f0c080304 69
    0x881100d10044c010101900681080340c01a4001049801d058805060464035180030708405140f038803c020400e68070030401200724040f052a002081540c0e010002910244566042d40500740e01c610342e4020701d40342030200240042c404800c090320f0b0245814100083c4507843c1c0010700c2c80d40c3d21280388440544c0c41030140844c1c0da03604000810280c8442c1c40510f05050a03104041d59a0180d4004c0105108005030044510b50242c041105200d05462440d000144c500702d0500c0424860700841e000560816007011002000b0b000d454100c42901100030302c0d08101c20000d030040e6050356006c55101c2701301d078524000b20f1002c4020b0009002c0c2c500141240642c0c2d0301d800ca01c1c10645007004c60030305040120f004140701c0c03903e043e5a501c40d0281c0b030410100314582c0000700c0d01d200000d00104002154000031070324000d6584005003107103080c0c80d80741d0742c11481d02d641007001980756440d075881404402e0610000d44503800c0643e0b40b610030034141211a042d0355441d034441c001600807200c02e60010408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 548393794 1250 548392544 548392549
    0xe120a05060a1a060712051e040f0e0105061303060b031207050c0301060611060103020405070909050907140a0b0f070602070803040f0209060103020307271a040906060e030a2402031302 81
    0x1107181480040b00d0f0985480304650b5840c1018042c0c0250a0622001080c8401d588000d40040030403c1080c032000b2755640d44a4088450078041030085260086040c800030540e82041c4045501801a01800c0c3c41e440e407030341c1d9851000d0b0400d40d00711601030180c00104030580b42d0100141034904c0c810005020305000705003e1500315622035100004111041d40301d000943e8000c02d819054070303019507000c95a6a01c02405403140740a503070011180a20301001c000c004000070070604162840300011241000c00c03001001114015400307801080d01c000c0003003483c00b4015100030080301e0312446016003400240e4a4904950b08200d40540b95440a05002811450404c041603400007003401c1c21030031803d001034000c0c07030361010403006540411070706052a580f0700f6030a40400148000200e00300d0750b418501442000e81c206d0f10510016904101003c650f8030302403124442c1942c00907000345454270080d04c42c0044100506c2c01840003000700711400080e01380c01e000071841102c0c0021b501e403010360180305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 548395044 1250 548393794 548393831
    0xf1b05061c0609060b0910024903090204060501050310170c10050408060f010b0301050d0f0203061e010e01030308220b01090c0e030f030a1d101e09060e120a05060a 72
    0x140d0714110340210b0140449426070312000340c20418110110302103a800d060720116a1544c3e001c00c046c41003041c00c149d00c1520303410b400400c0100c0c4251002c1c04130b00d41d910019a01800700f42d441d000000d001002c244406031408624030800b03100d82c001c4030b400854007004141d070140113601840000300c000034184400d4000308001a008002030300614100e61500000c165540410b0091078410365146040000784014035803107042142e001010341d600303400c011100215030302598030600c1960301e8000000901c2e4a4181045040342c0e0151226005075440003400458000b1210400c15100c00d5000300c0e40100e030f1040c000ea8064280580001500410b40102400d0000c14003181442644003100307605050318088162001c918183c107000c0080725000c2e40c102c0d84000700107601030f084005481203810481d40030f280c2c210001c14010303510b44e07440d1010b8011940300381039000700720200710140c02c4403d6500b42026803102101001084e00c00c0b0f48810ba0f20130341022425900e0101e40c54a444084100c02030011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 548396294 1250 548395044 548395069
    0x11d1b0f06070c08060115020c1e0a081006050d11220204030302030d050c0a0f03021614070501080c040e0f04081207020a0213020403171809040f1b05061c0609060b09 73
    0x5010351500c00070080000e643d600e051925a001d05100f00031140301018007840c00342d00d03001c02008036541c035465850b00f5a803137001c903103012000380c18040c0c0081c840c1000121042c005400a1003450b43c001307108240400c42401e4181c060b4a29201c4804100f00000e82c40600007441c0310b81d0286584080d0b08441e0f00070b4070030103003440803d88410400e01d11404e030404000b055030350241c100580c4406040b0440c8204607003804000d0301514658181c4d03588010041550030a5a2090700c0d210035545030442244070340d001f9402540b01ca8900035000c00c507500c503c500640e42c001c3c407400e2040c0c0780201c50320001500c0b0301c00365281009030b4855040c2004602d0405042454400040c608505042c599110f904025440541680c903981d000140c0c0354020003200c4124851820140a450341c5040c54640161284c0c01e224013529840384508440c000b45900e040071004480f0014500ea04160003448501c810b4141c141e841d6804c076955080028035116140607540061207440303081c80e103402c4071030188003641d585078 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 548397544 1250 548396294 548396309
    0x2010b0f03100e0708011404020a0f0e01030303020c011d010c0e042c0f010203040f03080603060402060f0c0a051e01050c031003031805030717011d1b0f06070c080601 73
    0x40c409441d07240042c039801400d20040d004202c82d100807408500b0042250409a015428042c04030301d0340b801d06c5045801284252012001959140d0740092030b032545010b0000b841c0940001000424441e070080e003a90545080005031091031400b4590301c003101d400070050b00303035150340c44c205540e5003111712801c0e0041305880600001200015610002c0100c46e060010084814108030b95070b1800c020a50840c1e6444000319504c1c200760074405035815072100f040b00020010800100a4100424818002c544c0502030b00e00703000909081030400d0300701c04801003152047ca003104c40860000c00050900004088105040c40c02c06c5141c1030035118000c2100e00a10820024172041441040300c15080341c1d014580703810162410984100080c034940d201980c14480c01c0004109802e811401e00c3c90700d52400020440051014490407c005031010418019000450301104500503500c1032540104000c10320b0508200040000316180c012840036240c1e500b111009200c1d0000c104442c3c1e014081c0b4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 548398794 1250 548397544 548397559
    0x240f0c110c0609040c1704050c122a0f040c050d1a030a03142110060f080105090603120304080c0d0804080409021c05250306061e051905040602010b 65
    0xc04082520ba00c03840350f02c00d0050b5512034070b019402d07105064204044098a0140000e428035080041c2d03034032802d4000c1c91054800346244030070741c040001e1481000604516522008450320b4004206400040280d50820310f0032a0b031410b15940e074404d94038071131196120144c90303041c100020812101c000321070192041e045400081c450350000390a600c0719500d0f1428144902190007800802d010b01103203119000001001161024081400c451240e43c54244c01e003412070b501c58003140c40e451510006000308008400500060400620642d4044005411108030b030741d41040710140d591044509982e00100030401c3c00b81c4000603ca0041c4c0c64a85203080d2059007850744500310f0610036881100e80f82a400a18200084080c0710411556090500308000910f426500c01c5101c0c2d41c000f20007809401c40c0051a000c132130007880340c841941d1039a603641000d000d40d14041441240001400c0040c800d05104d124103101c03070103001e4405c0c2980341d0380700c030345940ca0298041d003920700303620704248110746 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 548400044 1250 548398794 548398813
    0x90d2328030b0d120c020a060e1306210204020408030d0b150703080f04020102010f051503060a061a09060906131a040308030f0432210403240f0c11 65
    0x1288003d00440c242c2000380356500d1440c42900b5107140b001002c009400c05e07004080000d045410091400ba011030944044290811640c900300032903105009500c0801c0e041c0c01d407044540c020a4030700d0180f0348050030051815407100885480c1d904401e11a28202d5250172680409042400d04c03418055944040c041c241031340c0c2d503805010b141000f0048503420b000c001c0010113580c0300750040840c030301260500300112304040039100d1700f01501100c0c1e00d019115502c0440d0b0221094858401101c0820803c1000c0001e00303061050035502ca007c8065000c0380078172000440359540c0c402040c004081e1496048554038100302210b030300e055450322000041c801d000c1040840d403104100c0c5e501c4422002000c3c12170303540c0d19141e001daa4003070303092042100d42204902c42009050308a110b030010300780c1c00ca54005200603258200300c204402c20f019202c0c0107010801c0060507615064403242c80190003184189400707c010710880300009500700d43c1e2500c681c4c00b034620300c0d0000c807075850451000010300385811 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 548401294 1250 548400044 548400049
    0xc26030406050901051e0a080901150302150a0201060f0e18160918120305151e0108070504080a06232a040803030901020c0f06090d2328030b 62
    0x10b10400641440000506c80303100080c0b03200542c500d81d500660b0b441d02c0b81d8918000403c00c0e0402c540750640d66291210030111000020b4106084950041c8918914200180301d00810b411021201e4255900e8010214003000f5000828010f00f20a05040c940c81ca41b10064442c504c060600c0440316030040090502d80c1034141d0300120940e00c0519001c903201100e20402402c20803940d9029120500c0d140003014003d5248e08014003a0180a04050584094804010044000e40075099102e00c00798500c244c0c039400b0b410515800b840d603040c0607007810f549145c458104900a842100c26603595405039900030030000d008402290500c40e15034845c0f0f0091060f0303d03a201c5c000400d203101d40d50b46586580d030000303c0c000c88000c1c120440540382c07a0b0506e10b1074107010b50000030724811280035650540d03405c410005413240c41030507000010445180420300580f00c90344011030154240c0c5a00b064400a44130700401007c10b59103240c1120142e821500c0040e0380300c03928200720f000b014281030340d588855 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 548402544 1250 548401294 548401297
    0x306180d1707050715020c0a03031b120506041805070305100c051813090609050d0507050d0509010c120f02100c020a11031e030a02070b0a05070609020d0c2603040605 73
    0x500b80c14480e6451920341000c0e07140e440b070609442c9400d400001c081030500c402042c185001d9100751400d001040d03035500c1c603209103100608260002021810b03500d0f10312501e60040c640040028100086442c80407944140c078001d90a4152200d0384006410800c0260820011140001000c0e080000940c8518010410301c624a42400d540700e444454049c5643c4081190148030b0340558108251146480d0202c050410504240c4080c000c2540c010310141c0510211401d07c1d5001c40a0001c0301c80301076040e105900120300950420840460060000d461813039010b00305041520303440b985044a0b20024540360380c0c800c650481e6428032403410801c58000500402850340000300341e04a5141102082c608500151a0034400211f8021040b04500100041c01050070550030740e5034131a180c0310702076206d1062000310000603004100030300200345158848924544010003210a551140d00c41c9424016590404005100d0070301c200020000340c44071201c1d08203a520f0246041074a4820041c1a5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 548403794 1250 548402544 548402551
    0x7050a060807091707032010120603051b0310060b04061202160c0303110a0b0c071401050c040501090e0c040608090f0a0303050f0618010605180306180d17 68
    0x1400071160116110070700038500d0801518240000703c0c0040c0e200c0e5020355495400740b100761400d250700c618401c1030940c00040400a210050601c40c500001d54104455094014501110503551040044009a414420403040da841c03075001c50b440240d40d5080504040c891581c14100c030303242072410008160f01800b80d6040b01d0840c00c0240c444d1400600c810003034403a00d00a44070190044c42d0060410400940c5442624026641c404030000c05480c5190b44034554a0041d0100d0903000025445050000040c15828451968416840440c038a00745c00d498003030350388040e8090042418021541d200200d6002010032080810306401c1403c4401d5252083c2e0061000700110b0700001030703001ca0100007540500b000801141d5100500d410010001c020540b0705000708041c0e0070104586181900c0403405481100082c0fa040d039280c40c4e4181c0e807540c0403210641c3e520069003000381c3d00340c1d0107000e403610445c4a481e00c10003203520001400e0900541005003014861000c041c0400209003a850030390 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 548405044 1250 548403794 548403797
    0x703090b0904021b070603110c030f1e120906090721020a08030f0304572c0702190201090509150102060c27060f0304050a1407050a06 59
    0x10307920812000314019120b508010f11407926400865500c0d0080015900c088a1041d941040700d2110595144810322421601c01e400d07134024060403280c00e40200080440c07410945141c4c610b100800e204180e650801c001d01d020090b401c03401c100c42c000061003138660141100c000303401402e00380300c0c40500e41041c024810003842c41000040c001c544954080a001e8034884089940307904010710107240f141d20480d4111107640d542e1b4032001034004240b1419510118894000e40082410351901048240030310303e5080c521000c50000744541c8200f6600c1c00508a54001690001d441311140c807011105031b8003881c3c042142400b040201a804101c085040b103d02890490340b07441800101c4842e1004c4e00700c1644150440c040c044c444004501c850702d43e034000e03020780310682d844000640f0207000b003090369401140102900a116841211040c6e0b50100040015080c4100320711840c045030001c590455495010001038414800c0156040003806103400c01418020b003003001107070300c0d00414402c400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 548406294 1250 548405044 548405047
    0x302010f1e11280f0309080702010521070e120a020a0519030b0a0c1b0203033406050f15060a031e05070918020f041514030405010b040609020703090b 66
    0xc0403a04084203c0351031071021070180195407103103582100e0342d40a100c048008103000800c0c50340c81e80e000b4054892400d41009132a81060302c250011340e2181d000001e11340c440782030071099110740c451078001940031b00b800d9580d071740903515001c041c071034404441c4114080607031100f00c400d0016540c0184120a50394140d4070016100b00140c548558004184c20040000e110b61003081055a810b44c08140395031341580c0c940c138803900081070140503510555806034140e001009400c1c01c2a98803000b150021280da42d0041a9049480c481c404121100b1402c07941c15807034201344640c03545450304040d0800b0780c1c90340741840540780c00d002602a1142c02c12480c141070b00c8050000092002202c1c2d8090018020014050f0b81380c8088000d00c0d501075401110480340442c05107800c2004a4402c0e140e080346510803c51a141c20003c142c0d0444600000c84420040d107880302540f80104100994051032160300003040100183c000c10003034503016002080c03003c2c810720028000c2b0f0352003840e840850300c201001a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 548407544 1250 548406294 548406311
    0x1060e0c07020112050109140f06010c030806031213060e03061303030b0a210201121a040504110a090501140d0b040303050711070e010810050f150303130608040302010f1e 75
    0x591341d00c5030742c0d4603002d0094039200000481052940115007505200e2100d040c280d540c900280d004120f042c1c440c42d0003c0d11404008000a0149014503001030004080310300340c403400c90780c90303049501040c4081c2907c08804420065240c1000d00200c0c031103021006040c40c1e10b01500f0011003c00c1c51400502003507100c482030b03055602c0c6c1c42502c5028202560540602c980701c1c0b2a60b00150000074005ca0000d0134100714020b0307030031491090400d2880042c1e89040040340403410032001e040d02910a0301c10201004004020ba81c501c0d07000002000b003104046040d614003200e10280f02c050711a02da0061800455107030025042c2c802c066403103641404d001889841c0e10f0000c03548017500c600151407034408d190000c94041c5106030841c0c122010314003119000c445810180c0c00344e520641c3c0710b403080218440400c0310300000c0c2989204a1b1800307811241004002c80e420b80300c01300c469000c0408a07146800744014542d082c0280088001e0704c031014012000800d220041c40300c4081d0800c12500c2e5180c0700c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 548408794 1250 548407544 548407547
    0x90f07210b10031b030204060e060304060e03030f091b0a0b030711032704060305031e0f040e180a05030a0c060e030f13080a05070e07020c040e03090a060201060e0c070201 75
    0xd9001c100162030805060100107010b4001c1a514032903070030b842610b500312040c00d41310f4000c942c15105903a4402c000c10344c201081c8080c1c3c2d08041c2040352040c2c3c80d280c502101c0c0e0010000b03903206088081d0f5034001070034903000850900010850100640d20542c01038682a10703244840c4046034810300c1c54540c2c1e03654001040750740301d0040203110818000064001c11010902c101c440f0258103608580da03d1121080410040300e00c41d1000816a03041441103a01800d100e851380000802005440e9103000310810a0010301d41c060b800c540743d41c100c488180581581d00700d0900000d202c01034000c19810b000d94850507642e01401d0a0042003141d0300305500e0801080f03810100071440081c04413501d40408924800d01e54100d1180d481000b2160130303000403034078000202e07404104d80190103448800c1c240200204800401040541944562003c0101640b111302c10410407041c0c0c48080d58071511b04408000e002c1d20301d503110804581c1041c1e4140011004440110307007082c18200c00f00e50b1140140300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 548410044 1250 548408794 548408801
    0x14060717091f2c100e0709050f0a0b0d03091a0f030c0c0105130c0b03060604030503070309140406060e06070501090b070203040f0501030203040803070c05070906030809090f0721 78
    0x46040b00700352803990344010052680000c6101d20403481c0030040482030440e0891165810080341003154451300c0c903606001202e0b888405a00301c0d88003601c0c0965100c00c00d0100365a4180c2d0300491185041080140945103885084001001151114400c525a03200103000255a02a42d0072409111500c4c2c000070020000711041d030010000182e40303d02c0d00c40c62031032058002c40e60302a225401c24001490704032030403054400251f4030440010084e410300703248003042d400083c144d03500501d0030000800030890030409010072038440c3e6140740d0340310b00b00b001c447d4107003900814031030080e814a1010300c012034020742e4440d080d1505484403a10754140f400d005014010401e0b0151995610f00240201c441d0301100400076103101115285015540d400110202d1100301c2d005400740c2e00a0010501c0148102c0320500c100f4082c108441151351180451002c848c042d0380101c41040001801d109142002c0c0c1c0e11590021011008442074540003001074621640c8040145c00749035015100d26800503d41e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 548411294 1250 548410044 548410063
    0x50604060914010f0b0304020d110d02040905010e0d09260a0f031d0904081605120a0509040b04020f0a1116170f060105030c012a030302071406071709 66
    0x7401405071200d03052014041c2c41080c0150406620b00d610301246100421080301e000360703400b0f002804c099100d40c84890700b0b200407030205507100c0a01d409600c00740c2e0307a078094804881d0046000140c5540455202440c1c15002060b81c1c0c10703c04004802c002007400c1e41101d00e05842e401a00494020400c1601030500f01b41400040c21204500e0808050503400310108000c0f00d50310080350181c0768403034200b0680c040f0032980100503443c00c020f00f0300c222491110b4080842c0c49402100c00305c10720b00380b002200385c21008418000580104e80300703442d482e00c0c1c09620311000040c3c0e0118a4401c1030b08105030700380b05d410000b409024400c44880f9948000300080c40103549103441c045211a11055160855480c405150300c6610032003400d201440e4000c1841d0f412544000c004000022024006448c5503041c0c8003082d40c800103241501018010030355040305020311a6500580c2c0c1c0040e481d084c000c081c4c02881224065010030200704c1110b0300500c0d094106c0b80010300000c0f840d5a6100c481d0b29180703502 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 548412544 1250 548411294 548411309
    0xc1003090206040b03240a15120e0d140c0606040c050c150103110f0102151806090c0a0b07050a060506040609141504150909031e0c060b010e06030a05060406 69
    0x400280907004d10010b14000e9540c260003841204803285420305501c9032411560740907240540810004800d0203007002c0214060400c10764480c0c80000c0e50040356451510708003584c00006560300d00d2a84004441d141154501c01c460514254511407070f41e0388001030a0a0240c0c0e50340040c100c41c24000c8085d9100c4810320030031901081e003140700c20f000114013880103d07000c04841c10402d40c0c5141200c8039180c6a6410703401012410b03110b21035104c00c15000703000141041108947c100c0d000105001d0140308540748001815042000381c140032298a85503c003410078402030201d04002480440d00100564000e10041140e46540000400516142e07018203d071601e40656402000c002c0304940d4840d50a44d54460751000e00c150038007050700d4295124034035604038014180054200c0707038803401400d40a407400782002c800b40c43d001e949106810243c50040346410145004101441c0903a8245103000e1900291203c010360114002d4003014162000700c5841d203001581507203c6078022030040468 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 548413794 1250 548412544 548412547
    0x605060d150603021c020f0409031209061d0a0c0b13123002030f0309010917040e010f1401030e16060905031605010c150902030a240606020c1003090206 67
    0x41021910050074944000c17030044010201100020440d400441030150b0080d000c85100f44a034801c2000501c0e24a104800b44800c103410440342c03490354420300c10b46a100340e0001503591a0074450110280c2441c40000d40d50740601c45103000502c085c10701104494020406070788500314280c0c0181c0e81030280e0814003440c00303501405018000d00104501901881ea0484c0380c42503030740902c494800d1046203890700036078410802c0d0407289403800015640a031803040006011095503840c10520b10800c410390b8a040300215013400703020311004246004000762420000311920b45020300540e070307010244640c145607542d551020540014012090180e045400c294016619840050550000c41c01a80c1c001e200320500710004030800c0c451101690340c140c40b4001c2d8080c3d00c2c2e9078000d0380107050140742c010300d455102110042c0c800304a5100070302e125003849036a080c100510b0209155820602404860810500308501600400c846640031003c0d580701c1c8600c400b80f90103901500d10401c0003508407a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 548415044 1250 548413794 548413823
    0x29030705040e06030a030e011409060a080f0a0204120f030201020c07170d1103070b1305060901091a160311040b030103060f06060c1a06040605040e060610020307050a0605060d 77
    0x910000a0042d00c820702c40e91074080d240d2609040d0303900030703640004002c02e00c808001000c0b58014000f03d11380804400b055407070504100c000c00c20941180d490702c3e021481f641c06110840010440a980c4010140e5085041034a84207145103034940058001c1c2180c1344001d2140c081c0340c800e4046609500d42c030001c0710383c0103640c0d0030720f505941900307610b4030128040d51380d0141e48039108080708954803081030000c0d41003d02a80391424040d40c050042c0049902c42111200060020301140348650407081c000117444481781441d9039009a580005042900004104203500e482e03170140c440409001d180002e00c910f4038842200140c480d58000d030f11841c0c0080000410001c00e90400c02c120002c60b1404e1010355038401c0141c40b080d4074240003d02401c0203121a05065072445842d5502240081c00840d00c0365450022404544c46c201d0071a401d1b40184003048114201142c4048091040744003e506e000d0243e1500790b143c012280000301026110390200e4495901e4103203d142c0903400c401c500c0310381c45 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 548416294 1250 548415044 548415047
    0x311031e3307170a020c0309121e0303010e0a3305181905060a0b0a03020f04090203090f3909012301030216020405060301060b030109090c05040510290307 68
    0x43d031682012101580030000714058038600a58540e8000c0000850404071381c42d0030461107001c201e040711541d11807610040700003000310418110505040c2c02456895060244100b04042c00501184002d81031003000d014096010014000098002c141780d03000f00c020415030181280c3d0390b88010303400a440c1296142c00050410b00300e004001210006900805501a2600342d82040390540c0c0c0c40100d5010070001e000c0764000429080202c2d20740185403480b1301141d5141500103400c80e69400f41d010080000864040200c0003408007030300020800b605159107090801044a00d90340310004007190300400900640000d032090480080207030b4503c1d82c581202c540041414103032100d0084d20880c414481c0d5000303200b00c0c0c1c0b07424101c00381c04c0001402a003c1c8000f80c807002d415660159a034690000f4800d210700003543c0a010b550b84040740508581c00c0201300b18029410852181d89084207020365085031410000c2140c56104c204141195012440000003c105032180440c070000010001141e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 548417544 1250 548416294 548416307
    0x2030c04090b09090604120c0b070e03010b0a0e0612011107030e0108071407082809140612010e040f060f1401080c09010e060301060b040311031e3307 66
    0x480154900b00a400342d018108008030300203440b101c105822000200d07000c01d0907250101400c2e911403c000000783d1155544000f000343c2204ca5400091a50039840d8040c6000e0061220006048843d8103120b410503c000c082041c02401d403610914202d5008000c0780000c0d000388100d034040c04013403500c030a074900300600f00054406400b0700082802c1c000074a564010202c14800a6107a80010300f00302c03036035075403003070b0b59001ca00d49101e001c0c95041c2103601c0c0c000c5000403145411080e40c404540500d40450142030018080a04c0e100303541c20311a84200010301001d143c1141d903450031075922501e40317060210066031800806030070f20341070141c10401d40e1590780014004551001c9ca14640d6a03850800720348450140900f5540611000300401c108101d0380c0c10300360040f80040000516035502d00c21041c1550040c1c1c0101c580e00c2a1080380b651b20301d014040554401070312040b5244d42640c8082c05521841380c1c1000d9259100c240910720191000e4451450045040580050f070b242000080a04007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 548418794 1250 548417544 548417549
    0x1110f0d1d130f050606041410031407120c0504050f0d02010c022106011a070204090309050a0303020f0105010b04080d080c0714160503030a0f0305060303090a030c1401050a090b0307110102030c04 86
    0x39a41000e000c50fa150502401f02e9045541e051145000d00401400f007080710b00c0d5042d40702d8101521850030348690341010040d0380c006c0800b500c1b0002911740c0300c0d08000a4031241c4280d0428007006210801c0307a0f0310b076400c882c059240c0465080c2d000041902c0103a401c3c0a154a01942002e2a1010071700c040118103e103c04242c0c44400710303000e80c0e03030702d4580400048105090300452441481071303c1c01400c0c10381000b00b500e840790800072040e580301c0002ca00e480c5843d610079401a0701076240d40401e0202849143e0143c5070000c003840c502410185480d6890302000502070030020b20100041c1c19101c0c900c03c0d50320550b803021132420a002e068400765540e16a41c01d5a14841c4403405001401d490000b045a460110b640c039482c2c2c07002150386095004060040c50203801d40010481d00b04159102030100000c5c509c152a064074660906200720110404482c0903418072008200f144950f80d0411000c808440d541d00e5969036a568441301150001c4569025030b908c1d60020061216010641001d4001d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 548420044 1250 548418794 548418821
    0x3040303020f191112030f120a050c0f1b071d07020109200f1503070207080706140a030213060305090c0d020a05121501030c0501110f0d1d13 62
    0x18482400199074480e900411030b81e546100f00303104030000814540c000e42c4980d800900400220015407425429940160341000c034105000800031000102013400a401c540e20001c100300350700e0403180c00f4142d0f201f81442c0c1c0780c46030340200300b20390201007055014642c0500341d0250b90380e140c1e5850442ca55110b0480c1400071700180c070300024628030310520411401d10703000001c104a6400704c0c1030140c090105080440d40046080c01111101d4407102254100704040020381d9650f8600240001c1c10704007541c00c501502e1300700400403c1a990b010b182840141582e2018a68031504510160000c0c070601c2800c070035130045104c00250300c6406a00461003100e540003a101c507031210307204104030344140e010004d511884032002802282440b000f40c030100c00c84141124034020310241c01c45482082644122922510304d0b50900040d41e01540d04102d52034054010f101c4402c01d035110a0300c4599100c142001c00c11117807200f5030030101e040031180c1e6200d0060716540c8080d2230480f4010181005542200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 548421294 1250 548420044 548420053
    0x2010306090203070f030b03010b15040302030105070804030c030f0309050a0c090506220b0105130803030703060902250302031318110430060e0a02030f01062d0b0406020304030302 79
    0x26520007a0084034441e11040d62a0350140e01c80d010f00780d0040003200c105903015940d50321a1400d0380c0b64000c0594460010f402d8003512285144101801d585009010768100400030b0f00303120001b600441059155503050078032458400245800b10000c110440300a4458414410040c0900c81d102484009541d01c454080c40540e80e000e0911240440501c1280600c05100e01100000352142d0b00c0111142d9051401030320301b030003c07502910080351540107009284c00003c14090f485815201d80c40060001400950030b04046d0140c90401a03201c02c403400300c101da15070030501014400d20460341158208501c509045440e107007040c00c02c984c10015410b00c1454901c00120070390804060704c0840300216514000102501c408521002c12090740750003006803071a504001400501414500040c840d00811016146004040c40d140c1204452100e03645004401c2c0480e17660050300030011a030340f100c5012443e01c2c0c9450030706103208036441130010940c040b0300490301c1c41e4048014001c9a00945c200c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 548422544 1250 548421294 548421299
    0x90c0a03080d0e011e0e10230109050103030e0609180a090302060c0f07140718021215060406051c020c0c10030509030a03050a090c080123040803010519080a030c02010306 75
    0x59080324906070105845030038583c2c0d113030821081c40d0084d411904402069504400710507c007403040d12000800324101d03000000d941c07022141c0310f062442c01000c4070b030018026545140c030068a181400d440c0c0501881d4001030260264070f40000300c0b8000a141d600300070302460f11000701d400504200744e00f00c0040c080e0102141c4408821810350b00450190f00c8924a0500c10380e560105483c0481d50b0641e040c003a07400300003441280da07860800500705c04074002d81e035105582e8900c14003c00042400c0c0018404070030045a507250001030f5020340e2800c0c10540e65413802ca04121017510109800704400a0000511540815002c2006201424191950500c440c5183c80540590780c040381c0d0203d035944148035010303015110390000e0350801503540d0005031020f03181d1240101c000d625088005036a441d622515510b21005c0d20f0841000054011840c02c0e04250341c0c1d00c4210b100c18840c0c6480345606601d03d4601304480c3c040c1c40020002c10080340e034005407510b8041c120881c0b1900a0b400b086c91700000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 548423794 1250 548422544 548422571
    0x23090f0102070203061609030b04080315030d0e01080705090a03060906140705090118030614010f08030903060f100e070e030c01030612020d061d1e0705100305090c0a03080d 76
    0x9540b20720f41d00401803e826680c200768003034034034619040c00e4104a20742c400000441d5910080a000d1402041035a0b41c83c40c018103103042c043c0d09020b440e8040d40c401c140d03880100b548400800d210b010240707000c41039034490322021119405102001d81e4804402c00d400000c000741030380032403246441014241700501c1d0b2040310b80c0100804668400200c0d0b41000025001d611502401418080402d00740040540302c2d16070800f107640f86191546009050381c014011b58070742ca0005001411030307200a514181c489804030343c4a00002d8680845400386001051040c0071507031105024010b4206030380d08a180c0f082005122044120380140640503091502119500c28080c110503940068002c2500c04810340c24082c2060030030200781d400e2903031811030700c800c61801c002c094076503e04d4900500704c0103040d184080c40907541d80e110114540c03040d80c04114a4071101080541610903080c0050183c1d19590b010b81003107110501250301c001842004000c222040c00179058070a104242000345038489981c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 548425044 1250 548423794 548423797
    0x608030a120b063109230105150d020c0c060c0d1403150603061201151403012703091503020301030318030305030a0b0a050901080303041a072123090f0102 68
    0x340c01d5028255041c190b4844101204c2455101540d048100078442c1d42c0c560803800c46d0b50306441c1041030038541180104016081e4282400f40070100e401c040c00040304070000c04244182a540c1e00041e80200b4010b190380424415103440306000b0f0b082c15920042e00000c40d46854404541d50007244d54840c0d40801e5000240c19644203510906170010211881000c100d00c80c0c00082c00c60303503c203009481000309202c0070301071000400c1e2500010001f030303410948182004403446041502a0b8945004021194008100381d0a800c1a060101000d00b40900f8112090b40c00f82d0015040c3c101d40034401c4804507490740c010350407a402550303603c1d1040c20301c03225400c8909480c032001c0e001507018000b043c070148240d804a0000d000041003030000680d5040818504842640000010f801c007000300001d01049c08542014440300400c0c12070589807100001d0089580c508445c01000e40360ac241008000065100c408058451920024109002c40d01103604041c1110010014000c0554130110b4040500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 548426294 1250 548425044 548425057
    0x80103050d0305040501020d150602010b0102060f1611060c1c09021e010c020306250f0c031808100504060b060c070509040507051507120e0d0b0a0608030a120b06 71
    0xc0107000388107075100c1d0490103048050002d4a1a544c06c000e00e0600100601c0741e2000030400c595140e542c03524080380a421980c001c1d00d075030305642001080200a00700c3d1185107620807801070001d030320001d014804507030801c0320b101c4047d42e6102e070f20180b104c200d042d038020f403070360000f1620030003000300d0300e18600e1058810329440290008080c0b51402c1110b400440c0310050a1010b2500100400f04d5400103444c0c0101940d00d0190f4040c100503944000c107840303070038041c41443c074145041c803007100035030080201003020005810401024050340b1b080035815848001000140115156201082100070040c507040e201282d9261501a8504503410401f080d03540c00341300d0390003404800c0d241509103d10400c4c0100116100e00880d000842d140d80d88805030b0000c5002005525152082882c0c0180075071400342d624010b000703950f03a285141c2d80d5002440060158410103a80701a1607000d1000090102604084150701010844402e071a90103803480803e001c01203414082e0441c000103005842c412075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 548427544 1250 548426294 548426303
    0xf020d030903021e1f200309210606152506050115110607020712020a03050f100501090612060f09140d08010b0405030304121b121a190f1104060f0f080103 68
    0x2846c0c0d210f82c0582030f145080c110450100362850111030300001031000c41c400300100b0304c00075651014610b000b01007011076406401034480c8006400a410b02c0302c1d0a0095107064060300d000c0b44e0801c18521826140e1440440d4031040501ca956109c100c02c501c0368020304201c1000510100d0b400395510b60011304180101c000390050b0810074104803442c0c0e003180c0060030130f03030300400942c1e0004000b030010046507040a0041014080d0000d04046045c00c2e9017040e44000c05250410b001403048082c078818181c0c1c655400180010003680e1600300c180a010b10100241020000b8112582050b5005c50b074505580c0c4203503100340031a070b2102c44086990055005190301a8014041071113404c90504000390300900a416040356141d640c003004614400d0340e0814084028141000c404120030582c0540c00c9a45003030f0319100c6840e02c1514800005500d800300d880700350303d0b0f00100042c51442e034014100070765000c04076540d644c1c492402424015135424424005200d0080d40c4024503c1448254140c9501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 548428794 1250 548427544 548427557
    0x160f060b010314160e03030a09180b0a0e040f02130b03010c0c0c0b07031211130509090a080f0c0a11091f18060510020f010e0a0f020d030903021e1f 65
    0xc12130300b5856645400a0780d014050281204401a0b0301000076050500d0702e940c84940d0076061a44400c0480090304030200d915003000d40d09140d03942c507019900190340c0484410800c959440c20849034900081070003a4002008440410200710309401461846030140d009000803003a9100c100da44101407c0d0140000072414000e2003000d68941c010300d8800d000b86001c0c01c0c0303084480250001c8901407503c00d401004000b070b0000898441c603100400400b0219000c105516095204c152908602c1c44014042c40c000928840001d09420030341d003200d005503007100c5d4204147d140c000c00654540c40203c3c41404001c0008401c140d00c0c0203d18a60f090803030107000324920308104071610050a4001071038543d190000402e990700d1f4800040c080000c00c2e401454040083d0342000d0071150303100c160300070341c1e040a0800703004250044c5800000e158180d8a23500855a141011500c110f082e4200a50001c4c08207400c100c03080b5505140f9803c00800c40d0410307000202400040d402d0304103d1106004101c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 548430044 1250 548428794 548428801
    0x3050319060909051b0a270908120108070e0108030d0e070b27090103080703030e0106170607080709052206091e0b03010203060f0d0c05060c0703060609020708070f0602160f060b010314 81
    0x90f18418890038a4a1240214188d25130759107000061300204038100d4045e0b5164010030800404111050042070020041001c075410a42c14a07182d00c00e00c51000c007041c2e151081c5419000080108200130480d103601ea40d00d0789100804125440660002e90005008114601245162020303080e81280d9006691a2610910360b8080d0003500c049000d2085030755071a800041d07a00d039100800301c400b4148c0d1018140a00e400400900000c0014144100700030520354107125035121452032502e0040c158101d00b103c188c03000695000340c12a41c000000141c01d0040301e05080d0924240e810700c400780d08901313124018245040c50308070f01007150075941c80759004800c0344240c240030b404106481d00807480e9226807501ca00104600b41d210100e20152588041c0c410800d01000f44112406452880c00030b600d802c4454403140128005c030030019014950310070a200420105a04032281c60307000c08188180c5100390305022551070742c0c6402c02c1e202581002c5c0c99126540c407a12424a900603007045807600d648 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 548431294 1250 548430044 548430089
    0xa0b040b03160c060501060509030d02061506090d06020f19050a020a03030e0a0b0f10050103150302101b06060e0601031e0c02010204032109080a03050319060909051b0a 74
    0x795505000c0050128090700400890304e5402410701030000360b00e44aa075160b059082c1032030000c080c0d203c042107400a00a020040d898080347c0e920b083e50841d4041e4480920000040d442440800e004059600c0041d5040303100c1d0f1a0b1001e8849020ba100e04a1202103403081c083da01d07442003054800c016004012090006402580540b10320102d5004540030940540d80da50b2104c6429500a132540e15180c04000d80034110940c020301800c800c0c6030901c001021380c96075a03caa40780f800004c0c45244412141c000103480b804112108111403a0520350b0041142020402400d0fa40036448a995140c0002005540280104800b401c2c210002c0c451138186200c200300100801c0a084045540800000002c035043c0341113008803905078401000b00e50121440130341150020751060855030007540305c03c0301280c0c0000569030300ca002c4140b600da400300f4002e041401800c0c0f507001014010b180c040c944050150000b80081403084807464110424906c0c01004100c0e045441426540315070501c80103480e2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 548432544 1250 548431294 548431321
    0xe061e04180503071a0c0408100c17070801080601090b0f0d0804150503100602060c0a0324120506010e06030a14010f02210c12130212100b0a0b040b03 66
    0x42114981c072a4400000d50b5406045a00041054690b200034080780350107010503c2e00c1641000e0005d0640c0e1600d843c12450540325056920480c0030311381e44881508103240070307881d400f03c080704070003080d00c640c80d0240b0081d103108401e00882e00548608000440c0003c60b600c140500c410340104240200d070a40400c0100501c0c5600781120b804070103000018a60810300c07074400200005d074460750303120319014000c0c0210701001d51042e03007158010b4040c0710041160104644801480c0d1034040740018007110800c0500c41505003215030301c081000005011007810314182141c52080c400c0c0c421a990320020750340c0c50807050380d0095164101269000005101080541c034a040f11800401e829500301c003079000f203070042c0d80c1c0c418410710b14201204e5405c40b100040c9501c50203031b040310783c1082005070814480c41c000070031203110000030805000c10b40d5500da214545403080d40080b90503c440700203980d00601401c030025070084000c1140424004204c005640c191034a420415042d5614107154072031300b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 548433794 1250 548432544 548432561
    0x17061f0308090109031e17090a1811031311010903030503010909031e0c03110111030604020901030b220b0d0f08090a170610050d020f100e030f070e061e04 68
    0x5004500d4000400929410701c2c8444c0e000c1d0300340c4010004295400c1c00b8000c940b45100181f48040200070305003c6956081d01d4030140d07440c011541f11920241c580c24402000304140f4115410310100130030140b1a40604604609032143c01103856040080e4010f403220480da000050225001740014064050268030020704540640b81041003c0c040d00c640d40b100c118902c5039240001c0072035885105054002c040c00c1c18000c40307400200008110303c11140800d00019218600c41c03a000202c81000da0f1007a01f0071503160100030f1000a10104200c48058802142e10303002c90943e041a1021145282c5144c0210700c0c02e800040343c40000e2490340c0ea401e1142d01ca00c403e1907003c008401c0105242d0b6454108038a40000c80005200720f0800400c03540e51a41641e204c244244000724100f001601c5105d803544201e80160390706c000c0c03090000c4068600c038842c5400c0ca42c043c8100c211404906800280300d0b02190101d001d105c100761181010702c403071800e05204161505110385515521400c259004680 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 548435044 1250 548433794 548433797
    0x3040b040201120f06141513060e062704050a0207050a06180c03060905120405060d0f0f0e03090901150503041704051e030105071107050906130617061f03080901 71
    0x2810410400345400300c0d0b0750b54002c455206c030740b5400e800e0581020b002c01c400c00c48041d0045400c20400b030030400c2d00303210280115000c1101181d001d04540e00d410064510891800c503810310202209034001c0342c1d803410500300703074802e9041501045048405108031122140c00001804024070b04d80c0b203510150210400340300c880440c0440540c081115020140701652040c100410701c84250306145140ca824405440030441e010481080a07603030304030031a1600c54103900c010980c01c4004070b01800602c1c0c0d207201442903030b0800c1c1c40d10708504008030040c10400012a010007482c2d80780e0030760010507004000c2e807401040c000c1000c28040381c4d2007030910704910000399000b803515072144041120100c3e901503420340c88454040300c070000e20b028080c59901100d01e10b0482d0104400e081c800d50f485601d4800d45008040300c03404600e2079150100e0808140040304030034801d440d03030780c48181e031441c1c07000d11000c4a81c01040d004c20b201c035158038184102e030450204103103003050442d1039881559000700140c90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 548436294 1250 548435044 548435051
    0x11103011206051506030708150306010e0103030f18090c02070b0307140f0702180717102304021306020724120f0606020d0e0910061103070507030f0c090203040b04020112 75
    0x700c0d0740b148002c5124002035035070307441300d800c04d40c01002701e0b409400f00b0f8604c41d0b0000f0300144030b84291141e10f20304494042c41c0c0305999140810741640d4026800c3d0313480c0161000404003184140c02a00400040e5500d5801c54010302d681d1150b802c50f41c0804e40f2144001001c51142c015a225407078007508088100c60790356454091951b0005010440384100b403000d040300001084079403038000a0191001d040b10800303070940e213090002c806020b034881c060716a18902030b207200d50302c00101034103021500340003420071999400c143c200803003411300318072030300005114941010500d1000c03c10f50300010b011171054103020f10700740c0c54142c07030300c546481310b90180550b582500103140d0b903940070302c2c0000c162540203810350104c0e00d00001d04003800783c1d0bd0070b80075100e410180321401500107100030440e04640f8040d468041186d0240d41184108440030f4241d109070140403040c03145c1c2030b00c1d12042a10400c1301d15404c0f6504c545450036400103c802502c00c01c0c0240000b40954003408280c024521b0b00007001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 548437544 1250 548436294 548436331
    0x406020a02030f0a2c281809060b0312270d06270506010504050907030503190210090b0f040809271e150307030b0a0c0201110301120605 60
    0x700c42e8020013039200004410603403290b1130321490178050038064015400c06000210020104001c100c003a81c2c11101c40d0000440481c06241a40d1054042e2000d00200b034404224454600c01404034080c090390307421301e0310944000c2032600150200000400051b00c1e41000040c080031071648000e0020501c400c80c0070724440b143ca40e24044512100c42c401c6000040d02110041c03500c280d61544a040e510442c0700444c028042240000c40c00d0468034100d40c003241c5607541801c410b051210660000380103100100d40d801e85844460540414400035508540c0b01e9000c0080c54002d0302e50f0004058400c50034840455060f483d4600c0695119002d401d106181c070b00c1781000b0075005441ea8180103003001500840e08589090114070315003100d09038200903842414104214030428018210803041d40000000b030ba200d03181402100010764024510340c803030f80b80540c80c00015240d900c040310011751078107050745026050b0509403816100b140d4400b150f84690b613581c1800a03c3c2c0580400c403900a040c0700c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 548438794 1250 548437544 548437567
    0x70b01063f050103081b07060504090f0905030c07080f071a0306010207150306080c0d11090a09020402070b0612070e160201140903070b0f06030a020915030708060610170406020a0203 80
    0x10140218801c44005607a95030300c060350007400e981c1c03540c00041c6421507d02041441e40c400d0a403015210b0244001500c0001d41d43c5000060450b100c00800c4c1d4017011906101d0600042001e80459403c003054a001010741180075032181c10f0741c000c0811078000d00c252103851894860245500c00b0040c0111803c2720f841303820700480f03403da00e07040800003a02c0388010305c082001846200070001040e510480720480c0d50341c2d1143e119190100c101d01a046810018145840f1a00f00d03000e00b42d00600f00b1580c42d202810841c0101d0800c4031981e00905070440113103904040012000c0480310b42c0d6010b829580c031280f805038010b010300e400e0082103648903450305400c03020102ca024042d282c1ca20003940e86440c1440c110078406001803d19141300700c0351040140e40c1e1000320300350040940c100c403180300c00e5450780c0800111801000c0050307010b01c036035100840c11182c0000d010340901d4040f2201920342c0c040e080c0c122002c000e004089080144600c0100300003172040d40283c0f11400290042c0c0b82462100000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 548440044 1250 548438794 548438801
    0x121b060108030a0f02010905190317100905071d09060a030804080102040512030f0a0509040912020c0103110a09030f030c080f04030201090501110c210d05070b01063f 73
    0x600568200194004500743c00c284e0501c0c40c0e80341800240044521740e140d42e03880304d8030815021020b80c41a220001010b11a03c240004091040a94002d03802c1c05c084d61004918180034100d034051420011403142402408040d0b064101c0ea00ca00c03036601008401c0c09801580030f401c054000650100100000e0204c5c1c0113080030745170b11400161103070718000400c03903001704140a403070b5281c00800c90340c0112000142111410102400e0a03680c0311547e101080041454681c06020400c000020200300c03980845c4a440070781c401d13a8240310b403480c04100441345100300008080032440d030400c20400207000b00b01d000c806178040e007086940f0304d8550303c0f43c04090b80481010680074000203003e02c02c6680180d10b01014080a20b0400d110768420002d041e80d0303101c01c241d520310a102c032400032030310003044d40b83e60140c031000442075900c06082c4210180c859040f4480c2103c84145000000c41c0d01840341c1a8424030400d20f482100140641070350000c014803034198071686001c0b4030201c07540403000074003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 548441294 1250 548440044 548440049
    0x1d061002010e010207060504170408100b0a03060e0102091e031b0d050114070f09030c0e2a040501120902150304050312010e01030209181002090d020927070602121b0601 74
    0xc400300d05c603e0285080042743c003440041e18007952080c4802e0095100018106a500e00241400030b22180020001071100081c1e9000418450500c14000c005407010340141005803002d03502d1003018840a2103030200364882d4001e103500740d40460b04284080c0100d04d198142d40101030000c0c41885581d403035550940d1503a0300721800002c065402d000742d0340da011264180803c82d40c070b8010b04090441d500c90010344014410002d441c108030300401c109000c0041460300c4080e82d941005080e80d00781045c51410b070803a115450204100c50186480b43c041c030301800d001ca5034001c00d10a40b580038010300803030706e80020304151050321080c40480001342601c1c07100d03400791145441030a0036605d103104002500c03800510804880400f80200c50700c041001030340e101030780c4240e900580c44030066804200401c241507000b0703500584940520032048122000e6140e401004c0c2c10f600d00f4140d140c84e6155489125200c5d10005a100c0d048a080c4900350202803c0b000003da1300c442d881084c2a0304192829000380c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 548442544 1250 548441294 548441303
    0x708100c032c0f06060904030c0326070219080a0c0318060815011b2418060b010807090302010810050d060c020105070c050601030b0a062105071d061002010e010207 72
    0x40700c800d40c0c040020030070f0700c1948020000402480c81c0040200d8000c90f80034000900748201c2c031014908144c01800102e040c88010307000c000d95603240310a00003c948013030b40d030800907000b01c101c04041311410380644c111540d0880a070500e040c1d400582141c24142c0354000380e0400119145070400e50200f2a000c40090420b80d44400042c00c212545203a00740e07000c038109041c81049110104071400e440401c8091680108904c0403040001c52003103500380c103d4807140e0b034203458130703044600400c600500443c00d03c1c01000d040200304201c00054030919800d8070403a0101c0d034601002c00c01588502000c40c0d200c4403c00318100200d6440c00802c00500c2d84900860380315880700d941b501695824412240c0c41034803407900301c401400741c0c0c84e00c503140c0d0b40600003d055000502d001810030040c94011200801d0008059103480090050090000400410031562801401000240711800840051000031400d107110566210081085900080300c04004250354851046510400080c400351a505015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 548443794 1250 548442544 548442611
    0x213080c090112120309020111100501030b0105040e030d090501060e0a0b01180b0d0506030102040515071a010608010b0d14150a09020f0a080a09021507030f020708100c03 75
    0x50340200560072205802040c18950b01103008000714804110900080001d418000b80c82ca02da4001200c502804800e40c684920681d11000307000e0301c1503401a4102d078001c02c81450580d80340c0c2d003003000392490700205081c15401840b6204c0100e04990140c03418510071000018803c3d500e07084000118411150349050594804001a1651300904003180e4070754080801d0344610b081000c4100c507401454000d146442d40c44c0001000c0b6202541114042c05006001180315038005107000040da1000071f0441e030040f900c0801040e48450072000c0350507203045481c2d407142c82e030800f0180901d83d00140c2c08036001c55144c078640787c98840c200318194001c6542030642140d0512034428004003814039445240d03024410041c0c000c00511610a64400408c42d16021900d500c03150201c8015005200c40139502208000c220241481d0400051290520989840042c40c039641c50503606c0d9045440b03017000c1c0750444a04100040404d500c004204c50250500086003c491600c5c40c908584440d806420800b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 548445044 1250 548443794 548443813
    0xe120f011b08070e0907050f040306050c07120e0d02060919180e060402030c091e01090b040c021527010524030d09120c0e09160b0f0f030703021308 65
    0xe010a240d9032003445814444c407005511008101c0400e4001d104000308040441c0003c04000094100d03402140c100c00d052144e81400d50010110781e214a074200c9600c18041c01c03400c40f56005205070308400300d000340a0280d0310059000d20150f07070f200982259004011580d4410745c0444114654041c21030307100340780e0101c0302c150350040072521a0211001c80358004810440144d80009038561151000e0714480c02e181c9a400c00c1e101c4e003030714ac0d01c1210310394801c3d0b000104d04184160310056107010300303c45c00d004081d4011410f0741c4034400385014a00404034000043c0d10201c03500400a4030300d0781200743d480184e210222050844406a44522004196141c032001480c00301010120110007200504071806030701401500c044035600c01c0104a1041103006018048440111002486e0110303140311580f070081c0e911a11841031031030140c2017252101c2c010400410b10401e4443c0d406005040d98681410740d60408140c0c0c10091256040580030440460282d202131104001024814014140e082 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 548446294 1250 548445044 548445047
    0x302011101060b09151303030807081806150f030706050d1a010903140c041805010f0501062016060f0f080601120905070b031014040209010e120f011b 66
    0x40d20840034010303a04109003800050100800c441e0031503000c8900c10900b0a25144090150007200304028040342c03d80300001c140741d08044081d1241c090340e910001c003681c82c1c036580783d4a48500f42c80030019070b2241d4002421440072000801100c180180008a10850800028075041c1c1680081c0c001503000f00703440d481c8004038040d480790085242da0340c14076030a200340020004ca5107880b0103031041c1d2502c10303407400700807051140000140c00034000f44128190381841001e074180b144403c50340742d0719080090361036016030321540c2c4c1070b03541e59a11095401c035080418a00001c011910b10034501034103031000701e80c109040108000300016100e521a80d042e02c100504056a112121024410140304101c0b01c2eaa02ca2006000d0200c031880008a44035581042440d0500c80c3e00103c0c80c0a0300003007417003911900700f62140c0859010007455603549002400380070070390180111a034041008081c100c8040e14060310000360a60800c0700f200c03496111030a4403820740e00380000c1840d030724001e15010107155 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 548447544 1250 548446294 548446307
    0x150627080c032b12150b07030e090c0901120615020105070801090603050a1419060f06050a0e04061806020706060303030c020607020703062c100605120307020402030402012106030201 80
    0xd01a02d403c05180a0010b1140140400c6080341004010480055880b40f41c12075000800c0c0d5050079103040e0b10300d81c99030180ba0407540443d02c00d50215442e01491041c61a001048600c5266505a014280f10559006413100c44d040081103841c81c4d00d903040802c01052551034107150040702d900102d00c90038039481c05410000f040e0484048a8205001400814000039a0301d5401d40d103c0c802c0000828510811402d1a040c524410101c4e03101810030014000150444190b072141c40c001045441e83d9203041020154041c8a86011240910002008240d441c0d1040002405110388030600300950794615080380d0001b081200c14999a600034001d05a05205000803614580002c0c02d1342e040588029650310546c0c400103280b580c564001003082454003115a018404000f43e01d440c0d8000c4404940e00c0b0041107503000d9000f0314105000400d4900150940c46003201c1c40b028500e460303095000e00010f0b42c401001030741481102e9001007015440c0030010f685e0250041c03c0001c0303e078118800108807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 548448794 1250 548447544 548447563
    0x80904060b0c0309060904020d14011701060f180209030304030311120703200f0706020609010f090c0605070c0e0903090109080f0c0918030301030c06030f150627080c03 74
    0x90300780900c000311903070100100b111000c070000c0340e21589440d0081e0004000c2d120343c0501154941c00c05424000d041c44541c00c02c0d0503100c0160080c00081c40b039441d41401c80b012403090140c03880e1034400030048000c030106084560081c81714054a0b14181c0c10210f071541d0b00941c011000114207454044125800303100c54103941c200300c0e00c0303a0302d4000c0725200180745d00c15902580e20703250030010b01035000b05400c1100c500d1049100059441c015900e0b00b010391920811a20001c0d6035081190780a900d0000c4e1003800d0f074807540164449039031400d0142c2104c40ba041201d048034036a00884002c565101d4141c0b005108404c040001c60303454113000001080c4017119440815070307500c05032600d84804004190150030071026260801c6036990400c07040c00c042d55513181c0c02c006000c0040088103103c41080080c0c16207480380c5003400b91800f40d0103c141280d405040d030b85c1044443c0001403241610981c0399841c2c12a1010141c41c41019000c000340c0c0d403a4055002503413030380c01100781301c0c207505090201c0c040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 548450044 1250 548448794 548448809
    0x3070b03090d02010c020a0c06120b09011404140103021f050c030d0912080105090c07060b061323130b040f0608030415080c0910021c091404020712110a06020708090406 74
    0x1c02507d81d901c4500c904d49600030700c030501482d095840e0844600742c1c007500611600402304041565a10115100340c4005880c0c18020f078107002040141c2d032040c0303003041e04999014001c504101692072a40c4542d4144a024a041000c10069400000010405000d80c00c00c00e0400141038034052502801000d0210320607014004d1100c010003240e41c1d8002044c0d80300c85642812035940403c0d00d80140104240500c1540c01580070920b601010100000e1034142d40780d02c1d441219a10800d1101040b5035103400000380e02c07a2401d503880ca1b0703420658004144038000034002150076505084600700340c0e5190b8100301c3e01070388041010003000341c1d40c108000c800b4286041155241c207001c01044d0452191038040d03070040040d0302d07040180d14803c000303480c64030f0103880d2002c18000300340350024540210b5114418695035849900e00c26071800d803007100c0c00654000c030880300b001c0781d425083d54410004440e00c0c505009518894020488900040c455244698240c43d0748035007500400c021194650407281 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 548451294 1250 548450044 548450053
    0x1205012402150a0c0302040f0b0403020a0b191b050f01090b01050d081e0702120a0b0114030604020d0305091003021207110709110f0a0c050d030c0c0f0203070b03090d02010c02 77
    0x402e0340e059003a040d07410120070b100100300c0c82130010f400e070043d100760751110300014083d41001070014010000b9005492080710001000c5554400314135a50007499610070f04070354034914107100e0901034040c02c0312210070140e240720040542d403507203420a80e90301c48049a50351111445000c010700d80c10070b180580700c00c6420944c070407900c0c0c44040c998090329802d000c064026400010200000401740c428490740101009403000600c14803648803154140101c90780340b178101c00810f4160740300c902c2c103100303c3c40540140700c80e540d55001c1005045d81c109007641800010031418005840d85900050049060b46000d82c1d510700c0840d5035a00000000c020b442081904804603803400380c041143c2c000c0790841d4002089600700b20300101900e00c584400301d03900c5900020080802070308010110281401102a99121442502c05070300f81c0342001441400074031104141400030705e802c420450140d0001d400c642d0031503103c4d1062000c6910948115415502c42111810b100f5030900450400e21203034030140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 548452544 1250 548451294 548451313
    0x90e0c1305010f0512070504050c0d050919061d1006051c02010f200a03080103021008100506160203061509070f08060f0d050109060c0e1203191205012402 68
    0x5141e030f0505406114460010b650b6998075020341084100050100200101f2150820320141106948200301506100741804001200701c0b5010801110f00300380744071501000360041c0e507002c0040042541c8440446c001500c4d2034a150b40820840b407501929480001d4510f04107002c200504912004500c0540b4051000400613603001441c460f562580d41440c4810192003079a4044500604011a080348520a00c1100780b6520841050403640291156034500151440450f22503208440750780041d804260200058100b1800070b001e0f80d28441d0444161103c0340e07000a09082050300c2c5d094004c0e803100920304080c6809180c0b641c00200320300f0700001c0000d0200e000b50076840010061440b0759100001880941c4420191040d001e034405c000300300598a40c13500d0401005074039040b0340022540603805001d410301c07010117003404204500860a114442824549085501340d00000300312078079244010302d100da0300425010b08104081404d2107007502d040d45400c0c01c0f0700039030182154082000b6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 548453794 1250 548452544 548452559
    0x40209030307120c080d050a05240114090607081801020303150f012006160509010e04181a0a0b0901030b040b07140a1e0804050312060307090e0c130501 67
    0x1203442c601d910a1032a0030606500500742d03010180c000340078201c01000504140303001c0c69540301030300c03a4010030803c011039251041d028488003006842c000078040109000d134205c1d0301622075a2906080348841510f00460000490100d42104000f00e40c03022010400c40c9804488100d03080c15140e0030320082d401c42c1340500000c0c08007401718102c540550030007040348102d64402d01280041264062240d035007c800500d00c9655054125000d40f0a02000c0c2c106400440c4550201e4040307c005a4542034104040e40c01c20004000903c0f43d00010020b100c00380d00055a44005034445812524082242c1d20b4042c100400382d41101c900e1610400545006000241844124a4109401032070329111343d40c075041d041e101e90480541c24403040343c0100b00210070755445040364610012000c880c04101c0d14008041d200f060064030000c21541090020446640b500003501c3e034031010090454842e00c1d40e8076064402c0f901e0210b0721042d190441e42c1c0c204240e043c13040184c0d80d407501c4030104006940c901000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 548455044 1250 548453794 548453797
    0xb0a03090203062d04020609060c030702010e09010503280501090c0e060f090a1a090108070f290a0201090206030c04090506150313020d06112a07060507150c0905040b0402090303 78
    0x130745100241010406540700e61042d90000880984820f5883d1144034081e03980c1e41103800e04034001071140300b020000d81041030f5540d040f260058010300d00d2035000d0503400300c004881e0400241c1001e0103104400410400d000311200b05010702503a0816904005045e5070141000740b050f4040c8050a021005984072000c40c55840401c407880051074040504414441040941d1041d6000c1580300000c2038104000c1784080865080d403540c90103180c0d48605c2d8512003042401c80d230300d40710310509010020206070002841210410b00c000100c0040303e90000340303a0b4005454003640e88802040621592409101c0c00b60420001c41da1101c0400307500481d038070b840c17000a2840c8200c40502c00c2c000304645400601b0390055a00c0b040c140b00342006050100300d2a003103003044080070400035a0040250000103040848044030384060300c0e86508240064489a00a4004494091080170710701d0000c0da061150380c064210f90340c1c80d560594135040030001030702d00c180d50a6114520410ac500345640c2e0000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 548456294 1250 548455044 548455111
    0x1401060b0a0507020303090a0801020c1005060906010e18090d0806031b0103020f04031707030f08010f06050306010c0501050f09070617061509030a300804030809070b0a0309020306 79
    0x1c1d020fa0307620380e5440828194026564200c1e009059040080f40821064000c0c00784d0b842d03502d0450704c0e0001e6a11900095900945e10380c0e411914800118405520810103802031200140010b0b1100c0b1024484e101c41c2c400071a0400c8081c1c124410110031280c2c0b042c0303616042401140104095070101c0c0140c05100c03041c0704c0c02ea050541c0019000311741d81d045401d071001035030000c5a01c40020062640d81240703a000d80011800155210000d1410902501c01a130580701400c1c0308070075041c01d0100a582aa0018207041e0601544150002c0001c4090240301c0c4104170407003c4c104517080018003280390509039000803050020482c050f01c124802c0203c11030348000c046940c2c01444408035100e507054030030380c01c086806009030a4800c003405004a03105081100a075800c11101041d0703000f00440700d08072103880d03001801800c003050101c3d118498540e007003c1c070907040e5440755648100d40b1400b03512200810740403a45945241042d894140442c42e400718100b40d03a90405001080041480e48560 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 548457544 1250 548456294 548456297
    0x180a06052d0a0f0605100908071d010308070201020c0901170705040c02030a120603021009030c050603102c01080a0302060c0412020d050a05010c17060d020f1e1305041401060b0a 78
    0x1070403410600f40321504100c1c000c20002e481c0080f00b48601c0e500500d10040ba000f92400c0303120b5200f000441806403202000d03d80320001c800740c000c3e4256924a1107940c0300e500305904502c100001d240300c0e50f86054540b802002910b0900c40d441c8160900c245c1448001e0740410b01c903910b402400300c13035907401008031100c1032074501c1e02c0a210100002d21000804441d0400381d040704003c0e500e05200c075089089002581e00642e10190311960342c1703040001130310046582c041d252910604c1000302100002c000c0207003004030303814400400304001511241243c02d91100b0385540c0304080b01401e041e011700c00309401c0340b0507011491405042c042034080b842004100240103010111505043c000d0500640360030542c40340c001d02c00ca801901000300401440c0c10400740300400c09020841d503240101c400c046d0a0b901501004808200ca41040013100200360086005004640300c510181c2e98003140f9814059403103800901030900e420506c80e2030944000e4807600303032b162400900a8905aa068840d800b109 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 548458794 1250 548457544 548457551
    0x201180305090d050f01061401110706050f03070c02031b040b030a02030705010c0c0905070503041e03020a140307080706090b09060417070c0905090703051603080909180a06052d0a 79
    0x162810b185003d40000c01001d955180071000f00323400d0340d1811411840781d000da071660700000b40000f505484200703501c0b076500441e030704019014101d00060080c41d03108020b8140175081b0580d0360042814505900d41000000a080c1d0001c0358501e4107201d00d800881082d002824031072a194080b80d0f44074010f008407414030401044c010200088010340d840a0709003d0b1043c00242080b083c0136103140c00580b8101c1e1040c05040000044c0714104c1d008584150b015401412641000d454104d18041c032070380c09464601003048038101141046c0b00911000b4400c1c800021004100d00b8040c03819034021307203400c24030b41018040c48003054880e040d48441d00124401180d60b104145400c1005c8004c6070700c150b00c1da80c10002004001d010209030b8408803402081038a03407404204007203101041c11030100512080043c807920106040500001e81e1203c00411203041e0075141e100755500e850490a02140d125071a0740c208452004540c00034000c45c2c0e058442e840da400700007a03080100361401400b91854554 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 548460044 1250 548458794 548458819
    0x702150c030c15070801170615011e020a1703060622030b13061506090911070b250309080a0302070f021914090c1b0a02130b01020118030509 62
    0x400d1048a1110b10000110388181169074000510030b0f4048070040040b400c144000554054250302000c9001d200700041c11050780e4a20388900080088402c02d030402260110003603910540e85400c0504040c1c0350000d080c1c81c0860b152854000c1c80005491010341024401c0c8071140d180c40c000c0d101054000d4034449020007e07280c1010f20150b00f640050300042151090141500e401c0700706071200c40c0164424030142c107424800c1e0300c00c1c03400b900c22040001c00300720003008070052540c4042c51186001600070302d0f1005a486460099070107654071030f180d0508003c0800540181031440e803600c6482d041c01d0040034941d484001c07403401090b10700b505258000030f0003000c0012203034600e0345265004180c110b00b2581c01c045881410500d0141c000c840c075240450301b6881c640301c40b00d42e1298480d1140e4a2810140d141e042c10300d2446a410a01c5501c9601d11324401682c4241c448141a1000f070f40c0062981040c000090950f000c00e010115003005411422010070350100c112007180c10f01b502e001481a1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 548461294 1250 548460044 548460067
    0x30e071d06210114061816051605010e240705070b13120e030d030e0606041d2509050403120507091e24321914070215 52
    0x240540b8500260354038000b1018418254882e41030300521003951a0303101c84911043c082d58054003611030743d14100c10450a0040140b2078070007006040102d04284048500035a945429200c940004031501d40000500c0c0800090038070700003a82c2003601b0f00000c2642044500a003541c81600d00140145032603000045240846118101c1140e41c4502210f0803003c034040300601744950180b5080c840c2c0100031074100c90034440d0081612510181024100c03a465681c10080249400010309444600c3c880c055540000240b218805000908400d141401c80d084807103180c40d8407680015030b4062500052102199108242e1035039241500800a650307142d580042d150304095600c550201d00a0003202c24620324591100c10833102211541e061052781a0f20700041c0b4215802c04034001018a40708800d0000c00c00c00403042e00c501c40c0040d00307014401002034a0740394011086512006880e1842100e8142c1c807490402083c0706002255040200d1a80002c80d01c1d015941c0b502c10f002e4001c140c1c980382d030707 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 548462544 1250 548461294 548461339
    0x9010b090705030f2a070b010e090312180a020a0b070b18030712031b0302210f13030309080f130b0a020a0615090519050609040c0603090f02040c030e071d06 69
    0x80b11780202e40311249860284241134090051112210100d004a101d400703000054078286000f00100405170f0740d0f0a904248075500039281c0e142d0a10841d4110000340c0c551a651303401501d14880c0b030300c1d0f88552509002d0120300002c2e218185400c0c00c103200480300b4801109a860700313940401c580ca449014120120081c1642404c800c0c01d02090652000900d0b42550040000000031311002c0c0c00b5541c4402c1c00e0440c001c044610210040000e000206d08202041c0d241d03030780b40d1080c01d0000341c01c80c0e41c1c2c540c90501e411800b03004912031000030b4840e95a001480032180180a0742d00910720300705078814029104c40550000418064071030800c1a00e28107190032200241c03045600400c0540303003030152446c2c00007024112111162402c00842c0b1141484d1546602c100c0d0022f07006010030f441c01c40210000d015825083c1c540380c00c03081d00c2900590b11405011000d454550300442c500c90142c46050812580c0d9100c003604182e603080d060b90480e4201a080e500520880e003441094060040300000f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 548463794 1250 548462544 548462611
    0x308041d04030914190603090c14010905010c0501020f16060b191205030c0a081909051503062e020d02070302150f07080703050a17190b04090b09010b090705030f 71
    0x2203403825040446c00507490f80c02215598000d5001040042da02d4007000300844100d2441030004004280900c02c550040401489040c030407400107180503a0400c3c402203940081d11024160001c000010041c84824001c8a401c1281140e14070034504110740781e203219583c0c600c81d9041140c00c00400340c050100034420358015410b8842521031051540c074000c425540f01c071440340c0c445004040700ca42a40c0c494240d031401e07a58081c0c0b8101046802070b25980e440e401c0100020b50041d4040305003002c409241c1244898a4400c40303800e00120f5002c04040c0c2044040468001103500828017000569102d40200079003112101006548240c814000700071880b40c800042d041d110000703005003c25a005008103e40e40300c550311480781d000c03030302c45c0c011610300d0907600d5280e84480c002c8981c0510019a00086481304010800150441d04d40e440c1e56030444100e501c100707540d540d8980060306041101d074166003c00b980c64138a2541c500307500d15120031100a0200385508844400801c2c0070407030300c040c41c0380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 548465044 1250 548463794 548463829
    0x90a140f1e0607080708060f0a08031303020406080c09040b15031606080a020c0d0f05090a0f080712050d08100e01090c0908070f03020f0414010308041d04030914 71
    0x2640180701201007080c481c510440704075200b040d0019502511400801e80a40000d640d081c1d2144c035480100001c40341442172859000741e0701800010002e004000a011542c98071214612880ca940100401c0700c4181d4440e40c3d994028040700d1340300b03a81e01d2030660360084e030088545105881d00d95a107c01010115040703074140c03090700030048415000e446240110f03561f075626074495a50300c100a1069002d480d5810207558410a120303400da43c000d640960491a0b10301e0558101410940040c5031042c066000404054108800340b00c0000288150009400c0061124680e44080d5945940c0c9480200c1c00e01b08221405010400300071200c0c0011006165440d000412035840341c0b0018010302c9407850803030101d01602d100282504010441c08100e90003184100c0c1d1007480c1d40c09106c0c2500d480a4000d90190342e42e03182f000c1410030a8140d6010390f000300e00403522241071031920010745442008810301c401000f810080000d0380100084103840384422001543c1d10520301041c44004040e40700c05 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 548466294 1250 548465044 548465053
    0x12030907170a0615120b0a111c050a050106090302090a0b060d0518060c0409110705150115030203090705010f180602160b0f0a050304032006060a050306090a140f 71
    0x1056000011644045806150f04109003240240095014401c0780f0514940101050303486000c2251803103c141d0103900303240081000c016441d020100c0303500c01141e205007658118038401e40030344248501036114100c40c80c100419410500003804641070b43c4030080c4690030310300002e01e5000700d41d08039038480000642450780703840700e04600d2005000304071820100002c400c04451342e40d803000111030740030ba100184410303c0c00e404c0001f01000b4000603000140c0d080d4040140100081c800c216090400c100d026a19001717504000251400b00400d94040c41014014000c0c0401d441000c41c100701187c100f402d140c1141034004100343d520701b044255060f0386017100000010310603000710b0030030400c107c03443d0b14250b050b49404004078a402894001c0d008220148010003400340144001c5402c01e00a0a20641503425088002e054190700301c400c4409402034414460141002c617940d5000c1c10f011406030440d0700e4032440b0a0790301d102101028081d0341500180100b1003500344440c010700d410800954 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 548467544 1250 548466294 548466329
    0x20a0909020d06171b040218151b0703030e0906130905150109020a05040e0606040305061e0a0608030703030b041104030302010203010e090705031c180905190e12030907 74
    0x4020610380c844d0fa103503007100e036152a00980c00031800d030901141002c4404510040c20702804000e42015481c070305070086250110080741e807007440c8101d01e4003400540c6a620b0740d0030620740001e405c022143c01242e034040181440001d80126105000c030000340d8010b81180e0b02c81000540d03902e26404072152092401c0c0c08041440f0300401e030755400c081580301c020070310799030381400004030700c00c080d920400a0403d100511a005055500355006040104642d01b004e031251680b0b410524113482c1c031403101010b040c00e4040100040f0360540c1c0102040300402c24589041e4500ea2a4811940020105503503035078550640e40e0399a0140c0094250280481e80307598481c54041e0017540207014814400c81e111000804803440041d4901c241c88019002d402400b200c600c0321404251001030307910034080c988200e49840940304c0c2c170040084c080c140000c41e140c04d0824038841c28a0100c65066001400c000700902d06880000c2d045011240d601d072200d070b90340e865800980c2003042c0ca070813204065040f410503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 548468794 1250 548467544 548467567
    0x1b07050607111c081b191b0807140d060f0e070e0106050424020120070b01090603120f0509030109030306061727010b1801030201090e0708070e01030906050c0307030c1103040306020a090902 83
    0x4154082614134910041d03989600c8096941c0c2c0345417044051803c02d0841c40ad606090899109450911a040110b90706011003550010344140d0500c543d850340c00320a04010086d00303040c1d0640186a1424403e24060030f0210506040540c1d0b01c0c8002d00c24801c012070b0004a100f58081e45401600c503c0103201c0c800c589003c074034030340e02070740301039440200c0180003040c104c14034410031045071b52102003c0414556000f040d01c401c1540741526040c454240414645d50700c080c02152003852007030b41c0c00030b000d44c00e045010307050080c19011f00301c2e000c100404108005085801e2078130b000d024181c000700d42100e440807580c09850303003106080e003001140d00c803580d14103112020035041c0c074805d80390717070a80a44544485200d0107088420700c00240000c0080382e039050003248100c0d09080306240c085214409900d4030070a850054a5051410b0303400420000c040b03915100300f050a060b149040b03100020303012101d540d41d000e1030002520139540022000d06142c098500b10380140307040707807044d074881c890b03050b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 548470044 1250 548468794 548468813
    0x2802030301060e010936020705030d06090209010e120307050f060105031903090608070e06070f060b0f012a170403031706061b07050607111c081b19 65
    0x18500c00304006020f4480d403907000d20381540c141d82500c06075185000d040c0740f5142042c80d038480c0040100241910380b040340c00440c001060300d075018400441da146102c25048040b42d240e903201c0002c0c0c91040c84440d03002da070b2008028481050031103441041001f908002800e40c80348150082040c8a40d4a01c1b481c84800450600d048620850a58849840300a131414020104890040000d0725034402030101900806046810501c5480d0403045c40a014002c81c04903031000d00d00703840c0b21860005070800c00c8124021084030369011b40b0f412010340132300340000e00001803225000309610612034141d01c10201000da024052504561050220f449004a01c030403039100c0d000c258009008101100e0423200100c0e6114050200170f000e03070349040c10f1110b6005a102624510141e180501c0d64006250390341e64000d4542c05024143d407c8403003140c0803c020715100e003030904441d040500222400402c0c0400207880a010100f400c8540c038113106a121400c00c040088440d00c41c15210718220180040b400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 548471294 1250 548470044 548470049
    0x90903120b010912080a180303080610110c0f04020f070317101d0601020a02060f0d050f01030302030901051617040816050f0f0301110d020712030e0307082802030301 73
    0x82040021541d40c1004440702403481c090141d41c60a40c100b15030024020304001d00d004a20740c0b410080300c2040c0703450f0034241d4100703520940010701c50720705010041c80c0c00b940e0905508140d0038440c60718460030110039143c08203440c085100b4004030040c4115512990121104c60300c8811500340e4901c018a00648036042181d2400c0382c81d9460400518160380005451040c0d4507101d46c901c900c10395004c00a609108000c14150441c05005e0000c00143c0f60307038000c0c03c40441020f8045e900c446003503c000c81111401081c1c1c400d4410b450004001203500881280c104843c20328000d0343d60040c8250014400ca08510300410844030020081035960304003000c0c0007a038205006550260361092440c40c400283ca000d216801901c59995091600c3c19000722541110080e00115004044040ba4440390b000708408040030303600019501e04204c0044c0040c6001201343c1002c2040b50504111b00d65280960b200c010030040c00002c4c801c2000c061403134008111500285075840c9003d44105c001d450780c00a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 548472544 1250 548471294 548471327
    0x804080304150503090a0b041103011407030f060f0b090a170607030b030c0306370b24030c031003080c100501061103190e0901090e43090903 62
    0xb0000c070040c0c1d00c03480032a4012070100e0300608400e6019143c82031041c0c0003902c00c5404c0044101002140c0e2800e0180810101a0024540e8189068413015050307030031000d41220814680700c02400001c180840c000c09171382d5000c0c00680c4405021000c1600e40d83d440c0c00c03500c1890241261a148510b0004110384160510f40c0c040c800c040d85402030540c0c0c0c411a8040f180d041c1c118100180d448041092080315828459081e020756481d081d1440c903c40004404001c165920b0311501442400e10304000e10400504189090b90040c4414408415020280100c60500000408990005503c038861405117030007400c0659076185000540d9601c103546070340c5612041c20310713000140340340c0a9299584820080e10255141c40c0c01405c440c1115841c10705c0c40c1e02401040007103d2380c03135201d0310704180c0a0300400100282c4940d0f0f52500900e00440000030b02d00c101c0352207a064910791942130012030106100c21030744030120014950b030402a1401c1e00022085498148030000340341c0c0c000c0343c0e4051000f14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 548473794 1250 548472544 548472569
    0x11010b15043b0402041107021e210f0c09041a060d060e032809030303090624090e0303152e0c0614060105070210090e011205011407120e0a0804080304 66
    0x124180300c0d91034062402c010b5401400c140c00750f6041c42544207400700f902001001c0030b00380c801d0140e00d41c4422030a054640b103540e21400302c0c400281000c01041c405804107d5501c0c1062400c2d40d075581800500104031180b00d1050740124500d911001c40551991d940045c0500c1548130500d003955980d0442a040101c003410f100c0506960320841c261518142e2443d40c405600c5415500c0503009010f601c54103c40013552303080f401c9601c00402c0640f14410201d41100710886140042c00016220b014682090790b40007001800320252440541c8401101300b074440e900c8008910b40d1052840044000c0a8013042e4007800c03c602c10340e4014600c0b080c041c481d400c01c01c203040300021200202c0000b19451400728900304486405440c00203014003a0491524002200320313210300095994850a0b8800b81107000680080f804004080c0a510000c8010100145241c544108001c0035010480c028017071072a0348901035199150188540d180700c0b904018450340c0c581e0f9441a50340d4039031240c407910302200070303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 548475044 1250 548473794 548473811
    0x3030301030308061c15020715050c040501020d02032704020c1c180f03080309160308070606120210180803130305012012071e11010b15043b040204 65
    0x80c80300d0682e0046800c000b8040b141403020011b40029448500305172541401402188481d11079806618403500005a009490714988000649800e600c01564020741d0010300130182d199025601c9a0b010a071804218112000c0a0000c1402482015042845030082c004164030003031454411107545142550f440c4588000100c0b0700b05112464003070082e012850300c03410404221040c000d150000400300c00e45031040e58000a040e1125825402141c01c41c0011a141c420b101040c4079036002492040f902c4c05542c0c0303407580050304a80030454400c061114507140708041c5d600110a0720050903e401c00c40740c0e0b504009010440070805840101e0f140d42c20810684440d580050b480350100c40c1d5608144d041c4940c2138010b10500314000c11060030407088542c034800b4040d9440c03d20341080401d44076001d145d25680142400d403803510918502640c0700000d420303284a152070484003185e90001c40f45403c214100d10703051904146c0021074038010181381412154058008002d4001d610860b41045401c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 548476294 1250 548475044 548475079
    0x18240309080d05160212030f1005030a05060105010905040912030906020c010e06100801020a08040602070201050702061c05010602060118150512030408071202060d020306010207090609231003120903020303030103030806 96
    0x744c1c3e0b038100046500031f2001c110400f8000242d1508107200900505030701d500e60000c81d00c0c00c0e000c00d01c11340315940032070010055560000c005a015042c1070301d041c0b000c3d500549803481c200741c0c549001000c0542d0354407500d091000940c1036039130425140009000c03c05010f5a09541d0303040542e0401d0040c0551800069981014421903003290038a031525013030780d07440b900d49000030b407c0041c0603414400200b000d14010ba99150003403100180c10410001680312480c4514101c40050b0400b000350752001005210702444101800100003600d07401050381180c8007440169181d50345d1007039400650b90500c0b00710896002c0060401d541c0c0f000111080c041e80e40c21104042108901c0280d0403640400bc1c10b44031305040c2c0c00450b486181801150007055540c0d0110703003100c0060340540f040310b41e2000700104501354070031107070041c0c428541a80250b04180003030340b5005d10680300007402200d006030300c008403501458041d002581c000f42620b88035a9a420081c00061044814030b00c11f501030800709142c0c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 548477544 1250 548476294 548476303
    0x303201e100e07050607050307150c0e120303150612070816090e0c072a0915050a09050603100c0512090f0715030e010608010c18240309080d051602 65
    0x400d0340c8005100f050b00c1c100a000d02d42d81b04e40001d4070f060004100c00404241c4c00c1050105010944400050741888031100405030348803841e6403031080c40c0d591254101c002000086e00c2d0000c41c9144042518052140000c40e9072182c00e4001d80340444000170401c034140c200004034441c0701380440700d8503c0c05080310111000c05160040c1101d41d00120701199940840b1405040c080d44107454550410001801e2107181c00700401034481c01c0c0640d00014003094650380104160a20303c0d10041d0161800d100008240e040c240c05540c041c960355900250856404000141901070310070800c110240070023030010942e80c85030031900c0c0d80a07014004154409400a030b40840141400e02501c040c2c0e05001030354010440f0010075030105a25003010307452900c0d0a10543c4000c041c0c2c0e0000064001c80c0050151400801c07004252040305100c0041010340c01202d070003440b4036400d0451901c1d028003202c0640003041d40d0300010307040381c0001c180f04440e4506503000b580900004402484544610401240c2c2c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 548478794 1250 548477544 548477561
    0x40506030f0604060f0209031506010f0e0a0909061407030b0f1519030e100603200120031308101410050111192105130303201e10 57
    0x940d4000c50014012507407960104000010345c03000949440c0c070f4103000030304d815140c100350103903144244107224296800408505100e030b85810030072103512000c000a001c0900318820407021940319040c80e410004d440d03208140c119419500c0c4801d07402e10300b02c000c000b4041c141c06140200d095040d180858070309800000030754003a0b5a041d500c6c1c50790300d592001b01c003480c2100e404213240c0c40c0c0d00540392400e018400c41915079580000028860720394104864a03594019000c4c4403c81c5501441035180d9200d00c2c02804000c0c100005030240240001c0035141d8402c1210058010000c403002048845001c41c00c60000c41c1d441c10140719106034410100f540d454262558505121440c070100210b50140a20300e5400c06400260fa40a003001c8801c01084002100100c40a00100138405d009180c00b540c212a0805e45191290510b050042050341c020720310f001c06000c1c03004481a664003410500c01c3d8401d5080f0f90410780300c0218550451003104403500104038800c0c001c1c040c00c188400750500c0b031b0710314 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 548480044 1250 548478794 548478823
    0x4150213050f1809030d1b020705010f0519091806211106030a0203040215040e07051b0d02010e01060911030411270103020f01080426090306100504050603 68
    0xd464a040104508511002001c0e0b801a03030f010f2801c405003519a00d418814035442c0003071550b5000040001c0c00703c0d807948002d00c0b5070300b0840e05910903d91340050701c0010f548080c201084403828102040d25180682c00d5510841c44400660941e0070354450070000403590f8580c0c40c6000c00c8070050303580043d0b0720240074403400075195030000c401000b8556004009580030745442040d010800c40850b001c3d50088920035207054000060200b1801d04441210312101c00340801d500f854144032040b05c0000b0041e281c4010414003040355066441402d2802060030086821245000d18140f4040d019201203501c0d4640d039440c001d8001940e80c95401a4411070442e6150740d4078580d503a03941c4401c030b43c141900c4141c00151007055003840f98a42c031003e480b190025180e461081d85544100007540e02128030341c070f04001d0900b041c0400140040120080d5405844180d11007070031150311a0850302400726095814414030080c000744a4400c61410b090340d2059406008030798850b0300707160346c80181d1002c030742 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 548481294 1250 548480044 548480077
    0xc02031e0315220f060317040605031f050d03090614040617070311040e040b060f1804151a040c050703300219030507110d05071b060206041502 63
    0x2030320380b40c40b0f98800303010005451403400ca200340c88050822200c082d11001c8066507502c80a10602404440c4030305030b81c1c01076401d107240c1824424014110701004d404003114034071084418035608105146c0d80c000d0f16000d4110800c40b1168107005103000018403800010820740c0d050300c440d0f40310080456054078400e44420761071504006000095150040c80d1600301992400381a0804603403900a200400016580508074102804e10040c3c1c5080030700314621645c400c0c003078a200ca03158640d42c40b107c2c1c0c04210650b50690b4032400c11003c0b00c0c101d03040c00710805141c2104600c000d80d042040d0018010280c4c1c007000003050b80c0c48282c6082c40780000103000315000d50f074500e0551420035900364200c400721034814800c120f5440b044041c0e8100c1481300c00c01c10740300882d00d00c1066051282a40c0f00c42c152512001c00e805200c0c3c80d41d00c0303501400340401000b1000603101c0a109200e04480d00840b44d042d23030715090503503441000b500c48100740d030f007155012503101030090311001c5802602c4003400c4000504 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 548482544 1250 548481294 548481331
    0xc0c0a080f031c1103010602030d11030f0a021e0a030f0501050f21030d0c0305040302151014040b090708010e0c03041101050a0c020d030210150b0301090c020a060c02031e03 76
    0x10030f0800030008058004035160f20160030410b003100f0146000301050303001541c4901c00c4005100641d00c400082d68030040b424401c005681d0342c4240c4954010f07042100040e43d5040380240840040404000d0100392031000541000c81a415841552220b446910812550341ca800400165500414840750b02c115582c4010b03100111011a5110200b0b150007140d00c0c0104041910341074910042c0b030680441d540c0e40030802856014000c040c0c980304240303150200c0780b078080c10b000400e90541c01400c0001ca4400615416515107a20448030204001c14069040c60700c158020314a0350f09004140080e1000004a10001000c03810742e40541d600810301540301551100440b0290410140384042010310039013000940c491000c810211070103a40504015a155042c10040c0c494918985092500b00700b410080080d0030005c0c0e07415180c9044010035801d2030704004a107801740c0072801410440ca800070786802250004010282c0313051032129200c030500c4a1a1000b03003400100c5604184030f4010030346 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 548483794 1250 548482544 548482567
    0x81e06060f0901110607050d180201020a080906070212030702041d070e07050d050412110a0305071511040806010312080f04031107171b0301020304030c0311120c0c0a080f03 76
    0xb9025540e41807402c9070405480600540c034003401914040d000c038078009500140302c17030540985030801c4102c04501c1d0381055075900003590b554400202400c0000040b6603115a9500c240454401c0f41c0c006280c040c18800780d40665490703034455071040f481180780c115005007456908110a200b181c0b5580a002064504146218008002030800040203404c1141c00c0100072103100c0c442c0980e002e104803a58103c00700b64082c3c925031806000542c6075002c4d00c3d0401c0003036800412240304c0366200b00002c0c0710042030703010132005d001c040709450646070b03021802080c0c2010000f480e5040307901400800050b001c0225041c2e5449005442d8181c0000c000000900801d01641d0040480c407852800c0361003880d038031441900501203c80041285411080202c1003410174200965150380d8110021032035070070316a03805440304e107031541e00034140007041c40c2602e102c0307105018419110180103c01595000d802c0c4c101c98403a00b010a0a91203100500c0011815520000d0382090f03c4030220021481c00f04040d55 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 548485044 1250 548483794 548483797
    0x120f0309030215030a05060603161812051f0504170928080f01141906030f0b0103230712020a0329010e0c0f0706020d0606081e06060f 59
    0x50a400344180c520000005884184400c2c1500511421850712414003910300016980c005d401c003441441c00f4000d201c0090310480c24911446030508140c60356000108800034815544d6001043c65401448140c0c03e100003c600140724418001c1c0d4912585200c0d030300401201d406540250102c0c09101d259540240701000030401c0b504000d10030340100c0d4041040c2c40ca0500f109000c03800ca00a01d060030000c0d1041040baa00364cc0310450020f000c9004501c81098141c02d00411415280e0100309610390311886650010300a15005800030300c90709210301304146501c100784011038031041c1c103011100802c0039461a6101c002c80140c00340c40d6079450504c684002107603104081c0d0384400c4170f000000006081c500c00d071413030100080c04c4c0b0103c103e000710389c50300510050380040002160740003006502903000080740d40c180f03d136a10407900d5001505040f402800fa003c0c030b2942080c44c0c45004218990800800d41c0702d0900b2190390940142c2021004411030000d0712156004501800f818526252290 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 548486294 1250 548485044 548485073
    0x20f0f070f030b060d15060f05040902031005040213090804060e120a11041d0f010c020a1106030a060816140406030510020705160611160303080a0515032d010612 71
    0x8060881d242d41d20b1b2030704060200c003406034111095442c182000028405540e40c0c0003804200c80412a02c400c1c0c0c1c010035180e1441c003840840c245d96500c00581103584503880c13503a0046540c078040091260300d25000d107403030307226000d0040407400c14188882b503442c0404128410a900304007030600c014003a81d4040000349800065075000703403601c125405500403010000390350000305005203544110322900038210703011075400d0b40c1107411060010003c900480c0f0b0f880c4208000742c815a649556811195004000b190000c09440c0101c0c2d4500803a40c217400080f03015141d500d5501039214204108002c1101c074240300007005508140c0c03030b52103214555400740c8842030160090b1414580120b001812000498200360b01081c0340b525010815030040011001205182c0d41340038072541940c5000d000644020140d40c1200d88501c00150320781c41e0481448a98000641100c0344a29621026200250040034000702000d10b0411114451414000c240494035000345080c10910b0685982c16201e2490703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 548487544 1250 548486294 548486299
    0x305030a0806060c0f01021201090209060f030601020c18040c05040501140904020406030602030702030a1202090a0e040501060e16081b09012012031807060f0302071a07020f0f070f030b06 82
    0xd04ca40a66080180103110b0040c0c4600001680c4000000380c9804106060300044c00d414410301c45004261520011601300b54802c80540da16a500c0c000100c2c503045407120115004a200b1000131110406080b02e580a00d1252103450840350711b400a1000300c40092140106c050300ca2001c0003003034100000c090741c00c90f00241c00898030a03220344504083c0c1c1d0054504000580c0000f5203c4031450388103e00340410640c0c030900303502c0d1455040000b5040e145900600320254041c102003400c11000b54041c00041180014600032441c00c602c080d00700300209091400031400300b00000d091303c400040400580c640b5a400701d41000009001141e50b0b0010b46000303000c41c440203071100001e4508008510010443d84070056036894014a004103000001d88035200355449810203000280c0c20092181c0c6581c01072400586520701400d200700410301c00c8060400302800c402c14844c12a50224806151840b102d08507440e00281b40002356031402c00c0d02c1000c007655498602800021a28840300f038011000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 548488794 1250 548487544 548487547
    0x20120d030b0315011706011406040b090415151701080a08071a0f07110319030b030a020a08030a020717100f1d01061410090b090a08150618010305030a080606 69
    0xf44818400304030203800c821203c2e0346207030500c055000100825405020200546030341d1154401c082003903401640115003c09801140c5120142c44640c007103d8030070300c0460740c18103403a07860004c40e1181600e0310000002880079171618841c103070740c032210034102c070006002804150304544035080c0300d410070041110503449000c0900480b44000d500c0b40c0c0600f103003400314010b030305040c1340180400c1344000301d0110300c1d002031280c001e00c522929010b007444841401e010900100d0310b0300090800d41e040d00c0080d40007000d0b00001c1080c06001004d085034074810b40850746456120700d1b0000c0d5404500951420036409501c060702c50310815040480403038101c03040400c840c082c0300c68201c62011020007098482e036645a003000106074041c402103581e4403c0d140300000205008000300f00850500915a1813400094030014030b4442840d032800a25000054500d48084514290b0980900341d513140c2c82040000c4032030313144011822005040b254408011460454000000d464402004000f568021030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 548490044 1250 548488794 548488813
    0x41b03020d17071209060806101704061d03030a0e0307080403061a0a1805100503030a030908070b0708040605011409040f0302070b0301090207060e0c0a17100920120d030b03 76
    0x30441221300705407110340b00c4c90000307801c10500500018005129920501204040ca10140c3d040b0011003081120044a11207555440c201000038001907074003905d101c0d101781c003144440d0101102550140c2c1600e00e080c86002c00d46030b9403598134010994040d0200008000800004400c0d503c2502c00150020521000e1001e0800050b1568500d5001c150305903401504074202407140d21489500071040000d041c0818203110200b607490154201d06424599101100390a00c40344401396101d1942c8810160940e14002c80010100e100c1540c04459260034070b000802c0000042840c144c8034900078101203555a1a82c42d8880e0000c4106801d13815402148800f00c0d00f03045120095000c0d0000400250f5200742c945000c0b82110b0f0b141d845844142c1050300c20000310383d1082c00003022110007174640200250003001560602c4c0c201003405201c64a0a0701240401c000c00d0f0002c45115458140300003281119002d000716000c010000701e5254200405e41d00c00f943c044e1f4013540003203d01078101c810440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 548491294 1250 548490044 548490053
    0x1201091110030905060f092a010f090f060906120917030612120a0f0e031c050c1902120d0917030909181e0d08131a041b03020d1707 58
    0x5d801341d51002007a01e11a003041940c1c90300f000018200b043d568610441c0400f0515001ca28014a8401d80e0402c18a5080d0049a620980f014400303488504888588242d0b21800070b0845480d600c60312006c60f804c12807a050314002c138881e8070805034002c0c07031504100313074210100d03040c640c07000700380030390242e896403464581703020400ca0b030a03403064260500c1303030794810004028105201c40d403002010014214510304540c0c41c0840c2d1050715006101c01714010804a5105481d180601051080d039840785080e00c420402460210070207040c0243c4054020001c801440f544682000390061302140d2820b508100000c00e003441500b100c50004103881c140808440040e407141d00990f169204207680c0440030011180a000440d41204007a0f254560001d41d08400b036125a104c0c141d200601240324006074454080100b4030b03245590060240405000c0504c1d4400c200505660560302010035a000e010a4840c420a01c2c003070b0781c0c0080845103140501d50b19501d003006c0081000c051204203010307131000078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 548492544 1250 548491294 548491303
    0x61006140a050d0e0c0406080309010207090c050702180f0c0a27050a060e0406051c060e2e0506010201020307090e040206072103180209060420030c091201091110030905 74
    0x84081340241000000042c100400c0d03c0c801c0d0085402c1d40c00400c0b252520340e80008800e070842d1111000440c400c480722a05581c10700030343e0406500076020555440c4299242040341d40f25546c82400f118043d2164010111140542c201e410017007030210300300500c0c1c40100384007050b2001781048201d094940707030300200700000d04a601c2000820364500310502640380c40c2c01408050607050341c0c812624a94281c0350300c180c5c41d940001500701542d4125215038810140151805a00d40064114055040d07012115007030018000d1203400301d1500e030100d4501e40c418000ca034060b21056555200e02414006003003a160030241040364003030000c00080c0c001034038903180c210003440c904412802e2405014405400d50b078284240782440c40540010304010799400d03614a8120000b9940059402500c05510013030010044075440c00c1d440200c1004180b18141d00203088d0094203503203030703012600a94090350a0301e40310b0100900c144038040d80218a424041c00070b0180284528000c1606080e41c0c80b2903080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 548493794 1250 548492544 548492561
    0x3080c0703200d02060d020708160b070309080306120708010c0207060801060203030c031302040f050c1305031606030c200604020109140d020f0d0b011502061006140a050d 75
    0x1508000d40c00c000340070004409101d8400c2d407420304961078a0a01c0041d00820851100911450011603e415420450b81c1694041540804001e40e1032030200b45442812100c04411182054071000048220b0300c6070040440095101201f1411521403100304040440000c200c8000d5119140c1c0c0090010400d00815451040070340260030302c141486002000800145c000405640c820428003414100a0f001c5039408881c240d00c0601a00351440040c018202401842c0425401e010034000c2081380180100721002c80c1c6900480801d9031101496100e0104968160a1444410342084400d01a030851036001d0400d240c0108102c074030841c0082c4800c1e42c1c8905074096800103007044119604014000c002e024131014000762802c600d8000f50700b100300794070004e024000320010fa02c2c0743d40f9507414010425901420a809540e110b41c40c400c80d520407034a031100180315a5003ca00c08030303c400b950310140d6540b03586450700c0110008410718103074401e2910317804129041104041c441e0247c441c0406 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 548495044 1250 548493794 548493817
    0x17011502061803040902070204060e180606040b0319020f030307030f0912050d11011112160c0c09150b030c193b06030103050715080412180308 63
    0xa54841042000707140c40001801d0b2110500400c0051040d0000041a90201c801c07001000d6075581c054070101c1d0141003a40d00a029040c08003051180da0300c0b8952107240500070301400c031080c41d82d500040009444909110580541000d81094507200c0046400034135140090720b020303480745400011910f5988440c1058000807005802e42081c02d601205107001864001c4100b9100181522031079150480d07010b100040c089000280ca6000d0781c00e4200100d040111090192210044e011041b0030800441c0e00790340d101c02c00400c0c15070142c01194546011a00708420785242414899540014040301021a41c00d214588001540c881204001c510030f1915410071600e5014004038840c1070703403002d405c00d01489500780314100d910362110301c01e805104d40c40c000b04551200041c400580025400350194210b140000040180580000c200c0115034525400d40900d2502000031103203042c1c140e80040a00f40d032610482249441020035142d01010032905200e4150b881d9030301c00c8680e00c24021601c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 548496294 1250 548495044 548495069
    0x30c0c031217010501090b040b031810020d0605030628020c0109110306090c10050f090406090212010608040804090207080903161e030b06150417010b090c130501050306011701 77
    0x51041c2c10382905640141428280820070500300035480c2518000c5024206070114040b0002d203003010040609000da03500700054450049030800d244002c2e510841011001c941045400680c509001401a1140c1520b000b002415480c2c802150f00070041607002413400c9400344004030540000b886002001c51080000f0007130241c40100f0715041c40380081c003419980c0c20400e100003083d11050140e0000e10550310b0150f0f03480b5454000040180140411a03400500d0040301040f40800e5600418540d070301b41c156022a81c0e0f842000700e6040c03104030703070007000c042081c0300c1041100c0250300030b0302d01c0074402e92a25040c0016180400c0c03070101b0312184070096142c1040304104150344000c0c0c50000c6030361a4041c8032490f0940d03c070f501d2503070009843e29000715540e11210300350382c06540070745005d00101062010b1610b401d08409000c0c01e103d0089501c9102c0b1070b404100250001c4084400c4000341010300d000003840c1000564164100610407030502c081200c0382942c0d0040d01f01d2481c042d0400c2412035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 548497544 1250 548496294 548496317
    0x903030a140f0423040c08070e0319050a0605420405091e010c08010e04020a0503100212060402090d11040219090312080906041103011509050601020c04020a0c030c0c0312 75
    0x8511404034943d003078045d502d0000e8210b206640304038003503401051030134a092440114070110740f5010303044901c944158140d04595041040204405071241d00906080c440c0d03444040c8600e224032a1186507400c0a0b4500826600c3c8440c0e50713420001080d075450043c00c030021000701140507075408481c4c80c4100d4210134034007081d00000c004058001482a802000114143d480140c001003040c0102c1c5503030040400003400b15914040c0000c060030000c1d007520f01da00c60b01074000c0c02035044030050840c0030300314400150799410700d031080d6207812400a21103001040b40c0d0300c0d0290403480840711560490f07000c104000b455804080100c102c0c0d000307903485d10034440c614108020042c019403d04000c00c041042440003ca40000b10303150420b41001c2d1000c0c0c40720044c00041c0c010b0140c40720050070030320303044030001e0080340c0da0b03100911645083c3c00781c1d1300e15420384c42004200e10403d103456000c5403403241007101103441118030040e55881695211324080d142c3c0c4a202c94009000110741c001490a00301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 548498794 1250 548497544 548497589
    0x1120f02160501020a0216060905090a020f0c0304060806030606061909050604060903150203010e0402101e030c0f0f1d030a060603052803021203040312050c0405040c050903030a140f04 81
    0x40e081c100003105d80c3c407591f80c140320f00245010300b2403207103510072803100001c100d02c00150b41c101c946280f000015540d95422180e142600d07600240301e0f00d40030502d9100042e00c07a0501041e10383c401e4000424103440c2c090813180100b04400d01107000810800203840100b2a501c80e0340051001d0302098a401e254103256140c01032010260f84d1b0740070f80c050b0040c001000400c00e02e2244a412a40c11145812039034803540d401c0741d00700c034004070002100000102c80072031184c066008004c1804140d5500100294001c0148c070010b0101c80d6410004544801c050083d5841c00b041003108800201a942c0074040e0b07441d100140c0c0c00d41d40095030250480c00403504450062400320030741140ea140d18403c00c440c10784001e52500a110030f110780d007100000020342014030a1801c00b10b1803ca01e00108010304140f500c0380299013150003080e0050b480e1a400c0401136000d00160781c04084002c00461400450390001c03201410306800502e07c050042c010178401c41c41c440e0240c0b0180915011994459490380e0a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 548500044 1250 548498794 548498803
    0x7090216060e1509100b03011a040209011701030f0204060512100c140304080409061205060106031d060412031104030b160903050f0a02040b040c120e160801140f0601120f02160501020a02 82
    0x1100b8800d81c5044000a000103007204009d010103011580140c50b2480200180c0d10b05105060041040b011440007204100584030b80e0b988190013520100301554540c0c05101903e20b400c01003014a40c041120100038a1003900410503480180c50030b5840c01c0d42135103824500750020345d42120302000124090040700480d20482005080c441d40030038540e032880d00ca490315140107002b48420580c541e84a405080e00044071101c0004440c8211115442c003420540740007040c81e589240040c2c1404440000c600400c02a06c094030781008102e640f1340c035150410306206540381241000d01c4101c00c070000220740140202d9141003541e0b0090000507249104110443d084881c00d40c2c4101c0c036080c00e40b2900c035408240809070b13000034100000c0d600d1004400300e1401c000c1815500c0281004200800d10040c10b4000b4400000740d208241c0c203a440e005200e007032001089071030358006401d600910300790740b07440d800aa01d107200e481c40040c42c0c00f08003419030030005469401600c1c1690002003a0441a03030402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 548501294 1250 548500044 548500061
    0x6040608060d031b061b170a0c03090c0b0304020117092a040e0601060806090f0c0a02150903070309170307021507060c0504060f2d050d090c03020307090216060e150910 74
    0x1410300a81d20b10000c080103d0315025007000023082c0d441d0055041c2034002e601c4200a00c3e08070004248070355640320540801d40c42268202d0028080d000c60112058030034000c41c0c00307580c502c4045c0c010340c045c800801c8140040b8580002141040c0004c0d42c0103078540b8070501140701c801401030415503040c03e4000e1302030072015091034000c1d198981000b1150031018901034000240008640e40c510008500324608550250112981c52101d000c0c417028400000080809511a441c1d4000050743c41200c0390150850525000341d40c0c104001400052420851b442407005040c00b0780307070070124151141021204a550664049040018240700b00c5400460000303c2c42405d14150141c0c20b00d00504580d0400d10002c0c0c8000101109201038015020784251040c0c0030303505108221500c51410031200490980c44160b01900440d080818010400c2c0200c40002c100c110141c0d10520041d50340000424008004a650340900d04184440301c00d209011405001a900180a000c1032003810704100e40c04c09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 548502544 1250 548501294 548501297
    0x2012109030f0e1c0f021504080c01090f05060a09150f080a05070c0311011103150a0b071121060a1d0d090509073b06040608060d031b061b 61
    0x30a1050309507a584800290400c3c1c44e00100c2410709240c0341c40f8103101507500c0006c2d0b100364900d502540d90088100600122004841118080c0e03110b00e0040d01d107000b05d40182482403002e10018846810542c2c02080342c0402454080d21841da00c0b008001d02d00312250035035000038545882c40e0202c0b07900c01c480f581c0040200e00304000505200002602d08491044c0c0101846201380d03948940300400e5103c684c120100031005541d1340f810040c03511800784840c0c500b91007031210b5280401c00e038102ca416540015400342684a4220035602003000d8100222136426141422044000c040b43c020b010250007005018004941070041402c81c00500c4981744400300d0b507620072400a01d2065000d02101d0490708203a800c1074a9448001048441c0284500c07800c1c05c0310389010900c5815406030130800d4100c0042c0e5518081030060030f040044500c1944641e070300041c1010081901441c1464082d60414440c0c1405003242c1001c405100020000000c1501c1e07040c0d4417040040340790a590443e0401c00c481c4e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 548503794 1250 548502544 548502557
    0x3030b0402090d0f03200106080601080102120a1e0f050f01080313060305151804030201110405100f11010c03020909060409020904081303230c09190902012109030f 72
    0xa0802181c00c0e50003810020308100d5002200130141801030b841c802003024481004036210b105110b10b14041c042c9481000024414807000164410b018400e0f9007030649228031803800c64503070613850b00142250507902900c03130056440001842e0742e14030820360324000d030840100311454054040c510001059008503283c0e0070421407845c0040e88100000b09442c428100020940c80380b01c01305012404285106402814848484101010403208644100c2c440e60080c00000c0c2c16001c0712805000b070348249a0040100042c020a082c018003016170510a80d1500a143e01c0225031403a00f03580342c80030781c000801e50019070b545d00c90410107903071070380408140c5060000c0140b60340070800300c001c0204060705550b40071444400c40309024071090025904235400d20107810414150090507110303a030307250009114554045a007810a1150244500d10b02d4200408030354003c0001c00151886010407410085d9007219034400e0350941200b4402076070351440000d81d0980b1490040c0040c0044045030003400354 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 548505044 1250 548503794 548503807
    0x1807330503061e040f091e0c050112200d0b0f031009020d0f05010b012601050103020a030f060f14060403080706110405030a0b0f13051e0c150703030b0402 68
    0x1002811079070002c0081e9501070340f9180390104503070450f103694109503126041460881e01e00c03425411044002c0d00403524151040310000e0818903101d104c1c1c90040000c10126070811903903002d080340b00d8041c0c440d5907000c140690440d892013240d0254500c0b205941c2c0010406442c5240288540f2826100540d03000e9000825200001d0b40d0303416080304101056107a02002045403070b200b101c1003d01d03038030004c4518000e005142c91130182c4030009016002410201005038040c61603c400045040d603400409661703420000110080d46c081c84800c41810b41b5003450200a4045119800041c801c4032440240e440c1040c80a40c1104040c10400348502014030003480407400050860701e180b039209100140418801c101401a40a0f5901265140c01183c129805202041d200588100010000c0f51065a02c2d00c1c0403111b20303c589030000c4d12a51100c00070705480d03084400b42c3c1c6403040c10380088030704400c010f8002412410308041d9142ea642c001054450805400d07010b04000c000c01120194140007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 548506294 1250 548505044 548505047
    0xf0911030a02090d1a041b031e061805070807090c0906111207081801110a060b030a0b040c0905070f3203090f06010e0c070b180733 58
    0xd0041c5032010b5001420340200d41d0781c1040d0809495006142e80c20342620040e0318040d10341308840c2034400a603e134412101c00404030142e1411b40c0d9108480540a2100c035060f1410310880317401c202c8400360b550030203a80005a404d05029801d110b04000d20006040ca8a690f092040540c420030300c203410910342030080764102841d0307400d649080c1340c0300b8000301d49004800d00d001040c0c4012844e0303400c0050741c403080c0300424008100c203085c402d078840b1420b42c0341c0c0011038400d1031881081000c2e800c403080c8600025400e402c034090101c8001c04a03407444500307444502d02094207a4084a0f5145d031544108110281e42c0101d56001da1242052380c143c601c500c2001d4550140003840d40a20302c00251103e0000070031a40e50490b81289007840b603120324000342c01696460070846006003500c500e400008890341c01c02c507860f1140c0c0c00000254245251031703644810b0098040c005080c00c414103441d080d4000002c02c003500c001d0100c5030032080e41c03180c040c0301e0310a0740d490100f12566100c00301c100c02503140e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 548507544 1250 548506294 548506297
    0x51003061401080a14070e10030201020d0906020601091d060f04031101091203050a15060f0215040c1a0c060a0204030209070512040b06031e0a0b06090f010b030c0702060a03060f0911 80
    0x6410449000b00c08030100241c1b0300381410342d00302e01c600b004200148500585074403025001d0f28400e07021200315100380794040c4c8041c403051160000503440200180007010141d04100b609800000c0e81c0d840f0241c00c0344140f403c148040703d480e04003200710802c10091550003849080396041c3e000c002c1204225a885070400e030400700f61410207154070b401c007007824415107500c0840ca4015404001c1c1c80180c0300d40c1d004000c905ca04040a00601c100e44240b521441611001406240c1c09a1100c200138a450510140d0300560701c9200f544c000188402084078406224031489036007c4c0c5401650780d400d5204020720703c00d001c0e20f0f54003005414021078032500c6101e04840c2d0041d400442071804c030340d2001d0010745840300359240c6423003010000f031682c2841070000070109406449400340002c0d13a071f616401c2c0070158404885402c29441d503000100100364503180159001294924000c0c40c000c8a5004140301c6d0b0311000400300080d035540010446411103040c0400941a100b0003440b100c44440404c0c00c45 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 548508794 1250 548507544 548507563
    0x1e01060804030e0a030b0702100c09060c15110f091905090f0901320a020a1b030909090803060906060c1b0a15080906130206250605100306140108 64
    0x10700a442001c03c2c5107503560420301c0000c0d948428a03020514002000070b458000030b0044801075805c162141009a01440d8032400351101aa1100703a00c6100d511071800d050541d251041c1c640d079540311404040150b070b40007080702c0c0c0900e030610380d40e6118942c00e114400c020b00b0a0103050054410080c400780d940d12441c0764004070642074011140e203a010000b80100003109010040d403c1c00d0300e9021081d07028130020030038919140030a0080b130341e6854000050b0701c04c0418443c00a9030302c14001c1c0c3c01d884000d95001c01039000745040c0301e8140d2900401d03001c640f0150004d450341c0c0000300400c140f0b49000c1c5801540140151002810700000703004041d6207001d010907440150032081104501c5480f2154400c00038a0142c6002c8040c900444000e05400c9041e20a0100d40c01290f00140782d01840d5107040a11550242c003080c907002003110710420b45500700c0c280f80d12210410a5460220300d86000719402440701c6000b01c0c40ca00d14529100c812a00c3c010869141c6e020001e00401400b0b6001c1100b401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 548510044 1250 548508794 548508797
    0x15090705031c0503060a0f080a0b0a090c030308090f010c050d0c0905130209040209190503060c0f0304030302090103020d0c05300703020a11030c07051503091002130b070b1e0106080403 81
    0x4880d00d4000001c0c3e0500c07030a0b0411120880f800c7c000040f032000002d00300b22054000d075010980785c0c48021104058a100884c043c00c41c010040701000041d00c5010900c0c0d02030203c00684030b034011000c14480c01c1d607e5480810001410103d0a012544260300c02c0d494201c5803800c15103d418034290100314000c520849581e00c2c035502082d00e0506840304d404071100304800520205226011040002001141e0300980707001e880340400003074002c4500c0c8112164410b0040040d81145d44594040f0b0103540003250711810941c0901c00400541ca1030700a051091000b915004d0f15802050182d01510303c0f4040c1c941e001a60b2101d030140c0042ca54512541c00003024036001d41e4a0140d21f0050358000d00e40e00c0b40ca4418800020464007940c0301242c02d90544d52b0031600f40c000c240030b140d0030401e1400706441d0300a49820404207801c15940550080441c0c224007031400005aa560600c10b00540040d40156007034100c2004110100243c03202c40362501a0780052503005506285008180d0754008000130b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 548511294 1250 548510044 548510047
    0x1050729180c150c010f0e06090a0b0f070e0603090d0f14040b0c010612060605030105060607030f3005100902041203050307140c011b02240606070515090705031c05 72
    0x6103c25141c11502100350103c028000c001c04466035400500400c141c0000d03a000b0b50000c505444c0c1c2c003284801c4040d400003400102504e4084425102480103403a81091000c1d00c16500020340f28013001e1803007650f0f104d0140540103030703200020304400343c151101c00411800c4c6402c050818481400d81c1c041d41c50f880c50b026140c200d441105030042109400644801c11072090350000c01045420110035104160000e2060303072181c40c05d10400340940000240455072040d164034419110341c02598462783c3c2644040c1c07901c080e0751086001c900c00300c030541036500e4481c010400b04c24481c24480000340b002c2c4404619052800d0103000d21545640300040c1044400004110b11502c00c4812050301031060440641d52100000c01c0390080498a0548034102c0c2d0a02072801800d0020922101700b01d119544601c403079001a1006891482c01004958030074418862100442c00c03c0001d6500c401018105102e0b605101c407a0303d00e00740341d82d4031052003540121824001c0400d05048601101812b04099 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 548512544 1250 548511294 548511319
    0xb192f03040611040308040810090b010311012a020a050603010303090308030c091e041505300a0b040506012c1801050a0605040617030703050901050729180c 69
    0x40018140d0383c0c40c000382020780410040300748860b0b003009004030741d50041110f0080c410103050303406581e6020005400c24420700e00410201d03d148806288140c0c0515101070384404508156085c2400b00018501e10003840c2d00c480118240103d000d070241a00f200c3c8542558590b50b0014208507140c00014490f8001201144901288000780c840844006003190054001500c0d444034518600c10814400d50030041000d402e1036000a2240c01c1c1c5101404c511022801c1200000860000c5000e100940300d0b56150f21380301303e0b41440302c00100c9100329a070360310a041505095281c144107030803510304c1d052103c0500c0078813503040a010014081c00b072862a01a40c0700200a498040c02c4400c04003a035007000100f000742840c070b034084000d48030308031400c100098441400510885a40b800c0180503482007003540c1c0071a0041002d000b882d10145091451b241e8556540000c03000c194040e41040c00700c400c8162040c2045030b051592083e42000c10303400c803102c2003001e5030b43c541000c03031014050003010004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 548513794 1250 548512544 548512553
    0xb0612150a08280215040909060b0402180909070902070507030b06060f0a0f300c050405030c040504240219030c020615240319060b0f090a030b192f0304 67
    0x42d041c9205d2680200d448075510400e80000e40340c0104122902468244012850300e4141700b6120080a0f0307000801c0e1540100c0c042c000b00315800f401340c10b0148549480011003105600082c0050340c4900050b03d0450300e10f143c40050150b0151201c0c2c858201441816480c1c113006d816201074095503d0103a2240b9440c2c3c0e0182c0301d003c01602800c103416100c07181c42c0550203940002d84034940300c1c1c48081005022094049078140a24060321f0f5040d040b80c800c4407981d1a082e0401604940100411032040744d40c11580300d015880e802099001c190017094032404600f40b5803131b15199840504050110744a900e0000307444010052012800c101c0851081c04580c440e8250700fa8009200c518501d00300b50300042201c002e400032200307203c1c1200b5145194510160034002c2c035044594161900381010702184c1d60b450320787c00c000902ca42200e01c8072030000200d40f014802d90b010b6250051051340081803041140161604030341e6644502100401416901ba0740240c1c00c034040000041c10b40d1207896602c1d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 548515044 1250 548513794 548513809
    0x105070821090105070e060309030d0506060405030a03090603140c030402100e040203090c0a09060f0e04080702100c02012c100c020405070e12070501020d030b0612150a082802 77
    0x280000407401c0401000362415403005000700b000d511111128a0440c0405c00e0600c0100d6034a9a02d410a1202e07000803031190300300c0d5401c940024056410241c90748003191401e0b24260082c1c0c0028804442000180e07003510800c8101107402e14643c001e82390012000685200181c0000d00410000325200400d51190114034080300d0000c0c41550380741003001c0c40380d50f10307007000c10751510404021000046200052243d04101c8411414a01109107030010040608800600c00e44c0c0f540000c10194005a45001d40d00b109090303980c407196650191400010b1540d00c0c840c0018840c410082c1c031080c12401c4405d030080c44032404551201151b481768008507900050128001d401c2410704c0184044a60050306800c103800c02620035aa026882c0c1d000b09030350300d20503c281070258200c60340841d403d901c65000b4101302400070380340e28030741140078114000d030000c101c410f10603031302a00900044e103192140c0307001c000b0000000141f079860140c0b0740e103040243c02e10041030400c3e1041102da4045444444 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 548516294 1250 548515044 548515087
    0x10050a0303120f151d040b01060309030c0b07030f05090c0d02061b030409020c1515090c0c16051e180a09021c030206010504140f0414070803090a0603090201050708 72
    0xc09114010811030307204c104a90301e0140c0003011650200c0d00300c203e010310110911480c4c0050440d1240d0b440c01d8002e80041140c45000d81c2002a2a029180442d0890000e54003600c1381d0356000481c0f14210482800301c50003d0f06145981c0c00056402e291940c0c0c600b40225255012203607680e5a0390110715030144441c101900c41003c2c00042400070341c032050342c1e010f0202040034106840f0100c141c90340d28416080308852558502c0903010816040341000290103900c010321340d0000b894102180740803440c00e600300042c400300c106200410700081c200440fa207019401281c8456801800361310001e1449001481c0c42e041840c12080000c0a000d4560444201b050b005440030501155100170303211620320920007038015224440002545080a1003505444013041205070456111401c02080d00940500300b940c01588a504840c000a003e12204000b0300c6814015643c07000c90700244180c042c1d19074407032070a01d40303080c444d4805030760401d00700c964595010f032140b0342c0c0300d156034201140c3c0c03461503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 548517544 1250 548516294 548516321
    0x510050d2105120106080403020c0a0806070e030303010b0a050f160b0103061b091401090e0903092b260715050a0c051b19030f0810050a030312 63
    0x151040c4052101c070201201d403400200010711070300c10014600761800d00c611268031031520814801040b480341714803c0250001d102e4410b81710b100a0b10400244410b1240e00101e140f600907000307000d01940c04c80300214043d03005030b001d141035600d000071448090081100c81814003100083d020040415141200c00481e41038204c29104090f0303051840703058100b408201c8038940382ca81d0703940c1d50804081c410340c0d0398902d99a6000602c0d0600910178100c03170fa0960b50314180718000314046003010040c001144a03c00500080d40c0f594020130801c00e441090000e40303410043d442c00450300764419000001d20640c3c00ca0300d24111815801c004210301d601161840511282c0810000708100041d001c00d101c001e0000380903c01629100003c008a900110309400410303c10007580d000c0441d1070462000b400b9004080d1042e8107005400700018007013044003100000ea1102c01c814455400242e0340f50098421900c114a0500f00000b00301700301441d0002600f4000020780080e44d071401070300041c0b99407518 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 548518794 1250 548517544 548517559
    0xc1c0f0507090209010f091401030b1306080d0f0315150c1703070f0302120105130f020319061d04060f1e0905010608030a140c01020c1b09100612051005 67
    0x142c010030402500a804002d0005012400114803a88a075890005542ea030180660100d40240010340090624039142034000e600710034003004201c0d081c811840201485c1d40940182c00f030301d49009101740314401989041c540f61400e41d24490b00b289030950240c64214550b442c00782000042584c540d06001001000a01c04842c010400c0b030103900514014040c0d03440700c10b130800c245541030b070030780c080c3c20803117a48150035000400c0645460010a501c0021030b00d00042c00c1d10544110a09036031048030a03404c440550031420402c1c0015202c1e60b802005c02c2c210150f400962007404080000340980040c10741034480740c40044103802540f000c1440c0030072100c3c8503d401441c1e08590042c2c100120243c0c0c1e1546003a9000681d0070001c01111407089043e5208280e800034081c102d03610f9080000384c0c184a40d828030100d101907078100040c22440d1f101d14905842011540d04110010342c008017034003503803001e20104004043c0c0240040e80089401403020405549004851480300e1066119981c400c85 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 548520044 1250 548518794 548518799
    0x3080d05180607021f050f070e0a081221100306050a02040f06020d021b010f05160f081b010915090318090e0c0f060405091e010b1801020c1c0f0507 65
    0x40004805c02d03a03440b2143d6000420510702c258204071b410490b0103007036602c40b80f00010105881408041c4040da030040c4a060303030b55110428985070800400c21444803040c0001d03860ba0b9040009429042c0745450b02e142e2440d4507007026034900804003480001c0c40c094031100403c035820202c0e01581c0c05408540c0c5138071105607a032000203580716100a00c0030302500403010102c0e40c01039044c118124500041e1243c0031300d01c1c10310354203c440da0b000c804014072000f000d03240d40e0001100724005252a03800340111640b60800240c02c2610003c0c40b03240c0030030700c3e0f1404183c040041d1f000310580b021100501c00c0001c03154850b0905403224a03160b51880d178041562400170603000c0066000c01c82d0743ea4028116102d8060071030a1150320a0480c045681c01482400208070034a0203001c8294821041c061606400c200800082c640c1c600a030008600070a01003843c1d821042c000d1070030202e0340030910003810803060002c08070b95407000c01c3c011074201000c1c48107140305000c0c4505007034a056032300200b15210b266 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 548521294 1250 548520044 548520047
    0x120d020d0f14150a0b0f0408060a0e0f160e060d12021b04050c030f040507120312050a1a04110913020a0201050f04030807120b13090c0f03080d05180607 67
    0xc41c141c508101e0b1100d00020604044110340d05080360030740030700b0f01c0914508100b0f00c0102d58003e441d032901c400b68108030200d103101e402d01400303004458000c1c001c00c4074502c1642440c1445180c06400741540e20800d42050a502c0504002d001c079a04094103211589400f00440c1101c80401c030054224440740310488189540024200311100c1c2c030004080c07009000408000540d00c0648420014040520204440a040400d203a400c60f228800700c50210741d841640354280344407102c040d00401c21a64042e8407103180350081d980d2104484104220343c440700105210142501c1c0180303809030796154040c403014160f442c2210000500100042c0c0e41145603400d00e00079502200000005500300400310f21043d00c2e8111b000d0096a040e21440390395940c0000842d45a244500558003180e1100c08286050302c1c0c403003100005940e014000b152446c018100704c0100607080d806101144c14404040001c60801e001761920030007901000b0860361581402964802c0454090451034021042800041d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 548522544 1250 548521294 548521301
    0x408030a181b0f0f180c030204050a030503030a0c1106150a08120c0c031c0e0409140d080c0316080c040e090a0606050306130605060d151e020c120d020d0f 68
    0x585030f503500b0340a80b6484003d20305201c603103803003203200369102291209904503403500f051203e21000d03e40141816a18000102e1414041e44241c603140c10000034454810040d006000c030f01000c5040c626000f004248425540d204003c000d81c00342094000e2011403513442c0e2242400411101088491208420801021541c4118651a114480d0840340d9006080124041502c90301d5204c2d0440030185140d000e5034598003071506c40360720954441342c03000024018074842e01d2181e20903000701650101c2d8900030b05a1713a070280c0000007444040c4100100c0074103140c4001d81c284c4813441c1894160700d400710084e205010f641c00000c280500181003040040e000200440d400d8002d2400340a0155200c06054491206558a100354802454803402082a5810a54101c10041c109247c00c01068403031342d02840d615250003403810b84030080c0178110940d0107001310145c10094011032402207086419a0350b07004107040000308450208003c0740c03109840d0705030b65100c1c04804052240e4002d040340580207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 548523794 1250 548522544 548522549
    0xe163e0318030a0f021309200112061410090e0129130902090105120906071412011401090f0303052106090a050a0209041b0e010203030408030a181b 65
    0x201400c003140c01c0d00da858002101c0705015080306071080c0304038aa409020081d0b100c40b100c1c1c003105480b41410300016082000250003004d400b0459210000c2c01000104041c4941c10395800c000e0900740e050000300303040d00099032041401c42d5100f00c1103552402c1620680300540c03205580900e504000034071031000295006c98000258004407407030380c50704440340060180345580c489036000504240311801107036004000b40e440c14181142056a01c00443d400e04c0000c651104c0d280d0003041c140043c0c01c0c0c100704003074124600c506500d42042c29221a070070080605100303101c0d154003000441221a4064244031000d0802001d407034101e079403207040140081e0b2080940e80130b00c076075120140f000503e00b03511141c05107500800000d074036114000520080d1101420040406508000d40182555248a84c0c114451100031141c51078481050240280351907180007030664008004000001d8503420840b50302404101000540e1340202c01c4201c4d5400117440011b01542040003160300d110030340802c203003c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 548525044 1250 548523794 548523817
    0x90b2e03151203091d01050402180d0309050405160e0423010e1b03040f0f0302100207110f03010b0d060504030903080f12071b0b04020f030d08010e163e03 68
    0x880d82d40302548008400755100e500c90405c2c0320010312007880c0c540c008241817260821421002c0008600050008807940f07822008203215440810003420b01e4000d1071380c00224145c01030001c1d140d01c0070180c40c200701184141d00c00c55449116035401e001d9400c01042481c020200380001e580c4030120035400780e000792804510101c00700c140000c0c00461004072842180c2c040c007048816201740e6501c241c50f40c00000101c066018681001a04201c03d20203000301a00940c0c1c003074164030540c001d10420703103183d40b07540340246d0414034603000e1750301c928030300c100e8450b03102c2c1d0000380c0e95480d820100ca9040c3c032a080200300c03000001d8190f1102d1903541c06030440d401408020000f90b1109030003a0381700c40d04001c00e120018541c103072250101d60041c0945521500180990202240d00700c0001d09040c0c1c0c1c5074150b0013003981d40300140301002244c50903e9205206203180303c020a100140074200c4841d052503030018103c40d607900310800d0404150a036160207031000a81128820700c2c1c5042e100c0d00400c02c20786 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 548526294 1250 548525044 548525057
    0x5030a030b0409080a0f020c030319032306060c0a0b040b0124080c16060e01020c0d03060f0e0a020702030a030806030d02011e0c17010b04090b2e03151203 68
    0x14403460140f007043c50407548041001d241c005400301c1a24864082c0c1040310950050320045000d5450900003001c5078000c0d0310504002020048001d030071184121041e00181e405c10b84420035400a070768100d900710001b219a59110b82010b00103914200680e04000c1c4000000c60a210810038041e80423410f9a441c051111040100b5000314050080c101210f8000200f0380404590400319850082207400942141d03801812490b44610068400d4000841c03030b02d07940010f45229000041c8a051000c1e06240703818407105290091070548801d19008907200c9141080104c1e030741c5001a03040300d409680c040d054500d007001e141001b8014200c100c07003050081c002c59000315426032062040c11000e01e0140d2104503440582282c080050044180803818000d0006490515a41940c40b030b074028030003200e0b4140e60701e042c80d00240c141c655440c41503004e8a0700c1c040c01101031070010803080c40c00b0140718413844418801401100038000702c5900354000c02c40c0c1107000c5503110303403a0422014103000f0344914 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 548527544 1250 548526294 548526311
    0x120c051e01020604080310050a1716080706050904090b04230a0b1f0315290306040b06040b0d050114180604150906060603020901090605040f0506160f05030a03 70
    0xc00030510080c1030050b005000044d0004944401564016101e0311006191507102d5020581207041500101102d103a40d042402d42c21030304000112007040390742004100c0030703c0c1843c0c66907140e201c3d000e20350501401180b01111034840354090790050b40c02c01010b44140c201810324142d007003034801e0181c03e0164400920203d040380007652118081e8440c0001c0e8a40e960b0404918201b15080c042224100e280304000005c5500c00c95040c1018038030410005000b40300e02c0304c94000389142d80994481c203000c2030204400d80e6000c120a40d0260308040c900f0855511400014001e00b14440c1d90b0f640085030b040501d00344601580038002001003952280e219490b41d01d4400d810160b0551a40308030790120000030000b0f200300b200c0741d04041c850b110210b0000f0300c0383c1d60b14041c0c5a85810060020f5404a208915982d00c404424010851420441d2500b42802a502d4564030140541ca00407200000e00b502c030141001c075103910311030f0091191201040710307203446c175100d030b004000302c400083c14101d04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 548528794 1250 548527544 548527579
    0xd0501050105090105070b0925140312030103140f030a050c010b09221716050618120a0c12090518160c0203010e070e060301110f030103030c0804120c05 67
    0x203d81c8400c0050310f400f03062010683d25990307046001014140a4011011420740c0c6441d01103180040c1000e004140a180303041c02d09250313004400410140c4654003013161200b9010040e401c49040d42d4120030240300000b1002100c5281480c54004070380a03101c00511018410b50140180a02c0c01082d0024080c3c20b20b07010421542060590300700c00020301069000c4101e014020306405410b1007450311204002000040c211103400184030f880780701d941440b13072408121061000982c807003141c080740c21074070200e12a990f0f40e91100c454608401d400c0003c003010003030702406004140d19444509941c40031441c0f040100708041500c00c0c14081d19460102504214400d40200e01c940b0300300c221400e000c906010129040f12035404166015581da01c00c0f803807101da040c4000400f420400c5913004c0c0504008041c1400c461502031200041001440011401074100b4226030440c3d805203031010140070340c0e04012030207100700d9100c4000c0a042d50b56001c20131040e014074100325281142c0f02100d4080000c0d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 548530044 1250 548528794 548528797
    0x82107153b0f0c09070c0804030b04151a12030708031806070c0809040c05070501140f0606040e01140103110319060b04080c0d2306090709200a0210020d020d0501050105 74
    0x802c2540782c20082c8541d019040441003d42c0c05601407600b0302c440001925150400d900c1504151089040b403000c02081c4018568640072401c410b00701009000b80a580211894103c3c0e11414807441e65a20f01402200080040e248500d070001d0b0000e070b4030300f0421440c0cae0b810340100e00f00c140306000701c40006400d6402840460300e150742108440d817414000c2420030005104101030b500520505010210103c0d07003d12408425101c1e40356034a202c3e003069941c100c032000004140a100700d200300b00030700058020741c04403811141200010101647c0e0b100059025100602010b009100040200078a1610042c3c102d008203554400403c0038a031075450402152056000d181041d40c011900111075007000141d498829020784242d80000c449440203a00c06c00d6010038075907166004000f80b1140c03030300511070a0f006111000c2c00b00701007055413042414110b200c40210302030300c0012a41c6c24006000b4041f0b121900c5500d00215540c00798018200001c1d0040502017040520b03000001c11694040c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 548531294 1250 548530044 548530063
    0x204080708070b0316051b1f0204050a0302061c150e0a150e0901090501060f18050f070c0312091a07030b22020405090f01082107153b 59
    0xa90f0b480c59a52904105202920400c0001041140400c2400103c41c59442d00da20300041c8030000c1c010f1607221003003140040c00d110070801021441000100b000799150110701c400c03070f07906940890700d1751010700182c00000c10304860054054244840c007190007940c0381001c800d49122802c0a4043d8031100d441004503100082d051062032050394090222082030b80c00594030098000000c100d28081d659500c0c2941d1389a4041e895081b0951414822100220480645e8204040c0d04018500d03040b10901500c03034020b0412018000312501c1d2805043c03060b910900520801807085c480402d05140403a00014a0030116039411002d0020030340c1c10b03119028500d03c04000400115a0000728110200140044000c4d078185980c00c010020b001d03181e030400144603540c807410003a0503614245e4458201100e520310758100b000d59003d0b0880c0c2081410a0b03c03040d0b604880c424010300364400599005080510b259044618a20010800b10030391032400c000c501c080301c0c120901800c02246d01c50b610b07624070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 548532544 1250 548531294 548531309
    0x702060c0d0e0a020409080c07060203090d080a140703080402090601020105091203060a0305060115172202062820120304061107050109031b030c0b06030106050310020408070807 78
    0x420078494440803940148a040d0035100c10b0700c0141e07007141d00003011260025030445030401c0c086070401c025101440800010200c03030010318074009480001440c2c44191030b0000300014004120030702428425241a14a580010350701540c0c1d65460030050540c1008441c200d11030100f44001400551043c090300340100806d100400e203102441640e000c1c01d4000400c050381110f50070380000042141040f9450007001d070208c110f03e1403441004001d181004100f030001a03080c2c074505200e44c0401c10704000101b00d0100b1108400b2484620000d0100e1281d00110123818031196014004e4080c9612417002c192000e48440c0454450950110b40200c0e601100c14060303003241d1009803000301070100541c2c0c00340c410000010341102003204891355410018090342e103a0340d00d6041208040c0c004084c50b2641100c521804542e8206640c0100380b4101c00b00001d0804542c003000c40c440c0d407002d400000c0540b01c0202910301c60640c0f54107035002900a840303076699500c28404005009040030511409507403d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 548533794 1250 548532544 548532547
    0x30d030207120c060e010c0e0a08070305030d0f0605040509010b01030e070609120507051207080d210209180a2a0e10020a02180108011524050f0c0c03060702060c 71
    0x182c03a0079038400c849510259846501e840981d40200000c1c400c08098100d41c1d00d847c052002c4031424007004003003581240c09103a01140c014000304200009840554545030400705401610710b20090107001580d12285e00f190500c003e000a658042d080030070b030b4182c00e98042025445038885565203036560321454003c80d0100b502401010040680042e00b98050301c11107000c143d40f0404506110300c00140020700390800301c01804107203000e112450381d031245440c0030351294000c0d08200c1c90009584082c03101c420307800142d411580d15000701410107140c2803801c40b1486c2c41d04030704141c06404142c3d039036009440b15100400580e914240034003480c01a036562118115030550500400d0543c09021a0079480742d5140d110043c4d480ca01c1d0079205c24501d0034801c2055140861007407d5070032032315500c01c00c654400d000b07000141384104100000e511281d4080048003c80c01c017910188130b1520810420300d0006116618100b000030542105c55084d800c480081c0c1c1c0e8024100d8680e402a104880c60850 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 548535044 1250 548533794 548533823
    0x1a190608010b0a2109021203070308060607050a060c0905180906011406070b09031305120c011215140109060206010e0a09020f04020a0306030507140102030304080d06050d050c030d030207 82
    0x1d5030024040010843c02d15802e2403c0c0c0c4d03888407003000103000a0b000801d072102010070850a1201014000c0b4880c00e00035410402180e5001d0300e141c0c4c0c0180144d001b98030104044003030000401a8655058214008014050700100300900c1c50449004960180c40744000307004072194a14405403080184001805160f420060001490b4107400307440755110205220010100f41c909410078010704a031002555a1420100c83c0740b1101400e0344214030452084100c0d0601c1d03107020a950340082400d280c0314007062000c10b81344c0d00511030744d80c1d02c05000c3d107006400724081600303c00410b080310f02625621109550761030102d07581c0c08240a4180701041074004215840e20503084020310500c01000c140c0c8040300080800c0c120303040f001030300000135162030042080c07150a020039401b40100d40e6507031000901d1000040d50b40d10003d080200550400502201c001521768000d06c007400c0001c0111010003140c0c1022555016035040c45803080c01201040d0f000e450092080f0741d041c5a00030220078200300d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 548536294 1250 548535044 548535059
    0x9060e2b02120319031a092701061206060e19020a170a090b0c03090d0c140a080c061311010509040b0406080325031b03050903011a19060801 62
    0x3038015030200d810103640300c203080801c00b003800503109000907250f001c4041400302d4002402d039403071101000c0054114140341c0e0700703607203580282990005240254140101c803140818240e050880d00040165192500124501030400008440076001e5081403040075225064941e142c001276942107240102c42c038019000c907006401034080c6000c5428030a0003160344400c4c4004000d400c9828a880c0e96803258460108084000042c1e0000341101071141503103401c050403540c60394560a4031040c400040c074080108013041c5402c080419910098170341250491030060503d8014001c01021350103a07070000340c000584030300c07080c10b1541c000c844119000081001500c0760f40c1302d0a5890340240d140c000c0286a80c07070764020b02c03008084c9200155511407141040b43c0b08036404203110103903051403024900219031301c01d040700c25140d090750110504001c58942541e0902c0381c00d0302941c25500b0121606c041217580e81c48003a030f020b01650419001000b10510085502007405141c1c00f00b40710100510491 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 548537544 1250 548536294 548536369
    0x1c0c080a2f24040e07020f010902030d05130506040306051e15091503011e0c08010513020310030b0c0403030311030415150b1201030303110304050613150c09060e 71
    0xc0100258018801e80d2088102c41643d015400c450015141407003800100f40d81040108140b0807403400804c5004020780c00241c42e940044000e01c10800c0225694203458040c481e410010a402071074507a4a035503c1c81e01c3d001400c011610010000c1c0c2c154542101810490f0800b4426000341c010000d0300d0785a00704004042074003512183e00034807459441000c61300c091050b40c802c080c05c55a181c103075540c2500c03010103880c0761100074420882e0710070040016480b48944a003401e280c014000d82c681d56a0000420382c54690b41c0042c0c5001302d00340038440a240c0c1c1100a04c1541c0c002e81d420b102030304507088011410f2200392001090341c3c040000f40501010301740d200c1840400a00000300c4101d5886007550a15007002451400c031089410040007019054414101c8908240a0450442c039040d120f0903200c0c000108418415816007071420f00f0800100744c0d0f8074103145540000c01550514840c02000e114081c004c18001c10704008a6401c645882030000910690021004042d02e58014100002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 548538794 1250 548537544 548537569
    0x80708070e04140f0705030f0d0504030f030c022701090c0509010f1107030b0f090613030507150f0506010207051e1909020f031f0b0403021c0c080a2f 66
    0x103ca5080524020418240f0900c00e140030100000c1ca1401e0528080600b0201c40d0304d2041c103182d004031450090345400c0800d603804c6941000d0700c14403210f41c1d230505032078440032140c000b0342c0581d462074001040d2880e0050110518800d201000c031b541e0f200d1101008460001040030040f4400b40a030303a541d90301c101079001e0118a94641480344210004e4420f00e0456a030300100c3c1c13a1140b0004204482207156455503210007407100400e40c60070031424135a900041e40c600034040110010302a410b1007094095013203d0400c1a000304000580e00b01110004d0409441c5180140105200040c09250103510110742e03080e85801074010603d05401c10000074400040c642900b2a1440000f843e505244064071031078005801e415900c0c83d0134030240a205180c10031108a8000c00c1030180100c603c01819507080d207505907082c01c0d05801800d6108594900864001d10800c0784110102d00d6081c0850540b00d000c1c81031034128080c0101c00c08415030307405000bc1d500d1200710416250015403800d41c1043c5070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 548540044 1250 548538794 548538803
    0x40f08070c03060c0309110d030e101103030406061404112208030705010b010f1106010e150d0c090b0f101b0f1209050316060f14030f060a080708070e04 67
    0x15a1503680c2d685600b1341c0c0d0802048400309696980040c180b10800d04280540c1c0b50442d0200004041d0340e802900303102a000117280503030502c003019280ca5001e480351072a170303511007400c803500c81c5440e00d481c201400c10750103100701c0015050940001428240076420032440c1c00d0702d2081c00c10308102e8046899500b002c1c00007003081001c403400a060503050000b0407281e40a2400400e907016000e0014194030f03d048520010010b00c00060012a40040340490641d404441581200d0b22000601102024110a45540728424070800f13007c101c04070900004a0340203c0c4144082d025030420400e03414614101990001ea03200030210310340b4840e40c1a90800e0005c0582e11000e90142d40f00d04c0c0d0711206d0403904803908200311039400107541e0490302034001800110000c1158444c45100c0d903070700c1d40062107501c042c8002d1000310709400d8020303007110f000c486140306055140c1c98001c03d8805410401d583c0d450140600c3d4401107407a81012170b942d02a601d81d1802814030314074000d200b00c10440010070035603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 548541294 1250 548540044 548540063
    0xb0109061812060504050d09060206151f0305070f1d1003061a030a110913050606160323040b030f13060e0c100306060c03111006180c020303040f0807 66
    0x2401d02891019202600d0040f0400181c0d483d040c80c085141c041040981824040011010000c141e8000764079580b201a4083d00c01705007106101250034520315020345000c2c552038640b10840194103600646c0b0404c41aa540b44000e041d2003001c0d00c40341034681c02141c40d00d040250302e0185e42041e404a928022480c40e002600703a0359140c000e045055544600300d007a86000040c40204207880c0140b0300ba04581140e82450075006100058000c46405030b0141103503120030000380d866907210300365000150400090f2200c102c461400030700a101ea04202d0810901c00070f041c0c1070202c604410354041c1d82031000c0300c51454440d49508450040014800c0300c15150000361100050010f01408040e48420380003080c0e0034007100c040000080c8000c0b00310081600d45001002101d034400008980b090f00750401d64440703a0100740d420f007441010f035869204903040800c0001d00e244041d440140400304000208940039460350126102d00c4251009070450454021880100b1071180c0203205441c807510070704 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 548542544 1250 548541294 548541299
    0xc0906110f0613030806060310051309080d06030506090703080304031803060c11060f0f0a230108060403020f0307111309060509030414060712050310030507030b0115030b01090618 79
    0x42c07074020111924001e240c140c076824410180c0249680d908174200722101420340c50400844220894a071041511480300c0c03441805000400e58408800c13181c021103da503407041040d0440001d0320041c441156603102c0c90700041c1070b0a401041c24015279502c200e06ea891030301c41d074508407214660400c5e20780038403400d500004002482031144000c803459640713808440030711078047d43d0b04043c8024001c07184844800c0c00c119510144821850303010340c150b140000d03004500f01100006201c4034400418035034024001144000000409a02c114807a03400c4400c11300d0315a2031540c5a0013031100060003903c00c030340307501740602e04000300074207844081c0d00024999685071540e80075a202501c030040181c00003d170512520843c03849552800e80b0650f415403400d1225a120074a000294800c07008200010020803624070418800070002c5420404030351100c1d40b20704058090003402c0c0b1405811803d6951128489400781c000c181d03000105858090f0f40720f1402c44262501c09043d040880305203c082ea02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 548543794 1250 548542544 548542573
    0xb0303070320070312031b0918020702090c1306020a0305041a070f0b01060e0d110621011503050f16080604060b1201052103030c130b0d02090102060a0c090611 70
    0x400f00114041c0043c44a10045400c026040b504039091161464002e41d24904415030005555001c0302c0f020307030f030041c40c0100f404501c00080c090400025840f00c8101d051207000c00800020b0417844100406004510b661401d0584c0c1e42c02042ca00200841c2091204008140744100c3c000c403411801d052081c07500c0c50b40c1c0e40d2000c42007541c400495a01100c04014806203910080090300341d5800e4442c030b042c44007540c80d4540c1040640c0081486402d0005010040c001c80504c0f0590043c0c1e20403840d815541c480b042200c0c150003200300000002c0c900400030300401c6540b0070160144c2c01000844507031042540c0308840c4810014500b54010f9240d00c00042ca1400000041c60a210b200b00100c07074070f50502003000141040ca440c50851060400c04151104034040112608001a0b016155a5020000000b40c42c080725500c074003036500b004076400c070407610503030000c02c0740100990a65084c1d5644106480860380c007521843e0005030341d104203005030343c01025030059000300041101c6a41e17104145 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 548545044 1250 548543794 548543803
    0x70602030f1806060d061d03070b0a0b04090213020304061d0d02120a141303020409290403021009020a03021c12080702120a0c050d080105130b0303070320 68
    0xd290701c20008980c2000403280381d09040050350546000607180a00303003180001e02e40c020000010304681c0d5a01801d1004c907404200118802040701c0a80c1e80360411400c2120902a0071240c0703000c00b9080c1b502c240b1583c68140b03d25440941e00400d08c0650001039401c15009420043c0100c40d00380d0391f6982613110218200c4420b0b450101c0d94002c001500d0381900c02800e0030040344c0300650252040c0003643c100b0340c200c85039190341ca0945844c15220b45000c01e4400242c4115070020750424501400c107410321081c2c1c0d03e1009030810840c0300c05009100b040c4034070f60000d4102d1f0054010b0b04110b118061101041e0000c00c0303100d000400d03501c122900e907000a118540d035001c88070300c3c1012050b244004c0124020700c0c000311036224200105546001c1002075140d148000c6800a220800034024000a0180000e0818142c000e0115191030410241c0601410803c1c0038080c45449505410b8484400d42d0051404010b4080c02550a000040c0d906403520743c0764a8a0042c19a00ca90f42d00c0c598200812 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 548546294 1250 548545044 548545051
    0x3c0513120e15090102010f0e07060e060418020a08070c02010c11061308060604110301030c0308030604020f0c07080f0a03050d15030b0f06040b0f22060b070311060106020c150a0507060203 82
    0x4010b0381d036524034070006402c50317584d407a4028150341011000c07104a02e0210f448011100c01e401c281220740c602ca80000e0041c070403500058581984840500d4200039168090150074010b52513450040d1610541070300c5040c6400da00a00141000c4c01100001d401101e14090700c001c058003460800d0303092002c01d10754801d1500203420540c446403c02880345424066105080e03004404c807491135045403186107001500d400080d20049001000c181e00382c440b9030454584802510a4a49803001040c1041c1c8403540d510450f4003d00c00c20702a00901d84001c180850540e501d038641d107240400c1421a0b00c0540502110124002c80101002010841c8000524031800081c3c41031046441c1c240c007000210780481d01528000c4000750000c0800362a000148202000500100b042070034162020074050401c1e5000800d00d07000200d0300780101504015414145026a4151850b5a07200d0000700d80c2c81050b8501c441d40089000c15208e5210240001052009140c2c40c0c203070301d01403198413041d05a074410b9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 548547544 1250 548546294 548546329
    0x30c1d271506040c090e04030c03180305160503122205040612061107020901060e0d21080912040b28090314010e06193c0513120e 57
    0x14000c006a80c80e0900c1200c02086281c101744107814100007024022a00c02040117060144c4c0d1803d034018140610400740058900d42000083c103516481d107a41c41e001a1600c1820103090400080b5992402240e600c4606074691040d40c103122210424507901d0480034078485c140c20b05081c1c086050b031901e0141001410701c512010301903007142c1c82c1000440780070b4015000611b1091007080010b0342c0c1c010700d05044604519000c990a486140004c000003040400140301e0303102c6456003251b00c216820360f900700c84080c0d1214042513581002d000d8495214000030940361504000c14000c0e542600c0250000010401e050105036941114074a54115000c03024008075480443c100204405801c0c10310520034090000d0200040307411065607a1030015104030910485410445208a0701e5480440900c01c000c10f00c420030f1528043c8210800844002101c4203940e0040540240e0720381d000c4c007801500c80d104a070540c07403496140c003e951005088803e04014441307181c2c48407039a0700e84071506440301c0e1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 548548794 1250 548547544 548547583
    0x20607030f14070209010504050c0c060106020705130509060402060a0216060503151e090903090411030702010e1c050a110a051f06030206030105240a09030c1d27 71
    0x1103014045007030b00310144001850402030100162203001c64a1704491080d9004110380d140d0301141150350049001c40103051080500014085600082000c03c41c1d8040d95100007003a2a5040201a51421901801243e0191000c2801810080018000c4900314419034056008840403912410b0083d400100004e0001c03080c40b00940c10070483d508540f0007180c003603100420b00101c1c886544000d890045c451415040001c500741c406200315644400c000f00100454034628000884681042d10744400561070322064498603d8000349042d1344003485503240c0349606140404607a55400300c00c8035001c02421862101105400f00000001540300b44041e0401d031a481310682400c2e00c8402c2542405802c020003040941c0761070303040301c2c1560015900001010310b14504091004500640d008201100040ca401907903846591803041e60300c501603040d80e06943d04900380d014001801000203034540c0074003080ea00351000400c243c81d645e03d884106560190b10415070700b006092071000f215103a2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 548550044 1250 548548794 548548817
    0x3180609060108061810050405010f06030f0b0a050c16020102011404050a1b12140f03040e0103062d020c0a0c0b0d05010512070e0c0702130f0c030e0613020a0302060703 74
    0x301303004040e031080e40c84501d0450f80644130710195550020a0003501039658440204040c0f0100b9080b4420807000d01d2000e1284903900c0c0750160034455400e406444d03007a07500c030100340c54507244d0044500645040c0748c03141c10042d0400106142d141540d500b00c0c19907580d81c0c0002082408003c80e10310642c0500090202c851035804c205d056210110104d2040c0140800e0500c001c00b00714032600b021a402149003040445100d04080c9800d003184aa00e0007880007190025403080590280f070305803849010140b01600c07500c80800d0640c03d1420000c14010340d00030802031112107a0703028040c60041402256502c1354581c0b070749100301110350880400d4000000d4840200400e9002c0c0d140144400d50307071b4540307a610003613520707488950710b01602501185610118800080ac00180c170f8443d500100208240dc00240f1090006c0010010490055040c003030480d00d010302030b01c14901c100b4042e10150231540c0d141042c110035041e111000b282d0001b140303d00800940c440d80003411003203200340c50340382c2c4d07214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 548551294 1250 548550044 548550059
    0x20a200d0f0210030c1e03090b090d020f0105060f060d09021f1107030816050f1009121b02040b0d0503030f0106030e03031006050a0509030d0e150f040b031806090601 73
    0x24001103c840c141824140ba800806a00c801a0260014000e40a100c00c0032004c604a014001060f80504071001c40814080140b03000300303000c4a9403035560200d40d903403000c201103e402d8880071626680c0c422032689000c14582400c1d002094030000501001640440d698002082403200802600e0f002001a0201c40c895411030a009044404080101201490340d07070341d0031041c440d046605201d001e5080c000020410100700c00600c603059102920941c5804008040007002c40d000700347d402c00000c0c0c0c0b04404c89405a41c1109130740da0650748541d480e116680901c0060841c1007607064002d100c01342d054011950500145020740903e02d03050020b9490010000c0175644442d050005940041003445041c0d064881c02034129000c03401c015446030740501058660b80102140581c041c011509204141076000c100c40d8592081280c408124480c0c202c100e0810303010340704c010b00030781d5010041400700d05c4d900d4029640c00a00c094013a00700e20100480c1354108881a9000d000c242e00c891b00600c40340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 548552544 1250 548551294 548551309
    0x6010501080a02160f0206130303120c051c0b121204030b0601030b18100f0b0733090602220f060201090b060d30030e07030201020a200d0f02 62
    0xe580282c007503040c200101903241500c2c0900f40d005205481082c2030200f1500e0312800d480e0700072007030356400c0300300f039501d0601800400109a080140500e01b40b42880c055028101360f07030642c031000c0d13075000000440c40c0c0d807032009100560b0301c00e0380b00d85005044104044200714650070514542451a155841d528044030284406002c2e1414582449500740850b2240b40d94801100f03111900380301e440c0c50f0103164200e40d0060740c0001d10030208101000c9100b2510b9002864214031684002001c4c01d607055800349001a0078154142d82e483d10340c0a00072070b040070b0b00102c2810703000e000014940300000300c1a01580c00200741d401703405070b0425010010044803080b003400500085c0028454080030b9a64580700500044ca0180f2800c81030216405110b48120300c000201aa5400a140505c0f000c0b000c46102402d02d4401001074140b02038800f11802c04a003002c222a81a0024110b418466a071030204a0014034035842c5c408600c20b1599155450001e404d070003e00944108103420420300510455 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 548553794 1250 548552544 548552551
    0x30a0204051203160f06020403020603043905040f02040506040303030b10030c17040302011d070f21081b030f0403030914090a050612030c010605030d08040b0105041805010e0601050108 81
    0x60f0700248035100090b8480300881803041e80c013402190001e030103442d200e00213010320741019412000c003200304400c00100d0b03000306480050f0048800204881c64211003c50021340800c0d46400c41a201b0030409410150016030710003640103400b508181d100c0d00416802c1d041030f401540001d03120201c2c01407070304000580c05902001032400344103900b404a4041d140300e00501300320310540300c0c030130018091620070b5101e050104100318164001080d480c0c5125510040b40c020074000c11401e090004e0400741c01205401c03030000d4845004014a01c03038549079900d070081c01109910042644544402040500052060004c020300e040d071a1421401e006007110a182c12030b415850806110390100ea076044205031f400700100101203503036a2002c012410314200c2c040804040e200118011040d81419040301e0140e6000b58121210b9203e4900c1c00c58402400b0344003e000c00710107000601890404d504403003c0d901807940d07444c0e00000b0301c0d03880c03d00b11054121038a42d00d0b04510014441c039a03100800642 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 548555044 1250 548553794 548553829
    0xb040212030a1d01050f18030c0103021c2c0a031b030c060b040213031a060d0f14030906030f09010606090b16060b1002060117070e07080403030908030a020405 70
    0x180440c04001901ea0a40f80c000045800d000062aa0007a0300c2002110000000c40078035540307800c286141c00342826446034806109005828440700d10303520920994458038000448100740b0395640c111440104040812405040e075101c1c80c1d142883c0d8012100c091a45003a8014040c07401542802003041c0c52081f84103000c03c6080350001d0110f40c1c400b00c015205a0071035400030703500f0300c4600000d00030b115850403800c40310050400041402506628035800c2c0741d0b252128038140e558007080003031030990700500903c4d10303100c0c9260201195041039a1440d841041d421289028141e0380000e007281c008075030290b44540800c041100229007170040000408407414059803107810044100c5050090781001941450418004c03810301000f904040020500079010b02c00c0c0300e000910094030b1343c00c00d000c0c520300000705003103924100c1400156172084404075003a28038180c480305002c81c1c03045009442541007580b0b401c1840046a011001503010700c098020040e03440d4a481306002c416415183e1b07640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 548556294 1250 548555044 548555047
    0x405010303080406230a1a040b01092913050f030a080d020d0204090e0c0123120406021207081006080c030609100308070605010f080f0d26040b04021203 67
    0x100207508040415007040d400940420110303800031017002d80080403c84080b41d4121081400f1281d403540e441490810440c401003545842c1c018140420380d400d9454079400100d41400c03c0003400d5841d841010028a009181e0a56204020001649800c00070802070802c0301c2c14401c00c11031500c1ca050001c5e004003940640101c0d2080c0e01c2d805031f640a80c10402002e55000519500c0d9034090b681100c004d032940e00e004004c131045840e074441d920640c0d090b24074003258a90801800c0020880f50503c000c01d500c90001d0324041041c03100c1c8a840310b0180c03046448640138480c0b01038030600041014400e00c240d9035440c120f442c1014060301c0c0303500e0380da00c101e0038855400144030351003140104a991000301901c1c91307031441d00da181c00e18600c01181c1d40090715040011444004001860b0002d034121a004100b0904698440259039203c203480020210b2030380c405105035501500400c064500304200b800038644000c221300c000014440100d030101c0342107680c90300708421460810700d5854128881002036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 548557544 1250 548556294 548556299
    0x12102130203062b0516121502250b011211151218010b0609030307021905030d080405330402060d2c03091c110604180506040501 57
    0x1650161012100c410040d00080000c055440301c60800d0107015404006195180c4542e41c0148402010343d000c0312079001c0c042880003c07040260304002590000c039010181f02605039100c1c2100c500d00c107a207110194003032000000500000e041440001e9260100b24584081490031181c102016088804121724007054080410100c0803170424081e010388040c601c032110700c0c3e00a1001e0041c4260f0280320740359007040040901f0001e00c13000d229140c6400a2006141c09402c02406014403120705805500070301164000d2301d0110803049041c0304001050f6080364031030000c0381c00d181d142c41522001c1101c43e010322003000002c105c03c0e2000310300f1016100203160001c070b4081083c42e51505142086c04440c005c14259038034501103d481500b035804c10490f800f509000452400c2c0305000071100072030042d428443d884000300c102c9450700402001511204030101d60032000011054098504614102c140c2c0825155440240301074074090940c0032140c00d01244810981e40004e08031401142081c004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 548558794 1250 548557544 548557549
    0x7061b09060e0d0c0305190605070203070305030a05130501020a0203090a0e0121080c16050918030f0f0c120912010e0a060903020c041b0f080121020607120503012102 73
    0x103505800002c0b10304404211072420700c84c01d48002504050308501130000b07030750030264506a1842040307101d01e1080c4015038841c1e81c180e07100e0003107400140100d030b41080000c848508640c041a4003030407041e52016001501d0f1119800c980107144881d02607032001440968a00e08048104020031401e1030400456040a400c4140b4034001e80c480100c0303504080c101c00c1007014400a5686014002d02152040a0b624107107081900d031505c540740c0110007403170206030350401d692501000c506241005624100ca00000c206041e84041e07043c41c03a600c000d00c10f24041c66000e0003100c00c1c1e040c44900701d81c0c50740100000c0015100c07407000d0910b1140c1c98404800003007000800c5003400150031500001d03948002d81400c0e030502d8103182c50f0760352040c50099480d0b00e0748441c8842d4a0310008a540305481e1030030400c019903c802c002c0c000d1800011186000600f044500c10b51003007005e101412030f506011a903030b64003001c000c1030079000c00401da0100042c81101e80d1101000c40700c1440050b22000b030300c000d801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 548560044 1250 548558794 548558807
    0x3020307091406160215070807030908010c0806010e01120e060105281e1d01090509030a1706271906060e1201060807080c09130804061206090207061b0906 68
    0x701541e240c00040c0131142035598048205060f942c2e5503d1595441c40c00c0e01c0d1014007035002c5401107000c10110403000c6040c04051059000c5035050b511940035644400e80191544140384118904000590040000807041805920b40812060303001b01201d504110030058424118400d0300180c00e510241020040d00e8002a4801c4030014220180081005425400a203500b50450b01c6910f8000010701c040f40c20b0544605c0c103c41482c0b408124549a2400b000d07201e200d908920400503400003004801203590134022500845d000300001201c004840b0700d02c20800300803458013041600365080000c11191080c9844800503801c2e800c00c80d103030608101900111040d5110703409000081030040510509600034405800c2180440b851b45076140000c517035500078a10443e005000140100d440111100c500c20b0703110f94455481030429040c080f0441344591420805004a0348481c4009031040d03851000308038580c0a80404605041100555186003083d00492003c10024000801c4010361214 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 548561151 1107 548560044 548560057
    0x3050106080c1b010207060e0a0302071e0603021614071404050906160210140a150b09040b010e03160806070813060b040e0d03020307091406 62
    0x40080310a0344054400c01d40c42c181c240550b81e402102481101c1070042008001410003001e51240401c1e00c3d42840d0010254020018440a040d03050240e1400b500c5540d500e40c2e0003806100501346030740581d00c0341408040e804211f4001c9030507040c4111203031940044c014200400e1000549458405905c140c40f50311080151014150405000e41480f503940000034010a5a818840800d058103c8044104600404002102081c094860806401c501015054884c40c10303507960000c0380c004c010540e420058802e000c0081c560540c085480313203841a207009c12281484001a904102d1048401e40c0c035004a11002c801801000581c90807514660200ca103552241c04054400100035a21817580a200c4d410600125500d030f00102c00d4100c2c003030300000e68005d034400740c01e003010181c0c218030001903000800e20200c20791111010010705179a0902000008102c00091041d01c40d19 = true := by decide +kernel

theorem cover : BRFrame.Cov 548381294 548561151 := by
  have h0 := BRFrame.cov_init 548381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 548381294 ≤ n) (h2 : n < 548561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
