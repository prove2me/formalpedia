-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3631
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:13:31.789584+00:00
-- url     : https://prove2.me/submissions/9d66d302-bc4d-4b08-be20-36b4952dd766

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 652877697 ≤ n < 653057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 652878947 1250 652877697 652877699
    0x5190903080a03022115100207090f0204090e01090f0b04050a170903010b0a0b09060d02040902120411010804120813050303070e03070f05153a0f0b0616030207 70
    0x700c08280c1c001d07009420010f640411000f034000d1380900300a58228200c4c02c0b83c20f01e450030800300702901c200da02e06d0600501c090b010340c100b114002c01c540700103020680e106002400c20748440200030341141c07041c401d14a041c4001d07460904410700c103800505800c604042040d40c101d403075070942c2c0e64002e80300b01c80f00d110b035280480214016903501d0402c43d000e40900c0340d889020008150075500d08003070b6503104124000c2e003008903501d50001c40d810140c051360101c0c5c440c40c21684140003030045600020806000007088403000d800d045444d80724030311600d0f44038078034080b240046442e1001260010810180b07901c0c0f524525000d4260f80d0380c44a507050020115054aa41c0d190440c2c01c00e9030401e0210b00e6954040030245014084100a404a40d0100c0320040c94400003a00c0c0305003861007068007480001c1d000b054142e80701050542c000e9484200d0121030b111500200e8000609030198441e14900f92030044640f08a00843d214840000d10390340c1045002d60309001da0701a80300003107080d84102d480c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 652880197 1250 652878947 652878953
    0x6030c14132702030a020c0d020609031c1b020a1502031603050402270108070503060c0307030209010c06020f0913020a0c022b053f0d02070f150f0c05190903 69
    0x85109110445001d40ca90101f0f02c003161400510032600b40c15034003c0c004105030b900c00003080d01c0b040711102e601c811400382c5540e9068000c1040325200d5004554481d00300c1101c0c4d40000381d8076441c501c100707080010a900c0c00010300403408155030f08110002410480350802c1d1180c0c002641040c0014911002601c01407980d90350700b107003802e400c003007840c240f03004100980c0144440c900801080d0041d10303040c03030001d5024030640310050000041c11340c04651520964420240408a541d00c2141155565004032886400fa08491341991291016403d0200701c21114000c2d283c100101747c8600c2c035841099400c100102c80b0352101c164041c10030b000c0d034030f024030448400171103000d000d84094a0b0141c002580d010f14001c40340c613a9014002c41c00540d000504058880d14071221640700311513181c600d0b0041c1c0ea0045e124402e000343c1940c00300b207206030612140900c401d0030040003002c100180314800404800b40c5035900001e10206400f400003425034181045104068240751030075407030160301d9075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 652881447 1250 652880197 652880201
    0x40f02010804030527010f020d080112170c03120109020a0c0b071404121101080601090b1e030c030601020d08010b0d1d151503121b1606030c141327 65
    0x5000302c500241c10714000c181950300907547c1011265103102400d091094a240a4030345e000604c11100d11103240000f8009101e4034860901350b003104003100560b1585122450b0344d80b900480300c2d2420481d44200006100c0c5103074800c4034800380130368440900d90450b0707403900950203c00800030402e0106031070070400c881000800400c0a0022494010b269002c18144500e900d000849403d040c03007001c1c07091044c1daa0304003645600705e900f25001591b0b100702480144402c84070000b1115244a408000c0c4186041c010001e18803c100c223a0031202003581107181110039031020b200b442c4000c03000304440c0b0f4455419405c050b000c1080280141544501e510701c6501d0580c0076500c0f244480680c13800d10404640001c02402091411002450031004049a54049114140040c0e082403407454080c45051070038010b40300c04c0d06c0c01e114820f074041c1d566040500609804203120001504034419950012058000c5d0b900c414a80c4c2d0489031181d051590840c1c05940d02341e061058800e07c04890340308510070b8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 652882697 1250 652881447 652881487
    0x20a0303121e0c1404050901120311030a090305060f0103031d030c030d030518010b010210230906090f0111030403050f04030606140901320f0307090203150603040f020108040305 78
    0x10ba800003880c0211050300420076140854a410281010041041955517000050741136400c0545c400041040742d1a0645001c131340071a460000380008a0780800c0349401c0f02410341228000c4d82a40d6143d9509030200440282c01d0100070003107550301d922183c408000c00c0c6958808400903044850401c45c41d000680b510325500da0207000a91605c04100c038112802c0c0d03420381030f884030354001d0001d00e02080010391141812107480702c40a03a110040a0000346440c1c40c90420744c6505020350150401841c1541c854004035201c507518070402da035101140d03405105c0c1c03100c803d40030145241942c5450303600b1500c0f036103c02040b9108400500c004000b16045c1e106400090039200002030041840c50248180f02c00140d00032805d08120084030114040c1d440d5942089001c1180044044143c81000030103920000f4101601489001d8010420582690096000d500d0012401c11074200030401c0020510017240c0061002c1c03a402443d100550107a2a41074009101c0d00f005800e2040c0003038141401050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 652883947 1250 652882697 652882751
    0x5030c0106080c10080112060b0904060c0e06090a0302060c0f1b010e0108071b050f0f0c130b28090207150501050604140d060e010e061e04020a030312 66
    0x500d180c00c00c02000b040040c81c508010540346110950b2011030003400000307052007280513030005240100d00300161a03001941c0032000a0400d950360a00d420020b00501003411550042603ca840e400d1851070031600755070103402c0c020300102481d0308550a00580c8e80040800c070701c1500c01c0326544000800248011503e58000320308100c11004840d0005010002240400341401043c0050140065020100740d0325481c07a4025845421000d15007a4500f290b40c1c1440c44160180070f1203412003407004900c51440a60403212011500c104d0b040d242e00701c912200302d5507407020510414036010801d40c0f4000c4150184100054240340d500d1074400b00341e80c8800e104607829142c071880740000c070440748151409004169202405d0900300000400c80d4a40400468481c40000242c10100203140c2c001826004581d4000d0140301a032150b101c1c1e450000341d070700300d959800740d05904181c013650142642c8204e40052603d081c1700c0c6542c07401e4070340800240641c0c0e59a40c642100075103400d00c54041601c1e1440c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 652885197 1250 652883947 652883951
    0x3010204031a16051603140301090b130204080d0f020a020901060f1d090a021606020a0804050717030901050c0c0a15030f021809062205060a060305060102250305030c01 74
    0x8564018080c0c410720003804150349200c0da0046103c1ca503804000d03070362171258084000340c81504a050944103102c0d90721011000d640004000306885a00ba085003801c514280c8004140101c60b04000c400e078007480c015115260f00126050790160b2003286a028130f10764a006480141d1129004291010400d81102021424904180c0d114691085204200e1910604d04424540f07030a40065000c64000c1c103002c403480d4001c070f1084d41c40203042d0040c0e62000d0303001c80115030764440c40d440940310810445040d070f1503001e04000062032014800007480b80c800804095441c040c0180015030380d5800c4045042c58038820110038884945410120780003800044074846503c00c0a4140101500e6008600240c180c0c0140074840000510f441a004100001c035918403180e50f42a010807041c05807078041c59440c41420421882e03003101a0310441c010241654000076aa895403c1502503138000e881460050340141e010100c808040c4d010190919518041c040c0307110340e00c2c0c5607540f031904101e0580e80165 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 652886447 1250 652885197 652885223
    0xc030228091814090316121701090b010e0d0309050108180d122706230a02040509100e19020405040f0e07080c010804060b06160302030c0d03290f0301020403 69
    0x48204020f564485a00c01c01185060141c3d0107070558125103072002080a004041040809801450104000a80403403a417000750780d02c02880d0081e0140001040c08211600704007a454140b988500c6411034150f11000b900602c1c20380119913950000700021100030401c842200311182c10310244801c220159a8249200505822a0111010f4050304040c02c00b0342c204107039540307000e140515180d0f07411420020700200f001d501308888000c840c20074044519060200032030070f4076a0303004c0d1042c1c1e80140c41c3d43e0302d82d5680031205001003195009075044215141c00040500440c41100c1840086154000d410b19648002041c1503402c201207105940762038aa9060803071804100050050904100400c3c01e0005400040e2495201400c00b805407070311528a079026480d42e8080324600c050043c403010b0750400380d003030003512074000d4012460140501c9840001e0342e0b101c2c0c001d8150441c0e4154140480000c00f03085503003021040020150403e50104002445940c00e2001d04019405500019484 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 652887697 1250 652886447 652886471
    0x70e03070314031e0301210203032109010c090b0d0c030b100e03060606030c03070f0311070f05010e070b04090207030315030c05030601060c05060601030b1201060314010c0302280918 80
    0x1507080e544c4c0119450000e000400040c44007281c140e202080030444c000414205001007411846400c41c0600300c400c3c0c008082aa545c1c0388008588102d204c600200405540404105d0301c000b60343c414100700c074805100c50080c40e42240d011119803a081c4c103000414184950210b440703000c078908010080b450403030502e44681400d00c18a54040b10480b9280d03c0d44c644219036514070302020388640d040020321781e0800e061500903800b4400b40498980c400c1c4c1c840c01940707424910444800b400304ca0319400e00c1c0c00f01807102c00016501040e40d052121035070800e0f0510755000b0094000a00503410940c070b420001c400311600342c1514020b58061309450704202d0420040c1468540180d0007075040060079008140450004202d11350020303002d20380401d0110b6140c5c0015001e20319112401c125520340701000040000d90031140f265284448000e1103181c6861030260200d00540b000c14280300e150f41031000c01c5602c601400b03003000105040507600303075032280c540050444402c0c1c000c1360f01580c1c0300d00004403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 652888947 1250 652887697 652887727
    0x30e060109060518041509050f0a0807060b01030e060a020a140408240106050304021903060e0105040b010b070b01030809041803030f06050d1a190c020c0f090f070e0307031403 77
    0x30200c40c060009003865902e148a80104c000c070031b806c903070f5980039103402c1260912484c00d441e01e10308212250340f201c40c1000c2070b450303004d9071048818902e400107038603055019001c5e03d403845c90004041c142644d6401e1100740a50302c400744420410044c000d242800035122409072014110400003400210000d007010b4900140e0007888002890121004000045c0c1c0601282d0b8080c0d81903565907841908556030200030507850700000c2c42c507804c01400c070540c860158405403040b8020300c03403901c250766614490b04483c45003120140c281110ba90041c004035680800610f0b03800300240c00010055521980c0c2d4500c451241c1084001985402c40448150b41c14022080502000c803070107480c00c20b840e03650b07441190300024620540c1207c04001410741c0b40c030301448401c1800100090040002d071a40c000d40701e44081020600c40c0b42d1000c007100700b0b400c045800c0c030700c11a58001c11000c2501d0b61141176a0b034071501c0d140150300d4400c4003c0800040c031820401c09000c00c100006686840c40c0701a1101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 652890197 1250 652888947 652888969
    0x301080f030319020f0d020301090203040b0f0105030d0c022106041727011206080c0306011d01030314090a090b1c030e060f0d060305070302010f0f020715030e0601090605 75
    0x14154420720510032500b548918090007500f440100590399103501005000c03074040c601d10386d842c1d44d10100001400c09101e0700194401e5206884c2641c466554100f5011400390038007405401d5400380312005841c80c014850f002000b03000070304030081000186413419011843d503040c00341c0e030341013501407000b01b000000a9000907a4419122418410030145a6000e10210a00b000042e5804020064107074000e80015180d241c00c40001d000868582e411140d4403c0d81d400e0141c000d120707000000510807500c50a4050300190503c0a004503443e6840031125060410098060384804001d01502940c0d6405040003c04c00301c00c022510b034100100f040481200141c3d0344800000944d01440020790107400701c1311010017102c841c0c4d00e514000b0b200355428000c0e4407000300064038214001c414440c0000b50354089078401d0380e5404410301d070158221441c075170050615003d64042c500c01d1100c4180c00120b05607030942450300007125000080c0e81442e00d002a0f000d1860580d90752002d000905040c40c00e00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 652891447 1250 652890197 652890223
    0x1121403220e01143d0e24130e0717060102030c07090e0c040908120709120f060209091501080912030a05150909010b090f06011e020309040908030108 66
    0xca01d42c5040c0343c03100c44c0101e00b04841e204035415800e454180c410350703141245c0a41042544110103c001c69240c2401e96418510800301718000b031480d4192400b6403c0084040b1610005440c80300f000807801c0d101d4000140c40100e80e00056804505031841900307091281c25107956820044800d111102400f000c00b81000341150820080110800c00010300482103800f01d91000034002806100681851501030002d0b07401400d00703c3e014144018007000c0d0070031070401500074085496900c415a906040c0303200d02681905d4030342c4040082007895880c0c1c01190300811001d464070414000080c40c40c4404c648148080e211205013180d03d591040d25075030304c800004000c1403054030807140115203003c01007080e00707002c7d11000058052600f5003a403c0203068050403520142c2441c5030315501038003000c98100d000710004000213540e000c11142c818051001030312004c0b41a40d560814107810f848003100941544000c100032040360b00e491182c16000d60244100540381e5041c603642d40c1c18500500c081c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 652892697 1250 652891447 652891469
    0xc020a0501110a0210090b0a08011806050d0f06090b0a0221070c14032101090e0703021f030e0d020d180303021f0608060c04080f07030b0112140322 65
    0x140ba074450001040d28103907804640160314071600c00003ca40004aa0b00400b0342c1030300c0440c076010256004601c07241a01d45200c218201c11040f0206107040710084d119496104c1152080f0320007082c00b012a00c07110500078400811402480d8686a80c102c1d03081c1ca1090050f6800551208800c0017401003030b41d04048072141221500305804028064404124060550510055100c40c0c840701002210142210a880c008609080b0411841b000c00c00b4402c02907024200040c0350801800403d03001e0070303294010150700c1084118000d6206240751200c0390414140d6541400112103130401c600000e04003140c1c014586c103e40c000d07009001c5c80340c9148905009503855001c0c03001a8002ca03401c08440e98940100140124201c409009428150f10003001801010188a044001400184152030b07a0782c040311a190160040550b60342211712025140c040c24800502100d00002d0620096600880110407240c2207110780900715440700d90a00c4450316412039040c00d0140030700e08040140040000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 652893947 1250 652892697 652892717
    0xb0a0e030118150b010c17121302010906080901022a070f03020d02040504240903110d09060509040209060c07030605090703031d36360a120c020a0501 66
    0x207800091200d0422074180c0607103d801c12882a4860b0011b2004aa0047d0090030116481c00c1c4881140d84071002c0080c10700382c240e000805100c10b0540d8445002d80c10b0b5110910b151500d4000c60b11208083c005c440955020014024550440c4400c08503480e4003c140b40d404441815003981743c0801d6500c1002c0301e00c002402040982d0340c0c03922007201d040c5c05680226050340d40e4034125034039411000035517000800c00d0034941881074541c0d120100d50343c440d4540601000120b80c016aa40b81d081e40c0c007000080c0c03500001d220491048000e0031000001034009801c03c6152070005207a6004500c507034529a0122608005110140c01040e40114900d0040c02065040d510021b20070141e1010001d055404412010802d48034640f41a5014074a1a07024210040081d43c49843d1080160020002c8039401d0100720508003054028001e01044050340c110140900100c000001030054408414082d528161010602164192141c1841c41d03075010182d800602c10000500c5241c0c04c020304014441c81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 652895197 1250 652893947 652893953
    0x30a03051012150c1404080303040521180a0504020408060a0501050402070f0f1b0b070b06040203010503210c0d0507140309101805120d02011a09040b0703060b0a0e030118 75
    0x1d07581c603080b559000c0101344280f8912095a4084007160203070b42c40780c40003400049045011000d0360066100d141503440c0d50030000548041c1d8000c11445004480d41041000421594503d9036042d14102410515019070b45030b001804a0304550305c8403a080c1c000d0820044070155521a05024010841d400c501700003090300c51070b02c403000102d00104550136403a0968140501e2505100d80814024031031202031380c40c0e00c004022a001400129400541c0c04040ba1851805000340d07410303501d003c5d0084c11920a1421080e01710140300591504004007008980346005041c400303001c0240c0c3c5a2211581c1d05a58a085850020081e8030b44440380c10901c1005826a100d1181d20074192079031a040d4000f1100c2581040c000b00030340e01c2107501000003400900313504808a40c0b0180909150001c100c50709a0421116030045450240d5a010910800003000a170000b103486411980310b190000f5099115050401d650f4410070740380000c5014035801c407026140034001c44064450048a101c85001d941c0c0e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 652896447 1250 652895197 652895213
    0x6030a080a1b0618060b04060803090609130513020307060206011d0901020c101a0402031009090c09060803031006020c10050a020a17070c060809191103030a03051012 73
    0x4841c0c102000110400e8015107a185504125520780128080001006510030801009001002150310504052544c110b61030140b20f240121001e01d00650300c3c00c1400c0003040b0403a8400c666aa5224000d80d14900b2202018440c0794490407080350100381c1c3e091207004246c40d25030345a010300704650005d0014088041d4012040040e0b10680036120040d4461502d002e000e8001c24036900c1c00d84c0310350022008801c15642081e500c91502046d4a004d14000750188003d1380b02c01c94140c007e000070001d0800c100c0e002d40d400380c1070441c0941e01003d8070303d46503d0700c401501c0d940e6000500960000c42441025044a0544802850035000526140d040d03a40440c0c0000c045000280a01070045003808516000340030008440c0d81c45101c91090000c400c02c0344405400c454402c0e564068201c0300461694000c11075540590f03001801004e4041911030558100820004122107110410742c071072600e614108050000310391030752400b044500d08002e401c030703015202d41c1c0428400ca16110b001c03400301d00d0350 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 652897697 1250 652896447 652896457
    0x60f05121908090d21050906030408070602070b04060c120c020c090406150b13050d0209040b0a230a0b0a0f03061a03070b0d0507030213090b12010c1706030a08 70
    0x90008208098007402d14910038000e00388160781004040c03030700b2001c1012160b11201907600a8900b80c1d440720340810115401d004003c1102d800040401c0410041103010000e00041032203184051719001c0c05076a074107100c0100365402c440d840c0d240c82c00c0c0c940712a0800100c403154645c040d01045810500d100080d40e07846014546409481000c01083c20701455800200741c001c9a0218070380d00c0b0303a690000d0f1800c0d510521004140402d4454082005e00e01150703d10340d100d0b001000203000da22192074120342c50710040c203640b116581d100254503140401011000f0000d18048002e10189002d1050f0b0040d9001c989140303106d4076000100b8007038002c00e22a00c034162500102c0006050390b82541c0588401600d0303034120340c03511030200b0010b84210ba100090a80d400e00001c14801b54880800c1502030b40902980003074645110721081c04055400d920a54594400a12207281c0342e800b0030131642141c0002c4140c1001449511046035a000f0b200300a0750002e40580081180d82505d80307402c0a18054 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 652898947 1250 652897697 652897723
    0x411091b180a140a0503030310150c0501050c1206030705060a030c0c200109140a0302011d040f06090c171f152102130b090402130801060f0512 63
    0x70030020305030100d40141c1103800c03002501c1c01e1034190722690084079802d40e080c0900d10480103a030300030074141408010317240240075100900d980e090070210081e4040101410010403c0b0f45080c4100100e402402254040d01344e5081d0965030f4165280000404030000340f005009500003a8204141d446000803100000c0d000d00d000150391024001c02c03543c202c550203014050b02c11280644408003180e0f540c159407090241c0301d0003980c80d0755044446185a0000000d80e005504400400255003d4080c0003400e00e440410388040e030034040000303001c40d4114070352060602e5039007800b070100c03091505c905212080f8030300b8800540506452900c0071054000e100d1f00c01000022a40000384048114990103001c0d00a0f1401c1c400064402c01001200390320040c89020748004601d40d0200d280d4421582c3c00b80101d03c01c0c10b8290700300300040300a0f50100c1c24039508107a00300058140c0e003c1100103000900b0b1a400003003405481c0c0304640341d4101c100d4226a01c0341c50a039084040001e8001401e81d40100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 652900197 1250 652898947 652899001
    0x10803070b06010e0a08070f051008010602210708190e0d350301120b07170a0e1f09020a150c0f020a03080d0c140c03180d0804030506041109 62
    0x8408945c142c1895809120240f240300300105038409144400c10544206550740660022030740c0301103520704420302c10368000d42c00c00c0a900d088c1009c44003004241000907144945090929919122241e02c028800d05a0100c40d103d801d0b4115445107102c1c400305d008448281c90b241e0991192181016414490f2020800b00d414980740c1494034262120003040c110300c0e20380c50390b0355601100c0264003400341c11140d4802050004002d00e00a050580b010541030414118665405c20882d00030070b4a144580c0e100d2280c4020290703000e200c58170700700c180e003084500800d00765028030501c00b242e407494000801c0507801004030300c1c03416448015281c1040e041015141d0149113400810304401060b000984154400140c640610b0784039040103182e0000f594951840590b07030515100700b8003c1039040500c542041006010f5502d00301d044101d03050005141009074169503407001c0380c507806a1b208540c81c0e0050400c2000344101c0c0b40e070100f402e00d026070b403400744d61400300302c0c0b1310f240e441e040d00c801c00c0b0721 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 652901447 1250 652900197 652900217
    0x90902180f0d0b0c040f1d013c0f08030a050a0f0e0a0b070209061e060a0314090601060f1d0904030203071401020c01061410030b06072405010803070b0601 68
    0x154607800190021608110381c410541060031000e84d00764800e005080c0d80400c101000181d40ca003a4108114040c6410812140b6074280b50150300300b215403044180c0700c000402c0c0f0300f0b103000c0203100e03481e0454003003107110a0342d09146c08041c0a84600c1503001c4091508103000256038940c2140846041025500c3d000340030b8007110300150350010800b081c0c1c94008450303081c04110051940020080f03140200c3d0510102c1e540d40f01000030311224460445e00800100102c40b4650900802800740043e02e0b0170302242038042010500d000000855407191240c3c0661b004000298210548000224880c94904104501c1c1030417400321202c10010140500c61600010341494400d00555581907070104503035024407841030455000c7d40000300f40440b254a0203000080c8104440c03880d22901d080644148190100440c0640081c8403503441960001e00402c0100c1c00104030308031040904098212540e0b01e44071420030b4000b1500c050708500361681c001c00488000c240882074640d4015800d00c2d05202034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 652902697 1250 652901447 652901449
    0x40302030604081c0203160314090a0803130501090609110a030b01120804090c020c010207090b01080406270803041b0503100c030b041107060506011701090c032703090902180f 77
    0x302201303065100c858804001d20101c000703048507442448030299400d0000340240c1c00e0039001c032003060f1400282603200b2400c4800090032030b0061a03006840c400082264400c6803a02030940300d602c9005c54005070790310542400c0006214080002c20300c240c40002c01c036030440d95546000c04040c010391203c2e40b00c800c04e880421031504103c41c00340032100f6050040c41c22181001e50b4501d25802d4050150181c0e844c04558403956105500200c00140e40b580e280d44c031244c95890050000141606544510044444c468041b080500707140c18441d041c8240d0301e1074241003131070780f03501c6482813a80d80c003c07550301c2080fa1b0f6400258a102c0d54840d0a07000900400e500340603401800103080807904135042c1320310072501e0707003922001d0840580100307000d01007565141d00444141c030145115550501d140ea006100c82c881d0b652040c0041016800e000510b10280070449403c0407007101e10360485003100c4501002c060b8890340381c00042022a50039820007500e150700e01e02000000c000c19004189004811701b031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 652903947 1250 652902697 652902727
    0x1050a180510080601030e060c070f08091507050f030906090112090209090d020f030a05040312022401031a0c0301061404090606081f0602030906030a0e1c020f0304030203060408 78
    0x81c00014030b00b501000003410060540b400440c2c200c0e012034038106400c1c07002c180110f009403041c4045c8440d0340c076004a940d101ca4008a6840c000e48060b502801083c50a0303c0b550f00d2100201040d500c000d40b244030360b182042c0b4000740100d02c9945a0424800405c40340c5480d000d4804200003424802c4042100c44140b0000b080c503c000131754896495001d1040a10011800041944840c0c1c01c1d51440300000e114641e50b032203250407503030009104210800c0401c0c0b0200c20510a044e1910543e0407a880c02c42e2070303040545545200f03603608038061004004100c0c400c0d511310200740c4020448145840c180d2062012030005104d01d2080c00090010f55020351581c400301e601910040004000e101c0d2100d074020300b044e40c1101c5140c0c4000510b1484907503942c1100c2c2003001c490300e55000b1440d216910781404107941000d0300c0c030610182c860b041c1e05002c3c070b014064030622810342040a6040e00e03041343e0091400c034a8186078001c5030030400c0184003507200454400c1e40b142c0c01c120001d594502e21000340c44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 652905197 1250 652903947 652903949
    0x30604020108090f100e0c0a0e040b04050f0304060203040914070804261204020102070b160816080d0e062a0c0c090711060123220c120e03040501050a18 67
    0x4045c080d4040c0c00a040700c03903a000100541c4500201c940701403500040c801c120310340e0300551183c2140180003c0008003c2c10407958404e03c1070b01500c1305440b404100c1d42c556002504a0000341c0c2010500b4055a4054450404000c1c0707024100c41407030805a00240000e140908081c2400c1000d44018003c1030400f00d140d00850030461241d030344e8102031740392440c00c0c3c0019241280107000314000007136517980500550ba040c00c3e900319007044d090401d40c0d802e00254003200480c580244d010794450040344106000d0660f41d1042c0d02c007c82e40c0c141000050f42851002002c490b2521150b00d44481445080d20000e1030001500500a41d224519203000d880c02c0071303100301698803003442d10402c1641c0740e01000d29000000041c1c00c0b10405d980781d2000082e4034040426025090709000d0302c0022a01d0b10800b91101e40c1c0301d80144041e07850300d03001180241e8409110180210b542e117065045102004d208840d6101e00440165041c1030502000071300d03901c03e0120300020800e94110381203000c0c4802507004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 652906447 1250 652905197 652905223
    0x6191803060605031029040b0603070309050d050c0a06090602070c03051e0c010509040917040f081204052805030714040c0201140c0a1103130f060e03060402010809 72
    0x1159195280340c2400648038034040c01d4040c0c001c99904000468660095074811071000d01200d90030146800703032401c2c031040e201880340d0142d2600c0900785251641001103001d00c4160f81d0216048105061051401e11113080340030401604106004c0c40941c042900c045d0141c0c040800305035000f00303041806c041d02411a000c4d045410b820400400c1000c009658802d07804915601601c100c40000c4158940a80601135400319104000620542c5043e0303128006052043c1c02c01140f0368000c15401d202030704180c0201028078030700182070000000c20008150310826000c049807919082c20041403812204041d0303070704000104c104030212101101280c1020b05009021980c0c090703039460041c141001c228500901961911b040044c8a03403060281c0018a100000e0032110b584407908030340241d52042401808208103548c0c5035002e03403406c1c00101481000308903040100c5090644440180344aa8005018049800740752019900c0c042440c0758001d80909128059650b00014241008540301da40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 652907697 1250 652906447 652906487
    0x50f0c0f0106031406060f04020903030d091103010b0613060503070903140102030717060f0105090d060203180c061314010302040b270d150c020304050901030f120e0619 74
    0xd0900d000c150701840440340585400880c4002aa41480e140c5105031801c0c1d8000518085503c0030742031a40041c41100c030054200e91400304036038035641c11110700e8a4120f5052005c203150741e605203006d018101d000d583c1102e055140403503203440b501d03410540780715500501c20702000140400d4000d000103401103800403141245013240030031042c000e6004039680c40101c1c2800161001d800d10401c0c80342e00c2144050543d24901003050015242604111445e0341d10000c0410184000307103807400918020a242048140d08409079802c0d030341802d661041c09800760b20b0900c901c0c0260541041800210390010085012034078a00004a001c1e01c16a007149402d0480000e48040170a1182e034101880d030f0080400d00c009129103001c100340100100c2d4080c14a00d03510100c0300000c105980085440c0781c950040b280b8060340c51001c9803100c0030036407050300c44039606030404080c03004980420103954606d04d0040d0250310a5070010b00103024522080c002420030b84c0901c42070300d0213040e498150a04103144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 652908947 1250 652907697 652907713
    0x9060e030c0d0816020a0312021c0504050c01020604080a0309020d060221071103180406030b07090914100605091513181802090901020f030106030e0607110607050f0c 73
    0x252580d102c89110700c44000519640010303848400881202d0480602e80c0c0c00f421031200c442d10101d80c0c0805c105000c2c0861a420000c1c992051269240140703a4802c1030800f1070a45040d0400c141003090540009044d03421080c01c0000243c0c4140440b07543d00d00a0400041c01072250001c612540c0c0d9051005010610000d80400c02c8d102c0e2110b68003d5031204d0241c2900c690b04c0a004072688440040c807030605a00501211050180c2c2c60701c011401c0c1409400001d04554a4552000005085d1025004a8019041401000c003107001381400540040092140f40c104044881005089032045004200000c07800c501c003995591260341005801007078468030380462624400022609100d500308400030181c5c9121200094007510409505040d82e07441d5010890b002c0c0a200c2000501002c490355080143d442d80c10b0025028501a2040b03960000d010403002c1c80c0c40f880e00c1c002804817000d11041c501d207040c8030800025925800b008078544183c48401c0780031100071038024111001000c1c010108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 652910197 1250 652908947 652908967
    0x9050424020f1206091302100f18060e0108010b04030c06050901210c0f090f0504050414010612110d0209011502010f05040f0224030a09080c030d0f05060103020c1009060e03 76
    0x400b809540229400300d100d072140e04501406c180068402504031981c0d1440c0300c0400e010302202d96103c003040c01c3c0b01102c2600318039402e4080c8059080840450711220071340155503481800280034003118041c09103044e0a540340e400d030501240c4150810803e0005a1045603441061280e13072101c0c8503469164000e201c2d00d0000c01501c00e1044080000d40c41000c0e40041510500c041002c82c2e0b007043e4400031040c01e1405100c05010001d20a40300c0141600d440303d1103030400d22070702e0010145509000c20301015450b0009a913903d4402c4184a104204110310240ea00e0740c618904549100d4030403405c1882036042a40036050542c4040719007481c00b0200b01c144002407500b51031591007141e840b041c002514104000303c64107003404c1c0d90b03415018000101c1c7d034452075003d510341d24040c20040e803c0c103820740c42040c030703643c480e800400f03800d51245440700f0b010700d00e80516034004000342004c0d400c201d200b0049a58926201c5440c4075035540fa08140300c1444600d6210901d82c104c510266076599014031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 652911447 1250 652910197 652910227
    0x10605040b07061d1e030a0c06090512120601081003080a0e0a0f030503040305060f0f0f0603070f15020d05033304110a180f1e18090b0109050424020f 66
    0x10030901c42c0c131911101c03444581d440c08021620101fa20341c60b0303400402c2e4580c648600411040b0700448040c80b5480580d9406060f0402609050b807006080c3c050511f49100010413109000c0c1002005655403241840040c00000540c0c003280642e140c8620700c07648030400070750150310301d50001681c02140c600210034400080020b10549000d0011641e46485200b00514150000c0300c1c40740d5290014004504d50941c401e040e01c0c1c00400041c1160045034880742e203903000303d040fa44136452240d0040400307010342d42c0500500001c42190b040c41070441ca4070034001000e80565100618160f401880f07501c1115646035074840d02c052010300b08001001d06465500300c2540800c0b0010085110502081c200c0f080110440042d660f111114085007840c00c0042d09c05010088094001d43c200d6043c086294500b42d04801c41080c440c090100d08001682801801c564041e041812017a082030200030100e400c9000b0a00c032565412031024001a407040e82c1c030024001c0c02d40000d10700c00b0000f21054140501c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 652912697 1250 652911447 652911463
    0x1c0902130609151a0f0d0c0903120207060206061201021b06270703030804050102073207051e060c0a2f030d0305071407200108010605040b07061d 64
    0x28034400c0044840d02c420114030743c50648501d002403802051010724031800385010340305000c43c40748040d081106020101c01661400150100000d25109080080c071950440c1305090026500103440c0c01418804000c2d00d50b4002001c0300c0c0241e402904581ea0004250b046586c4083d40310a01c95041c4103070b0003000d0321480c055945041d5440c03111022514000842407041c841303681f907001030901c1c038510703681510640380050050360b55540c00e00291022540303e200d8084030b500b00300448174850305118081202c0d1a05100890075a0303100350424403264548198400322005130010350884046000001016071042e00c0315031300d0034020500c3c0d5008010a203222404104903410000b1001071040c40300b107105e1141a203140e5030541c00702c184c0c032180d60f001e170340701c142c000c0e00521701855044201c040035081d031780c0505001c0341c0188142402d140354018140301340003440d200340f07801c080c03c2d40340c640020554060341c021006544d400042d05002c200c440c1d40050b00c21030001001fa50404544c180c015110113070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 652913947 1250 652912697 652912709
    0x807060b01020f1c0804060b060d050a0c09050108151f080604180b0f040c0b0c0309090f0402032a100309050d051c0e0a170310050a03081c09021306 65
    0x190140c54001d00c0350200b520031413a080b42c40d10724000c0000d443c0c00c850ba60360141c02540c4c081e90fa03100c919040d4403500b0003440340e070406120214450601c030b005801210240810001040100307442444181e03400404030f9044459204880e08040d0008000780c60b941e04c0c5666a03584140089000603555007109060b48600811a820001d01c200e2a0a03280000b15031100100b17030b8030408c400140702d00c111110340c6030458011039070700503215140c4414800c564841001d020042d0f201160220300780c9881000e00d6400303400008500c109060950100390341e12024410a940300340f20142c0c1e40085007606038801e031480001000c6004c19402c001015005201d451004d541d80c0c090340410f024135600840c121401c284c03408400011400060304c840000b030038450780000090140e0303520003010800c055180712001464201c8503540c0e00303004401240b02c0c2480e43c0810b000d01d240c000d041000c00d40580c25102001c002044014259a5a0b0b0310700c8010414120020b40c040c04d0315400105a81c2207921820070713282 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 652915197 1250 652913947 652913953
    0xc0807020c011e0c052a0901140d0f11180117150106140903120c060a050903032205060106030e1204050f010e03151501030b010302090a050910030807060b0102 70
    0x10701c0001142c2e00c00400c0301080200040780c00e40405284100240020070740140280c51010300803004018600d0400c6035904190071150b04055820b1800000c09401069210060b041c4000e00c100400c030a007a0039000a4002c02c40a10250188403480503100008280185031038414070b01c3c61280d511144080c0541805c2c8019a00c141c100780d0ba002031aa285110700040c40c052685c81c101084441b00780030301c40308070b084a05000000c22030f24104013183d64100c81440058641901e180d100b131074a2030040140d41c00034180024000041c00c08003c50760881245284002619449010218140d081460050030340c851040001134240c0d02d503200000382c130007560540d000383d44040c10b00815800b4034011254480c0351940d00ca0050f60240c034040e82d00c100050306540d00480c098040701c3c0c8400d000c4640098500058100004a69162040003d0041d003401d0440c18156110041200c0401d1402014015803c040c0882c0b4418160313500e210081d0b51020209503229898513096029280b850010780c0584 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 652916447 1250 652915197 652915213
    0xc050f0a060c0201142a040902030a1b050315060c0d020114010501261008060709031203270206040b0c07030b0708011a0a030b0d062c0c011d040c080702 67
    0x40c418007421000400074545415186c0701e0040140008181703040c0e010080e1001e030005a00d00098102800c01040d41001c0161640381c111071000558032031140d5002035041541175880001c1d007180540760020085001c001c101417851010900e0303845030010341c0d0518412807900c0d0071020340c150801c0c10071101c10002c0030b5107640c0c0c56005548064440780c00804011212000900007002c0d0340c805607214650003540c0080c10340d5480c170749061801c01e0341d044000410b441410300501458200e84010b144640c5030411484001c0c0b0a14080810101000e5020140008145040d542e80c0d000341d4015007460000c596a407a410100c50395514010701c821200c110070340000a42c40e40c000c100d01412034502c0c0d0380315a0441c0d100c540c0d61400d0b5200700c900c0802c0c10b582d10003507846a2034100714003000d00d00c5044006150b03c0584002c01317680c807245034521640b9050b5074000031500c3d03011a12494040080c00c00c85090440885d03544c1c401c4814034407158000d461302d0300140f403040e4000c070301ca402800c194095030302407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 652917697 1250 652916447 652916471
    0x616050d030e0304050114090a0306091a010e0c04060e04110307030213170307080d060305060a0f0e0f1c0c320307080412080c07030302010f0609020c19030c050f0a06 73
    0xf901440c491240415075060b42c410308240c100c03000b0081c0364001406076604585980e030342350445500200c242c03090042c07000c0960002d02c2c206402800b50a40d8804400d440c41d2024440c00c01c2c0c42107011785010042c0b03550600c16191200d0700256000c81801ca0503544a01c1c1c03643c80140203401805402400c01429580050b00c1d07081c144230b840e00900580082c528020311929081d045500100108850540d1440000301103482031000c01c1c02048030400114081071121800001d0741d280d035a404415801040b080c8400c2080040c07044000c0001510351681c00004100030354040c4903022000d1318100701890001c4000346d0280d0709445843c00141e100c03003140340c501d00d00c680d28010500010000101003005115001c400d82d01818080e01c00d00440d460141004aa14200f001341c0d40201d025079124120b05480c0c2445004010150407031050441c01c24050545580e600c91220818102d010000e80c0200709142c413a02100e41001d0b004411a1000d8204180041da40c00c0400c4003501e250b8504034181710740c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 652918947 1250 652917697 652917703
    0x703080c1e0c0a170604300f0f08060a05040e01021312060c05041a030411031506040e0309130f0e030f03070906140a03050c0c1b13050108070e060616050d030e 70
    0x2260582c000500b910346c1e6941c1d61082c1035041c80c0c80740141c00310760042c0c1c2160280d01d8824000001640e5500840100092400b4003034620070030700c441c1800886000c0062540340d1000000480d0400c58000c181468035042013402440360407020900000d2400000c0307190000e044180f00114403400c0100711440000c0e80c200c8403401075000381c05820307100704403401c090003e8101a42c2c00601070001d4042c80e042d1000040d04d05642e0702c0461b00c0c800144800c01020307281610403004010b442c3c1c07010714501082c49000492402c10040a170a070655034900c101030303e6096074403a60040150f803048980d035055505291881e500100d416500080c0320050200c0c10030300c10700c80c02c084416950b105e030341002c0701d069068000d000d000b00a84550b84042c011070f000030310200024002c403401d80224041c40c003140010700ca410001c0f070180c0c00f2500d0401c001041030700070014090044500b004400d126517107035540054641e2240c2807050b0301d5030105007104400c0c80004500d40924080c03a8504000390710000d40c04c1a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 652920197 1250 652918947 652918979
    0x3061a04031b0f12151802090a050c0906030a0b1909050702011e1a151308061e09030d0c120c032a030b03010f090302100203090703080c1e0c0a 63
    0x8032542600c90410920110b0071481000760720a8109204a0007020301d1721049030241c01c0100180740e9203c1c2ca640640c200b8086080e0800d44828041c803281c50716542c030565502c01ca486d40b60041800200099684060b42d0051010180060a143d02149001140c00b60014680500005107107000c01040d086801482082401843c00403090604c002940d03044005019504910842d61241c0395212442e650b83c141246a00b81840f5041341c5070100b000d00090701031029008454a50300500074040c0101c18940c107440200810076516082c2c0d91910000d80c11801006c6003800f1080c10501031114454104c42d509a03c05030340d490803c1701003031b42041141a07458007508059112000030fa2400c030740800300c910500d008450b040c049005042c3d01c0200382100c40f581400d80c0070303030f644102140401d0b80c1071000340340b4244d11a10940c00e40c1800c3d004591200f138184001482d425002408840b001000d01c40c60015944000b0700040682c80140303010b8640c80098655886801c054002094032264541d183c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 652921447 1250 652920197 652920209
    0x8010b01020d020a0221100903050c0c030a020f093129040311010207050a1b1e2102031b0316030b0112170408030901080a0507020a06090303061a04031b 67
    0x40c2c03440302c009406086840e80c0e1032500e44a8080c1c034000111f4020030340101c1514a100b81d5136160b460a56002c0780b42070400c958004d51181d00503a03484030140c6c1e42c483c034240780f8420484800100741c66201c0c0c01142e20381107180c98002c10051800c102c407444c000d5014100081c1c014200d80d81001010900001c0e8841000c0a0a16908a0202003008244900b240011550809000501e4218182c03200342c9024000c0d54200e40c90048640d200c03501c09950004031004000780200e200c910022a229000744803824040d00042c0c1303004070078909030241d40c00c11083e41280c000c2c09480e4501d0226006404024032421901e00921031810484100000410000116038000c100807240e41d08002c58440300d038482d03500a452940031222402d1400700510000d00042034201e0003565510100c4001618181c402428080103d240408101c0c07080c0d00464003240d8030f5482140003445d01e40781d28040d8002d181030342028451003103106801103e904900300138019240200e180140ca03180256004039998003074001d071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 652922697 1250 652921447 652921459
    0xf050105010f0c030e010228110301050603072c0103080306040e0c010507030c140f06010f150c060c031407051e030402010c080a0207320409030503071b0c08010b01020d020a02 77
    0x42c4000ca0b205c0c01001d03403100c030140706461780d042d900d015001c02021150381400020344551700700410002081c0d8025038032082030340207101c146401d80000381c441c16a4850802d82440450040301328843c00440c0071091060b003e450300ca196164104429075400403a641e9010320b150407000e4141f180c0016400c1c20701d2405a48040c5002801c0c0d44c12207008044900850b0950a000206042050103001020748500003174000d007042c1d807404c81c03c41c0c0b190100341c0c02003264403400b0740081d110b50b5014040102868200c90086107654100c1c0b0201c00400001500502d43d00c0350f1801c2c0030f2031991000003003800c01c43d4040c4180503000c06007a05c44452209460007800314404089100c0003850680161104006c140143c4813180d07500c0104510440440c1026044414030080d8000d911074144030528200030140c90030410391501c1d60f40641144005040c1c031050051850600c1108001107810419240c4d00918910b03801c3d42d103e120038040e10b1445001400340c01041105203003584001508052560000c2031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 652923947 1250 652922697 652922717
    0x3030126061b0a0e0306040605160509091b0c070f061812020130050414030c0709021303021c0611070b011406120f0603010f0228030912030f050105010f 67
    0x1141c890f40000011414859061100003e940e41442824490380c01590089668900002400c107c1c2840008070b80520206010984ea15161696510761145222071924116803855410b840035000c1c00c2d04000c540c1c86903450210700c0001d20003d4404942180c0c5460006406e006060031112442c4e0041c1c200e07240d000e03140040503602c1641070040080012804c1450010180e052660360550180345035201d075118024441005803a000012446521901442c20700c440d001c0f04640765000d42c840d218038150045142121310444c03505040c01140e004280c650420400311a84084002e8040d080e25454600314086141005406c100c0d2003841d84070424245c0c81c0e09200c10b00510700201100d1316004201480414050380400810314003030381c040c0d01c0000542c40c00c03804050a40306690050707215a0300500031440c1a03100039010005010341c00400103a10f410400c0100c0c020000c00d10084c0080140c080070300e000c00c0d0142d20030825940040018003045e070f03d94005440800707000140b080042c4a07510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 652925197 1250 652923947 652923991
    0x106050a14030c1308030405150c0c01080c090a03210309020904121404080c0f030c030d260708010306140411010305190c200a03080c0c010b030303012606 68
    0x1c5901c03a07040035429050420007003004c60040d0181e00010031540c4000b5050081e442c05140040b003034000200d031103180c0f55020000d41d48030700c804004541800b0b5400302241d400c581140c161450704001411800c60150b8904080b0010052400a9207110307001c8030321400e40318400d02030401080d402400914580d1035a54030742a080c0c80b40b038100070421040504454140c050440108000c0c11900c0003043c0c8010007200b04150654840030302c61007980440b01518060310003040c5440d00d102c0d141491050508040b1907101d5070507200d150312001480c4001001003c0d50070210140c10780f030060f441040f0104134014100c0000c003040d50701401c03030110310f281d01040758400d41095902514203a100401541081d60507400c1c1c0d80701c00e14410100b00700040c42d0034041c140c0d00340002081c2e445801412442e405840203024454050700c6048000b8000030400e003104400d40084170300e03a07009402c80e0740d070b0340c0e40c0c2c0710004030100c0c0b2004407458442c00d141e0148100b0400680140192a4150450740c4105069 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 652926447 1250 652925197 652925237
    0x90f08060606071719170a2d0b0a08070314010c12111e031b0f07030302091c05030403120e010e040e0a1a15060708090609041d150106050a 61
    0x107031050300004081088204440e4500c4030020111300035120700008160300701c440e0825030320040510a20520b4108500c8e0640c03100004007008401e807420a40001e11104095006040c495516941110310b0101c0010310a1000038901d084900072403840c0104018040164261080d140017074000035180b208030080420fa65000d51101c4d8240c1400c5890403010009100760701d0b8908505132107050300841002040c045131030f80e4040105507045110301d8036001071a042d010707000d02c0d0005020158045031045254464407200590440841c4084643e001c051801550b60751082c0400c842c1e8006041c55034190f14000c0f0861540c2031816191010140d00000c1400024a14580c903598144a01c00103100868400b080135400e40c80001002000c601c1d142c0402031401c5074a01945001c0c020030040400441e0b00c00c1d0640d141c3c20300c2224803954031340c50000000e000e01a40d04900c01e0080c00d10111070240c01c40025502542c0c00c080c0f0f000c134103d03a0707544000c2d41c05000e6000600003058915400071011020781d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 652927697 1250 652926447 652926473
    0x80702060f041b12140d090b030c0d021303060204060e01092d1d0604060614180402070606080a0201030e010b010e04110409020a05040e0a090c1202010c05030307090f0806060607 78
    0x40c0c45100030782c03581c2d241ca000c50011040b00035641c40c50780c030601c84848003003484606c00142c0c2d2030074581c00292400c83e988205100080204400e0000481c881918442c140c0440e08543e00001800c0c11345074070b03428190001d52161184a0100e04c060854140d43c3d40115108402c541400003034003035801020b03160000111208481c03103216011400301142011460300d60840d003d10318100745c0414a0014144011600a0740105061000148446036146545000ca031044502100003410720307500e01c00032402900906d02c00400d003c3c00d02d84041581c200010f512400a8003d9034140400d42c980483c2078202c4442200050000d4011080040941415044000d0514400310a1403400d903464201000f07e03048454a0b4000810005080101c041d580908541140c94413400b0820495155515880200c05104100182c5079400200c0256030198541e21505a042015030b0741e2850000300040aa0741c05010b10a440501108041400140012550700c00c200141c112132410405031150000c0c0d90f94 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 652928947 1250 652927697 652927733
    0xc04050d02120d031a03070e0606070c0510080426030a180605090705010801080106050619120903080115110a140a1502210709170c040e0c01080702060f04 68
    0x14600903000000d02c00c0091180d00300003564005442d200d0551a4030741c4840d5410004d00c02d0b03104810500200d150303a010b480e0002011100c2c1580c1b042c0380d1915455a274019032040781d1000c0401100100c0c0d40d003083d48070344203074424054400400007142c1d084017916007c0080500030b03101880058503240c100c0d40542c0600c518406502c0030718a4903961351090f01c000321038182541d00120f0f4100101d5801140300303805007201c50001c5c0700796401c0501203000c9004020700e8540f248070000810310710074094001503260241c0c200041c4031000c01c1d4100a01707004020b1180c00d59038900d18045d410602c0c420740d00c400000d01c0c160301410702c403440c940b0352205c00c1040004000060044e01890000525420080d040a4910340710142c1c031a14080700591610103250f420440c3d01580004102c11307264410b00880980d00d920300104c3c5500340e05a046490400c0f610310075034025242c00d102200078040040c0c41e0000c0312090342d6014480d5107502007240ca525040c3c1c1c06400ba45e207400042400540c0d030750854541038413 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 652930197 1250 652928947 652928959
    0x801050414011401210603050d0c110105032e050102100b010504090203040212032101060e0105090415080d03020705160501120207020301110f091206010f030308060f030f0d020c090c04050d02 84
    0x1108170001c4802400f89241c036221035844000f00708002c3c090001902c03c0344141031031310301080307a6150802a42c840748041410400f0020005a001c0b5240502400341c5d102c8407040710b100050805080218941409900c0c00b41c801c48006003211100d60045541143c0c042c0c2d0341906240c60140a0000303900b000d0700481c0d000030300d64184420b022041000d041e103e400c90909402c4d4504162041c0c1040c0c1040e00300904020190221a8440e600001294a140001d45000031242d120440c000c02c900d00980183c265401200021542c40d40d043c0c02500e030a60091040e00d0041140c1e0001071580704451080324041442103540707100700a50307513024280f035030300180c0080740307100c0460421040b039480f1040040001501190800311410564900761241001900400b410750501ca0710501a200a200040c2080100000910103072641c2c409a440d180e409000c8031076603d180e1580d60344500c5109038980052085c04440c19491602c84c0080d40261004002d4601d45805e00061040c00d200d110005d81c2c02003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 652931447 1250 652930197 652930217
    0x703031418031e12070206190b10110a02041e0f050f0103151b09031109012403110703020f0d0203040312050a0309020a030b060a08011e0b0a08011401060801050414011401 75
    0xc100708038043c41740c101795010b045c0702d2500243c4194811081005124010724080c003508141c1c468041c1c5c9800341c3e60368107004184240c200f00c0d1514010f2080720094006041c00704000c01c41d24806030040030000009414041000c0003c00b040840b0300443d1031050840c0749000400200b40e043c03843c2084144190b0300440d12000d42c080441c482a4a0a01000062000710017081440036610020810300c10071581940c07154500305550201d4800e4401440f42c1d035a5030451450518002d0b80906c3d600120081c1051f125011420084e4a44201107020820781c01240c111005aa2000c003c54082d80d9200e0034262030300c0e11050007241c09801c41030009051540e24000c02c00549e4401d541d86c00110b02c200d880c3c0207a41340070014020300340c5180c1c3c000741d0036070b041111007901003801003861002600072841c0000c2d481501d8002400f02c040070380c00103240d5482c11011140402c9501865070681d165a00c6044d0f0590340d030340a000485a510184200d9202d2810041c40002c0300510726540651051400c5103040b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 652932697 1250 652931447 652931467
    0xb030a050a1217070c0201030b030c10140d1d010e0f12030c09090a06031b0b04031403120403090e0606040b0d0e0106080d0809190506070509010309080703031418031e 73
    0x303c0c1c054510001003458141c4d464115070303040c00b603034145220a401601c40084104c000c5603504140d6000b527030034005159450081c601d441800c1e02c01c1c64207401020301c44014804c1c0c10100001c8000c803010841d508124490280c40f400041086402205500500b0800b41000c584401604003805960548508210039645940d4182c01035003d607407007490010315985980361041d1400d60140c8903403000381c0c1d640d100b0044080c00100b03032021241c1141044003404032007610305040d88101803501180c1d48428081c44141540100241c06452401907580314a8681104210752402580705d0074a9011040008100c140c0700343c0c200c19404500c00d400460380c0c1c2c1e114001a4107001c1141d41c0c01000600d10000c220324103c080240c1c07241036100b9003017010071a40b241c0f03902e501d52174014464414001d002400c040c107644241d000244040e049403a80e0307201c110914004015040d02d018609001004a01190260485200522500c0110002145494024400c410460702c00304600001c200062120f4125 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 652933947 1250 652932697 652932737
    0x40609060212160305241921260306010f031b181a07030c0507030b0a0b01081b0a0c0f05010f021b07051311160804090b030a050a12 58
    0x24035101c00050004010780140101100c4000745444401411060008040c2003440e45c4882205000e0b5452400302c0d04a504841f800c040682c45046113046010b505071207071078100c28004035144100000c0118092030200851209071150141d940082d04001141156000c1c01e05c400030810a0706000c1000c02010031101e10030022044c034800403d42c401020101584134148103800303402000300c00c52a2600303a40141003140520040142404030f03800b01d0006029042001d0801141e00c001d0000c19481d003519201e015192035444280400d4602001c0361981d640b02c41001209918000190304019241404884001e15108140c429020301405403010070f90078012a01005030a0320003681d150080c603044007802c59008a001510b42015030300303000070360b5003002d080134205030000082900354407200c0008043c8500482c811468806006003000c03c51448081e20885100350701c1000f03040310075424180c658904050040403500310700001c00c001210814107890381405407030a40510f04072840284a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 652935197 1250 652933947 652933951
    0x50a1b030e2509200a0203040f410d060b0901080601030302150703060803070c030c0504090b180f0f0601140604060827030d0f060b030906040609060212 67
    0x40000e44504420850340000c00180c40010450202c526141040302c000082060301801419407182d2a018088010700360301d144400d0140f4214000790380c91000c0000a03699502c07038410484495030204002890b45113000201c6002c10702c0c08420304140d03c082500c1d402204e00000540c0144410f1403c2c03000c2038a5a800032103030a88590170001d9030190307080411400ba8030507801a070751640640300600009a01084024950181800082c090f490b5410309401805880d0417008076072001080000603c0003e06089007140e000c1c244c001041a2604148000c0d6049030001030310201d01e68000c1114044001d200103014402e030010340300f18941c0c0d40c0610341051014040601560320503c0103010030b66491614001c01042100c0c90303482c0ca842c1c40340103001c4000007810705007000c1c40d40300750f00300044698801c05500b410b43c10983e07544503040c01fa0b0000510881c0000203050345041c40114000e80305d2404c880c0100031902c003c10155540796602005041c2e0354008070b807529020b100e0380031280102d41c0442c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 652936447 1250 652935197 652935251
    0x160615060305060a050a052b1e0b010e010f0b0d0213081006060c1505090c2119031403040c050402040303030f150608010506090102071d1602010618050a 67
    0x4540703400c000d000c001d540345817600818441d8007182d204003c0c0755141d42c040602c0f0b44402010640190010002c00c41980d50042e015000650f84880c204070400c54080210615200e005242c01a98030b5207004240031380e0074000c0045a01c0401020701108291402500c030042110b0800361801d82101c3e50710001c04602e5000400d1584400c1216400554034015440a8045444c00a621503100d407107115000c042142d100c0c100981d00d001058000b102030055403541c0501801401403650700c0ca0014010107140800301d28a070042c2100141c075004a040303401040303078165461800d0398642c0391710030146030700140c0300f1a40c18940380d600164580f914005800250b000743c034005809400c3c254510281e85542d00208c0c087d40c04c44105028198020b14024155401a81c101c0e8a9480c0f000060780350800036045a42030b51401c2e9080c90b804a0071403000c6100d2000c5400404022403c03010a13170036224140100c00c540c402e0143c901000500c154840e96000e066100041641b41c0c68603507510f0800c8000e0418 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 652937697 1250 652936447 652936451
    0x7030e160902071203090b01050f1809060a0606021f0c0903060903020303040309060302120f06130f09050c12030301062d09030c0b09030c10050403020a0609060305100b1606150603 79
    0x3900c144407180108404160150405000d21b0740c1c20394035100f222105010761440303030b560800341c6e07611780c3c07a010480c0800000443ca042c8244c104000c425544100480e01000c00d41d007402e0002c01c1061010a0a0850116181150039a2110307001068040c0103500001c60400061003000804200340f4010302c01003a010390091542c13820603080c020a00c5806402190600d0b0040040c42d080405601034680d22420080c5d007030700310b0b0f1102c000083e000070301550b1350320207941400d0260b170042c40385038000c4800c54411011103080b540e100c01407041c00601c159401c0000d030002c0c401001050302802181c01444500801020f04028a6804900300103181c004240010041d4000b03100304a00554080d001d00b6030000b0705400c0008440000c2d60315000030074418040c4620503031020321940030b001982c016507030080910b82d283d5103400004042c03104521a5a00007400d000104d40780c280000c40765007e403003088521502d418001c080303104804594090450707081e683c1d400e481010030408502900030f00740951700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 652938947 1250 652937697 652937707
    0xe0603090f030301030f1505070e121603050303010e0f07090e0603031c0506130b2d10021f0504021e01111006032009060d0f0501020f030a050702060c0307030e160902 73
    0xc00010803001c7d1050451803412050114030b9030010801c0145100444c1c080904007041141c2e00d0900e50003c62440e4401640007000c0204500400503506031601c22044c45800d9652484640005005807841c01c003044441c1000e0191601c0a84902c2c0e0007000501101d1401d50301041e030407550300f001e4000c6014207540e08284181c0785440c2c0d001d5800c1000340d400501044c0348440025442e00c03503031400d10a21100c4400100b07030081c1003001b10380210b18000c2c035a0859078021180651500f5641380d04c4600701c0510202c500d8109a64890385000c1e68000e80319010402d18909400740072181351440d10706101143c80403c040000c20010701c0c24650440d000461042d20b14079110b40c80710110103d0308044410300c0c1c1202059240c03550030310743c030107000c0303840e040c07200031f541010000f184409401425550000030f0021001c200140194000c0c1134001d401c10251340e4a482c1243c50394400d40700d0810300601000441c03070381c1e4402d4100c0f119808001003075505503802d600f4002108002944501c29590300810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 652940197 1250 652938947 652938953
    0xa140a0f1107152708071a03100506030a090b010306200403080a140f12041a040c03030e010e090103053304240510030203060105060a0e0603090f030301030f 69
    0x18411655904401004041c0c10038224899441501c803c00341044060710b004110b008002019030100407203550038984050722400d1480e2520070034014000403200f690580c0d84252400c2040381d00c5090b4078000c03010843e05100801c030a65201920b0344c1105a19401c0140c00700b0502d00c1d006000b540b2a12000821040100b0514036420200044541c3c4940030b10080010600346070440d0950b255a19150448520411b54282540640441040100b001090800c0040c000c034466a000781e0040b00600701380c610760f80c2c0240340e1500c00c07a0003c00983c000001000083d01445080f81d1115050510002950740e41001c180c083c0001d074010749481d0f1022482c1c5002c94090b4441501001642c150800450780348407a2900132800540010402c2011050b0a0302450b10f10800c040c014803070f240103102c1c9042402c01c60f401c44c1e41900041e4828052003000049925061048079104e012540700c41100003a00004c210300c940004041d42d05501805601d2062203d05200070740c080c51060400c040c0c4420541 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 652941447 1250 652940197 652940207
    0x1005090906090705060a0c0605130b0109060f09020702030c0d060e2a030a02010206070c0305070614100f080a02010c061805030c060627040c080318011b0201080c0a140a0f 75
    0x944454005c03082000341c018003d50060b045c2441caa0403007400f103070941324454109090703150103e001c1d141c58481d20002ca1328681e0707504206c0450b0041c0700241c201584441b4140102c2c4201c6c007009616034061480040281410042e12050500880c400a40f85041c0f400b035500b030044120400351a0301801a8207030354000700300c02c0c90010007000d6000f000c407144642e00103543d54401500c0b600a0001e24403044040600c51800c84080c03d0f07001d04103001144540c138110000c110240d5100b070b0071000702880406c0c20842052108222007001d0010501550180c0040d40c841e5041d090a031220303511501c401960b0400c0d0032102544501c0380008503644c2c540c501c20a8181100a00080e10981100700c881036854402d004d583c203041000c80403911a616985412010741e85d072a4840047ca000204d2190142188000700581c6c640d000c1c0c80e803940714418a10f11107a000040394000340031803411710209000301c2d047d0001d8a5080340b9404d11100f00c1e543c40d502c03501e290b040034091100243c45c0002000f050f036441 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 652942697 1250 652941447 652941449
    0x150f040204090f23010501081902120103020108061f1409040204080a0b010f030f080a1b050309100201051012020a031a060a140d08030a1103090703030207082410050909060907 77
    0xc4540418078032000c2c4182c258051381881190f041020038804a18040911844800c00c4c0120400031551481c1c400f0707004018200900c001d038081514400001d021b41003000f110f01100d000c2c000d0002c0380c80440007094540082c00c3d00c06440c120414405554151250702c010009000041d009200c2d0403840d1500718402c0c60141c010f4040c440c2c02400c00c0000500420080d00c0d041c0d407008015840e40c030482000c41d1710b001001c815682501038000404144080840100040403040d1050f820b2006401400d038241d440690780c00c2002c0a40c5003080003040c3d41d0700d825800c9148001c201502c4141c0c1c03500c400070304010b204c5403280b50006400600c5003901e0325802140040000e44900d0450103d02c000140b0030030003c080c007404503880040050300035591544592400c1c2d2405001c580c403030502d0500e032999a07010b40012005403081200c080f41c59080001c11141c100c482140071021241c0100300d04200c5603010b008444541729100c80403840c0d50b52002c02c0c07446282618011702003841d00a00d09840c10002e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 652943947 1250 652942697 652942721
    0x415050903270d080304110f04092001031e0609060e0405150a0b03030a08040c0e060616030311070f1109010f0314031e040305010e0304060503150f040204090f 70
    0x4120300030305820401c00a507029100c0000010b180e045480c04128a806000d030003c040503400400c0004020f0f41d03960b101d042400607500b04c0c00e8410103000380030860b20300309000b41441d4200507400d008070300120301c400d0141c203041c03601040001407801d81c00110003018074900000c517295901889180400d1103a50024400c05020051605140d01c03001d4407407140c9410b0380813890940380040e94544075504041158603002e81103d0b500c40c3c61541c024660360040e1412901e031a8000780000f440c080f41901e03c0e0140ea4020f10031450096002c0040300d0041107800704405040d12062040105a20000a81607003401903241c83c0c1d07001d5a52501420110941104e14402c054980040c4040100710f1101804e80703901020918612800d0290035103140035601c4051501080285850080c10103a400b40040b00c0c801c60091041c2401041340c191a8084c0380a000d0000350144001181410f00340f407000c140c0680500720700010081c8002103400ea90085c1c06c1101415152141c115203500b080c0308072414101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 652945197 1250 652943947 652943953
    0x150210060308030f090708191709011719060e160315050d0501060f26011a010c020d15050702100608030708031b07060f0f0c02070314120304150509 65
    0x1003141d0340c4041d507000c080c22110710540c1d00130002c1c1c01038000308900e0001e0010f5404580740110350000e103c01968603440111a2074451110102e80031090303d0550b06480016115010b04810386680854180b800400c00ca85003010322440304d412044a06c0b80030041e12448514121600c4e007460340410781c2d01e205020108142c506095200450300c0e008100303060b12812a0786203240f407000e0030102e01404454024201c01b5070a400c00040d075120034030100008000b055400d1114000c825440c500f2689044a192000c018823409006d1661054000601881c030041c040c4403020080d845410148042c3e00e0714141c6c0a51fa40c043c801c11540401101e10300110110080c08000c1c107000c54103071070380180b910042004002001092007440c3c0c1c030100d40100401001a80e4840c2000e00b44000642207920264400030b1030724940c04007a100c140101c1c0822001a0001d00e60245103940700c80c03c0460340e001f00480c9010b00045010100701100085014034012180700d40721102c0d2900510490f6400380c03000308258 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 652946447 1250 652945197 652945199
    0x209010f020d0f051c0203090105040501150b03150a12060504021f0221370503220309090e010203270706050a0c060612030f0302040b0f09040e0715021006 68
    0xb9500a0100b003901c078444c03600729110030840809000603006244d41c41503071030010040082d01501540600d10035170081c0d001f48208070780c0c03818420542c0100c1c003409195020400000c1da09445040364a5410340e40682040300e440e941d00701d01040540ba40314103e801c1a158414441585001c03c40e202c0c2001000d10648409020110017075a1031005840d851801c0c541d80d200040144400b01c10b680029546c3d59040d103003c1c0720450010981102c90504400304065882180340300e51244084c1c0f48203150300b0440684134034664046000e43e0041200450030420b200d01c000c902840c450046a807146540700000d80c9a0602c41904134a100176000c0f101c00c00c3c030300300340740381300007000000e9031300071150913080040d52204c5200084a05007030100c2c000e048142441700c00299100c071900d25400a5000340d64102090010920031400d900c11442800101002400300c8000d00003000024580c00c50020400100070085d190610b0804e480c42e4021003031205209201002240c050000408403490311604200807 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 652947697 1250 652946447 652946473
    0x80a0b0606190804020f0306040302070305070e07050406031505060a20060610050d0b10050a1b110f1809030703080c2d07020a0306020a20070306051e01090209010f02 73
    0xc42c05050801c040002c0c44000c103080d501c8807040004013040c00383c00c1e07861900c1c080c10065560002480111070310722620f07a000498149044086000d161250b03a4130b80381925006040300a00f502c81003000d03a10b2600d100001d03950745d0b89030007003280000f40d46860b004014100303d81081003018003129202d6800510030008140c0c0c4015030540c80c001c0600713059403a1a03518854000402510003450f4204481402082c10103420a024185003003031390340d801e040680071441003d4203000c4940d0040c418070881d00c10040034504803da0905c8610302400359820701210905005500740d098400c0e0b00c2d03980001a44406060307010043c03941c007202c0090b0152410b1981100c2485520398004800041c0101204c031200c80340842045501150300104130840d41901da080c20707402580000809030116552442c04020321307009a080e0101d01d1030300310141022514648900c0701502c001040c80006076003940c0c9944100c01232401590103440100f41c01a04d40c16080c0024100c0320011908106541c44103e480e455 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 652948947 1250 652947697 652947727
    0xc1d01090810052203051801030b0f041a0d0c0501081e0402040506040f1e060609031709010513060305090c011409010e01050903030a1107091b0315030b01080a0b0606 73
    0xb84001c01d1500007055615003144440360f03001540444103e0205420202c181540301c0d018003403210401c0504d03009420340800640c115070641007400d4003c41e2034840e5440500d01a8400c1a00c41090410310744076100079000901c580042d800c1c11125001484018080c80d60b2042d5620f03070002c442c0c031004100380001407982c221514000c000030300c550b483c0c50020b0155105d0742c2102c8070318001c46405000d050711848421315201c00f034040c41c0b08802e04e01140040d0a521420001c1c0403650040396800c400903048c0890900d562188031040d05011003003000502520074181602d004210030b035000034003410000c917454101049100124102300706085400000748402003115a010001d00380081c001d9100750050f19540600c0312007542c180004034841d000507400544503e011040c0311309a07111561100c0010b4112101403078249425030028000c1a0024041c2c0e00145c09032111a80e6451299642c2d51a110f01c64001d03003109100b44c020741042010400c540051680205048030258140700146001c025 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 652950197 1250 652948947 652948963
    0xe0703080708040905010e180c100507020f0a080718151e0b040b040819031b030203090405010314191212150305060f0a020301030201020a030509040e010c1d010908 72
    0x103054001465508010b0104200c60003007490103024409581d660354440c2c0a400301303c0e1001501d52140b0f070910b41480001c512aa15414014440040320461820468603038221100491300003040051440342a81e40c44444402404820001d000850520188020411100562062250030b1510702c0b5030401460004c442980c44514a03000c01041458100c08038503015442001c1245002801058500500005009a501c203004860204a29421040d2a21103640c00a00041d91442040001058a5029180e103074000d09c103ca08085107a400542114000c0c1c0c000c641122440440b0310b14602c0502c07070600b03405070210108400c404561603490b0341c54002c030466010852810800810340e01d0680c450601c40c650a01c404000a44a282a80c0e44081c2520891040010306c170010300c0c24107481c02203034141e0354107030302400800c0015581a200c0b50001c13186150b0080d2900c0b14900e004100b4840d449200308aa5a002030000b00300e45451840c2d8040d916150400040b240c0600012100181c202 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 652951447 1250 652950197 652950203
    0x906090a180c050109050609060f070f120305040605070f021507110318210307060c0e04021809060303072001020c09040c0f0509010e0a0903020c0a0323010e0703 71
    0x144296452032044001041446088986100401d805405024031180d191007034940a0300e039500c2c6a916141045210b000384003010741d1100081001203040c109000103003000a11814503001184003555902a04440a100a00001ea9201c0030041401000e01481da049503c50510281c03040150500035242d040400b01084c000e030300c2002181940e40f00e07402c0007500e07428002c1640d071603114400201c641c07188010701c40c030310032008407025017405520905103101c9200e03074030300440c6022200d41d5400090103d0000c41801e020384c0e001c280055032240d000074000c00c404400050108c141410410000117805030005010b640305010001c0000e0060f01c250941d40c4800004044035a40388004038684200d441c60603801101e600140800c00440c00180e106581071202d0b40c0c84410780341ca0610403001000d2007130b02c405c0c07076041012440b151000e03031110203032900a1065841002e01040031030800e1460f41c2c000c4031032410707500d0811401004c4912000035815804002e210301c10100f00314541c2c54485000107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 652952697 1250 652951447 652951459
    0x213090504020616171c0b1c0b0703110f0d0e0f0316051207030906030c05160b070e092a0c0a080a02100501092405130f02040914071d0906 61
    0x118040c44150715850303540450b00516290b4940711b141c1000c11842142c21400070281c00c0402d440001c0c50840d011070850307601c8582c0c480c101002515440646240030346140c0138542d5031810078100c3c000b408000c11030040101c0c1c0c060390f143c9001e500c0380211500c02d2146da0498002205415894002100f1a00da50b50742e500e850f080d50310300e403c15034102401501c41070055040001c2540815030020448011503565880070400d100111105a80d1b5100380b0308203c1c120500304c103454001a9600c5c1c44160045e01c00e1400109e4000f5880c04183d68840039203280601e0301f00400e034200c850a5802c2030b0404140e020b020141040c000740040d0750b9600042100401d11400402d842090030710800092051005002d03081c80107503510b030110001000750551502084840c1c503a44600b00590341e13080c200b11003020340560003003074281c8a500c0040040316140005250204000140d0b1011805040e62200d0040f54140641c207240c500030b81090600c1800740d039441c5132800d010f0941e40d00e03c41c03601c2d40101d0641d21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 652953947 1250 652952697 652952737
    0x70b2d0f0901111b10080106080a020c0f0f010e0c0a080712080715050f010b0703081b0f070503130509151c02031e011a0a050d020402160602130905040206 68
    0x1611100d0b6141e000b030f00301c2d11840781983d0039034010741d074015000c1e8800d0301c4a03182081c0700b01080b40c00d01000d00403900810482408144c2403034465004065000c540c80071744407014844002c0c2400c0c81d980100109241e0745038600c0d40e0085000340220b4100800c2220360040c50b40c607004807036444031454406c0d803061668500c062420b21010800701da11040e44040f190f055601082e9032980204025200f050031810300b0800800c1407404441200c80d180d4168603503a5596460f0400445540d020b0688840e04000501400c1c1a10356100d01408140d1310600242d9240c1040c9190700c240d071032182d4071852141c2210300500c9240304441c29090314240381640e50126a070715240917100b0700700b000c0e00003d42620407078044015030b03100d5100c860896040b01000303014142d90902c414200c03183d5809802c1e44006102c03000c00281c500041240e005510280c030160510380d90100400d0f00d444503450654907960000307600702a8000c0300b41c14070060440d43c14200801d04042d004207010740a074031141c010090704e03001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 652955197 1250 652953947 652953949
    0x5040f090c090b070b04110d1a18010618110a120b01031104081b010302090a0608180303010b03010303021c1202090a17010b0f100e0d0311070b2d0f09 66
    0x10200b00070b407201505140d030351051440c00500311003045405443e501b50146420b60300b81f80000c2e40040990300052602e2000c0414004515040300251030100c1117107800220380700c0304200b03015041c01020300c0400e1481d190039404050013680e07405041d0390450441084501a99070308405d80100980003079500240460a50300160003c1040003801c1d0200640801c0c000780c010780014400840701d90b135251302204001d00c2001502030740680d00c031342c40d40001e1030072081c05080c1c07044407443c0d44580781194000d45100300240300c40c01c41d407080c0c00002403490000010f000740364040001c00c8842a817502903540400c0f01c2c1c0c600030440355110f652041da043c3c0000c0c031801103a84851403003002e004204c40d068440d6482d003e150303000b4030081c000d050007070307000b400c5181407444d0262400d030070500c4c141c50f00e810b101118803c1001130500401c046003070088038400e406018000704980e0010b0004080d00300d40e034035880b0b40d1501418603280001001c014080c90b01c0d90030003100000b6105c003005a2101e030707130325800040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 652956447 1250 652955197 652955207
    0xc1212050a0c0215030106030f0501050616021302070b070f021501050d020d0c1811090a1703162301051b090a0302060f03010312050316050d0908030a05010602010c05040f090c 77
    0x9000f962100790072038894120150b00000394102c0310f0648040181c5c0e80c54071400d0081d00c0003403249a0f030042c0244801c10b8034000d0f541c1064074031403004188005100c0c0d120040e1080307800004041d125490f541e020005041c0d0800c030480200b6107503000600000743e45200700000c2440c14001c540c025080b445c01c4404540b10303a524890340590104110b4083c43d04d80d0b054440c51070083ca44514454104030484540c0d441c03440442d1640c02c809080182110300f0905031464000400d401007038184030400210003880f0101240110b6a8070690f00c4110345041f49402a110b0a08040600000d9140006001c0e650344840c18035411040502070701901d40300310030005000384540b507002035001030000985100302c03e10a40118140d0707219071a8a02d41c1104c026040b24203010440e400b80140842c0341201d210140030f600030300b0038404a661b011410382107944d20000b96400985188907400e882c5e9005002542e02800b6041d01040145003480c00c0030302d81880030124110b60311860851640d6900e0340355039a8492 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 652957697 1250 652956447 652956467
    0x9050406090b030d0534080c0619090305040905060105040305070e060f01030c0e01180f14030f01020918100b0c01020a0201050106030e0c2404030812060d0f0b091e0a0c1212050a 78
    0x5c04847c903121600109a6900c425085039818404842400b07803905158a41c45200c4185801d50340d2181040c0c01c0036601c40041c00b0251525060010034000000007a4080140501400c504100c0200c241049024400241359540c101030615041c42101c0d0005030380002c425081000034a0400006a8402e1013610154155044001402030000c800314000c038001000300c190030030035000c5544103106040701a08034000d83e80342c2c40d400000c410180d40700c0014030302ca85401040a1101c0ca0300b02e40d403a0f00480c080c1d4044401c410f02c594000c01c805030240d80a214944c01401c817400c003440140d0b03035040c050313840308140c030348441c0f058070450910200c0030b1880100440700d03410454190360390754990800040c96009090600003420f0644006429424401e0300100c105078070040b80d0b01e0b500c0180d40c1c0c40c149120010f2141c1840d10542188401c10201d0000c44005000940068010004c043c108003152401c039400626a141c2403c0341280080e41e020740c03918a8191701d00d0207a89600c0030000c212003540c20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 652958947 1250 652957697 652957703
    0x9151a060304060f0912180807030b13170a030c11010506030d03020a020c0301150f08030a0507060e03090a0905100e1b091c150c03090c1509050406090b030d0534 71
    0x114102e6018601c0d0807c0b241644041d82008085005a50b104c12941c0d42c40c6e1404010113252403000030407415130115219a550380e108080c40c000001002c2140140744e00072121010000f620703403841c0c0c0681500004142c02c01e00c1c41c10001d00c403901c0c100c40443e555070315000c50f01040560000d550800d0038801d220400b000e010040c0244643d04060950781c0e0401720764000e2138000f040d81440050f40040c00401c4a030001100e440301d90030800c4948a2000030a9180f8271702125010400501d5081d6880c02511741c003130290a4000034440c2480134214022110a03000785a844000780c090051100103230b0100c6004007a6940d809a8400c2124003080c10f4508030405411404031080d05841001240302c45001d241803885002c10021340c843c40100e040d02d4440c003010703000e0500500c0c14030071000003a048071040c940904207404050354407800715007181c3c0e030b551085100c1c6941e440d081480307141c00d2110000340c03542441c0050400d02d000c0044141400b0010003c410211001c011611400c12014035054443d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 652960197 1250 652958947 652958963
    0x11b031707030f1404050114070c1b03050d030e1c0203070809040e07090509010b090f04020d03140a0309060605010e0a2c13020f150f1303050109151a060304060f09 72
    0x30341c407442c804c0010140c82c1110039500b0f0000c0e01c8141c0310005601c520071121075680c5a06080940c41d00e912a0303083e5070101d07040240860010002c28000c001d000c241c12159a03000580c520101d081c0f506203e0b281580c1c0300e1980c00c0d0690f020805a0000903140d00c9900f2901d82e9948851074000100105000700401c01140103c0000050b45c408a034482031007800100002e0121546032000c10003082d004031800128201184041005400c3c902401c0340c0c120320a080a40900aa512107070a850304644e1003840042e88440c220401c02c9114040d41c0300a20003030808800c407a01400001c0d001403590f00504c0c0c102c3d000010144000d882040b45090480701c81d40905805007002d640150b860140e100003603000e103003110139042c01404c1121000c005052958403650070304094110b0980b49900c2500e56000407201e03180301001040d402e03c500c1c042c840c8680031059000210741c4001c01074580c00d821844c6141d5100481c01c1d40e81d2500c02c103c82d84594040000038903001750080110007020f8035030000d01208 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 652961447 1250 652960197 652960211
    0x230c0102040e090a06110304030f1d1e2b0312020d110918010605090f01020a020a0b040e0708070f1b0b0109021c0e0304060f090b0a02060105011b031707030f 69
    0x2400202e5068140c034083c400a01c01034071b1412241406100c151001070016420801d41ea400034450044c800c100315080180030200c00c01c0c1030001e01c041c03560415400c10403488c01c504910520f44440018004424050340f000e00c440d1505540e110751120050107424080312164901c00c000c01d0754100d600c0d503a0122005c025501e008006003c258000e920760390b0140d94a03881171000071005108c45812107200390703a1186050061018017aa0b01c84910b081415031180c40341103401030742d4a42032140a0b0805407110b40d03c031442d0031981141c07050081d04580c18429490107010916500490035805801c030340c2010400045202c0a07000f82100c504400b84c11440081c002084c00b210303d030000c003c9116603440c0d1860844001e03404034201c483c03d10815680307601c2000100310860103051209018400c0c0d041c034110441e6980e006040c40c1d8000d0003a440140c001d0070060204e9a044070241d005403483e845210320751080703580d001e802e0700c0c2d500000e0098070142e08000750000b03102c3d812800308c0c1e400046060120b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 652962697 1250 652961447 652961461
    0x402031014010906050f030601031403040e16081006020a06150801020307030b1216050d03030b2e080f04032003040906030605070302090a030b3d06230c0102040e 71
    0x8807000b07008990340740e802c0440005041c540881c1c0e110040c00e0003401ba21071a46151303100d04000810400c481c60f1400180b1001900d03511004490348116000f06080800d8101c00d44020407074000105403042c400c19000c41400800e0b80001c1040f501d640c0664002150140000c4120407440b076940a101698000402c2110a0354543c10020000d03c0a4901e050080a0101040c1c0c03509808a80d240c0400c0e5209400c02c41850718071541e035801402070400084070b99220000c15881826001c5035001340001054280c4400890020710380040365500d002d8045040500e590707480402e01900c0a03042190607908a00403420072038645401e5110790782104d030b4a907680c001c0c500281c100781c841660f54514000004031903034028005c035204120001c041d00341c1d4505581e15506030150142030b08111a040110b03140c40c04070340007038241d2112942c007501e25622410b444c2c020341e40800368100e43c04000b0b8540d091840b008913034000c0c229507200c850280361100640340c001802401254000f180d2004031030706002c01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 652963947 1250 652962697 652962731
    0x5041203051216020a060f230906070c120c0606050a08070603111305010f02070e01090504050c010e060409270828020705090c07060c02031801091d04020310 69
    0x18a024402e001405948010400b03910000440f41c2202503008555040001340c600e0b801005020502140025252410310881031883c0100c0da15400d080d800c1014850b10b40400c0041d69407000c224508030100f40c1242d50f810b020000c6035440d035400e002e105048501002940d0704200c01034030f80039041d8004181d952029640c0d0720003c4c841da2001c20303c0c0c550000c01414001003100d1200003040c2c2a5440145400c004403220344c03a030011901103002ea04c002017202d940d0880098000c1401c11408121410242091818805515166818803411031615138207a200c140c1a50101c031412070001030410b03c04003803200464005070018041441c003100301410030060101400205c3c4c2500712403031064010301e8070781c000500c5045003280540d210724001c006515048100304c2d40b15035541803240c1442515924035050700c142d01a0000542c00115130262458007070b940701282043e0900c0d00000007440c060b08850000e00c5005004076401c0c000e0002015074408104088010b041000708022103500041e000c20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 652965197 1250 652963947 652963957
    0x60f0b04051f081c0c17040b07023c040e010e060a140c030a0f0605061617041d06030a14060402030c090403050307121b05090918030f0a0504120305 65
    0x82c404588010039180b80c00500040d00d840701d03001250700e42015203010381d4071402110085030400881d1504524400500c00603000800102041585501c07007841004400c01e002180e600c00700c091754075801c119240c2100c00501d0315924010998031804000c0c04200a400550702d01c0c2082d40c2408022000a8000228180700342640e200030488080803100308240340c5025180c0201c00c0100b840814204041c5070310200c44480301a000148003035580c40450010b400208100c00c3c911112200c0c1070902c44040316524192402a086502d49802d0464442d20102d039251604280e040c0040010480c1d1010400c0e06100754100e02100c1d40c50000014040d5203601c120341c100d000b4002c080380a42c10f0300309910400d009650545a05013107540d5400d089440f0b40c80c107001e0b9080c10f41c5500700042d00640700303201c4680740c0c2c54035a10130b50741d404040d043c000d0080300a065a18640c0c0c120041048554020095405000841451a9454484040844043c080e580041c8441091545110f042642280c0100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 652966447 1250 652965197 652965241
    0xd140313030c090b010c331a0a05013501120309050306070e09040213050c041a0705030901140c0615030c0102010b031207030c140c030f0c010c060f0b0405 68
    0x9007441c0e114a850410381d02003031a03640c04921650302280c00100701f03c885003a1100154a101d0f03100703141541a203041c1d43c51440d0701802c00d9650b43c0d07004086400d511180b140e182c094036640d2816243c003000071301c10b513801044099000b0540d242c1001c98000318440801824121780b02e1043c65850340301e1900e460140003001c40c041955a88005401e00b008910284100d84948503c2c0e44400b82c0c0303060040c00c44c401801203900404504070380001214900c602c0d070240380b0000c0400c0d1958144035029000032111032403007003030110511140c1c0000d400001100e9111a00303103011a00101003c000c9501800b9560101c80940550300c1084005045c1800403075100a040b800c0b035291a80120059003220413409865405400c1409519400602d240c01004c071180703e464003081c04032140d101c3e00d0079030304c50400b41c56464101c01041c060b00c0ca810030440000110f844d0141a0150346140045d10300b05040d42c0c020420b5840309a15a24500c0a90004907100000f9005100317a00d0600c42100540003819808 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 652967697 1250 652966447 652966463
    0x40e1903111605010c02090901020d0c08070e15040303030c091a071703090d051806030406200307020c0d031101090b0601091a0301030807020f0a0b03090d08150d14031303 75
    0x500841c16900c0c0c540002c441c2c06071280303410b406075502400700b00d07800148006409e44d020468100007614030300c0f601c01461000c0e5952115400d010b64020404000190303468443e0b01078295285e480c11502088034216070303040c200058001081242602c801d1600d500205040e481e40c00c0840019081c80000c000031403151044210790350785c1c5003003034000e40000c0c0c603041d8290384042c80c00983c1d03d0140c1e0060000c5450201d1300035550601800050b583d80c4111411a140c6850f507801c2e100300490840c03d903859024000b019030542c903003050b00075a940800e075602c52003401c3c600410310906020b601004030050221000703004003003003810540c2e2503800555800780040c040c210006003549854a040701c002030301c0c000740c40c90b6900c0d50321410302c15040024140d07445084480c04074401e41c3c07281094401052000c4c4525264603104d0710080c04c2404826414041c131041d00d0400c04842a50b110703541c0141e80031035000588110034100604803001c4071000101a100020310803114120091103202161710070280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 652968947 1250 652967697 652967713
    0xc210a0c031103040819022a040b0d030c061515030507111603031d03070e2202090f09070317250308060d08070203010612061811040e190311 62
    0x4080b00c622080318050400740c014001e17040304110b00c00070803040368041d104865102d00c20002d003402101000c0c0400d001075094111302c4009080602503a9002102101d00303100900440d1405084002410801044295a40c04030203000032000c0544002d4030700d440e01741041448980380a0000d003402d4504001240302c034007029200c020005034924a40d8100d1440d60071040c038603503059880d0402e81401802503000403002c0e0702c25880c2001004002d0804a80c40f117800c3c10504800030002d040e00303117101c1155002e19034080144c5c0700e655521740c000d40ba8100c00c0c5482d580d1412401d003032150790313040140600700301d41d910000c0910000142c1409800864458000c3c181512400c00d90005184014040307070080c00013400c81c3c41c1c001e402c0140c0500440d0006d10f440c1e03482d40000e08548980d003000a1030350b0102003a10902410340729100043e0120101e0200000150326045205038018031210302c150f48030704030914050707028040c41c0c1e41c00883d140e500300903060926024000e090310403185219407045501c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 652970197 1250 652968947 652968971
    0x40302030c032d01110703080403080a09110f0105070204061509080102043816060501090c0914060c060c0a033602010c0b0a0b031b01080c210a0c03 65
    0x100031400084803a42c80b0150600d84000e00f4a00761500b0b0f962590703540c0c5050450900000c03100921507a803203035030740780c649151504d000380c841540903185008440c501800000050008014007400d04c504aaa07080781c0d5600400480b100e20131842c0082d00b01e0305096000500742100e2039407014110454032400005c9403900c01c0c0d43e080b40100d108442c2841003011555041e0750100030a00703041980300410441008a001d00e20342c1507407003042c40140803542e52241c0c00501140388140703400b62044170000d0000c0aa15a401480a0014064800c0408200c0101419980c480301100d810540f01c5050310020301d4403041214581c9c12080140e001b00703045c200c12a1038054000104888041080030000300ca20b03041c00c00140e800301d0444100d040c007051444c0c1c440410700d0884054440e980004001c1003105111050500b00030007070000c03c07a14840400b4248080c0e801014460b408101000c605854209640b62540648a02d1008840182c0c0300c00520a80b60442e4020f04150150350310103200b4000c00307031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 652971447 1250 652970197 652970203
    0x70b13020d1202190f0605100e0c04260c041d0d03020315040b0307030f03050d060810060603050912030603030930060f0403110c0306070e1503100b13031502040302030c03 75
    0xe4008005e5440d443c10000029241d600890300120f5481c1c2000b8400e4444a08005002c410389a0320200c3c01d0100e810011070211010700c49003c4e1844040c50310515600c0035541c2d5503035159001c41c5c440d0340c64080da014122610003402110403c00001c031a400000001c01034025407060781c1441d40a40c0d41d103520401410140544c1020650107002003401c2480c54584007001e0200500c03c030104001007020b04101c03a07850081b40f01601c07204010348540c152200e041d204031780081c2d2042052600b04010480321000200e1406d0344054a08503160380c0340d584000090035840b50b00b401f42d90050780400400d40104050b001d404856a0b10200140c900394540b0388150b0300c91045500880041c1050001800617101e4a00842c00104d5034044407075041030200004e041c2036080f90340c640008c9028003001254a00130f08140c103c0c00000110b2465030410141848030b4903d00e028000401d03038001400300d0300c40384804a0000458000800c00a4100c1241a0502942c4284410f9109105110000082e89408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 652972697 1250 652971447 652971493
    0x30b0c03060a0e0a1e0b0127050d0203030d060b091306030206070809031e0c030d3207050109080d050a0c0c02131d21040605070b13020d1202 62
    0x42c100d15045151090007030049400402e0301d11010b0b100e1082100580100c40b140710140d03507851300425145540400105404400409612040004490081102814441a829100f095900c00080b403880d00109165205d41c1c0c246500c4035203802000503a44000070041e0085540440e803a122003181c850f809c00a0300e84a01010703502074020020600000c030180004e050a10000d8262291402d0000c120030070700e86103d04500860700000300100740741c6401e1041d501d10108508080c2c2800c101d03d48207140302c817805181d09a4040c03c20300f013205612030201c01c1c1c800b06c5500400a00416076035107400d00268008030307001035145082c0f0000c034400c2c00a13401000c89094245c3c1e035441c1d1210ba40c0d020010719210901c0844c1910f6078070720020201611020729112007551a8004000c00c821459400c10928a00500420101002c0c0024004154800102c80156401401d80c03141504c80411440c0d10740d9101c43c2c0290f10a0142040000b08960b400043d03640e001d191f000c0e80d070009698450320442040f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 652973947 1250 652972697 652972699
    0x506030406020c071d0f07120203070801050102100c08010e13051911010504030822090f021309110d020c0114090a0b07020102040b0d05040507080d020307050c1504060806030c040213030b0c0306 85
    0xd0a40006d002c114680503150380110305160400002c1d80e40c1041c00c0480e84290344000c00249140e0041c401275030100648100100d00c42d1040144900c0018000e05484060090b801400c3d0032130041401000f0301e05002e0102c5800100303664410f0480c01900b140b84504407400c48104018900b514881c2d80680140e4080300c0d041014a072a00e81c00c02c01c04114141c00700750010130300c20820008a544d12251080d007908462080c40107a817551081103108030b5141940c46248643e083c056103800d0420038000b0703280001c1110074056214002010180e01420075031410b48000304141d010080f40d17000010325101d049000e003035503011039221710078102d083c0d118a0040e000d45000070448028511801d41c0310a40c098001c0c410307103001c103840d41c40003420a20707810700800042e440440c218050140078000745604990444400d100b40481c41030101031030080e48211000c0c802100300040d0385440901540148103c010000c659a0600754040b4502c0c4c0040c2c04107032020740301d4600251006120300100d0f0f014480c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 652975197 1250 652973947 652973999
    0x5070504110a031d010e07050906090402030d0c0501020d1b030c231b100605100306060215090c090705190302040b1813020c030406110c0d030e03070506030406020c07 73
    0xe208207068000e882d5080100c910740c840d20241813504d01c420b00c1440e0009030020081c042841c901410443c2404029149610a01001040c8001650b0000d610201d81c9100e08240848450b107080144c02400b4008a03134008504021a2804044010041c0d00039080c02d43c03020411514100400c45444004000c803610b20f188245c0442a441d44110281c00380d0480c280520180c3c501c005d4845062285c0c80310108206900c400051120303180551001d14424074502c0e0030885182b5140e0001d50b16001b01100040d040b1780400131404d451307030130301c03414650312005400070b00542000c403402051a030010312162b1004030007108036004a0700c680211000c4842c8400d0160a15444a0099101c3d88101141c0e5500c0701c10040941d00b14075050015103010f401000180d51218a0400c010705250710000529180ba00b202a1412007562101000d001c42501071a108a40c662000082442d116050700300076803105020080104104540c5c00402101d0344500595200300d9448412203c80c0a0300c00040d40014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 652976447 1250 652975197 652975207
    0xb10030b090408161401020c0f1504080f071a1005010f021509070f0b192f030d0f060302030c12060a0e030d0908070302070b040b0d0203040503070804120507050411 72
    0xd50490301030510b1000d5135006400307442696468060500540c540302c5000e075000304404103454014007a000741015800c014010003140711140c5003585c1002080102030150205440074031201c01002d44124541c032100c0000c0b60002c050703810301a030400700d400ca03c0790440301c4808a000e51041c1c00c039410002300c03900240719042c4204400c211843c401086070780c0c45e10032100c00003450b0300d031092141c0c0244000000f995030344131002e02d0703120410004000300090200e186003401c000c62501c0d0305144e41d4181d281d90609481c142292081c00c41c417498954130b480c58208038000228413040d90007001128070803012107a000315084184070507004004058062504014000f8845100c1c0e41c10030000c214046054900e480443c42e0800b0441d1801101074540900124071032042640400544002e8804504654142842c041c095201c520038509071203a50f50700800441c1c10030400b0015602c416500044168946031285d050100d10070050406549030b05c21b504e00003c403418140b06510701c8003d41c80c0064901 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 652977697 1250 652976447 652976453
    0x10c0e0f040e0a1a0a02040f120201090f061107090902090c1605030703051b06041e081c0b011202070203060402151e040f0501030b130507050f0d0b10030b0904 70
    0x4048080c1000d900191240300010003071009002d0880340780c0c031650f0350b001804a080031640c081e500040190b401c89104100600180980741711103400c0741c00340c1890114451042c80100c1d405c420036840b03000b42801004022980d240c001d0010400c00405804a43c1865514541141911484140603410424560100c0e0303d15404030000d00e4094903001c4a00700d1640981d40c1e0300d02c0e55011a0060b00001c002242f81c9482d02216070841e00441c903e18000c0841e41482d071140103100340840b282981c8a001e03107411070b04010074a81900c6030350380150b0700c461140e6500b5441e034001d000381d00f11140c0003441d05d415a05c280c41540c400d40c1c4445401030020240c9a803241d0900c0100310b10002c0c1e01c0c0030034200303000044010002e0f410744803d888035400401d4455240a610407500c58250700010305141c10600c49480e19160081c0a208101300c02e100480e042d01c4241c02030703660b8865a44402424200007500d1018044680c10150708903409503a08418101126404c03812100c9200403d039110008002107008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 652978947 1250 652977697 652977709
    0xa0b0f0612011e030807050d1209210210091401050c0310050603100b19030507170f061c08070209060a080a0204110d06030515060415180609020c0102030a0e010c0e 72
    0x7050a03442600a540d44d100d850303d00c03071601b0018045542c1d51240ea0171141c2c00d580035140c82055000704074103109541070340d504c1850007480215041017440910203108171092013005842c41603801904100580340301403c0c4031207036820100b9507005960801c1c1c0400c529000c000102c2c0d1240311840240c1440c142044c0802c8403551016004504441d041e00000c90000b03d0800205412070440d0299038403054825406000d85d40010248418400840d050100130092142ca0540c010b07902014141d0507680d61001034194528400480c003a01c4031124540d08004d00c4200418000e0b0085a00c074400f582c5480400c001d031400350041964070303046080d1240045c2019044404000710701c810b12170402c6080143c0804a4200d40d1080d110380c0e0014444008103034480d01c102c1d8002200b80d9042c40b000c01804030040440c0710b10700ca90758040f0920f1903269003500b684e0303219002801c80810195500e1454506e400d0103504203986461300249041e2960b500c480051084081c5106543c880e0404650071104001d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 652980197 1250 652978947 652978979
    0x25091d060f090319170c12060105030108250e0709091116080306010e090a06091415011d030307080c06061e1003060503060f0403140307080103020d031101050a0b0f061201 75
    0x1813140307100410f01ca1032469000e171762054115494241e00d03816075085039240c0100107802a4188441000140320f2050b0102d81903202280d81c002034105a1169403c3c0800c1c9200c59001c1c0301071804e42c20a1058450f4490140d60854007054000d1012415a090b85200d521881d440c035441c0c0c4107540d0610002440e518081d507881700050410582c54a20417001c5014000300f00c0340108d01e56030b12300080c0b2465407140b24031081820340040801444c68218a5041c910103420862814000300a0514124205040d2590b1181c0e1010742038070303101c01d66450070a0303d41c1c01017002c50403035005400004000d130034940280343c600b01603903002600e400c2d402028406440d108070740000415031901d02c04541600c0800ca00380c002c0c0300700003070900b03545450708000303114907402c0010700d1b80a8010002c0c0500c55502264503810740b60105d8039030f92006160b00c1c0980f819801e03180341d021a94204010080300d48510750080b072200d24103485881c4203940354002c0103403600c00d05540120f5a42c010b801802a0b45961b05015 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 652981447 1250 652980197 652980247
    0xa0915170118150e060606091c080706050708070206060307030b130c14180408120a09050f060601081008100e01021204110117060325091d060f0903 65
    0xa104440080d12201d0030303240c01e07060341c3c80103d02c0d185690807682031060031040c0e4041409803980b814030000040c0f0a101b04d00400d882490110051030b15031419a180c4180f09503c4070441f90350303038103500d8268044d000454004000c81c141e5000101111f002240041c481c540003401303000c05030b0840e510000c1600000e051781d802c09a5141614000941071030540d006402200101c1004607600802c00c042c944451030042c04001d490750070321000903549004c3e41d16401d060500c401507541e07560300c2d003c003d10320317400080c2083c45441b60808034074201240c144d005107000c0e038175607040340d80e407015400e00d034003c500c206941c5134450801903d02c403926501030700d88400c003100050300d8203140c06800491510155016920040c081d1051441582c0148107603914104215070002546440c83c0020780b40c0094400d0b0180c1610400c194030898242c0d000c00c0e031f000d0002850100031800780000050458001c01440c14854400c09020500340661804a24410702c005401585084174858000c0c0e40120b80ba8451 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 652982697 1250 652981447 652981451
    0x13050f0d0306090b030a2103150312030605010302031012080d110c0f0c0a03020d02040b0406180e1b010f0908010f0926030a090804090204140a09151701 67
    0x95084400240088003002140d41d4020400900700f42801d41181d581c003004074407943c081003001000802401203203940e140d11a0462400f40c0f06a00144c000d0700e0161088044207201200200400c030103043c074881000c3c2c140da400c2011548a40040d8128441501c2c00c40d0098280c00c07040020b0080c42e080d4000b40c610511502e4140b10303203c403a4406039408080340c1c09121101045d401e0b1500c6003017226481c07110b0054014805004020045000d4484038000a40035491a85410040d5211a0028880424054001c0080555540d001043d5010560102c0c031400d0a100d44201e0341c81d0f00154260707003582c4080000502420f00c00041d140c407521b1411281c1806613900002408590a100320b000007071300345001050142a83c5004010351300b034614044040c0650018041901c5010700c00c1c1d0b41d100381646070001e5080c10504060b41e603405035a0001c4203050000401180c40601001031404180f01a40c82c400d1841d180c14094040c1d4100c1d4041c40b00d40341c0741c00000c1214803014400a2002c000417000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 652983947 1250 652982697 652982713
    0x406210203030f03090a1a13110301021902010608120301031a07020f2505090f1603090206031501260c07060e06070806011206081b011106040c090c090501081305 71
    0x40c010f40350004c03180d44c6416002205000240704101e1034180307407140d425680c50300c80e14091500d0902080d040b54041e0a4140c1201c030a20306850960440708909049800d904c404000f50703000a002e40350b42e0141811500070380000312514003c2c007061f28143d1b6406800030982500b54080e1851402005000f5400c6201e440a44a440303507050140591f0170314410064184844003007039040e040d01495008900801c05641001044040c0c4207040d80c1120a445030500325031f5080c94202e014040c034031400782d4000e000001748042401a0445c1024080e400c1c5c070755480f801492090f400d05290b0194144040004c003000103045c0402c0d013802403400610032400010f480000c007000301d15004040b540003012a983c1d5081c4070541d03800c010001c01420181000b0321031181801d11168540c81180e15004030b0143c8154040100c0c1e00440d690281c040d803030000c4621518107030804403030700c503403603c2240907040c50301d41c4c500d004522034481401598010b07103400d034040c2c03501e003400740c40043c140c0010344090141d540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 652985197 1250 652983947 652983967
    0x10327020402120108060f0c0a08060904110a0f2607330e040506030712350307030f02070b0f1906120c080f0a0b0702011e06090b040621020303 63
    0x3c4640a0b2220360020b20a900d00141002503140000d0110240300c3c1c82400030648066100020a500031400e5500554646403440c096880820301c515607a8820390404012441402d0707104000119850409098a50000c1070f600341c0d0002c103104403400309030b0008503042c0300d025604000d0444d16030a10b00503004413040c0008443c01c0c20600d6a20000003103960301485183e262034020b403a0002c1c402c0b00900712403440c1c40c031780e8101c08003d42d0303004000200391303001c82c0050300c540c182c807007404000307866280c0428800520900403607000b00c1e0b0580c086898401449418841032094425850380700104189503264500440e8038410020304054031408072003440719100340c0d01e01409000f0400c0c2a04488907030070070300e03100a00c4540ca4000700d04903400f0690b07040ca58000050192007482d0441980c0d00311380c981d079104030f0141c0000000d11301c00c00100e03040a14580c2c41580503100301c612a074820004018140308000540d54144175900c0306006040f881d400420700c035686400400c1c4000d0443e8907103030310b90f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 652986447 1250 652985197 652985227
    0x20606420a08010824071d030f0a050f210f0d0e031e130e040c030f03090905090102090a09180c0b0405040605060a0807030f0e10051005010327020402 66
    0x1a14040028000b00d00401400c042000b0901e4002c92041000ea2241442c40620400303020052000d800c01503092030350003a05009120710b00d003000010b001c0d41c18106011030070a69900078110300312190b11031100e0400700a00041014014a0301400da0b141404462440e41049500000300000f00590108018814040c462085541c0059440051919070400380c101c8010400b044d080140700200400145202c0c1502110720019641c2a80f1070b0646070b19070f41808444415250001000c0c1444023072440c05150300500c912084510070070040c080d07940c0d90141c4a003070380122003a06821043e510028800410580c00c00320740180e400003915400151030311241c00d846450703805200b690100040c01d1085007172501070703100900780960710103280c02c15400c402060081e006080b002055030741c1c1c210310010f890f0703a000001c81c40c0008040390620001c8101510017403e05503501141c2030520400021194003034020824008401c11500041052540c00d10340010305030b5500300d81c081d50800a90305003070620 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 652987697 1250 652986447 652986457
    0xe091b060313030f09230405150f060f04080609060108012315060d14092b0503040c030204020a1206090e0d120219020d0f170105060702030f031902060642 68
    0x41030f0900f1ba460540410b0004a59000e812020110340b0302200201c1c5403a440c080900390041640c1842da1580c03090380d2140c10b800380e500001c0c068007841060010014002600c941070300c40000080141c407a98450300080344508149540003080600d001459a111b0580c02101804014251516000785c6210701c1084070100c51003800900900428080004001c00584002e0140c80b28404a8800d03030b80c12401002540141000800c40000001005c1041030101d0400459000c0c02c203640381c02c1c04010140140e003040c81c0400e5168600003000a0b50100760280445103c0704a010b09409803100380d00712080320142d031800341d03600e4081183c1090340c8250681c111060340d0b5a030141080e8815500d0060003180d040344c41000300721486a0f408000c81541d0501c50441d44101c0d00b4545d40c180c0ca01c007103414410359050790300d41404013180d420541038440c40d0032803085507560300b130700c40b550303074000400865085802c10791411814019860f0004011110f8541054421001d400e07c1102a450703120a0f584c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 652988947 1250 652987697 652987739
    0x2030a0f0e011512081b0a12080a050610050a0c03050909010b0a02070915120f020315102c040c15020102070c06030903020d1202040e091b060313030f09 67
    0x540c02e50b0f60409200c0c22210800740519a0107095418000d4403a40100c3c040c0b070400c8050112024560051203100300148042d00e42e001030041285501742d0406443c010040701c0451180e07040c000041d48524100002020202e0903031500c0782480b0740d40758212a0524000301c22020f03c02c0400c550591759036600001c50080040300c01040d5110150000242001c08a50001200a003001c0fa1a8401000c50160740c0a0b1100d019554240803010b00f816000b6062201c1e0280d0140503421241450251a5640b940f0600680d1076460f1001e6030340d4104000451554a00603900310544001c960782814200780c160002e00034903001130b1040c0c60302c2d0508204c40002500202503940052030008106072011400c000308030070f00301000500c3d45a140a51102700d1001c20108100c0703007882c404022402c95056070b01504298980030f40d1460316450455550a21225103140c9240030b10034a1454074060085034403810682e444a00058082c0c0c0e401d0f2510200b8240c0301c130600091080205100c0d2400a100d000b20304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 652990197 1250 652988947 652988951
    0xa052101090e0303071d04140f0106030e030a02060a050a110412050105010e0c0d0507020106120503040302031903170c0409050c090910050612060f0a0b0310060306150302030a0f0e01 80
    0x450002484102c40820342080030310f070004d008100c4c00390340100c0d10407410026811711682410100b00007500030711403540b070001c0305810710050001c0c0707207103038001c1754140ca1090310200009443c803000a80c3d00c0c0640400100140d02c5640000c060b007004c1c1d006250800a0703580c1c08102c00078000300005494003e03030400803440350350301078440c2405001d01695005005502000c0101e043c82468600d09d4031412601c00041900d40c4086208180300b548030308005d0174280c2c1c9600790741c045440c4c600c6e2242d00511007684079100384c0ca04903504580c4500500105a89900c540074034040e0354013202c2b0342c610000c0810200d418117200000b00c1529501400744262491601640e8880030001081440c0c0d03400340410014041d509401e101e103817110703001c030b50070698440c10050441d6504800154003400100482c1d1b0440c0f008040042c1908402024600860914520440c410b45600041302181d0703480c825051811500480b124900303001c0d900031508801c007410042424041c6240c1d490680f50f41c0c4840c252140c2d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 652991447 1250 652990197 652990199
    0x606130519021602092409040f030e0f1e0a0e071b03020a02041e1503231e06010303020f0c030c06090f0a0b04090c17011e121101111c03020a052101 65
    0x40085100c4412050341200c40c403c207400d00d91503125010122740710041c18000c04205d49001c9540d109401c03103002c20011f01e03800c000300d841401550503c041c0b000c0c0701e00a03640b04101040f40246030b460144a966039035516009001d07142d01d0560b1620fa0164140c055010302c40c2d10001580701c41c01280c00c5c00c884000c10b0b40e220f00594904800300c901c4100f0074540941248418800108d094100344e4220324402000c00382461384920660811060b041e0548a11134030a00110702d059010420038101ea002c1d40aa94407a0700a8500c5500c2c1c5d162540303116450341101181250915004000c0c3ca4481c602800c1400388456800104062041e40d4008018810001c1410450755509000361009020030385008141a002c00c080c2c04443c0e241800307500c07803810400d443d50584100100c3c0b02c00042507070100c0c200c9030211307a061644540411f2a4580d0000d0180f01010149001c00641c200244102001202040b00329020071402034011080000422804011440304207017130405003054207040035003201d001c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 652992697 1250 652991447 652991491
    0x50a05010f020c060c07180504052505061e0d0b0913020d06020d09020910080607050c0a03080a06080f1b0a05031b041508060613051902160209 63
    0x400115842541008200d00040c040c503907010038a504091000d580c0d40e900c65550003151414081150440840c26504010701c13007014945030040790141e40504151110507052205074403900c1641d021090800810390b20802080c10803000130808141004c1d042441040000108011540701e0340410713240c4d503255281e46000d85428003103141c00c940c022a0f040030b2101c0a90218020600740301e80a0102a400f003070500c4500c407513401c03001d40c8540c0100452001d00c0c10400c054210f5001c0c0c003c2c0c0256100710000101c0d243d002d50100d032001955a0024030f251615540c0071501c4007001824442c6039600c8a5000030846030030030a003014101004007504556484600407a00440503c00c518840c1a50f21002c00850724040340b0b02100a03652400c00041c2c00081000c03801404106120390a20300300140005407804020078418000c0390220b600000200401031000103681d0152140702e442c1507a03441d45080349200398028290030401c02a00f0350300f80307950b070001a5490720032218200380781001a01c460351 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 652993947 1250 652992697 652992709
    0x503030316260711010b030a020d1704030807051204051f031508071a090a0b030916120506090610061b06091b060207060906050714060a06061403012102240405 70
    0xb0b0b03c4c9042d8000c010908411000a41d036102501c4068003d0304000e2522080c0400d02d16a0140b06401c00380480d80c90f6501d1410351403039440b0300c00070364285c05821b081d9102134a94004890071180010104001009070b040c281c015075070745c240307c4418075940d004e081903a80031415150004040840241c44000e25107802d0701136144c3c2c20032425820355030420801140e0355a05248005031003020715141d481f0b0f60782400403494005107001500c0c070a841140c0000780c0d15800e418202456108030306565641d1070341011243da4842c1510041658035140206126107845a03100d840030b09800f240c20000d10015407500c0045802020040e00c80c11030214405100c000b5400954009249030720040025510300000101821103034066072080001c0083c68500740310000740318540712080d1100351111402d00d0f003460301c000c011900c40d080c0807a0354140c80f2000c03020901c0c10b4034102e034202550f00c1240607882c0485044d256030309908903480b42441c03088500e04186007400e51900c800c0d01110035a60383c2003a0822032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 652995197 1250 652993947 652993967
    0x109030e03010c1e181208270d06020f0f0315010305070206070c080f04092a0c1a090f190308010b0304080a081503010c03141005030303162607 63
    0xf044c0101c0b210b45122400304501c28021110003842c050300040f40081100005d0b42813a40721a01d0600035840441c144503400c0010901580202c4403000d6582d0242c05000515207441c02c0641c2c03001400620b000480d000d03400401c0c0310402020300c24984080385450340c4182e0400d44410090300b070384928080032960180304440c0c1100380d03800100390a2810341c0f0300030040383c07a010b40140082c001040e4400d5100c544810f0b02d014000500d014021b482141561800030042c1e40300328504403a103411100481c6009280c84084650030000104040f800b1098410581c940a8284002441254071008080b1000c0c810340c09090460a41155590740074100207010980c10b07040007031202e008005000014031241c0807510781c0120390600352000d036204481d034003010f81804140740d019401c1921080e00c050f0b040e841070340f241440310a80300164940c100100f80b070300640d018580d05984100b010139075002c040c200300220084c0c0c03880d00d02501010100b00140008140800400f00b202580c18411003581040080d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 652996447 1250 652995197 652995221
    0x7081204140a05030307060e010908030903030f0a0e0a02060c03041e03050d0305100303200607021f020a02030f0f04030204060303090e1806150406080105160207170a081b0109030e0301 81
    0x18030b80c01d0509000980700d109080004088035980c1e44122000b14081d044681503a0b0400d503500d07201c3c80d0401d03000351207a10440f01c421806a80100241c21140da40c465402c000103001300400a03400d4035801d20505034010710156084c2e07c42808001a07000a0050f90000c10010701d0310608030601c1c518009243c554003804040525007840c0400400c03010301300700d220440e85c251401c80e55000040704580a20311041400b03a049005410030083d042d034002030b03402000c0030040c1e031030782040c44800320400403806645203400c0103801c02c0003081c8081e03514002804081050b0284d031864203075030340d000408541599004402090645508000340301c040c0a80c5c95208108a503e0030501d81b1106881d6101e00c80104182c7d60740300302000300c0c01e0b02d80707481d80801c01178200791000304218140030402c0310034181402c05a40041c40707480408181ca98210030403a03054910705c0700514078015a6550145c007030b0000d6603900b0980e2264820042020001d000c0c1c00c1c04280aa180c00d100481d4910615095800070b007030301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 652997697 1250 652996447 652996459
    0xc03080108060705120a0e0f010e07080c0a140613030303143612160c0b07030801060c0809040504060b01080a0207021c030c020a03151b02061303020708120414 70
    0x10703c0ca0f8001d01240c0f02c07000f058504103803e039500d4020200400c0031483d00c91151282c61001c04a0140541c84020300c0c5803698121552555114000c0359202420360b80940c0044c854402044000281e141031803103100000c01c903d0502340d000350401c0c0c105110307900580c00651110030414000c1d070b00085054124a101805601115001400c9044940c5480c80f030b44151241031140c0d51003400038000025003078841c190861b80d41c0c801c01040b40194921850580d500e12020500051442051081300c2c2c0301581501d4200c4942c0c03030030509850405240c5401d03603d1b00d8003003020fa1101c0d540e034401c9c4c0c4c0c41180700740c4000580d10f629100042802d10000c01102d0814410445070002d60384500b41c001c2040c000411045112070030785000c0320804c0c10944000c1d000321030180d0200c10002c025124030a500d420700004c01c190740c61f15001034400d2900c034103403c015804c035001048090860000c0f0b140c90134003034011244460b545a00280c0707862850300c20021030a0780801d09100804508141071425a070071500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 652998947 1250 652997697 652997701
    0x305060a0605180418050f07080606010206010e0c040314150a0b01020c0411130b0415030c0906181e03110d08091e100503180f06190209030105070c0308010806 70
    0x1014080340300b0900e8400c8003803c50303c040c80d21981c80e81c008030706491640090813607590441c030707213260350b544145400b009a000f110004121540006000c510a0205900903c1913907c2d1441d0303022900750103001e00ca100501008040042040410049804010f5038000d0a400c2c0030b4090820915501500041c035250914a8003501030380d0000e035200f42c104049a00242114040e800e1440340e00c00c000a9440f0880320003400580750401902a00440e134120307500448040c8220405ca080740c02c645905c801080c807943c001c0c03140070702c286494407400c1c0d081035100b00f000c2d8659801d0300317901540510703088501c60705079014010040d04030481c1641c140284c41e1544103009907078036070515000b1091081e00800c00005040b0022409403050900001c020308410186024500300614903801210301f2421002400c070041003100001554140c03c981a20241c038907900c1e2a4501c00076132810110610b02c40740c003400b0705d4486540a20034140607107142d480d5542c80c500b09180180594405a2000d000350f040039007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 653000197 1250 652998947 652998959
    0x702030606100203030a020901090302121510030b13050a0614160903050c060306011418010e1c021002012408061b2218051801180f02210105070305060a 67
    0x1031700d82000708402c1c00760300c035408440100c8594500d58406036003c44041c0c000694400c01040c4081e80410b50b055403002c07507a0350186040e91200901c0003c01c0340c0c41240028055501d040008682e00b07200d5026901c901003d070321a1019035101003244600000c0c1c0c0f40c2400fa800b201c80c0300c61000031001e810030a401d50310b5038581a80310030220400900070040000011b03a10f81c807955a540985580c0d4100b961100401c0b0718610003601d2006442340403c0c0d440101d86051310345030030011000b204402603581d00102560902101c4100b41c9004020356417100718095821000c002d250250001d0300d41940d0600b45800103407840d00f0000341040054003d010140b000e2000e110b411211801c5c0c1d541c050304c68000150510314010001a032015a05041f507964074412840303550072071402202143c00c100c2c00043c11087d998200c80309a0050162203c03080004c5000444000140c1800ca0005046c3d940c003000d24400e00075201e038403601d140e005075035520801034a29054817074250082d200360303400c240c7d4504201c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 653001447 1250 653000197 653000203
    0x5010909090c090c021c020102090a0f0b0315040605130b0f061603080c0d0203070c02030706030b1e130204060807170609070507170c010603052802130605041107020306061002 77
    0x4000c0183c03568580640164240c020041d1000d0242942c140080c4698400c070300a0003500070381e8409100721100107001882c480031000c0030060700c09010072945182c481025600300101031558107038005490307180001c0d9641c0d554900090b680c1a040340400c503400d48804001102c0c3c4a00c105d288680c00a224442d03420340500050384002e607050030b10808540ba00c403d01a0140200038160340340d14000010031030105c0c0c2c02440003090350700c25804c403a030701501d0300016026034016180c4250000740703040281c01c4418180044078003400740603103610b842e609800e002c1e009070703807003500072030049001c010500c025903510405444109040000980f1242021800904100307030141c500da0070483c001c90303210207206c04207070400c810203451120303990f50b00d60f0304006502070031192200352040e002c0c1075540491070f0882034108400c00b00f99482180021465420040c8040c4c0c841e418044040d5071f80c2020503103403141d100752035078241704160040d00c0b042c891042600d405801020680191094108801155000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 653002697 1250 653001447 653001449
    0x1a03070e091e1c0f020f2b0c0501050106030617010603120807050c012f040b0f1b100207060c440f01090e0703030504050d020406090e060105010909090c 67
    0x200c0109081000500860316002c074000015505034840040041c9250f0807010241304800c0903000c1e11300400000182a0f119640306422940f5104003d0746003500400030340f100d802c480c20300c3c100500100182c1c2c40342401c40d41c00b43c0222002c02e9480c40c045c02012000e022602e06011064024041c05045075168000b0024024a5200b801800301c00305030094011001c2d241d168803054001c208550058104214401d031a410f1069905d841000581c25160600b04480903100042c0e107840c0f500d4510350710032240f9440001511000340d031001e510050300b071043c4820442c0c51203123071016881e081d03a420401c0495100300b22030000d2005800801c80020008002c4840040c00c0c204410079040701070002e4207110002c1010701c01a5080d080400901414150f2013a060320004002042824519481ca9603074404601014000c00c0b401d000400a0340340103d401d5040c04e00c0a40003051956907004494241e90004001c078000d40c01600042c40196800700c80d82c1d009001e02c100911071100340b51220305421880d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 653003947 1250 653002697 653002723
    0xb1816080123010807031811090709030314031e01080c01140910030b03010b040c020115050109030c0e0a0f02040308071406010605040504230403090e010e070503070813061a03070e09 80
    0x8130100140e4000c0c0240d010b8031480c60040c104640307e18091078000211608503600700d10a0a14a0116551a103d1100c601c15a545030320b4951790154503480e00302490300014184d0300b00b454101700744a0701038a02d5800da4000c000e03000061268404110015200d154203000340030843c031090002d00050b07624198105851443d07810001001c079000b80100780500700c1d040740303c0e0300113040010224505030305600c95110007045a8000c6403890301e51004548212191202500006240d00144040048410030b06e0300400460700008c0c04070070b0803040c08240d0308590700c2540d5885020840c14240700c200415400c1c0c05119401030040c541c10071002401c0c9005070300800b80030f656201c0a0098201c80b2582e508409904c80c02e4241940c0342a150080c501400350013070030010065800001071a0300c5104005003d11900e44541d400c556440c1070440350124020501714004110725080c501180e824400e00340401d19424070b22a4100201c414980303802203d80c0303d403d0480c030880c10040319900101d02e4100e1469 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 653005197 1250 653003947 653003957
    0xc03160603050717150913080406110309030619050a060e13060e03040e19050402010f1d151e0301080a0f021816030615120b181608012301 61
    0x15080360466100e003659500003680c00040050046080c01801c040c800c0701030441c2c0c5181c0780e587d030030050810651000700042490170203010500c407160003403c24503107400c2d0200850b410008035800280c94190140c1d8250001e0120b0700c00c04172014050301801e0350104000409202c40c41c5000030141510800920b00c107002d480c025001070410410350440d1a6031b003110001c498480e525480c0d1014441b80907188440b0032a40f6440c0c9080c0314401740292481160140c407000c90380750b0005415101800c6600484803140301404420b2455070710b00c0703481e601c25800c402e40c2ea615a08601ca0144602c5000503400100850500041154a03c0020458a580c1e4040c1c900c59142c40301e8408503100740880c03400e04506582600420079490741c072541048044106580030301c0502e0356002c00f51903129010740381c04001080303121001d81c1d15a05821241304407401604007010424210340d100c11090301901e007488122044040c0340e614130340c03100700180035001c0d03682507414202c0c1030b507840c04140901c0d95080e81400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 653006447 1250 653005197 653005201
    0x6180b0f100f120f0506030706140f25050604020111150406020a0509060d0b01030f1a0d170705030d1407120506030304030213091b0b16020301090501060e04050c0316060305 76
    0x2e8462901c000250300941c0c0b091100c40050038903180035000c2250f40602911036400001111485040d5110804030102c490780d240a150400140c243d070b0120350764120120000365201002459031074408983c82c0130384c0141c4031074140f81c0700050103000300c02c0907402998400ad940d5400a90540c0d07045821650021005039070301e4112806444500440000030340c8208085210403403a0300540010000c1a800d0303a04004891401e000e6070f0484d606d1001400340c010410f000f0406906203c00c20b00c0095011b890400380c0f0283d0a000b0140d00e500061040b241c41e040440c42440c00101801401074140101d4002c43d480d02d007401006000045003000c0e210f511b42c48002040c1207131000e0084401454018102e0341c2040340000c25000605402603044800c8200c80c0419021442482c0c4d480c0c09071604104910310f84031284001c200b00c861031400581e4155a02c0d00c0350000103200340300e00002000d00c00c40e02c2d55145400d0400d2402d1808660b10a40179400003a07965582d00740820102e01134030720904000600da = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 653007697 1250 653006447 653006477
    0x907050103051f0e01090e01020f040b0a0201090501110d050f04031403040f0516080c01020106080d030f1103040b0615070206031810060e061201140f13050106180b0f10 74
    0x30411034040c01c06009601c83c00460742c0401300000c241a5143d10384244400f0f5809000c0358200c0c801c004c040c5058a00c02e00c028030101440c00020305426140d803001040040060300c855003100d40d5017010807485000014490304a030428000e0b00c0e80924980111003040ca0070b078402030058141455400c25099001000404001102d0142a80300780c01c0b83c111007600d503820300d5299070100b0300d014400651240407041d0100398414003841081e02c11003006003505070329502c0140c0c040c1503103404845041303485000d117030100c04802d070107148900d004414805080c2440414000b0f0200b40584010083c1000c00c00b0501503200c0c001201c2d000f00300381c001691845c148060650410003040e0b540d01c03416080c1400001c840c81c2060444d40212012a01c0a40040c2d448540c0390807540c98500344030074505001c00103032006000001e0b00d1303813260030111030240c900c0d1141d03205400c585058226080b00c488110908010090074810b01001c41c1086d140034540d0700c1280d00158440c46212a80c10801c25883c40c101c0c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 653008947 1250 653007697 653007721
    0xf0203030403050d0309110409111014070501060303031527020f0a020a0501060506131a041e090c0c050a020d05101a030606031c0e040b0a0e100b03090705010305 71
    0x210f030000280c0703284c0e5140c0d000080107000e00b40c1060300e41c15200884102140b5244c801c00030080e40c400880d4441700c49000074001e4803020994501706008940c17020300d1000c88010018050786100740c000090b16825403030081c00f119080d440c80c941c1c2c2d0000160500040d549c0458040246010480501001c0a0391010601071303c2464003c0d03590442c08601c401e02c440c1c00040e0035070400d05c200002c0c0240758444040c0f01a85c042c584061861007140368081155500c00301d03007003400d41260042c491804d900c914009100c00801c00c2d4000810400f00c0c0d080100b0f1109100310401c504181c54041d03204840ea4a400755900c801e83c101a120b89100c0c2c00440400c00d04101c459500c60f010703e070512401000300e003032582009840010034024003c42d0300040852401040303c0071080c031a880d0040361138441e0501158010a8100c2c000d400c03d590b071070343c0d1070596070b01011200141915204680b06140401394030707041e24541d500000c1c8458090050202e0181c002c03c281084d10400e1070001065503c204a20709 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 653010197 1250 653008947 653008949
    0x2030703080406030f06050619030e01110415022109010f0903170903060c090105040e13080409020301050f0102012018150703021501050d0b04081308061005030c0d0f02030304 77
    0x700030310014001400c240c06400c139410400062101300318407071f5500d00380300c0d280c03148040110000700da1124952540e8081d9201c03c0210b8a504000600c0d41c00761482059143e10580000340c842131402c0c64609002d60400005074070103a2034800e162204403090028106003d102004e505118080030300030740440c800c41142c0c0c000c40c0c0007403003191416100040c0207029031252040501900402001620216160044606200042c1e440710302d82803900e1361034280e003203002e00410402d580b9000c180740070824a4000d08060520b4400050352549064204002c0c40009801c41b415641040e42c00790707d41001003200c5c420b041503062141e03601c0043c036081c4c085005072400703019800300010900550710f6038420043d001243c4030380c0840d403240c0c0b1a03c02d41c14a50009201c4c065200c000c1801290001d106403001d150420b1185528030304040401988031000e99080d001103445901c001d0802607000c0f039440c0c0c1c1c1001000e040c0c000d04615078002000c03d182803070110001c1e040c80106d00e01c140441d02d003002264 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 653011447 1250 653010197 653010203
    0x31b060a200a03120c020c0d0209090f251409010b2a0601080106060503010b0d110c0a0b160c0309090207110d03020c09010b120609060a090c1107060305101202030703 73
    0x80b040320182c0303400b401d04a100744042802c98036004003017070390600025070f1120220005192010740182c50f400c00000140003000030f034071401401040620440100030241420709001c0c61280c00da00f10800014100b20b95078810412403000c0e5580c540d00e07072104c0c0161810b640c000c4400719a20080c01030310640c0555207a901d95842d8503880c5000030010004503c0a0680d43c0d110024041542d0300d40c400c544501080c0600d210701d5104104141030500d595020501c000410380c055030810003550201402e01d4186041500c203800308408000600020388141c00c103406290a00c50032001454038001c000d0383c2107004001c800c90703000400906001e400d560022801130010304d1605c02159518000351641d50391001d0b1402580a0000840c034858500196801c190030324003445680d03505d0400300b00c146140613000c90707000341040034045000000c0d40200360210301c590b282c02030740b001c101c80c0302403034141d5940c0314408042c54542886007414100080000711400040040c465134a1400041d00b02000c60f8401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 653012697 1250 653011447 653011453
    0x1b1d0c09012012030f1303050d0e1e030a030f1820030d0f08060307210f080a110606040c081b1207030f0b0111030a110a021c02031b060a20 61
    0x60007070711000009600c00e52100d4051176540c0c40340031441c3c0311003840720002000705a0a100024078108990301c0410b00c50490001c403901905040c0f441c1e0b8403182103501c02101d942001078038035201c030f4043c0070320054895180c2040012207144003503200d20300c01080e0000c2c229802840300114011210a544e02c40c804001c05440105500c901d014009240b481c0003900441d9411000440e40c0c030b00440c9600071100300034007000d00d840501001c60203078101d61004442d900700701d850520103d25124064111201180ca51140406940c41003c1c54020000e00182c4500d08007602c80d0007984d40400710980191541003032000e00840c4220409190045108128524400c4020811507583c15002014880c2d82200b0402c061080c0c240116200002c0403c07031882070380200180950948110304170284555980252164107545600080740144420181a5005502ca40070410741c5018005440c200741d810071904a00f00100003c170700300b0f02400d08110240140304801e01607910403c10b0141c584041582a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 653013947 1250 653012697 653012713
    0xe01020c060a0e1902010c0618140601051806030a06020f070b1614071a15090c07060615090b0906042418060806060c01091b1d0c090120 60
    0x880189038451081c0e49602c84c03001a0a00521a42c0805400702d4040e50303150010045612804090001c21001240c01002003d032100869401056a0700010104010749099450300041168071740c409080222031205035014842c0c0d5640010349041055031011002d6116023000501c0821801000401b40c00380d40c40e07900f0000070038006460042c030361501d5200c4449280d0703940a42202e50081c1744c402014090f680640444100001c22041e900c022000c565001d0503c2c01c0c00458a440001d0340e43c10304040020035108200306043c00b4810140100500300c0c0d03810284404010030908881c0708150740d1b12400100c0c00d44a842d80e8045501031300782440110034819480950034048208807070001d000510000ca8442d01c4203951504034200c07500d07560b8108107615810204205640241c000650075903070b62050100003110040542080c4401e03040340c119017481c0c01234120001c110000c1c8003003910b03c12410441001d000702d0a42c1e0410000307207421080307503d841c60700340080e0101c62924840d500ca5070b49 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 653015197 1250 653013947 653013961
    0x711030114190c0806030c01030917210105011b150f021b1606090b030604090515010810090308040b06032118180711030904020d0e011a060d0e01020c06 67
    0x960903540d400b0b02d0820070110090100494006105443c80c1d0f40c150441001e4011075842034114540e80c81c020340103c070038046540707010b42d21039100941702c4c0e03400032203400d800d0030b040ca40840450040c4003c2c200070340c10010800f035001041a04140060488400c040154801e441c0342c0d0080e030f13468900e01e05c1150345075082da0102281040345500c0800c07910440210006100710000400e04032111601c803140700a04040506403140c00090005402582c0c071400c01000c138101b004020071010b83c2c2c0d00500100c1d41006509424101d01d800c14180d881c1c180014207001a0b070002210b540103802224a00c1c9646403040003d05100305100b0310f00e00303001100c4045000024150082c002d00e40c0003440424407002030400d01004407884150740700c5030703041d1340c1c00a1000c0e0f025000c5040304296401c00d91349441c400c10001022a042076404100702a9030300800c0342489024030824403007507444c3c0080700c800b020070750000d4400d214440b0b40001d002d0f1188841481c80c0da00b5015190300030011070542c2c0082c5404c0d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 653016447 1250 653015197 653015221
    0x150a020403020a03030c051b030c121002040e010e100b09040c051e032a0702010804083c13031401020f0301031415010e0c0a0c050a0b040c06140711030114 68
    0x11000d032904c3c0140d14650000000c407541c234507a000e0300a00608840d02e03020f400c0011070000710300800e83c6405090340d415140c51451005001030014100d00050950501c03421464961004080c1400103503181414400084280180c60410f1070882c7c0c040303204c2a00701021603442c06116600749800c0c2e14bc201e000521900742024521581c2d4010442e0340209000c050341c0407011802e0388000380510104031400255105051055200b401420030a2800c140742400010042c0a03900d06010700d00d0059210680010b200842582c40e4865060a030500100c000000e00c0d070300592000420702070803041c4c80c10461000703405440781804e41c0124962030f03680d40d08156100c2ca010720039132078650148424494184080d05442c038140d84940314044140d82c1c9441c84c1c0c0401d54031883c00d80e00bd11030403130b90300340006404001c1d180b405817103205011054101482c048000800c19080344042c04070800c86c810030180400b00303440440f070b00b020f40b030519042e40708013190040c8100405418076498010811007114580 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 653017697 1250 653016447 653016467
    0x90907051c0f030917010204030201170a020408060906060907090303170a15081b090103080f09030c06030702011b03061d1807030f1502070b151305070c061d150a020403020a0303 78
    0x240e0b00342c50310142e10906146c00c074452804002e0228140d8901c0c0c1c0380401074401c0c980d5102c0d501410042c50183c031000650724024080317480303040e142d201c0381c1004031706e082120b4001c0d0840003074200780d0b511505540c1c02400100381a031003002a1510840020301c20b1800e6000420200e141c4014a88a6038480b19040d0b2585141e5004c14403c0d040511040814202024143c1c100e80d0002119800c01c5c240004111041d40807582c8154544610209441640d85000096001c2c001c103400000d10501200348402c0500b0140f051001854507040041000201c4201c908101c1c03584815119074550f41e4025000c150082c0c14001101031282500100800100c0b000380b144450085184074180000c020f9280142d04c158100108503405200c0480c0c031006050f1030340650f0000050507016910030740e08000e011908121044400101020b10010900980b442118161006541c0c0d400004850303070105d5503034144e01040411614007060005d59004a01d60588010355402060b529070307103a0301c1c00c0041c291030301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 653018947 1250 653017697 653017709
    0xb07050a02060d15052b0303020d0618050603010515210d02030a1827021c02031803030402091f241b0c03080a1701030501020403060b090907051c0f0309 67
    0x440d104c0860300740f620b4000c0d0115981c4074644a049080744c00321800350302050030342c1141415000d020740e466020550091202078502c100300d50110030300100f0300000360313007010708101d000380d14180c00d00400643c280700080681800b5500e01014070140250f000d4410402290a1000d00402c442c0ca44015404001000900c140d5519400340e02c50042e41c444142d102c92149114800c0e1a40310b070081003042a4a641900160180060130a21401c1c09041c1444000c540708210300c1c2d00004101070040b40a980c005060030313000042d411850705030301103044248060a03200650f09540d403102600c155003110100646103048010700245040320b60081850000e8048801081c1084a85003044540050f00341031039401070214500986903887e00801988a00d1011040200107058080c0111400701818021440350000503501c0340b071420040101d5241c20700c0e403072240c0200030a20240e10300014110081c1c4408582c00890055200480300c00d020384068020140245500e1403c14150000c00342002c07034603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 653020197 1250 653018947 653018981
    0x3011503061514010807030f150503160605030c030c0c071202041d030a12020427050f0c040e09070314030c1509150a0e0f10150f0b07050a02060d 64
    0x145541d0080380d41445001d02c01c000890383c0a10116903100c2c4030b095400c0700803824009041c4070181000425201031035410b5110050600c020480c81c103040100301c07221002c0288007489241005030007461440b010f8480c1060701c502001160280f03d240d0211100581c0d544201c4490a030703241074490340d51407a01c900703034440d41c41c0c10000c4030715080203205550415540381c00f4525041c601142940d1312140c0c210251402c0d0750038031021944100014a03509000d80740031212410041d003010180941d0320040c41c1e003480d050000c0a02c082d400460040c0d0f41515900c10b0818042e503a00d050051070042c10781c0c006000701c1103441c4072005a110100062008410b0034090718404500500300d18840030041c1c0d403011641e40700310051443c0800c201450b0790403071901d0760081a0b14000740f540a00c0d107082400068403d422118000407031b05e046200702502030040c000300300300381460000d441c0a0714500b4850400009400070b40c03d0100130003400207180d40ca0b4001c100341e403181405040f0500410f03019021100c1c0b44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 653021447 1250 653020197 653020211
    0x20c0c0a0e07260c0309011b0c141504081c1a210c010c02190303170f06030304050f010e042a020609061807170102090103060b161707020301150306 65
    0x54405080700e003d105240990004071380301c0303a1520f4404d60004000b800995030b90307450b5010714180420281200402d690b00d142079094282800d42c0a01d42d564120040c43d0302c07a14034105008812201541c1c041d8029040903110a001c1180400303036140000d034009118a80810b00b40d4080c6d180101103002c000680d801c2850545509841c1c0e10740300e1103110060298011400c00089622440190300e00394809406211520324201d0b008641d070381d981e0070031404264103210301c016403461196a035a000f0030f261050507241c2030400202e6102d100b18000c050280d032201c0540955a4090040007005003805001042411140300103c1c03c20f4482d04001c000b60400c5442588549100040040c080c00588025010680b5500d104031065120312013912018050400001020640c070440d081035022003c00243c0d48114401c0014110784554210b9440761500380600e2221040c40c81c1d0003201c040e0302a008174468194240240d14038080e4101c029407544c2003007401c070340b580b25030210f031001c41c3c0c0301d107001b844a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 653022697 1250 653021447 653021477
    0x120408030711040c090e0603070506070b0609071d0607031b060c1805010518010918061d04210201020f0c0709050c211308070303050708010b03070909020c0c0a0e07 72
    0x11350604051440002d01051040c01003604005070140c121200808440d00c480d901d8002c680942c00076601540c03e0100d5104000701400e10640003a030252075442d2121400f2401c0911711403031036420b210240121804541d80d41018080c107440c1e684800c0da401d240c918074a2510380800601001c0142e180010701d803e064030030320f000d80002c03c0300740c0e04141c4a10f4200103040754520104c4084034440c46c1084400400081c00d040542402120845c0c1024041041d50070500c0310380c0e00880798448c11083d0f00100d070802c000302d8141000029406003801614050101550080b4064000c5580c041207134030001410135420032000440400b03e41e0007001c20b02c8030359181c08905249000d40104050101d00d80c82c0c030039243c0091030130229402070740031fa0110b0b00d0b80020346503a0200c0e044000c080340841d50b00d4050020309a08101041c2c01003900118013441c6151a0b88024007280d2240f0070210502d80226880e1104481030107505d031070400107800940142d9403200d9890311100203403500c401040444540b4100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 653023947 1250 653022697 653022701
    0x150806100905070914040908040e09120414100e0306100303030e010b0105071403040e04060507081501050426060a06061d0907080711100501090c05070c030f0512040803071104 77
    0x441c50a076111001d03414030308820001024502c174a101e034402e07910313005c040c0010a0b00c000350014144c00040200c2d14038100a00500d000c24509450154070010720080120390342401c07010041400646049503030310170b80b02c0152100458214015070501a80041094403411425035004072030180d6010310829401205650032251500c20150003c0c0d010044c500114040c00720303a03213030f16001c10b00712458035a4811058181034030640b0110380040c0c0741d50500c85110352200d90b00340c00c40502201076241e21088800070b80135205521951110307449410031145907100040000d01546950750075240f1070300d000c4034000b0091071940149004104c0000d03001d094010f800004d600d081c84040c048071015151090b081ea00d2910003041e8100b00903042c40e4459546c07505102540c110704034444085401d50500488100f9103aa051055017000b1003840b5a9001c140110900c80c1120b8000b80120300a03451402e1441c01c3c16850506e00c08849000680007444200010041000500548a01c51003c40000030042 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 653025197 1250 653023947 653023951
    0x40c030506010e18062205010f15081023090a02040504050717010905130501020c0a1211060103080304140f0a151b030b0a2d080109021f03150806100905 67
    0x1440642e0a0006170b00e4180300c80d4036400d107140d005814420801c0b110803802135601c01d800c04840c08000c1741302004541d4100e183d1390641d03101c5080840d8a86814078a480f0040d480b0320a038403803513807090002d060300382000c1841c408808014003c250075160008074500654820321941d4002e515003800030700c05034400c4101e082490030b000241c40081e440c1c41502c40c040c1c00040d00000800c91260041c000160003440200b400d052040c0107000446004d0074200001804080b01c6811b0055440200d0307685000403540506503944880a95140d8440341002c81e01200200e0b0b410f07549210f00d10085404200008084244c07910540e002001c080c02035400d4402d9800c02a07211104080c040151010540039030407040d10740101034242c45210383d07981c508400001540c0c19584074003841c1c000240504682c005191702034103207100244803102d51a0301084864400d100490352600c414030b002c6a40c148290030401c21032061401d03078052143c5039003074162070310003d954104000c0380003440081c03d8803c42c00f84038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 653026447 1250 653025197 653025229
    0x20d050612060f04080a17130605070509060f0705030702090103050a1106090907030c17070f09080102070201140a0e0301090c061d0a0501140c010212100b0403080f0711040c030506010e 81
    0x100d46031905d903181145c1350070019900b01032141d030741d400114414034611020311820032101c4010701c1c0040c81c1003a078100c1300c005d0270010401000f0000140141c483d0320443d0455980d035a22559900aa820082c1c15405004c500951107036940c000003003402000034010080b980a86208000d00003d5010000948202110140c01c2a040c0c40001c09080c0a40d101030003019040c24591070441c2c1c0c0e225074150790762080310004080384d0050140242142e018610002034000c2000071890014550006403039402c080b035110313042d000001002100c3d984074100b035540800c00980240254505840c1480e11003e0a0040b000050324807000703441050004100642c2c032100c00b52401a40e2070800004440d0704041c4018020b07400e00400000c051030500b48014001c400200d5008001420003c04190700d214840d8003078080050300744014004981c00078201c56a50241d6041300ba80c540a524040c1c2844140150f0342d40d02602c0c1025101520750503811081c40b5000c247e886080c040040d0381005070002d0b91150303003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 653027697 1250 653026447 653026471
    0x90a060806150a021905062a040e060a0b0c34090f0b0a080d0e22020702010e0909012f030a0c17071107060f30020d05061206 55
    0x20032402c0d820801001c90808610544501d071a0b41094100d01d4507070101c0c200e5807544007108100500a41d556449041121a00340855484142a8400b1380b80181e00904103103018400101d8100c0e65180d02d034200811101140c16102c1d12404019a00e13000c0361b180d044940c1d81c2d0740b00060250000d4101c10040c41240c00d000b07081c2c25040000b40d03c010000f0113015094580d07200301c0410301e5511504020024900a0b0090101a51540c80100f44d101d05288450191a900c04e07021902d049100c0340304a10760355400016210380490004a43c420b40c1c40b20425003020219080c001c030710206410100c041d0315400d0468008008104280b041407c202c58a204012402e1021418520b8030b40c2040000c5072080c40c010080461000071224150820f440c8500822265207440d110f1604c284040d10080401e41030140040d880d480000e010460200310604808100b0281c1e01c00c1100f04028481c00c00c000038004540701c000ea64101c01c002d00d0250352141c42918221381c41e41d400b600006103544100b19040034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 653028947 1250 653027697 653027719
    0x406171909110402071410021213020d0b0403170601090602102301060206070f0309020a030813080d02030c1506060f0c031608194b0302090a060806 65
    0x200c400401d42064215040c00d0b601040c0c807810760350f07800a0145603014016900d4900c034400501840c0c007035000840c40c422401070004809a0711640d104a60004655800d40f60012803440003501d03100c1c00c203400410964402d402e110038140d0101c4503c14503039208179240c4080d201d01c00103550082e4944140310060740711510341003004043c0e41010301d071040d603441c0f07070180d00c0c0c280e030303110300c1c013610260801c0006a02c41420000f5076035110308403510813405800c0130000c120032034010418100041c04054943c1c030000a0100d14600e5103045440202801c2c0291010400c0c203c10003901c0360f000311a0101c0034480d48032446485488510303518050800140414600202004000420b801c421040a10b50006200c1c0815a022451182e0742040c0725412a65846035464010041405048810030802941341546100e0080d40040340c2801c0c201031f07500500c2c20009030b0007010398000118164085415502c444a0002c0e015000303007030044c00446503c004a0744440302141c07120343c11207010380c7c04041c90300e03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 653030197 1250 653028947 653028991
    0xf09061015050f0a0302090a14061e09090a0608101e0914030406080a06080d1202030a24031416090f181a1014090711060103030203040617 61
    0x900190040301c141030079030420a42c0c64480d1120303040b54801e040842e40001d1107050038981307249000c0180224615400d14113601c000401c0e241d010316100c11b184101810750080d0ac514042c1c040e25600d4800900c07820340e518040382c0000241406120329030b0503109541c1d85020009150185d5150180000030703000515064400c0d1801070082c485c415140d68001844d04161050148001c101515031600c82d1401400c0180c5000112411a0710481c07803134005a101d40d540f95481840c1c20700269000134007580702d80701c0c08440d038010105001617449441e000703100c01030480e03081c000100449004505442e542d260445c0d5840d1601c01d40380214080b6200410284150140c95001c045c2113403003007100007241c3c2e5019000c2d028164a1050984004841300442d0074040d458420301c9903ca07000040c403018a6203009403680b52040719100c45886454841c000903c030f284074440b14884910704100702d80c0e03103513503905011752a5401406840e000400e010000542c04010301304250040c2852108100c003000491 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 653031447 1250 653030197 653030219
    0x50d0c0803150604050607060c080115020307020f0f040f0f0b01052803140c03090106050618010c060e03071a091504020d060b0301020c0d110703030c020d050a02090f0f090610 77
    0x950b40d540c0c80340081c04045001e07254000500700041c420b160001d8000388070b01002d0500001648140f03e203603d08170700300d00d080354088199540d90783d06680030350003008c1900000340d01c00252070030359801600e0035060901c00b1400c5e411040403844c040008002c03410500004488900c5102081c045000d045061240c0d02c403002016000100c809203400a410100307940c0510790b000b42598101d4203c2000300601080d03890a110b50f02c020031044441903d04100d0340c80d54200070703a0650b61541030005404100041c0003198111401048508007501d55800f65890003040314040c96606ca03c00d04038030000035600714000101e00c0403602d04c080505a4644e20780d402c1025440e4640320032102c403611103411180686090018112002040f8081c1ca0705000c0f42400070324150502c5074501003079110990800103e80c00c107010000c3c0a030181c4541210100c0303410843c1c501001404000d41100c805c00812810101040c4040d0292202107034000080d1110100150348960554203612421100c0b0f000b0400c0070b07010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 653032697 1250 653031447 653031481
    0x3280c21030f1403010f03030e041a100302130b04210803010302041d070f06030f14040f08210103150e120c010e0304090e07050108040503040504021e0d0603050d0c0803 74
    0xe103490f61481030303640f82c0c40071541c01c00c0e4030692162501240c24000c0507005000c9003540001642d042008140d81584c109680514250107402528130b41c050481851181e012101c801d09001140c41e002c5940e00c1d07040a01780c0c85442400d44004e01060214013443d07a901000320041d4000005506590951b000c0000401541d074404a524401c41d05401c2c00d4601030110400402a5980c81a5103525000700507003621280c109044a41d4904000392200d40d48542440e83c02940214908411018074500b4010074481c5000440b08a41840082c8034010007000ba03441c1603c2c401e480f0440f0140b003d880a000780c0d0100410100290000c242003040300364564080d220201241c000450f40007803050805085078440d4100d00c010640752503c0c2ca80505007041500000c01c002c0c60b14000910f02520b50b15140d0040b03000303107481130750001030703604d1042001c9100c0c2101c001d245c08013503592480e18402500811940c4001c4599004030004c2650990184000c501036907080600c0e40e285035914013a0100800f10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 653033947 1250 653032697 653032727
    0xc17030703080a1505130c1d0d0b040602221d0603031215041107050f15070305040c171e011104090209030a050303070c051b1e03280c2103 61
    0x3102130001120f98602421080c03a6011190005d03400c051300000404030070348010f1150103a4103c6c4401c2c13002d0748540e11002c052a8005151b442c540d241c0d46007001c042d00c1400116211108486075044001d00000d154034202c1c0e4482c203001e29001520f81d0103080b52002140d40540c10740041c0501c0340024a0b05085507405140010881a000e144200107000c40700c1e84001200c20500200e02c0070104001000f0380308007100808020405001d5034010380b1302180c1e0003017a03113040684036000b00707007002580b0101ea03001d8040400301070801005208510356903a04200310310301c0e01600302402c00714180e0600c520500c010741c0c40f410740d103040d040c005524007039800421100d405229200d40000403c80500245d030140035280e450b2000542e03e0305041d032900c00300c02e60329030300000c2d40090544030b0380e0740c410032042201080010f1014031040f4000282803504100786001190f811424424036100c880c800c0310480c0d40301d84001244603850303000111801c1c64505241032843d0004c1030001c0442e006031241d1080c584 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 653035197 1250 653033947 653033981
    0xc0309060c020a170307021333091d01052505090d053c100f0e0d09080d0804050c01030e1908041d040203060a05060a03050a0c17030703080a 62
    0x40d13180040c68602d244051030414503080440d081e0114502109410707400c10010f40d0a00400d0070601d00400548071814903000700090004c8010200c0c035050003c1d27002840b0700c0c1000c100329194848440000e000c440e00c01e049952a2100050b201d400040324a521101d2905810100b00e80740c0000343c4882e40958855030b8401102c804c440c0000b28100b00014050080b13014402101041d803904408038104640354105800d000c0400e66101c403000140382009444451011070094403036180b8000808012800a00074002c45904501d100c0d0400040c0c41102c520300100c0303040d06d03500d003000c9860b03502c243e400400a80000200005561203500218110003c400590343c900c03100c1040d0380c004d2122001c0854542d0008542004441035403000070030580401d02e010b070300720700d4558002074031040020700b00118a903685012800c81d840700d0207600003960384442100c0b254031150404980c942c01621441507034100b02c490f00504540080140c4902035855158824681c450780c0f1301d4405400303100503816203d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 653036447 1250 653035197 653035199
    0xc150705040807150908060103150f02190309031e0e04020304081b010e0c01031a100516030809010e07030203030d0e030f07200f0a1818050f0d0c0309060c020a 70
    0x1480030f10040008240c0c00b070101c18880130640d406032900042c0c1d48400ba880d000040108046100480c401810100404000800c90701101000009010b1145012000d244588200040640540c8000c00d0113009844070030613190f48540d0065207030b40e2500c234840041c00c880d40c420503074181034018640240c42000a903082c80010311a04180380423070b210780300c140d0791180d0385843c901c542440040d000100a203014041000501040248144180311541c080c22454920364101d502c150144d540c481406003401039101e90700e080007001c4403410741d081507039941f0300f801c0001c1001d4009540d13011654090091820103030344403000801000d110720222180d00040101c142c0e4000704000814045108581c040c0251165a02d0806034621a43d10706000307480c00c81e08108217a9035890008119401c040280c03c080f1a0390298030080c0a00d04045150860100130003000c001d400718001550070040c40403503010b442082c034110340d00c860000010300420b2120005012242c41071020008032070010340f61710139003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 653037697 1250 653036447 653036459
    0xd0e1903061e060603050f04020d031809150803090108070c1e08031f0f090213030204110702101e08090f0724021209100c050709020d0c050c15070504 66
    0xa2a140e071000382c28901d558824141e0280c20f84140d10140603a80707420486440c0001669a11100c09032010b889140c40204490806200d500c4840510300c040550902c46507840c22074101503e0208003801407800b01c00008601c40c02c0002c1a0744200005941e54015501d49040548142e181a141943c0c2410f10916000c0913100103034814181030b2250420380c0d542d2070600d0a041c00000c1d0341603103a03028500ca440810160400421b10300036500003100059803001c107034803500e00080155000a4001d42040040144009500c011340702c018000e85180c82484130406040b01d800c4c01c01d240701c0c0d5041c0c00440f11200c3c02889500340940c014406c40854119a22a5150525007502540003070104485a0450300a0315103034105070004003017900050800345c814601000d80c80c002c900701c4078050a4809060102c03248100f040552194002e000d07541c2d581d0f2561180b001951000340501070711424003190380d071428414008c42d020301344640054540a123403000c0002a9106c00341211080040611000c500f03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 653038947 1250 653037697 653037701
    0x1200a110a06050c071109070f1110110d050615041203030e0a050d020706020a0f0b060a0515130605070f06050613020406021f0507050f0c1006030803060f030d0e190306 74
    0x2811051402d55205c00703052600d0321010001d01c48a5000e10904030910059980100c0108201111410160750b000000303464985402151030740350354858280154058001500801068001000071081c4030543d101d00038880c21056004030304420420801c01040b141550342c41c3c58041030700c6480e020500da0005034101d483c181429005a0b565013000104103451a01004040000e00d59030000e060000016191050924200305001d481c0d41095000504281e43d00090304019013001010440c8008141845038000c0c3c110789121282c0303800c11040403441c4e0340521b09840c0036035403118180340f403070045e42da030900a0840607000307d4204940b034051081c2c000c0c95001030f1001c0c00761580280420141c40fa1581050540700d4240c00d0510b18090a00414944c00821501c85070501508190f070351b12910030f01854000919032a900c0d5500c3c0c072001004000074140114082c01040354880e01800f412170806071602c40081040000c1422044480744600f04501c44482440d103c104104070f040da2a121503003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 653040197 1250 653038947 653038951
    0x24050705071a0c0f0d17040204060509040f030807050313120c02130b0301050a05060d030807050409060e15011d1c020d050a170c070b09210f01200a110a0605 69
    0x101420200307505120707030030400c00c45004200031001170039004c4041c040a8a0704142d040344021081140000402350746403501b040d0300500f4060540300f010314103420240d0310703035802c258200c000880c00700104030858800d000ba40d0085a01c041100310404059490761881290041c49400b80310080c0d11007405a503a44a601e06100c0b12007002003054031645007050708403103004040c011703c60328100901c01162078840c00d51414a502d81804402501c43c00300986050280381e009030300312410001c000c500420380043d000d015034102c1203c2001c11a40780c0056a2806443c45284c00b401c0203036041c3c0540e0314003ca6801580c00100d2003401c28620141c000c11403002c16010161010f03400900f00740d0810441c5900101e0310b080c0030704920f040080c81c0c0e0310540c5506581c40b51030808000801e441803141d071040002c84900c540300300d0b03540041e00d0040e4429162452180c01091b0f5501e448202c0480401c4640d0340811202005505458900304038800d5440ea111088600e007540700c1c08030340000280440c0b00d514 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 653041447 1250 653040197 653040239
    0x30a0b03071e080a11041d0a1203050702031c150504021215010c12030f0b06031f0614161a01091e14240d1a012405070507 54
    0x15410391502040c6030040d0381035600c100d00c164010149840491200c10307080d00b41744d200b00c0300410038803066000684440c008064005c164060b01190740100440843d40c42038100a40e04c01b40b0407666092002d2781c8a0069070805805540d09218040e02d0300a0b41c3e1201c55003a214049020206231503201080898100144502c8100b14440a1002340411803403894600842403910310082d1426135910710f03005840810316401d2585690b12030364180c1058010b180c003004041c103c1c984924200380d000e403400901c9420b20303141415080e0081025440703101030f180d107000d45205680c600954040180c43c000b010180c00ea43d6100028403c3d040c08040104081c0200b015840215500114000da0243e401c0808080c100f00c91600c1c10490740502802c0b07030396500c180003100502c078850031400700c80301c1002000202e690281c1700350084000c010400154004040481c2141640f41e81c031026001d1141c1c01e01980c030384005035000d8100744880c0c4280003c0815a1103402907a11841d03444c401300300203542c088888 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 653042697 1250 653041447 653041469
    0x12050c1905030d0b03240f06040905070311010c081210060305071b02030f01140f0a020a080103030c0f05030309010606030e07081c021006090903030f0c080a150b0c0c010906020c0312030a0b0307 85
    0x4070801d5001400000c1d003154040b2000c0003022030b034bd900c06070b4034051488010249110003200041913800342142003404d03504051815610300340041d01c094514411240380038510180d01020a03494481e1140c03902c035511075140e0a5050103480606400c003d08858200c2c0d05120f540c2415103945400e004006c7d1100302c80000b480300e070900c2451a20001801052000c0040c8144850050941d2000c51681140d8143c2044000300b0403034203152a0342e40403c6405002071200000380100004154001d10880d0704981e001c100c41041151101e403154440c0c4205d0900740e01041c00aa60146610708840c20789a2500440b030700b0f20a02003d01060310030a42c026040c2c941c3d528604e00905825004ea90b0841c0841031302003000b80546c2c8c1c40a090428007905c3c0c50301040e990504605211440340c101d002401003a219035443e0f002c4150b0244d5540d00015000b8002408000c6c0001c00900001d03030700b20041c2d001005404039907500062004150801005054007603191070b50301a803900d044c048030026154403515 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 653043947 1250 653042697 653042701
    0x51e190216030e0909030a091401051905090312030c0708210106020a030807022e0902040615031512080a0302091e10112812050c1905030d0b0324 64
    0x200890204e0060101c1000d800c108a10741d00c0c0d80e40301245900303440c7c0740e0144e5540400c02200403076050243c19280007020f40e40207464131501340c0210140c004410101d04035000200400380f0895940001d4a015076000000e20000001403405405409032081c0a85400450205200c10000440080c1d01c40405a04401c01c50000d040d8883c0c0c03c140d0240060005000018440c901017160210b46841190000c01c4895800c619010541040fa02150020030500000da2201060f1900d03901000403500070030f140c803070520303c602c2015081c10300b01e558038003000004440c542c07a045000e40c44041d14404055081002d401e40d60f40c0c104511016546102c407810001301041d0074009010241055803051210101d26800c121100040d169036046988102080c81201200c10600f665816240280324225981d0040e008035480300c05026017400c0d0100700c5d80d915840281d0712451520200c4050410b8004020544a065054002c0d40c500240134040b6003000da0410000800c840481034200b41b60341034401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 653045197 1250 653043947 653043949
    0x60117190605062a07050d0305180a06050f0d0204090509010212060418020d05010e07150e0a05060403230f030d14280608060a02090301051e190216030e 67
    0x2041d4070103041d00381c0e440c80ca0001030319000d405004901103608a22038842102000f480403d104001c0207240c017400464a0004c94a0b01070899000700707000307004548080089000e5480c0c100850411582540c450034a011101660050140e2001e40c0a02c2840e40030840014010f047d4441c040c0300c0c541d00b200060300c800c01d050b8030451040002c0e10040c45a400c0400956400c20524001060030782d044860281220640c40c02034050100a8043c00e010f0240f190001079190f10284081c80c3c050b099030300c030b44052000504101c0122058000d8075009881400b09000003440300300c00c0744010402c2c000181420120080c580e103400a5000031801540000c1403480d0224000d0064a50f203110142c3c210325180340c00141d0000c005604003544245502c0c0401100e030391a00c50740104080c0c00a241528000d01d0081c1c00b5201030f45c42400024000c0d8680760000d41c003107042c1303280003940c48620441c020146e00d07607500700d00b4140420500c80d0640c40d400c10581400800c154441c0304018482c0c2c1320140304200703403c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 653046447 1250 653045197 653045201
    0x220305030106020d031406012a06150617010608130f03051b01090f0201030903050d0e07030b0c090901030201050913150906080f060402010c060b210705010302090f0906011719 77
    0x410941c05150070320607160601c844070318186d0782c00002842d0106642d402450840042d1103c072010344034070b41861914106003e01508580a0345100b081801002d17581c0d190100c50794010b241c0494030001007070300140200c62140c400c15400000a41ea4240ba102d0703940c0301c4444900782034030102d0200b440003c42003c114191480030078120402c4c1c000700104c0203262030307402d06000303104c00007410140d40b010300c481010700550940303010030210f02080003c0d4403483c0c0d131569950090700055801064410000345030b450803200701c0d440e2110140c150360003a40703107078019961600506000703070744280341c032401d1044003d041c0300d40708656041c0c483d4417030b80c01d01d030207200f0703040360180e4008102540107264101c400600c0022942c3d0025420710709400300384080c0c280200180040354480e6480200c405251203080195400031601002c1c00c0180ca205655503c0190100d10440e5074003600310b60401000703040c51901b20542c070b520502c103042083c20080c0f003d0700c9503c414000c550075003042c12510003202104500d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 653047697 1250 653046447 653046463
    0xa09050a08012f0c031204050111071211030c0d0909060b03070207140a0e040807030e010905150717030702150604050606040510230705011103010f0e22030503010602 73
    0x500204501d01180c0c45250340d04011080010081000b030310300c0380c0a0b25903001110f03113805240c8252600c80014a0040055031030980e803e440b5907003010100f400751500d110031070302c090fa40107004030005069103206a0b07070358218040740e80b0f06010a003d800302c4900d05100d030071101c05041da180428a82811224001c0f600c581c0c0207011003842c00d1041101c8240c00040c0c400c00c2c2c070040d1902e091070a00d01400101d0246154100c2c801d0003070100240010031215102034001e140c8282c4803030b10200a0340004407a008041e02c521a403200c2d5141207940c481c4500d01c0102141401010442280c4030492a0848242d200f40e40440c010790000800704603814030f44000941140381210b0600582c1003000009850780030750f0050343c2c85000b9102d05008020f010300d09051041c400da40c8000c84509800b440c0c000c1c0c54010b003a05807042c2d420000340941d900359040440f4165250901c0202c10b8a05102c07030008541c1c401003c90000e40d80d070420813807880d112003580c540141d11981e210355032907040c0383d4000d05224403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 653048947 1250 653047697 653047709
    0x7090b0a1e050d080403120914150a1b051c0816080a020d0e250b03090613030908060a06030312091212020d020309030403050706140405190b0a09050a 66
    0x70100003000380c1071034028040c0c11a00c0450766003114a1090030003015074481d5610040040304a401c22200194210340c070007088a810020515440e15684140203030700001ca0550b100304502003160b01c551074050110750015010105070071301d10650a0381d40c42c0c030384031000000e640120603403c5c4107003010781d00c00f410503072010144025440c1024a82006086058050700e000300741c5402140c01c403040744a540c069101c2a03d00d00440f140b000d00819180414540c0702c0c2018210001010702060000200003200e000f04100c0d07000b0622503450b8000e80418a0803041d04508100350b500000030b201c4002c02034580502444180060103034950310300074140388840c07001c001c481ca0070804018041114610104100d8001d410085010b1840c0c210759402885803426400e0483e00c08028490000c3c0c0c000050000e40340715100315540241c403940140c0d00c15508480d4048420300800040c032003424410820703100ca0700710215040c25141c07074583d542520340103d41c00100040ca80d200030411842c01240d030100801c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 653050197 1250 653048947 653048969
    0x60303040303090b0f190e030f0a020a050d0c0b07030305060a06031e1d100e1504020604031e06050f0906010f081e0c0d030f03140f010e040609020307090b0a 69
    0x100c1c0d690050010080c0d8458001d1881000c03400100c90a10b0364100c403000d13540d550780102c00c440d025001406981e4400c50490183c450452203044001000a030055616001400440001c0c602003c00c800400c5c80942100c065004d1880000c000d41c90300054900740b072080c0c07130109049c0b0b4907000744111407030941e01c1078017018281108078111500144032070301c1c4004802804140a40c01487d030742100210201c0d18003491190b100016890680382d4010809a2350070fa00303607158203040c8941c01800e034409840c0650721a004100400c00507244503510840c0041d00702a18107130342c80c0d13510313034100b251003c40d00300c40a0004242044400308081c40620b02404004950300c00c41828220500c1d0f4416181e0038680840c40ea80c06210451700c030806c40508084002080b05681048034600105000440303810030700400d081500c2c1000106498420034803c00c1d203c02c1003201d91317103040000a042d0401a005841c500d03524100a409030f201845a04050110010003081003070701042840784103007a5a0203607031015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 653051447 1250 653050197 653050199
    0x51f050f0f010b210c04030c1a041206060506070c091d0319031b03090c0e04050a030807121506020f0a2003030c010e0c0109081501030204020328020d0506030304 71
    0x5079440c4440c6064641c0c800c411520756003884129104114003891403500c1e40000d50800800d0310000c002482078030f00c0b6101d41c5803695520709804840301e2583c885941e28020921081c00b03510704a80c0111000c80c0035180205405603a000410758a500c1703a181170300c81c40303556101840300d0842070180c4010869550b101c0105980c44246d900e440340240e4480441000c298040c102c0746600c00c0c0c10502d05480744449000381d0340c90700c0794050010720407090b040b1510f00050307000040c40280ca0030014440e541000103401c40380a241e900319081c0c00c00a022006101c11608541e090700180d100e440e1080c4250040d51940906014002e450000d105841410301d07402004840c0000b9080c0001c50308803003040e9621481c85041d0300c006421802002111242d0750302e80600150700e500e0010310036141c071000381c8502405541b5410300f15111601c6240e1085103c2d040c07001007005080a500640d84a43c0c0c0107800306040c6070b0f03e940e0304003561000c182c1d80304903a008110424213a0700e1340701b10303130700a481140210300d40703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 653052697 1250 653051447 653051461
    0x1a0a030c080f0609060d02030114070f0206012904180b0f030102040f18090503031f0f0b0a111e030702131416120203180c01080709170703051f050f 65
    0xca14001c210f103000303040410100e96551940c0301100e45403640100240490014421308902c6034008039440400120211841c40c2098004203903503060760718611300c0140d03145412404801c1000840e8a802724900200400904452200340c031000c080b10f00c54000c100f0303501b9807040025820a10b030406100340d204000c1041102c010544100403122000c140250030310904014200600c1c1c880780141c1136000010030000c0a8591440598015100000c2103402d26151400d00507120520f0040720707044c40701040407641e05401904402002c0074280100e5541e0341071200c4100b500c0505024403a03955201148000841c42c089801036554600e01d50308016546005100c0c6c03500c2800a80040b01d4811041000100a80300340001001d0a005180566903401c040c200303890300a41c180082560f40c06821071500480d80b00b0644507000ea213a81d17135183c880c80d0034031103104120002c000c0d071001240714510700000094001e219000b119502400e81d41c000c107012010f41010794400a240d000c403000c10300208111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 653053947 1250 653052697 653052721
    0x1b170f120d1a0604030812091209190f0605070501050a0b1008090a0f140c0f0f01030c1e08070f03090b07080712090506190203061809071a0a030c08 65
    0x3610315221000b01e4510400d8032500c644103511022142c10070300000d808824485203500418524004a4160350a60744d92104940c46000651503585084c44c10801d583c0c0610706460302514028103424207103249996889d0b40c07261040554040c0002c1180400c03c8801d002d400c4c860f150307202c26604000c0c8040c20500c00010000542e5441a609220364100450a1150308100e1446070640c01a14080d409a4034101000784140d1a01c2e819040d12400b50319681038280303404414071040b03002e400740f641c3c035641c0001900540350000040040000b41c1e03048405a07000010022201c1946460749000d90500c003c0c001d003000d4000c01044145414500c400700003921181295900c180c4a14095403540c0740e0403030032280c14142c21903090100741860161000d009001c108175005211403a000c13322503c6140308241640002c0b612103901c1054005125a1100307200201540900801e00781c88034103490740c22101c001c0c490620708186001000c07560250458143c465138a245510b0f040c009050f141c891100300e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 653055197 1250 653053947 653053957
    0x414090115180504080d0c02100c1803080a02011e02040e060604060c0803060a03050a03080603070504150b1b07030b09060c04080d030903050d061404050c09030d03091b170f12 77
    0x5150f41d104001824000e1401c140d604050303903814180220242207000175500e00305800c003110b41901e4080c01001aa000d0402c495441c1c103a0f00c401003101d031840d10348001c00c0d040b00c4161400d65407502c80109090b854034106004681040100680f01c030708112581e1602c070801001d40d4002c1e88100000c2c050103420001c60141554400000741d0b0766903440001c00d582019990008100340700c0c04d035164081681060549101d01c1c0c00b074007260310081d620b100f040107407440029a941060494030b01070110910301401000030402102c80381c070780709006203940c615220144d84180d03200300c08c54080c428540b900b4040710303030020484020241040e04110403da00c62002c007440e0000e1503a01c20400c2e0405010b4019074000b5280301c030302008a69510700c3c144005001c1d90701d10610840c07802001400c0c1200203000c0c0e9214482c0030300245908850380c3c400f07078000c11030b02c903040e81c01019144a231004418050781400142c41507600ea20341100c0e10022440c81c00514000150b259000080b41030440e20075a010b4a03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 653056447 1250 653055197 653055239
    0xc010606090e18190c0e041203150f06050306180f100501080f06092716090903080f10030807110f030705151c021306120204030f0f110414090115 64
    0x7a50080c0ca4903100c17009000c41c0d4002ea0000000704208018001c0b890714928a1140b42d0f181404400c803c102000c0e00c13807846001c0c07954516280581400554402d17030103594041b030302502a00e644c0d003681e038603000401c4089503110b51003901081041402e040c0d040038140108400e00f04075685040c05040c410031800000d000341e0047e445040021000040002102d4440f065280c0c51503000b10b6601d141501c5001c0d1044010b4400c90321140010712a003103104260000360160340d104584d450303948105032602030103000c89080c40364102020000c01d083c6030082818503c109041d1355910131071b10901c2014050512014031940240b0020007413a221201a42001c5905039000c65136003800034100459800c0003084a440c0e02d10118100c0c4040100a10780c800740d410329201c11100003103410300301040c1d110f00e00006000420b50303e41c8900180d2030906c2001d00c00d00c130350301c0d80f0a02242d49010a080380c2016155a030701c81c3c0c4403410311070301080a02c22a00d10910445a1385c021a042080d4005a016040700103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 653057553 1106 653056447 653056483
    0x2160b060103060e0103170c0a05010609020a0e12061602030714150c03101211100e01120b03060414160602030c060a0e10090201050c010606090e18 65
    0x13150481c1c0d4014220340a2060750100031229401c4880c0454682c0b04072038904002483c203000d0007025143e00784c00140c4030030f0640002402e0306008901d60303009000f000410342000901040340d99206c049600ac4d242d2241c1451400c91940c490143c003e05512540d20b070b03101d241200456140c4158150100341500d41d1102c014484031840242c0301c010f2840d031813800410211030003ca8081126018020590f0321004d944042680e209000c4041e10001d400305550550942e04203204141c410303004102004000742c10404260f0f04d19000d40040c04041c2c18004120175104100103030b41240340160011003007565506d00c041d6998001d020000468060140022404183d500c603002900c080000240103000045010300c00510840724141e040210801132822010400d0242034000c0566960300c00c6018074000c8540c01c0c07028081e024448844101c66042c03050f070740000b03500030050280411 = true := by decide +kernel

theorem cover : BRFrame.Cov 652877697 653057553 := by
  have h0 := BRFrame.cov_init 652877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 652877697 ≤ n) (h2 : n < 653057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
