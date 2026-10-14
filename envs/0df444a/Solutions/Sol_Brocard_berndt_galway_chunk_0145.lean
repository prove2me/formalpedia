-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0145
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:05:28.927618+00:00
-- url     : https://prove2.me/submissions/0f30a041-6b00-41c0-99bb-81add2e9ae74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 25899286 ≤ n < 26079142 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 25900536 1250 25899286 25899317
    0x2070203070618030201110c041503061a010905040c031b02070812121801091502070b06010903200103140106020c0a080105090606060c01021b10060e010302100513170a03 75
    0x70a100003183c6a00c081241d010005540106004500c43e801c00059170340664598010600361514115881501610440c1c200140520752140040e00d103c0c21140c000c01500344070000303080a49a00880d803066540341c8528410b40c1c003d90040c5949407051390031100100041001944a4000344540c141c0c6003d0030403240e0b1209100c404954401d80c070044000029198080154104041002044071070342da5071a456010500719234440e0704848075802c0140c2d54884500e00441d81c00c00c0030b0074031410b00c00c05d400e0900004070062000f901c1c1041c2490320800c0c0e44001da0040b405410b1103514265000542c80012030744d05d40c04640d480320040241c407280e41c40d964504a480c00c0b00c10448041e0690342103107003c03074068038081340240710341e8080000150402003903c1181d40030010f50000c00007140d000d070100c104079a00e0360103003d0041421084400c0c8540c9950003103540003010070040030401034002118481000b40b500c0c802d020382401c0100c0ca03000c4000c0c101c006c3d581d00882c003090f40071904142600d0103c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 25901786 1250 25900536 25900547
    0x4060803072a0e040c03060b0d020307060e04020f040906030b0c1201060c0f060e100f02040803040b0a2102070b0a0501120212030f0d0b0f0103060608010608190203070201020702030706 81
    0x22a9010000a6a1504081c2c90a906019041c0380c0312428511181c0018540410122140140d000728444800186503181000444200b018014000c3d8501c00d042c00150740c010540d41304682c0c480c20110b10300e03411240040c00030310501090451802e00485e020486c10078984c80030f000c2d00e1240d0503010131510b4043d2000c68a00400320150b10381f440020050000503c2a40c000d10b03500d00c252203905410b60143e03582002e13036580020350350041d17010024589800403503001d00251910032603030852034107003049112500c0384100d001d8900c04010000304034282610503004045408021460000c52014401303a402c0694040b05043e02c1d10088034021070082c2406204150480c1e00000c1b420354422096402d00c80341381060036800d013a9000902543c80325203c0c0030002c00482c0036007080028040702030420840c41031186151207041500d01041131080540102006054584508000107584c3d9503400c40c282018148092008285c0040f05201c4400c1e015000f40281910803010f8030300054035008210350 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 25903036 1250 25901786 25901797
    0x10c02130903090503030406021501050f0616050102071a1e090d031a040e0a0303061d130f060c0c0c0b030405190f050d1706040c081501181401020f0d02030304080901020a0204060b040504060803 85
    0x140701100b0860034130000d40e44051038000c10b10c640005424000a911030141c0318074558a581c1c2c1c1d403105075080104d003114000310b1030a480f4012400782100d0a01c50080da0351400400e075007405040d42e0f41d404e04214020ba03c80a04996030080050000742440746440740c58408401c000c0740420308043d8040340040c26048145039285210100001c19515481c4241d0446d40d400320076520b420000d03411101040c2c590295110100490f21030792001d0841d403405a450340e025a010f44100141072080c040040c001242081788032003103180e040e07400c5600e42002e80211302c603404010301a104814650712116044010720200c0d01c5c404141000c95900e00040c0001d440f88803d049000808100014051031402944192048010324103450480701c6c00c2c0080c41b0f0359245400410760218032012555881d030b0b040280c2002c1510110190050201042d0060340d81d00010b40004c041040c0030500c0152640b08020054100d40c000b0410f11600d030341d840c0c404040340d2190003110f000b00e050900120710000000308132030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 25904286 1250 25903036 25903039
    0x1902070302060706020a03090f050d09050102010504020307050907120203010815011203080714090603010902310303123c020906090f040905030a030e0c010c02130903090503030406021501050f 84
    0x6140c500c850344c0d000025800003d480003415030380c1da501d80100f01c0c00301500307641c40d00c00d20050000517424203029003622220707030115046a050004000043c1c0340400c01e181114002d03101d900198450820640303136003a111840b07003141803003c000001c00c2140011822401d04000c6541c0001d41d880702850403140b07880000280104501e070012030290743c0714070b110301e0481080080c491300301081840002c040f68001c0e8001c8100c02d80200e4811344001c1400e8240000c081000600e003003a20481e80c6400c05501244805000d0005005080c4541128bd03000b480d21010907400a054407940188a50b0040340841d4010a200008510504c1440a9803084540703c410003032581d81000144c604101008030741540058110751205882400038800700098406c0c1d00140d1008100c00080b250b035285400c242c1c00d401410040041828805030b240d424405c00c02444049010803100044c0c201529000080c0d8083c9405103c0040e0020707246078041550000c0c0d032441090040b05036680c02c10070202c1a02c42c95110b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 25905536 1250 25904286 25904299
    0x9030c0b0906072004020d0e010507030501031a04060209061204030e1212070503190507030e0906150901030b120309010909020301140d0c03060501121a04030806040f140a021902070302 81
    0x3c0c0224a035050410000040c003c00b000c00040c11501107000e0303810588082120035200c812440c00310b0b078203000721540030300b143c6010081d643c59619800000c01d803881c10074402c04081c1011070203224079501186c0860401500056880300144000d0b80c8104040701d05800240100800e206207140001030403000c003001c4002816102e002c0400440300340d01c44007040750b80d80f00810400000104c580d03680c4110312100e44400b91940f4a5090241420413248001841245d085041200c1c2c0c1e41d59601c24641121034000702505c1e40c3e0700c04010790041c001d90020680c8000724440b401d03800c03180000103100301d41d0280c0c0c0e0960081c1e910034407074007a80000e0050f46200c41460500c0c014500704060300c244020b0182d8140a03402d9501d0f11244200d49080e000004140a14814441070181c090382155014201600f19907951074a41c60061441d03101a082601c500d4803044003c8101d04242c00c0b02e4004c41001004900768200030002d00001e5000c40f8030680300f030f00c42c501003003081d500100e120301c00c5a4010300340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 25906786 1250 25905536 25905547
    0xe1605040e071a040e0109140f04080705120d0c021501120c1d1006050a0801050108060301060810021902061915090f0f1b0c0f0201030e03070309030c0b0906 69
    0x81002030451044a100c041c41142c60000f002004410707001030351400d49030481c0c2d0322410119042e00f0540305070030100016062555440b60340003202451b66010444600c84000c82e200c51034a0300311031088a070054807a20903900007030355200c40000144140c03450709500f0084224016001d9840b000901079a10a11103450010010450540b800c69445031148010b412a1501c819950003100d0b180c040322501d0f20001000c0061a041402e802000b422442c288030303040c000030035002810b0620500946040041d0480402c41d507480175001700740500340303100c2560f040140c00d21180000b0b410140515445c3c3d041e0041c003019140c00480c0300c42c083c070184103164000d021020700110142204107000c4180708180d440020714010707248a00700390800740004c041500c1140f80009000c0d2550050f034107840803004a000c2060540000c6141146a80110b401c4140501c0d400160f00800c1d1402c910301c014000022408201a4001350786c5082d688142c000704403040d11448048840d0003018540e640020b0208034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 25908036 1250 25906786 25906789
    0xa0b0706050a09210807031b0e130e0606130507020303010b070507030b0f06040524010e0402040b07030801090e0a020f060304050705030d05070b0105030a0804030807061107150e1605 80
    0x14a501c06841900031620001c0c0390381d450044d4010306440d14440c4a4001d0003205503903c54180d036040000ba1a007840034030a070042d43c5078010009420142840070316040074025480b4200c1100d140f05220200b0402c10b46a442c4ad1500d0f00c60171281c03507214a000c07048034150016984509406081e1742d5009600710b81c00c0000c2c03000c5c01e9020000170385091082c8400080000c2040728214030422040000010341d04100080c441a1800540b201080c840b4011a200200c00c0c18582c070007410809190000c0000d442d10301080c02840756801c1100d5a041c0080c107035050580142d1041c6c121014070f8400c0021040c1c040a5684501ea00500254441603d016004061801d0f5014540042c003820541d101203035180002403900740c482c41c0050101d80d01062107420300c0004a034060050a0981c09096043c0459440360780070b00c2107020041103d00c0104043d820301c01035600c080410404480c00326038503441030400c07042c18205018444002070038170000c184024800315222644c02084031020190320705000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 25909286 1250 25908036 25908041
    0x3040305030403090b03010311040c0e100c02041e1b02030f12060f0405090105070e090105090103080c030c0703030903061b12050601120f0f0501080a05060c1602030a060c0e0a0b0706 80
    0xc02c19410065066404030303081c403082004600030b61142103030840f40500c490500c8107607210b013a80d090900c82480860000c5440301002c0f80c41d100c08070702c0c10101c10f0b160307440020300804c110061200c9800c00c012a015529a0907071014018280301a8030342031a00344002c0483e928820340e811540f03c000e09104142000440310402a00300700c004b0150780600181c24003040481d5800c41e0343c0c80362607440d0002d000070550440c031603a0000d84182c400001035810200031500c44841844010035103403000803104da00c0f12041c029101c91035001429203500ca1f5a07420000c00307101035400284d034054500300b80040007005444100c070b01c0c4280c64507120b00003451042908000d10b00201081c0c10311400066101114000b481a52a0300105420000d10008020820411100142c0281105034008191030001c24000140294880c4030861740d46d9688c46081580d103001c5503081c000035014450701410100304a4a9045034005c85016a511f21810560300100300c80958944035100651400300440302c0030510300d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 25910536 1250 25909286 25909291
    0x1e0106090506130e090705010e040207080f1308070b0c01050c090d1101090b040902030f01060203030403051603090f09021b01181b211a0c09010e010903060204060e091602030304030503 81
    0xd140c101243e55920302d0b4002c0d1450880d5044400d4128a100744002e41c0c0203083c208101c0c0090300d0842c1084000c3c0e65508071480341d0840c14020080c0810030000800300010324001814508040d55812650b4a65620dc00c1e0088043d040c81c039400d2170001201f000380c000070764000010040901d864850b064503000100f4288500890410504640100e00e4401c01401400180000500141c1d44e181044240f441644182c03c44000c5410030424040031136441000da0390f000000202c184040541850180c0701026285e00c801c1d400784600030f00144a07034695014250102020540d10450405400c010f800c80b4651088841181d62101c1d12070003250302c1c2ca004119034580e5040e9080c46a0303c5005412500750303404da49c07550315403402c1110010000804032505002a08114034201d0741010400034070540182d10019042180c03c2c5203c500d036038030030f6000000840d0494005c40d52140c2300c140042408108295041c0200e01c45004541d0b18551100c000d260340c40164051030641d140c5540484032648003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 25911786 1250 25910536 25910557
    0x3060f04030503060d0c060e150403050307021203090406030818032d030c03030405010603140a020604050609010201021605010e070b04050916090305151009020c060105010e010c0501141e0106090506 87
    0xa417410001000721000748060b140c96200d109010107000700300040b490f140750645408080c24001003000540c0041034602aa1381203030681c2030340342c10b0004546035014044072968800d040c01000000e0014080007040440041120b46050305a00814950f80f00b000404200302e11407213112505102100d981d01002c101265001e1342c0c64800700e9130030a45075400130f4501f555030380d640340010010402c41c254200504840c07000501714055054000440f240991b1048174014000001d0f01c21040e072003903041b105000404c83c91a1648001400c0c642d0081c0803040d07110150340300d04c041c045440d4800e80c0c2510101c900003003501c809613840480010416a001047c44240655490080000342003842038030003c2c4031320140380a0f949000c02821142154a0f0301125a59204120b1a52005000b140e001e040d40c00a0070402072903c55100100d84801481502900b203528009002e06031600208401c0d001e8210b00c1103002c074410707201040d40e81540c3c080c4901070200d070103103c00b003116060200141150854 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 25913036 1250 25911786 25911799
    0x306060108130b01150206070f08160302090904030305090c010212070f02030a0c0b0a031505061603051b0a0c06020c0a03140c09010b0d050a0b0f060304020607020301020c0a05010b03060f0403050306 87
    0x503550f0b20183c1551017a0860040c51866801042000c0d504101c01540401c452820b04090020264041e026040180c049805c82e05510100040207029404035102030740040c14034075641c0b400d400e00900500065825040354007a901ca403500c81d42c400240400c042c40036101c0c042c984640799a40fa03502101009080b40c241c000c01a01e44080391082a42d50300078000410701707070340c0d6140c148030050444d1401c85d00c0c082008184501840300f0f803076080550366481c09021030b4140344001810261018007503800d48040402c1944242d4030149008101c0d1300d4040e200e488081103040d00d40c5001d0340c4466469900a4100d00841000c00c0898466000400956581d40642d90b00d0760b00f460110350000d1091700b2a003044040000c462401805511800380c0c0140e06010401240360b0600c00610462046034909101d800080082400d40d900c04048910581d40140210741c0c030303c03d080b0010b44a000160042d1155407a124180c9102d0601244840c81954409a40d011954982c1d0341902c0f190805081f094100d078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 25914286 1250 25913036 25913071
    0x90a060305010606080703051e0109050403090801020f0a090801090305030f1e150111060403020d0e03071e030320030301270c090f090e0d0809030c011b030605030109020306060108 79
    0x800030f1180714080c04031640c8841c19407402820180c00e8076009000010340c141d0740e4042d0307000b2247e0302c0007041c15201360020108564a481c1011102d40c10316800c841400c0d480003400418000803080201094016078682000c51562920380d14205c60704240050702281042000902c09122405010707402402604041c00300c040090f680182100112803441d01c0b43c4590f01c80700070329a008092841c0c8040700e28010078261410ba40c000751103100d00d004200a02c66a2000c00845650600048014140c0703800303c9040c0100c0c65021803c1c1c48411322083e4082450a46040b202e8400100d1402d410513452004500e540d20305550300d0030b1042ea00e240c4290350599105071500034441c90103541d443d0f40c005d40d54108494240300090300c80c00c070540c0c030454000307180c90804c8180d003d01003017403040c500041c14181203139513445018a046116040141e00c0729441e080c0442c2050f00019000c040725101903a0070000542c50f5024942201e003d02c1c406949036100d04001540e030b41c41285000c5c0e0200301120b0040851 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 25915536 1250 25914286 25914293
    0xf0c03050304180609091505090a0f0506070305060109030f03050d0204090207051501080a05060f0601020312010f0609090b01020a02041a03010c02010e060f0708070c06021b03030610030501080c090a0603 89
    0x41e000764004088801072030050fa0851091401500c01400708054108414406559030074401101c910301d2804898030340b80054980c550a010380401070390004a5891091307014541aa1148801c443c000082840c00d00401c0b45940706003181c0c0c0a50340e01050680c00c0315000d45060341c2c2900414400c103001d580800010070841118009002100e22807001418003d10b415203011625105800800544d40100360030340106000058050300000c10054000f40d40d01c92100403810342c82420186c809040f01040000b4501c8402504981105c4036a0703075210109442c0e07464a0262a40700c1c00701c50044e84034010140240c6096070100000c8000201c440c1c01142c16540824251101965513001603503441d00c0d000d812440a000d00c0350b01020340c0c0f015031800d00d400000036040802c040c014404200d004c44040c400c101550381141c005440000050a4404005840700c1c0c1e01d2780202c40641c020648120a50703034050107406458181d40703d0001070a40c201c0da0340b00384804080300500c1d0240d0562202ea001012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 25916786 1250 25915536 25915543
    0x301230130081606020c0607050f0417010f020319060f0501050a0e0d0507090b01030b0607020303030112080705060f06030f0a0804060f050d020d05040c140d02010302071a09070f081501030f0c0305 86
    0x20584580005601d4080503141e042c10414020700c2300090000c1008400307506003029040344e060b2001c0c075601c031094a126441e5a03004101340014010b00d14400414132481c0c000030701c1003441d4840601001d20000d505c0e81c0003405550941d104643c0401d00911070000b00c0f50040c4610140f8a202030094016840c2546a4615003041948032030180c50390ba4aa030101964140600c000c1c0f1501551420b15143c01c03030340031a9a0703110503c5002075075058641d0070800c01600008440701c564120045422a09181d07803a040341000566484c4e201c0e116040c01d0141461001c42d811080d190441c0e10b26003440e2404c64140c2d16141c1c0d00100c0c000300907007046814900000b900c00340901401e8454002854601890581842405500b00000581038036050260543d00d200d95186110350a103000f58072041b05240c0360060030f809000d0020003005000810403080710000d082c0003102d003241024032800d40c2d9150300c40c1d285c88502008640031800000140041001c12401c18940c81c482e240c581d500f0396403610b50504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 25918036 1250 25916786 25916827
    0x30e070e09010f050903160201090f080327010905150d06090c0e0105120610090306051302031b090c090d050f07062607030f020405030123013008 64
    0x500d11501001c0c0900752009215900018011140400c194188010540d60f81d00980c194100c840b10039402d803500716407087c48031100810000020341c0320951640041a140c2d0090a544c0441c160305000380301008004ec03c0391480700806840e01c54004c0e09200c24018616856000c20306c0c0e07420200043c09040451f40320f25401498000c000252940c015180105181c180000e41e504101040c03040c10f4404034201361094004070304541c0241201c0308002d05071807010032079201810080ca4481000360100c0c00105070a40c90b84220142c1d03000241c00401c8000100ca6050705a40110254001640f090241402024400d800030208089244603640c0c0501e4540180300c1403019804c8030504029450b04075a0f40012071f911840c11103d140b24503030445040c0c2c1c1d001401c0b40d04050301e030620a440704c44594100d03406010090028840e02c842e2100c50f4100020301c90303065140c0c80e01400000780b1101d0603d00300c090800c4102c002d40e09025000e141080400b03502c03005583d007402c1007020103080c01245501c00c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 25919286 1250 25918036 25918049
    0x90b071b0209270105180d050a030c020109060204090507021e03160503090a0f03050f010203010b0a030207020a031506050f0f0904120203040807060c050607020c010905040c0302070c060825020a08030601030e07 92
    0x403645401b80a10030014a01000b600c5141c0c0208007910205402000b620388443d16864000340e440c405031070030ad000d081e00742c5000c0c295510004000c206107001d82c0040784601c020f5022203909026000e000031580740601452841900140401c0c1c140078040f0184d942114001c1d0100da050422010000e4206020380d4403000c44c0c4101148100b041080c2881b41103425415034000310700b076601d4070301184200d1107116460001c0650006042d0110340d90210344101031508481080090000c41c0221401849507000d40b900c6900f440300c40340c02c0d914141d0343e022421500a07003500b245803501d50380d01c001d05d12005140c80550009000100d1a00d004000c00801400b2070360b114207051000c0c1c100941420303000f42000e411500595680001641c00081d14800c4503030a40780041c1d52211004228000d0080303010017400d841107a480081d50344c0d413040d8500e0103051042c05000d10f2504820441084400408407003000d60040e12010740031039000809140d101c80b060601003209844190081d0038800641c2204 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 25920536 1250 25919286 25919291
    0x405060c0309211908090409020105070f061a0a1802030408040b0309010c0e180c0f040803030f090706020d0210020708070f03030e060901060305070e07020c06030109090b071b02092701 81
    0x94120400030401c41d50b02044c1c030307103480c1070803034075074688030403510036080c100380100d484510020440e44681d00b1201f5054100b60035187d420401e2402402911112031082144841c9809094480c40d0045c0700710201c0b0700d011201d01c030700f4401001c000d020750402081954000307020f000020707e08108000030741c07203403210b00c0c00000c00380e40c0f117a07010300104c0341c40314402d010310000419040348140c01c85940780c00070350b030310344d00b43d03c81c00c6400301802c03107100b1500a10741d0f500010043c01a1000701c42d03011809840c9107810f885c00f0684582c002c0f40d46060640c01100180d10180c010480c0302441d40c0208289801050043d1400e0416120340034040d84080040300000c1d0b45545072405000d00303100190b0404c030034400034041c03245940c542e944c1c4c0d5001400350500c034105c0c802c08070b03400c64004c01c00c03c089024050310003a1a50f03920401075005200d10300055407028091400207101d07921039601026800401000c03070001e511641c0a00144100c003c0030100103442085050395000510910440c180c020b80001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 25921786 1250 25920536 25920589
    0x1803060507140418050c03010503060a0f0b04020403030e10080903030c070204061505090114091302030604060918060f020a0f0c03180b07020f04050f040803040f0c150e03060702030405060c0309 85
    0x10380c088485c024450b402d8a4000d00050000769004182e0540000f0180c3c804074002482140d03c034000d0108c80b50440c1e1051000030b0001c101500441c04401c103c00486401600c40c4085100f030b1600300d0210b48803482c030740003000084c0c0307801c24030006440c460380007030710000b03540b074680d4455080701c1c524410000c042000400d01a10a41c0e00140171483e9800c400d4003039040207807140124030280104012014030a4001c000590540c95550107440140000c040030b20485183c01594118564250029103c8a0802c500d07968511100c0c000c0710f02c0600a035031202010303054074004480106044008a01f0882e05001c0081c0c50340c81c034209540035054441030f1907503410891042007440b10400c00c4140c0194102400c100114082e012429448ac0e004000b56680343e483d031078005280600f42100414400300f4400102d02100035403e24484600c0c1602d03104981c0d401c1d00200b40e92403000702d5403074005a004000c18407181c01c14902030300206140504503420503003a0320003760300100390400a29000702440c80c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 25923036 1250 25921786 25921829
    0x605030108010b0a0e15060d020703090303021002090f060a021f02090a0e090a0f0203030c01090b04020f01080402240904021b0d05070b01032618010f18030605071404 73
    0x4425140703a04a5801306410316100601501039401040c426055843c1c03505400c503920f0f41d00848a187c10341c00f8045580d14050b10307002d04482505c0c001030b001841001484074030700c042d5100300c0d800d2810080000d00c2d050801020801706600400b2100f04501414070300120642c0e01c041a090321184140e0090b807941130060521000e10b03842e034080c0742006040310038002018000709020f0103043d0010300d1800c4001850010074038500c15001c21400d1513103004c415000b441071221105008510886204171344030310701c1004580c2d6003400d55000e940940400041010992007602060a0f107000078040b80c1800d03550000a8200d802458003000e03108908104490008020b200802c01c03614a4108130703040c404541c603142c04016050000a12540c0c980905e5241e41c034100071883c149031900e401444e80c455813020701c0c00c0d114021000c020302040840311207142c400c1c0154111482c071444540f10b01d40c0c440ca10740b111009018003900c1d10060080c03200303060356010607030340090020786244085403440b50740122 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 25924286 1250 25923036 25923041
    0x603040501052223070308040e040309090b090708072303010302040609060803030408070809060d020903100507050a0e180405060f07030c0c0311010b0405010f030201020606271e01060503010801 85
    0x118950f44590324118410006500000b01151020b1001e4200f600c0440e0401c00d03071420f00d0070381015091321404100058220f41d1025458801c42c4690b07035420790f4603075501030b00e02910520035a092744500d490b800110b03100e209500342030340300e51a4a00541d070025040c0050302000d26804d00d452582c80c001005006508044c00b42e81300a00c2c407038804101c142d00c1c0060051700c038007001d44000c1420100180c3c140c2072052002c181c1c3c649d0030000b8850380ea81c010100300200227621a4092070301038010050160110781d5680b00d00d5110780c1c0c1756102c25281c6174140c003013182d440d05490f00060b07000c090301103282c4240140d607010520480c4108024082401c04840440a445004000c03400705420080300c0380190754031606400070680e05051240007100780110b05400360010702840fa41152a000000810f43c03080e4000d8801c80c1d0003a0282c4545460302014482003070382c0c0c2c0f600441130030000a41142480710850003d60f002d4034080e221220f1301c000001801176140280c0c4400c0001c2c44c0840144407086003132 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 25925536 1250 25924286 25924321
    0x20a020a020333040303061d04050d09030b01140a0315020c160510260405010f0c0207050d020603040206070b0403050301031202030309060c0c0102070c0308040303090614030a0515060304050105 85
    0x4414210f541d0780750003142da03203082008000d0808880c0d988041000c26020381c00840280200001100c0202c1d03080c04141c0301510102c4d001e86591082410602d0194001c09003038056982010b0700101d66070800c80d6031019803000038040b94005040380400008a1022186040c074407900a0000da13403020b044200d0b92900b03943c0c40703500150103074001013004a1741d03c01010110b44112410800380780c081e1141480505030380300e100c00242860030801c020820406500c150b100c201d10540803c068403040b86e04a035204e11602036241c100c003080040c01d0140c40d103400616030040c4000c0880d440e2180542c0c4084001c10700781c804a002c0360001c0014410030181400b038032030000320f17840250b04514082071aa543c0360340250041c06030117000034800444c42020340484110340d800120b0928160b50724034201c43c982e400742c40107038001132900001241c230301d10560700d0490100304003d0300d44c20f50f15141c6804001f01005002420b030000e402c480c3d00c03050380792030700610310a500640001038070b40340030200c211907254007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 25926786 1250 25925536 25925563
    0x30c0901090b0301060207030201030c09080604050f060c0909040f020415060509040605040902090f0403200303010911031303050a020a021503060f090702030d090804091d010f020f030103030e040f020a020a0203 92
    0x43c801842050350005040741120340903e408106010b40d0001610800d80300e801031401401601c041109000c000600110203401c0001102c810741d80c0c095610180d4000d5108182d481103c9070702140100303885046401031036000420006140034180210404800c903a403003e4041400442c1107011850140b003004002c01040d6001d20000040c0c3e40000c0c0a0b8400502221400f00d0280c0420140741c132507010140130312190410842212020762034190b90b50000d01c606a045410840e900c030840039030750182c0707000d849507030b8a9205051030707941c060707031140c10403801c12003140301e0f1400b420056034460380802c1c400800c0c000d009640e410000d041c021861040b6032514001c5500e8414020120b83c0002103403042813803040b0005007414a0700c1c3c21100c5200350307031245044606000110648414141e029600c0014100081203060551003d001c182c0c001c034030000408210a20041011900070b88030040d141000410001f8601c0302e80c460304089070004c00c5110010707400b4012002c11400c2c01c1102c030404158 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 25928036 1250 25926786 25926809
    0x31502030103240e01020c0109060b04060506030c0706110a110d090e060d02030a0203030a110f060402130509010207050f010f0b0108010806010b0708070503032505120703110f030c090109 82
    0x11034498020303001c0e9100d088514100f280070b02d541c400c03890703500111110310340a00955413040c6200100c0c4c068500c0040a035980341ca000c0c0c0140c16072419200759400c032000a42101e04564520307560000310307000307a081a01d00c41d8a0f14007030f035021040e50000300030006031034503400b0f4480c240717100382490201ca103d91034041c40742c1c0701400c0c45504014807010361b0080007156040c0d18180b1034030100307051401c000e100035010700c004075100e89580c0d000345040032800c1051041b900c03940c480d0003040d03541d01015034000c0e4004000ea40707094803840c000c2e0000741c0c1c04844040003500c0c1c43c269540d00c91509554811852003650b40e0b19019100340c0c050300404082900900c0d020794035504007260b554071144107103d0920f405400140d00b10801c440382054480f4103400000352616880c0a0b50f0000050a032a00c1140f02581000c0c510f5900700c1c00f031002d480030300c652841d04c503203a65a490400d60043c2220166400003e000303100302c54060070b004005510804c0c04821107030b11048402d00151824a1940003040c9844 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 25929286 1250 25928036 25928039
    0x303120216060b01120203040b090613030e04020901030612050609100207021f140708030613020c0309010815030307110306010527190501080604030f090f1e08060f010315020301 78
    0x140303000036842940c0c10030b600003640910400180c0f011401300c40c03600d160305e0002c0708000921086502244c4100303512402e444032550342c10380b0125440c2089000401050380001c10300018200b03036000d440821b1045c10300081c540e071604003143c40502c0c642011180c40e07026508110b940d5906000c1c40d60394214000040d07003401d60a80c0002c0000c641c5c801c800025501740e80d0740701101d034030800001031780c02c01c1e40f44186d698003240e00b014002030348200d600c10301500300456600c03581c419034030803901840d010380040c60406044000440d2003500140c4a0145011003001955480c2e4080c0028400b0034420115141010702080c03c0c5400c14105a10507803049816031180d00c6489241000304c40380e030108071820a1280c2d1002d02c4034001d10005902c104a4a20380000801c7c0c1c880000b0764107000328041e4581811040c1400c1c011245828640907609503120510020089044c03042a614003208802c0e14020700c039034803081c500c2d00e00201240d00c9105049824010001e00040b00000c58031190528025407866 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 25930536 1250 25929286 25929307
    0x20f01030e0a0311070b0415030507020703020a030221030c0f010b0d0c0627030b06090609010b0a03180203011a01080c0408060105010f1101060305031b06040b0703020702130c050403031202 83
    0x1000c0c0814043e0901840ca6140314034014140a0340000c0c0c01d54032586511507442e600c084014001d901110000b2070300e04404101054000100b0700b00300e1f035004114011007070960b0300f0302c5a20351002807000007500300c9210390b000082080c4007601c100749641005002d0b44012411f040d00303484162914901540c0c20305051004211103030080c500307569680c2040119040b0f00d564140b0b0012821075660080d8140e64408000c00c01c01540c040d0241e08200d845060703d403550000c00c21000700c28403c00c402c010f010411181000e020380c010b00705c40c4240c3d00a082240281c0c0e0042401e407108800c8001602149090704a880c1d030300001e45070340040c00b03495900d0801c1d081115040d680e54040c0611030510401001c0e01000d10f11510191380b40b80f504000a1299560328504140d0f01c3e00846072132803408400744401000b18000158051007650821000011a100c5c00026002503020304400c1e41c200345d140550401a40046c00303081c0e500d007096900d43c1d507698510704005001100d0311942d003211600410100006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 25931786 1250 25930536 25930543
    0x60509010b0a1107030804030c1a031501180504090507030b070f050d1802031507020d020f030d15080a050604050d09150e0307081f06090608070b03040c0e040609020f01030e 76
    0x5200030341002d00070302d64020003c625100346540010260100060302000b040140e104050440f61805052500001e140d8409141400200c0c0c1c28150039001c200c2c180c00540c4605410442a00d82c0480c20081c40d0312138020601361410f03a0f80030ba5403030344000b00c10000c00c15120710442e401421403500010242444030014150b2064007070f208061510fa48640760110040c1042407600c640c028100c45000c03401403440c000803041194410058025040007201c01d03400450618541c100303200c0070b5480c0c4950520500001d2410280d003c1681b0280d110208000704d0030840c0c000ba49001b58001d00052406181403441c0c484002c0d1203d0411168050800060180400f1520704c0321080c1406100c084010012074540000e56001c01414407800c2d004040704121034140e5041d02d040381c40c09124490f1215026420b441c07051003031600c294042402001301e0511200076681003803050a1a50a940c2c4d6980000c0d01020b00396001c0e03070030315907480e028011803400e480030808611007130800380045200030001584 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 25933036 1250 25931786 25931797
    0x605120606090405070c030305010501052a0708010606020601030506070c08030703021615060e010509090303011205010b04050c09040f09020307170a050f06090d03060b180103020705060712060509010b 88
    0x80408240400c9039660380005450b04103801402c204058900712100800aa10344041580070030703e403100200b40c2d5442102150500210207441c460f07000030f6030500c50f01640480c2040001801112800701d02e5050a001d003e00070306459008000a50460801901300b09008c0c011106000c4c0c41000c4d140010050350503258030807201d040040e19a01c945070300c5c0100320361410340103100807004a4044000c103840d038880c105540d10310011003916030301c0c0da0030b01c41400e900b96103d114170b6000b80010421140c600ba0a6003040348500300102e40040200082020343c1c906035201120041e010500d00058241807242003505a2260f409004a00e41c2e40c01280e1030b601140034a00c8484040d40c112441800b08004241e8503a5010b0b040350805466000355070344030401a101d44d51700380940c0c860b08920b10f01c00e0240e001520076000303200e45044030000d42c641c3d85d41400905c26045c0b58080c060600480c501703003e000d10401141c2c8902d080c1d45419041c40084031080d800180c8540441d000601c1004c080800340ca4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 25934286 1250 25933036 25933057
    0x803031308090f0d140f06040b0417040f09020904050705090a06050a0905060705030c060606030103050601060507030314090c030f03070308060402030a0902030a03110d080103110d080408070f080d090605 89
    0x603641d80a04001c200f51048103882d040c2c11112540e6041e0030440281d0a607081441d00e035080d204070750b07108140a40c03280d10584020744141c86a8000c0740c0410601c0c070b000c8591011384142186001d64402c2c02c949800443d5001411891f03020440301ba071800c290203003e43c030244903d000c41c5024651000505014080e0007110b04100c000300c0d0305d00d0100d014201c840702414004296070f456100614016030341b58009a0411042d001d80c00120742141440310030385c0d050fa540140a4400380e800d01400701d401d0307048001c0582c101922400d40b000314201c1700b91401d01401c00031000c0c050400c1e804050600d8140c0d004c01800060b8810060600481e07400510b07241c00c11402c4501603980c0c0c5822250001514001501944c10300070344e1201001c040e0015407403100812100140c51001025140554191200f4840135094100a0009004514003a107480401a00c034000c450f040c252560f03d51440c0003241e410511381181c0112040c442c4450402103c01c2ca03030f02501c4d160003028106040107141c1d014151101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 25935536 1250 25934286 25934303
    0x30705012c06040f030b0103021903020a0603020d090605010602060601200d080603010b04140106030e0c0a0b160b010b07150b010507030f020109020301140115080919060e060405070303080108030313 87
    0xe110356a6200840f8010607503070010720002501da041c1404190070a200c00c91048004100503a490000c1640d008100c03074006000900e134914100095000e50300424640500300d0340c0d41c49603800250030380301c3e00f4041c00e05a0b00521003894558009000814040b00d46031102c3c2c0504030309540340000040350180b840c0b4a2501c040c1c3c40d20f401d00440d02508040e00303103690050030f00c002807900c98203050543e4100c40d0f06030342c140814016a1200358984005104141d080204d40b28280000b036601002046440000895003802440a4032240a08002a0044440c1c1603000038803105200d500e80301e54500c5031424204000c0c1c0c0e00034200103007143c0318040d8002c00f48a0304117481c006e81ca00071351202d810a0340244c024003c0441136004c106e1024024081d10403031a092107105e1910341c0c07044642a00ca42c401d50700820750711004140041d8141503241c0103c40150300d40c6400a00000d0500c940c0b80654868801014404d0562801070030003107050700306640540c424001c0103001c1010010060380240c004159 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 25936786 1250 25935536 25935617
    0x612020f031506040b012102270a030204110913060503010e030c07030212031c0c0906030b01140309070506070f0c05010809030306040207140d020c040507020c090619030b04050a0203070501 83
    0x6030340c81141d28407c00000d20030160341d0071803111650014800107001020368802e0511820200d50780010744094a41c11010400742840142450303400f2003518110021481c6c11b201070b62001820711030481039102e002c642c48200401950500740145207408410501460030035043d03400c00c95440d11540b0010744200c107103140d41501c0c0b800c02c0c0200d414040a10b00c010b28418008031506024004203064a000a9900040000d40601c28460044141130595501071161000501c0d541e0642000d00800c68a014800002600e80c4c0d03210024012103104642c01c61125030345080014034003041d94801030620007001c08121410401000703c1e80d201804480058442d446030030140000246a81d07407200038800c00a40b800150f0700002c101c00c90344003c4070180004c1d40c43c09012a120382d039408116400a1155000c5030040c41c1c942000c0c601400f51502d090202c5550f611147c05078601601c1c1a5910b801464485080d4203050291130054542806d0412100050786400514050b60680c05c42001241144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 25938036 1250 25936786 25936789
    0x904020d05060a06030209072c010509060c0604110d02060304030309110d030809070902190309021504031506080a02010f03230a0606081005060405010809100612020f031506040b 78
    0x20160030322900301c8201c0c0c0030381c500b0002c000e00520080c0000c0e44a80c40700d00010703c080d8440d0b0b0114842c41041c90f0340b101a01c0e168080016410007954800e8140102400361004944501001c0c0c0303d940840d2000f040d0506143c10500001c2191078403003400f42030b5101c905405a00c840c000c5035005a4545000640d9030740c80d00b06204040c451484d41907100c15403000410a069104040b60f000d11280030a581583c0da944445200700e100c0c0d2480700c01110301c548203e82d1140d0183d40a141d182d03001071b05488090805042c8440c607035105400c00c88060f4a94400101c404216200f5000a0b04003d001010300e584550000380c240e2400c01010700c00c040d1103801034481e145518a81c100c00f44d5004036514068200030b054036010b0102805604001000400014188201c181041e01100e8000d4222460f01342800c004540241d0003e01c520500d20a401f203501c200303846481907100070003000c0900c0081901c90710402c00c40c0c2540142d064030a2307126000505844080b480720b1908114112000201c2081100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 25939286 1250 25938036 25938049
    0x5090a0605030106060f080a05152701120c060207060e060705010e0105090d030b0306010e060105070c0b0d270209010b09010201061a03070e030d09030b0a18030e01020c011d090402 79
    0x4001d2909075003042800580c0980140f848103a0402c141c49609580c0c4d202030082d012110205d803100c483c80d45a440c600f025041940c40030688054030103a03100c11814038144130300d442c0340a0388288111014902c8210900c612040c1c0c402c06081c1c2c51001c3e05c030940c60001c00400980c3c16a41e4980b01e414006010b200700035095001c4c084402044000340f01c18034050800741d031284003011449011a0801800301903070310b0302082c4541641c151410a4807503403200b40045415802c00001180e0151a100c0c01041440041002e0310b040074a403400400c1480b02c4003488107810807489008080700c02c48021001c0180c3c0d03503040c075505450018101035103035168040100d014040a5010142c0b8002d10709501c0030003050040114843e0b08035031141241c0c0580403080c151707586104548080000e820314400c2c00081d90134080306403c540d0040010036140414030382c0c001b50303a6505208801142c5626584405542c044c028400702210034244582002c044412441c103144d44046072a1142c0e446500081c21548e910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 25940536 1250 25939286 25939289
    0x2090f1e0a02070f0f0b090304030305030f070c020d0b01150305060603062407060b030d02030c030a030507020703140d080603070503100f060905010e0108071a09010804050f010e10051006050405090a06 88
    0x918407030384910035092580c2e0100c0140800e507a1b081110002589015002046804480c0c0c1a9602807543d510b0050115040201030220800c00c004001c5000141c0d0328401e80b10000c1d401503080891651500d0720074a407150301d901c0030748103060800701000040d94425080c1da6100320155242d40701452401401aa0a103086400d401581e001144560920840313900a00442601340c0072034580340c4c03207505c05030fa407405120b210603101e80c020400c84000f103210b0340100e50041d84a004940384c0c0c039260355441c8200c1680070001e16050f807090060005e5186e11004e10741c0c0000d070a40c040c108640c00c2c1004203482c1d0342d012000854480d1540c0300d080c440c0095a0003403004011074481003241e56142c0c130040104120a1007400010320500340301080c020410340c2600f83e03050b142828103103041003060040d1043c5c040200240c0e0b0034010b0700c60360080c1041c00e024455a11480d00d000c1c2403801110700c0308400310350024044101e174a407956014091035400c00c0880c0c0640b9000c66040960355214030084014083c00e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 25941786 1250 25940536 25940543
    0x1403060f0f27030a090801050c04060c08090603041208150a061d1e01021c0503010509070323100803040b0d0e07090606020c0f06070218060103020909010e010302090f1e0a0207 77
    0x1400b095542c0c0b03003404405812075040c21741d1581c070510751360703014075080c0c0e90182c0c0c1195001200704030400c00e41c1d00aa51001340710384944103250a000c03d0000040454104940944140071070050105c98641d2084e40140c0c40780d42400e107840d1501840001c0740809101c3d01a400600c149001da0030922202140c07401407244004080d20000c002a02c41014040d5140c0c5181c1c0c0503104100d1035042c190907044c1c1340307440c000c03d940d07805003180c2c640400c00c6207004010f4508810300d070fa06d240956407405407034100c00ea028078200c85814a82408020090700c40d940c0d0703120707001c950404d010521514044008459049074a00b0780070402d240a11030b8942403003281c2e44402e06903450048005030342c50f00861407440303c007170444029100f440c081e401c0c002540b00303c0c41c000790300c280040c00804a4405888001c2d0304140103160060500c90380c400801c011010030380110311075030700c4903004000710f01e0900480c2e98400c1100440c886a8100040c080c0003071901c580d1308401900200b030020343c100c038650f4140d85440d81c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 25943036 1250 25941786 25941841
    0x50904060b0406020114090a1506080a0311070609060c0b0411030604050d120501060f2703050f010606030b01050706180213020901090603020a023004060503011403060f0f 75
    0x1e0710711030400035074000c1c8140fa01550906203081034400212041c2803103224400081d00d2031190b0b82d642e00d2091100320709002000f648c1c0d1000814034641c20820b4100e464401e44842d00042e4021664a03d04601c1c0e0340035408001e02c0c0031080c007002d0781c480b441c1001036078441d044034040d444528000b64811121240c07180c052185030304200501400194186461b40b843e00c920b00c02c0026001d10000781c0c0c0b800d028000114207490900072445120b1030003418004e02c81110791406101c0c01c1300703160059030700d58004d85142d03211941da001c48003820302c076072801000e00741020401d40b040e14002828a0043d080d01800281d502d9508000038219880d80d82c01451b401800042c68900310354050009410401c000c0d070008003510320110310a4001d1089605001541d002003500d05d00c861220181003107071804461900b0741d980400301003040e4100c0a48060000340c0c89071520703581818400f20807007203c0ca9070584a58807442c1400052503c1c19540f076004138403001d40c081282c0d9455642d804201480c035035400d0000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 25944286 1250 25943036 25943039
    0x60e030c030d0b0d11090403020106050a0f0504050603061302060c07030209070c05010b030708120c010204091406011202120c0c0f0a060e0706020106180b01120c090302130504050604060b0105090406 87
    0x1002000418455402030010842e4070312601c180013154400040085c15540e1702c258041091030810750190748035200f0710002c00c041c2e80b82c0e800714800764103070341c802400010501c1040c00380b40792a000c2d0302d80c050015801005103141c5841c0040440c650300d9001b034064000041c404a02a400380036500241da0060003013040740c108060010096220704100f640c0c15460700e101074900c1c0c41c001c9101011910450001c103440768240040e0900d55000c450007141e1036508102c0003034004070501a0441140d4401134460151820100141100c0305a0103000d00c0d4503c100422142c90341c0903440e658100c940150031030340b1001c840d404986003585802004401c2e100780b0030060700b08203858003e00403d40c00802038401d81ca42d06d2800340d00b41c0b13102c2d025404031516805034104c10341d0425803019194800524003241c41d24040400581203c18036800e80000136a0f085090081d820001c00080e0a061a5441080107141c01d484154507100701520080455840e007040201c168406c806070b1380701c85030043c020041c0320f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 25945536 1250 25944286 25944307
    0x909050f040b0924130b0c03070f05190503070c200307060201020f040e090c0a14091302090a0b0f10090302030f070609060c0c15030c200a020409060e03 67
    0x80d044400702c80200d00c000005100700008202c08001e05030780d4000301c0c0764040c043e03001440014001c103200910742070480044003142400c134059006281c402e01c03040d80c03403e05100052074182d8101c428000d02404000000c64200c0e030020744044411540390868807511480c10854045480090261a400d40000560000c81ca81c0c44a005480c608504803485590303170f58801d074240d0180541e5002c490005210400c05002c10400750b95204a110050728106d40b11040020080521900024400105c1c80c00c04121402c01081907030304518a00020000e850751580041c1d01c46100400074407600340c41d60001c0c0d0181c0c81d03d803024a207880008141ca45041942600107001d01501c2c0303c00c0c4d10a10a040c814001301d140405ca0f40709442c0165070304103e050400c0c0080d030346580c4450045900b6514400006901e09410041041a124555002c540504a10002000d4903c071070b60003130060610a9860010b0900080d800412542c141c40c0440e41d1106c601b014001454214101c00311400f0014540510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 25946786 1250 25945536 25945561
    0x102130305010f0c030c0504030b090c0603090601210807030f02010603080c030a09290a12091101020c01030606020c040e0a020a0b07020109090204180207140a0503030a060b1204080703090905 84
    0x60004890130844501d4060003102910428480180450410001403000c1850100388a40c0a600071003101d195000500100300b2560044880103010340055006001000700d1004244050000980b01202420b2075140c1081e076114214008050205007205000224000e4004000843e0001040e07925040c0c1074001e580c030785e0301800c4610005400f90300086010000f4180c0d40c50188000c0100c2a01c0310108100300145500c82d00021090010034680c031040c03010340d40a64907501707104110220038500f0000001e4503052101000038107040c10148144106640050b4004c9403440840b0301090540b4005d00300c42c18007004440182d0445100e005c04103001c80302d0402449818800c1c0d0f101c034603055a4a60740000c9001320700580e1401c5d8018005241c1e03800503900908242405890080c2840010540c96072510511060454540c6c1001c0100503420400f4821040100b0003020307100d1400134001c8100d2086040148020100700b404035240082c14814000078024102c0c0420400c19420009130303a203039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 25948036 1250 25946786 25946801
    0xa03030f030c1d040b010c06180218040f020114090604030501020c060702030406091a041e05150405031f1103010602010f0b0111060601080a0e101a09010605030403050c010213030501 80
    0x11a0400b04480c002c14442d41d0700d07070150281e1034000340d000c2c0654002c000241220b8002c040c104000884c2c0d031808681c030b40c4520800540a214048a40c032080c0c418090240414251168100b04190800000c180714148494410340e09213054142c0c0c00745034100d483c49000c1c8983c03c45d04480d002c100071003007100c154001e0003640a08422a40b9a68414000301c1c2d59200b18020100007800d0b0160400c0100091a0090000b10030f08440e542003503280c1e079004030501e190013481c0c02403805001d001c0125090044005800960114141d403030513003000c002c01c0e522030135038800c3c0e00700302100c2c0030f0651080e2060381325410202d881c1e04046d9803965100b00090103030001c00c1c3d402070344a00d8025484020760007003220342240c101c0381c0e0107040c81d0350701c0c40700540d500000141081e100d643c48034103501101405210b05000604203e0b0700152851441e0a44805010310201c000e00580c0351100500c0f0343c0b40c104007500e61003a4580b50551340d640200070600d02901412041560300c0401380ea0200c1004810f4202a1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 25949286 1250 25948036 25948067
    0xe0a05030405090f0c220306140f0615090f03030d0525080f0a050702070b04060207031b052103070b0423010b0105041401140301030f0b10260c0a0303 66
    0x10340326140c99041d600c0302034030130138280442040801c0e1110b03c0480311055006d000340004d801190f0f0f944404043d1100034180182083c45503082064002c4090910764000740705a03000e881d1442500c409070310354856186035501c2450b5030a4484510f030303420030480da290b07807a04606205274149485008544400440202903001d095442c1a40041c0303d00030041c82441c0b1f20042031019242d18a42100809000e000c003c1103004c0d80b400030a44104101c010001005182e000300310303403483d40c02d0490b01f40441e80002d41603110700c5403003086240e41d089162440b10b40d0810088000500d0480c0c40c1d4514403e0060041519004074200030070b2140114144a0144000c5130418448684810081c00c03201d2074481d042c0811804e010a00c0f0303440c08072092050001040c140000910b0817049a2115604264811203002d00b940d11031104101c40580c00c40d0300400d1040180789034504000402c0201c220700c240600e60184041002c044100040041404151002c4c00c8907000c1d580740d041c01042c0a00440034003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 25950536 1250 25949286 25949299
    0x406090e090601050103050c0d0c05030a060902090a0308091908070509070309030c121202161101020703050601120809060c0a0507050a030309091508070b07050c0105070f02040b040e0a05030405 85
    0xe00903015a9914410040100a462580c1c03c0500640040a01900c81c1070b030803c05101c08020b94405225013615160305807a0307076440745043c0d8607850589a69420980403030b03005003d4182c082d2100c0b9215402ea80e4046044c42e21a9100808a118030084882e840907504003244001052070021644000f07658003503564002950300c07a2001e605540c000301000700015840e9500201041d00d07040e070841c101c000e0b072802c0c10030849800010030070b90300500032540c00d8113203070036409080010b41a0f203241071a03804c0c0003402c3c81902e1a21a03039280e202c14444e40c00064015500e000c10080c1540071555900e000801c0079440c2d031036481d409640c07171051a4007190144039400020480c3c2ca84095140c1c01c13a5071541e90a07900700d04044c10301c0007900c26001d02000c02c001c01c01010411001c2800303c4000342c2845007010707442e84000e080240c503003400044000d0502104008907404100c099202903034554050f0782c04910f6520140c082002054024480261030007011303060410482c2c044010320844a0882d0107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 25951786 1250 25950536 25950539
    0x3020306070806030a03080a02130e160f021f0f02120612060622090f03021c03020a0818070e1306050907060503040209130b0106030203071808100209030a1403040609 73
    0xc2e00c007081d00f522250b038942d010b0005030000030b01c103000d483d5025101642c05401c01036000c040c3d60171030000340c200d01700020f1443e0800c909841080283c0144003c0d0345400c00891801d004042d460300320140d108010010364840c4a00c0c584510340213200ca01c500d070141195503c0c41341127944100d0400b9901c4501c64181114200e0009200141d480c0c01902c0040401d2034000700a0b0316251348400381c2904070071141d00c1d00107080c0451084880c07080325600079000381c1043c0140711240c01c0d0f21140d49007840181413051001c81440d581c454a0558040c041d814948501c3c2d814a01c0b941c50f00340c0c5684403040c4900c00b00100120050b03e0000d01c2c001500c604024000768885441484c0c40740c03010302508000820a10000b805441c154840c55000031086562001c200101c0c1c40f4040c0d640400d03000345011a800000348100079a000b0070600c0301e00100403114894509001c0f5454a40c80c440400e5201c10380c0200381c0000c1c5540c1406044809135001ca01c0c003120042e502031158590304a0310070701001c82e954540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 25953036 1250 25951786 25951801
    0xe010501020f0c06091c02120d0f020303160e0105071502190201060302060904090c0902070f0b0a1a100e040f09030e031501090f02040308070b01090b03030c100506010e13050103020306 81
    0x24001c04100000b4203a80c1441d440006002004074601b003d6105c42030740b44540400b40e2680303200c0d4210a402d00000e0216000e251102034145c1c1001c42d42d1008651041040010b02009074080b00300c1c4021030318001c40d0700d48801c00121000d004911016100e081004c00b0100c41c20b02c02e600815035000c0303040f09248803d0340e40209908841d15440082c0d0083c1f020014090b880ca0240d10107604240b00b1210010001e032100e44a204a07002480c1c1224210300c03c9414500340082e00c90740c80c0d40084101c5003840340400d42c030011411050000711140c000c0c151400c0f100c5c6101d0090b030341981d91220140c020030041001141f10700250501c0c80080d004100000e1400301c0904003c518250044170f0400540200d910f0003014030000e009901d010400c0641c244804400101702c54000c14a9034000c0689110950419103044219068616100d00c25441044008c01040001c42c171584c0e100101c86001803169102801a5120701ca03103880a5806207800002c584540d141d980124140d81c0240d00300c883c00d644904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 25954286 1250 25953036 25953043
    0x6020703170f1303030504050108010e0106021506010504080d05030105040507050313080c03070804170106080f1e010b1809010b06090109030f0309090f020d0f020f0a1103130e010501020f 82
    0x3000e4100101c40d0703a81c22148552000500312000b02a050501c2c1c05860751070480c100e40d40760000c40c0040c4000504100c2c0d580d03c002e90303902608075103949800b594034060010303555009410b1100032020500c0002211603005000b1340d0000c00824080d50300756142000c004006074424040d0300c3c4954074000104000601c0360007542d00c280300c07040717030790030b040c52951102c0250f5000040d11103124402008003c00088e1018041c02c000d003420081d01c0d80c00651202c0c1c5909443c540d070040d414540c48a9200100c0ea500000d80f81034014001d51031000400d01921203e0140007a226419005a9940c0c460009008269082803140102000804c020b02d4908200581c84c8181850b90b03000515440c022f101003502c8611000600303100303060402013203903900c0403042a42c40c00703000f41504036400f10b00700c10940801e0266030001c041c1a8421450480002440c84150207803003200300c104006681e0f802a901070400443d10b03508030705642fa124503542c1d01c955014041090180d1030060040c40e0301e05140c081f000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 25955536 1250 25954286 25954289
    0x30c021905060402010c080705010c030f0f09050c0103020c0709022a0703020a18020c060a020c010e070509010e04020d05030f03160503070903140a060e0309030105280f090b070806010801060207 85
    0x81c007501c010303115900115400e0030316800c00d940d0180b040040100144091251080c00369554070045036078041e906100040303903001801d030f00045041c00a20320010301d000c240307245480d4003420010b07219180c612540b0300e04200c54012000c031270301c00142c0a0044048000608d00c502a0440d818400245401402d8940c4003c1c40001d412805a035000c2c0800030000c6c035a00741035402c1000045c140703044090500c0c82d100c0d0945a0320481d0364009003d070200c42d400c1c05151a841d80d503000608200d032404001c6800040148500c218008404003c14115510925100c0100b50410202c0f511000c541222540d241c1c000d40f24943c6c030100840340300140c00c1c01003060381d1003500305454182c044c0340345440720101a0340140b03c0c00a07a0203802402c0d00011003e10030100389103028801107491f00012014542103c001508945408a407a03203c03c3d407881c601b44000e602d51700c02c1000828a01d0802210078064002c4041c0100030005560801007400d910040040c032660090346e650150366a240000d9803a18031b103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 25956786 1250 25955536 25955543
    0x6090204110a0504061b06050f100b040e060409020d05060a02040f05011b0201120b220506030304050a1e0b0c030304030306210609050a0203060c04080c1f120912030c0219 75
    0x20b2208018a074040c111850581c07412400e004200d00d1555540f1040700c03400c4072402e40700c4109c0e0061104450692025001905600c400c0628190501c044c06091480041c046803103962258490011511050640c3c02d5031580601203680c0c030305064034164081c0d00f28ac0610080940c403031500251940c4a4151030040d0340701244102d807000c1d900d0300115103411008900e1440c042d00c5144100d00d640350907074403440b0b5002d1001e40c038070709040704c0d40400305544021306101d1280d40240800d00032651258144000ca81d4403c4e100b140cac071035041d0140d80301c070021039104101c00038000c0f44c651160100400118480d601c20340e0100200b9442d6400c41200001c203c284050b0b03442001d40400000c1c0c665031004401d00d0144003140c0c0e00c0005540002d181002c104e03081e0341c07040d00124082103101810030000154801c11500301319081c42166128002d904050000d204101021141c072850b50b0842c2e00c00b000755500b007018103800941d20340c0702402804017136807624014803c1c82d816002c54440f480049a45036403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 25958036 1250 25956786 25956797
    0x301030b040305090301200c0105090705011e090b040b07140706091505090402030703020c0607080c030f07180f080706030b0907050903150f070e01030213090c0903020d06090204110a 80
    0x210764608490710341003c0b610542541d0f072081103c00f4030354020001c402e0005d088900036a1070350790003141829140e0240c0001c130581e000003828021a0380240020381d40c0e04695a0308140480d011000f103d07402150b60103404840e40008010454111030001021900c1c000d20284101c5120302c0101a556a540e125440c006600f100c028003016460b18284495007c0c180307400d90030690f034200003808a92042d520b07940440d50015525810640520020794071083c6070901d1100f0381350150340b040d5240302c003c2c04080c6c803411700c9000904131800342012a41c0e032008200000852512007040c0361010380d044c005d1006600c075114000403820301c280901d04039200302821445013521400341c161255001606d81c2e0313506010340c1091a5050030307001ea64612070302078642c2c0e96419080089016002c43c00024a042c101401005a581ca021400d422501243c0e0035010001d21450300e11011141c000032a0402540011690458400c0c00007540002d6400c0c2e00885040004070f00c01015a407042c0701ea049584007260 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 25959286 1250 25958036 25958041
    0xf140d03050a032414060c0d053406110c100c0509132016020904020f030a0b0105030727020307030615050315040509070b0306030f1c11030301030b 65
    0x74800d9001e01640a110b04011a10944003401c1d0035410f25480500781c4004481003040144818035060903807803039030503210a4580821001103a03210340c4030340d1180052100005500216002c0420750040854841050300c202c8199181104ca180c00030030000d590039810059040c860011100490308841119001003403106110030000c409006c0c0d036441c010602005015018058440340320304503603051004400aa090719400c0020425001e403008020740000a01c100071060713102010400c00c03a6012604201959180d05c002903095001c0958103426018960b201d1041000299001c1d06032403044003656151910380d80c0c031281141c010f0340c10004514040c203a007504580c40758015500524586004218580ca46035083d089043e080310030000202d00104020382c0c0010b00b04100185201200c0901842c01e010582944c1e801290246007120705d0000082181581c0401030000307400c1a000644605a22403156080f8103441070301d00c0000f0510313200e80c65442d524044102c03816a988240492042c1c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 25960536 1250 25959286 25959293
    0x20d02010605010219140303010816060203040e0112050a120906030506030d02120d15150e09060906040e010e10140906090607030e010f0510051302040e070c0f0b070203040f140d 78
    0x1040c802030261b41c2c00e103941a1104a60509000440c06040800001d0034200c0040010403400c05180c2c0c450400c54100340410b00c0032903003801d00d42d81150107200f1484164005418000d04103000a41c000f040c4501031a507462440380c020714000c0803509981c0701080f10781e03155410705485030074480035400141c21001d24040c0b01014640505a002c2036000001030400403007052171202a03194100b002d1510303051030079a2046074071007071244007410306440007400303400c110700483d0100e980039100511a64841c0d03c0700848120950040080720386040441d004280b050010000500d1040e004130301494003400012079100c80020400d006141c0d0790700605099036403041c1100184001191b000c0255227501112200356900e008150155107034400e45030030180340004011103103414045940c1c400740144810440e200803840c2c165401a09410a20061249c52403c0300c113501c0840f0004001d1000101809400d942c0040a40242d50741c5182d0550050744a0881c82030101c1b40d00480c0360700200390030350300000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 25961786 1250 25960536 25960573
    0x5100203090f0d05070b13110111150c03010e090a0503030103110d1208070f03060806010504090305070503040e010e06011d13020c10020306030d0305040f0308060307050619020d020106050102 84
    0x1c150007205031000502920308840c14081d582d10310a000610100355201403041c00000d03140c2086c0344122103034410b04503584400c0a0101140414140010064a01803c0d0400d00c0a48500c90811001300c801b413521600764880368200780243d400e4080824001003240000054452485411a00460840c0e2030742d030f0340082001c000c16a040d003142102c402d2000050442224150344c41154451601d50700d13161800a08103d00001000105070801000300300800e40441c2a0b03065940681d400310700c900280c01d043c0d60622800720010080d200000d800100300840c0694107043e241c80c0200d6034100d4903044011101e1442da01c080c4000c403510b04105403000d16000713400342029101d0700c50241c00c29012000150800300600c0f8110441030f000420007280f4502070000c0d12407080507050030031080c203080d00d41a030169000f0100038140201107020521135a800c004a030003c1400030301a50342d40c01150008585420f501204e04003612500818200c40c40c0180103103030035501e040e0700510b060210540300d0030700c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 25963036 1250 25961786 25961791
    0x90504020406090c020102070308060303090a06030e121309060515030f0a110a0306030219030302070b0d110301060e040b0a050102190204020d140105011812021516060e0c0103020705100203 83
    0x380070b66510341c00106800207000d00c1c04c0c060196000140c07076141d98180940b120900405652098208018100c15a95120300850940d9980e14000941c041541030030303880d251004c040300b9011400890740303581201c05004124141d400005d410301200c1d41e11002c1c81415290900100101c0c24180300113850345160103d940d40c0200c0300400420800401d191504c000d42c01104400f00003078072801d09005504100704a1401200b1414118448a2458500a444007a1805400d2118800280303042041d2007e030407031b0741ca042d031a40c011a500e507580c01010304004c800285840c06113007424404281c0b0720b40202860308545040c0c000d4101c0ca00c10146002803a0b002c2c5004990040e070a114074a00d0000c0d40c4250342c070203016100c0742e4100d541800009032015207010800000042c41c0c003802d05c8a520090103030702e0000d40c1900e04492400741c1c1075500419000300b83c1c07500a0b031218020006c087c00301036000036040c05404019110b59540300c0700110103a2142c00400342c000c1e03001e80f00590201211740d00455 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 25964286 1250 25963036 25963039
    0x10509032514010507030c08220f050f0c120a0b0a05100905090a020f090103030212090a09050a090309051509060903030712050d06170d080901181406090105010b0409050402 76
    0x460444a60707106150042040d4240303410f41e41d150104200720f0b405200c3c1800340f0580703042c81021072070040c44108442d42e101d041c0e880c052003a600c2020030440d1800607103070041d9000c0b094a08010b44050b070b03959662800702000e4465030343c0d61180000200042000003403260045d0100c0c609594003c170740741c0038244c058102110380d60041e000084181262181d103024080e02c0020302407002960040100c60a66400018440c4000b8401040000c1c1c0024501403051074074881d16440740d5485c000152500025800b0354100c40c1010104041c9030845c0c4d000d1aa010710a49916660903265001e0222a20810f140002c1c508010000c040561402c0e00c09805440c50003403c032407402400c1c2d91a0a00442515007900125034042440032803c690380c0241c1c0e01600303a151350b8500010b10540410381d02e041410420050005020105007422002c2d04030b80c181083d802c0684070008080d107000ca181d000c048002203000d00510001c208202410301815040320110760b1518101400c001100004180190080b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 25965536 1250 25964286 25964347
    0x60f0b19050d020a1d0103020c0607030b01050d05010e070f02071809150204120605010b0f030601030b01030609060605071b0e06060a090806041a100302060d0b040e0709060807060201050903 83
    0x260382e580301030b000400c04a80c05544a8035088040d280c141d81d5203e0205e0403505140c01480b581030742001c0041c1c62640080145004150b0340920401603840d881406800305c0381604040020540d0007640b02030a00801060fa1002c0b0384d005150022621030081e80905402d01c2c2c100c100e021885a00ca41000c0d80c87c500a841f5200c000a41402c603008a0788035500c000d40c030b10b5406409006004540c81114014503030007a0440c502611001c04084922001f003d00303040c540c0c4e68441e0304140e48258000780103010300e00000c0007500c0e210480544541c1184008542c0320103600a100c2c00300500a1004045a8241000400c61388485040000ba43c000081d26000c000613481d001036000410413440340528090f21103614000b1108440622440303004003860a0346142800410058841a044075207410a603200000c22000140028010700291710302e0210038030603040c0104162032140e0080c0200d81d05501100d60095852100b80e00340c6000300c840d50459081401b000d00301114168505200301c0000100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 25966786 1250 25965536 25965547
    0x60f0f040b15070501050106020d020705090103020603040f0f0804090c03020412080912070e060a05040506150d020702040207060c02010b100903030c03110a060603020a270b060903060c0c01060f0b1905 88
    0x49282c00e8101c80d43c1940e21340e4540004000c10758050000707482183c1c0b0380c801b401c400e5003070002051083d80103100090060300d00000080611004000100d200d80d071011030b00038159100d080a910a401c14010081c03002c0c0307481d10170a40140684200d508031007142c2c400903540c03552034507040419000b07528110b4001a01e50129080050306220082c050510700b10410150700700799040c413071000a242c10081c052407401091050300d40d505110f1000b8039100181443d5a020010804c102900502000942260002c1340c08420002d280d00b20340c49643d07407940200030b0b8180d010101703e92910007001690200d090005e02388003103407042455403842c50081c01d04a03c080420315185242c0310319014180d0b0701b296254018011440d200200320000e2200348e1a103540302281500c41c5441c144099000c8030380d0343d680c80c60502d058039801c059034174041005003510701c58900390010180c15401036142018552038842c0104203182c4601c5894190344036404c1d89800d0200c0d0a5640100b084c00c03441c0344081c080284103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 25968036 1250 25966786 25966819
    0x6020a021603050f12031509040309051206190c1704081902060402040e0106060203040501051612090305070801021804050603070816170609121303080f0a08060f0f040b 74
    0x241c4019403041000304003580d0010101c504107400030760f2150b00759030200b083c0010300e180d50003591454101240c40e0007054489107030503126034441d5400513030090704403140007a900c074010580d00d12405010300102d604400140f080e0084804070001000441c90ba002e800c0c0c1c07480d411a400f541d100703203e044010b290000043c18803e25045011810303006038001b00c20441141014010500b0300800000284129418188043e44900941c001e803410418045540130401412203140d01400f900143e8600c00040c00c41d030000c0c414001d0b400141da241c401c0e51800034101c9014401c9401d03140c3c00c00100040c1c00510410000681780c0601056810f1040d0ba102245103001440458040c112018000955274540f04145034100a41100d60311681c010204218841d440820040054019a01d5090f641c101c02036881000100c036030400742180e100403441604281c0103030000d10b07989000d0740310080b0b07030395424042100000100d12400d401c10449455103007a401c00340c10081041c04014007000c80d00074030380b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 25969286 1250 25968036 25968073
    0xb101407060207050a060603051009021509010306090e031b0706120b0d0b09010c0f0c0b0105090c1204030306060e03030702010e0415090504050706080106020a031e051902010b1504030203060406020a02 88
    0x3e425606e15941c0c00f4208100076041003071801c00d08a0302c070144079940294000500c12001b422841e81081000a100d1025038405c3d48500c000d00010001009031200944440740d80360880d08035041056507541030700d021000e000a10100720742e0281d84021021395085500e401415000d8410758100e208550801e0000c0c0d00504050f100300c080c0e40c00003c031302c040102d000f054081c030801c0d10024801c09a40d000d02041850f80100c1c10340318103030b03034054107901c070b040b0303452100d00c07840e0301640744002c82c0380a010815505410002c00c80d100daa0759841a6280e81040544a1041080003400300300d00c2001c0300307194146038001d54494001201c00300352003070b0380d491b212095443c2141c0c12915900000807e002d11a0010a01400b42000e88002c0003ea202560f02501002a010320340804440d882c1c1d035031890a00c280f00f2604c615242c00e0306012a51039a0303201a001c1d02070540540d01c9403400011280c409900e02003a0b50032641c000b0000c0410b5101c0e86c88e100029440390001c1c0c400c50164017200f034804400c06 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 25970536 1250 25969286 25969303
    0x5060a02100b0a0e01170304030f03080402010207060503060f0d0302010b03010606090f06050a0f0503100b0d0e060c0a0c0605040503071a0103030210020702010905121c120b10140706020705 83
    0x19005004124a2180740100b201c407014041c0d0712810070410300380310240074070314814150b80d0101a400700f803650600c901031950141b1b9000034071803200300a0000c105a40850114010b078800c3c1c00712801d141d180d9030140c9144c00100c1e042d0340c00a005002200741031501051141b2003d003e4000000d220110002113801d41e04a40c0244011400c0400d041200c0c807002140017004200c2850410301381040680c00404018003144024204400400450198031108a80f54002c003940030209130f984643d2305017000502480b000c100050f004140002d4041c1c2c800742e0450b410300110380c0d10002c00844940e01c004c0200800740050311035200602c04400007030761403d0340001c014602400401e807903246140003490104c04105ca0500d0a005004600c0140d801819180c2036400032111600c2840c001c0000d5803401c405c55a14400d42c0b8403c400b8115001d070000b15004e2148080182804542011404d109146110458000004001442c81410540308202400c8203501c030707000151030680765071034461610204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 25971786 1250 25970536 25970557
    0x50a030e0106080f0c120d080a02090901030b07080906040b01050105130e01060c120201090f02041107020915030115050303030a051801020406080f01060c0b0a0203061305010e041b0f050d03090506 86
    0x84001009030720302040350468020302100d8402e01b14220012a42c1c4071651011840240910b9a011581c0c0d414140c069408080e0080c040c1c1c5a0f540e500d0611190511059417001c010406e100301007900c144001c01d04c9441280c202e1007014880e403070040119180d034494101c0075554803000001040080300089501c0c003c0c1b4695841c508600420b0401e0140708103040a0314066a241007101d200061030018884030b2560101c2340000e050500d103585281c1440741c00002540000c0d40000c00c074000404c903000e03500303240d4243c0007044003c03607a407242d0b10103508074052940d065005000140703d40d405038100603801070f050b22801c000c035449415020309980280d00140c0110341c082c03080109a0304072141d00ca004003814030f0070100d00780050b1900107209901038282c60310180c0002c0045c0c11a02d4000c81c0342041044070350300b00850740e940c0d1441468084203407011a410000200c20192010795096084103581c940d151000c100d6140c0b0040103040d00c0701034070403424098075641c00516943d4000181241e4541e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 25973036 1250 25971786 25971793
    0x9060f110106030809190f120311060a050907080705090402100201110c07061205070c030e0a050d0501020d0507030207030206010e090c04020d0209210a02041112011710090210050a030e010608 84
    0x8400302040544a1b400c6410141c0c1d0901c207004105502e2041501022034021111034006d811881c103044400041036180450144540400e001160f14207500240c8558844010368030031588a070900c030380310301d424851160310807000f5003c2005480c11580710064150203000001c0c02d05070708044003a941d00314000c1031140350040d4104020480d00658100c482d00032030941040300b0f161071600501080035500c0b01808003d800059642d1540b41c1109a01c040e01006090350044c01c050300c0e00078041d40c0315081d1800c2039801c1001048034035009000f80d03941c45525070054010fa070300340004900c170220001c01c00d1450307204134408008036450b140b00500c0c10f030140803005a503645501007400160f034005229100100340200c240858154040380e000c0038a913045030041240540040c03c00c0c400c1c000d80708d000e1440790294000264100b0844a80500805500190380c440d845015045003200d03504a0065003020325255110800c502c5030b001400c000080303045c005000188114a942182c2d400d800c11190f550 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 25974286 1250 25973036 25973047
    0x50405030a110d170319060b0301090f0609060b040906050405070e0909030d020706090b060d0b0106050c03040305030a020f0601090506060301120201110601030303053702030c042403050903090109060f1101060308 93
    0x240c02806e41c006550707840c0d406105052400b60240d110348030512401c140745c0c1c1d03501310b8001c15090340c0c1c011200910702900140001030703c440d00742c2880e901a101e840c1e282807400000180728203250141510924480c1c81c1c507601d0200000500071400002025440940002c100d6000042881c0c4040c085031405250001040011858030302030062025000b82e1203584d01c0410440051a14a1424103540365450321503205c0e01d01101d164035500441e04001d205010109a100e5199400140d200003500741c0d00440e20143d9945000d10300320703001601c51340e0300003000300014440041d9400414981350310601d446003606030100021404c2a80c01e800c00c8000075100d0041c8008a08071440d05000c0c0088001541d00075405840c01803558004078061440483d00440003030070100b4442c0c1584c008180901a0159000a0030b0700c24000d04125a070300b9000c01e24010214082440000a40e1502d00c010303101d00400d17174200a0191069990b03000d281c800c00c4081c080c0d6002d000130170700070740004610030001715881c2d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 25975536 1250 25974286 25974301
    0xa05160c030209010801050f150d05120c0c0109030807020906010903080d0c021212011403070e040302030c010501060c020105090d2103050103060e010203271c180501050405030a110d1703 82
    0x5040c5e210038440c2c1e0514003400300302d41909402d141c01c00000340c010304800b500c2c1d40c080784a07000d815002030300a001b0400880f0794001d0760002031900000c000c0c141c80218900800546404000d80000f0700042c1c41440000c006080283c01d03290013100c14184640510b1f5280d0707600c501940004011184191900c200000c01c940401c0242c1c0d01d10110500700741000480441070079003007814443c02403802c3c0500070148042c6c6003070258201800701c03040e47c54654585814040d541b84d02819055440303601e050000242d042c032460b00400c509505070b44040c03510340860300b0004401100e07502940d2421403030151040c5403800200c01a1003501d1624082015031450606100319000c5052a00c0c859004008014650801254004080d0550585401002907109100e480c1c81e080e510301501880d00036507400e8000340c1044820840f04044509000c550380c0329001180d040c040c80c4181354140d401a450040041d03041112140000c5014013800d40424541c1c541d0340380b860394402001140c840010500914 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 25976786 1250 25975536 25975549
    0x150703020d08070c020d02060408010203040506040308060108070c03210c0909050a02070b0412020a02040606090e0718090e0a020a03080304020909160605091305090c01030e0f0d03020a05160c0302 86
    0x24400a03080460061503da140a0500c0300c4070303c8004d03c5490070300210740440d501c031801e64025202541c0210744929140c1703492030b51540240d40075004121554000f0f042c542c40b800802d803244000381d6494484403496038050b10b460004045140d2140d0503d812401d11a210f44109514003030140e6800c0070852401550303204446000c1c00900d1030600411080000c95038284c0400d8015070302040d0f1103c5081524002c03410080d040b02c0c029842401d205c00015940c1d803194211060324000030041100383c8648500b510701c54090000840c50003180c07002007002010507031001d040b81e14100c050314400d41c0182d0004801d8851a041100c01c2180401031000f076003028082c030390740300c0d10500040880144494242c1e00e035802c0d500c80c0400300b14001510364600e448010143d0fa0960001105000c00e080c469150341d01c40c5504204a0300003442d02d41000c1c2d540b240004c9104800540001508415010350750840c00381d440800c001c070034040100124011148405110049240075024a900c0181584100b080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 25978036 1250 25976786 25976803
    0x1805010503041106070206040e01030b0402010306051c03030b060706060e10170a170906030702060103020102060a0b1f031418070902040e070309020307050a1706011d07030e070515070302 82
    0x40110070300400000075058000243c001d2011650a03480343c076684001022480703607402004132851600000802c12103007071161340c0194400d032030070f100031510340301800001707101c420800c00700c03840034002c00d000f10f4020740c00f01c0c410311706c040e1009150440c0e039103e2800b03482807540604002280801003000010002e0b04400c0502000c0ca182810a030402161030b6070303640306200c094041080014000b903008140f84c116400c4a1010300070f50348034030b0405000303522a0380034401640035010301c5000502c03415042c86000d4a4074002800307000c1c0a107400c540b40c050410300e400000700b8181d8a4032440240310410085034030450303414220001241e40c0b081680c0c1810025804007000030b00501050000414143c2c42c203600100d5441d00245a4600d800002d00d0005282d12040e08420000c030049400102009401d20f508804411a03805903030b11540344107401c0291401c1741d00000d606020881440c8280c000e905060b40c9a012035002a0b01c0f0b200140d10707103268407240300e00010002010b004054045c816a035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 25979286 1250 25978036 25978039
    0x20d21050909150d060c1206090516030b030a03051b070807140916110705100302040611070b0306010809010902040c080703051b030a0b010c0f030903051902061603020c0d031805 78
    0xd0000b00f000700d802485031003001040941c8500f9240d050a108441403c10342a20300010300515070f643c3c90081c002c00342603602ca50034040d40300d1189040c600900442221103c003400404900b41d190720211410381200c4c4c040810a0000c0c482c039a48032004025081c05009204080c00c55103150801340304c03821031f01c005501e01400280f01084001d012480c502c0e040c81003079040c0200001b07001e108140c1081e046800c500d03441000114419103c1e81d040e400b130700c02d82da0117443e00750300c0b2030001907010394854841c400d42c080a02d0030000a00309501c94400560403400405c00418440713881d40c005804d80b5400c0d61084006200a4100300701203515004460b08040321004102844201c2081840740344030040113102c545440e00381034100c9074800c49105440740e40110a5103004d010ba40340051100019120689091080900030480c2c1404c6805002c011a4010221441c1c107001901c8024010441c403000d8096000c1d00005141c203884464442c14028480e588005e00040406000c1c0d840010940015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 25980536 1250 25979286 25979311
    0x5011106070f1103090405010b0903070f0308070303110c010501080105040303230c0f0c1009020411130608040807150b0307080d080604090503091306090507050a0804020d21050909 79
    0x4814280c00c2048419041d1091400d9003c604450304000e143d4811859007540191600c3d00026049810a000c3e0101950440c180c0360300940c0c820a11800c150240409800000f0401081000a0099008000c0000010342d51801c0c205000c210b1821201c09a0014400d40d45542c2080101585841820b09980000e0300d00300e0050088942c21000391070040035908900341c0002d26000c001d158006075079081d81030800b15001010b0b2030585401a08600f40120700560410f00c0e107540b5a10321100b0740754042540d5420700301c4280b03003042c104d540000c06001682c80005c1048404041030341082003589000740f034880410100c01213403e00d4039000032a40040c42c3c2d9080003d041c0b00701981700d4692504010100c6010941302040c1c10040d0031845201e060380e510100c0000140101102034101f2412210203140c20441c5542e604400e803a148a00c0b00341400142ca40d6000800610b0b0410041c0e40305406509002c0c030510301804409007000c0d000038100f011450106141c0810701c1c11043d000c1c0e01444003200d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 25981786 1250 25980536 25980541
    0x3090114010305032b0204120b01050301051b090f0405010b090108010503010b0f0f062808010e011203030c090b031005041824090506040f03020c01020601050604090b030102040e0f0105011106 84
    0x1019100d01405d03c0c0d20006220120071403080822a40c100c4298010301c640031076079650750b022074001c501201d20086030602d07280c0c03000041d00d03c1c061045e68030a100088406e030b02e130071100204021640c0000310481d40906000e090000700d40b2548035040c06084111f030100da540e0307094800076042601c1680450b20070780c10007482c40d20680300d200c00880ca911040d181d903036041604000288280c0142d44a010b00b80b407244000411051800300115100d50789900d5034101c0e81d89600703052107084801d015681c0704a00355006580007034403075441039192040074031b0800c51141d114000c0701c8081e8403c1d600740d42407031150081804146000d03c10070403803940d0341c01005001140350742e41140524041919186284415450016500c02900300300c1c8041c3c0d00c07406848640c90a0315008540c2170024006a005100340c1076901d80c42c1d400000d800c0e050f40c00091040d41010b281000f58000342240b00c50498045d50280f10010702d00c032200081901406c8041c2000e191076040000060109806010181c99a44a4001d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 25983036 1250 25981786 25981793
    0x30b1801061505070c050913031e0801030809010315080708070509010806040204050910110304120c051c020709020c0309010201110a0507020904060e030705010e01060b040e01090f0b060a0302030901140103 90
    0x4101402c0070580c10210b450b80d441e410044000c641a5016030381141040080111000c0d10b00081182c0922035140c505e42844c400b0558001d0116003854000425134600051010408840140544000500d00850f120703c500140d00c005201641c07001d9880c4e806440c0c1405280000e10549003d46800d881e00202585804102070350761001400280c000c07a5920007182d01c2200612442c501c003d01035001780502e000c03010422401c0c0d0300c02c0342d094507031610790800010380a02c1840380007001500100140700b03c0d9100ca0502904002450454055110300840000c5080c0e1134000b40c0302d11071000c005507845040510019017500c1d60300400441d1081c0030401c814200b0b800101b5103640d40d4043e41c48a555580c4c03450301100400001c07182804a00c4049001400c0100c15000040190820b500a21885640c0e210f06000e038040d40c0607100500840e107005005e480000d80c4a039406004000c404190002508040b50044e8000700c1d1480000390004100408407100b4000c642c3c034440d015001c040298510388 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 25984286 1250 25983036 25983059
    0x10c020304150309020604060c0312050603151008071d0708010b0706020a0212030a020c0f0606010f030506030a0206031e160c0201050307020c06040f03050c0402070305121906030b180106 82
    0x1a034030040000c0b460540c2454400d40c07110084540c080d00542c3d445441e0000038110030811001140003c84c40340c2c0c6020004254090303680035800150090800000c400040001a03600510310b43c500d600c010b1000070b004104100300c00052616030b02801200702c69030520300001800510342424840407400420602e904582242d20300c54021100617155550004100c0c2050507510307450003e000e0110500801810396402040d00d120000200e0b0040b100d50a01c2d075440c1c07481265101c0c0414907508075094028020307000180e22000080a4610215040d0b0000d01c56030400d075a41d404500c055090b0025000f0320311131171030f000f802500c003401030604100c40081c00c020021070000d04104d80400820070007402040760f4103401c14001d00301902d50381c850603200c03c403010b02d120544152040398080b00350780c100381c0300b2944075607010350701d01c0e00e80048004480340c080c1e005010100001c102076044200740146204200141d0700c91801d802c842d00349803281d03c610342013150414400346d240c204100306110300e03c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 25985536 1250 25984286 25984289
    0x6050a14100503061f081c031b0206012601020414090702010618020a020f0609030d0b01170a090206070b09060a140f01030314040902070f030f050f0901030b0d020409060b0a050102010c020304 84
    0x440c900b540c0c112942501200c5106a0108243d485040d0640380d1003070104510a80400c020360323040141c2840500f6200e42020b91010120150f0440030040c4080f40421141c90344140c800c458622040f00311001c0c640c00c90340f181d80200d80b52219a107040442c0e2601d29080d41d00803003584001e100d19404c0428a20301c0145041340b255074240e0018212030114001c2c0551401580100140d441750314007014000d442e07620044a01a121349011040b0605600903a580b2022869141d6001419681e4221207001030100303c3d0140da10070000d0088000107080c0700b10f524880e555120140c002c41c10030b0000e01c8165a4501c00b10110504080208429108079076841411a40c061815074100d01420700c142c40940310b142c1000c100e4500000e011000c0c0882a204815140d100c0c3c2d41d005842521110111071600416091b40381c3c2d00000c1010284540c0710390071030350b0303800001005840901080e40c00642190340c2c1350402c494607611000b19828519121f8107600040100b0b00090240f083c201034000c8d182d2241d07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 25986786 1250 25985536 25985551
    0x1c060b0a090b1809070e011427040908031e01090b030c0405180703030c1a01061b0203070f0311090a020c0703030c150501030c180212071b06050a1410050306 69
    0x208011a260183d854050144070000c0c0c000d00850030444002810034250002060115541c4200011801c1d11001280e410010407005800d0002c40d0607d2001800350248075154060748502c600008201104019402003400b07040000d10310b443e071050380f030b036088050b8030101d01d46140111220190718045581c02c3d003450101c4000450341c0e07071144031951404420071101550301c540c440c00700c20140c110090700d44050040b25040c03404501d000c1d00401c2e0300400d000c0c40d00003a1600b42d9001801c2004e0400d006200d1005058400103521801c40c0184162030354015101c9071314280c8006002e0070031400b4039400a40010040d031030415000c0c0c0c2d45c0d40e540d4182c4801010003143c01d12040c180400800e0340d00c001c1840c2002408a543d490a00340c000100c1d03070040c038031481c500c5440500c25500074030844007015011022403005690b0000141c41d0b40c0c110602d140e64a8000c075081c180091304511845101d60584800007a41e04450280d0900c1301900410004034101841414001035400040c0c42c0d502c00007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 25988036 1250 25986786 25986809
    0x3060118050a0e03040801020903010e010b03070605030406020f031504050702010504020f0d060615171003030906050a030b030f060108070506030618090a0602040303021e032d0705031c060b0a09 85
    0x101d94881c1c2004083e103040e40b80880c000803078042412041900242400c4408800074400c04c150488800c0c201c40c0e11014040d4190b01c104000c010641c040d501075903006000f681c006040103001401540958001c41c0c52080a002c4203000740f14031b00e0548a550740025040c402000a450b066020400c0c282248482c0c520590b01c02105c10104201a08038402429a02050035401740e18030384090070354860714081c0381402e44040700061a952100740354404a0350035544181c803243c90814150f4941d4000d2420004040e19070030019401e031010401d024010444800608143d0300d8408203a0a044040d08500d11500042003884a40d903507a880e152040c4102001d40381039602c1d0204d845140c00c02c0c0301c000801a0f80081000400d00d9000b0881080c40400c881c0d580c0d64807030086040350340324030520401d403241484002e1a0f41e007401c41d40c006c0c103858036440d5241a25000c540d49039103107960040d42d10250f02c1500c1da00040003100c100c3c09280018403020740403a00346918050007a12041c0c01d80120341c2c0285 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 25989286 1250 25988036 25988041
    0x15010806010e13110c060f0411060306010e0d050604140102040503030d0213051c02010306090207020d030c08040b0408010515060403050604030c060908040603020703020c0105030907030f140607090f050306011805 93
    0x580e141141c0c003083c0004107040240f0441c0030a00265500050811304d000d01072400010045107100c040103104551007210b0107030550300d080401c0429003010f00810f0400090644503111510b4070406081454040e10040119241c5031900c00540100401440100d03401800304100b10744001081d103072120110b100c0982c031000107644d0600d4040c3c0326400264030041c0001102c00e56280c00b5059640c1c14000c1ea028410311b0b803254804002e80c8180c1000a4020911114034000b2a103c2c42001603628420308200340792540d100a441d90940140c1c00c1494141d545000303101e160803800241f41d0101d201581e104d0304242c80e5860789902d07010001c2010f024008215049020414598403201140ba803059180b40c0700d5440f20801002034002c61412800361060392105600c40d80a041500d20a46507040144100ca0440d500c00366403400f000c2c011200f803001e284403400001400c0c044c00f40b141881e6a03440c444207250034410324035100c142e404503000780c0017440180702c40c100300d515907030700c280000101054a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 25990536 1250 25989286 25989289
    0x304050c100504060e0402030c19090806090d3203100504090308090c0d0b06101101090b040302070905070807050f07060603030206011805090c010f050c0a030207090515010806010e 79
    0x208029856800300d11110303140c5107aa0410090016103c1da5500d0303a0f0016007000c04c0c00100c1c80283c4d8102000c6030306000420a0001b5000b001c200e000c1c0c130349840d110065541592070300d414810b0b9506503a98014026040401d944500741d02208044410001508103020f03045144550301800030a88012001001650442c1900c42041c020302c4090410800c00055041c000e00060096450100c41d010344507214a1524241c1018048150400914500c41e100c100c1040719800c0d403813103003200b80982c800300c2c224008000c1c414500528003c42c1004264541840c001742410403682000c504d0502c4c010901041e15403044165500101e82d0928a41d1819030001e000c585005038440104500d0800001000705a80030808504032140300f00440017801d01c0d00c40340c1003a00ea046800301d803d80c0c40010103c02a62058035904030089403800d005c3c0c5003942070071186080c40f441d80c40540260340725010411a0414a2188a078440c0314444810701c1d644039480003c0c46074601a1041d410001d12000c4e01246 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 25991786 1250 25990536 25990543
    0xd090e0403030b0a150f0e01030b030c0f03010f020403080702180c12070c0f030201060e0601030e0307080906070203030409050702061005030d0804020a08070602010501090b0607030f050c030702040e0a05010f0b0a0b030405 97
    0xf418000c541c10056004045c4000c101039440c40648000030054120006554024000e0004448009004e003440084103000d1022407103200740d03000c0d8199250407410b07241c001d1510092002d5805060340594444480c014032070102c003181e400001c05604801002200c0024509581d132804080c60101030320345070b000049640701c04005015180558090030342c010550150700000c111030503c2d034117825665629005404079002c0d0314408485408c1041380720006071004005051504004128600340201a0003192540d006600011481d903a94007e002240b50100100355101040500e141000c80c2003070080790302c8800c107241800070300039201c001c1011581c481e44407002401009044500003640c40b00300902a000a00c00d010000c0c0c6801c0b20001641403500c11034900b00e4250300c41c041c0c448480c610841c1e10341c0c802110482280030134066400140e83e1409000e50f208400c4004100002c1103080003400c40c0c0000000c00c01040c9410580915030f22046580300440c0c5468140315165580d0f0f0514604 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 25993036 1250 25991786 25991789
    0x9051c170a020a020a140c040608070501090b09030f0a03020d090b040f0b0d0902060d1d030c030412050309030307080904140103030e01030903020a050109050303070f05040f0510031401060801080d090e0403030b0a 93
    0x2400b50201c03c2c008606c000098007035142c0c0307400c907001d1000954400d6441d071543c0b128007666000441d8420305101040c146c0c2c0041c680c5060107003c030f4107800e0400b60085d04000303024008a0040e00000c0b0545500ca42c00482c0c0405401c4c0740e40c00900e081d1030800e848410315040d01c0b81c608000008a503903006110a588090241c9801408040c0d03200104281c00300103010b41503030040c2154a10342500900103001080c1d405006008008525050900d4400344510042c038504031910b100030030100ca5076440074000341481e60720030100b440d00c0d03100d03030310812041d80e084804c4070840c0b880e6070b401040800c0d03119050b0003044000782400200000f0740e060403814200000d400ad092903003499010310402000000035071246880c1e035541d002c0a26818411502071280d40304102c00d203000703003d080c0080d2402004592804069040000c3c004d03219801701041e50740241d000304041440e0800404c00301609010480021034a4075100c0f04040c101042c000f109103014002401f0941d450018880f0b6480e030a07003450 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 25994286 1250 25993036 25993043
    0xf1201090611040f12080711060c030c03040504051608010504050601050705070b04060f02030c0d0e0d06050709050301060b070c03060b180f06031c020303240409051c170a020a020a 79
    0x31005201e144810394940c0503200c0e415a031113200000203030b42009140c0459526030701840d8140742c2070381519110740c8070542c003010f1580407400f04055940501c040000300040070401c40990707140c1e0300c2c003020001241d6008144442e6094031001c440e11643c1c0c01003076035064400803100000c03c2c1d194440101c8182c000c01b40002c02520480d400440c1444d41080604101d580ba9a29598030611269040f0b072203005006506840da8007512070808401d008800024180d20007400c001c030a0307400c50b25208103981c1c050b20b900000c81c05500c0305000c80c0c01e080c000c560103090690041482d2590a60f6a90301c04407c0d448042c18907030f940d4070750000c1e598032004001d658030150003043c0d00900302021101c4141c2c20540e02c5510a02c249040b107801001400300080d0f807558903070080c6040d03980300503140030030508280480c041c280039010304100d55a2140720702e01b5000d00803002800e040ca01924900b0112540c82c0c5002d00b0302402d422a40300501c130046165034445080040035807606180c21060b8500a9000f0004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 25995536 1250 25994286 25994291
    0x2030a21020408061504020c03030103030c0317150310050115080a0f05011805090114040b060f090702071d13080715090605040203010b010f050906071e0f030f0e0f12010906 76
    0x341d01c440018070715010380402e90904981742c80d1201084220710404035410640e400c18001007001c40d0162090002140c024102031208884001c0c0000a11307200301c5480000d6481e09040d425175040402071040c88a410070000c00155061450442020041c00c64210030840a40f002a00003206904140c3c14a001c0c0134090005586a00d001c0d00c90000114881c60f8045c0340c10002083e110050141c3e0804040640040c911034455455040401500410458212180c030f0007c00345500d5880a0b03510a5229a02800d000d5007407482c040c079440307446140d2103c5c08075a401800700c0071055031201883c440c0c1c06500f8030b80c0ca000c10f281082d0546880030314003a240380380c0718054040c0070440d00450310a0348210001c2000f03104450040d03404038181c41140c0c00080f070070f10404485080c040c009050807802908440c181c58600e24855045412040048035030230101d6250004154010104031425501c50500c49514000d00c03012640c040b580d81da044e03100c0c00220a107201202c1c000e5000040e65504400306 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 25996786 1250 25995536 25995539
    0x9020a1a0c0f030322020f060703170108010203010810090506070c050f0304080309040c02031c050a09020a12030315080303060402070317040c080f0309150a0509131406010f02030a210204 82
    0x1180c0c89400459400e4044003d2030017640120b040b40e0014a0301541c0106820350900c541014021340340c00c0030200310140100c01151482c2044804511402015500c0c00981d996042c07660b81400d040040e2008025039040c050b080e40041c8010030066884070482c82c05403e80102401c0c21445e0816406908a4038040000c0114003200301000520309460241c07000d010f00180c070311040740c7d20f06c500c80d518104007104000c1c100c100324850300a01d401c0340c18140080341e000741c10b400256840c9010f601c20306654501c01d0500023050b4040c0501c02546e200e140340c6020300340c07421103107580743c1c44001c0c40f00344510350000790442050b01403140c407480c4189940101003581303080d1601c2c034440b40060261091a20900f16003e05000c000011103240341000741c0000031000964544500540080c40c0c110140b03c0d0038044001c80e40c5543c0c01e07050005004c800007149074010140b01600c203e80c080d04040c1006004184100255000021102c01c00158540400c401c191210b1081c110034210300b0425005000050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 25998036 1250 25996786 25996813
    0x151504171207061a09010806070e0609040606120f02030606040b09010513030b060306010e0c07110f032b030902101b0816140a0f0314040b0409090b06030109020a1a0c 73
    0x10003480322155040f0b04d10030010800c0001c007042c24883d1001c030f5030050700061002c6110f8030400228607005441141000c032204002800e9424640006002805908451081c0203184c0104400b045282104501d1070070510040b8400b0320a900a07848034200010343d020050748290221400038015244e14580c4e25100c1c9050041c902c01520760038440e22400340041011040f01804034000e81c0c0c910441e51400c8c200c0d649280c000c0d01c0c40028280e00501c50003502c02541c5061050160744102002e9140c1c031880302c82c41d4044041140016202050714010310b040c01611030307c0220310020760b1418904c040c030300045a80640c514070b81d54000e00b400008107400b80050300c60141c44042c40d11506014a40240c04a2800d558031103a00c00644a48246502d80340424010780c1d0f0b02c108a0b400f41521450540c80701c04da0340450740709034841405a5600e01c0c04034280640740a01c0303074100c2c104170002d000d144520b400244200c140c0d800b520613007003480c0c123440e0820160134003111103030340004d401d50324403000e68003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 25999286 1250 25998036 25998041
    0x60408070c05060d0b0906010201050106093b010612020403020d0609020d050a03021b09060907050a02120301180f150e0901060302030609070602010c2d03060b1215150417120706 78
    0xb17668601482c1c649010621560041c003e19050b5000c0790307161018503282c0a18810b5010720900f80d00b441141400080c0c0c0b4107044a100c03006814100d440002035545040e40080c419440380000503c441c0c41400705100603500c01000c5540540c01c040d000c00d0235070031400001c8810300f10100007021482107040030720401d40c000c51980001000c04050f03c05050868090202c0c1001c206c0b4100d504c005840e000880c40c500850143c0714041c1c0d039104460034501d4100744240b9a910a0b00040e18040d500c152100d410035241c00b5410b45403910750b00034020307241c41c1040711072015598040e9034101402d440000304d60100c00d500c200300460b0024100d42d200c0c1400300700180c841c0401e029420055090104500c5844d00941104081d5501450305e070703000e00380700070002e0f0401d03d0841c2c201d401c1545481d00003c1c3c4030b10f0b81c00a058a003122448101450409988000b074060b411541c2c10b019260f241050001585880705840440d0f00302d8400740055524058981c1c18402c3c44000764903a00004500d0606010165 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 26000536 1250 25999286 25999301
    0x7030e030c0a0b150102060103060f020405030d05040305010501090606120b040e030a03050a06080102040b0708071b08150106030608070b1c1103090106080a022803060507020c0f0402070302060408070c05060d 91
    0x4400140c0f454440340710601e800040d0b91405805a4803600040001802c2035005012000e2000390050500c2d485400190920b50050810302c000b490124090043c0b0000f84079080c0100191001041000e02c1c040c0060030940280d4028003001da501c00054215460340d40044804511b940d043e60303514244800081c00914050300e40e6071050307180c180302185011052080380d09075400480c44900f4504030750f4070000c465110580854420505407100302d002c0b100456050f0140100c0b4014008401c1c6d0412489454881607200c3c404060070640100200b000201d2681c0c00d9a610342d205941d60301c46818500100c1c1c40d08585400c1e114907110f05200002c5007040654003a8244500034080c0c1955092040e54400f0480c10195201011520205040c542100e0034480d01d13100940132042c03203a40ea01d408080b6001112080090380105401c040360346020704401c1c0300d040c02180c0c11401c080081d240250b49400003440180070b044001405010301000640100043c20001d000c26620007001c901e820150601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 26001786 1250 26000536 26000543
    0x1203020d0b040b0120150a02030601030b030a0b01060c05160b0403020312030c04050607020409062c0f030406200f0d03051e06060f09040e06070e0303070c0b0307030e030c0a 76
    0x2894800c000c5803400c2e0050409012050392240844900304225403854200c4c807500c503205e4442e581400c0c0079103006a10040c07044000704401078403860203600243c01c4e0351802d166903100360403403103e16000a034a024140d0654043c1d00c0c10007100000c40c035066207005080801c14011802e0700701d000985003420b42c0104241e034400d030155501e618a05030011428001640c849a01e40c40030b000030710140c1028009001c68074001040401e1454007170b02c440b0226980000800c48480c2c0e06031103c000c640050341090424003540d802030051001580e22039031a0b000c0c81c001c0703c0801c0344a070050140e40c0b010030a480743c03040f00d50043d140710345060307884241e88a400200d00700119003000001102036a002148440c1d0050212203013850f5a41d40041200da54000030040d41544000e0090641a032030354840c4c1c42054170200000c01e110700f4000d01c041c1900307100c096418030079441000040f0000d1003010000007242d1003005040d80fa5183e18130301ba03010300222241611795210204203003802007000112840c06501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 26003036 1250 26001786 26001791
    0x20333190e07050f04050d0b04141f021305090106090906060509010c0f020102010f020d020301030203060c0702030d0f09170c01080106030e19140d02101103070806060904091203020d 80
    0x103403140104109100ca12a46240701c0007140011505800b4400a001c44040c481e4034914040c0c82d01d00190402c3e00381c0800342e9030542204200301c00c22405540000e558107800006107107500c5c030840201d00c0056079500111032140c02280a2205031344031401c02e030140c0700c0100000020368540341e00519440880c461680c1c0c55092900020700c0078011000c8801e42c08060703540101d10101a12640340e01684204101d0445d0f60f906010b4440f00b4140c070180540c002c891070701503aa54076600405252160241c44010200410060880165070010381480a100b1a0502144040103804165130b84180d40c0e204080b6404125103100403580e02040b0401821800d0b04d55200301c3e601c0700c40407005c4500c41c03511200503503c1000e81103019442c0c42480300c0403d11a014551070a08800315080c00c0c0703010018408096400480c0faa00142564000c0318120740b001400c0c9411484e0100c8014041e8902828050042000084c4000e01d0303215500680c0c071190708a144807810ac561844018020750040300803964062 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 26004286 1250 26003036 26003059
    0x501060504090f0b19020307090e0f10030b0c040503100609180c090e01020c070806090601170303040807030c0209090606010e040e03041509030501050108010b0a05031f020333 77
    0x40c0c07921038250030680105055601150355034a103c06000c015100804049244a494840074100e0008600c1240310780d8a220300b19244c0722040070000e0300500116862603000040000c0c045c15480140201da030020350a850507201c070070301000a40300c2c1d0307000150180600301500c00703040100d410000854000c1c4104100006d0420504501c075424040000c0c80010b02c960100402070040c0c102c0d441011060000608d4005052901803a01c006c1c3d41c88180c61790464402c02214007401d0140c5801440d0302c0000901e43d01680c5002500c0b440020401070590030302090100515101b0055a038186601812400850a202d281c1503640c00381101c0050000c0c03410b460700c4129003040d0203402c0d18400070000450405007000c00322502a1058200c1c001001003581c000400b15900340621f500030503040b03000140e1500100148868552036402042c0241c0c415040c05d6041c8a00f4214010a070790021001030312178a03200034017061101e902e00c140b0443c07030090000702c0c03981604100f40f4648070f02c126100b10021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 26005536 1250 26004286 26004289
    0x40f14040e0604140f100507030608030a020304030303020f0d0213050418030909050c0c070e0f060618150d0f140601020a0b040b07050d06060503040210030605030d0c02130204080a05010605 83
    0x291100600700c0d0181d0059400300b000a2115061446040b51400c150342044d8074036459a45031041500020b0030b415140ca080c018040d405100740c03405015601c000d145490724020020703640380314601c002404c02d60300091400d0380f00551400d41e40c000700c89000542d40d42103100760440c44038049014182c0304620f45192800c030b06180c64032804c81ca66140c1c0302c98011500d8001c000c8020503000b00600f814040c10000491072100612003036014048030360000d43c03075060041401c03070f00c0b680090046001d07940c02c004150303008106580b0850245000c0f0349403000051201880801030049130819811705080c2168005042c0e0b81d40c020f0380d002c00100c0014080356503480012a035a6511039400b41c50f04440101140200301a002002d90000c0c0d282442460007055019090886140c0c0e8402c10006401000f0b1004601d08602800c042d402c40d468180400b81c1050002519400ca00b0030f03201c18000e48a80c4142107440c2d60079002c660003500b21045464550352034a07030f03450724090030089809510f810700c081800d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 26006786 1250 26005536 26005541
    0x52d0108010609090f0b0301020708030a0b1c0605060102010b04020d02040e0a1802010f11070608010305210409180f0309050901080304030c05060a02190c0501090602030f0a03021b03040f1404 84
    0x102ca00301c3e41c90401c0185041580700040084500401d00c068440090320b1305600c00b40010807040d4840c50300c59a0320715000c00032808036044191428031403202c01011400348111074000f503024940001d800655900c078140183c0c01000003180342d50300a40081481c0c00c0e92070070f5034043d1084808540d00000f036542c070754640034101c3d0035800a01c01051200340000c40954410036203000648106e06200041c40100b1300001d20b0024654005000110000300500802505001000d09815801e010300225081601c40080303601840c0030384001107030340f01e5925660f8080403945110440d0020307a5030f001054141001040282c10380038041c006d0b00ca032000000d4640740041250100c9412a510b500b029017071208001700c6078801450002144120410f603003c1c0170f1150301010881d8840e0381085080c605e020005006510030b13a0081c1d0646d0000d220400b0300034401c50032100ca0701c03254a00141d032004103101000c140c8602100c42a11803001203008140400708030344802c1980c005849610134102484200410b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 26008036 1250 26006786 26006789
    0x527010c0e0603010305070303110a0f05010b01122901020313080601080601081c0c060204051908060601031404080309120f04091811091008011406120a020109030813052d010801 78
    0x20764071914023000440e22a0045681d28103081c8240c41c0041c3c200e440d50840b071b5148900035120791355140c0c040c405960700000011040c24514100b408903100d00240c884071600005528041c5550402d114040c0b41e1003801140c1b6520b00c00c041949515440e01b007840d0303036204240910004e52048800124011034002115114001c0010528150b82c0f400c0e5812150180703440401c8a48079020300010407641c1d034045850303ca82004030740f940146840d060065290881c06441941418030304401c0320440701c0c664442540c416003024050b650794a4007a0310034901640f0480389001e00c10041171280300e260083d00140115542030000740244000082428824081c448000300540c02c03818841c2c11a0404a030855413040740b034103145204981c3d401c0c00d80d0940340c7c03c55241c103070b18014000b003141ca0b25021b0070b102d400d48282c90040900e03902c550b00207040d9400707034080640300c0a004100f2100ca20194800340c005054050b01202c00541c0341440c65070303906540c0218910500b080d0f041c1c04440d51140240070f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 26009286 1250 26008036 26008043
    0x30e150610050d021b0604060f0b03030403030309080702040510030b01080304060f08060f100e01170708040807050a050a030e1201050f0c0702032d0d0908100527010c0e06030103 78
    0x240700350510754291030581c009034a4001441c2c0a220300780d8854286210302c000d00c0706601c054002441c061038400708648030900c003403802e40d00d0260441400e441c000300365000d0300d41c5410700040070116030405141e54022100b000754410f003000100030741d400584041d04101d0344207464001061340ca401e0340584a000d04d004150009610b0200c14450b684210807071500150048c010148008000000c00c20342c0382c3d084140c601042c0304031071030700a03541d0101011711503110010300107015044c010b070000e16078080540007a0282c0e80100d00c0c507081c0401480041002039119044508081203483c002c0e150b41c0d603441c5e0961256034010410210068103005040c42219510b001c07080340e983d00c1001c13100b03540180c47c0582c1c0510a085030581c0c01c0044105400b08120400c090000382d00800c081140340100011084c010014410b4042000074400120300d240822985004201caa4800a404000000000500c0040c5030028220b0651800662000c3c0c210340807a69466558440303c018400c03144002e00c00107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 26010536 1250 26009286 26009299
    0x306040605151201021305061201050603070908010504150b030307050c150c01060902091507150914060f04061b0801030b0c090303030411091302060910030e010c030e1506 75
    0x50005006900c40d0341d000d194010948049122000403c0030981e0a10b51120b05a600080d0350b10400c188800400040201b1260780c3e1030a0f14240c54502c0d07150042c46818059200403001c1174007117004100c2c0101a00034a07000f0070852526040c02d50480e4401c81d03184000ba40b4024a04601f400c012003100d200d10740102c0180700c076101000500809441c1109049079a600900c40340100c90021b0150b8001000598001758964220320100442921411043d5020607810407140000800c5002d456002a03101000092041c03d9410040d0b40d003401c81903100c2081c01400c0c00c01011142d00180f1500841c0200e0f410400020001210110f40405114910118038141d00400c0020ba42107001760340200d16102041c107080500e80401d19542080c2e03403c840510424503e444039040100741c442d440070940d022021341e80000d4011405501c100c480450040c00e090128072008c41c001c2c0c0200c40154418030003004000080b510041c0104446016400e503405030f049007404140340c5443c130b1409520001d041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 26011786 1250 26010536 26010541
    0x903050a030f050d15030218040b07030203090102040509090d03110a1d041404050307051c05040504020901020a0506070e03060f010e070c06140c040e07180b0a031e0b100e0306 77
    0x2d44090005140c504108401044407051020260040071010303139030b4100e08102c5500f188100710704111400c240d070300104040c2c02004003007140c0e52904c4d074200700c007402d0041e40c03626601100d0740a4403c170f40101360059010000d00080c9580026143c0c1020480d83d410400b500014440e000301d40319118210002801549401ca120001c0341e04a2000d150000d00c0040c0310b41c0310540b4a0101075084a081c3d8050b00007190707041c140b01c024024071201c0d600d600340f1070804003822240a4003d00030ba016260240f903001c01c1e00181030340200000c1c01c1094009048528038074105a00810320741503652100c0c040c0c01184041100b100b94115660305072001c60b40b0280b0300703540f4040c0441c1d2807000c0b99000e0f03900700d031102140303100040380580e0328bc060240d14218a03500c1d4100000f80020400160985080000309161102d2544c41c4d098908192640f00001a6541c0407492045000e00032000b155285d203a084143e641d54034200c0ea01030148000306480015452448810a80303c03500c0c05850941c068020200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 26013036 1250 26011786 26011793
    0x10b03120d09020406080a03180f062f0d090b0306090103020402071703040602130e07090302040203091e0a021203070c030204050406020706020c010b0f0a060c0b090703050a050303070f0903050a 85
    0x20300340c00000c08400088042c642d0300043c2c1a600150b02422054000180f0401410f0b4440c0030310040b41c0d84000c0c40100c0520b460074402d81700b5680e00c90441041034035401907102104403d000d0003400014210641c0c88414960001e455080c0d5207000404101d08c4e000001c1c20b60301010660348505001400c0c008640c1c41d507002d01000e584182d904481502806001e07000f180301d404042d5020b503000d840c1c01611101c61520100c0700c04601d811005456442d4420048880d51140006055950641300580c4984403034803034901d4500c1c1046417801961780d0f4440521200e000003005d08820b0b00880b018400d488103285a103460740b02d0440701601e842101e0800b0720242c21705401140e0002d10a06005151106c90789441c0c1c01c980240308000307a0b40c0d440d10580c6c46140303440b54084001c4142290042e18140c6030403409030000c0c4043c40002c0c8144c2c9140001a014001482240001c0d034001d01a42c05a00003450219143e50040740d0400200e04452442502107209080c4142030380d51100091100320844e85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 26014286 1250 26013036 26013073
    0xf06050f090301090f0b040c0509090c10110703051615021c050906161104020405010c030e180108070e090304120303020d0f020c160b070c0e0403050415050c0609010b03 74
    0x884982c1c0640d2500182400501c1030744500060501443c11180783d4149403802c2d491110b620342c80a481240d5490038072180d0440400e040c12642c1c1d0403900c401290614081c01c0e11940b403038203400081c0d8021050008140b200100e00000425428400000c040b40c40e01c141401802d0f01001000041c5d101000c0c4c00b01e1824850180503000c401400c10a0601c861400000e200740d02580000c00c800000ba0100c10820a2100d0f003080f2030341045505504240c02d00000070003440c0307016806402c01214040160791612000c2ea400c00c140c0c601300c0c14000c00e6031a40103855030f441d03043c803841ca02601600700181c17001501100b41d030142c0340000d42103074106942d40c80c202c010350054100c141c6140d0b690720302d91050a41910041524041c1040a009495400d040510794038601c0d600400442808001c0d4400007008984920300341c80c4003142c281640d4030f90307081c200c3c0c50f406240c01902c036082c074518101c226580c000c0c0142c0110715681044800c80c1d136482c1000c45c00d1341c1c4441505901070b070001e42804035a00031903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 26015536 1250 26014286 26014297
    0x901120f06090c0902070201030b0a080c0d08040e040305071202060402030312090c0a03060b03010b03011e0c0903140114090a0507060f210204080111030f040305092701050108010f06050f 82
    0x500c0c010404240360b443d2028044400e900c9242c07100c0e03001581a046507010702890030002c0302122410340c0d01c2d10b00700c0051b46035040002403030710400810740c112081101c144245c0d0f001d400d414003400034502c3c20349006006079100d00b2040d201d40602d510002d902c40d1000468071704c21a03001d0051424004520942e005510000d000710600d8054100030030a1745d21500f403e040154001e035404034001d0902d109060850719164003207406641410030426040700081c00380b20980092110014143d10160301c120b0303122000e904000e01c81c6406d00d02c10b94207007105420070441c1c40c00c043e001c00401d0707d84c81c2d00030795180c00601c8014031607081040c00300410342c094070303103110000c5d6a41003a503034003100d071032140701c45141c03080400c6403107980490180010f800034800c4440030104403031014a0360600c65241981494020001410000c0c0002c1034015030719402d071544041040c0070443c25040340a05224003407440240034150006d42104000200481c460303001c1801c95220341ca42ca4500310044201e140300b940315 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 26016786 1250 26015536 26015543
    0x50d030c0306030b0906240604030809030307020a060c02190e040f02030f100f0c08040c03170d020301030b0a1a06070609050f0303010602060a0b01021b01120b03060717060901120f 79
    0xb958800800700e481154450b10403103000001d009a45090681101c20910100785108190075000700c070f01d40c40d202c800454042d40c0e0014030b42a140c50400d80007030300d1031050480003500070a40343c8000640c02c0d00001b00d44a4240700311210b03004007801d048941080d000a10400d15507a41140c08600410400307440d04400324000780075a4008000803040030320300301000171845501541c42d605000d607007501d8402c81480c414549480340060038036403610302112480d40005010340c44040440a0084000c2c1c0c100c0300c103d01496015500c81d03075642407880042004441c2c1400c064248694241c0340c803800032569000322002031142e4104800c030384684000701280001200c0522410300003071210b04040020391b0080c02903034010301081c90103000800a4840340006070b41958041d0000d5094a4240005080c091500780303000140c02c151619040701400345900c009030035014000074451159408400291481c0107001000480d40381d83c418800140024031441c0085064142050009125280d51005c0c241c003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 26018036 1250 26016786 26016791
    0x6070f020a170114100608070e030a1101080603010902060d0b06040302060304080307020f0c06041701020d140114150d020901050d150509010b0a021b03160b040303030b0607050d030c03 81
    0x550380e000c556031003100e40000a101020b51500605580300740960f0a84128080f402c44540c1440907082d140c00e0154054101803200002c001540c15126605418030610300908903050701203141040c0c208214514401030018029900290350340c20140101c11401c1c0c1d01070b04e00c40c81c1c12a02a086801031815200095000030200400005a501c070406580218000c1000c03c2e40c90a104002924150380c005001c8440e4000c52140c41055403400181c1e0300710b07411802c1046a002d070013a00b0794020f00c516600001480d10740000708000b00620540d8078142d42e0105481c0d0042e903240810880d1891030484161000002040380021400680c1c01410b0000d8043c1440e80c103046419900d80c05956440800c102c0705520703042c080000d8601184030a0040100101040c6402102d00000791503003145809401c00e81901080d0502c2901c040201041d4800d051312052501502d5600d550717072917031007440306500280c05c0c81030101651403d9012240e503d41d10a00a000ca10000d0388168050f00c41034509405059 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 26019286 1250 26018036 26018063
    0x81005060d020c071403150103031403070e03030715110c030405040b010215010305060906060906010f080c0d060f1502011e0b04060e070f0215060a0b0c01271a04030e0607 75
    0x901c204914009001441c40e1680800703172141c181407800f0072480105200c00300043c010008240c011113248a24900c00640c039035203654541050300c03030400503860107401d8400010401c05003c604c003500c61580c031a080040c01059000481c400300da0188001c00c29080e0000c020070091483c0075441488040010300569103078401560180d1180c00c8240e006070f810380c02c007204001400000b4882035500503000c444841c1903040000009002a6800c10f980051043d50004591050361600640340d00b1207840400384104e0b900c0f58003000a50100b807140090300a45882130480b0140180600d01c1c54030030440710802031003d80740f014000380c401150056005692502d002c21404950b00e41c0b540f040c4c50302e0b00d030118a400c000100038a00000302d229041560014014006140d0b15450310000300c0304000140c6031146074014a45004200494440034030780c2076500301168044400032030880090092002c5d603d5180d00c030040b6010800200c03801070000e94060346840c031502c0c142c005000c1d040d006000002240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 26020536 1250 26019286 26019307
    0x9270708030a0207080c0105070309090504020a08010f09030305010e0105061905070507060504030209060121020a05161a0c070503030a0f02090310150f030809090415060b0703030c081005060d02 85
    0x154042c0d4690801038000800034882c2030000c20071100140420702c0c0107482c00740140c070300400e40700250290005113511140840d09540d00d0609002c05008804000c208148201740190010121070340103c0c0403906142c00080e410600001841c12940c0183c0010324120701c65818000c0010011403090500c0824800b2801040e400c01c6107002804141d11070303c1d03a035400c0d030040029012004051504100c0c1d424080342d00d01922101d200c4012150900c0542c880e01660019a010b002d440d03c41168a4807034501c5a060100340c421400018141484454098841d003a140506104c0c1c0c60700541180e101f0000b00e8000025980440410070141c000107041c80054000242810b60741c0306010500d81d222907011489440d46410301000f4201c2c81c2050394028034640da920401e000320b0741644e11034410140001d050181007501c40c4118084038400b0403286441d242c00180b80d4101c59010313000686001c4054503c540180a418003489414180b0240c0914060070440245e115030101c5a20580a100b1903108 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 26021786 1250 26020536 26020543
    0x309070b0310140906030703110a09050c03010905010e070912030e03060a05070801080a050c0409020f0306070503010602010c08070e1908070b0306040c03020f0a0c020a0f031101080609270708 84
    0x35000307580c0aa40b1040c80e00d11001d50040d002d10032103200b000c031202840080d503400034117081100e511440ca460690381180026000840d2603105007a02ca0501042104080700580290f050310494141080303a641c07503017403491b4070480403142080410315181013401114080c100c030f14502c17032080c94482d0400c1001800700c0d0a0480c207482000c40981c903a014418031071f030000c005a0240810038000e01e44100e00307480d403a50360700260030342c14051656900500e003913488141015080c2180541250140d040882c0000c1a03503100344201001540317043d000c1c030341c0c50b4030980c00140165503994840100030266000c011240c01d100d040f481c80c140d0b0030507001030241018001180142400403120351a480c0c60401d00040d00c104840314001c151041050402e40d4540310f0031b86503941c50f01d15114041c50b41c90310208581904c02c2d000300c0801000f2010020400c00e84418240c0320710001e81c0c4a068a0312003005201286205981200c48099410074070007500c0d10364501d0400c11b007120022030780c1e02540c0b911964103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 26023036 1250 26021786 26021791
    0x50720030f0c0c030c0306060a06120b0a0605030708011e0509180d0f0207080d050a0c03171006030f0c050306060f04091508070f080a060b03010e0106060504052b020103020309070b03 80
    0x440c2c1010030f0503030f01454184403a1203a4042540909264a00030f400070340c04540703502450307090020f410782c80d00150101d903000e0041223402502e01c4414548500c4003500c2da03002280c00038001443c090020801c544612055804080210140d4110030b003400100070640200402501100c41400140603600508004503814088140c40d000c036801c0000754000d048c50f8007508018001d5101114503e40c0c15404001c075040c036410343c40d080001c074038180340c1202d0000d440211080011940014801500708000e6a102100c4880d1400c01800c5500c00c00d000c10781c0e80302441ca0012440c24400034205051820080c211802500c20561404e42c403408000200c404800c540312008410540034400742d0720800494000c0c00e0410100e0704980d01e400701899440c01c000d50000c2c1b070a40c035002003a0141c0c03400d4010007030b002c10440003032200580b5081d004040313401038031500f44140c034002c0c448041344080c0710021100542ca0780041c94090303040e8006402035440a0a01d080c82c0c070078a1400140c1c115100051030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 26024286 1250 26023036 26023057
    0x120803190501150908120412020303071a07030c02011406191d071808070312030207120e0406050109080312040f020d050a030905040c080402010c33050703050720030f 73
    0xd041603c4207100074846080c0f40c0105446030301a0380395600c0c10601c0d1082d42c3c211060484800c031060114401f0a0840c020804014144030361903460b640c0d13401040b1039282c03080c0743c1d9680c01c00400c03290403406c03800d9a00c0d6542c001c480155840101303000c1d0030405500d0340c2c0e40c0c0c8422819901c040d620302c1e40c45807000e540803410456001020a100b945544624025070704030b003080e01901c0303090611210325116000c81c80300906c24800100031568560203070f0155852260440307400a00e14000b810058168420319180d107201d6403801601246540c0600089001c1e40c1103800210300340142141190440f040c00b410941e10104600408001642d84c401d180d03104c00e200e000030b0603443da10352801400100440c3c1203c0e01c5141056402100c10ba0b2040511360b100e0340900c0e000012120908105480c0c013189c01180c0e00040315001103420018000b900c0d480d800ca1030110400aa5a8210003107088850075610000028000c118035408401025082c040407a02c84003501e02d032140c1500300040380da00001010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 26025536 1250 26024286 26024309
    0x5040b040f0e01171b01020c04020301030501051006030507020705010503040206040f0b0a0813030f0c0c08071716050603160909061206180b0c0d090203060c190504120803190501 78
    0x5210491146202c60f00600ca195039100400d00c90140c0703da101e0000241c085200042c00021084583c4200032680e103200000e002155696124240075010300700c01ca4650307082e6028945c0c0000c1080c441c1c070441c0c0c4035840d1070340541400c9040030011190781e030002e071041ea44a241403102140e005081041280103200d960002c69903520743e060080d14001d0010103258002c2441861000469004800340e4400c4a01c1d01e004101e0745642e160041499906802c030075958420400c004c14800c25103619024415a01c90869002c60340441103a81105034500070690014014404141c010544100ca506828074609000d00e426031180d01401c11151246d02940030003841c0309815050108600c03d00b5020940f02d42c45141c1d5034141e8403002001c010180014031050f030000360080860f80e1a23801b2080b42d540c010155011410074554010b802e4111180c0555200911814400b58070701a404803011038606480c0c0ca0140040b5841c1d40032141c01c01041c040360400054141d175001c030010301c030f149d001e480c644920 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 26026786 1250 26025536 26025539
    0x4030c0603051b07050703060c20030d0b0901150507020d0b0708071e0903110406080109050c0102010e0607020c0607030e040f0614010903020901030209090a080d0203010302011b0f1205040b040f 85
    0x1603e05036940010070f040300c95002c00284011402c045140c200b501d4010718049544074188130225172090300c211801c524a5003000710b00b80e0a0801100a0a1208840c2003c1c045030000c20101311156000f0b1194075001c012035640d0a0f045406140584580c60006033074045081e42c5072540d0007001c80488000c0001080e01040040c15600305c840c03869650f0300050f4100603a55840800b030b0680c000b601019210300c4005110158664803a00014081c0c10b40c14020301c446101890701d5550f445d40c02003500d025500340440312098040014141d0b2081c011340d80100040c01448090080561291109604100c0c910b803074035180f0385680c01880c11304120340b4000542c15203850082c8120889151a403410003600d200304001580c0c0b42c2c100c160650350103c808220541f11130f41143d25116801e103006000304004585413040c001d6660155048900030717227030003410507828071440d0240021414028582104181c0b02d03030205505101600d03801071941070442c03401341c88003941006a00542c1c01048000c0c0344800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 26028036 1250 26026786 26026801
    0xc0c2701080606090703060b031b1605070905060609030d03020706150605030702010f0513030e030106050907080a0f02030123040e0f01060305120406140f040506030112060e0d0206070c020604030c060305 89
    0x10000da200c1140d1804000180c10304122003209e1001900c81c0e02802501c10223680703154510400c44510b80c050303a400340041c0e10b1034545903440e08054807401810524060000e07040e0f00380a0102e40481d0001800b90500c0e08210300d05034003d42003284159100c0d40e490b016641c0790403039500220007034801c94480359241e1030701080003801d5606032244007041d40d080c807043c420043d2045e8001081c4c0399050074020005207081c000b2a00520003680015807020108090000c0203403c03081c1d40d8000c0032200f01c140b00400107070041c003050303100038491040803d803410605c80100d24110381880d20803500500c01b003280b103040200c4900c0c1c0a511300440c02c03642d640b00320410410200b0400320809185891030f03581000d00d0403a0241490490350784840c0180000500c11052003808821039014000c000c00c03081d2a0350315031a41c4a51284030100c100c80642c0307400780d51004248001242488450030f0350062016a40703a680444440c4014601280c000340c09000c0440020032460014000d003032540d80010381843c2212 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 26029286 1250 26028036 26028049
    0x60a0c08090d0b0906130b1506070c0e100e04050c0105070809040e010f150302030c04110d05011509090212010510091208070201020c0901030507090b1c060e070b0c0c2701080606 78
    0xe01e0342c640c01b0302d006c801e40001031100c040c003030780300041c4150190401c1d00f00c1c02064480c4a40b500080505c0120031010654031901000d260007000589020b2480d15100e01c200c10540300c084da00a001c40d408a001040325621900007412018449c0c4609818100d2202c0400c090364902026100680d44034200300d08000310070321640d83e80c003080140c80c4044d10b14540202c3d403200802440140102d441d4005006550142c0b42151a10000003400f08495070351000d890420b20040d040004c00502c2e0342c0d10004510314a4002d0700c0719100e26010f010500c5c1d18100801c0201e0626005407001d00c00041d00c0000d465101110190405004000b0182c1c1c852030307440024102030420450b940324060301c00051020500000f92581910010907001400003100300018030300c51200c50b503040c448414034403140e04110784d41d0407020040e0036040c03c8035038442e196000d4640c51b01484016055a5100e90780351852840c00d9861410802c00c10f080190141541040c000707040402604400c1c000c1c0e01003001c0c42803e06000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 26030536 1250 26029286 26029291
    0x20304030c1a0a0e0c010503060603070309020916020d0305010503031602040612080306030105060603070c060b040b0a090e010b0402250c0902071209120309060c03120f0618020405060a0c08090d0b0906 88
    0x1e4060400c50441700c0018001e800003a010600907030b004000600880d010342d100d6000103400600104203481d100b1810000c0254941040005000d610214501503010f0302540e03050700c000038042c50410341c40322004040d001c101d00060b40c0c4941c884500190180c0c201e2400c0c6015400382010b155640b80040500d0b00f910384c00b03085140100001c10421541a510043c1200881d502000125030141900000740c06810380c0f22030a41c0c09154850000340b00d1301964403c82ca05050701e4028030078000c0d03000400040340501000211140d40300715800840f0b03410101207400d420b00c9001101030071034480340d02c2d404a0700710032003c80c1d04804082000c54850b4200035090000c000c5000300d041300c01c40c3ca5070001c10321400ca2144005106802c40d83d04101401101034240311980c0c00b90801100f00390104a0340038081d01d204640c1140c4203001c0141c14003206008a6003511713409401c8a140c4074040104a07030b4805a61000c1e02d0004080c811100250b843c60901000030b805100750380c1860521001c641d0500c50301 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 26031786 1250 26030536 26030561
    0x30207050a0509070804060f02040b030601020d020703050309060a02121801080c0f040b1803100218010504050a15020708031c05130203060c16020603010305151e0109020304030c1a0a 80
    0x804030400143d5911020f150f448280d52a0418103520740d46030410280420610181040e8004140450205844030145106510903422590105000401a030b22805940030290242d0810004030724281001c4008090168052044820340106c420403101c464000040e1074040c43c0551b5800c0090f981e00c02c90107604800e4002c9204e103000d103142d6000c41648a544650116030001141d00041d201c01100c54142d2904082c0503240c03100100c1c00e21900940c010b40d080e807010011101e080c6083d5100e282070300e041c2c2d1000350000050a0416101101268056201200714420075801281042c4144090080b02003800103110800215405200c19074500400c9451b040c4450410030002d640e00080322504a20800840369648410200f41c0262031107064010303402100001c0000304001e40002c01030141070018160310b5542d11004803861848203180c0794a010f2413600d1006210b0207405074003c50f007061082c03c01c2c040003486941c0350380e060151a8842da500280c1142045010025405407a026040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 26033036 1250 26031786 26031799
    0x30506070f02060103021309081204020301050108070305150a060305070305150a0506100804020402160f1e02011d1804050312010603061d060d020904081e07030905100c0c0602070303020705 83
    0x20708075000f540c4000c140f00191080c003a2a410801242c66944005556600881500d036118680c0920125984054408a01035031030f00c4000140c9076400710765803080c1c036806405485211b0049512042c1c0b440064149030708190344100000014008100e0074000f10b20600140c121403000ba4900844408000e00038070340c407400c00082042a90300e81720317503c51088241c144040c6a85a60012a00070701409003041d40b0381c0469003c2405014800741052091441945d0045080c002191a8950f10a60907002800300b8010050800325000344e030300700455034601418030b407008a081442c0740d035000702c2520305580f02d82000175008004201006040e014240c2070030140700040c0380c0140704644080c20f101c1c60b100c5900707031004a40f617a03641010410b84160000d0048801e4203003030821030307401e078040600c5041c6619024070541155550005540c241509525869082442c0c1000d1001441c17580d5040f030304001c07081c0b1102d0002140f039410040034001580c001e004050440c40c1c040c3c0790403e19000f1611034132 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 26034286 1250 26033036 26033057
    0x905120a1205010608011d1b03010f180213180905010f0509011416050d0b0d1101080708100b09030c0307060e12030f03070c0203071505070201080c030f1501200703050607 75
    0x40261140e47c24040d4034405048580d20307008909a20300c90307100080300400b4000000224400e20300d2500c01a00c0090202c001c00301d00305140b5504a200c1d9906810005114050802421040c3e00541e890407404060224880350300d0f68a03a42111445003480701c840742e41d10248800c466091040c2c044100f0f0080072905a030030000c02d40c01c28600a0b050391320800c10001030f9040004e40e130750818a11460050804003000d5881c0c0740c8044c21040e60000c00740051001000620341c0780c480d101107409a82800b0300440302d6420640240480d501540010340c15102d4413402c070178030362001c004d0000105001e43d40e1940081ca01000c01c9450703900c5080c3c003046503000344000914043d02c40b084036044a00313428240107034140c03480400d04001d0254046480d44070095584551a60004001c00d0f500d8803da880c211755980c2d0303203000c1126000c00c0e01d001140d442d650b00016412000031980c01c0d0a0307201412329004890200c80c1060030880005850310642e00803203001c00c10040204603e9810061a0406000a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 26035536 1250 26034286 26034299
    0x5030421020c0f040b06030115020d020607050f07110607050601030506010b090f1009030506150906040207050303071409041805060903090108041104060905070203070302070e0c0d0905120a120501060801 89
    0x24812411558424030b804526803016a13601c0d4403400c0b6141c07001e410f25440c0c0d80c0d42c103140070400380b082a80c1f00160064803502c010340b40c0b0114036548282c00c2c90b19032a08100040445561581113104116001c010001c62007680350749d0000640846031080f401401b4541c1145041402c00300b0607400204804070074000482c6554172084001e66446050341c0221a00124000c121805403203070b031000e0081e010341014440000c0701e12008419501054841900035203c0b14148004c91040b1840681950018000b00e41658070801c0e07440c08081412a04905001e0b00341c002030205c40f442d040b80850140501c81e01420400c013400541d500400c143c001c1d504208102001810001000304020b080e07800b042008845590b40d40d1001b405003000c1c060070495440c00c15400395607607200c808140c016200d10100003074122200048580305804100341141030410700c1090310003130280700d0f90446060049446070000d081c584000380220284603942d0b841c5074032115410034100cbc1c006070858170820680c6001030201 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 26036786 1250 26035536 26035543
    0x813032004020f12060a09110304030f0f05030109020306210106030c09020705030405090c0c010513020f09090d031a06030702070f120201020d2a0b0105010306061814030f06070503042102 82
    0x3907804440040f02d0300d545e603100203280038040740c0203070b00010b1401400c0c00403003a049000c3c40c4103d10a0703e441210600c2d03250203407240f0300c40480c41c80004008000501108004e60051b541101d009003070301500d09410000d030008103030b40c4204400181c1d55214200107011800f085a0000c0c5101c103001c5141030f040da1902c58884c07046008250051500c4000f0503222201d0600325941020a440204014100324860304a500e089000503440780c0c817a440c2e15445458081c10403802030311258000c107106d0b540d546098002d482d4440385c0365195941c3c10780c0c05a454481c013006520604065000e882003e0030f240074407401511039044201c00711071200940c0010f07600020100c2a8140134249648031101500185205142c420b240d52032807501d50011900300008800301905070b4509032010b11080d52101011a032010030544640c03039a2105510801000e018030200c00c130310400103800d640c60303170000d11440d034903104040c0e038a4400a40c00100308800d110070080c01104410340b0400d80c003801000b907a402580c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 26038036 1250 26036786 26036797
    0x1b06070c0e07090b0c01021902060708070f0c02030a0b010501110a03020307230307030305010302030105130203120d020c0708070504060b0a0206040201200709020c0f0a0b0a05040813032004020f 85
    0xc1d0704904800320311614000d880c60700081440c081c1403540c0b540308940c224041c1d04050800012422982443d0f8041800401e19510504203940d0304c140643e115002221904a503c00440c1406101c084250140c0c074180180340300c450140441c1200d95162400051015940115508042d000f5200d0940001d03404800c4483c00c80d00094100d980d04514180a49004810200705c1e249100000d206000c268040c1c01c254107da008030b00811066941051404110049450080d45a04140102c4402c8200b401c040c08501c08540f10050070126039001880c0762a107942c03c0f400059009803c10829403800d4002c40e00035040d280c0da0305040c41050364011723540380c00181000b8140001d4003076a0301590011280b41c60b010522a080f61406690f0f018680000c0d88145c1c10442580503840541105c0100000c00111440c0c2c0a01c18107030702da6400560700c004000c080c200300d4142b83c08014400300740d02000c0c8400c004d036001f90070f06200100040304051440310000c2c6058012401801200d0074902e004081d5031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 26039286 1250 26038036 26038049
    0x3050607080703061503090c05150403080d020702030604050a050c060a090537030611030609061905031501170d02100f0f0c031b03050903030402040902030a141b06070c 74
    0x250580c5800a081d001341c640360704003e820b18402c1e4121000281d04d034000d40036150042541c100c1c515144c1c014000c840390340300c1c404100c0c0030301044100005000e4100908445102107401800c03c04140c0c0040d041182c1682c0030350700d03544441c08040900c1000d1111000344202114500d20300000b030040900000c07001d2045920030003411161242c01448000c4036200052510951444101d010742030644a10b0303607000135240e042c500369220070a021507070200c1e4001c0b500240280700d2a0f6448041000300c0d41e1013620811040151080080c030303500d0802c0038840c01000b00004000350340c10f200c9032142d070140d0395030b07804095403040d02010b8225070040380005511128180204000328001505409410b003089149411807030001005c10465159002490304800c0040d002c951200c20b0740200d060740d01c01d0b50160400c0c0c10410104006141a0f44040016031025083c0e84203a031450300e8122030355805800c24040c81d045080c03500406141c2e8641c410526900f20398641c104003580d1598070300c04140380681c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 26040536 1250 26039286 26039297
    0x105010806061909080d110601050d15050403020102070303050601030b1e03030f030a0204060f0c03050f030a09080a0305041101170406020c070e090705090601030902010804020405060a05060a0503010806070903050607 95
    0x507116072503200480d0825100c6040540442e066444020f1940c1c0d07141c8112101406003a1404071118031560900002500360030040242c2d03420071042003180140444116001c0310b1154407140d0f43c0c4040d0041901c101d0181d000103840d8010390030081c080c0c407070091005040514140204c441552030f84d03101d080e02031034445000e00c03030f0b00340c3c10109203944140610021400004000c0001e900c100b600100150791013650707840c0e47e10030122010b0b225142d40500003008103105225101d501520305000c6c6510004400c800300314000d00b80c175000c6003036100c502c40c00000b980b600e00704000d1080078805000032040a203059a9080505103c01001040c0034000030071454002a201c000c0050400c5201c2c0604651004040c650402d003c82690301ca403e4442e035802568580d00103081580680302d02e0b02565010f0f1a604016983d56003008002c0000030400c9074014211803002c10103071a510080d00ea01c5045484040c0d030b95050007a80351422400a0100041002d101c409000041010405540000083c00d14 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 26041786 1250 26040536 26040541
    0xa03030c030b030a111504080d08060102030405040603230303070f0c08041e0e0a110415030608030315030708010501051c050c0310050a05060a03050d0c060b0d0515010803030f01050108 81
    0xca019282c0c441d032080c0c0c14454600d1000c03d211a0350f02c0f0020708501190034415008000b6405e0031030b0b0055100b070501942069000e00c031418010444550300600c14416240f03066200c0d00014110b6641e40c0040d030710170b50703403405d03200c01d480c4a46000303071083e28214019070841c604100000c0c0b022404116582c1048101803e4800f0050307010150b4010700218035038200d1407018442c0e0010010441c0c49451018242d280104805041621440c1103012103004818503103801c1110352451142c41c000348c9020140e5840f4002007100e02030001d180500e0306030f44501545e2040300101454080103801589160749000010099070f0344054096184220440e040b01090381182081820040108001034040c080c0369852142c228031980440c0c85074200050800c9a80c4030f06081c0300c80d2000f6400005e2080c1e1055070040300c2c0f0742c0528900040544558008210304c0c104c0c80219040610140c8100c171a940002d014040f224400043c0c20b02400a0000441c110303d4140071a02003118184034050601c02c0703130000f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 26043036 1250 26041786 26041811
    0x908070b0a050d0c0206061003020406080103020d02190806090f030c061314010612031710090f0f09050a06060e04030c0b0408160b01090e0a0302070b0c01020408120c0c04060302030a0303 82
    0x99a201c1d00005004025071358002c18003035141c800c1116031a1050381c001e5480400382d4064800e07201179940b15582d0002503825582030004000003150241d81c80800c181d00c00602400c00491000540041c03006407925061680100f45000d2403281074800641060007500a03a1b440004d68590128400560800c88002c6040443d40c002107010010321075401c0080111303428202c4051b801c412440fa65030760214100e111840b0070340440070385480c081140e00140802000ca4a908403000e50311400c0e00010b51184125130410485101c1c59003180d0302c0c0c110001d60000c5c82018800c0c43c0080540700c15003412842c2039900140701c070303007640d400601144035040800c051048140a64994010140101c04821701030305200e101500c003485042081801c281c132000400d0004034128000e2036040c1c0040403014205040c8a609801c52120280c00b59801e2000050b40502004003211441c00481c0c0075075140300001040741010b03070300201e440c000c82c10704e075007040140c80000d800f100b40c542510303000480550300c51 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 26044286 1250 26043036 26043047
    0xf0706051c020d20040608010e010e060d03051605071e0e07030e07031a0603121603030b190b0a02060604060302060a0e0409141f050903070b07020c04060608060906010908070b0a 78
    0x282030304c105219003c2600108004402401038075026186c440f0309030380e1030038a03048a5000b401400d01c2000058081200340c00c00c4090b0014249c400e040c69402c00d05074aa410a5004c030b070090a84555000791000c0040d01141c0070301c420071588a1501c5a074290909014003840d01000c1c0c80e1030105562100d003000100014090f001c040c562240c140c031444200c0300401056000246d0740c0510034003c45820300003880d412030854855008224240c0c52019507618141c0043c120050b125030008902d11200c132071030006402c0c44010301b0341c2c1d0952545484030304600910304140104542d014514051080c000350b990359040d10088541468503524100ca8900414058030070f95200070812840807445105410022882100c003440c00c070f86445200980130001c03002d80342c0a071846182c6070400c00003100460800c0d000180d0004040c012145034803c05000306048542a6100300c0000300c0c005c050244a242c00600706800200919003084000c7c1441180c4d40c0700c90180c428881ca07844005800c41100380a80c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 26045536 1250 26044286 26044301
    0x3030c170c01020d0c0e0a0303020c040b06090d03020d020601080604080d020a110a0501060518060a090b010504080303090610060c12030209010c020409060203041a24040b0d03020f0706051c020d 85
    0x80080d03484020300e6404134040c00c10002c4a401140750603250181c2e60030813100e2601141c0e05076000b44240c01020003844024030648848503041502000440103d843e40d0882400d503501c01e41c000d01c110000c00c100207003081c0d4181c00500194001d8000c1c0004a0340480a592400c9000240103983e2400b21071b0030303660303c15010a205a03178003460421400340481980b003001103034001e40b1480b640c1e4424000402080004590b203542c009140601400f10031080c2d88200c22000c01810614603142c0c0b528503080c5960001c4030010b0072644814100203c2c10320754440900202301ca400c1507100807059550380c80e031180c00012060300f01540820401e845038032868004e110180c000c0c000300480085803c008010394021078054940a8480300301c60b8480802e140700300d00c50302036840c60015250035250001c1d6002d80220485a005e82c0714a40380317405a80b14540d44922038880e8004200d100480d14020741024041da1203c4140402403100c034128000840d0004e0220380c034500010380d02c905d2005048020035a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 26046786 1250 26045536 26045557
    0x9010810090509061b0901020307080a0507020a0b040503070b03071e02070b16060501050604060504031e0b0c030603010e0609190804090c080106080105040c0f08151507031101050103030c17 83
    0x511040c050401004244c00c0c0c010040e560001400c50300c00d01c0c0305c442c58814483c070346005900c20003280d008600240040e0039400c22515004c5c2c80c0c1603068000902030881c0f604500103d20000800300501c4c03508210840040c908407012504500d00f013032020705002084212542682484041c2d2100701e4070034010795000d00b5403500d0309510784000140300000c1c80600d42c0d0440c0c40520303110021a141c681078080e901201d20f00c0d0744591070315045603034207600c2070319a95488081c420121b417248005460a2440c5110741010714415440386000c00801d800d640060303261a0a0f500410240440d28501040c81d0780642e4030202441c034000c0440ca0326070500e110310727804040481d04e030205000c0d46a9004640c1030407114256242251a62100b00b00001c46890405c070901040e4170380c252804044c042c0c4002a4005480b41040561441c540c02040208094107031a0100d0302001800008068104400198018158008100e03a44c1141c4c1c024000000c000700c09481540d001c64500a205500d800f01c82102e60f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 26048036 1250 26046786 26046791
    0x1615020409020904180209010303111515331305030114010501080f0f070e0f120105070f180501270905041e05071703040819030e0a03080901081009 65
    0x6465a1400003508008001440390381061865a170240d40c07005111036990300100304160b2a40f96a80544070320070f0440004c0140d02908030106d890390000c40c03810f40b00b09011407105401007030600421107401c020f10030204010010740300358000c5075048c244c0009003c407c0600c540d44c8281040000c1d9181065500250380340d0b081032188880e00c4005409a41210400e8842214030b4940c40c50480a0a004540411000c103842c40080d0700c8902c5114100b010380009400031200142c01401f00d030480781081d0150340542e4542040c4586036500440e2400350546900d00121004031ba45c6580c04403600324825141000124198020701c2408241041c8840c0366107094529500d5544038204080c1600319801c3d16510759500e4100720f07000e09040d0814905034440054508541085045645205d2206081e02244424040418040f40800400d0b140d494100e14402011225241c014040c4040080783c45c0902040c24040001540c400c040c0e50b0401c2c401d0800079a40c1e510343d6103041801c1d001d0791081039080e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 26049286 1250 26048036 26048039
    0x301020d0209040b06030403080402061803060703150b0703020a0b040501060b0315030105010605090603070305070e030d110f0c0109060309060b0d030c150b0319080c030a09090614010516150204 85
    0x2109500502c22090141d40501030004500c08205031400101c50103000700769840001401460701000401e04801e01d01c02c0c1c52000314124020901d4a4011600c000110f41e840104420028455028200500000c1e044904d0504150750003920341c001e00c00024903400403500440d003041403e403c400060a80203800945918184640c1c2e0250311401c28044c1c0039510f0407001007113491140007107861110024080525588804000700c0c01070800410030720420542c08100c0300780c0c0c0d4040c45800c0c86240c01e0358600c80400e40c1c11101d2070400540040c0340700d40f9884030b60301d0700c02a40c014030a5801c0756042c0c100051200c0c80760070400e02800400a1180c0d008904800c507004043c7c104e02c1181041d40a000d540c851084030307421410445110341c03d85503050f84030102c81d1400701780710b10140603014030032182e02e403c052546c5075451079074025401f010042442564148010780040c4101c80048c81b0303420a00e0f0089003a40000f030954803900c05069800c0c0011000311051003d5110304854004112a0865031a03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 26050536 1250 26049286 26049307
    0x40e01020415020a0c09140609040204090506100302040b0a03020102150703060801020a170a0920030a05010e1e03031012060212070917060c030f25051209010c12020a020705030102 79
    0x4e80104004942ca42a1803c01149170007103441703001c070212040510003001d511400c040010b909401401264041c0e22911214000b45080c841c490182e02803451003c5000d096104001c107132480312a003036020b000703103090402c050b070383c0000c110500580c4c88500f80c40700d0301c0d5008100d01420198200c2c0304c45600018081408950200da40003c00036070f1a8842102d807107000c600e6058485648029000b04900b096061030001920014422400b0040031503041021030f40d01c0a0039110b440c080161035400074191080740c0381d40b4174003501e00220460040d51031490041450000c00c5500d0003040d020651960b0048200166541190f661045403170038030050b440d0041004040d05900c0c000d24410244143c070203218160005103507030040c54803800310380c1155100900c40308100801030149080c8003034820240700c8070076800e98503005291240d030340075070340e510035248415890000f4083c02000d078500044007800591010050755030045007c8056901c1007525000ca00c0c09519404c6940d042d440014142030a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 26051786 1250 26050536 26050543
    0x30609100e070f0906020105040f020906040b0a0b0409060e0405060a0b0d0f0c0801110a05030c0d0908040e010e071e0e01050c07061d060406120e070306050103060c0206010f050f040e0102041502 85
    0x10901d21340e4607540c0d500d4407000100d080c5d42003681c005180388401c21400005180c4000b42c6540517901500004071000d894000030b0010099034010117411a00240134011500c2d1401035038040c105d4540c0740c00560816607a0705a031450004e2803004116640c840d424015901e0b8285a041c0e03e80040700708400110030f0404c40c0d1107c0103846004102d40c030b0102d0090707562525405558041c401d0340c803070600310f0b50f071900035400e00c2e032000b46002d0582e5554016000000c5801c0b010300040c24078a4201d9120b903042801441070128007818003001d01100141007000c00c0c04c041201440381100d0310301104142c0079030300161441d0007445002d01190042c0580072130015400000d0a5640c800d204c80302407140444024000c0e14032940c00b070000064681e515281d4441003980007840018408021100c00300d0781e945407001104c0b4281c00840b0320984517040c10309010303030412402d0701608170058482142485c000001c0c01c03425103106094091525800c0e190501c003029070607074005140303514000d1010445584002d45 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 26053036 1250 26051786 26051807
    0x19020702151b0c010f1209020a030b040312110f0702010c0b0a0905060a020a270306090305090108060301050c0a0c0809040603050f1203070207030f1b0e180f03030609100e07 76
    0xb018000c9000004401030000342d4000150040e11070300080c1d841081c4c212078400c1040c03407103107500d515818020010717141e850550004501a11842d8820300b02480c000f40310300700b01d04441580c81e0a1a03404880d10740903100b00c5e81c03a40b81961900d55509d215100598071210030020182c260b592200411544a0b0590000c0241d5403240e401e446241d502e01065601324003e85040100081c003c00701c0b02031104138064580d089040b0200c0000c100c07503070f81d03440d10f041c3c031514a01100000c0b00440d0902c801c0d41c01281554004000303e001307000310300c2c0806d4591668002d4482c41010414154440420b06c006001106e000440c060030134004d645d01c1c0c1c103000d80d5400c1d810070300079014418032406100a600b0281074a0003002030340e0250030198a1903c540007581c85010301600c00c6111032090340064041034140c039008000c09480c041083c03401e100300c120944100c00802ca80c942195080241000d400700071254084012100c010550310b41201c00034440304150003a00d43c15607030000703101049820016a52 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 26054286 1250 26053036 26053057
    0x2040f021e07050307060513050105010807150c020306061e040e0c030d080403090b130815070f0c0302060c0310030b04030e0906041103160e030102130503010605030105040b1902070215 81
    0x594070094004815507441000e101070041d0b001072250200080b03954205a40017103282644c01c0324407030b41d0b450b001d085030020307400540c00d984200401c01144892600c19012400103081200020550f134002c00d441d40300061101c3c0c400c401c000344a005901c141c5501d4411003101620410680040840d03059440d54000c3c111071082c41581e081b491950b04c038030165403080d507041d541d40c0085e910f802c00c16141e68000b00c9002c07990107826400456900800c21101c0c0d21314928003004040c50410800141c0b603d601c0300740480c00c00842d2200b2070042070700010b1164102d650110580c3d42c0340d82c2c1c81940c080034030355600001d04081c0c120301804180350784201a50325280d0300716407044c1c0c0c9403247d50401c01202e11108131700020389814400501c48001040b910044c1c0c0b011810441081c183c02d2000a00b280c0c0040d1580b144003152203400e0005007000d10880000c0c020590003040281403640745d0260b0310340000c292509c0b1054140c501e40740800c0f03c0c0c05036140d082e80540002c0700c07408c008020300785541100100a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 26055536 1250 26054286 26054317
    0x605030c0f0607031b0624050102030415050903030d060b03010e0603061303050306030c0901180f0c0827030d060905070206160509030703050a06050403120203060f01031802040f02 79
    0x40c03080d140451290800040007069540f421895640a48001120381480740990351040450400b10f0b0483c050900b165500501300500c00340700c444080980580c68020504550043c402800607882c040c6542248a04a08040c4c1d2640da0900c006417071840784104029405084c84400135400e44120051416601055052042c590b06c2e142410782e41c20b801c03070b002120342c000cbe5480c0342c1c003090003030004641009002d400e49150000030300c003165400c1420b0384130784480c0b1955903240c40c1040d100d01c51030200340c500040c28003004640d00380c01814420090a005140b0800b590b80000e282d003d0700707001e02c0e06a4030100340c0703072907025002c0c00000074281c5120b400d0a450514001078455480840d0061180c150107640001000c5514821a01e580000202a40600c603802d008400700d60208071100180d4803810020805107801e1500a01ea001100103006ca90350052080c40b003a680c80c001070041d65402031800040600d42c2d182000b003605040100a500a441d0a503400395100c0c01d42c00401c2e2400f80821407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 26056786 1250 26055536 26055553
    0x70906080709090201090501031d0a0809030f01021206010509010207090e01020a0e062b0b03011107030e030607051c0212090a03030c05040311100302190c0605010b090d0b0619060201060503 83
    0x56400d40f445103500a001800c0b0040a2001d0342c060350020203c03011505e131802800d61558581460315030760701030039a420b41020401d00340301e00c1d04000f043e0380385580100960a000c22003402030654a4064401414003101241c0040c11f80d20801c0800d000300507446c8240140d40300308920038003c0d40a2032401d40040e412814100c0141000003c5a1a1503042d000050101492605a000005007004005411501d8203400c107110f580034003030061441081d00185d65070b10740c0361901030a10400a00c105019401200c104074400d9009402c1da4001c0c006c00e140308424640d4401c0050003481004610a1841c0f80e280a110040b1030018426108610035141001111154030080e14140201d1000401404449a44070340710b080c0040140f6100c100f6003000350a1070441704a07446100c00d420300c8100011100c8100000f0702080740141401403101c045254607009140c1d003c0380701c2800141e0058107000607840828040d40b10310525102c8496010318032000c25481d414020302030042c0f40b240e180f082c442c0004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 26058036 1250 26056786 26056799
    0xf0b070807110c04050402040209060c011509090201020a1401020d1805060a0509071202030a0605040305180d0f02060c0c13020c06010902090a0501120908040b09040c17060d0807050709060807 84
    0x1090718540d0316200041240543e00c204000152100034000c0742c2058003031101029a4030b1742c6c000303425040e0000d00080384040c052002417038040302c107500448142c1d080c0713201782d409030760041030058610380c2041a02204910001000303002e449680c1000a0b050301d0140c09104020a4094030b0b0446845101606da1980341c03c3c80306019141c00344c03405912504504010000c2c11030503140e000240d8400b07000c1d9103c54070162102c400b2503a080f41c00b600031480005150b6050702d0840d543c082907a0044503440321414494680a5003e001100028001e1100041c1709440c5a8100455001400020a02c02c1da082041d20004041d4000c0c0c04111070324401c02001150103111802512484000640ba00840525110046803c012000900b2643d1076075408404007141d101ca0082010305020342da196916044507080c08119000c500d129010085892401c0b60010700b0180051b40004048031900307078000050609541d184a160380040c040c2c46107480000d4000d501d90801421210800180c8020030356404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 26059286 1250 26058036 26058047
    0x5010f03150b0c0a0506010602060603070902071502030c09040501180b090103020d12050d02070c030c05010c0c03060c02010e0118031106070801091d01020a02150a060305030708030606070f0b070807 87
    0x610311010307108800041c4290030303114014211180401007120040c410707503107500d03041034001e030409801a085541008510f0604214034401400b0b1003004501e8080a07440c1d00300d070703007091034800169640c001020983d495030040c01e4802080c4000d00410942d40e4408412803400c00410145690600703050317500880c0e1030003016075412260083d10b001c015a2030703943c4007400c000140d20f04d1014000b0603c00c90071803090602c0a004d610784940314814480c1d0031800d03e48241410782d400141003040e03170380c61030740041c60030a8810101c0e98032480108099514403416400340c00d20a855078002e6190000c2c404070340c0b42c0020454000e60003921400000c000000450380c549030112400d1001c64107007401081480700d50b80c41105c40d200c0300f0407030504190408074580e09a90010841c000180d00041640c1c2655001d48280e030340101900404002d175a103141ea94a4a0307000d190f84c00380001c50b0200c00030300035072100d00c11500640ea2000000100da161481d05c844540c0303007500c1d004006207410b00080c100d5170140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 26060536 1250 26059286 26059301
    0x309020301140a0e03180411071208060312030621011107031809061203080402150d0203041101080601090b07060b06040e0702060f0f040f03020c041a01081e0402060d02040b031005010f03 82
    0x140c0d01b00c51002d0f001014030002d043c001e1035040080030104184404241000c007480a42c0e1440d40e40c950450030604109441c0480008200690103400c1051009a5a441031220164124280084451100044501e0041440049180081d8070001d050407c05920092541a00944000c0d0713100c1e1035210840c81c000c4440300d008281044c408407202c2e1012070301404145038454070092101c01030508961b0001800c3c1c000c00641000d448d004002d01041201400d514100b040302132070418200c0c508100000c00c201003e00c5003451285000030074500b4411281c10034440c24201038129903850303582b45580c4641d0b11003160704200500810001c50008024402c4072070140351905590310141e01d541d05c1d0b007000c08904080c101c080d03201d841002800f9845034004c03e061101565a04021040084009415a01c00603e444000011040d1000310710648201480d002601135811540b16001c03c0002c40017482150082d5120380b102000704908001502c1c9460706843c0281d8508410b01c00c04c000941c1500c092 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 26061786 1250 26060536 26060557
    0x9020310050111070f060305060906040b0102030d0e0709020301060906110a02060304080a021911030d0206100e0606070c090510090b18060f060c07080f0a05030414010309020301140a0e03 82
    0x2200303420050396118030b054402e964034407400c0d210501d42e144000c549981d000e521450209840303004009240c5410b402296100400362018050307100c0140000b51244581000000b0b079640c3da0005a1000204002810182081c00401c5550356125007000d00510a18030a20001410a41030101c0d030003c08507160380c0856000d801241140c45aa030b400410340c201c6411482148900584016410303030200078200c0240c040c00c43c2c441214032003005d060411001d80499019584030720f06001140f03240a422804440708049501207940316040000c1c0c003446100700150510304ca10101003a40038080d840903000c1c40380c91014a00e40e03643c60207018190b94400c08820383c8143c03118500c0314040915140c00e540094010656070003d2010303400208140c00100000e4201d42c081c404c01d0211101c00c21100e0f00c484141c00c020070001a1907070391035650344643c1c003c0e044200c5c4803170315521242e4000e420041029038020000d0010640081c2c1203001c8000480d0b0b081c607a58244a6003115400c1c0100440d01170035034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 26063036 1250 26061786 26061811
    0xb04050411070b1e0603031e03091c09090b010f0c030c050c0a0b04050f010201050c0403060b01020705040507020102130b04060909020912070e0103050f01020a08010e10150513090203 80
    0x60201000010019621000541c0c0000c01c100400540401c1c0c1a512031401000e40800041468800340d030041001404540298010440d0000c131200010b081d07412050041d103076035901d07039920f140e03241003070080e80381c0d1303201c0140b0103608016494110800c04140e070320320340c010003445001c100111004a420110706010910000800e07001c684600c4c2d500d140c8074011001c4031140902d92000c10541c01d0035501c000c0c1c1042012405001516052010f000000c400344020700c19420440d6108150b441148002404945c0d43c41441415074020f01020005000080041040746884100a4041e40c8400307251800403061603000b080c1e144800d0b041e607091300e035140d448103402c3e03040c4810b10000b90304c9035408590001c2c000a40c4906074104000b0350014041c0b40c0c958040652452030154606604050040070f5640144402019240e010103100d04407007481240904580310302004a1500303a1541101c100d40e020f65140d80c00141c1c211009004074110035101141051b595580f130001c0b400240e541c40d18148 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 26064286 1250 26063036 26063039
    0x4020d0206030a06170307050f01111204141c0e01020a0c090e01090f05030a09090e060c030a02090901140f010804110402090105040b0a0305010e090a0b071b02030604080301030215040b04 82
    0x1010300142d03030300900b00c05000469a4032122261880c0d0b8006201c46055400040e000c0c08202d0140b03c0507514001020080c1f1849180741a418014040c010121030144000d8001400744104292108041038026041e20400a0b225a100811603990f0000c000842d030a1900840ca81d4400180d049005802007140d83c025400d1032220005440504d0101005648949020340403c40d00b101660002c0e1041c07005641d140c42e1001c01414540541d800526000e16041e44580c0b224004551294029442c450310b513034a84e40c6104e820007c0c00ae02e00c2558124502e0b07800403d421051107503181d003050080740d0014402114000445100700203c0e0003d21905007112203600c0e6080c0f50300074140007541414094100760300d80e5010f03052604055003003030000340c0311b000400c2190550244260082d00d060040e240201e580d884011800c0c4c0094020b804014030b803010700400d4140400d4135a0455030003020380d80ea60501e4100080150400c1c00305900c5054580c50419603044040700325800c8805008a0701d040c00d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 26065536 1250 26064286 26064289
    0x30a0b040b07091a0d050c040807030303091505040b240102030403020904080702100201020301060807090501050a0f050c0a0f0506090d140c03041d0a0c050a17040f08040312080a0504020d02 83
    0x300e0014203003800344041001e0100340d10003080d004100d90b0f04c01c0100e182c0c40d00c3c01c070b4041d034050b00c034003901d0b460074804100410f0004080c0031444905898150401240f0b0141d80d14104500c0400790460b6400303d460401070004021003605114080c00c501c43c500a00720380e461041c4c43c0c0c03030391001c42d083d8090391003040201f005081594100e9805806880d10354240305030364002c94003500f404a9124010f035800401441000c0e000889980c005616281c041c02c030b50704100001e0580d10951030800240142070700c0070740d0040e01c81c40466941043c40d50544540c070742545019107139440c02420458242c011030002826005001034a15600400c030390740ca4510480305650311250ba4451207455000e0301040001140040d80340d00081c9405810383d401c00403030b02c3c243d242c81d000c64080d032031400104001003101c1001c15030300c072200da02c102d61700c6ca506400c91303140c1340340000c480440c00708010034580002c01c00205104855203c0d821403800c503103c001d0035a46561002d0102c8808460082d8483c820741302a0025 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 26066786 1250 26065536 26065553
    0x40f0e060a05060117060f03011b03050702030403240603170405011205060d0f03140703090e0f0705040504110705060705040f0905040201020a080d0213030c0614090f240301030803040204050105030a0b04 89
    0xc1079000e4000404820b900740400e00b0b4400042c07450726880780d2464100c1052f51725205881d8090013905c041c5003410f0455889410100000600d162255802e2021103071280c0c00d540404000d5a0241c14441094402c0103500600d8000f8800d0034003180041e81d00c0d0003440c04500819114a400401c200c04103e030707540e110701c10510b6031a026000c01146414140d0b117050401c0c014004a8020348403000d0f41450084905013070322005040004078800c0c0030500244581101c262402c0d15000c03a0b011401c140e1101c0d01800c035010301400a40701e4403c0a0501001c640c105005000755481c880c0080c9a06895907090000d0b1002510000c0c0141d10102086000c1350084010300401c0706140c402516080c11030071800b0011107d50002d8400520721401041802e4008106a0b0741c01350080c1c0182c100100c1e13400040302980400038070f5014a26203504000713080840c542c0981203100d00d1804580340d5840342443c40c0590421a0f0881c0140d1400700003241620b00094000d825560211828602c0d59903540d41824 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 26068036 1250 26066786 26066791
    0xe01060f080715050d0609060906171e0c0604031103011104080307060b0406091409010e150c03070207030c140f09013203010e0a020a0510050406050f09040f0e060a05060117 76
    0x4101050142d031105e20101d00a64008103640741d40840c0301420b0002c880708076400342d4055400210039066101c004900428000b0f211020744018101c21076250006d582000c50300c40400c0d80c002c00004000c0100070307820b83c280c020800140e00810000d2003507040c11420b4841d03030041e401c0b02e906c103000c40f034006106904805c5154101800214941340d030340700c89d80c095540d42031159040015007020849048002d108000c17044d241070004055801415026460910f07000e800c1c00c20b40000000010f141c0350003040701e04001c42d4002a00e13000a41e4506d04000042071410321948038004c0c000000341d4518003c0d4545041c4e403050348010701c2014008011040d2003a17507000b052521403094000708015607081c4902542110003602410600807503104000c5983ca41e80c010720310070f58900030707070344540380e80038080d00e040c0d4a803420507a81d21005840480d100c0d006003041d869006003040301c906900ca5040e003194003524603c90840c1c4580d2150f140b403606841048178100e000602c0740401ca09000c2c0404011034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 26069286 1250 26068036 26068079
    0x130b0102031e34020603130c0e04030f0306030305040b0a09030203011b030b0d03080f10051f030e070b0a030c09080d0e09010e15040203060f130e01060f0807 69
    0x249031440800d0456030340304000c2e4112200a001103103c0d107016151007010740d610380110968411409903283d21103c10394000354041d00030b107800300c002130f00340901c64100f440064101d0704950380282d0318614401e600314125011000200c00e0307529204228001c0c0160740580c1e0f45034070b800303090a00340505182c29400c0f1f8900301c41080b142c6100003001d42c40a01c40c042c1d501d254103502c1d600b00c030a5010050309441170740c0e6245010304045c400000110f5402007415170800043c094501c0e16494003401c95441030825040140d200060490750079400d00742901030f80f2105455182402107140d06160151100c0084c82390040104081200090603403003030b4080e410b13590850a01e8603100b0b4841302100d01c0c02110a4074a0302040e140364000049191840010340102031503820751f110317881d01d900c40d0040c1d280322000d440d01070740c3c021001c01d4180d40c0d020000560081c01402c2c09941d80d0f0350101010140c0403914010703215501c1c20801042082c6100310050956004100414075a49001c81d1101c1d01c010040c10710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 26070536 1250 26069286 26069293
    0x30606010e010e040609020a02010b121903110f010903031a030607050f12090307020406082113030818010f020c010207050607030306050a0b0901030b041e1a04020d050f0903030402130b0102 83
    0x3c20007651039101e900042e00e0000da0050301c0f10302c400310190840e84900201840b03410301c42402465100000350310004e0640460543c000680d82d8035055400c68070100300091140518180103c3c01201503128112a5000e0303030f014080908042a02d01065110b00502d40c0c06030031820000ba140f40c0103000a100c070544d11100c040c94101400c0f282000a0020380c3e1100c40f6410000d03080041d07251500441e006042c00ba0040d1500c0c600c0c400e041c1c41111480801d041c400400424400010489403604800468202c460b046d07072221070030440030f039844680c0c24603808500800302c401c45192000800122815041e0002e0809a023010200903040e0800d680440416880b0140031581d62074001819000b41459284180c5541c2c21900150649242020541c052464240600e03800581100c81812441291000003a00001c2600740451400820509500540001040003050b4960b03805140304071901305203800681c9584182e9a1a03103c1900e02030b60010701981000c4207803e242c3c2c00918034401c1401103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 26071786 1250 26070536 26070557
    0x201141303050601030203070e09070611030906040602010209120607051c1b050a2a1e02091003060608010207050d18030b010303111e03160201020115260606030606010e01 75
    0x114a03034503025400403a00c54100200400450904200401c00b03401b031148a480e285c90035040f01c03a0ba43d0b40910a00007000095010101c8590003802140c0320880c01501e0130b5951925a203000c3d01035407118003014080c1d010303481e04100200d40440c125000300017a58441d07180c40d01d45130b6800d800b840000411113500b5a1210408003503040c407503c2d0328070203150f80c44480c2c4801140c5c0029240c54031180300f0030340c0074801d480e101c182624826807501c5815841905840b000b040901c88500041013a00001d411100c40d20030b0289404000c140c900441c0e01c684010700501c2d0301e40b0006804d1703000f042c600901680c042c1900b41440c1f801a0540c1590400c1f00315222004e40e603903100c00499078070a0b031055010448d41052008400424410310780e64598991800c80340090180640e40e0300c1c800c504401d185080c0e116548003c682c801e401c070300c55540c5584545903aa40c0c0f00c400c17207291020749007281d007030b60b50f03804601d1814100045045403268000502030002d40c1d4400b00155174070f03002801030a040250301101d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 26073036 1250 26071786 26071807
    0x60e0106030302070501080c0301050d03050c011401090e070902070b0609131e06050f10061805040f0e0c030a0b01030807020409080304050109060605010e0a090b010c0807050d080a09080304020114 86
    0x303010080d802540280350444c680030015005400240c4901002d01c4200014045900c44861400b0304903071601d4400d684a190030f64040c0100901d444200743c3e100e05000008900006030004030016101c0010369884a9036455260102c3c40b44010040100d2203910000e0000c1c0b901c003035141c3d4010490140c400401401c0e80d5154201201560a200d191002e00004418040c1c039128a561180801c641c0d01c1c01800c01c2001c82c1c0d024249845030100304111440d502ca80032201803500300003050b021b4070501c92580c4900100001d48000d0300c814503a032240d08806840382c83c0000d10200d2450300807688e03070000e90071500d0303810f09a43f00d0301060740c00646074259100020401c0006501c40d41c0181e000081940061030714005a1700341e035006904204c0d141c1e030b603200d045d520b1903810342c00c0b2801020001010340e980c2d0010703140298060009005400041204400d118000c1a035000365807403030341c0d01c10312581c402100ca001c40d1010800641815400e1000500650041045129072190a84650f007031550616 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 26074286 1250 26073036 26073041
    0xa1704030c02030609160f0e040609020102010e01060b03040b0901110d09020102030918090c01030e0d12060302060a110106050108100306020a090302090a0b0a080d08130c1a03090d0309051009060e01 87
    0x3501c00e0015809000381603851300400c01b0b40350151030310642c90240340b458440300801d24080544050145959035102e141168001d5126805a000d40ca009212603551000c90180c9234000319070954114800340001155500c06200e118599903115064909003000c0005610051508400480c1507110403c104140d42d52020303010b940b41d5100d4a9030890030701e864000942420310740d139080d9050505052095618040c0440c6444139503134245003081400c0b101c109808007030b002981c80170390810800109040446d03400580c1041c0ca9007a80020701200f0765401c011a03030281c04594011070104180c80a01c0040c03030b10340007001c0070314403440c1035020151240c0000e0171083c010380f108040ca50740c40540185605101084000421800003d454420403801000d031503044c001300648030640b000245001008180380d5584090410904c80c8041c0b220f030f0902d2106145d009940c2c500712172041c0d00000110074443d0255104095000c4040c0030341d0010105100c1c040d141c090011103480c0d0325a802c8180102c803d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 26075536 1250 26074286 26074291
    0x41112180a0b0f010501020c09040b0a020705070504050103081306081522110d0e0c1503060111010203040302011a030a030c120917010203040c050a0f05100c080315030c0102030a1704030c020306 85
    0x3080f81960b5151000185c0340c2040d6002c103500603d012010000480c00e16801c00b940000c0c0b901026a4602980c54000d00b004810f802041d0300500e03250000c802e1014503805003200c441000a4040115200c550a5900103030464806c2c608840b01d9100030106e040041134802c020603501603140034a66203460040946004010307011a144010483c10200c481e41d0241090302c02d070400c06000348080030400b080c0901140c640d029281341c0004007050701e0fa4880c900e13540d110368440e8001c6440e4105480c0080c040e00c03607109116250020b0740c00d200d0103841c02095032441d80351701d0b0719410032500303e070340c0c0e14074254908401440a02030341350000500100d070301541c42e01411100000503900d10b01407900c0ba0001000b80c0140d801411403460034044040c0480f680c50a54004070380c80d91250802da4000c50700c80031400002050f24101005119000581c040c480f0b68210088003501c0311010b0380c400490380c03405041007075400141101e4010190040e00310b840d50300a4000c1c6040c0780c5c14035054001c01c1c5001c009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 26076786 1250 26075536 26075551
    0x501081b09150409050f06010831031803060905011104180c0e120a0b13080708090303070f050a060b010816081906080d080c09090f0a14070c02041112180a0b 69
    0x140001c0011f2581d1140c00d03140c2c04107a4190401030a454402c40802803001c07850040004804540d2480a01d40112000f89140c0841088011055143e1400c6000740006c03040480c0d0960130801c1026203801010142d03419101a494850105248450960007a003201c040e810240104810b1074030464484c04c90071000c0322440c1c801007a0744011841d145107a000f0050401182414230082100020300c4a01140ea466400c0441c0a49420700d20002a05501c04c0c0140100f8010301e0740720803020004041058255940258000c111010002005440c1c10074211a0901001e001d81d4041f02064050300c000c580105101c003104205280041860342142e0700e58004000c076501c0b030a000c1c1c0e0702640c40b402c0241d2106004456500741074610300420b00900d0040d20304c08101156030009140b04100b503104904018a02d204903100341403890703000c4c02542a440081e4000c508105003520039504000c100d1f105079945004c1c008850341c485011032800c040d032015112007801107403000c6d4046035100840303d019144 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 26078036 1250 26076786 26076811
    0x9050d0c0506090606030309091b1912060e0a09030e060f040e01080307032003070203010c0e040605060705120a020f03070606171c0f11060a060501081b0915040905 72
    0x1681c10510324105004103640ca00d136200d4001c0065541303005c0251050008190742e42c41031030f00c07490040c4ea01c1903541e141000c60482c0100b140b513106000c11035280d440303a0081c0c8440e00c01c12020a50101a90403038000c1c1c044404840002c200541c3d43c2e80c0c81005014000d143c041692401200002c4241d407001c240d80744200b0b00490180084020007a03c10700401d1600c004520740303139503907030f0240068490a401c00d04005090300c1c81b90b200b80c018811035664640c0100200002d2003c17410240c610a01c8500d01c5010f01d1a02c10049491b04298049940180d0410f00178522050b412103501b031594080764502045000743e070802c00f140741d030400192031074601ca0000851100d0070050101e04414116502442c15270040700c202c0001641403003d2103405405180205240300e54520560748a01c03040d000000c1c034460b85040201c0303c90a58032101c15200300740e903007212030380320340384c0043c0c8240c0100849241c101040115441d6440c040c091b8901145000c0205414280c2e104c0c8204201c440407500c4c500c1503207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 26079142 1106 26078036 26078057
    0x30a0804150e0d020109050c0f060414010201021b0609100212040b0417040308030a0e0304030812040c050a080606030d03020a170406140702030a12050105180a09050d 73
    0x45944102d9180700d8510f50300900071300303044601f030f543d41c01614240000c9242c000c04001e201807009199604090421807602c121540001c84c1606540d403c100035030003282da5034854648030740014054169494402d9460b41402680100042000e00c10410440c50f100342c81a03464200390842861101a0b0366460300159400c1c3c034031011811010701290000c100b1a42100440c0700b62240001800f268010184281c0e80380030700e000085c0850014030180d081f2510183e502c6a10034003a011107281d9070358500204c0da20341e00d41e4000c801d00750001c2003041342d61300701001440e00010780352600314030f032800c405070050146041c86d49400d0500b0040d0046030038002d90707800c40030500110341e03030342480c2d424541400781d600d038841c41c24800802c0c0104480401542940304640c101d54014100300041c84145c86000300b00c8070002c045000f401da4907405131011803001c00c80034181c1502912040700c00b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 25899286 26079142 := by
  have h0 := BRFrame.cov_init 25899286
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25899286 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 25899286 ≤ n) (h2 : n < 26079142) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
