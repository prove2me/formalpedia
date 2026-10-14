-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0848
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:08:47.974363+00:00
-- url     : https://prove2.me/submissions/77d1ae8d-d269-44e7-85c1-c8ed70b77fca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 152338129 ≤ n < 152517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 152339379 1250 152338129 152338157
    0xb090a03080609090102070c0b09090f0f0a0c12020a08011e0501020c12070f060306080106060903031710050d0b0a05071803110609060703030507020c060a0f080c0f071203050f0403 79
    0x710f1405800200959028080b07900030a1412081c4001420100d084036a0348142c0070602a000800520000000c0007034800c104041c1001e0192075440111800c0014002c07084940c1a02c4201440f030a5101c0c00340f022032003c03140360f00b0444150503521150704072a001d9002c8400108102c1c0c00b13004490041e0003055090f51141404d65080600c001e030708007035902c0300c1d840f6607000c54040d41980c856400a5200c0b042000041002e1044c9030240090780340c20040c82d030039500c015100c44040c0141040c0c0304a1040003c143d0443c81a244000e004020f0100c032107a009401c20203140c46041d00c031040c180c0d18110220388911701418154504c1002c0d03601c0050041c5c515204d0b41e161145013101c1c1c0d504880104503d0003540e65401c014038049119880004140c202a580289840840403a060040b203040040c8400542c01c684c03510f004c00d07a9468154826546c0d081e00c0b5007103014100c6c40859840b00070138001d04000b03500300c80307c0c1042401d6500f0401c035914015200e11207881690090041044440c000030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 152340629 1250 152339379 152339389
    0x1090b0f090603130206070f03120902010504150201111605010623060d0905060a02180a030206040b2a060601020d08010f050f030f0f07180207080a030915180b090a030806 75
    0x1a01c1380d007198080c0c40401c41e03500070981d43c3c1d0001d10220703210340d002c0b1800d42c10035412138159018a04940810006022954000390032172045014402011035004e01e007980c224030075000301c1022040b200c40707180c403203030901c401c079a168080d505e080702c00e075003081750100d1280a0381502c2e116808042c8032000c2403012103024480140e11072242030300b609454102d0304d800b0690402c2030b0340c0140410540180e49420a440b8070601001080b501440780c00e940c1001c00150380d80718203a901f51016014006d0350741c03a41c8450290300001040c1d10400c5c280d55010a01c00301200480c41c544281001c0e02503803035413144004100c0b08036009000b0302c004140000d4081c041800c0011810010341005001c4a8112045454051511072110f11000e80c0c3d6000410502c0804070300301d4018240b00c0410810f41c07e01105a1700d07056113004000700c2004140d80c5030004000e0040f01c0100803003036021090100301111400e520021140141d03142918681d40305004074154031700004140388843e8041d0f84008194444200300a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 152341879 1250 152340629 152340631
    0x30a0506101a0a0f17040803010315020c121312080a090605040602070b07020d080c060a06061b0b0c16060b0a050a1805100f060e0f0910150201060f120201090b0f090603 74
    0x302017004c1100f95154401c0c41100050040d0301412180362690300d940b40c112104524609a681c9250041c8080a10108005442504964a03082c0c4586030342440c42c2c8507468407219440760408060740c2c00e0700d00522103040f00801c0c0410840d5100035513035480318015581c0b88964801e060060740102d100f000081c0c0c402e005405d5203403006114010000d416110a10160000d4004940c5034000d6801c1c00000d05141c80f50000600391410070078141c0e40d00d030780c101c043c02307652010240020350420005078644009070308803401030604118030202520b260814500a115021449002c1c1d007149402242070f19100d00301004a95581c18441c424500b0016000050325000c1c040007202c01c0070480104010318500e180c013002e00055a0b803408561401e1040000ca05000e030000350042036500b0a0080106940e55048103070341c1c4081500400c00f02604003240101f0f80d03540030340c0941050100c08030720f5a00600010b40710f103000742d0301c0e44092034440c0c0c2d14483c075100301d680c510040182000800c80d1410700c003000e5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 152343129 1250 152341879 152341907
    0x30602070812090c0901060905010c08210403020f0601051915090803180901090b0a061b050a031e080f06011b050607020d181a070f02030a0506101a0a 66
    0x2241090500c0400c0082c8280907242e014140e000f16402d545181800f00900380180007a2800302203c1c2d18250010303081d480c04003405090242d00044500c01501c1c280c190300d903d101e68410308503140c5000e0800a40b10404d46040c0050360203088000900e80ca031191100800181c20003034060031a180145500040c4010030041c000c2c070107000000113001500b8405408640c000d03d0329581c9400c0400c0802086000580000441c0381c58101140400d841d42424802507e89508210030040d05000010700d02e0103d001c002001480b81c1801801015445166025404001c0505000f020307100c0b030742a200c0b01c10844a0400d200801000150190f2040d0414410481445e041580c28041a01d0795810b18800312074440150744400f82e1031001c140e0141071003102020b00e61800c0c4686040c0300001184a40c107040d2090000e101081c042c050000c0c0c2400040d416030b00804032034000d10549482a1210402c5840c0621498081c038002882d0706450409091804188200c078508480c407001035030194007060304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 152344379 1250 152343129 152343143
    0x14010219030e010902030601090e010f0e07060e01210209040c0e010e09150402040b0a14040f030809120d120b1008040f0627020f06040b0304020108040521091003110403060207 77
    0x131100562000e21540340030b854018400308480d42120400b600751090114902461403915081c154200000300c1d0380010f0f18800c0c5400c055148001d00120ba03940411410821020034401010004400303e900800c5030500076202401201e0700070501303450807480c01c82268042200c042030540286000b030451075200003075101c04043c51360700e9004a022038000d9040f0100200380061804211604541c401c480d40405d1850646068101507050004800d10700c4000c01000001c1658101030791030140820400880b04120f0300c28030380720007005000540140350b16080b50720388002d00d0f07124245070000b49507141803074640c01c10649882c1c0d05ca8100004800c010340e5115640d40805184135042807668072441d91aa028405042c0075004100e0005035800b4031610403941000100020001a81a80d611a1302401d01881d00d5545003041418111040c240950440354500170090390788248c2c019042c1064240d42c011801042114207804a070456908000302d003000744410000141d040e0001d1540c0351040d00b0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 152345629 1250 152344379 152344391
    0x3090206070f03091707032307150210020c0615010813110d1e032618120406020d09050603040209061011150901050a05061e01030204050a0306060314010219030e01 72
    0x2006101d80c00c00c540720344907608408010824450024000c00c2d0408040d08c4c409000380000e10620ba4811641c442c07058228010100e100380390340244121904092412015507460041500c01500c07a0300840f01d00040003500b5100e0ba855502c039030071480c891200c0c08000420000c1e02e45a09050801d6007101c190300000301daa080000a0203419a42401c280a640e1603d80d459149805041c54040b56034508401c44a02c0c21011a005060780e5641c00c1a050a050110303031100662841c24a0030355004103064a500241c0040c03e50b50015810312207240c2659802040c07600c940030000c65103c141c402075402902c4c1408246186030040708040c120543d42401c01c042d1140d40c941c6818105070840040d10a5400010801e0141003805074581c80321000d40c041095103003d1000410303048100420500b0f021018401d80308503402541100c028001c020043c2049503640e182803005441c141c0411a011600048034039107546050080d281c0800303903e1068500c41d00d03803000031001000201c942802c65134840d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 152346879 1250 152345629 152345639
    0x70c0f09020304051507020a14100606020303090d05040305100203100905010f03031e020615060403080f03041a070203070b0c120405010b120f06060910080f0a03090603090206070f0309 81
    0xa100140003820000d41c4914040c00c00e02d061501c11034003801440d802d0010032400b1a0301140c18200b090340030101015107400d04214614201044080300380da030786061800301b0b00c181c0020196214200741d800316200307a1035034001100c2600451100900c903078030400c01075140c19201c0d00655032085020071000815a42d9106c401f0560b0030070f80c0f0402d002e4084131414804c6c10341c846240c04560b40701c0482007c40c103004107002541d03030100502e0002601100d03a01c101c640d41e140c0f02102d008540019103651140d5910408801550081c2c070f01b20343c16001540e13051032000c4440e10007442a41c03d82c000d507060266689903a180000000e00c20040c502040105044c0c2062600030307507000d5800b030000003e1610211080c0543c0900c0c20000c00d005a110740c2d940e03501e8040006810b64000701c1562945d4036900d6580346260740f030886400400a50040840303c03544c01e14006040514540695618005507980f88015811103006100207508000c1c1040303d4000b056120340c044143e10b100c0e02d442240e103981c035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 152348129 1250 152346879 152346899
    0x1403040e0a0e0c220b0604050d030e0103290f01140d0504060605060403080909010b030907060c05150c0d110a140c0c06030a0b03060c030105090f07020c1306081903021002070c 77
    0x991000044c40b4520307001d070000c6000c0d5101c1d808240800740c400e01d00e01350400d00012514000c14400038200801c18076461201d91003908030101c1600c4488444500395400030b034026514440300d84581c043c200d031940304400e0358842ca40b5044440030b1000d8051800c09600700000103400000e0081c4c4003d500c90a00107000c0d26210000c0008600510090b6201c4c981601002070212060b840320004540c00e1007031181c0d506000c2034000481d60039081041c4c2d5040985003144c20001d50303000f1440400307114010824007800d001e00800000100400801c66803a01c090005183c0c011043c2800024402e45c560148c61200d01d002000020404401c8030000e011242c00180158400c6481250f82c1d501c64407070b03060074282040826040980b84070080d05540c140b2002c03c890075002000b07550014164000308150a00900c402c4070602ca0148c80070a0f4171350401d01c2a4003800f200d01c43c0900318402c2ca41751035207402012142083c41c81d810341c0941040301c0e2034500c00e0080d41162000740c40200490b0000a03001040d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 152349379 1250 152348129 152348149
    0x1514040e0703050a0b011b020d050706050405120d09210501050c0d060e0c0306010302070215070b040b09060708070f0e030304090606090b030f01090c0311161403040e0a0e0c 76
    0x400c61008152904840050680f0380190688013541c0c2068500340d15aa0420810301c1203581c214010b8101442c1800021318590603000042d101c0e0080c0031011410756031000050003524016a1480054008070301190703070b1840c08000040c0019000c42040c005020b5408454401d940e00709481c1c1c050031601d03110242100c00a490b92150300c5000945011510b407a80250001020551200e461900d052410310000784001803807a810103030300040d58411590703049511101e015055040603164940b5240842007030030103403401d460106032240025403401000810701e1003400c8590340e4100d1625080000d4074030611040d004004d0041c050481162918204003420040039401804607566280c004082c2a52401c1e41011100761010010800c1c20a02010b0960444071032240003d0314211900b003c50041580d440715215100c4000313402c00e114410303d260000e00c0350180403681c078148614080c00ba42d0744500c1c07141ca5640504800055a100042c1e845092072280000940c0d0b01010680300080c60051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 152350629 1250 152349379 152349389
    0x20a020c030705190e0c070b0a060303030f0203060d0308040203211308070f06050f0d060627081504110d0b2401090b03040302100518060a0213151404 66
    0x200c04802100c45160801540c0c005242c10742c3d00a501a031042c41c52090030601d80034595400700310402060700e18411008683d06160084100f0f28942031000910002d046a48070540000f41400784035050750340144200c90058000034583d801c080c415641c143c3d6403150041090360306010300b070400a070000048442802503401c02403040c0d41e407400e452182810341d6031038100b40b8055104d110144461141228044140d483d1410100d4480e100c00c40e07890b290380704464800041506000000456507041000007020040040c003140c0301200b101c602c0d1941e5035003407240e07040d10741c4800401c0712000d14441441c1c0d001806407040f40808400b400225401c401d000c0b83c100d0307079030300c000c000c01030354500c084100f00b010050314690034030440c503030360000307105041c00d000d545a0550f000000c43c080500800c020b86c0380c2c4810072414481340c901000705507075140c1a060010800d00410b4000b814600c524821941850b1000034600000c80c10702004075a011100300e00041031080c04020012400c401c0000341c00200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 152351879 1250 152350629 152350633
    0xd060c020a0212031204020d15020f090414061311090604151d0d060e011410140d080d02031e0f04030912020102060a0b0105090a08030a2619020d020a02 67
    0xc0700c0c0384107204800d10703441c4850145030420300031401d0701c00c2c0c3d00071131603006901160800c26400c00b03420500e00d10200d6025404103c1d00c00542d040f51040d209020302000a003c40b401c102c020030000c3c1e0080a01003c9070500d40c4518414052004065030303030f00811840b40d299134014200030b001408184654480d030401d0304000b0341c003901d0b00480741e03000e4250310351820b10350310040103070140b40042981e07460203900040c81d01c0e4030740d01c4510b0703103100c2507000065603889035040102e541803245100703c0b4582d66000d498034005440303400b103d1a0030101c460320300044d840007845151280402c0d8140007074002400c1e0300b51082d0011400310554880740c02080c0102c1141420340c0c0c0310302300342c40c01405081e100d5001040002c1030707000f0040540c0e00400c1095101018190200f43c980512004880d944110341c1210f60284016502140c40d2070300001420000141c0d450b002c05411003101400740381c40e881d40e0344800c0d050310500020300c030100801d58140c0d100d14802e809420700440c40c107800143d80010041800507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 152353129 1250 152351879 152351893
    0x50c0403080d06092403081624050c0c030d0b0105090307060305011809030f081b04080703060c0c120f20030901030c0e0604090b030a050d021605030c0f0409020d060c02 74
    0x30059841001e4143c401c0300c0300e05003450001c115601174035555200140541c00c0129500030a482c0c6103602601c02075016150015241e034a481d9074240030b154a880410240c50140014122400c00080f24180c0c100310b4021420072000300820005021310100990412000740841681c03520100000300c084d10107030310081455810004e464842c2d102c1c2d941c0042400c0d04146400300802d1700841024a001c102d03280100302030b90745041c55283c00c6210524050f8140c000a00041c0c85000032609101760382c401d007014411115154000c40e900441d440024020414503c1d6008075140120b81d8018850360605002c0302500100310707a180c3c5800c460220003001e070400500c111166034980300380c082000b140e05009082c07442c404017152403400345009498607070f030f07446140074155034041100280041d80403046800045012000a4a840186d40c014800709500c241c0410689400710707110000c0c050190a01d00c00752100c0e02088040c2c010858140c3e0841240f0b03c000e00412400d0103020b0141d0301d140c00800304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 152354379 1250 152353129 152353139
    0x409051618020301030201090e09010e030a0f08010e09070b18042909010b030c0c071a07031d100807050c2505120703060c20010b090c07110103050c0403080d06 70
    0x8100d008030900710441c41000140b0050f80c2280c40042941d551820301505a95005807440c01020760328202d150500c008190b140d4010350103025009030482654032a1080d0740d0301da00344161180240d070445032a420051047c05095003603409132025200058803103003c00b1745a8003081c110303500e5032001030700c0e21031008020b200104100c8181c80012825a01d1171400d600d88a8103810500002d85810404c400010710008a41e00130003080000e03200706090076001d0a074050360245982e12840048001c9031441000c090620151900c0851166000e469109040391924003107500c224010585400e0040030b04c1440060103041042860711f80300c0c1591b44c3c0301d4005e00d00c04050b102065a201e20301c200c800e0b00c4840d00606c00898500c040781c0e0701000100300c62440000a80d0958001240460046c3c0040d110344e03000d18054100c410040d0059485011940b10901c000800b03101c1c030480035050078101003850071254800c0d40889c1e4080128242c1c0c07800e1649070740d83c2c01c489074000ca511012154441c401801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 152355629 1250 152354379 152354399
    0x312010803191d011407080d020d0b030a05061306110d0e06060402160f050109020909010603030e1f080c0412030302091507051902010e1005030a0e030a020a1104090516 74
    0x24002c418201442d070700c040856034249664003200340d10304220314102c00d841e15186000903074010640c030465554484843c00e200e44000c0d0409135506900ca801c04102996a081c04103e01c0301c00d80c0c1140103800c496840117400038000c041410100c500996901c80c00c98200d00400285c2a845071500002c0f0300a400b030148140380c254003800d00f0344520f01c10415180b40c1c80c19110700890b80c0e603229110390b0765101a802c040c2d004140084010b50070408200400100c4078041d4032903000d6a00c66140e49807512070a1703050000b0b40c1000302c804610f21280c8110400a50300540c602d0358080d5030f41620b289407584038211400001c4000c0c1e03080b40825004140412980f03800c205008040070050407050504105489441e991f8514104c03c1204409010500065901c500e824540019001d4078580c80500c41400040641d8412100441d140707240135000100c848000c400c03a21090903a500818080344551504c1d03010820b41026281c4c8150742d502c19030b001440910289001c00e40c0c1480c05509103184c0072060f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 152356879 1250 152355629 152355667
    0x6020f060a0b0a06030f060503070308190c030504030f0609060e03070302010e030309150c09030a0807031215051005071a07090e01060503070807030e060f010f0807030206030106050702030312010803 87
    0x61292400c014001c02a510383d28010002c035041d40c6170103e4000f08071000d010040c580c54000700d0b05802114030101c1809102001090084000c0300d0f4010303c60350030641259680c0e1007100090025004000402c0851400709200100340c1c010100068014802ea4072036007143ea00751620712030b40e000400d0f00f41c01e03d0f8086c41803124500165006e9032840c80c0041d03220341c903028111580344103a9000008900c0c0d0a01c00403d071103204801038201c1e01c0c4030101d414041415085003004032300080e003881d02c0c1069542d40e401103100f0140804a14030742a41480d040051a102c000140d41c200300023801404046814000307201d6078809981d0042045080c82c9038010704420303054211404406a91004100c625400012658000c0c0b0300e00e0184000d45039820300328041e01503850040e00f18803a050602c10201202030801d41240d07807803c442d002c040c0c0d07555121912807c0d6403202079800756003440108a0b0324000c400a045107032000782607914080491419040c0070303400303802060340c60384042080980488a00110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 152358129 1250 152356879 152356891
    0x316080c010203071101080714040807090605031902240f0408060f1303030b0d0b04120f0f020705060304020a0308040b0a080c04050d030e060c0102041e05041e0e0a020a06020f06 78
    0xb640c40c00b40c040c1c55400b01044d85c0b1401604104212000030542c0380308100c450100e444089066030b86030b544074000e5a454049006074a0f4291401c0c1e00021585400100e503041c201c110b080300804101142c00700701d440402110420212103c41502c4245910008010504c4095602c0b40750307216130a0030005803400e20000e1250a40f2404601845900d03031455950342c1c03000d90b00d49070204114100380c0116650f4110550010700c021548024041000703c084400f001e02c043e45d030740da030070762201e03510088880781d0b00c40c000383d405a04060020f01940c1817200045038031170700280520b5440e907174940d92503207d81e000c0c0d80509c6618002040c5c0581d00380c0d011018541210102d00c00506040c203000002d400300c2011003008041c00000c400820035510350001b51401556260b00864681c0e03580e40240c0303403034040101c031900e1120800f540428070703103490320814944d1549010014440b0355400c3c0e1a600414a0b41e21140c07031442880c0d441070042c0d03910014034003c1d10082d03020344400138020003100d190203406040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 152359379 1250 152358129 152358133
    0x60f02030103080403060c0507080307080f091212060321070516140f0117011508090727090c0603090b06030c0f04110405030a0308010303081005030a02010302180316080c0102 77
    0x10008184220141c2d400d59420290002c1d47c200205800e039054400d185004000801c040100808243c00800040c881d1440700501c00d43c1e550b0304c11a0584400842c2d00381141054180180c1d0001c0c0701d15a10580d00050140c1110303950300c0e03400c4000000000d40c030610722118100007046420082c1c00e102d00ca48120000c82040e0310542004c5a032220004038030041401a0100000d11001380e1281c14110040400d00c03101c00c03442d586901081138081d16000030000800c1c41100030500c03000300007940c801202d4444141e80720481300b1441c410815030000c600701254689456510340482c5603480f000e0003c0c01c00791000200c5521501e021801d419000b410280f003500510000f608075201d1541c460500c203412100001c1210512001001c94012030300300d41c0d014440c80044070101608071824a040e2400394481848540ea41900c100c0c1d003200c0c83c092660190041100d040055029802030100141f01400c0c8141740b03500038004c00e143c00c441080c4a40d156003a0041085094070034404803428080a00c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 152360629 1250 152359379 152359381
    0x20307090e090c041109190801061a0304020d081216080702030c330426031e130b070f09060302040803041e031e050d030b0306270a0c03060f0203 64
    0x75191034201d81402ca42c01217840360b0202c03201d8030582040b90031030800102000e0a5494a000c001c2c1680c455000d00c0926619280c0c0105040c1c841050080134031506001c0c5918594559080c0107291450032412915801c3c1888200c2440300d00010051103544420b0080e09035120010004140c40009403450041d90420046603850800c0400c0c4007012000b0000f030900300710001ca0702c00040040c494200c85811610704140b0082000c01560041008807801c01422061100c0ea419041c500c42940c1c07580b041d903140c00410164074801c01d00c441d400500c01d00181003414850303d8084107a00111100c0000403818041000341580155105014100d649011410f150415440c80d07900d21a0740608070466080e0201140b044400c008000040d50f40700409142640704160050340200a5000840b000c1c00352040c0c10700254460b110b40d05480700c0050090055807030b40c20b040310351294504012460306440d0391403c1c21100c820440c2c03900d8944280758081c0c405e495401c1140c100c4a09400c40c0200d140108 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 152361879 1250 152360629 152360641
    0x303050a0c0e18150418020f221107060204081509011e050406110705070f0e1005040506031c0509090a0209010801030821040807021201090b1602150a020307090e 71
    0x501c016403000f542ca41c0d08400307030b1641460811002d8401d81d540398003030700744103009281760404140008010b100756051000f03148100108003103003202c19040011100952707000c0c03260004640164180420610850340f40041585032141a03a005800030940341c1d010503507550340e03503064000c1c465020b0201802082404d038120080c25507407804045061801c1e440314046024000180d02030003100e24440ca10a5581c07040b8980b00d500e80180b803140c615030348004180000c4881a803000c842c40f54052203085051b150031300b0104001050003800d1241c01d441a0989801d40d00f0b02c6480c2c00140c4000c40e01c0f003588550100f01004110080244994a000d005100c84c151750f90302b0120207030549920401d125111121400c0d0718002880440c41040d40f540d502082c0414404943c00a1469600940c1c81814501a00c102c4500360303901000001c2000c1410000100c407a4502c11502121100da8416500002403501440c0902141510340d1100caa0740042030003c03a6400c071601e07000400d040060300100785455 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 152363129 1250 152361879 152361889
    0x20f060c0901110f07080705010807030605010c02010309030302090406271503030806180f0412110a150e01020403140c240a090b190206011215020d0b0303070303050a0c0e 75
    0x400c298a05016003040f2000c002c0318184a00c404d015581c2084400d85640c0740d804659440d0b0510840d4045a4000d0100385d0b03da100703000d88820764106844000b102c180b164011402092000420780c1096420b2100900c10741d00c50107484002c12652207989610404015056000d80030380015801561400d40d2880d001d9492991640403240c05003081c0030b0720354855000c6100e403045408020f030590343e104c04200f07208206908642c015405041d070001c1000e28801e042d200c0d02a0026001070310741c811400d00c00060741c07449000c1001d00ba10200483c2c200090042c440c01d9030007a40048820804d107203d980c4215004015551000b04103e400b54003480c04107030100c003070030180070b1030000b41e0000181c9420103134000d0705420000c2c40406541c654030414845030700c044030340028040005025610002412580e8207000844544e0094090006001000c0c1c041d030003944480c001500b115161010302035266018805018414000d84011500c0c0c0b4001d50008202ca441710f07111010f0040c50400d84c1001d80b61 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 152364379 1250 152363129 152363137
    0x6010302120312040507080706030903020613050717010b280911090901060206100609050307060507020d0b1906060f050d1a030f010c0e0306010311011b02091501020f060c 75
    0x103403090000c001001100310b09511842041d041980e0118044c001040303400501303101152030110a44900c2070303d07001d08409840d04404040c006901c19408104440041035403001414816030071100c44641d520701c0203556020701c10074108070340d545001040e15410b01c1d004440d03400c0e00d040000000301001a58080307603480c89008100741981e540340e50000c100007550480f00c60010041102c1c07020340c0d40c1c00c4000c0d5070b200202c90b01c10065840c1c202c0010154040c0c240d080a03504020064021281840802c581a80103000c09070b81c442c9012a0b98000300786004c0102e8090407a0300c44060050b514440c4500642c0d1507540108204405800d2000045600c031040c0e038401c0420000100380c0c5001891100c202c14410348032190305000700c0c001c08945a105510084112005454003001042d0b010201030700c0c0c00091001400040c503014400806600c074101244490780480c1014000007480d402048040760102d07050315144403900c61440d01584c04002c02039000c505c0d280140014a4110901781c81402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 152365629 1250 152364379 152364383
    0xb040506040b0307030f06150b07120e0330040b0301170c0102070b07080c0106181401290409020706140c07150b060d110301090e0a05071802041502070609090e060103 73
    0x82d842d6200d820081300781c00803230301c000121a40b600010340b00c243c01c04240d80100d108446421800b0707843c61055000e500c0360003844000801030041800000041c11240003506406210301142c0e4480b1811003e9890290000c2c00e061a1040d48a40c103100050700001c11450515000364400300226107240e03800603c0206030745210390410384030b00e03c6203010364203030148040080c103a5090180104110500d40300301c000f040ca100a050100c0c50803071a23060f01c88402030184903c0c020100c401900c0c0e0352402106105100c4107070150030300d0150745d111003004903005880100e410344d03200c41521502d01d4810485607040031055086624151044d0385020407080d180d8100500704c0d44591032005165184d10903220015142c103024029001d08400c800e1080e4030034001c5052640c41c149401c1d034400800508622202d50003002000c003203081011501c1c0314140d0780c030740c0420590200000315140e09a064407020800c055001000440c0c18003c0103001c038102d81d005070714107610301b60a1003401c2d5000240541102d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 152366879 1250 152365629 152365643
    0x2031504240f050411130204030f0b040f0b040c0513180311030405100804050d02010e370803100512030f0706020906040f08010605030c0607060c210b040506040b030703 74
    0x340c2421074490140403100d207000b9a542c0740c0801c0000340714001d520804040310032168581580403003120501240600d00014241d000700000d000009400a888283c200b4000d00c4801000d16056903489080c03402203030701b140c103900a0002004141415805100c059600d0007041c89000032284020007a080a400054200100c40c812003030040c4082c030441e4003610000d0035a01100c13840e40c001401401c400d45d030840b005e10540380f030114200c7c41031154412000540d000317420140c100001c3c41d0708404840400c1c880c03407012141c86440e000c800d18002111503204010881e10392030030000008074040154000c60040c0203070b0001039200340c80401102c1498036019001510b0f9400d03170800c48000d0182e2005141c1013003001501241d004900c281400032100807030001d0003820744840505440b24051501280c001c0fa09110040c00180340d070300401c03000509132406591100e40a502407a00642925400c00e03010759071503400040b802c16028080d0301c40e0313094405011410510f0003190382e4482500c00a8100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 152368129 1250 152366879 152366933
    0x10c02070501170a1506020a021e0a2c0f0603160305120c070b04060302040806070513051002030c16062006010e10080a05030d050604051003060b120f0a02031504 71
    0x60351265200c0f43c0000c0c0e403148085c40a640b0b8806c007964558880030203034411203040010500c152200c021060b01424080c1911a40c1403914a10345904620422030340c003004140c00c814500181240da010303118111143e50b00035541080d805160800d450b40fa86188000c0e24440b050020031800104584100380d00718056036107488800c1c1607400c102940d0044850b114001500151065064000d0300c1540e1441098624588512505580500c03603030414044489109000308024034003083d07801001c103414016a890103010004040c00c1c1020701c40541b00044030400107100c030343d0384101d45462005030124404054182402e0380c1d0368640b0140728642403091a1300014058401c29a03144009140ea94100d40910000c0c0ca019500d0760010200344800c80e262500141702c0d0718250041074041d801c100c414a9089003140c90b80000307031080031902c035088070f00c8100301406204100040c0300c0f070442c0500070b040088030510415092601c10080c858001c0d0a180c18880403c21740d036294086010051900110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 152369379 1250 152368129 152368141
    0x2031312020304080a0b0a060617040201030207020409060f05100b0a0203070f11030706030204030516060c11010509060f0304050f0c0108280905030307020d14070305090a080a14010c0207050117 85
    0x1c2c42c49a038015003800d000302c5240000b0071a43c481e0b014042d91403440e050000a86424080340c2580340c030444040002c0f1120081070265009034010006240060004a85000140c8a10003503c4d071f00c1000390000c2d44e40c4c404101c507240c001c80d420400b5050088203245420544c080095a902644c000074040c0314001c8402401c0000c0711402c4401441c01900391025242e80f8403014000f9042488160303042e01581a0340340003210310802c0b0000395484c0e5243c8400708482600d03420021503e407001c507418010100280012a03a8180251407038502252b009540d078600b601d0124200f840d9490b41c20708590010500c021130303a8002e2071140e482640392500318884150b6a80365924070040d251a08141c52030310190701d051200203c0207500c14590781d02110030444030034130200d03803800348a809841c5483c410302c0740300c3c00284201d0050600c03940042001e0802f41e258a080c0e07040220380c43c003c4900c2c07140620020b142040030302801a80c070f0040c0c0040c154191a007000030749480306030b0004041e0b00b5420700005003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 152370629 1250 152369379 152369383
    0x501020115140409050d1e030b0a06120621030e04020906160c032f0906010203180303040f06020319080906010303080601021014010f05091608040f050609030a11010203131202 77
    0x512160060b0464010520110b801f60244560780d0480001028400c00126050300078001e02500c000d015102c1011030380f601e042210f2074218490101e18143c0c40d40030000d40050500000100c80c0d03000c1f83c0d40f030a0682c1900d0051f095444609505000707030b00510055042d540c031001640d050b4130900b6a0b0002e40300c1e141c5005207500c44203030802080040250b012160302c00004500c1925204c0c918103d1000e20071410400c03540329411511140181d00130040b801400907000c4100c031701410054100c03420551541044102d030f100d1a040000141c0c00454609500217660080c10000c240c5810700072032600380881820f0b100e250500010701072050910218106900c20802d120920244003010045c00360700700c00e80c401d103510070f2040704915a8107540219040c6049202c40340560110301d03100c1d407601d500280c1943c3c1407000603c1a0380c00e004070710f580d50200b40c041c40054840c8120202840c0d44044603000940700f41038034030501e03545030b205000b0001e603201042c0d8207100c900d4008180f44510b085004080f4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 152371879 1250 152370629 152370641
    0x1b030209010203040f0902030f0702030c062406070614010b04080c04050c22050f040b0a030210020f0a0b0a1d060703050406020d0606050d0e190816080301080303060102010605010201151404 83
    0x10345207800e80310000f0703c6c207040d0b44c040d5018031142040328986441703800b0100e94a00900e2007070159a0000000309601300323050b40c00d001c0d144030400050202800b042c0002000750b080f491069891036122107200380350301100003440740580598030340503003041c0c208465259202854005d2500403551103000c602140003a40070b170741c110715000d6034001d2a0541200d04500c10442445441d00540000f10307541c000307242a02620001e01000741901c20715614503001c0125001001d4061070550041a4104054200c2070110003501c90288011062a041c6408400122140c10782000f162810f00d100d651811840491915004225882c003c50662100d06280303000303105000564940610703101e40041c010b600000509409100a00c040101d45581040280c4070340c00604d840c502040402204000102e448014140480382e407030780c08000846565411001d684280c00004460340b0200800400d980e0901507036005d04401e10007441900d440c6004140c8024040c00b03071400407002c000440716251076681c002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 152373129 1250 152371879 152371889
    0x115120204050402160303050a051909020a0806040308010f1d0c0c07091d010609020f0403020603180106170d020a0b190f1a0901091e180c03080a11011b03020901020304 74
    0x440d990702861700745203400c401454007100480d04050004265240034403c242c40f803486103c1c400c28809100001c0802041d841108a1340f003080c03a84042a031743e4040110610032482070f220b0805550400c035610109803503550000d155a42c4c496a00c1040340c189601d00c6030444107030401c0b16182c014101c6000e003001015001000b00074a02028880c0c244410300101d9100c0d500da6000b00009a207e0403190281d1181a88030440c4802c1000300708018103041000f50340c094405800302e659080000e412600b9174805a02a004014950f406d40a81840901c5a039400c0c0506000601e040200f650f0b075001400d500800800300c0003610b402d25007200600b42c10540880507a0107040010f1010200c0c2d0012540070000018002d03250710001141c0105e10740700e43d0b04000400b005c0701f8600d06c00038031710704040c0506a209292001d40c1021100005800c1c4180710090f500c680d961b20348410400d00c0c003c00c611010440b02c80140c0c1480f904070700d8a03040007030840a19486203805660ba07107039400140e04d14440c070b42c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 152374379 1250 152373129 152373131
    0x9010e011b03030507110105011406070c0e0a0f0c020a03020616050d020c10060b0c100c090506160303050606070b060d0f1211010605040501030515093301050901151202040504 77
    0x2480040580c15400248588919281c2d601b1425025942c80c1c220b40c3d00340030308000100d906614480b64a8100007401850f84070309840c24200351107a001921011081e00d940c09850345401d102d0009000318010002503140c5440200341ea46103a0701c2c001d40e1800060314442000664201c203520051264040b940001602c100643d61000340c001c00c1e5564a10100710710048610300720010440790324103401c4501e4112014024a0461203851180005001071a844030a021100d0000a125256800500f000103640040c80c0042d00f001d09004d415100c0003480c6600c110300c00c02c1004005001806c40c150418420348418180402d18941070703403645113a41d4003824101a10449001c01ca074010440c00e440c81742c56000f40031055590061005075802030100a1561b0480c590820a215491030718a40c003028810480d00e45545607040b100182c0a00c020190000030b07070503950b40e0008964031a0900410341600c825080b580350520145030140d0034a841c00c1001004a05409407550f030790161406440c00600c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 152375629 1250 152374379 152374427
    0xf0d060e0c1c0506090a050d110a02130f0c141215060c0d1107031109060a030c0f0f05030d08060907090306180203010f05010b041701060902040605120903070809010e01 74
    0x3a101240310501c120860f076134800c0c1c400040300140b01103000e8110720783c8500205583c2c4ea0458041d00d406e180340b0640c1c040340c0300c3d0940707a00c051381d00c0080118000c3c1c0c2401d40012074180d01c20061082c0c1e04418401c0b420710800e40c11004d0341d400308008070750102403600d041c00c8442c1c8484d0030018482c00180100d9511550101d050750a0590100301c43c64500a10313260110b1028011002c07944074080c610014122102d201007228450030b10000b0107030300180041c54035400c543c40b03581d02442c407030300390300520420105202c00b40007c56100700410050b0404070000d0505164030380005000702d100500301c601800d0310760081945e213802031002a0103503520000074403151a81451030004c94600040c140d120350f08280410b000b1402c18454039041e901e070086030614017401c20700c409040307410404100711259640c103400a81c82c229031010704058551595079139074400f60341c20449a00300001d400894036420411682c00011502c0c41150110b03002800c016040c44070410044c0c074100304400801c06031500d865 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 152376879 1250 152375629 152375659
    0x30902012016080c130b030309030703051e01020f0d090f0b0f040b071106010b0c03040801060e06040c3212040b09190b0103022814010e0f0d060e0c 65
    0x1c41c1080da00c0700740e0608041d210741d640003003507518400308070800d070015440c400170520070245400c81c1c503000d040501103c0c500410f00d0b000c28034100c083d92050b40c0e01d070051034156510001c4207a200c41ca044080700294103019010300c0300da0461141031150b13541d060360b4291450400c01207180025180d600a04005041d20380340a0110f4010412541245c2a6000c10000340c1c06a02036440d003603140c918600140126030070302240b6056a40112800020343c40244400034100409010300300185c0240b10502000b4103010003400150703208403144c501481440888040624441e821004609104624044440250900403080ca00c501501070204a0300c0381c0820060129550445006460000071202444600e501244011710362000060240d0700f00d0b001040940340c0301d08511100c00c20050520104e400500406401c0c0103a544240d800c0c844a042d54001d0b0341e040761241d52a600280e9030780582200520002c2c0c006034100304002c2c10f480c0d17a20034018241000b000b40c3d144404001c0d00f1840054084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 152378129 1250 152376879 152376883
    0x150203040e100b0307080a0b030106090e1608060a0c03060b070605070e460e070201060e0105010503040219030c0b12011401020d0f18060503160f020d0309020120 71
    0x68001c034a010490500422001c6540c000d0010032248100702d100e095445a00080700d030140c0c082d120f03040a907104c489070703000e594082c0b0500005190443c030004035965101441030400d0300e1650f0301c1c0313598030325a2020040d40c28081081e036413080d807035400094031440e080c10650050046400a907002200410510704000d11030740528050711a83c0c8641e28448203d1007000700b500005c041d04846104140d400350100c100c3c241420204012071940c803005c0742c1111b038640840220b0340d4440c2805180b04400c1c003102940a1050f03a01601d00d8000000701907040400180085c8400b40c4002e006110801c1071503440c071010000031024644c8480710a4105640e118000d4160f04405002080001c030305c000041c200658041a481112040e0090300040d003101000355443c0020000990030300030086e1800c2c11580580b00b00c100a002603481d450344906012807200e110b591101342c101c00b80300540113442c5c481a00050340341d4803031140c1c0c50042084249840100c8450b031800104d2110f098003110f81c0da01c08140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 152379379 1250 152378129 152378137
    0x40b06040524010c140d020105010518040b070c020d170406030e06160c0c1503050a0b100903080c1e0c101b08090103061203032009090109050709150203 67
    0x49a09000c0c0c0d860321811000340a0311140d01c0d280c0c884216142c91103c0d40103030070894843e8007910768629898908000c69081041c0e460f603400041c0d43d1000144003900d440c41111035a002c0c0546d082c0030300d107400c1d0788240211002800c400c0501c0040d001c80c404568440e10080c107890f13807102185151154104003580c09070040c1c043c000c04039080207039262540300002034551042d89241300b50018040c44000035200800000e20998801c12068404500345041c1c8a2080409050382e50000341c0b4580000f0322821140480076440c4a0ac80c0c6007622a01541c0c40380112003030b641c2101c2e81964404c841d40c3c50603d403641e8080101d6112145003441b181401f070114892007032200948200c01700910703192080351b8400b10640b00610000c0c949944002061110000d024000d4040c100007410300c0c3c4030004c14007034080010003100040e88420032011501c11309000807586c0602000d04509212507040014a00e00e0140141422581d440e0f000034039051042003803a00420003030481200000070303800001d40385d600c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 152380629 1250 152379379 152379391
    0x21031605060604020a02031c0612050c0a0e0f06090a1503050703050706091809050312010e060f0103020f070b06030c061603090806040c06030b041104080c0103050c030402100c0302030c06040b 84
    0x2004005055428280210707507000170329038007861a0030700b000540380c1c40400740060101000d656075008103078008601c64a0341c102d4001c10042c034070314040a080041c400381c150003100c1903864a009100803050b40504244c0c20240848011181d0f94a04000c24000c1102450320072003121284000000c5c071002181401c1503d0042d4142d40303880352103003016500c04840f8410116611103141c400f61101c0c0030342d4032140d440e510620990b071605984200e00084160280c210400c1c552502d030a001caa0b26080900304046442800c0950510550818525081c0614003000d40404964000a00079a034140701c0c000c00400008c2449440d03204581e0a03000040d25410120003140400700046214000000c26901c25503001048000c034038140034044001d00310300300d43d5582140d05e800412121590f400701402c05809260020711520a00000040565201038010311003450b08000748000341c0c440b2441c0540705402e60812800c0f008003440e040745140300e07014800e15540181c6082c00f0401200d6204a0f000301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 152381879 1250 152380629 152380633
    0x703180b0c0c04140106080907030602130801140126010e03070305090a1202150d0b0a0b09010e040204050a050d0302151e15010c12020a06020d060509010b0408060621031605 76
    0x403014500384412958413816004132140c0000c0100400d92003070b5811540401c2420603601703078556a5480340c3c1a41c01000f02600101c5104d1814007611000b48901e0380c0480b82030003241e500b54500503040c01017410070380380050480300703002d09110201001d421620320b0a500c0c004680e6110b41e03500300242503802a0304c00f9842031418010002d803883c04100305ca080389030002d00212804c81d2284803141540c3c00071005082d074580303880304510140d640c580841e00070602d200f0401c2d42c80401400061040c514015814855807052201b03000d96200da00c40c12050b40c1c400d4440b11540411801c8c20391070000d8620841d03540d000c0760030801c00701000c1d090300710102c00c200b106074018648500c034195981205000724107000031442c2c0300040c0800e4440120201880c51401a640c40f00000e0322100283d07030140114040c11511903400b08058201405c0d07040c01132103500c807414107160406990540b110f20241080f80701d020946815640a40c0e544a46850103c3c90011240d03180b942c511614904000c52a081d203941c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 152383129 1250 152381879 152381893
    0xd0605040506060c07050f011214010602060912091302130605040e01050d0308040b04021f020a050609010b0120100618110c0c0415090e03040e0105010f0c080703180b0c 74
    0x1030810b0f01c00c0d901e0154040d0040c1100900385001c3c030103848154a8814100203111090f218201e0062180c6004d5008040c9198469070414401a00d480b201900c4841c1940c04225444101030650083e1044140203c03100a1003039140308001000c0e0140008203102481c8a60001500c141c222008204072030420145602580e80c4204100e520320b001d03030003c1c0200d40782000003000030300c40307030921076201e0720081c141c0c030703000e0002c00700fa43c01e0040202111015a20941042e07042c04010048994803a201e50001e000d03003c24900020400040003407003c454141200c0201d40b181c106000450101e0070b50181041a5030303032210460004241054548002860326aa20789000500c0c4111032043d2030480050803501129001d20004104503a080003d0b04055100400e50358610b000d103803461a00c42008580700c0f03041040d600e000c248180d100b24103000d0311000711210580c03c819881c003216040140261107040c1c604060307a096406040725800c02d00501c50200c0c0d0f11402001030021841c3c0c140899440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 152384379 1250 152383129 152383141
    0x206041e0611150109150b0d09031107050a060f051c0b0405071d0d0309170a05070f06080109020309030c160f060806030a06051305070f0501080c39030d06050405 71
    0x40e03203400d1602d200683c410200610000d43d4641094024034074481000359807599400c0000b40e50780009052010b1552101a84010705900051001c5429039040141070454a000005220030100d841280b0902c042d124400700c00324010402c8e508800003001007029a1004403816500415008041034802c40c07515010980541c4202e030708128074030074003c19140142c083e00802008108940c4201d08000700749030041007629055607861862180c60004000720340300c900c0c0c0642800340a0b0001e40d892000d0f500c003000659031000711603044400d03a442c0180c0e2515485142800d42c45180102c2656106849035400800703000150142241c000d90404507480b034841504507400c1c4415941e291385903010501c40c1000c030359181d12164000c1a280e000c0c401158071540d0381418015107a00103040c0018003d006c019550b081001103a0000074540064581040b69040d20300d00074250300a40310f0703500c425110101044108280314140c01c2c940003141d460f810036020540c0074103828000c0502943c101004102 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 152385629 1250 152384379 152384383
    0x60702042f2107080106050912120d05060d1a15031f06080304080a1e15020d0f02070b160e040e10110403020102060c070303180b060114090d0f0206041e0611 69
    0x100482c00f0703a80d040050b91030110300f103816400c0079840503840450ba0910108000b01000198103410103030310015140c0303214042d264122000145924040c1c0d201398160b0001841c110b2030110040c0d14840005115141c00103081c5040c140300854a400d8030a20100c0c00c444987d01e00310300384c03141c09214203009450301c61a403180c03070b806940700f050b00d0b560281183c4800038201c000e440703905480002c4501c101038419110a2070b000c0e0260f1240314810340c002002d807400c50305070244c10700168009100f035281c141c03942c1c0e13180d001620040204030750074074011004021501c100e14000d4900c400400a00800c50301c0e0400c40e07261011014072180b12464002c40f01a221300c0c1905a8040740d40580103804107540d140b0804c0882d80c0180b608404040c3d44d0f101c134018a41510610341c3c5043d014101d0460b051030710340c002520f40404460304002c5102c09000140750307a030394134034085401c6030302484003070710803485101041c464050782c0c20104030342c2703a40003078070446c400501c0510049480da07a5076079429982d41d52080d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 152386879 1250 152385629 152385631
    0x60b0318011514011412040804031109102105030a111c140a030b0307030c0504140f0105040b010c02030105010920030c16020f040c020304060e030309060702042f21 72
    0x40d40c0644803d240c000650b020b00c2e082558641400d118500c0c004d1443c10020100b03c048800301d540d0350020400f8014003120050f0004007400c1512410700c2c500b05115000c90422041c07144c010b11452070040038003442444000d00c2000b81d4013104903600c80340031a02c05449100c0e0420741e0325007032152840302400001013540561000029498000304582d04c0c500030380450348454015424991102542aa6034030104050030085025550301070046042104000c10703503040030503400c520030f4601e0501500140300e0300018115101118005401000c0c00f0040e1103001d5503c40c041d505501c1d000000031001c04030b4010f0b6242e04500c41c085c102d90440084650310b42e000c19128054111410700c25804c04000c8031091442642c002080d41c4007050103000090143c0d040400a000140c0002c1010040c41c0c0e00040c1d551561401100034500f011100404a00a4040e03000301038851034a07000032981c21507120721101c0128620b00841e0045603412543c0b080644d00491001c002031104144010100c0b0080840d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 152388129 1250 152386879 152386889
    0x30c01030b09061908070308070303060902090f06090406051201091110020d0e210106060210021606051b0307030c0e01030204050121060f0f05180c07080d060b03180115 74
    0x18140c40c0c44440521011209411130850803c21400c400701310100100031000042d442000c03140e03510313a1145001025a04213074080100c0034014400b0781d82c1c9689800d16030f0002d0405440d8079456410450009015040c150f100c2c1c0e40000904961070040401034100e680301500490823130081384000300c2480000542c0c901d0040058010703a101800c01841190018805500100140341a8015448910100c000492824002d0b07550301002c00406405100c100c204628200c000c50400c11402450501c2ca80c006c2e9008041d59502c0e40042c0d42101d800102c440d4460034054030726180d00e801c000160003800c080d0301c07240c0441d1001d41002c0c1075602c603000312000d4232818ae40707203815008000b60440c208070224002070f68203903c81c035000c0f03001c00d29480d050004124451000d10101d00d882d00b800800010b5502c00403c4c3d4041070108940c544c0c4200c1200d0b1507541c0446015035640d03106501600a0400d60003840c0e00714800006c5c050700c50708a80030006080400790080002c000c10403944206002c1c1c2d4810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 152389379 1250 152388129 152388139
    0x2030d05061c080d02070827240903010204270b0a0315051e0703140906040b130501110406031d16090b06070203010e070305100c050f07050307051b030c01030b 70
    0x80c01c00150758140a054000d5000c0b10146c2020481c2da5806840e421845000e2108d82140b0041c1010404041100404140030f40300c0f0440171019440c1c0e5884c5201000000c180c80c2400200a005030f10258111001000340d60395903e130010203441d001d891076000c851484400c904050400c8074500e800003c02041301d501561050f54028900b1482c2c0c05403034014529860f115400550515065011003058410703c195603001842d91012010590300c000e0190170b9502d0381e40100704110015180c0c0c0042500000348003044001075085142c86409041322030380c011001c404c081400a00300b6056040360011045648610405003903602880d541c1e9003100382d41301038105025100b0064400c2e1640100c1681d900980300320325001494004c6820f41e182c45480310074681c0508400c10500c03100740183e49210380385410501c08007001d000300030a2405210301d2420a00e40c0018850300704081081118610360f8020151182c880e140030420401100312000740e400b80c0107100c20603540b50300c280b040c41c0c440782000b05 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 152390629 1250 152389379 152389429
    0x5100c0518061201030c0f081c3c08070e0a0302091b040b030a0b06120c03060d060f0501030309060504060801090522080703020c0f03030313081902030d0506 69
    0x70104030405002202550450790800041400c1492007210034080c50151080000c840d2500c2c14480d8001d0301640300a620390040e646841d54020907098802c0498141c0ca4418104202e18220801c882092034820969084001c1100545600002805402401ca451300c031059610040300303039002e0040c00d81d80c1d58407906149040c001441c001039055008074032010038402d06101a00541c281c0d50054104c6001c0740000f10402c800003083e40181b0480403000d40300350303007000d21002d11340c0310210317010304a0408554040002406600c900440c52002238215605202e0013009420b200700501080c001070300064110440420082c0c0520201d80888de01d641e203442c8640c0c03808403120007c29010380326588200d1500400120701a00304154a601d9002e490000e0343ca07985480c019183c003100c100b155009807907402d2200b40955020083da42d10010f4031140e40681549490046164411021071101418000c081c228030544e002019154242d15403000b00101d8440301e040045101c0c201118242c0303c102c0c41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 152391879 1250 152390629 152390647
    0x10e040c0806133f030e0304030804051e060f0906070b0406091a01060e010e0402070212031c091505041a07050d06080f0a0f050c0405070e0f09070206070309051c020a05100c05 77
    0x6015441c40311301074500002d0385403940c41c03e42d08590150f070003652807100100b01400640740200203445040d80c1402280c02c2260100c0201e882c81c02091701070010007402240c4844030f512041c0c00c03030b18496400000c584082c0340c285070550060004400030f076105441031b001c03025402030009085050314560384074450110380007001114110502405d051b0060f80a00c174140068a54042d0018526419009142c586001030540364600c2c0c1c0c4403000c0c8880500b85008000800c4009160f11a10140180085080d81c2c030360900390f404d00b0446141380700c00c11014003000030b9a5848009030601480c1c298040c400c0c0e80c1d8445c552540e981412440034243d400034881900004c902c0e01c99051461b2140003a18200d010304400a81114011540000892201003641003a840d090485852080d801c5515035400c0c2000d0030000d40c1c42c3c1d0000d001100741640c0d101c8100c144441045043c0180c0c43c1007004400c01110050000c2d100c010208040fa0382c4d101e6811100710480e228001c3c400d1180050b52134a061102603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 152393129 1250 152391879 152391983
    0x3070807082202030304050a0f05010f0e060a053613050f060d0c0801020a030b041103042409060e01020a09080708150a0f0f090b090312010e040c080613 67
    0xb06003c81c0d06100c1080f0002d016241c8260050042ca01c0e25a00e982d114906000900014506041e4100700304e0301104025140c0d90f008203940140c0e5481c0b03003aa0311000c0080440f01401840c0c8103007548420700d1340400c01c00b580c40c4c080041a0030000d4035680380c2c01e072800c42c8000513074000743ca1001c0858400c00000b183c50400340c00c403030040384c09210a01c00c2941e544415508903444069100c2c0020341301c00d040062070400340201142038040211705c41c0b42d8a040d0f2644046400d0f060094a0a010040650003070b5903541d80268620603041042004280912500d040c000d50181c030407040803887e15600084c00c3c0d18041416000c032841040030b0101034888074400c001c00c00b0300400c0071030b00550741c1d01c00c200328240ba40301c3c141046e0b244400025801741542440780f56000010032040c01a801001307001400102c00c0e041c603045401c0000c1d06000c80c3c50b0b925116200561540200c1c0103481000200035607015021028a60f050140364020001540003103512159105001c200c00301218000880030341c105a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 152394379 1250 152393129 152393191
    0x140619020316050604050625030b01030f02040b180a030f0605100f151707020c1c020603070909050a020f09010509030f161e08070320150307080708 65
    0x69205881c9419440e50510035000600c00c4159010761084040100308403040181a400031056240c910302004492071131000082c150081c0030400d501e42800c0500c1c1d074000d41090b83c01040524055403156101e09441c84550040640ba498980e480d510b8003440b0b00b822403400d0156a040030403a0390b60802a19004c009e060701034500315080c012498002001020218507801401568a50340380083c0c0680009110740d20319054090782030311110030303c09c01a400141143c445482030751048401102d041486076005d1340d880019400c0b0307100004001c074280c0c3c0404902e0540c0c1d000e0508011607220354008004074051401c0c4d000c1c00c6041002121595030080b8041e0008460050884540480d040d10080c14541e8107040324100b904285000c1c480001c0c0c0c0d481d240034081ca894415080c140c60004540e40d1201103200c0508884070801c00c0f40010111a01c0c0f02c1d490102c0982040042d00c14442d0b544141c2e4011280400000c19000102e41c6240c400e001e03503802446804d054501880c14840c120480d924 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 152395629 1250 152394379 152394427
    0x1050702091009090c05040c1d0d030201020c06070203030402010f0c0201020c0108040837020105060a03060c0203130602030d0c020a020d0b060a030b091b03070b040b090f060715061406 81
    0x3800000c0c0030401409071403803045c802c581c1c003042c90380b0301014042500c460b1080e2a00b489414201d0741d841041001c141045038008544100070396110382000d0b80240306045d440d91141c09082c04105526030004015400341e4400c0e6200d0620014410003100d501d20340c920003d00503040300403651140d40c0710314044e6800074002d6001c80c1c6804038881045c00302d1680d0030b0521860710804803981742d400d04c510180328074220141c0000d10030343ca0b210000512400150000a20441e500c00f8084078140c070070002c0c3d800002900c00b0402030540c039a58007a40d00d410005104000c6414004501c5216101152818100764050480d180508469940800d080c10007009190008070082300040130400d0003a501d80942081405092210b0110800c94281280151454000e80c8801020003003205180b0858085481c40c200c40b9880e0388516001400d41c102034a8090351014010400400f13010007a4040c90301510740c0441003005031741c0e59608e04000304401c41480e038040014003030020020b603c4121405006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 152396879 1250 152395629 152395651
    0x30d09030e030f0709051506040302060c071508190209030c010f2105040c140102060c0304020126100f05030312060303090901031406071e0e0d20031207020105070209 73
    0x950740c2020910b07240911248640c0790b0300c61042002045000c0c4596074000040411448031030304558007080c001d01c141d20000740510000646840384803000d0040d0030141c445951001c2d005a000440185000c4099a0a61030010990004c0360004040c3c8200e469800018000e004010702032001903c0c00c43c010710341802030189280c0701000001007080d03041d0f40918554400074843c10b180c200340d41d25003035070742160101c4101c0c85c000c0030050ba00041d0035940007801c044000c0d940d5445100495084420220013a55240b40710600251005280d0510b4803ca2016071f0f041c1e8015a1019030784158003151240f5034264004025480100000055065100d0302c0613085a00d004018400710b0b5044109920a80f01812003c00e2040d85600c14054117030807500074a403030000031035000200b842e080305c50300240003030080c07040d01185035489034107139540d40075000008a1000360340d41074009400140f205241d44a401180a443c41c0e103490b10041e10001e98041c0d44060500003aa42884408000034024141c19 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 152398129 1250 152396879 152396897
    0x320040e0d05220f03080d02090d0303091a0606090621040f0c0b0301030c0504050a0f15061701030b1b0c0304030501020d11160215160c060e12030d0903 67
    0x20160400c85810007000303a5864507078a032000040005a21048555901c2c100a007003400c000b240c01d600100c00a41e40c12080c001d540722110408003009109110440390001c4101030284181501507010318000da01485044640c69103455500f8001da40c100c41040d0701c10414090506181070810141c03102803a4a2401d41e4180012413640002050480e811a400010a8203030400c00c10814540401441e100d0101030441d41903540c2d605400006025803400380340e40b280021070b03002c10307500803c2c084110070404211102d206081c1442ca021035024450204403010500a40500c1210f4404c0c100c07504070003030741420788412540f030690000c4a0510428001d0510200110f24424401800194403032000143d4030400000f00d00182c410b5840d900c0164581445001c0351120090140c1c0d81c0254102c821240800807642101030900500020880c20364040c001d01003007040742c038600d00a4604c2d075124010110704020800c50f4600340501103114981051103d10032618094000d20a0107100b1b0500c20a5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 152399379 1250 152398129 152398151
    0x140109170a05070321020303010b030109111c0615140f0a020f1903030501090501080a060b0118080a15020307020d1d15030a05100609030213090203010c020a110a032004 74
    0x24040d1250001d4070389172003020720072102d4091969102030f040c049002550842d8505103460b03646000c1403145101d030a494410a08148580000302c5409104c1c118441a44004101c07a0000500d11070003440c0f4001040003610042c179020740d43e424030420040380711525210b40340c0d807811310a80242001c2803e61003075400d085042001030100c20301c80048100c4076045d01281381002001c1c1c95040c0d01204000346042c005001044001c10003001b101e400c2503002c00e219000c840101c50200411000034070103d9000b03808528004041440704e0018060184550740d0001d501242c1c04070300c400e0316014096404000d20000f07603802940b40c201040c0798404402c05914000c03000c035441c01c503880c0d100d00d0106400010011106130603c2026040314a40400039541c9082440241c174044150001174071500074407c0d1415040c1c00740d0011101c03554054024001009903510117580c1c0d015000e01241e004600b046e81c0610f074244400d64008a03034000c015840ca02000ca44800d940441c003200f8180c115894030b8072805 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 152400629 1250 152399379 152399383
    0x1e0204030506040302070e0c030403050a12060b040303080a050721090b0f0916080618031e2d030109050c0d1a0f010306030506151201050a15140109170a05 68
    0x4502510142c440c0b40341c5490001d003412030350b07082881501200f04c00e0140b07541e594001d80303500c5641418101c0e80c40c900c42001b601c1c80d0400d1039110b0801c80c20844040f55144070240a40101c034800d4842044d0b9480300c031000b02c1a0340c0212403850001d90300003920b41c0e500c03004000c480b4030743c4110791001440400703a48a00000500c111180585101c83c8010702c0f41c1e24008004003040a0858030059400341d08007007102e0740341c001c0a4224007046080c42076100e00302034148112505d07103072000b0701900b400280030540032864001d20f8010002d80d2400c07501400d02000504a1001c1002d8210040c3c6140c0c00d01985100800c1e000d07080d005440030a1004242c405414442d0b4010240c030311282c81403145602080018181103071071b1042c105401e2600c10070000703a0002d940b68100b2512903014840f04408800b00e080c03103a080140d8a103640c2007034103001c8144507a61021001104419000402e59201e600d00e40d6140c10518450340041c03801c0d00104802075494a4402104030303034505907002c03200c03e910b58034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 152401879 1250 152400629 152400637
    0x11030c0a21091110020606030c09070207080f070303080105060309030d0507090e181b18060d1a010509011203020a03030507030b063105030a14161401020c040501050f01031e02 77
    0x80d0101107501c1c40d00b00c42c4c035045101c9480449140300070000b40c42c000c2c004c80d444440413244180140380c0b06006c240614000d2010102608042040f01e4202042000d8156201401e100c141c000c1448000081401c0c1014411244540300d09030081d441c190042440000510000703002c241000500c042c00b1900c1e45000410300c1c0104c10184d0301002244005055900b4009080300c5240404c00f50b0f032129225440301c411290504164142d01030b07250b03641001141c900c5032810030062001c0348080303c0c1c4a5400f011404e06068030300580b0302191513030b00c40021300401d10744100c024016034444c8092200003442604111350205440c5408111445001d0114156400560b001c04525414100f2010060204a498400d40982c040e01e10030041c90000800d407142c0b41c0c5800944185030300410000c08400400a4641700c0031402440c610b80c40c1d980b034a2035070820010800034010f000d10403001040349440d0241c54107032000109820a800d11400065000b0100d07103503508010804102d5501e03554501d840030b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 152403129 1250 152401879 152401883
    0x9031b05060d020a14031b0706110c1c0f1e210903030f091101050703020c06070c0305211c0b0306131707050307023304060311030c0a2109 61
    0x750b111031310030201800c580340a00c0380a0040744180b00308800411003286020500c2c0f104035171540c0d240680d06028001e000c1d44040205102c01c0044d0b600c1d5070b48400200101074981d0399014022040c009502240c01041254004000030843e0741c0040c1951608128402100014140030003040c044520304041000072214020005035505044002d058041c051401c90100000e4100201d035102e64441001980d205c82c0c0604010000c01c0040030140201702401d999030006040c50b407944803a14200100041070301007103406024420300194224a02840701e025220b21038486400c14018950030542ea070300754501c01e1801601e40d424002152014041d5034000d0b94803002020018203242400d0903030107084407015400d01410030851001c500c011043d202c00c0781e81104c81e401d050303441544c010741c1c104000315032003c0310400191940c1e4865410005000f2a1010f0300c2c140300c6000d822001d240c40d40011a68003105003420030281550030f01c102040b0100e01c0700401191074182000d90541d04660100200b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 152404379 1250 152403129 152403131
    0x203180a03031d0102040f0308030601050d020d0507030f0911040b010c0c08010e0c01090303080411060405100f02241504060f0f05010207090e031204170c06100e0709031b05060d 78
    0x103000400e0380303000318030110780055100175440c0c585458503403460102684801390440d003020020410f03981c400c07011a502e03a1009481903403607403c00f404400007800700742c0340c0801180c40c4c078203030b12000800b5010f8140000d03045281e4030010070703412040c400585229000d02d0304100d200182c80002a40b00c1c03903480003038068a00000f40b413001d00d502c8070380345c000c07008801c5042c08001c6004100082d40f03d455960b000c0d920a0f0100c0410458001003242c50080d50040d940c0001c20020254183c1d90040c00700045c0701c007550882d5200c05210004280280c4c00e0107101000140342c2e80065096032030140c20f1443e010010f00000307000c035910200d1703820b5412950070084220030311010811066904000400203004040010407a09001c0001c181c0e482c070801c108247c07402031103000901404010b0801c003a00c801c000708010340d10b807200717511661101d1048400240801e910346010622101820700c1c2449212103840304480f03e4155103404001e4880729003e0a40700c0440e0b04003245540b9444040e118600010b10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 152405629 1250 152404379 152404391
    0x2031c09090b06070b0115030207081605060a05060a05040203090a0c03051c020114071d030316060509030306030607110f01090305070203300d0e01050103030c1a15040203180a0303 79
    0x10700405480788074140512614090084102051240d41c0700c0d41110800d0603e101d03017a001400950290142800c06440041c010580b40c0f4a81d0f200e03901014543c1c07085050351003e0741c44020301421a40c068a9440d00045040c8c01842a07041583c021074101d0140c4086508114007a80c0f5820300ba1301c4c5820803111a0051400c1a6951658541c80702100d42c050009118410411020980c0038000611003030030060000100c01e043c0d491610161030046020f0f01741c039618a090102102441080c0300c0886082d894680003400089000c02640c0c0200300c001c001d03203825198404111f40184c00207040240da130007000012201e81209105030301006100351030300c603114070003401010b040940d000c52085004908980000d803024104581c0c0300304c03040c2041441d845004c00c0d14050000c00406101203a0b03503107400c0c008418580c2011426559911071081454001030300f540c2c1e502c072106d099801420743c807034800c107044191600703402640c3d1150f020303512480d100d0341c00300c005441c2c19100403055010a035190 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 152406879 1250 152405629 152405639
    0xd0606081507140d0c1e05091002030c030304110112050f04020f01020105090c10090906081c09030507090f0e030318060105010c02010e060a11030301080c010f0f050304060902031c09 80
    0x1881e0140c1c022180d003011203006610041e9403082e44610400c0e00c12059440704128000c5000700c2410010a20340c80041c40d40d858000c0015180b60f01c12000c0303610800e040410703910081d10000855120084c4d03a006103040d611265280d040d001040030144e07040c8024560f0400e076404891258900c143d561851034111810680148604c001c02844210304590408040241d6508002600107a202c0241c032211f5440720500803c03190005c250704462816820034500041c5590700051035902d0f1764a400f40500e0f540074604094800c0100c40c071000b01a50050f0000b00031200c1d00341e01c1010203e0301c1c0d00001c119094014055401d40c2c0c0308640408030b406402d2130050070248100720b290301416003070034407940911554001030491280e0495440c420301d000512040c080780b158500320000400c1008803500c0356110702031540c0301c102010240c1d000901c001c0048034203d1103140500c1841700c1a481d142c0c0356490b0707500c400c0080d007100703101603805100303007100d10420200404030020286401c0d0b503075a86050600b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 152408129 1250 152406879 152406913
    0x1f0305060109050306240418050c042c070f060315080607020a02040e03071209060f0905010c111f03020403060f0c02030307081305030706021803060c04050607020d060608 75
    0x2400460400006002c24441500c00040359500002d22240c2c0081c1c800402c4c0c0100003130352113440c800d90070909140103c442c050300b200d41000c140e4450b0081d200c0424001c0c0601084605207881034103918007407280c50414036400c040c181003040103041911090342c1c451a118581c0e000c581d21010000c1d03aa154000c0c0c000c40e12a00c840064844003001d0319460810b814002c0d9940204c1c03c3c064400c603502e041c2400c2040042017210456039101c0c0030400c0c0950351001c0030b003885c0c840b07104243c0490b0260079026005846000e4800503a03005071640504002142c5a40c1e900d00b0b0341107802d0781c00420711400c1540004500e05c08140002481e40c0c0940c5d00c606500d8542d0988421007400032007981000c02d21040c0315004000c0c0c0c0d078841d810340780c120a103076900b40c000c07050142c000c040030b4641c2c0000203048082c800b05400510b2501b400103400000646c60300e09041d582d000840da802c01045080c0824406da1400400419206000400701294003101d074a80c242100c03503c0d84072000e03d9120702c010240d0107810b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 152409379 1250 152408129 152408131
    0x9090d110f0610170a080d0c120e07060210050105011b0302100f0e0c090609010311062b1d0604140c0901080106030201020c010f0801030803100e04060902091003080d020c07051f0305 80
    0x19040170307010680080e5034004850080003001e01643d034407a0160090188070302c22654103208600070500014009030201a21030b044c501401c00140951000c400c9004c017240101030403604182c2d90f4400205c1c480150845100d03010004904500500030005c0020120f40505e040f0b2a0000200248503487e944640c1d10b000d1031804010300441090003080b001d51b40b00701419044940100698080e1080c103800110035209400c0c0709500452409a9a4a0100c42d5041d51a901d519034004200d03103440e804240b40c0218001e540700d40d044e8007070000200003940c8040c50a940046a004643c4080035503000900962401d070010b03801c50b952180104107660741005600d03100482824920780d00c03501d004000300704140500028240d000700002040311840140b0180d0000d00040c1280461f40c1014034001c40500761030350099200741c01c09000702d42c07003400c040e51120407668480c940528010f5200c3c94a0065000300b88070201030b000c1d440c00012181c0720901044805d03800079100d80300000050300c002d412983c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 152410629 1250 152409379 152409419
    0x2210718170309060304051c0306090f061202010e010e1806040f05010b16050c0904150507020609030d150302030a0b090d0e0f090a0902060c07060e09090d110f0610 72
    0xc12182450503101c03011003199484001600d000d43c5d250740f40d0501c82d00d811444692001d0010481409002c229410750101303003030342c0c802c0c50140f00d0f2511580440d4180c5600340582044604800d40000c015802800780ca0b04801060400d100c0041610f000204250a966180401c8480d010b0070400b81d880d207440b950003803505800017000303503504020407849039000c1c18602c51556204449180d090001c2040059441040204951080c0c136080c50031044200400c40f009a04608080100340110300215145104036100c01c0158104460150764001400184070900d00a600c8803c000c40541c500348035006c130a50040549921605000001902d0701074103128440030062441c42a90485d91400200d40d0103201c1200d4607003003502c1c2c0017035031030003080440c00080d40044c002480c80001d00d80030030407000310383c0c032a203c220b201c1c1106400d1155143c0100c0c2c1982240c0c20004440c81c4041c0240d01641c09000400e007110303000c10080e0502c51070940140c13030071700303840e0400346040010105000d6200b20b412 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 152411879 1250 152410629 152410649
    0x603170c0f030a142107110c0117070e0f0301050c090102060a090201080103030f0203090a031203151412030c0d0201060512150103150b13060806240402210718 70
    0x76040643c0102821074044203080c84400000d880b180f0718aa4804000b08401454020710b1642401d86018240c05014413010001b03000700040400d8640c09141061069074518086e42002c2e900c8070000c13110b02c43d142c0b031000d038803412207644420300303840900c41c1c41d100c2e0000d8141d86656014030303c00645840e5008080d004804d040dc4003000040c0d034083c0d08681140d0741800c0803483e00104032001d0b07045000b2420382541061070001b0002c24400140c01540b04ca006c0c0c0c0c0c500b000b0040e5243c0d61070072106102c2c0208a940d4240081240d614140300d00011101a520401c4c2d0b07013006040c2c50050704040010041000513034403054217121501e080c60000155030746900003001405208503541d01084014030001c2e004aa00310040c1074000c20681104e40070342001002c001000c01a4000a00204410701071000c45201c2d01002804804c409503100520f4500b042c2c0c104007080d082410400a984411646c00b004001c4000150300f8408058000b8005c03815031303c07034407002c10000041c59038200c6207505c903540b41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 152413129 1250 152411879 152411887
    0x180304030f02010e0406030f0b0f070203090114071a070c0b010b03041509050f1501140d1e06020d05010b07020103050a05060a0e060307050603040c150c0305041401030603170c0f03 79
    0xa0604409040351a0b080c209010004082c0002034000c0c5541c1d0705c0074040e01c820760001000c0180d0225024410600f42c034030782001d5141e0304030072640d0307004640304940410f0140c030310a200d164001c40a8038030b06114902e2030002d541781d801100180081594400d001c51182e02c110410465083c410318098410703e135940c3d08510306511000091510b01e0a00101103540358841404d200c1c00313102107a0541c90070300c120342040c05102d240c03010101091040d40800704121820703075185c0c5000c4003510310482c4c1006e002c41c3c019642d550046012280c05004a520507400c1220043c102c045000b42802001c031742480300d482d41e003e0300024094403070041020041500c2c1c58100001c40d551002d2a90542d00307441602c40e155983c040109107002c0b0141c1046034841804820041040b00144001d010f40d0f8141031040450302c00d41c0e03000c2d180c0300c04103000140480c0052006000e03405079201c0e01d0805520503d00170402556a8503030340380c0003c91040300340e8642000540c020701c6880400120081307400b40d40040d450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 152414379 1250 152413129 152413133
    0xb1c0b030c100e0a03120e12070e0105091f06121b1e050708190f170c09040b0438060f0a180e060a08060f0c0309071a0318030403 57
    0x2c200200b400a9050112030140001c0e1500c410080102450b0b00000040d210900c0c0c00c0050080503486c0300b424031800700a03c407218075807404900b610845070710342c1f03200388580d09100402ca09003000a22a5810701e40003a20707a8417101300124a000100301c1505c54010300c02d155260310f0306a13001312110700c6600c070b00c005944d00380a9009904440004119804c0141403040000c101c603240304280c00a490030038003049000038110f07401200390207941c8645a0b40c221107a1100255001d86810403440c180604580010b0a10309405001348995030b4014000501c0300d407203900203800c407250a0611084084032007072032400f070403414840088411961006800c590500000030f009480f4040410b0009007001c1040414140a0141c010701c20304000b4190713a01d40d8940b00c104101410480d0b804e4418844018005492900425454018503c01090300b07040c0d9629004010382c4c1c0c0c8050810070251007a908001351318007a2200120080c0c101224071903480c28519140c04c01000400d81802460300200001c00c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 152415629 1250 152414379 152414389
    0x5160513050f18030708032d010b070b061203030a0606200c1c020a09090203011a0f01181503050604060906291e0d0c081003030c06060b1c0b030c 64
    0x9400426142c070002c1600c2c00c480b01c182940a0b450004003215070101c00d00022003000080d5803823040c0c40c1e031800a0349002180360306445000c00c4c0300e11491180100602000315035403140c541da0121024000c000344001d480d4280d032071580103c5242c800c80b5a1500c1c2404003503404079075440603a4603088100040282400c0031511602c001b0a41445506da41400a40c0c04403201d43c800a49034008010f03a4101c5d544017811009009050f034100c3c400c1d441c0070000c200d8888442c1645800d210701074a50f140c440c901030010350b0040100d00c410005000641d000003035502c1c42c1d000c004014609030b500450b4908000090000356856034000f9801103003403038414040075001901d9a10072140d507800143d1000c0c649040c8015511a28065004041a8081d605c00f6030010074002c040f0b820603400c0401141c4002101166401403d0365124070b0030501c0d007003c0010900c141000e800c07003401414002206551855802a03035442031010601034210000c52041000440c41012440c02054002d0880e140490001403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 152416879 1250 152415629 152415631
    0x1030b13020c0c06070317130f02060d0e011e0b1c03050a0507080d05010303020d03050c030126030d140702031309020a0e09010311040e120313080705160513050f 71
    0x8007a40401c00d00d2200078100465070715030300007070407042c0e0307401ca1381c140100154428603201d001243e210000c5804000c194060500d00c940014100010080c50b034200001c0ea8808008201d40e103403103a001d126020400e215a209010f0b03441290150341a411107030800341d80c8846803c5120380c0340c2d60111543c60030002c0d42504219032629040d6604c14918605036264024114060000e680110b22903001000030390019040c0c03400b039022540c900a031083c0440a4034404c443d91101c8001c01d01c0100002407100e02c10f0304444401c0316004000f9040400c903980780d90084e030141c0b403000c0c0c1c8400007007032030407409480c19030043c2c0c0034405503143c003c0400000710020018411060306580c000b490a0000307204001e000d00411000b4292101540d413400e052090040001c107242c460b42c5844145000d01100003114200c85000701d80240c01c1d503540840084840c008000c0a42e00c5440410001d40054400d0090000500030542151106030500040c892040c44460302d0301c00c0c0c0e81c5013800b40031036095120001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 152418129 1250 152416879 152416909
    0x30604051b220b0901020d0e0103240311031209090712140105030601060509010903020402090418080a080a061212020106080709021902010204030312020706090c03030806030c01030b 80
    0x314940d107a440c1c0c1c2112030341003507980d4036001201080345601c8441102082290554100c0c01c407400c140c03150b142024a1142e554014050ba04c50080713a80418000c001d00d456068050500089114102c0d5808100c00111071924030b40c0e21036110140104601c5084802c0c58600c254010680d0340740030202003003948200300d40b06109503030b810009280c0504c6442904002481d4034000e1107450040d169455a8910038021248240109000824160b1045040c0c1e094894165034101e5403501e91303020302c17000754400208250810f480b12400380e010040c1d81d03030307c1c88020705ca10940d035941c41180a008140c000060022801e00e0b042c07a10030081d0000c00611451040e070000c9000c2c1c03503100221800da00412140e030014039503006003400000ca15595034094241e2406240b0111496604c0300000c03801c07403141c1c3c017009011030501030301c500310305069074040c0000500c983c6000403d0320440d04e62050081003035008600003110401000301506044c0a1035100341401e0070280a001529000640058040010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 152419379 1250 152418129 152418131
    0x60f010e040206090d030224270f1203010603060b19050903010b0405010801060302010e030a0b160c0b0c0a17070e0d03030f060e010816060c0303020c0a0b070305010918020303030604 80
    0x7260039551500202e48003070000400d42050064181380c00794958002420420010302503102d1030400a82c00d5011500c140c1c0010042c0091201c1c2c1000c881703813800410398090b154410081e9620220b00b04020030b480c041c890401c295283e40c903204008050300c02503008110580014070034041660f0b01c01c0d03c08002030610f410041e40720b5840f0008a401800c41c015450b501c20300b4280000348016065010805a038008e0b66490030255803036081c144e80718a010002400101040006101443e40c60814480d0f101c10303141440380b000060b11041070300681661035908810002680322401900181040350070b000107003140c41e907031400c1d01c005032040c400030003854011206c0d000700404141c403c5e44500b00c0d26010035030400c600c5890f500503025500090150280b1407017440030f0200c0511508510300203c3e41d155841c5840340400b0340e8100d0194005c0b2a10303242c540b00700050880042e03215104a44a071015540006081d850440d4250a40f100002615164883d854140016880100469500403801d46d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 152420629 1250 152419379 152419381
    0x10902060f0d020d050103080904060b09030606040c05070c0b0316020d020c010807050405090a0204030320070b09210604050c010e011205040c120f030e040b030c04090602040b0706090c08060f010e 86
    0x8040b0103482214075040400745014008000c00002d00054050400c0980b0100300b00350722165004140e109020100f9490750107900082c06a1403c0e07041000300110918116040070340701d80d01c9201c039502d290055407a94074080b00704091b95a5010740321003052010310081c05902820340c1c019448118a584481c100300c00ea000103803002c1e018000b00d50050402604c0c803181464000c90a01c021b400c24001280001d42c451030000703100300580390000c100c016042c041c000d11460300450003000c0c0d10851100c0d40000f40b1425024000d020341d000347d605224440c000d0032041c40c0c40e1030040d061050a00649051140c0901d040380c1a913400a501100410f040342d0024660b01c66090980850301140d01c402c8920139064445800c0101e0342e5602c3c844c40c3d200e07446500103011642c04000541d080d4500c0250581e0090350610b11034600b54000b19040c03805200c006180c50307101d001d54541c80c0d100d1802658499180d541284c1006400d04c030802c010510324001e080d00f8104050000411181031107030200042d00e800c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 152421879 1250 152420629 152420647
    0x5070807142208190501110903070b0c010902120c09010f06020c040b12010c0203070c0905040312020313020333010503060103030c05031903050612010624020705130e0708010902060f 80
    0x922000090030f526000c4881140ca0400da0003d040c01000045415500740060304c0c00c810031402c1940c00690004001d400c4a905190343c8140e03a0300800c401501d199290711000c4056150b0109040b80d44410300042c0603210ba00b0020b2060080069101805120f64558100a49a03010550442106046601007505e0780400c00080a0f5110040c0c05030b415482d0000071601103400000070921144903461110405648210701d41c01c545c8100c07009000708012900d20381002c103a586c003e55001101000b040f9890b80d60b5008240351442040c0b00c80c03241740258400340c1c400100000c490b010bc0315402c01080e403540c1040301080e140c00040c4402030034403040c5e0702d43c40c08005050043e01c0c0c3c4045801140f00c0000060840180500000e503034081c029648618011007802040c0981c0007625a0f4418260340b19402c0742c1802d620b03041e07a0031080d085024070030740820940e80300e2407450801e401700e0b0408540b1a20380600d40b42844417641c080a026850125400010307100e4502b03440d05405c3c880c040b540c0300d644030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 152423129 1250 152421879 152421937
    0x5100c0903050304090e0d020c031f15231c031103040312411c0f020d0b010f0906050a030f05070f02120703050d0b0a080a060507080714 60
    0x9a0070080c11400b01103004030721030501d82d002451410710042242c4200b01c10310300aa850b880c2d8000c000341c06800151080b5010b094000010400c0c85204400164103081004000c11400d0030341c0005494000c40c07181c5120180c4140980001c5000482d0005008010700040c0303044407000c03400050030710580c01c1c1901583d0100340203031343c001e40e08400700041007100040003c02240c4a04c04801200074903907c0d00c0b0000381c400c02c004038480070080c0e52602c121080e400075040d5800040b800b0207034270b4003001103540c103041c0d0340100d8911307c00c8245e01584a6030080f042c807040e200e10044840c100000294030000c01980101d1100c1100d038203084c11540c074074025004502411410411681c5941418284207003075a000c1500c0f0820350003542661000103180c00c404269104412000e40081c3d0240300ca54114402030f881840e140c07000034030f00d10f4041c1c4d039260118109000d1400540e0190366540401440384d40041039240d2050b41450042c2c0c40c15503008280c0114080d403012a000141e091420300c40e440d441c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 152424379 1250 152423129 152423147
    0x12020909062106130b1b09130e01021602151c0c02100513050105100605091306030614010e01080601030209041401140a090512040803070b070e0613030b0f0405100c 72
    0x180303000d03500f040c6440743c4180d860500c1071500700d40060036003000441d151001c500c0708107001130420301c0501d4a0b52400c208009400c400c1404c015107560f94030141d10004003440107080d00400f10040e0000c8801500400161400c00616031611100400150741035031031603a00382c0c0000c1224000007c50320000b500c00c9241800248030142198030f03000c140448051580140161144640020f201541d504104e0711441c4a01e8171441001c1142808120100d1405a00a00a003601100005030030b0b940d940782d207010b2324031100090b00d1001c0303214010b010000f00800b44902603ca101c0c010683d551450340842c460550090018101502103140d0b202070364000e400a80000c19100300451007820710f211174500403c441d4504417524400c0c1c00703c030500004464240d5040f02c0209000d90708001080e15040c01c1454018456010040d000022021596800d800740180d0000c1c1030640c0c030130714110b150a484058010340f0605401c1c8100040000145e400a40c004000c859044003141e0389500d00c409540b003103d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 152425629 1250 152424379 152424439
    0xd0b0301020d020408100606090510111518070608180a060614010914090a020309030f0703030c0906020c0a0b0a0215131703191104080d08071202090906 67
    0x4000202c110107401c160700500f06a402407803d541000b101a846171007118014031400b00031544040040103640740003542c1450504003410605402802840c0342800c02c40b6241102d0b4902800e08103111a00380880701c07020410b00400000c2104034101740000d82445001008042800c2d120601204026400d010080c01503601000500a481e2100549804d601d01001d0b1103001074071034140010110b0711030118803000c82c0040e144000c582c40e00e0b403041010f540020a0716082e0311041000c0303402034540200400c08140070f96400200f0380c2076054010040b07402a030144c4115845201445070640d030781010b010803038560180a40d0f4031a03113400203a050503201ca0b0381e004030310804820040c4003100c0101007031550744504e01c80c400c2000703610780601c030b113010680c1c00200801c481c40802d00440310030b620420907a82584045401c190b40d4804c3c3d80d281040c0313044040300103460007090143c400c0c0c11548001c90014441c03000c3d81044181c1c80842e446840092409100e00003500d00385000c2d00c0310441c0954482 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 152426879 1250 152425629 152425631
    0xc05040510030303050901060518060d0b010305100f020a050a0c0c0b0a0e03070806160509150415020105060102060702190204110c070f0e1014010e060a031a150901050d0b0301 77
    0x314080032088008038482c80168040303402d1200148807100c040c0305481c2503a100030075403400180c1c41032184030702103c001c100a070800d04160322000490f0900f003109000354400d4004001600d442030000f010340c4e0404400c21005401441405d0165412005a42c140300c2d06262600d0314bd6864149900030820b00c0d44242060840040c04890141e0311220303000d64080e05808036000b10340e656203101c1d40c8d51006c03942c00c028194040d00c2e0000c4940702d0310040c980f64030000d05040755004840030140d402d07803065200c44954043c030785243d40443d030280281a40440c09001a11047c07800740d40294581c8a2614081d00ca4500384a14a0456485d580061915021103a240703407100455010503a684150b030140b000c80c080521800a18610100c010a10810308c4c010700c88949071500350341c01029a03820a501d8144201d030701100c2c01d1038035000040e101d240740b559030110314001c1c615055070007203040400c140c2c058041010480512201a400c95041d0f940c00e00c0c200b0783e10401d0102c00f000070134805113001d80c15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 152428129 1250 152426879 152426881
    0x411010314011404060b090906060d09060f021b010605090c0d060b0d0213120317040503121501030c05030606030f09030c03070f0308011d01060f02030702090108073605040c050405 79
    0x101c00c408503d060000096508010f880e441d82d100042e9030103078428096000340c00000140050600c140503014001400e5008640ca0020356225010303107804400701201d141e03010500b02c0303222901500101020306048001c00c000c500700340c00b25400c3d650040c841c41942a00240c001485045c6030b11220007406081d000d40d0700c5407960f0382d904010303500140038002c0039101c0072404103900011628290200307605880f117240701c1090320400903201d030300200140c070075020500901c140014402401480b171128004100f50780000c03a0005412a008a800a03080220a00400c900d0741c640504407500b10400101c102d8041e0740d12242245507100703a05c151f802c140000300d011800c000c084280380b11a17030b109465014407130380c0307510049800314260f00000c0300e0301c10001c0040202e80e025040c40101202203105581c0780c00200d8000c071300ea011082c1d00503105648125070410034404920100801d1140128030a81d00081c40c0000c040004003080d00b0418442e0b44a000c501088205010f05c40200030141c014801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 152429379 1250 152428129 152428139
    0x5010305030a090b04061e03091a100605070b0a1503050a0305040905060114070b040c091103040b010510020d11030409230601030b0a03110f030604080403050d090608041101031401 79
    0x182d07045072441e5404038000d010302040a14510095800f0740c0c1c00c42c0d40340240c55004690401c15001031780e1120080c140e4400920000c80d6801c44c004c4140849a41c40c0901e40c101400c070541007520a60201c0100311060148038002078480440b0368110343c01d50b40100301700314242c40c580d0340390b03a80d030b0f2008001c2d105800740b800825400c5070190007110403a640800c60750340c441c001524010440000309040013402c200d210b00241e00310318110780160182120481d020b485186000442e101d1052017480d0f00c80200c20081000741d41d020332409050260b50f021541c8a800c80702950300c810601c070711030074010380241d048400b240c00c00030b6a008101c0010148082481c64941002e4200c4100544481c61381038070002c2c04a500901622001c00c20192060740306a183d82c86181c5504109207149078459465403101009580801c06180114068000565120725604c2d00600e08031200007880207020030203004000f880d07001014035520940124010710b40214400040340140200c0c00d848105000382310012030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 152430629 1250 152429379 152429383
    0x406080406050105010906051219050702010e06090309210f0a0606030204050f010503100b011e030e19080414010309020315190203010f29030903030703270803091005010305 76
    0xc0918011241009541d89950044880c00e03800d000d0600420410070003034070121903061041d0744c0840201090180c0841c140e03690f80540320b050302c0c0140145c0d104d568011762000240032540c1c0005110700118035080202001c90450502c0c0402e03504600805032000f04011000c0c03058800c500429010b4036058602c40c41e0020080c0a40d000c02c0e40100d03c0d000016002e260b80d885418180c400c010300505000f2041c1c24442d0141585640e441d0400c5020154280c2215503580d0b8078000e544c240c1c81c0801c0030070700381c40f0300c3e0710301042800180402d1030005070302004175241c182190151404250020388035004040160003404841c0002034040c85450301d403a03800f4509400300c3e800385461800ca07600e0404442c880609901081c0240d000c0400031a00400501c1b01403035642d2000421428260440070540842c802a07420486c0c888185800000c01c01884541c1842504800c00305031011b65101001c143c240712074103811003401801410004041170442804222718600d60b01c00e0030040c411981c507403910903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 152431879 1250 152430629 152430631
    0xf1b0f010e01021005131101031814070e040507080d0804030509010e0a0b07052d101d0d02100612030203030a090c050d0320030705060718170303180105060102100f0f02040608 77
    0xd6580300c13107d010442070f5031207402403000754081c2c9202d2800401c0c180c1c541d030101046600404285224200c2c000855413000780b0402e201324003171406000c21524014440d0700300b030840c0e941794040003644400c20000941013001c0e15440c0900f0f280c116039011080d8040b072007480c4107070460001400c1c04a03c103400c02600041032201c00d481d62440f80c010300310580d5005100c00000007a142d0f160043c00d0460b640714110360001c0200c45c110002c4000f8036000307440241c10304c40e0303c9145900580050102440300c040c140200781c020200031042a2440042d070720000e40f00d010280582c91120f49a0341c2c0503007404455603051303001d080e006140411241c3c2520b8080d00c4d2401e0785da0304807013180710030850490b01603000c010b45040a410402510b810f03601d4420448044000c0c116540100c0b0b1821404036045000704003440400c0145c500441e40c0342010740710484111040c0032074440316130400b01003080c00d0b40d02040603041060744090101d6800c0c940798004010b0008540382c0310215101081c0062016848003800d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 152433129 1250 152431879 152431883
    0x40f09020c070824090a020603041a01050a050105040324020c0c0f041b0c30020606040911010302090a050d06050106080109021608030a02070f050f1b0f010e0102100513 74
    0xc901c01e030f41d501c00720340e01e48a007000c0300070100703d480d80d14403da0b050a03910390354810032007419502452059800580e0035041541c040d01d1346152702c05c0a407081201115050702400003102c0c04244140b400000804d58402c5010051014a04140c0c1c03c003101810410480e0440b5516001c3d51922240c0f40c010340c3d14202482c18034800d00c01582000458142480b910050410401856840c44404542601c2c01d1811030000c41e0403c407081c0c1074a0011880b402e42819850420801c2105402e252000925000d0003420f000d220720302d0b110303408002540d00180341401000c2820003689950705030300080c448091540c00660004001c240000400c181544551306071403007512071158990300d4030000c104038011026000d4030745015104032000304007000003a5070f000d0705415001d46002601e0b030312810344240e00d0400300c440740d000111042c0843d000344441c032195035584582c03500c00d0f41e0b0f00d0005605036050726000d43c188001003c20400d00e0f40f090180e101c54400403881070100f41800c41908c5c449551406003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 152434379 1250 152433129 152433133
    0xe0f010f060501050f041e030623060103050907091a061237090f02030a0309050102010f1404110a03140c03010605011704020f0402040f03110306060108010501051608040f09020c 78
    0x1002c105980200b082d211400103104841d801c0600305240c0c2c0c0800d500040440c0365403101200d000000500038064009945e013184166400c0304003003182e040100c9000741c4502d06060504081241d442c9000424600300c4191034004120000400070280c3c00391102d0303c0362600300800065000e00c0da82104802806030740e440c1281c2d003010000c0041010300e24540d5034040410001c04500320307000071864010901e2280641106800e5410315030000b0318050361842c08402081407001d04000710368081c480c030a030b05070390200244001b036010b12000c0c04813000103100512168403140005200d844010070032015641c2720002c08000c0c840c000a00341c0d00e20741a4a0503109608184010881d54030800002d51050304907510484292940c5d400c00404950710110190095401d0100258030007405403060300840c0074540041ca071201074402d05051100c02008103042c850341e2401081140d0f0301008491703642d541401c40206902652800c8002c5101da64000003081003010004622905035034005c0000d072404c402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 152435629 1250 152434379 152434391
    0x60d0f0e030d14010f15031e0204090e060606090d020904060b030a0c0e0703020703051213170703030501080f12030703060339080607050703020a0c0608090708030c0d0c060e0f010f 79
    0x164211341c4040b81c0c024040f951612450158107540a50040c4124010410f020231949030801e040908a070800c0d070200000d1600c804902c3e14011080c80100d402072800e9452904d80319665002c02e04000d50520000d004450640014040c4403081d03021204084006064508111003070401240c071510354052000c28000c5c503000716080314020310031200080e40c161034482c24643e0808a0b0180d01c1c0c40140342c1200d00880c05503140005542d40c400904800741006d286e41ca0300d0b89410000c0072140143c0000110794060401d040c54100300086050800000c04080703036480d543c420044000e016135610081c0f0074400090061118444130081d100c80f40000c804501c3c00810f46450401e02010501c900750042d040b01d03000c81c03083c52141c030003410a14040d0044462420441d5640d00c1c81e00d5080d8042c0b00014007000500c407152a0034004e420082c500741c0010b5003850104090b040d1030f0740c020785c0c5034030030310000755070480400c20b05400c07002c0801d80400c20f652540e001079460501801d0214610000145841 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 152436879 1250 152435629 152435639
    0xe0402090f0403020a0f1a0903220503191704180b100e060906040f0906030302010c0c080306061309050f0a0b15030a09111f09090902060d0f0e030d1401 67
    0x114100b441160141d0080005820341e459250b00c0c451040c3c5c01799100316070030b9003038004100805840c9000d031104200455807056021030300c0a508076420394840862074440010023403950f00242003d003022500210b4a0000703c249885641c03040c00e200344040d05000070400082241101e2850321207044401c10078491030460310104a90603800c0400345004c5045001603590718141070000e0440694007a0101d440c1503201c00b80c4415001456100680e5151904024001c066080c040c05852500c242000108901a95100c00c81408010240c86c001d07180400d000c000100c00003800f500904400c1c2d4100094101105402c0f102141201c410f580c2c0344c00c2500d620b0340740c14034410a24205460300076190070354841c614040e0181c00d9407001a584082ca07046800700740c0e80d40109030400141ca4180b50710145201a50140a107036043d40440035161030300030114050707100c02c1c003140ca1880d5a01400200480c420082e07a0003040783c503140d0001444040f655400b0703001c2c254030510b1200c04009410040c0d0b0303030754 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 152438129 1250 152436879 152436901
    0x201050705031306050408092e0507032703120203281218020316090c030203010506030103020f0a090222090c0219142b0206042001090506040e040209 66
    0x644582a0034801c0b500c03c100410020307842250004c0c82200780501d030100000004070b80e46100240d0103101f429100944915150a80c2d80f0f81501c800d904009060141c280c4010749a0540717040d940a102025103000071040c0300b00d5040202950b40601481601031714140001d68030307040b002c08440c00300b4800d5040940783e940c1c80c010340d503242e84c50341d10041d502501d0508032000e000c0b1102d4000320069541084030045e078040c40010743c508103024082109901e4141d03400d0586214070840002c4c54410801403180b501c41408490550f07805481c803001c1d81c3c0203e4081140b0704003551240da441e91011036040c034549481e44007141031401d100038072111a0745510000c012039205207c00741c00f41c0e1005648020105c0d1804071400c9560081c140c24140749812070b14070341800b41c07800060030401000002c0b803036101c002c45810f061548662004000601c3e2076550203101d044642403243c40140300c4020175a850b231103000114060f1034080c100c80e4070740350f44040900c40f0000030b94040784036a4982c00054403100759 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 152439379 1250 152438129 152438131
    0x3060b1c020a0501120f0e01050402010f0e0306040f230102030603100204050f12030c060708070813030f051c020c0c0901060f080606160210110d0f02034303020105070503 75
    0x140b44501c80c0d4980001541c544400d12031040c00c041d11541c4000304060715125010b0030421040c0040703107070f14080c400109081140302d281e105000d4030302c0c2c13000c50b0b90700d00213400d41c0e020b80c1c010040c0c48000041d0034402c00c682c16030840b0820407030301e000222141d0031043d00030310301584050b0210b402c103516010519081e801180100c90300070700101e91126042c5400c80011801d540118140c9203011a01c002c400d0500000300e03000000306000e801403040c001e50145180c0d60082d401c480304002c111956034002c1c00119410542004c002e808104400c600d07a460424035184d600c0200308550f640360006100e5221501040414403424440c000050114050107100081800316680c503a501e0303907a035042108541249400d03102d0402e0f80d5905e0300040e2280004442522465200c0800c80c07141320f68003510340a540c0d00104100b004441c80c00c03501c10380002c20394544907400041000c400f40440609140711407000c0241113254401c09644400c010700d039401e500014040e900900090351a654244d0303c5100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 152440629 1250 152439379 152439383
    0x51203070305190e09010f060e0409020f090601180e0a14010f12060f1802030c061905030402030a02030d080703060902040b0a03020a2c030c03010c0503060d050c06030103060b1c 78
    0x900300868540c6403424420020110f00c40e00b000d400c050503010100d01c0a0b0000d0300804401148400705107d02900118014002d001c1220144840c400390303804a81110001c0019502075050800820700683c0500804070078503101c91091820a543c50a08420048050f942a005946013100c3c84114003041001d0354142c0d0014056104114588554442000301c41c8000343c604545c1d80c480c408204146024400003200103039062030901d0141c0c01054206140400c503540304403010000c1c9108060291000d41c030286182c1019600c030340e40c50010a0401842c00402507040c00307914403030210560026039003801026a603508104150310b901e1100c040384980e014504c02c0540034800f800c0482d205e5002040410410b01c0c3c2681e2110425805644840d98150000009840c45c150885a41420003410202000407802802070302d40d4000301074200c4c48040d0040303019085907041c11040c00020000301000c5180640265507a41c0c1d07a050034001883c5a0300600c0c858402c00100314620700e54508010303c216 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 152441879 1250 152440629 152440637
    0x80a0306140a061b080d050c0715140a021813020703080106080103020a05060705010e2a030307021e210102040e0105060310061b08070f020324040809120d02070512030703 75
    0xc00305100d21060740100e0101e0b051724041003d002c955185001d014010009410880d407219035500c0d00040781508503101e02b41d441d01d001c0001120f6034140c00c1480e00005152001030b511250155542405011444150303003020b4100102030015680e0f074011b005450081d50780000d01d0341c0b21401207484140c28403010f984503444540500040c41d00c100140307619403140700000381c0314400202d01030030304800d5500751910009003084409108005071146094030000c501451401881d94001a0404070006140b0290b58540900c0040351322502d10f0340341001112966458010312000e1824040d40c000e001e03a848030710150000180609104064902a28a8400014426091490031110380b444951085111071402002030b020030303900002018194061781d9000c602403403500500d4038010380485074140103204d5a080440104011807169082030f1310130356840c3d40f06005800500b81c0f926460380b000b1140a0b0740d551007201a0006050011039500340c0e4032100000862641c1d988030300610364040e002c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 152443129 1250 152441879 152441897
    0x903030a0216140a060c02010204180f020c19121409010c0302190302061b0301030309170312090606030601090209031b0a0f15031104120b070903080a0306140a06 71
    0x44a103640180103200c240c46842c41010841ea1a019800401e10f40340860b5600500050703000e001040c01002c41c3d81e405400207615080c9444544480c0c81020780424840540d20481400e00c00b21070b40440d06140c80f00b004850000000f441003142c0014418012281c9104108941d00314130300607810940440d414110300d070700b0101000015100341e44c4100048046000f44084850350201040c04660100e0180c0d009001614089003580e02e00308000c2c2400d48500307802d200410010303034802c000e41c040c0c59601e40300340104038282903058070f0f5003e00c0c00d80e08100801e0104001d295030000503002e200e00811422074525980c1d54401a04074812401410b41607000079602c4950141110702c020612003015211300c9010341d445034160444519600308650100d840040e0348139050780760244035088203030001c405140511341800f600c241c0719a800010701e04802d00b000603007041d0041c030b00203000b1034101a01664a040c4850000d0042c400e6005484949030764160a09407070412a000000b540e8003511010b4003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 152444379 1250 152443129 152443141
    0x60604030605130803182a0118240318030e0d051504030305040507060905100f032003310602030606070503071109090a050606090903070609050703031106090303 71
    0x30b010000c1c44140c8001a006440d0001a20072004500c5004c0010501010900c2d50f44450300301562020680480d80624025504402c1e00b0503030304944010909040e50b49480d181032070900301d5000c3d03120401050107810306584180c88040da41c800d211403644c3c03c21000c02541400c0070304800030072026001400e1180e042010b41404004400c260740900101e41c81884852140514503000302c1e01140025259414003080100c10441c0801420190030302c4e50341c0c0381c04c10001c2030312000d06501150801c5007080d10070301038134002e80c807895050840029521a00480040c1c498040e07001303907444070070070009500c0f19a940941e540340c0100340403c10350240f08001c070354803800003035080074009580c064000c0108500190302040108000e52140600d0304030300790800b00300810558000c210400540080c080c20000030310101340d01d41d01040444801c1000d03240c0c903c1c1c0c0f41c0713180600440101424a424040814440d001485c10202d030b00c41e507100307900c03a400122201c1d2956001e46000324158010710101c1c030307 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 152445629 1250 152444379 152444381
    0x9020d11030a06140a06080c0703141603180b070209090c060c0c09010605030603061303050c071e0504090323070213090303050a021e07080c0d120b0301050606040306 73
    0x4060410810100e40c8110020003000d5941c0280c07040c600702540ca090401000c1a0401c46080000d41112048645803034854003500c4040002c1403c145407400040030130825018411b2010207a00071071807941c81d4290390810f885002d40c000429000700705d040640036001d17101c00b00031005030361110f02c0d19410440075034213010545202611440b00d9025104822205807101c0024042d150914801081188407080c140414500c0603008141004000c008010250710300280c05a0410b002d010800d00801e140d040c2160140075505100580b4000d44100280109460312385160600006107601125656442040300f103030348151004000c11005410030701401c0c260260f04200a41c0070034054502000c3e540011203d15860103c045411750300c20504090541c944500d6620001d403010441c50552822160000c00801e0b21015030702c0e420014042e0100040b80d001e0324081c200103400c6440720083c02201405009a1401001c02d040c5003920044161a05004140c0110f4000d803406107020700f140c580340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 152446879 1250 152445629 152445637
    0x60503040f26180a44030d140606030c0913050c09010207080a0f1205040305010c050c1509030d0c120603061e050f1501020a12080714040f050108041a040302032802070902 75
    0x59032200310304a02d170f0014080c46421110817082c3c1c1d8040d640d5403908014403011603132440074401c008003401c820040030382c03070710002c03070b60440c0d1080726254842d001000015480e01d8013000711a401818130061201100030f03200a00740c0c00d1001d0b0280d6003083c5d02e1309a2036035200d945900c042c2c186c0c07034a441e001001c00d048a11101c2100c005142942c41d003522502d41e0307401c0d21010041c03000010400500588410310600121840464400c0b8070031003400c2107206141e49010b030642c908605907842c1e202c010342900800d00c1614100b04070406002240d030b2401c0c10300082c07160501103050704c0d80391b0003810b036220428401c20703203c0c1e41d0350707681c800c141d88480e04008483d104a2002505500c282c081d0500480d4003640c0ca505982000e54400d0507600e040c4038000c1845903c1130100301400401e00c400e02020940e95100e4090382c1d030a01e4511161b40c0d03a4200441c69100b030000105d501d000c3d000510050660210081000c003031450b55119101c2c03010b00e105410301090903460070060304068010b014444040d0018 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 152448129 1250 152446879 152446949
    0x702090f061503090703031409101206030f06050a1803050301060e0a05090f07110102070201090515040b0a0c03080c04082d0102040905041704060503040f26180a 71
    0x84881d030035460300210b010b40c03090300c0700d48282d4843c03c0f0400405070b2092200004e0300704c046240e405c000d524004034207134410040005043c40324030502c8010b44415603003c100155080303120601100500d05094005210503a1902c8200d400c1800030451000a060b410250700d525540b054036581c070f480021648018218a061b5100d070118030000340517502c045900e1701403540360149210030304004101601d0103078a0000c3c40000e90062088ca0301507a00100080100c403400d0703c2d800d80c6151200b41e002d10500c1550010043d0074008a001442194000412a43c3c54484e440389501600c0b00596034810340a688550504c551008000b04101d180350424869505904540d6503a280d1400c90940d0036038101e130304040d40c001e5643c0304020a102c0c022601d9008190450301d960700d0700d41008801070051000410107000b40084030f0250f020401440c4100c054064490341c080e1041840c0a910b240395400231031060326811365406031041c9440c182c00100c04403012440d19043c2044080c0056150174507521308 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 152449379 1250 152448129 152448139
    0xe150307230c060603060c1c0603061d0c0d11060c16230d03020d0809030c07030803010608060a081c09050307080607020601060f080601140702030109110a0801020702090f06 76
    0x107994210071030700840074803a0301000105034461296240140c6481c5000f0f10142c4244e004c40180000c6562800454008a210f480000c036403064049a40c000b41801d60300085c00c261804d021081600303c0e00745240aa004040c003070301c01d05d802400401041040494019092419000d6011100e01c3c020009118031000031090304c418040304101507000300f10691200768071209100b20209034150300021039520440407200c4000303210381514000d58403154040d0300010312200b900420b41000b0b0410948146202007011a200240c4134a0100d007690001e2003110086101c1502181e864a80030b0314078425160008000c041d8180c186a2009400c1448850501403200079040803610352401e02c40000903100360f000400c41405c000800916000b41607100c0300c1005507160039117801540c05002039800040074031309048000c090b007c3c40391280c0303e8500d000b0760561901d03a06000308020307a102d1205840f0300b04c0d184100380d56211060f9007030f4072030100025441540e00002480030510318407075076040400900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 152450629 1250 152449379 152449397
    0x7050a08060f1801050f03011404020d1505090c130b15090609040515090702190206090402040b0a031d0a050303010306020708090607110f0406060c0201030f1e1b0e150307 75
    0x10105040030100009803070360b03541180050060f4141100114000c907030070b400030040704409c81e43c1c00c1e05826010340700034480c4d131a000e20001840f490750200c14056107014403c00050900180e081c5d520202080070a000321564083e0098580a03840345500d0043c1c0908007404401d5010500c002d0f0754400e41d0030b264403240070f0003144cc0b983c813140320f641d103d103c0c1407a0798040c0400c5a4200103100c0b00003021002150701110703001c00e0b81d00200c01800010b40d8151031450721003407103a00040180c002d5400400014802007104100304e80c2c940c01c500b2441c40002c0740100002008811207403601310a0b40082c18552040004000040981d402446054013949409040000307000c00201c007030744140c2003074800880400c02c002041c605034812800e403440440d81000041d20707000d005001c6403226200079040c59038840c01c80c1ea00340056041428071425441541d50460710414000000f0810242d00c0400b96081481c6005100d009503031141e00312a0051100c1030008105503c1803880c2c0c00209550704002d4000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 152451879 1250 152450629 152450659
    0x1060b040b03070f030f0f020904200706092d021009061409180106090905010902092b05160306060e090a02100302040f03080705061320180a0204030b01090507050a0806 74
    0x1104012004100040150743e9914000c100400d88000e804009685442509245905032f04034040300c044e10741c403d00200301e251090900308112a10f01945c0c045088100841218101000d000c00d4007aa100301e4905a803840c900381c0440b0306071184d01605000c101050748410007503410002901e100c5c10f000700288810b020300c1510f14407082d405e0f44500301103441c001003070102400b203005035800b420007450214100303240e000004030021208504101c8082c052040003000d403040c03000b02c06050b50028201c0b90b40001d0003000610711800c1c0d20042d07500c586040d01c08540c050110100602402e40040202441642502000f0303e480111284409169003080300264440c042c01c058802540950610313030312200030f03041c50380c1041c074000d10702c404600c0600741c0607002540e008283c03008042044080484900c419001c60300c1e09542c078910301c500b8002a0700300503007010541c000740705582c8101810100f42c0d030783d540000c1c141c0c1c4040d603109010900910038944898404c6104650251000b011000f03043d02003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 152453129 1250 152451879 152451881
    0x20d0213020405030f0a030e01121401060f030e010501080715050c010e1006080607090618121101090e09120715020309070e0c1204080d140a0c0201060b040b03070f030f 74
    0x180c0211000c5402040030011840d0500c0f0360452441400054240101c40d980c00502072007003120b400f41840017107a40d02000a155510008182030101035600c03144d6101c0001500074030040003800000f80c180702000c0400c545c1070040e00d04032407002c402040d00314148600c0c2080a14488a00310401000303016403d95140240281214030f58508081d140d42c058003044907054500c540c11420540e40154180b100481d030000d00f81e01110801d01d41055024040030000300c1e004078542c1b0000240703840ca1501014410741e0500010300c8007090705e030424030030b664007074103207507460100c0d492003d54001901c0001551025001000c20602c2440e80da11a55400f84420089820903904800f0a500040b400e00c40c820114240b030303800002c105c0550b8244110320356060224500108010054603021956001c11a840e4022014541e43c07000c44000b1032500d9003000005103884051000150b0a00d0000540c0300c15031022102628004080d11b0715555a031401500d0321029405c1840c10542e0768540c019800413a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 152454379 1250 152453129 152453149
    0x90f030a06050919030e04110c0106060e130501060801061103091f020f0c030a020d1109070804110a0e0403050a020f0d05040602100b10180317030a180308010909020d02 74
    0x1c5141c00107942e00b01400700e43d2419034100c444d031100302c140352680404030b03421a0380d2000382d01c42214081800102115084120300541400c0584c642c240368000c180740fa08203c50f21320510043d03520301103044009603c0c8080c3d070000e204001c04901482c0041c040207200d001c1000400803d00b046034a02f0a0140c040b0b0680c003403143c51003070f8014020100e11a200d03810b122000c00c0008010040003210807241c0001d4803000c18400003803250480702406020080c2c03070b1110704c0b01100024841422441d10040240601c902120100d540114105150106141440001040c0c0e0001c121140c202d42d1265002c0d1107981c007456281c4194401c80c01c4c0d010443c04200248110641c40b6500c25072540e24100000e4175124400f03c0d000b04250606030b80898030f4480504400c048501880c0035103440751a080c2c5160354455580000c3c00131440c001406981d0342002e002580030b00c800300030402000044031324203410786000303c20080c001084200100881042a0030078003449000421b0a04101c0c91640000c803070800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 152455629 1250 152454379 152454383
    0x804050307090e1605010e0d052109010909110d09050312010323010e100207081204051c0302120604020901020309060d060608061014030a0204090212010f050105041406090f030a 78
    0x744882c07591a555009108a51132a00903410704c20301e450522002074041d0401c410924040c07100f414428092050800010202c4c4c0103500100408902c084074040030b90707109001241c007040181e1400900030b04c040c4501c080102e5840e0b003160902400c00012009000c0241d8192242c1c032007440b2504401d444007a04ca40218803035100b21200c0510140104d02c00010500440c00c00c0c0d2401e100c147e0b4800d4045049040c0b1103100c1d40c016603440591030310a102d40202c031420a52040c4080c10401041000581000c12044d2400800c0d01e04c03c54503411001c0e88151904015825984c002240c035604054001e0000b1541c140140c03814144401c001c5506074010184002003140c540c0800c02c000d03078001c092180c00031000c0d9900601006602005403000e401c2054041c3c98010010000c1c104030502e6055402503c0080c0040d59501d500d480d0f0841110401c3c00351540031500d0b200000341c6036001d0340c01c860840d40380c1c1da03100f128240032a00304009a0080030101d600104090f010302480c0e0390600645810718 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 152456879 1250 152455629 152455631
    0x1009030903121d0607080d09020111070308040503070b03010b0910020f030f070213051b030a09020603010303050307030c0305101208120907080f2d070302130b01080a27080405030709 80
    0x5000206442043c40c1c1d01c12140d03010b40f008010080103c0d5030320044440409542c0e901154000c0d8900c0101c80c501c1d21500b0040301740c02032210100c200000100280100c517011006c940141c1d0b01e0301c20103a5584000c0c03080640400d402c20083c1d003142043e2186490320a902c0c01990540d054880c191811944402201031003840002080011460500b524806010001804020a260040404010700f4100c0700504003200e000c000580d00e06101e4201c0d508065000c2c1c4020344a5a691401a005400580b40300020901384141001580d11070b02c509841840c401c0c2070542c1c1ca070314041c095000a10000815100c003001001070b0007107040d0400c0114000c081c003034010020b4a15003241582010882801840150440380c202898808090400280c0c26141070400b900d03528404074007854004079520080d04070150251200c00782e0f507540e0182e01c0101080e280d4100550728141c0c00300846588c0300c000340100000c002402c18802c80d01c0703600200148291141c5141039280e80000b0301d0100e031640100700503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 152458129 1250 152456879 152456897
    0x2a030327090606021c0f0c0f0f06020706180312020c03040b040303090f15080f061804030503060102010b010801030c03080c070f08030702102d14070b07020607020d02100903090312 79
    0x60f40d1304025000a00d880c01c4c041c0090180c1201700103002404c500022000c00a1f04c1d505101031006402e01000003641c440f140344805210340c0340c44c501035042620b09030f034000e1400505030506528601c00030895a40f60b0b0301c14134000f03c8030556030005d4000300c0c203926051100307000c0400c0d078010880092002c1e43c0291910550185083d2200019020b541c110324007511102800c0203015420400403504006445004cc18a5580303101040490b6025140300b001c110300002803105040e0414015130007040c007a4024003500d15640c0054401110a200007014082d0401042020034194000707000c3c3e00c2c601000b51a040d80d5500c2c04030010300002d401034111a040062440118580b405402c008510613003821820b003581c0b00c0025030a1081c0f4a04079007455500c00c21020181c1c4224107a0781da40b0410703034285442e1082800c1c00c410500c02224204054440c41c0007064281e400090b40a04200950303008068402c81c01441101401d2148002c506120300300401200188521072091181d111a035141d60364 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 152459379 1250 152458129 152458139
    0x6190f11070215120402100509030610030b010504110304150b06220e010b07060f110f070501060501020c0904060b010917010b1f020d08190501030f2a0303270906 71
    0x70051070448220036200200240c1c00000146071341d0f960700c40d804403564038424044400564140c45084440c41d4540034040070001282071441d07840f82624000d40d0381120796a215001d1008644030f0082c008480070060000500145008407601d424502ca0400461544811008a00d1a40140c0c1c0080314400351466600c0e5050b140a81c540c1c0103002410300c4035419403428250039864460341d030300546080e0f01c45503000d00c420066081041e02c010714003580c59640d20b548100003580d030803d14085540d0350a0080005140d1320000d00c84c01510801011600d00b52150f40c1da10004100c15000c103030520064034000600340010321110342e000f600400c00418001035510400c20b889102c0e07002901c2c1000d07030001c3c1120f41940028031011043c003c0c00c0031996038961015013401c1192041e5140d41e154144000801006206401410b240b40718408403684404044c9400c10404440d4074048000b12040c038080011030306c41c2040341d4101c12025604503800850050b4200c4184054018114041c1c4484007042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 152460629 1250 152459379 152459389
    0x3070c0605121e06210318090a0209011707090e180d02070f230a120510140c09060c010509010c0f1403061002071e0f05040e06190f110702 61
    0x291094044040409010b0768001d14140c915014101c1c45c09500c0c3c03504492503021101c22480b0441c510388080340e84502070380500c54042140307144c0080c011000c00f4041180511a4001d80300108030503143c1c1c2c0e03a440c840c40070050113450014940d104007d21014000380313450503c000c5501600c040130b0b1111240d02c4061200f032a005500f980d0b007045512a500c10041c041440c40c0c003009841d142c28031001044c00800c504060654407010041d030003004440c0000d07101500220341581d0300d04c140c0c203440c40300c031507041d07080211548007460b0003481507418006800c81401c840104407005004004a082901c0c8501d0282190011611409269900d176240750900360010034110350940140380c401074241c0c42002901c802e0102604c10740c01140d001e503103910600c0c020f009240c09001c0d5001c491842e00019003e40b1300e4288a4411807940c00204d0030081501d0500c1d009044485c504c400003441192600704552500c07801105192042c0341ea00d07101507100c80360a006070700b44440d2925829440d1052801041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 152461879 1250 152460629 152460631
    0x9060e0a030e01122309010e1b010503070c060207050105010e01090207031e0c0f080307030605040204141e0d0308090606010302070203060112170a05030901061a07060b0303070c060512 81
    0x44140e000c40103400000358841c01e407282044080c44c103070b4411240424504050083d046200b100d141c164000b0700007080c64900c00c0b920544181c8020f0004601c00038410303444080c3c510109600401d00c01482d4282e5000720b00541c6c01688501d4285481c14054035a94100d0304000e2080f1501e9445000402c000ba006034405070142400e07030411403030b01c1e1a0347d901801d110010100e403205880d00103e8105e010340503d401c0d602258020300302d0510780003145821840717544101ca5000c0424980500130620b03090501c00d45059606126034032007020300100c2005030314110f01301110401c00764540d050f00780c1c1d1108540c0702c65140c841d0701d07a4151810f1070342545090410013044641013603c1407260a026075000940581198a0f401d1807940c80a07140c24060040399040c8225440c4440008000040a5020008502c54a28000200100e64481306146103417440164112442142881071402080c003e0741300d00150b940c0202128603161f185d90b9016500d2134250310120220310080b6114032030320410001c039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 152463129 1250 152461879 152461901
    0x1a090405010b09011211120a090b16090b03060901031b050301020a03020406080604050405030712020a0605160e2e030603021207051905030703110105070c0e0702010e150619180906 79
    0x80c0306d41c0c0c890f42d001600e14014642141100003400021900103541d5620121a690300031694040c0e51900e03071081040488c90324905000901400400107921480200b134130b000e008002e00011a5174615201c0d00b44c0451007035040200b50000140000d0107a800344028429110680c60150f1281d00d0f110010b010404028100e6020380e0500b0200300c00280c0100440d03200075881a1322014a80d1421400c9250445580b4000d0485280c04180260701a1030459841110443e946a880c451042404c0c0640482078008100e9401e412060704d8081901c40c0014205d115110714000981380d07660740000d40410480d48512002c0c0c0c000328010b0040382080c0c07480d500384c0c8807204103c03881c10b490040425510720281c03002a080206410007292260300c2002260300317043d04250184e0811740c440001e000300345d03402c1e01c581001d50319000307000e4002d00c0c01190031b40d1910780301481303a2610740d0345070140309da980c140c024017420f010211100402c00c00700600f00016070304c0d81c80100168802552400d18110303210750400c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 152464379 1250 152463129 152463131
    0x60a060812040603150b0705010204170a120320070b0615040b0f0306130504051e0703020d08070303091205071109060306060d0c0f030302030d0b1203041a090405010b090112 76
    0x5050060584070781141e044802a190019111004803000c82440c10326030421111001d001620005202d415000787c001e503029030305607030b41c0c041560300019a105200314004001c80c5001050000c80c41c06940102c80003010550310040c500d2660100540d243d02800080741c1450094043c0040c2d07090035042140703100445441c0354601390804400040030f003e9070440304011900080022460b0302c42e4141503100080c44d040a0003541400d00c1c0caa610740050100e0015940081030404503609000143c44003140d40191a00f040400e00d51140b410b198403200b0150301f4592a154074100041d0081c0c00c1440e00160366640c140c48150741d1818020200c5140346440c440e041c401c040c03019540d40810050303000300d4100e4030301e41e48042e28a003440c2c240d0401d42c01604040c200850001c1410f40100042140c041090320402000300701c0c004100002180d56034503841d5510078001442100000315108804c8039035a24801c2c14080800c000500f0785400342c1044040315000b03c0d1a00455800480040c0700c003542030b0f4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 152465629 1250 152464379 152464393
    0x220314070b01230102120c07121a0f100302010e15040e0f01060c0b0105040b0f1002010209040f050103030806010c05010216080901030c02150a11040312111605010203030c071a0108060a0608 83
    0x2000075500d4101200102d11350386c0008880c0340700309007042681d004101c98908411004c60600300140d403250104c02c00c0720358942c00c000050700400c0041c20a0b2185007400c0041540c82d06503001110081c041c000040d400c41e0a6070041c3d0440120300028000524a48003a007119203000040301d80c042e00103a200c0401d100e141e00000c400684203d200605559040e034001a2203405140003030644640d2804990b000203030100201c07003059064000b460540c401381c400b0302001d6400452682203c1c0240b00160010f510640882d841c3c0d80328031029000c0314081d100240c105030352204020382c0c1514005003142c01c08400140d040903540c0500490b10f0000c11342c001b03052131107220309134440300681c02400315200d80d0b6a604400b04208090054402a40d004034051000c3d05c2c00f01d401404030b08011404a100d84504985a4181c50888481c1419200c041e800b0b0360640e200e007480d41d0840d8010f00c1d01180d0110020004081140000398400d001b00203180092030030381403004002d004c46620340c001604030b4001807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 152466879 1250 152465629 152465699
    0x3041205130510120e0309030f0a080d0b1306330e0f01020a050115080f061501030513020904050c3a0c05030a031d0108220314070b01 59
    0x112001d802c45a0560781103604001c0443c04030b80051086001004407850b00b05204008600000501030107041903040340d003184c40c0c0f05c41c4603a40e881c421100a240070000c101d91400744107e034028141584001d0080090301070000c0208040d102c2035000200d0101303480b445e54240100e40002038843c400462640d18003454501001818004e00d10310b014011428003c1c89002d036482041103601240c3c000c0020030100302070042488096415100d24000c03031041c0042460101d0010600d00c0c0038414680030000c0010305400190b018120041042e0800409940d0200161b00d80300540c600ca00e1148002d007588080d0f041c00c02c00c1d0b021018020100882520003081075020414175103040031283da041d64005035507030b841c0410142c01141c01c8207400d4000d80480604143e00040d05982441d2030101c1d1034001e084900044451140480e041d440c080e0320602c1690140747c070300d414200d0050007460008240720a880c1c90450692040d0760448040b114140100545260901e1001295442140c20800d212140c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 152468129 1250 152466879 152466907
    0x150e0a14030d030e060a05060f0a0806180106060206010608061903060902091005060906070204020c0a05070312031104050409060e1b04060f0303080402090a0905120a080709080712030306180203041205 88
    0xc04900d40e00e6907c07404140981d031642801030724202d000300302405035902e845480383c03140f005648030700b00541302070485125510103000e1102510740c0d60b07009040b240c0c60520200c0c0c05020151416400171112258140d071034850f40c42d004061070041030045400315042c8184807009100030194624444822028811562030f01c0440d1743c2031404581080c0c841c0c1190001500a1040401e200d25911440020400300301000c500502224020480444600c5103904141e0079100305003204404403000700b0003070060b4a0654080c2040c1c03400307090001901c0e40c050102a140000c02c102d4a81d602c058510810080d1500e40a00d038050400d107001e507190300d4695a4003601060300a04000e2064020000180e440e00c0e003540b2928107150803000f150402c042007642012594000c07410040014000030010300718900490501d0216607549005140780351404803401d02201170360350114101a15150009400b886001c0e20030081c1e0100d13440140d481c1864640080082c0020f451070050000520000d5211803035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 152469379 1250 152468129 152468131
    0x9080a020d0e010503011401110303042409020a03020d080705010c030e100218060702030325110d02030616121d070e0121060b0612060306130507150e0a14030d030e06 73
    0x211039132061007d004140181e03040644290740c4123041c4400710802090084581c104031319880e80c1d0348007640e45c050703150041054500b075010207500616000010001800e008800c13100807800b44800c40e09051083d503ca60a40d19440207080000e910382d0326800301e440382849074680e04c0d102e0020452078151030070f0b0100454810203144034132038040802c01d0015900c040c0121082080b5812003a01151526003054500e0300c000d4405803148a80c90b11b6a40306410041d8034020404d400400500c1103a44101c0c0c16a510303a4030500c490200060824070700c806103407130b00841c6030141e0300045140d809054000c901e484c01017582d001c804148c41280c0100200c41c2510050400f103240142c9980c50004281086000b806201c0500da0b0032510025a80405011300c003801e500807503044040e02c0b03564035601554110a00c079483c1c09002d54105850800410284103440c890207441d50601a03502100300001528051040d4080c0c41c040800030364110607440d0a0100c003500403841d0504110744002c010605030b03201d030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 152470629 1250 152469379 152469389
    0x20706020f0c10031b02010f0f0501061b0804090e0c040f0b011218020612060f090903090f0d0803100306050907060e010c3002010b120303070f1209080a020d0e01050301 74
    0x5441440400750500c40d400c4000712920104284141c074489910087c02829407181d95280e0a24100e445040002c2502502d030482e511640c60020201410071090002d01d00f0150485540204200010381c0300d030b42d030040f284c440da040005000301c5589101408180c54a2038084500b491901d02e504c0440d80e00039a00f26201d086108001030303201c20b0424449810a5080c102030750101e80814070040c600400b03803405100e9201a1981e0421404810500c10503000c19601c00009400a1180700d60034100010511041403004211002c25826034940e4070450340300307598403448100c0c0400b00340706000050068640241c160001001e6640c03400c2c0e03006010703070116280c4c0c1e030412011960807002e1062104814101d60b003401c00b0a20641c801c09480102c0e01c0d0003201e418050350a01031104814030f07202201c034070803c1c0444051031070b42e43e0b06234045070b003035503074081c0441403002a41c030741c02c0b00e200f00d0710902480c0b40c8030b140b049035a0006004042e183c00428004001005048040f1480d580d90100550781168 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 152471879 1250 152470629 152470639
    0x120905130e0f0a0b0c03040f21030b0901060e011206051e030706020f0604170d050709051801030c170f010e0a0c0b070c030311031b03040911070b060d060b030d020c01020706020f0c 79
    0x51124900b105540e040d0360801f81019142410848131010f00340544451152705e6101000024540d806110011009205100104a10960490301540611804252003100340030000d282c544600000e46071100c1c1b507a4a49940c040c1d00d02811150404001040181000d800103144002d0400b04083d540c8a008100070301c0c0a0005d6908411031031950141d0b18010303403070001848980f030700c41402000c0351001d00c1801c0c480c2c1c449402e000480000c003d1642e044e80e0b04112036001c1c441c00e241d092880c83d80c00054100f540e00c1100070140c1260002e200e2000c1100b01080a820010305034105004041402d0300320b02003698081000d540000e2810f0600812664541401e0828050317100d4400d04500940d84c0c01d80e9002644c2003060100c1070040000d0080d02c0d01044100308035074200d02000414041c103840200b045043c00042003040c5460348003019424414040814851701d04004203080c11007800b0b404015074015044950740e986c0520030380c005030403144000d118408461100030f0b0740c2c00c000e06c0950702231 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 152473129 1250 152471879 152471881
    0x306010818031e0c0a14060106090e0103060e07050604090608060604050603031210080706030e0708010c020a03030e0102091201090b0106020d0c060911060304150614060403120905130e0f0a0b0c03 86
    0x104003410240e4050200ca413050f1101c002d03450a04000000e0b9004140f61103000301c0e40003043c03141c010030141c01940c00c250540121070382556100c000078080b0100704800c91103001c1d0002055545c4000602c0600501200402c80d18030309641c041c507010300541100d01c40c1c1d040c10104040ea850020503680c038150280802e40064403960310300391043c0d206800c40009030141b400041072103a01034110321001e4014000b112180399441011500301e80ca074401070780041c0c2060b200344000c44d129802c0500144100c038001840c1041e15400601c0c0b100715803182c4121651900c2041c0207008005200700c0c01054a800600000031075004002d180b200110350040c04150f480c0d00000602510414100031000081c0000b0381d01d00f0f140c208038811202c05046e5041c00e82c10039901041582e8451032204818074090a101d04281c1180d6441080543c0e000c031741001c02c40c085400041c4c41d5180b4003d01c401c240b0400f40062081000300000d030905075100780041a90b441503c4550000b0000e40846600a0a450405881e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 152474379 1250 152473129 152473177
    0x60304020d0204060603020c0f0705061c0b0306010303120b0d0803270102160b2a0a05090d1b05041107020d02130509330106030f02040812030601081803 67
    0x501441034065005840c4c200c02068064140e070040c40000c80301c0341100c240004003500300342c1c1c4032010700031036411820910046164100703071b010001e214290a1408140c840360800420f18241c0c0981c41680040e90b03030300d180308282c0d029100d126200300041d9040502078980c0d0316100c180e8070020b072892034850b426641d41d81070140800310060f0340f12001c0700207555450388009410410320240c3c80565000003904041100400420000c000c0b03154070300e00b500c21001c4905450046c6030004800c4005101d030401c402c4e00141e80e1030b0702c0700306aa44983e10032201040c0f403210b030b84084421900031601642c43c11030020301c03444146007900e55465042b07078130240500491000c503089002e8889004103260403d010b000c64182c012448444103030000503482a03205c0d02c01d02501d4a1b0817107007200e0b204485820010320107588650800c00405400c00340140c0381c944d40d800c106250400d094401460003e01005006040da4040303601600140286801404910020101c5481e40718400ea81060303840b40a4403080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 152475629 1250 152474379 152474389
    0xc0b090c09010611030408070e160503070e01052a0d02010516020a021c0c09270b040303050c04121a100b0d020702150a05070515090a0b10350106030f0206030402 71
    0x1030304040e400d95190391f40d09c42c0d100001c460191140f0200c05c3c2d132580b04503161482607080d00e00c5400142e0342c030f0007030b0780e2184010b689030f90050352010b68110008000c1c00800e01c200303002d0071003004500000d06400d016188000d00311400601035201e000d00c05041440100d60000d80700a00341c0e0110307240b0300418010003a00e81d29034204d9400071b045980040c0001480c002a60240003200e210026400c0b4502c3d00060f8080d08125242009001c1c0b6078500c08600444c0c41381c0d00460b80402240004c5107010745650502a62448a010489508162038003403401007506078509034100e0380c04920910400e0401c0c20482c014002c0f004130b10700032980030620f0025560744a05120746100340010b201ea541c0328800006200e640044d03400c0d2040e01c11001d90500ca1a501d205070340c0301d0001540500340b0100c4030394518000000c081e00c01154292107131030211313040910f44911520203042e041a4070381d840b0b14079134040009403851804a0310340d14020080000c1072840100c0000554111401680d0303940b68400a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 152476879 1250 152475629 152475637
    0xa0303111005040f0b07020321040317100611030c031b03040f030605071706030d0f0e10080108070f030c0b030604020c070e071805030c060304030512070c0b090c0901061103 76
    0x10012070900d001d01091140072040d913000b050117804100c0c1650b8400c4d60503650707031084284403000701e24071141c0361030108010464181c01c2842454603a043c40c40070900c10382210400e036601001000c0c100b00c1040300c04e81004000160030329001c00b03142011400040c06850b40100c1c1261085030400e86044202050309204540181c03135001501e03d050b84e2641002001428100e40040104001200c0c01c00048141c08099120300350040080020580207002115540d80c85507940e000c1c000d0b941e1001110b5514803c0041ca052265942c03810550300d0082628946000e40d402040e420400080500118950007952004c0c0c03044005541d6594a4500c0400c000744904100c2c1c2c1c03890b0207480c03000304200e20400411400740c400e03a959004403d44154403141031440e10b10400760305901c20303041c0000a051180c05584e10038000e0400a08102044003004403648040b6086000200e0151020041207201c080b600d41294540e03008001c069500700c01b04a0011040c000c500520524408203404400d0401c221 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 152478129 1250 152476879 152476903
    0x1060e13110102070e040b0a05130f03050903070906031214070305030105210d030506100905060910031d0a150c0f200f0a0204060603050702120f07080f13050109050a030311 76
    0x8502170b0714041c02c0c0003d02580c00d41300313070203000d040c08003282600902556803e040d507080521100c0b14545035030243ca55a00500301c954042c0901c1714000f4842400348034420081d40101071b403b14920303454000a1071549026022801d006c414030690003c42e07440403d80741521001d440c7c080304034000800c1c13255003100800051400344512411164100c0c1e05820050040c0d5091b10546407503a901d034400c2c0d6440b1914020190400028003040c01e440c0b0f040c80d03c0104010050600141205029000198007002410017201907406802c0c884100545214215004450503204200ca034011020081074089680000e1040113803400401c0c80c00c0503042800ca00c0d81d00807601301c440e401e25034080a503c50345c181300180cac843da20b04100050b1060103400f51511642c0143d024084203040c0d20b1075001c84e50001c0d014240002e406000750740000c0c2d2a00f008086003c40b80310500d4696440021190711800140c1006040004070341d001c009680310705100000342c03a818200304002c0f60441074200d181140440d09 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 152479379 1250 152478129 152478149
    0x20405040f0c0f06050706110708070f030f0c171b2d07080303060d050304030b07051b0a03020d120f06060807020f0d0f0c0203100501090b0301060e1311010207 70
    0x24401000550300c004103100d8803586001c1c205580d101c3da5002110154450f5202140080040d00000783c89a48040b03084480420324504011144e2202d224540000904482c1143d92403001c0c414150841c0c00c3c00083d121034900205600309030b5840124881002c1d10f0074280c1500498203081039401070031724520b2413102904403503040b043d0300c04081c6040c0301d84008004c1044440b070304959040000c10180107071002c200055256840350410b10060381b15a410a640c503000c02e20002c40001c8041000e01d0181c00356903600c503180e5041c0103082240000702d05582180d071780545c0344200003d0b000f0816002141e224180714180510034035105002c0c00640b40c405a85625104002c1039803500103035610700800c19542102c55001c000c00303403107076100180450741c000705128440000501d841000140c03c2188090107988a180d00c007c03042064400c04e0b0000801146c0f20400e015480c1800d200f000d0080105e4044040203081c5a907080707007281c100303800c064400e03030a0341003020b43c6900801200004007200c500d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 152480629 1250 152479379 152479381
    0x11090c0307030b0303030606070f171207081302030a0602030a200a030c090812070c0b120403030c020313090228080f060108250201060f03051b0910140d020405 70
    0x11110240da004880c041c01103490100c201c003190400000ba01e2045201801441c42c0c18007984418410b0044d15904031020010b520020035000d501c1e0000c0c0c40e00070520f180020704c0e1300b40160040c1032204010329131009040b01e0986a8096039002540090b02d0313820080040e0707240c448405c2c4034090501a1010b0080040e43c1030031081444040009040c040007640e800c001c00d0610344000c9681c98a140301c1c0c004039521010001d0f860100d004020418544a5607004c10541c0e541c255005058000344581e0040c405160300700010715405008002021080f032001e54034180440841441c40d4105000d405010b0740d0205072070482d0340e4400b96920310400024000707011400d014000800600341100c4043e051100303c0c010640310b50154224030300401d03a00130518000544890013404510300d11201e40115929054005052581c010f2030700d0140d40204094034140c074864600c2c0700103400742e0000320302a01c03440013007040341141003a4840941d94903101c40d0b80003034110000201c215401a9000c0e41c0a0b141c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 152481879 1250 152480629 152480641
    0x403080f04081c02130611060c0301030c060f0203120a0b01090605030106050a0c0f0203030f07030315120b04020d0b01060504051f090b160501060e0a0e0a1707050a0b04081c0501050a0b071109 84
    0x1610184540d00c3c0c030108d44283d6186141507000d40400e10004001034502c07041030114902840c4540c2900400f441140e00380541100d10b4044440c05507100390f00d4030b41e10000fa6249581c8a080c0101404c01810080d2541d454140000c099100c3c032004042002807003c103960030803540040910126400800301c0c2d455030f034109060b6106611035941100071070b10702990304a404950652480842c1c031101601d58400c1c2d13442c1c840800c0507000400480e130000303440501100043d02d2070f1446010b0711643d03a07040c0d1181d0030300041c043e00c0710010840c40403d40c0301c0713106005110f038004841c0c002e60309070550301902c1c2d05411100d8001d00070440030080c81c550a180c030200e03440880030192445500e41403410300c00780b12010240ca07203034410710710301812127164007600d081000c0c800700091071103030311410131200e8000707190b1a006d0750b2000c140c40032140410002005440d0340c06606c004102d0450005013007140d075261800042010f2140d2251082007000401c00700c0500024182041d203441d00581440400c0c6003032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 152483129 1250 152481879 152481887
    0x2130e10030506010501080c07240b030102090a0302010c02212413242a081513061701150605040f032303070b0403080f04081c021306 59
    0x18010141011105800a112920311955100440350020054001a42032000448403004020407600400400b04000000514901c0e43d14003150400c0001c01000040c0ca40c8080076034000d0754106219a0040c0115562a43c50201c0f48080369824240f41000300c0803807002c07892029228100c0d0002508419540d0718a00000c20351076078058100300000d584d049080c0e0071100220301510421207141c0705411500002d00716204071300c0c080384e95207080b1207801e003d050960141c8850b0740340301101c580c02240c1c02212800d0820b040740403e180381072240142c23420281d49003007000f40b400c0d0184a10003503000d03c446480d0703660001000d00043d6402e000c5050502080324007030600b064118000784510344c80000d4142c130403425141a207080c0e0211882c040d1464545080f02c803e0250070009030510100d0b60800d14200300010a201d0b482200c5402da10700e4281005001c0c6080100107002c40d410440802c0700141002c3d01f1145440d05080500e038816080c100d4410003801080d00300412580040000700c3c405400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 152484379 1250 152483129 152483167
    0x7110303070b071205070813080c01023103120c060204051806030609070b0a03020d061214010c050f0712030b030d1709010e030406210203100e0702010509030414060d02 74
    0x11344a540603803044000180407a5000c490300400a02d040c0302095414410340302c540c44860281c103813681040383c0072213031a003240c0c01002c000703401c20458400f03140300ca5148140e00ca8440402c90080d0074151440c0c4400c1d07201300e140e4040000308034490031100308211141d030643e0064074019043c504e0030300d03040c828a1115202075682510034820307000017814840300040c501d801e5842c031007006800c100d40128240d006c2e42205100000c0b02d41c49500211b50b08456000000505028140017441c0030402c0e000f040c00c540800f0302e20810081c04000400700340220000304c0e1001948410200c102643c80c07002200208280038140f6070601503c02c2003644076a001c00b80121020007010380c020291207940e01d050032103203150504884c907081032008000c0240030751014844c1e41c822250102412000c51846012a4000c4880046007007206000f03210200c0b246ca84180d100c00d1a0008100034180400607a6480c0103621441d241c0751184203201c80591034080964020711340b105030039903c07881800da00010f2898 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 152485629 1250 152484379 152484391
    0x803040b030402180603120a020708012a08100605030402030a1403031008060103020a0b0a021c0f120b130209010e03060a0e0c010c0803160507050a0b04020f0604180207110303070b 79
    0x3280c0c140311307801550030600c298066180100140360000004c0e9901c00700340c10120001c410360148000003d0340220a00070214a40385420741071030000d40c7c144036400e003501c65810860400007242d042184003100c1800002c03e44d010b505180762a641d4902c00281381803494040245003200b0381591649210000000c0c0d8003458004540b0840d150f150715030aa65160300f44000b83d88180c1a0108000c3c0ba642440180302003c0b491040da0000006140c0c075001d1801407010701000190702c0303040c41c9007660780301c070403000401c070fa0b41c605110343d42520001401c010420404142c1d0300ea40002d003d4001da00440b00c0e8502104043c0036201c2c50f1034041107000c0240a8417003628824080c00409001b2507114401d80000958021001c0f821501c40640246080f0340341500c0c4024400d0810002c8040703401040742c020400d103c0d6911000340d182620510003c000103140d664042d680901c01802524044850034500085100c001a2683e03140d0404903007406400e9101c5802d8000001c6183c28058181d01103403042c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 152486879 1250 152485629 152485639
    0xb070609140c0a12050f19020301151410021f050402090f070c0b04030c020a120c0e13080c0705090f0a0b060f03060103090510060801020d0612020916090803040b030402 74
    0x1c501c0c041c100d6141c0b4a2584501d40c0000740036400e00065640c0b13400e00303141d54001d40450300116086c40c06140780c040103611840b42915100300000031403038240118450038000d004940501807400e030f00c0b020038290008825201721002c00040c04418401c1001e00703158613940320319240203c04c00da40d8100414040d20144c0c01080900000b4081460b000c00c26030098009a03903c0c142c106880d1a410100314000c0e200b00d04009074101e502002d03030740d000c81a0016280d0300c0301c0040076600310b00d490804100564407100380300c0d202c4c80070005038805002c45607104540281c00150307140d840c0344442d820294903411a0f03600c1001d00052201c3c58450b48041e0344580c0d5140c2040080155030300400000b4040c01d1400721000301c04000140055110380c21225049104004892015100d00340c0b54094818540110140e03039070205904030740645c00c0c00380e04005c2c5000100c01d0701c600c4045d0007080950f000140341e41000010558031110241c07013041890014400d003401d998596440e0152551180c2c01075905900c60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 152488129 1250 152486879 152486903
    0x32408010609050c030f040602070218160306030206030601030903020312130b0108010203101a0706050702010209190302060d0b0d0c0303050904060501030e100e030702030303010e01031e05030d0f02040b070609 92
    0x8041907226250003441000071301c5003103076140c4403103104400c80104120342d140d03028420000142c54030007255804000c040c0c0042100d01d088004d107080c2840f81d440da001014100743c0c080000d6211041101c1e040360003031801003240748450030260f02d1441010705000301d0040f50020071041c2e0301003101d00700d1500c0c4114809402c590f602d40080d4281c0c002030306c00d21600440d0702e0041000d941000100740d00649003a080e24100b0189071070b80411181d0444078100582d400080d030b0403203850a50a050007404c04806180da1450440d00130032a5801401603422000750385109001c000d03646d007010f5074009030340075117140445512441d00a1183e00010740031802141407210102d4158028007901051f110014010004094620981009030241c000318154601080040c2c00160b00d09000035400303800041c0c1d07142884d501d5481c110240b10490024440780b10380040c000800136501008503205250801c3d0040358034aa00168080240715130303401851020300005c1c54108101700c680000000b01d01409082c952 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 152489379 1250 152488129 152488139
    0x8010b040f14010c05030307170627100302030a060f060b0c0a1b05040603060b09130f0b07020709090506150301061a0711030f03030411040b0a12030324080106 70
    0x2450140340240520694642410300080e950002400c9107080140340407244040252038076400c0d030b4410340e054000107440b01c6c4044e030000c4104510f2500f2030000d4455808140d00103800d42d1650015072200f1420300205404203584504841041c17015540080c10340d01c3e4107200786090001440e0454004605600348036000400704281030030340307520068000c05400e0500140d40ca2070031081324410103060134810540c4c046440e40741c5100f043c1c0958490301e000100ba5481404014603004000c00804100c480c15101c03400140c2010000c041059004032206125120320700240d042030b0294200034a060310b401c1d00e900a0010000341a8002c07180c0c0c2688014090030881814286c2e540c0c1e000b481c14040707514a41401c01030401000b0000f050003824061010341c21140001d00b400d1f5960410105584007009000c1400f03c0e20034400c1000504403030401c000100e46000c01c0c480c050f24820303009030710305240200007414001d40202c5007100c1d04d507000074030445101d02d01801d456518021081d0369032a114001c68 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 152490629 1250 152489379 152489399
    0x2090108060f0147030a0b18130f050c0301020a0c020906010e1e0301020904020c071805040c03230d11070b031b030c0705010c0806040b0910170114090705010801 71
    0x1079410510b40380c2d015451806800f040704d0b404c01500c2542030003020108002d000c1c40c0000554050014408086001e40c0c046c4100100c00ca03400040b0084280c040c0d00784020846c00e103034158a031940c4031f03c440c02040003c0c145a404c142680d02040c2c0c16500010310301d075046602c0083c101c0b81e54800c5600304907944801d4011198400d25503402c27504480403240d1040806001c2401d0303881424010000361a0507084404101660010300c841c0d10795a02c244014040c9503401d40040001c1d50840004020078540f07625070941041103444050044030b4070b090241c04107460000c034800070b810408112115035405a40c010000c9140c5442210340f405400000301d101900303682140e00501c08500e0740344515241182c92407441e4009401c0d800c0200c020800000011000e010b1200000b100d0385458140c2d26003076040c8003da50340f0022032403007400280100020036901c0b8148106550984a181101d0701c2c588101034010255000d40310b0424814400f000302c44100009c020043e18005e81c4ca61a03607917640d4500300703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 152491879 1250 152490629 152490659
    0x9060f0815190b1203073c0303020403060e070f06051303061d060106030c090902070203100c030b18040213020301030b070f020313061d0901150309020301020702090108060f01 77
    0x3528108220003040e0107024890070268404150b500020f141100c40f000601504c4401d41c0ca6030b22030700081900d0050202d4070f040303000c0300b2181d01c480b544039a160824503044410b5003a0643c0c8041c0c4071702d45400902d4404da042d20040d40e44480c00308403049810755126900c1205200d20380310a6466000420f000780f0660503a210001045680003c00341155a24800b50490f4101000b04072001d000c1108800401c11070140206003d4400040f44403a103000140501c01035002066107a0040040c1801600d000400c1c00303c180c00070000140c0350007a58001c42c05021801c494039440148446143c045101d000845c5006030f208884c201d80b181a0107081c40d06034002444090314a804e5440082c00e910b01640a07134550891601c10749107000001c1c40303904042c030816005a40000d40609040101d03081120b01c859075074074100d4450b0290740c940032886c00c900340c051100e50f040580707800d520303000c6407030075015604619402040c02e40150303121600c4560b0340404503a5000d5401c01340000244480d4016214 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 152493129 1250 152491879 152491903
    0x3040b04030204110d020703110601050307050a06030203130510020c0613020a0b0a0e030601060903110a14010507030e100e09010e0702030a08060d050d0216143709060f08 75
    0x28105490764003008028059489000011320040000e846084000e1009015440c820385840640c50384412840e0b10b0f1180581200f0300950001d00140f1480d6180d01c441e60486040d0f20700035a03039984020181d1303000e812018004280e84504011400c0d001c0d120b8000d00726810074401122071075518851081d1800e044d082c4081e40120a200050042d160700e0342c002c003910312460410140c40d0070110082803400b08245d00c284000340741c4070010300802c02000000c0d508103900311400c81000c1d052800514110004001c1c02d8140080000c104c020036006a118200c0d1290041010983c00303188400502485404010284500071800020400e201c13520340d454000c0c801d5600460511490f410191903092001d00400e40c0680f5462200000030170400140d10840d16681c0500041c000c01854003501d1042900003043e001e241e100124041c1c2c0794003030114078a1000680c0300042d40301411416002070800c501c0c00e101c0c08045200403400c00000d070002d004441c25103031101065a90b03030440c640c5031a000114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 152494379 1250 152493129 152493149
    0xc01110f0f07022205060406050607030905190302090f01060201050c04080c01080703020904020d0f0506061e0f07050d02060417091c02040609092a080604060e1513020405090304 78
    0x5031000141410010700b900d548050102584803107252550320422880740c180804c00b54595041260f00e0070079001c0d0800070721085e0ba085092002e940c0e0068150301603406154051111f8418480600150a00d090003c580242c00c0d56400d05003411180c2ea40742c000d0183c0805903007880049590750b01074008542c12580700c1c2029000410400300115001c1d04050701c00c50030150240041d42c030a60f120f100404890b0040880000c1c810b400143c054140d030342c001c00d81c510603001400750130040e11605a000c1f2030209040c101035640c2021601094150294040140562082040d5000d101d5000a038680c0641c0c010644115250741d03800e00c000c4148289003942c0e40189601d803003481960411140c4441844c40200007088991b1101c13681c20442c1e981000550340d50185080318506c02035031642d0f2901e650400300c01e19141a040c201e90341d65034000a4001841c203039652000e00080c7d00c0a220a0156004000150f00c4d941030150000500c000702c2c00e803d0744184e182002007584041c0002c1228201c40c10310070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 152495629 1250 152494379 152494387
    0x7080103060c03060513020a200c0d0510020406020706090504060b090907021510051215070f05211e0f0a0c03090209070302190905030a0803090c13020c01110f 70
    0x10303a860240c0740303802c2a04145a1140c0001ca01507985d24901080400300f01001600c42d811017800078640002d0042c40b014058110b200c12110030340119441038101002d680f0700300007400502d0224074042c00e55282d40f140e00c1c0301290100f42d466000c115071007101c203159603807050280c0b14000c00007128107074071070710045031010800140903013010710a4035800b0300b090060b5540a000c094145800a10460322140700c038607820720901807864503c078988100c1e152040200100084079a12408100018207080140204480810b601922500440380e90b88211544100b506112005a0314090815120040502c2038158070280c0040d0121000d403144000c1c0350441c1264503010400790081c034090001100301070310b40d01c4400c0940c0340e109407a4055820341e500140e0720b1645081c4540942c003100c6411007006003009041084d654009407507001503420400a543d241c0f0340c01011403800b03601c26420b9402c213244100c921150709041c0d0107401440034010092080c4100031046845034442c1e40700d50504500240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 152496879 1250 152495629 152495633
    0x21f0c0212031e06010c020301090309080d0302070c060c0206040b04090203040b0c070c1715090c0a080f060103030327150c0c03050d09061103010306021e0f09092206050603070e07080103 82
    0x1801c0f40e03800407010f051959a07909070f42c01080c00c1d2040b0020541c040386a2000820411904000f1068201d82038038086050801907a540c3c0c44007489441b1340000c0004280745070b801c1d5074a110403103005103802240e0315a9182d40700d040134083d420880d001c0e01c2c000f10580020b609028100201d80070182c0c04046041d41c44d04028070b03a10303408105000c1d055148220b0900c40e004001040219025a07241c10060084035000b000b00440c24a1981014120390001a07a480340c2003c00910705054a505007400716100c0707202c090030b25003844405c0203070f02c0d02044140c854060243c18540d054010400060922213281d008605607007070805c0e04401000100104050944110254409100c19120340c0740032820412489003c039042d00203030010b0b540164000b070008100c1d00f1403800d04440154200303200b400c0800c045c408840c0c501800320300500070920580020100d142c000c1c00d5200d1480147c0756660101d800d820402c0041c00d0444000e4003074803031000c0108880e051880d1051194070141e40d100c21030780c20b507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 152498129 1250 152496879 152496931
    0x50c0a0503300a090e0601030c0503070309051f0c0905090907030602070606090c09060201150501050711120303130b0f0405060c0c0f0307080d0515010519021f0c021203 74
    0x41c406840195415400718a000c0c020b00000c080a2145076a82031a0504201002040c090094400742c14903280491204c00036401c20141ca40c014824140090f403e003103820f000341405211740c544038000303ca031072880c1541c420316480015042e50581d2001002c40d22003042c003203100b0b01a2a590041e60000e0410400503003290024184144180800705c0d00795a03445240c0150740d200c40307458000c204035104c14800c055091103100900d1a01e0a081d008641ca0040081c200380302d400c50192400c42035405a590940761041100445100b00c0700310b03503072880c003482c52440010144004a9503031707140b0b001080a04d03003200f100501464001010b06100e444000804e409640103003400d50440c010020f200030b80d10001d00150030713040c0c000d2041a580d440020b0f070820444000800501e0a402c0b40b4013602c4050340e125064a0160300c1c002c0c0707500100d041850080e4903200803e600341200c07414000d600c604288042d04006144c6100c0d800300c030180c10790700b108035406010484c0c03503098908014401d1540b80c401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 152499379 1250 152498129 152498173
    0xf030313020d06020f0c0f0604030c0f03170106030c030c08010e011e0807060e09060102011e05090f06240306040b0a0c0e100818120711040605130603050c0a0503 71
    0x2009203282d01c00e512580da0300c0c090384c011304034445c0c15000202d00340366818814040c2030f442c411500007400c4a03190564000c0c001c0341c00031501070031051480a58108141c0105400020100641c0640a9079a55407000030041c0562000240c0007078100300713862120502841000d4181d4b0010000455268203000106001c600141101e0780000f19601001444a4041c070519016020315900d1448040291003800070b4150080c1456045a245c2403c591103406c03c0490b0b40c031174502a0002003002e4445123001c41c640905102e240d045805284207000c034509103c1420854244180400c01030300c400a41050784a40c4101c40181944060200041c01080305a009015031041400c008100d0001ca0b000304003100c01c1c1014240109020f6818085a800046007012583e0303601401400d002e014904801d0050040000040c5200d2000c0c004041c41ea0396170b080040544000361010340c03092070300c0b00b101c0c001e80007070b21050b40e8078014441e182c0035070f0403c44070480c2030b26000b900500f0031500404281ca11145 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 152500629 1250 152499379 152499383
    0x221e0e090307170a0e06040e1503030904060e06040c081b210703021c060503030a0810030b0c070b13120f020a0b01080a0b0105100e0d050f0d200f030313 67
    0x1084180005084500080f026034840f42040e0f4481815010180507444074103204c038480d15060104210524026044030f9114022007006020190742c40d011038a14005c0b0201c9a901604240d80842d01d190320908062040e1001c5800340700c484206403040c1c424039000e031040e840b02109034901c0c1091001190040c02d495180c400c80c460541c4070040c01d208400000d80c1c0c4500000d800080c0c0c003039405160508194904207001c1c00f00180d82c43d000019640c1c1c45030000b0502400741a05c00600040c2d0082c0100c0011500b1100c030001c070340703440e0803d40c0160740800011200141c528000c41c000034600054440b81d9680400908030f50001c8400a40d500b80190908030110304c07483c00c0e110001030055400301d008101d06002801100c000c0d15105c042d00300140c01042c024a4550340411546900070f440010000c410354400410032201d040035402c2055500407250584143c9180082a60703000c0c03541d44000203200ca4070541c000448440700d0711101282c1d030300d40700e9500900210744842c060028202c6054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 152501879 1250 152500629 152500633
    0x601050909070e0a052e05010e0d0510090c06021c0302370311030c030a0207030c06140a0b0904022206050406080102040504060b0304200f06221e0e09 66
    0x241c1e0f20004840381d0141140d00c80042d603140c40038040040025803210344140d80e80700324901e00b001c481da400651441c15101e414100100c050403100070b034a4a00c03c01c030074241c00c001911511046080081c01900442c00d040300c0c40c010901000400c180701150f00b242614601c00d03c885006c45010086001e90031030100e8400d82170829000810703502408101185800104141407804240c440f00a821220030f0a500c01080c1c1c0b0030801c112001c2c0c0c4480c00c590744084001001600d46200707050841d00030300c0e4036200030f04661900d0389102511700b0101c03405200d00103030030301840758a01250902880c50b00a4500a4003d030350344220f000001c160344020b10060800c00c10005000307a85000007410380b04c00703510001c640d0f540001c040c00381d400d190007148040c15800a40310710f1030900c0d40d202d503ca58601c50400d001c0b2041c3d41c51654246d41c855040d5400418020a0786444101b1214484140f152004140c01d80943c400b01c0003c00b06080f04110044281045070301055518100e51a03039003d0008003508118 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 152503129 1250 152501879 152501893
    0x13060209030d0206160f0819110a08061c020904020405070e0a0b030108100c170c0f03160e10021504021201140a050903040b070303020d142a0304050601050909 70
    0x5501c0801000320036000580c010051350a1040e555090022a00052005c00505040c90b03404d007500403001d41c0c2c102c8414080130720b80744045034100000300f4080980c3d103210940020810707a1030b5888031003d4094841121107441d9007124292601899490304d80c020341040340030300050050302c1c265009580c820001e081c0b1091a9500d1400a0702d144515005192030301302c048010310516400b003020031203180144504001c10701581e42d0140a4042214080c04040d0303032403002070003180ba01000d5901c401c0006000c0345d224100b4a40d101c01e8501d1400755800069008a001089460102c281d0b0060741204e802510005448088503660450020000e90304400043c541c000f0b554002d2183d80d807500040d61081100c0d041402c04030045d00d50203488414154424407080c040103e81030122a102c1d03a041c00c00580d03032090941d0303000c080c080c44c03e0310a0100c0180020407498007206030007462440d1b03090180c08050040300c0a0109903000c241c402a080740c0c42140144540d04240c2000d0381c000000704122011 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 152504379 1250 152503129 152503147
    0x30f0e0f030607050a1101110324030313170a1707260406140703171f06051e0f09060c0a0b04050114010e07020c01050d06030b0a090209061008130602 66
    0x15100e01940c3c0800082c2c00000c0d040c2205500c03001e40b00280074844000c0c80400072415171102d26010240842c02103805d1501495980c24591210010040d0007038280ca8907030756858209180034000344601d446090640460390b61001c0046032589445500070708484800b440c1c1410000160082c43d004c03152840c0f040d0f1a0464000c5501040e000171501c80c0e8520f5a440c00d042006209141e0000552100503044c480707100003035004058003e0314810f88a0f801c1c515070718505000f03104101040504580036051001043c655032001c020100341c8a00700303050440750707030304d164614003031080040219580e1014040211246080b40003400000f01c2c2e44201c03482c40120b40c8032030303070500c0044d2000c5820780e540303100100f1180c81d080d01044c01002c8109200e0780364500f401001e901c070348016203a241086000144910014817551180000c0d642280c4092800e00d046000d40006100303443c010b03845145080f000404501d40030031458854407881d62111b40f0f944408550151441400344100c41468080c051003403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 152505629 1250 152504379 152504383
    0x3090a0b0901091a0c010b1507020d0f0f0606060305010609030c050d06060b0c0304180b01122a030b040e1903050a0309020d03050304061505030d0804051e0601170a030f0e0f03 77
    0x12501d41300d211016500e0241812043c00c5800c18200c6c28040e01d44400c0c40f01e0310720480c0050740c1602e40c0513120a14207100741d28080000c5509050f000706503001d0150030000b4064513620041c00d40f2025101040308e070b41c03070302030944640d010b82c0b0000744403a914101c103001d503003003c01600c40c880b403050b50040344107500d540458601d60401c2031b031206640d0000c2020819044520301e8403500e29a080000c2000e2680180001d10408070310b0b1070320800b1034a801c80309860880341d0412540202c1a02014140c0300420000207011b030500515040c4242d00b042e40c219410000804e0700340c50806c1c46040515041d0031641d00360346035000a0703c0078051540d201c02020160700c80c00790820a10340f099642c51b07524985440c0c2a001c84000b0028a0380c1f01d00005400d2106032000103100344400c0243c10a1080c95079030b45843c03460910790840d440d00d07a400440000c1c1940000003140d42c1030b1002c21059160101d40d04407200e0340d0750035000d80500003c03032101d04a07a40c10700885e01840c2036400a460300b9000080000072038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 152506879 1250 152505629 152505659
    0x20d020408030408030c060615090d0201020a02131d0c06030708091603060c03050f041e02040b0a140a06050708090909160e06011404030b06040c020a05060f040c0803090a0b090109 79
    0x9800c1d60400940d6101c405410b201e1f2503441001203c2c0300c4044000300d01c00300e200780110032106014031042c00413078040d68000c006103d0410750052081518100c000d01c11405841c0c0c103002103410704c0f04503400c840310480c0450104205040601038a040d65102c20040b1000718010704101603e001d2244008640269100307100090340c001c4402080483c80389000238229100200071100040826081c40f0008001b40c042c0c411412a402c2c0d5014100340c2800002c0003009885141540003034195000078007002654550086074078111170050907540d880030156280c0c801d400300100f070100d08012101903840c2103495550408414012211b0000302c0c500c8a080048043c0c2140c0c3e0b0308011182000b42669000d41c3c901c20703d04202d40741ea1300345481e556170030400700b1014020b50711a40d01c500c13002003201c1c0f08008510100340c01c03104503503140c00c0c61541c50303004003020b0341c0694500c92802404503105c04004102c0f0105040038120145284c50300604640035009010100c0c10000060400104c0b1210340e13a2203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 152508129 1250 152506879 152506889
    0x40b03101127150901180e100b0306010905010503090115080106080f0a03050a0c0819080a0e070315110702030601030f02091509041515060302040503010c030e072c01060215011a040306020d0204080304 88
    0x2038000c41c2071188d40c0c05104011644400e01c010010010030044e40da00010190031200300382041900c0303031901c0c84906d02400c6a013859141c0d80c3d80100c03000400c0c100541280f0125000c41054446880801000c9903e50080010207004140100b1030123001510032400703042d445001300030b0b440c10140361000001e0554241118500020084014041d081d1709510440d03440304a12001803428034519920b403a451580004188a215911020700700d1000e0503074120780c0b0b0b1690040c103448007036859185c402c54031903280200f81d000700c40040008614615885580070b8280e4000e0400e041d555031a1f0b901e81885100349039085003191140c502808482400395140d0141406403405a1124108400c0c1421114010324135810141411402e0b03410510126152040e1580d9828000d01000920280d000512415059100301d02c4800000200158081280030782c04420592034000e50b641c807400101794107001d01d211482c03100200001c1002800d103500801c0c1d121829400541040c6d52081c5650444d0050b0307100b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 152509379 1250 152508129 152508149
    0x90102070209060609240705120301030605010506040b07020904110402181201150b0705010b060409020a031401050306150f030a03020703032a02040b0310112715090118 74
    0x30311085241c10300d9040e42c000c8060759110309225481d40096114040240d048441c912007000b020000c905010856030419008401c0b03c00e031221041c03402003a03600c00d1000340c800d645400700200c1e444c6003000491f021529400d020741c1c104185d640800c0499a80a442140c10403100714000d1000c1d1560f0000c6c1c41000952504c0000000421003400a0340228120794001030349440e0b4848591020044a030003516542d590040e03c9282601e000c50040c00c070300a420703620103404500050781c0e00b000c3e00103003940f14495406014021440c6c61441580100307008155044d0000c0d0001580d11074110f10110408200030881050007941e9800702c0d04025507600e05500580022906205054000281c2d00301c1c170352002d0001c4068582c280c0c00c0c240303080c00c060000384110b444000c010030700d56017000000a0901d5002c8200542c80b1600c041f00ca00343d21100805403000f04889030101140064000b01484a402400045101d09000c0310112607501c640d4086051054013982200e414140041c900080c1528040d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 152510629 1250 152509379 152509387
    0xc0215090303010f05010c02100c020310060803450a030209090304051f0903030e01030f020a0804031d03100902120303090a1a0618070201021603020709150b0712090b03090102 77
    0x2d9419204d021a00300c0da0502104010481c01030705c0300b9104a8200324286498650b0748030354800070342050619886e00c0c403050f0615101190700c2d034000c002440c212004c01c2e4222811400030040040000c402d0088509804060001441d004c0703000b890030580c40c2004244400c419142e03400144000001e50b54456641d10119050015003490000c0c0d005031a140f0000a540000e0100001d18991590100070100400e8401080c2c3c3d50b400390f0040400002c05d02010b6480d40f0700210000c0c900c0d502214107500041002c03154110720512b6007481400c0c1c0c68068043c102d081e5121851202414865404036086500c0d142098150f440034400345011b5180301c2c0142900700308508080c00112001285410800036043c2806259035415030521180c1b0b4400c29400c10030350350380c0c805038024007a103840b9100086101560b10b080540c081503a03426202d8200080200c0042605841890461070060350a00d110030805840851200b010001c1e10703074090320305410075544401c00c0760044d4105a440d07500e569004a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 152511879 1250 152510629 152510639
    0x12140402031e120d0b0d0b04020a0609060e06030606070503070f17130e0901061e090e0111093606091302010509010c06230711010e07030201030c021509030301 70
    0x400103507401d0504540e071541d50842d003061140c072950800303c50000064001800c401d1a031007500540242ca10050030801c0d42d010071f08090035000c404a40803803284090b440080340f140d001d180c0309403c0d6403090703680760902c096101c11700c4142c2e44040c040701d0b0b000e401400100d0000e20100010401c10b03105494814500c1c0c0b441c981084141450740b8075070780c020824020a07040442c3c0002500c200c4844602614480d03d481c40c100d0300400c040d40100080148149195911380c440711842d00031200314402c1001107141d0030400d1400c8844417203088a075442c0400060394689815444020410707800e04152128030102007400c5058241d2078092090800e0100030003280d03290074400f00b50320100708500c0540044150b40001d089214100b034840c14404007201c01000d00015070703c10300d8103960032112a0807034040300b0f80300046100c00b101e40c3e0001130483c01c41d5800c0b209060281c505000c00403001030071220708503401940980700c001c110000314810400c5c4a50144036000d85240a01e001c1409580d50b9410030b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 152513129 1250 152511879 152511883
    0xe0d02070f12060906021c061d060f010e030304182003070f081008010e01050603010501170703150f05070c02010206010812030f0a02093a080a030b011214040203 71
    0x160301640005025440801401c0707880c541d01102c50398014400100c5156038070b0890f009004160064100d80c0c13051208111107410345e0300070720580e104000b090b041d9000304030a156600d03a04840054001c0d032402d01c0c01000d035000d05e9005800b51001010b9904098891b0420700c1c01140040040c0d42e025240c03403c49a510b0b0880448403100d10440500c81d1440c6418040a051049824103020800070942d0000d2091926181200c000c2c15a40000340010400c00b110313680030340b8056581c1780c407070b510f81400040e52007641d0140e103140c041381f100540541460740d202c014400d200014079101d01038641c0424a807500352442128890b00322522003054021b0a80002440c1c940142c00c02400790f401f0300d00b0070840c2e410032800c3c2c2c0d81c0480c4154040e80b00d60794413500000680108441ca580024106034001a28000816440d52031b01800c040c1d55030a481d510442c030200724460340c0241001c0c6e0700b00166141640300781c004000d41034040c1054020310751400102c10403204000641c0303100c400300c10240011440c00b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 152514379 1250 152513129 152513143
    0x71506030b100e15010311040905010e0f01050d06020d020d0915050703020a020a02060702060c15090d09031a0402030a02030d0c03120b0315040f020d12030b09090c01140d0e0d02 78
    0x20703140002080d40c0c140f200f11041c0000c05403e6003500d03120a81c2c0545640c1c0302e0b070800c01100d00d03425041c0c0c0c4c566948800c62800340070223010383e001010303c2c400065082e646003c0224104c0d10020504070944901d6151880203604c90705210140e503400308000220b400c401d01541041f10720a100d0034081ca00410b142d5000c64102900714801c1500400950f05142e0380080c2c0c1400154040301d1040d6039110ba40700040d018410144a032456010303101c845070142005071100c521803114031040da005107500e00c404590014603408020315401e007541e184503002e02140c03406584944060216000d03a2840d400091901070b400350a5000241e18031031050406500c51484010324001c0242848405006000281c8400040107031030f600d4a4818001401d10290281780350b000368000c0c001401c8095942894181800701500107000300f821712441d0301450411140c03540c450707800d0b0000303041c2080400004440764048200c00800c541c40078000d020050300644141c40000080c80c0003080c1070801d1140186c20020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 152515629 1250 152514379 152514391
    0x20721020c010305070f110f12070201120204031509140106090f06060c051c021e03040f080607080115090305030c0a03030507050403080a050325030b01020105060a03021302030903071506030b 84
    0x8240018414003070b0300103100c0141e80101c0e0410b87c0c0b403000f04e80ca81034a00b00000d00c0769201c038410b071042441080d240e84000d000450003a1390b150340b0b18049483d940140c0c030440c4002055002d580c061407403d131110354400c04150340f044907120b42c15550054810700359501504040c5001d5541c0314036400b0003200c0d12900d4010a05c0d410716074100c1102d40c603101d4446528500404c00040f038031940c2d204491091102110409a84100103613164000d0400d90b07a940190240b907581aa0400b13010a0781d032000510f1500c5101c0302d9442c0d0b0340d940e090001c006151448a070030841405204000440002c8040c00075250703c0081d00b004098910060600500b540c0300a0062410300004110600226141e801147e10109141c1003a55980d107171907440c0031610000554622000070201241032090f98550403109098030264000d0040361940e00811410310000d21000303601941100000048014035001303554402c030b01005036410000c00e52582440c443c10f415000691503500e0b80c080c0300b0072010500c903a070002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 152516879 1250 152515629 152515631
    0x6061206060906080a051015080a0c230607110a090207080d14040308070302090102070b0a0507050708010e07090f090f050a030212030f0105010c051011120c0a0f0c06020721020c0103 80
    0x1511686486071201c01035087c06603265240d07800264910780d00c40e944802082c042c404c88400a507903041c8645250703c24020401030340d9020441002c0099400d010a6020500402035860300030250b40302003500a04c100229005404033b480042d050050707202405695004040055a90511602c2101169402c0d10840d4804180100b0710010a500c0140e05520081d603060042c0d46154090050340380400d035074400f40310300c00001401003c880e8402d02900407988690101d03100c042d110f035415800d03038901c4903191940d0340c082c08040000d2902c640081002c4004400e00040761aa00c0d110702002541d0741c0c10540c2c0c1a8411800340d010142e0400006d04211070a0580305c0c11418074606c500c0c0180c03418414241000302081103030091080901c105201303500d030018104800c04021007007000035003003900e98800c942e40c42d000003000e00c41c002003140c002188503640c2c64401d03a1051b0094409030500a001d640155091100c08002100381214903007103217031402044005010a08000e151a020052042c109 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 152517985 1106 152516879 152516893
    0x2061303061b020c10020d030f020f0a0216080a02010804120e090711240a0203180109030306050907030e120901020f0615010e011110090606120606090608 68
    0xc80d10720b4080e20084140c00042014440c040b1300c0402c0543c102d4807c220b007182c841d6200f01904182c0210060804c40c1001c025040c80d044003030000c006da40108004d10402d040c101c00000108200030080482d001180d00007002d0080c0908000c0016414101e13035295030340540c81c2c2d039840c410b02a04492561400030002061603031404007a9a00380121003c90000310705160703d14030000a645c4900c1100d803680320078400203510003016980d085400c000b2641c2101c02c02e018503050315010390390104e20b0f03030701704400c00190220140140082c585007699440c0d0140004c114240d45a04414034692a0911040140d0400e580400e01d0103030350003084101f00c01025001c00074042d0311000e07601c01010b00780740c800640341c1c260482125180b5911807020744101c48501e07040707080c03502d2156502241d1142c0d260400c407402e21064404580b86a201c09007403185051500c980c000a2800030014a0f503 = true := by decide +kernel

theorem cover : BRFrame.Cov 152338129 152517985 := by
  have h0 := BRFrame.cov_init 152338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 152338129 ≤ n) (h2 : n < 152517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
