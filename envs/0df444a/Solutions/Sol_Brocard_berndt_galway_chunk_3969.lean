-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3969
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:11:43.403251+00:00
-- url     : https://prove2.me/submissions/840e2397-6456-4a1a-b55c-235e2b2d40b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 713669064 ≤ n < 713848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 713670314 1250 713669064 713669071
    0xd020102280b15030303040314070204092003120a0c03050408120c060a0509070b3712090203060106230d05041e0512251103190b060904140d08 63
    0x3408058000511100c1d80f60701d04036a0001d008010318610f4480762001c5a580100d07442c0c034002460100100c42c0141d64622501413040e1141920789920300cce1a61b6414031300888100c60340d000b6004030350300314240708004e01103540140c401c0c01c0c0011281d295050451f410700941c2c000c0022480341c09640e1848101040c050429100c01101720b543c590f80d0f05044800b91001034969240310343c0070030401e101e0084444040d08d25052002e410301c180c0795042001481140c0703411003046503502d0050500e10542d17401000900142c10a03001404400b5482d40480d650768014400c0703108001c14a5151125418000b40d0307207500d081014001ca0311548881c2a44005010513a41141c0d0214101c0d031200100038551140201940c001002d824401c0300e00d01c4486040e4800e40147c0750514810843c00d03281241400344000c02130040304820690031200c400e0616102004111a48810000032850005050b080c134580d4040030965030b13480e003916245440c141041811042005600455586902955105543d87d21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 713671564 1250 713670314 713670323
    0x70203040803040f08160b04270c1709070e131e11190501050304121e020304030c0b0310060f03090602160203010506010e0d2a0803040f140f0d02010228 67
    0x41280c2d803411342094108184103030a003054044c03104010000490304156000400340d08030703041e0107542714094000c40340b20304101d9010450f006003016a001c07034210360030341c0300722524000c201c550b003054004a441078009205440c10000425a0020005800c0b8107541001f000d407840d146544152070b000c80c4140285500501916040426004481981440b10121001078440926513151500d850508032460310344441485a540b030304c0301c900784803500c0007101c0f84641c3d4080e60702e4904501d00280080304e41da0194504803820f2084c04404410180460b0407140c0d035080c840161500c82100740c01500b06105d01520307040c4040f82d0340f03054003003100240041900c00c030020000341c0e80e9003005444842c0100e0495812201c591014400104044580e0000c1e82c0070507400706801e211100400c0d0308581c03c0c0c005541c0e540020404010500044110201030000e00412884140a02d00455001c6803200c1c50180b01d06000c3e1554010359000307110104c1c400c1908000c2d51201c90107140070440b2118082d00464 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 713672814 1250 713671564 713671573
    0x315042007140115050d0f0609140d031104050a180e0706030911030f06181006120201120903051c020d050103030f09050303070b010308030c0f070f38070203040803040f08 75
    0x40d004c84070011240c03d80384014901c0544a8003900c070002d560b001b4981c1100c4550b91032090b4004509818070403100c0c42c40000c02050980300702640202a503644600380c540180d000c3c84188215034400100006550b2005410603042000e003d8034409080d524800403c00e008154010554a82c1134001c04c2d440ca005000e48040a072a01d070130705a40708000305407083c0300e0b0031800208045602c21700407550030030521340c11150030804500031002122225848000300e001241707089011540c0085040402c1403240300204502a610780700034181b80b0032500d5122568009280c40304005840754181c0303903d406084800c004ea50b07100c0c9400380100741100c0c81000810070b50540001d280c9000070450702800da210020110503442c541e1410440d400103046400101800d001d03007107191200401900d407517809040301c8500c1251608004003101601c1d14244460314240251000171801303540140a100036488003590360782c1c0c84d0700040742180202d8000c0d110303d001c0024001060300d000c80d1202c05540341107003541c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 713674064 1250 713672814 713672831
    0xb04050601031109160f11010203011e152a120c02041a060d020c03071e0c0906230f030706020f0c030303160e0a0506030f160503150420071401 63
    0x240d404c02102c4e00180348038003002c00d191040c4220301420000019041c81d001c040450301e841c90a81e0000d811030005a0324041c00c04a207041e0f003040000003003070401e10403d413000901d400202000d4003211b40034607040e02403034001400202c100b0070100150b0004055540c241003642c0090115000080c160700c254140000d17100c0404020451031a026801070456280c1490403000c0f402030b4000e842c0b840f10300d0000b441034001084009140d10101c491000040c422210f2a191030440540550444500e06281c01c0b401d000300200c0f41d020b043c44d10510009030540516940001d89515a42c89000f60107004440c00001c400e600051060203404800d016120710710800b0041c035590f1300046841c0040031100d0307209070704028004c0ca140d080f0950003420007002c0d26250b01c0860b01c50ba0098a52a605d00708075810001d06c0000d4269a00030703a100391602c50b01d581820181005080c090001341071080355601e04841c0c25000c0610840381400141801c581c45803281c4c244804a1714114140f07255550a01005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 713675314 1250 713674064 713674069
    0x207060e0607085e0f0b0403061401271b03021216020304061218140d030506240403120305090d050405150c01200a0201060608090607080601020a0b040506010311 71
    0x49054000900c51446003800304584c2005075144442003030038184255640202d8954143e103c02405845c20b969425907440ca0340c84d0450032206a0848015803100c20001805a002440f00305005844403d0961619401140c0d8020082a10000c1000e0000c42d0f003521550760354158000d040100c104016103042a40d60304450f80314040e0751502d030740060300108010f11600d40901d81034218400c81c4075000803940074480100ca030700280300c001621600c15440c0c41c0a40d5030b07002c0110484151070f526050206040050126000a1041140e030b0804004215111801d100b4081950700a40c4c00c0108461264070596015006040540d01c0120700c0c040c1c00000c2d03400502a400700d5048982c058028030120103217030b5640302503400112100f000781d500c60369010707881d5180011080442d68045499039455000c680c0103401c5500c00c3e800103082c40b07107102c10031000842c0800c0341e6034020070b6814800ca00d40d884d90300403400c0c0b10302100d00512952510342404244400000c4d01c506031f03449110700c0d1458038180e008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 713676564 1250 713675314 713675407
    0x402040f03030c03052710110c04180b0a06090e150c25050d1e0507080708070b090c100c150b0310020d14160207060e060708 55
    0x103040c900e80c80c114001c00000303100d070806070079490013850f2050400104004103921400090404802d03080a50024103292611200345003981480307080c07034030025480a10440d101e41c0c0a4200d00d02c08c507030b2441c0460580300310399030008066070b0010315070702d0030320b0154901002445213006107158a80f518400c244031150004803151748018081045c0384075511003404086a600c290b4170310340000031381000406103081d200d40c4141b80910800c0500103101880310010321f07400201400e085210304c101c20713080700c564116044580c0e442d00b15035902e0340c420280c1030604492080c070000070015a0f0304010841c800c10041004a5045812903076480c003640d42e228111401562803a0183c480341c07022000005500880d404001e60241c05000e441400d1600d5082c070b012031f008140281105030302c0d46582e110703001000a0481d800345001c0740348280c10320b660034025034812140c050f010a000300d4200b486907660b6014151036030aa4040310b90b69a55044494040c100c845c0d058003001032001c98070708076990502034030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 713677814 1250 713676564 713676569
    0x1240801090215091302071110030612031101020906040b0a03050c58060803040b040b030a0603061107050d090b0f07020d050607030902010f050a09050907030b190501030b040204 78
    0xf00540e8000b8141252221550303c0310181551048140c0000f0f42c09105500180c140a8010709610f070342c07480c484090001004103020b100c0105490300c181071181400301d21020642a0701403030031200c034541c5404000c0c0288164042107511040100380020744140c7c0d40010059004c0701d81d011f00581c0c84a420214250060220391181001c1031116000d01c0d9071429107902200350ac00d140320304088916055036240141c400703484024070429150701d105c0030410740110346c01010790100551030580b4004406401d80264005c5071402c01000022501503c2c1640110002c0d540003a401c000100b4040c4030246103505c040400c45260250310710004400d801030140c0c40881d181c003202e0030305d400c805d030120389126801040c0890348080038181d07441c080707201005280c2c4520400e407000954203559000240101c0b80070141d0004000042141482c1d50740d00c0b1192504540d810794054202c0c3d220484d00743c0c060300c01703800c199800481c201b030030300400c0844085c40d40890b075081c0c07000c000001029003032005034071450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 713679064 1250 713677814 713677819
    0x1b090605040f060e0102100507050415081e180d0206160c201c060501090623010c020a0302040903030b0f040207050316030504030506010f08100203070f110f012408010902 75
    0x5000c01615000e0100e01013418014410b80f4944070301d880700c46040b170b001503c1440028001050911010001c8100e1591a11440c03c16807024070f40251b00c5921841d141c1210100d001d590030110300c01e0320701d44a40d030882c0c1504805503208400354040c000d650311001c85200d514400804603250729907002c0c0a01e04d080507001031010309900000781f84004030f10201524280c0180f0f110301500f40e1211401501c9094600c42c00d804a000e5150203125401d840141d000000142c400700f1480302d21101d40101c10b080f9a00a007001c3c0203103002400056888486a80042c0d005400c000001d01007690690204100344410ed900c86601d007100018003080f40211070005009500c10000205804a00c4490924451091510914094603070b912a800e0a4082e4444a44000d0914041c0507003901441191a010f00808086007140b0702000300030b1580140091001c24010713101e5250b490080148961541c08119070300030f01ca08815120882035003007681383e001c1d00b61a85103202180035141030040106080c0c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 713680314 1250 713679064 713679089
    0x303070305090c0a0605190f050d0b01030f020c030c0706230f070807080d0b0f0d060209041b0c05060604061d100305070308041409040201080106120204091b09060504 73
    0x114001900140360103403105a00b0311400c07080701d03011342e603201220000d000b1554640da21400125005512101100c134284207228016444402060748201170390580441c1e0003022500310f0200005030002c1590380f6820003000d000113508111140000001d200c0c0b803224900b200c4445580e07640880e400c101ca0b281880c1d181d01c140710744440d51170b24030b809071454204010304e071071070b005940da280a069440078000319040710000c143c01d0102c5000d071150402044c001d480208420a641c0006145a00e601100500e290b502040c0e040342a02c1d5507201d0b6014404000c007100c070088850901622041805000b19000d21910300021807600f010f0140344100c40d01402c0d07906030f180d0346031700721244860020301c191415101142d0000c0800e0041041c10700130350160b16115903a0f4102000310402c460801e0500380a0326100c01403000607640500784504523074052400f040c0c0f800a42251101a00c980e0f805aa10f260a000e8150790849910240754145042070b1034000c452070b6a40750544050050344120300304901c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 713681564 1250 713680314 713680321
    0x614040c1d0903160c051f08010b0405060d0c030f0f020d0b01020c06070210050f21060f090f13050f010b0111371b03060c2a050f06041b06030e0303 65
    0x65a2005502540c805d1440740c0c804c03611000428083e107000c5000050309210003008050268114030035074003400803d055030389040d08000109000344942c400381d05420b0742d03610300022506c0c42780d4015441e01d07400010038043c500140c10388a01075049001c0b03007804c1d031703103482c0d11500c5075800010201500940a03044030708050315030302040710000c0c02585440c10b01008021720100703140c03008020b0038244201640d108440c40c04001c2d0103481c61005244d10701a6543d100500e00c159102400154000d403000d000700c405a50358080654420740c401e10040c824401c3c208a150b01810641000c01c0d0000700380d0340c1e40c05100c803140302035542d080450620044060420320b9245112007600c0c04594244100d142556005502d54641480800c207100200c1648a2044203000b04082070107000c24407951450301c00c0c44694640e840c0020180308003624685640d1f003060690070001c043c890401d0b00742170364003502ea45103040d0600510020600c14130a90050481d80041070b100e02030321620510881e440021825940c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 713682814 1250 713681564 713681587
    0x20c0a140607020d08220b040e0a0c0306170303010513090209010303030c0c0c060e03070f0609060c0507031403041811040605090a050405130c090b1c0614040c1d0903 73
    0x5010300c1050760840498949500840d01e12001000c40b40c0d01b800b503464044210314440c1303e40001541003107a911804200c100b0911801209264100c9030b0b0203000565104d0701c0d04c05038001c2c80c0755484480d940d000311119103019640030006e14101c40003690f11a154508110003a412510701c03d20080d8000601c0c0e0040c804280700368410285540d031420320084808046e1900036030781d070056000d80000340c0b0a11010113281030500c1010300400110410180d03240c103082024002014902400080226550009080c07010800070200150741100e50854a00c029011880e180d0b8041e0003806001e10500c058030001c851030340b250364071090412901500b0b003800e00c0d50440302d036800048965032203034544801023556561407249a0050540040c44011145a45455940100319500558025203003502910003901c2e070103c44070203001860001e030041d40840c07804000411800141c0c500034581c0740c2c2040204440303407410320180c0c0c0410710b142915180e00d14142c038091400711114540e580040c4161007040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 713684064 1250 713682814 713682817
    0x1a0a0c05010204180606030c0804050304051512040c05030f1c08150a0f0617040b040212120a0201020a03141504150819120f020c010f0e041803020c0a1406 68
    0x510a40c00580341c0340d62914400c208114036102501440d68581041000c20381510840d00c4058071414100481e20302519869280c0c0102d00c81c1c030b8003498180980103440c0707111108907038281c0080301040540d4207050034036803401d81c01da0050138001c2c8110207040708207100000d01310340780710203640303101c103061108041c2150506805408244101c140b141c10f8a031136520480b0300f2000c0c0400c2c50700318903840c0c5031500c000c180c00c0e1503481c0344044031943c205100c003041c0700e100140d0f80710750151020401054024000c0d4035109440c030042089c81c1c40491284072072035040d00104696000c940c2c1c14000a8a1002088281401034507041c903c40000c40301c10036181003540016049a50b89160b088107565516080d6080000302c40c00c01d03107a1a1941110340422900ca07900505280661a211020500c0c9900c0a0364851003a1f440c503040c0421620440c058038841d17a80754603011405801032001c1e8054600d941010f01d20b0000840140c012603511001e1030034040c80500840781c0c0390580b03400340e01880b000d00419 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 713685314 1250 713684064 713684087
    0x803010b1605010c11010b06070c0b0f090a06090302010221030a050402040f062601050405071a09040e030318030307020a290408030f0109330503060702030c071a0a 72
    0x81c070200c944000c0201e5800e10500801480d9170701c44114841900a0f8942102c00321122948503000c184a204041418054000f040d145011034065840740600c501c4030840c002d80100c66804000c00034045036060380a011141264400e0b000c40b010031005414403294203030250072800a500c4144002003803130549401c91030b040b5002030310002d208250f990680341030340e132143c20000a1b00c01d041c245040c04031160f450010401d40b00c20003000103041544d1817549030302c00d80c481c0209156851b9414000305880904440c60000001c00c208404200f00d00d1302c54882d08220342081c440d02d20401a0101c86002100f124411102640905080040d55803440d050450001c4650034010030040000d50b54581301d104103020701e008142c026103c1c502501d240d035802d10160064400c1d24100001e0701155400302980030b081c0703d024003056480007818140c100408102c5e9100c0c1d03506215420034424103d401100900100c504402a6000d0b40e0315510403022034040da00518041e41e1040181c0e04410740319504071401d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 713686564 1250 713685314 713685337
    0x50c160201110f011a03030901020a0b10050406030308010e1501091521020c19050d050d0b090a021c0915090c080109060f0f0b01091401140712030e0a0803010b 70
    0x91a00c1c003260b12038507141d0a900b48a10b030380c0d51400c1c0c8000e03c003401c4000781019503040300158582200080001d41f05d101d642c000810240781e40c0d000c101c40034000040880074040c007400c00c03ca560390300c1c00e004003100380c02c1c4623282041d480e00002c80d045e035103548608150050183c6842c80c51600c0d00340855046c0c90078016400411505041003014503d5170208401e0b0512140310240c0c41c0c0141e046501c3c14071503002017101c0703112401642c0e00c00207480820b00000c0c80d251801c0c11a20b070203115400700c0c0a4060380e41d95503802054078041101d20b0440754003401c42c8091212015140c1940141c0142c102c40400a0180c03d00307180d83c181204414041e045032101910625106103001d585031501402d548041301c2c22940b182c0c070350903844404001889542d045c03060079101845403080711000030340703290b003e0300840300b00c07807049400502c190b4081c805180078000c80d1710000741d8501c0035040218602184885010029081540d407069001e80000e18031078840d008a24245140d00c0c0c06054851603012042900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 713687814 1250 713686564 713686577
    0x204061d191401140907020d020d0509150703020a0b06060f040504020f071a071e1209021507030809121e030601021f05090c150706020702060d060b070312050c160201 73
    0x1084682c500038000c0c000d00800100c1c00106400c60100a103d0b0300003080d12003107512400240201982c00512031000b0031850400b5a82d840300d03080483c10250301c5140b00d9940b00e00005200d07081543c0010850400f9001e41510365558071080c0400c03030140315003100c1001084050100740203030329160303008000010509802c42e15099142da241c0392660f43c1c501d0000b811510000803c443c240d0030643d60f8001c1d05450980070038841089170041c06881014030300c104001e80e545a80c2046413200a403c640c1885490107058a0f90658580208201d0003125441d8007806540c0010400c20882e1083d50850724603032100d4440300b07000407180d204940005014604620076880c02d502e000040c03410200c2c18010042001c5100e1904c82d0342d0501c1c103c51110141c0c004d000c0b60304c1001c1034116050540e840b59500040141c7c0e51840f0f0b0000500a0062030035100d03c0d94642440029810b6030600285182c9101c1d132100150303032400c2800311003211070031194040c0107982007001241d104540124030f00c05520506200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 713689064 1250 713687814 713687831
    0x5121008060c07050c0f1e180a060303030f0b01090608040f06140f10031226090106030312200901051902010204080712210203070f06020301030204061d19 68
    0xd45000300541d10202e400d08009809030a102051101c402a0794081d01c03008800a2050042800c61400600034103a130840c1410b00f040300e6032484240710007071148110130701c0c590820900c90720082c41140b00c210b02003440c0ca0412a5011224040c221600384d05071900040c041c988281615805c20050044540181240c0340c24002042480340c00a09200903000401d249403000c00c0151900c00508022445c00a00d101040042c4d4001c400e01c00b04c2e8258981110024040010109040b038410b103005154840c2d08100404088158407030000c60303000750b0341e41a9102024080c2c00c1100c0010114510540074540c51203078070381d14400201034200307042c03510620300802184000044505820320400503500000d00b00560341c020400b40c0040d010702d00d42c5061040c0e0aa9800b6a041c00da0000311410b00051103401c440c0a00a1040d281619002002c05410305514a4203000039802400100d204514210010889080c9204003880c01903040c412f180a94071003840e225588003844021030038080d121900d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 713690314 1250 713689064 713689079
    0x506030f0709050f250f020c030a0b040611030f01051509061206130b010512062209030f0e011709011806061a0a080f190924020a051210 60
    0x59001407211050001d140d040c0161380c4401d000c0060308040002903101d01d039002401003110702c102610814244422640040501603003010502003c450341806200000b80c20f0150394400184110701c00c01c2c08000901c41c030401151940400d41c2c4200b01d082c0c0740f0f801840541000305804050f01c24600d50282800310790f07000500c16038416248803041c3c1c6010400d0004038100a094201c24549c0c2d203009100d0b90702d1020000340381c1d004901c86c85403c1c1c405a40420b54a494820042944400718440c1c01e271242500c52101010b483c400c8401c60025020702e0076030a50f6481070040c0d4030b950005035102c02100301036800d0940c00c400c00bc1c00c82d0203603540c0c0300441441c4200d16002080e07590320030a0089100351503c40402041d04000020100189082040e80c50301c561150a003980010507500906042d01c036040030301d0007102e0f4010400e07801d61620401005010b0007000e1792988800280c50300c44400c010010700c405a001d410349000100c1c100740f00492103200d0000c0c0c80303540400044003425034560784054 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 713691564 1250 713690314 713690323
    0x6061315032702010f0201020c030d020706020c240916030b330315060108040f1a0c12060d05030a0522060c050618060a0e030c010609150e01180506030f 67
    0x2d0204207414104074038001c658001100151000b0180002c5007841e00300341109840340314500c0302901d107a40c0001e1400800c00182e06942c64000213004554001c41001005d274943e015202c4407031001c241c0d90b0005100b14400142d03410b61010005003030307500e4516540d83c041080c5005401c01900203850203411080340c1c0a40950680d800c40304480b01400c06545c000d05081500c3d110760308030407901c039604001860340c01444c0070360440d03805810403d030480d103400c1c04107890103941d050181280014051001c04000440900101d11a44440300e0b003039141d071000c0042c50001c4c940e00400c20b4000380704107100640a4030151180da11003240c29403031a2a21480104404c0c03d135005600803a0300e8580b54420b01c0b5042202684c081e0590100760600040d041c00d042e42c03008000e044103000c1c3e1b119154095181e4003442900d40385007048009120550700ca0007070304050410508156089000c0403000103280d04c1c40c4900504a618680030940c803100b20541140181c82c00808158040c400c0d55458490340b40c0400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 713692814 1250 713691564 713691611
    0xb100305061807090f1d011418040f1205031306020318070801050403020f1b150904050f0a0b0102190b1e0408040608070903051b040e0f01090b0606131503 68
    0x1613138607031aa8102000800300301d026800c04869040540102c440c010b20b039002c2181951040c01d110040c04803444c0004840600c3d17981e44064880f201c20a2104100c10407000180080c4038500c003a01c000c5c1c0c1c0d0101124903000845186500f06500d401d0303600404d0300d55000310b4200e014050b941c0c9041b898400b00340c0c070b400d07003550005505030340d00c0c010841415410b110701f1f0032501024000c5c6c4074001030045201c01e02e800f0811a64031070801139807030442d1441c01c03070200d0310b503b68042c005000ca0b160003440903101030000c444581409040c405405420b600c00300d4440500d903070403000c54940144030b07201d014011800409002c449010011000e58581d6460702c007500c44e62250a4841e9140d0814a0090400c2006403100d070a0002080702031000420100e50301080b070140040c1c1603a80250480081c000e00f079203100c10000380c09440a03420081d030064020302d00c098080e2408441c9a2540418003c05208004110403035010b035040a0080584140589078540f0341c0f49800300c1c0b0020108506515442d52a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 713694064 1250 713692814 713692817
    0x31203040507051009090c031506021b010302031b07110919150e0c0c1204080c04061d011502150106110f010603032708120306130b100305061807 64
    0x100822007001401c10045003d840e00307a0f4041c1c1c50201080300604504c219001e81d140e85500c0d401c003101d020f032103580000304041a0070340001c119035a80101a481d278110241e4001030009110101c0700f50b5010340220b9004c0c103480400c58020020210308a9190380101d6001c507840140508842055a16140258020000c1100e000304850015540341c045805401500e00141322003038040044030002c0c1a22640160006003003030b61655020282410199203034090f0542d014080f0b0080703018400060307543c0c5405000c1c0d8080051648481500341e21030290342075440942c000e0300040c03001c2d0105811141c01000b060044846411164500a2aa040c260014000030324580441e655032001000980c1d0080b203600300821002c3e045450007042c500324105ca003580d06501081c0b00001140036880c03680140300c03400c165800540b41d5103181c09140d0059402c0ca02ca403141d1210800c0c1e411130307841150a000c41c000d001d09440e802c280000c1e400b80100402803a8441020600020740c0341c2420f071080d108403000e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 713695314 1250 713694064 713694067
    0x3040b03100e010e01120f03211506020c03030702060a0210090809180f070305092506110313050d06020403120e09220822170d050702100c020303090312 67
    0x2d201e81c0380d400890580c01603202440d84401041482c1d500c0c0300000c5036a0b08039102103080c550906013621190400c5060396150b890484a10b2900007080d84260788c1c50100f5100034140310b40d20130049036105812070061758190410003807100145045401000456446c0c01a950248401840301c0211480400151a280400240619030b0b280c0344451400c3c0d07201c20300c10010760b410110035806c96843d00030140828180e6440104040c8a4100800e0b070a13000722464020514a2001c4041d5000200e44100e0012078a0711544188500c40031040e6903580140442081000c0d14007030420010240c01501541c00540c01c11000c0003103200c2c508450044003c640b500464030710a0f105018a40c5c40092002e90b0780180d82c51300111300300160b81b51441d2182c000d14131940f60100100c460101d040040300d00c0c090300c01003900c00a40300c801c201190071044103c038180c800000ca29801641e0303920407030500075440308540385034010041c0190429110140064200d80c20400220301080c03a0800008035009003140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 713696564 1250 713695314 713695319
    0x3030a0f0b10021c090e0420060703020106050a0806010b0324040f0902100e03150a0216031e021203070804050a05030f0418020723010906050f0612070503060105010e010203040b0310 80
    0x40e00c8500b040c4d50300031340c909910110715010f0200398440c0003030802446c0a40744074611840c0c15003081070700d0848600401480c1e8500d144d141c082c6c001e00d0a0f22445000301c00c03800001a02410200350a03040740c105420561540da1440751448403000c10170340402102c00302a00e02c0c440b070744480c403e0200c0d00c001140d000843c89124010004809480d035a2141008908500e904590304c01080d078000300c44007821311126946403031420201a00407002258004071007121840181548040010304d940c03205001d066401c65242e03812600e81d1104010101020b004002242c4681d20550440364058092419600601c02540e070340c0b400e6038448081c03010303000c0300460140480701c2c1c5804031010a28001008510b007840661310004100740c0c10b0b000610b001640c9480ca0020142900008002e980c0240204854988003174144050b15040da0402d014404003540d0880c45c01c1b00003a130074143c0754010022305550f842e1000455030701d866114030a0441c0014480081d5046c0404040c0d400341d0000b01c1110344490 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 713697814 1250 713696564 713696593
    0x6070c15030e010e06060123070f052b050304020d0f05070902091302340b01030302061e1302090a241e030804182c0705030c0303030a0f0b1002 63
    0x11803030a01000d098000d0018415907a81110078003481c1c1c00038042e56000c0e0001285011441c2c0a12200500012a012b011004210002c00d030718801e00e501da05505c40030040f61486940300c1c50b4011003000801c0040001c98050714000d0403540d1544d21174000c00b82004215528181013020300e610144600d500494064881e00c5c0035054038040c8075204000318200444d07551041d180b42c40000030181c0e80340403800c030b00c0d10103941c0e0618a00c000380c00002d510704e0355a4a24000755a13110031210705441101c540388007056100070800a038042c4140f00c51264200703400f44c00b0030000240c007800f02081103585031500e40d8a51845148812880d40951800b00d64510b08a60020004812140c400c004111000c0500005444030261019600600e041c1201c403d5280c0d54240100b5100400d101848811000c41d40040c400304204150b1006441c25183c04550311000e241d542d00203040b2700c40d8107070410300000e20030317240d154450302400340c40190126155011802041045103202514401030708071300f410300f00c1036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 713699064 1250 713697814 713697821
    0xf050411010203131401090329010b030112060b01260f1e0c0703120204090c2a0b090a120c0317060904120e031015050406080a0206070c15030e01 64
    0x300080c00a1072502111461008191045001d00c00c0e041041d01020301e041d0340308546100285a1061000c00000005c0e1001c100011400c01070031440b504000021030403200d400c00713481c1240c0c902500d41e95200030340d43d036002c05042d40ea4003850422885400407074004600305410440f0898080c0c400b01103040c941050003c2440090803a1b03513803103103107000300c403440240b160b020f512500c2031401035142e4410745411940c1c8442d55010b0303d212800460f01007046000c56000b0707544103503143c4070002408000204000000100061b0042e500c41c0c403410341c5d0100f000d18050703070703800302882041e607145c00303503550380c1105950224060000040019844030100346d0003440309042112403051490551911200054100f100240010039629803900c0d0034404a0090070b20000307214008090380d540c0351011080310024404000300d81806004a000040c2909281c8118419103c200c0d000e4000e42180340c0030f01999500946080b60780414240c400642a1003000c84c10051203281d98000c500c05034061511070a4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 713700314 1250 713699064 713699093
    0x2040602060105030a0b040f050c090c0405040b0109060f140d09050c01020d020a0f0311160e150d111909020c1b0910090f110705030a02061612110702040f0504 70
    0x6a404201200003003492141c065a0059120440c2300c140b4000d45421030400152815071034101c590034090203945516080500107541c1d05a40c10842c03071105600440f4441e201c0d10801c00442ea0310390801c1a002d01c0f501c1095680a00840120301c1c12003c2c21480c82100c41d160415202c0e03070440c01c11b0207003d680c144000c4500c0503041c401002004016195100d861000b80f5009040c060b108001400010b001d024030310790b01443e480d5005da132a940700403a50101104a42d501110724040d0704014182c50100111038140d0b0b0000c1400b010071a40d807090080f880c3d0070800b0300c10707601005200050703103c503280010000c0c0340c44400a010303504060b415a1000c04440203106100b42c0d22481040000300d01d0480d80e20449042c55004030b14148030031206030080100780a4541c0c0c00307200042e0700086c040300000401031010241e08484260750748400c3d0395582400c60490a00141210054100d006605d401809095a1a100700e516141c2039034009000c403015419050030481e124400c101c1401003151500d140c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 713701564 1250 713700314 713700319
    0x1303020a090c02210406081e0a1a060a080f070201020c100c0909060332190203060c04080604031119060f050c09060a1211040b0d06150903060e01110d02040602060105 73
    0x44c69180400035900403802900200070300f50340060791300c0c140d10801100c4c10010381e40010a5040000f80b150150207058100b4000c2020503000350421b00300700d0201d41c0340c80c2c40d540e03d081030f680f54140c1d00d0102c030b030010700b0700c0046640a00400b12103074803e2205c41400061541c0004030034216400c05419070807158001c034403c0c0c0c5044020000705221100c044202d00154a07807141c44114032034600b800c10b1000c0c500c4051071082c54640c480c650560104180d03010f0084088981c0313962404280c100500c26400f13107481980081003c9000240105002e80c0084000c8050740e60600c04c1c0c480031280307440894000e4812507124002c20541480305e00c141500100015055441c0004841c0415001d00c41d20759094200300034000510310b0010f007075220900120000d401c195031161b481c82c0500c02034000c1441c203440c1e14a00b007030005414280440300000b2206039107541010a1558032000000e0000c3c5d84918059521100d0041d1000b1140000b4038072160001e9005803524200781c0d00030b1400e0f030142c22450 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 713702814 1250 713701564 713701603
    0x11112060a051309031101020c1018020d02100c050d1e0f0813050102090d140f151314060405011d0303060d0f14161401050a08010b1303020a090c02 65
    0x760b8544400a0183d0060b0303000c08200c458480c5421607218081e2801c980c10b95101080c9000068004240083d2800d036041050108c04283c41a0046150020710000e50046a0b504208018100b4010010f120301c49418000100040c6440b001d040a9642d5010400641040811006103260341c008030032441c0c80b480c00111424401c007003e00003080282c0f03103600460a400c445000c02c902501150341102002e0021018090750f8945114203220240402d240c0340075040346221500e000141c6441e4208100c8011a6191941c2d2000c841c0c2400a82c03043d560142c05040488582408001e80350080f889140001180c803211491444103c0841e411001c00d50030400c10301501c1d40d03844141c0f03000c0f0b81d0000c41c1009882000c0c9044900200c211003910240d010780400100b81c040da4402e00421170f10550013601c0c1040311302c0700441e075521403180c1d03036004600a4030041c010054482d0140a05102e80030499406a0b01d940008030714000c103038040c60b0f4291302e65401918140c1e041c420a40440b03c03071a40c19 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 713704064 1250 713702814 713702819
    0x31c0b011115070e0402071712180706050a120c0207151803060f020415030b030d0c02031e0c060408030c0c090106050d020f040f08030d0c0e01171008011112060a 71
    0xd0510b100054510030401070018504059681d90f07a0488915541c030041550061903441d1980c641900501c11480382c001c911000280014440341083c40b4010b8a070700600b44a41c14a50103a580d80c110003060380030421100c0c0500f0b200c0c22148035082294002d41c00908407a441c0031a000300d091400c3d4500001c100c00c0a84095890945498070400e80b40c0c0300d100401c04d928081460350003270081c0c3e8010010108800344084003680c1542c00800c1d00d84094007614015075003444d0544104110640c000d40692013481503902c481038200c01c41c00305524880a540a01c03802c48000744075600150040e00d4140c000241516038600c0c2040314600c2c185c1c00b960000b4841d0314203c03002c2e01500514040c60081d9400107940c2207441c0b480c004441c050044012104d5415490780e0700140d4070b41014110200e501d16082e001520140114182401a03a05a49444940c080302d0f82e08480740c9006400803a101640c1540411039000030300800751420202240c050712480500100002998060240350103520550001e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 713705314 1250 713704064 713704093
    0x1090b0c0c071202120613030315050d20040204090c0e0307120b041a04060902041a0913060b03010212040201170103050a0303050705090d03020304050102152403031c0b0111 76
    0x902007281c03044444100f10003854000300b0344d0b59022041d103184c0d6000381401c0000b225641464103261a010340d900f0410044244001903030059640106d550210401c1000c000180307254688480107103118200303001ea820b0480214050343c001d50400d8540d01e03160b40140507460b0f0301421840125030110010b1448074500451103000c0c1c0c4005101401e9a94808000703824049040e1071540902c604580020302d5103483c0c14010014521f24004900c994200700d62400c1861600e9111a20144014144201c1e619400b5a11660083c011001c65140e0349640290b00b0070340e02071020301781d10f4404040744030107441c0500c001040720395410915400100d0070401400855800238071400516031609000a81d61200041640c441c087c0c10301300303039109052740b00d690704243d404405442104e0080c1c0072680e030090343c2180c030030000001f260b4503245910307100889030128000d444da400000030040c007604c4c9440b5480070000d00d460b0440d0122800c40e40c0310651900c4a5038400c8c9060440d00c8520041e2504090ba40d56 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 713706564 1250 713705314 713705323
    0x106120e060c030a110c07080606010906030b330d0501090b06040e162f010b0a140f0f0d0f0302070506030402310f061a04050108010902070c0e0901090b0c0c 69
    0x2c000545680f01e4140030005c0c0040c1c00c4071380e0345074190111840380c0e0759580055520003084540c0c80c0000c02c6800e000410900038028941d1a00e00140820205032101c0070811118903041e81c10850035402c0300c162031000059900400a60b001c403d00400c40758100003000c01521240d005960050400b004200301c2c1c003140441d6103800510301c50920180509281040344e0000c8180080184503640c2c4032160054440c0e01000246244821f0090003103884403410080e06113058494000c1620042100c1c8529240031103000c8022080140048940b04094003c60744000e5504c80440f40041c19660b84801d05804000000082070b04942c1c01d40385240550110341128810000d4020000318410b00da4080c8650823680307850310300c480f582001000345c08003080d0302030240b81c46414884e61100c400540802070310710488041d01d806844068140e440c0c8000c100003035201c51000e44803031035000c1c4003050b82070001d42818001c0a0f200700215201049052000303d03041f004d000401780751010030040d25a10310214 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 713707814 1250 713706564 713706571
    0x21e370e0d0c21050d020a05070b07020307050901060314060a08030901050c0f07030c031b03030516050a0222050c03040206030106050a210c0314061f030902090702011b080903030a05040213050106120e060c03 91
    0x604d81c0d44bd41180d10100e4a0030030981c00403548007801a00208403250705074880cc01544a4880c1c0f40ea103529818140400750020f40603101c00380d00100310925175035014000422002d200441150259910351107164100310054004423011031800f24200107010301c00c11000e0403000c0311031814602e01d25582d40a001c502c5000c80012100080d0712110041c0801070160104254014010b01c00c04d5000d404100402a2000554a41e9500d0180400c24108405054a114580c054541c500c1c503420b101c01a90942c0203900e81c2001c00540d81803c9109448082144003042400440032505082c0500e014060303803e4032007202e1440d00b00360100032550384c070380007014501c1e4181442294107980a00c400c6014001540000e5040b01c5028180948542c0c15400112140e02c1509141c505001d91142269116002d944044180e441440490240c1d85550300c45c50b0054401880c40854405941e41c3c0c100f5100f0980c481c0340403500700c0307600242d5400c15005602120944902810991400d62202c182502025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 713709064 1250 713707814 713707829
    0x5010c060b06090307090e0d03050c030703050907150f0908030304052a06070b1605030709060f0c02030f010b09090102070b0a021e370e0d0c21050d020a0507 69
    0x1070030106481d07100c41c001c0f548280e0002e019595030a44030340038440501400541c59059201700c03000302814070701c607114507401050071090440c070756150789800320046c000162004005d4000d00b50000340c10400004152804040c60f00c07a040002c00c101c0001d4044c8196034040c08079500b0800c100700025402041182000304180d41c1c02da070744200c4e4240f41c400050142c5a0715007145002413140b00380030314006203520520a09445c0014a030f0031038002c0300c49010580f00000821807201052100c00e00072124200d00d91018500510000d11540000b032800c11a0447c41e10241d41d242500c40180c03c1c0056240c2c2d011034003200030341c5021860740c0c48070780c0b6100003000005059408190f40441600d50742d4154203e00d0056821901d51121001c980e01d0303503014111086801c103004620312100510340b044c0d00000142510b407400201a100c0c14411001000c80b411525254640c10101d80b110b018101d104601c0a1322000c06840105450101e1030101c941346909e042d03500032000c010000340d0009189007501c40300f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 713710314 1250 713709064 713709071
    0xb011106040b0703110f0d1104181e05041a0603071a09030c03030403050601090507080c190c02040203011215141906050301050c070209060d0804061d030f0f1605010c06 74
    0x10f4032012002001403124000742c0800000b0300b614104c520f5405840c14921b03904003004600d0400e802d00c4400e201d6481801043c0044101d291480c50044d40601000c20389004100386003203664541008841c001c40f8101c860743c503801c2c201c0c201d410300000b48136849101071313000708104d50030903180c0c50392010000c4ca540d00c83c040000d5140e0003500c003400394099002c0e0240841e600da42c3c403480c1c40f81d10384000340030342038041e403900c1c0001d0240380c0300d41c0419000d140c02043c1907281803a01c3c00f101041121014801c0b0a100a20500000613125072008500a11258400c040c056425161000340c1119601e800f00c01c2504084407a20b19586240c00990400301c03406040411010302c0e403140c0b000d08100c1d408564154640301c10004d10042d102d0013040c419200311a42d43c0281d5a0408009003407002180c081d2440e1804d1105009944c01010318000a503e00000d50503880d119070000307490074210700d40c1580c3c01d030850120114140d0040242113285148030180d0241c42e410403000800c945150000034101c2d944 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 713711564 1250 713710314 713710321
    0x14010c1709030c03070314062d04111503010609050d11120708010f021c0c02070302040c030f020318010b01050c0c010806060d022809030503090d06060b0c01050603010b011106040b 79
    0x2c0030007038520207400281c2580c480c141d0760301740800c403c120407a4030384003401500001104440b581615105400d2190b594000101d10040c8440680800500448000628040f42443c07640d4541090840c40c129241043d41ca40c100500106100420b0f40030314000c03581d0380c0d02040002c101c001800807104080c0c0d00c4076003903c0071403e0180f80c480903a02c400d0713065280000c2003440c91000d800070b000700c4600c28507044402c86001040340440303041115940c010b800904d01800103203070540000034035940c5440c021034405e2140420000301d030f00503942000403405c0e400f030003181c084083c01000e4034880c0034205182807a0750450ba094803080a000d0701030400c012000002c00560781c1c1c0c1c06848902c100f03020708546440a11468400311400d29103448515081001640001c0e48560035801c1a00c4d801000f450174081d150702842241501c0b0981162819103030361000c2041007160014000900703182002181034242030041c94215030f04030f010141002454040c00c0b550301705c002292908035511007140881d540c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 713712814 1250 713711564 713711569
    0x1b1c08030a0b0d0602090f0a1d07200106050a0b03130f051203070f0908010e070b030901061508041b0e0c0703022503020a0902030f0115052214010c1709 67
    0x10002e00c099030b02034000c0711080240701c1141c1c007030407940b041580d441107614024420010031703110300e100301d0545a150340341129500a100302c50f00c5c0c200c000fa05064070b042031040e01d10f12050445400006040e903542c14100154900070708c12100914001620502d54140940d03100e44003507244c0c002801c00c4207034616510421074104039501900c50801c031250340700d00b00307214014121541d250b0740100080c0200340100d0422418450050040044401080c810349000c0c07070701245070401131041711503542c0e8440000c1e00070030220501d00743c00c10070398801881745031034139002a04620f6100e0000c03604860706003d11100900c8400306800c48440d040c0341c0e0300e078007a40c80d04a141a402031202c0c546402c8880030071042584090120742924800c0b20b8032100c0707a448080c00700490100306c0f80481661ba04600400246010224040c0d111159142c003902c1d240c00301c0c1160b8680000007a0000c8c03c110445410801003183c0312001242c5d803024a81241c107441692511021140b07642290601c113440000d01945c00d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 713714064 1250 713712814 713712821
    0x80a0c08040b030402240306040b0f0406030605010503070b2b0209040c08090f011a0607081b06010611010b01080a0e0132130b070f0e121b1c08030a 65
    0x103611142841d5916241d0214500d40d800644d01203004461a03003c5c4c07501c01c04080b00c40c0120400443c00a815582d0341e404000103400d100346c05a4018040410401143d115805a14051406194042072651500091503c1d0101c0da9109161a29092210004201d03010002100550040041c0f030040c980d4945408001e10491070003d911502d8082c40c00c0120760001d001b02d2150b40010f0683d10758030a00410142a5107412181c40358900344001258214685035015001c814080c980a03410506036000c452080d84034502082d00990100004011281c2d1181c003c0040c80041802488080710b45000a0074101c0003408040c08a0f4854200508142c1e00750704c0340d00401e011a80c161180000580c0040550803080c09045446210100080e419013800038030700710b815405140f410060b81c45020407104030413031801a80c20811090400d4417181c1d501c00c4640c3c12201014040c00d20800b028680452100007411341034042c000d501103c01a00b4218a00d8800d4660885810740e5695075600002c2e004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 713715314 1250 713714064 713714087
    0x3041506050d140c240a2c0f040e0303060f030c1804061a0102060a0e01180b06090106031104050409020a1d0f1003020f0d0204060b030a02120c030c07080a 68
    0x301c00300d912610107000455840c000c900343c10b5802d031211030f94110240440c0604185803408840e6003115000120700e410b0300202030311003003071030014200308040c0c94859084010388469590120000c02608480c50304926030003d4100469042040a1000d0f105984901006040e0741c0718802401c40080e45803418050120425070043c103c5100105c64047d5020b0f00c4c2c0b05540c2515001d2400400d03c04605030700c0c61f0443c800308140c0040c03030203527542070140d002b1f001035001c0c56511707540f10501030b01c018002c114815105413243d12020181e182c40341c24011250b005030f01c03003400c05040c1307508190f80c841a48120750656034192000300d0300c040c17503002085207042c003940300808884141ca0b0342e101c3d188484410b41d0282400c3c0c1010002510b07402d1441070100039902000c0c0d4001010310000c0c140d45001814002690b20250010a8055072044402036941044480d440c2e110b03000524046110301003801c0fa58021080f401c001c0c03c40c18050b40c4c011590061040052803902c0000c4d60041ea64080d005000e40b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 713716564 1250 713715314 713715319
    0x2304020f04150905090703020315040807080301090603290714070525060e010516050a020a030305180301091e031106010815070c030c260c0625050304150605 69
    0x40b07440d8021019030700040d20300c100a001494080403504800c004180341c41213030f800800401d1003c00605807035417003990140c0704640f5541e0030008100081d081354081c41c000c0c002078800243c0c0910314101600b440b10002411228600c80182070f1031095090040c0c81e4000e4030918042420503440c803000c424503c01c0c900080c0070303032044071245841461301201240320001040c003912091540c0300c1042e01c8060904075038902160040c000c5c40c58002d41035015560041c00707801141c860328400d80200b00ea503030780342c0c0007680010300c0002c0c841240e400015080c1440b500584c0200062040c40d1030343d08035480580303da4201d404414400300140341c4281c110140c07141c500010343e080d035656004000c0d51204c03c42070442c081461500040c1c01640180280c014050300340e1694445076072541d072000780c011b665030810030003a007000100c8d4042000c00006024009040002807165040078529004110041d60b005045000003a04c56607000785d00900742d9422682c00004a00c40c0c4005103442400303000c3c103401064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 713717814 1250 713716564 713716571
    0x31009020c0f1c091e06081b160c1a09090604020c060115020106060f020c0d0302160303051305040504021c02030120070c050102010e07120c0f0b0a0f032304020f04 72
    0x45024480c000360f02c803086144c03107900c0b070366548007400064105d448002080d10200c6003800c000281c007400206920020150a0011402d002000c040864106a08421810014440120410000c445c019010313021161920007a0200c400900c00180701e030383c080601460701c12011402944590b0143d0704820b038200c058422540c3c5607610085a201d0b03503003682e0010b41c05d1142c009420b42c022248100d04000e280e01511240c0600014882126481041142103218003829281424101825003020358401d0b510990b540f4982d0b00345038400b0704603400052007a031400d018040145d48840c80c8410070101b0403002120200c1d030340000b0380100019491441c031703000d103050361720641081180100b60f554452104501c440351510012400c0369910b80844113a5840b40c681403002c02c403680400503040b84a0701e0300c4a0069169091110000016482095541008034000d49941e170009103c02d1164030a103420002000070070507201100072004d003101c42603168000030409645030303c1c4000c910f03400c2c05841032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 713719064 1250 713717814 713717833
    0x50109081009061d1b040605010903031b080f0403060b0a08150c0d0603080c0d020c0a270911031b0f0f041b08160908030304081317060f0a02031009020c0f 68
    0x3103440e172803040c502c140011803480c2c400700c00d46030a201e1f0340706882041e9103203240c00d801c5940503a0036032113542c0e80c085a103082c18080000614440000c2041181c12444075444a00e18075020040e10010a02d0510034204408240b000c0040029042140b0652810300b440c42d884910780046140310b06001d852104c2c0c249080801070050080042101d015034800310740c1c07405242c1400f00e8413210308041569000c82d014a082151412415402d6248070380e40c2d05110f14040072582040c1103e00202045500c80036889080b41945820b1182156a10700c100548084503108000200700440c51241c19100321040c0d401d42c0c07d0303500d4a5002d48104480003500e11040c010a900c043d002400865100d03000c5491092402400d51081e4059000c0395981d60080d4150b407196507541481d50040103c060383e080c0d28540002d05100b103a00600460920701e0050517513420040314424071000010200320701540100140b0000ba4080e5031380030304443d02c1c0d4000507111130400050134102004205920b503203200700711b400d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 713720314 1250 713719064 713719121
    0x812070807090801090b0114030708011806140c07030f03090204020313020405070203040e040807050c0604090f060b0307302a0f09030f0510021b0705010908100906 72
    0x50a000d40402e0301c4044040307a40d01100b03800d03101c030103400416100e640341c01001803002d0310154400c0110001c0075038000c540c55611380e0782100e0072214500e0842004800312024403d02c2e03c120708800041014080c220301d4207a40210f668031985a0050400011041601e0100c0c03003903010ba40510750040c0709640c0d034240080c1508100b0a24103059100d20b00c1d15004c20351150000080b903040b01c004c90204084c9580d140c41d2010ba41d0041d460a445074007800303024450300e55800005101900c82d038140028032400100b419022201150000d946a10702001440b038000d421407155a040c1c00755024400e480d1800c00d00388461420f018200140c101c0c2002641b00b00d039500c0555034080305030802c0c0c003a400c1c007000c10340480e0039044050916001c100303c01000e0001c10416032008040c01d004000b1507420440007651141240e110344000300490742001320700c0800104c107104803001000c0910740b0a080d54146003440c1c1e1100e0056000c40c0c90b1540d1010a64100b10094010403044404030b00034020722800c0300c12 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 713721564 1250 713720314 713720327
    0x7260a060902090f060c0c091906092307020c030f0c03010b041413060204080307030c020f0f012c1906080f0408070201030c030905010f0b010f111009081207 69
    0x114542400d040c504042a40c0340e052003a00d035100402041e039585809002e040c8001d40d8807a02298540e0700460151030a961149650180291070008802c400d81e030308170301e44904850040e048425454100003000803410066000c110a00c0380c0d401401d059511001c4041c0c0c548010310321281d404d1b000301108220a0000407590050510003174000f40100d50080b400c100807203900000300d5278003403c000c002c03901c440d1044000c0c0342210311a00e8018a030a071550301542c50340c1c01c1420308a00190404c1d00b15021030608140281c1c40d00d200395203a0640007191000a07202c0500c942d0230700040f00b100e815550800900396a0154441d0dc040d1a444103501c030244e0301010302e900c5000343e1000c1202d600204140c50904450301c0d1040d0781000c442420419203a004501802c816480b03c8101511101d1010110b0801e02c20240c102e45100d0000916002d441c002524040c0100001028840c4210400d5003860001c42c05180b440c502640004006c98145040c40660280001d10010038500400b0001e05503000354 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 713722814 1250 713721564 713721571
    0x20103230702030405010f090f14030f1209120a0b0402060307020a14070f0b0403030c020d0f0b1008010f0b06030112170a020d080a020906071101051b011b0e0a030b0726 74
    0xd89550130403006c800180c660201c980b080c02c0324503100c27020410440d89042414540340c60018144e607444141e10000c0c034500b500c10124000920400500320398546000c0041201500c0843e001e81803180300d03074448094034107000b4000f0f030190030004001161284207100400d8001e0b44140250200722070440803590310310340f50240340201512004041102000c0400307030380803290715030f603440d40342c03007041d0f0910007451101802120f8500c10414200300007140200303c288a030b04c09a00c0d0724912403401f4130160070b556460700c000d14290302d8440c00e00c0180e01c800c01201d0542d25002c045a41c1c002e0203103010042004251005583d0745004a00001c2207a40403449050071009583c40760000d8035000e49a900701c3c41151803983d0300a6040060390002a507210f8040c031040c005041460610041100381c140c0d800038000d100006940d80c80d80002c0000c9200602031158a1910b4450325502c171510100b141201140030243c1080c03461300000300414415455100701d903141d907411008201d0b44400104510b034066 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 713724064 1250 713722814 713722817
    0x2040803090a05090115110705090702030a091505090d050c150c0105060a0b0403030305060109030c06030f0f0203010f062007032d05101140060c02010323070203040501 74
    0x9050004840ca000c00030345042c2c0316000380985550181b0b08042e544038040701c40030383c041e0151544c000788507070321000309510988035a00074560700d9402020080800300b083d00f103003103c11180040303030743c0d11542320007603450702542528001004502418003d240c090900902c82e4400480044922902910405051194010002070049441d0032003007001100f00c038060003080041c223010030000b1034070075049260480030606040c0e10103030f100d4030b03420010100e0741c0010012a0b02e0380445818140c40b071141901150509034110306550410071901b24070354070b0344140010004c0c84101d489403022811612100142c0d41800c5544440c0d880c50448108a192a2030b407080510b100807413940c0a203c54421710b405070307105024001c010403050456004200340c09051008610610551100401d8145202c0d50900314140580c510300540080c02c85284103d03030402c90a881c6020b04104594100c44400e0310b00f982400c0104808101c44101c2000c1c0c000c194112000910800c20712031440c6d0080028825548203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 713725314 1250 713724064 713724079
    0xa05100225020306071215030813050103180303021c0504060b1309020a1e0302030a05030c01060b0a090e0717100303030c050a080f130503030106020c1804330204080309 74
    0x154049000070710030302010790540c021000041110b031042001400f0100d21071000180c00c00f119401110750503542c2c01c2101c420b4000643d0f46c9034034800007003801c0181000d28092052070003095203480921207a036030040038560003050312902088a0400c419580780e819408000e68509420182c001e845c00820303480c012003984080c01580c80039401443d1440d50003401600040340781c0610b46038181e413606000003146584103008801070b0b9003800741c20f003564024801151900004110b450071070f40b49038000b04800b00100288202075400200d0701049402405170710f4400e640f608000d540e290580b11146145440220801001e0740e8000d0a246c00d46c3d010303a038108201030b0340714402d50b03442c454801000c012400100014445180d4240b5180c0e0010311441205091440e541d186840c5800c00c2c2c01c00340151304407030101e0200e81801485200c1100c40c110090b003803400d05491b11408945081c42d45072404d072440d40d40106030380480000340018035400d50300310759850350789141507280e8100c020030921800c01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 713726564 1250 713725314 713725357
    0x62705101d0601032009040e030a02070b0a051e0d0f050105060f072a0e090a0c060c020a0806090c180405030a0c110406060f0206070f0905010f020a051002 68
    0x9440c88510207403a00000314802211400c45048840c80c030050035a4109501c4801c05001c3d8890071134511322071002c1d54046901c800750f00d0308010623121107440c07070b558640c4103000304010164001042c0f4215002c5544603691110300c0c0c0c00884079841140698041d0400f02c0403101c482085060040800c110b020f0720401550888140a0055031828030500390b210b442400f030011154200b80040c0a403d10504005803040d1030b035141e24101d02590000f00c0090b04010504200036841c04001a0780001620041c00a14240d5913441c80f05034800c0c040d10040041c0050207a045494524014015203044400c40740c2900d080d0182a83d40c070801c42d48107000b10364003902c8900742c540403107030140100ea00101444c10680c0750a4200c9501c1245c52080d500510040c0040e180e54489101d640c3c0504220755448001c0103104001900c0c142d0054820307410414002e101d41d502d2940800c021054440903c0c0c0303000d844401641c1245800028035002d0203e00910015009200a541c02030180e2840075148121011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 713727814 1250 713726564 713726581
    0x30c0e010303080601021b100509040612170a05040312110114150105090603010621090606060e03190308070c05060c0a02070b030f04030e04290102061b07120201062705 74
    0x31071004c80746140300c11f851200982e40c80c0c2028030340ca0404803490701c2400c1510280004095500b40c1c0e100f6451034908070b21940c10702440142c4e210500101d9816680b0301040307904028003901c140d2001405941190301c008036640d214100300ca14440a00d4028020500480304404c00a0320a64542ca441c01212001000e19401001900c0d01c07142c0c0200480d04617032070b2010a44000c20110310072314a4030701c10101c8858055162103414200303401910001980c0f41440409801c5080b8a41403c1c0719a0140d840020b600c40069030704080e556140c600f9058940b11400300356130681c1c05400040540c0582e10801041c8400c510180005800650898407903e50301d5503055001c0c407054440300003201580380041c000c42c0c001c030f00f80ca100b00409000010881002c5c4092807201c4094081015100801103015032251f034108134007601306028040e0b000701607224007610003440c841c00300020310b4a0014503a1420782c034000c0d845030380108030544900e402c072141d612110440d2a40c469101c1883d600e03100104a240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 713729064 1250 713727814 713727823
    0x110d050702010b19050a03060e07150207030209060103111804110703110d030c0f03050405031605102909090109050d050c0d030b13020d0b0a090603150b0f011107030c0e01030308060102 81
    0x151000340a100406c0c0c110345070716025001460422030315214840d000030726001c0b140f01d8140c504006034040e010f014110f20401c50b600d403001d85213504040c1030130500000541e100c4210303080398820941d00c0007070440c2800418050306115041882004001c507403081415084058100703001a0107060b150284d01d4400c5c160f08403214461810b001500d00702c07401704103030301a034070041c2c10500400c1120704290440003020804400c000003114550030151003010014090f026901c17400300c141540b0b8000303070941c10b4000c28000c0300c103850a02c1244130708003059070700d83c0030750080203519004010780c1d03241d002c0d5040c0a8029405030004180501c20301000440710f43c401d04c90101c811000401c1020032030074241c020000307500589074599041d5138840b040740c1a6a11080c11900070805003e010511524504085d0039554541d00e10104090600858040c0342d6100741045092140c03d00b440400e040f442c02016180c6002d58000a161449000010980c07d10414140741281c0c46550303803445564600c401261503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 713730314 1250 713729064 713729069
    0xb0306130c1707030206040b09130603080f07140a0302071a04061409120f161d06041e092102011b031e1e150e0a110d050702010b19 58
    0x24040d58001845050b0a842000851180460403500c0e031603140e40000c0c6080c6d115034010404100d00192030a4075042081c1120034110034460304000103480c41d02e0308030440c4100450f0300201180001c00008000d036020b125250040039004440b000c100500c1c02a581c1c950754002d100c20850080010204d00001c0400c89050710304503516031204080fa09800081c5030440120745a1001a44040a8120004002c400c101003100340051842c03000500f8541801401a0002c064641900f581944001e03200a05a508400c0580700000d0307410029070608400c40210703070000115030404d095041408003003005100966650113100c0e409404007102a800ca40030803503002c86850003088180d160f0350081c1c1c011003a1904140708a9906422a450001103503184241d214000745a10900e00d01d04c00c880c40b4200c1e032016180b290008280c02c0ca18180308502c0e004014054441c0c03a44100d04020903401d054406c1c40408150602850605203006406441810303513050061030860420710b5600c800c40b54007400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 713731564 1250 713730314 713730323
    0x21150504020a0f080721020603040302210a0e1509032a1c120306051c05071a041205070302101706040221060d120903060c03020f0d0e011e0b030613 65
    0x1e070b50b24041c8810b02ca035144607006d1041c21002181900035071644030003148502d101e54060b1211841e2101101101042202100c5030a0401d001502e661900252810701d004012500c80744204210311040c1d0340b0380329032054030340c050091494410303c0d0320b040c507e10b90304041d074010512060a005000d225040c0094040ea90101c5e4600d00d1032070100d500502c03200301081c40c0e8a0042800341d00c440c08036050700180030b00503000c81c4020042c0c0b42072040074450310340542101004442e0703500b000080e414503802140903000f4400f03040440101000760810002d001554094125110105103120161000101c1100038462030300c42c1c40082e005181c42d100710380c1710791003940320102c00b2640c0e03181c80c07408010010030f80b41d0131110b000e1121022810240010b440500c096807201850b508628141c0152082c0c20048810305006210000f01000c41d08145c0e074000030000800110032154038180c9000d07102081d080318041e40b0072030302240a80519000320940b540140c0c1100c455464904400810891003030b000340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 713732814 1250 713731564 713731573
    0xa0e070e0301022b0b0603010b04184d07031112030c1303020a1212030501050306060402031f090e21030c03060d15090c05060a020721150504020a0f08 66
    0x7440602c04034039580c0d600800080005e4030521090200b1003d40c82a00402000103000c1401c0001d00b03880000c42d440c08c0240c01043c08000d1038a400d40e8500800c0c160b0600040d615651581c0000c0590500107a90000e0b0240d0944019032644c01c2c2c1078140e0004106500042c18408800f80e441c20000313907d05004a01c15455103503136030343c900050480c1c005803006124848001000005030341c0f481d4040c0c000c1c1c001213044061504051510040010358628000c0c00d0505110040120343c0e00800c0050303111000766000342e540c0c3c1e40d4480e0700390b0a5030710048000d2144c0140c040494900c0403a80400403c0342140203c4070214148200e901c45d41242c004100d100d1082080000c4841040d40007441c0c000b9405004844900115a04c0f201d01d0410481c01000b0940d51310643d0082c002d0038030b01080106130a0b2035081c504000c8070700094840305103009020101040c240034403280301d810328000700305a0304100002c005002d60140100501001e5809903c0b680d14031001003078880080c0001821180ba050040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 713734064 1250 713732814 713732857
    0x102010c09090c0905220501081b040207021c0b0103060c050f090d081908040b07050711010e010224090609010209010f0f0516051509030307090909020f0a0e070e030102 74
    0x1400038051018404082040d48000081e0301e4481c2145507141d0f80c4d000c120781d80d0703001b60300c100c80040302d0050384011101d5000c0908210350000c8070182c81c00e499810b90300544c1d501078030700201d4046445115150115278429207400103000780c007031505060720300c03401c4e05000720320f100305045802c2e00030f820701d02959007020095003610b03103800807540110500c681510340c200380c800a01c000c042654058084007041c40b40041004000c80e04400641c0842c180c107100b0b003170041031784543c01814207895003203043c0902502418910b13030007040b900d2980d174072100341000da10b89190804043d500098503004240d00ca04c4002c211802d00c18025a21000320694500c80d603801d03032420407103049884528040610408110f841b50110b282c040410b40310b0700620041c010320041130684600a10020700303001c0560400d01c188201954400020012100034081c04100400907000003051034948180300342d88000f0b41600004c0d0b0080400e0503034800e40c2e403910b41190440c200c0e030078076080c3d1140340f2880740c0380c800c1c40b100c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 713735314 1250 713734064 713734079
    0xa020c0f0d0c0e011a040e0105060c0f1e010e010501050303070b1515120610080a09051e071a210c1b010605040f0209031506130504030f0801050102010c09 68
    0x20400c64240040c049810000c86407948044404581c11440821861000510245105103003001c1c1000c100b15000e4902450304640028019040c05003611031040016131340e4400400b04200301101d01420181c846251407681ca0f0907140501c1c9201c0312071942070020605c032030320042c07040c40e04940f409400365140044581c1c400300b104500401c489003000c3c0381c800d46c0c586c680300e103907032010789605400c0581d58520590880302d6400400030462440740d610b485d445607820f5800402190447c07003002c00071800d40c2680c40d00500302000c0000c1c0503040502d4614410b0340090000f504811141181303800c0c03a08658142071810300f84948601c013265103c410940000d914240c548070395000007103828680c28070102800340d540040e0036200302c0f00141e4541405200c24a1302d4440c020804000350011864021034001003074540312070b4a02d200401806400150740d070344404c1844a814040b000003001715142510300500b0217041d01e944440000c007040c00118403035005104918440015481d0b902e80360789003501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 713736564 1250 713735314 713735329
    0xe0319030f02030c0706170c031018110f0403021521100305030d0c02070503190b04110a080105090613051e03040f08030301090f090804150c0b070818030a020c 70
    0xc1e00441c8802c000b49480d0340c0041c002d4401414031aa182d000d180242c8031500e411000281614080c148104140103600e10318a5a80701110804940460407100041c0c5110007410110b002000003e030004009448485900007401500e1003200c403485040086040450207000b052800c80c0c1082c1a007840e03002b41120301560030361001c0c156081821554407070340c84e1b5045820500c07039910034a4980d260b030a44c198052003d02c0140c0001d83c01065000c081e4100000034050035031029001c0110240810140800d503901d205126401610b81c0d020340d07617258501402807a04503041e202c94010580861008081e1161441c59250010014402c1640c505a001c0a80c0708003101002580300c02c1000003000701044400d44010708204001d55200d616008004080d01c4603c8030b05942c0619202d51140015641004d89007504d6001e080700c0306075170303140344141c0c5d02a1100c540503140c041c10004001d0016070088025100b000e907020221648240340002503981c4c096800600050b0300118003040d05814601c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 713737814 1250 713736564 713736587
    0x13020c07170c040e01020904050609060607080f1210030309060c08040918240516050a3005070e0d02130c120204030c0609080d090e0603010f0c0f0e031903 68
    0x42070311030b0080c0080010742200c2480d01038010b00e940119680c0214541882803550090040e21400b180c0c3c9400d800284092044560041c030301000420404034034811102a96400c010301da9401e0681d0811001158182d45103210803000550030200c04501c01e489045203000159102e92418101400c0c450204064481c202400c003090a041440b100820140c00216480060340903a02403070038809014481078801c000c2c071404840900300c2c0000c100560080c1110910f0404d480e1083d24600c010b040071071842d100307807110080b15000800c040d07165144c070380c0618000e0317005403140e00e400f83c1351209201c010350342c0c840040d510504544460389500402d82240d10408400d190510700307103401006000403a089500300359221003e01c4070500c0a83d801c058614098404403000b0003400310050001003c0100a00a840080c0300324004641d003504c09400c283c00c4429044024828406000c000a01600081c0165000607001c9143c1945a041c0800e204100410803541003400102e25201a02c1820041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 713739064 1250 713737814 713737859
    0x11202120114182109150c0d0314040213020c120f040807050306150d020a050301020705060a050a090203190215041203020d0e090f310213020c07 64
    0x20940d04458030a2050708100c1e411511500740600741084600d4503200740f8041d114181e8810841c062041c841c22118900d050142c080095541560380c004c11110304200700b0030740e0041404111407202c98800705843d0000031039560300300032501d2038122104a5042c16100071b50080d20903040c555081455800900901000c0c03011147c2e2000f542130b0280f1700c0c1d404640540441040402d00303100104c0140414401480110001c1245050000101954080c01c2404038820381d400b03202c00c0300319141c0c40c2c0d595000b000020021034660031030b03040881c0c80c0c2c081200c0b400070803807a100010b00b000004d0b1041c0e01d00182c01a006040ca19440c07a22a00036844252043e0380c0421241081e088410f0a5801000500804809821499070501d000b03403500512a8084007845082100c414840d1500c05000f0f0740201a02c80c114007035201c5200350444102c40421001e203001030405030260030402c915003541c0b407601c00e403160020f180c442e00002080340901d0004c02c0c000c0d00150350822240c47c5030041802455240c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 713740314 1250 713739064 713739079
    0x80d0f060b07030c0c09021c02070c05040f090b090d020d03020c070909030f021912260711060a050702030f030a140703051504060b03070507060207020301110310081203011202 77
    0x54210901580d004110120002100c0f8500c0500300282001c01800900c66508254180051080c03403007905410382c030f23070019102e41c045241004d200006148000404000d481004072450548415028103440714040c1c8116a0980114211180000301d402e0120441c0d4040c000303c0c0c409407000c6000c0e45c403d004949640c4148400800c2c94520751003440340c0c1502c2134407440c01c400c2740c001010303051610440144804002c882c40c4607010480080c1140c01c0a002803600c8280710f102c4400e90520b0180844032110100901d07810018259004481c44088500c81c400300d4409a440c0b280c490244e50f000c5490b900160400c2c050018643c03100c0c0050364021134480340115a404642e004118500000c845c05000203407140d0a0040b070b00b40c044030996075600b054905001140c1841d051158510010740361030b0070018001511070500460b41c0c19286455401002800b5800c60710b40d2603c6150006c1c0d824030754251000c08000707030350040001c548066020041019095070310300703445c540801034420702c283c1e0000d0a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 713741564 1250 713740314 713740319
    0x141c031802131409070b0d0c020307060614040e0c210316150f0b01090e070c0203060c09100c03022d03030703060303030e0a03080a0b041103070507021903080d0f06 72
    0x126082e6450303421414202c009842a1800f20820b072812001d00f01c0011904000800e0180c802c4100440701d00c000899404104030418003801c03459440380020140440b440c1003008100440c252170008a003500031101403120189900c0700a4550086181003640690b0304042d20740001c08624038107a260fa105010750f0f051900090309002008081402100c02c031484891b04030b00c1c0032940c0302d462031581d030502041003009004d00000e401d80d811801902021001c0f200000c001c0e601c03820907681102d60141c2038541e81d0a100303032007030000d80240702d01e00e10465415001401e16132280d180d01c1c5809405074001c1004402407404241405207542c01d0700d40f801c0c0010007443c4500d03070420095008a01b90380c1c00103946455810300030100c45c0c10448190b025000040c800d00820b42c041c1d02103421604946000a00003a0301e40020002e11103010746403081100402000f4000740c010000e005a940240e4810080500006414402440300d0100410034203050080c0b0201e0990f540c4481041140304100003022078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 713742814 1250 713741564 713741569
    0x9090f04020409140c18090a2307080c0901060c020303120c090d03020d0e0102032b060305060106052d0f0307090e0115031508070506070305040b04060c141c031802 72
    0x390303802d00e2154041c0c82001780034200307080380c0800005040f84020260034507403019602d940000c040500104610b90b62140c10703800d401d490951140000d02280c83c010b41e140d03809625950005e94a81c80368401400004000e8010450621803e9004001d18238224802844261400e00908500483e8405010410968440b4a5211241030090f001007000c0f004032a0000c040010515800341150000e01c03003100c401080282c0122038130003d0000e003140c0012244881e000700344591026002d8420316000080c029088001401402c1210490043e02000510403e42d4201e145c0b046c0d20300740b5000c0040b014088901405180c002540340380074400544e655050140c00c0c40b00b03820820826068200c400740c026014410300c1d6800f40c0d818102e121280c54010324984948440c4140c85c000e040004880081500c500210f402901d44070214030307201c5803120b1004100004101c01158481d09156000e0030241000071640d4079103000703205076914400402800c401400304226030000c8031400589110059 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 713744064 1250 713742814 713742833
    0x30b0402120103020f04090809151e0a1206031106160c06030605040c0309050a020f0d060c09060f0c0c0b0d1401030503030f0f0405070b071a09100c0509090f04020409 73
    0x46000e0740441540354114010098000c0829020500c900c1c902600440007480400a03108488002c407880f407900720600c1800c40092040b0403683d000e9400c12409255004052805070104144c0395030b4841d4000318a512201c1103484502000d07200b4180e64051401c2450b04100400040100388925604000207941d03000005d00702d50010400310740c460005103c6800c15218000088040b0b180500010200d61101c44e110100d1690103401080d034a041c05445031035055168180c1540b08004000001d141030f0011308101031400380a000801710151004c0d89441240c9031150070b600100001c200d1482c1c802e20740090b81c003040090240035155460031103820342e1050010b00071401400070315139901d4280c0ba002d070301700c900401f218410b0f800c04003400081200042e0b018141e40c20101c00559603125404c00b035400e041e041e100c00305182c003984200680c0c0c030000f28440ba00c1d480310b40c03401e00c24280161800d403424007901d4140703504044001c000038541405204541d0b040f41c0003803c00510781100d07803900c4c17161 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 713745314 1250 713744064 713744077
    0xd02071b0315090b0f06061b15070305010e0a1e06080307020a0b03011d060a05120d12020901121d2d010605060d0f1e090b011e060c03030b0402 63
    0x100c5a50440070800d010140e040c1c00403031070244208018410182d80c0e600ca1207400a009a10101c11510004020340c4a8404039501403400d6030742c07055880c0c403031000342c0d0340e42480815050fa410306240102d01410300034001e81e4180e441e6910074002554410003554001c000591030500c0c400c0d4649048000c83c3c0d400d10900d800307071a080000d141d603035145006200b5000d0b80c503481440c1686080004101b902c01030303101c15100410301e400f0012246c560500040c070405960700040d03401041d10380c1c480f00320f0f84001764482690341c5a44806804500b2003500030104d00460340094049540b2400061010a840d442812520740c1c4420303456050b00308a144901c0c1141440d0220705031583c0789640641041c003010001141010f0000070f10001d810040407410f140904c40208400e03d4441e0100241c1003259003010700d4101c09980c00d41e40411001c000a00580030b29001a20318a0b400300007c541300e080d11489822007040b82c888103065901c0c06a04a814a800a60580c1019904c45030a40d450b600c50000b003d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 713746564 1250 713745314 713745353
    0x9040512030c1e040e0609070c051203010810050f0105010e03150a05060114070f080702120f0c04150b0a1103040801020a050417030702091f0302030f0303161704080d0207 75
    0x11680fa00720f01a03110402500d0029a00f604203100030000032882260b00b5a1040058a8085207516a400140d500c4486d040f00200300d4001e000400902040d80c0024504131981c1e28120382c0050400140a02220030071384082c001c02c504040140300b00d50003403815194010000d81250855600082c1e81e000c0a0000c2d92031944032520f0f003040c040d2940e030001200da4010318118003940b805241b0f070740b40c6003800f0102d10000c08856000c14038105556500190024040180007503800c1c808240d0b15050322001c10503035240c465850004004c82c0703600745601600540d200c1a282d10b10709240c50409640200a0300c5101e000740c4010000460020801c1c000740102c1803581d12800c2d221414210704004600760701d54403042c03c2c0d00501a880250f40c4141d40702e40c00804541c03000d40314407003000d081064404180c10207034142c42019504051418000020361181c0b407803060380032500c16001001c8920780441026280c0340081d010215021804140c014822034030310441c01860109150760b00c140f4012000301428 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 713747814 1250 713746564 713746567
    0x10090b01060f02070f23040207230705010c02090901021b06070f110c150c070308040806060f030307030503130b0106050703030c030c0207060503060a1706070f0305130209040512030c 80
    0x49000d800000b00310107080d481c000342c41d0243c01c1000d00039941030607100c0e02c05110032558803034031503c105000340c1d0b1424002400c259500c00480c14070103080c03100040d47d00c100c0e83d800da035141700d204404a0100103440f016076501c041c004458003000f5001c00043c0c6030983c0765608100300c046080c01000c51080b0070182102404151a00740400382c000000318500100b17200c08400044c04029010403160030000d000c5a01c001d036a000c4c40c100700c4690180000b22001c51180680100c02d00002002800455403603104440c0c0342c1d43d4038018401d131a00c10800785500b6074424861000028028409143c0c859883c1c1e412042c600d02075160411408400e034000008541c0014000052641c54020340c1c80e85c1c03866050a003d80c1d141e0040081d51500a4803500040010110204802c1e64492500704000c0c00c181c00c420740c0306440d40b02c400707803202000e44080002c00d5a440340d04040078000e014051059000464000007450b8580034040c0c403180040003220240200074280c03444a0400002d0350003491480e0806 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 713749064 1250 713747814 713747819
    0x908120421030b0f01050c011b0513050301020a080402011b0b04060b0306090a08040510021c1821080c03090d0309090b010e091810021207030f09050a0602090310090b01 74
    0x410365110301e00c5001c000c05003880d88585213600d41605400340c0900030710340155541d102540042c01441c184c41104055082e1068400d04030740d0080107004d59000e44002d84200c541e4450815080f0b118410500d0081120040002c1c0998095010001859081c06020182c15901c4c4c0e00c60072822421a4129003159503030b6080d10444c1820091264403490340f100402c2d54000944800405000d5445098030402c550705074450803609c00e000c0390700150810303005141041d001d01c1010300141d00030030031002400c824090018103629420104000b0110740340b0112030495458071101d000b0361041000d642e15110030080820385071124108205064081d1796031000f00e0b810305840c0d0007502c8c00b94095504110304108800451781d80c0d1041142c01c50b004041e24000142040d42050418a000759007007200c601c08035004550740920f01d05584205120b036010030501c884007602c4001c84080b1040a010f0f40d002c1200c640c00a40380e640245800580141240c89024102c0786640c1a40e4944d03500700c54040304070004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 713750314 1250 713749064 713749103
    0x16030e1c0512280f26040b060409050111090301050708250504052101050901020a1418060f07050106060c030c062403050109060c030e030324061219110d09081204 71
    0xc101d41100a001a005c1c040b00c84109000414014002421075146c250104002d95115031042240951080090200c1080105200810342003400400c4c002e5007050001100c6d43d1203103411070301c18501039440c211071a80c100034008503000c5504101c410300a0800c00400ca9503540020008440072003900f840c1000c00f03400105003540c2020308a0700c5640c2c0107201e80c144164005525000c42c04e0f804a06030303251074142100390311b8201d2184001b60800340c00920850300c2c4039114002c0c20058040c400a00400da5540c82c2200d5108489801500140911a00c0310015189030044010340103001445a150030307505114411400304c0e0b130b004407140e1395548840307401c010107406620004c80a41c00c0c108000e000202c0c4298981c80000d152120340c2c54020720790500120104450701002a000d0003c684600d501504081035900c00c0d01c0101074061503c00c25801c80e050760160b03103a00000c203071030f8506044004801c013000d091014000c5818440c1440203849280040280600c43e03401034400d40c001c88841c000c1d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 713751564 1250 713750314 713750327
    0x309061118031b15041203080403020f0c0a05010f030f0c0c03110601060806100201180606080f06190e0c040c091a0403020d0b090316030e1c0512280f 66
    0x1c0140c000d40110280c810b00340d503038002110000006a40415071041c00401042841c8034581100c090a165503291105050388203159600c00d5120b6001c589081170076442c85c0c0e50300c403410340c852640700c0ca601302c0074445940b0030300080c860440241008038456461002002c2540c50000450001408480d030344014140d100d04000725407085040907200380c0d4180b000052814a00031300c41e5005407030007100710041c1e5100b5400381280419611951555042034034198010385032520035410b070f610402031090150280411003a014666045c6110709c0300039000860009030040706042200d0f8000c104000f1010344407801a001303580c0c0c0b6603407070050b0103013403c5403001c000300902903843d0440307014401400161901c5041d0310405400598030060745d6a604a050315520580c450802c070b040b84840c140c4200354015201c1c4185004c100d4941d42c8132040112090401c159441c8080c10503441042030b8451050f0202c010b000d409403107500e80b10340340e400c20b100c1e415450b04441d680c0b0000d80c0c0c03810a1300c00a80c0c800d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 713752814 1250 713751564 713751607
    0x303020c1801050303030703110d2301080607081501180801090b090a050304031e08160501050c090d060506011103040b1309060e042a060c060c03090b0708060103090611 74
    0xa07404039410940030980d82d000041c5498189651094407a0078500da40b03041e604440c10364581408007445da5030303408524100e01405080c042c6486000403c000d4008120325100d001c85a407020510313601c0060000a8211510700b00d07050160750503e00100007208241c840c00b9148030000410042c860349071468210000802200f0141c020542c4540000d001004031000c03260461140c12803072410206264042e0554000104460720000e8010a41300c0000f020188150040c07000300095a80c9844411141c842c0c0d40103641c0c04001006d2002c0003a10b03030ba000a03040107040c5041010701d9900c841c0d0514662041e044514002c4000c82c1c2c0300c40390a1441201c0001c2c0041c140144011494031607000980b12002e08010a0100038070340d841c4170604090707820003200c44a45640d2000d80d55035803028240a172212403d8641c541000c510303c4e8902c0c0207000c1c21502e41c0e07202c01804450b544000b01114140e00c05040d083c1010740781c10500000c0742550040e4095120341c92042d44c1c1d01e50340011521560000c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 713754064 1250 713752814 713752849
    0x240204121a010f06050403060c09180b0f09101a042105011802090c030a150f0f0f05030303010b071103061e060a031502070303291806060a050a050909010303020c 71
    0xc00044c4280760703122081c1c13000c40394030403c0820400000a025100c6034645e411484c0c0503400c415000940301c4d00d03a0442030007244159480320b2420a00800c0c0700411208a540c0008058103c03130070003d1002d00e203664901842c0c902c24807400d05d0744598074206145003003007115842107240c0a0b0001030140070302c070f41c2c0842c584111008140c0c1c042c9901043c800d0000a1440c041c1c2c090100c005040009290070440b00100d05091101c0002d03203d4408403808110303400f80d00480100c07040d01040303040c01d101c10501600c00007002142160319003440405540e1008408076000c1d03c0b880c254070921b840401c0760034020149d50f10410440060010700c40c1d103030707600113050303910480c101042000071503200701d910018a115100c015944411504040e0080c0c251550103143d43c0b110320861079170644031240c041e90806000c417480c0c010000003171741105074904282ca4007540003004101111800740140020301410041c1e00344541030041480000f00000000d078030607800341e0010b09042d542851300540c8240c00c402d19 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 713755314 1250 713754064 713754089
    0x108060a0b030d050a0215010b0307021b031e10090501360b09250801060f14060313062a0306211407090b01030b010507240204121a01 59
    0x78002640c4000e5612404280103001810381e5641b44207100d08507070707600b808903070450b9565a40149401940704545c03200040c081d0040013081600e84804402d620400140103100700320b401c0d10b800710b40c04880340c00f403046845855126a002005402260011401000009400c054000b0841d9010030510041c0c00d03600c49044584102c2c4150b01d40c6c0210958000c08540a01ea48008915240a44c0b0b440d01551003620076140c51221443d60085500b907541d030100030302a03141d884148015415490083c1d02280154540c0b413406418010080c60340003200b4141088071080e10345400086818102044515504080c6894141200c0b0348200007840b03503518040003100e16005407000c000d90400500e1070345a202d20440b00902ca01d40b00f4016181c00c0078810707501480c1d0345541c000020003072001c8080c086030418089529660103070b03050784d4881c1e0f04161224500c50075040301c889480b070f0007440042c00503402d001c041180c0480c3c0000c0305040744901200040c8880320400103601d60816400320200020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 713756564 1250 713755314 713755331
    0x605010e0906010527040e0a0606060503071e0525020901050937020406090f050a140f1503090a031b11120a02041a0907080903040b0a14120108060a 65
    0x28840100c44440e099003400b614040f000b48106131010002d0b00461b5403182c01d0403007182d40c41c032003c00ea0a8109128090402102d959240d0941e405d01040f60107001044950790074800952a0790300d140c401d50500c2c9130503880d007104552164140491181008042c24404000c4c074118100081d400380504401c0b1500903141c58100c80b21604412030501041c606500200640c00746188941c0c0307018213264040d415529540c0380d14005000e6200d40c130543c61624541e0100282d40d04101201900391007014606100b07121020301403210752035880403600d82041c02e6210074850f0031041005540100710302c00150110905a0900030240054034080045100d00e030b8204400190822400e25070080c400d50310320224011000700d2a040caa0300d684080c0d0000c2c10304c00c401400c0c400f40c01508180c0d031000c5400d0f06603500d41c1e14089458100460310078000754001c01050040071044006400b0181041c0f8020307804900e501e41c02201500a4180011000d60000040c0611182880283d0f84100d003050108030360302 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 713757814 1250 713756564 713756567
    0x60603061614091c0203190f0204051f080606010f031503020118080114040b0c0910120e010e0c040e120f030a0e0a030e010210060305070b2b0605010e090601 69
    0x2650700d00180e0a0100c08241881d0405541041c0e0b054070400070311211030101d580c4000001d207a4001c100b01c0c802e000d004e040007480216503444000c055000002820400c05650030300005150140c224000b80c40312070021707220740300d0b01c02c5490054a042c101424103420001b00140c001c80a6140344803e250814801940043d0315045810407260240b0b081014a114030146500e100070035042002a07508000051032840301164286014901c600203080451f0354005000c4150302800194a0380644c08482c0c07026034a109020f00d0b598030303600102c0040c000d413620100d5030842d010401d424115030010400c400203840c040c442e045030942c803103025081d40d03000314410704001c1c8030311034811421003004004182035241e00e44c031022001200d042103e10034082c40c20050148082e00303203058014810302c24240301c2c0a069028600032207510070001d1000034207001c01003096411681c0180b40030202c10386c0c8111680c242100714444001c7d0008000303025801e10740010302041040c0311160240e0034110600c44141d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 713759064 1250 713757814 713757841
    0x801060e010221041809030e090c07031d0310090b0a060f06030905120324100917010b0301090803010f0906180c020a05030f0c101404030503150910030506060306 71
    0x181040c100280e60885540d030300c0c0120380541c0c1c001640b4200300b0710005245c5115075001c08119030103500ca112500080c001000146801200c1451040c101072042100081c0160400103c2c400110880b9030408407010100303181c0503100b040301801e241c48940b0041800001d40e4019082126094144000307030400c1d1b082000e00c110b42c030615080665072102042449414800d08180c4400021101e41c0c900b000d1b951105401c844400401c04440750030058242450000100c1c03040e0a265110703840800e180200501c451a800c40a002079075403211010b02103035400388603035181248140e0540d0b44035410914110f83d03481e070b41d8210f002d4079450841e040c040000819040600000c5d189400314042d10285c04c204c0c14100100c0d0010b00510020403c02c2c06070041c03601920706104200c0403030348500700000c0d0b0901951080031002000c3d10b01440803401081c842c1c03004541c0b085e004c0400b145803000007000f040100e902120308072880c480302e020500400005109094000d0011401860707141071a130052030300d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 713760314 1250 713759064 713759083
    0x1403120609090a0f0f021f0315210c0504021b060f06010219051029010203040f1703210411100e011812060603060b03030301030807060203040206040b03090d0801060e0102 75
    0x24075180d484810410510b000c03001c13641c86c1c0c0502601c0000120150702c1c0e02205000e0340e0000840d0420320340c00410700300f000441080b14500c0d601030540444011040c0481d405440050303600e0b202d0582c0200d01510b032400241603410350400c0c1e07101c2c280c400549050403c0741c0a4599009101e1180a2010307583e13000541020300d00d10f210f400b00c5d1004e401e14005141001c00442c4001c40c904003200c058031404078209800008405000f1441c0110000004907200d11440c050902d0308000c801c001c1c000c5950309524000c1444007441228508440d0048010301901c80c1d4010500040c0341e002044100806603515094592003503610b2540c1da55070880c084d01405050141c00e041010000b081100450400c2c01c031401020724022071803028080d03041c1100034210f103010649a04d03041c81c0300505581800004c4034100d0360002c40f07070760901c000c030f81d10080030303600140040e6404071042c03001081c0244045c1c01035000e0401600240070981c0070384009000800142c2c000d0341400b0140060081d17a980206968030b9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 713761564 1250 713760314 713760323
    0x2150408040b1b010504121b05030418020405060403060501090b0a03031e09090e0c10080105090103031b08030114090708060607020d0c030f051011070f030c0f1403120609090a 77
    0x8483c15140c5901c94403034481c0150720f0b21982080c05120600c00417010124003000e066803007080e00b404117103071075600340a503035001851a8010032080001d24146084415080e4039843e0142c40c1507614070016070785400a4105850090b903d01c0100b00d003c001e0310428052110950316070f1827051a548000d44007980c230090f101c075036644108102c640c1d1489550840c01418501d03604001c14000480c0c0c8590b541071124855004442c00014124160b001e500914122180108003450a070f00315941140d220301c0464000c22074a0b2100400c1c0000766110000d980607001400141100e4a8807000b0032000010160842041c001d03240240480f50b00e500b404c41d01303d03a0f010795810200600500e03040c40d01101d187c1c405030503c2201142e0004002010850641070304e10000e052040c468224211030591161405c02040c0c00420400c0000082c020080018050300604103600c001055880e81815402d42d4854107803d80c10025003c000c00f4644284c0542050f42600c0c03802c1c4a26001900702da0750a0303d000040c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 713762814 1250 713761564 713761567
    0x50715210207030c0611120606120723400b130308040e180d0c02040e010e070b09030f060103020d0f0206072004180201120f0b1c0302150408040b 64
    0x101410701a03181c0b8081340c1e5000b00100252400811101015001780079107100f282440d00c00304280d454814191480c003065030540c00800c1c1c80309031054400103204000b00d03100003801110908036aa040002d0000c500c40742280c0c2d0003081408260a03044480700380005815480341241f080407407004580181a22605607880d0f030780b41401c0740c0e417014820455000404181c80010080b07100c103102030301c0c0ca004003440780c50071802c00c0501803540c5e205c03c3c640b0034000020b0345e520503070405440e003608521084040b240001804220186c00720b42071410b10703000710b50400d40005015001c1c4c107040125240500108016100301c0d41103a000075082c1007040000f03480348170b49000c150150368610089805003039201c0c6209006649010707000c4500b00c0c03486640c5202ea0715101151028200702c0310140307c00c541c141d450114005500103050003c1c00103400202c01103640d2140c840c49a140c1c15690600c1c16010040c0702c1c1c00004500c1d0003441c01c1d05401e02000c81b040d0310010302001030b41c2e541c00d96050f103038004081c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 713764064 1250 713762814 713762827
    0x30e09132102070e01090903110f060420090412120e03090d0524010e0705070f060f06080708060118060302150904020702060d021e03060609010c020a0e040507152102 73
    0x124980030113504211425640800001840001a401540039600c00e44440e01c44902800c640d50710755100200b030003c690044030001d00014103044286050025042ca5545030406c0f010104140420444003103541c040381140d540ba019802c82c9138001d190400c01d00c00c0c003540320f08109007170b02e81c000c40e21440e0098121144010800030b051201c5c3c4113640d10364880c00c4408c50840301c00710f0031500c28400c2a022000d030318046506a485141141d40207a001045010300900c4c03039039488000c100c504014400036503122070110340c051040c0901e100500c00f400080c141941040c1c0c6240072403c401600c480e0710762400c2001c2005803140d10151010400103c03603191034000b0380000c240a4410104000d620030b9000030f043d00d850403198003506403400c094018449660344401101100c2c40196400d40c2d10100521042c1e00540c0329030b40540b1010b2001d8a040011035468882d0750390744400b51012140750b0001c280501641000c02ca42c0c280303a075018a000c0b02d03025401d91146c1448840401807208117a00002c90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 713765314 1250 713764064 713764067
    0x507090e0405010e0f060a180803060f0a0302030f010906051509040311010f0906020403050d0f080c09040f050c0928031202010e0d020102091c0209010608130c03030e091321 76
    0x2441030800010242c51008001c117086070707191003040720442c990030328040301e07668120081145042019441484903155480c0d030802c0000c001a50401c160780b14500040c0803006072070500c21032141e044a100003041180c1980740071420b54034001c05586041130001201c09141d039401500981042c2c06051040011040502a41c05001056404070540f41417000c07440030408103034014011030b80660b0580e00c1000748084111020b5603d0044040004d900c917001c40c8507424050000d110000c001040054085004540c3c002914000c035824000c0340c5003c01c00714840e090503500c80300d0340000c91802a4504042401100c0ca044042c000903004510f1480c0070110b0500035800051621b241c0c1007102d84031114003030001e020f5070105800b40d002e0301040207541380707403261100c4e02c04100343e00601504941c0c1c01d00d10f003103904900003041801c40d59070080070710011500c40e0080d44043c601a55030703150740038020010320202d01d4014255007a50030700080007001080210440400540b00043d456803218440d080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 713766564 1250 713765314 713765321
    0xa0f0908030103290412080702030306032104050d060f050106210b010c08070615061b0b090a1505011a0306060d0c0513180e031201090c140c060612010507090e040501 73
    0x2607130700e0101c40841800203104494842e00102c00319551813000907174410508986900003030301c40d190190f20407001c81801584280507200c202c29841c0391181005e95450009280408000e81a5176080d81c8000180d140c00d40c90042c1d5000d00110b08110f08140042c090954900c41a003c0e136207032050355100c081d8580d0f1700c01c8a221a0903038011102c5516500c1d076081007802002129000c90520041120004180340a81d40c202c0881050915016442080c0d4544001650f001030080b042030040c15089000200161402411400706c5900020f80d507041c245100300d030401c0391a101811803400d108000c010740d00c1204441e04083c035000003041109043c04140c80c1c902903007045885104002801141d05c2e00c807804200c07280c0145050603c200c3d00303031901e800d480c1d01c80c2112200741c0000b12070042c01401c000e9040000d042c01075242264a0811980d440d00070341d0408100484590000d0f401d02c410f62030302c1240d010408021900070005030030880d202400c0a04140b00703010420821320001414040c080d071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 713767814 1250 713766564 713766623
    0x6030c061107060807090e22080c1204030206041809080a0f140f12100803120106030c0e1f050906040905011a0a020c0f031c02060a0f0908030103 64
    0x4610100e8454a001c0c20107500c00700c0d100d04521407100d0000d070092288002a01130805902d414054604107a100031140780024a07642e01010b5004c002c548a800e4480352030501c1c3d0190010a4032515507100050810610039801950b6070410310003407001d603803800101e40c210350407130290040c180c9075200d11002420f8484000380898001046109070b03203400c000d12004465070380daa8811421030460b91040b00c0d01501e8400e5010300028401241240c9808008903008031150031603131200d5540f919070a00d958084d071813080b901074a40c130040060a0309800750b51400e4030756042c1785481c4001d01e8081880c0901c080c0b084905682a0701c10581d500340240b0072070300c2042010701044e0303440d6111070204020f00801e2046999600715840341c4089824010180c2c0c41e480c1007540600180b440708410062a0312505001c250305000e26202c3e045040005040c0b55008040ca4001d00300310b1801c81c0503401190504483d40c0d6009060040c20400902c0500450341500c2d40f09801c00d403003a000341c503859002c840c0c11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 713769064 1250 713767814 713767823
    0x1051c0501180e010612060902012d080109180b1e0c07020102060f070c03210906240303050906130b211003110d02030f01060f03020a0e04051b040603 66
    0x500116400d495902c01490710611280c05005840c9028003442c01c0300d00512407a51080221503007000010500d80211003140c5c014503042c0c01c1c6943c555680079210701200c010050152109071114211900203403028010660030508100c4100041401c8280c0401c2d00d0000b408280220005010121112100300800030403894031881c40c60001c1c0e0903c207983c050308050740036104860003e035051035800a040d21401296484c20000803265409032485151880005440781e801149102c88030b0552240c801c2c0720380034101c0468020840c0c00061441d80003844400c2851504d46820b07c0400c0e00b040485240c240e00b65452643c0d500c4a0600152009040d00320940000001641c036101c51b05140b20550303482c40303100b0700c1c8550b034a81c0c0000640c10300041c800101182c908507014005071030b02c008030b07606c00360018050700d60500280c00b42c1401c440d0690000786894400f8001881582001489000a40703c40e414440c494245a240c1d10354031542030305894910f246800440c6d4040c2c503035810582c000c6034003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 713770314 1250 713769064 713769071
    0x1f030f061e0c0908060a18060b01031b03470f0a03080d1a1c0624031104091a0a020d09030504170c01390b010e090f060601051c 56
    0x4080c004200e048203100d03807132441c0b0805c8042260240b103481041d042d00304820400300f6540c01640d03800040e081440185042c1a5960b031242c91a4107640c2c0030305400500c2e40d4001900038002107201d107040d503a01c22000803a40c11203084111003041c6443d820040360340c0c2c003180400d0484010006440c01d25a4940300c0d0800400040002000307904805800c01a100b0102401031201c02400000085103001240f507101006007030a59581e22107145400c2c405000d55004525400c00150b410561040580045200803c9030810002d0181603500c580b2034100490302030012050b55290f887e013150b10071980140d00c070034075008101d0b42d200503411201c0c0700101220900914407241070180c00c0340c003c1d12414900b102d100c1c0d1444407038240480d840031800016141c60380d84c004540d08041e545e44200b00801451480c2164503010758a60350050351009208041001466040c02d1840c20b28200203800b20134258002c1e2071815803078501085aa902c4074003840c0060700c41080c0c001c2001040c00480201000c5440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 713771564 1250 713770314 713770331
    0xf0c160f0f1e0510020d020d09050f0f010908030f0720030a090b2d0c0303010801050105010e03240415020a0906090b090102030d09050f03030f1f030f061e 68
    0xc50800c20341414040c000070444440001a40419058920001009130f042144000d4200295030b010304642d40e4088001810094001150b0040355245101550740fa4000481050700c50410030410f40268004c0380240000b8045945000a0780406071400c042c4038101e8000508136441250030010300c80318403050106551000c541c03152241c0c4199142400070711580f401148500d40b00048965030503400300341c18891042402e4000c441c01d4584070300288a03804114852042204102841c00b07800c100c2c00000c2d50394034107000034000401303400705103000390009140d01100c1c4415198818000a006c80c94080941d03d602e00049805ca68000d8036446a01c0400c0800050b548005482c0c02c0d2000d0362a990031f4551290804d030900d001e181049401648204100c034060385040d00006aa80d2040017240e5101041509042c20f6400450380700620515441c104203500940150031901c01054411000c400d9096840d0414400e070307040c00c0905050307100d0b00c0040300240500c2c10030315038440c040420407801d42c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 713772814 1250 713771564 713771573
    0x60a1e0503040c063e030a12180c0e04020103231b0c030409111207020318090c0315030a020a0b040512070620011e050118050f0c160f 59
    0x10020354060740c40f404a01000714009005000034000103c0805200d00b03205480d00c00280c103c100703044012515002c24604035a210010000303020340c0b031040d46640c0b01ca0201d01c014034044900e40603404038107040c941c5442002c102004281c0082d03e817082d6400e5030700c2c0c0e29800141c0150a2407016800008800754401c58803002d01900c0a002324295680420528000040c07506103004203410034500e80c0082004000c150001e9100000b12200500d8031030520b10444140c5034004012100d140141e000040c8600c0c0142200d1003562640c44e00b1515070b10740d42041200506940070081c00b20384080f503003081c4034100e6a803c028540d6482d42c02080080803a0f1200303500c1096800c82c2c8286400b07402c0c10000b1f0107440c82c011071b981054070420b9880d00d91080a042030f10420360f6000c0c18414041d560781416003503004003071100b0811903c1c2e480010420354507098480010500c0b0b41c0300c401001d46044c0900000500f0fa1f00d6051304178850700343c000c0c1c4440d20f01394242841d0030b50300002050006128002010403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 713774064 1250 713772814 713772817
    0x50417160c030c031109040818011709061b164d0607051b01110d05090a0602011803031a03030c06070923090c09100e0a150e060a1e05 59
    0x164400d5000c0d84200f00740400740840360b082607e008000020902100710340c629001d1441007075000514210b1092049030b03c07810040311003614070130700c203070892010040400101c0c41090040102d0011162801481d491100c1101e480075000a01604000c0c0910760480d1848140e0480307032056030304980c1d80d12140d0a502844000e025035a50211900d0140102035203450310603100d20782e4000001d03003a210800003200269030561481d41e4103121a0320b030303002d14003042089881c114490b580c80300d541c2d401034802000b59001d40c036404481103a0410b140e0070201e80618241c503a950350b15003030105215100c000c0b030345800010a40e81c25090310001c941c4a045503000540140160982d0b242c010a0302e450342409407840089030031048550b0001d560716000e41c01e0200b40b080e40442c4800c4810b06100c2c207440004c11550011412a0000300c04c0c010200043c80c0031f00d280701c01040e0740282d00c44403a402c5200a026202c054112a04c02c050200c0d061000d45e00130b42c403242c009035900103818542c41c05143e02a115 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 713775314 1250 713774064 713774069
    0x3080a030f1d19021c0201021509010501140603091504150e0105101403070311180f090114071d04060b0708070c08070b0f130b1c05060301050417160c030c 68
    0x214450714491001c40c800c01d200c1c10810f0b5030050100e00410008042e68001001940002c9046100f0010761011358a11041902d00600d11040082601d516000408a0582060813500d2040e00d003042400600781c00051140740140b415044103c09549508204000c0c01e0203008000310075080815102e0340a03010351040384910003505140250030b49a00000040d200b0700c0301c003541c040e40101024404500c0c01040001135140052080054000705007100148810070303641241980011818006242000e0107884000c0344020114081c500c1d1014000b080c8100100f03a1107141000041580700c141c5864109201a1500c451010380c0c41c0348072310f07103540c403640018016507901c8010b010104a840340460508110b0300312034081800c06c15826010301c8079920600d03111a540c0700c0d606000411681c6440602040d42c0303c0c003a42d600000c00354003408144c1d00010145482039240004001c001003043d03031000100c00c3e0546400b5141c0c13599603c07001d0860030020000d000700544d560008200100c50612105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 713776564 1250 713775314 713775371
    0x10923010f0807120309061d180103030f080402090c0703031d0f100603020d110301020904290d0b040b100e01120201260105091003080309011a060a0903080a030f 71
    0x310940e9035070021484400f880c100500003101d0100804c031f0148241d400645403030707845c44032501c0d540b030000006803124a0585002080c0003558010018141c000c1c0ca2103280c0b07040b40c24101094034056000541c040b10042c0380d02e03407040011501c001414403070341c04070600001004d0946400801025142d0799000440281849840b4042e46000040341c2030250030200da83c040d001c5890794105690719840402d4404401c1c3c0c0566007841004002e954500400c0c000c20b0f04481d41c0303180303489400c803030340001400c140c48a07010340c8100c1441000101c0c0907000641c0181c03c800890900e48035110203e074808095444007606440d00400880d440380a2807440c05084e100740c9440f5402440c5030f00f84005080c0c0c1040c0304031826104001049181444030481ea8000c5a0b680001101d5450b5524003042d0381003a0381504d45d980d547c10a20145428480b554407103c601110103d003013560782040200703419004d02009101010114900718158000e821504012004810070b10401609400b50600826002e06514 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 713777814 1250 713776564 713776573
    0xe0103050708030c06060103020a03020d150501080a020f04030f0f0b01080303070305010f05060901030b04060b0d02070c06020a0b150a0509160207050108070525140f07050609010503010923010f08 86
    0xb404480000031100036100580180c0016a0384000640094100c100d0f02d2051680800404003144014410072140c030000000003002c040c1048001400300b2001001c46401910400c110000010756805850840354000c00d11680d60f0100d1078204142d205012000b0850041c0e68000324160b900840034501c642c44030f40d41008660303a950075020000503070740719042d00a8002c01c00c4c483c1315403003600b15a502c410b005d03001080d071540d5200050b50503440984124095a070200f0240100075041c0301c0c0c030009140e2032004140622003074582014001000e055110009446c064040c01c50710362000d00c10052100a007041e00520345803031041440c2500e040490010f015600d0082415802000c0c40c0e8001d405585c0c42c0340c20002403000c43c031405942c07030001c1c500b44500c01c410540003660601114105040a402401049101a80340d6217001c0707082d0002c5105107001c1c09a00041d1340d0200c243c0381150100d80700801c4440035502c41c03a5440f440c200c2050365040100c000807a070000300669040407601040c0888 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 713779064 1250 713777814 713777819
    0x30f03030c020304031218030c08030c0f06100b03150402030a0902100314010506070602040806091c1b080a1e0f09050612151f090312030e210d060e01030507 69
    0x40f43c6030b10850100414042c5030041c420b1400d031040665229a03603030856841c107180c3e00e81d112900c003014540e01590113070703100085825074550144074400801508000500c0d80742012001c0c440034903400c0c00790515800c0301000003100700044410214013400301070002c41d036170b0400342102d0b805042844001c0c1c1c0901e4141c4054402a440303032051141c00940c070140034120b0303400c142c20030100394030090054070207031b800b80800b180c4841c040c40b08901481200004190f102c0d5000004000c0d84c030410b2031841440052040040080c42c07600c0b01030310742075200380810341d03035003100c0c1c0143d0324020b031070003800c8012500304004904c1c00d41100060a0084035511152081035403072041090500c900c0180001405503140070840c6102051035070981d80000400380c440030402054180e40e1810004000c0e80003c86227170040040c000e05158180921034a8a800e0282c0d004a000303482c0c0e642c030905032201c2e00c1d40442c41d0036240d6100040a8a0118081a1051000c1c560f52464402c50500038001500d05000c0c00200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 713780314 1250 713779064 713779067
    0x705041103040201020606060a0203070b0c07140304141003020c0d0806120c0d080721180b0406051603020705041d060c13090507023a020313030b040c050a030f03030c 73
    0x1c0c0c03407189038140c0c005c1c00301c0da07100340901c940350f045504900f055210601c202000a000407807054842d881c03412003580c0380e0b6041e0070101c0b46d60050701880c90454204000602072043c80f2214102190800c0d40e03050400000041b04500074421010030144034010003127054100741d400900140164002c50381c80460003510000a0b85846405c01c10340e0b031045072102c99200040009024090082c0500b00040307000700e803072103100901d40014400341d00042b041c000560b10b80f2400c0310914050000074015504081c04c01b03070041d25521400d1103110000d12404503e508141c400c000a03400b92001510512101034050082410000b070070010781e103a030103036030000f814072224202550b1341d85401c0e004075190301c3d14100344034005050240200c01140161401e00d0404030000d6482015121004c00712003403002402d003504922900e9002e810210b4000700010040c00300c3e4010900152600080e2500e0b49440302d10b03246001d1003080c0d21194209401142c00014440d1a2030f1040c4054040d8509100c024542c040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 713781564 1250 713780314 713780317
    0x20c0303090a1a0c01020f0304031106060904031808010e010b01080a09080319020d110307030c020d052b14011a040e010605030415290a0f12020303190207050411 71
    0x1522a00881404403c109a40e110440c2c80c00303c2928456062a10000c00d600300d00f640e0068200b010b5501c00082480201640616007404110444010744070702d08040000450001f1301500c06000c2010b450189544107005081180060051900070000035042d06c815602800420300154042889940001c1101429010300ca6019a00c5201541395540314042d07104464402c000d00e1045541c207101c6000700c15154403c0d4401c0b2504020801e48a00e800030700141a110040f007040c1c119000344200c143e910ba0030100341d40e21040524880c403d26507080541078104400f041d50600c1b401e041102201d80c4906202c0494165004111a0840f41c0ca603a054080607100d07610034000d500741400010800c4138841c0e0040c41c0c100e13109070025881c1c0351079107828074141d9040303c40404208071940c1c071158100d01a00701c4010f91500030781c0c0c240b40991902d883c0c190101020700c1000c03c18680719108800710341d41130084405041c41c5c103d0400140540741402503030390b801406800c1c050783c80d00034407070404070380d180 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 713782814 1250 713781564 713781577
    0x3080610050c0a031107030605040b010302040b061602060c0111030c040303080106141c0902060c0610090e06060405130b04030509031e0616110f0c0f04091e02060d050108010903020c0303 82
    0x80078510000d03138080f103424540304034a003c1809410b01c00300000c5c1c414041c55025601501e0040f041e94154010402241c0c0c0d007803a07840c4200e408000d5a15003405c982d1f150210150101c40721501d07644525442409481d180041d00d100c81d80020400428000040140040c4d90083d032300c11159a0301c8080c2540d1100ca80c0071100b12658042c0032040c600c40342011158907c1c1d03501000807860b529142d0205009800072210b02754a9000941000041365140000000030b10b10320754103100700d00d520481551a5503014160a0140d0b40700d0300040c011440108800b001607900c064081c050b480d042c14000c003103410080f02c491081c000c191a003040061489030f40c0d801c50031700c0c1016001580f1a041c0081c0c1c101c014840070740901c0390300c4003c5050032205015211203601c0c100041c1c070860002c401046502c5403454140c1e845181741141c003d0100e00e404240b540803954102405040180d02c0c000510680a0b14808501d2a400d110021030042419000380700000d01c60780858410001d480c082544901940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 713784064 1250 713782814 713782837
    0x601030509100c02030f04080a020108150d0b04020f18011a040b0418061511160f030312090f0f0b0f0f0a09020f0406060f090f0303020705060c190308061005 69
    0x10842d200c20030105a0156004403814011031389003204400c40b000050f042070707001440c00d400403030120042d96000305c626940400845880d540841a542c000303240d0240c29103024102c514987c0000e021906c038900340f00008403008110940c0c200c5000b140280c1e000e024003030b80d89024420242d40c00246a0101a5400d40c0c58540c00b0034105800e0010348082e42c07062b468100a220789403040016200c0002c43d05d41c02e010b942c1d03550805169500c0310300510b0700c0380510501001d0074a4050800c0703a21940300c901c1d030580343c1c18600040c40908600d40348000d000d0fa8138015200042d0502c540c010010514190b00e001d80c403400100703280b5902c501c081407860000b11480480c540005000800100080d4024110248000c280800304520b690100303044960640110380410151031000071282d0300310042100400700551011003450456a0007034992840d841000d00038240400c150003110310500c03126040e0303140146510641055800c0040131000295696030065100d06043c0405030300c542d040b2840c91501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 713785314 1250 713784064 713784073
    0x4050d03020403080f070f0b011502010c02120a0f020307170306040e06040b180a050a060b1c080a050f07051c030f0b030c13110a021c0302191404050d03170601030509 73
    0x105d84401c40b095101c950101c52402843c2c69040000b190564203902030021091089804041c0041c041d0071104410024415503000112045c003040c40030040f1942c031381c2d03149061044401800800c2e4a1409861402044021044081c4511590a6001d94412070301102d003843388922400f80103484040540d0090b04200604d40005c600c4103202c000e00d00751030000004c54a00025503180c03d400c00552a0084272540d49410400315140b4044030f12600e00601030000c514640b08598a61000c0c2c42100110340520401140d80d400c01c9548005458141c0e41200a554140e0b008100203904602042421000b09241440000380e00503d07219141c100304018005200d03200d807400c00c000c603084103455409205515550a10950b800d200c0290448051940003801c0080740300001c4038662003403443e040101032041c42640e00422540c000400f00e10090b0034641c0c282078140c3d03400340c00340c0708603042250400b403454982020107900c203102c00c05541e1401c0081255485481c011401c0e19800c0d85c201c81594003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 713786564 1250 713785314 713785327
    0xa021807081501091505030402041401060824120f010501060318030503190c2d050307030504170309070f05150418060504050f0a0c080601410304050d0302040308 71
    0x74a0b10240221014100241400d658a01c0100b11000c1c5902d20400074201000380811030610740107070700e0300d404020048100c941c10a0001040c0b11402802c03c0c5000200058180390061403d0688012841c081d0028000c104644030066030b428042ca480409980b9001c00041c49a00c2446580083c40940c0c502e404074000302d0b2400c072070a400160400d001032711644640d403c030345494420102038007078503203d032129504101c80b0940300c440c4580030008101224604d40c2903080e0703c00300b125441900783c00c0000c0d50b9225030502034220148295a042504000014416900e000142c1d550444030040f001a0106407a401849907074001c5508140010760140020301040d1044116100c88a40c210b90025440d89d0f120000f0f01034a1080d114072140411410a02005503480e00803180e0700c86542c200014107007411341c0001d00000c1201c510641a500e40f0400ba41c4500390154140c082101c610b09035406905c2c40b640c0d1111581c002c0e5801c5505100380901c03401200d000c0c1c000d94080341d420070500c50a125 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 713787814 1250 713786564 713786581
    0xc0102011a01031a1906140322051f15080328110d0306090b0102061605030c0d020c1e07210204090b041203060503190813170a02180708 60
    0x311002000d14072841103111308154441e01c0c0010030a031103441c1600065071038500d01502e0070365610b01e0a80c0e481d030b00b001040040640e00b1074000403100d0680b0103006101003810038606105004107034000c0c0e918108070820300761140d41c00500d0601c040000072088250350708021940c80c850344540303403181c01e0340d03c2c0c12010b00c0d0007100b40798405a00d10b0912014000b101081d0318140000b0601c50f0000c030b5500e81042c089040f140c841d1000c03e0394207000820b11403c00f145185100203e0801d04c00400400000280c0340000c44001e55500960500b019504d95500400700364442c4100c2c1e4505404490340525114901c40010b403203400c5400e10001c00425600400049004103641e20381680c015444405040c001b400241015229074051005c3c007216204854009013030300c40b6980420700c6540580710040907490b03074111a2001c2c540c400715150f50303980b45d03100100080b5080e5000b00004548040003500709031010903250072a44c42120450450301c44100038a161385400c1e04c070302002a030040006010301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 713789064 1250 713787814 713787821
    0x90f0d090e060d0203070803120a090b060f04020f0c0609120703080c030417040b071b150305060f04050405060a0e2e0b0918211207030e1203090c0102011a0103 70
    0x1181c0503044090644013600030074900200c980c4640714035400000c45803207a02c501b1744075640100b0b04460238010f08090307440f60241100003421131803090039601ca410286079200d60484003150320f01a41c842e11844483c0d08141c0b01c4500f220b01040c180101d14440070140c91210888051561684500d40c458880ca440d01c1c600b90401402119102140c480e074421203560300c40540021b01c80082500d03a1240e80f481d144205868111240c40b04108240c03051082400007601c01c481c5101d0fa180005142c1e6441d0b000030804580190702ea40c00c00c2c5020240300610101003109442020400786c1401941000f03123003a40da036407003802c40c0e1420002102c42000031002c0c050341000043c2d084c18010034010206800203990080640e14643c0e95950164460745500e800d00100008010342e5600c00080e1406038020f00c1e452182119180c212180710300052800c2d0300a91120400c1c403030700d404441c0e1050b000c2e200803a9540c8240c5520140348510306040c54990710501941040c4040c520406a40800690055018 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 713790314 1250 713789064 713789071
    0x1002030c19020307061109010237031b03030507110c09010b1c0e07090b0a05130b120307060c12091203050a112101060c0c050603040204060503030d05090f0d090e 71
    0x45000420924000c2512400f403014403801b0704c80700030f0382da1080780d002924040c180c1c4100507840f21140d00c40e0024904030301141384030806900b80c02041183c40d244c201d03020000d850301d0b15220701e0707203403422002e050345540300903c151802e07110b108400d032030345420590360303208107130360584c8402080d005102038000307170016128840000751140381141e0b0026202c4150703005074601d420503610040d020004110540100e20380c2d403a05443c40c0c00c0b01824200402d6440614003000c0b0b080c191618561410780d103d104425a80b01c48080642c2d071925628a00390000d49a00c4081c6400600d817244041c524140a1044540417980040d40243c200c254071800e5001e008001c0140743d07075a07603c0300c1001c00c220190008001c00040a8003040300c940618201094214042c1c02c403100b0131805e03888002c00a0b5a40c81c041c0181c074011980a503c07580c4501c00600580b2503500b0103905800701003243c200003041034011502070500c5c9402c0c0d80307151903040c0708556070300300a403d02400680300c842d040101d103c102194541 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 713791564 1250 713790314 713790317
    0x12020409080c010506030c061e090307031b06180b0304120e0a030c090c0e030d03020c070515071403030601020a03050711030a030c0b01060f0e01050a02010906060f081002030c19 78
    0x144003103180c85080458100052074040c0fa51214100442480c0a00940c891010101d400318201140c0d41e103900302d420150801c8440d20140003e140640e0f540402c00c01009551060944c2c060450150103205000300d07074894080420605e0401030111110440490203070fa0b02c45c04140c2c250354681c0c031442c0400e1411a001c1003400708890b140358a98031006122005103008454900c215440c2000a00480d800001d804040103648400000c0c10707900030440040c162464540541c035001d051038032609085250b40706950080907641c0700d02c4803007152409000407a01903005606260041c2a15685030311044859900681201c010800080c0c001e030050130189000d03c82c0d00503111040000300c0d240c910040020380114000c1b0700c2c440304100030402d60340e02426280c134000c41c01e412540f00c00b501404080107502d051060105481840300d200350702100d1038a030440c10a1015566400f4002c6940c0e006010f91301c03103805880d982e089407030207500840e070242da469140a80b030320220303c0010300d401005d05010300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 713792814 1250 713791564 713791571
    0x5041d06040902030607050c120703020a0f060e0615040b10091217071b06090503070b0c0f12221d0c30010e06030d0516080d050702010c09080304120204 67
    0x5a1401c1201c176126600e262921541e81741203074000c03440c0480f011882a02c512003001740b40c00207903021074610340995006100c0003440600f880c06802910f03d05680c07600610400302041810b21030051844200c4100346c0b0200502c42d080700c10700c694032500795202c00103e9401c3d1010410030003942c2051542d14094000c2500c0c9039410341ca03a0003640d1024105641d03d110303d8000700742612800c00307210700500c4a400c018100c3d902d8440070035100d0003140300d103e005581c0070809088102e01400300102e81040c100903181e0004400c0c1d4030040c950040504c100a0303003952200e59515001d02180d440546041155902044102d2000c0004880f4001c00048484500740a2000c10340c2c00e5441c6040391b001982e200d540700320590041c1803801c2d03605a02c01880c01c00708005018964030089201440c00c4000e00d0459075802c60465143c0e5a54900200104035100000d00c501c000c02c0344d0781c0101d00504046c0d000388101c0c800e8840071503c0c1c1800d80140036450704204800c20201c0d00090910071910310280020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 713794064 1250 713792814 713792831
    0x31b09040b0604030f0b250318050a0507060207080d230408072405070b0403030504061b03020c1b1003050901151202131a0f030a0b0c0d05060105041d0604 68
    0xb65090700194012200780c4407081e041001c2001ca03d0f04030707502084c0d0302000f00b030b06140c540c40002c0c60706000104406050755070341d0710030455100c0380d40c06260a400204a0304c0072203451404640d152654406c420060007880400b0403085c5000c50032b100131880b00c1d45c070920300881e141d014988030203e40303210700c0002e0810000042c401c0030038040340009150700070001c10980303510090220700c0d60904042004018040103000c00064000c11020b4200f0b4240c640001c132070b510341c40e0420040400d8951401e0030518000301111450f03140d002481030741c074410255480d0b1100b000c0e407400c0b0b9103001598182c0c0100e0004c1c3e9402002d00c01d0b40704070b520851200000c04e500b81e01c7c0702002d075501d516802a070102d640081d000802d42c140114042c07120b080700c04082003803440740f4440f1a4240800c00c80c00e446400ca00300726140b00d0f90200403010000740c11000e01100c0c1e0401e0242400550300c0318010030507450400c0c000a41c2c2d50f00480c03d4500300c50200311058140075003811159401080203143d01d034441d5407100321 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 713795314 1250 713794064 713794069
    0x2406040905090f010b010c0c17070e0a0e011d0303010b18101d032a04091a010815100e07230a021b1807021002070302160605031b09040b 60
    0x7418082e62800d009810b80030341607800b85081d1203203a4881030502002812000c0021031220001e400c5038002250718100c0010b200803c0c2c10101c480c0d000c88004010007042c00440840c0754000c040c1405050001c206140c80d98662403500c2750250242d4044d90800e200410801c04a00c0c0200319026494086481c0807a9010000301031110100c00700000038002c400c2c01c801c2a030386125140c020036044008100c4510b00501200510866825040389a100e0281c4680c0d55213032a040004400d40c40804810504104800350089035024480c1803054841c1001c0d082644101e41d4429008a61614980c0c0655041c401580c1d03160301c2c0902100c0c02c00c5804a02c10181e00381c201e00348540900b8286046966201b00d2400900e48000c14000034481d50194031541c00941ea24500c3e41c91501c2c0d400b0300c0314241d0380d034802c09038108001d0740c0030a0b010900000e40c1d03008160f4041b40c00c8103c0306004602c00380c1c4a0310b401007120140402c4480ca071030110495011100c0020240140c010b0101c01040424841c0c080c501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 713796564 1250 713795314 713795321
    0x30504210507021018061b05340b031f0e04030807140c0a060b0d0213020304120e0303090108041b03050303010801051b070308070c0215090405060924060409 69
    0x400c0006080416403604626000d54500695400c07441e18217450425500030312840440b44c03090b241031000c0170403100a00c100d00302056141e1a0084190780280a26008680035035000f1705031030302801e02d03048507410384010744d0850380280d900c010f000f9070840d45d0303c0188800031008000144610307682048000b41d080c906020b89441188260b4950031142484032002d01840256543e5030402001440030341e81c00c001c0000d0482056411050114000141001103a0f024000a2003e5001215100e006901c0f50a80d0011805075110b4050340c40f408503a0a411507401c480080c84580c5600b081000784441c2d03200e0005c0642090180f00540800c540702d0401d003403070995030f40c01102c1980000c801002001d500384501540503400400d4081c0c45405c0b050702c185d140c4074618005061250400100c3c12640c8120340b07914640c0e50280c0000c68810841c4400d02c2183c020441652046007058005520b500744910f07407901403a8800340c0c8005942180c100e0701c450b0502603a50070380003031f818000000c01104601 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 713797814 1250 713796564 713796623
    0x1060f0311131805012103031e05100315091a0711010c0f02070b1e0a0c021e10030b0f010318060f0506120d0503071103070c031b170a03030504 63
    0xa082e8840740b884001200079607105034400850003258190090303032003130f00340c611400040e41458001101d50700c9c04680601900718110b501c0750b0528000421001070000346480003039a00074241002011200003c0b030081c3d8480180c0105286c5c00c00800b40380d15040f8003c00303600180309080c400d401624210310030b821554401c58501c002143c603400c56030b0a64041c0000e401801118004501d00480101e08210122a03405c290303040f200d0006200b00d0f1180314500854480e940201026003811003219203000541f004443c0c64812246a81d545264900a1061000f45e0f00301074401e400c144900c0380107400908800000c0c426107a1301d1211a00010214401c280b803403c00100001203a00b0300100303005a40011107030910940d80302c07241e0b1000d1190446d0a0303d50100245c50021038102c40c06007024258080d00e800140080000c08010042100803044080002c0300c07458030090550f9111180c1b4421850380140f4204e6821030390700080428860b0300829803090103404a40240400f0180e010007030240107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 713799064 1250 713797814 713797829
    0x10081207050c09100f0b03040203030f0a020a0503130311060316030b01030f0219030501060518040c05073521060a0503100e010b0d050606131e06051801060f031113 72
    0x44814046003c2c017907456009041e035886000c0c1549084d901003680c0384980040c1001c0000042208040706208100d0030f071b0855486826a9100c1c40d906299010038030040c0001c44199224101d110280c2c1040c2080c1c1c0d20914102c0d1242c6000310060030150003c0110484890425071100048000400c85000401a1014801d01c8039010044404000e08030b82041c1c00040400004002ca40009410541000c40012084500042042c005c600907981c03803140a000038907030b040c001d1042040e071100782019003000b803402d050487d40d0b004108507284c10b0703c94090058a0108048061880c4542000040d07900c0640540f0b0b84110303070340701e1001a00d00305420000e01c00c816110b210621640c0e900b8007406c1e5a265041e180131510800594a0030b882d201c0082543d80207001c08802e01c0345c0000140c0182168070ba448901c001c00e80807042c1d041c8040c20301d50003950f000d01d04103000190700b001f4810885040340e90742e9035408451f02055004401a007400d544880c20382c9000c3c004100381903000700000c1c0080540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 713800314 1250 713799064 713799091
    0xf1101150e0105090106140a0201060510021b0616060e07092d05040f020607060f020301080a021f05040e100b0a05090f030c030c0103021c1802010810081207050c09 72
    0x1481c058041211058002900807807840d00104113140e00550428941c50704e00320aa030b190a20850100d00510f1b00703030b1240d540003115540c680103a640124940c4205503d00c840e0000c5040c011091205074403605080c1400600d0070022800400c615a0210302d4413200c09080e00c40c1256106000000d5032a4030018102c148070102801380e1000f1200d05415030810312140c140040d103065110030a40d60000310029004032000182001001a16844010201d2000c80119103d50316a0201a91900040e400f00c2c01036280001c00015121a41c0f180b880c0300038183d071060724103410180002d40000340074041d0170300ca04803003030b000c80d0a03a5403c2c0549142c080b81d50700c0d01d85a000d401e04000005e400c075a5098001d403c2203100300415100410f40800c150b2080c240075030f9500e20004d0038408403039050340c046086c6141c808030005441120f900100c00c0c83c000d83c0d075500300303444004080400111b039210b00d0b580e90348111002900400288050050700f4051019240c08607880d801050f80c01c0b102301d600c443c10011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 713801564 1250 713800314 713800319
    0x215130e09010e030a0503220b06010906020a0b1303020a06020d0b01030f1509110c19060b0604140118030506090a02010f030c0801090509010207080c030a0305070f0c030f110115 78
    0x80030310650794020070280c000d000c18903020b4001500e91048000342020010000001004c0d400c0c080d08800284516009507500c1141e2801c118101900590307040d070000d200070400055135403001030400e0003581c100c40c0171542c5031920650b00c0b2425402c2c1c1c40450030350183e1607074140420741610242c09242c1c000c2c03001080c0f004d0350000060440303180c42da0320903807585048210002240c01c0395140341502d802d00f000040310203890b0710102841c003500b0085001da118401c3e104a0b044a00081101d40611458040c04010669401c0100354081d41c041c40032400846001040190310032513071014a0244203440e180706030789a842d0141000030454200d00705034054028002156446007200f01c1c0c80c1071501d07040054100880740104280740600c94404866203600200740042020b40c11202420342c40900d1581d03880d01c0030086a1641c01c948003000200742b90500241d5010302508081d485409950b68040d502c243c1c40d0340a03140003c0c0b2041c1c4100300714400c48003020344036007440380d0310643c0d00364082c0c10603061 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 713802814 1250 713801564 713801579
    0x50604110a06050c100e010b03030c070f0b190e1f110c09090c1201020c0f160f051818010c09030204110901140703020307050a06060305151909021513 66
    0x100ba80850100074080101c8081400302064080c03654098000208000d40d14520b1580900f84130f03d4a0b40e40b5000000300c0f2801950006080001c0740c2400304681003840e0f0b18816559117000d01c3c0c03010801c0c54115102c2c00c401c2d0740f080d42c0f1034200160040200820f11004840c00c00031000b508508000b02d0701e000b8054030140c4e0b041191400660b41101c10660f0351a080d000103171104038041d20a4042d0440070420b41c2c5d000401c0d016a0014015001180c9036100340018951b40c0b0074400c0c2041a060084020200300d0068240d050000c1c3c507009030121000011043c1141403102c1d0082801903407540c520000110711600307007e185070720700f082c1d95007001032401c0d8010081151017070a541d10110000f041043c0590f42c0115038120002c100c03006258941c92241020b90840c400c0d104000c0540c02001c2405040280f50303801142524021700c2281c81d902d4407041c0b001c3c40e8100540d58082d02c000141214070710b0121a03001040d10500c007804100707401c00954424202074105a003400c1035800c41d1082801000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 713804064 1250 713802814 713802829
    0x130308070b0a151406070b0c0a0f020c03120a0c0f0c05210a02010e0a08070f0906090e0c090a060906030b0403080601080f040210270f0617061201060305060411 70
    0x9000b04100c0b401046180040c4108a80720714514001d94081402942c1e580d0400d0b50061908003208203001c0c5010080e84442d0740c81200e00f0400f0032901442d6080d010302c006100ea00189014001b05110b50550703034080b4554105030345030400c22091111120010f0071600000d51083e20031040e848407a820300701004000045d90342c0010071003110400301c003107112001036032800c001d4086c00d00300314003911030001c42c042840f1a082403c031440b92800002d035419a04c0459000c81d40411001c205150325100c480054541507807182c48580c4c0420360080e100c0c030b0440c14a6800401c10300300010056660603044003512603a0703000f034540c00388400800042c141c0100480b0343c05a42442c1131296460403510f0082106000380003c3d00810003403a402054a0256041b500402d4805c112032580051000440740005607a0143e9032600100607000540e150041348140304815880808420590703e03201880b1625035484e010110329034071068000701281080c005139000754007828011280512840510009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 713805314 1250 713804064 713804071
    0xa020a05010507111507180f0807050a031101030b01020c120313050a06090303050f070c14010207080601050109090b0409060c2a0f2009010801060306051b070b0c130308070b 76
    0x84c8002c041d01d0440030f15001c903030079281040034031460b4520303150340c0422502c00b030840d0201c243c0c0305091071010038055000507031141240c0702142101c40554484060140c200c2403444003c0c81483d00b50080d205c03560280d085801100c0c0103204440c41c0f00c0f40da0000640458445402e0103482d000054142c0c1402d03084c0c00144e000d031005562102d8403900d0a10014441c040e180b101808000300490844c9441d030010b01150540c83c4c00c9000d03006101d44690095003030b000507146041c09440341e84400945210003150041c102d96058481d03500c054a4804100090800340640542c050f941d00760002c00682a0710490300700d041c030381c1d8071a0708101c0082c060100c200d90202081c100c02d0103a88644000483c0401003400103079010440c803821403180e03070000c4030481a508525511150540003c40c040d441540040c046a00506041c080c40c0c403262010b032180c200c0702034480c504140030055500032502c9508581e4104822032122403030051050b400c4011410190011074403144000f4642043c8101c00302c141e1f42 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 713806564 1250 713805314 713805317
    0x2060d1e0b0f100306080d20010605031c020709020c0106050a0609031e110a0e09070e041a0702070b033c011401030f05090106052103040e1302060a020a05010507 71
    0x1c141940700018401c03200d0401080e00c500e8100110803a128442c1c0c010100500660741241c1141111a2000e0524604541e041c408803020002d00034140d44140200f108944026024101c2034101050440030440030303050a005512590400003006526440100032240842d40005a05030a280c200300c82248240e00c07800412281520900208824960518854000c0d03c004020045145800781c050b42c2100d81c19a03102d11541d60004403090704025452150040300161a0855201c098400900200741e40280448601c0c101d296017500781c0e1501c0540083da0b9004030b50305581d81d640c0c0c13466140c0c02100d6140402c0c041500d600480b155681c0b951450342954540c002c49400380c0d00d417031824003c0505c40d059000e03401b00540800d0f039019a22544030707041500c400344110314194001d2030103080d1620a00e1b00a600040600b40c0d40340d81605010741904034a0080d600c0c062900c040013040310380180143d1420a00d41054600617621400189501071894018040751816403c2050868000505550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 713807814 1250 713806564 713806571
    0x12006131103150f0a0908030406150812040b090301020c0f0304052e18090207062c0604260703030c080903180d051005011e090c09030209070c02060d1e 67
    0x460250106a4290348405100a011039517581c2e100468007408407101c3c090101c0400109010600803240c0007121078046000d0724106441c0e4484809944d152088030140302c0c4241800b051052692201c0105a801c0707005001500317052031154054180112101044202d50000904100508003480044070400b105d00b01400004024042090b464008002c1e000c104015011080000351a94007880085d0040420845d1603a08a2400da80101101640c40c1c0d03004805070903240f1941c000307000303460801104001030704072034503965101c103409a85404000b0f500e000e0081410800110b8001070f02085000c1d030740c0407400324180c00010307007803c401030918a00342e0400c22020070120103080125004880c00e0764610203e50003420558184140340c003044a5044c201000000c00307188000c00740818031a04005050340d541d03584001e80c21500d0500200c000314500c0081080949050a50645d0010325030a14401c002c089500240080c2e110002d01d00030555560a802480c00b1085410101c0184401080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 713809064 1250 713807814 713807833
    0x20c0102030a08070c021f02010f18020d0807060b0607060b090601030501050a060c050312010b09100c020d11130504080d0e03040e04120207030c030809090601180302012006131103 79
    0x10122003000744681d045c0032000c0011001c45d20758002070308034900502c48190400001c407100074041e015800c40042d0481c00c1400711541c2441c0c822594011a03402050200da00c0040d60714100660441d60050390000e60381c0404c242c580d20f031103005055041c4600f0000800142441c02c02044a030040c1401d410186442d0042c000b0361a8000b0707100c2600c0d05800d00c0c1c20104400d1034082d00d0342c1302c2d844003110031501005c0000b4410598038050551038000302c3c1c5140380b0400c448003c54450a0380c8001075400700302a0300e03217070106584c90019501118058412020303500c5000701e14066680035a001c6410f104c0001c0c40c58034024a6201d510b40741c0103140c001d5071802d8589a02190032074009071020701080781c100c546400c43c5001b080180010b5902c40041d03a42c10b6502d0808400c0ea420024620b40107191010000b10f0f41c0d8403c1484138540145030481c014818119001141c0010f0341802c0300c1d680c40000d210521124034100710040c0304007811a07001101d104d0b0340c500707107110710941009075000b5401409103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 713810314 1250 713809064 713809067
    0x80703120207050c0906120703050f071d0703090312020726040302090a0b0a050909010501180603050d0c1712010810020c0604030f09050603070e09070e0f041128020c0102030a 77
    0x1134002da45001c1350360204507110f40f80025007084003220945024031030110008200302c0b011076500300a801c1501501e8441d43c0e02c4440450049000b11405d007200c1d0942e0014480b0380c060350140d00010300070310705000807113645a103c0c0100c1e84401802d0b901c07615660b441c550a5096802c000212503160150182000d182d5404500340c9100541001401381c1c403400c420040d03464008810340140f80c0104404181d0800401e074074024402030007042c02e243c5109800c50f0700c4280902035802100d500000030710004e01801400c44d0440d0402e0402c80e64401c07080361004285d420180034102c5102c503c0b011031955450245075a19120006130400503803801030000385c2c3d202d030000c10310b0740c0d0298250400a52000c2203141c2110030801c82d07008184d101c0004401e00c484176500c1034801c0044801a54250180d0f15007103020385101a6045100340d12444104035004582000e8004103446d010313803400c46040411070f5040800f001d08400c10260360900729444012070950400118020301400e00113103141131201e280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 713811564 1250 713810314 713810323
    0x6020d0c03211404050606030105010f0603020c0106090f0b010e0d080403021210111b121902010b060c03130b13050405070e1009062d20060408070312020705 69
    0x90103414080c84035800542c864010900c001c456508090800940f14800c0105084100c1580c003602d5a118207000550641414410035040c5e42d080c002d005522480c020080f4060360100300c0340c500554071500c0010700414103006250400040704000309007021a00001424404045071940c0b017400d038024000d010030251006c03202529010703211007e01e0351400f41010301d412050410045160316007804010004a003001802d0410704d054000e0607602e003403100141e5a009030722079010000008000ca0840c1e140b40c00c0408001183c43c1c00082813000c2003000049494111548041d6903400c00101c641c2146070280408001d824480c10150030140d445d03003100d101c1c003940e0003014015580c80001c610058010660030021100080022040305074949008014031024854400805c0940071845480001c800c07061030f8000d0045090340b502440c512086a01c604d14038000503a0750b40207402030358281403c1c460302e81310314026550a030703a03100c0510300108a03402c42e8100710327100c51040c00030030001000440e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 713812814 1250 713811564 713811587
    0x304020409051f02040e061210050604060302030601030f11060712030b0d020d0f060b0409020f240a020c03160e13020118080a150506090f0c1c0b03010606020d 70
    0x2a000900c0108500c1c0152800341e98900602103100d58454034550100703d50000c000f5981807451b030144644501d4240000d21180003d04a19604500d00c03501c04480707140d20040e03100d00d0060010a0699494001c241411001e0700240d40302c01ca1400d545041c080d460742000c06034801035491074582400c0303032210304c1c13005c1c90a41e590b010551964a606610395400d60340141d010b03002045161508500d01d0426a1801c1a4004556443c180f0707a42e000a4074140c810181300340c0d00a0b0010f11022828410041c0c80310400284080310318007171307440c0c00704c01480074081c0c1015607068000b000307010b003001c1c102b525140d0714645c20004000601400e0003844041510345400800d450b03c0400705448500c0180c802c5002c0a0600e1003001280c1d100041d0882c0001c2c542203003501410011003103441c07865019060f9003003254100e40006d01ba90200b0905091a182e01ea4405100300003103060486009484e61411508080e04d032076684c41c0d90824900349401e200d040700511950000741881001c4100141c54590040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 713814064 1250 713812814 713812819
    0x50919080a300c0209070f171e070206010314030f0d0213051504061407020609060a1119140607021c0e12010204030b0a0605180402010c05010509100c0302040b030402 73
    0x80400304605855107091000c081c41c2d080216500c80b03444200400c04088844140d203d03000355000709805c1da000d2a0480200e140c0e5a580c205034480d08100507082400240c182d9030b0034101c128050b68130311415800c043c054003c560203030203039500d10300340100076451100ca00e03401904104003014880c1c1305d41007100d1142c407401501503112030740080915030030841d0f03500181d00000c0e900707850740206408000501c00e0354015100c440e48501080714482090060a100941080c0c04120103840d0345489006402c0b8490039240040348000e00d154024182480141840503400200710b4030300400c1111080b4030b03070303910300f160050005140c8054000d684100c0d0946503a22418260b40d0031031020300c22000c0b06003441001d002076035030154084081c1d000b0b5000e4401503034071083c040d01148009402d80681c80c11101d00501c442c0408810380850f50300c2c0f41c405003040f030601c078502c40350100041082c0a0244911031440c05000031039207900c001d00035a02e181501c61708142c4104018001d416023002901c2c0c005806 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 713815314 1250 713814064 713814083
    0x509010e06060910020109020a0603051905010b0403060207080d060909060e0a0506010302010e0621010f0b0a05030720060f1f050d0b070324030627020409081306050919080a 76
    0x12078405a005007c0014080d401c400300f50400304d0b0702d541580015010381902540100b440c0c8511b00d0010031600c081c000c1003110075040008001042c51500030b400000d0240d480031b8545170300c076514002213404682c0030181140d10703000041c080c041c1510403c5042403002006d001001580ea550715110041400000c0c18800069982c5a154540700c040c2c9051170b40c03034595642c08082c60303482054451001d20a0540403800c20030040b641011070820b40f42c6002d140d8541c2425900c2e07064041d501c00a4505061000400030400c00c030341c00e4001c000d414010090b8041c59034440c1824110350301c501b01c01840021298280480401184d180d060301948050f410940000841d203c0a00c110041c0080da0107402c0c4100c145d108920b8078550007605c01003120b1081004010035101414441c501800742e54a00044002e480b501c100981099045022007a204aa903c1d14085400d468407034444000d8000c1d4001807800314545590b41004d4400b9000b000c02c0030541000315190203108bd507a0100981d004015050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 713816564 1250 713815314 713815339
    0x90b010c2004090302030c06130203030a0e06070f08120a0203060604091808070b09150411120a06050a1d0a08070210020709181a090601061b02090a02040509010e060609 74
    0x28007a0045107080100140598021400d009689410840c003045007030244602241030300030107045401000c1d9019005e14182000300d0000d545079100c2200d4290418810002c41c03000500c1c42003100c28240c89551000c0c0c50342106141018482001080080341c0d0707104105201c4581e03107070025281100d00e1081c021456007104800600c2c1442842c03801840000c01040d40420043d00080c0c081c410700c0400d0441e0000c550251924a140c181518060144040b80b14201d4150034040f0690b00784080385002c4804072166561140d08640b0304490700b210301c1780d80303c0076203200198881022040c40e088000402c1c0210058940c40110710034190000e02c1540e0640401048500a120060050cd02000100008a4425a1f2440d94400d081c030489129034180d4080c000ca14080071082e00403200e040c01403110783e081c00c030b095400c144002c0070f170002e548507400c1b00c80045e034600c1c1040e44154101d100150b1582d00d0242400200001a00320601c86038001041020940303401050f0b0349180c81c00c803240c074900359 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 713817814 1250 713816564 713816603
    0xe1c090b0a021905060708090105070e210f010c030b0301140c07030c06090f2f09190509070503010b0d05030a05030606040314011d0d0e1e13060f090b010c 68
    0x140082145105001041601000d0240215149206c0e018588070010944c0d81e22902d90701706d442c111035190100c4d04001504c06542050748010a00e1a41c0d80c2e112858680c0b40b5072503c1c039010640066030b01c56912405c510216685c1070042c030340c100b5000c0c1d00900c0f019000c402c0d400420000101002c5001202042e00c1007454444c070500b450710703a00240c0400100c4000e0411b003a110040020a4682401040d40c90205143e801c10b6100f40008118603074500c9a04141007040707003800500961071034100103015040c03c02075407280d54010503c010040c40c160f86044c0905082da80c00b42040e610404612504c5804103201001f15002d03048d540c50510340d20741c0c80500107001d0b4000c5800c0945203070718210b294101030005510040c1c55801c45216020000c0700d0000d055510511085d0703080c0010800a991030050a001000c2c144501d6500c0d8042020b01d20700b800300c1d1403261709100c84090f1a45441d400c2140b111102e000030040c103001c06040c40595003280011388007400a050007015488202d1428014a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 713819064 1250 713817814 713817823
    0x6110424050712050d140f040f020f0315090f160b0a0c200103151404020304020d0b07051b01110711030f25140904020603100e0103060e1c090b0a02 65
    0x740d8801c8030701e0040b940890000701903405c007800c10100f0f640b8014010307000c1424000c40c036105400d4030030b0700401c40d50350741e0322140081903504040760070020300c5680c0c445582e014402c648550003440c181c0540c40c6031107101c15140004140319207240d031b0004056004500b80010f2200d060301d003966490755a41d50308600480d080c05200f8030140017807511300a00c00080e4401d440d40d00c0460400d0b42c0c00d100900709008545000c0d180c911940b4116480c0120b003003003d0404c0c0c0c000e198800d0000b8130144011619403603ca008800c112070750300000d0310004204443e400707016070f0303900d1300700043d4004c00c01c0c02d8800d05000d02900c200348016280e4007a0281c00300396990200004018500104142e0319054195500782c0552050758552103420280d007540450100c1c0114045403c00200802ea00e000b41c81e50740900000c0c0e800030703090b022608031400d0b000c5500718020798030500a511402c0c0024051816552080c00c18600040c0743c46805c100c2c0845914a41d400b00b541c0c0140c803d0942c61503038641005105a190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 713820314 1250 713819064 713819077
    0x1c0c020301020409062402280503030412080a051e090a12021e010b030a262a0f0d08070908060c0c06010e1315020919030611042405 58
    0x15600003d40451406520381014040342d140146000c04074030314003140450003500440c940e0050f4001c400f8100c4842c84403c03034000c0e5030070060b01c1d0311240304140c9801c3d055074802c0702c0c1030304c00085032084092400d90050711580e1041c407444007001b4604000000c05045003100941031044981000490b403030b0b841c00d000c4264030316885400181145d0501c40c010351107007103e5081d481d03a40d2000342c400d2079051040c05103140000703004011704003500081d41c8400c9604102080800b42c5441d8031048002c0401410080843c1d84418078415101610200c00c0b1000d0008010980e0203034100141c01c070300319800001c2c605031004103402c00349525a00c0304012150903106074081046441407a0034000f4180c80c040082c100210300a0542c2d400b40e0700d902c000c0311454810340d070340c080d40c0d403c82903400702040840840c074041d02035801025103407140100000f0420300404100c4281000c091034100104046403240105100b01105618180b1386041c01c2806030305100f0791946181e0010382d00d0560460310440440b003d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 713821564 1250 713820314 713820319
    0x50d11150f03040c05131103061009050a06080604150303081503010f0603110901080d0801090b010c0c1707050a050f21060c1329160c0b130e091c0c02 66
    0x1120b2601d400e020b030010142e0321405006e900365402c480c01805040c0100c0c40000c0448003031524644407031050000d03c450340c442c004200481e090001c12160b0b83c219021004103550340d241d21075810000c08000031142c0a89505040321500c400400001345c0094505c2e03484110300c2110791800070b030280428003400003814602c4c1600d1402c103001c01000484410791003030032001d4030b003400540c0c1c0301ea019541d40c01781c600181d00460000c00041008070704540045807090410b01d06007090140599842c80703645402d41007075044000030280602c403042c04002107070041400702c0b10150503900c0c14000c02e0100034002011405142d4400480302c51912180c240784101c070001342180c403c3d1a12480740006600503040495003c074507400005404192441d007031508201140418000070490328044c0c0c0c070303070307010358454a071021116490034041503940b480c620042c808951010781d0342c3c110f039401047d940b1503604003207882520350007400315289000407031108400f034142240f41d1604800c0d000380c4500302c05010095 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 713822814 1250 713821564 713821567
    0x91b030a06031b050306040f03022b030f0902090c0d06080d080403090f0b030a0218030f0706030b0301050f010306183c0201170c0f1909050d11150f 65
    0x550311240d540704004480c0030340140c03a0301615807410646030740c1c0a44a030f00c0d459408034000c02c02141c00d060340c4440040c8603004540c5c0101103021142040b21415804404806a91001100341c0381c050113800c007500c5c0320000c01c02140c0481d5001452601c0040c111050500d40030421000811256011801400100080300d01500c00002d00a1465004460440015995040c0000c910b0402d450031002d903040d810b4168190743d101c0640c1402901720f412400b1110360302d0b03a080c01650f1402d100101e401681c500180100f1420a0304c05000d545074203854901aa151004109002ca8072f8510541500d82c014400b05030842540c141000d0300401da100039041d1301185484070326141d80310035081415201040c00880112030302443d0800307450400006030102c1c10301018078029545078600c407075100100302134260521411410020098000001406101d17101891441000750000400e03001410701b1982e445003040a070361000a201600e81304940100580322201d030b14901520151900d5284910490307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 713824064 1250 713822814 713822821
    0x20136020901380f07031215030b011505030402121f090516120f060e0d0c060b06030c1921050a0e0610170c04060617010b0405010e091b03 61
    0x6000c0c2e07a00c41000800400180340c01e040f5141c0401604800ca07010340c007500b41850340d40803038012954002c00e030031070801c01c4040c0c4200c4411954071804046c04607640c001001a410740c038040b0341310341041c0c100310401010f812040c0d01c4640c2c44402c60b548650b05a441c80744e2020580240e610300410000c00514807081521000d4100b80c85500c4a5211030051048444c0c40c0e14440c010004101140248864079200c0400c0b8400300303131601c0080450300e109900000d440184403514a043c55580310602e40017840c600312036001d200b92401030400f50a0f04035086807039410a00440e0209105124100c1401c2200051200000303002d0014412003c1000c0702412250b9820030030071000340001ca070300c4007045141c2404508182c1d00010a14890080426682615410f006640003440b844290149280c070176024000c0c0503072202d0240038000d08442e103400840b10b98542d800086144140c105400a9006000410071607a00001c1d8588014041d241110280c560110403501d074400d03c1c0d182c42640b0000000d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 713825314 1250 713824064 713824079
    0x2040b040e100f0302090403050304050a140309031605030c210106031227051201110d02030714030903030c0f07050a05030903011a030d080c13120210020136020901 72
    0x181c4290724007010100966141c101c3c42460318000d000184d0840782141c00500081e004200540d0840c1c0164101c81c00a4020b139220040200c00103031212043c0c1003c10500414107040200345286c08000300400703040c5007000040390380c4001c02566940b003029840c002c60441c0c46900400c4040407c10300003404030580300d041c0001807004c102c09100024010644d0710b80d941d8050020b440c1e665068070380b0408614584020032001c110b5406030824295a2110048a02c0f07850a006003075424003a44007685924002001a0001c0e030a4285a4011301c800c20811810b400c02004803903008400003540c03a141d9516015120480c0151103006210340328001d00c000c24030000001420340500200c000f840200c10554406d04101e80b99003461750181c5c8292952503065012b03c40301540501546541c1b400c040c9070719200b44003886181d202aa000030725198180c1075017000300142c0041341c0e003400248440c0f03900040d200104154083d90405001482110a10a010144c82c0706400307500200584c0255844450 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 713826564 1250 713825314 713825339
    0x1008010504030c1505060112020903150f090114310f0303060e061903120c15061505030408030a1a04090b09010b030c09010b3004020405090f07060e0402040b04 70
    0x13502c820118858190b42c807405802818801c070300613035a1681c042c61404940c0080d4105008095042c042c07621400400030710910860b2052250a20f0030400d0300705094164211481c00be0442443d594050820a0f43c4110120304081125043d1114100c1c442015044a480c2d108640041000009516076411f1551540145003500d190440540064546030100000c880c0c4024500808180d50314040020400442c0c10f000e001c0c4160616080300911507580c90703030340703000c004400e00c68035640c11091040034044090040344910131708001d85181002c0d02da40c43d1500009100000003526101100f401c1c03103150300c41c401e02c00c101030014804000180b03031800b110001115080413542c0703095140d9056140c0040e01d44000c0501401c0703821183d003810000e4005502000e000700c0c00c01c6034400807083c2c2c804c0ea1440c030141c43c02a201c0050f403908080c81008150740000d0b2410409501901809207619404207001c004c560181c20a09200c1c4000000b00d0068001c2d40d105804611020a0001d41c0c0c8020743c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 713827814 1250 713826564 713826587
    0x40218010f08011d0c040b03091e03070c0519051002070e0f0105061c0e0a030c0228050402160206030103050a0c06050f030a11070b1614090d0605100801050403 70
    0x890305041c19103940002c40d100d203024400d6920f41c10854140c400601c80c4030b03403115003002004201d05c0c6001e403603000c4090135900c00d8488030895848984818440656101000713280d02c042c0c4040c600e001382940301c0741c41d60300c500d010341031003880c0c01c120041180d801c40300800005c10300900302d00301c4e0359140a0f004c1d40319813080c800c41ca0780ca4103072000070b10b102e41d0010720700e41a580020701d100d08240b43c003031051040400c00d00c981d4188580d5a0200d10000b0000c1001c0c0008500ca940c8244480c0010b01c14041041107a40812002c282c4009032403c0070980204180c1c00e45005503070050301c602d4041101800020300a9000c0c1d000782d40080080240b040120300a421140140c001da00c0c2156643d1084450344504c4070186551503003480801c4100d0890b40050346854450a175040c1400e00c02d450b0a1700080040d201c602c0d009142a0001029a40040e201c046100b10700c0031603800c1c09051800315200c0c0d40e1b5a24010546503a500c00134194003028400300020f00f818030001c0000b4585450050025400360 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 713829064 1250 713827814 713827817
    0x606120a0204050c0c07080106150f0c170a0906020d090e070215010b1306050307080621010c0f02100902090f04061b05090f0f03250b0c010912030b0a0608040f0204021801 75
    0x30303c0d020031f41d403005004034000c4031100500401281c170311600c12503280120042100c10021486407010204610508141d103030000040304940e1140c00b600064a00c0102d640004155000102c0700036880340c000d0031600032101e00101803092581c40e658200e0400e03c41140d101c0071030214600200e8000c8200707000d010384942040c4220310340f40d1120800e0301c013400112071f0f001c001104a40090720a06007003010f0403c640903245804804d0100a0390282074a02d1042800001298080301041e2039034100b00762040f045240c5001c10901d181c0c0d0700852000d03600140361440d01200e80003c0b404021555002004c0710f08002d03c4c03c001e440e14100d00410302c0e40403c04452044501c0072041805180096102c0038820005009105410500400045268100054404105c044040021160f0401c0000d000a0a201d4000500766500703203071030340030450560006020903241c03a2070280d90b0f0310b0b0100840160b50187c28084040c1d80c451900041038181401c000350880e0010500c2c5204561000c42142220800d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 713830314 1250 713829064 713829073
    0x8030c16120804091107080d0f060f05150c0f0d080a11030f0403031d010c0f02070806151905062106100f0c08040906121202010501080606120a0204050c0c 68
    0xc400408082070044000600501800c1008001d1003520341d00501c111a81142c6550422034103440b003000940124120181c00c40c3c40b0a10051007071014885c1201800e83c4094a85001d42420301003002000040075070310804600080c651084241044000c500301362a1041301c05070041602c000304540c50a44058002c50b080100b1301e03084140705020780b0f100741c0240d4143c007416621520201d0251181d90f031000f407108600303248581d12003c00e000c0c00c00303101440d494240402e903090000a1030704181c2d030711601c20764000e00c0c02d004480e08042850300d0000c404943c90040d429856000241070301300340d481306502c40307400100c4120f4501405546d50080f908000c0031422075541405120308034207417500301d80025004140b0b0f100303070f1800780c1000c2c40e116008111060134152512403560403503600f500f090f4a0030f510648107008210115040b0740b0b07903c245100170b2009501d4003d5079503841c50040c00c030394482c01c6180700b0096000001c10050301e819400410510040c18000188001580040c40c00d4030303e03008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 713831564 1250 713830314 713830319
    0x90609120507050f0303091c0c0b040503040f090525050f070b0601081602060403180807090203091905070311010302070515090c010302040b0306040207020a0302060a0f020c010e100305040c08030c16 87
    0x31003607c0c072034007244010342680b810402100c60001c0d4042e21000a102220400c3c00100c1c608040030b0340701e0b91003407005540c5d6a081040c0030709203100561085080380d08110030803502018010500c40a4440a0003103a008610100284c40e2030007907200b0540c440c0c0307000ca040d4050121240216010741c0b4280c81d020501e4907001c42c2c0584650442402d400941d000034041000a0301c50701c004070500c0b840d01c00400c01d07151581c00b007500344075895020400441e008024062881424480221901e00780946020034058036a0703015200c640d244030140070841000c040c003049034060340440341c80325848000e5803c0c103039000882c04042c410581e500311407441005410b0000354005e20071602510b86018035142141c1d124000c01c400f035442010105c0e0024180e500020040e1110310240c02413500c203031265034100c400c01100924041002a9a0b8100304000315050703100e4850380c05541842540785400f080320303915800e0142d285a010380c040d208600c00002d00304004400030400f646003008003000d10a4055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 713832814 1250 713831564 713831593
    0x506090c030c0315060f04090203010810141801020f0406020f100e1e160b0301090f0902010e130e070821090a05060721030e161809060912050705 64
    0x1241c80300303900c0e001080490529001c01d440d5184c070340c000070402454104407182420054010b50b00010402d0f801200500130503805100702204001a1082008024800d03103212000540140442c901030b00c00c51052508102c00390129a20302c01802111035440f40e85400003541c80345040209030035801000304c00f01c800d030700502400700d040d140b080003400118a5004590b148003000f0319601d04511615113480c61500820708981300034544825090303102d6240030713450b500341c4013122030344500740b4501104040180e800c8a03e00c030031043c0a403540700a0202600d10403005010407440c2d0061031040180020307021000095a500b8007403404450f07003070f00b560010604024002c4021159100c10141c806000a0400030058070030076010300d81800f1400d6000907003002d281040c200082c0000d803240a80b00c0000e10800400f200030f081540d050152614000f0040c041c1d1250b40704c10103400c0d07203504020302445031a4022000250304010011110303150f446010740035a112280445007030003a10240360038003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 713834064 1250 713832814 713832817
    0x30609150b010f020d0e010e091509070203190c02061c0b130603050715170906010f0602063904090203101509051522090509030f0f09011707030506090c 67
    0x10f0095400501c5510603807241580c60004580b1038a04000c0360070201c1029649050b6014011208040d010382e0202c9081c8c1031041030800104841c0566100b0010944035200031200e40c203d06075145448450041184002200f522980e00c03418402002c040314030040d10b4480d071150100802c121121000701034852282d1040c0c0300988000f138010b40003018104010505060082010360343c510305644000e22400300145848000d030b90340545507100400500c41003a895000401a080c02d00041500b46821007502c04800e1600c0343d08030034030b126002c9400741d00d000081c0c00150750002198194a987c2c81e42d010358000e4000711058912200480800a25050900c8648240740306503540c40301d0442c02c0a0030300c8017200c50310f014402c0c0c0d1881003103c2e11070541c484e402103034031104108103800c40515007082c0400b60342c0c000d012240c80b50010800d02c0c0d07103071000c81d044541151031070017929250210b40340166210804500440000101107081110580e8141c1c0300074802e0b0811102c884403a10394045d4071176035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 713835314 1250 713834064 713834087
    0x110102210a0e030702040507030b0909060402010f0503011503200f070b0f0f0c071b080a06061a07110d0501020a17011208030f09071e0807053304030609150b01 70
    0x2d03001000504c0260501c0e4220701c0d0b00045505020640c80362010122380c9141c4111031400c032980110707050000f19a80001c840045444902e05542103504090200a90035000c015000030705171b440c000702e41c803c0c9281c800d801403010104903054890490f020009040d40c0041c00840d040a241c00000361481c03030401c161400707500b6201081180341d5030101501c54a9200500c1910b03400310a015460044880030000009055100003a000c54442c62820301d0581e0345541106914940a0032840584002d100a5925454100c01080510260130740810105120040b002d0b040754000166900740c25004002a4215141d14898000a81c0d07645108501c11400c0345009102040402c0401d101e0301e0000e1246401c03c40b804180c030501d03503540c240d407030b84094068105103503500e0341d180400480c0d41c2881542e0080c003040c0d840c07900c42035042e10490f0190070030f22000c0004039101e4601c00070312045c98080d5005103a01640801003003d66080403070482505041110704c05003015505c003495403055102124 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 713836564 1250 713835314 713835341
    0x50108011505072a030602180108010302010836010629300405010e0c0906062b0c0e0f010f120b030a02130c0816020d0e01110102210a 59
    0x2003100c01c0d911141c01c4c9030038001d5001e0040c0368840c0b0707074140100d40342550000c40c0300d510016523820300c0780c520602c02c0030408003943c14800c02000402c0580d820415081d40034000000ca1200400b030740024185e60041c2c0d081d17422000400595841010f48154040f105035481c0b48a10304034610740608403142210f45008100080da01440404083c00482c1c0241040c01c0040c02550803220011103010342c2c51500303d03000d0f50169180d03500d11001e80e034103100020311107206582da60401e1819901240b628802c901c500c1200016031564000203041800c414030311058142010301150070808001000d02c0e0116451921520940c1c04420240d8001d80c0304454140080d00d890304d0b0212940041001042d104440c0d507018011698010010780e03501c9000240e501e200c01c1c00140c0540309203401008200020284605513400c3c940c800c20f80e0b500050f810080e001d06203000a45c0d00040801200d098991003560300040d80007150420301442c0005100b24144d4026445c5182e80e620a80c84c0e0040e81d002503c40030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 713837814 1250 713836564 713836567
    0x160b01060905192303010504031206080c030a0f02010201240e0a0203071d01031107080706052d100f080307060b0a050a0e0c090a0b0a0305010e04031d0102070302060c07050108011505 80
    0x1080801100381950006682c000d1401e104c0031410100c0d0039100112021000220b120310034503a54031030340c03003104060407868000303010114202d03000c41d54420340820050421204400c0050444e8802d400c441140042003403c02640e600320b00b84142e12998500880004c40c50307900015080461038400d03244500301a1703980c051429201c40000342e08402d040c0d01c81d0304040c1c8511079005040c08920042c102c0c107100310f01159072507005003007100407550003404489a5024443d240c940032034180110040200240c10414090b49404034030980d07081c0b040c0d001310100c6000c04000a40000c0110103000075900544007880b208108508210503015130f4040c041e44104803060a009601001c00110760255844030380614202c8000c00117400700013190322854a80c6000a060181e141d418011203004055120100180e8209550040c0094101c2488100e0f440003455540096038800c1004c1c0e401503401a001da5500c01c0d0407803116443d100d16016980c0032400c041c00015a009103030f02c40c041600055512035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 713839064 1250 713837814 713837819
    0x30c08040320031c0e0303040201020c1c0c140414010810152102010f08071202030901090b043519020307050d050a080f0f011a160b0106090519 63
    0x942d05201e1450b4104400d0344400c03200b000b0000200010700344402032111185148512507021800c0d0742d8002c1070f064568101707009001c0180d0b0001116210103e08131015203044003214a0a98401d54041000d0b008110040c000107a0781d240070103503805140300390f40c2400782020500c2c03002d400c2c26080c45021080d6004140074a09281990300200420b1b25200c01070407500c0d500c240c0d50082c80b0201c00308904e4120080415411583c0000d68401841014203001c0c000d4a403409001e4403070300c100440884580d40020010300201c90a602510310a5803000b403041c03035402e140c2009084014081390000d015100c03d01c80344035179a40603041c0c560b480c044221480c07070105000303d2405a0b9805294031402d510050029200284c4144080c00d20150301d40c0c3d41d141c076142c429000801400c009800010090a682d0902c002c0820302e001240c1518507a000000a260408170120f11038410b01f040314007681d80000c402c008100c0910340f0103040300c03803550302c0001c00c503184d030104032110001180c001480400300d0b404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 713840314 1250 713839064 713839067
    0x6030c0d02010318211806050f0a1e0306050f030309030a260a0f021e03090411311706040f0c09050a0b15090d0312020403061b0f030c080403 62
    0x583d050f03418803140d1121044441e50707030044040d01518140e8030788041018070411180d00560080c020383c001030b00c6d12000d910300305014181d881654132551940c040040c1588595018440c29494800b601c01c21b03072003030b81050100a00400b401d00800d840383c07018043e01c6080d8540042a98140325009014005001141d681c80745100125a400055451000880c142c441202805080c00d592a5111600d0700050b11000a0400724201101c0e841100c1d00e0848810f08040001503685c1c80720706460000309807107162489910340c0540e182c0034500c0c410400c208406101c154610015403400000560b500d00e48071703003071041c104100146043c41a8440b40005021132107003510320340b242d4000d0045e00e482e05d8540828205a46d004ca0318242c0c02911055810b90300c0c288007a140e150b45130f1881d485030501c0b1071000010400c0b03402041c040c08002100380c014650203000d604940003035502240422000000d031000103110045410b80c94045240d9010030341040c1d009000d030071480b07001660340745216070380c0e90f60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 713841564 1250 713840314 713840321
    0xe090f030a050a0e1804033b06030703060b031303021501050d080f120a0e2e0b040615080402090c0711150c01060f141f210603081206030c0d020103 65
    0x104035030301558900e50000345c45410813180d402103000740d6130b8511081c034090038621502010042c10400001a6a07560b00c078002d40f40007045116801c542180d5a500c0d090300440180c212a008030001010000910403420400c0740d601c3e0031030b8425000e403031940158900b110fa048400744103242c0c0106402a2a0001403c1034009211428001b1111070070100d140306104110355045850641a5a540c02d8070100201c00b080f200001c280044488400d1140e40050580d582c004990140322064603103440144980c0e4542050001d0b04000141080c001c0c4506802841000185d4080e40940c041c10b01013002c0300d80d16801c40c2d550b2a00611080d07030a501d20000d1203000300302c62504611086003800382c401082401c1c00307070100405030590034050240c00c225540c041d1940400809120715000048060708888040c02c112014040e801c003c118041400d04421903800c01d1480700b041036240401c007000704103000000e00b0a8590302200700d00166510740c24590b54ac2070040103036a001400802c8100150b21940 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 713842814 1250 713841564 713841587
    0x9060b04080303150d080703230a020a0b0702190501020717071e0f200a08010b2805030f030d0c0306050d0f02060c01090f0209060f011b1b0e090f030a050a 68
    0x10503c4a11030416106c0540982115404074002801200e10b949180c6003001d03072200751800541e00a1500c808400003a660b01c001400c02170048a401001a14040c000d000c0740a090380400310b5440300d0b01712860301c00d000358001e0340b04890710029014002c84a030845029140031617401030144040f54140900240400040c400440b070b2110720321140360014140c405060003000c10f5070b050b000341102130300401c80107032a40d8010030442d03850602c138000d40382d13100c110020540445200c0c03540e4403407078541031600c82c8010340c0000d509441503c582241a840000040c5075005070720304104100a402c1400320103a941c54452581c0c084418401500441c007d5a03c003a5031030310007400c0c14500440c1034070040c29108503100c180d41c1008001c0f684401d600704508d00f140e0080d021039038124100b10103000607204d000c0788182c442c0002c80e09209802042130301443c98001c5c01049982c640c8040d90750362115251201107030320502038010400c80c03020699001085d6008066984c580b1030038880c1d4110100d0f100030680 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 713844064 1250 713842814 713842819
    0x20031015080d02122215030608060c2a0312040605130f200418050124030314070803010e040510060311010e030304090204152c0f030c10080109060b0408030315 70
    0x1001c000d12510707105d40c000c014400c03150004074507881b0100c081c04890050b480700b012a00701c001080020000795003214034081c0104420507141c509a072002e400c0642040403450b9071710000810481d88206021814841c03803143d00d040c0301070b0f61140600b0f43c0713017900c029005000d8000c0b40420b10005043e840420b116546010300d81018001c0b1700d00003030603600803606a080c0b4050079101442809001e0045066012500c0d46010303a1030060b04031010021913520015040003200150141e40d042c4100c112a0600e8203d180c01c0d07141c2d40c5510540e82a81c07800d840c01c039254803d40c0100050b80d09940034160860340c001480401c920b0074a0015144005040981680b50004001c0464046801c1c03010740054070600c0c0c00860b8000750058080c14a603d2a0410040151741880300200c2220440800013107a000f0303132300e000d1a000010046450102030849040c0d120400f0005004016071102c035140c1261480e80052025983c0e4007015600791183d0b004401080c1c004000184124240712540e14820703e01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 713845314 1250 713844064 713844097
    0x50306100c021305070f05030114010f05040e0f0123130b061e1b03040e04060b010c02060c1c0e01090b09120304090219090503030720031015080d0212 66
    0x880c1d000858424015412500f51580c500034808043d50214040001d00100e0801c2444c0d5414107a070b0b8070f0700c00302c002e80e0981040000100c40349d50520550a0754028405885440d260f0705102e030f0364034403d20090140319982202900011540000c1e14a180386410b0050500c200da1344090404001070100c00302c1c100c2d000b00c2c0c10420400c0120401c1510b0183c0c0700b108500644030900c1501c1e542d4013464405c4d844000d80d00c01d01040c00841d84141c007050f0096400343c00041c8607088000141c50000010308003035403041d8003085d1001112000f10f540c0010810313840c41b0f0209041c00e02c0050b14898041c2c2021070008403105000e00410803414020b16030600000c10707514a8041201924ac035590041c0c000c08922030b0007044002cae403071407820020780102c1d000742000e0000c5814000441d40d01c1c00742d01e1020300003030402e4480941c00a148002c0c0444460050240e078609041660100003400304c4507a00882200900340004815a01203a203c1d45a02654094100e0089030004107010380c224092070b060f050720 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 713846564 1250 713845314 713845337
    0x9031b1c290108160614030a0906470603060d0804150806271902040f05010e0402040806011215090f03020f010501050609041a04022b0b0105030610 65
    0x205201d040d0104004460080c1140d810001640e0908504d00303c52055540c99103400d100b8940c006280b005009020301110341c4951714194507401070401c2100207452585421221103100310f800d40201c0c650800342e2180a4801c1e0610722000a0401501030407030720346840ca5401085103031486c01160000d600516003c1d807000235449840c826406544040c007405014040114500e40008003e940b1160480e074404602002e0407201b4102d40c8952041d500358860000020200c255090462107101000700c4210748070340c2c41c2c2c144003021650314003407280485e107080814002c0b0300c2e240c021142626405405062164a003424030b800e483c42a82d4210740c42010b4480e8034010b00060b2150803080c0780901e44014840701c040c1030107403e103070008103114000d074141801400b4545903903041315030810081c0c400164901c51100380c008860040100c545d0302030b0001070b4a08112401104000a851104240b0741c5038801c4d02a0000860304005504d5020920a10006240b072401d100b1a030452206410070407034404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 713847814 1250 713846564 713846603
    0x302070b030109020a020615100809160303020f07091a0906121f1811090910052401050705210d09050a060b010f02070e0a060f0b09031b1c 61
    0x801c00d0704400090703a070100701610990750400c00300da000031032200045004031451001c91506600c0103100000d0148140101d00301d0340c0200401c07445040c511550b07411441c2c40f850000d444402000071000b80c0e1203920300101d10482c2c244108003000d0030500320b080902c0341f440140141202d00a2460b030303011640210aa440050a0181c1100d403038042102d510504001d81c01340080310b2850b41c458101500e03c1c00a48001401d6141000c050402224440a070b581c94140f058580000d1190600185052030f06000d0396601d2245111184404044003080b00d84402004658502540b5000341c841d80c030681041c481540014284525400c0940300f01c0d2901181c030181205681030008103d6041d4080b18640050207810b05c12580c900c01c3c24a8418442000108002d41d02c2c10b09004504010b04200003203500c5403099800031000f80462084100c045555060f0b0784441e030060000603000c0e0150341c940804000302e078030b500c0c0e04003c0020240d020240d905251640406009101201c548403903603020780114 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 713848920 1106 713847814 713847817
    0xa0905012105100e0c0a1d01120b0f0a1b0512010515040314071e0305060705090108011401021f0f1107030e06030a060b041508130c060c0302070b 64
    0x20045401080c01c10f03822017160399000c0070202002a1034503880c81d01c400c0e040041c9032403185507a41c03020070841c651a25070740105030000c0400003c40080e010204c503504117a1250740021000940002800030004021440c1c1c00b180c004108070848500b001840e03405130005407000b50715680100200740300c0340624000100213602c1c43d040000391070000c20555005140340901c8500c2c01508028240b100d440d240010b407240e004400014482901603000c9030b0103504180e541d03010a178a008080d01030180d86d40348450450041c0200084130111843c1c00707011945280034002451210400c5980450b28103912086072000e0501c1103902280d0440b075801d070004400d480441d540d540c6c2080040c01402550440c6152900c04100405c440c0074590344241006255116100e06450700916804d021009440050140700e00681c140000c40c85034100c030041a00c07a004582c049500d928101006 = true := by decide +kernel

theorem cover : BRFrame.Cov 713669064 713848920 := by
  have h0 := BRFrame.cov_init 713669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 713669064 ≤ n) (h2 : n < 713848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
