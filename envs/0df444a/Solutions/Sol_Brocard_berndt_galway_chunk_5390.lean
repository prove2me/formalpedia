-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5390
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:42:48.904528+00:00
-- url     : https://prove2.me/submissions/ca31f710-b9ff-45a9-81ea-717fb4d19f31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 969244604 ≤ n < 969424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 969245854 1250 969244604 969244607
    0x8030612011b021009151e050405030703030b030c0a1403150415060b03070c0602090607080d06080607090e060405060a03021207030312290f0a09050406060b070b1501 73
    0x4903100d85040c079030900c090149151038000441c08011110b600300d030045802d10b0070710b03005d84010400181000c4040e10b02944a0549038000c0d091107000c80c02d820000c20700c80c541d1a8100c0e041280c0590300780e00f000c00c0040c01c0581c140224005184110028844090700b9400969480124403a03120341c2d49000355840202e45040c040c1c001c003850321114079405841c140c10b00204488241c5018803520b86008408071b103191004003628081c401e2a681d400d0404c2580d6640360080d80803441241d0721810034010034002400450050104404103000455006d15101340786280280280c80e14052051a07141800203203403140d0000d6211104076804141c0340c40e090041121a01c50740c0010b90401d0b20010443d03c401c00000710032088921170350341c0701800c1145040e00e40c00c94140da0070030082c036002102c030a5401c4240c043c2e5801180c600801382d2070300e50711140016180b1481c69001c41e201603141c0d030800043c004244a081e00070f05512000c0c07444e00c00341d540d9195900c200100b034110984007110441200b40d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 969247104 1250 969245854 969245869
    0x80f0c0c0406230123070b090105060303160f0305070c080a0303060e011206020f0f0301061e03060b030402130b030609160909170a030608030304230d0203030117010b1306210c03080306 81
    0x2010150589585611b20b0408501e03d00c82290402455800d000200329141000411601e050710b0b1125040c4458446035201e14070b088484000350b04000c400c0c0040804a020001440010132081009242841c00b620f000b034180d40540e4000540a00303680c004102c0f010182c0e0011a18030313800000107a4513010190b0200341c0740100214842010b20210000c1051f58103c00013500c0400f6030424003d0a6458601c00c505481c9a0700900b10007120a2000c41c00508020301d08640c070a405003000700d4155003210210303141a200316006002c0da4003101d03c0b408a80e81d100340c01350103440201c80a006010b482c1d00c92500e2505145031890000740c3c0080c6070596180301354403010242004d5016680e0340e0078282032142c1c0a400c0e614810607070006034a103400000ba0000340c80e20b6007018030b4000d9410345c0c0c6041c01c8800342c284a12101c0c0c0c401e549400348101c031981c2d0001a4580444100b400240d0203003000c1c5840542514041c1c0358104400508014020481c4803400008a90340002203035030300e644000100380301b03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 969248354 1250 969247104 969247157
    0xc0906070c0906050a090e0304030b07020f0105090c010f0905060f130e130c0603090b0a020a020708030d0e0607020607170403170a0e01290d080f0c0c04062301 70
    0x10015407800030410084940041c41214422a1280d6801c1c2d00c0d0081d84080340d2801841114680c0208000c10008160703420041c3c0c04101401907400c01c25140700006d09641c411200b08081e40c0040d8003285840da080b0452804800c1280380840019007880041042b6202c0c4440c0c0d8010014046440d0321038014401c0c2c4040030700311400c20360321903040541240d4401008150101d8004150030404900701c0d2003807161f010f10507086482c201c2980c4940d5002402540107500380c0045000301c000110300360104000800802080303c20000d0242c030044134960901401424001c00c5411020520003032660245c070070102d0800401d0f90174020b0702c6910781520030407952180b4580c1100702a0810841d198070354443c080b61a01e03407009101900c85e20341c02c03500c11080e90b09841a038030701c0d0014003100c2d0f003004d0508601c0203100c7c11006140c0038031f41040014503041024007010300e50065400a5040c14503001d0300c0010075520001e400e2a480902c5849146054280c4450400c400c2c803601511140750313141000740 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 969249604 1250 969248354 969248363
    0x11010204120b27100b060c030912070504090308040b1b1e04050a060203130b031e150904050f01060f0510030f09021201020702010207051509010c0302030d06090c0206090d02060c090607 81
    0x244800c1c3c0902502d5589113820755a00c2031800c0700d64502c5007008021544080d0110010314902800c410402c0301c2c1c00011518803d03a0310640001094540b514890451554000d4071809182e180900e030141803090020100d84042c1c05900c0c0d280c0141e8030b404142c0e424070640b4000100c2010004107514030354000c591003154030504409001415503000b0000700210303002942d1709944a074844001114500c01521070342040d18109003103030340c08000c460315240c0105002d01480c4010480e0710014a44420545043c3d9040e0410115092613490034441d2100030304007242407aa0061400001131007804041c180101415110090048441c0c1c099001c010786542c014400d220041503d15035a00070b400c5010102c0c05489858404100c6e840d140340f4003005101c100c41031b2868101c1c0000111000408203100301d00b50310052104803805041ca0041402802c0c04140c001880e07012035000074a003600c0904091540e403c049140403e0750b42c0801c0295001035200f0b8005e55a08008001c103509105103c0c02a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 969250854 1250 969249604 969249661
    0xd150501170d0905060a030f06090212100609050102060c2d0d0b01030501050607030302090d06141b03040b0a0b030703051501050a051c0f1119030311010204120b 71
    0x244805403851184a040a200100d55402c601900c058a074181180680c50b402582031103d41491846034000c90000b064860700841d10b19030765460034040c6c1e08440300c06521074500c0b00030401242c042d41c920000610442c60f142c0744451030080041d448440c0980942030804001401c3c0d0569010855003c8041c004030300300d000f900017640c098102e2500044090306105041c41a51082584a03004950590f000100014900301c1e295130194025444190655003000d82030800e54003140c00b510418014445000800382c03585050803900c00f02d10720701c81d0042403400052090001044070040c04540c084003003100003034006142000a03190010f00da0008003540714100c03800d80260b480c0c044417412250180d44c2034050326140c0c0c04106030601070030f0303401164258074003108000c41d1000808050a034000c11200e04602041c00c0482d0022445800c400ca20351400c032020010980d03c600c40d44006181c05000314180380c20440f400e49515020072000c1d0410078000301189840d04140e4440c12451446c0280c503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 969252104 1250 969250854 969250859
    0x1303021509032d01061404050a0b10020d0311041409101a04030b101a03060d0c030501091101030608030921030a180812040608253204050d150501 64
    0x341e100460b10100c10442060040041d4182c00050117020240c0d041c000204452085000600c4002c1000030b00d20301030980c03190400b40c4241c03a0391840600440e190380c0030304003a0741008000740035120844204a10000b040008005130551111400140c1c00200c07a01c0ca46600d9102e560b141900303098000b4a1160710041e401b400c1000e10324000d204980c840c81d609807060b0340c0d03210010405070151154100d00c8a160100b169208180b200031a0f001c00021f04007855410692a2684000001d40007110f00c1da40d60903191082c0112081e501101c1e48007403901740440c0e81040031454403170240011042c0a080b400c104c011516451091032104003544c401269182c3c142c4001c01400400112855400c03448445004503603d0b0011841049130303044822964a0246015403c80e2609002001c40c40e8045081c80c0c001c3c0188100340413042c02012681c0d4a182c065025050021a81040f043c1d110419075607000b10400325484005546c100c40303044400e0401d29140f810090b660403c40f20164a8440c50003002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 969253354 1250 969252104 969252133
    0x6281113090b0301020901020d05220f0602060a0506030705040207110d1211010b010e010e01020309130b040c0c0f110d12020102031e0601090509090703200411130302150903 76
    0x54400c69144070000d006211009040c0740c201d00c03414440780d0058002a200d0f030b000600450083c00100d00d801e041e0b02541c403203045019095003858214461610000c10100049941042040e400000c50402000b003400d02d10002a0f65815a1007241e00442c0c0104410041c00840d1000b11780030f41c00903100b103011b0110742c0786c1410142e45d615103100100b054504480e0801c1c03c1440340415208042c0c50b2005082446001901c0741e0b030380001c13542d04600c002c0003032560b2500c4a00210004080100340840c2401e000b004010541c1c005480100c10001c03894140720100b071800314409005a00144011a03c1044201140304044070313010107009a44803100f5036987c203a0541c01140300d8030710b240c005848107803104055120107d013924200e0020303051142c18001864a0031394160481e54601c11aa18644d5940d9041100c1c20140407075807910074002800d90007030505000300d42d00905056000c52500640c5c0306281040c0049000c0039015070010b002c801d100e07050f00700858440c94801030444903180b00c507110303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 969254604 1250 969253354 969253387
    0x70f0905060c0c0406080601140d1e03090302270c03091c090e06010c021f02030d0603060b2106010b07020625060e1f0504080d0c051209062811 63
    0x70f165010f549445000030350038a0104180741681c15420782c2400c0f000c4c200d410001c183e1203514080d41c00d40503002c0400049480b0900845520380300c3d8540c008120318600400960414100c0d507924201403410020088d607080d04e11555001c0303a41d40501d42c507600c517482e003145415488040104412003401c400e1042d81c0d00074440381c003111451504503425a0702c20004495030b03009040003d41005201d5003c4440340442c141c1c00054403803d00c122070815443c42017080a4446a50080d102180c1d12101c0e0030311400c20120103040880160b00c070a444048400d101942c8a0b414481d1103100240030502308115030f07800d011107048255031120761012a0710f01c0280180c803140c1c1001107442524020412096040100d080380c009000d24800b100c0c2046a9400107000d800300802c1128501e100f0016030252200d14850441c600e80e4550b40c158482c5a059400402c0c410042c16545180e40322000b080b04002c1750510071000204080741c644214060606d1440142594415501045a020800041441d590308 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 969255854 1250 969254604 969254623
    0x21207050a06171308070f020f19051206070807110c1e01120c020c0f01050c03030a091e0f1104021c0b040b0402030103080904150b07290708070f0905060c 68
    0x21a0301d000d511068103001c03495074281030040601c481402240c010031055a0a01c7c1480c0c005802ca0041d8180000022032604030034108801d200c510340002c3c80340b410503400c4400030001c498010403881c1070040015041c000300a00f044208a080065040100028003040d15013010140c2544806824086c14a00700480400210700180700710003503014412181c00340e41c1c5000d1440d0050301c0030071a100305201c20b00b0441c18013181030000030441d1035980e00341000118855400c840313000602280d145001406520030740c106940d21480000b040b00443d8090303d000c0703841c903848401541c00210481c04107001e40210310300d401100304a1a10f0050130140c0d500710351000001203404015103080f44c41000103c0c0800e020242044806200d41c52081c1082d03445400d090f8448860754104540d074486010b0140d01c051004c41c0c8190502408007102e224076421500311045040401d032a910300014018810b0b00010070b030a0800168003241d4030081e00480e2004068007015040d903680d5050910071035901c3c070240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 969257104 1250 969255854 969255887
    0x11120306010f0c0210080c1309060306050c0f04122306090f031213050304030845090a0b040e0a02031b010c1101030f0203010e040b22021207050a06 65
    0x160b00344a0464425621001c00d150300825220400080c5a001c80780840010003041142104000368845a0741a44041000300032020011840d20f05629145003503410181c20f0300c500c08401d101a5000448440c183ca0a4500402c80b908500a0600303010300386240100b429145e0b542c440d0b962044c2a00045403452241c3e40d030b207040380c55003041758a240c0e58034480c05022700030820b6154003007402e0410b10300f000111a40520101d03800d1a44949690010b540181401a00720781004030007090800b00e4043c40003903614000b005500c030701f40a40c9001039241341400b0b20740300f0362401c00040c03d180304507400b009100d8070141040001c803900350099a6036501d1018164824480c2c030f20300c1110440c003454070040c60b0f40182d544220a650b281d8980c0f0a0725075881007141410740351010f9902c940f809202a60084c0348503134510f0814140b901b0442c0c1072505c080c20704030120207010130107120600082c0d80da03003001c2d606442d000a1142900200b84c1410340e142c00c150350008004000088650f4803c02110014645 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 969258354 1250 969257104 969257117
    0x1c1403090f011a0f011803080406050315010f0804020603040212030a2105010302031f06080616110c0618030c090109050709080607020606012006070306080f0307081602011112030601 80
    0x144400f60000c40c081c0d8403840d8801c1005415111552003165410039200140c002076030125103035a10603045421580040380000c102004001c1b00d00380000f1094100e81003800c010301e14074528034005000041c020406401000000085011500c1302030f4030512080680d4144e07500c407404038000404070103506060001282201090401846043c46003a0403250700600401490b6214400c0940c0c841c40082a4018940d43d036500044200c1c06200d014072400400103203401d08020318101602d0005030400000c40c5900071814001d0701e032500700490300008804101d0802850f150b00010785820740402e45a5000030041f000041c1e407a005070003440c0500c0e0140c44046015403140780e21580d480701140c02c0801644043d02058039035010385c0e0045810b05e814510646042a03c8090b14034140c0700781c4035280020381e284002c000c440414400140d8034031101c0040c6d841c00f4201c1d00c0d980d03194051a080100300c01e40b0166407404680c02000c6070031241c0e41134030550340c2007040e6082116030381d0411030340c0c1404a0f0780b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 969259604 1250 969258354 969258371
    0x60f0201060e06060d050c1303030e0a06180608090309031515030d0e0402090a09090f0209090706120209120a03051201060e06120a060b0c0102040f0b09031c1403090f01 74
    0x81c0700c90098420031000d010517007030507940b44603200642005880d802000100b0001c400d41c0c941e801c850030000e540a0740f00c2034160754a1006014811810794012000c00070101002c0c1c1d18011041c00d040111032842c0780c20015610780c4e560040c11482203100d8558584540a143c0000c1c011119a440c41241d0716581003880000002c01d01d516260140c401c0e80004500c141c40000c5890035601401841101801500c00192a49108001c668260030285c4000c0b00240486046160003443c9a500001c1c200152501524000c8042c00d800c142c41621291640c020400c01c00e16210440e00c1e42142d000b1b00100c600c04816420050110b51240710b0645142a00d040045802c07405490b0300d580418018015130310b040c001c3c801080c4402005000781c00031070303140c4c640015643d07110405800345807001c43c00103949138504a1840e4032a003898ac04440b030701d0b50500c040d00f000c0c1d4001c40d850710100c1d2900210010341030719580454090381c042c00d04404400000c414801c482c1c0c40001d529240c2e8080d04000c01c0200d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 969260854 1250 969259604 969259619
    0x316020f0f011b171f03020d050f010509010216030c05011b1e0806060a0804060603020901060f030b030d020304030b0a0e010c030b0405070309020f210604080909011d0727060f020106 80
    0x200b11040d5013095004203001c40c0c2280303600d007012010300031244203960b10f0f25104d07400590141c107441000d491a80c010709801d1501d44003031080c03076002600b0384001c62400b411079a801489040c0c01c580a018880207460750020b0147c2900030800c130544000302c031980170b41d60302e002500107520201d03103c03a105140c258180e20300f80543c2520340070785001402c10f414000036040440e00c070140140100c5905465480000050720350300342c130f2800780005488802419a0340c4100800321003407000050b100c0d07404022081c03240c80e008411202035a41142c800b8106d680c5400b040c0b4050401e0038291203441d8a402c00880207254594070003d00c1107001c0b2414452525644021420780e17214680283d40310740b28000340e0300c60b4035140102c2440130580280b1540c4081903400c0307076810a10b08440644009000260103541450010407480c0580720700407642080c2c8a548e02514100540108004184002c1e40d03581d0b09840c2c0d048104170200340c510ba41601d41c2c10303214440100f0281c03003256050055800c1101c04541079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 969262104 1250 969260854 969260867
    0x602130303090312080408030604180c080c1804020d02010c020d050a1112060613150f2d0e0604090c270b1212030402060405060409050712020a050316020f0f011b 71
    0x9071f800024203802c40d00c500e000c000c01491180d05074104408080341681c00a00e030121404000e180a00c0a0104559a14244a5078464039050104484001c00403c401030b5148540c0f07007840c0f50203181c84803044d045403010038102c241264015201c1e100b00c00c102410009070300c0510094040540320401f10740d90030f0191640d00e070740c251085584004455500544142540d22100100c0b4103001d0600b001503a0740b0201000c0030301d0b0780000040c01080744004201101c5002d030148011014164072265600d090380448006401619113841246c40c2c01d2180c01740541241d01c5030142000d81001e92030040c1c40000c20021000c2e484150394400c0c1800c45504541c80d010603035034009032001c4041c11800c40d0443d204171031a80008e008aa2200d400d11012031952a002d01501c00b61036030b440d0000c1c5504105030040c10514007244c071036510700c1c0104540100154403500392504002c50220781c0f00c00044001d4182d080c48010b150180b2148102c425061804805401c00c00584401300d1a070301c0350115000c1c084808 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 969263354 1250 969262104 969262111
    0x3110603091903050f0a0201060305070803071205030c0409180b100b1210170d110309210109080a0302072102060103080d11070f0209060f030606010309060213030309031208 76
    0x1207810156541d8540021903000e0940c80f8030030f2400d10b01e05401a040c800854021303184c0d61006071745d101000d03c20400d04004000181c050b180046091240340e98455140080c0d100c131800c01c2007804404945044a01d0301618094407000d6010300005659402c01d1600c000030710410360341e2124190116000c0203400700d00c4016181c2c101080c0d45000a00d074404ca09080d00501103401c0b14103d4800022141c240d51600d0b80f088045001074a41d03807200c032100038280b42c08004040e4554108024107011a52941030550910030203040b000603020320b00c840b541c010b090010001d0030010b0700007240d2880036032541c001d090413846490b401c4c01400903440e6100500900358450070159021400500200b6020805000d54050740140804c010310120311151481d00001d801321105020820390324118613280c0c5402d1b50018090f06c2c020741050121000981d106405400c442c14182d5410800f402c0c010742c1d8046a8a4041e8000b080340050b940703240c014074100041c44241c403941007200e40541400d05c1144510300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 969264604 1250 969263354 969263371
    0x12060a0b031b0d0c0801031505070219080d0507030608011404021e0d0f030906080c03101815080703050c150712050c100f06050406060c06090206120c030103110603 72
    0x1d540c2ca80d1400c1540c42003401100034001424811050f0082c0c0500840c0e06a8200341e481001551542c940f000e076542a900382840b0f12030600c0104408a680021b4205807040c1d00070081c681c510860070007d0301440f520205030601800c0904000c6a1501600000c0481d9002d4000704142d10040ba151070f01c6038410b4900139440040001c41058000d021001c00403a413a00504061110716103a940310241200001d00300e000c1000c0c11010410b5030b408c40b0400d0b50046158041c0c43c0b4510b0074800303c01400b000c90082510349443c00c2280c0d0341310707071459010707070881e0001701c0c80d01d0146503c9084550b0b403034409200c21901841a9405610181025803694001e00705c0310314914200f8506a0344c0c4c400c3c9000110343d00c3c0c10020180039a00c1e01c980c0402c0150f00c500b16140002800e001c4203604001520322a808c05ca0181d403c0c01010400c0a82c030282e068565500040d00061031040c51000401e542309401000d071041c40c9840c24844030400110056040f280701c2ca40d403030304444181d028003286000c115130185 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 969265854 1250 969264604 969264607
    0x60a0801090c0306150b04060c11010e1807051309290a2c04030f08070e0102030421020411030106090f0315020a030e190c080312191e0212060a0b 64
    0x10344c058009400d420708410b506620141c0350312410541c0e0304141c2c001c0740082d003c0310141d01442035800c00b458040340c0a01c4c202c0751100310000800c070000811034808005401d5080040c1d40c0c030380701d0000c1d200c0f0700011420740301c3c101c1c1d0fa402e0300101800155407010100751005080302c0f80d5035201e0701d40c900726040c0038001c0c4219519001c0201e5500070046000020380ca071000255046404011703000781309034866155414034006541000f003254000a1039803041c81440c82d0001c509030f0700003060300d00711880307990249a02e055600001682a9203030000a402504101214616089501c0614140e5036a0b94504280d25603c03180301d0494200f9120180807a000c5c00c000c1c4603100d40540042c84088464100801c402894840715440c001d88144034624071a00580318400b0008038001e04001400090021800d00d00003d9060300c2e240b8024115401011101d8291800803086030800480701c89a28004010488118042c5002e036009501d200001c0c00104006a210b103403042d0a4001e032009001407a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 969267104 1250 969265854 969265859
    0x21005010b090a0f05241603031d0604020319020103091b0e10060f0c020607021201020418051e13060c0503071407050d03051b0301260304031106161a060a0801090c 72
    0x91341d0101c25071100d000b640c6c4080143c000c410014810084407a2301c680d0700001c00c5101e4000203c80e84120300c2c8180f4a07030300a80b050001580d000030b04481091030160003942c10355224401a002402014402080d07460010710200640c20200707005011070351a00c501d10416640c0d03428503c0c402a880c01103901150f08030304a50340c92442002e0b01c1042900c040c01c1c00f440d00100303800061a030800600e1003e00c0b82e400140c188103450303040304100c2003c46481020311507402d01c8080100e0003020204440201100140001c01001d204000d00180c103404c039004001d41c602e00340004103641d000b140c4e40d0b070100749074242488003000310310211080540c05c403001d8421042d8559007100549009006001002c4020070300c0c01c100000324009500811b40c10461070900b0b10b1009900c101301c2c408000d11800f0307070418031080003c01c01545150754801421614141d640c440c5401d0b01140c01d45140b0041c1c4a2804410f9152403014002c5100380150012125103425690f60b02c64242a2041504020250300c0d406030304 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 969268354 1250 969267104 969267139
    0xd021501060f1422180225030201110a03021e0309030318010b060f091302030105090106080601021006080d180b2d030712200a0f021005010b090a0f05 66
    0x30141c58100042169150460044044e00c04580d05900d21007204410b0f2800c002560402c1e00b01380101c0c01207038080d0305003d0303800c0c280b070b240300300010055a200320680e2510041501c01c2d44540c0c842d2000c461100c1e1505103e09008009401c2000740301c15000b207404c200902100b2000580340700d2480c60300210725594a29800c00e022200c0240c18032602d640300d00b200c2c0942c0d55648040c2150301d407591000707611340d2043c8003008150700103841880314140c8100018006915691038a070306455036400c14130403e8499a004034034264041241c6868030380350050100310001c0220319100c01801656542688035040388001340843d865210750b03100c2d92005c002c0345010b24948601108242403481c0c54080c075000907400202c10740d100719006d01c0020b015403400a02c1c4901841500042166104490101710704000d90359107d1203103c101c00140034000240b1030920b0720030007146258805d0f901040c4250359581c203000d40c075034020400701da200f084001804101d880004224070105c9000902210000040c0c202 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 969269604 1250 969268354 969268367
    0x20d060b010c0b09030703120c091a12042108061e0d05030c0d080907050a0e150a090f110903071a130e1603050f0c0c0708010e0d021501060f 62
    0x200c40c18408800341c007202140d80200c030284112040406190754880c6841e00404c0105c0300d0312140d40161900c02e10031040e0f40c1c88a8070a081d103078a003007a607c0300002107607440811b004146141e00c51080c16008c00c02040507040700c01144502c2428501346c081080c0e04103803458042116440d030440b21000902200083c1030300040b40342c0c2c0024098641450190715000d086038007801601c9450340c040820b412070781d1740c0092025070004420003e06100350500b00001d4800c8141d128030010005090040b812040200646203e040b0340203018032100d03a034a8014002502c034210140748842d14209040300518001d0044a41c401002005001c8490509850340e00e00001d6841140703841c2002e0080c02e4500c2070f81c0d50113030080d2a901d01506540d14103910b101c41d145c0c4c1480b02c1c500405003003c003800380380065203900f541c1001e2110621501c03901c0f506000ba01c0e240050340700508030740c240300362403020184c00314080a007a4601c1d070980d1014003480020100060083c8107103c0015001d44161052610411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 969270854 1250 969269604 969269621
    0x308060402030c0f030f010303090b04150f0318060b01020106060509030604060911030a0302061005040c08060d031101020f0d060504051015021c0f030f0b031213051801140a03020d06 80
    0x120f205003040f00070008240190011039110142240034401402450703002800c42004100c5100701038585410440b60504000703d0081400500c034501e0b800c0e102e003d0080d0020407800e070325011070341001c0e40a401c15901030a42500c200c0c0c0594a010804200c05105c0c034100d4120300070140050585482d00d5440c0b6005110400c1c0c107842c0b040903841848510350f01400002080c0303020741c1c014881404d100c144030391914400d030320151095280112110362140c06c1a80766034040000c0710000b4082100b0305054417820742d00000d130b590a510008080d040b00c3c070604041c02c03103454898810440c6079143d100303000850b9030540c0c07804019944904e0405c041c0041c1c0c402266507550a1055807444201034000c0b0300e011200d80f40340c0c40030514020450507101c5d818890340d501c1080b0f1000a120a14007803005c00e0b160020b0078528404070a000407150301940040e08810010a00074020115000c9250403600584400b0b0240c1041e09503407040b18481854018105019641c0052101214a01981d1440010610003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 969272104 1250 969270854 969270871
    0xc0603060b1209030d061d0702013308030f0d0b03070305070312030e060f0a0f14160504030b0c040303110a0c210c0b0c0d110a1202160303170f04030806040203 70
    0x20004500810b11701d0051100501d5002041c41007044402d003a8031100400170408c9003160b00d4090300d65039041d9014000f0981c40c5117024901031003002000c1c074903200445074003e80514400000c2006400e00010000c000c02c0e410000c08109411501c020980c0b00d010510028005520030481400410f1050900b860b4a2080d810001400e001041d141c6042207011510104c01480c00000c000c41080700d07015003188005441401c014862124407040410f03080a029014a0038508400d941c07898043c0089501445e000310007084603180a0381c2040f00b9900c540801c40020702d0542600c0c0c4101d8001a41e00000396011440600440c200340d84180c02009180407a0902d1491380300c40404102c50285880c044c01e04e41c001d007a03036601104501d40c50701c078007540300c0340802c040120303650440400801da21040951000340050780300c92800b4101d180c4520584803981010185200008240c2c00c1a042c902e41e0418240301c5080396500f01554004220440d070203000304030018006800d07490700342d0040d944841c21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 969273354 1250 969272104 969272107
    0x9230606062223010e010e0307260a0f0c0f03260f0d150f0317090414180129131122090e030d0510050d0501090c0603060b120903 57
    0x21101981d0b14508456072072480d48546460000413941c2c002c0403100b40b03034001e00f032010600003070f200030030380e505840d10603800101e010b100e0b00000326002c8280b1040155076602121181e020b24289030040342c0d0341c0f07001100d01e213210301d400103640140b200c101c03001c99401c4103542c00310b400e001c5c0c0c180d82c5004a43301142d101c45000c010110802102e40090010102c0186001401d00f10248800b41c0c1032602e6040028001c0c4212020400a081c101d41031030090403503c1003036120455000414040c2070080a111007980c400002c109844104820044c0b0810050380240f08400a0518000b100380c1000d00c60070701d269980d00032010300d08200200019000c4254070000707028003c2c940c000702d80c0c0c104072801c07002201300000c90307550084a81d08007405003c651004000742c50301d140206507203100304180415401e0b00d81d40060888415038403072100030032000e0a044680c00e0780d071805a0081214010840e03000c003080c0c0021031f070a4400d1049106940d00408528588081100c03d1110004010440100e45c8070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 969274604 1250 969273354 969273359
    0x61f090e09010b101e03090204061a0309100603030f08060a090218011103090307050d1104060303170a0b090c0f2a0d051303170706092306060622 64
    0x5904100e10722a440c000c0000556585690400000c1d9048107600b00c00c02c0200001c200c3e011403594040315241e80a0306000458000c1c500c04100903001507030120162014a820300194428501c0c0150301c101d850304191217034808500c400e24211a880d010180004007808024400180518240e5400060086c026000299a00074450599002c4c119500c00f1401324002c50001e560444028280440c41c00040c44c01d021000020a5880ba200d00c00c0d9489404607a48040c28444044409035000c44050010300480b0303220706002e0b0040e003400e1501090540100002495000c00c3c0c81441c0f4000401042030455072544112901d09402445645d03800181c00c2003040703600745800d440160000c80da0008503c82d044210202e60a01c240502c02c01c05001d1b00300240c103190106000c000003684d600241d070303c01a1221900d040c0450140d000010300c82031900e10307074605001c0321100303094000e00348503120301c6103085468505880d1070040d11907640104042c03013001a01c10a40c408504501a07024002c0210f9a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 969275854 1250 969274604 969274619
    0x30c07120201150e150616050303010806071d011d0102010f180219060503070f03110d1e0603151a03100c14030c0d0f0b060705010f050f061f09 63
    0x15114040c400940e55803080f540c954402080c001000340001a2003c1e0503203800c009150030b401d41c5000b4644216000035400340c5d018400d0003284c006d26080b0f8101da440e5070312076500c180c0d40c01050300c0120105a18540c0e440514907107000f910188203060f075508603030f440c03507071081c000c40c013402011f25041d9525211000c50020301446455002d141020704021420418010f1207a01054100f502401d1080e003601484807030f0700030080b290002240d2420420540c842c2008400034580b52114101030310b40021074500c0d11300e040e08548100c2085000e4002d040900c00e1000c0120b610a11008052200030500d024580c0304503401000c51b02d00d94070786950310440c10700c0020300306a81a9150340807180c0d5031409040084c2c0c09104501d04443c0105860f107942040c00220041d4050852007022003034540301c0d200c02e050602c0e00b05200364840640340a403104c003130b450054060000040751440036407501000850003084014850f025a9004e4000616811010120307180d00d200c603c800c2c0d0501404c2a00050101c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 969277104 1250 969275854 969275873
    0x2a0516142a040507230909090a120513031a07020c040b01090e10080a140c010e060306040903030b0301020301080a05100501062003070813230901170a02040204060c030f0c0b04020402030c07 83
    0xc10031754443ca603504110406c000c40c0d400d0103802d5503100d5001400240001c0c1c42c03c0c0c0d80340401d18041c1810350316003c400c40c01d1110801c503500001c2460a0700c0c4217141040311b00d061290301514943d001d588a040c0214140004c941e0382e80300d00c1d070000780c00c800c0802c82d245000c0d4001c0e8101c2400c0c40300300074040d00c030000d8518109058508480c0c01d1f070442c440c81140303076007803103400c0c4800002d203426a8004e000c3c41c002403681c000609814462075440c2c501c001050b009034000000443d01034002e5443c1c0da92020748949410069500350f5044c09042c80e0900c1803e103a2060b94141c403000e443e00c40c0146019050710007050110081c40031644410017031600810b413400060700c071101c01d50119032511420600040c0103100c04011030000088201403403c2c01d66111388115054616003000c40c5440701d2031a10140c5804208a8044d401c07500c0009e0118500354403c2d8078081c01030180d02c4402d56600031290884580a4520001d010030761a20081401803410740c00950f040303d10844182c0c100070494a540f00f04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 969278354 1250 969277104 969277157
    0xc11130e101a2e170a18140114040c05010306060302030c1605070308040f0f05100e060a09120b04050c01090f210212010c030f2a0516142a040507 64
    0x100ba0b11030528082c4500049015174020b0100c5414442003c02c1200f82c4110590040c00416107104141c1c070408069095010a105d0b505112a140803030500e810a41e01d0081140501400a401c0c0440460542e0080c001c4a00076011091010b261209410002080d039640a90480b0140603144002000c507044c040030b400544a00c0342d51502c03640c41c02c0359001c02c000c40d42d40610b00030035902424440b11070b048540b0440d13001042d102c00c0d50b600743e042c200b00c9542900342c00091200d11911024804d00c04007110240c80340d4841c00c00ca43c81c404c1c42c2c00042d20300070303618400e0030602d0f003440c2c10a10401004281070300354960401d402c60729100150340007800403078107c0081120741c0c0d540ca02140084c0c0d49405401000c03443c460081081105240c0e000b07148040c2d104154150f842200031a03980c1e01d1080040b030390310259426801e07030314440394507210407040b0b401d031050071140c131400d8504060b50500e00100314080c001142d2002080d002242808050040208808140000080701a02403800f50304282c11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 969279604 1250 969278354 969278357
    0x50d020a03050607020c0315010308120c0906070305030a06061e050c071a07020415060512090c0909060a05092d100f0603061109030606010c11130e101a2e 68
    0x46c044d1550516203009501241c5560b200304031401000807c0c140422225070810703008140c0c000d540c800ca0300440d507209801503507404c0003002070b2076003d059210015602800101e8000c2c00313510703503525080380e82d08062210040c040d440341c011020818052070051100012074400d80d50300f0791b17444014010480e48500d042d03003d00e00000d6902c0c21843c0c10b2140e6a45c00007881c00800f031350340c10400c00030301c135010781c0e41d00071404038104001c24450001005000841c000090030314000d440c014410945941c410f80b410035025042002144400c3c00110703400100c41c4400c1124a1020b000c1e41946051585030070000155000300b03282d403a00450903016105107600c04d401c3c04941e8501e9440c00008855405090741545141400000710b10356002c91420f410107000d2034100074512042c00d08a0390f00308859591940541c11070f080710303000e2100da04103003c0e5010100c25070309002da4000141c000c3c1c8141446001800c056211b52241610304040c0511005048086120041d00c9102c0303540e40d00301c0c00303e40da4030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 969280854 1250 969279604 969279613
    0x1205010f0b16051506190f060f090306050114150304080304060b0d0b04081e0c10110f040906050f0102150a05090337050a09060f0302070506041406090a020a050d020a0305060702 78
    0x60328100f21001c0c05030512414141c00c0c9541c98100c000061f0309041c0034020070000d84100c2c4800052190031103102441d00840104204d50351610040c03103800e4100e40043c024210348031590322121100c0c0643e846a0340095074149181d580f6504c100081c0709118110394041c49519140b00403920981d441d920403441880351583d200b41d2a054204513030b24418104030038040c10016540d5035040880d5501840c00d034824081048044140e0390786450160148842800d9004038000403035000c00e4008008070350040d00c3c10084224500c00490f01c62030340c0c010191200f4201000300e400b800c825480580c0c04524842a00c2c02d194225040708240720521640355039082070b99111011511700c80d82a0754103001c1c2c0c0d0820524021050b00080e00e80685440f0320b00c140410a6029510f960081c0c04546200c0d51040a07034607103240900e840b1803c500310000300a6075114820000d0000b030000583c0d400c0e0241c00500129065241c0410041c0501c01d510040741c0026020384000b002407420003150b0b000300d081c2c2d0042c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 969282104 1250 969280854 969280861
    0xb070e06160f0c17030706111903020d0b090f1303020102160317010e091005190f0203040302150c090f03030d0212090607210b180c0a1205010f0b160515 67
    0x3c00c1c00d0079564000b103e0074650f601c02e41040080000c222014150711003070100e00c00e550f1f071182c04c5040c01540c1d0041c40140f03124001c00042541a401044040c0018408010320102071303043c4490307641704849203007805104102140c204200420441c0000b846071001500e40510303041400240b100740b0324100c021034140d10f10701c0e0b0642c040e0002c10340900f281d001e0810007498440035130f60340c81c0181402c1070440c542d141301056600c20003800ca1100c40e00048401d0120444140b480303c000d41c001c82d802c1d00140030352405c1e031600c0c10580c1c11441c0030303030754650010b420160200e08000c40003144850007940740c0702c108038040c2c00941500103041107000d1030444860a140c40380f245410080001c2800c02003042c2603500c03030043c0050b41a6810342d8802c650b80003c40000b03040101e1518000d101200c2d01e4105890200a004014540240043c00c820b6613581039052021410400f91442801a503040c2034408505110000d404805045e40e2440140000e0003450720351900e50030100364182500c4004040d1040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 969283354 1250 969282104 969282113
    0x60702131a03100504081b1603032606130b0d0b0a0606020d0e0102032502030601030b160c080304121404080615092e0801150305010b0105070b070e06160f 68
    0x48083d60740b035070b0180854035040d65107019501c2035140403141c201040c0600140340404100081c0381a61040b501c085950b2207040140c104080407824103006480c01001e058040c2c103002c40540981c1000e0607140c8100c03600302c000000327054920001a0003a41000d500c2021a10310390301c03076004030644480040c0a80c00d015000742424545080780c400d00240080482c9540d03070000031242d00d11240c00001c40241c0f2190710708c0303108403900080030b54544103040010090265441a050082c051840020300d00c1c8164101903812800c00e000240400c113050000402040c1b03400103030f00681e41580340481d0002c00603401d490194100340c1001f0090740c052410082e640e4034840181c3c60b480400c40308410f085c9000d11120726600782542e1000188110140c0503a81d8400b0500c88c2d0001d80310007002480520180e2819454240c00d521007039500b5801d0091030321465000b80c2c100d03111240c10118150303c5542c5c40307100f40d51014004032550741058041040c0341140014100b5140e0041c4601800c00040358a400c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 969284604 1250 969283354 969283363
    0xb0f12070b0a111009060501050919110403021e090105010207030f0b09070807080a0b07050c0604030c08211015020303181c02010207030e03060121020f0910150914060702131a03 78
    0x4ad002c2c406010a20491080301d016413070740c42200074400b059107070400c1c0c40c084140c0543d500083d003080300086c802038130b00204000141d0760030042c2c0c2da8200030382c0e0300c01c01266140c00c2403001400714068000c4413004200d001502c503900140e40d07021a000340d980c03040355034079280c41d507408040203402910041c4104121842c82d1a040041443c0040c20103850050003a02d40002034001001c1c0801c1600b0700c003c11146d0303c140c550030540d603019843e0f03030f800c0820540310481044403040d0048040c0368011402c0b0300700503440d07428889290f00039411742c1ea803880d64141c0c0940c10100020310b0311508100c4544007040c40c174003000e040c0c5035a002580301c1b807041c64060421520000b07071038400c1d01324000601041055440403035414050308c2040d48030724039500101d40a0186602500c0d00f1010250800451007030389119201102c095100b2180a01c086800490740b0302d000303000e01e030313406440700c1c2c01a20b80c1c0c5003207405007110a00043c001244168502441403c9030449400354540b070b015051951050301c0c0922 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 969285854 1250 969284604 969284609
    0x607060b24120c090f0f01090e0a02070204060e040803011203020a02040c050a030506030c100509010311030f1e07020a0b0a020c1e0d030603020307060c08120a0b0f12070b0a111009060501 82
    0xf040900f00404031001820446010f000d40340242c1a03148145000c0c0e108000220040c04030f031610700d5841c1000e0521802a500c030346026400f0324100070700010800c403a840c20510581d0010030003401c60342002c2d143c2d0b5559011400a80c118072480e07014102595032445080c44031500350716019079408141c040030701030310310040215200e50400c001ca01c2c500d8445210064861449103003040d40c2e0f85003180142c1c0181b103080d035403050340381001c020043c6a000f2080d11600406c0b40030100c0510030301000910318040d0080b100207005801c410700c06c10009000000140d007100142601504006000b0f01d107902d8040c910f40c0704842c091008112043c010030500050080318402d00d81405214255000b290343e903a82c038440c1104001441d03038a6000e200d41c1d403050b10041c80260110f024a4102010300310068400100030764450380c05603101e08041e1400b41d05449070a12041c0161008500e05408941160062520803090001406a403218420140b00c4040e540141e000c0c0000c440006040443c100d0b00142c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 969287104 1250 969285854 969285871
    0xc060b06090109090b03010213090b0102120c030405060d0e15100f0803120a06080708060a1514041d150a0c09081c03180818010801050607060b2412 65
    0x4200e0400540d0f4410304a00954800e032601240740352010f00460700a200741c2e0340000394040009408105001980c1013004010400d034210b804c0c00a003821082414030590701c500c081c0c1d91081008000900f04400030304a003103060440001c0c00181e030441c55050402c05032041401034000c004010f1a80310128205026000b030303051000b8194200081c00d65244201c2030f036044910084400188071240c0c60700541c8c0034105400aa84815a03508203080d6a03400956850300c1b201d007000200c08001020b0070300c40c0c5c00c580c026140d80810240c89000e00c40184214000c15650000038100034454003c1001000c08409400702603d02c4c80c45c1030082e500455500ba003844041101d18038082044000000e039119103180828601c10f03401000742016030060411184074022042c9034141c600900c11940042c05840f000e158401603509031080045035070010074001c00f0b44c411001e008000100305980e02000342072300c001d406505103444401400840041c440c02d0303185032880004485e01e803080208046c50304444c20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 969288354 1250 969287104 969287107
    0xb0a080f090c1e0a151b0b0406052a04031104022d0403150f0c14031b0f03011e09090812091009050c0a0f0b090f01120c0c060b06 57
    0x8414210348035542c0058040c815502c4400d00b4201a16005046107000c030004c00710406107a455051482c01c4d0300003e40980426101324492050001c40112001d10039880120b0804584d215500c8000400018206190b8600b01a02034815144025100100f1151001055071039a1071480c02c1c040c900c1482c01001c0c002c900500c41698100310755405c04002201191400580c0c000c5020702d45014002da51019029001007083d1100054565001d0b0104c84805407080c81100382045081d51a110035501a070b64000d010000525000d6210550201e00950514168608100141120680d80080e0000382003810200c44002104036191080c100503c0c00c41020b00a14509448152050086400c2d01050000c0800084e031007410902101c0d810030807414041001c4611420519600e000c070107080ea000350116a0080f684501c9002100c0c11210030b0010300b40740540c400d0034045041e4000307a0841c10701003581203440d4110710a0003010400e0366a07070707107060000019040560940f01d5540069004010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 969289604 1250 969288354 969288361
    0x1020c10054807061b0801080105040b011503110f0a0e0316030609140609100c0207050303030c0a0504080307150612050c040e0c030d080405010b0301020313031101020909010b0a080f 80
    0x108050070036800c1003800300c1000b1030111015561150f00c03e01400511045c605600b007441015410901044042c2c5a541d080c1a41e88907a001800c0f6007040ea0042c100e868010010803c0d0002c5400304407001e5414680840c0c03a210304c5030601210380107040c0380c291111000c90451b044070b500030f158001c250b00071801003141c03403d007044414012000d408043c00585c0c45e1034074a0f060000507580038008142c41d0003218102e20f070102030b90b6290003610f031010606608014480700c03c0c510000d00d82059500003401303145161500204c404083e4002503400d0107100041c0400106034009001511155006440041070103901100c04000c4454640181c1036240315581c820012a10024080234600c6c030984000a03106d40709184680b50001c00c80b4640d9042c07140d0000580c840d50b2203031880b405584204000c1c00052501c80801d802d0380011546c0c0c281d03100c0121800b4001c60310500104400d080c406000502d030402e0800424401c40098002c014a40000240303082c00381c2e40281801e502031910703400300401c0e09 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 969290854 1250 969289604 969289681
    0x105090601030b130c0903020a090e0115080d0e210f011104150804060b060f0703082217040b0a0509010e030c0109090225030810241101020c1005 64
    0x88400c0e06640083d5680c5c04a40055001b6020303040995001400995029a40e0904c3d07c0640340708259400d4075424002401c03105000f03a90040309546d0280003520500b004001c013183c070014215003055120030440820074075507140d810303440e00c840d00d0640078184080d2000c10080c25650144443c40c04e81c441040100f082c40981c1c0f001200104c00ca2038004856240c1d03080c0030b406071000c61071560f03112a00090150b00142e680307000f03000341c81c8a80c80d01113050b0745200545d24070004a5102000c045540800a40021189007103010b000881c1c11740141441d48800d17011905030030011007900803c9001861100940c1c00c00d4031055098001c80c0100b010308900000240000a80e20400388800d40108000c4100341055001d0140e000c03c51080580c030702002e00b0001c041c84401c2c0d0f602c04040246900100e007621300311603030000b00d061146070f03141134400c0784000701c0d085d0a10001d40715032951709001d011034004c01805003078841e20b80c052000c24075042c41e9800b00d082c542e00d040c0d281842c410340c2040c0d150b0b09 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 969292104 1250 969290854 969290869
    0xe030712050c0909030903070f05010e060c0703030503040f05190c140d0303020c0106090f050a05061507080304030c0f03031a01050c0a020607050a080d050912182e02060105090601030b 81
    0x1800c00f6202d4059a4803920b200724510300034600056494000c00c040800c001c00c03164618011528241c0c4c409100c140c5100c284001442000952592600800b9090001c00c4c00b0700c00940d0010322807c2d6040303810000344c403420305001903419281d0040c1c0d000500b10080c424450300610242210310a4500c10301401b00c0000e0042d203240600405048d00490b02052964080d40100c2c0100f818032070074003038500c0e0405842d0042c0400c0300e038120341710b24000120b40c3c10b007000d803423000b07094040000181c54060300d40c0741c2c1049500010000c40401c51518400302c0002c0c80700103000422440f0b918007085022207402a0000d0240d0f103503286040050521106c4845180002c14a02840d01521b4030390380ca00030b900385542003000c007030b102501804000840c117480c0c3d8801c1d80103c1c401c42d921800c1d5050300d0251180000c03035108900005840480801620009152010303150f02c03100200c41d011445031200e9100e4240801d0315000603c0540c00c400c0042040d41891111580c0c081e400b481c04000b100121000550720 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 969293354 1250 969292104 969292123
    0x15090305072306220311030c1002070c091e150b0c060a0515030a1b0909080a230301051210320106050a0f030b1f120e0d1413060e03071205 61
    0x6c1105402081d240170f031003801110340d009007000070b660a00890402081c060340c0480e100b2203420801940c0061684a94491501c030313040950000c92901402c01c52080161400b031901d81052031540b0000940400c10000418151407080003801341c0b0b140000d0340104031040141310100d80f070340c104000350061368080350701503a10798805c0428400400862024a240358130b50401003d00d8034066101080c0007688000d010320050319610910b6064540080026005840c0d0200003e61400d0005000070310700241032079052030100085608a081c0f596801c0141c903018803145000c4c45410f0402e502e0030080ba00805505a410000c0f01e2140d4500f100041440c400c11840714200000703c130351018010711039080301601302030007060065103a0f03070704c03030012000c84003603d6202c0410501501106111400d000300e05403806190007605003546500f00503901e481c03078030b4180b0720010703400c009410f80540c4150500c400740c105030399901c40801c0745805040c680700c00e5400c00c415a103d15100348000607030000b1481d10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 969294604 1250 969293354 969293357
    0x20a03291318060504050a020307060f0e0f220f0c050304050d0305070915080712090f02090604090c08060a110304050703240203070f020705040207150903050723062203 74
    0x9240c070700181040c107842e07849075004210b14200400d00080c0940001c85070307074041c001c6080d43c081950341e100c04e56114a2510784540071031440340c2e280c02d0b10710381400e101e002a04003400e5040500d10100d00403c0c180020b1088000080d0741e120f8541190185101d0341c9604062800e1081c80c0d030030207440d90741e9643d110010710000c00d911000002e0740741d44202c80d0794009181161351404100c29106000c4c290810444100300001c40400000070740d8541307400350924943c0c00416440140b2055000d01039856401084035070030980f035803040c0c80010300a0300781100904030303013014100c507040c418050b006485011030401c3e0340e00c10900c28000400c0d8013094000440398010204005545055443c1c4101d445842540c501e0610200401c000541c0207684203060308584d5081e20001034851007084201c0c001c6150140240b0320142d100c01004240d9800713440900c0c06800c02d00c3c01d000d42d81d03075041242044542d450600031440010842648010419a50840e1208150b200d520600c000b074660903034050b0301c0203030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 969295854 1250 969294604 969294611
    0x28030c0b0f0d020c0f07090b03060a09020f04050411030d11060601230304061407030902180c0f18060a0c0c05060f18010e100e03060a020a0f21020a032913 68
    0x507201c50040111700d092400d860246d88400f0343d0f4140c0303d0014001985014042e000e85400152802810703c03036110a5940200501c4180b488881408000d0500500480b0818662a2403984e01e5400700141d0000049503a40c611450f000f01c6240c0307080a401900407818005030000c880c8001031091190050b031441d040c1429200e650354104071000d0416074514a42044440b0700748070440d0303410341081c0701c140d00954000c480705441d61003001c0510340454262840c203605010807115800d00000501c0c0140360803003030340051805040040d0303103544091501030101706000500c400300501c9400c20002001e045078542d08001041d0300b415034070302c20b240e0300b060480001e4110042c1c40e8000c0149050241010304262030b000c0c20381c0d5001d00030200000c0d116100b44030340d600203404a1858001c0701c0d403400703444e95000e0010021400c25181001c86401d440d92074500b0041d000d13400b1505101800941c070302da540220340f400600c0040d5480100b600040700032809111040300d2651240000d0756081c0700100d4001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 969297104 1250 969295854 969295867
    0x114010b0f07020603070c1202210a09030206030903041a0c0d05070303021e0d2706110706050403050a0e0402090f09100305030414030c0102161428030c0b0f0d02 71
    0x7001c0511520400a6204902200780030070550700035180244544981c540c03100034030582e1816a07490407180c1224042c01c40045d19601c5120f1240d01401a0f05018103200030140d4403640060143d800484082c183d07035101080401404244c07241006411507040e00003407030401003850581c4c580c0c440540840912000040d10001c1500c00c0c2c2c122504a84040c0740c00b4500006103015503150b5200969211240d41060b00440074a0210080c403402c085561541648460065031000302034107460240d840d281000780003e0012684600455100e42d2180d514155114840d10003c2c2101c8080c0038505c0c0114030512103001292540b140d070606155045401400c00c1e500c2440c01483c80d440e9801c0240300740404079000504840e244100f02081a080b01914214050b0100480e56050443d6440e940e40c1c41840c01084080710410807036402d880b01504030480700002c509103000a8801c0c51081e03601c0f8180c03840401c140718010101101820301c0030042031803d80001c4001c5e6480c06034002d6180003a80c002081d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 969298354 1250 969297104 969297127
    0x806010b03190f0e0d050405090f07110f0f0d0e060d0b060417060907050d0f030f050f2b0e1515090f070e060306090a0b0112060f05030f0114010b 64
    0x5806904528100a03c01c8011a0340d000c40a40340782904406580700c0d08150000140c054801e460550f100070740300e401180d54a078001605c00c40b0107048203082c00314440c2d00701d50a140521190f04415001801800c012589080c054505000f0030300c20070070032003101c05a5141d55604011a001d00b200c0034404075081410000045040c8500d60040d15003183c2d04105468400002c00d119108040040c15500002c1d03070360003800540c4070305550060044111210844c0064056010903102e007100c3c0c036200c1d0a103c89140070781690b501c102038002c8000d040e1505600c80b82c0c600f203100e20418400481c280242041518050b54030340134215600c205009482c00190a581c210b9031710454a840145480102e040031015030010f46003d4881c00c0001e1100300100c021418440201c0f0b0003420084d0003581c2d59500e6011200062000301304071410488540120b007821a2603000304c40140c4085450344481600d010b007014501071030a00504500d0b410f000900381c5011500310094111208242c5640d03440039200103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 969299604 1250 969298354 969298381
    0x309170c060315150d0905010e0c0303070206130e0c120a09120c03021207030509120c010207090c0c0203010c03050a150f0308030c13060c06180f14030c10051608010806010b03 77
    0x11808000e5101141401c6030349074581103421b400740100300801c4a800c1d01500c5030740350040017800301d8055104108e64401400c0c12001440014500004024100c4d11070a00c01030101d8103440d10b0703450410216250145c50208410503402920211041015401c103507141544030400c003072400148843c8110031018140240402080b8807110300c3c0540e80d807041854058819040764100f18020026500c03030403c001800540c20305a1031058000b084000e10f0003e05401810381015940104100345c140c450042c0c800b409480c2050300151404180c91418801c2d1604440280100c01c0c011480706804125100c00c1c076000000756030b0030501d25940c980e034940c40880b1501c540c102da156800e5158000103509640300960b03410300c1e0310505081c00010791385420303600544c1409c1e501a004c2d0365000c9549000481b889496180d040c4c5600c113487c00c02000300005810b09800340d01411149854004008149a025500c00e40c020365030700b0810030550500c0f9100e075842c9814010f103c0001c0e00040401c0b1141014203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 969300854 1250 969299604 969299629
    0x141606020c01020d0c090f090c030b180417180402070204110304050a1502030f0612010f06061710080a0b0903092806080c07030323040309170c060315 66
    0xa020341d529110504064000c1d4401d40801c00c0c040d24000641902520481514049803800c4a0300f2039240e043c100780742c004200e0300010030141942c44806118584815001c184040601d01120440d07142a0800c03c924190038041000d19000402854141c80c840c20116003c082c1d0540700141c030341c8030a10226005004141500f1034840000c0200030404c000081c221540d035104600000a15a903076100748107074003007a2144d01d21040221700161290410022010726841c8080011031511401c2411a0844030b05420040003d2410301c10303085003008402c0d04a0f00400011064030b0700c1d41c43c0800c50b07912070403c16001001c0b17069110214401e058208281e510f0303598001e0041c0300b800c078224507511181c00d80c2800c021500c81c3d4040006501805844014843c801d03003c00c2a00d40582503404030f00400c0c8003107201030030380304940b8911030030903030b04110b40d125602c42d8459000ca81e0074440d00009005001c6a405610340c030040040610b9100c22090b01d800240c840b13521480000920006540341c00444d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 969302104 1250 969300854 969300863
    0x60d0b040506070e041a0d020a0b0a030c110319081008030a1d0102060906180a05030c01090215030603120f090411132903100b03090c040509010c1416 66
    0x100500c020720a0114895006195580322685000481e00c240001e031860410804242d0080c8042e0005904200c1c0c3c841c0744991004000100e0241c51340d01000d00c5820200e04d030f2000075950740a5080c01c0350005607500304964050001d5090041024545004481580d42d0f41c0c104100f41c03002c50240c8146d9150100500b4480056a407500038800004100c0340c0303c10303640d1812418030200e5803103a5001145042c0200e0240d40684050342d5280c0500c0360b110384001074840745110b170401c1e100c0440d400b030001d0048655000008100c2104c10700412a18518445070008800000c00601c8915a00020380b6010460141c2c1441d44600d8801c241900c207010b0454059080350605e501446a40e41c10170040005040e2415880252030b203480c481108080103840042200c15454401c400848a1002a5600c1f4a80c41d090710821a00ca90f000c0050750029507101d4410740c0054480311151405000700e03540000c0c3c1d54020407000c0100e0200415000390f400304481118400101c50b54205188141e09c407007150007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 969303354 1250 969302104 969302123
    0x1020a12020d030518060106050306060f070609020907300e1b0103050c0a23130806040c06051206041a0604060801231005090f100c1208100b03060d 65
    0x5480007035107a146558507540001e180c4000200811441905c24000da0402002812140e013070139015a02e07503102030003480e0300030420f010340c074402c0c4190001410340318452100446c12864500c140302c82a58098841410310003400c1a00a4601c2c468480c0c95440c0302e5100c920052104103c1c0c2c1c84010040708414500c01e001c1c42075440e00346040300380c1c001041e034820b0340c1c204a5551000c014070600c1c020503803500c000a03043c3d030001d50f50883e0202d0059540001070b000314a0106102c20350760004001f42d10110080d04940b04101c1440043e09140b0014181c41c02c0180c0b40201502d0b07a01000040280a54820b42d0f5803401c0d0111501540120350300d15001800f21542d850310761502411a481c240704280307902c008101519070401e00302007e500c40510242c4100000f8143d620169120b03045443c1e41070300100d03841c0382000b40b81d5410080084465580d11801001007990030b00716220040d6200c0c11041c00140c0e82070100c84107075694680d08480d010a4030303072788a40f00ca20014120300803060020780301410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 969304604 1250 969303354 969303383
    0x20a03060f050f090c01090e1803070302071805010303090509040c031e1e02060306010c170d0203040308100f1206020408060a022d0306120a020411090102011a091501020a 75
    0x310b640541c0c040d1a0740b00e030290303c036a0b030050256610351515542c14000b60000c0d5041103a14048605d45802c05984100440748844001140703280d60840c031010703001a8021841084802a14100c01006040f00b4500384429819904c0240582c000c9118690154022400040510100140042c00f4552080750560420b0103000345446d002c9030440309484002e00e48071080030411924543c05032807075000d4041d078110b503030f41c00c019921004028406c1d212480001407004c5a403082900500341c200d10300700010b8403070616007001400310782c0c0104035181400c11203906010068001451204461980d25260030703050092400001900465110740d00c148207600a110303800b5416000342800b80d0b013a104250540350b1808007520300c890782040c8403071a400108007143d05414909070fa403841105603401c8130300044050b40030030111403602303503050140c0f4808a1071218a42e03081c0a50b041484000c07590002401c4500d00154003401d025203e1903440c81a490104d0380c603402440042c18071031b0400103007100c400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 969305854 1250 969304604 969304631
    0x1314042307030b10080619230a0c080a020a120b13110c120a08061009080312010e0717061306050307030c150f020a02040f0204232e0804020a0306 64
    0x69055a140c2c2c0c04c800c040001140e100e030005802442140c50031100d1001d1030010302e000004240101d00760441030004150ba400c0e07170791100c0086025800740d000c0019a80401c03003004240c0040580303203e9885004102c0c030940030358000d0300855410980c0f900001d1001100001468402844540382000350800d12000380d070403020b4010302441d13007003403054480c0a03110110300d22240c440c0c00c0340f00004c5214100465101c0c02e20204989811100c1d0424058003a150102c1910b03640045000c5040700c85250014050890604841904080d1505003841c0b030389080021150403060040c03419001d000280d02c04115032a036a000600200b101600780c514064480c103116030f8a90241c005e2a00741d07981100e550380c0d0244640d007600300c111100c0c0d018100b4800385a00300406802c0c001c100095880e000c1c0300108140c0c403c25030500c446180ca40941c0780d100d040d80140004641c100c01d101940c0e81904640c010484200401c02441d1801072920b03008030340d124400076051411941024052601d032000d0821042c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 969307104 1250 969305854 969305873
    0x1406010e130c0c061103040f03230c0a050d080601090b070203070f1701051b0d090302011104060f020715050f0318011b031406010f030c051e0405131404230703 70
    0x5019130018044d0710040308440500e803009a4000307040443d402d054601003841886854012010445001e21110703540112980940008140314000d030090443c11041100800840364002503504001800d458084000703005014540718071048814001403520031035a05000e81c4000c1d21000d80c401150360b454503507180c8509040c0f01001c1e0550318080115894400030680401525100d00f0140c6c87d00c11411310580250040104c100d0a43d0340310318510700c0c0c55440038080c0c4041e05041d5540f0320700490080c0000d02d40303480c603848035810500121030070081030f9000c0d08803061224105403195481d2151030f0740c0204029034803800c21f0075510700070b244c81c11504041c08040e02c002d250303541405911100e00001e000d058056030810301040c000c01807441001d000c0d4005a18004040c2422800c090318203d0f45078011030031401038120a24002000d01c198034189000d6101da0b4407480d81000b00c03401c9110fa040c58848050409014000d460000d182420b40d140100c954032034155065491096681c900745205 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 969308354 1250 969307104 969307127
    0x111005040c09090503090d08041d040809130f05090d2c040b0d05030403080301051305161112030c0c0d111510031a04121d1203041d191406010e130c 65
    0x20f282e480070110704500b04ac10b4941c2d000e6500b00080310314100c00002080031303801c000402b1210480d110414921440940d1085603c66440500604041c0c40d014100600045120643e4070001c0c48104d0044045075042280340c91018080d14009040c040c103c000504c50440c020004000e0310001a021042009180103541210f42c180c81e81164003c2e0007450406503442299076211100e244081e500c242c41c0b044030440d14107940c26090318024104e400190120b580121a600c241c050005000c8c01c04d400204446400000d481c5001c20b6000000130303006d40c5807c07650080c413285181050200780e03c450610b4a0200941d807060181c8503841d074070a0302c0c0100c504100e0f000c0d02c2811200100000031801003a03d8003910400420030118a4070700360801c481941501c11417541c0d448240404030f54007440089218122a4200d4901d00c1c910344030801a0191141800c50710481c0c1c102800320821a08a2103038a40252003400c05030b9103d800000072a03509040c00c00340d0f180c01801c000346001d442d9000f4251589 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 969309604 1250 969308354 969308369
    0x4121e050a0912030c0605040212070303020115050a03050a0813050916030b030102030c0f18090c0408010c050f07030f030915090519080a0c15060303111005040c09090503090d0804 79
    0x9a65070a0b2a80e2070702c9003c40c0580032482034240c41e000203d0581c00264132a200400002210541140052414041e0b410450150f907481c0c041042601c0f00740d203c440141030480d45d491040e811992010307214910201d00828400700413130800b48150200300b03100701400740036086000c503140460141c60440e68103142440468505280d0046034181030080383c0c80f0b118582100c5d45485598074440e0b14035801086188601d0340d0340005d0340c007182c0d225043c960060b141180002d44640c00c014050303003119000008142844010000c55440c45986801c1c0e039452a018103000d18550034000f410b034007600d0240ba008002d0201000c0035800c181142d44100070300d50240d4112041c0800e100c411840d200c8001c43c3c040c2c0349080504c10030032440d105003e0984c285110324042c0e14203880d0320307094005484d015082113011502121203060802000c100ca04020201120103001a0034152200c01305004940198641107440f020344100f4010100100c850100c0045d0a8088500301410b103902607400034001c411 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 969310854 1250 969309604 969309617
    0x501051e09062a09090a0e0607090e04030c0201021501170106090b031b27060f010c020a1e0b190e100210020310150917070e04121e050a 60
    0x3030345a040014080d202c1c03074604581181c4000207102d4601c100c0c00480c0e9440d10103400308881e10940d02c0d20300300c103801840c044001160314003440304183d0238100300030400f0003007052080c0100071031034400340065080b80d05030814004c0802c5a00040342410754081d000d044c003c521100000c1c1d00c80384241700f0940c101c3e039040204001f07074554030340703000b5520400d2820707615138000724924100e0070460903070404003440201001c14485000003002a0014810200c03200402c248040000900344403142580010b002d10301440301007290342c000b0700d01c915a402000d020342101c00f110142030701303072400810244c200c1542e001d44071508122143c1c103401d00305180c0c00000300311865186503400e2040250b0210101074010701803411868a081000b50401002e10340035480c80302001a00e28004199041d0410700c43d0b6980400324203000d0b002100c000010f081e4443c5a000d080204000c0c8640e07103845401581c410a50b80c00d44c2c00204003156008269851824a00c01d002400c3c44883d8020006000584285e140ca0707 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 969312104 1250 969310854 969310861
    0x40e0702101b0c060e0c0907020309011d06071506180906060b090a0932040606240c21090303090504050c120603010608120d1a0105250501051e 63
    0x2482444070030500000f2a812107680800100c058201100c0100c1840031184545506000030b00050000c0e182c000158000281d0510300f56404800844010032242009055001400200f55a88a407000107041c25200140145c1c5050854002130028200b0900603400035600781544402001600f00c00c942061403e5000904101c0c150181c820b00386004000d4045c1c689451340544c09000210b401c0403980c08061900d00300c0a900c6141e0aa0440c20b0302055516032802e858200101e445503000440d00c05407041400c0034102107440c0c003140114040ca00f90303030300321858030707141011031032821040e40510122503403100040c1c0d1203007034041161302aa0f1105209035540c420f01040341c01c11b441d903800d0b232a41040125084504070318210303003010700500002412030b94be07e0154203244414004184030040068100800c0b0718031f0250030314010070311042c2c1d100410305a0020301240b0501c5a5500740c1c0c40b0604021080e0150503502007140740d0000020300080c43d1509480ba19040800805880c4403203401c0030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 969313354 1250 969312104 969312131
    0x5040f020c1506031f0b1032090d0206070204020d0b091f05010c02060706050907051005040b160222020d0e0c0a06050f0408030c0a120c03051e040e070210 68
    0x10b06010320000390140010360039814010900c401d10307001708809a5140c1c2d091209548030400c0b0007541c0400360313a0350f40381c0040c00407000003600030494641c09044c40392060480b40c1c6001104403807444400716500045619070b840030500302d009003034010b5030040c40072914559412141c1c000d031002c00401c40c0c280704035549100100d8101380141c1002c622020fa5000103120f03550251706594456800140100d00745000c0382c1e03034001616001c8800c0401307504201c101308000d00f0298107501038041c09090181c201410140801114024901e102d9083c5da4401c3c0000305640b618034070b120a080c21800912901290300c0e506c840a9071000d100140c4c40391400070038100e08000800d400d250001c0c000c10030100075140c004102c0c1d054110340c03004820b0711810072002440382002c00042c03000d00b081c00c000d004035280c5030800ba08082d0200384080141300784480e01724000380c0d0040880342c0000004079440541c10b5030214001482c042e640001182c5419903051050150300041d050042c03461500e020704c03801d22070441 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 969314604 1250 969313354 969313393
    0x60306080601213018180f06030f051b040b030307030e011407030e030f0d050409020a020a0222052206021b120d0c020601061b0c05040f020c 62
    0x241404080344001c0000c0d41c109408941520600540810200c0c00c04e888800214401061004074410711516a843d4040c0e004050b0903a42042030341d0310603481e1310340500040301102500000354103560320008000c00100c02e0340a80095074000d0440c52101c071803481c2a075130700c1300c001080c0d03501c400c46c021440507103280c03034046d001d84020080c01460804500d640e041e50b04000075500c9505200b002c0750748240c0d0310704c81009402c1c8640240d49095050f504d4100349400c040d80c00035415095040b0030006050550404103c034112004840c0c01030307685103083e90490811841010007940921451006400d103190a80c81040e0700480741d40c20000c517260901a40300756602c1078070a45141c000c4003040400b040c076581c003801c011900d0040c464034401c1c841c00042d040944205494501d55408690300e00c103508244036509030090325000506040d41007480c007501002100031505181c01e020038442c800c02c460744595600610b405002030208182c00074101c4041e4100301c1106040b0f100b40100c0d40388494541d42e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 969315854 1250 969314604 969314609
    0x2f030718030f021003090834080a08071106010e0105010f09030506310501050405061e04230d021b010306030c0b0f04151e02010b0f01051c0e0304060306080601 70
    0x82146900002d54203200d007550080400005042ea0382d01aa0f0214141c0d10050004052114008010f0070b42140008610081d4582d8030000c0c40764441600001800901150720703144450030444880d40d5001d03030446003240440341d1600c2602a034000001e98043c11680241070314400d07268100e401c8460f50040303a10101c184000780150748840c0110f40f4000c1001c140c005410381030910400c40107001408803502c0501820201c6e05695940104418400140034850b0040851030000350450360110600e4203c074005400038100000c00030154514030050000c035440326503000d0940c0c484404000d00a911100e01c0101609010000d025541c034942c800c3c40ba020a80780c0c890242c0322400c2c200305103003009170050b0904800003c0d041101040c1d03020540c0a00410b4201903072092900500040c0d4484d4101e004145401560704102d0310300d005948240c05821094804c0c64841c0e00c401802c0f42038001c6504041e140300c640c0780f03001c014007003203800440140140c80c980c3d05e080c80f070b81e580ca19000c2c7c0d81d807070f092 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 969317104 1250 969315854 969315863
    0x402040914031206040c0806010c061a060c0a02030105010b070f060c0507060e0601050108160504210203070801150b040e060d0203071505030f0714041a09100e030609030c0a03032f03071803 83
    0xe0285000140060744190f2140c1021901c0741c903608000330209025920403d031385581548100442d40840c50240120b07030140044101c200e05080490380d408030308415a41c1c0041059454400c42d0409612420590340b419401140c144803910805074001c0d103e034802c2c080c890014500000207603c54492031140c202e00350b40c07541c0d2545442e1a003680b0102c01c0c65100761115080a0f003081d00300140e5410410315000d0320743c42c0e000250480c2040171002640800f0703446003403403183c01d1008024075550b2055403a0300000c1980e00c00c0d401d003001e10010f42406030580044c01c00d8000c015840782516880710281d80f01315814500d0342c5041e112200250355604000280c403e8850081009021364524103842c0b2315600c1880904600300081c20300040c80d14070980b125480081d442144c05800d0313240820209412042540265207081c185c040c0050b110050700c1000b5045c180c41e503440d203100d1230107075080301c801c0e05190030000c410741c44c0818842802c0d4002d5a030040042e20000e00c1280c1d0228856241041380d900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 969318354 1250 969317104 969317117
    0x2091806011409060a08060d050f0607030f090c150315081e010204030224071a1e010e1b09131e0b010807080421120e01140402040914031206040c080601 67
    0x105e490031102494010f0655801c00c10b02044078000807010070102441028400c090a424a44054010101c0300380c0180c4105082c100840200400d00310510107060302d111b209288540e1805990a030003815950744c0c46c0b00406100d11000031640d002140300c0200038081c08a001202102c1c0887ca8283c0c0540e00020790711140020300c0c40c000298241c0303100b6110040c110b009082840395210711610000b0184001d444001a500300b0424807008507614030f08000203901a4a95418000001951803000384042c207412802d0b24410440c900000507038a89210040210200c218042081400f40103200c90400702c40901c42c1008040f15141d01480780190300c1a5680401076030f600390b0449101201400507240c1601400c101681301029201c0c48030302c0300560301c8480c060041284200e080b00d02008102c0026450107080161f0b60424020300c54210350100c801042e034034100c1c144000200300a4503160300ca84000076500703c0b951311f40d010803403007194115030800c21402c5100c0d003928031100450380d036030002d0709 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 969319604 1250 969318354 969318367
    0x411090303030a1d0607030b0907110618030702061c050c2b0603062d0e0703080a030b030706081905040237060203030a0b01020c10080a0209180601140906 68
    0x461340a80d18a02883c0100e41c6040b0426098a0a002c400c0d220480040d45a5902040c03070f0412902c003903084401303440c14440740c103010300a0316101c2c43c0c05000c0505408100340104c0c15030f001041920000c1d500200744070703565180d03041c0c0ca24030302d1500d501d200c03440d600301030000d801d8078a0003066404244075015030040800d218860141224000d044442c074040d80c8910100108045105101126107020500b0b10401844911030b13041e00c071170a200c88640c41c1070042200c0380c0e11010411400301d032390201d1a103441e6003000000742d001d417880140d016010310640b01d0010340541e010135980d01500c12052600408801200303400103450f4100d801a4120500350b01a9100e04d071861401109a0072016014550808414bc0d03a480d502241e4810030060f8008000e100e50b0482a20840d202100240010320004e89a20302103010140a800440203001c10b9100046110b092501201c0e1010700080041c0400008103203000004003080e10030a0004550410425220600300100d85503600e000304607504215 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 969320854 1250 969319604 969319621
    0x9030f030a0b01030207080d1d0106051e460614090d08031303080a0b09040f1b030f050105060a030c120821070f08011d09010b1e041109030303 63
    0x282a20b1181007542c20041d81020848082c09403d0591111502242d00010490581580721109200d52416454020100401d0740c0d0f0490f0400b20300001080141881d83c2800003665417260328814030380d01b035112100420102c0c000041504402d9410038900a154030460807a2251013040c000c00307001c2070011441c5001c0d1120703000030700007d1000074051a05d0190b40c1e80c0f01b82640e04141c552100c46178610000504141d001400c1e154000c6403c0d0b4200010305c0e040700015624003011304040c000711a0740c801c0c14140099441c04048507900521a844195500d1a0421b0070b070200c904c0a80c1c1740d51070000810114901001d5a40403241c0010b140354146080440480006c400d1110845007003400304010240b001e00000c441d014040c01454041080c500030340050140c400c12000001000082d9005010505800d00013481c5640c0950b11201c9581c0c9524040f0b0051aa8558051340700c1c0440303001c61800132050100005040d0203036014010660301d00c200c156107009408074503a254206200203001d84 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 969322104 1250 969320854 969320861
    0x60207061103070c0609050a0e091002130914060a140a05040c020a1b091b0f0e181f0807050303161704120506070e13090c270509030f030a 61
    0x4001e0025a45801d2030f40e580d1803010f00c1541d01c003801081d11102d04001920384124114010002d00300b41d20707042d01d0b1000f00ca1307884043c442036540e520303940810640c0c0190303060b1040c1d0000c0d203510f900400c000b2004240c000802c55003140c3c4580300d401c182ca00030880c009650100300400c0d5001d001202c940f400e140802001d8001c400400b021445900c4605002c030300e4001d0740f0030000310805843c014840c2040c8200050780d00b04420f486c000c40110034900d620079400758060180030024900701011801e440000794a17264240e03291440340d0520002e004202141c140c00045010307203020b40c110180e0307503815602d0721140c240c420b581d030540060040800c8940d0340009d400e400c920910b1030740510212544440c0d03440d001030b00b0038803892305001ca07a402001703c1001590341042042c02c0c10340881010b40005500c0c0c5150420348400143c641c0b140c9810000580c0c6040050958039081c00441c11003103042020310500300381000c0d003040c2011301207040c006012044640d9489044005840c6503659103604014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 969323354 1250 969322104 969322127
    0x120c051603120e150f040801110a0206040803100f26340801051317040e060d02030a0213020d063c0302040c0e180c04150e03010207051f050106020706 66
    0x1200ca0b10001c85820044c0041c9060400b280240b03032a24203140b182800c50300750300031510824500300b2400d0300807a00005e266501551120410f580d9907a03207051803400da043e56202080307207006410b004c240d030021203000051404c2108190807140c5801e2801c5651030940b042e28002040208088182c1c800c5032034902650500c020340e0b00b40025039070f110003900b196403caa503e403d004225452401308568202020384415851840e170b800e20b82494451488980060421803143d60003c2d05282151400c0c019025851b0300141400709400c004002c1101075404040800c841e145090004598106000106821440d40b003c1494401200d032103116848500e43c0380005091044040c0080140d170f8900880380d06503038030391300c41600e412040c0c1444560140c100c40701d121000c07002d04210002e0203410079142211a087d94059810340b214000340d86e404450020035402d54000550001031103800694803003400140c0c010408011001c6030390704110b62081c0988001604a41c0b4104000ca1141c180200c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 969324604 1250 969323354 969323359
    0x6080c0a05040e0f07110c010e10021f060519140108061f031a010f0e130f0501080c091b040e070e120706021002070c0306051003120c051603120e 64
    0x9072507103c80c00ea403d001801c03510748880c42204010803210640c0301c0c40412040e120100103148848072000003801c07802c5c4000c0440d01070030029049030803480c4200a01082151007203804690a1036403800d01e03001c0c0c00c16008040c01451903802c000c04111054052508a40c2d050340541100444040110380c031000144c80254044012403922414403040000741176948080c0d28001110201144240344c41d00714002c140d414483e4403140307501200c1d002081c9d001222403c5419020340f1202c0c2c12110000c0130514103410340341d460080007142c4858001182100118111983d0b00140d44203250014030443d2028010b0790100140f004000c1c0300d00421a054100e80142017030040452003401090420046d0758511046034442d0300d00300b151b180c043c0092000ac0c06810340651825115403a00200c1d054648001005a03607a03100040b01407a905101070080d540c4413030140480c82d880e500080c8032600d00d6605485500803401000e2400b12240422011254480d0f4080b210011070704090b15007201c4010800e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 969325854 1250 969324604 969324607
    0x319170706111c0b0f0918210904050609010b0f030c09090c0904050c090d11030102040b1b01050a021306030c0314100f1d240d0c1e06080c0a05 63
    0x24421030440003501010072448120a40020046024802c1e19507650085001d945d400c200c0310411340300d10b400c5035840003240426080081404209601d801d00c400b01c40000000500b40d011944035000340140514030084800384010385540082001420080c443c1d07442185081009104c0845c1d800003942c0e00500b201ea0482c1040c401d200841d01c49007013259900b80e0100005102600d910b030602c10302c0e401002603810729080c4881d11020890845014be00580304071400341d9002c9040c0da00350111405040c2250b0000c3d01d407005c80503654080030b000000d4080550900c00000d8a204ca50300c00c0e2035004480e40b039034032101031801c0010f40042101110880070503449084081844500070760107401125000d061030456461300a001980305140c0d002560a01005103402c084191160201c54100d00c494150f030000700e41d0f00307261460701d0300d211548642000203400c0c20001c0c00b003e0204001141d1120020080b20006040c0180c2d01502c07902454000c1703009032020501c6560f030000070700010f41030b07401c00a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 969327104 1250 969325854 969325871
    0x110f06040f060f09050c1309020d0c061d060901031e0615170408120c12010905060f06211302031509011503030c032d020c0319170706 59
    0x1814410115020748551000780e49950801400f88a0104038040c1d005041008000d16910240c0740c6d004000860701c80d180d02003c89959100507440610040e0f8003c00c580d840d039580d894596a01034091061601284041030310740ba0025400b200d80c2c28403e401440140b400a0034001900103015504920b400003d003451340c040d0895041c480c4001609250302c0b400449051b03080010070302c1c0d140c0b800300b0140d035100c4024880018200e0054881042c3c00d2070030b400a03070750340c80d406100034003901c0040d901c1800d00794000a00941c03960310650140100ba20740100303084070172080c080d291040c10144011071070801401004803a00c00f6400c0d03040241c014400300005000d400003032802c4529510030145104810902500f040c09104070249107a90300000f00106141d61405044d00740b200002174207010281c156080c08107046128080c41312480005061444004040255251094113200e4024070030035503ca124140601c031408002940130040c100104011684813106400007601290200d4984000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 969328354 1250 969327104 969327133
    0x3060f060b0a021f02160b0414030a030b032806050c091806190b070f0317253b12030703080105041a06070c0302190f1703030103020111 60
    0xa02180300c16038001d04d00c00540304614000320350219542240c051040182c40e060601d41c01140c0500d541040e0395800c0f69841e801c010303071001d00010306400280400103010118540540c801d01c3c40c40001e0742201c1c02c03000039010320849404000c00000c640310903a0880000a0160f802c01a4001c01c11204541810700b5140400e1040c80c070400382e80341d2141032108020701414040103844000034006255002c113840c2000b1581c4c0d510844001406148007100a0700905018507400c42d02c907003480a00000a2900d19480b401501484008403010035640008040007803043c031007200180144651034030100071811020002109001d440c641c111181c001c807941543d135100e14140d0103401d15001d10366400c646d140040c01107105070006845581b80081412002070980d900035040702094851654500160034a90101d1041d41e100a500441c0c1c99203a503640c8942d02810300031224500c08600f04980c640350224403080e65003914034001d0748140b00400c09984110710084880b00358000f602c620320b151090 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 969329604 1250 969328354 969328357
    0x311060307030626100603030504120f170c010b03122b110301150f0f05070639020a0f0f080c07120309090209090105042d0e01141003060f060b 63
    0x44600c50040c42c0800c44c2116003e101307a02d910080d0183c20040203003580da015002e80228022054a401141c104604011441d40f0740528150843d580d00b00122600300000c00d940c0c02240701144039401c1c030a002400c1c4c00c00140c505081c000c61220381d811f140c444c15456110380c14071300300480d08a01d00d8080003900440e921032104030090181031942e8030f604140c80c01d00110b14401e021010400d00039079a02c66503030f104210340111130b0340e0b1515503614002810000040d081000d07150743c0403040c21032024010714080c00d90078842548800502c1c0c0e1030402100a076202e48141031302511000008004200040c4562800c0e115203200b40d0701e05080007042005145400d010780c002d10002c8617401d000009154200034002d0041401c0c86056290030b5203a03011807141e170300c18828a80995183c0c0200f9121503801154004681c0c1305182046041e40d02da455030b0041d280b00070f1245402e5181c0000c40f950500300b401d0151241001a1070294481e01d50340d40c40d0001d1aa00242c0a0480d81d03501c0e02040c03441e003500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 969330854 1250 969329604 969329639
    0x905060702010e0d0203040312050c010f0c14070803040803041b0602160f0602031209100207061a0406060804140a1e0b180a080906090a030c090608010603110603070306 74
    0x10024405840e00040181c00c5400c0300b21540b507075521500d580010194004211001d8951110020155149115040c0d03040d005040c038850855007000c0c100d4021201da9440404949103d55910f0b4454005e4540e4522522440101410701a4200b0000d00400c40c10001035400c00e1286200148440740706502c050200025005840142c000d440250a490341e00c00702d200241c071642d024000700518050019550348600303140c0d038808550042c0000d0040005101444003030104040541d41d4020510b001c100504401e07440d2000c0401503117a442a0f41072521920040c1c850350b8075844403035112515594184580c0340b144000a1148046080004035042c440345100541c2001c801c040c4040741c9490002c0d104001e04250110174000750019000fa00099111b0900e5008100ea0340e0b202d080ae008a071803403144040054014120280000400c0b290380e810200325141c1140810805071190401401e84199100260a1ba0700c400811000707480c0a50086030480e020341400102c25594101d4585005540c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 969332104 1250 969330854 969330863
    0x30605090717030408060106020115090b0d08040803130b040e0f0408040302032a0d02030c010e0d0819020d020a0201050f0c0c040e030307090f0317031e010308091f0e12010204030609 80
    0x410100005e4004205090240900780000e001000c0030f1204401c038052144100c00005440303300032015902c8070140480419008549282c1d40e644450400369a40e000307030000c00344c1c007040030400030303c005022065070244c900102442605841d51001400c20440260054600b20020000040140da04000d118082e03c0103c5400e8102503441015084c0b584007201c0260103145a10326000059801103443c1040c0071090a00e00c0d10b8018035404039250444824005202140c002036002e00840150020204450300341d086030741001000c10308036128011100020301190040c0421031810f040d40018105c0d4240c1401166a414081b00c001002e40e4810b1600d401a50800020b0007c41e690200071030300034200d8141e90340425859941c8080140041648520b450140403000c680d41c00807100c020000044c6014101c80256120300f4540c0e0540c1c048107030700c0e1180c40840d00d03124001101c15940b8034102084d89651640c613a1250034060500340074221018555130070000480052200d1040c00d045038000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 969333354 1250 969332104 969332107
    0x711070501590a0e1003080a0e120c091602150417030f0105150405010504050603041b0f0501091a030a090302071a0706050603061b0904060b0408060412110703060509071703 76
    0x54007070010415850f0010041c0001c00010005c2c4001e16058001c122030340000010759454000804a5030340c40c4002603079a1161230f0100c4194000700000701c04059201c00c641800305500c551080320b400c41e00f41c002070400768000d04a100b0140804010240e84035004a49880710f070002c800e1100c85a40c0120f07226546a0312000040c0800c1c10706c1c503010010320142c02940c0b0714081c2000d001034800d00032031045034854100080050100005103104d04403c07a10041c40d01c040070344030103030300e80c03d00a00d0003114000f440c0420009148070b000c50b04685910b5041039114a1034899178180b8000d40060001a019803050503c001940041820302062001070900440d46404103031610070242c0d040504018400e034081800d0201603194100b201c0010103510b825540ea4104000200300a0801944101868040481c1c005608540459694440c0340b0440c94009514503200007911942801c0322030400e80c0d8040300c1c05100080d00d691060350004800d13004c45003020755840e5080f00050f140c000e140c060380c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 969334604 1250 969333354 969333527
    0x20d030f17041203060f23041803081f120807020d051605041406010e0d0f061d0f0d090b0c01020f070311070f12020d030c06050711070501 61
    0x31315205010103090030125090003140340c00714404a01c04220301c048410048001501d840750f81e5039014038040701040070b544542c00c10508014004031412151304948001c020344d42c0704d000c0004210101a20041602c4025852040e103c0c40a6500710100c12600604c5650400c00840e00030440e000e125811391601c01c1500d42482d0910080e05ca00e031840c161007a0001051017181da070000003051a009042e104414207440c02c0c104200a40c55400c400340425103086400707c0c200d0400c841512602a200e0b0403904c85011403001555034802900c80d00300000c1100c08281314002280e40104243c0c1503900001d8246401100901481c0d0310440702200840c458400c1001c580c2414440c1c41c004007610182688070724500001e01c00d0207104010024422014160000201b50003450140d20164215004000a1500e14400340407001c0c829090305a5106034940010039600c035050114880f441d1600c0c0d0908030550018500c0803581c0142c0f8150701240ca04000c1c01004003e2050010202c143c00760300100d0326 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 969335854 1250 969334604 969334607
    0x80316020f37030c050103090305040b0f03040b0618040204020c07031709040615080a02070f1a102108090d15020301030b010e010510080705091327020d030f170412 72
    0x40825103200440c0745502c2c0400104040c008100c085030428203001c100000b89141c102c4041c460340d0841080400c0100d4004100d0300e070703880038500c00c0f442440c40009988940c070030001c0b00141e4448800340005141c3c001401424540c0190281a4a07042181c50040d147e80da40c1040642d085841661204040b070b90034030f01d00d800d008950007480d81c00d0a442c03c076000c221700101201130040610003159000103002080080f01c29041c0d040e0340d040f05e0b4401c4080d100129040d100d42c02500c451a401c0c400c1000815140300d1145c280148464410070000f0f02d031010340c2d0307000040d041808031a030320000d078079000341c0030603020264035016417074801c4010390303035811841c0405070750406800c660500702c02c9100600032170b03d5001542c2c00d4001d25040c48034890b500c450040b115440381c0b80b442c0d0303040b0040040d4040041042d0300500000d19140170100c400884c005424014600c8010019600580440c60b01022a000b100d15032800305e0680b5009144003011480008030220513030f07040380d0000ca140c1001c000366 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 969337104 1250 969335854 969335929
    0x103200a0c0b0f04030804030804031701060503091e0d1107030b160801122a0f0602210703091206020405090f090d14030a0b06040f080c1801080316020f 67
    0x14261500583e418101a00c00808001d0300400003000d0002c100c0101e41458080d88038940d004a1084441820b0368595030000d0a0340c1081d40c96802c01d109240201095820034000d0b1100710400000510442a41000484149944032441c41c207600510070040040740c01c40c0c551610850902c04200007038803284000a2094005030312030300342e001c003e105a00014480f50425901d001c401240c03017603049400107024044070340e150b1002003a804002400a161900824609070070300d0021401d04041078860719040c601e2080e81c000030700040c118102401311900c0e0b102d680c0f403841c0c004d504c01030800e030300d0b100403844c03000040d40c986208030b004a041180040040040000000c1c51385404040c0d0454419440400d0001070050070021b91a0f1060340c0c81340e00d640c400d4a00510001c080582c10954400035103403a0349002d034190317004000c254008004061a04101412175082000661500e0b0f0003900703031039900c0031742c1408030fa22810741c200c1d203007032640c2d07002008040100440c2241c880c54004e42c10802207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 969338354 1250 969337104 969337111
    0x901032304021e010f08040302010e0a0b190b100c031112091c051b19032907090b0708040b030406050f130302060133080601080a1a0103200a0c0b 64
    0x11060052490005660300201789a034910311810103e5135900c07203240903405010110112091403207500c241c0070610010940c224001c903e00e204480d082048411704030161206c04003c02d802000c030380110310f0580e100302c7c5421072150080c03402c84e00c00c0c1ea2000101c2e003054403290840e400020086105a400d1034131104103c480c1070781c010030042203e401e075a65030300e841084030108a00c0810141c03170001030701d0300302c41c89036003034100310300190f07203e0b103130b1902400840e819648100c0313a207104039284c0c01d9032203141c814500503240780d00d403944000c4ca0900007107003da1101c0b81c12181d241080c80000749503541d4001440c040e40c400d26010407246400301c000003038000002c0c020b910020007c01c1a41c0866004560f05c0c5c1991003a0051000040c24840600f21205804402d003c8040e8110280350859500c034941c3e40c000c6074241c4e07440c82e050302c44d01180c03403d030303140b10450034030501c4006c1354501150300a80c03200e01404450310824080c028010346008842c0c100d14090400325080c5c1c51410304000480240c0f560 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 969339604 1250 969338354 969338389
    0xc071a0c041e0e07030905100c020102071a01030f0b190f0b03010509012304020a030f030203041d0c0409050601020f1903080a090503040e040f0f03090e16050a0302090103230402 78
    0x911890000041150700d4050704042c181692a04410207007c2d0500c038948501d12210006d01c41e4041044009000350710040c025075182442d82c0344400e03012409000da078101d035044202c0807014222a202c03071100c0c80e80030340340b842018a055141481d084486c00390107442944104006070007500c140900d800d45030000d14014059252038101c0e00850008044d09684030034603010400c4659461011030410240c54002415074591803000d40100b507800030060040e00c00102d00081407503074400500c2d006240075121702d9803c10091000b80f00c84840740c0e1180313600400520481d8403400020903c10308001500040a4000000480100c10b00d5040320f0256048005888200078200300f03522180d03101e01030b03405004500a03001c0081800d029041c0c00c16050f1036001b5802c0c840d43c0c61249409440c608062290450f4213408500207204c0b241c044e115640840c000340c0f5050700d030420b0020120020740c00f01003030303a060603900c030610413204802c4a4010400c0c03d20a03080780090900b801000303640840301b007200d103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 969340854 1250 969339604 969339659
    0x603120f09051e03070f0f03020a140609010309031e030f18020d082b02180102010506090105041d06090c0a0b040b09040c03020910020a110a030203060c071a0c04 71
    0x10854944101d80c0e0706500d01c030f103080d1403042000741c002810020146d0103e200f2210604000c0740d50180c0c0b002400441c0e100316502c500301e9640300300800d00c2200158030ba591100040c05800c11550203038001844040c03003880d003400307024200480f40b81456003001204000a0307481c0218215801c4a200d00859072031050122101d5140d00d5002840d001860351008150b9080880c4526100380265240003108101450f0143d412822a942c01e00035001001402021501e4440044103540180f1031240220f10181c1100896070801d824013014001020000d00c0c0042101040da2402c00140111400b9150840142416010300070400c401c2c0007484e000000c004070204001c004201070305048848920066402042440d44420141c00a000d0120482c0c0c1201500c106a04403550100d60601c040b0302c07501009a18100b40414440c03502d6082c00300a416900c02004542c4a045100290428601c81d148a80d0100c0c041100c4512603641525042d8000030081003d1080c40903400c204009904881d1040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 969342104 1250 969340854 969340859
    0x515030a120207081c0207060c0201081501051b060a0e0c090f070e06040e04050111031603050c13120510020f0412020a170c010305180c06030a0f0603120f09 69
    0x25110154400010407110340411078010312070080c0041c2000f8071042c000c4c3c0c0d50251030b0780024203040301402001e00060282e10800b262580c0034041400304640c040e0369580d895643c2000705183c041d09101c059040c4032040c0031960144000b215000d0000304810040c3c5018105910040143e4000c1300a2040030740040d010181982c84080086611614a0354008204d4032504c90a8840240c1e20350345a4104400190107d00c070052000c0c2e01e400341c2d2044000300280d4049290300f410501003540c1c00202800c58a03c0480c1a030b01c030350415904500c807038014502e0060081d43c203102030a41d40d84203000b01c000412180051003418444c580c182c0000400c00d525241441e1590340140c4034501495200820381c1152030255101c1801505c06800742000301c202d0f01c00c41d500c05581d264106c51303030030380001c0c28030001500c1e010008082146c1d4400d031a000f48628811101004a2074200426440695070740f8800142c804035907004e40001036024114049601d82c29490051001800080c51401d102c0300c1c1c0303c01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 969343354 1250 969342104 969342109
    0x180e01031109340e09090d05070336120f0605130f0302010605030c01140901052d19020313060f0507380f040b040f06090b04060515 58
    0x16a4084008490590640e601c07444580103421041003242070002400f0311011440f22005180c0380400c589456011064039403508214286008503800d0403180c0244000d030107118000e002411403644682031089801f2202e0440f00410140481082294084001103a0203004240074002c0a001301c00c401e810b100001380c41d0008044808080246143d44e9080000d04202d01401004d500350340c8000d41d400005c0303103410700174060003031760091503c1790280d241000b59a60081c1c070300c195800c18102d038188c00c1c0307003900005483d1500152040300c1c1d0400382c40c8540180d803c1591181c000002440e0b03803151130301042a81140201c51181c2d540095610800140d032502c0c9000b411002141d000780b5054002c01c1c50403800f11114040c00c10020407a186814050b4030382c5410365141405c0b6500c809020707104250f0b10181945d03040090b2401c2965004020100d00455081800e08c2d0344540078140c00c2644102135540c04048401400090341d010418409100c1040a980143c3da00441c07046280041c02941400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 969344604 1250 969343354 969343373
    0xa1103091b060a0509090604020d0e06040308060f130e031e0301030b0f0603030315030f160519031a040615060e04050912160609020d05030d2d090c090606180e0103 72
    0x2041d100c0c0521b20002403542c1c1c0d5540484080740808001441000c0d40c01c41c82c542d40b2841a2002c41c04201c80c4000220107003040f031200401e411001381540c105114199040004083c5014051f41c140401c0150f40c0c10b078004146140c0110751032845059481d0b1450415a2800001500003110b41e039040d0f044c00400e5400000741ca4112108003520750751800820b00003894a0469000102d09000d5440d45004040d0039000c22011190244ca00412424048035021701c850031501000708001002c540d0001412242c00000798042c0c07282d880000c0c00d00c211511010201015442540020070301490902541020f000380f070f412504000080403000f00a02004905000f40450030800000e48070408090040b6504004804c0d07030081c0034040e51009500b040c9440368040350400e00d540d07040030050b110003201e1a1000e1140118084900300b0102c1d000c03014000b0708403d81058428800401000ca1007001c00c2c070958000f002c00d42c9412904166800c0340741e80c0e5180d15800070411100190040020580010303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 969345854 1250 969344604 969344617
    0x1404050c0f0c101b021207020d170c071403301c0203012d0e040201111c05091003140604111201030b071205040f0204050a1103091b060a05 61
    0x411894070348000c42c4896140509076464010140e00b440300781031400040101c250110062035099540d100071414002802d8499070200a400980b000410b90100d04030105043c00b851004142d5854281d0300d510b03a524240e0103030800c4401c0e014080303400e40203103810000c42e50600c00c40c0c1d5801101074407080c034407a0001d50113100c144041400190500c8a182e04074100e20000340d01e01030840d12540c5038868154088444500d880418001c41001040859001d40f070740d007102c1c0e42c200349209a41d0381d41d00444440001e000c2c1c1006500c5007a91802c501078101c003618910002c250b0312184c07074080c804100a901440310035060203043c90a049400a0344200c0e8882c2e90000742628040f40c0003000302071540072403041360090462000124004010081c1d2650f22602a00c501d130340d030740d003030f140110381c86800c41c2d0090718002d1012040c135030325200500706900680d900c128150300010f4040c80900009120b03a00072104075100742c1060380346142508c002c1945e00d01c41007094403d035051081c80000a030080c42a00d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 969347104 1250 969345854 969345877
    0x2150c030a090f08070219030510021c091101081f0915030b010602010f110301050102061902160c0503010606020304180b0301060506161104020c10150803070302071404050c 76
    0x1841010590b001110707000d0740b103803150b4000c1c1e49034101842c1a810009049100b0000074400301c04044001020f4016a504000504804640103a00200a6004445030640b44051203c40015050244207403907066014000f02200c640110000600300721001789861108483d00c00340b015651003200440d401e07036201000018800ba0b19140d00120000c15920040903144014001300b441070381908010000f02d2046001e0000c0f403690084413202c2c1c0006d00400740141c0c0682c00207070001d0010010f0f1410380125490061400d010f2840c0309541d8007078920140c4080070950000c12031707030409102d0440201071a10207541094100905030601042d030300b8400f62043d840d5011940140da082d44040700415005041c0e6990f0190401c0a68550700c1d00710081e1105541507080620a0405008544007007503035070041c0c03501c0d07802c10030041c00800311400c001840440d42d04012401000400042140c0342c0a5001071510501c0c00c920100c80c10b5080c0c0ba0103000780c1c100320500c1800880d0005170f0701e0101d1031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 969348354 1250 969347104 969347107
    0x7060506030309060c1e01060608040828020102040617090a0312020f12160f0e04090c172505060901120b13020c0d02010513020d020d0b090c0f0102150c 67
    0xc010000740355000d0074404540c01207002400c0f0018140010f400c0750308081000c0c0b40000c00fa61112075a080315118810400854902e00001d40040d003404010310b812075009020540f00881487d11602c40010a040c030300c0541e50001303007405095040094400c01c1f01c0007030250341041c03410307140d0316403203921704500203061000807481c1c1c80741d00c001501a14081201c000f00e40f9101e061030941104801026501d03640b00701d0362410400302d86071007440a6a010308c2075449811090410006120040014080c25111f2459186002c079400c081000b03402d062500d144000c1018406084411100750140541b400701819041c00030032668684034141d901801d0b003401e00f000303044c8404500502418a0740ca0b040c4d845000352824000c4d001c440d6000c0d1840075051400c40324030241031b4100341d00b20342c000c2d5001405910b01000c1000185041350b4081c100c28030285c2321341d0300e4001c1541d070700f01081019079040e050340e00802c900039010309140803200307040c1e40309100800356040e0000304103c0380d0f10050603c0c03412420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 969349604 1250 969348354 969348361
    0x903030f13151529210a050103020109090c080f060d050601030c050f061c0213080a030f0305280b1c0b010305100203040b0604050604060807030c03060c0207030c3006020c0c06030c070605 82
    0x280e001d85c1000c6045080b20740c00313071520221041c01098240401c03400315007400d4021514041034401c9540220454441404c1d0751652050007405540c010701c03107030340601113596510000d6000c1c00382c035000394452450800f016090004000304507111840740c030301402040c00264440d03003201e01d45145146c8001001070341c80300c40f00c419801c0c444480d0040701180c030810440c541050381c03101603101d0303040f01540e0800954032140d262003818514100c000910f01c035072402803840700c0c155902c00700e4448802803400c9041440000c8100d407900f401d107400e0314208607810040080c00024070601c140c01103105000c5186140030356032182c14410140c500da00540d5203200040541d1180d510a00c0502100c400300c0e04002d07540c2c40c00800c10051070000711250360400c0301c015840d900000744601a00d40c445c01d50b101080c104075003202c00341c09013032240108150304201d800d015500c400c0f008141c42d00035a000f503a41d01c071050825240200d4440d0240c02080c080040041d0041c40303030181c5000720b0340001c01061944 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 969350854 1250 969349604 969349627
    0x20a020d170d050906041202030c1f020712051e09060708160618140105060a0b0a0905270f0f0105040b030f120a0212030903030f13151529 61
    0x22500742018030b92800e010b2144000f00003035040e100360302c40c8600340c004103090319049880303010344807045002e40d01c104e0368006100b0b00c0c51020492400c3c040d40041c1042c2440e101e68400040240304540800c800040c420740070000924010071482551030428600450200465811700c40d46101a103e86000704402d0307150500c51804505842c1c11050078005500702007800100c4a40500c82103642d0350046080105804042c00f409204200c02400a80e80c540390070841403481e4000b44021080001042000c50150b480815002da4030000618900da0241e002c0410300c804000602603504100600d0100101d100e614040d0a065840698010a00e61041c00c0440e2070a10420813152040c003c042d01c2c2d4002400800c007506004c00782e542201d81000c1c800342d41d06090703c416200c6149541040000072000c0001203041c0750031001030020710184019a48074041c001464181c05000d00d52203040300d02e8142548071101024040110952100d4403050b04102d840d140414201c0705100300c08507005a0380e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 969352104 1250 969350854 969350857
    0x17030301140f040c02100b0f0306010303260c04062006061009030c030b063c0f03031c050a0c0c0209040503040506030c0301091d0a0f05100c050904050106020a020d17 73
    0x40702e000e00107010580e840070000e9180e00c1c0c0315140d0320700289845091104c1c1c0c50646c403c0e5104010160180c0050f9086807405c40e06030100100703405941c0041c000b510484c42c0410001d40c45416003c0c0e40549550501000401d08101861115005600c0c8600d0780301c01400886c800d40c2007071040718060041c03404400141c07010000d41d44090a09030007840c0010078000c03060b01e003a1040e201140c187d0392400519200807221110000c600341d00c0020620507080c0315000b40844160058010101032040340c0040019155910803002d54088000b41138902c090220540a0a50040c41c07056003401708181c000d80051100b1311031100640315400c402c0c0400c2c2809018012039001d000e004d880310750350345040303040c090040c1d0080c4202c4001e203281c1f0540c510700c102c8000300a4903802451014084440301500d85c03480050b8038800a0300d10f40641c4d490441100e50380e120f60301c0d100002c0c1c0c8401c2c1e1030707400b80d00411046410503070103a025074001d21012001607545450381d59491380d0100101c02c1d81082441c0c1c80d0713080e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 969353354 1250 969352104 969352129
    0x91a040507090f0204050a0806010f030807050c0a06030b0108010503060c0a030f2a110703030c080304030926011b08010e090a1a0604202703010c181703030114 70
    0xb01490150400003140454000f8801d07282c00f62001d545a650b5002e0b804d694400921400100380300340c000c1400000d40960040944c40d010f0f40c11140500c20b10070010f80b590813154041400f29540321b44e92491035800c507041c0c44c0140300440180c0440c0c6401d030070489103481150200803c1650344d00070080b00b680107611039240c00c07017032501c2a1011314140e41e154030400501d0400310003040072080080d44511000901e42c0071399a15542d225911009030751030040d03d4102800031401e225068402240140400b000f48000c85203950228544010000e02c103802c49040200d042203800e2041d00b90300e24641c01840c0541190306c03102e100f103002d1303880303410160609a0648004000c04031000c080711025491101c110301428085500b04202481d1004c0b05119095207442c9c11070460003444100250b2140510f4a42c031303151040c0580d1004150480043d00315050701011802082590031807500d4000500303c800007074a043d00030151403403030440d8600c0c0e0ba804144142108600c2e043c1d074840b51780c0c81d9015074542c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 969354604 1250 969353354 969353369
    0x50301120c080d11060114010903110d05061f08010501350d080708071b08160804032009040b04020409030c14061819110406080a0809030c04091a040507 67
    0x40d0611080700504c07100d0705003000f800328400c0b04004101031803078610b80c1080c4041612010051851943c43d041104200f0000961200000c0a00c1000ca0014001c040c800c1d452251490103940001552003010100d81d0400382c40350b803406005102030840050284001c8c0451101c1c0c0100b0804154601460fa0b40c400042c0b50501070406602e610b80d80040c0e07070a003e0065629451078a548001c0f0032a1094150303200c1071600f80f00d40d400740c00450f00e04d80082c43d24000d07031403043c1d01c00700d083e84035810b282e4040c0d4070440d41004806400c00c0e803d00340381218401444200c0b003c80c1e490400761a81d001504028201038030641e41c4d40e16910401d4010200c070054164450401504980014046c0e5103a010423a42c104104000b03190070191000b000c0f0320342115a5000307400d24043c2401ea10303441d000003a11080b07582c0082e95020003264001040226111440c400c6c1885951105500240b40c1018140f0806600450400b10684001913603808945002c0006080940c1d40340d03101e0610b039240005c0d650103044d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 969355854 1250 969354604 969354613
    0x2040209060a031a011409012a08040510020a02130e030717031f180506030a08040b040618030c030201121418060c0406050a141908220201050301120c08 67
    0x10280e076010f40101c8911812a800e1350490310303100c0010745a2000c940083d0b4103056007080760240640c099044500a0342032035015402c3c00000740d610540c072210b102810b55505078007103001c2101345003005ea02246c0110728400b5180701d00f49076003c61840160b40d00700320181e949500340c60f050f46c42e04005039013605402c800c00c40019010881d025200c0c0d8000d50b960548100e81203401c0c00240000d9011408031414042d0f04038642040308580c000400000d05016854001d40403200045003496000d0409800d090a040356914600f45001e05014038403614035402592031002000030918420b091011a602820541d20110304080c2c518002c0015052844144016405008082c10166400720400301d014049500a888800c200e101c140a144504070005008020741d11205119802d0000b45402184245081840151150300310100c111001d03000281ea040400643e05030f0600007182c06860f000ca840e04050807500000c10a01c41401a041080c0f841c80c000002c1015101c4120010600300056a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 969357104 1250 969355854 969355867
    0x3020d032106090b09040503190c0b1024050a0c0609020a080c1003020c0d0c08070609060c030c031505061809131b060206010e0a021b01060812040f050d0204020906 72
    0x1180100742c540207440348a440d0000003030f40c5007050442180110f070410025402c0c000c46041440b402a03c0075400310421a88010140014200702000b40c001c0b56110000000c542c10911132040c0c286d4030070204100303c1d90100017410b4194200080380d03681c020502d800c0e00e482d0303600d0403c0005403c90300702c025000103500c0800201078401040b84081c050048500a000d644800000c5069000781441591a5000780800b60049405440415a060321400d001401e00d01592035a5080324401c503c240c0b030490f282c09603614410341c103200764000c00e0b46508041241c0d00350015051402c03252030052501503900003806c3c850500c54017204032183c400c0200300e503000e440e2010307880d104a8140001160b00040030500d294000f107000c130901c0255400c1c0d07401015160700e0701c1d880ba080540080c01070f0703160782e03800c0000041048181c10086094540100045600351929005070700c1c000c5c0040d02e080c80084144400c1c030003400c40c081c00780120b40c01113401f01d010600c1c50000900900ca821078442e8800c4000072030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 969358354 1250 969357104 969357167
    0x9012a080403033911070b09120a120e030d05121504111303110603010b0d09030e0d030f020601060203041a220e0403090909081b0c27090f0703020d03 66
    0x80c2c00c070b086440e0b541c40b0741c803011714446030f070f5101c0c02c4c0e000c0c907900c038101880004414201151948070000000e000c0700c080d04120344840790b09822481000d400140e4402d036040242c00c0802c8840401665490541d03e4440f1705000780484200290038900c0200e42e40400d15450ba17a2500050600150f8035485941c0d100c44941409244a10303100442d91550114180030103440c0c0007090341d040341d0080c90b11520b4008800b07a400d009051031102141480724060110025031940b02c4e01c184eda80c0300b9204d050001e03d80e0040a45440416480034046500401052101c07144484964903200c05024005440301c01d09891004a900c45480d01d0a0081d01e003000003039000d50020300140214000c0d12241e0185444044a00c281c45e40008090804001084080500289406180c0c030f000c0c103920689643c103107a040042d40c990780b03511099a802030b003092454007070020000801e070171042c0d0380010003864a86650700c544860061002900c0380c0ca54542640525014901081003521092020340c00190391012 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 969359604 1250 969358354 969358451
    0x71103030108100b0a12030c0309091401030201030b0d03020c010c15050406020901180e010302061606060321090f061b0b01080a030e030a0309030809030102040e09012a08040303 78
    0x80c08619908000c2d030781304c0a0500801d0315040e1645140c1ea489084d54a8030155103410100204030200700140c0c9000030070568910400d4622807110f00301800f40d500d1400010182c581400000748601d503020168800690002040c081c070081c02e0921101c241000e0038090655400264121034039400c05080104129059000306aa10002d03225603e1840300440c645c0c0ca09042c5000d60070b04500240014805031a08101408007107442c00d0f500240d0b203801307a45d030500b600d03400e6200b105c4000c0d1a540780c0c48640820341c01002c2e4101d2610b0241005860270441400f41c2c0c03160b1007002d06109840303402c402a48a80914900c002d90400240740542d40e6500d456580d882c0e81010660000b80034006c2a000740c50003080544480c0d0f095514400b040382152038001c12980030300000c551544d420000010031034100c1c0e07030b240e208880c4000000345102a50a900c5507401c2041d0030725203000c0b040350b15501d120780c004ea29281c0141c0c1603c0c00103150a0b00b0341d07100d41c000a4a1803240412408650000304040b01000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 969360854 1250 969359604 969359623
    0x90203070c110f13021b06040803010e1504090b010e01230d140f21041d071107030b060a080d02120304020607020a0b37030b03010b0a0605070b01060f080609071103030108 75
    0x402101b2582d603411010340c0703e00c0207480c01006071004100411210b0265440c181d001010340303914118401684000504a9101c4501112110004d40041010a00040b50180182249004c81135148000c2021070101c5509102a40c850407801e211a0180310a04510050360380703121048441109620b10b01654a041100004110007003140c0c00c961401c880070252801c403111548001e02c0407003903000316014800c000300707c03104004610000002c175180401c4004015805a450703200c0b40d080003420701004411603004486990b1080d40300070086580050022840100c15814a032a03850b68030004040e80708819001e50710801c100360108101c03000100414904085180c070100c0d226004110f40103109000c61000c0a01080100c500c142c940250881d111303d070b03c01000000c4103105400011081700d141d800c4040082c030b01150140400040c0c20030f85003d0183c03402c01c15080d5400f144003c02c0410010001c0b401001030780b01041c0810f00945200f10402d21090039030740ca0350384403419940d4654211 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 969362104 1250 969360854 969360877
    0x70311071a03010906061e0c0f0b0115020106080c0d12090305070e0702011a03070b09040e010c08010f0603050108060a0207080705060c0a020717030d11042d090203070c110f1302 78
    0xb240000702103002d1440002c050340240004403158000303440540f440313148c421040d62101d009d401078000280e83c21720180c0c081d144042603aa11408500002421164a0b4024040e140d00122503901a9510050204401d903408070804014248d0102c00301c650052541c1b00510603c61250041075140000c580c46108c2d0a2540c02040340400d41c00f800681c0000c0041000c0d010340200300b0600c0046000001040d140c8405000841c0c44000b18400c642155607581ca124005030319640107000c08003411031860b004001d107103018000e5506224400b91580d001404020085038000354180c200030301c81040e900703926000025200d984c9420b001d03540240c1c0c08500ba41e03005018401011846424140000c8200307428480191b0510341c0d0345545d280180a80b4a00e45003d2505020016004c1959071a811072104c1c1c100c092911080c600d4150380c13540a45420034000d0300d006000b0090f4480d888011940c0c8680c102540000d041360400200d013402c44c28403100c070307085a005500c0c00e0307026589400614003804803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 969363354 1250 969362104 969362111
    0x140111010e0d080f040b162a031b0309050f130c021e070b04050907090f0311011404080307030e04110406050c061503060c1e041e080111070311071a030109 68
    0x130318410f42c8070280f04039401484085403c01241e24a048501902c81e00111400d18050350032110b080b21031404408250314602c030000320004010141d2158a88404403000400382c0a00e010940d806400d80032540112070140310301e80542c42080d40c0d404031a505051002e001004110f814402c000d44a030012921070004081c1120134409078000050b0700c204032406240c032242050300b40010080b495801400482c10002e00b1343c40400c0901c02c458115006500c95000c8500c6120703000005020001c041c204224080c40c103010400251001208881c2c0f042c0d4980780c10030b021240000024024070702d105211460144c04100461055041030043c19000400e4040340c4050340c0d403204481d1010035002005406410002c0801c1c100f44d0343c00701800400360310380c1e540d818420682c00c0781109504154410000c40c200481102d490340e89400030800501401002804000601c03004000340c0d100d4504010100005180c503041240814400c840191002025803080a502c0b141c5102c690340003800741d45c00c00d916 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 969364604 1250 969363354 969363361
    0x10c061113170705150903060903030a0b0307031a0a0608030c0d090e1005130f02070809090f010f17030c030c0109200108130602070209072c0604140111010e0d08 71
    0x95400401480c42240008110440c00d00041c490500d2030304211107850401030080d1b1000307542c1804828483c00ca1400119100c2c60b00c0c4007080191420111028040d0304043e4007840070130010b0070070b40418282c80d52200481e84034440b0740c00042c0340325440342509000c0840d00400c24800401d10350000d400607640c1d851940d0703c8204052403e141640d20450200208001704660b0500200202c2e00220100000502140c15a0300c0e400340d900154040703039824000200320007945030000b0219003108406040217220760401c8115400c01c03000e030055880321242c0030010285001d08208441c60f520003035040e20744510302c44920074041d00301405c1c2202c0c8550403c0034420b0155585a030009244416503c10601c0d03142c0704401e0910034100340701900c1c1c0035000c001d144090f0b203d55418034041d0015980300d500000b4030704070a0f40300030301c002e10340300c2480e0b50748003880301590320b990a40d0140c0304800b551070800d000550050701c001d003130100f10540070b5003099098000420086159042280b05413601030190340c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 969365854 1250 969364604 969364619
    0x60908060f01090902030f0f150117070302120a0c0b03071413060e0114070f0b010b090102031c0e120a12090206120a2705011d0d030506010c061113 65
    0x2038126407034000e400072034004001e0340380c5075000710060600107800c0d80e175801389100005040c0400c00d00340452075070260b80c000c51041c0c911071803a40140b914542040d1650b00004030241c17106207500c0003034410400121641314000042c030084110320b902120980c00140c0c2c42995070911f4008545403400319000103681911a4504011144001a48049440f88500b010020790b6403800d60844241000612840d190090540e1801403104a000e00b00c5011a100180307080d47c6182d00580103c04040014401a038a40e41c0020a80340c5400342200c0103003c03056482d01c0b12008000244244c0c61600c10403480100f120380800051049210a0b680e42d001000003201c910152440b40d400250420020005021707a0b464803007142c6d0300310380140c002103459100c0f841d0000081c1c2006440d401c1c01ca00b00c0c01c003070b01080024840e5015001000a510011000400b0503948034a0a841d40318103141d11100003c0f42d40c0e10440a060700d07903038080f0b0f040150300304c0c1805802607030304032002084000d03035005c03004221803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 969367104 1250 969365854 969365863
    0x130e15030d0f0f050d060e06040c020712140f150f0a11040603090302070801060b0a02060f0f060603070516060504050d0e06032404090b04030f0e090a0b180709060908 73
    0x400994440c034400b0071031808115a2240b0110318007007000024050310040c1e0074940542c0f002005800000d0500381003070005c200440309522200000c1d58803010b42045003543c0c4001c3d141b91980c01030580024000900000750030004a6072852a0303a00a01c00008407034046e43d5030040c010504180d0400b00e59440803c258100c0d03c0246d500346490b10709010800815110b6080340040500c00d20549000503500c90b65142500d0a5400804030343c4008540a4070131641000790350f41c4040076110f102c0c07050401c028814440724001d09094000c2000100149000d40070b5030032141120580441400d010049061841c002c001c00c0d00c0440d0305000303441026000074800c668401040c1001407013070345151544d24002181c00c690800c01041d8445102008815903200e202c0c084441e406002c40001c81d03c1c1501c1d0060401d8184243c5000340800e0301489901d80e280c2c0c2550f2580310702d607400d0004180f400c0e00002800a4543c800c44081c5540580130801c1e4203520003000c504844061322901c038125211200aa200c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 969368354 1250 969367104 969367123
    0x1205031801021c0b0d0c030c05120c060412021f050d05010605071101261603110301031205030a24050103060b160b100503030d060e070c02011e05130e1503 68
    0x3507001d1100f00c401c1c0401c503441550b00800040c141d8a4040040e074400d00b00d80c510b070b44180c44d440180ca81c10001c90500114588407074610b800a040190035035000076940e405140120309541d07c10102000454480e002d52640300109041001e001c2441010014840d91000c00000145810324000060050040c6c044d204020780c000220520062400011141c203031040080d201d6142c0c142e180112103334510000c07103015404036002c0e440b44500400024054030819a007100c070600042004001140c0341d00c40c14151400c082c58440d0703407038903842c00c84030140400d440f2000310390314114180d140084164400204480d42a02c0078400183e41d500c101400c1c0c00782c1c0c072400050f0804100307014001903070384218644c000140f15151020540f1a8003103442c58000701c0d0700900030b594545050000c4030044c407445500c0b42e0603250a4124031400d43c0000d00a440d80741c00d214003980303008090740b550760145060314500c40406a02c4001542e503100382e006030310010703204c100740c0e41464040d5500908002c200d0021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 969369604 1250 969368354 969368377
    0x408072f13020a17101527032a0e01090b040506100507020607021503040b070311130311010e040c030b010318020a12080705160311010f02120c0703120503180102 71
    0x184403c00d220100e40c9890003400000b20a1141d0000304542208202c80462002141c3d00c900f1806051201e0201110050403041f01d440002981080040c1d02026088082401039482c1100581c0440f08510504020341041c0d45504a08001280c000c20f03ea0110659520445040c0319a4641406001002802059203c0000c004000e0700300076042c80360040510920103002c03000c44c2c1d24102c01620458100ba03a0846210144c841800f89540e40b500031a0380346030490707442610700440c40111038110700640c80300402e00300c011200400c0c01d80c06082c54038592640a07100b800180d4820720020700030407442d003005000c07a01d800b044816800f0f44100a105003039014101546035803d081080c07590700311883c001c903444e0104000c034a00160342400790b07010650800801c80407042c19481c150100101802c016070400c030742800380e06460356002880c4284081c22031803413a69840a41031103030520025800240054a0002d000b00c4030035030100040d0321901040c0c8010a0601e000d21440d4203034414400c1848 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 969370854 1250 969369604 969369617
    0x60301140c0d180501020406031409190209060f030d030e0d080907030803060310020415030e06070e09060a0915140604030b0408031312110c01020705090408072f13020a 74
    0x2065240c1683c00140e481d00b5180020038900758035a221401d903840341c0c0003800001e072500c40d0b170786107908651445038000084001a040c00b81e4060441d44c2040140c0c80e01074464080c1201191707480e00c92010701c0e00417030005416910342030a2640702034040c0c4840703540385880e071003200300c0303880f506100781e9085003d1a00440601030840c5103031103400240d040507009551602400c07183c0030704240e00e880100001d2a180c00000c4040c00e441502030110f8400c1481c1003116008041040703007503039006017a2a40c0c00400c482c1b6510549a020128244c0e50303240d00b210f9015031a203200040250101d000c404100c0c5c2060b46c61114141480c4180034140c0164407000f000103045802260018901c100a1740d4441c0141c2c0100b82d041c861900c4d8070f00101a0b000504011810318001c82003030900912031203c07048000e0000302242450000800c0001c0c0d00100080c00702140490440300700000d0740005400c00c1c2c400307000540e40c0c0e503c0e01c3c04c001e02c09481c151441e220304440d82c506c0e0038143d054001d9034141031181d01c401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 969372104 1250 969370854 969370867
    0x307090c0e040e07050910061e082a070503070c1203140a020309060a110105010509060d0b0912131503090b160216120c051206071404050315060301140c 67
    0xb1018020f03206004485004450000c1456218031102e54030541c0010020f00c00c2619000000d000c906c0520b8003080420b0828126104103604411440e8010074592048000c0b850408a959111400c04607941a0090000344a6050110020107401c15900417800300c0e140590f58070f083e032550640c1d03a1000740071176025403207280c214061601401c414550307401134920b40030000f4001902580321605590114207809000c1000039030901c035103030143c641905c0b900c00718140140080c2c0c400c200500010400d0200e00001f4039000420300400f096a10310301c04194031a482e04122410307041040c020440c0c030002c038002903e0094840e018000785a50011a07800f61a01e900c000c0c03261801c0e440d0101001e520601240001000742c20b0105d00080c00d8844110105504a140c418044103896000d18403038a00c03c00d0001e00c800001c10f010750032404c64240810f040c0401e2141007000d008507402141d040c003461083c0303551940c2e000d03495407040400320000c004001109a807941e07a694150703065908030000740040c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 969373354 1250 969372104 969372109
    0xd02190305010b0f03120c0a17071506080309041104090e010203220b0f0403170c0c0d050f0316110303010b091c110f0102101a030c030a2a080109050604020307090c0e 73
    0xd2004041f1601170b10b004908684500c8003c1c0c030090500901150700145640c14410341e8408071141213182c0100b4015145880c2c1856500d0040d41540b80c8200d40e0f802803091600c021204171002001e034000d080c0619001c8810f0a4000c0d0002c562101143c1d420303403400110003000c24154240980d1010004810703450740090850840c500600c12410300811450f8614070f196000c1c0d42611231541c003402c003940c9180320068542400140303240c400920005100c50400301c0e4621003500d9110086490806280703c1d0110219214030300400140c900c2c0c0000000032440b42c441000820604d9003d90301c030320300281d01c01c0e0240c92140713002001038040a58003004101c01e00c2d01524518a040c0144101c410a01c100f00c0d4640803035403d00c003201100440c0051700042401e00340808621080201c000d040c44280c0c5480b4441624180da221400452880310700c204200b40103951140a40313920002000302d00c10300d00d405035076010103035010b82c03007440b5100000801d10340c240030304849010700e0707030341c0f4140000720400307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 969374604 1250 969373354 969373357
    0x5090d08221a07020d210605220e0c0303070b0c36010503061806040e010e0606030d05070b011404110309160e010501232808011e140d02190305010b0f0312 68
    0x290359a07147d454580024082d50b4040e880c003801d8408008862601070b000d10340004070b900041100c1c0302783c0c10541150645035000300c2903c0610f50440c030841c01542e190301d140030040c444c8418a0403d08429200301c02c070080e10441c1d00c000e40061060444980c803070b01005452500080b60503950108071410344a242601c041c0d403894001e4000381c07021440030200d1003c2425a89900c41c548400e030300880800c42a03140401282e13200800ca8203109181507200d4544001c900d60501440c0440c82c05c048484000ea01c85500c040c0c20007007810030003503c9003041d036443d0391a24580d41d41101426003100010520000c102151812900140c49440030114916502d030003450040d0110010300b001405800c000180c1091800c00c4512482c580344c0310310060020103000848103802000d804411407498405a9901c0500101600e1941d0301142e5a084510f00043d07283d03044040013508442480e8504051902080d0004181e07881403000340300d601e001c101031100032282c0007041581035101c1150305880d05403200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 969375854 1250 969374604 969374657
    0x30524010308190e04111c090309060f050f031503010c030b100c030504050303030f0712060302092206060e010f0b1305150708070807140105090d08221a07020d 70
    0x203000342038002880004081b24002d0600304000b03580018407142c0f805c0d4502445050801d1004100503e12041e1002000b40989006020034082a10f484181c454081d0b4103070b8001c07031061545588e480c5007a450103503030b030302c071032030390345000c2d41c02c01c00e0400285009000f20251008003600042804a56079000c451980c0200c2d01902806010032010941da1424002944503400384101501c45092180b0300412000c81c80e0b061800381c0b071400400f44016a2500702c015002400d45031000f0504a05110040c03d114002100409036850400c000804140650880d41200e605822000711940e4420031000d891250340c10421020001d01401d00007494082d890318410948400c801c0d003081072175610346000d0f520600d0187c4004c40d01285140030844101050b0700c0044000000b070019040152a03c0d54699003240c00b20107002d11040011420310303480d0311018420784202e50502820040f03041010f0070744503040581101c1741444d800181400d0001800704050f5907565224800c2d000d0350007450007030b01d1a40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 969377104 1250 969375854 969375857
    0xa060c0e1e1c080d050a0f0e0601051203121801110c012703050d09060b0307170607080c03011719060b0909010b0d0807050a020a03052401030819 64
    0x180080440e507100e80c40820010200321020341c582070000020411038000c000e1040c8005000541040d001030100302c20750701c040c0039601c0c1c0412075480d8480c1c60302c05414004546814240362000302c50b034035100040c102d030489a050b2006245528000b105030703100d00c1100c0e042402040d9040110f00d410484440c051440c000380000000c02001503103007280903034080c214404150f0b464000c1c000c0c5c01115020041c5030555020021031048486550241243c0200ca402c180b039140e6408403902030201c2c07600310443c0d0b0440141500c0050391102003441d581d51020480a180303204590009280310301901405001d040ca156806003140e03c0d16803400d0f0035955201c20310046025844030950303000d50150301b50307007554411540425915801401e1141d50b030390090940c0c559a050003501d042a032100c04440e034031286c0000da11556684207051443c904288010300a4000340c0c0b8038000003d0010100b00320b12500c00c491030a07198809004a0685410400e000140203c03a040002d2080320441b07952000040346135 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 969378354 1250 969377104 969377117
    0x10e090703110f03070b1c15031e2f0603090613080c010212370f11180a08070602064512030c0409090201052811030307020a060c 57
    0x100b0000c80e0400704541e02c0072000c1b5801040c2040c0c41c0500303003000b040c03418091f03c0400a400803e407240e5284c0c81184406006071503040c00d000f0940400c000e00d4022560441c08139003200d501d91074081004040104006e5100445044c5c0c0e071503038030300b100032030b8044e9141c1401014161611203115003000d036883c0c0d088420090401c55551b03035a00a0028181401540d02c00b51010710f007408000084040d00b9107912070320500d00150b00703100140b8a4421103c0621003070001550003400d00c615000b0000354100c03042c80800070441d103003c0c510003800b0780f040c14001e403107880032103039030b5211156565680c0c0111000350304400000307502c0c0020900306000011034040862040321100801b40109005d02c110884002d9000c401480000006c0011076960700c8040c00303440c95403501c41690600d030300a0b402010001900c900200056a214400391203410950045000c00301542c032009500904245000501084901010403400b9030f020040e28030526483d00502441280365580e40018032500d410241032094 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 969379604 1250 969378354 969378379
    0x5090705010f170403030504140619151e140a1a03042108010509010b0a0c0f060608030d1a040603021f110f010609110c100b032112010e09070311 64
    0x180c0b801584c0254085d07100060b240c00c00342080c06400c056001d1040c181c0c0c3c440c02c140503041c0c4a0914014801207a5840018081d128403202244048658081204958000d540d40c58034550305112500300e54001d0300100c18405000b05112040105115100c203030617009054100d018000002598803501c41d0181c524428016007000c0003114040c0340c5500043c150310b0041c0900d003480703140c240c09000c81c0790f5043c3c2403001c0c80b40300078810004004020105500d81d00b00004120aa40080011340b20001c256601c1b40840c401c2c15004110009001850411041c1d4884950174a07204940030390780c0150200019100c6100b20380003004058010b40e0801140b84500f52042e0000d01000502100340000030884030724140025050311040c0c3c01d0b081000710108450450300d480003403183c0031144c4412000c10307a460040000380c01c144410410f032949110070b480785000440c000004044d080c0081c49649080e0740c8500c0ca007900030004440c0f10402e035200c2081031001c15080d051a010702d02004250035040f15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 969380854 1250 969379604 969379637
    0x6090f021c152705031b100b2409030c0907030b0406090c0e011808010f0606020607030c05030a0906020d0c0504030c1203080a24080309011205090705010f 68
    0xa400e075681c0c8803500d00c2800c0715040100c020a081001000100300303002e101d442c01c0c205042c43e440300011000080d8071050b10000c0000910aa034120074078120894040121a80c08680341c1540e5145030340c090340350101024061030b1451803902e040749040540b144070851580407203400c3d84a8408940d1500c01c400c03c0780c11a42e94071000e10710130382059901160110055060005950303d9400400702c0d1802c1040c101d07d4994030031422920100c0901c0c1c8114140704150900c107034583c607604442c00d5542412021204140160054400c80d02581d080f11070590740d00000b00c1c04c4402c00c84105000075030410106207451555017002000074000c110061500e201499141c0849240a6030640445c0c0c000c241001842604442400245140481c4d0b4801c083c2540c0e000b01443c04c000c0247e41c4c41a13603020074a10540c80350740740d10354502c0c02c14009035039a51910b80d40c9599401a0440d10700188182d000c1d001d5980c0c1c0740c01524080c1e120100201411801e05005580850000607400c1c00c01c01088003c1c600b40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 969382104 1250 969380854 969380869
    0xf070c240614090114060f07060903050703082214010b03030d1a010804050c01050310120b160c080d090512071109010b03160e032401090b031906090f02 67
    0x4458080000340c03651501d90011241140c040c0500d00c43c0c8228401003000e20300c40800000c5d5030908455065580001c01d0500001e80211600605030741d11f080b07111000c041c2c200005000d074900a881d8100b03c0c0c0d8078042100207081c000d13039214001c48134040000d40080c40c0c50414580c2a50780800109da001444000b02c0e145400440c07005080c2520780070785040f00e100642100c1e0b18150280307084c0b2960300d069140c03140d60f11000201035040240000010344047c2640049001030500505144418241824a84a0b9200a842445420710940080b0b140c09005007900d6048541c41058981060300940d141e0000f040c40c400c0c207403128012001c581c2c00c4507900b04006c02850703124881d00780811309984280001e40f0ac050304003250b8031100f08140301c030700340c00044004554401c0d440c0c03841c4521050004641007040d801035080700303200c0c08030130640316038141c00400f8180e900d4020204001042441003540e5a0050156072000c8400000c00e6000302c1c4070340d049244090700070404540ba102c2e5a60200b03210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 969383354 1250 969382104 969382163
    0xc041701020d0f05040b04080306040b04060b090f030d021f150602071d0415020a02070b0c0706110601030803430f0903020f010c030c0218010305070e0f070c 69
    0x203650300140c254515256403007809100c40704401c040000c1c1c0340942c3c4488500b50007602c060720f1510084001030140d540ca80100044100240c024040141d4800b013a19850700800c20080c483e004800100b140c0342800200031350102c4150340105170f044840d0300d1428400c400c81d84892507a60321400c14101181c6464410001070040d68001d10b2002c0c41e003156001a4100242c50b0140720510a05000c04286070780340000b130654890400698403003240100740e01d0000d041e485560141400b058901e80b106000c9100801c0320340a4450b00502040c5d4003200342c94600c2400010b0030004103201044854800103a081c002001c240c450008424504040d19980606c0e07102030904012030740301710069283e208101900e02100742c10600a46401c50340081d0b82c2d042141822030400c98040c151006140c8103000c841440380d0064400044401e0302c0786000708586007404240c900c2c0c80360400001d40c8005030101244180548481c0d43c802d40c03682c60088032500b0410b0002c0e01c1065080d0028844c961000c1c107112007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 969384604 1250 969383354 969383399
    0x14180f0c0706020c06041b080102123103080907081f0222030c1401020a0c0302090606070c23030307030f14190327030903060c050c030a09140405090c090c04 69
    0x1241610242002010107a2390849410f40e4014010100144131044000340c1041d0744c02c1101602000d04090031101d003400070003014600040d621544c062542264046000c0c015910941d00313090344030190f06030340f000307070345400c402183caa120310015400c01e940c05071000040d4405162a585621440e86a2141e855001135850344050b4400700201251800e13030003490345083c00545605415a2581c00e48000c5502c800381c040c08503480018410344d07403070080700d025991212441a015890b040084140c1120448120341d150713400704081101d14000047e544000c0e8545e0b110b015042c2450022a404440210500c445032000d02550342c44d40b01e568603641d41420742c0d9900240d1184215854080500c2c00c030310402c098107082d0503071400b182e440240720381640e0b0400d402007260300703100704212154464621840a503010224558245a5000303070654119804042c00015070342494080004555003036905a210380e00480d10310440341002443c480d806031078221000d081503500c1007900c00c3c03000c1500200d030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 969385854 1250 969384604 969384623
    0xf060207080307021c090602191401020c01020d0501050301181506050607030c0218090d18120309062607110127020102070b0703141305060414180f0c0706020c0604 72
    0x1c04401c0001782d080d1101c103480c68112502c07450241c010752039070041c0f4541150700c202c0c2d041e032005001c0c00c00014040a650307103000715904d001c555800c0f8001c0d00940c246844407414000009550328050040500b4070301403442d00c001e81c22142c0e03242c9021241e607001030071005840303440000d4240d590102500c0c02e140242c41e100c445a0103032041044808121010154ae141130805000e2035200010b51290341d2110380c10a6070840c00b86070311110f19071160b54480c800d00c062403081c4504242d0701801010446006881c0c070040c001c0144008030b0083c0c003a0344601000b44440c400503842c207200d041803041d450000000001c0f101515030f4107424184445d04143c040824200c002000c550341044140f0081030002c1d1590f003060701d540c0d40102071860003940d045150001003486400781002e82c00c2c000042c000280226507d40d03484142114402d1032f6642c003803145c042150107520a80b580840184242c01d01d4090304151781e01c40d283c20007240c02081090b2900740d400c1c8803e88848070108000c5002c0d5000e0382811 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 969387104 1250 969385854 969385873
    0x33403020904051303050a120e1e0d030c1d0f120d260f040c0902030907090c050c2508010e0705150c0c0f0103140f040c0506040302030a0f06020708030702 68
    0x4415a0030240402c0a54903640401310302082e402000d0714840c03072262401ca000c8100801c000d0000d08401010580c0e04d00a145991200e0070048041c610000000b5081d03404180d5003400903070880c0c41c50301c50840810b00b440c07401a544110b007081e840c4000e40007001c812410f2040008901c018840040082459102d0400c81040640014070011006403110040d12002c2040d0300c0360740601e1003d05060820448a40031604201c0b4401c0751380c02820003035504640b645000d0340074680d100c00b54456810003600e0044061070301c6108104640c0f100c2d10420041070b00188805d951240365031201d4208608041b10340740840d1901c030078060840328031075800041000d6403c2a0402480000c030644645134a001000250100040405c1028020800b100d51210110681006074003401c03544000c1c2c01e24440d81e00800c1102c0b12220400d602a50182c40740c1912107443d070080c0b007020303c40c500010303606038400402d103400a06d0b003082d400800c9100d04405400e0400030351721a00d96170016940310f8013603089100311 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 969388354 1250 969387104 969387109
    0x209010e06212e0531020a05101707020102040302010e09061011010e070305100501050d0506180a06051e0c0a051209071a030406050907030b010b030603070f06020c120d02030334030209 81
    0x313840d801600185e12803804a0141d000409a032068408c0d2130054400103403e00d500c0d4000d884d00b42007000000703001c00701031401c480c00070300030f5209002c100e0100710600040d00d8141022a00789204004c0682840882030480d40b0039642201a00c411500035900d9a8038580032050910100b002140725400501d594036080d1394802c01d80390160011350144014448520104070f00241d003070740280b42c0c04aa0300c0c517014021015400c01492030805030405d410320060000a140c8050304150150350280300280c5d0b0744800c0300c2c00c3d1b540e20031044040001201400f443c9a00720900c805141c0240e051000c403602540e446902c2ca00014072020801c200140120412061103114026243c1c01503000019200090940d81c8115030004180a049010300c4040002551b40e1010804203015000103484088030940d1020001c0d070329450700c4612401703035820a6811025a10024000741d00c03001c0c9030050360071540c80503040314a41d50141c07011007048920015007001c260250041100300b90381c650f00580e8600d1520207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 969389604 1250 969388354 969388411
    0xa090b13052b120203040f1203060e010e180f07091802100f021e030313020f04050109021b010e0d0f0917100c0c030e04020904090209010e06212e05 65
    0x310f2203407141c01001008006840750301c89028040c0e00030101816145072450481c02400c1940021401d07100201c0081007200c0e0a443c40d0307115400035150b421054600c0000a80c8402e4a4620b006145d442000309004e082020341007200f0081c02c3c8480b8001e102d1240c1c000901c0440e500c40610041400504000040e40c1e040c041140000004800502d41449051407142e1700c0c800104440a240da20306401011980c80748000c465101000704280495610760003400b0003940301d9032020350010030303250007400310b00740c180a04e00c5c4541001014002480da01ca03003c0c0c071100c04600c00b013001c0003506076003c901c03503004107142407504111074000d0000200d150100700c00c8030100c411050901c0440d2621500080c0e0101014400710025680903848a42c0640403402900c002a8000e6001d010300c0c001050205010300d00364451481103403081803a0281619101c20041a500383c0200303504804000402c12030740e0458101054030a68030580300e40c0c200040c0303008071403007902c42c48a40901c20040b004881904075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 969390854 1250 969389604 969389627
    0x1201030b061c320706181502010b0f0d0506010e0402060903070e0f102d08030d0506042007290c030a0606030606021e15070c05060a090b13052b 63
    0x20340c4083c200300c1c024070315548030340c28403c000030841c94000b15103800030f41030017480051100c2100c498100744140b10290282c40c031060818010309041810041c2490898860480386400c0409031036141d0a1108400800100030400e98129604020f003182540b41040005c008005d008924401400c5c46c460f601e8442034060300640c14050041c1050107007450f03c2020900484010348502c0700724401c204407034140c41056010341400e00000c20010550101c4e0740001c0d104480844003007001209000004462300102c0c280720390200801e000107000289038031030011a60000c822041940c00680300e40101c00311084602c04a240008000c0c81b601d00100d0160001030021420305004013410404001d5a85c1c050406c440c00c00d40105522030203250090143d01000c4a500181c00c190b89801d50019040e4240c03042c08070750354030507100018004032042c4542000140c0c014140320391600c1d005800e10008100002c01d507440d004004a0000515001c3c00d0101006801170300021004080a4003411000701c46 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 969392104 1250 969390854 969390923
    0xe1e0a0207020f040b0f030615010207050d0f02011d04060f06180e0c160804080a0c210311031306021e070b120c160503040e06061201030b061c 63
    0x500a9400580d50034800814610080c0c500150145c50440090030040c40c2c40c20344c0380c050040d02c040c050345000c00a241d81d2308440030303000c40702e00780d03511400d000310800e80d00c10140000050303007008001584215900b0110462522507904903855078000a011074041790302100d8194141310080001c2504546904011800d811886000b180f4040000c8882c65000f0908102d03080d0024200e85107610b24140e0480190b00094810b44494503482801e0f42d4000007032042d2600048440c0004150504060032407004040c3c0d000c5005141243e0350684090407030240c802410300083c0818030355030b802e05840c02d00030120740c1c1c000c2084a100c0d4040281c0b0f00340380b40180046400038007082c82411a100100c500c001212a40e18985684449080c01c180c00703910b41000c030400c102c440441c18400b000015205941114032809680d49a0404024952051401d036540c0d040c1d00760300400c08900c15001150f4400c00252001d0784041500004512081d0583c00c12280b02c0d0210302c6030007568401c0c2c0424000074016 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 969393354 1250 969392104 969392107
    0x5060405060d08090d150506120f0c040209060d0c1d121507030b12030901200a0201031509020409091704050303030a02070c1212020c01030218060904060e1e0a02 71
    0x1000801c980b04410311000d0b000f0f990004000505488807004400020342080e1041d022025812512001d003005a4a09102d049007416204084501042e18040502c10b07000401017109140c0c24400030350070020001d54003020038000d5003d9030216001f03110343c400340350fa1100405888074420072079107c501c400d524000d0591805030036611400155149102c07841c0720441e0704a55a25008402505514a0181e000134032000d10140c1140c2c00805400c1075003007604d440c0e070140010001d0104504900e070112a01303a002c40d00c0800554000c0e40090032a188580083d1801929000090700380d0340254410800140e4421602d010b0000300e602d0340700740444a43d49245803514040000c0e41d280006480d40382040c0c0e0000320101080001c0d089000104085408170100c2e01503410902202c000c400e03c2000036003e6541011600d611034802c490f0100400d40b9442030f500f0b00c840c140042a00a40c408a400558490011402212103040b140c4244007a0740012001c0c01c07052007880b071701c9034003924004c0c07450700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 969394604 1250 969393354 969393361
    0x603060c0a090b0d0f11040635070c1e11060a08040813030204110309100b0a2709050f070e04080d020a050702040c0e040b19150212190305060405 64
    0x1d1000b02c0d6000c40f01c4103070181c0c1d11100e00820074402443c5500c2c0ca0294a0718004445098203541c1c40580200c0e54180c5544120f01d480c510300c000c045900e041000101e4481d00e406500042c4008a4030b40c0000c2e841c0380c4821030303c9059840c1e058201c1031760001d0800314101e1a0040411040c5054250315503400e40b00350381400810743c00640300c500041d00003410b04030b01103540c401f454140a0f2000c0115001001440208490810400158000d0b00e68403607500580300e0b5103001c05110300030020301403000703010f264030645052800c43c401594100804111617490410034005c4031a40102e41030180130380094004000c4a04a00e8508169a40180b6141e00940b080002040802c0c040c0c1d050059a00c8000d6514144507104132014071480c90000d41c06443c1c500307a17003040e0f58000010203503150280d40420004802e08100307c00a030408030150907142441c642808241d6132407229000c001e0807801100d42c407a901014050003a0801001000300030040101400c143c0d9040c020941c0108090300c1c10003d40c00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 969395854 1250 969394604 969394607
    0x2130b0f0114030601030e030d110403140109110402031008061801060f15050f0903190606050414040f020411040306021e07110d02240c010b031204090b060906120603060c0a 76
    0x702040c5c18560f481075000c2092501f4000c4500100409100304244200ea90a41081d40c00a0109907801c211880f03134045209014031a5a0940342c00410300b181c0e2075041030402010b50f10090245044910310400029003c400700000b82c0118068102ca04c41000c3c000300c20390854550358483c1084c075100d10003c124801e03541103812105d90303a91802c6903a86041d8010810f5a00c01c0c81010350b01032080b00300b0445020034203068210b0140c400d013000d1000300c0d601d1041005855000b12a0303c015903601c1c0208000880c007400e225001440540040307651601a40d0004117904958003e8614030380028004c2d01309401810ba079070400c0d86502d400b6003000314036103034203202003a100007160003104010400000d41d951103961500f222030a840e04506e00001d43c1100314190418503907a41d5940c00c10745404c00f00d1801164041000303014030071203030600f8036107103092019100c000011508210108540451030f01d0f584020800c800c3c1c8020710741c01c0c03800c140c0281807a02400803c860203619091002e4503105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 969397104 1250 969395854 969395857
    0xf080f0d1a2b080f030c07020a0806160c0606081c0921061e02040f1403070506030f07030b091512060f15030705030a03020114010b1603081302130b0f0114 68
    0x200c4202e580580100c01890226802d106000d400611940048100483c004e216802000c080c1c1c400d440c03c5040c0d03a60781c17021550307071903040e206508401c0d10321101d82d007a00e11032584211503030302030781d808170b412961041164280a100c2c1402d454281120303803004c400319004042c1a0051070807004e105030b250480c401001d00360707400c0c0d003008003001d45414840d4442c0310600200b008540c10b020045558a27038607040b201d0214010710908612001c02e212000701e605d0b02048400488802030403251441e074400020395070780030009200301c0034181e8076081c81e42241c03141211603100e016010301161058030600c040001403480d00101c02c811758003117400c000e0f690300c501d01056040b206038a5032001036600b543c002810408036410075501846044034583c01c3c56030540001e400300c01c1310b800c071141a98966056941074881c80000f100d80050744101100000e11402c806c5500102170040000000c0465000444c028140f410485000d619480900803514001b1000003030a035003400d101800110009009a65 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 969398354 1250 969397104 969397159
    0x40f0204061704030504060309020f040507020d020d0201060e0a0b120118020f0f010c0213110c0703060501120305040b030a0906090c090e0114061c020a0b0a080703090506040f080f0d1a 81
    0x3059103d030907074011500e2f12550b000314143e0040040c02a4903164200940d90103800c1c004c00014400d01070152031842c01841034506482d0031750b810004135501d0551b02d4002e02002c9035000d0300084200c0651440090030302c1080c1c00007401c000c01c43d0b103a9806004000301c1800c45078115103d08000401e084890380c01c08007003141c5a40c1620301e54494041121200010402500341c11000000000c0300c41030b5039004125001602d02c0384404021036608e5288007181640034000090220300108820300c039900404019660140e140240401c3d5501c0a5980d0000c0d2520710b1070403120420821010b000380884e5005170082c202003000200b0a568a0450700709454001401c6a8082c1c980026903c1802041e038400440243e00500100c0e581566110810f00e5170303001e03944010020b090a80402c40c407034828090a810690408001e00303040d01c903502d900b80041940c40b8200c0d0201d00421042c2600310100b0050514615a00d000099075540f200e08611603039521507005101e01080b80c2013401d082074203141440f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 969399604 1250 969398354 969398357
    0x3200303121008030c0a0c09050f07030207210507020111121c020d0c0f0216150503090c153103080d09020d0c180e0303060f01050702040f020406170403050406 70
    0x1c080d2100c920340e0200b00b00d55004140036000008084911880c0041c5420341d4520629545c62804d9640010f40103d0700140c0d10300420b01002008a140d061094005e00341d19409040000c00b601c1e1122030000701869804080c2d008200040345207425980c00064401002c0664005804000021070a42442e803080f420114240006c500c05c2e0741c840c1c0010340c1900c0c0c0d0503032f9240e8100021254200e01500303c68806100070014850040c595640380081d005c2ca8080311162103000028070080c040c29210798000810801c940d1003100d0b45000c1550707501075075071011400c00c00030384d81c7c1d03051268030302c11621880c0c20744503c82208041c40305640050b4413107160449800c540d40b41d40ba0010414078001031311801001945c0090070300841418094841e01110840c4c0e14101d80d003008401c01201d14007644e1a074022094940c00920014440f410b107880c8d28001144149400c5140607210303400501140e15104200500c20f13408103003440b03280e412103001105101e14807110303002c2e07140c142c0c4d00900300d03c240e014020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 969400854 1250 969399604 969399637
    0x708040501140613021806030a0b12150606031f0e0a0608070302060d020c150c0d060504050601081611010f05180729040801052505180f0303070c060903200303 70
    0x80c1c00740803036286d40d1020b8003c0181f03a880c101642d810026240d03000b8034070302c550b41c02605c000c07080400040c00404450085c007078480694810381004001c0e0001054032200c60011940f01444810340d25002c005810340c24001a61402d04171030180031a540340c0c1040445502140e800d0001daa07803041582e4521000d4100581c1d1005804051400c2c210600c2c1d000c540d40326030700e041c410001211805404c3c40d0f40c0c0f400c2c0c200401c0f6540c40410055030802d640d9640404e5104020400c3c21071580042e24076680e0904000103070000f0201c0003800c55042c01c1551044503952418801c80340701150b4001d111040240c01043c0c8582003e038105d480c0504c0d8003604503601d840c1d02e003804241cbc071400141c4004094080003000300d86801a020f0804403420b01114130540030a01c48000c1c079600800a95010300d0f0f4101c040040c2c2034a0340c0602a452043c5807880c5e80c184070500c2060f001414511412000c0d00c0780d030740c0f040020b0b032461070811518a9000c0000b61100350002c07500f40c1e00d44000040e20b1507a500146100d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 969402104 1250 969400854 969400867
    0x4051009050907110114040b06040f1107140705030a02130b0a1205010509070905100e04080735040e0a0c0c06020a20010209030303071d0306070804050114061302 71
    0x262000d01880e403140b0740015000d410442c0e450340000f07010b80016080402800341c241d80700000a640d00040710b0040c070756008040440e0013420f0551040406900c02180014455039498900c107807604107010860b030f04540c000250901800c140880001000705a00400c050100c4ea400078002d600e446440748038081e66400e0642096079a02c00c038100800b911100d1441c0c980d01c0f4103259000e00001c0309c00455078400c0c4000010318442c1c602c541e51003403000004c4805124205000701c46080b03c080e0040d103d0000902c0401c01143c10000065000c005401020749400140207202c0d1400100a2401c0413030700061004000b0500301c000126400112201c0c009266201c1c0b020544584504c1d55000d00791501c0450700d12030300c0d0340181d50890b90500200d60b0381400c01218a449090b403040c1d45185416400510118180600401040040c080c1c080c1000d415151b491011900e0242c04445010024000c0014002884400e01c03031071006e04500420802503181c03900c040340603840000240c807183c2e60b002848 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 969403354 1250 969402104 969402107
    0x902072409120306030b0603211602090f060307061b300e030f120d0213180603060b030a030207150c140610051008010303030f06081f0c14040510 64
    0x100c021030b07009003000c0051030403400080081582c0e01045612480142c0852800d00e00050311071a42c1406550300c040c03480c0035042026203034001c2581c15180460a03882c100c0180c4d2501d036140d100b145107100c82001450315030708051401903582d200c2d03810300c0703041c40d03103407101d840d0021400c0300690b0420703400410198001600700781c50184c004004101c2c010081c9403c6002c0d400740d20040034007070840842e851242e420100303079194051000a8500d1520030403c1440f56030054001d00001d140700503450044940d510050780001e08800505001c090391b80b04240100241d901c1103d41c42e04054000300700480321650082c1d5a101c0e1801019090002c02c2803078100c080c401d54850015690140c4684c02d14952840170303e80d11102584c804035001140d08021526080402a42c44030040c5951500c0c1e0991841e24164010f2080c01e243d8410240c83d0080403880c1d000800050200134070920004d4903c00240c0541022525005250000c100396406802c540300c910394160790039030b1000c4854401c0181c60450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 969404604 1250 969403354 969403361
    0x70b18210604110109140303031609170307031b021003050405011506020c030c06030426120903120906010f03140123040c06030216030c03091a04030c09020724 70
    0x1014040351041c0703420041000354580c100180700d4003c1c2c0b03903004159105c0c0045228036022450f401e4050380240000b0340c100c4001c5041c1ca02512072810020f40e8540c07a4010424100040440c03420254070008e90341080640c40b18480d200d07210300c2c00300c080a14070554005005d40c800d4081d03050401d030f280d01c007107003d0000a50101400103440740300300320940d035103410280d00c0310382c4489441d102e8024211220601c0c00e20008481c4241e03842103058001c0303400d402209644800603889214060405d100c3c200d1000c20200c900e50080c080c080c025903e480003169203020711013004000d0482900314a0040098124007841310040c2c0340e001041815050389034003814010031106180004880795410f0b0b69449451400e40e060045008001e00c9451b2078580c0c000f5403e0340300711030388814000106085100441d01c2141c2000d031007442407400c144890703618107444c8030706501c0c2500740800b0100003404008120f490110a0004c00039440306604003400d980b0b4400d43d180800700d0000880c031840c5480f0440c114036a2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 969405854 1250 969404604 969404659
    0x919021503190219170903160c09060308030a0b03070608310305030f100305280c14010909180303021e0c0a02090f04020306010620031b070b18 63
    0x4219100c08070013002d6081c40c034619181101280541030304801100d11301c12007034440c008a900942c5000c5200000c0344074405024000d84011605510100304480d40e402a8001107000394041c9441e420680040c07000c4a1801113840d01c00d92207484100240d5411101841e8044003d1049844070700d6109003481c82c8031816042060721200c0d0701c03540c1c010150040b002c0d42c061342900514a100b50707214035000c80801901d0101038210b5200c00380e40d0321020b44200001c41c0142070031142c80c84508565071064010701d520782101c10f806140d40d0840340f40c0c2d64000c14440060006000c14400826200c646001044402d203000d400c00da000034208884208490801c0507440082c40ca00313580d22464141c003a01c400350904102d01c5901980c0200e440a003413141102d000d80e8006000e401d890340703050004c0c0d40c0e0b12607a1141000c560f1003100d0107890304405101408151810951010340b44220980560400c5042d8100c18200f0f0300911220310300c6020014843d112703e0003a00c5202800c4400200101e5440258 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 969407104 1250 969405854 969405901
    0x31b031f050103061104030c0302090c120901481404060309170c031c15030b0a060b0f1902030f030a020d0b1212070f0503070302060919021503 63
    0x8003034225155615512a40c1202d000c0e600400c480000032404410900c280e03c03018040d0002c8a500b80054588410f1003030700720402c0450580750903052342c0d241c2c10002c012212200307035075507035100c204181c031400e03101160318460114a08841e14840342e20f1080c03001d550305444511018100304092640c0104144d01c40c0c07001494000d92151790f01e5000801a065464048130f00c0050b10b58202c001406107c10350304650940c501843c00e1041c000642e0441c0303003203c02003500c0c203900e07801d20241d1110b20600ca1f2000d540904140c40d0b052030f00105120548182d07900c002d40759401080030b52a0b50810405031400715803800707025500d05220007404ca245008200505941c49400400d0003c20410741c1e0040116040111090011400401c10451644501500c60540d80c104607001c40c2d40030044001460b5042c412440010801c129403141072554001e48001c40141c0e004405200c1000350401c82c3d18644641070500805005c02a404120b141405581c106103160001c030220b0880740081e00c50211060f00c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 969408354 1250 969407104 969407143
    0x305100e0103151b090311180106050909060d0201080c0d1415010e0d0506130501200901110a17030a020912011a0301060308030c130e0a02040e0114031b03 68
    0x481c14040c62a050114100074042e2424082800e91400c1c490f4000800c4e0440c0c030740b0070900786980c40e88620913881507130284e0300502d01d0040d0080d20100340c00c440e01900c1c15941d01d030384880010003440411540585550321a10481580d440181c2e801400142e00c481000398880d00c481c041860316000c3e02440b000701100c05038000410a40038031992030055401000d0365818004000e00c000e010101031006009003c7d5041140040d1700702d160690a010300030700c12000001d040c0c1007441c240301c4410812450b2000d607040015010390320740c0c0c0925240c040100c200d019150414040e5211414081c200225001550300030001540d858900d9054900802e0054842540500011407030b41c028030703000c84443c020320300744c0c200c0355128117051280c0400e80c0d86c0115180d19580301d40b44a104250440d5088031a070103050580070450401810901780507014120000d1388850034411410038011051304001c0c00040d4080100c0d07501d580c00503103c80105103800ca84042d2420f80702c0803a0a10565a880a001200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 969409604 1250 969408354 969408359
    0x31e0f070602011a0409120e01110a0803101d1323061f05060702062b0b03010b0d0803070305101e080d0807020718060e01030b0a11190305100e01 64
    0x10103400403030811490701880310f040d50a42c405c100c115905140c02910700307441c0501e02030000e07001e103500300441c80301410140003211500340f00b030303103060b0b80410f04544824000c000c0c840c4c5400303031400000160119290703410726084000f41c8048100002880050081400c05202040c401c400c101d4683d441c2e10004a0300351a0001c6c103585942c1c4109586410f90380c0b24943c1100000c4401030720103c259140100404d2030326100b40c08100440d0484008000115101d08007c01c0605004192004410780c540340403560000d11801c04d82101c02c0c6140305406030203005c40c106c1c0003544003c102c9910603058240050141ca814501003502542c50b040400c2c0048501c140421f41ca001d0044401101ca4400460f555038410040440c1c0c4003d09588001c0543d2001100f8041300c10b019808000301c034403000000a4903a514001e18400c51020b07030054802084450600071901c0700e9021701c5444604508805c0d289c581110305404551040c00070b15010141c0d1100810f100e8100c0c115414002c204031440d0888658 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 969410854 1250 969409604 969409607
    0xe071e181a0304050615031f020d0509100b0f0a031412030117010509150711120a320412060e0a0c0e01060809030d0c02100905031e030105031e0f0706 66
    0x140159010740704d610444001441c020300d44100041c0c5a68043d001c0d02c41c00d03a0000031407112300304265101c03075025020701c02003504007103e104461085007904000c290702030100b82014120303542c41c040e017401181c1da0400c01d6415164101d1040860798020b41c0c039221000e01c0040203043c0701000644850250000000040741041c002c4c1c43c06181202c1802005151074104140d9620000c03c0c880710f101d00c0c0b07480700040350b6a00441c00c0240340301c400360556040780a59154100f040c6e00c42405400401d040d07110000040c546400c0035903c0f10ba054a0004c4004801c850603c1d40d40181d10030342000f041d40004e928200700c1103402051005001e0400c990724040c4034035000425003043d000300300007600c0250001503000d128140650081e040240038614142c004801040500720511f00c41c01980b040002c600c041100d607205d00d00141e0b0141000c1d41d1125125410040460b058000c4941004010300060000d40c1d400709150485000000342000f100400c0175038681061001d801046545c0100c0350b000a145 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 969412104 1250 969410854 969410857
    0x406090c03030207140a080c010e0a030b071e02010b0a050f0d0503030f061801120f0c0302060a080405010b0409050c130b0901081c1d0f0f0a0f0e071e181a 68
    0x1517901581d0410038a40d46400d06c0703c1403441e031107001c40c26409000000340650140310a0140340c080a80010faa003526926940c0301c2007002d450038400100d81900501c000c588006603419600d076148000e108a6040b0000950142154040e040c440e00c1e001442c801ca0381e44035011402807542c40750035642c4a1034000b15201e940942107a8103805030103030107031101403041681e803514140c809041846681041503240e9402140408408135400d43c076100f400301c0941da402d4050144100b055442c03261618080c5009429998691209400349050180d4880001c001203820300b034680081c1ca0001d894440c0e0703409000505032103070100b0b40140110001155150021541060070703005036154071445550380100325501444c8841991060a064580313010750319211100c500f02503c014011000b0b000c4400006074051510f50000e4440c0248060400c4000012101948d0004050800741d00031200c800b4902e08600c4014500c90410079604109102d441100ba4058003502a0084600c0300d1714a01c69404501d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 969413354 1250 969412104 969412109
    0x2a11100e010b06070302120702131103040201120c09062d02070305060601140304020d03120c0302090102150103050d110a061505030c15250b07030b01180b120406090c03030207 77
    0x10750800305440c145051040455508691560052078004824010000c003a00300440413a031008024100c4410000b0034080d0f140521100d81c4501c2ea43d042c5880090720000c602201c0741030b005d05001d05131003c60341014031a4120340c600d05040308103030111024031020b807000910b14034a810b1000c01485103aa400950b4806a91080081701d03c26158070005403600144800b000e0078202c800c0001a005003801c0c001e401820780b1a0422819509181c000c001c1940c2408002d41d00090b0301044c400510740e810404070404000d03a8004007880d50441d220541c44c2c040000301c00c0240002201154a150402c21000012580020b0304100c890580c600080c6a16160300c1818400c2c411034980c000b0300e00e002214002410503180c41c05240c01c0b0450404684a1400803003101d02d096610070640205a103c1ca90922850490b07400255211b0104c2c00034007048409900c0b240074120b004800e01030003002400b1a0380f202c02c02e51501c032183e80c440c6000e102800000e9801810584014000001c2540001d02e500a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 969414604 1250 969413354 969413381
    0x903160305061602030301050d0f2112060f081b03280c08010209030d120f05100e0c12130c03120908010509120403080306041b0e090a2a1110 62
    0x80d103c1000000ca0341c0740800c4c000e0741d90100c4017646803000940342c982d640d44210711900443c004010840090041441001d0007070f4046641810800342d0843c8074071881020740b011006507000141040b010581d10b00403003101040409504070209040d9500308240010784a50030300e0f180c01c071030501100d0851241107000c111030744200044041100c10060003074130b0200401030024110340944400480303e0214600d2240b4100e9902c2e184400c8180480c040e55114850301518983c20a180c0420610202d80c01021845414010b10400c1c525147c02d09600b6040900410b68800405503401d02951804c29548002c065000c45201d6144281e00208420122181c0b40007c01030759540c400304540310038001406180100702000b090000410a201a64004801803c00106e020045522910841c10109140041440c1001c40e88903071038041420b5074402ca4020040c00102404042d0f07400304074a0703c0800c44640701c1d41840200b190701c01c00c5c80c61012240d290403110030300c000a0900b001802464031112 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 969415854 1250 969414604 969414631
    0x70602070b010906050f10050c0a0f020a06051213081603020606010f090b0417011524090e0f1b0301060f021903090509090c03160509101802090316030506 68
    0xc0f20745103440340004880c800f5181750442e000004c10030103010041c0f801182400420710024a00381807c0082101842c4503507004101490701b40104003078024503a01a008001c0108000031003003010030303601500720411000308096144140340c0354003103000b0111511501501d0030501000e040d0b001540b41d000c2d55082c0c036401030b0201d101c4d204403140720950148100c8040b01b00000c01c4144a401c80d2107150200039000001d03650403d440b01c070030b6400191300c0150121701c050740d000720003000a040b2001802550904e071141c40d00e0031610030488900101180c120480600c00228841000ca5900034000301405840341e40390b8441d82c005c1d084411140d1090014490050b00383d1551040a0501c120700e5095280e00c1c074a01d00d0303c020454840e00c001d180c1d0310740340200000220207803000c00c83c0250024506500d030407200d08020501001d40d00c0103150403446501e131841008481c01c0e4000f180c01c0079400d80000341c0d441c42070102003841d040c1800c5011520f0030000b440001880000b1480d81c0c0210703070450f00c0e00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 969417104 1250 969415854 969415859
    0x10050f0409050d1121040e0f04020102120d2418050c030a09020109030507031101111501140d020307080a050d0f170a0906050711120c07031e08070602070b01 69
    0x407a80e9207100107080f94414412504820300401400140440303407411200b519585070021502c2c41c4458070b54003800c120119050000c2e00c021558250b10440d07110044225143c5600001d5031041048058020301d02d0015680e051000c054110305440b420304a0925800819040f240c40b0881d624404c10201220682a1003500b1f105401024040c1030b03608915800d54861062a03001040804030072414080f048100100082c001d02c441c1c00114001d10612030060f188900140c03506150003405850b070f401440c424041c8860121071241915502c1d060140e2061064002c10241500070344c010390f05200e0180005040720300011035100c51f61148080d5100560070580a0700c400362a02071480110300061075804441c8039030000c541d444040180003160382c3c1d4864481d0012502c0a90b48400000d40518800d10303501010002c000310955210b107140c5c504003d0241c0c19807950780d40c4c000144044805004400040840100710001c00e8008441030b07590700f00362130302c1c90096004000480e45134000c2e1000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 969418354 1250 969417104 969417109
    0x1d01020a0f1b05090a0203011a0a0c11010918050a06090506030a12032705060603031809090109080c0d12060f0303080a0e06280e0703080f0405030610050f 68
    0x1025540da40050600c810081d1603580311201480d85100c1a1005003205000540d43e46401205014040701d0000581c0e0794104180100c64a45004052440b400c4c10000040a19400320418007269004250a50f00c030000704012541e000d0030754890300c4103607445400d5001001c030310f038401c50180301e103144204030b1581e880060f0b5017034410480c4d82651513000401c0c807001003207000010019074440c5190005000c41415040744840103100361144c04161011804400c100040040135000341e011001581803e00042c0e0801c4200340e0390384554001c00000c4003280401d007094102c68107007a842040981c807128003062055541210140c0d090000b104c464032112030300d4941c800c030402e440501c00240100c0342561000d842c801400787c1640f00f2140e07a11815004941c041c8011809030304070522881c902c0c0240d104040328070800110b4180d00a2038440800682440010101d0842c0d9201e0355041d254103283c00400902d008692005416000e500100500708401c5515002076910403206100419681c0d000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 969419604 1250 969418354 969418363
    0x9010c08060f15030705120103060606120b0604060f02073303090201021c0e040903030e0d111b0a090c030b040e1609050a09080c01050403020c030a05071a04050607031d0102 76
    0x110b150400c0e803107a00390f140389a00300e0007940c5c0f102c0c1d2400c02501d071260102288016503c2680203940d403941e0350000344501a880104401070003813405007401189603480010f999407040e0700c100c10a1140441560300564024013940c001000100544a00540040d11098005070b420002d9801342e10f08540c0045c02e18041c0c42005100ca4045c4d00510700b609540d4410140d40088200c100140503800941d486182c0d1103018038a0060300c02d581c0868428480303841c01c2d1400031145114010300c00d0b115074021100c44005508503000700c13401c511074400380c00e1502049500f0001d401114110303081040b04684141c06030483c410882c4250b80c10803c0741101034009444581080382000c580f0f991440401c60703500c0320707000143c119031031a41c00200ca403c5551811020351140729040d0780c5946510402082c190148001c0c1030030a81600a80000c08256840e03c0d2110014000ea002c5020070070341e00d4044d4508001a01c000c4e01e00075001c595250303a1802c01a103542d40e078001e000d2002d0901e40d0303c004254030224 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 969420854 1250 969419604 969419629
    0x1050c161506090c09030203010c0525030512011d06010507110d0201030e190b06060901080c2a031903060b18130903050c0d02030418050a110309010c0806 68
    0x38000c5044000a5803040303800000c454550502540b144800300d8210f0b40c074414038480d00c21640f00c00355224a1841410b095980309601c00302804414001e40c41a60007a0304203020849508520101c442410f00e001c0c1c94078066044543e801c40c041c80f0000c20b40c0c00460009280c21360f6011444d0303540740e45200c01190b80e8801c10304002e08800d064078010316070f03040c459900d4095500c14100425422683c0464618200035118070056201e4142281414401d001c410f90340c011209859062402d04c0007000600007001c041c0807ca0008070008004080f071100010162191041c1a00101e6607a030121109640e5049900421034030076040790140e1000c0e010340315203400c0f100031602041c244000d208025000700c8060344100d400100900f9141180105d52240805c03030351182e10780540340d0114001c06840e182d0b03ea215041998000c1000740110b035680302d601041d044940d00003140035034580341100003400082e00c0012125502000b8000010819088189041407a0751540219030f103a00c20024000b02c1d0a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 969422104 1250 969420854 969420877
    0x403080705160e1e150301020a0f14070519060623010305060a030309050d03030906020f04150305041a0c090904060516030b0d0308090f0601030f061a0112270501050901050c 76
    0x91380d4548811080b201c583d84030a1144480a5181e241d03004a400e9a03c0000c6690000381d00e4000d0168154001c1c05800014104040c03c0d4100a101d0340d881d5610b010000c80313200c0e0009030f0000301d0300f00501ca4010344058020f092035000070312001c40b0321880300d4150324411070219003000000340c418280410f400e030840e80c0640e100c5a0310b900d01030500103403d141c50016001c1503240d011207004102c5900090111942c03030513106aa940c07a095000350381d010328000c170030101418001400049406d40c0346500c030748218210a8402900c0f41c0f0a9052584681820650070200040800042c0a85035000034400c0c00f40b0b030403d1510740700003e0200d0031500c01d1412185c0c0414140c07844000b003417203460900d50003c51882107894040510300c42916150003607000b2502040007002003400c11010303005080e0400c55a01421410000038000600550b00f410420300c1030780c1d510130a8041c10034010007419982c0710700c50200396030328081d41003d5002c0c090032038007a01c0d15800c00b0040703410480050222440520356 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 969423354 1250 969422104 969422131
    0xc0418020a0b0f211006020d0e0f0d0605090601060e0a031a060402070b0c03040606090209011d03030f071a0f0f16020a0c150206100b070204020f0403080705160e 71
    0x10300e075040855410042015841d942d00b8802c145441900756a28150f851681c0c41c04c1400b490042c901004000702c0f0740007442190040381d00f41010f41c3e080507000854100440b60071112404030008110240040c8001038841428801804082000400c40c241651b441d9070f16122030044600c00d000701c101040c8401032124800c04e45041009a02141301a004180100302514180960722041c030004030954051209080002c180410404c041c810346000b80b002103415424080d0f0540040d0070385040000040030b40440c290700c08075a0780c0500c01c4039100380c426001c164845400d030422210070070b450100b0510510018021a01010050388010322030b0402000690700c0703550b85d520100705110790100e04070a51007644100000510161a140050300d404d000c00000c40d90304040091901401a2000740c1d0040c0c03107001030100c1081081298100c075015200540d95111803030414103184144d9001505030707400403130410204500400c1e035046014072111804000c58854100c0c42030540306444070300d0f0140c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 969424460 1106 969423354 969423359
    0x3602120f01051303091502070807120303060504020414120f0318030607110c0d080d020406030b0909010605010e2b03050a410403050f0c0418020a 64
    0x10044691211215180600303c00d411b801082074105c018030f01d007100540200a90802801c0e0401213690041d501c86c00014589407008040f00040d04007800091545401c0c02603400b95200201005045600c0c1c2081241601c0b07600300030181130043c82396076125168184017422813400b801d90003034200c044039803c050400c2c40041c2140140503080c0100c0c009030300b0028020026110591b922400a226800c004845010b01070408059a00028001c42c1c020391540204c050701c401501c10080070345a0161042c00e0717480304d000351400121159060b00351031401d03400c80c0c081c80d81c0703403609104010701c800d0a404c00016010003e4000c504005480100136502c014580300038500c00c500040c0c8211840740040d59441c11060521806040280300d141d001c0610301150000c507072240031101d0703c1c5094801c007611400c021700c15a2155103003800c00c0341202d6030b03020f80c1c00117140d00600c485140307030 = true := by decide +kernel

theorem cover : BRFrame.Cov 969244604 969424460 := by
  have h0 := BRFrame.cov_init 969244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 969244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 969244604 ≤ n) (h2 : n < 969424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
