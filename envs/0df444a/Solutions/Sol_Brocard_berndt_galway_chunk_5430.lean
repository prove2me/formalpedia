-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5430
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:50:36.794881+00:00
-- url     : https://prove2.me/submissions/cc4fb99e-0ce7-4ed4-b003-489f3d2df804

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 976438848 ≤ n < 976618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 976440098 1250 976438848 976438873
    0x2040e070527060412110301291e1c0503160c050a060801170f0709090510051506070206210601110610150e0a08101503021807170c040512 61
    0x76102d03c3c4152044000729121040511a11261b010751910010700244282e2404200586080080d100e007603045d110700c0180f500c0700313080c0450a8040e0200e1003400154030000c100420140c401c1403070080750068421081000060001c0c03016088070040c0145554442c405450300050306941034001031300030b00154804005c00755008030300300c0c1150000300d580494030301a858100c0c01c21032500c51000311032281c00400201c0c6001c544c0881500c0c4d0285054440c0e520124451000341d5201788c8901c9106803610702c1c0751440e85480402059078500c0101240d01c0c1a80d01000c94075260506c8185002d2441e50504100f21942c020729059440c0e00b15001819003440c02c400301582c90501c501a010b02800d0044c62150007a00901101d050070b840244424600c55403180d150341e4900b0040c640840460602103201c54078000c2c45400c1c01665402004500e54060300c0c1c000d9420044002c0c01c0d6010401a144003003409036030151580d001c1c075038400c07285a40758100400d2181300c0b03e5420142c03031942c3c840c0050303014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 976441348 1250 976440098 976440109
    0x41a03012a0809070806100e070507020a0501080601022e0b01140403200315010f0503030705071809020603070207050102010b0909193e0103060e01061202040e070527 73
    0x40340d421400e10b0b49440d2129841a8a00019500003a40394030407001845822503141441c2c801b140c84408000d401c666682d0030455040c0104207000350029405001440258012016640c0c8004103104030798450800303010410b1068100828000d55490840c524900c114540c0a96100184282041c9680412600c0c15455034402c2e4440a003011040d4038564002c0c600e001c0d03200f000c25000600700c81e42da50703200b2110358500c0420301c41d442c03841d4a002c000041d10300b804000e8400258000c0040e000c1c81c4d2071f040c2a10b4460b0010b00301700000d04e07690424400140e0700e80d0f01941c05495982d008003900b500b0b050000e82126448549140b0a00321041003021240002445400c0400c40b2010308190300251314000b4400201c020030221303a0150f000b8401e1070313a070701c242c042e11034031000d1404040103815610044d4100d6003d405201ca5141d40600140213035400780703100044500e000c0b01c0c014645a590703001f483c0c0d60707241900c1080004030006031800c220003445031242401460165150b4034010003100107203 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 976442598 1250 976441348 976441421
    0x2150405090109021e030a021b16090209031c05070605060405011401030b03100f140a0905060628090606121104062706020d020f07120602090f041a0301 67
    0x10b01c3d290300041e00f59140003090142001858140340d4030342c0c5a0038914440b0303001e500b02c50700c042d1020300702156004a903100010445e550410b00c0c00c18000060816411001a40c041806550548036104134010a0758420903001c0c200811682d0300c0380c4450603460008103032000646003600caa0701300340040c4060401800350100c0c084090034009994085500464100101480044041440c080680240c058940c0140780c02c011503800c40700b01ea0b550600490212104140081c04690191000640c0d9040070203491443e0203444c1c1c2d090101c04440401c40c8080715041d000141070340c2d1240d00420000c1d4209501d090f00068034141481108000101210540210700c680020490340104d1011400d040121070301c000460003034060610f645a0001a59070100e4601050040c443c0c0190a05446e0000c81d1810640300ca0510386800003a031902c80d54041d402c032001050b41b241821503010700c7c41d078462040615242e07000200c10b50641d4264101800c449204003100c141c3c0107103138204400c0005052114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 976443848 1250 976442598 976442609
    0x4060801090e2e15140612070318060c120506031b24030109060501170f040b0601090b160507082e061220120d0c060b0a0b07021504050901 61
    0x1000181266a0408010003c07160b5955a16095004120482c24038465041d18480280005001e07540c0c4c1c284400c9114a4055011000d1407202261201d807180e0040c6d1070100a583c803010f8400e40544920080320100e800302008608142d22241c04c4908600806500c04c004601502d41c2e18411300c00060092500c00040f485036a90516000d1144044440306041d24036060042d034581d0385410300607000b0135003401454042030100702501c000588007500036108401c40780350801e69427100e13615015072944c054503072414000e0b00100070480c00d0444c8050803804c4c0451138144450185420124140b56154000e009039802003594828941c540e0109009030208054201c0c40100a080c200e2008041c560055890943e0008c500d20038456084031410850703005400c6a090300100c0c00c10481c80802042d184070b103c0c0c00c40300e00b050009020320104132940e0b00845c00410064000700004845c00840d0f00310040c1e20101246010540c00c20302c0500d4020050a05220b207003d04080005280270340500c1203 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 976445098 1250 976443848 976443883
    0xb0a14061c15060306030b0c090a09091e2603100506070c08030a0503070e220c0924020106090b010207151202030c070515010e0a020a021e0304060801090e 68
    0x200c031040e00c01507002c1494101c0c0c00c81150038094031040e000300a40050321058510100d50b5000c64400d8070417108035003200c04001c225280646c81c0201c9600940030b1034006417040072039402c25070a05401d0800a1032a548103004800c00d4003840d040102c2008035486aa0700e00320400c3c410410350320311940e00c100941d03d04903000d9031219078602d002c14000207150000c1e03a0901001c640030f804541c2060182d4099400d40d11040c448115040030312140b1007410006043d900300ea0111062440703100c2d841340e40800e0359032406107a01c1d600c500b00c1c1000590a4050503410f100f903a6074107400c3c1c560a10510000d041010014448103242900003981c441c168050401185c28052101042900640b586e503020381d20303d90190b48a1501000c22070540d08050000e95141c01140c0101008041211109040c0c40e42e020705464952500e05d0b03894000d41040c00300d60150310500744900d08001d400d42c1c1c03601090744440d000356615800c00200a010000680c0319050f4581060a01c5204d41c3d00407865405082c0c00300d03207 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 976446348 1250 976445098 976445137
    0x305090d200a030e01092c06040b04111b0703020a0510050403120509040b0301180b1008011e0c02060903030c0d02040b0d0e0105090703031e0306080f010b0a1406 71
    0x72441441400354900040500c240d212a80c1010781001d0603440c0c0140c262030f42d42c4c40075030303070710120030f80c00d10030311203514090282445081000704220100307812601c090400684446602c000c0780440d410b1001d44501c14501164040e01c2c003404131154000d0352000005407290a00d16404554226080c4c02128800c0c42484100842c040c03003402910000d64001c0c0030268110500803001c0d04d198810031500b07004e0350910f040d0a800d81014000e45210040c45800d45004070819201d1080720705000c0e01f88034086022000c005440c103000d01844076980300c051180703c10a145000d0440454401c81c04650a54011400f040841400401980d50100f4940c018954030b0b00400f0440c2d0007845190008885034a000c2181c04804040354007201d69800240000c20541d162104055075030001880020001801500c9021722042e01c11002e0202c143c042c1404114603442d0380c000b034104105840d4030030f01695200144003179031030543c041c4c46c000e21200c5c0b00d40c1140408103011070031512440c007920000000400c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 976447598 1250 976446348 976446377
    0x90106140d021b07030b010f1a1608190206100806040c03030f1b12110c03070b0d150320101428030906050a0513021c08280305090d 58
    0x50f180e8200368080c81590010b640781d1400f030840301e600f0b005d00321111104841c040b504911840e03400d0380700c00c2e024074018281522610188501c100307040342100c480b40b040c4001c150303007001d50740242e06850980c4c0180225103440d10700200c2d8041c0c186c1c0a4075941c2c1c030000a000101b035001e1680c08c05c4e03036010b140c0014020f42d44401030b5880c60000f00c68110808040e0465402e01100e00414441d1800c1075540303240b00600c000c106031741c807a2800c04081e07040d0000b8104004810200c40245840e0414000202c0d90459034500d902204015034800c1e2043c04030020442501c86070800490f58490301100c2d070400760041400024004148001c54000b8200009000f46100d412601801d25404080061400003600900020003800c501031f01182c0f018101404581141624064144500705408030311540c2c400c6502000001c603001c80d03080000140c1407603404007141d00c810041c0a4080c82c00340c050440019007401c000d01d2000745650b00201881c0c2000e1200100000c00d0701e02144103a890901d92a02108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 976448848 1250 976447598 976447627
    0x3050d02070f08032d010b09150d090215040e0114040e10020d06090522171908010501080f04080307360b12071407050d0c02090106140d02 61
    0x14940544120b4950940404000e840c034011442007111801101d40711080084100403030020780192404449002c1c010301c072403c0d418000c1d20b55840300824255007205c2c80e004041c0c99034404c007545509542c40e00c10304810b604020701d4182c1c050200300142845c05284c103410040110060250700c1a640c00c2054800c0c007560740e270300005842d0480b0001d07141a41c1080300510300940c004041c4410031401d00d02e0000f01c600381840740510039940c11004200305246030342c94601d42005103000300d135481c0350010346405040464014040c034040705031500041e20f5510138041c00091f0168400d5041060781d408024602c000b8504072a04a6030003a011a16920b440d20103462924103806008210070f1000d170406080614480070b40b102d420500010f104940d11a040080580b0a039080240361800c0c84010808a40c070030600c0c0840c0b13600f51404c16007020b8656403007a023070419048814002071100013180e400e40c94000b03030b0716006100c1401c00d085850903080c400800b0b801426100e8510680c0420068060b5192 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 976450098 1250 976448848 976448857
    0x21f080a0504170319050a0902060403080a0302120c210112030c02061c02041706270a08070308040b0105060313080705070914012301051b0705061902160506040303050d02 75
    0x5201d40f0307074036451728009400381d1500314a2183d000c18105000300d641c0008034031801240d5900504000e00e010700356114180941d200525280416508104030b00c80e4020518940c0c3c0546440d059a554440b11211649990071700740b00c1e0380402e880d080b0010000380460410f030840b81d43c2c0c941040c4c0c243e140140002062802810580c0542c40500a41a64140f104ea40200107554440602a00320080c030540b03030f41e840ca0111201e215081540705246000140601d0070a4070312558000c44a18046a81c2d170140642c006403004c45c0814003407c244000c0103a980c030f03a0f90240205682e00d504524205107000c1c0000c4d046c040140c06c1e02d40000754001400402d101503000f800f118503061281d840080101d140c804024802c18003001000417118551190310b00c10360003000d42c16940d0500b13150b00d0005090780704002e03a0070030100c0c5c0305489000810f51101000b80020490150940c108003488034000780c01d00300d540c0d4030990003803001603040c0b00700e60f11001910241ea81500c2c09503218200c16052400a10a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 976451348 1250 976450098 976450133
    0x13060f03110a020f070815070c080702061206210c060d0e071d0a060612050612010905030d0e060f0414031b0304030c14030601030b060609060c0a021f080a0504 70
    0x50015082c001c0c150002980c0d40005030103022201e1032955616a5034480130005040066011003901052071180b1400c80c03100740900405e000b91400c5540c2d40041c61540c095200441489220030401c48286028196140c14000c1140380c0740d030380c010314080e40751104179643c02d00f03104620109401080741c1b0f1550020f01100c001400300d462035911170350741d4501504624031020a14820308001918290b080c013400c4111009034176545c0b2010041c0f4001005014000c1c80580c01860758612500000801d001d00c5040d80e000300080c59540f10410815019500c0b00c5154144d5688444284036018060881c282d9015070050a0154041c13581d41d5000e00b0340c418502490307448080d03400030076a1000088000e10031130388689502c0700c40d26550914002d204129081048d41500300c140100003040481c0800c0394440b100422840c40c0002c0f000000b1156000501405a95401a01017030214202045149060754070000d480690343d1208100501002000303050b80c4a094481c1c01080400c074902004242c44213 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 976452598 1250 976451348 976451381
    0x1210609051c0906050a23071a0610020a0204050403020a0b01170606090c070210020313090609050a180f020a0f0b0315040e101107080301230613060f03 67
    0x164508140380c2e40c00511852028111184400220141c022600f01c4221203068840e01d003040d0f41400306079694000381280304c051340481102155104002c000500701e040c4286001040d0020036008905105401084035004403009414100625000501c0300148c640c11240400d9130b41e03071480c00301d0812100b0407005002d902c0020011407c0c03e00a007900b143e02204504854940d0b07204020441941020b440f5006921070400004003d0300b004810062100050b00480e4900441e007841c480c12000036501441445079514401c0c86983c205010703040e00012a41c1090190701750340c02c01e01c0911503d065009081c04a03100e0000c00b1903c501080200400c1d10b4640f44800f00d80e2109000c2d015030007214000401508500020118a850700c40d0180b01c101d0140104120200d03000804010303c9078030109101c41c0024000340c00001d40c85801035028100c011084840c03120307141c287d07131403030019200b40500c1800c060000700303d046a81050502221aa8900501941080d100c00d40003881400301052065 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 976453848 1250 976452598 976452611
    0x7091802031507020d020a080301090c030b0a120302010f0525020c04020a0809160602070605090f04020706022203150c050d29040207050c0111161d090604020306012106 74
    0x55980c0c21026100f600c50340c0036100d12940c0054100d8a445200c6002007642d5414001441007500781e40c03041c0701100c1142000242140703041d0024030b070404258401c406c0e81a1000c4010205035081c0204a5070144101040c0440d06140107100000e59010380780d036600d141010038030396142d84204100c803042e0b40c02038421991010464001804044100c030041d44c0e500c0340c047c02e52801d00300c01042c982160442c1d40507014042c1010030803103182d80a500b00c80d511045d90780e0001c0d800d0381c0c0e610040c0030842c03113003200598856484060038111103a03504c10038409240c685c400c0010442d5607480351141c24400c240001c0041c5141405c0c0e0340340c012085040d07000b40c0381c01c0003446a100c0c3c039605103001d08080d5800c10100e4286408001c10b901c50108010901e40100c983c05150754003e0325441c0c2d1250340e00e401e95081001d42d1240b450410200c0d070001c030079400341442010003098401100b5812014110203002c50380b40c80d0b0080703a0394507018401d02038054900400c01002c04141b16902d144590f1207032050000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 976455098 1250 976453848 976453873
    0x301150504090f1d0303090c1201090c0b070501061203050a050307120509010f0b0d02060702040e0309090901150501050720130e010207021516030f021e100c080105030709180203 78
    0x410880428440741390381031411600440380002581d01c40d0030700ca002000c0c003134244400c1c080c400c501928809001e40d00c4240610010303d0010003d8064651906825180c0000d414860300b542c42651003100c42280111025010a902c03a04440d401d03501c07400c2030350303594a5030fa104a59492410a000b04100d1400003403200710701064001100f040b1341c2d44014481c0d0360120040102c04da01400c0c000794094820130042c0010300701034228500c5ca600c404207503418908450041524034038103c4000c1426590352109084074484034440c40090402841c0c080c0c20100c0360344d14a8485044000400d280030344942d03200510f665401e04091003480d5030542131040d28400b160682c040d401024040b4440c110401d40e07400c0d042102c9040d03410040324040320407111100b54038142d843d040c04000c10700440c05500f51102e403202d40100340090a4403080c00170305405020300c84c01002c585050f00314104100081c0010041c6a0f00013441c0001e0362906440000c02412804a003c1012407040000b5014010140c44282 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 976456348 1250 976455098 976455101
    0x1608040528050c06092209080a17090309150903070b190e040b2b0b01170d030e1b01091203090f0f0b0307051804050f09210301150504090f 61
    0x607414852402c5840100303050041201c1170040d0301d44540c000020204110030002100e1241d02d14040c0c0010000d03842c45c0a403078014080e80a0441180030921040b02340000b9442d13164502e1303010301e0040245050201c030f600082c07280c6400f5000ca000c1c0b4100420022825a4213101e07030070003800c0c012032442d0f079404404400184031046000007030110340c0f855503810050401e4095401c40d524010503c8111000b51005c942d00440c0c42d08104806660390510034000032000c0d0346403130203070207034280300d4015a0548250070301c0c0040c548008810581010000e10b0102800500341c7c03031034030304448035400000072900100c40c5072105070311030301c1c094480361003d9040c560801448025200b0716103080302001d0f218030481400d48500e100c0d14159401c00c000080003940b040d4040c04e00000300c000880003410b05200014140e4200b9100d030a0246038450034083c5900b0200000d8001b96010010b40000a40351103030540700f408144030708082040d0780c022209a0034420350841d005800c24800421140c249030201c0030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 976457598 1250 976456348 976456423
    0x2180a060801140105100c0f1b09061508010e130203060f0f01120512130e24030c012f06090703030207050904150b0a05040e06090d0816080405 63
    0x201c0c2540782c44102062140618611410380e10017924009040380a40412a00080a90300035a001d000c1c42c85200300003040e80c040d4100f501c2c000f0100003112820040c005040b980750b50700c040070121074402e450540c960007071607207411100b4084000c00550b80d00fa5a158004030b800340c0007540b501901d400c1051444003140407900849251410b6101360f03803119940740c4034280d0994042c0480d84948150510241c640c002000d00790b140802e80580c0c1640d4084103d180b40c3c0948002e802000c1da01c40f580c0d50418420036241040d038040b0010004611240c001900c415541a0b03107c6505505c400c001946002200001c140c800e8281c08450721072400d100e01c142c44016901044005000e425000602c514102409601a58110002044001c4441d810300002c05005443d180c205190800c006050743d15445103085940c2d818000e00060321b0134003000d5003401100004074050201000038030405481d040c40f0241521507509142d22943c4682c14005d251030441605c2000084421202c00c0d20260a0742d000b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 976458848 1250 976457598 976457609
    0x240528121b06140409020f040306060b0702040c09050a0605070615030308180a030818070e0a1d03040e04170c120403140d2f0a1a0a02030609040f02180a06 68
    0x8000703081e00d0310000c41d090408603600d4a2032900a02007801000e01c0355004041c0d2486003650f0514240d43c076900c00c030a8509641c04000300317000c040303035003015030920740110b070a460b045103000001b20b42000005401c045060003080100310f00880d00d242009030365801071030303038680c48079052529581d24a002049500215800d0400d0402014400c0c0342610000d640294a6810b4454020030341c2e562204001d40c10889140c42c00e40d210315100000c0903440d41c54028000c81da428000705420006195100c1481103401525606500410081201c8042e0b00d000d0b03038105511407681400708110423070405050003140d400c800e1b503020301c6882c0030010542c41c0003401160b10a030901444001c00015242c3ca0b18004c0010102140b18115440c2d4030084041124000f03026040340000041c207000780c41880c0c03400001003284e42c050701c80d583d031034818100740541d5806080440d042d89140782104c0424000c00d0f010384020300002d00c40392450210b650f00072609440002617191503d4074504042910090465407044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 976460098 1250 976458848 976458893
    0x18150c0304050a0e041a040f0c090608010e150a110f030106050901120905070e070c05060109021b0d0e0d060b040c080412030c05030606030414070924052812 69
    0xf03551650300704c036144a55003000e100b075a150210f0131084142c18008001301c5081da0413070b54030000200e00b004d00c171000d000000c00c00254141800c444608460b0314107000c032115803211000c0c0101e0380320340f080103600100c10400841c000d400718070740303c001d802140c0c0154064a400710011954031b40c004003030700c010102683c03650681c601c0e1407a4003084410081d4060455000800103108540810740060b41000b4a0700c1e101d003484d0604d172a100e042110a0704030f100110340004201e100e0741c402c00c8c001d45188186001030800c0b0030407082c02824004000c4000c60107203083e082944180301c0f0301d44c800681028003900a110360b001140009150040849045030780c100020500c07980c6510a20501c01008419210180356483d441c040000503040200115190070300c42c001d004103840c060103010000c052100d408140902004011034002c0d01500c40381014400c1340908200651395a452030940210907405054480c400d1030880e0308402e003075044552030340502020340382003100d507411900c0b41d01c00c01c034013 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 976461348 1250 976460098 976460119
    0x4020102100207051504020319051e03130614070f050d1e0c0f0203190f0b15010c0204150801020a09050f1c0803071e090303020105130818150c030405 66
    0x11040203d004840c0d024019510003099411001d0134108515082400181101c0340098044051011711030290021601074205100389010b5582061194549014001c0910b05083d104085654507460714070440003041041542c50b41a40014011500850b4101813428505202e0341080b030741e65078180a06100103156000d040c031561183c0d030482c40c42d151007a5a010aa400720b6102ca000b0242c0d0920243c0e41400f440520300155803043c81d003d0321140c410007401c0b042c61401e08245000510040c00006491203a8407501800c0c0c6c0e03c4001d0003901c65044070002a05244c41c801c02c030301c51603190489003180d031001a075420456000f03200c0e041182e604440c51000d044100d41449040d0b828070344480f072055121001c01000804140c0079585c000140d161440081a00c070a0b2400c002500701301e10000704814140600500d036080c002d032a4011030105050114000c6a569801c0910404003840e03442c00102d5011040c3c3c2d40c60003c0d4245a86280551580301c2c00e200c1310403601ca40c054860140301d001d4400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 976462598 1250 976461348 976461373
    0x80601081005010e061e0a0c030219020f060f073c020603010603052d0601031a0d030f36060206010e0103060908040503150f0106090e0a0e030405060d0504020102 71
    0x10103070300070b4400c103035140401051000700b80501c507041414001c0300f00c600401840450003000024000001c1140d40350b40742c42c001810040c3c184803a55299171001d045004201c809600c07600744404030314009441c11640d030724420806074581c0c000e80348000c001d0520700015a1199101c668980003608054040d400301c0c0c24074000b1510100f04401c402074000009000410066010760b1140d540507100e000303194403000038031030503032400c606403203401d0082d40d08402400381c0c551303041c4690380e0b41030b290880d0545500640c800049601c58409001010002040c40d00c0250500ca07150703840c141d5844a43e10801c0c921440c1c60310b801a10074412512401c142c48800242044c80001c01504070791a80c400841240d0841c3c0700c4901a00d024002603900c200e0070000059141c03020818820400720f200c144c1101414440e10081c4a00b0040c0d00a004100e402c0109004c8100703140c0d070072608216807042c0090380356070303c540c120f08500582d40324590008002c10112031607541608251b00c114401d1b801d4548800501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 976463848 1250 976462598 976462621
    0x60509070b0a0915020a050a0303090b0c1c050712060e0f0906010b0a11010b06071109070e0609010810030b07020319140d020d061e031e0203062e0608060108 69
    0x1241080001008090f0803ca00c6450902c0320303142c50300d41e10583d20400313501e803521031416400d0141200040c1e510f114420900080484064204110640051400305140f070800601c88024041a0781d060ba5400421481c601510428000e240301c8281802107941e80d48013080c002008580b00701408601c05c000a54804003c240c0d135060f00e1000f040141005040c0c1c40c21205d02c00c80c0a0480020b41d03842230707102403a0383d034800584080c510886800c144c503c000b40c2030142c1010060700c0031090001d4440072078520341e181000e41d24001c2c0f0a18240c801561154801c0301c0c44080344e0f1003e41008105418029840e6000c0000c050140c50850b041010b05503444049522105441003030341240400d0042c0700084805070020401001c12840105550380ca41103c1348118158908004188045080030410008104070803010030401d8009c841c00340700541c01094450390010258034a40c00e40c0750842c80d4010650803040302c003010000c100708000340c841c000500380e010183d42c020301081c1e00b040040c4100d03222 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 976465098 1250 976463848 976463857
    0x50a0204030c0314070e15010e031b0402070609020909031314010807031a030d0e030f120306040c0c08030403030f2d0203100803070b04020f0604031a0a0e0109060509070b 75
    0x8081000c1140c80c648031000c0071503454041d100c13140190300700040e40001110740759015254080380410100b410900140203802420013a5000fa004810702e40d500c00c0300b01b5840d01c480d50007039030056552812403030500c0040840c204029840074410040c0004114008058000a00c85404960585031204483c001c4410b41d6080039000414920014036481e1094000c19246905001185d1400c41c00c440041e003805042c2550300c00049101c0d01700c032054501008008503409000000d81550415140d50070514031004001d68020360f03c1c0c0e007400d102c41d48a40300d01402280c10001c000c2e00c074105454000c019140102581058506108000185004551481030010740072120718110025601186011750030081202c030307107580f5030500052032010074002010031034442c81822009240620401800d03030341520403540140c505000600019081003120a0411007501c00e000155503a0400500546071041c002c1c0d1700b950030005040308101d00c40e003255015104006c2038413030482e22804428524081c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 976466348 1250 976465098 976465103
    0x80601030c0f0f0620012d020a08060d02010c0c2301030221150a1814040528140303071205090a020d02030705040213060f0504030b071d03010e10050a020403 69
    0x41c14800300030742d0b4085d2040c2080c10070880c48060480c1101c90b02c842c2150b514502042c401c5c1c60b40c01c0c0304c070080c0c1c65400980391201c641040450808050000080c80e84800401075030041d00002518000e681c050000c0401150780b2003c09e5280342c2d121104800310040000580610702a0000701c0d040d0b56000303000b81c440804200514299115101041180269020780240b20091040c5100c02d4140c40e2202440042c0850000b2800c1030320846500808843c0e2403103104030701075501018040002c030086403035a880c4012102a120300b545c2102c50440207048904000c0071a140504114480740021001d14071a002c60b4860300e850758403403030800054170411110300c5020380060b0007100061078004070030f207a07050014044904158032032010400300c1e03006c19074081d0280c0303042c101000703000d034082c0000c0b04400843c0f41150815141da6500c201081e00030b41548103004080138618003c89002003000000d5000400078800c1a441180341a19800d10803044848182420300146e51140c6074000c13038044a6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 976467598 1250 976466348 976466369
    0x63809070f05180a080d110105060607020d2a090507020607080a020a09030501110306090c040303050421061104050a1406040e0606070b0a1515091518080601030c0f 72
    0x59041c12180ca074007005104455803020303050781100c0d40f0b45200750000340c070070107000302201d60728802c024040d42c0004010000d103a04260400649840310029551216810341d0324450070f000e6031030203051480300d02d09400420343c51030410041078041c162682084443d010000c00568a50a4040380c4907901114102c0210f50084041208241e26600400d075010240c5040341d44d0781e460341c0d1420700359540d0848805030640c001c014401145407072004650041e03245105145000e2448c1d03000382c803a01940c854103250009103000e80801820305c560150740176a0141d0200100221541007189907001401001e001d8030100001184400740104490b010381b50040c4503a00706443c1440c13401c480c19000300601c2e0008010300503040024050302585010f114007502c080760b0660420747c04078010708680d2062004044100000400c1608901c0020a50701943d0b0203007000385003148203455084141c0314005401c4a8210002442880496200e060f00d22130f01c0b189906a41c1e9030083e50041c0954040d654802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 976468848 1250 976467598 976467617
    0xe010c0c030e0d020603180f03040e0406090303061532040308070201031d03040303030f02031905101d010806010512100f0906140a1409150406380907 66
    0x64000c1c41c80000b0800e005041c0b00e038080342c940c082001c5400c29a9140b0b41c50710340822448540006000d44044940c07144011b50812703103019a01c001d00d800290028140681c1d0303140c03140c18184241c100d40040e00742422006d0000b681020000c240c0c40f80000c11140084603c90b404086114004021218414440045040509607143d200b03280e484008224181075841003807d503021018042d05d0241e07400c080145440303601e035050180903144a841070400b80e80c4100204131005c0c1814154503244651f403280010340d03580350046500c2d07142c4150802c0d0360034508240644811022405664103071801d880584109076a200280300e0f1140c840075100741d143c0c02a6544418900d42d07940111401001c0280202d001e00040d04d0b000e0495200c5c41006050381414070411101000c43e019440c00d511410b48075542529101894507110040940b00c010721b111518082824420543c00c8400140c10803d0001d80c0c00c1c2d040c0d0502c1b43d03807050080740400080114000d20b4070314034104241621580c22915101d224 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 976470098 1250 976468848 976468853
    0xe03030f3618180105091507171311190503010e07030c061d0616021c080d0f0212010801060302013e01090501110414150919091e0e010c0c 61
    0x1101c1d00144800540f0b60036521100008009018690181c0c0e0100081c0100d90300a00802400c40c50091420081c829000c209038039600306051706035070104103c084285812550316220300c44020b0684c181d1381c01080074810b002514014070400c0c00300c1d40700300e0007002000001240c640e100c450b188000342c0407031303041c4008000c40c034015021850003002c00c0c1741d50000031003180002441c81d0050074040c030b00c5000d01d960b0841181814105294048690448080c0614059452203810304c20f41e005541101d4440d80050a0f81207540c05035a98001c03145603185556840c0e0000c1c40c001e102d076100583c001408124909a10308040302c1c88180204010300c00301da610005114001e56a0a412007035a9941d614034010b030200e0001c2c0b240c424500300220382169a02d2501c002500c208002e81486441030801107a09111150b410013101c011440c10340300d4030151560f0703401c6208419010750000c10001e040a0002c2040c2110140824500c140694100075560b8900b0a61b42210501c907888404209003603200c001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 976471348 1250 976470098 976470139
    0x106050901120204150803070605040c06050c0706050f1c02030406060b03220c030f1506050303122202031009020405070c0209070804020621060a1e060e03030f36 71
    0x1241d0101c8520175580d0760385c6110036895540910300c107652183c0d9070414001040100e1244200402403403900d9800e0020900000d51140c205d44503201c00c2c410b000a0074218205940140c81035414500b80c80f14518a10070964400f03940300302c4003114510b140800224150301d11006603130081e420f800705c0205481c0410040c207034104640d039066a2a032a0000e0010000b207400f0714440b8124464a88282d464135886188015145550030040c0300c1d07002032060b00038009100f400b056104a07044007059203a40c0c19042c0c4420031078401000b039014098406100d4449540e81c03c0031595520a650400c00b41e607690200b00c4201c04c10a0740254403550303450100d0f91482c0316000003500a40014030007464036a1406589000c0d00600120f0141c0340703050800c10540e0315125008200600d07010a0410400710310112403601c0075020b01411060000620019615480030401d541c503010320030703441c150345040d816040756424010050f000c00581c01000c10480d03480c6860b0303c24114440c054260440800404400d10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 976472598 1250 976471348 976471361
    0x1150f080316081e0c0124060f0e0409062405190501121b09050108060420030a090501022115011b050c180601021e0709020a020309090403030e0106050901120204 71
    0x204d100074800d04006014140060407180801c0c00000354018481102c0001041500305801e01030180c08420410b1a0f00000216020000d81c50b0030ba1120704410000380c010020307504c0162019250451142c4020b801c0c0300c10056405031442460051a0b64608200c04101402910410540b07090030802c49540600d84c180f12403501c850001c2003c1c580304007106181e02614106800065003040c2c00c200550300004069044a4103a9091040d0002c3c20700109020751841241c0c0050703680040011140b1525a0007604d0b4070307074410020340d504d100708202c000108000c6201141d0246e583c80216408004020700d40342c2c1280113131100c6500c0e00c0203c1d03002285101c80c80b000e0742c031402a50010641903480c4102d0500401107664001e5450801000080c50585503d800d03103114031503030380801c0e032540c0d0008140040750048100566031788001c80080341140034100f05030303400c010b185082c041050340581100d900100c10034020042180d0705d00030480c80715405e204040d034081c1d8001c40e00c409803c0503000b80303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 976473848 1250 976472598 976472617
    0x405040e010212102d050906060c070b03010f240e0a0f0305030a140304030c0b071e02010e0c010e0f061602030304230a15030e07050301150f08031608 66
    0x60508000d0f2004940d6140203c401409001e0381c068140710040e0001c030070010112955151020030041c4503404544111940240c5100740442d10010322266512030407038901100c440700391001d06586112000b1160420b004101d21102035407808903694025918620540f04911807032000b1058010007a285400101e003044e800c4070045402154950725000f890f4011341c8100001c650760388816400910020044032480d004000802c140300109900040e442d98140c0c01411184060700d60503815207a040c0241d03220241c49451001d00c045003038041d4001840d60b1880026960020041001111070260112a40340e000110704901009410310b01c015003030076030384080f442e80c0209072a0002403644d0003d03803000c000c0d845c640250300c01980707150001990854090300d0b400e54403404d05000750394808400104d00201a40d07100c00301031030a420000c110007040c018000700956040340d002c580c6251014011045050081880044c0301500001190074406040c9505185151180d585032401d90080104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 976475098 1250 976473848 976473851
    0x2190e15071a1b0403030c1518061109210606030715270803071106040f0b090a030c0602151f0303050c0f0618010f06050906010e032107140109080405040e01 69
    0x240c1d03003c001c10001800958080d486d2950700240a1030701c2802c104544440e5200c540c10505a9602c03e00360050414005905c1000402e0b030260008913550341e40036180515601040e143c12500403804100703468041c650718107050b51032079507450007415034402c0c5038031960130901c1c004c110107241c41d4072400d00758404000b01603040e5201c1c220505a80c40c50000c54101d080d0a4000254074401c01c50000405540300005030382490419150052008601219106070303020901d00090f101059520610000e01859010240c0c03240c498503a40000d507100d03420b40012610310310080116202d107808070f00a5081501ca008a20310645c1980c1e000c4840ea0001c485d2181a8420840c8081d1500d106104d003a00c01d14030001612105d2000c0b0705c0c0c003829561001e80003000c90f8076060081c03015031200e405480c0d00001c2800e00000100504000c0b034640243d0000305051124664410001c134003a505c01401114040c0c803580311215007002009007210403104004001c1441040104490300345508580f117050040b100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 976476348 1250 976475098 976475131
    0xc0f1b0602030408040806070c0b0610111f0c02070f05060c0703061b0e041a09090a020402030c070614191d03070309030201110c060304140102190e15071a 68
    0x4603081641c00030385003110b15030004039003070001986c20483c8070740c0070200345069a418030461301e0340c90302c0070780143c440c81c0a030b0002c210001c1c0007401240b90b51b000501c408100d4100002600c220030b0454828030700083d1207030410303240105081c4001281030603113602d20b402038110b52034103081104680c40940c2840081c085e8203000800310b111440b8041004184a4132106800404a801400310f08942e02d0315100b1341c90b000c078000b000007003a1401017258005480402c61070b1102080107251440200009501c54000000c12500d2030f034000c0900701081c480c01c401d00c500b042e02c01c44064000c2e0202c4541c00c542404e41381001c415003041e000007078000c1d40107110b5203d4943d040090307411a84071113000d40c04584040000c00441d68051800c8590443c59000340159a25000006007580b0010b4000382c82c0c00304044201511500a5045588211b0540c120540301c00724040094040c9078091010340c0b05900000c000b815031144202111442030340a0101e001c02c6000100c410b038030100182805450452241 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 976477598 1250 976476348 976476353
    0x606070c09020702180702011e0e0d0e0312270301060e0f0a02070b130b100503030d0e030910111507050f0a030603050d0c06150501090b0307031515020f010c0f1b 71
    0x440700d078000c4032240d00110741c661041d01c1242c12603c0d150700c4182e27070514100f58180030031800300349180070640074a046a060503141c000030b8509007081e09101020b103000109030821400c000440c5c0c1c210141400041c03100071404003018200d490070b10840c0d0144158ac0b00040c050221078030202e44c002080d01e401410a001603e4864400740215502107011010405000a20241a03c0d60740d1026000040e100b6242c01e110100ea00ca00980a0310984962620b03510a07002d2030a03c20396003420301c0074003890a83c40360b84500400d80c0310030300c1200000740100c241303205030a6002441a8490030140c2c480da440c01e04004550701c030591107004000c040550702c01000c0000360090084900c03171150f540e81c400a0343e189080c698101c5860700e04203807511010880c20801d903604102d41342c08491241c1c045036102d0f620800250041c04500660500c0741080b403201065050036900c0031a11b00c2015401c546c0d0104960320340302c0c200c078030020f0742c10040f070704451075454580e101c1c9501c25800c1511111034882204c4070b5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 976478848 1250 976477598 976477639
    0xb07080f070c050909012007020103091a180102070f1502120115091e0603050414010510060305011401120f0b130c0e0919020a05190210050606070c09020702 69
    0x4011100b0044085040045142900010350000c507a88000c1046880c082c00d55052441c14504900d0010070100300d403425a8066800140c00315000900c60301904241c08520098000444841008841d02850818010014400d89080d82d43c002140b152070620740d15007800810103100d00d160410740820403410004d4040701d01600800103000450740c1c4500801d8040c1a4502581140c40d4409200d00803511445280c8604812101d150400160940311800c0120a003024054207401940c240300c2131250380c103803100204040f00c503690f0381001036988031100380403807400c01004070740000d0001004041403201507200c86040d00c54840005074904508000c2020070140003a0705d4087e40c0c3d11081a084203800c0300382c039007280404441b06101e614001380d080301d40f4241c0718400c6013200e501103009403449009000b15a04000f0745141410000c3c00007400075561f0b4078841e800c0001a00300f0300802c1c0f003428404151000e0b00c0d48104681030050903c61410020740140606a90003000d240190400c3c00e0803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 976480098 1250 976478848 976478857
    0x60f0c0412050604020a05060f0904050a092102061005010804031d0415030b01080601030203100e120f0a110d090501182d060e06030f040c08010e070f0803130b07080f 73
    0x20368083c10a40c03825004000201007182c1c80341e80542e03402c120302447c021307148080b59800f00080341d0003c0c050b01d0b07189500b4010704680d007008101305443c07000000005142240451504520b60840c0e031282d82e101202c103200b84545c41a180400c1d07122000c100000d004100a80084001c03091080000800100040958400105452a140148905000740021406000d02510440e0f0040c07900d940346078082036075841707110302100a56503110070920390210184042c848446a5888140e181d11541000690a520514a86020841808503c40150408200b41c1c907124103548941c04890316210041d141090000003110004144802c042a02c1c50080f03102c040705501d0b0055801d1281c00c003030300c051091b0015004201417100e54525044196908400c480d03102910281604440e00c4610b050380340c08d452904810000d5080c10440c0142142c00200d5104584030700c4520b42e20156550302c8991a44551440c2e0780c081030070b1b030342d041c0894400c080040c50600d105400c040e1500c00c070b01c840005030380c02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 976481348 1250 976480098 976480103
    0x63b0709030302010f020408120d060506030406020306040c030e3c0109021309020a050d030c02151e190807050d09060c091d070f020a050f010c09060c0302060f0c0412 73
    0x80340c480c14001d0540c24400c10681260101003185000c1c01c004a180c6d4032a0b80003401c540c0014006600e448194582e04284d004000291410361207017050b1070a20081d410840d81e0a00540c038110503c00118402c0c002ca07494940f000c4041d01000300d00003040b0914500300401900001049240b00207100c11100c00d80000c00d03502800014820828810009811010032214014074201102440560b0302c010041003111022144024604250318040c3d0780b8400c0740c40080c4d48200a41d030340c840c0000a0100501c0758406401d1441002140501040507502900d0511280000e40b040d09040841c05416400c0d003000c0c0300d08003282402c13031300c0c2c20900548004c454111806900c030200048407641107091800940808942c4420001414003440c9210f03c2c001c0519040240c000140d02e4114000c3c0a0a180d00746c0200644003181001035189001e003807480c400da00021205040041d14510400101d102684e041d8060511901d402da031503060307a0030141c07516004c0042004009114865180d45080d80f92 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 976482598 1250 976481348 976481357
    0x72c0625051c1e03091106180a052d041104030c0303020606010806031b190e040b1315050c160506060102061f0e0a060302151c063b07 59
    0x11140014001c0940780302c2d1082c040c9050710b102c20401040c441c849000703010300d030010b0110f01904200b40c1c00180710701201d8000e1030000d44494404105000c40049240903034240d00c846541e9400c0c0700b46404000214240740008042025201c071401c84114681c1d00e000b0008900600c10307402a1030a644903a1040b101c155a02d041001015018464160721600900303021441c0d26142c00469142c20800008a512900b0160f480e03c0031303503030f06007000c070f80c1a9000d0b406007280782c540c80185400103041e00c007a241c8800c108001505082d140001003203031580500e40c0109550283d2400c1c0103410060185020356070240320380f4060031610342008016600520040c141410448006414090301500b007501d0381d2850751154001001071071909003100c10050541400342d403100c16050040c8815000258405104034100c43d14810507406403204103001400e6401d44842030070280100e440510030b4010f00408400e1131101c0b00e80305050900900c00005c210032400402c0d0b00203c28018080b1034140214 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 976483848 1250 976482598 976482613
    0x3040b09031606120f0501050d0204050712050c0702190b16080c150106081308180f1e0a060c050604080a0e1003331401091a03072c062505 61
    0x124460017003422980300c942007044030f0350510000c25941841880003074002c64856010400c1c042c803462020716400e803811400c0000b401e0031340251003158030100d026403040000d280e48520f07144071013a5000840351060451403030310f607110008105180303d05400ba03d40003800d1243c1c0b0000306003444440301226a5242500f82c642c10210007500d1614081d101810101c0101011000214000c0490360a00c82e4800c2e40b80b00d0001400001d10700300d030f0711603960b600070311105c42e00c0e034203c500071070446989801145d115030055240c403403c03145400c444001402030f40c048404500070509140003030550180358a80207100358100808070303c515841c0b13958800040d640c1d015141214840c0c0c06c3c00f03e20301c0042015004d00b21240c05080c4251083c901070041710404400403517400e81e000340c40b03c0004041001d0407880c00da01203425001c0c5600201c6000000c03521801114542d0b90300d14408401244110303030003d4213029036605100d019005900128010416a840ea0380d03142603d04052004d984114000d0522 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 976485098 1250 976483848 976483877
    0x1a01201f110304030212090a18051812040519030219030309140a14030a170c0c0109180b241c020c190c09020309060a0e06070203040b09031606 63
    0x115103981d028118603000910500001a902007400c40d40719010742c004e5500c4406060004007403100300c0e400442d445042001c1d400f085805a00f18600c21a0183c880141560700408101e4452402404202d04000200002d100c207241c400d050b602c0c1c42055480d0015100e88036030100c0c0300600342d0b4850b1084000075010400030158800e503c48042c2818503d5995400039000c042086032021303001e21840c1e1648003504100d152020081c0b2403100d500b090400c0700321318048944000329408080005a03600035504000c0c0f0550140c0d040c00c0449007a401203a407081200400311000341220350b0340e60740c8105261109004890009030f070b408074100e80c15103950742e160039141007040141101021030682d401031003140302d5260b01040e01403c074008241c02042a82080c5010000380510f60896500b0f40c2c07010051158110002607100d1058103144d07010488410200b240c1c90313443c40d08488440c016401040103029405809001e40300f6074401900b1154942e0200c070343c5801079072054102100007240b028482c41d8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 976486348 1250 976485098 976485101
    0xc020c0f03011107060b060c0a0317011a250c060e010905040510030b180a12020d030504150e0c0a1517150402160204060e0a0608011a01201f 62
    0xe014110000c00000c003104241c002c05004907540540a1952100da44c00a5150b900031074100b011000700340c50b512029890080d121214580d0302c9089032000c880081080703080ca04242c21820400484a420822004100b00715130f00d0031410f03054284c00b190007a800003542c0b40c0011000d4541611401e000d980340c1e000050030481507903ca148120b0401d02800352021020740d150041d47d801001302030256940100300c030b10b54607408094801c2441803e038080c062280001c100325100401da820b60b4182c50500c1011016160160f0380a40302c0d44002c5514200351183d030b4022601241d4407015102402600b40c00130300c1c41a541d6011042c10080e118081410381e602054103014141c0783c100c00400d504007104030b01c040d8105151281d00035640028040d0208003426100f4042030783c0107206024640d01c2d900354039040102034030b0506109051542c00f144141c3c040c060038405820002401807100403c00c01121030300f0380d881c4844072040001d802003000580600034000f0150b1030f00341840c0e00860341c0e0b00600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 976487598 1250 976486348 976486369
    0x1303021921050316050304051204030809090114010914130608030c0c12061b07050604050d030c0f0804080304020a030c0b0403021c080a0e1306060804060609111e0d0c020c 75
    0x5040003030420402c56000101d1980804c0c0c107070f051a00340e442c1c3d0b885107845031400041c2c40c0c243c8400100482c00000b040811030090201e10000d031081030320b507641d600c1c80c1c59495004c2c1103034901003004000144080d95060020319039503000201548202c40f403610010341110031036000306500d60000100522140340420241d0b1084405a0303480e00c5042100d200e403a11054040c120046032041011030ba8005000309055610050b00642502d4003800c151400980d54a40344400b90b01090030540300c00e8032103000e2401152064400c3c0c40c0c00041d6600c80e070795100b480c1c0c401003080742c2c000615100440494515044400074103000390b0100e54990440c0100704d003c4920070240c4040318103041008000030309010917544200c1c141c0c18000c0b220302d56800041c592400120410011030f1070304400080c09607100707100320300840c0100020001d054643c0403001c03da583c09859848100d5041040b01d80c60010b88000000e15411040c8050030b04c61090b0095041c0d803a0f081203980140d0214028103c0ba203048001c45 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 976488848 1250 976487598 976487663
    0x3011e0b0f0f09070f09090f0203040c0605040810090503070501050f01060e091b030a06231905090606031e180f07080705120c0409060e1009030813030219 68
    0x11481c268122001541002004281c401004503400c1e56015081c01006e80c1c1001c0c02d0501c00600119180402c0d01c0300942040b1810385d414030814400080d0306001c1c2c400c40d07060700c00d8040078280360b54164811802800150034110766070300c0100076480c0802d100388a01e03405071024000301825035140c030000620149030100a20721848410050103041c031140d8039003071090f00e0009121900d940d6038403505c10090000d503124140c840a2000709035507418142c203070014105030480da004121000300a0342d84a0300458003038241c20005060103e1181e1808401440d408800103007520949400c1d0908240042015509030b8200070902c5ca564464400c1407044a017035480a400801070140b074180700700e60f51003040c400d081c00f91100c1642c8110030901880791054400e4060000d00c0502c10358606080144800403005070303d409110707240c2c031940b400d502962082e150980e482d070203551904414140c620300c802d00218107502c681110a103081038200e6107420310900410f02110180c11042e20301008903221103a4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 976490098 1250 976488848 976488859
    0x11060f040620030403030804020111010e070515040b0d15080307030e01030b180f060d05030324010c0302060c130306180203010c030612080a02030f030a09060605012c03011e0b0f 78
    0x1001ca407400700005136000c0b65018900340245469500040c2d07040812420400300d15400c014403160b0b442e10026104e411100182e80e04e000b1100d4107802080c070760240c0d00a11407200010440c1320003030810f54001d903200a0344c2c085014820f96031654241d142d58081141140401c0003260412031942c0c25102d610140982602c80118811240303600007003c2c203004080c81d8241200380c0201c0c95645030149926010f550000407a552414120030a40840d403045008a80c141001158940c031548a08420a03520b40e154004002a4890010a049540100c2c4451405006600c00040030440078050304c0c000c0040271043d1f00300802980145401d50300803903482c90600d41880c03000c0203118004000c00302859088040d241d16150889012401c40c480c54103108083c00d0044140a01c10312294490000140701e070004100141d62840103441c811802c0036484202d000005c0d900c2800000c40381850b07000000240005000025450a100c4e00c11507115019036580c5d4030328030700e07259051441c0d041200900c00c03a107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 976491348 1250 976490098 976490147
    0x70f0f050402070f142d0f160b030402010c021507060e0f1b0d050f0f16050901060c0f06060b130504060338160807090305071211060f0406 61
    0x40d2215040c007142c030300030b0202111900f000c121610030300100d00c1d0803400c00c00c407409954840002c0d0100211015961b5510f000320407407502c94480020726910164500d4400c0d001c0300b03280c005103a4298100034016070500143d1422000181d452051006402c0c03495922a40c407101c950914004842000ca4441c000f030744820701760110400300141041c25141a0002d102d00c41281c0c03800714500000c00503000b031484c80b4404035a004040302145000d110748628044a86412010b0b41e8000c0407031440c400c3c039800c004107174014465503114020012a0f60302030000b079080c041c00d594070002124600e5001480134540494189049001c0801d0b0b5030061008a800b071142d00d056403075030a140c08014800c8000a145042d60030b1030148205000c101d514034820303600340c40b49000a5144410924654a0800034a8003000200082d0141e840d1070103807908040148500303070419002d0366248090346015965040c071908080d803d65500f03070060201c0c014000b05a0307100d41c50000c02802101c0d0781000c00b0f0b0165070744503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 976492598 1250 976491348 976491353
    0x4060f090f050f04020c100914070608060f010225080d08090705040b1804050a110103050403091a09060d06050907090e27010216030e0d051e0708070f0f05040207 71
    0x54040050b00c404943c1c4030800441580010001e100700080d0421602540c4c4201c0c00780c1c1c44070790244003070301d02950000d40c980840c0c421007500d6900700d00070306010540301b401240c82c03030801a40c0102180018012580000680011110a10b090a1340e84800c401c07425000c0c0441d2005000c0b5204040380c0f81403c642a05001501c0b070340310b2403140907086c06284c0e44e0b1002c2c54942d4414011440001041c1c10100c11814641801c54072000389500030b68440d40c0c10042d04040d94402d02c6021701c11905a9a0703030312001d0400c03c0000640c405500c0d20b828050082c03198034207075075554004180c409490000040c0d203501d0b000500c101050014941018801006402c20440c130901a0340b9500c070000261308018509180000508078103070700c04880302d81d031010035030924150914001941890007500c800007003c0d4084208848040d24100c0105280c00201401030424080110801c5012100d001c0e507440301d4403144010b103000015480204512840e00303080102c06000c0c59424040c00040c1c2c0c00758039065844c2c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 976493848 1250 976492598 976492619
    0xf01053a0203040507053a03030213062c030a0b0a020c0d120509060f07030b06070b1302130c0c0312090f0c030c091a06090d0c14010806060c07060f05090a0b04060f09 73
    0x640c001c010003071400c4e81f0008040c401e5040710700540c5807211800109413520001411081e944890b8a15110002109444c85105072f51004041c580103005100328012543c43e45501c0c0070107080c285219409200424102400b44511120020b503541c411500410700900c0600303440d40503202d40e070ba6070098820310100700b0a100740b40d0781c00100d41c200406c0071100701010801610400300c010307102d00094028890300e42e46480c08808500d000f01c0d5240c450482003103000c0f04440350b1840d0703440400c418480d24000a40942c0d0012800a81f507070f40010008140d4651240020340944100d60a8180d40014030402840360f113007101405c0c2126040065030211445840b1311000c0c802440c0c400d08003c10024820381c2d82c41e070310325a0359078004106020a640c40b0f00c03801d1115205c401031400704102400040050421009442c030038501c06000b81030b190700d4440d007034400701c0b40034200d0303001c00404000d1620319031a1066810020094116003d65592030b02c03000412500d0710139503d02c10450140303410004c40405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 976495098 1250 976493848 976493929
    0xc02101401050118030501020406030b0415210203030403062d0b090f090c1e01090b03040f02041d01020307050a09051818010213030807020f01053a020304050705 71
    0x3e0030f280000c00303d013580500e15120b25a100800540c000280071486c0344d03140e00310082c03182d020b55083c4019106c400e441503144041d40203840d0096140f250b008004030503c60b200080f140003400703591505032039031034000c10790f00c00c8400f0040240c40550010138204802d00300c540002411041048003a018400045081038040d01c4080320109000106514000a0250140d0400b00416220000c001d40a80800314401542a00e02060b600b420008101000300c00f00d9120300d0340100204200a1107600300300041000342d007810f403042102c001c03061000304244015406212680ca41d66100c1e100c505005020840b0b940003d03000d020441d84001c8406070035074030590840c85450041c0001401e40c03520074020b0041c04121808601805400001e1002d2040108134042c004d881243d00c402c03200005554074030074249102c0c1000159130341c088040700c000d000019007484480d280400713034a400c0504816a002980c080d5155000001e0420144c9000f030502c0345039084040d00612030120b40c0c04070071150a103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 976496348 1250 976495098 976495109
    0x50403020d0c09050411011e080a020a180b2701050304060b010e061b0f06040314070302070f0e090c01080624070b01060207090e0c0f0622090c02101401 67
    0x2001401403040146451010001d0300e94072004200c10702d010304003040410250340441c1d010032460608c0e910201840c8850089400c5c4039250700300182c0f200e00041c8025880804441d04111007080c103d0260f5040311031407030040200521040c1c5503018204901c075845a00b03004e5500d61a40d42c0a2a83d981e40c0280c150b0781e015801c03440000f455007040c1c00594442c00c50f061142e070b200300e0000c0c0e2440100c5054882400d0742c41d00c44d044030f800080061100355100303001d54010340442d0805040001b4004003000a0810364800e1055410b040d544689481d41402e441e000307070b0030450255042040d03000003008180301220003481c02c00c0f95030074000302080b44045c0d80348880d0721708401c016820b00040300d4042201c9005a0225480303400d581d542078002c1d16400c00f40150344c1d06508002062005800c001021002444001c06008e00655050104055540107941c031755060802c418120190142c0380c040312008180b01040403501e030740780740b0000741400079103100420500e281819002c540a00e24000505441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 976497598 1250 976496348 976496359
    0x6090902220603021f030501140114211e07020a031e030603080f030603070b040f0e0a0f0c1d09010e1b12010303180b0712031e1811030d05040302 64
    0x20080d4010703406441075400194004180004060442e0b51414040c0740400742e40d0360400417640c94a030040211301d411070502d40010340d44200740c00d0081a400080103041d043c404110350501c0170542ca06485542181c5240003000c3c050342c0d0040400d00e45100a03801030b483c3c400352000782c200c0d5401404200d01d09210110401481107040b40090103a88050060341c4c0104101340c480c140d042260308550300484020380a400791100009801385540141c2d001c0d55000909140d59504207506540c2c084e00003003050611130307158000d0901c860032511507d44200070b103079220b40110345c252811081c0d00c10f48407a5140242c801000400500d1010031041d5003050359000c01c0010340d2080c418041050040b402d5a02c618182c4400010406803c103480c0700003110b180d200d54001540e02e005154990090b4100a048038011000c0700c51118440e0f488171100c10a03c8819a07014265840e03a8800ca41c404c440b0b030501500b00d138040d074043c41540b8540c0518540101d0007082c80a4034060001c1803030185101c001e0240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 976498848 1250 976497598 976497649
    0x1d010b090310021b0f0a05150a06050d032703020d0b04081308070f0e040f2303210a02070206040909110d060f0c02010203010602070513200d06090902 66
    0x103640600006401180c0500e081d5141e03d4103124142c0400300810b0281c506200d115917884103000003160008040f90014003030304030700c0e68000c541c1c4031440c0001c0050546c6076541c0030109a980c1e035071101000c000c0c02581e85050b103018200c2c0003e100703a00004600c101c4a20300c50204016038440e11840c400a03844403245c5440c0d1118608821030b030141e089a05651804e845000c84c960600040f00c008550b018540039040f2642e50003036490b050401c0d100904045405044680840c4110202c1c14800101081500403481102c0c01c1a04542003a42a084c80d80c050541c44080da040c952001a0044001c1804524040c01c1c1d900060300361181e885102c2c1090b468180c08814030400340b6801140d02d01c080c2c0740b240380ca805071401c1001000311001c0741009a141c8806411a01d10502c2034074145d50194004080450134002000303040f113485422a080c030740e156228050100e8540081b058111403080103103441e1030b016195401592802c6e0801000640740c04d10000250791481c2d000074030b01d0542d0400c411030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 976500098 1250 976498848 976498867
    0x30818070b0f0c0a1518030903020415150215010e060a181e02120f06090c09150406020a03080a020c0c12032106011b050a020105161403040504061d010b 67
    0x203901801c42c02010f14021508654140b020105980d803001c00104001c00201c04d1404c082c2004080c0c1c00005000650048000d00050610350b01c500c2c0300c140540c060118084c1c0d640c004441901d05048054010703000142da180c0710300300c1080580d0151072441c1d24009030b858550701058041d4003921a942507441d58041d80002000d040d409054022082c101e41a0040101c8602d070300658031464426002204000000724988400383d41c042c01006c00604115403900c031145588420380020020542c0f098800c14503108150f86800100001e04494010b060303c1240c9041c050000c0c2e000504000c20f90b4010090305100ca5004181003a0382c0000b120143d6403056000c100fa451402609c103036100e40b1510380420700c843c0c041c03002c8040c41034000b6a248502e940038000603803403840748620028015401845110015030007640502104032010190300c401c0d41891302c5d0ba40a0700114440d440c01a040000c090195080034001c002c0038007006014001a00c05032441d68000820500c0748415a00340071078007414 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 976501348 1250 976500098 976500127
    0x10908090108130f05070303080106031a060a12050406090c150903021c02090702100c030c0219022b110105042601200c071a0313020d0b0f04030818070b 67
    0x1c06400c131003880084041c618045030ba4a4940c0002c0c0c1c00f140054000091440c1300e4010004541c0505201c6441d00041e441440700c03a4102c064404140701c050300b0b0366060081030388500c170300c507501554010426140e01d003420310f0300f00c90030341280c203071a42800d8421040503044a00f030360859505543c4c0400740041c0c10050000f0b0412038400a40c040044024040c4965000520403040741111104001c1607080d44001d9040b2281d040000c0701580041c019500300254251205907124000b400100740955200343da62186059144408a034908500a09041c0450404000f21224081c02c1c09440d150400034030303a210368a40c00b007030200c12520b84800742c0071601c00e402c0101141c000002c0c1d610112900401e00e00c10b60004d0b9410243c603c589400040d071078420308012605000241c2246155480c1e4045250000b41499000d0760004400040b540005e40d8401c2c94611444242400413a40c0c01e0521f4018940750340038000e007000401000c0c0b1140e40c520040fa140c822180c52038800d40c1d035200398203003640 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 976502598 1250 976501348 976501381
    0xf0118060c023d0c020c030c1f0e0604120b0106091d0a0b030a060e0106051305070503180a080703050406030f1a060c010603230d173420010908090108 66
    0x141c418204221301400315000510b4402c0c4440c2141621090707440603041c001c840c02c4819419295007245400184240c1c083e0580c443c85401c050f11140c9040e456600c100b0024400c1c400490300c54190900410a45501080d8000034194052000400c0303001c28120303810022024040d800c00d1551040719006a0740c04002140189600c4032041c80f440180000460090a0f40d1040340d01030750303880b645448400014460944180c004c1e03120541103071506040e080300e103006100245c00300e204050204003c100a01c018042c22031196a850383d40300c0c2024401429280c182b520b680c06641408a001c056031010001310540b0502071f41d0041d103641c0440e107224090013103580b020386843c1c40010959844001d1b0b500e06080a4810000c5a2030f018118108031101e40d0b464019150b1030821002051170310f144641d1540ea612800c01c40c076024881c5d400700c51494003c1c0700e468080810801c103a62045941050054103407441500c008111080320342d00c41b240356208100c1c46504010a00c030004003040103000003003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 976503848 1250 976502598 976502713
    0xa0510180b2d0106020c01020c10030e0f030403060605100e03070b03070e04050a0e060c03010f1a0d1a120a0305041406070c090b13060303020c0d050f0118060c02 71
    0x5414840414511102c6a802030058000502580c2040c50055000203014080068050409000310364668030403001020503140e101140d00800a155030038240400213030015501800c0001500340c41e140800c800e68101c00d00080c24840619010840c40c6da0100d0401c04544800c1402503503580c8010341200c1a041024400c1c1e80a481c10003031101c030202c40d600103c0803800c00e8085440c3c5403140d00204030903020900c00c3c9240e1088048051100b1110500c400c03103041c2d0780d502403c0c10300381069040c40c144c0c0e05191005a8920400120008900c1c00c5040c000c0d2400b54034000d065900034a840052040c41680110150142d03a04101c071490340742c034070440b0b101d00d4100b0700f138082441c0c40b050030802600300740180f28882c02003050b506103146014495802140d030302d5001031041069000c01d10800110651080c0c0d8140561482003030306c02e000703005030340f9046c9031054110304164803441c01d1401c50b126000c040e0219840f50900401c1400f4007020420745a081825454103844d00d1007c487d07802d0003600e1388 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 976505098 1250 976503848 976503901
    0x1005030a05100c030603080f0f090901031220100b060f0f12090304050907030b01030e06010b04061403060616060b03161401030b0f040c0c140a0510180b 67
    0x68200744680070401c48054040c02c1e03000d001c81500504100e05844060202a02000080145605201c407007001060002c07020200d660408514100041c00450241d1042d14076501440702000100e92043e100c0e030144109501a01c030860744601150303130761041400030011003a0b4403e20542180d030b0b040181d45080c07803040c0f4441d0741c804200c5401300c07080e04460200540055200d0208003600408020707101a40c5014203804840d6441c2d03101100540404070045061603a140203810b800f05082c00710318060a01c3c0d5082c1c590f110304c0e105000f04901c080384681c40d20b5040034030a101d556603c000480301c64613110706040007d20811b045c03c0d8014a500c2000e20b90510921412503039002c84100f5890440700c045036141140d2003818010b4003584c032418003180d400f641d440d0040c455481c2c01d60010035030304001d141c20b0191010650303a40348440400389000c940c0d58401c9910f0b4040110420850105603003c440c207002c0000341100d405031644d0b09a10040055004030700140c6002590100702290309914400b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 976506348 1250 976505098 976505113
    0x1103070303020106060212090303180613081f09050c091e090604020a080a03090504110405060c06100f03110907030f0f0e062208090301060e0a02032d040b100503 71
    0x20064004c180522409025004503107000390a00181f0042c0e03407a0100103000b95280102c402001d00055450b821400d503c20000d102144050040081c000c4c0035122140080c801001038801903070310107546140a1464600308640800000c3c000b00d44071100207000d42d041096603d0340d01482d00070310030001303961201c00044c030204441c020300014002d006034029100d148495807196580f640300d0303414201c080c001c40d410403410050341c180355020007514a07000300c1c420700302500e0380001039aa9110700c0107d192940814107000250513550103030360082500f00e050900c0f0501d19580d015104609455951007880d8400c00560b00758065045011410b60705001040404101700001008200415901c40ca61241000080680320381c6402c20000c8100080c140d001110145e407005031a60180d1100e5825540b543c1000454215905406020300e9003000c0143e2245408007007025001c0003030400c5d04006404105c40000010054022600143c03c200c01d0b2945a031034107045000703003041c2d9205913014070401d803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 976507598 1250 976506348 976506353
    0x70e1b070f0b01050a0b270d050c12030309100e101b030f0c0c170405030a0c03050111030708040b130b0a14010b090105040506131a0901110115060c11030703 69
    0x12414140714032070140d11440d642c032030013400303420121800307000070a541c10040342003030194a07000c903a05040c02e0341003240341d40c0380300380490003550901d941102e059110014601d540d00d041d1307041010030b43e11000150304524010800c103075103480020700c1001c01583d510515204a07801c2c0034000c01448408004d03c83c241246481c0201c0b070a80101c500002881c04e0010100101680608a070040507681c0c0c90b11030714840d803a45d011a0410101d87d080520040000088545091200c4106507003c1e1b4035180b203032859070610382c0c01d40d1400c010040001c54204204652b2540025149400c42e80120100031075650700c003182000801d0340240641075a00e15410407a070760a2a810404820300c01c0082c28006036620468812280600944a4081401484144030350308000020f0009100c149041900b5590350b0707517498203954005158908002d000049030900341d600440748000007074041c402000928422401c680b60840c4500495040000905180091101410000c442c2ca1401010b40b2039a65491 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 976508848 1250 976507598 976507613
    0x80a110105130201030e06010e01150c050d05030124091208090301061403101103280915110306010e10050d0509031e0f0706050a0f020a02070e06040e070e1b07 70
    0xc030403c900280c00e0001d40f00d02d008001c510541280c141c00c445080036402e2840c254242d080c21881c9004000d00007007a00003003881001610300e0803400e51100e6580754105542c0d481c240e03c0301c5c408420310b00d582c036a0350400307694408084001c981c2424122440380460346131940c0c50780b141d0f5500b10b500d0340c2040f030301280d203942c0340c08480d040a078110112840321048140305400d403441440100c0e07901e102400041c01d075524803c0340300032003c000361b2001e0305150030918680880300e131490203132141041c0404203c40c86000e4400e0060901c214241c00c1e08500d8810002031461070f038031101c0d41c0901d0348282000c803600e00410541b492034076094400d1001c0e26242c04a983e40340c01020130301c09180202d05180d554018002c085598240f0f128142c640340c003045840d010090704000c0d001c8000e880d5a945c00d000410181e04c0a0a1030140540c0500300c0c0f1031a0144480810780040c060500c524500f841d91001480c0c00664582150400080c04205503144d11040085401e8940c415251020002e040f50405c0001e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 976510098 1250 976508848 976508881
    0x1e0613030602070c0612090302150903090d03270806040213060f060302090411041d28020309060114010f030b06160f050d0c0827060c1513050a080a110105 68
    0x100e541e04c06e10b400361070f0480c40658940c2c03980500560044402e822071035086550032588841c144089910b840302060200f05c805000520070340020740d17540d110310700c1501c80c0c50300c05280e2000028100750320384c2084915601c421016000071320990341c030030180e03c0c083c990f40c201100a00060b50741c00c0f030807551a8005030195000c240614410f13032400300f280048041c1c8074151026075504503410080c8001c042846000b2040c040c3c14683c440041c0d1060b80010050490200f0103514140302c09612414a155030f2841d001040e00021310141e0a190a0092070f64009901c07080d8940a25000c1001140c031404124680701704100410041e40b001d869209001c1d8880800d400d05104000b1240f083c074031680100d8011018641c01460014100700301a0716000c03641030f020b8524001d0440911000030440041c62640c0254500c40054100c243c00b100701c2c0d200b500300c0985c42061550301c070001c08440d0b601d06031105a10600102500380124849071038502c0f903559064140d070782600810590408100c1a4a0b813000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 976511348 1250 976510098 976510109
    0x3090b0a0e1203030f070c151a031b01141e07061b020307020105030a020f0d1e061a0f0c1f14070c0b01030201030e01090203010f0b030c1e0613030602070c 68
    0x401511102d500042100d200d070f00d40b4006002d190f01c4248007100c408000440c2034500c000e959080d05200201881030400301d00002d04107c4070f000c0340c0e6041c54100650b0843d1803143d00b59140d6407429990b0071119080340301c82600c0c2020f5813203880d0b4290f550b02d5000034550b107114a0000c90141c08112840d40b04900080d107031600f0044510052204a0303507846100c01c02400038074244082000542960041d00352803024003a03050409413580088011109030240c1da0b07030804005400301e210000544200e01c00761a0240c2188900242030030507285070711070590b44a02c00400084c000509020034041100c2d5001c0070554841403550090148028044141d40d440101400710046070307155000c0d1501c0c004195103d0980070442c0c0c6960015401000843c0b54606036540f00ca0f43c1b900180d8080c4240002d0380065000012409584414146486200080749020b0014051560040800d40719540000e2004584850f52019540c41d94040c00d10b4607400201241d001080ac00c00300844408404141c0c1c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 976512598 1250 976511348 976511359
    0x17031b0a11070b1e2b0e0d080a0f2a0c0212010c0306090501080c010c0302120c060103120e06180f0406180c02010c0e04090609050304180b090f1303090b0a0e 69
    0x82d9420f044007130901ca18000305c0c01910507052552480c811829102c54241804400020080c40c0c20030400c0c2045c0e450010140050810b0040088440d414818074050021000d001c014410510242e42c0c06070200000c04150807200003010300d040c911846001c60340a901414400c1d42841c000084d60280c808034040d02e02290501c880440c402c8010b10925048440d044001c0011294200055940c481844820780450142a803200d0590040034000c0102d1494103004040640c55800c0c40c100505109401c40201b04540d0441c5200d40d84550039640c0008070001042c40c0004d88000155000703108020b0503820604080340018402d0780c504c00000c080020080601c1069442c5100301d08a4a62420711000301d242d00b05030000302e05241d4003040b15203200e4100000d00c139072280c640741d185421a910994001b200c402a100c0320381c1c128007585d4051842a40c03030882604116290a4900310b00808144200c3c0400040c84c040c944143d00f858010200c83d03850301c1d40c42e0207a102c010a40858901c007940580f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 976513848 1250 976512598 976512637
    0x4090b0a06120206040608070306050a0f080c0a030c05150405030114010302010f080601080c0c100207060504050d1b0212100606030614030a05030409180c060c17031b0a11070b 77
    0x6007a0700050040c090f900400c4e0034a8a800c0580075146000050262410144c0c0e4520104140d1154050880509070042809004624048e440f52402c1080900c042c090000403108000041440b20200c00741e40c403c0352401071100c40428442c0c000e002e9540700507811360a1882c4254801105c9003500d05a03030017030344c5031041603940710003d0704c020f82c043d2000c0b400a401c6000040300001c070403014100544d03c840c00c0c1c0e614048800e440c2420790304420020388106544c3c1d414801003002c01c212005043c1c010341000101030710000c0b10704c0c09070204140d020b03000b01ca080d0010444010b0a00c08001c0142e44c0100803c03c1d2a01e03850000c00805240c096420a44041d1490403560301d4005050022198408015490305040c034031401c000d041e03141014030944c008120340c480000ca46c40b0a15018103074587c1e80e03521120040c00c00d9000c142d10701502502c48102003080c02102c0004400c0011100302a50199650307004003103086415055101d00c80b0154012204081410b6505400420709808a82a5000308 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 976515098 1250 976513848 976513859
    0xc0a051c0f0c031a01300c030c0908030d020f040e16030c0201020c0712020609090106020c041109011d060d0c03020315010509010219061b0507060608060114041a04090b0a06 76
    0x1128014281a0081c08071310400d24401d40c070444202290701c60707410345070b002c21300c18005051035080040740e044402510b5904c040c00440d410701c1590718803c0c1a240100850b403074200995120312401040c01c4605800098260509180c4c008840c001c0c071501e52030fa43c5038500070310b5181c0c01019440858001038200710120003524814000e0b581741c180ca035000f07060700328544000110600d030008800c0b42c00a0781400a1400c3d56a010b11080c000c10b40b580103845450013410801040b10200f59078505400824002c0700641e9901c444ca10960310b94030084290b5030151903001611901610441c1c10140341000c42ca06101a0315801950042100d1800941c18181c1040196980c1c01180d840c1030043c0c0c0b02442103d141e04c80085074641190080800060002c840030718590b0380916a0318400c003083d000580241004000c1c42603c0c010710302803019001c07550616408503814034586179031500c01e03601c421b4201d404101d002c0702c442800000030b2040103000362502d00755403040c8007160300060b4170745405c80006c1c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 976516348 1250 976515098 976515101
    0x60703022a1e040b041103161b030509040e070602030a0314040503070b04030513260d020601050d0c0803041e080307120c03050c01050c1e120c0a051c0f0c03 69
    0x40c401001041ea00c2d21242d8081c0340c044800c0d40300c0005511946039083c402c141c0c1c489104050101c4c143c29102c0c1d5a81c500003034505000e03c50407030158100801c04041ca011003041140614000d80e00d40760443e601ca003424001070140000c0a4044168095103c0010341550008014400d60742079032018030031484821a41000000200c7c0c010b41a0b030000c00c6445c001400b880800703036110b886401c0c0141800c28030600340e03002c00b403250010540d603000503008661901e100c800700c40510441000030b140407c135100c13000391245c0d018072030107000d4001040b4600400c01080c100c42c1c05840d0030070442e52600d95402501c020385100c43c00f0b601801e8040c0c0c401151200011040f2500940c00c642011503040131700c1401c407109206480305504000050000c2c07100d1083c04c0c09698080c851150516440d90040740388500b0b100c40403c0c032100a408200070070341d0305030340c940f00385039102101024a0307440c0c1132119070070307101131040c50028074a0032942550f50070410342550040074082c01048040018040140c0140d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 976517598 1250 976516348 976516423
    0xf070b1908190209010c0b01090507030b0d030c02150409021201050108072a08120906040501182019090504050d03060617061f0309110a0510080a0b06070302 69
    0x82842c25414030301c2042070740c004150054061518194801d41600c41c011266005c4c0c001c1c40d2900c1c0c962090242545c0e050144003641d101c1220380d680b0242d400e42d40608201c501e031038000e0146602694812000250a042c0c5004084140082d9904c02005001030700612090241d0707400310b40e403900461400c522886485982d4504070707000072500580c3c440b071100003680303a10040b90002010088140020741c0c811182c0d000301d4007a070007010309040c40e15242d42035516024200811420009001d004255500e4682401024401d6800c50305150500462075003142051038905508030800c0c000f92081d0b480d40300501c0740b0300500a980e41d8100c880b9007102500c47c0c0784074075000511400340d9005180a8422055000a4001c015006120092941840118201c03c02c000869a140f01703c0042c80308070001c0743d20440003103602c1c400c11414a0300042e0720300f0500b107000c01000710640003d001080c0390f600c07254001c0001800d241d00e540240c0b8000755241c00351484008400c4100d0240403181c07403080c5e00103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 976518848 1250 976517598 976517611
    0x608010605030415020403150207030f0e032d01090b1801021c0203060111060c0703080f0106020307150603020901180f0b0a1208090d06090b070203030610050c0f070b1908 75
    0x4070310b1a15141c80e80d15180700300c2c440605607182d081100100082c20418a0300c04560400030158aa04c1c450070701405040040c0098802d219003403002c10190354001c02d900400d61000c07a07207081820844400c000d403001e080915030003150710340a018003c1c0b00e1291512445246406030908020307480c404958241e006c1d4140c140f445480c5045148a242410f801551340b2680c18506080c10045006043d450803c1c155440c2c240c0b0480040c00c0750038981d000200c80e034060350319540d5512552402030001c0d44e0744a40000685000c0c07942c1204c400d03d0016400510080da0002e107120155611100044800c00004c0c1c1c490302c1051030080301d20180c0f0210300400c0f002c0309004180c070440303900c2c00301d40c26000140c074001210030400c1008400b50954034000b41d03d071264083c0000113413000d8030b4640171200c0c200180c6201e05560060041003e655a01c0d18180090905490040e4039580d410090603e04100d001c038011460080000225444c801d0402821010480b40229103034252070f03880980d513241003030780c11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 976520098 1250 976518848 976518857
    0x1c0504060e0616150b04091a040c0b0703020304090c0c050d11010e01020d0b0a08060c04030816080a02010b031c0504090e070b13080607030c05070f1119050a06080106 73
    0xc02203680141e428619420000c0d100c10b14000941d1406140006405001c64400e030303020881003260507052140c449901c0042d6000c000306061520303017040ca140540e440720542c1a070303d00040d041115040040c1d0007014040709450315518503103000f079143d400500560f00740743e00e0224092456071042c1d10b140c020700d420202070692454290421201401c000c00d9071600381d034840302c401c41c0341e0703000748010010000384140c0020510148000c0041e109919486541c566101100340814004040221001c481d8019080d5641d92001d40c0203100026403610007900e080380c0410002c82c81901034000b450841c00850694443d0b403643d83e401a0f13203200108604000030b1003407100380002c04195002d070540310400d1044541c080c2c2d48203c011403130b03071001c0b1001e040c581d00413100308a036a000f0041c42d40c008150f41420702003c400100010440d0180d404040d2484914616407000c0c0506060f002080a401400314101c685408904c080141c10600c40c00d40280ca03401d00000c1d44900c01c009080c11f07900a03589 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 976521348 1250 976520098 976520107
    0x50a15150e0f19030b1e0f070210090501020d06290309160330052b05010b0c0c03030a02250e040308090d030e120a030f020315031c05 59
    0x411202507000c840c01503080040c400008005944961450303800307501402d81e604606046160000d0159405010a80c21094000324608800003541815512000c0500d8031311144e0343e82e01c0100c1c90312a9030111005114030781800502404010b400610760307004981001d110159445480f0361888101440f44900d0141c00b41080412001c1c041c01076403c441600708a070f90048994450305006010350307108aa400610390f15012103c004156110744003446100f0301000c90064100240c00c511440040100032423540440780c5418a25185450b08403020250030011981c4030060b8940d1603108840c819120b100d8002c81c404149400011520106510b03406003042c5950b140755810600301034491008044112100420412400c1c08410300c02d5000c3d9445c0d41e02401c102030762030700300341d80c8000f08006c0500300005101c5440b00010303054040c000422200b561022207180480c0100f60600000400c180004148030400415000c1c0c02c0b8112421000d4503503040c8510440310b003000030519004c001c0b40c0d0910 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 976522598 1250 976521348 976521389
    0xb12090f1c0509090906041a04020901140301020c062d04020a1403070b030c0d0c0206040b180c0a0b040608011e1e080613030e030a020607060c020a02060d050a15 71
    0x4540750480701140c20440d040218101c0000d031000320031510b0380381a074816000c2105008511a001c090000724161040302c0d820140c01084001005001d154100c13904140b40300c0c541e032825811500500a0003040d2140750901407848038007500c0c640d95500032001c0404000c40454151741ca498055940103220b1010035140074114810301103520000c40d0325005844001a5080c0c1c100020b40c4134071b6103403102e07540c0e4407500300c80002100c400381e00240443d8407070b00c100070003d034440310001d8021541c69150b180f08003000d086580f0301032000e0300080d001403240c07c002a2034483c2c00b001d8000e554058a40b081181e883e0400403042440401088034580c1d852081042108001020300e1210142009030951541c1c680c1c00c0d09207010070542c0c00400543e00c0f04602400d142d407040302c90106080480c06006650416000195940a0440b001e40007070756a400f040407030340c02040120095503001d08900d84480000c01d90130000c0c58202e84909240d0305000b910303183c003848802ea010582e519594144404123604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 976523848 1250 976522598 976522633
    0x30609030406021f0e100203010509011202010c0215130e011a03071407020303040504060e0a0515010f1808060f0415051e07120203101703030618040804030b010b12090f 74
    0x1301d68501c0140d039141407001c0541c100b802034030b600010b0030300e015a03694034100031301a903810140e00001c810010700c1e085400503a4020007168121b50121035146a5000c650301c1403010b40300d00790700c954955010050018032112040c2e0554101c5030f58030442c4140a0040c501010180310480d04280010f0311400c000090070000c002502c613250000e0100d90400d610b4001082c111001604000a01002d950410008140c1c1c1d0140d96481000300c02c11660500a080c006065a4211031102c410b100d0100415080c3c9614242e07010000e01c8a40100c0d046420a60410204d0b400107840594a800c0d410282004120560103107600400c1c1e95050120b5004290302c0042c43e0110203402c0c8010411000f150002c3c80c3c1c40b50015602039101514074080321442d10303081034005001c00c0c58025013500240704000c115622000f58461a03254602e1150b02c0d0b42d6140380181d140e01c82d9401c02012441f442c800802d43c41d6803a40548240f114000301e22425803180000715030307a2010800d030324441d64022510a05a41e41c0d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 976525098 1250 976523848 976523893
    0xe180709061119120c080307030506120a150f02160308041a060d02090702010b1207142b031b05010b01030b031515030a350705070e04080f03100503060903040602 71
    0x80c90440c1045c021551040d0491f4010f80d854000642c17a80244205450301c0740100d251803c640300204a42140350b80c82c4601501d4240d0321200707050340c9150303a5000d4130150f0111b884071202c5501a480401d4a4036000e00400019201035a803204c591110700307855a286d520217801506e00030b2080a0f02d641542c20007201d000003c005004554031140c1411040e11802070310060101840054450181420042080102c010610030701c51200180c00000015214118141140750444c11140c08800e0b0704007500c00c00c1603103040b00b51a4803004010424000103500054020200741d800344902e002040030144c0d40e296400c1007180c1c015240c400b0031240741140703941005010307002c0c0547c0d060f19482c0e11050850282003591103010020b490075400c000c802c0b1102c5040c0802e4000c07181d82001441c0c0c540700c3c3d642025002c0d1080045040c0d0100b030a00c86050f09071840c10b4a40d0085546d40d2134106032001010025100b400c0c003d00c0b40201051482e000841601c0030740302503a0003004441044401460080380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 976526348 1250 976525098 976525133
    0x2221a030a09050d090602100b01050906090a0308071a010b0307020d0c02041116110103111b0a080c0f070b1c0b400c050a0e180709061119 61
    0x40d55466100043d10600901d52110318545416884501e800ca01074100200311050407425454110149866a0044243c51180b030003a608aa291041ca42c0840c01d00c8406801c060301f9240081048410810b02c0c5200b00052105000c031030b805a681e500040005001c103031003107000b40c0c0110700701008103881410b8002d10640028408160030380345401038890760348682007203008100c00028807070034040003003401c044040d02843c08100e05a00404101c1244c0170b0070460510301440450544421003040061a40741e0350441c3d1015612142500d213075503124180d040800712401341c1000062100e0310807041c1c601c1c240c44c2c0100180080e081c402c03000020305100300060351101049014044103c02d4580320818225a0b20001641102d0024a0040e21003200d1239940198181411031308d4580d80b14082e580c1401c0c0a041c80082e0b8500d440000c0c03441c0412040c00030006005d5010411000d911034000700451b0b02d50303155100c80c1c00c413080c1c03542d454070055400c508003881d2142400380050003401d92a843e022 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 976527598 1250 976526348 976526351
    0x17010603021303080a0e2407260423090415090512030408090a2103031a03010f06050117100b03190501030515090a0b0f0c070b01080102221a030a 64
    0x280c42c4c1e03590304480e410028510000502c141d28040c0c603820412950065a9038000404203041a0480315400c10310460500406034000d400d01c070000511100181c0c038440a800c0030450325180c480c0c540700000d41d1407003c000340042000c11512824145031100b1400740740c01548120700c11120b001e103400a01560749017104c1c0c80c82030201130141c0d0403152020703600444c0b01c4d2451641d070b020304ca8201324400c100b41d00b00744425401800c1001e241072010304869441380c0c0c103003000f003903000e40c0c44004121074105603c0f10341c1550078440c811461804603802581503071402d0700c4d4400765504030070450405c801d084561402c42c080343c10040c01052104800f55502c09880c0704000d220880c19181a0b0550300c082e03004580c640d000c0c035800c0c018115040001a44485d8100082c00c0260507600c6e080ca80c144082c240c45074a014041c0401e50a000840459000541190b802007040d45d503080385600035481803180034a000002c900f0014960590040b010803550103040d5400c010b69040007100c1251f2026282402e1903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 976528848 1250 976527598 976527637
    0x50a0e03030318060708090a0308040606052709032110170d021c08060d1103010c11060a0c0903030e04020d0905061e070c1e0c0b0408010c1701060302 66
    0xa590800045100d401c0c0c0c1e41c9060080d00d1594990303460408040c0070401071100782002c021f103807180003d2400c40c05806140c40e8a89890f1030a0440080c041e41d0401604603000384402c60411002030018100d07030078511004045039840586141c0c40340503001121140b11130301e80064030072046c001441e54001c2e20224510030102d07540c000c6c142821450021448860708070500468407141c0601810403600010100e140804559220041c490b880041c15203204000d0b00c01d24000b4003c0c50448034100c0c4502034000c10001d01d031420007034481104074120700c1c00c42c4500000203101c0380d0740380507542d000f0780183c41d44104039096035015a202c00000d034100c0e07001903080c04558400d60290041c0e40350280204041c1000341011031140075001c0e070110010100146001c18000101c0e80300c40001c010039005100c414500103019031000c03146034441c4c130240c00192480408100034400380300070411a00204000c0100c440340300c40c140c80f41032042e5070b8841c8a405040041141e03a010390001c01710510507030b0140050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 976530098 1250 976528848 976528877
    0x30f14030304030207230901051e03190b010512030a140c120702040c0801030203060601031a040606022805060a0f33050d050303010605090a0f0803070b01170a03050a 73
    0xd503003085400360010b9020180800c54032144001b01c009110404040c1c040b111032450110740d0440c018429140250350358a02c1000c10048244031081525000b401e40318402821809200d600710342100a5443c040008000580c5260a408800c010046030300039505003100c0c1d00c42943c0c031111764103011149140400c61051074050501c4620700f200c041e41d40741030300d801c00c90051000721942c910710a81400480310051000d40c0d00080d0096001a092801250080c41d5100e1036a10480b8051104e40203805c00c0f1010482c0341d00031802c140070b02c0302e1848810000000104400c01c01c0504e01020b03000c2e03000000440d16058a6422100004401400106540e514a800c121940c0104034070b41038101c1a0012144a0040e01490309008280c110750f50b43d000600f0313031100e688911040c4030f203405000000a80c3d425603211050003030001e000580ca83c05078143c2d9072400c1c03501c96020380d00846410030108000b0451809501c0c1a08182020100404655030320360ba05613030a40c455007501c0180040c00010a14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 976531348 1250 976530098 976530103
    0x180d0b040b090f0610170a0f29040803041721060a03050d03050f011502100c0908160302101e080a021308030c1c050a051614030909070801060207030f14 67
    0x80c060b042c01c03d203a8078505040b0040804a040d545d0031039811031151000441d114803411840b0390382145000c00308081060803085110b00d6a01ca1349c180e80410810041805007400145100c0c038010b80015013010501607061042c3d1281c2c2c4050740d0750000480210007641011040700f940210098907030f140c00c90700da4442d14680259000c00400007900c4600700b020005018a01500515550061740451000100043c0d251070b480d000440d0f06540c1c50307100903420362003004040003d09915068440c1c0e00200501691106c54a000590040a081c45d503030710802c0c0709812003050b4440e090704220060b100060115007200c0c010b440041034a0f028400d07c46c80c40c1c9114411401000b691005583c0c90440040c07132424084007900300400c02c00c0010f4002d4134550018122070205a6601d4041d9031840750b116001e009440c0004082c10401914886030308440000008080c1c030030044940c40d03c942e950100803900c4840c2405041d0040e0080a41040010f000e1840d01800910911203004c801d0041007441c0d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 976532598 1250 976531348 976531351
    0x11203090b1b1c02030a0e27010f0e060607020d020d0605070306051306150819020a05090f031f09060e011505090901020a141c060308180d0b040b090f06 67
    0x190300e07038009080c110600340200a640024906451804540303941c0d43d0019490b4050682c406050210062206040350341d1010998501050310980389050f5030b5151110007000c20034014a241040403030070205454007a000018481c003001011b451521030281d0a00c40d042d21a40d0040b80c00103103403002c0c3c4000401c42c2c06100d00c10041e655000803c6031401d000c01c20102c1036070701004a102e01d441070500c40340c0300c00c844818005e01e03079040030350781c644814058980b0000540180300c0c0c010f02c086103040720301d6407040061182d0072086404440010b031342c80425072103110b02203a01c0b42c0301d001c0024607c403000098016840d002d000e00000181445c11000e0700e820f6401c0140368240890002605200030b04d40b010000750800c00200003181083c0504a0280280d1008010240c0c0030f4404102d01102400350840a514407480d84418004183d5910b0301c100f181c0c0101c400340e550030042544603032040c20800202c010f85600a85000c0d950f8a854480c04c101c1e01d0094149409406442c00709041e140f000c01c0010b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 976533848 1250 976532598 976532617
    0x16021305040503092110091a01090f06050433031e05010c090e0601301a04090f1b05030601120c0e04020607151e060317030f011203090b 60
    0x3555502a09000c01c2905001c5c0040d080030780c811040e042a200c400007030810540b043c03200002406040906110101c150400c4440102c00c00040002c130b48525241c1280c00004c01c1c0c05d40521802d0346990420095540c2c801d8482541036040341950705440c410954006024040b03d91004015240c0d140c0840f208880b1001a03607643e50040545d04000c001d11441d0141070461074805031160805030350500d0110081c0103079042105000400d4000345c808900c3c8400d09034841030500f5407500e55804100a458240c1320024a038075a68160300b02810306000b11411a80e000070000c012201c243e69078450340300d144041d0100a0103500c40403845890820240d0302809a00b441075220100710310f04403090480b81d030460010301c005142448016124081914030302940304040d0019441c1c4d100940c8010714441c0f540004a40c0e980111308011500382d84242c0c2664000d900f40710f0f03d1852550030411512060302c420541c0070130b00c4c004001c00d4002140f020310962080c41c0480380655259140401034100000c0c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 976535098 1250 976533848 976533853
    0x608070305060a140a05041b0305150f071710030b01030506100807050a050108060d05010501140307080601052101020f0403080c060f090c01050c0c1306180b06160213050405 76
    0xc0c000d00000300490b5900103844034090011114079a0a01c0c0c80c404041c2c0341320002c81d2a07a022600300301c540d900801c00a40e42015240c0042d9590406960b180c0c1c0401880003d03080c1d01c004502000c150120320385c400c00107a11425218074002c40c4941102100a000e0445d007514100003000054801030500d009600441c020020340c00c21500003100700005500003081a840301c2810000c1e9210724402404a41090070821442c0c0d4503407011039044100c00c0310052181d46400c00100302a065031040d00da80724825011608141e49036041e00382d4840003809202e07404020081525005000729014820a82000001500381820401d6010190700541c00403103044c440400c2c115052001045140c0c0c0c41000381e80b00c5802030600415183d00c40030a02000e604002c000102062084402c01c000d264600c0c001d082a840c81c41c0d408a000010f1003c1d0203000000c00801c0b203940c2c890100d0b0f004503201601c005081a26000303042c030101712510896a002c0341c00c1812103d1042c2c0c604054415180700728001c501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 976536348 1250 976535098 976535113
    0x50601090b0c0703020f0d0b04060f0b0405012303070f080601060f05030f0415020c1203090705030d0e010507140d0c0309060c0b01090203060612070f0306120213110d0608 75
    0x545400c869800400d0749400c00d00c120a0000c000140680481e6015205c86000c0d40c01c80000c145200c00302c20000d04505040750600c020032120354460640340d28030540400032440d20310104015920280300341000c004000078403410003400203510411421005003115580c80c1c1d83c1140f030001c0a625804035030f064101400400c02150041500000044c1d68502a4914a0300d6840c2094800c009000500710084c2d40c1d01070b1562903483e40c100c800c6500305400311540c07200c171a0b2222256a000310340540883c00f400740700280c0d9003000035000303c0d444455100c14801e002c03040c004403825003060405640f882400c40c0003054892062264000110716a610b0001c40701d0746080181402c0b03071a6026030102710000005a0210307903801405415103c4146000d0b07642e44411001901500130080121090710001052055590300b100c5240381550f00c0d520300348100c40d95100507070106010036102940001030300000300d040c061190701c850b01d11800f44481d6420900c000840c03e0841c1d00f0340c1c000c5101e5501400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 976537598 1250 976536348 976536361
    0x90c090411010f0507080a0e04060b0c010b040e12030a020a1b080703021e03041e0305060c0d0b0103020a0f11010603051603170a050913061d04030f0c0b071103071505 73
    0x481c2e010000250802c40d1802146655420940c81f90060070b40400c05d02d10301921056507540c100f0001020441d60460b11042d510341064000e04da400e8002e031007585840b040701e02070f0b00b0214190001d000c072039440c035096030756081600010354000c3e002582000420070040400504025100c0c00303440c014007005440c0c02261030043e00c1c1800c000d20000a001d241500c0c201600070000407203058071106100482d03401e20820041300b01800075003005205000324410052101104000f0303041804080c0350600540180c00d00640807881401d00701c80005040812100e103150160b144d8103540111040005051356503030b02e4090500e08424241040103030590010024003070b4904c1d00c80c1440502002c1185441c110307060140161095403da90300991300202c49840d02030700c55020034010658003c440b10082c104941c03031211554111011000708401c0c0b10201d100300d2143c0307490300c000f41c0e105400400310f441d0003c041e41c02084ca41484d613900e110401180d000520300d80e81c0202150340604000c1a281802e9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 976538848 1250 976537598 976537607
    0x40204060c05100630200a060f0f030504140d1d0102072d0e010609150f0e121f090201020c120601151101090b0f0709050f0405090c09041101 62
    0xc49001c8880d44c1825420b016400c202c807400030306400d0a0f140c0746005840c0e0b040c6002c60074016039001c0c1c06009010294002c10010070900d404101044810340c81c41c503201c54050300d03040b10b1305a41c0c6002504070411010014007075401290070030301079540c0d0105000c444905a2402050200318800100c81c1c00d20b90308218101c03100c20014040c02d001401900b418111441d488000000000c02c0c500f180c44081829070000300540070261030326160740302c030541e19400081c01c0c482041c81103000054105000704e41041c0b041c021111202c045680d00d12102e510403040003066125455001d8a40c0200d051a0055131a40e204607180030b041e072030000c1501c00c0b941c000641020704030b400c4140101c7c0150a5000510004501c0605541d04072900c103409203900401140c032a050025020344545ca0710302c000082c013080c01c1019200d26840c401c000d001d69203e003000c440348074141c0305a5400a1068118210b20b01d0260807482d44841020111800c14110400050324480c040d5003d0301d000302846508981560710 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 976540098 1250 976538848 976538863
    0x40030605010b0f031620030702090f061e040b1306051906140c0a150e01110a02070b0715020f0403060b030303060604030f02010e040608010f061409010b0304060209040204060c05 78
    0x100c50b8034506241c002c1d55400128400102150004a180135000e800c01d40558000002c0781e44803803040195145007400141c0d240c4c4030b9207069105154050004a040303c0104c04140b03d424043d101c4141d0f022106144034881c0150394040e82d10649400c8000c01d591240c13154984001c6c030100b0701144003480c002c2400319000520710628110f12400f24180715554010b101c0b19846614002032a98450000c4030706070811503008001403d201131219103106289880d003114400030b404a0003000b800c0d246910600b22403040e170322094003580291000700402ca41c2000540b4000d80503440000e0b0300c8100f10354110481c0c0c00013412404a16002c6010310920806105440d000b081c103500841ca0360502c02d00003480341c041d51000810464030300e5610741c21079100742490481083c014005000c0b6689a80c1d50394041d003040341803620030384d14000c030020300c90a001c407901c0c001c00805880b801e216420070848000540c00100181ca0f45502005003100584071072005000810250345e607416441298505582030450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 976541348 1250 976540098 976540109
    0x4050618070903052a090610050c0a0c030605060108090f0d050c10052a3603100606020c0901050640030b15100e044d4003060501 57
    0x240c46c405c000380764941d584503041622113400d05c6030b260b20186088500d40180f03103000408145151303500004110031a08403901448090701d40c001e82c0e1b41c68070316541c0e4503000d017a50b49002c1d0b031000e40080c10b014083d0008004540d01d0b2800e0703803050074505c41719070181c41c1e09490f45154403100340035000c440405041c2c650041c40c0020b00d110b10780183d02c03d501040b03814503500006071018551483c00454502c01c2c840c445080c6c0901952241d02440070890f005041c203201c0c00c40503018000c403508003841e1010310316041c0c40c4010420703810040415100d0038901d61303502e902c50820005400701c0e11080c014403030b034110308040750b40c0221510303043d4a4058030450019108191404264154450715940c010003200045045d1500000460b40b00f40020003034400041d90004100402001510300e075032402c548540d41c010000664a5000d181111998140f0b8800900c1a14a030500003000e0481d4180503048110000e41c0c125168500c260000c1c0c1c004d00b2070100580c00101010404000f082910700500d1300504c1e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 976542598 1250 976541348 976541359
    0x3040507080d021b0103090203060f0f01050d0206161412040317030106021905190804091d0303040303090203030712020c1201020a0e0103020f1b07031104050618070903052a 76
    0x110b600038080e5641c116400c110322a403a1021000c4020b920903408490b4064004044504a00f002c0b045500003103401d07135094904204c2da034008101400c001010b0080716601411507031604911940b07045002012001c00c6400010103000419409000c1100005980440410340d0f507030b81c0f65240441c910000001c45120009040c00104103207174003c22803401900c41c81841c0d807480041c1d460018142070f952143d1812500340340701c5543c01c0c041c814000c0c0c07065403403144080166100642901400700500880409907510810014000a11941003000703024170240459082c280340ea075501c256581069104d030700503444140406e41c0b42c1f034507070318a034940d0030013500031071902110b000000d1111449403122810715400013200600c0429550440f201030942007112441d5000201c901d03610742500b4401aa0400e03680c142c03402c07203171500d40328031030007118000e02014065429640c290300c0400300030800d000f4410804800800300b0320038803440d403419080305049400c68031141c4541c045155803401450091 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 976543848 1250 976542598 976542613
    0x306070509040e0c06190e030102090901031202031e030a05071103040b0c07030c0329061309050322050307080313121509230a050a120306080109080304050708 70
    0x854014040340d4049030140d030042403000401d9040c1c0e03d4408110407890f001400007400100344200e40c0c8460404540d00d40d1582c1c00030100308100741c2030f80201d580c519032103810600104009240780e4100240081e450045d82c0c10310110300c01e0b0502c44c03990344101d04054440082086441000761003071320b5001c00745003440e5080c8407080d280a5540c0c0030758002d40424107000140d107542628100408002158013041e00340f4140c0d140c1c80c0880004a2601982000284240a100c0c0d1070350300c1030005226413400342243d211022840461800741c9042d17001605c0501080040f1a0103911200d481c2c0ba40000c0c2c0d90549001a00c2c00003450b14181d01075202c014a604140b00b05e0704450042800d00e42190200c07050850026050704004800c1110481800009860b054004081140b11540905200011004d1340080c1c12000080c60301c0d1031900c04010995000300c40c1c00c5001a1020103410405041403600040c00358403541400d0868020540c25103400790007004020800504000c0754024003040800303030108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 976545098 1250 976543848 976543861
    0x1406090f040210030e07031401180503120601030609020d0c0809010b061815030a0c020d0e0906090a060b0414030d0905010206010e1905130201320d06080a051005060306 74
    0x140c50300500000c0c461900914048500d52290f00048121000782094030b68040e41c81ca000e910444002d4440301442d400e00c00c0c2c83c030041c010f0320006420142c02c0f40146281c0b14030150b40c9a0a040700030000f6041c55503402010a9a100a202130810007141c1b80340003400003515040038004440050004e00300742e062152540003621400d0603100f007400c0392403020710481c801c4000282000c0380355981c02c0d040c8002104010400b1140d800230200402903800381d0307556040704e00c02140c0740c00d03c07810001d400803010004106a8148030003c903910000e604c0d00001d03403d849050b942a00e5000c0da1010304642150413003144c1500e07003402401e10490aa080c0820300e6468400042c5d10340d10140f040403504014040040e4084034010105050714500c03d400f048a8640280800c2e1032000b450407e80c006000c1d05482140015100120940880e04850b40c00710107010240c44079066020402c03d64026445500005262208110204400340728402800d05a1000e07030a09048030300c0104058400d82c8400280680d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 976546348 1250 976545098 976545121
    0x1e0e15030721060503030a02030318071a1b030a030606080606041d09011b03093c0f0b010801020436021810121d10020c100f140609 58
    0x948403800d0006000260752090b410300510b225072104e030700350000044100c5503581c04402148a0510b80b201c44141d020400e401c59901d810f20b000b001101d0050080d0000440c4445000c3c04080e00310340341070b8880c03800d400320b00350a5401005407036002c81c0e150407007844800c5c0c011200351380c00300f02030380e100e404c1c681341c0303298050103010f88800d80f082c800c000c0010500f681420b400c1420390001c0f01801c01c90301402c1c810028024001e50a0554080c070b40d41c0b1a10700d007860060302201001215070510700005010b5603000710140803d032411181092880d85e050005101ca0300d60300e00030f059660006869914048501a40184416a8440d01c0505190400703521810a210902543c0c11200040e184d41c807201542d0480b0102c98892584440c01c0c0c1e8010a4a50b440711082030056940c0c901405101d41b410b090012070401c0c15070051444d0081102c1c10402c803115401341140c04600720842d1a110a40d8050804503483c411114428030380740c5188a0303000101e8070b03072681c0228082e10402c54600c2d00f80402403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 976547598 1250 976546348 976546367
    0x115030b0f0f06220312020303090d030c0903140303010602121c15050402190201181a041a0705040302010f090501080403080a0e0f0a060c0e01020d0f1e0e150307 71
    0x14420741c281c014400182d00d82e00f0a50300101c8400f641036410701c1c620b096911442c40244001c60703444608405003d403051010080d40d010351640300c02001c60b814003403419030103000c400d09600200306072084000701251610040d244036901190281d80e595040c104000c2c103040c4000403082030401b0801c000000c40c40c80c0f0b04c04000c400c11240000138921020710310b1800403902948481e90040c0007240381c104900c000c04400354201083d4000b00704070001d5440003400c0f03001114000d42901d4001d9450079880e010044115801441556030310190681c112000d40052405e407070741000038401190a02c215600074104148201c00307400c1000410b441c00c000201540700007000181040201c2740455400240e5401150b00c8804980544000300b20310039005698901580d426035005003082c44c0125841c0c000e503000c00c64500c0c1a405015684160702050341c003900e000040404124040d407013090ba01010501441c0b030304400f13a680c1806503440d0f070704011610030b40030412203101d0410410302c00d02542010181 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 976548848 1250 976547598 976547629
    0x40b070c0c142d0108061f0809010e0d1d09040c090e0106091a1e0a060516021f030f0506130b0612010b09030d02030406080a0e1908030115030b 63
    0xc950a100792400300391042010111800c4000d25004100003e1403000c000070b4644600780d8030440380b50343e0201004925210356010a40e20b181c20070344800304510514507664444c50071400882d21030031921741a450031002340300400c0001d1422121192032000703022000b0240004684541a43c2041d864101320840350380704012001d6a0344101001800003904008024451400d003088620011019541c08065051a1070b20940014041394002813824400100003400602400f0442d0709040307042d0f4481d801101e804060003008040b230001692442c10810f50308070000007540d0910b10100025043c1c0d00d2100803094010305003000c00c195500c410700d034114880c40e174a8020480c4200c000114000b40300700700240d901c1e4034140c800492900001c80050000340c0003942103503852121050100d0b103030701070b80c02440000780309403001c5007041c940c41d000140100c81a0080c0c5026082c2c4580003200700c1d841e040c7c1111050f0000c001006148840407140c2c0040ca070b40e003400d0182807015030000c0c07406012074050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 976550098 1250 976548848 976548869
    0x60a0b09010e130203010f020903070f03121413090c0f020a0308042303040e102108030c09031005090105060420070503040e0a0b031002040e06150f070605040b070c0c 73
    0x42c151590f03900c9422001350050000c11990340305000303942c065400320350305500034495107200168449031491110200c2e41c129241c03612028010038202c0d100075a454900302c00040501c04140101c5088030000000d0580039000103561032500c60251002e1408400030055403c508050000309410116450f03105601135600c554041101c51841003000d258040b14000e03200c0442e001c12410100038401c0c0c0201d8621a1506010f95554022101841c0711036007a1441400c800041c0002215a809981c05c9000c80380c0183c00c0c0004140400c1c40e04210784042c1552945420034004001420311410350004030a40d02131110740c4106a10203e02508808651010700e00005e800007404401d1043d00c000e0820700301820f8850601d003940c04003401c5005c05061181c0a510f01001d00e900243c42110f040760b46400006800796074034810048410515140340304d0400081040c400303980451801005501e02c102d200007110304140c100143c414000034060014021000140004102103003650011241022030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 976551348 1250 976550098 976550101
    0x90210082e050901091b0c02040b18040303050114030d1b0212060f07050a080103060c0e040f151719050106050a270c0f05130f0306050702060a0b09010e 67
    0x4200200c4000034282803601c540c000280904294411000c4007100ca0072960f800340c903603c414414048680b019006811a0050301c6041e051a0144480003442c600051000134200c54031000308408869044d480f04030700302200c04000426402d40324040c09401480384860400081c81c000c6541e882c500007524082c00a00d0041407480c03980c5c0410000e10743c0e4082e02041300c03500107a602c00d80d50441918941c00e4010380400041a6510071402e640d6a02041d41e07076036003964690b0715080028200d5a00041c00c2203014044215280c0311400340c2d01e012201500009108100341a01c208100350b00c2e0040515034000394142000544001038001c074045207041d43c0b01503010306180c40e5004120b83e902c081d03081800d002001503400450580c0d048107240c540b01e54030100080c10103036411100b40301683d0010075100d109034003140d8070601c050a8a001014140502280c40d00302d100024481d1b81c0c03048a6441c3c0b10400c200f03031140e0601000d500310f0780c50101840070a110f00d0000d00902c0050207000a001d1340e040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 976552598 1250 976551348 976551361
    0x91005010e273a0306061d030705120f010e0601060f020f03090121050a020d0b09100303080a0216050c19030c0302060304060906020c15060303160611131203020c010309021008 77
    0x1c004100e02e02c90b0084200610f182e401c03014003d407070507100719004030317021b215452080c6410f2401c0d0804604000e002d0103880b030400d810001c000f8407603441451320f40b040e010101d07403003002449040441c590302001041300713600d0400005e00143d900c000c00d00454000d00300c08180201c00006445540d4400d0a100c01700c0103040d085000740701c0140001300e040609241c02c5c0810000240e008112003048503005101140a1005201c07a5001c00c6d00c40c040008400302c001c1020a100e0040d0541080d8003203000342c5030449081449141c24000c117026102d43e0001c240819261400c9050749801007040d01c0308031804c602e03584603030101c50614480640540000000141080b103564400c01a50340d201100310340f650741b11200355030381c0c501c000758004202c01030720003003182841c001080d5200446040403040c0c102003556500c0d801761000c1c0d14565010301c0180032811818003080d410101511030f11440446144d1242002840d0040e40354070107040c18030340040040540c540d100c00441030402402e00440684424 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 976553848 1250 976552598 976552663
    0x1d04050102070506101d071715031629041802041a07050d08060f010c05160b070303050a090c060c0302120d0608060c16020108091005010e27 62
    0x102c1d0001c100e402103404200b02c1c3c2c2070140c40542540c0000b4094041016240d44a4521250696021000c1441300120340020342d10301b4200c3d50f0210040c60400008009440428941903641400d81d0364107441140a1100500c001c14803a8191000300101c078080500348541c52980c03086015000c01150f840c4000e41e00c0d40e02e02c2d012100101450081d0780c2100c20b41c40583c58031508485001c42d5940100b01c0301003c19031041d0345c01e500a44008018050883c440d00041d5401030a011086815006030720100c60b50080c4000c19000400c01d0107010356982415140080464000601000c01c85140182c07120108240300c0001054412038144201440401d05080e842c01d41816440042e202c00010f100924a00a800a07411601040c00711401d54960249a000c02e000e0601070458040e040c901100141d0300c5196540d8019110b4410b039481442e03228103034015100260400b10760559000700340032140c15207000d09820780c90302500c15000841805242516482c0c80c41c80e12602c5c01001d034101788810b601 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 976555098 1250 976553848 976553857
    0x1090513020c0d050c100b10052206050304020307080601080c010c0302031c020d0e0a021c080403060507050307110c0a0e15040e0606180903031b27030706091d04050102 74
    0x544125802000f104100410071380c0314199080c0140195a060304032009240600b1507607100051010306003000c001812103d03604560048030600740c2c60051014112441902e84010340003e60b54241d480c40d1074018540b4140c46e41d40084940d610040c010065808d010960550000303091801180680180c28121700e107000c2c0030354142500c03000c00c04040030032040d503000b020b200501c4c8006001c1060440c00403600c1d019028000380d044608034000c071170310f00c02c240609a155441303507a083c0e0509842ea100c0500b00c4504540603000b00b04000107004440350003810b400d2b00c00d0716020080100c03200348800700e03103140514403490884840070320100c0e5488403910364841c51410060300805c001c07010000310780d9590409a80340c6009154000032440001255008244540482002940b541d00d0700c81805001040d000c1c0a100c0722070090112044890418030311010345003020005c3e5000038080320401d800d10035564440428010340e0401040340b2081c0c00745414401081d09607110f070740d41d11800d01c02e019108 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 976556348 1250 976555098 976555117
    0xc0309031a060102010c0908030421120504051f120b1203161506030203071a040302040914010507030b031009021c030503010f4a0c07020312090109051302 68
    0x28180010109990107050951161000f64000d00c1401803401c02550481d1140c000c181c4290000c20051108003840d101e241c11103c000a2140420840d645132054a4851880030b400003030300014041003079140110428036000300c020145131041d2030b0315401401d1101c2c085401d05501c0c0d204e03140017401c0e50340c0c001c058414050b000c0950703a9852101400114080c0ba410040700c50b140d40c041c0c061307020f001900c2040140c0340d02400400240d410441100f84ca078034461101c0d542600b00300b2010005846900a008409104290440440110494a60075584000c2a080c2018074200706003085a0700010008014064001e00140c00303481400416902c07000f402e0000100d00000900c102056404030040d4101c51000e10440201d90b2540d001b44040c1441d0304d0300b062000d03074800c02a01c0e240d01d400103005507101c00001c03015106030b0304a8000ca420304111803404980c0004540d40040d82020b220205040321011422468080c1c2d500000e40344003518021940107903001c4020300c240c03100c0355045826a06 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 976557598 1250 976556348 976556363
    0x101e05280b122508150307090b03010509060f060402130905040b0403080c1303080901031b022d100203060102031b1b06030403090e060105090a0f09060510020606010c030903 76
    0x948500e0201001e40c08103842e20840c03003040000841c11100114207080c0d081c401040e00443c556155012682801e0203000c181c40380c1088a0701c0646981d0070095903008080e8850040390a001e10f1381058210f40004001c03c2d0a90011400c000500803500b0314180c0c081c004070f6005841d40f00041c1e081c1d5071054940c115030205846e01e014402809800004107200310300c0b035540c441c070039621400f03824203034014040c0500c4101144c40c011701c001107000e000703010348000614001a070030b0082e90064600e40d5001c40c124000d42c1100c2040341d0384a891052901110590719a81c1c052101070901c151703520844004814500b0750f0201c041fa036503a02c280201d03082821070303002c00c140800129540c9070700c4020541a451180c903840251506a0a0400c2030380e114a0300354403504c0c242490a02c1901803440020101c5040201c03c00c119001c503629480743c0c4000d0420a403440000b40d080903001000c4a400d500660b208880c3c400202034000e03400610154080401c0c81d04c0d00c4400010300d4280d03104005a00000c00c0b15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 976558848 1250 976557598 976557679
    0xa140d150909050f03160206072d051c05040909030302270102011815150801330305030720091e0f1006080c0f030f101e05 54
    0x100000c0d0000d0071414080c0f02a61400305052009503a01d104030f00c468040f80030410b001c0301c090300d064800b07801c6450041002a205008024882545003224034108000c0044c9140d01d03421300204120071000e4040306400703201e2803074800901402c1c40c0100c2c859031401d20b03201c040e40e00816101c0d070140c448100c000e02c041889406042c40307141c90360f100b00b0701840c015842d06085645000e052000b8824aa810030301020300260300100700380c00303000302900803140b03c103114200007411103091003002182c600c107104282000d0314202e4008007160b00521415210784401c141400450f00100c119504a50310000c143c1c02030004601056407003104040c2c0c0ca43c000e407004200019611075400c40c00d003034a9280c0526519070380302110030901200a031a40c09089100d00c0082c48914060444150001c1d03142da4058185000c41c1d0395144c3d954800c4800c0401500580c0c28005d0324201d1031104800b402058170504001700c1c0c10f01503040f280c4100d1040d1441800c1056a51207444821000c0f04048880c2240f035180340d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 976560098 1250 976558848 976558859
    0xd060801151406130b07030c0b1303020c180c031302062b09200334080106080d0818160f092906040801051501080a020a140d15 56
    0x100d02041c401c0708690100781c4030303003402d034903107001101c11201036649180012401d103007020505800c0201c2c200c0038000c98540c0100814205d1940700d100701440340580700900740618001303017008240c000960040d80e121460468050b0b40c041d003661300c0350000e80f8040d1290341d0320781582c3c3c0041e0b038103d020b50400000202c40140388041951030400014060f00400301511040b85c2a0841e0103148000e001100751038160f2010104010701546110002002c0b1840441c946902203040d141d0400d0011004035220081540c41c0c910a1441c401001d400000308403003840d0a2885448113001400300f400c100b140d01c0020031606e4250060640488410308031703030f003e00303018001d21500c83c00c60149006d044820100068241914000c00c0c00d8a100100344104204155405850103000700483c60b5008900303000124400d2024468188642030b070035040152030800b000050080103019040c0324106004103c0c546240d074121030820845506201000d584e096050694401046148682003e2085580b4001503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 976561348 1250 976560098 976560131
    0x231f02031206030f0c0f010210060803090102010b10020a0f0212031309051f0302041505190e07030b0f09060a15031d06060102120306030109150507031b12020d060801 73
    0x310945250342200c4076403030700310405649030005010300e000341d80041100c0c0068145100030a02c420710600450b01e110045001420079144039801c000c1c065840031655100660b424007454100420980b0440c14a5004200007034440318070903006403580345159a81004c43d21903000d007030f03070058651040e03d0711072103070b50b41441c021011407168514081c04c0034003203044142413007018009552a500d420a106241d40c2c00c1c000502812040307905a443c01440c005229104d041c040c16000d40205002c4c80802e00782940c45988900c094a07820030035241140242243d2140c281d21030025070200e8900c103c0d65207001c00204102d2458104204201c40207130300300034035070b01078000580c00040480d03102d1154a814500c00d540e101d0450311075005a02100c04d1000001840e001160040c50141c008100500701781c94220704460b0850701d2015203a982d03000c1044155151098440308d0080c4c42c7c00d80f03103002c4800300c010440423008010350180c0b90b002800983c101d0382580300078010841400240301a4403000800310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 976562598 1250 976561348 976561357
    0x1302060f0c010b102f0c0a0b1c060e0609131407051305090607081003020607150f0b0907110102092e0e0102061611060109020d0e010204231f0203 64
    0x1d018502845003800b103107000b005c0b0300b00c2920090b100c810100d04007132030380f492403007405402d02014060115140b00b20745401e1541d02c0070308181907035039a5900b00340c2d24131401080c010f001c01142c549000c4c002c0c00040301e401e00140d0454030444400159846554152034901b100e03c000034180348a9034496009484040740784000c403101121040040e59070304c0c0303840d42511821542a51180c10040c00290610b0043c14415000403e6480340c1d5005520395001c1b4842e940700307501c20344a6002e43d441214000071b01c0e0141080420303441d0424440b42c100c41003c1018600b0141480b01400600e0681c62000710096066600c60350009000325181d6207110001148013000c001c241019881450004c500d550040b120400c0f0f10b001070f402000c941c1e03a6044010504056481c0380c40800c07800c0d182003803031b433501002028003800f8044d100582c2d401c040da42100c01c6030708070b04a07203016034014002000b1020801004690401400d20010a528000d400040d805545241010183e10390303203000715442680007010f031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 976563848 1250 976562598 976562621
    0xf09090b040f0615270509091e01150501021614060706061d07090e0408032d19090312020d1803080603211c0b040e010e0d0503010b031302060f0c01 65
    0x141c0a0032170180980c50041d0700c0801400761242c4c40303200300154100400c5c0150700c0100c90066580c0303d00c4005040f01c0f007403456a280c0301541e441e07400c03c40c003140f114007031407006000900003072880740b8629004101c080194420242000620103000405850b0b01040324042c0398440020040503480e0503085d1446004042c50a410079482c030001204035029054120560300c0f61011801c05564aa6514200d40c0c001400f002c811903440314441640654084a0800c00c511030f8403202003440e180722406441419808221242c50800d040a80400e401c591003100c0c43d07141c0400565103111703170403501002c0c2c40458188504440108140000e01d640000000d0142c40d0481c1a2005465441c1c407202c801c007905030003078220020400c0744c4082c0161202d0044181c200090340418400280b800003400c03151802461a04c1d42d45440b0542c019040500080000d0111428010b0442d41008405a020f0000520320064184403078601c1040d0740d103040550700043c2103050010b603500d580070035081c060250100103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 976565098 1250 976563848 976563857
    0x80304140402070b04140a060f09050607140405040b04150807032603013320030a02071e0302030703030302180102070501050a03020711190f060f09090b040f0615 71
    0x32089142500885641c2d40d005000300d80c00c4d0300e85440d02c920064030f0f425682050b100b040c0d0b2110028907036009511040d041050001080b081909140b030818100402c41c0e0104500714440303200200c0e10100ba1800e80300e00f51000101c8450f43c0021800404107145400d00b0040640b030001450341d8001045002c1d01e21440081c00042101c0c02c00c01d440c12004030904243c1c600a000501228001481c000d18070058084007050007465039010301d64469098540388005194001c090502d81c20f0010300101c1c100d010780c011450310341c0310640291555540e010b0000e440c1508030142c0701104500340c4031009150014240c600306542d03464050005c1d400f10680200c140240700406c0280d600124a000855006855503854070b1240c1c00c3c01c0317000307500c9400112140c0e01d0100b90484240c40d294a01c8080c0280020600211800c0c100c80c8004800d15a12450420201c0c410b0011126841054181180e00c40e401c00304002428500280290410b00140405c01d80350140000b0302c2e071050b82007520319040755182d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 976566348 1250 976565098 976565129
    0x30610050a050315041d010623210709020a020307031b0510051f15030b09040302210405120d080c12150301020f030f150a050d060b01090b04080304 65
    0x1020340e45401041c1120740452818400224100a012108441000020b10019140d44032004030300c20b103448000b80c01d0031030303544860a11130700e010190a400b81200c0451803081c40c40c0b400c0d0014200d058030003404141c8010000034200c5d01501040042d018013120501076440d8881c0040c000d40d00c0d00441c0703050f8001009a9003042c1000c2d0398003036080d00c4030340200150824130200b83e0140301a00c00648003000c1360011050349a401410451504040c1c04d103142d03040b42d114a4400010107840c0b2107412300340304071000404e1100084e000140e134000100c40a00345244000e514414002c940a280e015a82020240c0350005001902258409018542e9104d00d84203486611180070b9070301075a141031580800b14000b150f40b0621142c2000301907080100050320300392040211007103d0308150323080800c4044540610400103413508440180d088255000300000c1c1c9441c0016004070b1405070b02500e02503442c1400013440c0d10503110400905001300c489039641d6550302401e69203a02610941504554014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 976567598 1250 976566348 976566379
    0x207050105040602150603030d09080d0f0204150309022b0605090601080709091b0b04140301231509010f0f0b04050303070803090a0b0420030d0207150509150306 71
    0x9041d142526000d500820306002540b104a458141c040d007220342c144401e10400c0500303180ad000e5000c540b44a06000b5844641c0398030001d080c0c0f01c402c1c0c0b607204003500500007804410310303c0007050b5000c10030b0318021400e0340c8640081000085e0014200c402e1040405048507240882112a42c7c0c07540308031003c00060340c84076102c9031207020070f02501c10507030890841000802800e0700605c007918041c1c500c99116000140c04091403820503405500c4452010800304549000f46041a4400d641070740203000c1268814010b030300000d0040000765403020b000002c90410f100040729400a001d01408400c180c0d40c65001902018850344208242c6005c9048003007945844281031350101e81010b0700550070102140e441a00130f07040100034000343d03c42c2c40b40e100c020684020429015500614040302143c2c07000d20300c83d440000e407020782030007544120721101d40154001035a130219100c906c410034645089080450701841000c1006d0750095001503070070704062149000318003030300c2c040311046a99420803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 976568848 1250 976567598 976567607
    0x420030c030d0e040f0609050106170906190912030225020d0f05030d05010f060e0306190b01020705031c08011e1503230405060601090f03080f1908060102070501 71
    0xc0c0d1050340c054000508241200d8000c110543d844070700280301103420310340c0c141039401b145c5555214080107a1202c004000c07803500001c2a00540040d614070b03145900e00300054075514031018204115a41c1c1054007000030044583c03100c019941d110812400c900900c0c0e1009001c0c2d00701812100701081e06042034a0355034001d1030903110103039015045000803020340d10395200303410300b0390310a41c5c15010401003041a2610b51184d18041c12a09512580c2103081c0703400100045181e40300c0c140254002020301492190002d804c4903010700c000b1002ca41c414401e00100c0c10f004c0380c0e0b44401d07010b200b003070040481d003910510140400c0b002596211a5a039a41c42781040c0390041d0302d801a58004910f00034001110305408a1030460064200400c1c95086a10368a0800c1c0790103001c13034500e901a4044c882048010702c2042d4002c01c3c00d02e00801240d0078050113040c2d040c468400100081c5002444003005421103080c0d8411750342c8a0359013a007440b042d140c00b8005035070840346240113000340c010200f8298000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 976570098 1250 976568848 976568863
    0x3100323070b0304080c1608010c0e0d2607032118080304110a09050901050c040f120c091e06090504080a0305040302070e1e0c250602040e042003 64
    0x14640104070040c9450407850595102a0094580b06000c10070b440c0303060010024000d17050038684c00c0c143c0f010b181100702400c4035a01011442001041e070318681c0710390307a0b85100042c802e422020440c0584007101c4606082c444410029110213000b10302d400c107240c1c2024820b1491151000b411072a01e2080701890101e0340383e84803030030100520103051070104030220302640d03001d803242c0300c40c104a40b0b05800203840b886d1581d03c400c40762611a4200b01c0700d1102801416044a0b54028441c20141426260641c2ca0841e000326050030070000d070100d0600800c204664000d10304c00004201c0a90012010b484842040c00c03c01030442c180a00025004124854035216581000500b4100300e90054101c015102c05001a0214450000b011600d601d00d60141401040b00f0280104004141605c0d82907030700004000d49072030f110a215012030034582002204450a510403900c4d8001c45600e0140300034011038004106a200c0541000100800e100c105e040503c0409281850f070000b0a04141e81c6010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 976571348 1250 976570098 976570163
    0x24040509032a070909050f0705150711090411090c0a050d111902100c11071703071b0e130c06030b1c0b0402011e0e10050c03031003 58
    0x410400520b85410b807640d450001c0041440d180c2014034010030042c503000c410380181106a070394491301410084200150700d0b06000850207025001d1a0000040d0300c2103003420000420540028517078200050483d101456201c0144840c0ca1401c16040c10048007a803000468080c800003008030b60b03020900c0056030007280c000d035546880e14800300c0c00710380501684400540c00c0301080c041c1a41c40000ca0310300001040300b9a004112600b0412001c0707060780d00c1400d103c030900c614206402c4034602c0c0411403100b038401c0200d2854030310307544480b0719103144110742c0c001e4010180703aa10400080403281d0f00310201e40d1442c43c68065030700d0b425642206c0403001c0e10002d122041909080000602a401044800e100180324035000c103484003401c421083d12000032201c0d12061420031007191303040840c1c03030840450a00000c80c000315102c4040d00c000600c182c014443c0300018000480544644206d8510170340f404223490f101e00304100c80c2140701c81240802c881c00b083d0029280042901710710702916021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 976572598 1250 976571348 976571353
    0x51c0515150f040608031c05010b09010c080c1f0510060503010815090c1503010515030c031b041212030605030c0a14040b031608010507030b102624040509 68
    0x5070810812460010100d00c0c282c01a40310f060018083d601840940b18041401c0312502442c03420103480701c02c80d00c050300850381e0020f00744040071990740c0c4500c1680000f64000e003480e030b840d44110620b034900f0b4202c0200c584540d001110045501c00c050300600d0041d4031440d0b03028101501c803003003503a550100b4050315140380d104c1080d045280d40a1084079401c9040a015078100d10f6243d80403c04c0010314510f0b9407410640000100a1402c04000c8031440c40340d00b201d030a0550610343c1522004e4800039105400020b9154810340150f100752040760003d1024544030803014032603141460030310806100100c00b181c038001c1c0c001214180400c3c035424240000307242e0003a242c1082814403030a040c2d060010b80181d40c0b40c1000a0645040040d04444940404c2459142c1c2c43c0c45840c90940700c000b01004205410b0080e282003039259144262014502030a200038801000d00c0040d07040f0a80c0410f40100301c90000038400740841000c280d5400c0404a0241c86e4142000d9003400169078041d00c1c2c0c0c0407240e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 976573848 1250 976572598 976572631
    0xe0a030b340309021e0901030221060a1a0916050c010e0d0503060337030309061406330f13030302010525020d110106051c0515 56
    0x821a240c0800d080015001031948601d0a59000d215403184030090804a65500c00180075850003042d0400c03030701c8030302041c45585010040440c4002c00c061000a001780e0003c1c0c50f04060001150903d000c4514200446881d0b28007042018060110790301e03d4107404079028840d55107420300c0e40714944640081d01030310320100d82655046030310742c3c0060f00503074480d50b170388140f40302684040c42001605103043c2d540980300d0800008142c1440c055095000c8258405905c00c46c58081d8004046c840d030040b181170011401040c1400d902608601800070600c42c505107030414000c841c09146402500281c4046400710000f10600202c039100b12100c651405400d036024034810305000080c48114080740740030703040008c2c04091207016126500704501503510303081080024950040b42400c500d012100c080340f441d400080c040d4079001e0203d004c104201c1d00850300343c89040250003000003044040c26410807541c070000341d00410b141946040b41e2a00503203105145140803c000c05020300e13500702071302004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 976575098 1250 976573848 976573861
    0x50909030a14090a08060c04030c06020f070e0601030f090f0b010b09010207030b061c080301090b4c03050a0c020102040608010e1306050702030702030c100f0507020f0406150e0a030b 80
    0x582c2003c010300d03500c0340340d582c1e010460030070600500740030301c20b14100240ca6900307510300861a043c5a4004004543c440c00e51030b103141c9000074404040302c0050b07448080d252a48401200909064400e04404a0902000c03a003000241c20000c0d030f03518001c1a488289036240d03c50080d452080381c0104c2d0060344081ca061022500301c030959074014030000d1500c014500009403d100c498410b9100342c0350814003200410651459001c0c000d000ca4040395041d0000044500755521440003848107403000d014240b41d10b100c56440c0141c0203a80700c1d911181c0401ca204004001e01504080303984003116030034501c0c10b016080c014000d90307042d0f03442c9854080140e0300b0300c2c0280e84405002410800151800e2020740c010a000d031140324001c495681c081c660f0b403c02801414542140b004240740507070a61011501090740c003d00070b0400c080e041c50802e036662441e0000071074440301d45801f6503110b03141150003e80e0309040b075034820440d080f907114041da1402403803c01220600c9444080c2c506500800040e40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 976576348 1250 976575098 976575137
    0x300b09060f040518010c020708010b01021903030b0109180c030f022a0a1e0b090604051903020109050d03020909090303150d0206070609110a090608121b06070306050909030a 76
    0x610072601203003410340004c0220041e080d12014246030380542c1012805000c09030003030140f80116102800141541c000d241c0d1164080940010044c042503691490b0209aa10941890009204030241688030074010340f243c80050010f0000200801c0c64100c2d2045240d41b64003d644050002504801c2240452051920580442d049406060060112481c0080c040c411000808070102d01003900d0762900746001452030328094200030700c80c0e0000c0100800a04000fa4244902036000c0302e40c501c0540602e0281e0160002c24070003000750240e00368142d2100c4c1c1c1030f4041c0c11400f20490721840030740c869250161f02c03032000307036604103440d81c00030700b192810b0604001e180e441c1c902c00f03404286030115503140d00080340c480500488660b400323580c2c000814980320030b1300000b801004400304621841c1032551a03940c003030711160056020012600460918141a07019550580c0d00c043c1d030f09a25240d0f900800814043c001c403889084404041800c800c40002640c2e281d13491501c4088024032403500707025 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 976577598 1250 976576348 976576351
    0x1a04080403140d09052e05070c08010e0c011b03050306211f06081507110f01021312020f0f0a080708011b0813080307300b09060f0405 59
    0x9444510400c40003000801440c800032014030300c000503101001001078010180d0401d58000c81c850701306a268a11210b640307196189082e89004201c24441220400685040c056644064100041580b00048440c01074100090031405001910080d42d251401510038448506007600c84050140f1224002030284c0e00454104000900080d100142c1c20000200c060380a00d1003800303a00718100801000502c019841003182d0012414000719061204966440941d030000c0001101640042a025405108035005150940301610404e00d0340c603542502035804602820806e0070401e90000d40e002105140605241e4024200c21360008504104880600141c5d02c5c541e0024410000140c4100100302100007089250000f14603420f603001410340710f00401681d6000d2004401c10042c038a42c640700b09400c060f41c070111030307600c030344899004558642000040458504515210410004529080002080d09004180641c260217030600008400030340b11203400003800e10040019240681085 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 976578848 1250 976577598 976577603
    0x1c021f090608100b0d09050105011a12040f02091608070c11100207080105130b0603070e07050a05130f0e160e040b0d0501060906031e0803060424061d09041a04 70
    0x1120b01d9510340c5404c0e00c041d0f0008052900703003a0341e280c0c00c0c01000400c0c0142401045280e03100c0401e054480d5081204d440340c1036144580500c140b002808001c108008114240d8021301101c1d5940f404040c0203a00605507034201c0302284070b000005030384c40e220340c041c204002d511015007051640318030140160f941402d00c081d800e60242c00c1000c602c0060074070419105040d10703d03c1142941d43c0c0d007031583e16241d0140c5001c0c0603400c5180c0c00d01452140158454002147d4585141d40b440069811655030046040c010000b44e450350000074464564580c10064907050b200300d0282c0d85070310b000010364503850901d40e00441d510038601c41139440d10b030788a008840005000c0b0205410180d9819003110417030b801202d40c20340d85a40510500c0034510380c85031010b514482518440f40c40e07445035121404010940c600c110703140e070500c500e100ca4000704140c00103040c1e1811010a034803440080d1041c90801990004440701000031161072629a94288c041e94202c020348040380d0a1f00c640300303c0204010000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 976580098 1250 976578848 976578871
    0x5070209070c0b0c0429160f0602070309090b030309010c0b06060d060902030a230408180603160206070c0c121a0a06050117250e1c021f090608 63
    0x1402d01080480200b14403034030042c4005036940c0d051400220140c2c03034118030003410389030400f42d50306003c9001048591801409540807040126450240c00601040e00b005001c18004600344007016004000b80e81a649440428461840b43c80185035803406240212800030b1072f13248450780400c40145415801a801034036840c40c1860310002142a03c1440d07100301c200c00c0d4000200700d03c0da1881c1c480c6581603680450300f24000080340070361080c02c0f100540041c1144000241154110351100000070202c1e13800303001c5a07107901e0300200d28400d03007941804050140c0520300003d40b8052064003011182da0780008101c0101b402d12002d02c000500d001022100e0b071040785034007001c1c1900e00500a11408440740701282ca6800c0400040590b00300c4c20086014031208001e001d20003060f2001d05100c0d1980c05a40c2c10701b4100800100c801800318060547c12003558400550001c07030846250351118000d03101c500440ca0744101e0360383e01e00d8101003100009940e038242806513500c50507009800c20038201c034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 976581348 1250 976580098 976580117
    0x40f0201021006170606010f0f050903100507020a170415180f0e09100516110a080a09090b0a0308030f090106180203010e100609051903080c0109030207150507020907 73
    0x60780800c5400f260400018807854030200804610104a2180d022070280303022100b80c5c00c000006070400101c1108503080c00408078504040e5101001b03241500140e11405000350b0521000103510b4103030440082d40e00c00c001d241d0031006c400100c02200c048401c07519110240034003181046400528202d0082c8104400c400c00051000701496800c0241401c0d407510001400c100c22414600402c0d4035001ca11141403c003004032148482c805c2c0807401103035042410604840050043c2041d048000c001d120900c04180a0245944040342c0c00c00d031000315400700032045078034081100214035480020000351080000030010b080c4c54200381d800c881e081c800813038002c0d2a040c4801306442c203950b5407070078943e0110040104813200301d4969048840d050000c0303102820124014403481c035034010207003c3c1e0816030300005c1a51000ca8094000c54008030381e5038880328203a030340501070300340d081c030550061042110100d48260000030302c0d46c01d43d00c152582c901c2c09010f40d090091120303005082d0420310201d8a03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 976582598 1250 976581348 976581373
    0x50705130b041a0306091507260a1b081308210c03040c09150504050c2206090506121302010c02041a010315030215030a1d0a050c090906040f020102 65
    0x4019160100020700348112003d0800d01d4a41080100703440740c9540300c0030032070040c0044440c0303050b00000705150072900742540c140316010907209000361403c101050000c1203c520115801035107042081314840140100c02007048500342400d4520140c0400200c8444002414100c01401d0721a15001d051b611460620400c00c43d50700110358601d010840042040104891045000d0240022440c204500003822229003d04511030080b140105e903108081220320908406941220382c4010307026000c5400580d41440380710f0184164804100c0d0784030042000c0c42c1178030540c1c80c0942c60003083e1255643d003803c0e099200703107000c1d0140d051002d070610450240e1114004c600c807043c841c1c0022424550100001800c841140e0301043e00c041d03082d081407005070f0741d02040902c4041c0e07002d005a2070343c4480b031491000b001400c0411000302c010341001c0641e0040818800b10940c05481079a090059030310078003840c890304466000d2580c20880000d4001440c0c8240b1004190061045800f00300c10342 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 976583848 1250 976582598 976582601
    0x40b040509071107080d080c16060b0f030f0304050316062102120708060a0f1a1b070f030b010e010501050d020a021213090b040e060105010c11040911010809010603050705130b04 78
    0x50b000721780560460141c5e015110380040b2965003104910b50f2031441c0003014a00071000311400c14000344000c0e10782100402c4d1755921801a04e0b4070000900380c0b424903450f140210755079841031088174028001c4404000219035420f038000d0450720759032962071101414580c0f880b07030080311540018074a030707091005011500307560817403500c20031582c0c644c50b0f02810240d040008985c80d80e4415004140c1940d010700285c0305210642c1b035030050022150703403201420003160742c10f814040f00120491040c9580003e40e644030300e1003031085a008011200c42c1e80d0700da03520000700c08400d00506010480400094400e02c450b680181111950b034410341c1d4504404400c1c4038403c0c0e000e102c49410076080c1c0d03c4248400311040c42556110a41141c0401c844208403100e59140d0905100d0b0606205c025542c0c001800300c051511095844001c00c20800301210b445c1801c5428003030010680001c0c80100000c001103014480c041c190380d0030500070107045180104204a004458401011442d110f1202c0c18054969 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 976585098 1250 976583848 976583863
    0x603090106031208040219060905010c1a0702031b0607020d1d040c020d020c041e0e0319090e010503160e1009020f090f090c0301030602031510110d05040b0405090711 73
    0x41e40e82d44c0c2d083c10309004229420b0420882400e000000c40030070404560000f0448003250020f081040a658890902c60301400c1d01e901001d050030b4198040100803903000c1b000780b040349030544004900c105036441144d03032890704485650240e400502e00c24a010300450306100401c1d920402101e5001c000c0380490203950344180d00c01e0142e403001e68414905501030000803270344101942c0800c1444904c03401100030301c00105030400160703a64009120140c806004440603c1d030a01880e800311564524024070b04100e40c810240100c2d1549e002003410318012441240584e00040724813081420201000f15441c4040d002d0800244610000241d954007030011304040c1524043c0c458031030300350100740024085030491207446502c0e440108900c0460207016281540c1d0481001612175070341540c006075066800d1803056100c51341114031403a641c0e03c100c0252415840c0e0341507a180d0108040c0c2a600c078001c5d4044c05c501c20500f403105001d036081507801c02d076001800e80392202e4003001000b0300314103007001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 976586348 1250 976585098 976585133
    0x60b040c0c0506090c0a030f020f030604030507020901150c11280e0f04020a090902041e050402041406030a140304051f1418010806040f05070c032a02060309010603 72
    0x1070400d80c19061210034031403ea80311414070041e00c1070762014000200c602620f0b010081420700c40103038030815516400c400700302100c406400c6500343d08050902a101d42c100010483c0f207412420000300b03102c6090103038411000c0d443e850350079155206582c0d076500345001a00070398200848c1d610b6040c100c421240d44001c80003155000d015002d040c404c2100224100030091500700c058282400b0041c3c0350f1451807011a078030742d040050051170754800507001e08480844800724620342e1001c420038007504d5020728000c0c4c2c402c132070411a0700400c0d280024000300864400e0b505070041034807207012030040c02d5444a07107207a01d0142ea02c2d01c1c0d11840010340d0403c1c40068410b0b14146108616000364000c504008101e5066541c103080441c2c3c505940c01080b10003440504002406012609c00d460f240c00c90456103c0c1c201c4c0520440c40c0000f03005284c2c044450303081c1c00040494021200c0e014807581050903000c9004001da0400c44581c0034080240d03c0070340111080c1d907864800101091005c200d01d2103400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 976587598 1250 976586348 976586357
    0x4110d020108040f150c030c1206080d0c03030e0303010314010b03060f150a05120d0207081501090e010e0a030e0f04290d081908090609060604150503060a050703060b18010804060b040c 81
    0x10030640008040080327a5140626451800310140081c500000d40406082528580b01e102400e1a203800c40240c000090750001c68800400044200011050341c00c103000c04103070003005050528410540d5886068401c5440c40843d0408920050b01b40e113900f0710f4a150107800a040f00d6030352004180f1010b4003040822035030708a2003809410507418005480180441d000070002c6080c4074250500025062055201c9250385818071156400e0a4001c060f20700d800070309640c0b54140a04003d00903c0f1a0b4522912801c00418844468038044c81444203d5078080c82d07224415141001e151f541c41070006d01c1a03030110b0100c29900c00190944000c00e00d441c81c030700890b06070540740b0300c0141018a01500b10350860300310f1403c1080109000510319449081190302041280c20041c04002c4406070340c00003a01030040c0c108100c80096075800080c0030740400d40d01041a50f079201020070183c01081d9107540b58102c095014006984241801ca8000d8003d0034000381c0390310060006012540185114008103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 976588848 1250 976587598 976587611
    0xd0915050906010e190b0d080a02151f050f1c06060e130f0f21030b100e060a0509011403130b07030501080d120f0507050304110d020108040f150c03 65
    0x78034144a2140101800204040a414401020140482002001488180d07940c09015055031582203a180d02c039046684241c0e1021140d0000b500c98407550f01d2895050600c07400320f12844498404204000c80c1d82e000c1d843d5150802e02008420107909034810b5001d8601000b0b0317401c2c09044000071119034803508002540c4d51a100c5142c10074075005044001c01000449403c0c04035003020040d0035407a910000c44244000c0074903003058901c2601c030300d0368540404d071314540b044690554401002035078101d80d2004000440e204c220b50311200d201003141c205c00103001c15503205000e40301910052105051018010b441c486a403050341e0011100016a100652840c10034480e01480060700002c031494184000c0d13041000c8180da401095088108000f45110744451141a40d445461102d0320ba0500b4071940c02c2c441d200610715001603d090700c100e98804120072182c40c00d109510801507040c0c43d5104ea50f42c0b20b48070081040803d81e0309544801c181801501c0d005c0707903407007181700d070702c85a0310b001880 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 976590098 1250 976588848 976588861
    0x6140723070312080105060d0f1b0507030305010e01260f030706020405040f0b0616171b1002130b070f3c051c02101e0e0d0e01050d091505 61
    0x1038201c0c40c00b8003014004140014010f5482c7d100c00c444c480790240300089100c01d00c3c07c84180c001c02c0302448442001c010f01500c0d220040e030010003420760a002e130b40d050100e46d03294020040038480a100b081d803641c2c1d105440c2d00711080c070680c036400b001c80b0180c1917903c1042e0414040e1b06603400b07410308a0b609540007400f130000d49414801d00b070100c440d101c2c0800c9051010008204148600c0d00412443c2149401141c20041e040d203041198460b20844280c950320f003a540c460561019485100c03440c0130724280751442e00c099200355890001c0380c803111f942c401d10344054140143d0100340c0c1501d40d109445200320210703108070708070050f405c803594030001c0020505021303117242050302160010000480c103a00300810000526080b11a900ac031680385400031131f4900347d00d03007001107225100c0d0710300380038051401c035000e50050701c0c42818a030b03028007140070300041c400d0303d8001e40340c18480480e2030f000940d002c0d5489070300a46401c40c1d4212001a1010651b140c00b15160a171400c26805551281d082002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 976591348 1250 976590098 976590113
    0x5370807020a0b0f10090b2404030206040f1715011202121b04060909020307090b040204080f010b03010c0302070222060803270d0302060a1802040e06060f0901061407230703 76
    0x1032486c490300300000001007000031740c0019001c0c01c1c0d980141441c000c0400302082c1a00b00c40085500814041c0d889075520074848020f8014490500307084055000d48c0440203011030450106d1034081c100b88016800d201780007600c8000c000042e41c109100c04e0201010791001c04c010000d0445440c0343c880b05c00022401c00058070119008042803506201111005803000101101550750f07184020403070b5a800c401240c028042d076809141e4610842c0d880c1c003000581035000c1c1e064020150020310600d081104142c00368031420300006c6d04500428200c8810505410040f42c50a045100219115682d103c5151454100d82440c2103442c1c1c0c1c40303140c046c400142c1c103881e00d84090152501443c0340a180c60203511a10003d0003280b8094507034a40b00d510040210060110750f42c020400c100e10760005030003954a03e01221464058a0040c42c0b88007140b40c10308207035040350380540e92100100c044504c003407555000b8890031180121082428041d034092040702482d0742c80014002d06040d0b143d410101d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 976592598 1250 976591348 976591381
    0x14040b0405010b0604060f05030a0207060c320a08041103010f0606020f121b0708010f0203041e0b1503070e0705070203161404020f0c0d05370807020a0b0f 68
    0x313200321004c02c030411609420124402d451a640e040031074403580c0703100740080603100b079502c001c00041c5400610480c850b0420007104100e40c490b0062000300e4041d03d4070018040c0c14202c00c0300a62800e201e40b08140340f0903050a075100d0b109980441c11528180046401e45590501c0d02900320f44481040c00b04e903a04000d40c500d401a41d4000303080d810805100d030002c0344180c81d0404c03000040351001d081e400004019040003400003900801c0a041d00d848008001d410a44045484484c000300414a042d00c0c400325154058024282d01100c0d00d5550009964890322140c09406000d500303000581c5003185074202e032080115807202d980d00e011900c101030074408000843c1c800e122682030b0a0103484140c5012100d0b40c40140c1c3d0041e95088a00804c4a0718000e00d00300b41e0b0785124a1050f4038107558048003410441e01700c10045030001d9902d0303000d03120b00342150502c0d00040d004014040130042c85200181d80003405801940d62160850f114000079a0045643c040c0d400d41900c207001c960100050b511 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 976593848 1250 976592598 976592621
    0x6090a030809180c0d090f0803190605030c1305130813080c0d0c060c020a080d090303030f0b1815090a0c0e01140316050f0403060608070501030203060d0b0a14040b040501 75
    0x102e50b6107807213030340d10300701d80075075101492940e568a041070108030740026002c00c107a4200110b59142d2401000f140c408581440050f0003140c1031160009082c10000b0302c01249110060010b0941d500a440c42002000d004000d440c100380e844110101007020200102000d0480c3c0d54480c440500301518545801541c1103281d0080d400c445901000c0303030030201288281e810510385142c41a0301030000404000c81500701c0c40150048001200586802013110400c0340e2103902c052010414100c0d40600320b4100045070ba0b0084844020200d0383c0d00003201065200702d0403060750350b1111035140401c0c080b0404540c1d0014842d036a01078542c0c81ca8200005d19070382e80c0d09180010707080d084450030010300e0101500450b0341203004940c2034043e5000d038087d00e0a541401380643e4031140d50f410410082d014078402c0e42d0950003410404945940f007402141d108400c0030701070030071a482941c3d80300c0513410000c14000348543c0e6030030800c0b1001c1a508140303001e940503003055109820541021401c4a04c4c00300007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 976595098 1250 976593848 976593889
    0x10213170601090e163317180604030206100e04020f010f0c0203061e100812070c08010c050c0f0601030b130f020a030c06080c040501021203040206090a030809 70
    0x20040315110024045055030000880031030424521018546800c0544011034540d12150201155030000b03d1110f0341601d484062090404005420f2800d54603103103d40000010007114201003004402d00c00c0f070390801c0c8d02c081c148181e03800c2c5141d8141031030000da80c2200140c010f10248810580000c1041d0082c19400100740041d0505600140301d2070000e500c11414000c2e2410b00c400c1944c094410812100d07009070030f031246807a10101c0c1c0c03080c1141004007108000140b5001c1181e40b40c25054200c1640e081c040204180700c00c4980d03000240d0003030041110003080341000801c04003800c1c0221005114980c860f80d481d0881c0031083e9040810041d20180c4a900500041020031440e110550708178244a0200308182d142c0d0a05c119a60418080079401401e007840000401855004000445a40d80c0d1145030381e442d07081510041d8400c910869005074028074425034090010001190041e10080505d403070148610003050140d1020b51060311091008907801c0c4507400c014030840725904501c440e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 976596348 1250 976595098 976595129
    0x2102304140405040305090d03200613030e1201020c06040c09020913020f0d091101020115060206041704170d180509040807050a08030c0a0915050a0f02070b0c010213 73
    0x152011180d00a1403100d100700c0d21000804c0c00e050060307080301e0300c4c03500c09846620a0b94180c100034041c464103440e03038812855003050079401a840400c50311300074105100ca0030f400c0d600c4c40d1011500304811660460f4000702c80703040c2100400003440103049240d0120064403441c0f5060512412500319a8070800c41140100a400103e0f980c6212070b4603000254030005813254401c8548a9490180700213500c450303844c0980303080500c40781042e501030500c0d00f42e0007400040c20001e1810441c0031640b00b4400580d0001c1c0100e400903801071070b2000c0302401202402e081c1550b510340d40143e41e110880c8a01d040c0c000200341d0f0311f1198890b1441112017440000b03202042d1805000c50b6440c0c4008201515908012132540200402482415001e6802c88101a200c1c2010410300407a50301044001000c0f0750018800620710111201e44002c0d6102ca80302c442c1001002c4a080c0c440380d0842c1e1090b4118000d881e004904201460301a21384044000001a2203920758048441e030040c0c16040306c500f54a1851 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 976597598 1250 976596348 976596359
    0x2090f07050910021f15140604060c05013209060106121505041d070815060d0f0503031911090a15050f070b06130905070501180302102304 61
    0x41112030b030715810307075810f02c061200d48002c9041041005000c10f000c4602c0d103151803840050380220100400d0300035010201d5644440f4030300c1260108054942040090000b04006030283c400c8510703603401880042030b00e0700e007040d442c0c1114841190b00c0ca1452800e01300b03040c0f2a0b100001309503010f14440c008120b15410020042e00c6161851300c00e041c1ba0340c8400c0f2140601c1d080d00900c20080c5000b41050000102100049041e14803078004079406100e0802c0000d04003c0008120714030039600c86107400607031914001e2203440740c8404415a0303810100741c1b582001490800007181304d940078010300510710600b14001c0c000e0300e1400300400c00040c0240a003080c0ea035280002d42c4200c030041c0f088448101d215070b80507500e80c0162030696a4061010aa21061007120750420b4800e8400711503003420012864072910840d064000064443d603c81c00c418801ca50152110202c0c902040d806035029546d07030383c00504919103045034080040d04d810505661950803c2014194554002c1000e08260600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 976598848 1250 976597598 976597607
    0x30308180c10090312020d0f0f0e010c060e060903220b04050105031806040503130b030f0c0c0a0503270a0303300c0903020120030d050718060c02090f07 67
    0x25032031900c54451911000882d0340a03280900c0110381c40340d0349070140c10f00700e00065201c0e080380440402103182580b8030b42200d4840d9507003900100c401d440300c1c2c9030581088011203042485150444040d5130303800040884400c1004140d1288203620025682c1c4e20101c20401900c403a94900c103107201119510a21030b440745002900c0c180c40b030030301c0c11503142d907145400c040e2051002c0000034074602030201440140310011004140b0800c1503001c101080e6035425820349241720072a46441c103140c12902142003011404001e01c1306c2c4072540c0c2120786468243d1252411075103d128500c1d03486c000c941521300352030126204032070360107021145038061a16640b0050400350a03a080b20401d03d0343c1e0381021002d201d0396034900034046045002000b111025203000350540704c850105a01044440c0b805000b0307401c0d2100d40d01440f01c00c10b005103003010120404074001c4c110241414081c00185c3d0b40d0140d10400582034003008142c8c0d41d50346020f514441c010b004070210b014086155000d01c6104001c200c42c2c20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 976600098 1250 976598848 976598863
    0x30b0414011203020a1a04061b05071101050d1a030712021c21120b03012304020303040308070b041202030f030403180905160806030304051c060f0207030903030818 72
    0x4280d4401e042d283c902241410f403030300001001d42442c1504d41482014101c42030380714510403c0c041003000800701a104038800d0450085000800410003040011315900300224200c07010f060203414150500070b41c50695070064207140401c0c031000c01c180150714040194100a003100c501a10304d05d1000d40104013138804540c03d004035801105030f4042040050b020700b07111035205100c0c61905621080005201c801e00001c5103001714203081c5140c00030b10b0180325082e00c0340380e0300320080c000c01070000c5d40c00f20448000b8802d82c0e0500003400000007190021000700440c6101e907883ca00305280610b40510f0282c1d140890f001150f20a015440000d196042241d8115405d414241004030810850201421700b903081600d0860801301031007025403040f504d03203400350402d46400b1015501c03142407558138021846195485103140c66418440d80c803080c54044428000c8401048000e15580040240d07446090118006140c4000400034140d120f0000b80e0091802c03a5071580306c00c0d100d41035541c0e039980e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 976601348 1250 976600098 976600109
    0xf0902090718082a0108090c010f021e030406090b040317070f0203120c2104060f020304031a0a1d0c06030603010e060112050f0f0d0c240c030b041401 66
    0x11105500814603441c01e031842c00418401c01219603d41c000c849007000c3d2140030300c0040c1201d8802c14007510a600440d42c0910602030200200340d0000350b5001111031198a292940a50143c02d05584000701124402c0741c0c9140c4420007160f480345814001410800d5a07071100b0202c030424802400000c04c10b165840d00b02d6501003a150b212501c07402c0c00f080f54204100000d605124020b600c000c400b14003006400307140144420b40d510702c0226012503a005407134221098451004020501040340503014844031000c0a104403030500303450307680d004418038114965044020007841040f01444180c01000c40c0c24102450201c3c0d00e00320080d4069454051003403082c810170022000810946003580301c55035003810303801110555650b036030750403074920000c650584c3e05000f102880103402c11300041c074025020300d0703070011f00349620400310131103005000a4045804040e80c1c0d1011200b4889800300550784864100002511840110090211010542880e004a00703180b5000c11051006491504598 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 976602598 1250 976601348 976601357
    0x60f0c0a0c06150b070c0f0906030209220f081210030317060105160605100e0403050d0e10050a0c0206090f0a02010e150a050a08070309020d0f03230d0f09020907 71
    0x6202d12280350349283c1e40c001e8210b56602041c49030601036050070107000c541c020060990403586400d409170a0300c5450102030b4120061201007500002c000f00d101c900c59a40410030210310385107030380d820590204104282d5400b0340208805040b40c507030302c41c566000305075900ca1002c15417942e90044c2080f1006480c50041900142c0020383c40d0b4000c800301d07088480c04064a80c0303030b800e052a10000800c000d03260342905040000001c2203603400d603c0410f0049406441700c44c1844012555080509107401c1005801d026001341001034000307a000d2a80103a15140010a030a02c0d8154001d1521030014100300c03441d8810001d07a10000e80201c2c00340d00c10303902803a120300380d00752400100d006002d14a00b818a8600002103445000303034008080c00c04182e00360354800c2d0507111040c0440c2910320b114006544007074031851440028411150411400c1d20a0400030001500462144102c0b079210b41014180d031800100b0b61518a020302c1400b080224210b82000148065000b145802000401744401c0c403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 976603848 1250 976602598 976602611
    0xa05010f080a140702070305010b040c050403021c200102481306030318030203120c0f0109030f182402210a03060b030925090905060f0c0a0c06 63
    0x4902d9420030005421441c511000d1801d0680700250b0300d140c0742c030090340e0369443d0601c0300c01c151400c3d020318415280c7d40e50b00c050616065400b000508103928031181b41040000301c80c44001821700301c100512050314140101310840c031000183c00c203001c0910345801e0300364000d4034042d03099255440d1170b900d60100307400d0000020414039840c051014880d50075444128080106010041e540000b42030740e100b65034512058108000009107c880d600000b58180c00090700503e04c81c0341c00000d070002d50a04c0d82250003090f2a0990726086400b03800b010360000e40241040b003216038100c00350042008000c0d9080c52141d00c4d202907002d000715078030041e85ca0b5043c1001129984e41c070800001410010401c3c0d2080c41c2868800446440c9d8041d8080402290418070002080202c0c60140d07441200c811000c1c0a44440b20000040c40311000c041c0d0555840744004045081400c0b0300c50009424403c500502c039030b0604000000804800410004840c60200007040d07041d80e0083c0d034000415800705020886 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 976605098 1250 976603848 976603861
    0xe0a15060e0907080d08010b0a050d060e040c0305060c070807020f03150f06040b01030e0a02010c06110c0109050f190b04031e050d0b04020c03041710020a050a0e0a05010f08 76
    0x544410307444022048000380a0001a10700811444112074034407049a4041710002c106807000c01c0b0922452011600510008400c5c50103500181226000d4250024031a9100c0c0300d41101c8030429102078800c7c0e2041d11042c02044820448103401c05010500d803418080156944078051199030802406444074000407403140d2030030000f0103400e80345e442078548980740002180003000001c640440c400e074282000384117a17500911550548124000240c490405150015031718a54810411030303400e0398550032526002c0c142c10140c581220b0700b0700041907050385030030030702e03d00280e01c0c0c00c0145a402c21400c044a6812040510400590100060b51540e0360703800c09480210402d003089800e900002024000c09907c800246039240302d044003044085070502c1808203d0040b4500321025600401050000030807042d144600490007904450002c101d09509400740d800101072003004c030303002040b560120b503000b910108903a441507402c141582e00e8107000900c0004201e000300184900a80860311 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 976606348 1250 976605098 976605101
    0x2c04110c010504030c050d18090203060f0406080307020a0504232212111c120e03040b1201120206030f0408070b0c04050a0e13020f01020715120f0e0a15 67
    0x140100e080c8020007041c0f078a030801500d1084140011981c4d0301911041101c0310f07000b4a890a6802c003403001840300a800c01010a00035800680741c00e44c800b19803101804141d6071401418082c24498001d0b5858603030600c1484400e0303030304d034004a10460411a01081031007603000e170040d1034840300114481e1900d070f44440303280e43c9102420841e001d6111190544c02d000000c00c83c45a200c480381c0d9007105004454100a8485141340030b0101c0c8402d65241c101300c61449081c01c0041c2d014101c0300041e400f00001519450f6030300c0f650000c50140070200b061440040034a090600400403005415201400b650010b40303540300080ca1070121000000c046000d000324081a21200c82d072045039030229080c0103802a089412030f200b101e01c03c903580c00000c510460b19100301e0f030003000c8000c0101074400d5213070708000c0f007034906468090442c8104130300000d0342c1c85600712151101c0541e4442c0030b051800b22425806407400708501000c2c90b404c01303400c040282000980300300b650303400581c07800c001c48800021b2030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 976607598 1250 976606348 976606357
    0x1e031815160c121b06110d08151f02011812031a031005010305100603170c120d0902041107020108070309080c030c030306040608070e010618090614012c0411 69
    0x1000030f9116114010420840c00305081c084480120b802c0700340d5102001c0b0350360b003a441c19010f00ca070003644213808003d006004013908035107111401c2c0a6520020042100410701742071802502c00081c0c90302d29960303028441c40e40c4032007086010500341001901d460f006410aa10b50004241c0e556420048800e45c460200100302001804d41c0c0242c60300752500c5010344800c2c0810391f0103014103040030080c0074072440340c0303400c0701d501c80d030b005850303140d0108040ba250b0441010300906000b82400016200350180040100314541e0400003a104810b0042c0000c840d458032085004070720800400c0090f0380c114a4407584205e480ca404030300c403c42031911a515000702024100742c3e00c40401c12a9801074040040c510840003554104100c42d540c0114a940700710a200d00c0c03400781e00300801440170a00c5807c14010300d0b810340c880010031030750314190303003003101c3d4141c0c440204042d100c50070741140d60b07024241d450001000d440e162800c01109061400004010860074800e5a84030080d03107102c1808401d80c3d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 976608848 1250 976607598 976607609
    0x1803080a080f070305060d0803060f0603040b07020d0503010b0415090302030601120b1b07080f04120b06041407020c01030b03010b0405181002070302060a0e1e031815160c 75
    0x15211008400050103540050354034410b10000c650028410920038425140300d0b0400600d02d403004155070b101d901c8960b2018010342c3d00200e18018084642d169400298003407445000400343c0782c03511031002810120354220340f03070030440c040004005c0403c070340c400c0d41d0665455040c0010100c01440050f1144841a403000323401d4014100000b80301404445202c0455014050b12991542c0c1d01c0b4190b03549000741c0f4001c603030556007844050701180d100e002030180084400c10480c40d2503200c00140d800322042c00411140044410204442800d090041644000f25030700070380b00a08150002070340306c1910034606410107507200c806500c995804d401482413000003a000f00400e00b8101c4500840300a44031100c50107219003503e00c51200c810340308440342d81d03405034007410030750321002e40004c0a07042c0107040c07030a54460351100815692010130074000c40032035007005560301e0081035409100c114164460611800121120042c441d40c000c0440c0c01000102082e04070703c0c803180c07504c0300d051011030300107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 976610098 1250 976608848 976608863
    0xe060109271b0f11060f103f0c031106120a0603030e010224130b0f040b070306030503040e04140f240601051b031c200703020303071803 60
    0x2010b54000755050106000d20442d643d89a582c6140300702554081c00c503000e42200740e8031910009160070b510304803082d00210748030161413441c1d94810182890181080100100c0903e81c5c0c201c2c070580101d0107008404010030f840079401104141c4818804da0402d110140030100d0726034400c202951924100e407614400d02c2e06805641c03d11000f403000030511408110042070500d0311415056000103184001030500d840a0030b06801c800c55240c150f0040031f8025100440030b4090480040d500d02d49062145003655040d0315a03142a007009810300c50040c101809040c944581403011130400b00855081d6960a01c11143c45d0b01c0d5407400700318503610400081843d0140e400c800442c5000801d100964010802c04071075414000c0c02e5004e0041c40540d24640403620410603c2e00f900303100c003c00504858080103880c148990355414101050b41014010609aa21703018407140004002d81004c1e030600d0003416a04045842e50007035581e110140040003848800086103c1d0242e103540104007440c0e00541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 976611348 1250 976610098 976610111
    0x16030e191205040e13150905150a0501050d03110f060726071209020a08030301180608010e0c21030f030403020f0a02010906050703051213020a0e06010927 68
    0x4105440322031180072181006007440034076929101d4030a0f18241d4107402d51400322902e4003c00e03010b0300441590101c581c1510740b40d4000500e00c080c0300e908001ca0240000d0b115060494640306000314004000c680b4035450140140511f44490320048461507042c1042d040e8204007100c1685070515240c1011050300c01c21080101c0c0c1903000c0c00e6403c4980403ca50440004a02411120581d90031902c080c00a420030484101c0805641c00443d01d0741c6c00580519445500c52000b60b0865009802120004c0d80c08500d80d1b4106625209040003001c5002c020841f001e15a0011030300d03541103050030b078440c030002c519505150304400f5079000c910b40f40c00100e03680c50822824604550f081200c054001d40034440039540510404541040015070582d03510041605181080d6159008448240c003000030a00444041d01800e60620f03000b03d0410300c803003001d50710520400030114615000001e5000c042400e0040a0b40c102054009840d0b0124004144407902c81000101440c05110707800918200720 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 976612598 1250 976611348 976611373
    0x1806030709170109021509040f050c0c0d0503130b06120d030c1101140601050a0e15250b0a0903030e151b0405030601141f05041409010e16030e 63
    0x801120445088000c81e51004402020b02400c0715944c05021350484800c440300d50341c181c0842d00410780783d03400900010f04d50303c050380d500b802c5071000c680f00c4140c5180020b10032150039042105038140321052421a155103401070b034000c0111030031400105034290740c20104900b961105000706160a484089481d01c401c00c44004000c4c0000c244540c000c14250740d00607444103018010f9040401461000c0c1110707071100001102c3c076a115040300c504200c01000d004202e56541500500c0d440c400640141d12141401c01440c2002050b519170800c0540e9202e40c0c4000030051404e1035070148000300001541301e500d04054000d4803010b42f403084207003d005c8640120440842c0b4244c0200308400d11040f8100380d48011241c0c1b4401c9000b000c3e17042e40000010880502c0346001000d1004000d0007030410241c109000800d02d5981c1000040441c0b0041414040340310724200342c40c0ca400d01220300b1605540b4010840b000742c0000b408483e04180d02602071007421f4000d4000781078640110741220140c0c813078171 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 976613848 1250 976612598 976612607
    0xb0d03050405012a020d1e0c1505040e0430050d0507030e0a060b150a050301080609010b0117100e18070503060f1303020f010f0203010528050618060307 67
    0x1d000396404281c000d44d010702d01141003449120054110031004044404036020071050a01201c030480701140c44080701000c08800301c42024480d0b00c82c6415100301420600c10b03501d45c186400490341008800d01041084001001c1c0946c0c215400101810004280181c44180360460315100260081300031309500ca03269100c0004c0c01d88061130700d810006510ba00c1c0b0210300b0740344200c1c8010040e5001290700320205040d54000070700510700601e070b440302c409000e0703d00f041500450007040c0458070210041058500502009034403041d41002000000c41040c0080e05c01888003000d9281c01801c000040c031644d0352624140c004d0140c1c282070030344070721340703d481941b110f90f1107402400a4001d01c0e100040900340054118060040c100f54688190345140a4428010030400b0a1341144180e0160302006d00d02031107140d861881d24079002d42daa606200c2845144e0f40e03a000c0044040350701c0c0d0300001040340d01d214100c1c00da5000b1101150ba51140c200e0742c00e05030b00307034181a552001c400014804c042d03800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 976615098 1250 976613848 976613857
    0xb090a052203052a011d03041a090904050604050d03050f011503020c1f230c09010207120506010f05060c0d110f07090905060f1b1b01020a020106060e030307110904060b0d0305 77
    0x40c0c00078810070004640324501e9a03038041151503144d00620050000741468409e500b68440300743c0903641041c100000140140a003518292045d030866420301051100c14801c000000702141420f0001d41000c0c900e041030305205209400d00102a04103a02e0554171030707011208049606022500d01061415003609486a0380c070b0101c0740310780f03001e5600c640140400c2030164480420448480a0b0340d90325003c5106500003660f050450080d86004290841074030080d0b040e10b401440141125810140354000f07602c5c240e000f052056174103016420604d1b4002508040186407413030700090145d0100c81503490401905550300c2c140c01081c82c049558801503008c0001c1e207006904407141600c49409c42c00000809640e15a07140300d0203c45108010004001080408901210501c950010a030340030308981042d4407410041c0d4403801c080003030907030081042c004603808402852804400e5070346d10350024058040030b03004800000000d8180401c5038486841207001500151800d5080d1038014180d620 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 976616348 1250 976615098 976615177
    0x71118040b0f07090501090b0d2c010c03050903090f04110c150c03010315090317010b03040c060e010e04150b0a230403031b0c090f0b090a05220305 65
    0x84101c002500c041c40313100c0010032141c041c0c488001241c10300c0410300065101c044407a0380b031600e82001c44950050b014111440e804041c001800102c041d0034810f003920340e100005000c01d03062105200124102100b00e5141a90840e00d61100e185a100850041c00c10030a940c40a10800300d0044006c050100d4203541000790000713456115555040e046c14280001e0001409410f072000c02d031a40d0314115403080b0000340c060b08240c0000a000701c0317555031f4024241c02c4180e03030325404014041003040d5800040090308143c1404d003100d02c04a40001d0183c8080042d961050303480d028500e18502d030380f1030b28034042c10150503400d0b9a013052000260506a190b59241c81c210703007422000300448062000d407400d896040e0340b6414584844051500601c21040c0d080d215400e0301c00c0001003c0282e0b10030796681001c004404100d0480300002c001d0380c1e103001408580118200800c200d0301000e200b41c02c41c0050700c246107490005080703090840d00d40c0543da480002c03201641a4034460141e42c0000780750181c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 976617598 1250 976616348 976616371
    0xe0c100507060b0d03090e0901020c0304120218010308091915020705210d2a03030e0c0603040804050d1704091a01051801050a050f120f09070b071118040b 68
    0x410300103002da013540c1d003a4003400080400f00c0902080c6000c0240a0704580d20400140c24854160951825a40700341d100610f0318614400c2002141031200c00c02d0725040e1983c0d04a50b0039031442c0c456442511519072018401c1907c956200005042d2080c0c950160074000d80c079074a000038201019569140340d00443e8440c940c1900c242d200040c03500304180560b0b200790040e1100e10b1a40300103681500c00070048500c8001c1100d080000082c049050140c01030282d6004114a00d0b00f1400500707200b401003805000710020410040451400e604aa0844500780c500741c010019a0074004101c612540952032108000a0000b0b15064039802000d002c0307401e80c2801082e40c00403001501c071445605c2c40ba498240050328001c00544c010700c0034100c1014a41401071030040580c01c0742406620107009000e00280c0e010900141e505500503c031750241e4410300500ca0076080888103a41c1c5c0c00340701c00c000c11450a2a180c48460f840c0ea04602c00007082a042c8010642024a401141c00000b25103198094 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 976618705 1107 976617598 976617611
    0x30a050a0c020a171e0c010c020f0d080d09110609030636030c25120c0509150f030c010f110f031c0c02070f05040e0c10050706 56
    0x5080d81c400500120945041d007103004481c09521040c407540000042c102c87d980081c1401415a01101c48050b106200e01c005503651031204401411084041408540491250030688241d40f0403801e0303c00c40c80120003886201e02958681961603441500841c0708c0d81c44180b1a040041c488990302c0e00343e07070708421415a003890408221a41903000240e002c1480d0340c184031507000c14140081c0c480e00c0110340c400f0701d28061481c1c01500c02e8801494107030403c004110b400038008280160064000d89044011310044031481c0c0c004a008a00c18105507005140c04180c010442105844000c180415040304468041e20380004a101c0d02c0707550041c140c841c0f420406000480390604800d804c00034011910426524100a40c500359800240188020001c01e4141c5055400070b840008010b008512005d142c2000803032032607048180902c0300c4680a522400070710081d4003992050020 = true := by decide +kernel

theorem cover : BRFrame.Cov 976438848 976618705 := by
  have h0 := BRFrame.cov_init 976438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 976438848 ≤ n) (h2 : n < 976618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
