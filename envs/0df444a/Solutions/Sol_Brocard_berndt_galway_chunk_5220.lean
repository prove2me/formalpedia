-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5220
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:08:47.728439+00:00
-- url     : https://prove2.me/submissions/8f61aeaa-03d8-41e7-82b4-ade79e2d8e80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 938669064 ≤ n < 938848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 938670314 1250 938669064 938669089
    0x90b0601050a1803150f02120a0510050402030906040516030c0920160606170a0215090a0e01031a010605030604150f0b2203021804020105070b0f0a050a050c0a050c03090402041220 79
    0x4141d62b942c0481c040d000c1e201c0c4a84001c180c02401551607003441d03c102070f01e4440075074085482c0e01c907004800980b40e0260b00c070131040304e4012542302d01d42480c00c521000904002002c4200c1c003200d0515010b10a003402010b4051705072069400c190300201c910780307c0701f02e0707010303420a034000c82d0380d030b890a80b07a180005041004c082e8151154070410700000c00e441c01d14050584841e82c080c0d0141e43c046092050301d40217a04172401a64100c842d00148012411140400e02885000a00c00c200092907401d02e50002141c80480409800c202a80c8403810440d426054200d80e51095000400740d03410050400d00d0178118072540690f071700c3c40c3d00c1e40c0d000031186012070420308940100700d800901560302510030703034240d95003108440c206443c1c9021a040035480407104000d55910344008a03c0000483c80345601c5940854409460100f4020040c0c03460307001541c11600502c401c0003149450b485600141006084640107500d05140c46d1409080c801d40b04080590500111030011106a560958601c01c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 938671564 1250 938670314 938670331
    0x5090a02060c100914060f04080702010e130c2d081f09141608070801120606090e0c15030708040b0402030c030f06061201090b0601050a1803150f0212 66
    0x90b1031912000d160b007840b4000510b2020320b0300e403121690500c1071160414018003e10303c00d8520b20f5441d10710303003824800241c801034800141441008015401803840e048180c100030004070a50710320346d0a030300c2610130485030100012950008000034034100d0407a00d01e00703640e201c204208490070010041c140440103000140416081d04040780f84040001e10b0f40140c2000313981030240800c0c1d0507420030001c00507144880b40380c0d48504030900310762041e468a8014401a541e20f603c603480d00d42480d10072208031409540b0b81d940e41800041c2d80449105144100422802030070802c0d40007070070040000c001c400c1da200040001c0040106007035014600c2075020343c1c01141649182c50701d001103032401414424968061150381603075600720000107616071145100f140c4000700c0306201c404c198240c0e04006002440d0360203010109404d50b010300c0161038494030340e20703241d1159601070390500300d8040a50700682d0b101400b640305104120440c09524400a4084070a41ca815209000410001c100802c2c0d01d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 938672814 1250 938671564 938671567
    0x605101e08030a0e19080d081e31060501030c08060c0a030507030603051504020a0807031a070512070903120503090618030c01140105091003080f03152e0305090a0206 73
    0x80c0d64007442c150b58041c2d403040748156141c503460b146c0c0d070700e01104699801080b290400501c8241c04400a100305c030301c0c140300045007138950b04404003c0c9405a004410003864042d01c1c40c0101d0903140020b081c3c0350013000041035035450340c2845544030200d0b411120094109030200034071045510104c8001c0d000c14070b0700207200e94030300c0c0b42280281540c0e04010400e0107801100c0b40c9920b94400c0041c010f038000c4550114031581d82600a07594001840010400180101050300319080841e14581c0108a41807540c0350892588161502c00411104540400c0401b00c003070003071125001b80a41000c003982800c61840c20041821030761947c009169850a443c40000850640000e0044c0d4143e07802500c0240009424a0004450b0400034000d180c060344250002521202e4690491000c0b00d4005d84124504510040d0140311540002c101401c00281d218088070a512001030418142c00c070100604181c0780318260440c410125804440201401e0905000301e941011405082ca03075412503026 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 938674064 1250 938672814 938672837
    0x5061c11132d0303023414040609020c06090d02070e011e09060b04081912080c0403051227010f030905010e010c02031306021917070605101e08030a 65
    0xd801d00d07900e00320420490000d8050002c101a00007512444400384090b58001103980702c980c0d02801c106c01c002c1084401c864500420040c98080b0820300e0040c80a4000325141d07854207842001d82c0e1050080000030351041c02007100c01c1c20140081c5000c900d4501c0681146850014034040e01c500600654002159001401c6e80172240845098014002c2100034851140d8400c6040d182c3e810078481c9007401c0c05107851960070007503244041d11120758480c0148110503003407441117552a2004000a00b003050801001c00459001c100c444c4010403440380180d600c0500c0b10010305103c0d007401645020390208041101c00e0380c3c1204215004d000586000900f080c09410014007615070354806080c1e652038051511401035010005084910202d80b081c0c2d01d45030f0340c61080741d0321091164004880d10304418444001a905825100d819035070304c41c0c2a080041d01d4403150100d9009454101e9168803001c801c0040c043d060032076030b54410b1005002e00b41c60b0300d400c04154403481080444000c0229a0026 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 938675314 1250 938674064 938674109
    0xd0803070201180302071707080d200a060b041d0c040203060a0e0415111602041805241501080a0c1b06020301030b010b03091b0102030405061c1113 65
    0x207440000f510307a21900030594103040c065107900141c042d46040c175410640344100107500040304c6048908160040884607032240085030401021112402800781d1500400f15101003080840c8441c0d0007580d00241c3c491350681040100d400c0d56440d0992030301c0d0003094085a01c404500c0641100d403d81e00981d5035940d401c00644d0245050b0407509031214131009000c148401e80030102c08044075907408101303c0c100d40c0384d051003a0003024031b00300380c10b4042c040440042c10541c002c4d0b0b828941c514101900b0800c180d99003400d18000e00500600080c000c004a540703003c0c1d81c00d6071f9030040340e01c0c056819401c1848000908540c4010903e83d4404d1b02d4011054525100307003a40402140d015051130850307010781c80c01902941c000c0c4800e0340d10042000000c5a00c142d18411203028404c10b00c001c00030311605030210750b00b008103d07a60302d05500040c400051a5280c140080141c0d401c0c1030f42000c03040e001440c1c608211105504011080b110510047c0c25401c3da2503400f50070344d4240c80505503814940d156 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 938676564 1250 938675314 938675321
    0x90702010c090f06211107150e0303101a040b032d070507300206070e0102190201110c1003090501050903161b0b0a0e120607140d09080703020a03090e060d0803070201 73
    0x6841901580c001100000d202040c0c0400300800300c1407030282720321040101c03882c0c1d4070b01003583e0300301600260000c10407060f14007100d104c20701921250700c142000e1351000c80d4496600704490410f025040700b8a4031280408007059803006200b01c10303000d01c1d103040401d40109240113041c002041306914040c603c1c4584c1d1142001c0000c1c0782d40060080f00c40101190013034480390103480d100003056010410394010760010802c581026482040820061915001121055508030100c03010780a1502140e1040c3c5641c6c1101c0346040380c80d04c02042c602030034030704142118001001c100258005010a0420060100501000035040a00b8940c1d40c00181c034504002c0e14594400c6000341800245109610707041140070894100c02c50301915409500400310f0f8440d0403c0f10010000b40d21850640b1020220030050188000d01007800190010a6a1064110f511555060300964040040c1e60304250340326001e075000d4a048c0080411500746500812000c17250b11000030b220f00408000154114405d50 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 938677814 1250 938676564 938676581
    0x7020301050c04061e02030a0c0212060408091009080303060411121302271609050d140d23310f0603090b040f11090702010c090f0621 59
    0x10000c01c40c42c103200ca020810b41d4400d00c91800400c03240c02c010240644d101d00e1194100c0f500744c010718034095610000711803c101c080310403030744050b904d40341280162080204510441c440c0c00159654529030b810064242840d04180c010003454100a1000040c08000d40c0d41100007513134081624050115103120b00c2c042c1345480307100700a5001c1040078980d42c10f200b04099900a58034007592010991503c085480031224540240509030f012400541d038039444c0380307180800f5103010500151584000740030019007240c00e81d400c101b00d01007960008014846c44022000c6030920341d08001c0c0c10070001071803034100b014000c1c42034008104e1401044120b0900c0201030040e00729003620451890b015200c800342030154411020b0050404910140a8416038030b030b03141c2158800d551075546a546145100090100f1a40d080088000107410740300d25004034001c002c60b40000c5910440000e00501c0e1000c1c9a00040314040c9100e001c21409410800c1c2d000d0b8501001c280c10f15010714805244060031503203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 938679064 1250 938677814 938677819
    0xa050d051531020f0d02031207151b02151005040c030e010b0913080d09080a09080f0a0807080310170c18090d0c03030b0a1706130305030a02090103020702 68
    0x741c20000460003012032410549056041c014801e81240c00e0001025039600000750000d016080d014007900d8121900c24181d84010112001c1c2c0c40c601c144941e02d9004000222443d11200c544c0d0009081036009a100008104110a100900120000307546a07404003072010110610004190259900326902c1c0140801400510a4080304070006008000c00042e100c0b495103014211030591800c40c000c98000d010140b0080c1440416032510400d9a00500094107065600c1c44681e0000340c500b400303040703ca030f103e840c0e03880154585200c2a00389035a14607050100d40101c20307583c1c0040d1800c401e81b0503950700980d1320703600c3e075980b1000000e03544190b40040c80b80703072416044507101f9000021002506081070f60384076030b0480511401c02c4103070f00c10342d00d1303040036000700369102c441c64400d03044e0080d0b003406841c010540000030b00c04580c2d010140e42029640c0407485400b1550f8000800c055078015040c03940034034075491680c40040003400064100c11310b0580004018040341e121b03030165103015400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 938680314 1250 938679064 938679103
    0x10e09041e0813061e0215071d09040803060a0f03050d110109050f010f0c080c0d020906070803270a021f050705060c03090f07030503040312090806180c0f0a050d05 72
    0x256a000f5100300740e0b40c030900103c00c06901881c4503c500c04515207c00c02c4d0045903928080d04c03510800e07034071001c69100c1e03030001c000080b6215043d0b5a80001d8140506e00408410f6681d013130010034000f1800301608a00d4090010500800008400144050030700c2e0240c030301450894583c82400e40508003403a03018000c2d00c100e0f84403100600b019440452100c202a0040092055200c0140c2d0703004402c542e01d42d078a1206212441080340f1940082c20396400c002c2895142c05003e9486078841c0e0002c0d2020f0303160714030318086400c03541d0004560102800c0c5040017030036030441560000c1c10004102400c00d2160025082072076100e40038400390b600103540907058038003929110402d070140d074108550395902c034443c40858a800c0c81c0040380b1142030b6074200014524250450b2075003001100810303100000c00ca45828009903000050201e11700a0080e5621030120300c814140c200d00d81a014610a8800c282400c45c45505507161100c1004583d0706590755001194141045030400909040c021440e505 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 938681564 1250 938680314 938680319
    0xc0503030a020708040b070b1911030c0304050c120c090708060d0f05010f0905010218090105060706020906090a12020103110903070501080c0702030706021615080a200f0405010e09041e0813 83
    0x1514903a482030300c600711810710300d80490032044181c500ae07802d250409a401c202003010001320304001c551150240c4112505100c41d0030100740039500e5a00585400c0d009194051030515103512108d0b000041494940c58904200d000030310007000058009004041341607070322041010a4100c510000401da00c1042400d005081450203503218403001002c402c540d4142d4010f61809141030f0303061790307006050b25080180d50750341c07035001b0350101c8004c0d0f52042040c09819290356585a8880150500440e81d6007404c1c0b1034030024040c0c2c0d86205015245120902010249440c0012103008450091806417032907101d11030500c038a480703802c0f4082e40501902c0804070f40c81d500040c0302800c1002c2d8000380c01c50607589000500c0825118080100000c41c010042104c1000d9a08405190540d1004103020001680700500e000c7d4031100b0f80761105070740414108480d40e0461041c411840060311000800e18107561015043c840d9518a01c0f91083d4820030f50341400025010f40c2c2c07082280c0c03c5441601c68 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 938682814 1250 938681564 938681573
    0xf0306090213080c0a0e13060b10030e0f0a120309060902181602030f0315180a0e1e030403061e020f251110050c011503050d0c0503030a020708040b07 66
    0x245030f80100301c014800c0214150060070000d2070841144c072401003104143d10342c07138641d9403202480700303080c0c8042c0c1d02c61404003c1d039036403021900a640ca40d034034002145c002c040c443d1828072086000f0f940351174021311135820101d44070b103068807445915440c0005c0c9903559450604010980400065000700c4c46000c04583c4044010f41c15010b459005402d411130344880500700ea903441080e41f0074403100c07030034000b05400c60800c2d03c0707070140400b00824440100c040c90414858130802210410310072070720380045c210303481000d0040d400304984844411a242d030005600c5139036803155100050180341d454101e01c1d400c03800018120116a55000195940c2c2512580404a0b4000d00840d00802d00e03020020364100e1040c0d00c02c00710081e440003403483c203912440100003800c00302c06c03801410b002c410862880300200a04c10303900603681032401030301864150f08180d0325040100c1203520602c11030030b9400000c00e200206907907200410316000b51f5100501e15108443c1d004691042401d40350101c0d0030700400c0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 938684064 1250 938682814 938682847
    0x90720010515040624052d0403171e090f030303070c0b1b070b0601030204031a01050102061005030a03080403120603140c090c030a0203071b050c011101110d09051510330f03060902 79
    0x140e0280030410014112b111644c40c080c841d0858841c840400200303243c00104449018021000d00180940340710765030240420b056030300403114103000500d00d031810b400300701d94408055040148803403004507982c5a403540d070246d4401d6401c003811004c1d011001402e02c7e84241c04840c061075124a40114a510722500400e00e00403c1c050300c4c0c054000d0000140380c0c00c003850082811120024000c0c0360a00207500c0a8070100006441035007004420507a031015140c49004501c0258441c80034000f540400104680c00e00080d540450b101d04011400d11500100307001c242d9402400400006a0329180ca2809868209021b038001403240302c0700f094042403020114540c0c40c0b41c5c00a8031121100241e00d44400c0c2203810344200c41c0c2d03600744140101550300c0c1c02d030744c412410310b4482c50459141c4410300041044200007240e002003030647c1c4506c24490380f040406c0d118803501440100044404000c121222220f8200345500304100c00452007001aa1003600002c008211228045544406019425505 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 938685314 1250 938684064 938684069
    0x905120304030f0807210f022115030a0311031303030504090e0706080114010c0606030807120921030c0c0602030301150509090720010515040624052d04 67
    0x116039154081d200413802008032510031411a5900c081244001c9140d190700ca03c0c02c0407920140359034092002d103010340b6100509a505280300d90015078840d012110600c3e100c014007500c6080080303040f1092a881c0022000c00255240c04c1c000500b0b03043c019050f14500442010090004190b9000014590004000e1084d03828100044c41103066100401da03441d24039102c0d4070000740568004000b00901006004900c0c501458034a203110160f03156103042d29201d41050f85d40c81c0e0000340b8803041100246036124102d04604022400c1454407000d0050807658100d100010402c01e0074107002c1500ca800c0c036031401d5500409074030780c658031404001d40d2a002401024501e02c10841001c8001d03000e9004d42e1001c9100500c00c54036540c1c0e01c00200c440d0801c1c030001031074002a01d584452500000e005883c03080310000c145a40351181c040821007900c2c000c0c1d00c11a11410602c1505c610036446112228030100706050407651010109a82c0310f4982c0040382c00702a945240510850a5403204001c004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 938686564 1250 938685314 938685317
    0x405190c052104170a0e031014100e01090b01050c01020c061f0f0b0a0908070603050f06090c07061a0a08070801050703020a0c030c0203191a16120b04090512030403 72
    0x141000b000002088850301507078050004010310340310b0b1054940c00c2005140b080040c3c0380420b0301035242d0012030314050720020942101703a1614030b028420071200c2035043e403005c400820154440d2800c11840c0103902c040c000c00085940b140484216640543c0840d021009000f00031507232425008039064451009485102000c2c20451102e1104034801c00000181c40400419410051070038800450f20390104030031030240a01051700144e001c006100d468000c00d210344020641c1e14204112003e03441008003510301c501c40e810203121034080c0110503a16210f0740604001040320381d074622a039010450302000348d8081c08040c03010070045404222001264280e000038801d58450308015400d0b4002c002c08400001c00509905000c00c0c401d5103203002060010742a140000315030728907040c40b003410000980703030003100700c4554003540303649841658846440152142d40f110594001400d00e015014402045602c410b5000c130035980361b134010316034103900c10100c4910030028400024145c10848040c1e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 938687814 1250 938686564 938686597
    0x60f08072f0c03030306010509220509060711013303051f0e0606010f1b061802240301170715031506090501020d03050a0e0610230604050405190c05 65
    0x2142e900b000010f036802070030b050b100c1c1c508100e552014481c15440e8010b00e0f0550019403401c005040f083c40c0310b01e50281d0f140c00b001e8207107843c080c1e1000d00408440c02410440780c0c03520350b250f500038030304c0d151000e03003400c004441300890384bc2003007207008070706e00c6810180880c0120500d0550031200a944100f009009a0007440400d403000f2440780c485c242240e04a01286000100c960018032500450560241e0802003a4203800c2035200c1004a4000807a1111301c05041c000003410b43c50b10f407c1041030a010f41030401010010505e0800d5140810722031002510205000e000b98400c081c0001070241c49a41440e01d05102e014100801038074248080e80c22a0001240c08141144074048144c16128103800400400d5041e55003180204002002d40d90103954400c00c607027400354207001550203401100784114142e800e00e00034482c01081750701003101b04400b41120030000c4e00c5070003d0b1011503404075400211035840541c492000c260038210304c0d0803540317814007029405030004041c00811400202c0c14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 938689064 1250 938687814 938687833
    0x1c0915020408100b100e060c0303070c03092c0621072c010302060d0605031c090602150610020c06030a0e19050c190b0f0414010504060f08072f 63
    0x9012900510401500800342c2c0c0780c01480c0600900c40b280d1b454030050141450803c0c0100110b082d60402e9078003c0008100c1c0c0001d46c1415400406140a07119001d41ca0740203004100d5032800040545041c2c000d245181030024110b0345d02c407030311380480f400121044c41c00ca0540e404144c0d2181c40500500707003000c1c11400810b40518a0011361800707000600810040c607400d507000c220300e87e045064501070147e15010040381e036440c00d020b090415a000701a07800c140e10840800b60501c0328513040303c0304541c04803014841c410b00c0400c1c0c080e0001c06c141d800f039540d940d268404030f05107880900c2c06900103a001092210307a6000c0d50110408504c21402d07588000c40e0000c61800c400015070014002ea07109240b20704280c40c18403900810780d42006540c4040c07a50b5100c849605421014a4041c4000d01080822410400a01e2900100c0d02480c20351719182c1407090203071059286050340400c101550300080e503240e005904050750b036160582c400380c8a2070002040348440d90f0490b550200c50082d803401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 938690314 1250 938689064 938689093
    0x1113050105100c0305030103030509061c1a12070611120406120c02060402010e130b12160f050a0303050d06091d0c0d08040b07030c231209061c0915020408 68
    0x1c140d003d40d4140c0c1c0341c62440c1d10f143c0781101c0300e40000c09a00c2d4800c01c1041410302103031b4850400c00c10100d03d200045018040400c528040b9035801d40703440c1c0614005502c0064181003c01c1400030341d900307030410042000c0c1d0304034002d141144071002200c80390030010380401d1064121901040c5900c05c1c85060082180d150300898031808251002404641c0c1c64201c10803600c2e20700301e400d034154840c10b0002440c001007000902c3c4180380342c103400441e42040d00705200a5840c00358003000b60906941804c4458a840041040c81c2c916103c003a00300040400c06e10586091500010f009010800003849240c100300b61b00381059030660003481c07444c07003141c002c80c046081002184001642101a550609103002802085a0f000180482c1045408080c800c00109114400d42c2c0011103606000c00780d62004191501d00491403400034084c00040c0038408030740c0e0f10b4000712040c06104007002440a0b880154003005400104002030141c2150301801064001c00d90181048580380390480701e4000c8100788 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 938691564 1250 938690314 938690327
    0x30507031403040803090904050f070e100b03010b03070e010c06090b0709170d03151a030a06050d08090d171b0106050a0b180102070f090c080105010503070f0309111305010510 77
    0x2da2110303500240720310340c294582402100d48c4107001e2402c0d100d1464480030100d083c002c0c0c03608482c80e40002c1c3c0b028803010b42a903500450203000141d64446c51541400c195180c680002019542001078541c8800500d034031903001e0900b110b41c01501407000f040c2c03174601180919070032104a000184010f41c0001c0f00c1c141e4407150501100c40038094104042c480e0303c210094021510109050b840f0480001111851003c03005540011004595102c1c20000061070942d2550b5000c113101d61440c08401c004503500341c0494100032000c9915414250b1940350003100c00040d500c004200e210040381c2407080c6049249407142e4100c20f217008006a40c2c448040124482e4180a01c10165006101081042013071400600340410305004842070242d880300d2440030f2030307490f40181400a8540404680c4250030051441c0900001d080403421444c01c210010085205911500201500c50f90224140031035581c4221140d0340190289031402c00410702a0080d210a10900e07000c2d40c07941044400e09445000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 938692814 1250 938691564 938691569
    0x1050a060501080708060303190305060f0f0907180e090a05060106020f0d03020711030d02030409050a06060c06091110050c0f162904060c060c0903080d0c110703050703140304 77
    0x3c44121003500c0782c02d802ca07000500149107c2d058403042088182c0c052a0300c1e0344046000560b50041450b1038404288a140050b00c14840c0c0260f46808101e0826650a40034951021152030b0407114010820300851012696600100c4220300322000e01c40c880c6804104a00907a0058080b1050b83c3d9941030100d07641c2d02c0c141d0080071581c100c0425150b450340300b5001448940c0c054a12a20703480002000241400220840c0002503480040c08115003c1207004195000243c10800c0020034900740d00a021441e20407001041e0b1951460010100540ca400414030702202801c107803104061090042c04560010900b000a84290002c4000b15100010350070041d041d0620922061807500c400c20141070780d0a118602da040b1101540c3d044010020050002490a036036103a4030304003030382080340840c0c0041c644407013080f500070f20a0001c2400e0204448519120072800101e180a0300400c85001c4c0d20040d0041d03c41c0100c40c0c00005000000840c0b4041d28080d400041480480b00e421950320321561 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 938694064 1250 938692814 938692817
    0x615030303050906220206091f020d080f01050409021804140106080c0d06090309170102070b060607120e01030b0d060903030e15060906060c030d0510170a0f0809030a031101050a060501 81
    0x900010006000e100000005d4610240c002d47c20305c1d00719400154950300c40c840c000060510300c0e40740f041d2182c2c1001419120341c000d090461950900ca1990741c01c205c0140105400355031914000800c40d00c03007100c08141d103035080c1c1000b400350501c0e01c0c01c0341070440d2012480d4595828441c020441120109410002000040100d00c040120b40e80c0c2c4800f038014224242e0034408170303081c001140011050a500f07081c2d000c0000607600c0c2683c1c0b8103a0076059000d4840c0b40030300d1050000800190302d10a8041f4071101d14100070000710804001203020304040010960800c0911288804000c019005004000c0c0f01c1c0c4c500b480381c500c0101002d41e4a01181c02020b8005145002088080c101768ac0d0081e04200040d0039186403e510b035a10528662104c56140a4290b440040068103210381d80d2a80240441000420042c038107840b5040d035a070030003c4003420844c854540181005046802c0315120b002c060140c5011880ba400c8c0a40031451905e07403140da55003400300040461484e80320707000035038105 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 938695314 1250 938694064 938694091
    0xf0b090d0306141e0f06030a0c021c0e0d0507050d03020703020405070c0305071410020711010e010e031f0207020301111801091d06031002033612070c030615030303050906 75
    0x8818003404c8116160641c07a030007419494007003042e030f2256402107100d004014008101c48004c0e41c070003441c00740a451510900440723040350390b00c1c0300d611002150383c000d801ca40d00c10720f4643d0b60400f64101140703603008030f41c4411407110107800c041e004180402280d000300e41c100710a0b510386a041d90758030303d01e040040002d64200940790010b90b1003807481207500b00c0c0100315110003204010610899101440030b540c1c011041c5400c6100f9a84400a5a01d2400a2a00c1c0110b6020794003c60798480c2c43d10251401a148a00c10000c0b00000d81d05403400113030000d00a0009403413890704550030303900c4130301c00803504586001500d4072940507920700011602215030018142a11682e0718010b000d014011a03494040c0c0340c0c49541d40f0480d0700166010701f1203600d144894a02070071000111070040d007400c0050014804010700b064001084940041c0141c034050350351a10303645401c000640705900001c2a0500d440d81d45650070700e01110f42d000340d030300c691420030164460845541e503032803003240c0e031400c004903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 938696564 1250 938695314 938695339
    0x2426060c0c030712120e011a241b0d0f0c08030a0f050c04050a1706060927070f0b07020a05130b03030403060c0219050703030503040f0b090d030614 65
    0xd000182088403030901a2402c2c0001a600c00b1051030841400c00c0c0061902d048a05d0003001610480c0c4500a500000300031500042e0b01401960344282d000c0c91203000d807030030001c04c00030201d45036140b02c1d2503070b110840d03441041140e243c2e03c1541444120f5050301c11881c50402d800c0c046e1880d81c203c4441600e852001800640e60300803607034030003001c8092003a150703001765155080328008e00d40250a0180b2241d00c441c06d140c1840144030741da07448440b000fa80701c11301701070106001c5003882d004035080e81d807a110b654a00390184200f821051002c0308110701202d00c4800c0b440080384800a4565010035440305541e030318240001402031440186d84244100400c00241c600300c04c0c034131240c118501003c01c003120840e00190650300554801c2d030340306413182c00c040c0201d0760520100c6014075440030213549160003500c4940d683c6106000041c18410008046010301080510802c402940520400e0451403c108241d88443c140100340000c2802c2400200e8400850394940600f210058101342c880c0c41d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 938697814 1250 938696564 938696581
    0x6030f100207030306050618030f0d0c0b040c12050106050a240e0f15070501050a1107080a0519020a050f030a120207080f040605041a0306010f080402010201242606 72
    0x10b0081c0021828590b88200015060300c800000c4c00080071000700340c04402025105050174078503581211300c0d00b03821004a40c0003040d007180350807903030740e42001c886030041d0307118138110030344070b2a5821080d00d0816510481c02007180542181c829500151401205580d0f1120300e180c01141440e0751520103404111401111446100c0f0783d144000014414201c82e01104089400700d83c80112001d01744c035000a4a0042c04803d001c4d440c0c00801a00c0200700b180d00c50400c1d14080c0c011a440200461000145040181d205505071600d010312540c640006000300c910103903030351040500454090280000c2008440004403c1d00e800030b0703280e01c81c1404c0e2007a20960340000e5000310300031036442c0400e110f444807c2d40414050300141100c5d8035440d5a031403d00e03141e0103061106d06a0000c02c03442c03c00c00c0000c280d911003030300c0c0e400f2001030a1400c3e43e034803284010b07409003001d04c0f1202c0840c0d0000100a03d42183c0c3d241030707400c03228801100e840000c42000078040018001c1159a450350001d0007290124 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 938699064 1250 938697814 938697817
    0x1e040e0c030405010624081f0e040606030b0f25081b0c0a0302280213090311120a1209020904080a0908100f06090209010c021306180507020606030f1002 67
    0x783c8208000960756840d103814141c00e00d0100d1094a00c0ba100f103490a014507002840190050001000d0382400c00400c0b000b00f40da8006c40c000e012185400b400400c08210341c50308094091a8828411007043c50000c581504240048070b62825541d403c003440342c00403103110400ca103450516030314181196182c014500c8180500c0f400051101820008856685014800d100100784a80e014128103115800415a80d40f610552603c095101804100041c0c0e034000901000825641012866420904054404c0c10404102c06100e0107008401b0201c0c91301000140300e040c0380f544a40f110f001442032004111424000300a411410f510041808146071a010381440c0f070b094905003216585420100b400c2c51003d00c140f001c082d450b440c0032540c4100078094803001c0c000c0c83c4011402e00000800082c01e01240040182c0a040960118079a03020700b5003008000d060001c480310320030244118408001c1500f1601034005000312004982c0710700d40490000c5c10038800d4030050a03102c1d003910302c22000b03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 938700314 1250 938699064 938699071
    0xd050a140a180512030402031c020303040632040b100b180301020f04090905071a0d0c090b040e041103072d030c0308190e06160206070209010b1e040e0c03 68
    0x121480b0703010580012410840c3d0807212440d8400c2c076850317040c035105140c90800503c20380009070343c4410f00982c200743d001041d2a401500001d010500403407007482c00c8a03e400c030303841918034980b05503564500707a6200d101c114012480f40380d444401d5911107160300140c0c20b4500408480003401c04c0062440011103c8021409600900040c0b5010300080c07283c010754041e51068500c1600e0f10020001d0080030f100f00b07401003164030b1030340106d208080a40121740c480c0c0b54800540c60313610444020901d21502008000e084c07050401651280c4958014010200865045075411908400e421103828082071450407104000c4101c900c07050044208552402260003103d4511181c0d480040401c43d00b14196000b0350041c5c409c140d4070650128020740c01c04e1840d050500b4007c0e540d05d07910f6252110f40c12664461000d403680c285140305480040d00d0b9101d1004080d600c11807034800440e164000800500b080d505602840400803040f0a00301a28001d0744240451003951800007812800c801006551 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 938701564 1250 938700314 938700341
    0xf0f030f06110c0601061202090603010509100905190e0304050d030f140a030614010e100e060403080f090315060f040509010e151021022b080d050a140a 67
    0x2d044004200300c5039280c0220320120781c01c0c3d01c80c40041150642109101c02c80490440f025480c0401c446c010841ca4030043c89494044c0c40440d000800c8410000036540240000c40028007203400c0034802c90f4600b0b000000c1822085140400c40074207020004112402c40310040c1c08009103104640781620384d0340200003484241f0103101c07034409500f01240d000f412001040d031000900607041c4030301107846070220b003c0389060029103409074a2907615850101c05001c0d892070030010120451012400b04d01030b5500c01020302d0404908034100004034800780100c40410b07000c41e01c550400252000d8218006d0315403a800090b203103100c12440c1880e810480d4409441000440d80343c03040c800039494600810142070143c078a000520003580c200c020041700611308169070301401101c0707102100103160300f004024850306e662803c0c8070b03810071110051001e18041164400f0300403060b04100304164407204908890070f1401002404010380c6100d40002000b041042020340d40d118200b21004002d16a1401c0307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 938702814 1250 938701564 938701571
    0x609070305071b0305040603050c2107031d0c0907090303091203050702102001020405030715022b020105160c060e0102270f090c0d152c010f0f030f06 66
    0x4414000c9446250114805d5071195619890310400504031203002d001d244444402300500b06800ca006000d6661400402490400f0f54490007c1940101a4030301e45500300b20144414021568011811400301074054403d02004d0b5039862044411101c0d0f07010050125503285814442e50382c0a42c5000326480c424141640341c050b10750006040018162000d000044060280443c00030054144121041d42e600c025070034281000000f80e107616403409907075561b10681d007080b16200c1c42084041c0d01314101c91590b401c060b00008440c54040c105822000156003443c1c0441c804400c03100c40034910807055610910310005965521018107085503c09980e90f409014000c03070390040740d07060081c55a11580c001604403030030043c002c400c0009030130707035100e40035403020080e00e00b4103502160700b070041007000014101c400c80c070860340f00c03031880d0002400d03922580f0781c25061440003407100341710142c80c2c060301c0003603a44c450510800c40701074003c0e081c00b06903581040000890252080c00814850702010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 938704064 1250 938702814 938702837
    0x1f05091c08071b0f060209030f070b0702060f040515030a050c03040c030b0601120e0109050f07060c020904050a0c0902034303020d020f07030906020601051516050a050c0a050603060907030507 84
    0x4130030040d080b0030207a8100c0da00040000d20780c9401c00401ca49103414001410a403071400b0003030751442c0a0424060f007d880000303105980081610300325006000e006204c194070080c1d01da03603100c140c0c10880d402091301d4540780c0891507030100d11059921440e4480c403010402401e5a44046100300d02524507070621001c075a0040c10301c0c00704d001c2c0300e452020704800082c20041d0b909007217160040c030700945501504401014011640d02c003005c22031554068811103130544451030000d18140303410304081c00030880d601c004241090103070021400f580d20310400b0405460000c1c038030b030012803a9850038451420745400b01c814021184d0b0f48550f5070901800d0050030408031301310000903030388a009030840301c01e000074613502010740001c1c0d11005042c1e1480286001d606083c00304400502c0d90f05000000200401c07c5004c3c80064450480758035403180681d0381070042403410660380c07100812000c0c440c22009802107680e041c040e013a00d12400000f00208001d0715800307000d4000b043d000d80700e10108034068608 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 938705314 1250 938704064 938704073
    0xd0c0c050d180e040b010909170a0207031a060a05040e0106031707021206070f030b040b030d0804062906070302010603050a030c030212030112060e1f05091c08071b 72
    0x40544040da2910b80485442c4001404094095000800007078800400c0c8001314600342080c40c151080700800103204100ca00b041c01801c9140c105580e04da61001030b160b06026408900071044a20950a100101c110b962040101c0e804c1210459002203200a04008618154004805c01c50f10500000f0b041902da4071558003000d4154100780c20f0810000d402c0046040910403505d005a070840601003d00304503000620f1400750400300c108040d110342d030280b82945d03113a02c0703200080001000c0340c820307031005507014190410440341038403070a142443e954414000c82a442c02020310310720100c007000c940d0108001c0c03650411181030341151340c0c410001c40010000c10507030000d14002c0d26909070034070340791900034580104a800400402c1b0240010407070405401d04404080f0f920580100d081200310740c6071413074071640355004c18251005201ea420300d07944507440103006a0751075040c1d4503c1940e00c54103100c041001020f403400a000c40c000607500d107225607108080f0301d500304019180d072202030300c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 938706564 1250 938705314 938705323
    0xa1d190c0206090d0c03140306060409020d0f0c030501080a0816050307080d060815040f0312060609140301050c0f030c0c01090809091510110102090402041203081b0d0c0c05 76
    0x100d0340150348401d00b4444141c004000c15103c50a10385480c420203541d50390300414080d482e0b00c28103403810010010038490350310300e01954064040e032901151120a04190038007d046016041d0640c3c500d0b01180001191080c00741038140c1e50100000e0101b41016643c28074140d0165003070238042d000368805000010f0301400180010b50045180740d85039100303c103450301101c0541c0e2024400740d201a0300c0380381440403001d0700355010741c0001c0c0412103a900d5040507114a480b1741868803080d8035081e408200103411000e041c003940c45804c1c04120031502034052508a6100780c8124502550038000000c907981401d0045074001c041c0c0c03100301d0811f5900c1c81c04a007558106c410403504403201007620013240c2891681c0c10f60080300303a41103440031041c40c0046500b02c2c3c1303000d44403c1000441c034046100d400003501120100d2034058021955181c1d50003001101000c01709080780090b036610045904400c04540940c1e9406641c10712500c1e00c3c007081c030400000c0a0003a00781d400c0c880d0060410b0040b030010700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 938707814 1250 938706564 938706581
    0x1521011404021509180a0b0a03052103060a120804090f020d0e0a030c030305100e01121406220218150a1d0604050c07080f090108060a1d19 61
    0x1210041c20248100325841400704403c0020010900451078a6a1503e1140300c551101c3c1c1902a0740d521910a060080c010b8100350340d40298041d080041081000146140207104002c60201c0034030fa61030301803c072480300b60341490380300c0b00500f005c3c0008140350413408a01442001ea1601d010f54035003035007056400d008a00740d40198046401421290315010f46a40650120081c1c078000290303680291140c4503414001d420140e90704005100d2000c1c0b84a503001904007070032001940d60b950558240c0b0240c8160080714900c00b222010355118000042003030007680000a400c0c02071480310004a10510100c0083c0c1c0d0283c0002003034502c80b2403000300a40113621007602c408540b10200c05104503868268041449100c4000f026045044440c4e61650404002c5601042c180c40e4404c03554494010140054012000000d03401d100000c6032000701641c003400c0c0c907000c2035a55000304118a400b8180305491850000c42031f000490045140c6241d40806a10b078200145586201500103c40020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 938709064 1250 938707814 938707841
    0x140414060d0e160f06050408190c0f0b07140c0102030a0c030212070602090a1a040b0f0c060c0c12091f030e070609050319081209010b04090b041208152101 68
    0x40c41c00f130001c42e02019807100580300608000d0314003898103003555a9000010007102d144951a0381040030442c480080000a024085424041603120380303d6192a0f400680308a840b01051400072686000200d0fa599031041c050f0091030800e0543c0701d081d10750081c030982c01c0b400c40c000c40711440740500c100e802404180380201801615600300c0c005004404000350002d1404c0c1d00340c4040f05040810a104541c203644640392656100c000d01784500c0700c1d174000c03140f4500a60081c0410070000d03001081c0900609080700080390080e110844210781d0740d05c030b10180642c000144040141d0100c03074a020401d90460540350008000f800300c0402170410200d508810700041030100200312a02d02004040413051241d481c64010300801e0380c40d100c00d44500a54944040616070005058020030340c484000010007600078440c1400504c0d05000b030241c103c4084904100041c0031220062140b80101d1013490398540d411450712040003003124030a4110030306010b0000d10f04404030071400078082c0041541c1c84c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 938710314 1250 938709064 938709103
    0xa03210504080309061e07051e12040c090203040807020f0f0a060306091a0a060c030c080c0607120c09050906061605010f1803020c01140d0516140414060d0e 69
    0x1032019040030400f403c2c624006c075a200682103010349428050b90071001c6801c1855484080d00c4141c003440760300b400a0000098041043c11034603200c0d21040e40f003903125110226029444052200803404290740162800c40140141c40050400303a41d000d052010040102d40d40709880340c0001d40000940c0c01000009848110402180d809405400382d54600c81852500c1203004001250741d08040d0302c104000c010400c00300e40145401115000300b02c2c2d8000018581c0d501e24501c2d0503030745080a481d100005803602c020784d81c0301041403040b0903033806a07546111000303182500300402914050031700c0354080340810412100110003448000d15900c2840080781c0f00c2501088a81144c0750400903520b0082c1c00c10a003400664049101e95202c502401d00d60402c5600c2502c83c10306000d03600300500d07800e01d0101070015248001d810014440032607620921445c8004001d040d60b406540724085a48201c00c500d00c10600e0b240028128800700001c3c00905030010090796450f10000c603080c01041c181 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 938711564 1250 938710314 938710321
    0x803040f06050a09050c04020a0513030302010912050304030e09040611070f211727010b130216110d0618030e091915090e1f0b030a032105040803 64
    0x4901074194010240c843c2040100c2281e1642500c402c0320400b41c034451580007031001040390085040c4d904032000b614060f618980c0302c1c80c1c064000e09407880240c1d201c498bc075244101a604c0354003124400e9034955915140407961320107020b003c5002600c200c4040c0c3d162006254952050700c003500c2602d008130103840301c020060903c914200d4007007002c1c83e44072001c0c207032440066401002038088040110340c030b400d00c2d94a291040c5913036810000261140d0140003100710400805421041104104030fa0407070001d480342c68400704910400805116401e07152860401140c120071610181c01800342c120240c1810981d01d01d002c4507030f040740c0c2107c0c0c0c7c5102007075030090540c80301d480c2004040546854a04c0c0c02c2609121241c05c500001c40010b1070344078001101d208515000e104024500040240012106a50501e0301c8448000d5101100042c04008110711011030107410040c042c040c001c3c0a01c01102c0e2400c1b2410703441c030f9400b890701c0101d03441381c034041403e0381c4a00782c0700743d01480700c2e1500d07802c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 938712814 1250 938711564 938711573
    0xd060503121b030f1207111c0305070921050a140105071124070e100e03010c0314040b04030c0c09091202010c080f06030111040e011706040f020613030803040f 70
    0x51000c910380c42c042d070040c808000c1d04e59120040300d100c0c1107200c0d01036a2641c4c07100740c11107404454503803421b4503008200f041e4541d409440004007520340252814480c076560305104a030003401900c40c844803041207403815907010340c072054003658050041c0103031194001d13982c40b500000103400d503056420b40e546104110040e40c0c0911038404458651003e460030000d82e44210300ca143c14690000d032050446404138010500803403440d00c48030f2001c2c0c00b502c5501c0303011a020b040c003140f0305810350117942400c06500d5107134460320074620341d407070380c0e070820070481d100c84d01c0308243d66100510840c1440300c0700100c81e0110301184e11020041c01101c00100d03403a01245401e181a50bc1c0855010940e070400b403000000907000104141c0c0032a20484001a40c0c1d0780000090250420002c1c02600510010340810721a0200e916a81640c2542401072941011558002d0382c651041780d0280c50400303a020340400518003000140066452710754000500780e00c0751145034107584240c0f0100e50f02a41d5010407800c20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 938714064 1250 938712814 938712847
    0x4061d0603210d0612030e090117061b0702030703060501051302040506070b04020334060c0512070516060315051e0904020604030f030f090905010f0b0d06050312 71
    0x25200303a0250420307103006030340c0302c1c0e40380b01c0a401000c460301c000c5080840c0452590100b002444905ca0704515040c40e410050984003c0c0540d040c0039100640c008201201d1030381c04003503210b8601c1c0040c20301c0c4d5948503404500380c554140100c0b03080000c120142c0903070303001c001c4900a10f0107610005980c0d45844204800c2d12060311000000340d00510041080303942d9401540d00b00c50700b01110103059036447c40040e0030030642c0000308600180902d13840c00325504400f211a2206450f81c443c00007030783c41380401c0c0c8003071070031810090003640300350781a80280c00034101400c80036220354116511220340c400041d10740c00650300031a0000c0d980d01c0c1e0b684100100030300b180f00103140c261810413100005103241028a032050722014000c50009010400f10b407a2402220025a00302c4000041820310345002080e4039010300c242c10000710206000705410100d0301c1060b049600740b60840b20010b240c9020303814180c10011013403d5080d640c02000500f901c0c14400344e00c40840000340345994502e803141e0034054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 938715314 1250 938714064 938714071
    0x4230f0106020c010c0201030b032d07090b03071205190b06041d1b010c060e060108060906011211030a0c060f11011808090d0501060909060c211a04061d 67
    0x210340c03103e4010000799070460600b075010794082c6008900202000007107460040f010004650144c10014020303010b01002d10400d420749030050660780042d582d00704003010b440d40c14003540c1d4180c0001c1802c0141105045c42c03155507620450503202441d03d85180c644d00c180d0508410f444840d03409041001c6c0b803404c1e114500d07009006070a80e8000d98602d100d00d5a0b030f14000700f81c2070a2240f42c200b4114141e8003642c4400f0034641c1c00303a402d120040b2a6240c0c207868807003e100341c1c4071307174451580400c00000d408a0954180c5415000e0300d1400b0340359880d2200d21003800045c1c16018000c419468021610060140c0d0140c6959200c03c400ac070f0140200404e11075500c2141510783e45003200c204036070001c214400b00c10940058090b511111458002900c000110030001e015620b098000210046503400c03102900d80070340003c210b2035110400503507410364110480580004682d440e1104074807260720202200514001c0580440e509a0105040715a25000403041e001d410000808400001024550 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 938716564 1250 938715314 938715317
    0x6101b0c14121203090109021c060606050309030717071a0f0a0903020c040b0612090d0801050d080910020309030a031701090204050a0b09130204030f050d0f050d0b04230f0106 77
    0x440030203103881507803501101c030312455480d400000407804045c0e094228410990b0010420703201b0110302c090001080c000740d40c00b100d0060a019000030000e0048050307a1150030b03403c0145d1700d000e1181d540c4254041c50006000000c45085c840a004691002c2c24121403604100106143e400d112142c504008001495001e0050a00c00400b0009a010032084081001a00c011801016940000e1030901604c1d8007007100502c0602044020100003d40300070305417103900c8041169880d9000e00c4102c84100034050109207003000741c841c040c03d269048034480d0805205a070b040c0b0010500207421f04a03001c2c41500020040b40d00081000c880d0120103004113030384d41045292918060108081310324502c620400c04030085030101c00d41d1151301c0c81e011070030000d10003195201c0d281e1410b01e1403000242c2c421b0b2001e118903560000c649024507c000800c49540d02c0e0141045803e84240000d0b003841800c1940098031002000c1c008010f04920100358007110040043c145840c948954201905074401d50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 938717814 1250 938716564 938716579
    0x101512050411031b18061c0302070632031b0c281101350915011a0702040b030703060c080708270f0d02010b0a0b070b06101b0c14 57
    0x3185550303241c42041081170079501004245d640c150000e1041c606590222014405050b40351040582c0455a50207403041c60301c0306140b10040c10040d0348224200c81c903101030300c00c4034160104115074050145038091101d100c05134090300140c105080f031340c0005410a0440c1c3c00018241c404030141d0000c00183d83c940400d40d0055100c0c0c0d01e0b0785554510000b0113030706100714030520034681d6800c07803c548005414881e00a5409100301445045210129403c49003801280b2076440c0c100341214545040b01c50310b5500405141d0b18080103000c40e030103003108030723232095071000c3c200b00136181031003050000c0d0b014140001c1c40000208002d0529400140250b00704072880303040001c46500010000c000302d440b404c4804036810142e40701c0c2d1401c2200e01c4c2c5240984600d10a424000b0350542040c128450b023550410f0340c03150b4030080e0041034002d00b00001c100e01200c600040d01402c00c80501c00c8000703114a0550000c0200003003000f03175910040810350303503428442411f2115000d00100545646026100c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 938719064 1250 938717814 938717863
    0x219080f0403050a110f1506010507170f04080616030b06040320040b1e1e03070b0f07020910050f0a24110706080a0506040510151205041103 62
    0x200c031a8a0001c01c010140900811561a044d104083c009113080300c60f400c4810780390503c8403060741e50301000d04000508903c540010245e51061082d903140d298809804030840350b50b031400a075a60051795164800d44e00520000031040d030200030703645c028608540f0b94100f48114150042c15929450102405072104010400009151102c44031704da03000055000d01845030300d0300250142c5080b485859201d0141050994000d4070503205588648040f00c09101800d61035141c00c0b050505841c015600d038116150400c02011490010209201e0000c01c841c07420600b0350015500f204103a0303460000b0302c1c2c004400d100798240841042e0100b1422940d100201e803500d141031500b8407280411111003002c800540700301e07500604100440400c004280c0b40f6070350b1514001040c42c1004c517080c8050900f03150100e881818940308103402070071040301405d40305013010213007903a80501204c0d80040007100c40b000d85100190344503c0380030314821192006400c418804051034205002c006085191090000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 938720314 1250 938719064 938719081
    0x1a211b0406141503100504060e06010f0306060e01080417031003030e1804030507060b0303031e10030302121b03190237020a0803130815010e0103150f090303021908 72
    0x4160074440860f40c2c0654940e2201e841c004550301551000d50064100800803c001607100603540c80f0320780030390303c2e2848a105007600b03c0648819120702c90100d40b11807084801175204980701d6034418002e0304010642c0099200c0c48040da48100d8090ba0300d140e41100900401d1f5000000950050088894540952071070346010180074014000900b8481e0005880e0304011043d042448082d0740102aa0340b280381805420b115484002c4c945440d06407034000184403044081c04900503a90141d005180084010310440d0f404e80c0080b0515284540224201403504010001800c02d103203c942e000303800c140300b1a0040d10b0309021030034600c1c89000c145002c004034a10205404201005034220450303400780c0b80041403842060750043c1b24540000a05a0f8080310001d541c602100c040e0000c550360b1149142d00d040041500303000300100039080c400100040703040c6031003520321402c01e094002046103110040c0002c0f1850580c00320b020940208000c4184041050703ea01000b210342402185490311503034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 938721564 1250 938720314 938720329
    0x803041401031e060f061b0510020313210306150c1511040b03010f0812030f060f0306250504081f021e1c1a211b040614 53
    0x90841c1090b40d500c0a440c8103001d1000a29100c58a02d82c00300091600c500c90044128024001d0b100810f0701e03038044000100280414641d01030b003200c081c00c40c0984c220382c2c540203584007508020440700c2c01c3c141140031600310860011101e02206a10003256140d460203000c0c0d031042c0d840244440c0ba074451070b00900384c01260070010720b580020b0034229070442c00d00e0540244040720100100c0031020602040f4000300500850603100c1001c2d0460040d40d1302d440607540c814075a04a03000030841030022500c0305601405454001200a000c00503148007103001c2450208211000c1044079480c00000711a48009400020740c40c0c8a803506a2130941001e0a5560320104000c4d02c200b1850094a1401201000e81c1a22a9905890210108801540d941c7d1060b42c200b0072140000300d030b4900500c44508090b00c10389480561003480082041c0025082040300c02c12880300c80c20040d80030b00814041304c0d040c84183c0440012002400042002e00700303010440e611a0050f46086048042001a0741d994a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 938722814 1250 938721564 938721599
    0x61b100209030d2313080705040506031b04060b0a020d09061806050c0309030a030f030c020619022b0207050f0c012f030a09051305060a05010e011404120c080304 71
    0x8042041c0b00540c107042513803888948940c00c800304081012003004005c1228007040b2240c4204580c0c19a465104110484205850460b450750016070f441d248510002c07010b0010340030040c0b001818680d24144001a80d005851000044c0c00100a2081403a0810702e49000f8050501d41a1208030980c0b81040e4038901c14081c400c180a804215004020b40c00c01c00c56030000c40c040c0990702612003038a000b400141c3c01c9035880b40428204102da0750140d100094040c0309450500214101d0010080244001d5001d1601c0b22a00c00d581024400300c104c0254a4041d07904584500595407011070a189041c5031071070481c071000307030002c0340072044580c2e201800c02c00080282210411104200001c940442141d41002003180000b00e0b9600b00d894200e101101200c40540c0c01d86401d40102104004a80c0122001d0341e000182716428005035101c0c0c000d51481d190181004118400c1c51a00140c490b003159000085001401c107458003007040d10102a4000c0183d10015814241007141c16a20010f441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 938724064 1250 938722814 938722817
    0x12010e030f071e050d11030c0304050609010302070b010e1008063c0f01060305060103050912091305090616050f0a03090201211a011107031e02061b100209030d 70
    0x440d020090000303981d44203d01c0590a0750490300e1141c0c5250690700c404545550130003091301c45410303c50042c4080225640b0100d00005940303032506060800616030061b1a180741003540c20b0183c040000d2140715400d0280075800b000d01070f18900085e0200084040707801400c60754004106109076504520745d52308446465200680031240520400e040e034001002e0030301c142500501c00e00211001200950381603038401e0790213009980d2114015030582c1d00940b6101216070000c11500d0030002c0d1720015151789400180004e007081c244039509d40a40d06c0c02e4817030169070b40244040c002180900103100418107118240b20f414941440114159070040a00d500103050700d0780700303101c2103a100310002400b01010305513284002ca40340e00020010310b0f040500c02210803210166001541c022040824034219000007080f20301c2c219560041504000640d641085508109080059448001034803080300d01071001006c1404d6000094076040446d02c05107101031042064840540700800c10744150b1049 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 938725314 1250 938724064 938724067
    0xf0603010f0c08013008220b071403090301060602030c0c090601090b0f090d140705010219031b0609080319050f0a0203180303130c0e22031205070e12010e030f 70
    0xb2100c44101c5d1122810f0000046036007020f4002c00c548440030345600e2542c0e098a0442082182c002040030283d8011903031018030501c204c00010340d0752040c00131801c0010007a40d041c00d203c54040303400d4400c2c6400c1180960404900d901000d441000300f0110b28100b140d0816140c1000000600882a9400303030010201c0700241402648100c002100d01e0050058007081c0e090300281004911403040810743d0449000d0301d1382c0064103600c005800001e801185602501d1040140d174142e900d8401d240c92440103c451617400400300d50144101041e00d4001d400140e40d80c03070540850f2024070716840004280b00e10b03144c2403085101c20000ca00c3e500c215800e0780140d694442c11007694400170b00300d4191000d8840001000100d24900140d613000c140303d42d0011100d0354464084200b404002c43d11480070908200300c3c1100b5040b03240c420744906000c0d04240d01e50300e00030800b0307100341da008603400c6c0c02082c140481e0841a0412905d004901601100200b05120b008840e5030744a108420040314181c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 938726564 1250 938725314 938725349
    0x5150d050102070510020909250c020d05070f06080a0c05160f0b0405010605040e010e06070c140a121b0c05060901052517041508070c0b0f0603010f0c0801 68
    0xc250304503031070183c00900315150b401c9411a0100030350700c03c40106000d01400400714100e42c0703230354501c07440f0b4044001209005a10600080702c00d030f6103032403080c0d80c024490585040401d030305100c01000307050a103160f0810141892005481b0f843c01034014403e85180c03040c00c0080075840810b43e4802000c22039140e0307076800740f4101500390900380389010b091248201e080c4020003805510500448100b41c03003d02800390669041c9088441c00d580c41407094000b0360024482c0b62060070785144452090350030007140c0d500c180c0401c1c9445d03d25101201c03d40d5070b406100c41402d4109900c100d0f1440c1d0044a6000158155107410750f6100c0e501c1802d00444010035071201580c0100140c0710482103250307080c3d079500c00c80c01d001a45041240c000340e507034580c140203840203480d1050843d01941d4800c45040700c9500d5555045604000051004040201d132101050005001062950194050010901701420600101400c44100001c1c0307880c468a07080700c04000581090985c0e04448040b4155040880f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 938727814 1250 938726564 938726573
    0x41e03081f0e090106081612080903011b030c031104031a0c040512010504061805030322020409051b06031b0306040b030a200a0b0405060c3d05150d 65
    0x4032030340080444207218402c12010f1901544218200c0d1112000c507085407001c0c08401041a905000301e00000c00d54001040202d0b01035401000b00d40c4014000240c8204641c0720203036030030f140c10750b00e038000f9844044800005605004800c107281d40d84500c03514151865403403220f910301340304500c5580d02c0210300140b4104030440176030f4000e24024024070302c3d80f265a0701d0a402030404070340844145141031076000710148100300e10121298850015459926880448107210312035942d180715071503818081c800143c0707842c041d40d2222440b601c000c0a10624481c0385c4103024105400c0725001c0c0b40c090080001900d10a144030b000f00541e020015520348078000030074054030700705401d142c15110310342d001420402d0705080361002d40c2c00900c6038854004600304004980a451041450114052005201614003a8002c000301c18171075048640b05112901704d003801e102c0005211407030107000008800442250303a610074401d07803019410415491f01a106040c0010000138881c0079a4070840d07000100b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 938729064 1250 938727814 938727871
    0x6050f090406180b090a03020f031e0309010204032003010f05040b1303120c05190302040311092e0816121112070e04020a0905090d030f0b18041e0308 66
    0x1c503013103002d01070360340f514005895480e01c4061040700107101d004541041020044140c950480414022986d811200c42e81e10070349820103051506155130070440000010300390441e20480744116002d01d90b40403441e00425007180e1080056603245418841004000f518500e421940700c410079142002e0b15800d0704048600d652620340c1000c0040c40c02c003181070f525400c04090415010202044007140031b5042c1c00300c050b405988002842109110a40a03140c68032000722603010010b900326016a02c18110100e407901803505c441b03d4000c140350018000120148409006114401032400110f45061544c1040712810308e005014205034603440603aa541d0842718011041c4450100c811860312444850102c000c02c1e00c0c2203100780810680094082407a0241500c01c1d015400941000f8144403001d4000d0111800c030003200695805052a83e561103a02d18041300306982c0b1032156038501481e2003400403400441800c008552118001c00203a8414100ca6100d50117010740c55031a075480c4a0304000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 938730314 1250 938729064 938729111
    0xe0f060108061c1a090705010504060203180d05030a0908060c0c0309042c0c03060f0702060a1d0307030905090108010917090a030c12120509010509010c05190b040606050f090406 78
    0x121015804d102c600f484d407140d000d001d1126002540c500035600d00041d40c55104034458640507820a1040c07144502641c4901d841d110300141075040205000c1e510a8192b5100c100c1c0c07900480c0e8007000a01184804110f001d60180320b030403200346031814601e40c103607480c0501c01c01030380718035201c40c071008800c044500108021f0404c24207801240000c0303030310b6985511848a140d40640310f000001a4544d00e0504402c0c02031011343c0151400f91144080343c00a88400f02e0b0a1140070182000b103400c8020030001080218020fa40d80c0b03007a1800c02c4c0800110940c1a172082045070304043c07104000c43c41c4094100e501d080307000b6015546049800c04101c540c5c480d9400030b000043c034070000040403c200ba0000701c0951241e0442c00706140c0d58002940c070340c05040718040c0029020701401300d465004600300049140603008503559001010181c500288100900310350001d544018841044858010b03440900400c440e200e001100c0309011681c0680c00070301c00f900d02030b00c41100e100304500c0002900c58 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 938731564 1250 938730314 938730323
    0xb060a0e010f03210503180c090901060801051e0105061806042601050f010b0a12050705130605070203031c1b02060717091c02070b040f0e0f060108061c 67
    0x14150b82d214910140500144403e0380c1840c042130741e021102c03c0d50584211031992036200c25055482d9020300b003905800d07000700307900c261282c43c0b80b03a05c8651305c0500e00ea102304d104000200361103040128031801d6440141a45c004820415880700c0d0400106041c0750559000b0f6a420f61211844042a52620101c004040c1c210400180100c2d005070202540c801401c0c90345604294000501a05800c80b9001c07500c468500940000500034400c01d2402049080181d10b0024a000b941030801001c580d02034070714001048000032103148503461441040010b040f9810300301e0409415401084c0c80344204001c0c0061502681d0910b01502c080340c0c0800c1c2202903840000b034000c004100040d60b03480d0181ca8000110f11215800030f4002d000191443c89405108080c03d03261415980c4806580b000204040550007100301c08030341501400c000e00000c0c44100480180b40d4500244501d14a1006d40382c900400d10060400070b969804c003009a0b0404015240d00c040320700070208913800450501c00041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 938732814 1250 938731564 938731589
    0xa0f03032c0a0611090904030806031006090b0111060f0c070804080d03050138160512090414012102040b040f050a1b0c080d14040b180106080a0b060a 66
    0x480c00001d0301440c0b1038490003082001d2000125002914010303002500d60050f0800009800284900c89007a08400003404440000001c16100d4090b146103400c21496590340d00d01040b011740e44500003001d0f4032070f01805072905003040b12030900185030003041c0b9002c06a0000e200c004200000d81250000d014000907140c403152800f500401801c02886441002c00c2001012005454003800e08004080f51607200300807403030307070000441c1550082e85904000500c4a4509000f0401c103001040d02c2c031403403255950380d07400440100000c03914158441100c159403500180125002001480e04808a070b82109007a04260310000c0c002d03004459049800604100c112171401943d500058000d281410381400640341c0d1a00001190f454000d0030b400040006001c0d001041e4008010b080c2c803c1c4169001c10984810a0b00f008421000c0e01e04460351041881000651151b0000f5003400d130030084001d1000d280390040095807500b01850141c400380d12170000c16070540d140100300f0300a00d856101030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 938734064 1250 938732814 938732891
    0x10c060c0c06050a14061507150608010618141302010c0606081e0120030417040b07110111070b04060f0329030f03070206070f0807020d110f030a0f0303 67
    0x590107003120b81c6076400c00841e01070100f07055141903c85580c0541030342c2c14260072301d80c4548880d00300c4600c201e240000300380c1d20507003c2034005080c0201d40c0607041583e00d080c40128280c0c8541c088600616020340542401814802c1d220220f9160500490702441c100c07c903c0c110703050540045c035169014000c948150921988202051661000e1a400703c00017000320880d1144030b0400003c00e1a504501e4190800c002000261080184801c8803d503090807420640c0b0b902204580b5400000309031088928004800c0e0320750390100c846ca5542c0480400791100518000321541d09000c0e47c01440c091141c611048241d09100c0e6005201c1c01141000058040c4407a03658a00149641e6030781c4c42c044e0203031284c1c824a47d00c0c0001252112580986041d1508104c0d0300c42c442180d0401c10222032441c0e0400c034900159480e502e0b05981c16000f0500d40d1124405a41003120a5856000b401d0107038218100c0300e0b020a152103c5030460542504001c11040d801d031001cac8082c13681c061b05030b04c0c400081540e803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 938735314 1250 938734064 938734081
    0x1140115111609020c0307080301031b09020a0903021c0b160906090609140423100501020a020d0803070e0303040e070201060b0711010332160509010c060c0c0605 71
    0xe9800501985849880d1246031580584900200709000c0d0081c5010004012810a56004141030310300003054904000d5907644002c02c5074404e90040d200201c1c400c0040400d00c0307071a010700c002050380203011850030152070006083d15089210191141c00002541e50241540d00030814a00754881c014011a1420168880030130380e0510050b40052920340c1c0100c0e1a50081031248141c0e5460b842e1000c08900d044444007880c0c0201c1d01c50768001c0d859840d8911204011040c03401c460710302c20480f20092901c0b600002e84100b10307034012811075001551444c0583c50340c04107502c00b0303a0440070141c2c0d00d95501d0b100342c03585100d004004e501407200081c00a002a11002c00c2c074000c908950007482103907500c45500c8440d0046d220050a04080345028859540c0a5486070705001440e18003840f600d216601e0501b50801486250324952602604002825100c15030610042c070f607608155050100140000b0903420400a000340815622012b502c0494001c0c400c10b100d556006006002da440d1450380d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 938736564 1250 938735314 938735339
    0x30a03051816030807061b0c02031204050a0b090f18041a0c12042301060608060a030b06060310030f0807020405071e18051207030308070309020303030c030702011401 73
    0x10311800c516003180803101d44100205119020041da9410424914110744030048a640b1440045910b1555984015003694200d003070030344030b070000d900c40e49500040d50041c1030074903100480186440c0c0b010803052005a84440844059942c1c80d03011645941c41a800324412801c41c0728819409100c032000188000d04041c4410b1145100702110010040c4c503c80e503005070302041c4d99030030f2800e00500c400d8040e07000320003906902c907000f52020040c41441a100b025450641496031240365103402e0140880c3d6040000360307400c0002560489070052944c0c8940d0030045014018912881001001c584150a0000c4c80b001664100c0001e0611003074901d003200c0c055203c020124095424000080c21a60062804070b03456400d4203500500011443d10885201c1381500e49030048401c50f5030045815143c400d80c2c404007960210041c000e0900f1824003410360b500003070003d41050f0030880250300684001c802e030303900000400071413600da4a403003c00346d014010030324090f01803030011000010302c8a031000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 938737814 1250 938736564 938736571
    0x6040b01061706100804020d0b011518050a05060c0a06140103110f363d05010302070f0b1302010e04150e04020d0c1707120209160e03030a0305 63
    0x7182d254140702c4440c840150440c0403120243d100340c854080c0300c0c032a402100d1080c1e0043c4002c240010000080e912801e4030882a0130140e200c45030003400c102100d400c0f1900d010110360b06185ca1400c9482c040c0052241c1e41e841c001d250040101040300c4a4009042140343c1240b03600001c1880440e1404408000114091100351072400701c810890826040551001104003000340c1000340c003600200f10231000017940780194000c0c940400e02c05c1e0058151601040c051481a00b412241000b0300c90312100e820f5848501041c88441e8503d11003495100d00e6058040b0384080c00c000d40c0301d01050a218901172942c0401500f405c0d100d200304122101c584150500ba54401d0b02d80c2030704290500c080c042202d00d01040300444078190301050014502d40d016035136006100034101070f034040c40c2e5600c2c60702c0049035521900084a6090511a000c3c605004d03540150264600300205410250006065031030041c10104249071084902541a845101c582d84500009070807240d4851098000034010903048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 938739064 1250 938737814 938737817
    0x20030405010b041a0108060a0b0f190918110d090f050d05031e0606090d031205010608130b06010e06180102010b04020708120c07060c08150301050f07180806040b0106 73
    0x450036100c2d441c00303200c1c04d03400d032074048100e030a0000b01a0040d658040040c12066010405440000e0b4020f4031900800742c200d00d65000d10b88825895102d80183c3c848000040140042480c060100c000030002e88010401d0000009c00d00aa501e401c03103155100d50070191003441e00b880c4001090016207448618101c3c480c108444403030542c0e000803902800b0507a0a502d00128100001002030080c1d1032003604803000a00040c074051400780060030300c00b0395080072000300b29103108950314608148101030040c1035130705116200d813424054006181104a030f000704407856040200d0f2040e4420314010311510409403480390388105208095071741d00088100f640c0150709000c440c00042c1840c1c02500c0c034940c0c0c803100340741c24200461038080ca07102c001042103090f4a030900c19100814607034090b1110f136004646451200c3d0604840c14019045003070082070180e030401090101062012002951124171841d061606015181c82540c1006007540a110940f1030780c0d040c4010f0002a684d21130488845 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 938740314 1250 938739064 938739071
    0x1e0302060a0b10030b0a0b0412120903080a260405010f0c0c050a02060309030d02070b0a060e0403090306180206040305011b0f08060418060f0603060c1b02132003040501 74
    0x2100340c640180d4440010072a048000c0003840d43c1c070340303010750070081003204004d1a12006030340791414520036030040d41c4610700020320191544240461021811001e4640d80b800340880c0e400c50721680d229100e021188010404407901300c000040c5694080301010501c98240002d50419092a601800c0031024009459191182d2a031029006080c80c14041e80e01c60701600104416400f0040c65800c000d1142102d03000070024583e403000544010103400344540b80c040082e06180d0210403c4a410f42c004501c0c1d0350000702070201090304402c084041301e610100103d4400780151042401c0101f0020094004d48042008400c000303064016013051900142030000c1907817001c3c0c00b04d61000001c49880080781c44034020a44500301790304003228000042c102b201d40c41c84a540d46604440300420500c0c8000e80c0da50081c02007003454001c2c517900040b1440c0048010307490518031041c140c444a4000e1043c4440c8031158a441207540295200400d9801e48000c04001c020195425a100302ca00312544d518 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 938741564 1250 938740314 938740321
    0xb040f02100207030b010e04110a0b1c020702090a0b03030912061b04050a150c020a060c0b0c0f0414040e03070c0f08070b04180e030c011a03061e04030c1e030206 71
    0x2c000748034011a900444006006d07441c041815038030000180c0181c8082025052003240e82e102d03040f15100820403502070681e83e03100d040d030107184a600910b140300402d00401c261000340e075840c8a85ca40101d1462000a06801c1403800680746118410320381d504080440c110511540e4007045040c412621007184052101c05130035100c64034403650050a0780200300800c00d2101e00010201018540c0076030801014500e441d4001072a058816401040020f00d81081c8400700301d2200002500f100c0f00022841c2849071204210070540241d0044000070b07000e06d41c0c1202e20b80d440d90800d803103a00c101801e5a0b69800c071030404050f941c201e40503d0a102c0340c2ca0000007803c10b800620341085400f80f80d41642014201505c42d40410b40c071030120088241c41d144503610600d000d00051000c0c0d0010000060500c2800703d040c24600300545000d44690000c4040003080d00316500c298049006010701d40c0d21239500d81c134065500502091000e00b410110240258649806002030740c5101d0003074085030500d40d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 938742814 1250 938741564 938741567
    0x9050a06030b040f05150c0a110f0c060c100204030813170a02010c020f0a0b03011e05030a0b070909050405070e16020a141f02070303110a08061c0b040f0210 69
    0x10000d10006103440100c1c400140812034074840406480d1151003600e42903c1c6d80a0394200d602020b4660a9207040001051229903400400308268003165201a000ca0aa40c400c141e4850540d400a0b50241d00d000600c1459400300344041405003d01540454850342c0701d00380303c641e94110010019a21040c141d0125804c2c044102c49140c40f000790008010705940342d4011160b504401c1022a042500c00300481c26584c1c41040da28080c0106100c0d440d281d614103101084200c0300c0e400c400f0500e40c1d985006101540b00468903a5007035400021010094580403005c460000c40c551107426024030303003400d1100b0000081001c0c8212814804509010f444034140b1500000e20640300601603400505800c000807840e000d010400184034090b9103000300d45000700d290502e20342c542c0100c2e10341d00041c50801c264040c891030180f02d6100641e1401c281c00390700301034810700000d0001803288251302c5541c1c42c52511000d000400540c003a96080ba2401c05183c4024080844c501c100c0c820b501d01c419885045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 938744064 1250 938742814 938742821
    0x606080108150406020f0702090403020105160f0512060303160b0108010b041119120c20070305070b0f071203090c1509030204021b011407020d0f0f031d010c0909050a 73
    0x301042c00c034481007500c550382c99600940c02404c6116042d0350601c03481015903198061184254029000460140740582c1c02016400403980350701e040c840038080c0e8146803070780f04040c3c41d00003075102c29141c0107455660009146004403000d05807080e980200d5102080140c0d054903040b111070744000d028240a0400304400d035400029500300d040d10074081c03071544240250010303103080e405041450607860014642c1065880c1c00b0410000300b0b0008004a00044603101d2103507c201d0706601602400d419036440035183e140a00c40e040c0100d42c003207103005d80b41d80c03074104890a2591014120740e007801501c42c054041e0210b4a001d46040c1e13040c50001404411010b041c0d00c0642003030f0b48444840c1e05542c2040006c0d0007a00e2408100c076411381c510461002e09200380008151240001078282c40e000c00028076007044041c5001c04c010300f0350000104141c118081121a001e0b0b030401250710243c00c038252000d000c0140940311903609111001c0d40c020b4006601c002940c01c1e548090003607940f4804841d054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 938745314 1250 938744064 938744083
    0x601050d1104020d06090f0e070e040b0601181e0e070e090a09060b04060305031902010204050a05010e0d0b19060b070206030103030311160809011b020d03260a0606080108 75
    0x81d003403408107400709840d10360b000f006851104480050029214444002115100d00000100a6980040d071441c84000c00080c8002c01c22041250202d10303040d83d880c1070201b00a03040c503060200204150001a08403001c41000d0180743c0310750780d100700c030107041422999031034810092101842008a44954814018410080409840140c8640390064010002c1c994030b1826900e0303941d03400d50055035650360300485000b1801400155240d20040304412044042030783c1f60025a84100300c2005151106030000013251000d09004035030300001d0010811170144220010219500c580800c10410201501091001e1070f4600030000c503a21100d510400d48140e07a4060b60041040c001000024440e800018800d00f00c6004507090107241c0d01000041824007400302c5491030081001140c95a02500303130404ca80d140c41d42003018910799004941850003035840941000300008001107000544041d000d91110401007901031442c02104002c005c00703007409a000000d2041000041488002400c01d18 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 938746564 1250 938745314 938745323
    0x61c0f12080420032b0305060108010f030b131505100f03200109030f1212090201080714130b0c0d05090102070b090109050a0e06090a060b090f040b030604080703020601050d 76
    0x420311010b0100f000b02c0400103041c561510a80f200020016a0101c00100074030150030b6081600d071140034041c0940708001d10460402ca2a00010004032034a01d46e00d1084a801480e004455112052140c500d04020600a040510b410a103400c0e49140c3e0740c8030910030340c05001c40d03280300c903141c03140212003030309a100140c140f084421814408600b40039004c0c1c20000141030004125a6a6407000c0340211011800d440c2401005480e903221a004805c40380d020100754800c1104141d00d40c006010140e000d02000100820342c0d0b444074070314200000706c6826101c101c1d04200001d64540d403a21190b405a03083c4000c9025051070000e119010301c1c156001d80d40141c001c3d0602c98104010a202c0b5086500c0d0b4a0400403040c800003a103444d50314000001c0d00c842d505120413480d1030400c2c000101d5000d8810307058075240241c06c200f8041400160703050094122804803030418814000390103030035000c0c10700381e1500895050000700b02c0700400500407103102e130302910403980c1d075042000040e1400000c041c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 938747814 1250 938746564 938746583
    0x702040b0303030c070209090f01050c1207090501050a0e1513140609010206010315140f0a14101403010204080304080610150c082512020c0405041a061c0f120804 71
    0x45c01468075980c055170141a110440b40c5c1c0c0d0a040d03031100d095420545440200a0000902100d100c4803a02c0981c2d0000c514101700c0002454680000c00a00c04c9020010411600f0b600000c0e681d6190b0a01199800c7d203208a03503100c15200b040d0008401451007050240d01d0310155808040c100481500c0000c03030140c02804047e0b28581750301c0c0701900405202e40085503105013040c2c1d68a42007512034018010080580802d2600503a86c60481d44401e500d0741541d4000c80400100f0111303201d00c01b05032201c0324000d0020203a81e6001c41c4c0680200c0c0c025400d00d00001c28081044000011200d118407089041884115910a2020900c840001105000680c503201e000b020890f4a80282009442c40a00d030140b50b4082812546030b45d1040800c5900c40c8501880c005515410401d404d8440400c640800090400b0340d22540c81071881002400c100303e8110025055a45003e6401480f04d00e00c0308968000c4551f00d40490f22034801f580842d0852420348000b07a459101d40b0803544180c0e0702030b1082c0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 938749064 1250 938747814 938747827
    0x120803040f140601030302011a040e21040906090f110307020c0d031b0c0603110c0618011103040b010510050c1e0f1501080106090b101b0b04080702040b0303030c 71
    0x7122082210380c0306545109400e48042945041000401d0080d40a6030001650341014074240d080702a018030381511540c1000d00900c200107020440306544c8101b00303071861b000c15515685801500031070f0320135802c0c00e20f404c40005000501c2d070498000c03079215410801a9030036201201080d400252648030069201d6024001c945c02c0034541c902407680a820300340e804104402d040b4101488256084424425240c41017101e681c041c000ca400c01c03202c3c07824182c244141c1e01505a40c03620010100e4040b00d1950100203040c0701c00b98000818103010f41702d016560326250900c190585400c1c414140031704010341445c0240d9103d2801e54101c01a040040c042001c2c241549149420305240181d5a601030342506c6500b001040000780154211003507107a04641c0341051090849415a0042e07005500342011081c0f6583c0741c001e507108983c1c49042c00c0400b103144070409210f55580711402004020301c0b01c140003d12004001801d4120300c211004e01061761408240b607224041502d9030080c03900103220f036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 938750314 1250 938749064 938749073
    0xc100204150c330506030105070f140c1501080f0102040e060d02041413030e040902030604330209090912030109021b03030c070203061510030f1e050601020712080304 73
    0x80310001c80c000c2c400b0600151503d03072020291001d090b101418810b0030049080860041e028035580000c084000b0841860803440242c0942c40c0d104d52a01003100f4003d1030040704800718250340300c03004590100da8040d40c2401900511394402c0c021000984103103080000c4641050003210144d03400e6102c941c496444103011300c603100c241c002d01240d01c29290000c8031101e940080c0014807a55041070240500c8075142030144c01c0c421902c940b140168101844200940c90014a440d04640d00c80c03d40c2d02207500754048441c640407c058800d42d08241c05415902168254024100100d070869418580e80c403038450a03681d8050b805100742a028040c00100824611f69020341042c064090643d1801758070151504d042d07074022200c0801c03492000c141d9100703604003004413980c05125407062034900e000c18000681111441c15000d01010b80741d00340c000010707909800031800c0c55901700014100d403e03001012406008200c40e094014418011f000400206501408175070030f4000c6c00492460700d881d101c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 938751564 1250 938750314 938750327
    0x30804060806131401091d0d14130605120c120c0903071806091d03030a05040201140a120c0e060708030408041a0406031d100515150c10020415 63
    0x2c007952062840c1100070026441c0d0242c0e1119070300803403c2603050b40c100709140d4101c8519086491001400e01119140403000007030310240032000781028814039030782c001030044c01c0c428200b0704040101041c80006002d50418041c1c590128040d0525950ba510006034150901407001a1381641c41e0704000b0642d4080300000401c1c065001409607180503446620f00004940304803024401d003607440da800c10510502e03100d4807030310201e50f04071048101ca40200c01d680d81d0101070808101e0907a2000403c045a000e18000042c40d10104100e5403224901240030340b207a10b1410003040c003a801d00c1038510020344182d900302068240202114180651034a82107030f81e40008208a50b144000c20000c5048164039000005094914070007641d503e00f040001420340b00f03078226032002c080c50502501610280818842407941440d400060700350303211a440b100304030fa0f543c101074108010805c0d648060000500800d4840003100c2250102000d481e850001c0b44203c1c4075070154009100316000029200e5070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 938752814 1250 938751564 938751571
    0x3090a03141e04090e01090203030a1b0c060302120105090105031f24031b050609121015080105090c010206160924120603050c060903010905250803040308040608 71
    0x201030400d40c50100120742c0040858020054007000300b0100125042400341c00700a00c2c08200038820b810044d404242d80e801054005004d1100181b103203440d44640b407040c64645a00480b2905c01c030b643e500806402036004800001080201e4400851039003054200030f4102c2e00043c004100c90010703150518243d03a4005010031b1001e03100d20585034480000d4940e00142842c00f0380001400e0318500d00001000d886000d142c640e14400303042045165104c109840c0381400944c1c006101c80d103191441414582072034858000c0502e01000303040702c010401030660030b45071305a00801080d100e2124803075aa152512034140168000c100054000d20b912600c840c2c03501480c00c000c1071030b64a445c3c3c20340c50446403a4203401c00c12050304140308016404044034070040d140040410042d401c64a42035225180003144900466001440641c00c0d1000d5206103001e50f0001c098a402c5070800d685400405884007029950002e40003000c561003401204407401c5a40c818845490700c5e10f400c10907100e000004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 938754064 1250 938752814 938752847
    0x30e0a0614091c050c120c13020f19030f06060c050c100c0b01090203041203181113051302010e0621061c030809060a0c05040b091210050f0c03090a03 66
    0x81030f110400b0b0740e080451940c1288208054030301e2a0403c001d00440a50220304160a030344a060308a01c241c807507891080c00582248805681c981c000000c000c10b6100b41c0e0a08017480c3e034018442d403a2141c0c1035010405060f0585801d0088d9a9208000c503030984d00b03550b025101d504980c0d80c507149898006584464244981480120b42c00580c440c140808000d0f0b008150040c0c0000410041003c0f0110100a001090078204011440c130001c0c604280048100148581c1034050040e44640d00d0b60822214008a25002d10892801d60b90400945402c180100e000c00c0c41c00038804420301c1d140e415550010004049001c1e10aa80802d445010401810fa580c003e82c0c5064102003051440020940306c0b8041d03200c964044c200760142915200c0020242c0c00300701e18103001d44400aa02c18200c070101c8000240c0b07151220002c100103040c82045481e036110f035110741c003090207003d02c503900000d11500c07004008482680c0ea540c2191b8103440202d4144100750425190320001a00030350704e4820f8411803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 938755314 1250 938754064 938754079
    0x12141f0503070602010203150a0b0904110f070302010608070b16110a03060c030c08060126090f030a02060405010605011701050402162f060a17040302120d0207030e0a061409 76
    0x180c40101c0d080600a401800050750000f003009060620321030310714a0f008042d2100120a860a0b500054a015510381140b2076620780408106400f001000d8441c03406034000000c0c0d070758a951901900a0405109895240c01821400140503850b041640c000b00b01c803400c2e1451040700c65840240b00c9503035189880d40315644800201c0418964030038900f00c03d03140e480010360142e100e0f0001d040658000c06040c1003215805a40a50140e01c881e4107040f00d01403e2600090f840e00c2c1d20031400c1051102d01e4029034400456a440116030004805015a0103400208551070700e81004403046640c1c51a0f40403451144030040069040650041c8411000440c0e50120032100c0c7c4d45043c1404c24165404621a0300c000091444030107007182da20b401c0200310b8405103000503025015002c2e44c0b80581503401d90f000a0001001d00d0b00921504940051442c0c0701607698000200580003034102e442e040c3e001809902c159030b024182103860000741c1d00980c4580c0508603009449503040d0b8000b141c0340b60401c030f9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 938756564 1250 938755314 938755319
    0x50d0e091006080601271805130203031b01110a020127050706120b04290f0906040b0a03080a0f0f0215010506250819051e030c0c0316020112141f 64
    0x102a00d9000600721f0800180e0800002a030a60285c0c0c00150011b241810243d25020060703800004444041110b21500d000418200c0d1040d8010034044280c0c0d0b800d13050000d003d005d950341c10f40c014984014030501a00c07001742e03010b01000c81342c280290024042e038000d0805100c0d07140252a60442c0200f80000490100c82e40030126040e100c03841400300c84150345883c2118255114042a2007001060321141c0c8481100c20001d5a0b03010040d040a0040b40d80780d518800f107441e101041d40295030807220036903540b0a5000014240d1038106140c1c00084c12800e00038008504c0800c50100a06180c2c14168180c1d007880d040000a5001d8201c1e50700202060300f210a566200d0300750907000c1400f07485901c2d1115503040034548100c8a80079a101044003c0140982c02c9907824951842c4541d1102d02c65102c1d543e00c100500d8a108031802c80c0031600c80818140004120f0707500d03c0120302d100b0b80e40c01c400781c00b41949031400c3d541c01c03590b4504030b00c4812000450060040c2990406200e400d52807200d0745a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 938757814 1250 938756564 938756627
    0x8070f061b0c0203010b01050a1b110312070b0c03060918010209030703050f190812150924010206100e060f0907021e030f0901080a09050d0e091006080601 68
    0x1c007000c14200400c11000e0520190b00d0700303100d088080c00d02801c08503d091229034000f486442083c40e451111160080e81700140410031a14488011001e01102c006240c224503615442e000b140007120003c002500192005402c0003d4901519010f0103488041c1c4560200c5101c5259580c07035400199400e004220041c1c1d010010100158011005010010007858429051012020160110500c91480400052901c0089410178542e24600170b1990701d8403144444860800b46205511016800521600d03489100e814040700c0141c5002e4824903d108005981b00e8404a61510f60b900207403504005aa11444216078042d00080c5032007003040c0ba1a001480708403041e200c1100691200c10b1074484510020700301820000707820b008600b40b070550071a03514544145045281007284d500302050011805030407070408103901c1f8054490340411247d00600b400030b41010688140c0440c4046010002001d0902c01512916034580c1e407955181c8006503a55030807541c0c580151211003044c080c252 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 938759064 1250 938757814 938757851
    0x50a0c08030a0204140604080c10170a0e190809121c090501120908270406080d120221280b0a0b030702060417041206050711070308070f06 61
    0x2c100754000144c807182403c0d4000d001c42521424103000ba2402c100034050440c7c0080c2c49100400b0454500c07020074100d05d41119510351620054115102c034106020031080b480d0080061008030b0401c8650061652040c0003c280401d20040d0000c4420007502c0142c0c00c03d600401000c01d80718049a0b444c1308901c0400c0240540c161410001801e0080c00740025a8040c080701d0020720240414086140181c4800040c0d1048112820f84510100c00a910000c3d44a070403c4c4c0c1018028002c0120568640803251102c690036900d00000791001811003038414184203880444105a214075003c0c011111001c0c050240a401051022980d06403c03500f80c8448a0449015001660100300c84006009000c003c0706150000601340105200308481d250380068807036801038001030040b01003001401c0204d042e10458203c030b440e0b000f1381e84004050107030580045020391403550b81c0a126490350030300c8039100c15040c00010443c0b2002c100e0100400c094200491129000d044005035452443e80d842092 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 938760314 1250 938759064 938759071
    0x40c020712080c0609060405071401030902060c0c270c160c09060609060c0b1609090f091505042a0510021c020715030e1501171b10050a0c0803 63
    0x82c600001080c407414803003071040c250052105030040503d81403d640b42a00d9082c40d0158202442c0d049180100507031090300544081ca8025000039a9001ca10b00d6441e124080c02081d81e0084034001c00c80c100072a003890200950401460310540d080c1c0700e5025001490b88800c00411a40f0004016007011480324101880140152107001610350728150000c1c005003400d6116405001c16070716501c003c2444d0110090f400702d0a00ca44440e40085640c06540c41c1d601a0044425640b520031100b450b01c4042d4000004140919030f901e501d412218414001d54804071002004182c06200103140070382003590520900d0b50641d400480591110b0100e02c03642417050103100168404061050044407400b1100221040c0c0d1010b45404c5081c540c0c1c101c0000101200f032401c01d6501c104200303400f42c0c1809a25408205000d5110055070350304040e611421010a1290090140351020302d40081084144121000041d1404502c403d00003800d9a041d0040004403060240710944040004c1003503000754413 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 938761564 1250 938760314 938760323
    0xa08100306150911030c0412140f0309031902030705060a0c1a150915010e010c050319021002040e06091f090e0c150409050919030c032a02040c020712 66
    0x4186803054807025241904d2104151040800900294480f103800b2102500e40d000d20003d6901c01901c0c10f540c5c241c2c1c44000c1c2403100d000703003d03010380301d004084000c0c1103400044046843c00b82c2e02d207246190030310260030000d6040e4041801081141020000740802c03c00504164094020b141c49a2005900002108088a619004000003114406150320442209484004451500c400c1c80d02203c4400440241070260b00444201c09038404d14030640d40c99400010b407a112000200481c000ba00c0720701d0302d4405402640c201c800120300714403d6504580d650118400d06881c0c0906010410b000500038a9180000c0300040414144608800004140c01d44001500510003100c160401b071580040500c107080200140c041b101002c405d49050b240c492100003041d40300c0e524401e15203000d02c3c080c00f18000b0489440b030145070b0800d201d1054035010381c5032151030302201407030b00d02d45940070581c000902504c614503c0242c241540710840b07407101401121412500c500035550800391a060495 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 938762814 1250 938761564 938761601
    0x50604151e0e1008040f080913020c0d0806032a2107090e0f06011e380f030a09051015081605030a03050a1701081b0909030a08100306 59
    0xb1950402215020b81e41c1c2e814034280c241c505095807040d110442802002c1c0c4100008249804031f6036802c01c40d1061400901d00c21036803a41003603109515030003240c8550001ca003025000a02c0c0d420042003840340c0c030301869680440300030308252800701d5076080f403030150b0072000002c00008a010031184031040a14401d0080200c1890010b04405540e88104903d200303030004c0046841a500c002125419903000080103504510b20548600e10886c2035403048240e40c000701715614807011090000401c00304104145c0e203d4030900210000d0610034904402591901000000c0030581c6170307032111138024403840540b8410002c188560007503600b86580f00c0035103031402c070040005440c10840c0e8040d081110001190f21441c050009889400091015052203c006102d00440b845842c4900007155010b203800c4083d40c4440d80180e450aa400310b1348045003c1511940c814036007040e0b017030302c01d540030f50003184ad11071040740807030b00f1389005020b02401c200315540206c0040ca981c010358210251f403400301c1e07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 938764064 1250 938762814 938762837
    0x90319020f0601050f010507030e060d020406170702010c09121401020a1805091b03090c0a060806100206090618011d0a0c0e0606090607080904150f0f050604151e 71
    0x15030401c90180d1013107214a030500403041c0c099070044e080d101c00c9509810170941250800d00400c199100300d92140808501c002030200705540c014422200340301c84040b0030001c558136501c1c103038203c6008403046008160701c05000c00c41610601c01800040e84101601050720940c00303080d03030a90300f10100c1c0d800844c80b50000b500025003800c00701401488100e5100c10039040500052a0941302030303c1c5001c84400c00000030311508001c01c0481c030030716005071920480540d6075000414501064617510f1080b680301030700202c00f51001400764050840754000c1e01140d101e03040c42e0303a034081c0d84a699000954032081074011002d00924200c00c5524a40d0183c28542402e2610244440503a04043d5403400306000348581c03a10703040d0a42d640307090706480c000d640c0c41321401e03c40712a0060f003025a60140c100b04061107140c3e9600d00203811144110395506003252a809038a00102c058010036402503001d002c20481034542d21f444001b103c00904211204d10100103400c0d4a83c20403401542c086000359050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 938765314 1250 938764064 938764093
    0x304020d02030f0f0c042708070b040f03171b0307230403140f103b0601140f04050402120a0b010f0527090c120618030c07060809031902 60
    0x32803c5d001002c9a0070003000d003101054100e080f082502e6100521025044c4608122545013203806ea00d402c40b1482d00c0134a01307480c1401281050b10400c0b00010340000d9004610b00c42510094003a0046c0d1003d0084e1843c600201001900f0040001e02000b650360080c40c551006040031000340e840000e0211759a0f405c504040c041404401c010007800d500005000491810118094072500440303000032604070050741c9400741480343c90742300c0c15400400000c007030032195000140c0301c40401d5183c15151180ea95030000410b040c894603034035422041102c00f8117110710301135001c680d01502c0201801c000160841c0058a458200e80c412601ea1842c01c00511032182c08a4420300103010071030742c00150780c0c2e202a1216049001030076500400c002100800c2c02640c050009142d904005408841c1848450b4145580d0740401d640c050000340084001110851000c8129558207003000c00a100700740c030300001220030380760050003039006010034010b40700d686104540301d241d19500307680100044400c0d50074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 938766564 1250 938765314 938765323
    0x40f030507051f090b0a030204030c060f09090c020a060e031e030a0e060412180e2e05010e2101050c030105010e010e09010b1602030d0504080d081b0304020d02030f0f 73
    0x22520f50150780944018030b0681c1c001046003c1e200d183c03002548500c40c40d0419400b9004a410050070502c9441c000301c0e0140c2c0c0214403440000e07040d5210f491243d6601055000c494400b0000c500507040152036002003801d0390032820300c090703108049a01d4143ca0300300c2c0c0d90a80d45a4080054400300000c14881c4030012806003c0341141c5c2a8083d00d00d90408c1c0c2e4400c44a103000040c030300240321804541510b04242014a00000c3c5a9562065624940103030002049141000300c3c45003a020042da107018402c60500d003805840042c0c40d188a091030540401c0100074203101080c0d1800001c03660085004402e000301401403502c56075284d141d506000015212003080c880d00e0341005151028200150f4a810215045a4121505c15511550039040d203011004101c0060340502c21029490111395002c0001c004903000d020981c2d961010b00c410490380003405036100d44030328a14640b055001c0e90600c1c011034204d440140400820f000b50750220341000d24100c000d00c01501311802c0145041010700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 938767814 1250 938766564 938766589
    0x309050a0f05190b070212010f09080319020c030702011b060207031706011b020f0103060f030f11090106050403060c0e09040b0a0606020d0206011e0803070b06011e02190602040f03050705 82
    0xf4a0410202e0800c8100f1607a0301544502911446200300d00740c0f080203007940704215403402d111051140c51349034100307050550b0003603a5100d9403290015032410400c3e440d00c2030302d80c00210724000d03500d040c0c01078004443c01980c040c2c00360485c000449509001415078401891094445c1c0c032980c6443c40c401e004000d400c200200503605000000c4000e54400c3c6800038191601e5604440c0101d41451250049000745860342090b1040c200040001c401d100384a041d00c01ca481c41104514248500c1c103040c85612407082c42440045001030106100280c0c450304141c01e00384082c90861031342403c1e030300044d52094082e5002c2d40e00504040a000021005006a001074001340c001060311300303880280295079480503c1181141000b5442e5400880755101000c401002c80c01d08483d2a1041400c04070718104098a645011900c01c00e401c007218030038156401024503080c0c0140c01080000c0900b160805281c0f003080712041d5081001180c2c44408001c1d000c051409540100f54090074203060001015411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 938769064 1250 938767814 938767849
    0x1e030c0e06030105011b060621050c010201110d110f04060f112404050f030c0303160e0a170a080f091c0206160303021306031b0f14070309050a0f05 65
    0x30001032050344d0300300a0029100c420706d25190154011400c2c074600a280681012000302c0740f080ba00900b03403d445000540322401101620800a115030040e4200d80c5080303180c104c034500c14840d42600c0c003040c0d400b000300501c4508041d0314005091741e005495500c190403160114212250080809520000080d000c1041c14001d040c0a08005d0241200c0b401d00c00c20017103007120402c0010b041000074030078000001e42000450fa203c0c510088900d80707036042100c02a060080200009000610070020488040000342599071070310706010b2a03144076803109040d44041c0c031404400d40000703140c3c60010320114101001e032580b42c640ca002040305040402505080c1500f030700c0d0080c000359681204039200206104464090b6203924641580030b8004c81c41811850b03259400c00117186d5030150020310300c0b500490f801402500c030001c0c098400307040292000d0b00185952041514502e00c400007420114064200000036555806c000b8000d040343d60030007045207662041c108080c0c104004e1646108a00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 938770314 1250 938769064 938769067
    0x30a0819080114041104090c0c12020109150c0e150a0201150531050f01090e060907060311220905011d070c0201030605040f051603021305101e030c0e06 67
    0x410b20200c5043d5107546034544115620903d052003400180104c400030403c19505200c01c900315200600503008101c0c0a84000790030344241144a403040c858004030a50100e103410104c6881d203d90001482d03c0e0f54050107101c00140070100340d07900d0182c0190400e040c80d03041a51745010007002401e594800d0f00b03c68862408443c14803499441140881042d0404015042d0300758101c4504096410003041d00028540750005101c60101a140502c0c165204a2400c0c0000e94400e541c082e0307030300c808480469040d0030550b410b00c03800384a60000d51042c01d440350900d003014031340c80c801c1c3c08403080c40d48008032420003400b00304000c12042c0a02401000c00d09040c82003450203d00c1c026086900070802010850001c401c1ca085a000e076100c4e9000e004090000c2215000414100d00280415030780f0000c2c801c159808941c81c0c034428000c0b5460300001e40d00349905685014103000c55801c98103507920a00c003881f1040d4101031601110719a80120695004c101c1d9040d01401070031a0046103040c0b03024000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 938771564 1250 938770314 938770319
    0x11506170c1210030b07170f0a0b06211609030b060102070f0806040c0e01050d08160218100905100e04060905070605090108090c01090e0411030a08190801 68
    0x40040d103918403128640550552641e6040e841081889801c56690500b44403005000803460401e08070710a40e4070980500c092a100c070748050302d484040c0d03014150401c1c02d03000060100c4040d03003a681c0e00400030900100d850005200010400e400151900901103040242d0030140902c0003000e642202d02102c8a880c0421594802421001280405820f80d0344503004140964800c124050040c40b0b01300c42c070188603403201031440e2130303141c296000d0358801c00426000c2030f8614806141412128001e110400207003455503510782c2500710a590b010000000208200503031074101c1000030560007000403510928180981d28064011600816400b919100c10446034a0b01c105200f815504c07090701070300e099030380c82c544003010b00b5a000000346240182c40c00001c80a8110000c0c1a1800098a40410300e503521695159108000d1500381c1c0050300c0c100d01001003100010015400c54015103500494103841800300b0f203000c0900c402203502d520000b0b5881c0541002409914440e107651406082c0c40d403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 938772814 1250 938771564 938771567
    0x318070b0306031e1204030f05010b01020c061801020c09010f061d0303031308090a241e0302090a1d0412022103131502030a0b031c0e0f0d060e011506 66
    0x303040c04d540001c0f0304d00d03070760090202c0582009130603800a41903107540e40d84da0703c0e441e00c0d03030f00c1044480c41200c05600b407040c410031a40c00231811414860010f04050b0610407100f89060f2805484140c45041d80103203d0500ca20392a0b01003200e020348040e01c00341191518200000f095014201c0c0c0603121580c40f25115103560360003000b225084004807480d440d02401c070741407014080c030941d81c03510350084414800140c00c400309003505000d6040d250a0200741c09140340b080d15004000c80458107048018031119150034002da02501003400c0141c141c4100c15100c220400c884100ea84103a5020750f4641c082104100c0742820300000d00c40c1c0c520280c500e000c101019241c0640100c85a007060002c04800905000c0681c400c4a090300d800c211081d0004101110480c025801640c00341a02801c1c950140414140003e012910115000e030040b24580310020803a0500c42d8900041d0784440010785840347d56440d8840422174070301561000684840e5a140c40c0d00310f5003540440008121500c0301082140d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 938774064 1250 938772814 938772823
    0xb03100e011d012709110109120503040315150b0403120507150c26040b011a0a030209010302090d06020d0e12041a070b1f0602070b0d1d030318070b030603 68
    0x120440070b0074003d0216404159091941a1501c040c802450070075841c5c1481b101c3e0240c0e070040d500c00e0b202c0140140d110302194000132240b040251259104200400014541c0f000d007003804500000c000492142503000448944040e501c100e43c41040814107005201c566070f034aa81d1101c0904180749089410f81c5c0c2c40c0003402c0c07001c0010041650f201d400c40c8442e4040c090307246c02c000c6a5100b4510700101c442075003200341002c0d602519aa4071890020030b5400710110400031070a50cc40029062005402044019501c0010310a041607003c5c031403103209803980f14030300c410300740300e11000b58903108a1160b040c11611910010308849d80302a044080c8011260101c0d010340f07010740ca43c000114184600000c140c4142c0c0c41c010b05040c00c00003046221802f42210a415100743c0740d17188500366541c3c00882c1c1d180e030380340034841e05c451040151000d9055182c2c030002c801040d030681803034804461440a0300319001220410b50b1800b00134035034a01e45006000000181c02c080c01c3d03c5003142004404030350749 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 938775314 1250 938774064 938774069
    0x51005070f0f14040b04170303130f0804050d03091509050609010e18040303060501021903020d050a021c0908070602150606091309051f0b0f0108100b03100e011d01 72
    0x207002c10480000c50003441580c0d10f0040f00c8410741c10a0341c0740d82d02c15228800358400e20441504040c0241c1e03490161002104580c0161404103083c8280c0350310b82c032452084100218203c03000041008001030320b8440c048a10261406a11000300d0586441c04022005c0c82c010340100c100428440c0600442d6140025650500000e1802c19807081e00c410210b401c0d03603804921009400100c43c10070040503456000300e003c0c3d5000780d0903124440e218604a21424510b100000c0c05600440542e044091062001e01a030003200d1040320b51040801c030585000150200c85400014071084040c0110b0b042000310f08010601440103100c4102000e104440100c4080c00b031034410640051028030035524a240344d22280050102040711040300e01e8266554420000c03d844c0c43d44100d03d000d00961441c0c07040d002d0386980607140d032008001039001190002002000742e09444076045021a0080b070b0540514071540310020204020742c02c2210148100c60164096036031011030000100e082518081c24a04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 938776564 1250 938775314 938775317
    0x160e060a06030c30390e060723120d0e0a0c06020706080a0c020a030305091606050918010602030403200402030f04020405060102030a020a140a1e051005070f 69
    0x80155040b8422140b0191051600c00d0070841c140d060384082030f4100703036201c0c2038601c3d01c000c2100c090419810284c801203007004460b04171001022450100c4521280c2c03441c19280c2c50104c9002a9a6001480b82d800c400b60944103004075002c9090036003011908480c212001200500701001140745c8402140709103503c448078551111240291400d082100340034140d400b940d41d082e10341c1c550740000e503a14114801e42c0b000802c0c070b00211b07200c10024401c19601c9295680034001c2001c40d40c900f5005008050705e00006840b070741c0d00b400309001e07a002d140c8001d8481d40d914036a41e29425002c0008901c07810f100c000710b8002050041002d2a000012102280e078400014a91501c06070524404a041044402d42250001040007505250389038a14800c500c01c560405c041c0e2569801280e8030302036070820f900581d00400d00c4078007041c0c200410780300d01e81e42141250b940c2109036440e4480c080142182c0c443c03032440700c60060100202031001800004c01d80c10f00300f04030714001e14020840080d4410320b20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 938777814 1250 938776564 938776571
    0x40b0c0f070609021207060f0801062a030c0209070e130204082e020d0222030201080c0f04090e06040302060a0b130c02030d15140102010207020904060b030304090e160e060a0603 78
    0x800c545518007111405c041e101c0c01e49400a42d00c0201522119403481c8080000d84c40380008104103000f40741c005481000004440c032501c142c00c3e0b1180c0c502c8201302c425001d001c50910307803000596601d400d0b940b161250b030303603201c4540f60300310148003020518604c5d4200c0140144014040b0210004203240103030903588641c140d124510501c10b2295100e0b18914041d1400040c204c1076400b0311750020503510266003c1952a024020060300502c500c900009000600ca00c01280600507001d01034502060001d01d160b16066980c11a002160280900c00b201c90700310300e040005058060003860ba01c054030003000c4c0009220000002c900c448101e0006000941d103945460459200b002510310351862040d003003101d59003444604221010034814451024680d001241955106000342c4000d19030240ca80113440d1120340c0c54402410300701a00680522040c000024015258022030014500140140c240c56110f2a040342002410750062504010742c88144005911000e000d0021030b09a0314000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 938779064 1250 938777814 938777831
    0x603030f031a1e18010305010b0f09070e090a06050316061b0809042309100f0608100902030307150219050a020d0e04110f0310080c06040b0a0207090212040b0c0f0706 73
    0x15a40440b25441c40e2500303941c0344d00110800505600079031811804a0f00020f68261150400c01c400e002150307824002214450700078038905164240c03d42100c09640085040350300d44001c00c0c9080ca4641d10151606603031501040555000b500314441c00c1846800160408525190059a8420289201d01603503640a04a100c1800341c0c502102c03d807001d00310118a800d24201c40c60f030340d081028481c05054581424080c10410038800c410840703403060b01130040e00d000d00c071002006014004080e600b502041018100080c1440f0b141c01c5a421109001600c541e01520054012044004100180901000f0700c1c1090f90b0001810045541c0c1c178940004a0019180864007030010021002050080401c010032001402c03409180300750b03030785000101c04a036a00d89083e5104440c0003260f800090402c018021100c0c100002c0031504104d004580c0c0d61a0781e003000808980c40b50006c0b210780b00148050000300035850790391507040280c440c01541054040728030220b1500c50b01c000101010340d00c040c0b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 938780314 1250 938779064 938779069
    0x1b0507120905090a05161107120203030f030c03070f0804081b0c1005070201112b0509060403060b0f0409020a05060d06080a03030605030607090b180f040603030f031a1e 74
    0x50074042c201c0a400103d8509121480d0009081c2c1a070b60003460b200b030040001c49145c810100c2500c44401200108021441c2c1603c00300005510082a07801d40001c1040102218400700150300501c2207511903640d03480d16250007042c9100e600414020010b42c02c00303100c082031b0340d00b064540b03000c800c4251030104601d00001500e00884040413a80256203a046201d52513080006414030600030307214a41d24010050303006131900704504403040502c1c414105106250b40c1c3c0000301e00e41802d175042107803520032601c1c00940c10b504654011a80140c03200d440d582242401d50000c0d82004055400b0701c002a896800a2201c400501413103014203004904015038640e603070052401010494240c40010f040d40c10014040c200f5400768900a1040001081c0d1440c403400b0342004403411004183d0400d18411306640703184540010380395002400903454505e0782e0b80e41c45510003c5102e0b455040d1740c11411900076055504030002c0072901540c1041798201c64680340d032201e2501103c0d031401cdd620322444000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 938781564 1250 938780314 938780327
    0xc0e06040e0718060b0c070303260903130605180609041404061b0c03050304150905031614030405011223100f12020102150c09030f0c041b050712 64
    0x74a65880c4541d60001908200d0290118071103410203005002003030700c82e1103e4401c0d108086101d10713142d01401040001c0380c454134008075045a89100e00d09407d0701d8160714207210b607081d602079009400c0041c08500d000c2c402d180d840000d1205040c0b4505101ca00b010f000d0100241d564500c0c0104c400041003122a581c1e984448034400d0300b0000c03203840e070415080c024010146032141c3c0a09405840d400240302e405040144a0f255050790782c0313451036945039240a400d25074207900c41026901e50140d540080c605002800c4034600e03c4185001d20002400c00900c102002401c098080d0070800051160ba42c0c40b03040306010300c224100c04a400c4282140745041401c40d15921003900700c1d204140503032040100c03410001c4820002160110f951989105005034940100090160788003500c078054900c2002c80c203542c04811107164604010114004c01e0400b00c18060098281c1c00000d80c0101d249440e115601c4401401d10507585141c020240141c4940308040018121640040741c00038614407521 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 938782814 1250 938781564 938781581
    0xc01081017061605041512091406090106091a091b0f0c0c06030f060d050c041505090c090a23100c111e040b04020d050702060906130c0e0604 62
    0x344400a025541004240c4800b02612661890120421a010201c1c072650544c1c040da50701040d488406420800e06907007518031001d6040c40d030387d100c100910100d56030080c00404c80207031801402c000d1800e030b10080e00b1545140c000050003440c05101700b5110540707441d440203420050301c10001a40350720b8070901026624041c0903603403000000d643c0340c1d01c05440e00645510080041140c8954100c2070810036540811500020b01400ca14005140b0b450308032003209809004800b074403801540d01000c2010341e88188104441500980c10821003802d00f4007040703900482c100241e5080c95031940000b6204601441000400c40c0c0548800c10390441c10058010f0042d4020041c1003842107031030000c4c01454048900b80d860440380c1c2c84d0502e65090005c000701c0700142e0209039000d403015400400000b0b10a02c1d0603150060b60a125180c000c07070881c030400f40500b189400509003450442e88141c50070000500150310151440d0181000500c1041c086060394031003603031301c6070650710080030034001c00c1e446 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 938784064 1250 938782814 938782829
    0x50f0123031e031b0606151c05240109140d02280918050d12020d15092012151009060f02190803060103090f110316080c010810 56
    0xd10010750102d8000020540b40c18401100042c80e400f10340d405403640d104a0315039801100c9083e5441c21803c5134002440f41036007181a4244440004000200b01c89040314180c18850303203c524010b14411503100804c0d850030918004a409040040084036440560003881c000c10740080702c10700310340e9420030510780217000c94100b0741c20030819042c10010100520440510134074010312000007a0740d0004410fa840c0c0c001004202d003501500088403006c0d6141161440d141d0b090241c40720416003030142504540c0700d040c00996060030b04146008a608811680c64408121100c94070101400020f480f56441503110100c0d06594484c007a6402040d41402142d00c894924243c400e41900300b8691010b032003040c0d070780940e51500504141d0f502c64a03c1941d900400515040d03400144200300250381c8000107140c0031031810700503a9090354001b50384004a0365040040d41d100e41d80d040030451080d445405d110101e10407443c1841d042d88410b45404d241d8104a6144000b41c040c20a4602080040402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 938785314 1250 938784064 938784103
    0x14031b030a1a010905060909090727050a02030615030901200c390a09360c05090a0b030706021e010212010506030a180807020103050f012303 62
    0x1c141041c002d20300b0b014102c0c50711080c0e0408410552064440343c082d070340060020303031030480ba083c10060324203c002e10f03003035840c801c0c00d8020909100d00110f45001700c07401a441d0149100f030048510996000400101d51944103004101da6603541103403d030200d10296007441d980741c40300001c0c940540390380850b001d510b1510184141260407200002d00c031800034142500c421000302c281e84080b000c20300c40755000700f04403d2070005001403082116012200010800b401050391001d503c0140c0d0b103050310b40d040540e4000366088084410f014031070303060203640801d00c01e40380655440400b0072150f4001c19019060100c002003110303030f240d03010381074809000b4121040c1582d609002950740081141020202442514440c1d501d40140240e400340103995090a805a0908040c000190401040c0442090f11555400003080445540980d81c0b40610302c2c459840c012800090182c6030302610b05141510f000c0300400501c80c40038809058901c040b1900d2815010701c40c0043d150210880c27000002112 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 938786564 1250 938785314 938785321
    0x8030403050702041503052508150714090d080a0c1502040f1208030703200d05060913200a241e0e06070f060218030f0102070314031b03 60
    0x1c10101400c04030340700f01c3d0b0602120500340d84075103000702e02d4840113007180d1042c81c2404507410400c9140e07001e141320481e00e020082c1d64401d00c038601220080c12a4281c44040c05000310306500c01c2c0303401c4000302c03c01e00306481c3c0852207022500203001d407400035015036008a0802061031141c1920303800b05400198101030403800f18080402035006226801d01f41c12000000908201124803641200c3e8001612034115a19900290080c014010071203c1528041c03150001c1d02000c80050b000f4090003110000710b5207060307001e004004d48040c1c4800720001402c00401c1c0044c9001d4914480400035902c0e00130452000d802003403404509803c90010510701c07041c51800d11410010380606100ca40d03480000546901503181103034500300546000003415800803c800b400c01710018031020303101c2c3d507003603201486544400003281c200e223840c98407652407941034003c42c0c07804120058000303034484000c524221582d41c0103051440b1180715110300d400c0104c0000d010b082c100015460207000715441941c1ca14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 938787814 1250 938786564 938786567
    0x1142b0c05030d0f0507080307030b060c010204030b061c03030c140c0a060f020309031204080d050403020114061e0d08040302060a02100e03160b15030f15160f0c030c08030403 77
    0xa001e45070191103200102e80766640702d56940050804030b501c9040c42c028160701e800103164002407001083c1070b02c0b1010100d054840b440208580c0403500c00050301ca41c11850983c8860302e0141015116181d01341a01c1900b0301044070201d446603041c00e00185807914604143c0f0099040e050403081c9030408034064a100c200811281d00c1c1602c590327001c12602560440b54000c90006803804280c55009001c9085001004031400f07806c07900541207241440c0301c0040321000d40b4001c49044005075180e08a0300100050701840f2030f04124102c80d0880307041c4d005103030412149070f072a551510880c440440c2c441401015022100a142c0251a0b590b81d0b2000080181d0796242a40e42101e03240d01d00424601d4001002c0103481c90b08603480055155200039403a0048160f81c050f000c0304040b0b18000400040356401c01c955002d1f44c5001003c2c007901640c0d040c0c00c1580d010010711690500d084504a0440d103944083d89405402e07484c1007846060815060440300c0e011003510050a551000040c0b00505 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 938789064 1250 938787814 938787833
    0x9041b030213081b1212030c18030a030509041503290112030203030712230604150302090c0a020f0f0a020f041a21011d011401142b 58
    0x1e81c0310000c001c40d1943e564840999680c0c880741e01c0c02c0201200107100b4000d207443c0354010016420581140d45800481580f1595944141d61491707074410009005daa07640018400400700000032000f9140440168a010304648220340c0c02c0d85c0308540d2511085a04ca0361000c0003030145030080e40e5142400d0310002440c1007912200c803401c11901c2d0b25000040c0c408568108100b110707070b0603406181517880780030302901c0c0e41c068003030b610805644500c284441c20401c40805408817100083c1414035040201c244003c43d42c45200e0f907003c013100c45800340050b03298824040c1d00100401080c948e0342c4c1004004074104908a50940858014047eaa5686000016410f800c0c203008580c0c220040200100f0001180c3c1c0c0044520b42d0280c0300010030119241080c2c901d0b0446101142c200700010b001c2c90050b0855074000b04e64a0118103006618140240c00d00c0355282c0000d213441444000e50411407401d100440840c145031207182080d6440203da07a4614000a84540382100d002c4a84003034980502c04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 938790314 1250 938789064 938789077
    0x50a1401060b030709060302030601030b030d08010e1503071203021507031a2d01050c15040b130209040b060607020a08100f1118060c070e011401051e09041b0302 71
    0x80d0700349003001c00d00d00c04040889000d464240c807007807480c918020080d030281d0802800305060603a80c98400e280d13a01c0a10a24140703400ca65103052039503041201065010b507020b408409941c42007803d1629603140022284180c5045900b643c260780842e2404a141c030280800c4007074118501c1040c08242501134221892030001c0300080f0103d04521401d000040d44d1404005125589983c0d08001c01410620022555070061414501c1c02d268040c07640d00e000201001c46003440314050402c824002044150354100500c02100e10303072403100381c0018042440280c0068503064a020105040f41d48050486500640c090001000c00e99200c001c0350308c402901904424090030a0391180000c0c140784a40f00c9084070225080c0d0505180a00c400000080d00c910319070007440070002c0c0015100104480320007007403a0030061120750304185000078016044840d0340c0c103104040c851b483c8002418089004500d00c4820031a49910304100090090100f500d0701e142c40d030340c400c8000030700300ba03040d00100311 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 938791564 1250 938790314 938790353
    0xb040e01080706050306010f2006070f020c0a0e0f0a020c0109120305060f0a290301170d0219030305060301140406022203120c0c0f060504090b0634050a 67
    0x80b56695200030342d61440100c0c0c030030740040c0f4142480c58210380914026440c0016200740e64001c03a0a41d0201850810240d4100d40480c000c494003544140d81081484030034802030b42d041d981107180005590b007c603006000c1010751592640041c5800380141d05940110900384000d2004044604040d0b809144170a800b400190a12001070f001e8105480c00501c074100142042000301c3c070b84041c4046a9491b04501c10150400d0030000c1400614003016501030100c5101d46202c010892121a1030506a0b684800035500103031100718542d050504807000c4107800d824046055554540000d00411564081000f441040010702c014010664042c0850790300e45101d004e16100c02214504e120000d512004082c41d4052401c1508588500c01001c0c43c64403410700c041b00d90f5106c074401138201046402000c00124085020003004103a400f8644040d80309454030f900c0e00880c0920601d00c140b0f00419044c0300e5180b55040fa0b0f0481b06d1500c1c03d9038580d0060150342d5220024a000c2c08124880205041c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 938792814 1250 938791564 938791573
    0xc1906050613020304051005090c04090516062d050f0d09020109051203090d1b060e10090e0703110910110106080d0807260c0c2505060706060b040e0108 67
    0x1000d01010b1081300d0003990080010401010554010001303003100410700d0495000d049a0100b81d030300c440c0140901b03940700741e0240031030100c882c014501d035021941c450020040044200d914400603014200c040301d40d00320500980121001040d580b88c07040d04400c1040480004810000c2c042c154001030160340300341d0b00c25401c180d9a50800c000641700c8450151a0b4208126045807441d24402c80d0751064822444050310b0006c3e041d20030041c1c40306601c60400f24201400100484c501010750a00c90541410618031990034400c160200070801048a41819642c028040c549404003045e110528030003812840614a1210020001c1d4684640110150b0070900c0101b50600081440da120009aa44110b569500d105040340d20b0054080c81c10400011450000007240703032003911901c07c03050000e400d5603070302c06500303003600c0d024401864041c2110f414035036030b40003690781c2004d204460040341d00585901c207506100740100150341c010b40030000e00140014180c51084100c504880c0144240d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 938794064 1250 938792814 938792839
    0x905120a051b03092d0607030206220b0414010f1104031509051f0b0405010b09120c0306060111030c06011d01090207020a121e0b060301150f09020c19060506 69
    0x80d5600c0c041c99813500e0b40309204040700140164079000304501e1710841803600c98030140309000708032950710980d07094005030080f40401c000690f0000043d1240c0b81007540706901102640c03111070b204100603200406050580d40f540b5144a0300f500554004824050100030b1440584000c0706540d215102c110b944800c00c04100c401401c4c42c3c440c1c034050030b4014026281c00351602c90443d8010500d46030307031100c80750b13503100d039082584940c814140640b00d41d4686990314035600302000024040f8070400b0529600400c1a171090703407004109a034000d40c081c01e020100f442032841c010708500501c098801103100e11000000e2a10001d00d604100034161041c1c6d11103a41c903144100305078481c941c07010750007035800c100c01c02404860070f400c00a03042c0122036030980c2d03200c200440110600340341401c1d0390b140120001c2c0056490300b8400d9005d0b528224403111201c07850060501c0385144c040c4101007505a02091f000c0e074581e07052210340301440d09149540d10742035061402d900101810b5405034058100c90411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 938795314 1250 938794064 938794117
    0x3070e181b12060f0d05070603050a0b032b030f05040804050a0602031206061b06041b2909030f070605121620010209060f0324090a0905120a05 63
    0x101d46103408031450b0100e0701c1c1e81d054103000420ba9a9424160801002078084000c03920901c910390150000d43d401140c1810560b013080300703803030700d5000262180d0030800152020138000035811100d41d940c800e64070a01e0051040a4000300000341c090000c01e401d0200700400c102c107880040007694021112100c00c1500c50b481240d4074005c03500580600305105e00450240e251030ba010f4440c0c80e0014038685100350707540c0d02d030905117401a41d0813601d0b8820b500501d51401207150140340544202d60002d4500c0da51409403c0c0004c9103148440521b68000521941c1c50302c00340b0003101d00344850812110b101e030f51071500501c1d03640f000142507900a107810200d45040d50100456200d607000b03540d030000c41c040d6840c0024494422500559840d0342c2044035160980f12040a44203800007040ca40b030b124608440b035419510290344040c031f5200103040b80914a96a0f04032401e4000d0003102000070306072010b140c10344c0b4262454071007250517800410600c4109070f0020092076100e15051382a094800521075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 938796564 1250 938795314 938795317
    0x304260f0d05070315142b060b03010b3f030c010b03120712020f06070507110406050120070504110315011106070f050403020406060504210f0803070e181b 68
    0xc1c00c8940c080e040000704250705151034035080c1e02c400146905480e41d250081000d41f4044032802803088014601c0a80a0042c24803c1c0c01109006800a100c2d0480613400910f040b030000c811802440d0007406020700800d8002d0400b60440031602a0310905503c80442d9681c0e0740185114034041d40c2002c2c48400d160a012820700344c2e45203d0010345042540541d07504d400c0f1001e05030503c045101e40581a850b00c41c04004071406003030940c42e05a640e4605088c40d021500160480c01e00490600b4010080c0b6640005101c4490b1080c1d4000d55004040100ca503040460310f0340411360160a0003041c03c080c1002d400110300804642c007c14201491100041d600e0400300030f054003554001c03c00180c1080e01038001d003480d0305c001c0d00d4828a0140c5941c002000c8a41c80e810160010384085801e002e00b245c080d81190307207030f129491010405800f0755526900005a0400244001c0740400842c0e030b910700862441c103c48030014507802d07442c14601e001c41e9444074201c4811003241d0041481441216443c230 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 938797814 1250 938796564 938796581
    0x1509010b04050618040b0a14031506030d0c08040305100501170a020d1b08060103080a030c140405012a050607030c0507020d0210020c03030309010506030606150304260f0d050703 78
    0x78407044c20301c0040c0703015001407580006a59046074603040c069109130b907801104d0000d4041400780490f41c09a100a05181868140b07002d03840d42d10b11410300c080c0d940c3c0011880c010704468540303020201e126192140c00707401140d0004049100f0302c426030070951815002581620030140703800c1c10000f0b500400c1c555641c01030030082c0d0130880c240320729004940801c10220404e4450b000c440000e0350b031208103078603000090388151807005000ca401c2c3c40c5e8560501032600003204c40e00d803070280080c840141c20440c1c0300f9441240e040c0a07403a0591b0109442c4101500310800e200642d8005075003a5041094031000b04450321f4000a180410810045000d00f00391400c054014207882d07510b98456007072000712481d0201d800198491010080201d55041000314801d042c040700200702410004240b628000000e05040c1c0f249541f601c0500440300110183d80c0d02c41d8102d03448001203100d00ea028801c0c0c4920702410740303507030a000034408001c81c00340000f82982c1d401c5401c1001071307a4811004600311140070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 938799064 1250 938797814 938797819
    0x706030203010614071a040c08030a030b0a080c01021038040c05030709050d061803090602060708010515130302060d1e05090a020d17040e0108060a06062a0203061509010b0405 77
    0x1440e0703002d02240146d180c5079001e4031640220900503207840c0800c0c91608030005d80c10001c1d80310f80c1384c080b0a0410202c1d40d0024a070140051220b5603480d00042e403122107003110804441d40d149034010255015104100001c86038009812a2240304403100c01a04152014030340618108123600b000f052055040301d110728503035039691081c142000100004550032400035111141c507001400c49102c0c91690074922035110741ca40c100e0a91910340080d0524900400c81c0741070209913001048070303403500c842042007281013210044d0b640d2260542650010317101d40000e9000b9002081c050f01142c9260f201003e085180846c214524101460740c1d415104100d0b034401c0b168000208400060408541e0b10103550b200300380c4280c46000640128101b42c105520124900800704010005190f05001080d00503443d448248549401d110300600100e261080c03880380900d41002d014090204400d00d60566540141990441e0400c0f1041c10321a07040204501e00c10301801000187d03400004080b20200d4101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 938800314 1250 938799064 938799083
    0x1b060911012712051c050403020a120b06090403110d02061e1905060d150203060a060309030c031b0b091606020a050a060b010c0605091f02040501140d0905070603020301061407 77
    0x7000a0079540c4a030714007044a041c410166096104400c14170050400e04481d56891344031842c500405c403602a080d400003480140e1200b001011075428058640d02180640300d4483d603440e207242c00c0712080c40d14109aa500c6c011440c0305810982d0104005000320710240b5841c141070811546100001015a1410320103021405022100300b40f80d00843ea120a008041c08004d5000f0f0f1542e480c0d08032004202d00d0700c0b6074000308005151902100e460090112171034100310040d85a0340c040c00c54200404058184182c400d000ca8a50504040740000594130410300d280904013040302c17581d205905180304030f4041d07001001003a4280f0000c0ca407400b15270031400034880c100c0b40d0f0702c800c0003c110b0400d9045c10002c40b02c0c1288003240c5540a0140200d0424004080810b40000700c0d0191001e100f81c1c666480d8010801000b841e0f1b0701802c805418a1070004055846640c002c1c1400201031007833004100d40180c400006080360940d01560407581151101d0344a859241c12000300c134400d501005180c55031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 938801564 1250 938800314 938800319
    0xa0323030412050909040503090406060309081209030c010f02040e090d02102c0a0c09050c070809040b04092603190905070e01290a0804031b0609110127 67
    0x5882030259106071541c03c0051030f0601500100d050740c10112001e481c81c1d440000d411714581403a01c10000180000d00d0104401400e41d51030b041c007440b81e401800552405000800c0300b03450203100300d41034048140000c1054264240380e20029402520540844010000003e07446000c085894906941c03070b0350150130710495650002004101703000c82031240c0300080395061007081c0705082040702d080d0304800400201d0030300d1401c1410400c00381c003c400214142018000b5100c0c1e500203440700298440b00c070644802c84500850018040f49920940c001c2c06e0901c44802e100c1c012240076284005031581140e10989031003084810b1001750f0341d40581d9019080c581144031311550003021040d01c15400d4940242e81c0300c601d0402c0080a8100c80b4101000c2d0800708007450130f4a03011801000b00442950805d6000500a841d0038070040000d01400007007501d500306808030206040402d0740c8110104441c0388541440140743c4c24100e00c1902182c014203801e590507000459043d44903020702c07860401d050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 938802814 1250 938801564 938801573
    0x36020a020f0d1d040b013f240303020309061c0207230d05030a0c050c010c02060603010e010e071509030f0f0b39070b01082808030604200c0a03230304 66
    0x40e00308030400c0034000b401c5100c810a050a8100840b52512200c0c02300717103103000d040b170b11a6038141c40c1c021030604646e1207008c000094000c402d98529607401c0b10641d4481640788660140201449008108180f001030f0101c00c1003203200c40e0030000032920f4844c48034094246c3ca038070f50b28030703101c1720f5500131680c1030001a000145e103070410109080c1d24a045410300038410079460030749102040b84009600000104000b60809104112a51002d84020300c14801c801051a8880742c850003241007541c1a02c510b411400e00550b801d8008542c03200c0322150020322410700303040d002122001102c0306070b40a0085480c01907410700c10310302d03101c40400c8111008035080700505240b404407402d20001800348a2007011a05941540d070082c00e410340a41036135000e001605010035103000b440110100229420310100301400280d0b58403010603078002030340200c034502d41340311741065101d0045c40d0f80c0f00142c003060350b031000b00d4844544c903c00d44854600c0f00241d15910004c541c54015400101c009100290204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 938804064 1250 938802814 938802857
    0x501050303031510030f18052808030c07200102010605150a0806031006030c080d0903031403090106030836030a1e140736020a020f0d1d040b01 63
    0x44d54074100058802c1400380c1e400e0a403181c06040121580b8080d054109025061182c442c0300a4598411414900010200751240c40b43d40009084500003000003100060060201c0300015084501c0c1d50b0280703a03525003104100000a0554010350804100044600b01035101000300f084c0d2003040780c10b2000c140c9040782c011340000d2240d5031520a050484007456064030814001e58080c040050b9041d08001a05282c12100038411042001c0800e003000420781c0180c1c400724480310242e4555881d19001c0c080790241441d900040d00e14800040c22110340d5440c003809100100d0b142020780544100001e0f43c40d80310510704001c9815070803004840c0b0028200c5120740c1102c118030401501400c0050301e031540c40c220340c07402410b06070748411028080b10024402c0f81c4124611040b5200700c241d242c407038619000c0001d56051840c1900451849070a6000f40701c44561a003041c41183c2001c42d05040062281d43c0310f0218140074155929032074801d0030507000307555031300340c060711041d1251000c0300806900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 938805314 1250 938804064 938804089
    0x1515030c150905060c010f0e0a020306010e1315050901150b030601050d0e010504060c171003080f12070207060f0c02030a0f080f0f0904060611100c0504080303090d0305010503030315 80
    0x400003008008581c995403d40174264860468000040c0d86c825100d8100454036101007810103a0b012800e07082c010703038001891a040d0b55180d10b0320000e50f05da8101e90050301e404140d0060054214108005d54004903600c03c42c030508428009000b10360244c0c1c2480a041c41c2c0380108810030700c04000042940d40504014400c446c191a0b0000394004e60008560868100352011a80d4680301c0b044403040591000240182c00c508481558030b6080540c8600e581c00003d01c0001c1054002050611102941c401510110655849020410314040d00025120f100c14000e5401103100040540c851a00c0ba006500c00c041e03010f4001c05a0b00e0705511204490001c0f25000c03111480c08115043c0c090289a02510a9844107002036231150200c2c0c0070002034aa042d0801010012034020070f038290100010300f1884500d0310000013480340c0380d008044031103214640000d4001e00c000030070300c02c0c140d900181f10300300001159020405a601c079410140c070b030301c410b40d898280007206894100b26440d020b04490034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 938806564 1250 938805314 938805317
    0x230a050403060908030402040b120c2b050f0601080a172503080417030705220f080304030203010f0e100c0203270a060302031b251515030c15 62
    0xc10740c0d240e41d48010340d0184481110385142c003105010031800d25000740f401d00ca00880755061422004000e81c1d075070b140403085903807240d003e0940104000325401c0741e03d03440309000c0b4107180403030046042060303480b0355200c1c5100d80e510a00c400010a46000308140501e19441004054900b50540000302503030800c16203080400c00148096540c42c2a4030440010244170352500101c07850541022000c00b8000c003c81d01490f1420020801c09592080440302052502c03c441e01a0f001d080c80d100090031619001070f544012041c6011400000000145c411640300304d0090003480c01034414a015900200c00ca0398a592102c0380c2c80c2c81600c296001160700038414411242024240184d1519940500d2140203000311001e03c48000e904004070100d01401c9141070551560a00d0b1102c2c40e2402c0101c03a183c00311510100b800404040b280c84245000710a480c1c4c40c51382402d0604125241040d12a42c2040c110b2614038032000b80320344038800c4412a60041e00c0300c4501882c14014680b030b500094640d60 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 938807814 1250 938806564 938806567
    0x12041104060e07030c170402091e182b12091a0a0e0d050405010c020a03061b0f08060f01080a1d0c0102010e19020f12010509010912230a05 61
    0x244203031a2403045a000300b074041035041c1c0604103800043d08450303482c5403001c10041c0c48040850032854803c040398006a0584458407550f031004034191850503500101c0d038a010005c2c09125081c42c582401c0f40300c4078480029141c0303884e500500c841800c1160300090b100c07000c50300c610000d020300803000804010f800c1c88012401d660580c0d100c0d0f80115401622003403650507203080c840e00c03120a00c2a244100007200c0113000404030104041e200307026900c50641002080000c030002c645500312010300a50b400101401000c003420100d0419007440500c03900000c43d0146210300030b5108144c03083c06520b0140c040d01c194400000111801d2500401079500d003600c6109080110000e0701c6055041340104010f024420f45040009003510421074640c0d02e580d00403480d40e612010400d5040c440346134111005140004800085103513034651194003009940307170108000880d0010b42182c100e580c4140051a40c2c800302c00303400e460030051031901e942010009802c41d400c2c94801c0c0000d28440b099400e00e01d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 938809064 1250 938807814 938807843
    0x4140409170307170a1a0108072007030507080303071e090303120e0609070302040510140d1a1317030702060723040807090b011b060911060f03070f0f051204 69
    0x24200b58241c6514007035035a600e000d60106c09803401c3c3c0c0d60b084902444d21224a04003000020718101c880702003c0346c0300034500540c1803181c108100c0702001319800350075502d603590340f2080203071603400403540390000c80d02c0801c00880365550081d20034600c98407519607650762030540d28101c03000000000b00c80b20052751003c0c460b161000c1082001d210304030f40c0005143c0c1c0c0781503105020544102901d06056882042e01c10312100441950088180d001940d81c1c10360400182001c0b50380c000340c81c41103078558a4000c1801a031f5903407030220004050088411540c520000c3e101f500d0075100c1260f0007001030b009100030071038061240c002c50100c0384038201440300c441d001c074503042d50075445540f1500440e40040720410050340ca9004e06007040d80242003001011401c0c480520902d550700500400c6103613941a00001c0000324039881e902030001808045d284d181c480c0c03110321079510507105000410181c0030b01502c0c80780304c1c072643c015003042c42d61520b0034582c12200c000f011a6015100b196104041c0c03055 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 938810314 1250 938809064 938809097
    0x40611160605090c120c0112091e061a01080103030309140304090b1c03050a0f0909020409020a1d01050415050705010504030201050103021203041a0c03160804140409170307 76
    0x8288640d805020000703100d040040015142040203000980290341c00b0100f0803621302c1c0070864041c0030000b820420035401c8004544802006040802000b100c03440580c0b0440f5500d0391000d51985216060800c0030240f00c0104080304c802480b8468009200c040060000030300c80e0700180c3e0303030030720070103d407950140c0500c12241180c000d41c001e4580d00ea60f644d01c0042c149031202c0d41e84d050300008002d1200802c2c2544006229102ea4400c44084c002100740ba801d40da8842c403200c2c00107040c00e5404644417620390402501a500c01c4403c00300281d203280c40c5815000c245000382c81d8101058581c6440c0c2464184c0b109a44c890f0f200940044c041c0031322044001c50303070a00031584614460342c00002c01e507045104010414845034222000d40e80305201c1800a80c0404a0f101060003040758225180e0717010902c030078034600c0341c100b00c0c91446150400300002c020952029106540313000c02c0c1c80c800e01c1000000e2004550540c1c201500c0c03a00c072780d13194503402e004103002190040d000b490a01e800120045a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 938811564 1250 938810314 938810347
    0x32a130603020d0b1504151205040c0914090601140102010e03030f09070b070f020405042109060e030f030909060d14070e060402090907082203180518040611 69
    0x203002003030b000a000d83c0c0d10042440340f414440d004441c0c448001c0d004a9401009003d6401100340c510780100c01d512159005a00c82103803200c6070b07081880585018905042414110b01c0380c50307865424035014235448940c0111092080803000000c2ca910303840c2c600c031500942da5110f00d0a0540d507803801c1c4008151418401107101e806103030703410a0302d030408003040e500e0b01e11180e1214014607010300210001454903010302c001c80743c0485020803107440342c3c10700f01070068a2901c2ca0b81c0e1480951030440f05190010321103000c44050b501c500240b4900a024152190041c00300c804164004001c058020704d01201c540b0f4110f07c0c0074081403080e40007941e60030118030303000400090302d52003010104104090103581c107900440954041d41031101c4031000c194010300140c151070a014611002442e070b00c03284018241c0300c3c040041e08a000008500340501500aa07410020842c01c480001103154104220340d48011144102c44100f25516515074000600f21034090f585140c104101940e4410008035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 938812814 1250 938811564 938811569
    0x170c0118020f0d150c02070812030c2d0c0c04050a0614012609100c050909040b07211d06040f140703081306020d031407030e0111070507150302032a13 66
    0x4006249032410301c0c0231a4039240b107524110b0851802001007010151541c8140c030381000c3d80c140044ac10342851425005907178105c0b000c0d821850404541d0107003c0c2c40c0060304a400002c10384003000161901e191420a81c1c0590040b0440c1c4060705006000c1355114103110b10240d0411aa0191201c0441428000c8420203840808644e0b0142c0e01401081040d0f01c544c5c4070359003c5060040c0342c11400d20203d03840316401400a08803c2080c00003410340c90042507054080c0b5414000d9180c4405c1800c0c030703240200b0910080a0a503600d2880140f45540700241031030050b5004000c032402c0c80c0700e594400084000d403414611041c0100040000001c80610213000481d0072406220b110360700745000240703055140c9001d101018140500942000c920802868210015260200f1454100c0040038003402e2403420001040800040303042c1070040110b030500a40d45000000072104036641822420390005070340b4241d001800701001000050740e071850421603c01d10601c54106a4042c0154501d03140c943e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 938814064 1250 938812814 938812817
    0x2a0301021e1c1b050a05070c0303110705030a050a11120303011d0627060a17060105010323060d1401020c011b030c09120807170c0118020f0d150c 64
    0x11400888840b055110180c00c0642d8403410400c8600303156a8807024030404020b041400720002c0c282004078410f40485550395040790030303101125603e00c2d00500d41300c0d4400c04101e050044003c041a60301e00420103080f0144c1200040900701c0b03540d11109a00040c080c8400d41c0110b400c8503c40d01d464090004c0c0d4020715860200c41c146a054030b0300c1020301322000340254411920440254100810400340081c5000b040c0f16400340380d599000401c1c80081a5044000c180101180101c101c10000840c1c5051340c1c000c1c4d0b014040422406c61275044c14202107600a090001c0c100000c6032400c000d01c0b03088003603008548542c1a211100026400c81c3e0001346c0c0541c1c42d9456440701c005a00001301300d88110a00381c43c0c100107201c140b1000808030f80450045850295084a402050021090940720369a800200c2d00e4100c0200e14084c408940c803080316003401c1d500300b241c80140030b180c101440d00708a07006010562030503840c604026200c14205011a0b185251090101510580b4824403c490419 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 938815314 1250 938814064 938814067
    0xc0f010b010e0f010f120f29031908090a1205010b010f050324030c1503010801150312201e07050603071e0504051f112a0301021e 57
    0x80c40010010389000603000c0c0600540703884983c00d079030f0224101c00c13401d21500d42000148190268500a050082c810080e09418031100c0d00021020102c0e0540030750f07428607044103c1300000305141e2600f024441290345082c0344890000440c01c3c0000804c40d042006000b50401034491400a080d0050b1030400d8400344c1d03488034142119608606c191100072481e00700207055160060300984202c2d107900e80c11803400c4031282900450785040094001c4403000a0805841d8000f014400304560802d10130300c01990f003440d00c2202c250846403841e50580350089860340c500402c200e4181c9030243c000e44803501d100c0380001c1072040d4850902c11040210310303141c00400b0092002806510302940707a04910b1040380e041080c04065601f02a20300301c01403224035401403640c68900103454070f0156030b2220f60400c4049a1100150300d400c0e8803031074108113f0b1a40071032541080c0c40581e9071642c1e86000a1500401d900f4040b1680c00709042c6441098001c0015107410900520fa21070050140441c01c4020700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 938816564 1250 938815314 938815331
    0xf01051f15020a2004050a1e0501050609010c030c080703021c0306060c1e0b0f10080c0a0311061c1509180222022a0a17030601050415020703050d030e1b04020c0f01 72
    0x4120a42c00c401440b823806021650415001030f800c3c0c030980321401e041c44022610242058000c0b04190b49840c0c110111075110891800c0280d02d41c04a418105000d428803040c1150f110f0207841844141c0301e459985448940342c039aa40d41d5248039600f64203289448001d011400078002c60b0080e0b219450040980944e418400030407100c5d0a841e8200003145d8101c0711070103409444405114084a4100041d200c0c644c5024008c43c0e0f031442504015525000c0ca01501c501990071604042c550760307003140b80b0541ca5503450032000e0446440094280c01804e28055840143c50700c45981c0120b062004002252a2404000d14041b07a1115074541141d4507804405640901c0044000f18040d0403403003d0011550300d55106480b03424400c0078090b8500c1d0100101d191a4411000c6e40e02400031003c80003038220264402940c0c401c0a48001c640601c2058110301030144a4021120980e181500a103010482440b036040c10403001d002554001c1d500f404400000101040780043c9128078000002c0d0425 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 938817814 1250 938816564 938816591
    0x5030f072a03020c060702060f091f03060510050a021f110d06030519020303191403011e0f0b0a050706140c03100806061f020f01051f15020a2004050a 66
    0x104013000144075510911217840961035203012036035581c46040d00c0e695603850640005000c40141c9503052203480c5150900030340540c03d40d001c08103031102200c200c080c803008110304440c00e04c00c03101c100d0f0040e04007504030210121100c00a0b10016050100440d1040a120f1118465040240f200c1c1103251102410414440c0c1400b50301004c10000701d0b0b120f560811a000b00790b491040040d072414800c2404888514148900301100c4c2d038101210348241d69594404513492100c540003107150610b907058000042a071103e005060481e0003101d0103d0800c042c2c50415070321030700034410644405440d0300850107032805940ca041d10800840e40703034640f0303030518085504840e2125001001c0f2a40a0002c0c4004ad607100780c80d0303540803510311f041c00000b54004a000c03824901510700840c040d60038001071010f62404440700424000100c1c003420003096490303208030071201040b4080c10140c1c21040c0e00c038010801030880b00c0d0085e01101445910041d80001290880701c08480b500045a03680c20485000d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 938819064 1250 938817814 938817823
    0x5030309010c090e0c31030605010302030d080f0a1e090b190c050405060715090c0815040b1b190921030801051c0804150e0a0605030f072a0302 63
    0x2d1103075070f102d0404e178030703049a000724075104110400300500044881c8148003504a5416096641c0b410300402a469507403402074050070082c041207200b802081034000340755200d81300e4241300d0aa2040007a10356124070032110020200150140d02d00c0890130b6100b050b251540c06041444c1d44150840071300c6160107184801444a0b405088410a0a14031120100e80d4850b05a5064800071101c00c0d580d18414600317000000d21803c03900311081c0c14605000c1c1400705030351031141192081c0c41a1403881c80c0d289411100d060302140c1c01081d6402400101d9104060060040b050390598061246060f0642c014480e0300e00c103c00f540e40014220700740a00a540c51803000300c1c0550910700200c0e01c0c0c40d0050781c02409041b014002c0c0c50217003a4280d071310b6041e4994096074940a42e0420102680e403038850b500c07c0e40c06022201000c01040c904481c0c0e82c000c2c00e20204980c2100c2042d6580c2e41181c58007040101c600102500090030800912400001c150b03002c40f0b4a118030764140e822581e10b58140c81c0103401c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 938820314 1250 938819064 938819069
    0x130f1508070c150f050910110301030b01090c0915020d0e0d08031306090507170d0807020d03050712021309050f090a150f2f030108100f0207120809060f0c0f031305030309010c09 78
    0x7007003001c9c0300410018036442c8000781500c804007004911540140c004803100c10f0150320400a101880c600c52188580101d104204003034541d6600b038040c0e100c141804039030700300e00d1740c010017040007000007a00c00101081038030030f254810240480c030102103403a014940707021600180080002c1d28150b02c406d40040196022050307503030400700c54a1811060203500c911450b1019414151a800020241803050010382100e407040170b01152246482940c1110b4115680541203100d850240800c1c0c029010350383d55807040c5588401441d00801e25900c0782c0c01401c03081a40c10301140ca401900054110f14000c4d0002075606450120824280e0300610b40d5150000b00c0514100703174100010b01c16010701052a40240d9040038001c00d40000180b82e4400900c10490060292030410900c50160740d40441c2660041c05220216a99500c1d490541880b8441c151142c0401440c10040c1d101d0108040700656800308101c8603a00200c403c42d101d450440d132040b5803c44141c1d55840d1400003e54004002001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 938821564 1250 938820314 938820341
    0x10f0905030a02061f03020d111201020405120307050c011b2103150609062d0807120c0c060f021c02191805060f130f1508070c150f050910 61
    0x11803d45c9201c00b82d0310b80c000c0c00064000c905503044d1405010045007111400d0f64040c04059820b400103040b24000c1d08540202071090050358000c220184000054841241c0c10070040c0039001401c00064078401510095800070301414020b2002007540a10907200c81c406c5a582c4980600c2c0081c00101281c03000b540301c00d2080000c0005101e0590301042600951b04a07052049461141c100c0b005400d0720324401e10340018508441102660707911115250140d601e503142c0180d032070251420f038010344000e05070002c00501c0d007022040125045400030f690009480d54010b280002c4951105c188001d80c1200200030b41e00000e25080d08841c40352410010800d0b440c00d01030341c899803a807020541da094440c00d8030640000c66014034884c800d4040f140008506103e03005c50b1591440d292080d41607034403d0800510019003c0800c007401204120712401e85561800b0740c807182603a42558104d00c00300a41011541c414110700000da0601c5038034028801080180040d000e10013401c000d45094141580c3c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 938822814 1250 938821564 938821591
    0x30705011b1107050f0102120c0c030c060c1c2a020a090b0d080a0905030a1a1014120f010606030b0f031903030506010e06030c120108210903010f0905030a0206 70
    0x4215000411243c00380c98085034840003401440b40104c0c42c1200d0b20180c0480340100003503e41000b00c3c00103055044880581c19070303412055203401c021540c0103a4400501c0c580002a0006100d46c004000300712090190910700070000c110810074200300c3c1012210036241c8030451613002903191200350100208845001404010b07001340110706d06940d2080003d01840021820701c0c000ca009c0d0041da005028041d08076060b03036802d0300340b11300240c42c081c54080d002c07054580030030180c2c1c421a4a2205540105040f040701d00070a40c148200800503a01c01115405425140b45004074280070318001400c89607004202c41c4002d4081200744c500e210b0103240719070f020a006000005a03000810406034040c2400a0980c0d40c5200584036110030581155200d10300004005030f1402e8003014080c000c281c00c145503950303030300c940405a0700d00c034848185c2c0c804145400a490724090400044c16000c60240001c038941102c1001002900c1c04040111001c0d0004142c860580398104841da40c0052040c6000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 938824064 1250 938822814 938822837
    0x3120408070621020c030d15060c0b04020a091e1407090519030c0e0f0906040819090915060809030319090204020909071d010503040203030d0c11030705011b 69
    0x5681e120041d10500091000e80c0e01e00c070b109030840c890001003400410301c055545400c2600301544035405101034810f131603e412000281c104441c0041000d803580c541301c017541c0d800107840e1710307103048802401203074006001c41000c940c2c001540030341e03010500600d01c000d03190034200030b203842541c0c01103800600c140c11070810442c10981c0f00d070189088600a54000c2448820f569080c1d02008981e08054002c0000d200002906440e0310704541c8a8240011080c10a85404403480c1d22100d0070b51303000d80001e000b880303006154082035041285204107030411416080c1d1311049401078907124418422100c4011604111041d0499121a40103d40c000a140b95180504050303814800321003003401c031165a000321404544890781118031440000b0300322051071a005800030324582c0f00341d6001400b400f16102444003940140709070790107154010003641c1407403000c0303800c90010605240e800d420001211010000164140300070b210f0319006800100f0900075660414403c0d9011b00105020092400c0c100d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 938825314 1250 938824064 938824079
    0x2090307060e0112021c090c080109110a08031c050702070f0312080c04120813030609060504020321030a0203100308030a020c07060c1e051e150708070807030c0212030f06031204 78
    0x411441d661b5210024000768a070400f103100d007200f41c00a0345c50703601c1e01642200f40003840e41400b049400403694424581e8841c04a941ca074012908030140b102c02c8100180703926042900807076400440e605c1100c00c0c2c2699a5003010410520741d00503960881d5501200c0d0b070ba40c1d44030314450b60004604c14201d02d0f146c900f04540013500b10441003c0c07d400f40200780000f5134907003407400f1002160010b00c180620036082c10140e00400c41514104d03c80e12032049100140c4030303503001160b1a42002035625003180e031619503080c080d5000a00200034860f85500c040006070402014501030ba05c010302c01030b2115410041e035450041c098001d05c0a0102d002c0d03078140012113041000d08514401490300c22808441d182151401000b282d03801c40d0940c0c140700510090b8070004079105000c1e4004817140503525110300036103165600340c03a0b03580010704c064002a8401d0290700500041c404030301c11100480310780c0800e000d0700d403c1940d100f8048080b0a06110151500f0041a0341d034414000016203880d203407110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 938826564 1250 938825314 938825347
    0x390507031b030306031406070f091d1306020703050d0b22020a090b190801091104031205070602130305010e0f100b060f0a03060812031302090a02090307060e011202 72
    0x48050407000303180809030030107110f500300360300079030740b101c60320140006c003459080c1c5654040399400c2c0010304005011000c030384115000030482c0c03040711046510040312490408001d8005000112407d4680c0c50803002070400d00c01483c1850007503075a10749070401951584e007a24012860300e4802c0c021203000d08141c0200500c850f190a181010041e82c80b254131902f0b4401c0f40c3caaa02094080c60301060682001b03591095862007000729695007610f90783c89041e041d08440507241601c050010a2109000040f05035046030b40c000c6283c248581011290f42e034520599115400412090500c1c58003041000300900513a4404035680010700f4611003100c02e06541c0c0e800c10702d0380307040c002d8940380d00c02042d403190740c115150391010850300d41e0342c0e4128000181c00341400788215945407140f034040402020109003070341d00412100c1c2000c1a9003034260200490004050030001d80582c0c20010b40119907410414500246a16101c1800d002ca4000001d4813030000c404221440900420941079a0040c426 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 938827814 1250 938826564 938826587
    0x909020a230402030403020a120206070f140301060c0c2102041a030a1101091d16020703170304080906030405070f051008040f0f080418060506040b160639050703 71
    0xb2001600c1c0e64036030400320f103450241e030302c0078080090204280a0031a0301041907881021a521854042c02c3c0c07520b0101c564206521800340904070501c0188a410311400c0001041401022844c0c80b56031181640e4050040b820401240e404400d005002142040e0082ca4500000d585004040c082d404d004281c0341d208a850091104858041c1d60105a000325006d0307000c0e015155004481e8440003041150300c00c4190f40d1181070840d440030000919100184080682e0b500c000c4aa4002c8252417071136802e50000740080780c001400703115840c00c40c1c031600c1c0990b01ca81d00520052042c01e207800034414603841181c201d40d002e0b05103d400d402c3d0b0325070820401d9401035444220031340321408030300b402c82e42140c0d9801c000b014048000f400040e00700c010700c040a4000e045910402c1116910010401c0d5845580b186842200b014003040848044004942d8407043c014040030811640c0400003140f4484111643e1045221169821050601c24614200d079a1200e040c039614240d80c40c0c401070190034228 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 938829064 1250 938827814 938827819
    0x501020c0109061b1b0311040506090408040e090c040c020c2409090c040e0c0c0d0905010815030a17070308060612061309050604060504033b01090506040909020a23 72
    0x1c010007445c61100c101d00313140ca5484a10b039540300e10b032404091030140007103417045041402158280c80c04050300e278000c0d5480309040d868a032510345800103181006107c00c2e124091054007100c10b4945000f401040c500e1b81c1d010340b52843c1100f0400240042000d407640d040d949515114001038510401c551082004584498143e5240943c0e80107078442c942108029121400c00d107d030054140303002e014011650b01c25250344481d007030750455040126106042c00900010041402c1d5a038101e218044200050151800350400d80c5540015105100424500c514001a90000d066201560075003029048682d40c1c500800000b40d041080406002c00f03102c5c04005c0c420307080340d103c658401e07030710586c0c05404e5852a150504102009102c101d40c1500420102c90700510003030450905101800c03550102915000c100280c0c0000030f01500c0c074001e0622042c0c2c0000705007a92540003178401010f0100001c43c0c04442c074410310506c1e040c1540000105540c40201400017a101441504441d00a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 938830314 1250 938829064 938829107
    0x50601030809090717060d2103061508040b06040b0d020d08190c02060d0c210903030e06091b0f0d061d03190e0402190809060c040302030a02090703140c040501020c010906 75
    0x1070401440011091040c156881c1c6400c4040042c207404d80c10586c00c552f124a038401009030302020a840c0103404a500501088203140000e0103881c099104000d0b03170401800c4950940d40d982d002c107000726941d81d004c3d90000f03804038607005030071076100c0008840c031498a0701d48041951540817804074028540c0c0e8036101926001d01201603442503400aa030342e048507507800f0000202032003480081c041c40100340e0000f4240f00351004040b03000512a406480b17200014400d1240d5030407050106082c252103c1d5114151002c8407095aa030303806424030307d070301994001402080800d88040d1880c107420740301b603881e00207010124040d1080540040244140e08080c1c0c007010f06500080c000380300b03a02006d6283c03e0030480e800c00b015070020340c151040354950105c0b02c1e15141d000d0440154015844001d41c5507006d8020708006050680c030882e0050303d0340c100891103c0d0050981901954119424142c42c9004201000250b90402046650322400e00f40b8036402d6061150040c45007012980c040c40380307101e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 938831564 1250 938830314 938830339
    0xc0503070b0405030909250f0e040c300c09050604030809150418050c0405030307060914010216151505210f0c0a140d0b040f05060103080909071706 65
    0x40030320440305545c00c01841544d840c0303405030380c5940205100400c00707421071a0030801c4c4c8803180242100c0d0710580b0641ca96445100d460002c101c054000d195455040018401131280c804d9203034804044000100e586020b1282c1a245040e411101542180820032a400404100c42d458410480c5e040c5c907000a100e603a95003011020903209001103502c0c003184080060001100f8200ea00708480c01581d40d00203100710f4850444041550003240903550b4503800410000b000900b8542c0480c080c1e621501c605100d0400b0001124226001172442c04c0840f4604002d200820940d44001503104940100070010048100540b0404ea901401294000c03a01402000350802c2500c07104102040180215201c4172200120342d520f4500f1760104034040c601e400c00c085480c2079440d9440f483c004000c2c044030002c034401c1c2c86260604601910941d10130070103529400200c4c00c2484414040c5009424181d51103014000b4083e08160007884401000200b181d0303405200c400360b81d881e4020b03c1c00c803521000c60b074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 938832814 1250 938831564 938831573
    0x15022109010e0604081b3f040f0501080a14280903020309041116060908130308030f060405040b040209061809010e16080309061315030506100c0503070b04 68
    0x2e64400416040d1040200300010418040000c080c00900c0050014a2503007a284065660310110003030751018170343c1701c15894019540518145507845180c0c801004200203000b802c00d95009401200f58203e1550f018412560840c164580218262b003042000c1500010810320b600800340c0500381400e6217108070303100d5100e00d07a40f031000800c860304104608892440c000c0d55075404400e1060045052811100034011803806a91034901241980701d0340c0e5000340d80344070081c03c600d103044030729803018011400319607034800c2441d01a6116070708055032802e0000b0400454500282400e1155080808000014032a02c08041c2c1140e030503a114601c0e500d5080008040c82420104422101d4840c41040322035441504900040d406100540d2080220710041a41c00c1d00140140e200543c82049056180c1c107006000788582080325007920b12458a8a40100e0203e442011102c00240c5a070107000b887d144c607020f6230305400c0c42410500d00304074550b5100c42d103a0003140000303008112010002414071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 938834064 1250 938832814 938832821
    0x1f0b0d05010f1a12030415020f07080109170f0d0b12030c0705090a0e0d18030b070302070b01090c0c06051e011206050c0901080612010603020a060c1502210901 70
    0x258010000d000000010245200a242d2141038000f5405140070044442c1001c0400c015003070f402a0156103020706041403983c16400002d44001180724000c000c282c54441803004d0070251560340000308401c6501c0c24401c02c203001c1c1d00e08121a8040420003a400d8103110002c441c0c6941a00c81c010a882804a000039849001403080c410707180400070f00b581c1002d801150403404d95030112041000c81c0c550381400c200b140c000041071000e940c40700704880020341c090340032044500500c0a4060040f40c40b07607074130410100c00f85d5844d40030a8010407050300700080c203100b4602400300a0003c20a0064012008028444000e0013070001581d45000c00c1c074081e4003001070403d0300c40001205803e5603643c004400504d81804c01076a41c246080081480302c0d4000c0700322061200160f5a0103000d40310301c020403440c0d1980a03114400d966a803a030010068031072035a1800203002c5502c1d100120000b5062000d13041ea060540d0030805441000304030f00419004100650502501d13464290503540c0038040c6005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 938835314 1250 938834064 938834089
    0x40b01121803020f1209120c030a0605091902090c0d0603021e1008010e0c0d1e1a0d02030307240603050d0f0c03090e1009020f04090e1f0b 61
    0x4050501c4a46032030354030850080311020b40b19600b1540c44141240c0920b0f03c800c0f05010f0701c0d6804008004030345c480d19044281005000400b002d40e440c403001003001900e007001902c021280c1c1e41d150410004022014440034402ca000301c015180400599030000d9a080c00003000400b14507004555000000519070100e005198040d041d80c5215421044085443c4215060f003849221424603414003603100301103560484541c02420301c01c907100c44030307862215007040d489032180315074a24070040d030202588555401603031600c1d4002800410440390803020050a8095400742d00b0781815280143c80000840e0603ea41150054944c040f81500601f510080000c40d03d11190510001005001020801032002202600c440d401044220b009507182d8000c80409070100351031610800c4414603034030031a03500076065008500100e44424520382240c02101c85034440620225040c40340d240c0358801c1490990403100101845c66500604891490248480241c1caa07112070000c8000d4a44d140060070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 938836564 1250 938835314 938835347
    0x7050c0106031e050712080726031312020a03120203042f0f0a030f060c030221060306091c0c03170106050909160c08090a030209190c02010b060405040b01 68
    0x103841119551801034012070b600d01356000d0207400f00015070796201c4100007100552064400c1e0a100c0315844049034043c40d5000d2000342d941110381c085541e0000002981b15404061080441c00624104860050382c03c41e4440c081d980820341031000f0a80040b03c2982800d8182e00c0503a07282d0701c13450f284543d105d02d101035143c803100d00400d031960103c07520380380110a0416161711901031207278001c00107244550300c8060500070b807600110020605a800488501c00c0c83c0c00c015241c520021852003034110b1100181c82080030a005004452406100c42d54020340704200900e400300c0c140206200c08036100110b103062041144103c070400d402201d20501c241c403007905200c91581d4074000500983c0c006000c031440342040350300044c0804c4003111000301d114890780e20071240104c1c82c4d490003c140d2207048800e034000354014001006a0780c2c0c8620b240700e012402c00c03018403107011148801c151079561200f007055905081d560b40b0b0b180c49003015101140c400320b40200c0c0304902c00340140c3d510b491403140d00700e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 938837814 1250 938836564 938836583
    0x203160804030206190e0a121214040b12060d1119030501050109020403030f210e0c030a14101e0504060e070305030a020f070e0a090524100b0901020607050c010603 72
    0x4117005400c400c840031050a03501c0b54001100c1d413004020640030300d4000c0c060b810f91114803060104203071000b11380110b556403c1100400385400322100d07454024ae1f001e6880104009805100e03074003801e0300e16401c2a0140c400041000c22940d0b22807642c40c2c00300d20103001d5600c0e011081e42095030050860011a0024020401961104035480107548140400c2e0040351300d1410130302c4042d2050f1a04031040ca4903c9001060b0100b00704d1030005070003000169103544c402d803003c000c4155402d000200308203209001d0600c07e0b03036001e6201410140f0a11510707030803d01e414468140310080301c00e95072020120b0040064a541e80e031a04000030413190141002c3c0344205071011040101c000002d01e0503014540886aa08042100301550b50b1080e020b40403040d8400f0b0045212100b20740c1000d54014850000c3d2040c0c1c4950292074141d10048038580e00c5600502414030258000c3c510031100071780305800d0028942540840042c0da50031018141c0c5081250005117880c07080800c0d03000001540c1d0141a05 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 938839064 1250 938837814 938837827
    0xd080712020625020606091008010e16050910090b01121d070902040501020a02040b060c06150405100605090d0302010e03072103090c0902160c0e180309010203160804030206 76
    0x250354090455940302280d50111000c090b40080c0c180090940c1d20b0f0b44d0043c0043c0d84d540c424041410380107090030003031003501340740440c003c13800707002e0900c00d0b0485100410102020f4142e47d03840444a44c0b04e1070141d103080c414818103842100780c0700141ea00311180824000c1204d00101c414495401e0040103030b03841c02e0300c40c42c3d40d00c0110765812003607400042201d1280340c44808aa08034410f5101c0c141c09a80407282c91070041c1013030341020400c0c840040c0905e0900040310000790500c40708541c5100d0500c2002480040c504d020f10032107401081410301e0741c520b0742c00c0200103091351142d0401a485001044217030b0040510035001070250014800a99884003424a80707884c86081070b80342c54646034038200000014900c02d204081510303070070114403000245041c44c20340083d400304001130b038400c1403100800041400e816030034004000b466841c1141d40390402c0e400c42440310600000400350010001c945090703a002050f1003400350800c144d12038002162030503190620965100941010010842 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 938840314 1250 938839064 938839067
    0x60103060504081215010807110a140307080307050304051005242412060319020d06110403030c02010305360f0d02070f0e010803120c070c08010501140607050703020d080712 76
    0x16060031704800e80320400141c56a20007600d2002c5007040d0444d0135842080f1034804103c5c80c48051610140032002d0364030f04611601c0b0394280381d000315024030100e800082400308010007040a11110b50307485404004900342100c08105030320300d035200c40454800003401a0255a5411001205812080440700a954140407502800c1e00f24584031642c0e8644000007030340380c0c18003181c5014405240c5400403541c4241c0d07030030800903011040c0260b60b181e58800410096070a030300010405180a41c80d042c2414200c2d100042c1a640001c0c5081c240c070072007911107501e41107040c0480a007400c0e4007100340106041122028603201d440d45d4422001d224202014821640115101d420758030030740300c0d013454281c488600400c02c7c1c00038490043e050384108020010741c06007a07251908107070b200015600c0c161082e1100805505641c1043c1041d941da01c1c010844070b000031015808800d01270740e085003480d09585880c0c4d202c071441c0c880070740039503600381800e41044680401c503081180c0c0245e04000c5015035400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 938841564 1250 938840314 938840341
    0x150f0406030507060e060316050f25231c030b03010218210c0609041b020610080705061b0c090c04050a0608061c020a090e0102130b0405030601030605040812 69
    0x10a80405c0b4800c0071030300c40b42000400c60344519004000081d5003082814116641e03440700002c0503000005020b1903920443c8000039070460081a60f900400e8107403810303c145c04013082001e84018034072016140900c10004504981c143c010980e181c4081c00c0c0b207c600764043c3c40c1e804001c6a00d944001401c0c41404a00a001a8044000e840311060700c11090504103103045644030104082c1d11208003a01e003440c0480041c0302009000e040400d460000b01e100c0c4040f140d00c140c0441c0540c0104080122000311074010000410004005000d00b40c80d203030110b140340c440c0d07483ca51b00a810380d42c80000700d94010000b4590310200600018110700e4521800711168025014151182d0046040010250b12404131503020f500024034102000414000801b498150341c80126041a0512000180c032001881501550b840a100150307540c40c1e221007030071780f800c0d040d0003c121004d03041c402800030341c50001d80b0b45c1c1940d40c081800501600c0700c2c1049807040c02066141540c15403a002045400c0c0003004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 938842814 1250 938841564 938841569
    0x270103060e03040b04090f20121b0909100e07051207032d0e12040503120307230d06180f0603080a0c02010e13050415060608150f0406030507 62
    0x40100812401000402c0d168811885800c2414509102c107002107101a81302102c0c0130100c03840003480c28421001041e44004071020300449080c08a51051401050140d01307038000f503107038100542d01076098403000c3c803402040d4119004040145c0016441708581000c040942180040e1500c07a04d082680100f681c1c1c40404001c9540f03082d4004600c140f406401580d070b0b80f0051440340a05005401c000b0381c9e00002d10b024000e401a01c84101040420003445400762003c0000300d42c641d50340c100f0081c5890700c413410007580b90320807013001009030340c560049044d000b0300080d0569014143c100c8042c240c0a0043c00d00c0c030402c4a02e85400060b0741c034a8090004110380d02d2841c00d0008601c010302100440d80544800740480c9410002e0300f6005102c2c10200700392031300c141820380d480e0760204085024801c0740c4e406010300a58031000d000c01d001c200c3c0119800d0001000381445101d003004801095481d000d03042881303020551802207251b550700c200d8202012000350007046150b80c1e90904079519002d91 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 938844064 1250 938842814 938842823
    0x90c230d05070f08030c030d0906090218010510020f0303060103230c0318010227210a02150a090303031109060304030e011103070206040b0a0504030f0c030618110d02270103 76
    0x40003079130400100680e40600365030b2001d1400c085009500b240540b440f94021a44280d881c3c827143e00503551800d015142a08030101108158188000c0c0501644c0030080c00095500820402c1d0440000100712644814286000304074440e012800250300c103c0301c080c1c00441c1041c9410860f2041811010310702c1410340c111400c481c1d13004062400e080381306465804081d0401d0042c4024400740f200441000d100d000340c07070754030202e4607109011406a000220203107650407007401c50056207021948119080c041c01082450b09083d1100034141d007600784030080916480355808501c1c90764a6007a07443c500030185c242ca03500e250134540140715140d8001b00c01c0c0403170301070840c01c1544c00303002040e80c00442d40a4481c601d800d00b01441c2c041c0c941c0140f100c002c100701d0100000b1002661894284205602c900c0100c0c91850542c5010415200a048031505000c81c5004680c0443c00356103510700780400c11f8a0303030f00107c50b017030012034485114650030340c01d280c080c1c122907005145c030036220a048a015 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 938845314 1250 938844064 938844089
    0x3030507150506010c170d020f090f01170121440f0d0e0109080301060914090601050903010b030313080c040903020303010608070e1819090c230d0507 66
    0x1d2910740c41c100c40c0207451244c00220564507440019865000320030540b06010061070410386d080c0f240303a09176407102c4d101d201c10310720228204085040600d038030841c9500908000b00440125a0009001d01051203284404c039500840002003018803404480880e40041e40380515440c02c01d4184c4001c640300d84d2090032201c0f000c200e16180c0020704c4044140c0c4d00103198191510315080b24a03450b42d002103003810103031503590380c4000c4800424801c100d40c81d07114648032501d03989004070241c001c0d680e5074420851000b0b981140311135030baa41c00500d81e0020003401c0c80d80c2c840700d141000c81e0040184141040e0148800200050301c40e582c1c0614800311003148003120346032080b60f000d00003070351003141004000d43c2c010310060042031b02403481d40341e0001051400002e00b1403400700080b1005544460303e020703030b440801800b2400b00e04000e42014002160002d10403862a035075110b64000d202d20802c0c00e051540c0a810b800209030812030000c41700700034102682c28070319062907519038101c0d00c14160b42d082c2e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 938846564 1250 938845314 938845343
    0x816020907113301060807021015050603090a15060f060c0b04230105070e0a0510080103031404030506010e06030c0913020f04110315100e0604030f0f05060103030507 73
    0x3081c854158440780403806009222003049204000c0d0020b150ba01000710f2920b04040b10f195400d1840da4000d0445d90740d11081c5041040c4040c0c102426051601e90745401c2c002d100c00e01404140408045030340c1a80d1880c2c2d03e540340903c690412550f00c01c01412802c04c9200006d40c4081e541248041e0740c50320142d0700c005a81c440054400c10500e4400409841004000801081102c940001100103510640e030000a210700e0741404c4580c100c402101050503015000031504003501001c0213030200f0345039039054810001c000b13061010144030080410156400525841600c1000d40b401075034068111802543c4a840d8040340705012900c4038000d2141010302401c518009040500070140c031141c1c003500d80310603006c3c4407030740d0f45440b9a140c02584a481c040e01c1090091f008621800a81c21241182450f038000c10034540a209148001c00483c2c1008032616a640343c100d40880c0e902c100c02d41041ca44626110030340e206086c00c0508640a03840002041c19007000040c8a031a10503001d5007914034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 938847814 1250 938846564 938846567
    0x103051513090305040e0412030b0a06080f070e0d0302010603050c19060e010c0c140f0a061d15031003060b032b032901090920070f0816020907 63
    0x146121503264407141c1d402281c000320003903a0103604554000c0c58803c0c0761546aa4070b1509500c0161003c0b600e24180380d1002c002d40b68988120807440784100c401211080c68001c0040402c08082c01e02c01d000310040010030086801441901e1495801070301c40303400000a400c020740200f80512068805005950381c10300385140c11481d4101c0c0307040802821050b10b08100c4d080350915040105039060016503440c01c8003140e1a010780600800442080d0850340f8030040511000003001c6ca90340c1d0090f007a0944c02d101030782e00200e03d0706000700507400b040b4000300014002840510b034010324041c0280b0000031310a416845144040603240150804c0c03001480380803d055407010894010303105020028401c809804202116421210076417902003129006010308003464140048104441c0c0c85d000c5040043c2c0d60405110401090101c508000443e8503003c0c4007544103100d00b07140e000e100c0010703400c41003251211071103c46540080800e40c565038604441744103a207201c5c0080e0f04c1040d03403100141895 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 938848920 1106 938847814 938847841
    0x8100f0b0702010e2b02010c060e0319111002031e0108030c01110721050f04090605040e01090c0b13051305160206090309090705121005010305 63
    0x101d020340300250201c20081c2c000d034002c0c41e8041910040004243e01e5811901c141550980e05404610048800c0d01c105400209030901d001220710110400101419481e140c441c0780f2000b00461030000c0d41c2e07488054065030740740da0002c400c6141c1c1c03060036000b46401c90f040b503428030700c0e981e00800e0448824500340c03c110180e03480031030f803602055824001c01c1600001c0ba51421728040448c0c80b0341d00e0503100b5614034903818a42100350f03a1400e1054040f900c0303000041c1c0d1030607252525840088054203051107464032079410000700e45107014040c0309294109a10007102020186001d00c02280f9402c01c2d4484034155a0207100090b082c3c03214150b40c008503405640000b194a0030241d542085450314801404550000003008071030140002203449d034900490350101e50342d1741c56004554905c180003061003c0b641207001c4c08280030b109607204086e20800d8a091005940b80b60121146 = true := by decide +kernel

theorem cover : BRFrame.Cov 938669064 938848920 := by
  have h0 := BRFrame.cov_init 938669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 938669064 ≤ n) (h2 : n < 938848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
