-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2079
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:31.857062+00:00
-- url     : https://prove2.me/submissions/1ee9dd7c-36dc-4c78-adb0-aaa8933fec73

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 373741007 ≤ n < 373920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 373742257 1250 373741007 373741031
    0x40501080f01050108070c080415170609010303080703090507151724040b010309140c030706140307030c05040f030b06011d0f041a030a120813110123030a 68
    0x11000040c440c0240580700c6005220580e000548540c116980d0324201500340c80030b04e4400c0840c0f0507504810601c0c8840d0201c459170740e5102d9000c840980030400880303040c0d02c502050049050302800001c010031550300015a4252103580312207102c0740100201c65820f0354444001c240581014160400a169150174000c8900c0d485291608184000038001d6072900c1520b03080368030200c06000078810b0740c80324009603003a0700c21341211a200c0e40000404040565400a0b179a80700c4404c20314500900803004000351550150918551041c601c2c0c0c121031a60b910035170210010144024910f00744441480003261800780440b07024007941c8202c203104102e041c80d80001d0500a004170514001c0302c0404014202e948451070741400c40744050b6808107003000300c045112440e61058003165050300c1041843d20a01003201070344200744006455071044c07a1110006014050500d150281600c0031070400074010354441c86119490810503188852004e804c0030024180e5801607584000c0e4503202c285900007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 373743507 1250 373742257 373742267
    0x10806010207080703030f050903100e06010b0901050418020c06090c190501021506030c0d030c02090a02120115030912080402122d0c030106080706120203130b04060e01050c040501 79
    0x12200340010203699140c00d903460358940c440e0100804120300a008005014010004d1b200c200c14001c0a8441c00d00d00b00f42d84400815a60340a04420b100b107a00020b00c0d100a80c040752100801a510b00d0716140c240814034040c510581c0c104040c0c1582001001c0c0440300a000c61030040f502140a4002d103c03c0350100a5005582c0d000004810000c1e2401c111b940e030006011b880b06009a10410855600c1c0d0000a00382411101d8040c0c0007840c3d24080000c2552040507801c200b4070071074070106a51518816a03080f4021a80780c00541040c110042c040348140d824030400c0e4000e50315010640078401e03950782c070901842c5141da41c0440d00314000e1208615141946d0741d0310b6010780000707060712134808050041c1000a04e00c2c3d04100000d104c24440c0d81007090043e0007103118050000d1198594510b40700e5620354943c0b04a00000b09410100c5681031554000c07a07002d4500c101c0d180e000f203200303a21484000c40e8068000c6940e030360ba5002e10880100d0a0055511542c080450703030351280d00d810700243c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 373744757 1250 373743507 373743511
    0xa0f0b07020304231504060f030e031e0c030906070b0105121b150904020a18080d0203030f070e0901030b0711010203040b070c08130f140d0f03030509030d05040605060108 75
    0x400d5402c140018040d500b44102400011002c4662901d0541003810202e1010707084202084880b860003e4085016a007040032074014441541d0100b161401080038513403039000b10700e10f079018252035456040d07082c0411809400b103c00b09005607407a01e44135000181321544450400c80d20302c61404010019450700e001300701501040b0f14042c203181d81502c40c00d02c0310150b02c5074000b07102e407501200d8580c03d17200d01006c0d01c4000e41c0140c02190f41c0c1d00703c1c0b04064a03c0000403070450250040b602c0204410741c02150383c04d0541040c0e0025415503c07418942c1daa110303001411a810415007410100b1a0350324201b80e42e000318004c189000c154101200c00410365200c448090380540e004105010000e4032480c100d40e40050a441d0929007812180307044003072441040c0341c0c1810513040003c0412007003403100940c0c084510f401903c21400c1a460306001c00c0c0d00300003c025090000d1000c1d6680400e020350042680119001e084c1c1e0b00c5e001d43c40009404640c019202500d996565404101055802c02c0070340d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 373746007 1250 373744757 373744771
    0x509120c0a03030609330801110d0c0c050304091d030d0608190804050907020a0206031510090e1306060918020405010b090607111804050d020714100c02120a0f0b 71
    0x8002852015010410b101b10f922481d034842c2c0d82040c4c1d03031075005032020360000640140700081c0310074448078085420a070054920024181c0c5410002000075020340031100200d42d104e0040c500f0a40b5002c00000101100d000e461428544109624480e001c01e00040402000400b40001c100381840501d41c60891001c0011200c1074009859401007a10503081c0c070110387c411a1482416921928102d06040300c286009400030400b0061040c00440c4032100000000265005503e0750344000c0c0403201e220306440340c16a690b080b840030450395140104802c03416801514085805942c50070031030101d8994140c5180010074035029203046203041d01685005200c1080b645052a01031000030f42288108600103110710b0750441c01d08508d441e0001a0740b052141c1e0a4100a02d06d0141825034039841700b00c5841e0014050700401040460420401d5009100d024090342c5103441803131400c0c0ca40c0384a210007a41e1080c110b031584801c401041001d00c8650b84203410f1340c3d0b400403051520914843d00504a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 373747257 1250 373746007 373746011
    0x30a020105010f1d0a24080c0f01120e0c12030903060604020702091906080d050309251202030f030c0c030f07050d020402071511031602060c0d0509120c0a03030609 72
    0x30065001c074039001c00c200f81c0e80e043c0d6100682c2c5035045d10320000e01c042c0e11a94070290f041c84146034000a004041000c68055100343c40c000c9014000304400c06000c810318030301080140000c0641c000060788003019503250308003140c69800c0d00400003410410007140866003503100043d0f0340707190308040c41220b0700080c0036641942882c5543d40010820341c402405001d000001295120300080f0329000580100900e00640c0c0c115165050000e000d54412610305503a4846e64280d50041d07140905000c3d007003442001c04280d95400c00300038403080d800c018001c2e40c5c184500100300c07a02e0f0400380300a0041106481c01011802e0b4030f5000d1608040b0303c1000445190080ea10401c41c81d1188049050007a904440050b81c600091411540d07802c0a0b0640b0034030f9618000d00b1031700c00b01c64000298010020003075a92204d21480e0700490359401c00302c136403000a000a01c906844102d483e000960009820b605841130300d141031121000641042801c3c500507802a40d413403041c1905803040c5009440c1d10002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 373748507 1250 373747257 373747259
    0xd0f0206040203070317040f12060506010e0a030303020a0314130c36020f03070c0311070f120c05150301030c0905160f1b0b04020f01030c080a090203150405030a020105010f 76
    0x940351041440007621561b00002580302036401202100c003d031460921182c811510346940c940c0140021104846052a100c040303500d40d8000c2201070303040d40c1c1c003e000b151040e0a5541c220044d4101c01448001d2640703580d0310103001c092580d404d9118032081b0140d4914408c007814110102002035000100004030f038000804800001010300c2e9040c24030003a101001e604507041300000303219190344110030305d00210a204021303520071150501c0c00d000741d940b170010082c10304806440b1215485078400341841c1c25420000f11401002c030072420340c002d58800c419156500007094921a5a500d9110346400000042c002c01520300c40441c068440018104003500e400ca910b010000c004c00d003440d040c04000d0000000c094861299178045d05900c008032400030015150412039144241c80c00c034851519110401540e501c01c0c89510b80300341c15030f5240744040e203e20a94000403c040d10040c0c0c0c15003e21203c0c8549203036032100b030900a5104034000c541d20214600004d084401c180c0200201100800e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 373749757 1250 373748507 373748509
    0x1208070215090a090510030804030b060a080d0e1306030503030903070b07050702010e0d2102010c0207090504020f09090c030d08090c030606150c070e07030e071d190b030a050d0f02060402 82
    0x3c103000544004010010355a100d0f0b00003404c40b400030358402410300400190100420203c001c00900600b01550102603d5488109007038a4020b41e2900100090283c4404001850401d640f216000c030900780024180e41c80c0d4443d1415640101c030001003c0d840000c98008224420312843c0e400307001e1346822401d03c0810741c0020a90303240c0322030305171040094401980034086220300104080d40980650314011a4048020340a042c9410542c005030281c01d200041c940980d0003070b14030690b40180b909100d040190104044000c014105801c50700c00c480c0e207102183c80070844601240300c6c07078641010516003d80c01078940b51100001c107001c0c1d04500d05200b00e40d03e8004089407480c8222410a0320b580c0c1c40b4400c140741140e96806400d034201d9000900054036095840758040805003c1903d00c000c1e21840f420107001c8607c0101d03804202d200d03000076400079070710004400040d91110302140b03010521002034542a66020256200d070892606d6402268112904a452164600262080d85882d0b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 373751007 1250 373749757 373749769
    0x2030f0601050309100c09260705091b0a0806090a1418030d06030c0905160206010510050c030a080a15030203060c030601110312150411190306120807021509 69
    0x1500d100c1c1803003004004a490a5018003e85001100085003000a42000315000300465228462800040884146030900d2a500010280386185100052a9103442d150910a0420004041c606925149a10f10407414044c00c000c00c84011140e48024050402c0030030094846d4010303000f403940303500c1c0c1501e2503041d200580c912548140d20340b800326107004003da0030380d045100316400707501d0091400c1000b10400c846034180800341c40c1480010002d80d41d83c2d5000000308010080c2940c09a842400100424505280c41d440151a189071403400c060450b0340c0f031b9186811895001c404200d0200410040c0003042c41007684040c82d921003546031500d141c000c01e40300d01c00900b49071000e0b08000000b81e01039004100c404079040c1c40c0b000300c0340d43c1e00500c00000c12080055640a08142031810031810714a400c0c06040c041f808842c0e0090720f0101c2c07040c107140108207a00c2c40c1c18281501c6000c00a1070031007441000041c0750141c41002e40d280818810003100c90010f403941c4555081c14002c50350581c03551 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 373752257 1250 373751007 373751011
    0x15151b120909061d0421032309060f0601050403080409020703031104060509060c07080a0308040605150a06031e0606020703051507080412030204030204020a0c050c010804172a0705100302030f 84
    0x141c006189140c03101c1c20b20461248084880040080300000d000c2c10f140d1380348c1e0003001ca00a402d440b0709180c0c03110030900f0344401401d07648405030303a00c05c201086401c04081d51040e00038005040c003e1074035a40b0303580c01c5c0c03007500a5404407021541c040303003040505405000e032559613410718901a25160410070090058001e60741702d54000e1034042000300240030300708003a0001c0c3c603900c0b046815105842c03030000d08035001100d0886415040402003083c0b108040c4232803501180c0101611496400c3c83d40840082100c1544d540c404440306221081b500314340c0c42000302038480f81e07003d0211282582001c1e1b2070280402c0d040004400390304d08208000340e104840c00c1c1c120781d01c0305441c0f0140342e000307008070080d0065803c0a1b60107480081c03c80d20250b00f26120b000d403a8441e0040d0358070f140340c1c04015109024100c0d40500b95482003030392a00c10300041c100030240d400f02404005e01c02480040d082c0002d26910703149041551142105200a01c3c00c9800080d00e4589407909600c1c61910360702d4000c200f500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 373753507 1250 373752257 373752299
    0x60f0d142d01180c0905040e0601061d060328060b03090f03040b030402040e030d1103040c050303070512090a0b040807080606060307020325020409121215151b12090906 74
    0x29401c042c13101c003807180d88880014200204144101c0c0b400c6189152034101c02e2180402140e48501c0e9440b240b040c2400701840c81100624140c25583ca200d00c2d20b403050000507010001000980f0002c0048210748a0381000e044003020340381d22403908000c1035203040100c004000072503000f4041044003819090460b640654180c42c041107484648030348601e90300a030284412041c3c00c01501403e07410441001c1c5101d28000d00701040d42c59500c0c0113050700d902c00c841c00980b0941060107140d18040c4840000c00c0900740180410514a42e58140302965800a07003040c109078022044c00c0004800401c45039401040446203145107041080d03001e5640c6c4588034000c9000c45120100c8108034606001000b0003076000f51007441600718915214956041e009020000700c0d009034130071010405c191081c071490a0002c2c0401500608100942c190b04206c1c02c43c040801c0ba46400000070030707000c0c0b510110954401d02e40c09940003001034000d05000c86c16045214100c2c50460304028000b030307842d02c00701c842c40c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 373754757 1250 373753507 373753511
    0x3070308041502183d120203040302031803030405060a03050a0605010306050a1e0b0a180f06090909080405061210050d0b0a021e040f06020601090b060f0d142d0118 72
    0x2d018145030f001001466001001004034401880005d081000c0c8000311100710394501181d4400024150124007055601a0050b13006110036000034201d00e1740c1c000902002002c80c0d08041c5d81e040062030b03e034032103101000001c0d201e8003030105180590082a010302401d003000e008041c00c000114030401c070180b00381e11011620b81c1c03806d044005480303500d001400005230b82959905891302c0180011054035042c0b81c084100d000009085206500c1102c265000c41e07403092443c510b8410b900c0d010f4a901c07082a103100c41d0030400000c850f642d49005014140c01c806940042c2d142c440280e081102c00e540c06a40100300c1c0305e90100c001140c03d4101640321412400c0103071203400e60600e9070038052035940803942c103150000d80030412990704048001260940e40c02c03562b9a13030302c034091407050340d40800c0c2494201e8030a028280c85824513201800c5128103c20780080c2c1c9030a0041404208501500c4140600500700103000d200a01d5159080c01d142840760045100d524003085c60910a0340c090002014507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 373756007 1250 373754757 373754779
    0x40209060607032a030216210c0e2802030603030f0a032c1e070512030f0403080d0515090105040506030a05060a2a09090203180307030804150218 64
    0x5004000c026982c030030700103c8420910341320544840380075050b9402d0303000d88124807541050003591800141a91050740d501d1000324040307800d03580042d03004002100c0518190502007200110800c002d840742401c0b2074100c0b80c00e44000a802111062018100070082c010130401c030103918000304403007906841d101c03d65912030480404800070203980301081121a90900c0300070b038145a0700c6415000100400c240d540c02c2038032250301460344412015083c11500f082c075040040d4030b401a0307815040341c0003809a81c5420713030008000c915030b8099042203c4644002c502218040c000e13104081e03025a0f00c01c0400c000340e0052000a6100c1d03014458580b0554a5800003211900c05000c40da0150368460210b070400e040c5220024007801030342c11000408400c00300b00ca40100051424003501d28440d1f1628810b243c10008071101a42c00203203d13030008a60804010000b59042006240e86406030303466103890304040c0b40c001d0304800c0144000d41c00c9401803120301614280540d14902c10041110710010702 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 373757257 1250 373756007 373756013
    0x1141f0e0c030402040f0e010c090603060e040b0709080607110d08010501081f050d03020307020405060303031303080705070c090c0306052b061d0a030e0303031618030803070210060509040209060607 87
    0x3c6c0c200f142c80304099a0420210150040054200384520708880e11a504842d031100022402c40d42180701c0c00120414981c007117404283d13207050841e0041da592030442812920307114210b00d0800190745c214000b4002c40340c0d440340d0000c00c0c414501031410ba89045030b02e40d450040001c000500181c80a0300c0424880c420500c0c003402610400000c010240c2041e000704190300300a910b0f604000c500342d00407400d01000920500d030102c01c40e4819540c1c440f80d40c0c4600410349084803d940000d1051060100810244010814045600c002400c865002140c606440c450007000d0341d4107a0b01280c01143e2003054050303003281c00d2480300b0410050442d0151040d140c1d0605002030032110b03400c91102c64401034a162000c00114a003c040d60098842072080044042803690300d11084a00302100d04520144903c8103114032450401010098030004800351242c4901044d50720070f8501001690204002c076607900514001c9078000e0500b200c0c030009502d41900070514440c80240388038440e03100000c400b420 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 373758507 1250 373757257 373757261
    0x706020d0b19080f07080a12090f0909051c09060e240a020613080702040c1e0807090519030206090114040605070b0f1e06040e01141f0e0c03040204 65
    0x441c4001000341c0603034940308604100b44029402801664051442c010030320082c0061100112081e140080c001d001c01a00c40b02e1400c02c1d0003594034200a00aa000100c641840341c403240981254000001d120700c452a00a1901040c1201e858911500410308201c154211800f4000c9415604007100d00d9001000007642800c0c00260005851840d00c3e040072080c3c40c904050300b6a20038a400311841600c4031302da00481100d0746003000305100ca0800c610001400c00c4d810045620445003420440301903155002485403170b0141d00c800c000745800e000c0040d01036222040c44010501602d0701c0c81850411710000a486006020103070003003000080d191007a9109691000716804800491616951244802800345d401030320309403010625035010a0200c1c0301c86400394012035100c1c02070911704e5100400301800810040c25154001c0d80c0300540c001c450420301030510b800710041d26001c6207252400380c00c644080c20104400f1203c07030700c2c001400022032184c13401c0d802020f0390f810b498a9688034400140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 373759757 1250 373758507 373758521
    0xf0301060305071b051e2508250504020d0603080a23040b0409020a0203130602061509150108150a060903050706111504111c17090a090b0301140103081e030c0706020d 73
    0x441440295402c000e87d1140c904010142c0e1480003c1d901c40c0c00085070b03032801d407428134000d40e040024140c0c820001c1d45415402001c40c01b401c00d0b0041200b80d03880d15a0b400c0c1d81c01c5003010307001080b40b803111566a8481907a840c8440b4210400140c201420308907508581e006078011480c0d0300f07070b00084504005001300f090f200c0e243c201d0150b5075100781d210040251203600a4403101d150310500e1521416600d0141d1000d13214002c5203010614101c551001121030360005440c80040501c6400054469280c004070358000e4002502e40c8060300b4078500d4103d18041007035110108000c0000300d804524140441d00d2000c08401d4412154642c40d0b03030800050700c80c0030a06640c2e211001071307283c1542160002083c4003c0e405485000780001c00c40107140a07030f03c94220702d1a800500400305002d201c1e03099016400034007018000046016182003c1c91413000b0a810603241503001084025025944078080c0340c2d1a4226600c850540c2489059000940a0000c0050105401150b5940841c000b544040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 373761007 1250 373759757 373759783
    0x5091b09150403050d0f020106051810030c12020906120304030b070509060307030f0f060302090604020d0e1b130e0a020d05010e070e060f0909030d09080f0301060305071b051e 77
    0x940c1d41c1da0fa8035065540b540220f80401c0070400c00d080020401d8010b200360411035101070000ca0304082140c40c0d04040314801414480380790010034000c40401c0caa0451040030700b10302005000c2620090042007010fa00042c400e0340b14507c5004c02001c40200403060300d048a50084040752561181a800c0d44c1c14042c824145030042004020000c20643c036030400003a0500c81030080140614001011041d02c0c10f07030101035088004800410150306140d8024070581c0741c0028002089507882103114200701c00c00b140c0200214020700f10104501c1c01c1000c000b0040081c4504000c0a613066661036258203102d6006482460508a0007040c4a02034100c038104c41d50103c155a5500d840314a030501129041d1b41d1580107005000900c003c90508484444c000d0030303400011814036450078401c03406000c50003411104100144140d9520004c03000245010702426100402c4624003c00c0c010512609840360501100742c10150102207003010545011182e41200c00d9980b4000f58510a0b14105000c0b1100c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 373762257 1250 373761007 373761049
    0xa150917030a0b040e06070906140706090c06021204080c101b0c06020c01050a051e04050904050d03050a06050904030305060a0f030812010603060509070507020a05041409060105091b09 81
    0x1103602e00c02c50b4016a25801c080710108112038005100c680d440000301c69800118103120401e216041c007d500e0440c26680608511f8035000742030382c9000a54410050441d00d0054201040c801c5c20340601501c81c0301c50b140b08526040916011605650344c500f0310166004014103911400c200c0d00c0307200704007048400114016842c500900d025004c007403091251000500410858070b010758400c9044a110f0749440d81c940e401d110005103c15a2003001d035002d440244810400018142c0700c0449403886a802072000d0803010a1701c0c00041c0c10340e1070041141c80c002e40703041414000c650304d025006402c1501882c0c00203940c0e6400000c80d100c2d0100742c11940c401d01e1001c00000800403c0c8008007180300040141c5142640d980307800307030192540c5008050740084200002185144258041c21401c0e0004040100080d030707410100c1c04450080c04900003040d41442081420001049010b0040500399069040c1c3d01d0084183d80c000417500302441002180000e0740900e5643d40e6a01403800d038040010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 373763507 1250 373762257 373762261
    0xf0504170102091804120f0c021c02030a2609060a081302030f010c0e030309010f081e18010b100503130f05030301150906020d02100c021f020a110a15091703 69
    0x50030741c000101710f504841d181310406e07252500703c6c801d46140f140120151070340312407c0007990070800c1e510b94070068000c0c005000444100903a07401c2050210a034080c484d0b00c0c5480c16401a8040c094020038607580580c1c02c00c0203549a162644c1e011a11148400d2802003036070f8444045015415a00c0840130398035104503494800414019800300c100c104550326007068010009041c0340c0c0701e0091b01001030114011403500000d0500850300d25900140c40315000c103c4001103d51a000140d05940e0b25a900a07817281203500030344248140103020f001100c2c0401c0481c14500020070900c402800e00075480f05100b40c8608102d40e110180100700c0c0d010080d00c4c0c8a68540c0c0c10fa5410707901c0805c0c0100041c01151000444600104040424800c1d6601400c1c4940c0c11b1041c01d000b51000003402030451180701c000825001003080070720306010000304003590792507201c20000d25101d4004070f481001c0d000759813080c0006502c0c03880460314803c2407401103503060715824002c2c42400d00310301c0100c9000300041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 373764757 1250 373763507 373763539
    0x3080613090c0510030618050c0c010218010f1701170f03192c0609011e11010e0106180e070f0f0305012003190e03040e01090c0f050417010209 63
    0xb42406444080d1114800700948a80407000e803101c1c1d01c5920310900880404c1e40e80c0c40016041a94011100700502c0d04e84845d0101003422617020b00510b000440b15075507020215030380029034002810180c50000c949640380000c85030350705d4045c403903500b8540ca105564950750341d0a111519038244818142c1e40c42d44201d02184445401d081ca504001409000b00d1018070600c049000a19503103400140c0c24000408043c0010b551010000314180000c0044201c100e412200c2c14406480c02503507660000c4094460550a44201c80380c43c4245904200c1c0500c1070701d948511450f0100604640420403034510360b6040c0c20308186410000d61100500b10210301c411140000c4400c40744240020404003100fa00e80072004020501600e204802c10804140c0d100e03d1000020b9078024214000140c11005200c3d90386160311544c0031314807801c000401009a00fa180c41003c109814500b0241c6200c0d400d0040207026214602408102c03510b203101030010103009505443c00804054000c0e010424941307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 373766007 1250 373764757 373764773
    0x7090c03050912070312091703090c010305090316030804140316351b010509010e0c030a02061b030d09030c111806060f0712030b1002070303020a0308061309 69
    0x2140d0745024440c1d440f96414484414049569aa4040c0d659101c40074001000c1e40152010038810313242904040160400c24400310015805509a8401482284038090015040e00c0000740705552075001400200c81030b000000c0f01032151a0303d4600300015503a5854240012401a81103980700d03c0003054a10131040c0c402c0c00300080b680190400130b4000310070000b440d0700c02141000340b0403200f030401d22481c00c08583ca02401800494180c00d40d40c400005a0741821500f0489440d0100c3e074650300420041d0740248100092020281c000c3c140e0601c04e600411514403500c50181c4500c0c03001c2802c05640d50b028800d4400b0b203d00c11400744018041428001d040010b0302400f0355400420340c01e80882c1d031500d11030010400c4030543c8080740d290b98800030044107410a0351214030380d09040010800180c18420700250245071500d0002e903c503c41024031444001ca8034001c0c095500003901071000c20380000e1004202945841d00c2080c60b6918000300d003a000508001c50f1080c0c0c18041600308100241c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 373767257 1250 373766007 373766011
    0x8180d06090f0b1308090f040e2d06060f01180e070207031718120a0503070c0f0f06050d020d091a01061116030609020321040305011103040210030e07090c0305 70
    0x1144940707055244c2d04c0c00100c580c054481c004100c01e00c200304452450a00148a882d2510000e1000442c4400c2c00e002e030b420410040c0d06403103c000d001e111028980440310511a001241c0e100504c3d4600d02400070414404030466414140b00a0b41e80410100000c803c9040103042c1220b00040c09041a04029594a10342d02040318080068044c4140d0100d001c0c043c0d5000958006044041c0b04d211004d00c40130449a90001c255030051000c46c0700400e6080008005d841e200381045105a450582e512211001305c2e080303d42244004c5e9001c01a03aa07110050b608200e0321600d0042c0d0716484614a00c0003800002c0c4020071910011407000941c485070713403009040303440b59158152411030411045446101a000050051b000f4403000e2000c5200c13a48400071151024086070a9429081140e403000403840706141841c2c50b0000d424000c200082c0682403c80078640030b040c1c01d50500317500055040c0d2030300c4100320400d07546081400b0310740c00c100111001404901010001e0103084d030310043c090082 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 373768507 1250 373767257 373767263
    0x18020c0a080403110906031c27050423040308060f12010c0f11031204170c0307030f030c090b030a0603120302130b041a0d0b19150c08180d06090f 64
    0xc0c0300d01c0340c1c0d01341c14541400c83c4904001400341400c01c031f0410190809640a40b000350030081d44020700384031048554683c000464941904061041c0b03400104804c0e40c01300000c40c1011000c0000c1d200782d0340b03060106135800c20345c1810f2038680b55803031101040c080c921007403006030b0000c0800e0306882c1b080c3c0107500001d0b9483d13031035440c0800740c0c02d4800280c408002c205d000c19020752041103002d58080e252441a60041e1180c400d01e44d10403a610300c00c003000c0d00b00c2880341d461500700051887c1050340184c2d0a128542d40c504003406010521403000c0c0485101e8800c605290000000150010905600242c0510350214011201d0625644028002d4000e840b100d0703000d0009100100d074524940043c0ca0032070342640040d0007100a1001d045070250407104034442e0b5551140e030403809940d90008901010808c0301070800d1100c0c50050340781605510700e4291814050703828614804180f80d18205c580d07000381290200b05603440e21011611011505601514940c584401c1c4001c01c587c2c04012214a40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 373769757 1250 373768507 373768523
    0x1603050d0f0504080a03020906130b04051002070e070c050313090b03010b03010b1003020c071701020a0305010902030717070905090412020c060a02030304030813020d030f0f14030118020c0a080403 86
    0x911010780e00448400b5140a00603410a200d0009583c1c40390300102403d0b50040d051030f0a0845000b41c01c0c80c0d20b0100d80200002040c082424003803400d000c2c0f80900c03002442d00c01080c5007441c02c8001c2c940c00e9001340108040003003840041c070510a0410848080a000a1110b8110355851550740014841d003801c2d28869400d1520204c010306e014000c58841e2080100222404419a00d0940095000100c2e0b04c00500501d0000210f160301103011000c03602103c0005aa00e00308402c0c001e04658058009801483c07041c02440500c41d80861040100044101da0f052291503581043e5070403211684520390044941040200300100c1624500c0012459001c481c0740303460001c2003180b1809079046110044c1d10038800240070920940c0e03080e41201d42000c804d00941e08075000b04c2c0d85044152030560114500545886804e9800340449500007a5440c1c9529400014240700420340300c10310030404224011080406402c440e40e040701d8412800c40112442c0c245a468560321682261005071501c3c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 373771007 1250 373769757 373769771
    0xb0c0706030f0606051b0c0d081201060c120c1502210f0403050d051b07051c020613060b040b1903060f0212180a05030408010b030f0f030417031603050d 67
    0x4501d000d40f00990f0b22680303070030f820040d1040c50111941c03107640e11b040180c4611a03030004503455004103205030b24060b1207202d66039000000341440c00c08040c0c0c0a1400c00c40b07040348e0316006c19a8040c0c5d0a0a190341480c080103035002c02c2c1000f400429051040c8119181300090f969841c2155500010111003120112503c2d039851100d0040c1340c06c1d088030b0240201e20300b08004c0e0009580c0b5400300c0c0d800b907844140d4050140c01c0700394103085038010702d4045603a50301c6024030240f8615100d00101c0803040c1440103240c2d914141030813200d1310444020003040141c6562241c4d109690300e03048081e2102c8040d0241c40a610000981541d5940ca448241d500519011082c9100c0703240e8022984d601442000103c056298007a000f14400a24044010340b0300918000c02d00045080c4020310091440701c001003140d20b515400c040c2046104442d90f54142e1204c000240f80c00004000d44080721455400d0b104004a10a412801c40c822346000b84220a8540074540030950004080c0c18501c9400f44104401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 373772257 1250 373771007 373771031
    0x405250509091e0712021e031e0405030f09180c1c02041409040f0204050c040906090912080702120a080f06040e0c10030609020403080c0c0603070e010f03060b0c070603 74
    0x1c3d00c2d414a0741e00c22502000924442c01468591040703100150014a003610942021184001300b403400340700d4a10004c02c1c0100c074075544019240700c215005054009003810b0360351956a100b400c8110040003c04112021039a881c11001e644c103c00ca0b803004000e615080c005481194442c0c0c1440d0300d111401003100d043c405041c400c1e2010b4840c28401170300e18880f0081000340000e0020700407a80c0c0b00f1070f1000b00005071994090a4018001c00450a4035141011150010b031040c680203420143c1c501036120020070aa103407072010141c1242410079071520740e400d040f8203142c0076108024460300b000031041986648130500b14400c904c8908205240e0f169402000309850150503d014180c0c01204101c03010301c0c04900300c1031285160700300003038142d0307030b41a140080c1d070020782c82a02c4142000c0380c000c0d800b032010302c0149130220048038514910310b07010f07202400340c102200e8030398104041c010742014218040d6010201501001c0041d9443d0442040003640d520800e00540300024140f900d03010320307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 373773507 1250 373772257 373772281
    0x6090d09170a080711030a0f02040f0c051e2703060f0106080f0a0f06060e1306030c030809130f0e0c12031b03070f03050304110906010c02040525050909 67
    0x21001e019014102189241d200c83c402500460410384030313108540d1a0b5040c550381005a2140148a004813090790710f00c0f401017008a9000c5228001c0042c144104c13818195489400ca81550030020311008842c1d1030b441e500000343c001c408140f0400c40f0f11f5207418401c0225010091080b0504400715401d903a5410071959a100c402e10820010a401001241441c1c01c00c220041c0c4c018038040001501c003800768800c40a40d0b03000d61001c008a10780300c1c01c80550b428503038811401c21550890510a00e440c603902ca25000c1891f1001800f840c501041c0c2d04286c1e51403062029904c10800b206204a001000700c1c000201008403050050740b2456102c1c40c0e10341040c1154008044429000e581000080840a8100c140001c4000d1980c0004c115070380000e2610766030740240c24000d82e510b540340d00c0c080c0740802040c211487ca6511420140b400c00c10144e0b400504217600b6541540c001c1201d84560000b081840c42801556140c011101c40c050741c117a0340310014000d4401c040300d007042c49485050300340769 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 373774757 1250 373773507 373773539
    0x110f250615150e0612250507030e060306030a020d0c18051509060913030e060415020d050c071512050405010203091216080702030708070b18030c09220506090d09 71
    0xc3c005109000c0101307040382d4400700503444482456813500003000911511034840c8548034040101c1d07c0441c2610070b140c1d201000d9580000140e031618a54204000081e0f0341d40440c4200a21484510346604200071003055013000038112905d00344070101810404101810088504d1a2803410485801d000e070315145913000e0151401030441c0c078560710f6003070a07040c1c611500d00c0b050301441400c800b02e400c0d0f911004011b100800203000c07000c1c0700c0555070f0402420005200e6408003041024060050b4030b1001203101e90450341501c001c20032540c13003110300b920098000480000e1191415041100303202c03041d0020751041d4a0341065884400203041120020301600300030308081100712000c080001e00c00401080d140e0300087c200e40c640740e03a0301d000610b0106a5000a0705003800404c4c004643c0c0204100d8004612084018000fa0401403003c9560303040001c008441c2d0b081c540007860501c8034191138010782140c124054031154031b407180e449a038400c03c048070240050180c3d100040d9107840580b81c42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 373776007 1250 373774757 373774759
    0x108090c0906120312040f110105120708060406080d020114070315050f03160305071e0602060f07031e15080601030218101203080901110f250615150e 66
    0x510790785480e024405038480b0550601a41d2004002d0f120a81e01240c039581d00c02e80c412889079565511500c0c01030000310308103a085061100500051205540d403002c06544140300d4905081196506000600501442d0b40a8100c40c0680c07060107000035030640040a00c1204010b92010a8480041c21003c440c20018009201c00b55160144130501d8194a54030382180010300303ca982014204d03001103d51b48590085807542d015840c00c0142d00d031a854101a81c1d240c40c803c0401c01d51400350042c0d01c45800070315503144600142d0000d03070310600a61180700140e01c4c0300342400d50b500b440d100d010020114a8051a21000b51900000c0c00540024501b410380c0d9001d4075074036402d4205941d4401c2120081c01142401c0360000700440d1485404d45003480c030502036510764809043c00c170811403c460340602a0a402074040040288030700025048466040c00d4520210080141c1c005403001c11144904c0103021783c0c14802d0803980d1030348040f14041641c408080240c02062014402c2d900780c1020011a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 373777257 1250 373776007 373776019
    0x501050408150a0209121606050307050306010f0c05060c0c071a040b0318010207080712020a02030601180f060609210c05060c0109020d06050703140c070b0421020c0108090c 76
    0x145015034042c0801070300403196260150a200da08030020303002e182261101c1640d984114440c152a0380170828110040170305080507461401c5c1514000c1207484000c0150703042c00a94140086130b684554082c20740070343c000082d41d40600b040c0c0030101c016804984060214407031085d01081d0700458080d85107120340c020740340c00d14143ca000052202508000d010110f11041404403400c408400c0c0010200c2d5480b1301c0001c0d9036880b403850030690000c261100e16003194000c2d5001001614001030040c15200c9414144001e1001011408040e0030980d20782c141d0075080501c00107102d60032072440000e0b070303c10403030003a00c25020341c0c0c80440d01c44480c0300c007410a0b070a0a6081149040c03100c01003100c640c174100085203061841c1c01268082d4043c1204660055841c407c000100358180300b10060038000c070304210044e0601101c108407034010800050281241040403e00300a80041440400c4044507107200518050900182d21810049400e81c0400e5030100020801c000214600c900f03280000c1030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 373778507 1250 373777257 373777273
    0xa090b0f03040b061306080606040609050f0c030a02071e020306010b0a1b030e0405041a0a0b0d14030c070b0d0507050f0a120b03011e0e03030408030a2003010b070506010501050408 79
    0x80c00003031031000b034002d603004881c840c3c17058001c04c01d500903080034021350401800740b070070f080701408211502e5074001040149400140a00c120303000358500d0300700c0c60303082400e5100c7c1ca0f001c190703000034032611a0007014040c0b220102d00b0803034203108410040c0c41c0203c040d9215a07a072158009d84601ca4404a5000642119294044d51000f2207401401c1d500900d08805d218610501090480303c080c0c0d02510401140c2161219418166040c55404007808000340520003038980860f4800c0f08400009000f10400d009030400e201c0c080060b074020703d036210111400c0c00d07076850292003036511031407840701c401f0b00f8140040c41d202d001b28120340c4161020302446290080d000070442e00e480d2401018403540761180d17011682c07135400740554102081e0052004001d01b01060340d50702114241071405404e5041442004041910441625806407080c1d00105c1d20b030040360380c800d0454000c2c00c050b021941010001064442d2140c01420038544a0310484207181d8a42c4c0041d641c0f4040d13841120442e80c02680c3c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 373779757 1250 373778507 373778513
    0x10203160f11100e031006050607020108060d022d0102010902090f06010309050102032e0f06050f09040518010f0501051f02070e160807170f06030a0b040302030a090b0f0304 76
    0x390800340a014502d070300500392035200010584000c2c144100d0002d541c0b5980207010780390a0003854082c000316201007050502d00f4012450b01d003d020f4019040c00010400213005840d014503495030a075005000039042e0300d60741680c845080d00808403d03801215441c040d45503500500c500500740740c008240d40c0d0303294cc0d114280d40002c030307000780610b040540307480d00034000840034000342d401490514000d03502140c6a2000200d00040c000c20740c003007282e0000007004414281c00c5a1401e0311400d1608596030040050303c0c054603c54080516081403800741000011403007110442c102081c0c000003400710804015144065071028080e09a005070404042007014001507000003840b1118011707a6100d0303951b5454440951411911080340107126081d5038416580711140d203034803098a04104414903500900060021001402c01044040036000310300a9602013011011040c1c0c4840b400700107190601d00207441e80c11029400012491500f004642c940d010b5040c0e0320b99542c20382c0000d0a554441e2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 373781007 1250 373779757 373779773
    0x1c1205040c14011e02010c26011a070b0709140603040506010611010f090f060e070614181309020405010611060a0f0b0901170c0901060e0906060d02041409010501020316 74
    0x700b151410711a4050380d0b89030302040281045900710300ca03000040d4450400c01d011300b01c02081400d5600140c0c44c01542100c4001404580341902e07800455440700612000c80303048207220301140038040801d03100401403000c0d0b100701c1d1042541c603030300740200d121341440040c031034103000c1a00c0080087e0400740060181d148030301c004400d00c890340700010030042c800c0f0f0001400ca03110010182c2d08807009510b050b09000355400b0b0624040c201000504240d0301d420002001940230300c00700764050900081590b41000d0740814a0101340e002001c20014100300c4000000a001d040e2301280500e05100000952600400300720b424888224040d040590b05d01c5103441c0180700d00402001c00703035035078030185566494008540740640820407a141c00341030ba00803180c0c075100300481c4651290301b0501c0103201040d8000c0701003440f400c00b80e50038003860700c600b40040e000d806006120700700c1520101d000036294000d40340421072401d0950b40c2ca8145c0c3d81300d00049071207110741c58030b43d11070001c510548000144030f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 373782257 1250 373781007 373781039
    0x11040303080f07141b010b0906011407020112050106050306190b09061c02030906091023190509010c03060e0103081c0906050a0603061a0307090b0103060302031c1205040c 75
    0xa440d00c8001e091382c080e070394032990300203210754a000703064011580c00700d007000d02c50701c20814070489000c1024907200000a0294100940c0f400c0e00e14400300f064030841e401545101d4864001c424140078660b103440d0028550b40046139007502c41c3d80144149220303421108a1035040c0c0d60b54949003464401b800052180d1540118812101c01c00390120905940c0210b2002d18010840710000e400b050408501540c03800d503442c08a0442c6a01d0a080c25010b105ca2003031300c0714000513010700030a40d6583c00071150038002e045414915600c0c284000c101c44040103510610391804692001c01c5001d49030403c0f04240502400001c04180c0c04010a104007203201340441e404802d0b5600200303001400d69540340645805a0718a00340329100c040c00d008010340790244600700311191100035a0420b9140c00641c1d10303101c82c412038402d20341d14a4000c4482e44290040406903401408903040071400c0c07190f10500d07108402c40030000070701d0361050354002012401000e00550300065065001420901c50407007442074 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 373783507 1250 373782257 373782271
    0x9160b0d0c0e0a08071d0f04060b030f0a0305220506090d020d060f09022b0b0601140f043008090103022a010609090b011a0903030c010b030111040303080f 68
    0x10940010850b0390380f1032154003800d5401e014144d030b07a02d00b40c101500c0807a1205e10310f0304d06209204016021a244c64038a84c002d4002c1004a0b507020400003180c1000015142c8106500410390341800307154200300104820319070071f8014840d108040300e106c40c440d0340354050300b80c1c0000304012551462030800410303820140020b00c0036290307054a694100840d6105020b0101060f21500c4000552618013503243c041c011507407280f426458600070000400b04070b00c1008040c1208000480c10301d900c200c6003420440c0003c0d0806654040990070900d15400c46d06c02d0307409502d803408441802601a8010190000c06841010044545a80c0c0d0a4142d009003540f103040507400d04c042c0f04091324001100382a80050b50640c00c10010305201c032829200075030000995541410382c11b10004005001003411034003511740300403429600002c606d0b17852040c000c05584c513100124150a40c0070041d88400d6581100710020015188146c0c8000340380d00481c44064080348030000010301404010740c5042e07100c25 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 373784757 1250 373783507 373783517
    0x10c0332042306090d0f030504080307270602031306021f0905030f0304110f0603060604091503020303120a06050a180c12020a050a0201060e0112021201020c0d0809160b0d0c 76
    0x40e08103689807502004075500700e84c541c403c45580d6290743d00403004085000d420310382884503180684440308144009800c2e8000c0288218500c0500030303c40c2c510710030b8846116504081141e41d010025a40d400020703003041b940300c0c0060000340b107900001d00015006240c170380e51010f10710460441001411458800d0319039000c10011140401ca00d000154462031080c0d00c80d41002d80b98805000198600b80704060007280100705102441c0d990009450441d0300b0500d0200394000b104000d080e0401d0315030700094040c880807601c120841d0403415000d1288040090800450355900100300f0781e83e50324400c030030200120400002c590f40301500800b03010080d60030140480d0911030802001c9034040010310700040c0010900050f219428080c60000340440710f91041154109059201c1d0021050b4000f403080c0e42d81d00c00920010400c1d010f131481c401d4143c043e1040604892000303824040b0483c2c2084243c00303582007056010400030214010303100340002c2581029000c0d105c00c0c008000741888007003481 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 373786007 1250 373784757 373784813
    0xe01060f12110c06100e010506090a0e0703290d081602030d1e180509100b0309100617100b0303040305120d0b1e011b05010c033204 58
    0x10710328000e48204400e0441019564640d41a84070b041141c00740100203404629a0208141000c141e103d50540c0d80840301513640d4480c14001407001d40766a400f80b103008080f01f04000314540c15901562078103911260394518110100d01c610a241060a403103540000381940c0980801c031168003a092031f0641030030000751903100e80c00003481c0c02010450301000804c0da2070103224490741982d008000380e415040a00550002c000b0b4041b807041103004150290014000007080700c0c0c90308016200801136042da0070358a0402c42900e0fa1101000d15103104c02605003440042c02108802c494450f02c101c01020f404004901c05003d0040c0041c0d00210b030341444180408000300707109005000b92185d54507240b40c1d0780c2010002800956110a5255110305022415003811082c021091100079809181c41084128032240d0103081c2d00a0030310282c0039610304a5007a104076095440714030b4007481000100c20390218040d0f110303e500d4040441314282244d01011400107040d1103480f0b43c0c080300440a00040d6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 373787257 1250 373786007 373786037
    0xf030821090a030207080c0603010308070c12060e01060b03010e1302010e13020301080d0f050a121d10110c0309060c011805070f0504063c060c0b0109060e01060f 71
    0x240d00203864801040d0030840200042540400c10f0f00002c110311800b03010301c0380200780010801e010503c0060045039002900a0800c01c513007016401400305920340340510040e0781406401803280740070005803580303007040100d0b4081850007034904841d410083c40c2460350b905003007002d1042c0e0301601241881302d500d100090541c0c5070983c880035020300c0540142c81c0d40c54182141d00e40001b54003407500b4040c6d0388480d24140d56008080700c00720030765030401c54001404004d949000300311541404003103810300005040c526501003000c1901d0705030100141701c2003070505244038042c0701300d00844556500030800111705080c100003070550340240c40700005440c0c1110808201d580c00c0e05c84105e0f01074101803010322114050030904009010b060354200600d03414400d450940580107240070004c51003085082503c100454020704d1803540100303039401103d41c0d81d007000d0440600c031241111000e03616800465580700b103200c1d8604079522001003101503407034103005650101c240b000403410005500d900c0505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 373788507 1250 373787257 373787317
    0x50f13030309050c10030f0501050d032a080d0c110c0a050411130f0f06020f28020a0f091d070506030402241809091f02040e18010e06010f0308 63
    0x8031707501d02d4402191021542030310108441050b00703c14856042c0740e04100110798004890040203191492039940c0002c940c160080d9910311a000412050001482d03165459080d0000c2c0030351000758445105242ca40441301c0d489102c051241a0401c1003248100000c0c6040c0e0080c940c60310f91305400c5480c20110080350341d0000602c0d0410941c4100d20b1b0000c0140d03c040301034000090035113101400000107405041525003200b800780805006000c088200117600c41c0050307240d050780c01001030150a90f00c50645500c501e440c8503c0001c40d250a600284000f8029500780e090081240a031684509000401c113080d00003410a0340c224040da03030704000000c81c026502c101602051030b0780b5219180c200b03401d548050450405401000c2480034440d045000007002d40c003074100c0d6811441c3e4031102000a1000380160340c4007e045895070400d001e80000780040842c1c903601004000c0c082d0b51801140c0c29600c0ca001e100e005c0322503052001c1000402d910b200540040c880d01c041410000100800c8405 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 373789757 1250 373788507 373788529
    0x91e0c130b010e060a17100f05090c0706050613090605060a1406190306030c09020c010c050f1e2a070e010308030c1608040e0601080a0e0a030507020a05030a0510050f13030309050c 79
    0x2516450207c04d0180ca071b80500e1003c02010101c40da0041450034003840c1da85805244d000800040c1c071203000c18910748d038400440d0781945840f0010406041c00d4106a00a8041514264014054510003040c02009442e1100c0c001401605080c0340100d03400c42041c000b0100c15042c410555034200c0840005c02030b480500044c0104900580c0354814000c40d2404c440c2101c1d405c3e414001d0070808000c00e1162242503600040303049040d03182c07a0840ba105002c184c8190845c04c0710115203105103081d0034040618500302e00314800c0446440701e44400015000c1070081c08040c002c4403041c00007900b0300e45040f0003004404030725503000c01694110390799802c0c241c006805c80d000e40044001080340f20359119603032541c4501448401c0c0301c58507903034034001d444458518000c2d0421a0001c0e8007070940d03c5104d06d00000f404040c0450300034146a0030025160300510300c40a1503d428000821194000c466119000e40300c44118610072503040e980580080c141c00b030048441d030050b041031148555a610300c0711 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 373791007 1250 373789757 373789771
    0xa0807030f1b1a0c01110c01022502010903261c05070201090305030a09140a0c0509130c060e0d12080907081903030203091e0c130b010e060a17 63
    0x50303807000140340941e010305500000031500b0850060070030101ca802404411a10326014900b56202e440040d0240508082003c2640d5210700240d50300340e054056000b003d0300d1041540003042e5080044c0c0150500304110b002034001905201c0600c00314100e0904032030b011184200050445070b8454103200641c10070398090403e0707981007003007034624030190040036407240c01e0344020040d00c00166030190442c000508030b030b20895a5071003003c0410a00c9405030b2004075041048494a000c1440c1c0780703120701d0b00d034042c1c00d004a100401141d40540c00d12260180c03a540460b90054003820300504840c1d4041781800780d6480300310411200c011030f0311240c200480303402d190f4440b48180703407040d5054589552907100340001d074400d1a00703012680d2105600c10040e50f05280142c1e49444450b111442e00800d07558000022101307942640002000089a070b105560070341c0c90600c426454042035080700c161524490100c0c1004264444502d0308000a118007841c0f4100802101450762110010550440c0c40d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 373792257 1250 373791007 373791023
    0x908060a050f0114031e0a080c010f0b1e04090809100207050102120708120603030f03010b07020a052e180e0a270807030201020d09061b1d0904020a080703 68
    0x4000c1c0c0c00010980d4501608149180a419206040200b950340c1b009116020040f441344ea901c1b14202c0e428400c4a5400e50403948650711903050200041c02480440c1542c0c5000c2d14056211245040101c1600c1e4580320040343c1c0307070080e44900309000c00707403254090880d800030003000345e586603039031340f03d01020302030803940c01003c50381e040c00006441c0c1081e1900480810600384a5000000c0f00c1508540c0140c442c4402c5110035212500401e00c1e60240000035550b415003c400821124904000307000d4a82c0200c413000000c80c1d80724188050242001c20f182e58404400b41c900f0040c0190308045c2c0301c00d400518021a50140503100303044e188050f40c11205100d503075076003841000342c040d008401460b13543c0c4040c45500340b515000b8600400c0000c800419400020901d1802e04d8002e5041d00d43c00369901809201c401c00030f103081c0700240444a80004114400400c40890611030103090b581c49107154540da000c02068801c00120400050041742d215206041c04910b03880240400c100643c070403181 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 373793507 1250 373792257 373792261
    0x40e0109020318060c040302041107020d0b0a20040b03151002010c02010e0c09060d03030f0f02031602010606080a09060e0703030f1709030316030b120318010c02090c0a0908060a05 79
    0x43ca0b2494240c140710703900194042000c0c0075100c10540c0032582160f40c1220005540301244540c11340d44d020b90140a988480d84041c1d8400780051000114400e00030380c0810001c4c0d2040c0d40762111800b98015151441d190184420300c48051600700840e0800714542c40d4010990340080050301135031150035003d005035164441c2080094090142d0440c0c0300707500c0060100c41960401207940100e000705090311074548a403902041c58065801301ca01202500001d1104020384051074001e54802c0d25544040c203440704014102d41d1041c81000c040d5100e03030f40c0315552031701c03484220270107800c8501c810390f485a50b07a07031000180c0404125400041d4401e88645c4080b0040c204090102023004100500071408081084a121804030403282d01081580c454a450320020900310000e00e064000f80f40c00c407880102c403441c209400000707042a05c00c408020841100c9107001150742101c0c03000700a40020519004c2459560a14050601c100c064070381380003000c0c0d813041c8040c0340c00000e4820056080e03407601 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 373794757 1250 373793507 373793521
    0x3050901180606091d0c0625030c0c08030315090702160e01210c0501031805010c08270a110f09070804050c0409080d0905160801060806071b08030606040e01090203 72
    0x40303074032170a003101d94802d6680705030304125200c4452440092055400040f101070300d5039103d00c0c900030807480c0310003600d412009140c040c1c284445504181e9404448020004103d1400402c807841003078a460703000c0b041c0840c9810312010740c10203012a025800340c051805103040101420700004c104040140c08954503141c105101c50702409a5400c3c0032890700c2d480170105080e0300c080c01c101d03002807030300080e48203141034010550142560001c1055080c0600503c10300d6110088601421054030780c9001d041130b807014102103415216a450054120309114400b09242c442101d01e0b90304040d1005103401c0350140001d0703810307100300e864102240c1c4440c207000502c00704120700102c8000980d02040040810740741d031182c2d4015000d048902c181c895000804000052107a04052446507001d02252512070000d58060b24841c00fa64000740302d42400a0900c038858044210a40c41c18601c094514600d03840d520103903880200503175048601080700040703011860006a00911515000689900b0721030307 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 373796007 1250 373794757 373794761
    0x807021e060f0106090308070305030403090306060b03040b060102010c0f050903010e01050108030d110a050d1d0102030a0b0f1c022e0504060e03060f01141c05071a190305090118060609 81
    0x1307000b07070040004070303031052000035100b00448090940500706240c0366525860110f13149a1503820051070302d13050a40c0081e07030448010140d40200d104840c100d84569a1900490884403604d903e1000940912148003002d8024401030400d020007400100d00d854540e400e29003501c80c203030321800850780300040b0403045034910311038450600c801e01e400c2882c010703c0b1200207216000300911540300076503904009051000b0480400324980d1481c0c0255282c0c079182054500506011483c1c50090b404041e04407418580030980d040e41e030055141588a0b5a01d075000d121000c1c501d954036008050503115100e01e101c440003880c4221550b6075481ca41d644d41414030082c1035442240c0420700a42c48101032010384500c0c0105c80b815106000c0c0d806a00750b075880d00140501101004910361200c00014580c14400b002c10358034140c03a403052001041c0b070081d80c83d01207140b0072050b241498103045a180200c06229400841e0000040d60001c1140b032211942207941220000007291003e41d99134041140e10114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 373797257 1250 373796007 373796009
    0xa120203072004090f0803071d090f04080705070b07021810030303020c0a060510050907020703120e0d05150406050c0903070b1e070c03110904120807021e060f01 71
    0x610240d400d02103180d444541c10502c0c048101c500211030400e011003078a460344521840c03504400014440c45030340c2080010f50b401646c08900080186490030750300031911601051000003c0e12640e07195a80746045001000d0103081203460020030807601c00895402c005c0b40000d00042480103a49100358410401598040c28403501d2501c042010800190442070b4520304403505401c000d40d480c803903541c41c0d5052403540353300104690700c0c4c00f040c8003801300e458918105849058030006560780f40c440c010b07a0f5803c45448018900407414200c43c414074810360041c002d205010b00241c000300130316607500d810841d01500072448418010100001d010141c0100d0b038000d508017201511300000e20022949820007801003844002c07000910008039180000810362000c1d16a59041d1102518903200f49040002e1105640411941002541525007807900340d0180754000c20030084849105001e540c030110040c951070a50082d080400344040642082c5448240940060b11a5140902c3e10b104402c81c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 373798507 1250 373797257 373797293
    0x40e070e040f050402030c130204090c0503100605040f061103040b0307050d1a01020a080f09040204060f11010513060903020f1006032105120c070507060302030405062a090409060e0a 80
    0x600f814080980ca020452405041c0700341c0e48004035512081520b030207486035070700c1680800c1c80d100818a8181e0701c040510b009080c04001d81d410035030b0381c8800f10303840d00890042c2c4190304503011040000c14021b0200e030005581390f0301513030b0802d503588200400c0390700304480e01c0001c90340c0040c4050358907086100d50042d040194003802c01090702000005d40d44c0c17050410040c0f03a65000141840b143c00350009903921104020411340d42d480e10f50000421034445114080049480c1d884203040c001010b0165902c52400c4510901c28404c5c0d984a00d4003a00005005600354003528a040e540e407402841181c1903a52003800105103e459132600e06c286071070f203050300c0d200f0300040560044004d0344242240c0034001e02e980700e0140f42e11100c007190190300c0b0384c6900034407a00c60010001486a0147c010b54400d07402001941d020342d5a45541d803240014040da040d110b00030754251001c0c5030a010021780300c2d020300600300040d61441699104100d5041980030070044c1d1001c40103408010600e11100c40d2045 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 373799757 1250 373798507 373798511
    0x207080d0b0405011406071115070c08030301050609060f071a15030613080901021507020d0e1009030311070b030405010b121203010e0411130606180602030f0f040e070e040f 76
    0x80750030400300c2c5205412209506c9100002061030902c07104130220a15500020014004690b61400c07500c8a0340c0413074001c4441d040b403850001410580031041d03904844015008610b02141482040120360011865118860060003004041428420740e4466007110b02c414001502380b401c00d07001ca000020008034403070741c007510801c054040031005081003650f0021141d40c417010710000503030401410700c90190542044204201e15a07034005545941d124094039950390b0f2200c14824012000109207100c008240300320810030000c0e100e4442c0c4064100c036001601d815945a5008540075132050750255526915141d1001c0c0910b40344203051095130400c002001c00c40d40b0200d0b850b01600052044c00c01d450f4541e0000b0341401540c1c00702c0b00f02040c2c01071210b000c80500d54205d600a209034043c181c00141203400940b00c0b0128800c089055826507002541403080d0070740e420740154850207900704401c000f4000020a0301e803101c542406054223440b0784022041d107070288000c541c442001403031014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 373801007 1250 373799757 373799759
    0x418050912130306020d110304030f0f0c020306061203040f0902070c080115120609061e0507050906120a3905033102090a1401092a120207080d0b040501 67
    0x18455050b003104881c0d015101503101d07125401010000d00c138540040b2851a800003c001c101a8030076840c1032010348a8460a004980440e01103c884076217010094240e440003011039900d2078810400072812121008507850551503001032450040d80394070a00321183c01081010400c4103605500300a01040402000901d103211004d42c112400303840b456a1002c6c0c00c200c60f40911100d80c0080c0e410303c1d007080e42801800f5000280440301d000c808099580c091415000c120843d01c6842114003001e00140880d040441c507403116142c0404c007402407151141d0302e0081c101e4001d000c0d041d20f003410100c4078242480c0c0310040385000f11101204086001c003d81001000185c1480020548682000310000d5122140e00305c10300c14410300b40c00020354488503080401220745c0454005074403200400040700b001340d030b03640c0114054801020000e0803002c014103008040c491900301c2204844991300c2e1280120008091520480c1d1007540252100d10b0001403041d190a000e00600008140c1641c00f0030182d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 373802257 1250 373801007 373801027
    0x20c120313031e050a0c05091510051303050a06050103030801080c0102030703050d0b09041101091d060405130c090203071b0c150509030102040e01030b0601021c080c0418050912 78
    0x26034840c00b00814040640c00d01d0051440e04168124800e5884400c84e940350165080c042806010340c07103140e209180304000901850707040000040c001c4000341c00c81c4035400002a042d22940c10030310010b942d0103034600000004c96800c110f501c820318000d090004081d41141801001360340143c200108541c002c1400d912241d90001c211000c035501803914a407140040400c10010f0411414116070041e0300f80107210070b004045606a014642c00d0302d803030007480d940b000d110045100c075501d0074002044a0703000034403504194005a0b40850580510342c03c0a910313940f24071107440e0f40d8002d40c0c0555404001c021000d90410410604080e042a039980c1d00461680e03051000001170184200c0c240c04140c1800005028030141c400e0000d00900030b64885440d00c503c40d01c2c0c02001d210030b5968400180115103d5400443c1149060303002c1140c68140200902060307030f00341805041044420010000058185001400041c02990b05000401d00b420190380d95490804040b016040c400b004209010903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 373803507 1250 373802257 373802287
    0x32001090b0403150b09040309051f140c1203100e1e041202011e0b100503010e0a02160605071701171b0418050a0312021e07020409060c020c1203 64
    0x112540900901d46009007040480007806401c2c1040381c006c5041d00500c02090f40045000d0161a020303104c10740000901050740c03144175002c00713211010034030b03602803404203c81c210020240010308030101c035982c0c04c200151580c40c0d401102d50410350889c0320720501658089500041e000004524602045204060b1890704601e0140009007200d10741819505418002c1d00404200440c140c03078130000d48003d022110251410b141c80501c50704290501c0440c11740100306a070f041c2d55204d044a94690741348025100254420b500105076a1240c1d1041c80000f400c0c0d02801c2d1040311940e590041d4080d0310890501026410380140c1a50091002c006202070400181d00303011204003000302c82d00042e44030101c1c0090003003490b0078a1107036488075a02c0c240107000480c501e05922941d03c1100d005c06403542d1030201d004000c2c000c641140740e00403990100c2c42243c013520340f40340024000110403940d035440000b22460017010f900940c004000300400b51610595816211954502840c074002440d599444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 373804757 1250 373803507 373803509
    0x30f0e15190c0f110a0b010906261509032515090210031119030c1b02090105010c020f0a080f101404020108040c0e0a021c09050601030209061801032001090b04 70
    0xc004c0b139024003111030342d01009040c22458000ca001d006958446814130301905d070a002e69012480301c0701d2628441c994405141e42c0c410b200402604d00d0521509044140c800c001d080c501c1a8401480480d18908a1001c010705000c1c00d1102c022100090703240c10362156179807040c00e0341c000e481c0000480c01350b10354100c03426122903030303160000e00c100c40d890001e01b5034040c8003a13008400440a02e1001920b826610075292038600d52944400044e507031031030300c1d500114054020f40185000004101e1540103185034032110b0320040c4001d80820b200c07404170341101d085612684040d4400c804002d1011000e1086c02c0e5120305081c01400300a81280e4101040c0381d014000038104212000000c09000c610074008001d40515103601845082504410740a0f40158075504a0b50210100d1429007907428801e04100c2da504c10040c001c607a1842d002c114552000800082e01300d00303001c0044103582d29500d100c43c0a948100b640c270703190000806d0392250b00710110540c18103005030000c080c0107892060017510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 373806007 1250 373804757 373804787
    0x309121704240513140f03071b1203020a0b010b090a03022b0606180504030f081b0f1b03130909050307060e0606041b05040303030f0e15190c 62
    0x48410321071080d585224102c2c650020500c51803c000e00880e15803540344141c00303034001d06080c0104400f50302c0444d12104545411119a402006502d001584c0300c5150880c00072001140141980e44881d0310401c0342c04c0720b0f4214010f0300001d51800030031142c00d074010b014000c11100141044441e0b4086800715280d40006803045e1520201c0ca03039400206414050784441c242e0406070020340e180b4010380039100600139128a40c01081d54209504a0351244e10b12441d0180d617243d07400c503d4081c060754000310103000311054065420407080700c2e41ca40c80041034121201c0c18090b9603100c081205080101651001c4084d50300104459031003243d402d01e010b0161005660300041c012018500740e0700d1445038150042c1a9414103035500d28010307021550510070308081e101401000c80f002c21290641c15440252804680103100602c0030034801da000722103480d44181d0000e0341c0c078070142800f45000300342c0150001c001d00410401907040701d2080405024001c03890244070014160300301401c0e442045030301c070b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 373807257 1250 373806007 373806023
    0x5070807020a09060315050f07050306040903090b031611010c0f121b080402030c0109030308130203160e0601140708030a110712021006120c030615150309121704 71
    0x100c0940d40da0426a10003810076900400126540c1c5c0f4040000c01207901c10300c10620714050004101c080d009200c144a04a142d0700e8503c0c5585481c100002055404016020000c00b81404500c030b20200f0000d40c0a40046507160b100504900c6008041941080244510341d042a400d04101604101013007001d43c00c50070185030710280414110f00405204c2140d41000ba80035211100858102d502503002c3d50099056a07036120300e0500542c0d00010340d00c80280020340c00d0000806140e0402101c40b28184010280d40403030104070b244814040d41c40e000308550396454414000c880d80c0006514041450701c0015600300106901c3c0d40d8404e000007440c400c5003a4072240d804041400b81c1084403800c542c02615441e0240c00080003d55543d400c1c114030f42c0391031030f00c0004500d140c00540006d8074254400c1c004000c0074219a12840a006840c5074002c1000d5151008252043d002c0c02c40c640907482540d00207200101410300648000030b52246400f0321000300000035406018007001588980c12040b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 373808507 1250 373807257 373807267
    0x3090f120c0c0d020907300906050703020c0607050a020c0306101d041a04020a0b030907170f03071104020403210807030501061e090b070c090c0905030a03030b03070312230406050708 80
    0x11550342443c140380c4960707c4858104541c00e00104d541c0080b25a0340a1201000140c1d18083d042d0201c0c4101141c21a1a034000c0c2c1c0050603c5c3d00c034800400f101c101e45c1c416a2618210100841d02d4120191145602180011010321401a15034030190003050006c00e201c8060a041d02c0d00070403031103603000360520501d0040015040d034a410040304010205151400d60341e1801d0144640c03600c4c1c407802140204090714403c030704480380005016503c2088a000f079481e0003000c1d640c40b20308803200d000254006800340b10000c0801ca48030290a04450705401404207000c65003c01401140700400a4040c0f41c1340200603c1402d5011482c4200241240c29030404010002c4003910340c048964040181c10100080340001c000d0303004075440403500b480100784000204040290b540794964090b594241d4441d981e0000828825040000100d0010f02034602ca1070712622010b50301c008001500000c01e40e03910303c180200c4014240c1d051602a2061868109400c1c42401000e0781301d54000174040e0100456 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 373809757 1250 373808507 373808537
    0xb1311120f1b130e100e010605040608090115140a0e1006030b041a130221070f030c090618170c09070513090203090f120c0c0d020907 59
    0x10469032803490000c00e41006181c29598421284000c65030000ea09541140840e010a004000e6903800ca1007525520b042a041220381903502c0d40c0180010703414032001034001034016500400710b001e0500d86d903d0a43c4d035410f0030006442e4071000340c0000d11580c0b43c0500c0c91180040841c5180c10f40b52b488814803560358a5400060207030344207401080418480d8014440c01c0b00d0306c25050070490b42583c13400d001860900c03040204464403181165840ca440c4500c0200c0c51601120303040c1d044040d4040142080c00d40241a600340202c110a00f0f10440d2450900c400c03943c008107240710148244c9420b0041c01407462000340541c006202d803900f4400000140211002c030390a014010340881c01c0400a6144194010fa9468011403516801541450701207054103100707404071600880f00181d5036094502c0c0c1210000250300003001910701f4002c080894407440b9051241240400c0c92114041c1c64100080c101c0341011608429184161a0802003000517101c1250f002e40c00b103190b003051600804009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 373811007 1250 373809757 373809791
    0x609060f0c010c08090d02030c0601140a090207060b04060b131a0c0604050d11030309070b0a1101021c0507020706081501110303341e020c06040b07060f0b13 69
    0x5203030041d55500f000040510581c1c0489030702d00c6016000c1c100ca50499801e44103030303213902c26401070080300e811120042c44086803801404404003000381101c6400d87d070f034941c1d2004903005010201e50103074584854400e42e292901644001c1e00c1c09070407040c5002c0c0c00007058289240a440307000c90050100c2032008a590744042540d01d05589a03096600624061402c0d0351280005003400300803c01c2004400313085030740042039038400d400140080981034100300003900c00b500400400000c0110401e0080c202c508203001402c0928a58a500340640d903d000700e8105440c00144008115402000200480c1d075010000c1d0f5088040c2140341d1500011035401210040803801400c0154840042030250001081c0320500140d0a1504458030aa40465402c00d00c800f040d405100015004a111a00c00c009100c03818030002082c01124860400346000c60801d42150b031180740d8000020480d4028488240a981c00e090000f18042007100c42a81c00215094410b400e140c5a066450b14070000142d405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 373812257 1250 373811007 373811017
    0x150e01140c120d0f15030f0807120302070507050111030d05090c0d140d0201050103080a052a010f110901170a0204080a0605090d141c0615080108070b030103020609060f 74
    0xc4060314441000d041003500b10b40c0c08007100300e140600c0c0000c4031420590078824020640c2500300050a100c3c6540c4881008059851058400c42010802280003808004a90416202c607481c050b842d01e03030f01d04084d0b041c6600d9a201a042c0721a8a008621920000c000c49072f0a6101050004031510b814002a292034000061a50000c00702c085d00028011209040b00c02d010140c02110010f144459040703082e19800e100040c1101000d1058500c110b0041001d42501e4403142d01c3c0800b510f40000180e041c1c1c60341c02c500101d459554000d0700580c143c0718096141985440b145031850601d071000020f02c1001400000c2c460410000c002c1a80c041711038040f1001406010112600542c1c2824804000c4c07100b81d464544610450b011401e445003d001240c0c1c03200c1030300d204d644c1450521010741c1d01d4203e40b1543c6800c03203039554601007001d540104040003a500309640e480e10030341c1022040c80c6070000301e4012013448023050004100517503a060440d0a001001d0700d6642e00c6111002030380c0711502407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 373813507 1250 373812257 373812277
    0x504020408032d07060504030c0203060c090301060f0b041710060617071e0e120a0b100e0c16020f040911100509031506030f0f070906150e0114 63
    0x40c0000702000000301500c06407460b1079885074260310b5502e40c01c50320b00f2107410308051210140586000f0409660003160720a001e810b100c1d0852a072940001d041400071581844211404208540303941400d1160601a104120392150100d00f482c0d1480010702451140306039012a0b01c0301c6540440041c003074024a510f050400784071031a19000e0245c02c88450f02c40c3c50312100c54000c0011715082c8241320a0340345201c3e002a0011041c0402c00485a0100804c465034100c0f12011081c0103882c010042c0038076150040403061168240308820f800102040d500460010300818181b0840c808008200c80601c039040081201100003880883d0001091410842c2c0c4103280107070310014444800c2c03048004240803580385101c85c91900d82501c0c28003c0d6245580c042d88034001485108001e1941c00d90030841c000d0895220b00444108580b501108841c0450350307420180003000000280c0c005e500c050182e1000a41c00d981040d00b00504601e0210b0307685040065604c0965100c110040840e03082043d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 373814757 1250 373813507 373813511
    0x515190b0d1d060108010b011b110415081c0e0102120304031404060203090405071d060f0405090408040603060b0715051f060e031b0f1201140f221113060504 69
    0x4a102d04181c0312039091080c1c1c40035508020516095601c94034602c081c3c01c00703408100b01c0c3c1602d103031243e04044c00b007104080c0e00031360f8070070b0780c41e00b8403044040d60300050404000030140c1883d01040c2c03828001c00300c1034210a0054000c10f00308160b80101f5820780020703144003407a490b69075a040459000c2c00810300c1c1c8010a9000401140459020004004c480d000382c50600c904c1c1c45000e000c991105890a40410281c100150394600b4a009002801c0c4090070442c0d1609103620b42c40010700c600c0307003901c0444810b00002800c109240d01401020024810b800401d0b09101403500c1f040a80c242c030000360041c0c075640d000021580f100120840018000311000c40240c113803a41806081c40c100c01e04028802d00c148211019842094914184210030140a01c40f00c0701144c07037400681040034450991035501c504000d006100081c981d14411500941c031100141801d07420b084021040d5102468041604c0344660f010030b40002c00754020f90010b0340d445040390800c3d50004002c004c0c9800203a8414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 373816007 1250 373814757 373814801
    0x40b0f180712050c091918020a020a0602030a150e0c0a1b2f061303030503090304230117040b0417130b04090b030a0c0605031b0d0515190b0d 62
    0x590031400317451070040580d41840c100c80454124007001c12103101300c4100c46003080140d005000303244c01802c10b000b264011558076891640c2c40c001a82c104171152100d8075a104a03009002c0e0701d291440d4004c0122a0060010b42001d0441e0749075889466640420f20a560380c1c074000743d0f992800e9440140b500b10009448000004000003645003c501c1c4c20b441d100180800c0c03100300e02c0c0460407245511011044400c1551465030243e9043d00002d248420380e010610001900c4008141c14510050800d030203035110307064400024100f0640b500086808115860802000801c842030343d03034000350040d40051290071503c5148003d4402c800f0ba0100610700ea580020b180007a440c081c10550303132210410b001000c2e000060558945240e900580306200b002420000d481c02100250741120300d0402c84441102400b0050440b5030014103048040c990351800c11040b000059800520300d80201c2c3c8150480c06141100d01030000b80d80280348055000144c00e0580c41100d07800000d5111000259905d01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 373817257 1250 373816007 373816021
    0x3020c0103182103060815061003020c07090c020114060d14010f090b0402030609060c0708030a02090a060c030f03021c0e3309011509231302040b0f18071205 69
    0x300c1003500e201800f180c14a017010038600c0001c20300f075803401d5826040480c2542d0321410000c10160701001e94050640c20407080351700c20410f00000014042043c00810b041e076448400900315840d8000084c0400750715400d02c000c030341d0b4269170082425000b80c04a4001841c202e800c500406284000420880c645148241000100c8492520490003102940d25030754401c15500e0300c508049402100905003000b40b00001075030100510303004401d4400060031300c0511808100184000d4100344040b6000030717460810194069030306c45004855140c2541840300711150200030904000402e0200741c0c031340c411103c109908002074070350100303d40d42607841d100000826181000d0384c00a00111549007800203505400c05004200d90310b88141d00070010589003d0f90403008003034844141c082c4818807584a1107001103111141d004203968540341c1003e0f1401d2041008803072440a0301402804a02ca10302d000355a00d01500d001c260904d0f4070752510b9913955100b01d03000c49903221100400342c9484180310b00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 373818507 1250 373817257 373817303
    0x14092101060902041413060e0c07052e0c0908100906090609080a0206091501061d0a090e010b120c061b060901020a120219050a03020403050102030108030c01060b040303020c010318 79
    0x1d03d15046e14060f5100a6075410f14040d5103260180c0d514a07410300020074803e60300d02e0014a02c0501410a540f079a500c1d20006080181c0b0400050b000f4510340b500c800301c0d8840c540f04280014010b410000d103c1840e05071039584442184400c015040d5072070f115501070050580044994551000c420414500740b80f80100013a002001c1d9540148694000101030710b80014451181000c24000c0030000e0f032a0480490314070914103c0811550041032114079142c943d4803080d07000d06922000402c1c0035103042c20b003600b110130802031580308001c42c09552420765000b01790605180d1040e00c1c01ca6541101500c0740d080740642c00881aa248603030420003182c0301d01907010b4103c18010781c0c0c5541040c20034403030f141e09a0103003980300c83c12103540304400303801540510300500c0d100d94641005400d2035901c1d282e0310708a8009078454901e540001440d41c4290310b080c4200f00c0600341002e4818201402d54600135a00c0000400541c1490b580e1000c2880c0c8800782d040c15402c031980803900186480c0c0d503542001da = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 373819757 1250 373818507 373818539
    0x603062a0d021803060403051603030e150103050f03040501120e0307050304090507080f010e060409020103150e011a0a120207020a090905030a0e03070b0f1809040c03031409210106090204 82
    0x88144821094803241d01c2c4c04107840780100d4050b502c00f41410044100500c0c035122070001181490780c3c5a5403040441c5007409196607800d890181031096601d941003941c2001020302c01309003141c01c10481480141c1e00020a04080b40140d000002c1400c200044140346124004025000748070100300050016126000035202e4402c0350344641050700c4245141743c07100310a004140300103883c000000d2442c1880d500150b28140145000f05a03405031120031420141140c0003525644080401032003003a504c2c0c0c682981d12000c0c00c104600d003510b014030050010034142c0740c041c8680e4000030a901950ba130451268068142c4070410484a889460300f0340e541e5016010880108400b40c04461540c50b0108540c01214490f00c02c1c1468084001100754455000b19030100c00388061140702c5010362201440c06106900c500e070120612429402c0180c60550350091030340c1030301d00800c1051003d80b1001d41c10a80d4007642c29941034080c0d6003c01c903a0151070310741c101c0846248042400100e012850324140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 373821007 1250 373819757 373819777
    0x5030703020d03110a0e0f09130b0606031023061b0c0406150c0f080a05041d0103262b0c0203090a0e13050708150109050603062a0d02 59
    0x42c0d0101c080300b01c2a800d032901d0003010341000c0c0c0300b44800600b540c040d94441e41614002001030705064100c40000d100d4001c25644540402445101b50040290102ca11900001c08503581802c0d46050368a0b0b280e90703a035502650a0304c030300141c00820b6000c4852500d4540c4000109190740740c8448040791003d242c14030001450ba0303c01c045211100c0c0c1001c0c070410301036600c1d810030020128a650b0007130f120309014070401c0340e920000c003510070007046411700540038242e25035a0300c5958500c3d000304005c0011400c9800d1f480031b12040010000101d002503900362011130420342ea1514082282c2c52039050089aa0100000c440b107050300c10714281a2401c101e0b03c40840d00100158121103500700c0c0d482c003800d82c041d500a2204901486243c45d5034001c1544201c444000c0602256039660f4075040170304039440840d0390703800301d05154040c55803d002035024200b004410405480c0c000006951200302a044082604051305840e030401c840c0c0d40d000503280c1554007003595400e90064440c00a520100850f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 373822257 1250 373821007 373821013
    0x20a1205060f0109060f02070b16020a050a182c060108100c08060609031903030b011b02011707030e0106030b060301050106030b031222090504110102011e090c03020d0503070302 78
    0x2078500c2c9442d41041d00d06190603996881c005083c000c068990280c0c40c04500150300c00c1c481c000a54044441c000d016408600031005a12920741c418058a0040d94200601c6211448070511260503405611400b03000c28007004120101401d240c2912a00e0350400c45644400041503824400341c000341c440e04940c51501240e031100703c08681c401c103c0d00d01800c1800001c80c2800443c1c150720340361015248015008080d0f400620b980c41001c16180c8a880c0304402103074541c1e409030307190343c0c101a588044562050f0f5505282c2020ba000800d5080c1c00c400103415803080e1000303c3c6c0f120344213a00803031080d0b0740c00000304005c079124281a1540c03a0101d800c28400c0d82058008100c084c402c1c007d452001d0340150003084104a038604858942d0050b220118100c500c80c00e8034440b0000305002d400050088070000108c7e400c0904280d00741034202e801d21410f5a0414070380d0400c00d00c010401d44003c00c107100e000602624245442400014140c3c0040d6010100b4040340c4103216011005150b00f81c46a021 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 373823507 1250 373822257 373822261
    0x9011e0501020c0a030b06031227010203040609030b04170a020714060a0e130906020f0309150c0a030207050a0812100609080304171912181422020a1205 67
    0x12681c50f42d0710541240c02401a40d0200000f403044d81c0f1050300032100a003910521541441c100045810903064801c0c80c5a13070012480150444a8159140c1542031026518250400d0805002e03400706110040003200c0a100041c14000000e548210b6010344100450303803060140c000941d124214021141c1010403040d803140c1c1032500200300c0c1da034032880da01c4940b1aa1004020860000b4907120101e2007592543c0c0d801d000a46144014031035000a10031560726401e260b84403d181485c800c40c444000300d10081404035070f203808015a40060010310f030250f5200b01c1440d100d41001c038218001441c9410105400c03141802d21031a5522038480340c2d00a610f11030356100b0403500c10560348070b81c5000341c100304000c0c443d001440d81c00d030300c0e888a0341c0100c034a403110039000c0b07800b840403003001a01c216210101c4003624681c880000505a030400c0e020300c1905040400009900d01d00100641c407400010359081e20400c01c544d054415140caa00c421074540445a00142c4044903116540c0003091500b80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 373824757 1250 373823507 373823509
    0xb060d12030c0e0f0f01140c160e010e07120509030c0304080607030b06130b07080c0f0a151116020d15060f0e0103110d03030615050c0609030a0f050a0e09011e05 71
    0x10161001150040c03007010700d0505d540040d9640d1800752410074100c50104a040c001c03910800c03842c582010980c0300d0a140d40c1c0742110701c1404d10b8041e01b00002c91060641400505c0c0d61040010b403920000301800121500c50007105491880350b0181090280004103000407004808241d2031b00c10221a1800d00000909504008540c440c0080c15100303491b000074107200004c21131020380b18407031003a003443d0324291080405501c1e04000e00100c8506500c403800000411100828281c030201b4450414480d46460003200c01c0c0c2c0340940c40882ca0000201402c00c01550340301c5103640c490a42002c03502c070b41c031411000b001e0068042402650303103041480d170000800100001c6903c1c100c9801011203501c02e9466020001406245030094003099161031010a900c5045200181034a40603200c0e140e8900704455460f00300070f402440540360750024005040426048115904071a0f1340d454038540e907645c4400141e032003620343c04c5901d40200c0c5000000c5008000c02c40c1040c0d0303100251700052403071075850b4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 373826007 1250 373824757 373824769
    0x30f0b010c0f0f020d0606090c020c0301060f050111100e0303010f061d010c020f060c0c1e0f060c0102040b1305011b030e33031806130b060d12030c0e 66
    0x320020002401c45082001090f102c0c502c00c0041d9100070030000440361103860700400c1c1c80854006410b06c52381c6207e140c5c04c007501002280e00c08081036009024041c5040c141e030304440d0711885202d05001c0100c581f0f02da00310341441100d0310780c000e22008208540344076071444d80c2c0360824059440031041c03680700420f42a0054900042c6450b50090000341c03003248070300440e0040008075040382c001802c002e100301da0395140c0014201004910005140c1140300c18200410f0b6290b4051070b486005500d00031907083d403610310756024441d2003510b06550326a500c500d03d600a1260383c0c4100c87d51540442c41c030a02060fa15030120460300240c2e00c8103500c2c00c10845036481a0360a0070020f000c140c41440d1240c10b4100010300103070440c442c0a030b0510803945141c540d403010700803a2054010020020401c000a1a50509000a00d8021004001501c0e05c0c40403800b1141016030080c11044160000401a60b0364051040340d01c3c1e440040000c00b410ba681e1b01801400e00501c4840105565608498507400c02c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 373827257 1250 373826007 373826027
    0x9051b150c03030a0b06070b010833060402090d050118021f090521060406020904060e04030c060b1c030809010609110702190f081c03090b0708090715030f0b01 70
    0x403000d940f960703c1d000d010030001c0c00c07910b05030354008030305000441c041810000018002c02962018252000140c600f07074180c42c040703042003100591962041c0d0003a5105280c016840b000685005903118283d00000d119000f01c40c40040c059800c1c07805416403166070680301c2d12014402d0714640c1c0d15000d0390769101100c1803000c00d00c81c009a1801020080f61a044502001d0048a1103203039480c1103c01540a050100840c0d003950240d8000441c19064109403090100811001072503400b80d06050760010540f550405028004030380765080d10762666200941c0240028404080c1956007106181c09807a1040448024545500c1d0080c0020812030324041c9510000c0d1108125103410216400c00443c006c640c5102c00c030034940340002186014080074013030082d01060005202440040311144c020745440c1d02c0060405040902140c0043c3c45206016004906401e10358469074a4003031961414100364400b0b40d03250389101c1c01080321509075121001d41e0141c44014030003002c207480191112118 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 373828507 1250 373827257 373827277
    0x108101802012f070b03010311090c030c1e0403030e010207090e03120405010e06190c030c0804080c0109020918010510060f081305030a030f0b1905040f09051b15 71
    0x69400a000003040118090080f094448054071080d8a80030319a80741c24069003000013088000401802403100301c044007694450203c915038400c1c0b801c800404000d00024001d0110401c0101e441b6403c510810b00211861a600c010161242c3d40c0b418004c217004555800d241c0503008807a0080358165450040d908003440d5680114034000810040d541d290000034400d407003039561a80440000340086c40036901440061180010301d41c0034180c120200e4070b01525607803d2500c0e002500b103203d82c1000c41160301c02d41044000751560020311565024080044c4000c0d84a03641c401000070740010301031110940491103008100e00d56828100020b60001d500915000c07942402080d24000c0c41016187e60000d120711481024080d80c0d13440c107107540c011003070f5180482e40b92840c5032000b079454440e5803195a0304aa00c08443c514070364132590710f24600d0086c14080ca40b14034080c08200000c0d0081c0b15010780c090125081c00c0c05884005241d460071511f45131003804003090b8046031000d910f055905040e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 373829757 1250 373828507 373828517
    0x503180601080d1d0d03020303090d0f0804060b06120c0415140f1b03040906060807030c170c070209040b1b18040504030c05060403021507020106060e0d0f0b010810180201 75
    0x2240340144c8030748240c07080c00f9154122440c0b1040f00d070f445035002ca40c100b52098004507113a041403031915041c02c134140160010002900200c1c140c40c0c2d801035103a600281c05c10400128540600e002c82c0305403081905111116031228180a5002d12010042003128144c071094450325014040448000f00c10316200c02d00081c00740000d1540c40603038801002c0070700340d101d600c5010b052606103e50035608160300c540c203e1640c61008200c4e403508403506a41c0404030b1714003080031030360741c00000d404100c88a50710518507410400103004c14141c04111550f13550020946c4c11245814a40200404011161416a07490102109103030009540c140c4020b4001031451030b486203041c1c0b09000003000d006200ba810440d10962000124000303000040c00b407802070340a0600384030441204002600094444811685894010088070740c0c04a40251805001c650b400100c0910b0b003060f07544d000207204050b2655105100014101c0d01c001a403200c040b14101d81800400e40c0c21290300d942861141c40640031072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 373831007 1250 373829757 373829773
    0x140703021e0a0e07030c030b01080106050304030c0c180e1903080c0705070b032a0c0a06050912130f060810181e090201020f12040b030414010903050318060108 70
    0x4038044041d007031500074001e007403503e40e500c200038107600042e50f0503c04030760703140602c0d8980341d89801100c0031000f0070301300800254901140100380d032000410140402c28118044000c0013503c004410080c0b0030104e1015118403110740200046c507080e1809031070303413103602e030720f4140710311904580c001441e095103408000ea519541c6c1415140d2044401300d445015a420105070100140091401106150070203002e40300c4d6102d40c4690444100380464070424280003030480310f030001400220b42540040c0219190f00c45004c010300d44854440740404111012a0040300c4548001a21f4101c650041e000150243d60303030b01c1134510352002c0c2c903c2000504400d000380f05011081444240c13100a082c00003c124001c6444031500140c034640b24a04151242d040c00199a810402d454070090310101810403940e200e40180d90611952003140c00d90302c1d0100c0001c0901180e080d44c2400301020000a02ca0030700701d45001003055004461001c000e8a16000010b490100016414140c03510070300205192 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 373832257 1250 373831007 373831039
    0x509010606080412030e0604060b03010b0d1e211107091116031709161a030402090c160c170a0c033306090e0f0a02010e04020409021614070302 63
    0x1844d4030320100707400d00d0386a01200500f10020002c00b88110f00030b10001820381030903403c0500351031500c0c8400748a107040c564000007284e851b14231138203490038009600c00c0c4200645001c80305060ba1003400903208000f610b1800d00a504046040c84c401c28a02c15a0740d1152900104000c65240822404c0c40b00c006100e5810695018400c201540d8020309000694030700c4004d1203d4501c50483c2d419080c0c0d01300f42110f109215203c24064060580080c070005c07440b444080b10150b6000041001e88182c0c0144081292140b00c5402c40320050400c900c0c5521650107800e0a1071078019034400d80201550203402e10301c00c0c075404908810019808100500d4051464881000000c1e01805d0700310320888005029600c00c0000c05511203140e2a1000845c00c0c0b8130f004006422104003d020701c235682c02c540c0c6001398105000ca041020030b80d09084c0500e0000411003c90024059074101216440c40083c40e880d411503030440c4030041900c110220f01c24841c42d07210315922180c00e480000d4010064221003000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 373833507 1250 373832257 373832273
    0x60c03070c0809030328020a0b041b12050303010e060a0302180c040f090e010609021207030e1f0b030606040c02070b090612040c030605010e0f1501020c150d05090106060804 76
    0x141d41d00a030203031403d10700064002070455000e0500c040022109516020511011a03e641d181402070700140903180b18585922000900003400280040b00e80108031460001009141c1c01034000301e001d403a615980c915056640390f01c00e0080124003000d0600091261400d030790501c080d20750183c881d075013071410041c9080076418041e0039054014024400072515410103460713040100080400400c895020050550845d240740e0014001c0c14010800f00c609017a0005181d42c21030160b140028106401da401e41d820b1034500400060f01000f400b41d803040f4003900b5002651019400c40c151410340d12400704200840c0d00c10f03000c140c0903070048001040090b00f03250182c03084007030182a0a10701081540030b80300c55181118111100d650001c4203105002d03051140c0d501500300303403007003a1440c104009180020300000301202003042d00c0a032240c1050b40300340680005040d02400080d0503951001c1040703503681144600c920500d146c480054611881401404100e41e2151035200d49030700e0301c0d160010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 373834757 1250 373833507 373833527
    0x1a0d14160b0d1b0e0d210513050a120f03050409020f09040b220c090f0f060206180c040f0e01060906080d0921050f030f0301031a10050f1c0501021b060c0307 69
    0x2860084940d0400e000406c03c460007545c03240c1c266a07096440001040048401104e50042405195180014403203112032a00c3c2e25a4290040300c0320642c030116140c11103440c440e41e0080d4010b035002013074810b1104034102c060304240400b207030140320001e88502030160500002c0b1342650924506801d00309050141d52101c81419041e2030300c0b205082d15000796841e820300076846002c4011100340c0804c900c0f42c1c10b2116507040741071040400e005103c2015026138502c0c1d046c804a02c00c40d0348410305025040d10340d00c074600c1400a00028000199540d40300e400821451281210368025800d4400145204100c0721041d6003101ca100e5000c02d51340d03a600c82c0d604e0000a01200d06204403403c06036040b000f0070203800152080d5001503601e606600e0300b0321130005440c4502e2070610102d4180040007118081d030b0300503a20700350b03500d01107203031080005060612031500502c14945c107031900c20140301f010340042a801c582c0340600b403544106004926500c50085401c261010801e001040180d4070411100c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 373836007 1250 373834757 373834763
    0xa0e06010509031b0108180307110f120d180b031902070b0906100b030103052e140a050c03040f03050304020303070212101a0d14160b0d1b0e0d 63
    0xd418001100d0100c0d184c41c404107920040408440740c040300302c0d03138010140340d030060010300c02c52904403000107016982d0050740e01c01000071065040c190680c0c1c4403804c1004c00030200910015220b80a102c90640f1f9500004803100014404c0d0b2030307070651803602d80c3c98a003101e4040120b10315580c1c9007541601080410007640c003207282c080010304042030303101c0542d03405604040c003e0a800d0404402c1460703040507079800050042c0c0e00748010004107401141c809504c0c280203000304840030314485026051035008041e10100f034602403c8a280301409944248031b0a843c003010000d546522206c41120300003224000c0c80050000c11950010b8441c4e00550f800900c06821a8182160340d40003d5540c081e14451031500d0303100103011060700c052030103900195000b031070344440c40113004004542c01804c0340d28094481841040b03900350340070081184003100000e180409404076200c01e0102480e07441580600081800c01080c0300074030300000b801120794056078555041c601c2d818000d0150007000c402c419 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 373837257 1250 373836007 373836017
    0x16050609060d110409050a0b0f211f0501050d08040b1303020406170d1817070e0114030d0302040f06030b030307141e060105030a020103020f160c0f0b03060a0e0601 72
    0xa00d48100140c002c080040706110740f07071500c0740e00300100c01040395002020b5125590620f1101e034610b0b21010103031f02d803820090f9450f07000e800401c4000c0c210710600b01c290340c41c1403188240f81d1821105000d002440d49050f400c0a00169981d00200540800b030b151010384559001c0108001581c80c3c500140f1490007a0b9041000b565a40c0d000182116900e41c0300703615006d4007000503051110107114400c84080103007005c0800c0a507584200141880d0b5001d0003003a01da0522480740c0d841c1c0100501001450140010040c941c0c60710011007058103044800c2c0c1c000c3c4209184200214024002d507000d4074008601050f0b00c5140840880c01741c042000c04540502040040074049000c54a00c038110700c8658000305103403c0880c02e9004c20000c500d5a2494036040b480042c030856034007061858450740c09117009a101e01c40040401c030203129030000d06001c8103030030808804002e808080c074012a00e800d40c002d104d15a4400b80768480380300456400707907c8400c090b000e0040e10002c80f603d43e0008410301d86 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 373838507 1250 373837257 373837267
    0x303180a03080c0604150e0a1202011e06082b0f05190306060e0604081b0a050d030807020601090c0c061104051c020a17031204020f0901031209081605060906 69
    0x10701e408980c03003803c81c643c841e00000100700500602c0510019900c2e030300300c001c0180d03040305d030001c0d91200302d407440040c8400c0250441252562007500002110143c502c000241224400d8800004050520420043c1d01407082800c10703850310781801da82501450041401d0506d0030030412254a0810a0f10400703205050080c00141d80c1c0c2c02401803145d01c1140c500098150609030b000c0c0c00c0000d50500b4510501d02000180000d44011030050b088442601e0b40300c0e513598490000400a0780290030458000c46482c5841c41415800b2200b2801019140c003a10203a98136507004805480c00d40e020708001c51107051a035000664550301108d422621a400c0506040d2144000744414802d600408000d6a0540602d81076281c081049002410b2a502846510640e041611344a0140c102c2a0083c00136090005040d5210310034580042d402c0113040b494590b03168508161102005010000083c5942a0124048000049003031240c00741d4504445c809151208014056010040702c0da04400207000f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 373839757 1250 373838507 373838513
    0x1501021506011b1b241d221803090b1b0102030106020d14070201090b0318010203180f060f011203020c0a14030d020601061b062306010315050303180a03 67
    0x4030321550511401c43c1d0000300514102e040c02c81e204c117400c50a56450719500c50105180d0311a00e240c0c015201e403c0002c40b10120b03400d621110740d681c01805820040000a11540b5204600f001070885030100302040900e6101208400401600c0d4000b0041858400188016800000a49901205628a0070450811191040c2a038000b81e01c81c1003d41d0100b2014800305400c2a249045600c40000b600d0030000181c00091480d80c0d140b2500341e83c0c010000108019140169245825843c1c08000350354038244514982031584d0030762601107843c002e00a0800f00c0b0000480c00b107004110030388050042e0b900344841c00a51401e91401201988030340e82412020b9150b16201100400700204040808a105810b042c140310350208450210b40002d4014003489030002003040300301100f8004201c804402d803400c0c000601070b000c42c403c24848807108040d1000c0d00104114800c650a9034240315103101c1a442c20840111030182c01e500d074009100d15090080850300d20318526030001c08092400b69070352 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 373841007 1250 373839757 373839797
    0x210714040b2215090b03041a0606130b090a09091505090a171e0a020703060c0521060f060702010806041515110d0e06071403130902030906150102150601 67
    0x19205a42141e44100f401c085241c00c158070780300810414900f1840d52429644d018141d44561000b40d6020b90190301190080e100c41d4151100341d1000c030110f05e142502d400070170100b5042584a144076a031140700114405132540150450154403150403091029100e0400010b800001c0101580707118444070746003c6291100581c2078284803030582c56554090301c504c2c2d1035002c0d0788121009032540070030a124500c0d038005522421640c100308000380210300600100c52170300c1003c040031034003804491403050300c101001c2d0036409150125002e001070b0400e10f003840781500600c00080c4c0410300e40300c005026802c1a4010045c034a4031811800c2c940b41c2c0307601040043c500784c0420a00094541c0d80785140412040044401c6880319003001c60401c025580051150b2007101c100400c80c456440c0710700302d1680100282c071814074040501d544a9501c0c4c16100d002504112141d098901c00e030341c04100944901c45003c1e1040701e040c0e001c4c0101040340035420040070009001503040120b07003a03025410140d10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 373842257 1250 373841007 373841009
    0xa060605181c0606150c05070311130c0f02150603070905041103031c0509010504020609060c01060801020c010c120b012307050a0f031d03030307110111210714040b22 73
    0x94840044d01a0500a06a1400b00d46400c50028400c0000c11a004244000790356003c903a80b111280842c104103074003140c1080810300d6a400105d0510300050600707070300000c00099821a036401c0f20059203c0d59205854103c0640305542c05d0f4010802c1440884100e420035580240584848284085c0d80800b0a03d164401c12a404107000310500080c810300c454042c040e002440c0030020700c814140364000072003e11030f0b0380000d84510000102903100b880290459001000148000c6440c0e146851a42c0d01900305e44d08201c00151014144001c3d03401d6a01c00d102070900107039284009450755402001303c6031010b502458070840300b803203a4000250200101c00e1040d11a8040301d40d081140c7c0382c0030b081c02610742c14484000b030ba070302c05423201030f1070000c2584da000a01d40780c0408401d036404281401448050328030740c145000014002c0303040c0b11000001d002c645545d41e405c4c44968800d802102d2403604c101010114080422042015256810242402c05600d80c80c0320a0030700049109400444d00b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 373843507 1250 373842257 373842263
    0xc1e0306080d03020322020f122a031509060c07150606030f0507020606010c020616080301080102180312040b090a091d100b090121050f0c03060a060605181c 69
    0x80008003405452030958502d40780c006e000d507061151380013901e0441c40525060145940049140442000708034401801c003074212510340c0c10341c4510480890301c107c2c420243c041d200c2d4143c24420130042c460001d202d00c0b004c2d0043d244030703211401411403d0b402403600f03480c00503421030000b00e100307214402c95008080c107450024a889401c15003c003905c800500a0b419034200c041006060303600191125000c69044650b03598070300c2240c1403034130001402c1502074aa15004800031948090550003441c5000e24582000e000740a071604241d070b50603540d0484c400ca4241440100281c6220b0b9010f0541030000500107050103072140000c1c0200c4145001c440001d158200c20f1544009052211881400340400184034019003100496150441031261895203035640c0452841e403d84100190b5107950b110017500c14004103080d000f0b40d1251029003040c400d008a902040c0c40f0001c91050008540c003c5c0c44890801c3d60785d002d049040b11504081a03086602000d900304103411001e02040030710700c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 373844757 1250 373843507 373843511
    0x40302070b1201060914010507110402040b0403081206030d0c031110020a0c0308060303091507050c1008070f0203042301021c090315052a09090f01180c1e0306080d03 73
    0x3c541362005140c10017950145022101b940e041107a40c0c0d9100c0e0031100500e07042030019040c01803102c0400c00034400c0703501005030301c035010801004214004c002001c41c00ced001d45812102d0384803d030805403503101040502e4003007060001c801000a001e030004000c054640410303120072000b41c2000406a030710054480300059003800780a0101600700124940080061300210304088040000c01c484510140c0b600c4258100441c0794400c000c0c0800254241000291a004070a001e4000c0074000210a0310b81c4004a9013440030351000e540b000040d1003c840280302c60070b00b120010b4011102c41c00303800c610f150450080b00600868200c50b241000ca0b24034850340d5070036800d0b2840c28101040e100e04045521864104400d003c0017501148068107040d0101000a00410a101c1310341c0261282000c9950000002c17402c0000a514010145040b504d41c0711704c07604001500300d036500c203c510781d8218002103030905846c11030b44141c080c0d95031000c004905000071541e4984c140c2d589000d140500e0440025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 373846007 1250 373844757 373844759
    0x3001170f0106030b06040e30040902040e010e0108060906150315090d0f031b2a0c0603050108060412110a0b010f05042d020a090e04050a02040516090b03040302070b1201 74
    0x806e0a04c103400041c09464054002d0851303200b030701b0400d006801c03048080c0342940c1458084145080e02200c000b0280c9000455403541d8848054100ea002449480c40c00407120780005580b1101044031841a803c107005001103503100400c54102e070407484c05c203640600c00c2e400985080180c00e40030314040d86180d40100791125010300000c0030070100303003248420941007805072010510085588808400507040400380d10003454100e94410101e25804e0944800070502c1c6410711242c00c1c45207055a400c4d503810f00ca913a80301c03400070340d0321801501c0060202e03100c0c2401e401c80f10f2150112242e00d080b142c06444070b41e00c040d212002c1492007a004506640c29208042000386441d01c9641c0e103290705c0d10301c8036803210750f08042c40c00c100e07041d00e01c00c3d0040751b000500c0b00c408510410b9107070098508134420f0400f500303050030086d07a036480303420040b4083d51030000414000781c1055001500340c00b255480d4040d807418030300c46500783d82001d841141980305459000c120b040005018012030758003032035024099 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 373847257 1250 373846007 373846009
    0x3020618030d030b150a0315120b060a05010c02040c120c030f0b0114030c030709180213061119020d0c03030f02060c040e06040203040309030501113001170f0106030b06 74
    0x8041c03040702d0700a061420301c100c544c43e1500c1c0b02045c00c140c0562503054036074000403826005003482a0303c0007501401583c0114020703a000c1c00191070b0b64094940800544c1d11601031111180340340c041c050214061252900c01842c003608203d140130224640300d20703800712509001041e2a00810394101181d210130520107000094491341c40c1040003482c15254203800240300b629503101c06400881c1030700b03002000a2445025950f5580200030340c001d026502054030080f04000c0d0000506c078014065015030000b44030380700c0c03d41d4a420b031070050040c02c0480100c00050301881c0725400200d0700030038880c025402141c1402c244600450194071840c0d0b038402c40080090600c003000b4241c1c000508203210500c40d0802c0100c100b0703400b10050740c0c01640c0e40c4807400c1c2580ca400d030f2940010000d42c20041c501d111550f41a01070400007080b5070301d4203031052072005852401034412000701000000345c0c00400566881e8400c020070190048140c800ca030300c014050b9070940c0d1141e08144c7e15441144180003017 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 373848507 1250 373847257 373847263
    0xc0f0503010515061606090b0403050a0e010206010b0904020a031d0601030512070506070806220b030c0f0f0f210c100201050708010b03101701091a07020d12060302061803 75
    0x4043e0610003008548220140007440500440300d65640030800469201d00f00a00c0717a1181c42c00b00d40000c4141d0161406113001407255101014000004541800720100c0c0c1d4000240c0c44d040c2d881000d541d40c20a4010f00034000203400c2074101c00105a220300c0040390341d41c0211992580d815648024000750342c19420101e1400e46041c15421111104108290100e0340c0070800c0d03a0492114034000c00d040e00c524000400900250041c54035003580c100942e10240781ca03074000c00c0c42140a40c00d88904045180410100340c404055164104a460b103114416140a403d020b000e03410050040070b01c180d414440c810014400d840c044419440084507404a00c0c090030050007104185c4000d000914004900800001d01031007503003504940400803c4080d42081c041001400300081c004400c0c900d52840c16000c0c1024900945945000c21111151582075030815440b56850350000d08400506a804941d1800f4070310203c445250360710b1001c00180c0c0d6560082482e290411840c007061a40c590030541 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 373849757 1250 373848507 373848511
    0xb0f0d02070c061b0b0c07060e010216020906060f0f032205060a0f0b0d03030b0f120a140d1e02030d05040f0614010f1202040209091003030f0e060409020c0a0c0f05030105 75
    0x4905281001803000a1201d0742c0c40d603110541b10401c640342d0280d0700d0500054040401c1c1c2d17508650000c100c2188032518015042e05c22402110b0035100e07605c4200c1408030f035208580c03495601600030088101003007444c03c02942c108400c90406501507540c62200404c1c00c0d02020215066000b480911404820f00d0040010245404c0000c00070082d40d100003544100540400030700b4551600070b6008540d03651413407000507207005403c0150408180c0901d07601c1e03090303146045403502ca9034a6078000300340c0009002e041440e2192120418084c2d000003000120040301c20400452200700844c0240304880e01525004a1040c00f040d41c0f0407a0915040303055800d00c111814941d01c49000400420709000c03400c03000c40340d00d40305400c0048418008900a8406c0f0600250000014018040510804c005140c1128042da4812030b2040c0e2142c01140d031014a15003160b40020b0900003401540f080c0c7d4020080e001c2c154007200c42041c031603a0354083c0301249030300016100c01c500c0410001403c0a000701c41d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 373851007 1250 373849757 373849787
    0x801031a0114040f0b04020309032a0304051909090311061501020c0127030b0912160212010e010e0c0103110306030712050a0818180403090b0f0d02070c06 68
    0x14140d814102002019100325481d00d102c3c070340b5110300c44209122903201c03a0415802420075540d9241c8030884981d00d9010840d400b012030301076050100c1c0600035182520000c0d00900c051883c00c1d191004000854500346400020000960f0f00094031011501c5007020061094030340c86000302051000c1402c01000401e00c86200040d05c4410038241e07804540d100e02410309003001259021104441090414050340c5030f6000c0100b22804400d0042d07d01c000e41c0f1803100c2e0700480d0046103010000b0892400346101c2c1615848000300c2000052030480908081d0b42c5105000040d0001e442c4851400c2d251301e40255102a0400ca0b0f0582d80303541d140c014070700001c45100b10145107041200100760b841d0510b105516440686c881d0b08401c1010500c0f000d400290032090298503448000903414018a038a11340c135101d0741241665015070f040c042c002c24412501921480c103d6460800703034a420b0f6100b00b072a003401d05020862030740051964806004a140a000422101c6090203006041002011070103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 373852257 1250 373851007 373851053
    0x12130608060f09010306110921010c1e0e010507050607031d070305100b03030f04091a09040f0314300c0906041710021209100e0d05130e07080103 64
    0xc01c040f501d03000d0605045980c011000194610304040344500d5024810b80c1d1071340054200d0311000c120325595408094117500e0b80003080f014038542c0d01690380c0350381180d103d20385551419807140c03524051404e0001c1238206040152074006943e54081c109041191240d0100e03507921501e04410014040d0b4034034445a0704020a040da0540e10b80d035903a80110040003074150740350401c41c005528140117480d008d40d10103000d1500c80d41c646841501910f82d0b0110300e44443c408400b030328640d18200303010f940260f0300410181030008545c2c070300b02c0f400d91b0808132901400104020061034540d03241800e0202e403811a907404090302504280c207007a00030140407005100014402500c0d5035a40000310380072564500308102e205d039103429000d814890b0143d400c03c00503101044060400c2c0740614040c1c400c0d10740f0710a49401c44290001001150001c09402c2c810354000c0d80e00d1007a481c06000140394118014080349402c44da61840b001c0903107030441c0c1442c000b50714040100302b080076003060024010070032104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 373853507 1250 373852257 373852279
    0x170a0e010c051617040b19030f020708030a05100f230301020705060609100e0f0402040e070b16081c02130e09031e1611012304171213060806 62
    0x5160b040c10320715800138142d140c0140c480480b4035440d4044800a0880302c1600d0380b1b80700b4004171b00385804e543c2140000440d040411310781030300c0d0aa2003161581d6070320184040c10f64131000188001410001c0504909226200c2c2c0410181070b410716010042401c2c2c80e61340425542c0401c1c03a41e0303e00030314008900a82c010701032080010004950705a00c141c003035841101c155600c3c0d80e080c40d40c40c11948281350b000c010f8010300800700410401e0500c00c500984040c041b0054000c003841e541c120034032480c07203100303400d20003500300c0c40040c1c07001ca600e18080c00040d4101004070480d00d40c04400c89803216030481d40001c4020810010074203040003802c02c4000e05c00e0303901d40031080e280c4a100c0c40800030940074001e00030644151050084e0748961800309403d07950310362a8540150a584100381c141e01080b10403520400c2000380c0c243d5000043c80440c031441c01d0514010380d44848a1030039220352000c1c0106d070720060122a1850182c14541000a2a120040c0c0341800180c0381c07110142a46000b6001221 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 373854757 1250 373853507 373853527
    0x518120d061d010905270106060e06030405060c09060403060e0c120d05070b06010306090e1e0c03100e01020c10060e0c0a05160203071203030618060321170a0e010c05 73
    0x4604540c04d0910114856940c82c0e50761444a20030411106080c168481c185080314055211b0b2003a1821030321000c034400b019104228060004450040c0036074040750004104e048094050044a50054403407030426481340e58132415181c0d40789004c00180d015200c049014640420340011250850010705102c1648102c000c22500c41d8680c00b401e0400010045106a44254000d100402c40d00c1000c00a061000c404580c54900d80c1841584441142d03152541e402001f04507952850301c000d00a1102201d59020361007e0114103041ca59555403d025942442c00140310b4480340390340800300040e050303050182640350b035140907100c40f080410500202080ca900402215040c80000c20138400c01d04035440064500700460704000001c0d5004441c4404064050700080140e41652640003080c1e03591560940445220744409403400b10f04441d480b05880a0304000d00e0200510301e00002c000d150801040141c0b4001d44030081c2255a4203030413464031900303200700d202c03081c0546003903483d11051807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 373856007 1250 373854757 373854809
    0x504090c0306090804030b0a020c0d08070c0b1e1003050d0503040812130c060c110d080a08070e220b0a1a09010201090b130c270518120d06 61
    0x400700408a82d901c0300b4010a00c92203500303803002142d00c04050302c2540750100010300a5000fa82c5900e9092140348600481c881c0920300481c41400039544140c40300343d1580b40c40d074015101400121100791030300b46441d130034031001c260544604030800c69841411b1440c40c1c00c2d850152180311500c00c02400303000380000140b4950803621414081e810b001150385500c07460401050030884001c15540030400001a49030704059041c0100d07005610b10302564028000380810f0f04500d08008140041c10003003466060700682d9515007042081c41e00701401c044140105030001d01d10340801d000340c8c014103049840104603016a01180c0700941b0310709030300c9280aa2030100b0031905418040c0701d02021030740d1449a40300750700070440681c002e03992944c0360412548617885032803650010360320311040300e00101d000c0502d0402042032a40385184e00c40f02000e903404480081030050081070152644412480500c1000c112140000c540d103d07a845c1c1d6004c0300003554048618030f41c01041815a00070740850110826 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 373857257 1250 373856007 373856009
    0x417091f02150c39010516180e0133021f1e0f0207290627150d05011a0a0303021b041509060608010501030b21030c100b0306010504090c 60
    0x10564401c4074010a2084c02c0d044004103074601e940c0b07800700b044000800701d80c0301e0040b007030b05440b04045c0d00300d100c5500e05d0401460061090200e110401045403410038211081d1142d001c614011001d0011040307449600314035900c6100681c4040307000b45125407429450480c0850742c2008000032a064560124101d40610400c1c0c0c0e4a41e4480c0c04120640aa404a82c003031a80403081d41a1092590030564170030380400d440c00101510000050304ea8203000c4c2d0b00034003c9403c0b148091904424910011548100402c8114100202c2107050075903241d41c00a403158501c52400442c1c80c03804d01c40b411a0054441441c0351003903040480400109801042701d0700d4050452000186132400721011030054450940c1c40c40a510b90301c980066034021030740c41a81555000d1740c5010040e60b032400110242c8181004490340100207a0b502945601455626a40ba0340d03150141da0500d42982c03244c60070071804010050100e900d5160056003441e06102c0f640c054071040703401b00700050303413525244e90700111 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 373858507 1250 373857257 373857307
    0x2100c080f040201020f0706020a121404120c0906150e2202070615030305040305010509070b040e060111030a0e0108011205030a050f0405150903060f0417091f02150c 73
    0x40780082425648203022029420174400704650500ea91050000d5840c000b12005856207a1b0380d21905540603c01c5a640d9a0140111106410242803044041c686070340b03c042115014240100014014242d0090b8401440e40728104944414550b001804000c00e0b60b9a0620840844aa111114580c114068505000384000680329040b40c50110000d2a00c06100900d9442c101c000204056200000340140c901c01ca0083c000b68513600c0c440340da40d440c640248071030341000744418414200c403c000b07240e00100515241c00d6004a4402007815640716268900000d54001c610300d0255801c03000460041840329043c0038075030b86907110075449014040089040100010b00148450303104d0003980c000d45401000c400a0300d00c040c03020004c03503000e0503800303009001303080000c0d8070024801d120300c0c85240c00007000d06a2089501300d504059000c00030301a0b000031424140010390f01d49805401c100e038900c0d0000e241d0f04c946003950086840c00100440345000c020400c450400c400e200c00c050901003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 373859757 1250 373858507 373858531
    0x14040b010f121d0f0d1d010f020a0b07050d0b030f030a030e0f16090f0e0a030e0604030602271c110105091e01090506120103080315060d09020102100c08 67
    0x507a40360741c00b600c0010940f40c006901c183c0501c00c50300b404252160243c0010707040702e0342070705040019150281e5441454001c0c14400c02d081d04c81d540680b11400024000344151617200c9a03a644403810b60006980d440000340b800b080c08075074001c0310310960781c980c40210000c2c0020075880410560703911580d41c2035020140c5570704c0b45000c215810030400e40c40c4428a803d4880280110b156004000d02d14481c0107075107424141e1f218040105440742d040d01707000305406004460003a440984050203c0421700c1c0d08103000300000030214045101a05040e00040500c8014008601d00c50b0800100510014482c460310840100c0300781c0d03a0903018403155409018075141c0401100142c95501501c0111500708100100c418407107a5200080102000241c0352034801a4a0303506010700c5010701070100c0d2850081c44018000301d01d50202556000910a601c0e020081780325020403066000f081000ca5481d840d05910421581c050000c88407074844a0010401044030080c014540b00b805031404842e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 373861007 1250 373859757 373859777
    0x6030207170c240a051003030c03110f0f0c0a051801030f08070605090a0201090e0702150a09050304080a2d060e0a08031501140c0309011d0411030114040b010f 70
    0x301040c07040340d030b240414044034031060f10884081200c0500803503858a4a5182000060303003071096052031410f880d01a910212160560765003036880075200d01c00ca005510803d445070000d035a00b0010441d00400900c00317410703120860303000d1040e1011b0350740006110b11020003460078103544940986045a8219400506a03a0030b402c04107140c2c450400050016410700d030800c07400e04000240211004c0c801c0e6603090180d40e43c0c10ba104031030302c8140c88150042c1c00600c1c0b981d0205100c42c070640c0d04103181d1140055845a41d540d2140f4640c890b074441c648941104180c0c0042c03203210f01d007807e4594040c180d030b001c6038500c0b942c0c420301604e1640d60080281da070315001d4440d501003c211140903103902440781940d9052a401c10180c03a842210020b0000b1404611082600c0c01003040e00c0c0009079034002103080005200064800c41600d44001070900c45410550700c80b0741d502d00a288051402e442641e1b0f1700d5060010504140014a01e96070155045c40c1a0600760799000c8094848100c040ca8034803100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 373862257 1250 373861007 373861027
    0x181b2407050a0c0e0901050f06130b190303080c070c0303031e09050705030c030307020f04110f04060503010f080d020a060b01030f0501091d0d0e090c0403060e010b04060603020717 79
    0x28021880302810358030030001c0020412500e00c2e03058003501c0394091418180d50b140030003582a074008070b5003918141e4012003c10b0719800e0079040810141d00c1c420010078000600408a010f401d20821000d01c880040a410014950028484c0750400b1a0021061400829440e20542c511440c071005041694607440c148c481d000d650300f0303082d0031182058244201082824040d40c0c540c050f009092090040090b003609a203000022141069030183c24112615184400c10008286403081c440207048100715600650180704014805801c0f1030702d440b0b881c2d50404203000001803040d0000b02d1700d0b905c02c405000003a0340004d6030407102c580c00f440101f4104a420300403805007020943c0e407241107007420008507044e8510b1300941d0320b1460440c91504c1041d0600419561021030100c184040303694007050592074180344001984c40008405d4041c41d05581c2c0d680ca03000c0704c003904101c0420b030f550740e0741c084003a181900680000b85545e10341541889019111108900b0700f0702c0304023495010004001c440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 373863507 1250 373862257 373862329
    0x1141014031311030a111c0b0403020a050d0806180702030d09150b060f07030e01030b0913050c03160509101d15220f14181b 55
    0x40d04821140035481c1c1c280102250000781445004888030740c10b00210301498200000c00d400c3d240d80040790344240e59410000d00c51550aa80415415200151341440c0420003001480340035901c29402400c9004690070682e08042c040c1c04e0310b4040103409424804a0790300e10410b5002003121020341c0e00652903401e416803031480350022011090b4180a028028010740001800400c41400c0c410701c89408440300308403807445200708038010100103200b0003003c02d2140e41c41810203c0107050000341480c0400000d2004c407022160254403003920b9048004109040c460307111000070130303001080750030120700c10107022407000d00445010310003407000030340394802100e030401c01002500c64200c1c2c03d5086030422508080300311884105c0000800400400c0d0418190381049000d6054425000c62152441a40500b92400e60040c44c15150120303401071440ba542254010342e070343d2915103110740442400508002940500600308550507141c4a035a40f10070300b050306442c0d254a515a243c42244200d140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 373864757 1250 373863507 373863527
    0x1030e0a051204081209462301020325020405330303190c0c060923330c030901030605120a080904020f03090303040201030b09011410 59
    0x120707521038401c11034468450100104252242ea2041c1d03a150020480c4843e21845401e551a4001a042e0400001c0c4103207440088011300150180e0440a6507103081011342103220500c698400c080c03c00100442940c100c0c5104407501e00340c240000c1541d221001039164082d00300c0c42c01e4190110301c141010310700492005100942c1c0144100240d040103501c4100c6000d003218030030100f030028425a24904098410f1803d201d50003001185440000d207410300ea00401801810144030000710000c0c005445a409c0310054019551041403461505025030650f585a0400c51b0715040404010a10b0fa00d03102010502641040e850074801150500000b0b85180fa03c4481c0c18a00c5001c503901c03030101008402030030809426031781407028649038000c1040b0562428a00a4581d1103120000e00041540c0b02402050703500600060403e0b0020303050b02c1e410f600890701c807030140c3c000008000440d0b0701441150403840007928031000641c10307c00c403a020046450710071807041c0e240c00401e05905114846c440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 373866007 1250 373864757 373864763
    0x504051b070b010f06080405100c0c06180c05040b0a0b1e04080a030f170708040305090a0e06090a05060a030602180d15240501110a1a150904030e01030e0a 68
    0x3a0741c4001e10b0420050040e0280182d1300030700f0f080302c00003071404c0c03040702c0756030246400c54050035041100251050040c0383c420244411300810a0300300700852a2485540b030203107841244c0c2005c4090700d00e070880c010601a00154856460003a0005098407030080d40300c00d60f03e00010321681c1c0c10040c0c410711406595200380f803004040c0003070042210307840456006249031181c0c0751501007210030301050302c1d211425102d4050301c201620001c0c1c2020b01c59138000c0d41007806802e100b46400803090100e2088421a00b04a580c00c60700d1060043c9030900c0038115034400251a0200000e0130100002846241d06d03101c050003942d0040703412000c0e402c000c1441e03080c03000d0092201001403098601581090300350400400c100b803400c40c10641e0499400e00164a048040d009110400d0034940107681a0302d048491007541c3c4075508003100001c6140710522a044408041500e0601c2e100f0f440c0c10b001c4000914090050030f00405010020b03401174040c600c510000d003404950040804821490000030507009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 373867257 1250 373866007 373866061
    0x3030f0603020406081f0504121808010509070608010b090d230607110f1b01050a030e0f0309030d050f031902070c0e06030106120c0b0c0f010c170105040b0a050405 72
    0x1881203000074203910003406c0302403000244444200071074100c410031203000d0f01c0703c407403004d05400c401d104541524018140304d441c44662602c81c90b0850854100f15038028480e445100e040c40540d4105a2a90040c465680f40e1071402e52403070003290054070448002089803c00c0300996a0046607444031a4000010000311106860010402030a00c0e80c00c0400c4da0141c01401d82c2c0c09842807010480c0c1c04103109070458680781c400850011200d07a0310090700b0004041d41c0320410780c1c240e82c05001c50038955030721400031a1203000076010941410f5a4050407024410100701c40180c100805090f44d0f445440d00008040842c4008520b0b0068810490001d00c50350481741d0108103614824295402000d00350000c011007030700c5010088103007007240300107000904505420460f1800400c0148031032203005003501c618082440308107094074840800d00010922020404402c0881c800034940181b20455091000000040200d1000100340c01a2070107142c4902c0050781c03820394504103140311980302c0c01c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 373868507 1250 373867257 373867259
    0x3051510150504060e0904020d021002030c060f01050a0609300f060606080112020303190e03060906040b0703060e1311060d0b040b10050a050c120c030c15070c03030f0603020406 78
    0x410a60050050350301003600300800e1179450504a4015118540c00f4220360012520764080007000c01148042004500c000c0210003405c0348184200341c003480411200c03010a5050404000f50002c854200c1c0d010445c0445082040c40c1c1007622013002400d0303960b0b490444086400c1c120100b02000c42014002010460303207a401c1100c50b50214044400d59030710032100d0f0b44c81e8140044080a188006035040d8000c2c440542411514480584480300310704107550b842048101090900c1811540c3c0340c026000742041100344544c100420f58001c8592404215190a111009244000192040b100180e01d0300344501002034000c100c1c403040c44020b042c00d0312000324400c10380140000c400118001e50804106134482e00b008000b50090031017603260750342021441001261582c2140c00e8080130380c4100049010040c200c0f1005001448480000d0f555071075200704090718100e00018107445100d0318208100e5841d610210700c27100654180b0300420403085003070741c80000c3e0126400180d807061078080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 373869757 1250 373868507 373868549
    0x30f0a0e0102100b1e19060206010303020c0306071d04090b0108010917030f0105060304110a140120100c050408060a0219030203150f1c0803070e060403051510 70
    0x103840c64004400740e084801c88060911101c065038084680242c012420070f10603409410109910782030344002511400a140d41d6100742d03a4a002150300c001c000d88c00000040c0180340e070600126156580c00d90061413242042e1308002d0010b0555040400c0a95074000324128503601e070742102881c80d402c9041400c003961148102d40c000d0042d4001161034514020440b051040b501d0f003501d10406000034142c0702c6038a018148409940001d10071203030441d00d6a5000740e155640d001500103803400e81204110814020000b40014100b560f1040c041c0d842c07102c0c98404042d0000d202e0070f0013400c0b11070108181034440b40556840c000c079049a2402e004240400000a4055001c1c0c4045417801c1180b41a10503012410f808034130055079621612290b4a850220500308080d001440040c041c0110700144610b1700041600c256250b011901d200001003406035a5500c0407140d040f56008880300c2e45864659500d4036038502d21132171112000c45030800025084001841290010544540200070381c0345080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 373871007 1250 373869757 373869767
    0x40b09061803151005010819110c030d0917090306010b0d0609050c0c0706140d150b031305010e121603030e030c011422060b030102040b040f15080709030b09030f0a 72
    0x135440900c0009090f0b000070207610900742c40b401101c00100303255400825201404c064030a40c0d503000641e003001c11441c0380f40c2204000a082a11300080000382014030351030559070360703a882e090402c0c01d4a02404100d0f02507030007280a5045501280c1c03040d94035000620b0b9a0003030b002960225036290b10704401c00501560510040c0728082020301960a80350311440c0690341c080b009092014801000d12186801d0b000030341c132840441c0c109022500e6420350358140003201e90700c01c030b50100849525021241c00c201e0240a02e40c110702078071004e80b400025013011058075000354220041490b0207800303050107160081c0d0044440d41c0c0b82c84c2c1a20341e9003c01030507480c00b0304041a03141c00b41218203000100410580394211040f26189485009090250f0301c0d200041c10001b11043d40c1950f0030440050130004013002040100b2001c8050815649040d060407041c2e140400c0304811b0107000e50030403040c10307441038681058070351007004040d40b900c40f40030091850264122040d07409000083c0308030459008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 373872257 1250 373871007 373871011
    0x30105040c0207060f11011b0e1306080307080912060f0f010609030f0312110a02070e0f040804030f050703050d0c1112100c030f0c0806031002040b0906180315 70
    0x291828001d6511140c01240d480c0c819200e414000f5801e0400c10007542c4c41507041d9070150300b91800100380500d4140480711981244240c0c0b4011a03403105ca16809420540c230000014007500c102042900c1c40c11000d1900c92081c0c201c0100900800250f118440c0e44004506604d1803251080310301a2404509030311540f2805e07503485036070303060100c00010f2a41c46075500034182ca5100d40c256084d02100d590643d021107650089030f010b00d8817110010700b20b01018001d0000c06000380d004242c0285412012800c07030358003030704034040b40e01c8082c00c200100d2461000c850440e503021065490031820707800d0850408260350801880740c0505202070750703016032190000c1180b40c020603444500040a1040001c1c1702542c00062001380c00984440d8600b0049504c50301c46c4600b1401c0c003181c003c5d11008190102c03040600c0e00300c0481c02140a0001e2402c040080c0010580005c4013140f9050801605c58000d0042c490f595200c0c210000e0f800141202d2416800c0301e825014044440241107690307884044002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 373873507 1250 373872257 373872259
    0x30c0714061f080c010509010c030c0f03081602071505130f0b030a05160e0616020a1214060415020304030e040e0105070e060708030f100305060406060515090303030f041506060203030105 82
    0x50b100c000301d464100480c56512800c3c0503151141340c0007030000155441d10f000d01c015014001d840001c0804607207542d0f10a8055442540d510305d080c0340641d41d04030040c2880e40e15170110b610005043c800b614807442e08240d0040b240c03c1c801d45400d8166001294500310760060401350741e010b40009079800700c0b40040c0d4061512924140629512004540660aa445594400140c00e00e45003542400c091000b080d1164030103084114a018507004251600c42d203030f0108500c00540c1e2071200a012001d17040703440f140301e2a0050301450034142ca8a131140304800340e0150105500201013410580030314040b8480401c040c006000d100c400c100c24500900c0d0840349000400d803e180c0c048030340d1500a040f1010564050b02c15411078891842c036003181040102841e90301d4201120200118a041203041c2c8118451a40410100d00b401d007880406503c4d020f031401201008d100e03c11443e9004030540c0e60044408541540aa80d582803d80c406c003103034a80300780070f645400804190181c0c04802107058841c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 373874757 1250 373873507 373873561
    0xf090a05040b091f090e0a0c14030a060509031b031803030301062106030602121803121609270b091e04140d030c1112030c071406 57
    0x15a400911040d19110382c40103038400040f40015014111401040006940e558440c0256940300c800240c129100001d000c2c06540c40000c1c06400c00141c00010310241044140404002c901d410200c2e80e203107000303280104110b8540d00024855202042501c2d200d4030104901c2d044d400c20300c44050f49a034800040c1140d400310074101d0440368180082164101da42d140c1c0c4003a00c500d1a081c580104000e0b01200340341480d11841c002002c590980041c00030006034620109150408d02c09902c030390404020361000c0c0f03410500c11007441c00712501034580d2001650303e45014011801000b02d403841c01c15003144c9020002e1140010310120079012014070384042001c10416000c01008001081d60202c80d24181c4080e5a9400000030900340d911540107846290b81d0561041c4806101d4100f0f06da800040c00040c2d5105040103e0716406640c20011103070100141c449881d0307009080304244002010f52a111000242e810100000042c1c05000c68507a1029030b0918142610f480c142c030b20300da41090a40c20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 373876007 1250 373874757 373874759
    0x10e060405090609030a050c2a0a06020a02010203030a0f1401090501060909181e0602270d02010c1211060f0603010c11030a210219020f0705180604020f0f090a 70
    0x54400903c00d8000c000d03480080d820b2840130300c0100d901d544410b000070120b00a0000c801000002030708407014403998003101c92005d40c00882400f901405030340c011001c550060340c8410150740c01004594004003450b10104000c4c2010b140c001c0a440408107a004017000a000040c0303403c0a640124143d624aa44410300540d94511144c140c0303a41040754007680c12002c0c0c11000040796840050013060152581280b038400c6512144200d0b00030180c6d1000224942c0306803e0106031044103c8605070040312802d004c4601500001c0810b2203208004020300303030f108000700e0098060340c1b0508101c914002142e400b89490420308110a500351059402903080100043e900c502521490384080c40000c000c5050401c484011075280b015090700107200d80701c4508600c407a006500081103107989803482c8028051070301400078580108155001c00c181c100200900c003655500c004826114059900381d191619000c00007002031045448d00402c3c82d800080c00219407500c3d81c040c0401c01d001303c0780c516a032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 373877257 1250 373876007 373876021
    0x308071103071703030a02070318031212090b0f0709080d0c020405010b03010515090a0b27010e0307030305030a021b150f010b0a03050a0e0d2a050c0d030c0b010e060405 74
    0x5910116600303c0700750400e10009401c901d085d03025002050181c0342c0085010307026a00100b005005030400c0d201039030584504c041071a0001d07842c404100205c8010094001c86486d01d07502d00c0c0c0e000c1e011034034001c03040b4089400f1500c6904000701400081050741d5070f0400280e03002d001c2a04a1034202d014034249800020b580d80c1d080c003900c0c1212806032204400868000c0c82d250503600054030700d58040c0c01001e0100301119402d01070440b40301d403403040c2c440008040740c2c201d1071000000300c0c0c2410000c5090803a0569200428076100300c9505080c0551652a0344602401034050340500450420700410a01310580c00003555100c00030040840740002d031918841d18030b1844d024040d03882d4600c0100005c400c00c41c46036115a9203c001d150001131543c40f9203800d14107120040c41c1040015240240425034100c180c3c60003090f00c581c1200312080c02c0055600c26844881540340248140103035a421b20505016008001e040c40d80450b07668200d68691507100300702e10050b0b0f642409689400001a08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 373878507 1250 373877257 373877279
    0x40e0121150f0b0a050d1b1a2503021011040504090c21020f090601020f01060e0a060f2412111c090f0213021c0b0312030f07030213030807110307 64
    0x17550006031800075540700c06e40314400d150842c8003410103102a040000101644401f0040e407084d10b021180c1c1d40d44240c0140d54000320211258200c3e030701202e14001c94002a00000d40922043e1107010101c0e40b540040301415441c012644030641160800381034000304445000c03810309443c3e81c1d400c50102c03840c5081100c4851a40d40000a400450203401140d140c030381005034642c40a4148120780d24854202001420344030554400e180c1e40142c5000c1c0f040c0f07002c0078098540900290a07240c009289007991440c108080102c80e04c480403450b0306c03c2c0006078400d411248080410b06007e22804e402030001c080207a01601e030000880f0003102c41003c200b22240102010380e03401042c107001c9014540c007000030090110301e03d10b0f51035500b00804001940700144604103803410301000a400d04604003030505003103941040e4484020704104000100e0f0710040b40d660409040c0c0740068a40030240d60100c60300c5119003024299500c08105201008065030350129a50340c2070301034030000350361402c581c21 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 373879757 1250 373878507 373878509
    0x10e0d08010303080c072a0504110a051c0917070213060b0a03050601120c020609100504150c05090a090221240a030f0b0106020d05040e0121150f0b0a 66
    0x1001a0b06a000b0660084442c0051b0103028051000600310000c44414503a21206450030b80d0180a14842c0c1000245090312810411061010070f0f14908030088800400354810700f52a04440f441e20320f0074481d1003580b070b413103410820380c03101c08298030600c00c80100318581c11615003207208144000102d5042e1160380a00400c441c42007810b141000c504500660162100030005030410039444031280701101a401402006038154000e01290f0820560f040e0800107003c601031561400e05050100240050201e100351980ca0100025039081e10882214030340302e80c079041c1f03920071003180c0c004c201011164000c001d0314001c00b003c0f0a0b02c008100c0654004101160f011002c2660350a000c15115007401c1c2007981184001d01b80f4910b60344940ea02d2710b00d110010410341d0705402e46401402081d030100100c0f0032121650800d00d00705440d00d040026138220500070344003031184d100032403a588210300640200442e44900c03c0012035003c0c0000c100105a041300102d901e508200710f003481d40c10b008482e40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 373881007 1250 373879757 373879763
    0x4080d05130206040b0a0e1c0201090504020a05160c153606030b040608100204170610051201020c010e0d1b050d0809160306020a030e06280b0a08010e0d080103 70
    0x1070602d40b030000205c44070342000400c40c040c4900010506903c2c1c0d0b900c0702e5840d81d0281d44800b00004912400010b01c0c0111039040390340100d104200c1d1710b2070b554001040c0c80c0326581c2600c0c0d8850321510703860310405007041da1384030003400c18503800d05c0c0d81c031950000c5218014043c2c841d40040190200030443d6031030500c0c0c441000c0c0d031340c9010700248000c40c0310780c218254100d000b500204085581e881d4030761808880c00d40f1480d2080e408201880700c0c0c140001c10703c8902a502004150b9400d10410b001c1e020056882003e2180740350300740e0404100e500390140c40c40d1043e800001c101c41d0084480058070354014083e40710010710f21164507108820304801404d88642c00c03d00505210005500a40e0041400b60036511f041c403c2d5281c0c0c000340031440f542c07580514444c54001d030711202c41c0c40000c0d040c3c0c3c1d0150403640640d04600c0800c81d0b1800590a2410100d0140050545031184c01c0f41e007070020b009102806811000e25070300800d101c0e00c1500304004d20b0800000315095042840011501d51400b80802 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 373882257 1250 373881007 373881019
    0x61e031c200d0914010e030f060708070804051f0e0102030f1006090810020f040312020c040b0d020640030c08010209150a03020909010e040501050c0306030a060f09080304080d051302 80
    0x91190340d00d8580d6100c0084c0041c1040d4480022650000c1d00c0d1403041c2d200d080c40d561051040140f801c1c1d024440301d8001506091485039410b00d07541d80c43d1500c0a1059205400d80c3d000340418540c0ca03150000300f90001400c000b1966401c00a00641038241c0860b41410311030400c540008110b4401d16403002100c000402401300c25004c0b20803000a580032030102c0c080ca48c070074000032012030f2544040e16812075854004150714100e84081c001950912640c1c0e074030a0391440e00c20405030b2580011910000c4c582d803c00c10149001021074001074010784501c0880032407010100364201401e0b0f4000c000d880c05aa04060100e980e9454982170b449a04410340d0080308171008480c2091111005c0c003149a02424054141f10501001c0350308185c090f844012500d1100c400d0000b403190030712902e40c01c084118002451840c0c2032020a660311460a0300501c0103913100d40041002d6565404000e030241d000031103a60328102400c0c030b107003250000c1071500c12071440d00740810090f141c064181c10380103a001e000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 373883507 1250 373882257 373882259
    0x601022503110d0c06080f090a0c3f0204050c07020d081c05070f03180305041701020d14060a140a03080304060f0518010b09061e031c200d09 62
    0x640b1007002060303036829003120150801e034000a2040e10031101401d020740d00ca0600b49403640541ca4005406440f01a0b01c0e042840e18402050481d040305040d5803031440f08182058880d444032500c3e40400c4400d0a5a4006142c9030400f0084182e4200c000d80c0220b806000c02c0d210103e60540e02e20507003400950041c984145000003c01e80d40151691100d00c05041c001440d0b4400c409040e581c0c00c45190300010462450400003d415204400641c0f038107210200002556a801a000388214007507901130f40c0d802d055022061009404951090072810018840008000059480828181c1e5903d120700d0710f94001240c08644210a10100d12000b810b1406061443e140c07008e255002070710a41d00e1030f03151000b0f10401146405118018080c072205c51203104c401e0700710705007150407440050748200900018080283e60301d03d200380641c8943c0d03d65940484a900009140101c1c14024080141e410783c0c0703030902c540d08010a035820305517104000c810154401c1e00716484040201250001c1002c10340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 373884757 1250 373883507 373883513
    0x213060912030c02060c03070b040c240509060c01060308040501031407081308070f030806010f1704020402131d19020405030a202107170a060f090215030601022503 72
    0x60110f44060000c1d0881b454140c03907000081c01c0d6445210f090f21070080810034001000300d40316001005208042c5603c00426000349044000048504070360100800400d4015044d030700c2004403503491141d003000b00800f40d03076890708001c2c982192241c14040b03890500c21443c0c44060b1030086125030b045540314000340d914490f195000d068003207030540d10000140076038000945030115007880203001c2d4403000010300e0b142000402d802a40b484510810055a132810741c80c1805403410ee8200c2da04680260321556043d8203c400c03110190b0080d10040400c4007035a00c44003d440c841c4c1d0203011070402d0a19120580d03400d040c01d0b4402da22403140c040c1d00c01041e80c00411000020f602e5902d02003031000781d00340c1c00c00d00042d40150700051607880a0a08850395455604c041001400804040d4140d82c11011406442c5480c0c144042015110544540ca405503007016980840d501640c02050304000c1d56800300e001f14280c1044810601502c60030451304510042c854006d070102d920100c0e4913240f03d0440ea = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 373886007 1250 373884757 373884767
    0x60f0f120303060f0303030b1003150b0714121305060403020d081815091f05030f0c0405090106090612140a090311010e030a1d150c030705010e01021306091203 70
    0x900381c080640e620720208612103407441010003140a590007280b01c0217001e080040741700544e6044010f0526022400c4589012026450111102c20044684130101c600b40f001310b0105121000c1001d0041245001c45104428042d0014007030120035021420388900a0100d81e200704c2c0000f80d44020000c0041700024001c00040c980e40a054440d0000d140752800410707002d41840c841d00e2140305020820b841581007090100b0700110180780508000692410003405a2002400324041e1051900028003000c00040c1101c1c0101f201078040030096030760f00b2009002c26200c1c06103c0008010200c8220080380d140540002c0742482c5840c5142c83d1500407100000717020030303d01281400750124119000d88428801c200c01c40c1e11000245a40e001d401310010030301c14002c071503030742500c888078054142c0b0b44515024024100103441110f60b6040c404201030b14502409034000e00c2c0e5803d00c8503560348040190041e100d043c44c411480b501142d112102600c0d2582c0a00420203800c518641c80d401280c407038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 373887257 1250 373886007 373886039
    0x20705060f07050109060507030e15041103190359130203011403060106080406090c0b0d090b0a330e151804211103041404060f0f 57
    0x7114a149040a039941d41400d41e03d03c000c0c2650115a20420000c4440e00340c0180c4542c605608040c02c071022002e51000b03114030020b017014100d03159910240700513450400010749034080083d0a00366007603282c0b80003020031384541d5a80d004905400c01582c00181c021aa00d0754001518565518134003550404100c1110802d0719281c1c1c030648181d04080c5915558a04000c07800b4080300540e0f0ba40c102180400d882c1c651240d028025405440104030042c0d110010700e4010f030f446400422000e48508041d126485650004124100c0010300200d002000d42e20000c0700501c9a000c4800d03507036440030402d04a40100344d40c00110006800001400c0d4010fa0060300d02551a606211074a500d81c88001481c00e400c96110f10349092000d0324017041d1a202d900c441603040c4080305080c2c585480e5480316840c0402c2908103090403a01d90030554801d0241b01c04038004000502140d0b00c2d1541e4007650380b00038030f041d0b0402c0e0040303140c0304000c500c50540c000c6000603900c41003440400e003454515090f80c90100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 373888507 1250 373887257 373887277
    0x207020f0f190602071707030519020409121e02060105180c040e09030a020f0c1f2c040b0d0b0714070c060c0614090c130209030d0810060f02070506 65
    0x44500480c444000045002c094402d90f402417003281d0034401d00c0c0f0703107042c0645030f00381031540080400c04c0002c0c00064444250325214a1070000491284080340251540150040c4410300070400d202411380d10000703a401c43c119040c00c104450f4217400d4240d072580380038064190060407040714003035260010581c0303e0f084080e80c0c5800380b801d50740c0ca0703241140340403e6807c05115000007600018175070b03040001c6d42100440303001070541c0107902c00014040079410b145003680da40001c404603003441e02070092403001580b5101e206030821440750003a204041c03408251072040349841d041c00e0f010b00300300100d01c0c03186500601c0450161a80603007982c040c0c1468001034925002000102d0004e109083c5042c01004503444070304814410349000e00594070601d0300c800d0030510000420940f100000341e51030305100191000e011005d83c01000303001034480c4000c0c4940520070140001c0c0c502d58411002c9200e2200d981c250310b261602c892084519000c8050070a00603031080c91b051015241800c010650255 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 373889757 1250 373888507 373888519
    0x1302030303070513031403070506010b0306010503010302011d03120c19080a0c0c0305030406080a060902070314090d0c0e06040c0c050c09100806090f0c0f01050315010314010b19030207020f0f 84
    0x5038070350b25091b4040452900410940021844030100700041004501404000c0c0c3c16034113610740840002c0c00c600052001070304010150b42c4080f5a000441c1c0703a03c070119000340035140b0034001c20544405a0b07018210000303240c410781408921906070788068000c460b6001e580d072131501e0300c6010100c1e41d41c0c0d1884400da0321403907119400070000e98200000e000600b283d03140e0780340520740620304800725a01c42d405040007500401085000039400620101007103280544592210710210102e4400f40d0081e44c0100301c4480f500c0c001c0740206d18030f0320b61442070008a409100c04410b2900031100300350074200052543d44612089036452408810241d8080b1b010140038000d10b5542501510b040c00549000344560011410510361410a00a41c062450280c4016101803a8000020998800240010440d040c08142000c250303100307402c14a002c0340703140002c0c449541c66401284a07a0701210036035601100005c21042d446009000303580c1c542d0340040c03200c949004494144a908800d81040340d42c010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 373891007 1250 373889757 373889759
    0x1415090d050f070801090c1d040201120e030d06140604060c0f0533011505040306020c07080111220302060414041b0338120a06060e06091302030303070513 68
    0x103200f0022900101a00c4d00081200703041420000000300490304402010340b8040d00c6c40c4410016551500c0e081542071800c0e018036514079080790001d003511a410340c12400006180805e110f030540010064607241d03803034207905c800420108145407040f44164030120700101404004224507180c461811070060381a2041c40c499601541224402d4603418000c0c15101180c3c50403121210030707001e026003c010a034184d20412008d0183c018000c6200042c0021303000602c03012688000d00021300189100c10080c04016518580c81d102504001c1d40c56100d20149001040222001c111000450360054489880d013800d0000c0d0424003480140c03003581098447c10036401042080d070540c540c50342c07035580c001070111204051015218240c0c81c2c200d0a6601d080a1303d045800410205003c8407084855005118141942e1400c00e07011210140207545066000107000c80000810b40c40b400c01181c0e014015a20b42d00410203006085e41e0181d0550300510000307c149000314000c14045201906100300c003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 373892257 1250 373891007 373891033
    0x2120c010e10031104180e070e180a0c090212090c0d03030b03210d0c110616020a0b04060f05070512010612090c0f150c03020a1101120c091415090d05 66
    0x3c5ea10661000d1280c0e28001c201104032481840b6486006132001c0141c07944a00e17000701c11f00e8541001d000c2e48652848155500b40800c802c018150341249e00610348181d465881c0d403240c00a4110000e05c41070069039800040b183d02c008103445040300c0700200307110307400120307500d04500030300b4100b540c0ba4051141208054041190103624050600546170361070b0380700d103001c140109a9507100240350500014000d6072010810209006500c0b403251510014185003825080b8a0041000e002400d00c480d0101448144a41600400020f0305038220521090300c0700c400484807449081c503205220302e00343c0d00510400d4890504040001c83c03440010440c11401e440b1100e11610075441100c0407190400104502c10740100d9004507440706013880440800c40303450180d2036029162005000c1c00300c907880100d49a0080b0300ea840b500d20741400806c2f40c1e409060340038140300c43c0b9018501c43c02a5500480030360703180880d0210b4488446042203402e00504c0c41c140034000340241e4048681d4010505001a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 373893507 1250 373892257 373892291
    0x6060f080d200f0d0e01031104120303140901060e1005060a0f02100e0303010503120c030a050901020115060f0206010b030709050f04020903010203040305040f0506040308040b030a240302120c010e1003 88
    0xa60348180d002d40f01d40c20200384007178600415240c40c02c1c18035040911180701404400142c038125680200d0309180003403946012401041c82c1304800b1400c1e00c0041c2130042c03030441544440b054440c590528903c030380300c451516624407421304c1280c0c3e014900f0450118811701c5820060150081401214650200ca2072032809880c1c494005041da43c1c4007200400642c43e08003e1440d011410003451032038211840369254882c8200c401120601030b0003c0e218400343d100f503000b1049190800340b1a296140c40c1c58008001c0e0140d1078002c001813040c0c0780042000c01d00344040b60301426164131007500c03561a0038103109282c00022a103550103603081c440303222151020300085100714803da889950f283e04205a42080310317a5500243d015040510040c800214110300300c40c1a42c8060306100d489954104001c2d0141003031040080392038640350311100c45004078071020f83c1682d20031208403048000003400d10341d5804091350b0081c0064410b140d80c0001e41080320404403240e62510700071480c1c0d000c3d1411086 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 373894757 1250 373893507 373893523
    0xe04170324042a12060f030f1a040c060815100c02120601031a010b1e09120a06050601030c020303100b0c030d061211040216060225050a06060f080d20 66
    0x25891401180402030f0f50f4001050340021802207410040355081c030000e8114054180002466480800803010a200030b60300d0200c80e04a00131000c1d0b115141c280780c00c40501105228140104140d880450144003101001c0d0b13003402c201510201d545078144400300c4070440340f0403080c3d0704076018101840510a080c40300341e000c1c40c02440511703d595000103c103140e03404142d010b00c0300c0b41010f020b05107024100f880301085e40e5044018694542480f080001c0c101c010300c1c13561300c0562180d1a1803504010031500050320914090300d00700700107103641340300340c2c2c4030b2108840d801514112984140f00703440e8840003030540e2083c2d070000c49040071800e50040b02207400a4006200c0002c02c0c040d080308001304e6858040b8a501c056074158203048600144155003010b11400419094012918070599408100881d50060b100030705081994000e041442e107030304092030262009402c1240220302c6008540720f1408440103c0003c2c0080403000e01c04071181d4251503007a017560014521000039030101040380340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 373896007 1250 373894757 373894811
    0xb06090c04260c061207030519181b0e06060d02090a0e0f060103020c060f040312020f041a07020a030305030c041211030d1b14070308040e0417032404 66
    0x103442c4140c8000d1a070f1810164010191181000300440d10a1070a59038150750000c103c0d09000c0380c01d86444902900408160440d00700a524003007004411190711190140214004c04401030001503042c030081c01401e081c0611064111048d01040007400d140d001004203040d0068018203281d41d42000801005013503015075910b640d482c083c8064004049059500100242411460b0000d2484035a845030002048200c0383d41c1c2c0100044c0c1418050307010000c0242101908560b2110307601c440540581042c040c802491480195049502c4c84201c12500c00d81e40040080c0445444c5980440d4207910040c04003041d0310043c4400102e030140e42042d4492a80300e407080b91310003907080040c0740c41c0080c4440d2480c1000f1401348080210b0714004210019250084006c400d43c540f00880d16240c0b0384e4640c0020254140000d002410340c80c03c00f61207014a100318910f80400044284010090005a8158038181444000e034400381c034452622055141c006030002c40e40002d03000300c407025001c0540c400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 373897257 1250 373896007 373896059
    0x30c150e070f06030b0906040c200304240206010e15040627050106090b09060f042c010303022d0616110114040f03050d05131401090b06090c04 63
    0xc0c0071000041003031901802c00d031300d030421009540c240081d650071000b030030080c001d5981d6070710380c405540329112145c620030008030043d40b075644e680803041e42e070741c0035114554542c0070035141034a1483e60503810398010304196005014590800e088420031500c081c0c40c0081c50800160f6401003a112801144014414501242c917684042050250384180740928000c11038035000c0113012036500207050b03c0a407502c0129950300c0740224408142c10388109908103c3c10200498001898620b132360103d8400d000d203500d0b4505407482c0c040e40c40ea20b1034081c04014056000003017203120040d5001c80d81c21900101c010940104051440014102841502d0b084e81c00707440e0340000d076503040d00a03100405090307840000704002ca11821103101d0800d0003500007000c110a4032800d1040c58801e4044d41c00d10364500408025504040090a0120455030000c031035005603e22041200ea006118420846410840b94103003a5108c004014840398020400c3c0380c5d80406210108845242d0183c00016012403039070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 373898507 1250 373897257 373897259
    0x1a03180a1101030c110a030809032503090501080903160303060513050703060506120a0b01030b0a0e010503060c120711030c070b040f05040203071209240218040b01020a030c150e07 79
    0x4040c0d80d13112611509110070039512030308401002030038009140d0035250442c0e9540701c4500c1e55045100c1c3d032490254400e050b04891402c1c207580303001c450f8024825150b550001e80c1c0c0d0741c01903e06000c12942c460382d5820502c0040d40003510103403044503c40c442d05e0f000501310b45940000d018600d50020512405a54030200b002035509842540090001120401e06200d0514200816000000c10340000b00b40c855441407040e9000344c002e140040740c02449041850340703400c00d20585a034240b10b1181300e8402e950120b0ba82c124114111012040c0b42e41c9008035581e10360304c01b80d8840d9581e011089540c4070422024040c018280041b0000d40603000c8010398031032030308000b688000d5460b00910700ca41d2040080c0401d0300e41041a801e541c500700c070030100700403005080c1040300389801d5001d0690400d1124403800c4c2c614003580144100301080e414250b200603440e040c04201c9000c2501540076901116840000c00d002d00003090110b485440040b0f0810910400302095502c460308400e41640f00d03104c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 373899757 1250 373898507 373898509
    0x90504060e0711070513020f0d05040f052a123f0406090314010b090f0702100c12110f13030c1a040905060d0210180e011a03180a11 58
    0xc3c080e40d030300402c1c02002c8560900d00081c0d0011059045140d000e40d0001f810200d18920805443d0343d10780700780c0204400e1405042682a2100c044030071582402040b050f03150b40502c85c141c002d8141c411a214194130b08401c03040c03046002c43c45904121a10505c08180224003451000940c0c242e840341280c6695413400005810b1704580f0344964001d94010f1005004a5a002207801e084a4001c00000f00c860842c074212401000166010b6070402400010051006082c1c0c8440d8000c00d003683c2182e4401d40084418000c842d101c202e403000244441442424030602c0f80c0010210500c5280901d1402c103020404000710750000d02c03038090b04031041000700107101407070040000402020040c190312500916100070503100f14084d100140381d8540c041141511600c0400661a90240c0003001c245140ca501400441e546c694500051030f5500c00410312500010005048401c030004602801161142c10f01142d000107046050640e8040c040310768602082000c845076600524000318640403840c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 373901007 1250 373899757 373899767
    0xb120a1d2a010201060b090d0812091e16030206090a09060e010e010e0106020709110c030703032406020307060e0a02030303040303061503111b120705030c01051308031501090504060e07 81
    0x921076415a490003c0401009010340219007892004581610500c00d0600c2c010303015000c1e52051040c1d0304e401e107082005411000a651100031750b10f01c0040c54440100d41c842e550391000e4008101d203000d44580c10801800c10b20050181ca601c000c24000a081d00c5013118012030b40c090384001d00b03845620340100300ca15046900c1c0f9000d0b01050704c001c60f04d5810400080e40c3d070f060905c6550511952000001450208001980c5506451034240c81e070358051402d000703010740030700651144d9482800303011450b004d00c4d0384002012601c4c0394000c0c1d0b05082c0340d52160390042c881104143c046000c1e0000b030750016039091000b1849148a81c60000d00c003424140400c001d445401014003d040c580460f5081d546100400c2c1d8040041e1000e180e0a0807640c11051401d141480c0f190f03990380321010a0303480c10000088082d200d01c45c0a07100030050ba60303800e4003003282c8134501200034003115020000318614100c65803004140070410f0410841c500d66500200c1c0440701113034001000c1000200074052100d500c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 373902257 1250 373901007 373901083
    0x1502070e0f06090118110a1d01030203060d0212151e0a0b010504030602071505010803070201020c0a0f03020d03020102121302040e0c060a0302091302041401090b120a1d 74
    0x581040001d45041400b09000141c18014100411242200000c0ea0100d54000c98400300640480c0c40d01c425107440d0140094400600e010442e14810b82c808015510901c25a442104004c4c9220404100d036003c2c042d0140008219185a01401001840007100e0139402c6000d88024a0390510704841e0350202c80740c4540c00340020310814100500b4000a030707401804d40f025250003010040c1c6c1c400321342c43c12801510390703c2400f1002d02d003072100002d02d803900071024103d110f0003a001c1e24102c0c8654402c1091140150240b501154820305080c00941000d400c0842c1c01d9100b400018688a00c0220f180c900b00c90480f101c1440c0c0c60034000400443c1054013074450400c03011001048282c00700b00004002d80180d0250030201513000c40d55a5095813000381034a8209981c59046507201e88411800c07004810020070309002c0740380400300168004204045880c03e0b141c00d541047e10392035880001c80603080303080c003a0101b02e444ea100031020800510540c1c112081c10000c2484e0584183e80c018016004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 373903507 1250 373902257 373902271
    0x306090109151401050d0603082a030a0f18030b01180b0d02010305060a030209010915050604060203040b0708040315050a0f021213021203030403020c040b040207050c090a061502070e 80
    0x2c0c845400b541802c11a0341d02d06940880c45060001c02e4503800480ba0341c040d0040b044c0c219420b020001051020341001440c00d40d0241c100c40301c12042802c900304d148120400000eaa80c0c0c4100304120300b4a01c26040d22144007030074030300300300440e541108001549000d42c00581c0c0801c002401040000c403e199490402413801205010700c0040744000b40e0f10b01c2e204a8060305041c0c940c000034025540c0c40200601559000b80340702c03201e5840c1d5880000a00c1a490780d03016a0b0088a00070401c4e00e40002900c003160019070043d4940780c18888400b03899007100f04219142003044c800800006e42d0a2116030300d22130800c50024103454808030210a030307101590b066500e60320400c01c01c44090f45100706241d21013180e2030540001c6107944080703085100c418160660314007010082c4001c0503404900a008140c088600780b146c030000c0c02c1080201d1045040080540d800420905984d042c014141503100212003000503080b640c860140d000c0365248880540147c000142c2409590350f01c00c450b0b80c104030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 373904757 1250 373903507 373903511
    0x3090d080708060114090d08030f0703060b04031412270a060c0b060303160b0403090819030305091f02041d06060906160204060603050133050904110a050306090109 72
    0xa003070502400d210740140c051410410083e064081003150344c821030711460000351106800842e107081504054102750350680302c0840300404503038401d05ca0f00568055604842440386414503541c0d40d001c0c0d40d80c54940107080d03402002c00301c0441d40b0514000d88828809005280c050640003101d0780d20510020111500c81c1c0001da0007448031a9126403207120140e48070804450b903482d100002840c501603510804001980a000c142c10008080c00040c0182e10a40f1002905a100d10700c194941c02e080806001c800b010f801040e010034443e401c0640c101e810441910a41c03128900d401c00600d54141141071002d07000681008080c50409203401039003450600d1140324108200094650300c55019620b00c87c04c800321350003191100d0841140e0203d64005c1c02000450b54503000980586000d00c544903000c818002c0e6059007000426640b4200c0300450b50300000120318000c1614280c126020309a0050342c0e412800908241080041c403820000d81c58072502c80c074119003040f1071004140c1048903064 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 373906007 1250 373904757 373904761
    0x11031905090d030c090305060103080405030f0303093c0d200705010e1305100608150f150418021b1b01081504020d0501050405100e1303020304150503090d08 69
    0x810100b00c10165242c0382c0380100783c1c200c05560803a05441139030405403c43c0280340c0000100040d000c014001c881050381a6500366081c10710f05622400111880090390f0452178500c1582c0e0304241c8000e08944c450b00d1000b074620001c1100c10246aa5043d5080d6070382d22800d100144243c02c03845641c1280c2c10151160590a814503400b51a0041882411b06000c41d0b004400e815941d070160b15541c402940e60100a0341c900203c0010800300d0328801d181c04036186402140704400810011150382d031000d001c2c0f080d0f00d28000280500d0b00b80e181c0241081c824107000100d903101043c2d03400150842c03841409a210680085030880a600c40810003009502501e046050f07011266002c000681003420f04051a42d40d0170090042d0b100c0e040d190355809840010402042c2c07290b90300250503524240c508008584e03450344910652034190017500d00844007100010074104840e0110072281384644143c07400c0c83d42d101c02c660300e10500c40c01102c001c18408001c00c5401c03071342001701811603d101e00e0590418 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 373907257 1250 373906007 373906021
    0x6040e0d0c020603090f0a1118010b0702190b0d020d1803020706050a0306211a0c0708180d0f110910050d0203120307020d0801050306010b19030e0111031905 69
    0x1103610240001c1c0030b0a00440041d0204a0900c01446c544112000f603941c5e94565142c0485141d0f00899030324461118900c41e80e10b40da805e400481d0503220500d481034a89106d903020003480000740d949010700d5a004041c0454503180500c080c0015864146001d80c650070020500c006640c0d0441506204146c0c2401010100354000b420700f0481e001c034104156280c5210700101c0142459400c00482151021400e04200c0c0b281405441e80307602408410303000109815041064103415103202713109040a00c0740e4008101c002c0014102d00c0691060a00c0e14150000070440303c41807004180c07200000004500c0901401c03403101090044200d9401500d40f400a03034580c031161850158500070700c0d51000c8801151002c000140c101c1880c29016074a03031520040007540c03030088180d030400280c244000010340e401c00080e454181c8a580c071902e41400c101c0c801000c020031000d181c103020162500e03140b10034900c0078400d101420320f0299000d6523903d010424000500045000c4107400ea2401d0108868 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 373908507 1250 373907257 373907267
    0x1b091701050f0408070606050307060c061404030e10021515120307020315040503070b04060e241b070b010b09120a030804030e03120c0a23030f1605010f0506040e0d 72
    0x480340d07004e8401511a541410050f0082c100c980000d90544101b80000c1146a0881c0310754400900c205000c1c41600c440e50a407044524058400401180d082d040c3c01e0814580800342c40001c070000d2040b907585003030300206510550425510200c0340003004480e140c29060a00302c1c0e04540200c0c070001e5182801c1e035804240e5411038170b400e0034102d41c3c1400201c1d0801409104070307007072183c008030905814201030904000400c2e468410011620641140d001003a4000b1080d00b24a58048100542540c409400a01d4604451380030580b00c3d90400910303000554280700b25000e041c42d002081c1d100d500007001d00c8450000b15070030100355030142c1100c2001030303400b000d01a403295051600613403d45004000c00c0c0f8003081014410b080041c041004d6804850000d02c0a106600484206084400b541120402070b4062514410190001c2100d4100746203508001e141f0000408800424210b417900e4070380c210b9545041e050406501c40090100c6843c0c107004411025034405d02034000041c440070058a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 373909757 1250 373908507 373908511
    0xb120c041805040f120201061e08120a11030408010207050601050105090d031419020c03060a090302030a030903090b181203040602030418020405030d020f0616080114041b091701050f 80
    0x212958554000408101c4d1100000d8009588904201d0031540c5c5c2401c00303406816039005002d51030921440070b074894030212011038202c4403654041d0127003410715403142803164003400036141441411031a03c0d001042c00c20081c801040000001a102c40491804504082041c0d000c18100002480040f6030f03542d80d45011071000ba8175040070b550b020700c0c00c0e071011601e0103504000300200c507000d658000e065801003096550703034404a0135160b0540d50941c28408031441740710040e0050f0310a000714030300140640c2c40b40c00000c1c081c1c24040e03000c503544c040315001948242c403400c5024441941c0030000303041c0000c5040700c50418002541c2042c0c14011300039540e0046119141201c2644465010303422042e50480300500340240c00d480082c10502c0d00a590b5865206c40c040302c9100e800b0014140350b5021081e00c080c4000c0743d865540700c0c0d180a94090002400f0b81e40103074440c0d0b0b00d44400c40703411240310490b82d1108041d100e000b806031800c1229014900398480d080c50a0741070408101e441007000071000c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 373911007 1250 373909757 373909799
    0xa021c1e11010c0606030803090f071a030123040218011d0618120d09030302100552090902040302090c0c10060b12010501020c010c02041d06010b120c04 67
    0x3c512001d65007400000340c4110f91014045a40000c244032034a080440c1d84a002c2098208507403c8681e00c850b00b0b03440c00503100399000300d140d00303000501c0307071254805400c0c9011120481c24004c200c81000001c0882c0e10200702441d0801c8080c20200c0b09581000040081840641e5140051f26050004c21010321a403000e038464140122040c07481640c070b480702001e00d100000c04540d10180c010300c0280c451b03181d900003900544501d200e42d00c80c1c00741c5409450311450a10040d9000080e511079404213006034500c1d0028210340400d241e00b0780d030f001410360700303d141150b86109120310658100504101d46030740042ca8a0b900422090025844044080703410290403001950b482c40c10012141c24413614a014085142c1811800144503102d800035051004072040c0010581c0d03a24001680c0d2203010080301030100350601080d80140c507040e841011030003414612a500f0070550300f16242058002d8020031000e00c0c0c081444124009020110395200520030301080c40c107420106a40b002c094042160 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 373912257 1250 373911007 373911017
    0x14030d0f031e0504020411070c05010f03020f0d1b05070b011e0509010b2104021e04061208030f0108070b03041202010f050c1801091401030e0a021c1e1101 68
    0x200c00c0644203910200c055560421108407159001040310050503050303c00303900c683d00b0903042c84003d4802c04111170529900890082d802841c1000644661004403617880c00e066092108008041c101d00c000c00a8810444001031107420880e1a043c0c099590350a44040207010b011a8000a80f0f131160941910202c41441e04141915003000b020b04a480c1c000d00d0300620314030000038030000310001404198018036842c01c0946200c0c0c04804554408a42c0071b540300080000100700e6240d5000c0d4060300800141000c0f0f03100c3e0701d42d0381450203900003000c01c64459a00208114400202c11b6600b03000d84801005000c0700d070f1819252550900010748052700756900e042415022a000750b1041482c941e034500c090101c1d20782010700003055008101340302e482400d6400245107943c1315682460135152030b0705110300c400080d44011030080600c0841c03078100c1c1c4602000000035a65020421014010081348080e140200b8600442840100c0e20501a410740c0b60740c0c403100107000fa54800380181d00c00c2ca01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 373913507 1250 373912257 373912277
    0x12304090c08070b0a030506010c020a0302040902120f0d020105090609120a050c100209040f0b15160b040506100e0c030c0c031c0219140d05060303040e07090f14030d 73
    0x4001007100303881d4442c1500d845049030001d0324040c543c02401d0850020b4808111a1b921107006448401201000030742c8400f403400c0500c0145010b5000c2a007150001d060a00d1496010600525184500000304450380c441010504030903030900949074085001c82c003628440c1818010b553380c40102601c0000c0030a4081582110244500c0545149101038012500c8038001500b0000c000e600004c00c040c0900c5c2403c40c20541c5403014020290007000103401e041d4400700480369071070641c10043c060604640080b40e200042150000303958043c174080c00181c82141040c01484540038080d1f4001d0b105c0742030f41c0c01000245580e044c207480c2c0c03103c0961718440e0740c1c1185c410000e04500c220b01c15040d0111207000e528501e034040c1c0c0d0203011110450314500c81400e00c100d40980c3c0d1651003070b0021440b081c040180300712050700c40d007105400810140072281055200d0030036142199007110885c1c00100c3c01c940030080b00310341c105181c2c000c2140c0b0103644607a01c100d40c0840d446000c0c821594081c4124409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 373914757 1250 373913507 373913513
    0x721060c11101a090f0609060102010f020d0f051e070e1c1110090e1b070f06020309010c030b010e0d050c0a060804050d09051305101d060901230409 65
    0x14011840c103000c101980c0404288030300a0005004800d44100040765681c0f000c800c42c18113405081c0504000000b8000f1591554100040050010443c904554841c62030b041c000280d400500b4845140700800314610041d480d00d10304550009105401007400211621042e094403050103421110342c2c40c2c0114201e274020003042c49920b05550010403681c10050381e40c180580d000250080480468025009407400348086904981d00d028039400400c0520105442400d1030302d81452504500348a10f051170602d44680e0b1152543c00c00680d10035400101300070701043d0a02c6092a0101c1d1420100f211035039050000304131550910b82070b07008482e00351560090040030440c01c0303a80800140410701003900d8030401421800c050b1022502c500c00c05180340c00d401e02500b11241520005811040854207460a50340904005407548000d40060f2201040105207219040c5a4000b036088104040c00d00300b09120351544142e1085940408511400e054251200d8103c42a280121800b0944024501b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 373916007 1250 373914757 373914767
    0x9060d1a1b040803070209090f0d0c0212190302010e070b0a03050a1b0302090103050901090305090d080409060902070b06100e190b07050a140a0b16020a1401020c0721060c 75
    0x3418609294000b1500040c0d43c0000401060403078030946001c85180c8400303290942e54120702424076515000708000b03804051094544445245c002040c0003c20003110326803e0401c045030119070030400030718500c80103145e02405201d0050105200a0404a00c0c0008140c2103000d10000c00781010740301c0c00491a00c03c00c9400c42020303042d040e03600c0550f0402141020b0003c1d031104e848640441d04000010300500c0042c859010103541644686c0c2c58102d44004014803555114811200880180300c041004003481c403400d0003600b0440c03170050356542181818a02034100402d510b01c00d42c0ca48000c0784402e94890390b265807001c002c0e92107000c0f503062104420f6990400341c01107a4810000f080ca4002e01c20002083d6081c14014140d4809140942800303030741711880ca0350060320340703c2030401041c1c6c0c6001c2d43c6d103130500071009841516204095a0384580f11111301440c142d0840c8c1d00410b03034081171401408818010503a520b440100c011a82c9030b07000b05484400d8002c0c2000e662690001d41c914014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 373917257 1250 373916007 373916041
    0x2100f02060c0a2601050a0807150f020a0c0e040b01091a041d1002030a060f0308070b0a0b090406060303080105040227150c070305060618040b19060603020909060d1a 73
    0x1608031880d000942c4138070304810f202c0921030b06100d2100c0b0200055400c5020038a4803c0d0740d1501c1c02202d024071b41840c2a1005803c40307446e1320841c46076140c13001c003007091191140d0192890049080c020700385410512114081a00f00e444400d1500040010848601c1040c1c00502010303038010401641d0140c0040c1c03070701090f041d00b0f1007a0152590f00c42d0182e0b6036500441c1b06000d80041081800c0d00c0f00318002555805010003881840200000c00100f83c0c0e00d040c07258040068100841e202d401360000c01e0758841c041d0390407034584e529030b9020310030503402c16401409002d0544d001c50910100344c011196503c05810245006112a4181603050b01e406c602c041d104041d07484001c0e507031034041c0f003110f80d9034401c1e10050f078a030b000b1940461040d160840240348003040340d041c0e09219490769110541104d5010740103001c0d4010280703020000e03000ca40100320080200d40c40040c1c81d0300d8040d0501841c0079004040d0fa00c00c0c2c0d52103e109001030350f030240030b044128030703440090345503640c0c2d14000c141121a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 373918507 1250 373917257 373917287
    0x608030a18090c05030f04050a0c1d0a1505040e010f021c060b18090601030b04111e04030507031707020a030605150d0c090c02151302100f02060c0a 65
    0xe400d444541d00408a14850718040780c1100801da61800320404031120644001e0005004101182c040e010f1200100c2c0c000d07000d8801d80f9100304403079481c0000700f0520b80c81200c110884000d00c2c09003001103458030381c1c0007003589000e0000381c0c1403074250490f0547c1406045e20a9598a03030425440d44250300c10140201c409000310741c0c46005440310070030031030111313844403405080840104101d01e40000361201e80c01e12003060010528098200300c6480341c000c001504041d0340d08202002603582d8000c07602c01407a100c64181da20050045a0070b1040030440b0554580d82c010017007000083d10020342d0301c2c101d0f81c0000c03c807a0716031490b441e071b06c10902c01d100307001e90312040310003003c420701c2040e51000d4011481c92044901400a040c02c0c040c0b1068080800f0307104210303440080100c40c2c11500001c2285030715106480d4007503603d9503800e00000c000e8985114803800c07c060340c800c5050101980003c800241080c06003100403200003940c8100c0100340c030309a04004210395052a018040040740c10700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 373919757 1250 373918507 373918513
    0x608060106090f06020c0f010507031b03030f0b0a0e06240301030303020d050105101205070c060612020306060d1e08191218020f061e040603060303031127040608 71
    0x603460320300802c20030442c002d103280c0b6a00841c001403c50300008210000d084040c2c00c081c0d00142102c0191195002841c080c2d090080440e00408402c070055500064140309440c00a5064402c0302075070115082e40e100ba50007141c1c4600c00340403a00041072a00e501800441c1c2c0c0d5503100c28002402142204075071412200150007100220070144c2540241103404890042004039aa0b1002040301082c00040c1c3e5030081203401d0a650110301d001e41201c1d5101c081d03410001c01c007030f116950301012074109a000010720030f000c426142c05c40c0750610100360001c03030445d5050f5010b50240c540d40e060b40c4180701c13a1009024104200c40401005200360f620101c0c80c001a0000410200e4001d8490007120710900307525440c04101900705200d0700958000303070390042d104000042240080c00b01d950f00c8401600001448100003500d010240d500070006041540c2c5c01207100c40c95450058280d54031982c00e035020079000d104800c0e46409440d010886d811100504040400206020400511841e0030900141c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 373920863 1106 373919757 373919759
    0xc020906040c09080f031305040c0801120c030204050a09051203091e0a060903110705010519121d0a0b090d05040b0703020106050a060f0e120601170106080601 70
    0x200c060911020064581c80082d00d045041602c17010a9400000c50b40d60044000103182c004000540d0f003803225849400e0b015001090500403440e510240150301c4080c006618122001107802910810032401c000300040042d21000c24241c0b820b100711b007016106680d000041700d100d110340341e0240c030701503000d072131030400403002001315501d02c0c825a55201d000c1a2148900d0000070720988551000d841700b80c2c400380c2044040c0c1c5c8194188201030010314070704444040c200c01c01030003a151440700e02c40920541c2005240b003503120088601e0090120040ba03d001941c613030038a00483c06201656590005150750b5200e07003010713100250052004000d250490405400c84a00c05e000103d0110b403140040340650081e0703030050340019030603040401401d400c841082040c1c02d080e00c9071f03039040c060707100c0e419278600e03044c8100e120320000580803d48100003944510302500c4c04c1001d41e8265 = true := by decide +kernel

theorem cover : BRFrame.Cov 373741007 373920863 := by
  have h0 := BRFrame.cov_init 373741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 373741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 373741007 ≤ n) (h2 : n < 373920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
