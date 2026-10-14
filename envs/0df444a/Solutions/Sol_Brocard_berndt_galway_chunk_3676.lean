-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3676
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:21:28.388484+00:00
-- url     : https://prove2.me/submissions/8c0c9390-2d3a-428f-af54-45e8d1e63f83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 660971223 ≤ n < 661151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 660972473 1250 660971223 660971231
    0xa20030103030e01180b0d0b040c020a150c050703050c0111070602070209090a0809210a0507170d090b0c19060506030c0a08030f0f0c0d090e24040203060105070213050a 74
    0x960040d90101d041c0c07a400404020207440a1200181405c042c2c8020740300c402000c40d030807020a010502b2148280031100050700000900e1080c84805549410318826100003080260546c81000b031a0307028240c00201040070010b007061929109402441c4c107450300c0c0001994801141c40d00900070743c48100201c2c0104c03200c800042c0d4413030020580e1400650020b41e00be24200c03240781000008607440f05900a0080c80901038026020308200d80d51059101d0030040021605113140f5400001e0070064040040c0c0c020072003114103552240f010700880d00f20308038a1303460304c0601219a080580100d0f024240e04505c142040a01044c0d400c224010b0348141d06503414a01e00c801813111207141401000255803040100411007103000c00204508803040c49181e0401c408419030a0508045000c6040010f4421405100b80581040c4180c0c100315460104c3d5941c07500711170b04005001c01d407011140704660100000f0080d0340554101c0d01840c2c4c0c02003003901ca80e100400342070002c20f425030f1041718880ca0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 660973723 1250 660972473 660972497
    0x906120c13060509010f140c121e0c0c0409060603051c090821070224090907050c0a061116060e0f0a02240d060e04020f041506080a2003010303 63
    0x180080340c0400302c060f074031501141d940d004c1c00e031f0742155030094015007150204228450700c402844210060321510002650710450040011a1000449001000603104000c442020307040050704c08c81044041e00c0128800b89181440d000400b0968000381c8140158039000300103218503a4030032000d0310551100450141c48000c0665112210075246290506400c0c1915128440002500d080c900c000e00301c0860b0050095410419600e000301980501c0f00465203015519000c0f03241a40240c152a0007802c00340059180c5644078940712b0040c100e682c3c0d58500c210310084082c210303100080c0180740840d191034241b42060050440705108507040c040c90b0740e9100315141c04220245015001084a40c44a52491070741041c0120001c4000503038138104213100f2515041c0c0602d1005141c1810800d07000d1400740144000c40c185043d0300f230f10641c94407441342f85034061022260117964543c81d10a030140c0d01d00c41d0420003404030301c140100a9540030340c107007100c2ca4008025070580380310341d491100c0d4000f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 660974973 1250 660973723 660973727
    0x3190807050a05030415020f070c120f0b0603010605040230070c032001091101020c0108040b1501110a0b011805010b04050d03020c091f23060906120c1306 68
    0x1025140c440c00600c0c00c000040c0c5031032103180a113170440e02910815107130440101912049901c0360b040030b044c003000410003c00303006500c0642001040da14050644013022135845540c02c10740158014006550b8401060260b1001d40c0400094003014008555400c0c080b140b045180000f0881e460b160340d2541c0901060070b10701710320203000307160686843c40300100d00d66051b00d12044204d24035264400d103040c04a4003100902030440020300402c90318460450102c0024205050740075144d052041e40f5080c400003504200e001944100ca9003a52219031440c040102e03003040c0c0508419040e031162607100000d000c1200801ca04840c550104002c503482d03003110500543e0400d00c503400540b4814032041043c0e040101c0e120102510900c1541d03030340241d800009442d81c0094031004d103200078000d90340810b01882a0054068001c1c00e8100748141d0b0b0f0310884039003501010321040d010301c10205100c1040d03299902514a440d2001d00d062031645801314403156142c011181200701000100c0c2d000035064 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 660976223 1250 660974973 660974987
    0x6080f010603050d0e1f0c0b010501050a090303051608030f01090501050904030f1b0206071214040b190c1403030a0510051c0203120f09030d0302040b1206040f05090319 74
    0xc2d41c410007402500c0078580085d5240409030301c100703403c078a080f020713070b00034024034100e664168200383c40701e9450740c1c01400d0103000010140c01550500504007c280162500b00c1d40c1042180e51520f441e541d240c84452107000062014580105a44800300a0040030300d104000c4138143ca01e08031041000d81e98813030030800d44a10035100a4081a130001c02e40102e244180c0304400d0b400500c11020300c12909540c0480e100340c0c0005810348014015010382140c45a000e80c50500000c000000e660401e814040c064459108100f85c25100745000d01d41e00650a0055508951a41d04484502c0c031b805081c0b80c03070780c1e03c80d0300480780852402d03e081d000944180344400312005844002d0001400108030140e4441c180300d020307500b40c1c1d1500c605e00c00a410107800500420070f0b2556840e0b0180c071280900b003498600740040c015141407600501091054075169019038124528580460b503254540b9808071b4010f00749041c5918551742404204031801000100500e02150a0b0f01c94187c1d0300c0404000315200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 660977473 1250 660976223 660976229
    0x30c030c1507020106064811030607090603021606060608070f0309150b03122a01110901080417040b43140604030906140c0d030e010b09070306080f0106 67
    0x20541d1030007001910f00901c0004c4144042c1c2c0c0c0c4143c00c45c002c020240324060968140303803090b00447c000f084800c00200c4001c01e0810300c001e40c010301d06401d000d00098888442c07400f0b40780c10503074042081c4010408132411100b040e60044420131031317039450b000005c0c01800120ba440011071040585410000d10030300c01d9514490f04030700803036600724810355110064001c001b1602e80c94402d44584080303001c801c0004001290b080209051008803801020071040081c42110a20340d00d400c03d020320700030341e590848150810901e00781d001a901ca10701400188140c1c1001c03001c05e8004240030601102c140014018100600340d1446000c4a0400707070714560042840403580c1d451070b4403200503403009030b0010358103d62040758040c0d403060382483c19515244040344c0a40001d110308034100100780d04960705030b440202c0d2500c03041c0b41154800d005035807030b40c101941d5002c0640c2c0d80c0001c54551001c1d80140309101e001490b20511741010803005025240da4001e030a220b0181c040c0c44541070070305110f08421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 660978723 1250 660977473 660977477
    0xd0c080d08100320061308030322050601030b040804080105010e060a17070303050912102403030804110406090c08060f04020909060415050d03031e2309030c030c150702010606 77
    0x200403d420340e61506a044a01c199401100c20300c0058a03040114000c400985143c500641d00c81c070304403102b804040b81c8859603114a1001816900200c2c6001c11801c2c1500e4000d000010140c035545071500d01480786900c80c404551810b00003003002c0009240250065008840a00b4401e455600314546414403012404059011400410000307006d0005403d40600040038180f510340d1b10b000b5241000c10030300d000700203180d50305000c44d00341031040c80c1800041448140c00840b6800c681d0701800b00000a0405842400382d051407820303560b55900300c01d025002a420600001e80070300c0d800341040e142998072034400c8100d00c500f1025400c10740700f03440f22000000c000018a03201d01003840300420700302414050800d00da400100b803030b0300d42d400c040526621999002549442e5182011003220303010080030312540c00e0140c0d03606022206c000820028043c29001e014607180e0103c803924501c944079034007507a400080b80e0f51000102c0440d244021054251070343e501561400412401c8800d24007840380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 660979973 1250 660978723 660978743
    0x150f1005071202010b061b06011205070902250303050601020c310f09080d20030411281d010e011707030209040c080c09240d0c080d081003 61
    0x10600590b040700d01e05005000010307104980c00c0c00302e2400d600100ca02581040e0205002c200118100015030050070000c0607001c2c0900980c0e122921001e00d4811504060b0300410440c9248030448030060012000c03407140144800c0030325001e40500f01c101ca40e90701501407034404d24514100303c10909048e2404200f442c01804500146181f16501e00303019080542c0c5e07840c01940b4a504511550580500450060303450b00c038807015000c103851280c046130341d0045a0070800d035854440d20058941059104c1c4034503070042c500e0004542002e040f1010301120b400101e0915469070300c0030f0f0310741c4160303100c1c0b0324045220759601205403860603080c85244841d14150004100e80c0d03410a151070451003402040c0c5641d01c1d40c9400040100f24180d50590300485c150508018540040140319103aa105450241f95441d16802c00070400340100200000840c202e4117010750350b5600300612411035844000303c0c50b00781c1c03070740c0e0801d998980d50844c2c00086664007011442014a42070b01c102101d82c4008480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 660981223 1250 660979973 660979987
    0x141804080406140d060e01051011031c0f05010b0a030e031602010e010c06020d02041809030938090307050d05070614040510020a020a06030c0c2603150f1005 69
    0x122103031003c00c2d08120025003030040c0021312000380a10b000502503421620200d5041100300903000040c450841c1c14014882207401903514080300b55400502c074400c0c481c03650703826505800c01600088500701ca8043c0740c5000071030300040d071030040c000413881d43d0340c20000310003c2040d059032441804c0c000569a0b448408817801513201d881460b1007480c042c5060555441d207540d544007641c2042420949103500441c0500c41c883e1441105003401c0ca41500511070407a0a1320044e0120489004003a0b0fa41425070a41003d01d01d82106883c2c0c028401000840440e2074209940054111000392b0f07211380917a210002d030b00d2800c141e00a0303040c0e4200c00500b070103030b00e0000251061241020014131000d001d1000280d2591220480385260646401912100306644100000480c0a4103d1824580750100a124065220603400484c1c4d0303000404e28205609060864008250701c0c46044910340c0001c00c02c2003c1c4d01407145041030220950301000c440c2105410820300da0100031800002810602c854 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 660982473 1250 660981223 660981227
    0x8071106011a070c1203020606101d0a0b0403050a0c14090c0702180103030c0c06140706020f04030203160f0902030402010e0108071107171b06091315141804080406 72
    0x512a0070601918610301145941c1381280e80c4107585c420070005420b11908028103405104040d4050380480c0d020402139040100500f207140800a1000789003206100e200c0b140c1c4451080202510702c600030a40c4560f680e103440342d950280c81c1012107440010030400240c1124201900040100082810f906503548800511581c2c02450301603070700c503024041c1607040120010105000c0d5000e070742c8107240c44580d0f0910718580c2440c1e070300c201c0800c00c00c49a42d0800c030301004151840550303c032001580e00c800140c1d507061389000780d800203940f60040851081400700c811003650119200b084038580c02c55550203008049010869001e40895400b070551031040d0311031f0a01e00c0d03004440e42820210320b005102900d28052030f03a041000500015988107841e0034003000a0078840026205440ca071348a02004940c050081c1c11680313016100101c01c1a40351900d5130055000702a0192000f14200c2e5503070300c805c0c2035035440c041c11801820340e00d1482c2101c2d262504050703c203036007102c3c0b0940b4007440c019003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 660983723 1250 660982473 660982499
    0x70b030705040e040b0702010c0e150d0e01020a0f020d02030301080717010216140705031f020c0f0303070e01090b120c250f02010e01080f010b1b0a0605070807110601 73
    0x5400c00c001e810040403a80034110006140200c0c01002403240307520700fa400107400c55050542d000c0c144200074040042d0b82c1d0322141000e044021020005403180031284802004d0a10b001c00b242055002182c9803007969404100b43d500100a58203c40448158040903070f120f00c000e0051103099004480f0900500c2041e40c840d089541d50035000519018140c11841c82e60180d940342141d00c0038180c05410351000007007007104060f00040b0046c0500088504000744501581c2c01c6100c0001c0c3c000c1810b40d6104000d1011540c214041c0c821380c0d0b52440c203020010100405804400d012440f05040460004484000e0f0341558000d10729507201c80d225902e800f201504000b0094425184011f10b0341e081c84940700c01a180b203842481350440380f0043d440050810002844418100041d050401c111305007202c58440c1190f08120b03e1564614064004411703c01c4054083c090501c1442c424004205650780711501c6000103685103c0b4580b01d81204440d05501c642c0c620503241e00200042c8a40c5404880b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 660984973 1250 660983723 660983731
    0x118031707170612010f0624090e090327040c090b0a0c1403070c050907030506030d05181210060f05101103120f0f06011404030b041a2e050102070b03 66
    0xe40c04140600c00d0301d641c00e507114149120390003521010200100c0000103624486d410800004c40c0300c00d0106903004182291920ae00030f0182481d201003202c1c80d0080c0200c54075490000c404092400034001e410301104110000340c0d004074600031100e08500e104810040954034403423442803800f05807500071680359150650555010354810f8030030a11040810040013054403540340ca084d00c40c6803008002950000406010030b050401e0108885a5000304060b070b01c5100b5818010f4440b128030000c1005d000140000f10f81021450707942072420b1030001602d003030025591005005181c1c641700344120030502c5108143d000003103030480402c039502030004c3c00b0805000c5401c0b00d040103a4040d0074002041e040d0358808800c8104003d0040c0c8028002d42c95130b101c0d00c20b091020310007074400c110352980d106500c00071f000c450142010904100c08803d203d0980c81d80180100b03141e0400da05042600350408100c000480c000405212040500c08010011540c3c140c016041640c40c2a658841c0340d40020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 660986223 1250 660984973 660984979
    0xb0c07140706090503010f0b030c15131410030c0909110d09080712020c0108040b06010c02030105040c05031b0310050606070606080616050325030b0301180317071706 73
    0x1032044032915000c1115400400181d91003503102c914100074103007122400c0c00285905070400704c000740c4030385001460240000e01600c4407403116940354114085c4e27000d8248e091040115103080000d0704001a2441c4e03041c41002c0391148031542540718250201e402c60030342507001c10103c0701e0402000c07a4a0b401000c844440c84011490412281919021074607032140c102e5070315101068031014040782045202000e0a140024031401810740006800c03042c004000a100c07011080c0040c02c039902c95541866080d40c054002d0281d41024a080d020104560080c20b0080c82140d100303000c40d0510916035500d059019001c0c01035810568400c0001d4100201001c1d08044108480c0c0c0004459104640050010901410560400c0351142d00000b16039101c240400002740140300e10003000303400d8800381034842444146100c1c4e0304c482c1540501010a0990b616500c1d111914500c0c1c1d4190017044000740c400c0e030f00c851032202c40e0241124550810f0307640700001245900519001d00c4030b450301da0340001c001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 660987473 1250 660986223 660986243
    0x9090102161509051903020d0f050f07290a0c020d12050702010b0d060504050d0309110f0301061215050c0a080117100c1701050f010c11040204080a0f140a0b0c07 71
    0x5482d80c61a08004005c0c2d443e456031340c0c8400c0028980e06204020408103a40f40c001d04035482134900900314061400040d200318400078001007044085c0c0003143c1c0666443c002066102001040d504c4032140c00c59141d1652030a05868110181c40413451a21043d800d03194000407031450005000100b100401c400705542d078034503809050765608510540d440e4444c640c08189480c01d80780803414192900d840406040c105840c00d0002103515540c652900c0096444818001032100080c0c05000c1c03652004000c50740d000c044100303100c08241d03120300754580141c00780030544a009541041e48030303500d183d0001540e0a8014002c40114481d1400b42005030360469400e07a0010741c40380222070700704001101180c070310144880d20180c2c008506004040c2240d80300d0350445110300103000b4400200e001062440c2d010b102e2079450780c07258191400b5140030012151a0400d91529916010612400340c608404040c41c2114003100020600c040b00e6100a6110403038a1300903a01070342e9001144100d40d96a00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 660988723 1250 660987473 660987491
    0x11806092702030108030304060c020607080402042d0e0708071a030403021002030705030105030c101d060f070b1e0c07031d090a0501181a0f0303070609060506090901021615 76
    0x42e00155010b0140800078650f282007a183c81c00880d5074002c81a415500b002c4100103c6542040317009034030035016200403d5141004620740030360f0302034440032100d541c400340140000102c5680310030700d20b003107040c01c4429258039409030550b24107061041c07040045842c00b031003512003030080295800a10900450f005440224158010390b001110f8030f000241012004201a1604100406071841c003038612858250300124000d01184100155031182a841901c1c8801621090119070061481a440c52344071440d80c82c1185203032000b0b8642c100040c0896200710506914503080354011302c0d1103c182172030710b041d80d50142c4145c3c00b9440500641c0b9940c1c0c820208940310540054850700440300001040d40c104000140b0316042044983d038407906c2d00303500840b201c082c0d4210000d1020219050403040010000181c610300c6041e0f402001c5a040601c1801000207035040640a110308641100050b03170343c60485801c0b0701520f60401d0b601c108403005c000104245545607000b940400f040410a420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 660989973 1250 660988723 660988799
    0xc0a060e060c071202130504051203062110050702030c0c19032003010c05130e060a080d05090102061b0909070e0d03080618010e0c0309070f08030901180609 69
    0x80d00d6130050020b07280d450403280440c078011503080b014801300e010400203801c2545503035030349a01e4840048130032040080070400c10b82d541c1c485560004042100e003029850b0f2044d60070f88548a491603810032905103004038080c00c2c00401619691103402009250000624080106506039200c1d016902c1d41d2200d00403001c280102980e20400402c5640d090300004100145800c6036240b600e10390400005002e080182c0105036020380443d440904585500e84601000840201c0b4640c05000b0502c40c8121a404840d00a0068080702000340c00b502c180fa82c4148400c5083d0800b4045500815810000031956103000304006411003858941541e48a00f0782c2d0102c0d02c0b20403804400d80c040f50440b810085185030980c2030403208100e86840c034945500d00035a10100120240c0f04100b0340c1e40110015507507200400c4542e0061120401a40754140e5030300d02a030700c0f81e200c0d07011240000c204046231441726140c001d02034215001c664610164500d4a0000c0b25200d4000b0352920480c404d07500c00c200401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 660991223 1250 660989973 660989983
    0x70909020705010b01090b18040509010b3705060f0d09082d1e0703030207020a15080702210c150103060b1207030203060406020a2c03010e0c0a060e060c 67
    0x140b0038400040c54030300c648005489038000d98002d040d902001c005908415107403442207045480d051b64040707a142c9492000c2800b50441b108002c2d0010b861420290007112010f6800040319002902640300140805000e00289e02c54021950018010850b68690140510050107054000e8400080002e0305540300899030344900c2030340380204092405894803244041c0b50740c0b112803030708020925050714114180710307802402c103001201120108030780c0c0915000350119214541c0c003d12041050b40c80e1211610966081c3c0862000107010500164500d8000601a084c200e10303210701c00182d400c0445c901d5680d034000c0c003114130303d80108014084503500040d5030070f0195109990100300c6664600901181d002e440a64050a510070801040961004110980c1042c1c0100700941e030340301c0282045da0f00d181400e0740c1c0d04401a000000e031007041d18281510154010450090001100001056070380d034000e584481d6004244040070032100303018460781001408050001800c06410109843c100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 660992473 1250 660991223 660991237
    0xc080304051e100c03021306051c0e0d0e093102061801140406051903022a010f0605010e09100e0a05040218010e240301020a050d0608150f07090902 65
    0x543d01c01d8540f242a0012405044804616882c01710b080900c0100502070002052007100d042c0800050110f00003002c40c80d29900d002040c010610000a1082c10150350319100795841001444819a404a601e0000c0c0c3d00d5000b440080c2002da84200450440c00340100e034518552900900400c01400503103560015000b00900d1600080d00410781c6400502480504c3c0035505000d1000c000074040240c12100303641c8256018460944081e080c1310050b1b00900c107c001074020b0711190300c00c80d000029881c3d00090301c1c01c180002400b00c407000341160ac0603110240119400310f0030001031121030382003e4503810740c0800b0b40449001705c82d5580703290b4140000c0c03d035040a000343c1c5850412080d8140031224014000640a4071260f40d894030810300106036014001c907282c0c2c40700c034202c9401d6484200b04046a014000c0003190f07070f10058907024045500c1202100d0481e400c1940010b8182000b2820b904541060030b0101c4135666092951070080600415202c1840b00a110200d0a000c2910140c000c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 660993723 1250 660992473 660992533
    0x10509100201020c1b06040e06060409020c01020712090b090127121703072007050411040303080108010902090f0901090c06050c0615100e0d02030102180a0b0405010c08030405 77
    0x1035880d9580b004c1341040083e1054480303411850340810003540b616012102140c0792000c1d0100c0700d840d800001543c2d40b117951302c10783c000760000c036900c10f240c10194020000c1034030070032000141c9402c0d09405c1d1403807074051084411911040c0000310195000700c0340c0500030600500061a00c003003100000146401d80d80040d000a161490900c040000e00c00c40c00000d1904071390000c0c00d600c0d08481c02081000340c081404914003103003002091500080000d000035000060050000d40400300001040f90814130095001528560000034a008188244a141c0ba0003815003099035861104083e0707072000c0601124141c0d0358403000c02004c04c200039041c1c0080d06075940c4240c1c2d20316805114502d01640901012071040f1441c0402440b59102c0100418607521403c1050340120008001111241c40702c60294140d40000f0755141c104140c015403c50049089843c800c1007501c4000302076041c0035034080c3d13901244410000e107022540310006150302c02d100d002200d0080100d40501c00c0d5504050049081c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 660994973 1250 660993723 660993727
    0x30703060e010204150305040206090f120f0d0f030e030306100513080304050f063408191b030503130206160b07020f0c06072603100602010b0105180f01050910020102 73
    0x8000c0740080b1419100d2001e1b4581809541085c1d00050038034401c0c0c1c420203214105504100000e900c0d180c0000d1011080324040e50f003400c0b11220700a0b16415242c40420016580f10346610081d070291064150040b0300300021401e650782d40c8140641eaa1042c0400001d00400780a502c8210840720008809801e00d00301441c2c0301c51500b01070000d4a1a40214148511411f011b0307220048481a232b5600610918041090444624210104e424007141c1c4c01a1180303d000072903c1e032803414501d0001c00382d2016607072450411040d180d204800800f008008000440c108080341c1e250600842040c800350004009518160302c0d11004c0d681d0113030342e1404440d00801d007010421016014841400302d401d6076006000d5206601002030014451400300610006202e07482d100c842010114031003c0d95160601d99580382440074035085078520b00d109200c0190300340780060185500ca8030944902d00e120b4280350300d456030140100f0500d80b14600300c841c1006400d0115108680e2942050000441c0700d070001a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 660996223 1250 660994973 660994979
    0x1b1106010e0a0608030f0705010605010c02030a12050f0a030617030705060c070515010303031a03010c0e1c02210d0302040612020c0f071805060a06080f0411030303040b01060f081501030b030703060e010204 90
    0x540ad5420b5607200b07a042c00060042100941c0303000c6901040194420068061000c1e00c580c29221342c082c003002070190000c0071031800819505a0b010000b5148005005030707450004000d025601d1003081e400804642081011a400b039100d14054000e243c0700700d00352007050748854000f00711060300741d1041d00000d84400340070401a15082c180c00364035109a000340040e81c11020090100c216503000d190080301b42411680c00301e0600c2145290130307540284559440650081c0120700040e107442801c2c000d0107044c403060100c0380284211000c688094582200c140c2000200000a40000e0b0b0800f28501840000b03204843c4244510806481c0c0206c0c290340c02c00310040580111400200004d0140380840414040150459003440c0d204c40c0d40404c1004c3c0e44e840340b0340b1018442c014a0303c0342c0c01d440003006110407c41b10b0240745042c0d0705141d580b106424200502180c030107005940d0b5a280101a401c0c802e40740d4403a0304014000c140240448100540e01e0341d8a02c112607001d64404056507012500b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 660997473 1250 660996223 660996233
    0x20301090b0a08070b0904090f050f0f060618090a050f06090f070b0702090402030a0b0408070b060f0906090916030f020f10171b0c011b1106010e0a0608030f07 70
    0x320301140035141c1210b09810b010007140d80712054041c1108100000c40c0d600400d54540d08800030050307005119200380c4101d450081d546940201640d0a2402070070b02c1c5448018002401b0391140c48001e14105210501040030300503844081c00b0740050740203408200f40459001c000081d105501c21000b013500c4d180c81ca42040c00c104200350800d1542c0c2101608024059540062354103054044880030070584030361002a150054208005210350500400c0006010180e4081c000003406078848078500d9079080e0130000050161503455a02800060100d40e50303081104145522035402d500b00c40309050807208210038035006a00c211031000184a002003141041a00c4a031200c000740c600d1314829500f56800f4145042400c400c0c404861003d00150170844200c5800c90541c404004133550b0718030000d2040d020b400c120510720031045041c20100c2040344500c0154171a10381c0c0002030600342c1d0a04441c01d500c544064111069561030ba0008102100180001e095461f040451655101403a14207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 660998723 1250 660997473 660997481
    0x50c0f030708030d0c110706030614061c0e010b030111090411131a0702060301030303150f06051803070503060709090b0306071b06140117191e030905031002030109 72
    0x2a49019400101042051510010550b040c446024401207074100040c08122203600700d10f8400c1d40c0a10500130300040840e010350040050742c41000c50010b82d010401c003400941e00c00c400c0152400900c0d91603812407011aa4001d8031220b20040000c920030040c140000e0030364012410707807400048001060129440d041c41000c0c10700e0305d1561810f04081c0d41071403c801201d541d104500e42140c011004a042c1c40030b041c100c95840d94002d080c5600c030758503414024004d000d400c000b00d00d108241007010680820120414089500c50707501d6602d46031140c456a0200d01400000d65018443c21034041020b076810700c03400e8800d0748230342d60f00300300d0307510707220601041d0303011004c0c0c03039019402c441e0510442e0340d0b21005c5004200c0b00031444107480307a191700d02040200848504c1c603607000e000300c00100e01c01501903000d800b00d8803d00c085564480414000082001c44504e004110502007440080d81035542c400803407280d03029041120305540d40b040800e003041807420600035201e42c000700522020304d540c03003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 660999973 1250 660998723 660998749
    0x6061c050709051305070e132304060c032906090a0e09160f060818011b020f031c2f0406030e060906071206120807020301050f090a061e0207050c 64
    0x1309002c14180f8040c080c05400d40c4003d0580104140400106203084079000908200d10400c2c1034102401c0610030300304880d030309445c112211800c01d03240b00c1c07070240320740140d0280085011b0300d0140412860785160a0140700100355400c41005d1203010314564034800510001e205204d21f00c0014600b03c0c4000303041010505040319054141c60040c410383c1402112032040c0c3e180390912200c5074880d41102c0598101182d002c1c5020740c21301420880c4e01c81100401c08200000c0d070204c400f1050b8585840c3d4590040b2609d1558128449000b00000344840d006014184c0c6000c4040391041c0c0c40840011041c0c0003204981c8906500080401c49540d05109000192007881d018110398104400c41948402c0046c4c0200204558000301140780355055114070000d003110000446081013524003420a50402007050340b1a500e040c00062608070409450352185014070007503d24041c00c0e682d040010842d2101911684645404942c0e20038568801440b0150003100148086205007040202050b5152 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 661001223 1250 660999973 661000009
    0x12030411060a0c0609150903110d0e0f0609040b1c05070b03070c0311160e1e100e07180e0a050612032506051009060f05060306061c05070905 62
    0x100c109401c42c0d110b6070405015501c0789000c2000c0c216030030070b031b001e101c9280c040b8059903103410030365020150010200e11401d03a8136400d540209403907160580c1d288180f000c41a4100c084404140800d1030444004c2c203803001c00400c0022907800c0716012030081414164081c040e840340d0000a410700c142042802e0040201080c140c2c034500c2d00b04402131a0090000c402800d00c94200b0f82d8031800842444a03000d001c1d03008000381807060741c40c01042030403035041d03c5100700c10780034600610141012400942c4a80a10a40c40c0f014616115440d400c88038000c050710100900a860010002c82d0802144014481441806017a040c2070b00c142044a43c054101b61103220502400c040840010042e1392079070108008084244e461400800c41e000300d442c90080010707141c40f040245218000020310150703142d43c2001c2098a8071035091a69103030321405969800070040c0006403540c50102c00a294050900c9190f41845420f1050381090314000c0c2c4610380441d500140500040c00c2103014012000041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 661002473 1250 661001223 661001227
    0x10e030433120510031709130504020901030f0305091011060907050a051011010e070326030a0f021306030f0c0315060e0102150103060501060e0103090302120307020109051203041106 80
    0x1c4080600300b045090108150340392240700003007400d180c2c0304c00d01000b1500310700e101a001e42c45020401c4182d02502d40c09200f501c0c8a04c0304035084041e48902032090303501601858240e402c6454900042d6019070089040100400030f103205a07c4821700100281d05a03150015a410b0303080640c0d040910003060400341340d0018008120f00d070740300308c84101114020b0740c0e6403a401c90120070403642e43c10000c403007070059030a104981c1066100050f2a0040728000c95401ca1003802d41d9500200c035100c041100d030034a02c0e007880071a81403505076008101c0c0f0384400000528040022240300c02c01420382e40b10801103a07880e2151042c40c405409044c00b0310641345800c120f0101e0f55a06001c55020a00607030040121240d1444c100f039008002d00c030303640880b940b8440750560f901e18004002d04824048c0070001006101110419402805006141685078015049880c003240c5010700075040100728a045640b5100d001d00828802c3c0f10b003403201145074800307a81d24503041c01c0c103800303c000c40a1018010790382 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 661003723 1250 661002473 661002569
    0x304050405013503040b030f15030609060a0203070c0b0a06091107021e06090a0f093207121109040501050a180504150507051803160e09010e0304 64
    0xc41c0e0003000051410812800d101850040503e25600464005a070200d00c004240825412000c3c015803060041e0340301c0c0403624210b0f0050546810f02503404001c983e01030403b0034007045094002d10b50148040c42e09a1441e0010707100d695010006488501c051603550764107100d841b00e580074004a00c8016000c03146400c0591303002c41c0c046110504c0701c080051001000c0241c640c0c80c0bc084500303172200140407000e00f03900c2e44000d101460b0607118840d001d070328040201c00e000700044a4004031809846200207401d807440c1c000d0840043c020310442c1009045200401d20b401c40c1c1c41020600148040000d03111a81d00060208441d4180c000a100e15040b403810002610002912000340d00d0004005c0303801e0715070b4238100104194800e040d190280c14142009480769202c005400209410180b05001150581c145500ca500c1030723001720004d142d590424040d0202d50b004603504454800300000701c038995a150a4210f400c81e400070886840d214a074581c00280240510114840e80d07821601c010758 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 661004973 1250 661003723 661003769
    0x6070605180f0316060f06030804060201061208040311031f14130b0115020a05070e07081b0405040905100c0f0906090b1608071202061e04050c01080402061308030405040501 76
    0x1000300401d10313400300c8201d0380100421604035038003404848000713003e0300b5203901e40358000360090301402c80158038246000412201c811303444014250030221720b0f4980390441d101c180d070322440107801940600c40c800000640c100ca0340300301740003420003030030015030303c58601c211a10403000a4404d403101e001c0548880c2c085280c9003103c0c0c0c1100d8541d05038503008564203e060341840b66512015105006a0000040c050f181c807509921a158540d5401403595400c10740040c0310f62090184aa10fa030b0a10003800389040139401900d44034007503406c5443c034a00e00b50140c0c040c0c494000c0354000241f030b9070b1980650309401c1240d00780a03040700d0808000850400f0100c1040303010340898140c404021854540500c02c00c4411503910f15001403100e00c2400f44074501a503581c10a0b100301101600d1b0020b10701c00c02c962040c145004583c0312001c3c100c011262401180c0c1030a02400580e070100c804c011020000f030715070405d80014070108015540381c80c90802040100c9030164008100b00b40c06455003040d0304 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 661006223 1250 661004973 661004977
    0x91c03180906151b050708060406060503030307020a06020d0216060b01080f07020d0c03140a090f090b0a120303140a06090f0204030b191b0c060f0204060819090206070605180f03 78
    0x808a8a411070466030543c8404d095940f808001400c05d02440d00080b41d101030100345180304a01076076090140c2036940701455604d201c21580c1400580041c5402800544140c005049484581e080907051540c141c8880290020040c0221049035840f510b03400ca55803c8110f29a002c50003e840001500d00341c84082e441c0c58a0320101001c00c03410f590034004150080282e10445100411551b445003000344024010f81b07005d004640304405068800925005180034603454990083d080b458041c3c83d0884d01e400c0010400c100b24103264440341955141c0030480c0313005d88920340900c00800c034640350a801c0740840e07440701c1c425049280108000c0c00800c030b034041840d400a00a500041180c3c034450000030060001d1800c03011940340d603112041500781c2c424503440329540600c0081100507810000181288a41d11941c0e01280c01c0b180000c0840044442c15042245802d00c08188004036500040da590310008c002c0300d4295a520612841080c080304588006d003070354000344500c5801e030300d100c1d0b0b60f8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 661007473 1250 661006223 661006259
    0x8010f050c300403020a060608030c0a1b03120c030f03060b03010621050702070e060414130303060803210901090b13020102010e0111280e0402091c03180906 69
    0x2034500220384401424046280e0700b008000109031581d03604151600039100c20222405940c0c031410210082800040130045459080b0150000d0070762030b2042d91140000382807a11700703803e0340c4040e60000020404d501d14522140046030340740d20200c003182c03601170701d0786000450500400d441d00038144803490702001160b0648545041c10100701d0080d5a40d9840c01c1680400d0700805404c03c400d12918680018000e000d840c8481c030918500d0341c07400b05020803542c0040441d407000c0350640c08100e4207000c0070005a132260085c940071460a885400c000d195620a00340c450410410700d0503041904011200135812215802c0240506006030715024264130024160b40200000303c2e850000316030007541f00303070341c012084c00080c0107003002c007040d100c4650482c6004a0014200d40d803000d00e562072590192499600503203841d904a1008402d1000030742254241a4100c84403240c08607004840c0030b0305030000da01c00d540d0786070303c0304645001e0b01d0b84030920740c0071804903800c0c40700500050038081e03007036040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 661008723 1250 661007473 661007497
    0xf08060d140c0a030605070f0e0303030f0903070b0114100c0f03050922020c0607020a030804080306060d050901050601120606050405060711100c1112101d0d030608010f050c 76
    0x90035010442400c0c42d0115908540c0041d03030300400002c021098104078800c01c03035034884c9441d61100d407105072500030008481d650715030000c10000b107403202e010b1074603500a0101c1c4210780c11320701c944d13882c040300042c2030b040400e44008060600d40c081c501034645e052600b040d464092003110751a0743e0321004000103140102170000205550403107480da03400c0903a1100c0c1071444981610240c03d1480000e5000100128041c0180000240d240b40009580001c1c2d661541d2510b007036a96688a2845a40000d8a13042d8441410400b01040c0c440c5801418080d582e09000050b00303003031040c0094000030081206607a11801c0440810101d81c00c102505c003101c005580d11656100503103050745445a9515201c0d5001c10f0303207a00081030a5000c000303103803401c0c85058034000c41d0202c081000201c196080223064940d000d91410a40402617400c0002c0e03a100441018a0440300c0045140c10301c1c001c40303280c40001c1d45e80c8208002d111000d00a00710000800441004039080090203500d0b86e214101080103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 661009973 1250 661008723 661008743
    0xb06091f030e07060503060a0b070215030c191707021b12010204030b04150b0307050f0d1401330f060c050a0f030305010e06030606092e03050d0f08060d 67
    0x200d000d0094110a0080c8a00c10aa0b02455110200a002c68100340c407858021618130102256489048044450703185d00102a41140000100c540708240d000500075406d003442400102c50003080256080c41c01c4450780c464000340814140400c52140b0020440701c21980100c00c0c000000e002c2c0c44070f0441440c41659800401400c4400e8035001e84250340c00145a00f601f501000180302507225001041d40c8881ea06201c125400000c144d506e00c141d01490368490599100350070140340080141030214840e401481460700c14280107821282214000c1802c40708007568503c40b40c005550100e260007030300d0165281541044800807401000740190000e03c030900d288402800710801200d1210381d880708002018115a00e0004d01500080c070034003c00c4007140022071032510780422102c0c0b10300340180240038035070b5a0244000300c507800c5c82201d12086203010006e0340c1d95080740e01200040c40c0100c1c010405110040c0c8011f14030f010351180721003004884024005c180d940d10341034408054000f40f02c0c030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 661011223 1250 661009973 661010029
    0x3080105011d0d23071802071a15011404031731030210030e0a1e170315120c010c060b030307060c020d020703020604171504050609010b0609 62
    0x1c10380703400c504103600c400f469481c80204180711600e881d14441801c16440d001c2040000c0300e0342d6034a01d024907901384c503c3c81d006191000403903005c2c2c00024021640c0c1056001d16981e40d888180095412000d0034102e50111075076960406007030420507417030080d107612702441d645411526141c14840740c40304500021f94480c0c80c2c07064000010850020b201c642107400380d8030702c090803003442c2844100d0050004c502e000100d03600074400c40c542c604c0d0769005046d0308005030340c0b86c110704215030300c205007090040202400800c011510174041104200d8403160340741410320106000114006002d13101d140b04010401850f00c000c01d1550107160b080c00c11510505641c40c0c2000501909504550140310110f07450701842590341014403040320680130b60b000011404000c9031641100d00010350018810482080b1004c1c03101e081403512001c51059a00e0030345480400c005195095505442e40d0f4050414040000d1080c03007884007184040350807900d4864a08081003d00c030350a0411018501400614 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 661012473 1250 661011223 661011257
    0x1118090c07120c0b060103050c0307030b03012403020a1202060d0905010f140a060803040f12080c0a030903110a1805180304080d18030309030f1e06060e060d0308010501 74
    0x180303101c6076000a00e20200350644000034030904440000f641d410400002294465009200b101d008141c8205268030715a84c0403001c5c1c01a12642c01c91640544d81e0356501c01e016003803a0301c14507200420b000075a050030716600400004201907001240282c50600300000103079144021102900090342001c1880c110b24144940145462000b00610b5030400a11100c900c000034402031003160482402c00105403140c0742c0e26540e0003540140c0303400c1440c0000510014154a40b8012500d12555569280041c5050003e0418185080c109c010036008141401000310503420116410015503148819a1801d44810b1080328204a42c41105076902c000c00c0f081000b08013080c810401800c1101d903210b544d8403a85685034801400f482c00035000e0003000404001c0010100c00322901a681e0420246c10b6448110400707c5582c800c491501c2510710342040c081c0701e20000306403a03008101c006415850a43d100c036003880e005104a03c20200520300c00c000941120b9020305403503080c030300005d9480b140000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 661013723 1250 661012473 661012477
    0x10c02130b04060905040209070806010e0d020a08100603021e060d0207050c090411010306120b060603100810060f060f1d241e130e0a18050a061118090c 67
    0x42030b4015041c884040b40c8802d1907007102d4001e51007038605c141680c2d26410221000d520544601d03001607040e0070a0142d6281c4414000480f50006210181c0d5030b07900d14001d490510f41381d000702221070715000b04009510f810504142703001ca801e00580a10054640044c0580c800d1400f44a82151f000c0384070400c0c4041040a034a1301000644041c031a41031a0074418500881560035a0000b41010b5012461440e0450342c10b9a155010220701e841d80c4540e000c2001c16040100076004003d102100040d50303002c10030403056141d00804000408900304807000d81210050b4010358188138102c500038044030752068079054502013005c6001c0d402032011001400303611180c500801281c40036212803400c005103200400070256031886003206001c4078403005460380035400c40e05070303c2d0760414002c1148484070203c0d90703400a0b290b500043c038481c0c3e66207a190194840713542610540c2c0030245a00401c449813090352100740038100c90340d0411080320002c101064180200d00d005000c4400400c01071000202 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 661014973 1250 661013723 661013741
    0x122503030e0d020a060f060b03010b0a0c05071d070f050d0b061c0b040f0608060a0e1204030803041419060b190b1e12161101050a1e0b010c0213 63
    0x400e4405004074580d0080d0b4800381094141c0d8881e11b06012902458600d00c6003000b1904c800b610b15007503a1824820810640050f20b201c0213200381c141e540c60004409100200c0500000e02c0300c103800e14550411121039100081c020030900c2104d1034440f0015400806407002000260008924a00303002d01103400c1c1d00500d081d2103031035800c401c407111445286170442c010341c200a490030000d032041c200a0105594091103960016007000000c581400c525400410303004a00704110b90ba9140000a001e0035640103a2060b05c80a03008002e000810a00080000d0280c40600061101000540c00450010307408840109000e6803211910b526440d4000f10b0061051000d684008069450401800ca580403080000749a0007286114010410080c00d403804d500d0801412480ca43d2069000d007500b004500480c030500402c8528018804002d00415128500a800100701c1c0110110100c1c540350f000b52002c1042410702240300c00c166404407907982450303011a003141500301c49980410050800305 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 661016223 1250 661014973 661015001
    0x3040b1302210106030203100b09060123030109090203060f070503070c050f030403061409010213050f030f0d120c0903050d0503060120010531170906180312250303 72
    0x500142c55981948000b084034000d406584d0b0666001004100311111407000c56440070342d01d8082041c0b94482e00d08030182c480b4580b81004421a45400c031800364000f40e0062003003070707218110a811424240f19107608402c0900241e074941c10214401b400c2408014683d40c20084084041014880100303d42840f111020041d66a92a12402c3c0a0041c21071181040c0c2180080400304643c4c103014402c8881040c000003001c2c01d92402d040030000041034004900780d041c400d0080b20800c2e40c0080c000803107085141d03159120303444408031b05902507074917842c406420721514000401c0400c80210301900c24690620b0216580c0c6c3d520001a9582d4500f140f02030351080085620401d0000c0c15480f95000da034400c940d0b40d50400c035400703c401901c030110346a040c01e284000c4140f4000341c0c000850180a041e0010030b14140f440000220b990768000441d00d0240800c00e403401c0e070260805000710055603c1d5aa1460715280282072402190701e4502140305017800f9188584081c10300c84c0d13000362440e120700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 661017473 1250 661016223 661016269
    0x1c0c021501150807090e06060a09090f050406061a0d051f03050d201e19050c10020303070507030c0305120916050102070501091214120c010c030203040b1302 69
    0x24103140c002c0b204804900c001086035071001c070305000e000c1c4100c0c0003200c0c0d0300c541d00b08680d80e9140900050390001003078002031000b01000450825504d024001140610303440014030b525050074888290b8150343d03c003042d0000454a801d002c003022000315010104600303400b044036200c0c1007002d1380030000e41c61001801035030712901108210303002c1484140c40c0040d90741c05015441c140782440354031f1220304074440587e00101c0f06a4200b100d60751540c0c00b14401030180c0b819604040a4080b440c180004112015006001580601d181200200030485182c0c8003d42c150728086002418078440c0a1014082c0003860001e4820180300b00100c8011840c080422001402c0050715690364031842a440000c00480302000b0580e5480001c014044980503503900038024a007120120700d411001e8015201c022490b05600c1860360f0401401780c00302c0c015410705a540b1039540500c1e003110b60280e6502d003014010014031004c41c49041c10103811007800c1d8a03e0307104510314070014007884480c5c9251160400d40d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 661018723 1250 661017473 661017479
    0x210a030c051518071508040212120f0c120a08010e1305121b0d021e0a06020c06100f080a1202010f05090706020c04140705161406011a1c0c021501 64
    0x4008611402606440d046905681c1c481202518410000040c500083d08180001f40549020b200e20140c07214076806a50510001e02c1e0a00700035401520203411031b901c0060640c001103c10850411a00c01191942e8140102e0100050190784103110300b004419561020a01802a0805200c4038540c040c080310643c405000300c80034240c11141440c90b00c000c8a040b015280e81e40413075019400e40d01c580c05031000b541241415031085c0d03243c03047d9031110701c510380d030000000b081803004003001803161005190924250f008001d5040d09508000b440001c070100400400744005100702c000c5a2004500b03441c1145010124010a518484031080c14280000d02907161000314140b001c0c1d683c1d5500b503415030b114070b00c00c3c00b0507220313501220f5034110918000500d030300f07120340080c12089040c60702803140d117a050f44451002201071880c0450b00e0300b2101c01041301c2402400c400180340c1c07001d00405c0c01e1a81d4140c4000c46445c242c4030042c406c43d21101e0f44202e00e4400d003d03541c1d1020340400071b4006961 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 661019973 1250 661018723 661018741
    0x908100b012a111c1401060503150a0c110a08030601050f0706060314010e060109050603150a050f01320402040b12091213030f021f0509210a030c0515 66
    0x1000c401c3e100070410440e110001d0800700b650069101d80d00071030710214105696020a580540c80c2e803401c2c0f55690721000b25079550140014a824244031100810744e0611000003c02c5407003100d1280240a2807003d40d40110030f0128490340d0003074016031256165552000140c0d410f20529485182c2250001a07032400c010659004030b0584c1e010b4104440c102c1100c80809080710411201c0c00d05175403103040100001d1069412455000030301800f941c091360104940707071070600320030f44040c841184c5803401c003c4e00104d0700c000e8600410791800d540988854044249909444500909412890900c00151161140c1c0c040740e004084146078182c0c0c9070041c5045004282c0f003a1070a08030380c0a2512100c0c030f602c140e00e0644100210001c4036400b05031440d600e1100e500b01d00310b030890b08044008002d8a40000321201196048825101d01d030350b850030300c0f00300724100d130404c0c480b408030000c601007404100ba40013560b24245641404c00711b81e07815103400c01c2072810740130140c035a4034503a01c1c80c10850030328 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 661021223 1250 661019973 661020047
    0x17041b030f0606050f1503040c0e041a07080f04032003040b0d060b07020f090a090f030f0f080702030f1303020907090515031513090605090c0a060908100b01 69
    0x1d07014041c2000340c103840b001044190010400c0d0940c3c041201a450b4080150140086811520519802c0740317144d41c56002c0d4040000486e004e03500182040500c00160155030489a80540c55103020b81e610702d0505a01000160050030150420066100541081000e07039441c103040641e101c1101c2d20740b40d442e028502e45520410b40c094005040181c0040c40c03941d180203643c00143d00416804a680d900070a11144580050000c44c44c25102d50344100072031000c0900c0c2160074080d54440d01c5000c60b100000d400340200c12842c6081207603902c200042c0d0f81e8040240d031070b04284a03070840d6403800d84103a0280d10076583c0e04040d503c11071131001d1015180d04a1040c10882c0d209550042d1610b544407001c048502084900c4490000c250600d0812850001c006010b042d600c50b00004100b034007500d5001c1103c008a80740040380d44803c05a007070038504180294014481031078125030240c20010300035103031240410400590390f1900702e0052aa801100c00c98007005019082102c0310b13488220f522249 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 661022473 1250 661021223 661021253
    0x12070513022505031b2815230f0f010303030b0a08011a040506030a0803040f0311010e06070806041802092503050a06061e110123060f0d020117041b03 66
    0x1c1c4103007810045c0740b820108407038080b500c08070f1481103103040303002c003020b001c4012900460701c125074204019900d200c00c2c45685031142c403105410030103940383c0c3ea0700c0b4403100b4040d065403080046201049035083d5004601e50660380e01d17203008151a1804030106044984a40004419500b868004480048e12021026240c241210300b0701443d00c61009240e08e902c41d9400203403020f102000014080b50f881c6003020441f42c0709151828048065102c4507084075120b035043c540e2900321605102c0003d900588258103d04100c9041009a100001c0e8148440da010300090042c0b45d220002924001410b1080c0c416014050307040320001c40d45c510090081004455946031203292103408074149204074245120b98518007911741c02003e2512098425a849030341503000c541d294070b241b0181002003404600000c0e0308003a030054071b05001c82080500c1c10303542d04050050070720800450142c0c5e03020a55681a9035038028206d07290304c890804212101035a02c0c641e0542e805104000108400380740c2c00740b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 661023723 1250 661022473 661022497
    0x30c1b09070c1218050616051005010b040909080c0f15100b0406030216020301020d09141507080a09051504060c03140a0f0621021207051302250503 65
    0x109a45031841a1101c034040380d009400d443c94000b1101c0d5182c0120011900d0100d0003c161018035a13510008509034400c43d5030200d82c643c04080d010401404000c0140000c0404d06d040c002903051000a0700c443c00780b07114448126442e219144180442c0c0d00480703e840f861130050780c01d00350300707920119a94000d45004654010b00c0e440066807030031040d88103809842d10504040e03e8145070440c200c001c1d40086550400d8156290f4031000140d40c00d20042490170030240000c202a082d030b0400c03d10b00245001c4005040d007084140c0200c0c40e40700920594003020750f00b03001ca13003a11050541402010f401c480100180314010104030408141c0322000e10440c8a28018001e4407102072003241aa01c907c4500800c1d05200700101d0200021900003404001a02c130002948596070840d04481190a0800340001036140c21807800b07500708410810300d428020300003812001e10b0400410310744056889506842d40e40480d5252100d174800c2903074101c19842c1d068a90b41d22505081c65602d9a025004844c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 661024973 1250 661023723 661023739
    0x906030605180f0c0d1407030c08010609060e0406110c010f020d050a02090135190b06160b06060702180601020106120b0a0f06050d0f020f0405010e060f0102030c1b 72
    0x660400c0010390360414030405800f4044c21188103051140c400302c0000200d4402840414818505008011034801540240602e0315290300d4100350783d00310b6080390082c0c010242400c00c00d020000145500d11f410552280c400941d01340d0729a40c5210b00e01505070800c4480d428600c043c91388040c580c0240504200f006410405900c802d02d4490807445032140d0907000c00c1d10080a1350940340d0480d105800d1300100368032062034041c0e203880007611b604111503800d010007504040804080c410301c210f20f0340d4941514501d00d000c064003904508140d02c00c034000c01c03c0e4005800903d041e11401c1c01d071142a035007d0080c103000d404a1031303030b03281c040c000701e071294015884d00304005200400c0b01243c404a41d00300d4200303816078941140d0720300500501e030051100140c485030006041d0700c50100f11402103000d83c042e9000c0718081c4c41080308030740f00f03c041644118107100050210b91119140e00c1d801c200c0440c0ca540c140951080141c0c04c60041340011442c03406165000e07501c44040c96601707004604100d074144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 661026223 1250 661024973 661025011
    0x503040309140d061d101a030721020303130b0702131a06070f0215120a051b070c0f09060509090d050a0c0f0b0c0a0e1f0e0103060906030605 62
    0xa00d000482c907001075403150721800144003003680f941c080c101113074030714403001c22100c2c00b241818500301103050b4040e00140c0d075040001d03000d45200800e40c00218201c016021184c40d14000802d12580d104840c40e0009004008404664041003100d40204926085c7d4400940d540a0b1150325084402e080e40034200310b1a001c80480b11501c44d41c42c1e000302611440f6203840c0480c0602070b040e000a0000c480c03a00e0808460001360351000b01c0e0b244d01314003070840d1980c5c03101a01140058100094040003000c0e042c10f0510605100080c1c0c00030b0030040001546031140c3c080d0804070080c40c1e1680c0142d580605d43d400209070021244c00900c151402601ea0014540321034250310380d24800c42c5002c8000070424083c44030681d100e02010700d03001d40200741d00c4070a4041a202c1302e01d40003040d147c20805c400000b03529055542c1128083c008048120b4200403c1c214144002d80341100ea0342c000c208025100035100c540340e0107075120001a20a90400b0810300780c8038034000c3c0080c1001c4d54075051100e01c0324502 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 661027473 1250 661026223 661026239
    0x903080a0f0c140d090609050109030f05041521050106090611030c06060f0a0305120310050409020f04020a090e0c04080f030301061e090815010f120c15050403080a0503040309 77
    0x6580102c81c6a82c03640c0c0f01c40004041003240b90032a03d0b80c149400e84039400340002c03d40341e016110407075000702d000264008040c03030060300000c1c400d0b4040c1c0c14130800740420070100205900c01d102d4002c203810011080500c8900391b054502e542d001b40c800700c0345050000b14070250f002c3d0b0303103509440d0030b600e41d140c0306201d00302c045940340250303841003205501140001b0120b0030160388079251000c014041610694896441e00e0410300000c000315003001000c03082004446808110400600f0261807c025075a4107070040b44400200060642c01644c0000b544071803244100c044800030a241c4124101c68101070303031031800c0c43c0c0c418851b00b4081d20548040306500080841120304032078060300e440007246000084075410b0390282481d5070512641070000a5251028064001040c154114140307656040032203031500d8581c0d0750004103505030210050400504030008410075039029100c1d054400030507280441d20b42c070550304000d00c103804c00300300b0500454024000d180594802d4a078030308155290115 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 661028723 1250 661027473 661027481
    0x5070f1506030b0a11300c131a07030804050f0a051606050405100e150409050a06090507050f0306041506081006050f0f0a031413110d020109051905040903080a0f 71
    0x48600c042000300450003d001401c4440c1c0300e06c00440d20341030026140340030a1107038404103c0d4200007421000580c501c01d4101a101c0201a00c0c0080c1c41e1000002d45503e9000c0701d00540708000c2c140074011000c1800d100080000a206060f400200c400700a0700e45440d986800000100100f8a0650400418100d0141040d9410b13a01c000c0d140c5051046000c5c0100c0d170384401c4010f02500030029004000ca90f101c0c080080004d004943d10200307907810314185200c21a01a68041d00066103008103010310746512a04541c0c42d600080a0035859803219400035000f056007002c09614003101450001c0c941c1e80010880d44a00d01101050701000d030394100c25150b910882070010f040c80ca0820403001c084580304054031502d8a645400110700806964407810b200d0182c1d00403021901c400c0e5210b0030421400381025070b1000a40c0ca0890001e80d80d400680034116038011a8807c0c25003414049120305408041030081600803c10702a502007400e000d8602e07841620b41d4036499040a11010032807580b405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 661029973 1250 661028723 661028741
    0x21030609070f0302040e010b09031507230409050f04020306130b04350d0b0a030b01050d02011218060c17180c03010f0209030c120303010605070f1506030b0a 69
    0x200516095440e001c00322012501800c000c8249903083c840813a42600d41045240130b0039103444015524640c0c5e100300741c604100c660b651020030a44a0800a031191311020710a1081e0794260840c80b0b82c20001c5041c092405036801400b80d0324900700800092251625101c0e005074004d4043d40d1094803048600c24008050302c1c0c01800d0940d0301004a40080c002050100440050540420703d100300c29070341e0401003000c0f44480d1000200480c50050b400d11612034003034401412120725410a29584d188404000c0c14421184582103070309842d000d690103040d51851a90750b52100f001648141a0f4a9020480c2c0c81d1003a40d0440c0303084096450b04e4020b08101d007191704444201d02c000c1d99181d150a190718041910035050740180052a80192424050031180d040b5291000d40c80b40b01c2e24007072602c0d082040554030f1041c41c68500e0707641602000b01c1241d0541c0c165245c074035030b200400d08117480c0c20039440c03100604101c07020480c50f40010f500d80c881c9080d0b174444c820398801c9407a418899800c0d564880 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 661031223 1250 661029973 661029979
    0x30b0904120f0c020409051c02030903100c020a05191b0501020a060c1e02031209031c0e0307140d0e0603090c040510030f0c080c01090608041e0c08210306 68
    0x100d03030201d1040c011400b42a9031070303140c0f0742444102c0355035005c00c050321010b1404545990024020b804074215900b0005a8034215100450900c524140000d1b03843d6558581180a10394518405094a1081c0705881e00c00741c0100494400300b010001312045d081d0414400d4512111180f01d005401100c00844c50449505038001e100444a03911150006d03e050142c01052120018007081c1c00b00700e440e00c19082c800700d500036689410f5141d10340b03122504010040c13030b02a0001c01c4181c4020028800c0074445503007014001640881d26105140395100300035010713003001e2403400b8034440307110300299005d64070049981d8003a202c41c0d410240061130106580c01d0109401c10100341d0014100380e48115448100032250140850792520745501075040c8080998041d0710700c1c0803d1144020402690458071020701c2c208159a1401d5002440030f440584001c0c042c0c1d01c1005404419a101085503854039008960000841d81d5045c4403640c8100a00000403e01059905034a40141c0581501c0c4980005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 661032473 1250 661031223 661031243
    0x30312020301030c0b161709090a0b1012060b0d06050f0d08180a0506070f1208070512060301090c081c030603020a0605030916080105061302031506030c0c01021207030b0904 76
    0x12003403d5546c02c00f803101713140b010488000300007044800040d8203103403407107411055440c6140d00c14050304820043c02c0c80c2c00c1500708060410380d03855101c20340309901c1440c648040c40daa10040090013411072907010480d01c100115070020f49005640c40301301112011900c00921405060502900d646030b02e03030281c0701d4281480f480c0c0760b00c01c240072851044000100107007020b035250320000350305801100c0261000b5000310610001c02c81d418902009021580c14911024038054900402c548030340a11080380c1c480e10004101c2c1d0703480c25085440b0466009540780f106644405890f95203020784190140500e0010820720b40260192051009036a0050030032481c250800300107903000e500103442d1421900c106080b84d0120342c021809900a054070308004220743c2420130070048158000c1c0090403040e0b1040081c8101310104882200c00703214180c50340c5ea1650344400d241e400382d01a40489c40d035194000aa019031604124448901c01c8116840030007509a900045c08030001c0125401405141701c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 661033723 1250 661032473 661032479
    0x240e060703020d02040e0f18060c0712170f07120902130507020712050307110906010c02010e22020913060608010306021c0c020a06050901020c33010f030312020301030c 74
    0x3280e0001c1001d070210901c05843c0c5a1b07a14210881c90404440c0c403036144d80007105100c2007030043c0c19040021070224008003054240320b00505c54600c1114401064418518449500640208004007840f900c2c0c3d6402c041914007120200c070074440407a034650000e0318024141d2508241c0d481058641c2c1e40180c101e0044c04442e0051000401000c2e00000540c401c04100161011444008ac5009813203071015544a200d41e181109000c005d40040750310480c0c140c000c01405990014003102000d4091808440c3c00030b490000c1080d400c04114907030394070703501c00880c84040c0742c641e0001d1101078025a4440700f4042c00214400480b1080d0180800040c00d41c0010004101260041c1c00c4403411040307241403007500419201c0c215400c3c0342c102409600f241c0c24090601c03031580300752903105108078020751a160340f507040701e500d58200d9044002615005240c6c03008448110342012103012642c032407003440d56140c01019505640710311089001540801003015040100d0003501d0480b68044030090304603003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 661034973 1250 661033723 661033727
    0x7030204091a09030d0f021e070609050609160f08030304201f03143318040507080706050a0807020f120405010e0a030519140a240e0607 60
    0x11818040d03510706850100040b01082c501e50190203081424011580c0b40c084034040020b80306038030030301c158192041c0100d4a07890b90050081c040801c0f0305c40032580ea40414a401320007448042400380403407244d00704100c1920000101046062801500c0780c4c20980d40e0308a60000d510b0601660000750018030118002803c603080e00280900b800044500f11700075400490b24001030300d240803400798070b818603480621b60940b04594200410090700d034440c0c542140e482c9442c0340401c50010610701c50b00c1070032044088041c2c0301c1a048500030314100d810300ca54051000c0c1502c060310181c541d801110720019050500107400c904031121078841500341084250180d5190000030082000e6014100b001c07083e400c8280215a0345100f08440e00d42c645081c40d000500307046105c1886401651014001e201042d00001c5a20a186070302c0302040150b03945140245509011002012944c8110507040c420804018427032018107076240140354003e03c840c10064250342e1940c440b0011074015101140c480c3d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 661036223 1250 661034973 661034981
    0x403050a12170c0301060806030d0f1b0b040b04030f02030a02070501200f01270305270d03080603010f090201080f061203040f08010c080c0418090b041506060f0207030204 75
    0x1d8400c0c180114403144402502c1c040c01e90499615035850000401400200d801210781a0089825001000c1c400059140038042d002011000401c0c010204a003201c010b9074103940402c1d007a0300c002c1000d140c1c1041e01c0c00102d0007206031801c401089a031064019554400802d0390075510141c0d004003900c42c50400155a103150300d1b03146915150041808400840d020420000420190000007480704218064405440e8400c0700c9182d50884210480000c82e41c0b24040e80c0c0101405000b03400704000f8410900032503810501c130944c00039001501042031541040c5810312a11041d00244500c0e211051128100c2e101010000e01041344200841c005500c4a91a594002307030182c602041100860355603803454200d43e100d411404110030003801020828010740c5010401414903030490b083c0408441058041c60113040301d20313101c400c40d81c015010560810210142c010391300e81c2ca2410309003045804440c4031200700c201542071500000f480e07071141c0610449411154003420581d400c580c00c200c098 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 661037473 1250 661036223 661036253
    0xf0306030a0f1101090b0901050d1d0d02060702150f0f04020f09161b0503040b07061b0309030305060904020a15050c070803041703030105130c05070c030305030a0b0301020403050a 79
    0x5072041c80856070019640050100e501030042c09400c4140080c2c0000412003d05c070781001d1840c0030b00740141016641c02909550044007c1003010502d0300c00d000002840e6000e545030f00b5071500c14801d0010009401180e0305011341103c6e4280d41484545a1640e80a49001c2d10000a424208400660151300842d18190030520040c1f050108500180020f02c40f00400e84006044102e801f01d00e84030680c21122000b03111502c0481c0e0461030505482e115141e00552180032045200041c0d8041040801d901c03041c0d4850f0113941b0103501040031130740200100790305001100031910b080c01245030b034500950f441c1d20450313005014003810fa01300314906e5641410368042d1701c14000c051101c001020300034800807000e090b03508021500c40e4074210182103403d50004030203120b60801c10041c0060703240c5401d0000c08039901400812400410341d422900f503c1620400303441a2074240001c000c1542c050029405103a0101003409125009400c1500700e00c1f40780300c01070050b0321807100c078030000d6661050381c640 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 661038723 1250 661037473 661037479
    0x108060d240605040908030a0506210c01030c030b03070504111e1206100f0c030909020c0a0c170604110609030303090d0306090b061c180804090606030b060f0306 71
    0x9080da80d81e03201e480950900300c0305040032100680ea48044054440d0200404089400340f007076005a4840f1241448040c2405d1310342038a820000d4050740f00d007103450012043c60301c0045900b266000d4481d8580b1504504240000d050000740c115070343c443c1c050715100040c024041c241c450300d400100001850100c2c034a110800050100300c0c0109004c1c0d02811401d41c00d0f00580340e90303414080211512040090400344142130740240d000c1007641c081401d144071074580c02c0c01035104c003c604041d10400354079480012002c0c000500012000800308008000034441c0c068000c60035160000d140c0328600c1d82c621a5000d91201d40050b01040c3d45020301d120154000c0c10640c42d0200d91404a815640200c403001d00b240d00564040d40c28507414810071004000c2e801080065039030490000e040e0b84a021011240740d96003881c0e0076503094969102c00700c54641c10744804a200300500e40242d07290054400d01011500c0e01c000068464000d000d0b1149680e0010000313440c000252550800e540c0000d400342d03030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 661039973 1250 661038723 661038739
    0xa0507020709020d0b0f04110415050d050112120503010602280204151e0506070201031d16030b1006081b04150305041203060608070c11030607030c020d030905030405010806 76
    0x8160b09948000c3c01c1c034110024004c2081d0701600d00380946011812045800750b0714115030003412259180c01d0380c0940d503070503605a00c0f0030a204002c031564050400c40e50b15203407409000040310f80c85480c1d090805449050412000c80381c0620503140d6000c01d03c24040560495080c90300780a400e2600405614050800b24085001a4000c6411680011035603005a10324000900c000c2c00d0902c4180703c810107074004240901d0400003c1041c601403144004e06042e154040c0040920010f00110f40c649148401c44000e0b10942d01038040d9100103110541d443e0139000c0201e41100c03095100c038030a48071503869080d45522120300701280c80c0c9070b08078a4540400c062002060002c0c0e020840c2c1003290300c40d503000c86d190a05060107a40c41d04078003c8041131500e07014041103001d0308042c80550003101d500f05040a01050306014617070211026100b035140c0207210810074415016401071302804080e41c21500046010341c0c2c00c0d4204c0b44031620240403035005102c200420b61060a4003580a54054200c107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 661041223 1250 661039973 661039979
    0x7020d020d1107090c0512100b07030c030507050f011a0603091b1807020a0c06030c09051e0307180b030708030702040f0204180e0c0609090a092127050105030a05070207 74
    0xc4100c40004400d980000c40001d87c0c00c101c0c2d54140c11007031f0031080550061701c00d03500d0043d00d050f03980304507840182403201c1c0c5500303c0181402441958107240c4c20205a4180c540041c005600038400340ca0310f003e4030926444410341ca401c0081c142c91255545400912004030794006075803a420040d44101c0d8000c0342810100e880a50380400c1d117000310760035001070040440780e1403d0006001e03903400030801c040c0340154480035264001d4400c422940c0542e0040310364010101c0007840400e01c06142901440f902d0b400141d0445e000b00021a1234250750000c01c846295007040580307440035880745422a50080c0084405440c01e9400f90741001140038006203841d0341c415030310030402140c1c0103502640e81d4844082401040a12410507054811030320b0a15045181d0001411000c000d04224613a1741e45a03601c508000a450500913441e003260711680d4510401d110062890100200d1a140c1c40c90b0840036030038010403908448c040d01e030140c5806040d81e4400c2e59204c000c0c031008002a04502c2100400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 661042473 1250 661041223 661041239
    0xc09150a020f061303020c090601090909030513090b01120216061e0608060907230d230c0d0605070c020619030501080304030201021f0603021f0807020d020d1107 71
    0x202052540d41c0c0142030881d0504030500d041c003400500d2150441c503051090000254040741652601c134007121550b85d01e07281c3c1c1700101c91400c52a0403410b401840d100007102416007200c0070704002034001c0d50701000582c40380d54403025a4032025110703010a91060340300144280640150900c042240c00500030b8281d075880d10401e68003058900c83d00d62048148400d100c0e00c4500600f8080c0861300010b00c00c9081008180da130320302e05482601920480b5050284488031200e000d40301e924001071025031056414103010491200c0e03010304e10170f0072107140462120500042009144507000030f00041320b50840d91079802c0a000010110010030141c03540c0e01c00140c1e00ea10107000300c6012212640130425880744003074100c900607008503034643c0c070502c800c10060780d0000d104504000a615001240444095840040c05d000c1e04001d6001a464240b0200440d10101d11200e014003562614110b0b00c60050036621307020499600e40040c2c015808041210740910008c010500300503088a64060341c0317141e2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 661043723 1250 661042473 661042477
    0x818060a0608010516091a0409020d0516210902031603050d0315050904021219030e01030b0123132606011d1906080f061006030905060c0915 62
    0xc900c2540c0da03141c0c0d09201e201c07024800c565000e000b0080005050040040140c50fa080d548600c00d14003154402e5402008125815074000b05010002992101130a1290501903d4111041e114907848080d0800e1040e100b0101c81241410b8650030541c070540078242d6001404d59640240c0c0c15100e0750103103840c80e0b1b00350300b0044019070241020345241807030580000c0554080c00741104c07034049880803e02c5103940e001c0900d81c01940c112420004100080001ca06050301c10582040e03101540d800c213014150004c44106c0c1018007642c040009662060064820004104d22455119140c0e0003000002c50804c00038080d4004000340340790075030390399040885035401240100b40055080b000c0d0703000454007000351601502c0070035a802c00340345001c1800c1200b074400814445001d04200c04030703c1410309039445440a8040c0c0c005079103101b1845844590380740802d0714070311a42c07030340c1d001d00041c2c80c2d00c00d02c5038040542c2c0c490040c05081c0c5511030f400d9010303044201c08a80c00740208590000d20030300c0c040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 661044973 1250 661043723 661043731
    0x241406371b0309090b0f0d1223090d06150906150503071b0309030c060c0512090a060e03010204050415080c01020109030c0209070e10020102120105030d020706081806 73
    0x42030aa030011418010a06040780220340d503000c1210a0410000c0c1d0002d04201c02d0f6110144002240364012001031403040c100c1907803a42040380e007954041840100d2103e00c45043c15901c820040e41c1c030700c3d10a01e9100f2650042028020407d000c580034925090b040e40001c28021a8013040000b4900d50b4071421040702c0c0d1001082d640c0d658020000b460f24401440f850020078200315003103191043c0d0213400144580240700f60326025002030b000709400b0341c0a000141d5000070082c088662691005420009003000566082c4241707521240100c070440101d40e100d42000d0f16020341c01e0320702601501e07e0349601c5071480c2d00d55000d01c004a4161214030800c0392003030703141165446580c83c2c50b010904144c1c11041c641e0441e410000c1c80404240c110200c1604554142c51102081d6511982140c0c00386a16488660203015810700382620741e4150050400143c2490144800c1e9903140100f5075900c6c6546800d20158224030410003480d406403924179401611104140800c1509080d03903410810300315 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 661046223 1250 661044973 661045057
    0x14010908030705130509040305032208030a1d07030203030a0507050106050d030e12240601030b1002031b030319020f040b0705070e0604140f0703090506010306241406 73
    0xc00c40503025107224880e13000078a415152a401824103490003000351000504e0f10304020760300c2600780102c40a000107d00420381001c0c1c00c03500e909145409502070500e01e00e2420444d05440c10745201c420700400e003d02207075401402145030007030804080e51640c11118003a00c0e69540c4490000b415190313000030442451081d51003501d9038001c101080000e9030740038503541c1c1a5000061415580c07644c20000c1c11501010607815109640d0b41004a010f04402c00405802031300c42200b01d070710a50000087c000f450700c110417421401c0c0011813902c0d6240412211040031340c0c4c3d00441e100301c00300161f008001104000d041185040d03200d18125105901404c8100c40d1644400380401911400c40f805036082941200d060011103001207140b003144d00e010344144140083d26011481c043e0103988840905580003054406640e0740c0c0c00c0c40070003010340040300385c1c1004015101940520900e001d12050380c1c3c004490310386500d40481031000640200041780410301c020072008203c2a90460702044c005002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 661047473 1250 661046223 661046227
    0x190615030507050c0706050d11070f0b01050d03080402060901090305030a020303100509010648060c45080d021015030206130b070804060224010314010908030705 71
    0x200024101c4000420b10010400103020030700d0481e8002c500300302158035510f401e988400ca1802104010400304001d00c01d200310002d400c80c10421300011011a2500424901d50721783e0740c2c2c0050020651900314001c00050034180014018541000503296a0300c061604c01da00c03688a0b640c00b841c42d4030880032200540c0c004410030201240c02c2c406403001d400b042e00d41c114194940b10014005011a1010415041d0048078840380ca0440c8074803111003120b10844084201100802510030000440c826070307005003440c44110324240038035010b00340642800c3d840e05103401030321049641140c00c2404401081c001b403010384a051002c40c01c4034058100c10f4050001407031101006427505d20406441184942001c000308110b5034420020002c4a0301512840d50340d002c100d0035841005a50780200e1742240000c9500c1041c0035510000d802900c290b0307000c6031501c1d01c0340482d40401c4016044220b003c0326a040043c4002070b10191141980243c8000208030301d4119602c586590308100c0d9014006200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 661048723 1250 661047473 661047509
    0x303071a0a091101030f0b0301061206060905010302010917030c1501082b0e03071809051b060304031115071806050c06061203040f06081b090109030b1906 68
    0x4005600125080000c01110b401c5940d5020040d850500b800e05040d5195032561404a41e50448810808014002c21610380c07124008180941d0b84003082c1d4603689001d0020030040e00c00c1c07140c5416650140c442c1040d8902d045540d0014180c000c0180d8198001484074000149017080b4000e2002260404d5128030740c107128400d0300d4918140300c580c1c0320500718a5400600c1c040e0030301e50707011140a45001441902c440010130711344100c0c0e5106d000d0000d2042c0c2c52002d0020598411219507200e402941c40858116220140710b60420780080d500c01010004503002a0152031441d4030105541c1c2694001c0c02c02d04100000c640044501a010486180d446440190002024409018070303041c2a030614020980300340e40c400300248050f00a10000061001c01101002030760000c2c210032051098a58940d40e008011200a45182014249a11422036003100c18000d907600d515041e511484e41d42d2031520b6080c62100058461286000409030100b50320a0600444020300942401441502c903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 661049973 1250 661048723 661048763
    0x308010314010920121501080c06072d080c010501090e0d0c12090e18060a09021804150603050c0f01050403031709030f0309060412020303280b030307 66
    0x650310300c0000360740e4586041d15002076212502c440400b00f038401c569822200280108070081c1d42c08601400910444418410070080c984444e4141c5400d034058600d00c0004070140080c60041c444020201a01c2e0300c203a001d002140410300d20b15040d030104501c0f402655443d5a56141d003c2d80d1180721a94540005020f6850b46000d0741c85601000c3d4000c012240c0c9501000708044140c100c000c1244403280b49003141076115428200c0a0484400700402a080038194000714105049510601d4080c240000716403042c140700d1010015006840101400c03480e0040f030703116210041045507180192180c51462100034400c0002440c403610042200a140c081041030088440490030704000081200340006a070100100707020071a5500c9040c000c0e240e02d0721113421800f506440d8101e060020040042c0f03014009001802103014541c1c1682c1e50601d00c108980301e22045481c1c0f07044000c0e40004001c4864072403420001d00700c002c1400109003c14400113415940800c00c2039030604044007003040e600b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 661051223 1250 661049973 661049993
    0x7150f020a090b040b0f0717030f1819030302032a0a080f1e18010c1d031b150c01060f05120f0705090604021201150207060201140115090b030403080103 67
    0x221404100c0340c1418540784117005c0301d20580d8920100000c02180b035404200c0410f00040c05881b148000319100d251003041290040c0c000c03100703009400303404078080b003100202080390740e1035542001c50342d150180c840e2019000b940c005001c42a0000d175001d00d5040c1d0030b201440342c07502040f00c0324420384c3e54000c0400041c071804001c0c20403000000d008044c401c0380c200005903101c01c441d81c428000f0155441241c00304110102e0901c8040950800d01840d41140c2d1210314014448048a500085665440c00703041e5107031002c001c0382200e0024001422214503000e0611009000d41c15059860521f21452607425107201d5407003590122202c104c1440701d031801c0d004043c41031024a0003800c0c02031089112070740d689090700c243e40c020780115000c03640b00c0d2100c0c2c040b40c0f02600003010241541d6990300d41c1c80e0394010888038140060042030404540c0c68070600400d401c4113517041803400c860742044040504800f04406403010700112900004050b8500000b035886a402910b038900d1561560901d16648 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 661052473 1250 661051223 661051229
    0x72007090b030f030714071a040e0109020c1e0c041e0e0a050c0103050c1b0a050c01030e06040213060e19140105060a0809010b060d0e210a0507150f020a09 68
    0x40d800c40d5608550114001058456054001b8540c41e52000942085410000700f82c100034140c20402d800e407440164488000c00c1129030000e1032581c00d071790b1107554100724010245030390b80b150444071103001c0307080d44200e020324600742c50700507101541c51803000174040328424034492503001507400c480650003440e84521002020300c140909002d41840d40c3d030540350703500d0386525410b040e501d6001c208404042820740b0015050450409101005035a40d5a55240c1600084a440c811500038451139482070080d414802a403400a1103940c940d03600b000302e1120074001111140e03036619000190f807011011028040d036008030518a200303d84820803400d0751007a101640c22410078000421581e2105422144003500a00c2c0c220b00300d844218106016000120302c80d42e01c400d011545910090351948106003492003a021100c20300c250f065610f4203040099295101e1400600c07a600580e80a0f00c010081da521411b130b84181c3c00d0150140c40c0449010300201005680e000c2510400e50b41c11218401c09 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 661053723 1250 661052473 661052479
    0x80a0915020a02100e0c151c0612050d110703030804020609181902040312050c010b031f051005010e12010e0607050c10060e01050f040b04060b0c07060e0105090405072007090b 77
    0x6c0345160004204090080144900a5a80012032006816140340d00c40819154208140402c83c0d4401000052040c07042044c0c55070301135198400c942c030b4040d02e20510f60589490261040030700d180c90944504200074000e0b80c00104c01c00000c40d20b40e440f80c0400306a0581c140500e034550074005854a409079000d15040319551040005202003250854000c44c020307103c0c5080e42e940c0c080182c0d4180900000e00b81243c1620401000d505001c9081d081e00c100581c48440070000c030f6403030750f076111202d0131a0300c0b13040e002c25110544030702142400c50003001030082c101c002181c10058694060314080d02141c1090000c2c5000c100304400382d2040c41540300c5003511940c280032413400c0c03d115804107881072050f588585078018080c461501c6640101000c04801481000615a68000d04000c1e034800f1030001407500846001040b264011003092a42e641c040c0d51f107030b081c14144d03000c0c4801008003403c440c0070720100030b492042015000c103a01402c00346100c06008c80e0341c500040314094034403800070148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 661054973 1250 661053723 661053733
    0x5070f02010b032802030105070503071d10080c130312030e03180f0409060f050709051012090c05060706140a061a070804050307120312020406080a0915020a02100e 72
    0x84075950008032080842c81246664034079000e00e04d0302465a042000c0300a401d54280700030005155004006503101d200c850b2101c210a031342c100360701055994071004980c0d11011a8800301c00161103180443d5103c403180e1036082c500f109034000c9180041041e03004840045c401040e030300381a035040c041d82c0d80c040843e200650810350800f2181c030b03485040d000c2d0b5074022829010f100d450742e982d40c4c0081d143c01d034100008214803903200300a00c018000446444001c00c0283c0c90006003810000300380b180300c180a81d60882d176010448070f000054800554180c3c3d5040303800b4000f20f5940e4603140100704140c8561400107559200b14203040014030014001c2c105d062030000100400e503034a54840b9815280e00e0700c81d0780d680000e8580000d00d405603410058061040c2140403580d440c201522504090107519004640c0c050b9250071416440b807030161800203450079000c10f0b05c503407854124002e81482540640c07954104a00b04d80200d82003402504011303405118080c1380503281c2d2180e11004841c14011304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 661056223 1250 661054973 661054991
    0x10305010f0504055703060108120f1c0b010e0406210c0305010e033a0b040e0d121104050f10030908041d102103051c05070f0201 57
    0x107417504921655000c0c154a61030381c0000100500301d001000502e01610740e0803441a00e014001c2007428400c450201440344001c60489250000c5d0560403104d4050060120002c01c002e07050170382e000300f59061840c80060050b91440d03080c8040030100c1c0c80307001c0c000290700192200010120242061a240140c1c0360003002d008852404856050955540d80c813442d02620034a070108186055500107400d80d46041001400b101d0003000920780b0407140c0300c600d003114842510808a0310325002c403154004c0300300760307109845000c02e404c144c0754108002c1001800b0316030118079a060160070000340000a1031700d0450901b070000c0e0b100d203000546131002881d0509081c034000c10100c13201340001e9441802c4003000a031002d80310380c2115841d198440704041c0caaa4ac3c03814208c14406040c1100e000c0a0344043c0060b08144c080da000c40c00f01d6214280c2c00c00003480300d072021059108040301c2907007040340400c201c024441c91340c54214034194244070300142c94505804010b01001501b1081421a41408104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 661057473 1250 661056223 661056233
    0x1032d020108131703040b0603060705040e06010e010201150e180105010f03020d05030f0403030309120e01091703040909051c1403060933040506150409020f04050315010305010f0504 80
    0x14030f40c000c0001c00803280c05080c3d42414000c1c0340b10044c0d9803a100300c1c00003c000401011102c0036020310710503011192503454043c42502d1174003a80c0070b034076511411400001c50562003039520103200b41060000091141381c0c10b09080702c607056a00a032120409040900154101c0c4480400104400702c3c000c2105506101c251a142012484042d214001405080e002d02006008446509422401c041c0e62030b0340e00d01c1c0140150201c014107483d8007230700f001c05511030b0740a07d209141951050f5101c19026003440420b2001e02004503000c80640700c1070102040800651103001011406180101810f2041090320203c200400c6007010802036100140c201d04149882500d8003c03008a43d981c40c95501d801a60003000143d40004c4032050345400c14160186280002283c1079809540500c25070b6210000c0c00900e07450b040038108070600c104400c204190696000c0e20508800c50700d51868240c0c0c0e040002d24040641c0016110032007030714010401c1200c244610721440100c82001d0041d80703456210 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 661058723 1250 661057473 661057487
    0x1a0c040810020f040e010609050411070302100f020c0d0512100501020706050a030b0d2603070f03050402180915010e061c020102120d0b010201050c16021507050601032d0201 76
    0x85981c541e000f003180b085519000095401034048640e210074a0340e5609070040141c0078900c551030041d031a2000a50070103d00c0000c460341640c154000300244900100a0401032035860030090313200f0707030a202241074508140b20744072050040390b980701d072120016404001d00740f03c00b40c03061254455160040000d030b43c005c160403040340c1c00d9080207501c840c91a041640a00003641d20030f0307031011103030701420108514042c0210b080b911020325100e004004d5400403511f1f2100b55034110124a0404401e20042e1181d00900c0c3d01510141004865402104980c0121901030704c0c0c9014582000e12112103480100d21803c0c0180f2a000640b1000d04200d03000c82d00450150206109045100c055030f070559001b00015000403802c01c040554070000762107094010003113003031214015400d04020030507207404d110684450070314801e182e44480e481c41d402c200e001c19240c866a804003000380811004550300303201e600d00a500071302d5441d0074030082e0b00c414001c07041744205030300d07042e42410240c50142c0da11280d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 661059973 1250 661058723 661058743
    0x50609060601410703390c0e27070b07200904050106090b09040b06040c09030b0c250506070f02010905030c030a030605010801240e04091a0c0408 64
    0xd50700044410354502c10460000e00e070710070382e00c0b291403030300c903040022110061101c20300940e1010388108039196120803c50326440481e0030701c481551624038800c0780c0b00c074110306e09200328039454850b551444414065402268a01074001d28148078559294040e1181f400041115000e8100141020b03d05049801880005010042d074000b9890b181c0115145008807800014808031841c0b510345800360203040703540074440e00c450904801100314207006070514000c550049a0041d80d545500a00006008801c559000c004c0d15110000100b164005041c4c01101c000581903039030405000084416040d80300800142c1140b0306030301c00820000f08860380c10940515081c00c80200541c000c80c094099002c010b04140800a074640b180c0c0c000100a103140c4030662020f100c1c40380e4410041d58000030034414007030b010007480d42d5880704c0d4070104108031541070a07050a400a24244011908a981c00c0340102d42080d18801c410300e04076090000302d13a000d44000c2100d0700d0182025038007612884001c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 661061223 1250 661059973 661060007
    0x8030406140904050f0912120604240e040c050105041503150b040605180904020105070b0601051c1505040b06040e090316080d060602120702060a0909020412050609060601 75
    0x240032041c192040044561420005100740402d00703101a03400c0c4040c500750b8101d500c2e84221404503180340156025505544035900d81010541c0d158020b11014023240401200e115a0b112901c41030032407032241e40009400302945840c460f1a05142907640c1205039000641400018041001904c5901d6554100e4400c030389404a500901e03102903030032040d041c0e000074459010225001c90450f90101c0900708080c903078001050f0b03489041d41440292007007507d000e40058010084d80d40460700d0007a001d904220180341192405200050040c0d81035a90408110629256426003d1000d0681303d28405000100da08202c1000500006040c61140303125540c4076541900020345511824030640b40620154212242481010300d043d001c160f10030002200720a2400002013002c0b407000468180b55000e1104c1103180c4159502000070b660400b000d250108070220348007042403101d41c000b401c001c0c0048400040c1d010054a411420704200400e425800d5022a0070040141c1c1c0c4624110341f414108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 661062473 1250 661061223 661061237
    0x61f05060403081b01060b130e010f03122c0414060a09150315050601140a120b040f0c05090301110c0a230d0207050108091b04020307050d06030b150a08030406 70
    0x154504c0e0044d020400c0300481344d52a0550018a5403040f0f40280042004201c0740c482c01521000e00e940c0b04131080c0151604202c20603070510008105034a048400e40c010705169000404511500d090150101c140071060340c0c0c0b6001804540c18103001f030070740d0b0f44240440c2c52640c0c6050004555000528450300550303a03120100c80121500d2510f1007000345400c07a09a0a4505258210b180608400d545090000380b46140d1140503c6040054a048001c40e5079018149112441c10380040c00445200d03682c407954038104856044850701c5201010007554070760f40d0301c0d14002002c050845140c20074444156404000c460070001c40801d54100c40da52100d03100d0a460000c0d00c1c0c0c80b4040c3e044d030380d0b42c520350f110760b045026245400203400012600260703500300c2c440c1d482c2c09a05441301c605d03501c0b041e05da54204034054464609600996840700742442c3c80d504002ca16121981a0b0b03406a1085d0381e61401c090610403080d0b018000446008015504e0a130b03c64a41006142d0f00e200300e01c00c403410801703c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 661063723 1250 661062473 661062487
    0x110c10030905070902031012031715090a0903120b031c030b060309030415050903060406050405031606020d0e010c1b060603080c010c080f06010e130f0e061f0506040308 74
    0x81c0d0300403a038498209085602c801d49940d4504000e40c4142c0e0390b55070b00e031351b01480003568080c2ca940220000340c2c1a0b07030f071032011000000011164040a0310380d4110500071405030303c0a4072800c1c2d00c581f04820f8020080b0310140f0302d04015041001c0c0f00d41d9015111f08018010015440c0014078104112100606401240210800720020702400740c0440d444400002480a20480040a00181d8007900700c8080070014160b4151064440c100d503403078150704030318001000710300d469003c5903100f030003002a285441d250a600c40d40f58800b61358220b0344141d010540c83d140d4591440340c10090b00780d11008100803136442c00c0140c030b1004403103000d40a444c440b00d621810445190810401160302881003525a20700e40c00c1c1034082d19031500440d0010701c42c41c0015881816095800b0300504041e1034070030140700e0340e04c14440702c000040318801c1c2541d164060030542c8401e41c402c00450080c0300000c1c1c80039013000e1034a13056003c00c200e022190450100c405102c140e0302d80003100d04603a8803140d001d590300341c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 661064973 1250 661063723 661063727
    0x1140d050c030a05151006080105090628030515010501021e1006030303060e06040b060a050f0f0705060415060305060a0203421206040f02010504090e0c010807110c10 73
    0x51691034007034050043c803001c2e00c00c00000040c108000c410050421140390f885a0305032024100c18421200040d24040040105080c402400c54000601400b91000000603041c10380c0c40040c200543c0550168002040041c80400e002c0041d0b00d400c40c50780305009516000000b9901c1c4418466008030360364861140340501000c21010282a6003410300380811584d03801d024005080034030071403c08691500c0020320919140c070074141480e4000b00914140741640c0d004440c03c0d0000025039031903600410224040325110000f80105500c0784006122a180619100310300c2c44034049840c0c901030a0100070300001b034011401540c4100c1e40c00005072659100c1c5041e80002440000e0550740c00316441d540c070002d4242882c1820000301e1a00d4114841001e4170900048944041150300260000c001040005001441440e003841c014540380b820a9251880b03001100c802044a5006a0041c03080d29101e513082000c0d19803141d90350400c9284950714109058a4040110407548200110682c14550038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 661066223 1250 661064973 661064983
    0x2191508040f061d0604030503010905060102010203060d030509150d0605041407090909030912060c020c0d080904021b0d0302070b310201050c010f050117070503100e0133090501140d05 81
    0xd00c484c0803a985403c25007805411640280100c0340c5990030240010728950050080b00c1c0905405095071140c0c16040d1011070b655082a4030b9075074044921025444e8800d400b0001e4031880e0b24104001070314a01c0c0074104001c852030000150390b811a07110821545a421038400c1080f0341076083c0105d0000800d10701201d103c61190860540c42c1108400d00d03042c800c580d0701c80713800036a180d0211130220414000700030312540020401441007800300081e65860034560050400c08904484c1d03c0c12110090015908001c2414182c800080d40800d0341c1041c410400d400e15004000c40c0752449485e0702000c6502d0400620b400100400d0307640120010441e44070390111003218850a00070040003113090f2030f180140800b88a001030914165030816140c8401044134803c07180d00400421031105010340c1d04010342100c482c90f100c0d80d5600c9141910600341c44091500b85070b95080342e480d6410040000c84d443d564642c0000019601d00401803029824140d1020503034502191000415086440d1240c1341c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 661067473 1250 661066223 661066271
    0x61c140a060e0f060708160e0d0507060f0927020901170a15090c1b0c05100503010509130312090510060305070e0a1a0f03030702191508040f06 63
    0x7561070000c09440d482d074085054404401c80034203960761903d45100484c1c1d0300d101985c000101c40c0c2541d00c0d60325501d00941030700784a090050509070340c1d1010390301d40354201001a405503003c1604a0802d40c11954090a01e001070000d8032a4800005440d00c4c110740009503c1d800300d040540d0005803407a1503070140d01980c4200020003400107030ba242041c08140074003a44445958482d00e01034011079010102d0040880e44185507890305030a00c02034541c41c94001d03160806480c06400744501250300c0d140d02802043e5020b42da210345030340c0d504d01814400d039040001c042c8119110050385050020f58004040c00800c0a10368002c11401138904166080000d5805c00025080c50120008100300d0080b401c01c04a40360850845a02c0c0e46080d840010341d003403040742101d0002c0084610340d40d40b52000040360003402c0030b4103c0c0e041040d00d80c0460400d12110610403460018402d0800c61841c09058801500c1010b00c3c01c0412420306a0b1070224664036103000038241a11404503040300c05805200c4a10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 661068723 1250 661067473 661067483
    0x31407150e0c0607080a0309032007060f1809020a050427050601020a0b07051c05070e030d0e0f0405130c030303090b0708040f0210140f090405061c140a 67
    0x118945a02010010105089148594040c42c2c20a90140c0b0700703001030300d203a1038109a9151404d82040302c11002048d41030000c400744054207a08941c0203028180c1011011400d0000300546030905030007178581107050f200c443c20480c50025500d200150b00c1c10342004c8a0a0f01c0780580ca650003480150b42a001350b0300040711955a80c1c86000700003080d80b00e010000b0f40c0d11f010810080d00c600004a89a03002c061000d04510281800310b580b0910503801011040891848421400c1980d034401c0d0913181c003510700f5800228075290003409482d0074443e504001156040070040c0d581d400000c21000c42c92103010354461a0b070b0380e0004900f042880034854145074480020304825440340b50240c010301c403011056580390011000284854010980b075806940c00c000d9141014401e5401c12561000c0521030008200d02e846103181a4a11302020b800180c0444061584860340c01050204071039000300f40c11320406246d040c0454098100d9040c0c0e40d81604a911281d5200301000154a800c10031180244 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 661069973 1250 661068723 661068743
    0x30e01020c04020a080a14060a1502010f09060507020f030309071802041a0a030501090606091509031b03020301050c0901140705030c0a0b0f09010606050f071e060c02070807080703031407 82
    0xc0c00340d0201c5c1c1c05100310f8002204004a042c26100d51075003240807a10f491300184207000c20710500c0303890302540c0003002803880041400c5409410720020f40341807460454440d0b48400c2031044042e0103000c1600d564074503100441c203601d0100300c8079948138650f2040b494a0003003070a038240c862295404540140000c0000c00c8010818418a4142503101829000019203081c00209203840035014040842c2c801d82d03208500c2d80c0c1446100b141001c3c0030f60030182485510000040094403880c2620302d5441e0440c0041c0580c0c3c80c50040c035094500051611801d0704007003080c00312581e04601e010345103031140000c01d41c880c0344901d0128a58440c2d00d80c0e90056114000004e010040c1103440d4034030501640840007a04c0c0c0716000714500b0703113045020703840205a06210b1040340c0c150781c40107401c2d61030013051034030000902102e580300b201840d0401640d195441d407085c0001160108130260080c01c0303000082003100d01d04028a070320b829107400020100442055841e4515943d141511511900103002039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 661071223 1250 661069973 661069987
    0x27020a05011d1005040e100503100b040e01050a0e120c071215020c0102091806030a080f130b0306040608150105060a0e040e0f0d1b020904170310030b0105060f07030e01020c0402 78
    0x54056041781c4030301c151140800c40020303110f5083e168000c0840d0b1001c1c00402403590203c075054003400d0109603171a081130b42c5603410003000c0c1d024002e85001d2642407400050035107420300c8207410810017004c0800001420414000d030400002652421640c000c02d64400d1391034140b034401d100d10816120182514008209902e000406600409400781c080f1058106074401500300700c0c1c408011200542c0c107400206111021400484c000c000039202d40d00030610304030800058162584071034020220104c1c000c01040700c1e030704091217840003078074004008100100c901c214510080f40140102da00900000c00c0c880c0000d40070701040000008020403d00001e8104c003e07450386c9400b00c00d00354032580b00b442d01c2041034500481d00710003210348410400c40c9040f0b4640a001c07240300b000d08122011080c036441e9600c980440b03c0610300801c0483c0350a50004c1c5181000c0d415040706803c0544241810001102616000000c0b551902c0c0d050a143e14880b1504006038202000d0b1300030b507600503000085503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 661072473 1250 661071223 661071227
    0xc07080105060a17060601030c0212041211030703080a05070c03140c011e020c010302210c0403140d0516170d0f05010f12080c0304031527020a05011d10 67
    0x56100b40010707a08840100da4031081c40c00100108014a4429007003900442c0d2254032980003002030044500484180d8010800c24902c1c50f0300c41c3d8858600364054620101c10400c2a00340e4001c0e0f01021030041808034150781310f00049e0300c640c4990078140000018500100035845d10a54000e5400001d20000302c40c0d81da040e42d031070b00b421400440c00520003800d86100001346c0480b5110040280d4006c0c01c4020715100154000e5100080b42c4000700a01d98120842e40a40714140c2d208603441a030640c4c4943c503614211482d00b0b101c080229503600940640c6110690041c20b480850680244100c00c1c06142d04001002c2c030b6241c000512010400511950b14403140e8000400804900e44100100ea90b68040200074562600440301c1c0314003104a01008a00044054010803400d982502e01d059030301c1d42d0b03001e800000c001c3c60701c18030768a40254900350280201c500380b240d527007140304150700140750340001c8041e5901d0081d181030006001507022030000561200c642c481c2d01408060024600c0000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 661073723 1250 661072473 661072481
    0x30c310203040204180b01050d02011403130c0e0408030f180f01020315010216050111031201231c060c050c1902030d0203190813060c0306150e0f0f060c070801 70
    0xc141d004a0501001179600e140d810078419525820240004040e400e03e800c201100408180507410458000c040403400c9031050001e42c0a003841d49001000c8841510323160843c068543e102031100f8640c0310812021a0081d4100c81e88101e00d10109855584c4401201c5240405016a00450711138281c551002e04415802580580e101c1080d644140125400499541c1c11110045c11800340d166001c01c00d0354011071091380da00e40e114080c0e030b00340380001e003034403409520076031018001948014100e50a00005074061001c19015200201146014200226401d000c0300c0001d12550b515404051401c0c454002e444141d5490001c4d54010095611401c52541c44403005900c03074000c928030107403064000001c983c40e8131004806580d44802c4650b0a848800300100704000506501c42044001441441005000b489544000501c40e00b4690302c0080440c1e82030307660043c0540302183d40d03529900c003001e0740042d03002100c0b044070b00745102011841d203004132110103a042c81408001b190007001900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 661074973 1250 661073723 661073731
    0x20412050c010e0321030603011b0903060c0e1e03031911062d040f0f0305030f0105040204140f040b063c1204050f07080318030c030c310203 62
    0xa503d80d0070b40040c0b0105a11243c0241310f444d5042486550f0b0390080724144055984281c0c01000020240c0c4000d1125840c507980d20303001030014007407aa00740100441846055172200300781c50840e5120808002140415841107007401542d10400440c40b640d40d020011580c95200342c0c180c01c86400120078025003079100c1c08007505d0140c0581400240100319420300c00488004503030036070b040b003522540d08286020003c2c0095400f0070b4100c0740200412036110340c06081358441c2d90b40c41da03240342c0700c00018000e03401a000140306600400081104c0070240a0203010f21070120b400b00c41d86002d002c0040c5c0200b44003c50b564001b000468010343c40b0394144020182c002846078440301300103500842d2403849032000c0001c0d48098041c41107504035502c1147e07456100384207900b04c410380c54020703524900d003042c190f0010081e944005011402007000038181c520445099000701000c0c1b0f0700c0000a0f803540400c0301c5040c0184180942d0345080c64031000c0c000040021901c1022000040716030384800707544211 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 661076223 1250 661074973 661074977
    0x105090912191209170309010b040c050a170603120a0215090f0f03070308010e090c0d0602031501140706050c1308070e0612072121020d02030705060604020d020412050c01 75
    0x1440300f16056198040d607910540c0c4010301c040c1800381d0b18030402240c1c101400c1e10000d0365071a11410070b10b403079901c20410f111505444040d10740d801c40c1d10060031441c100d80c0307000c0d0b00300101040c81110f031000105400d0041120340403545460b030062089144c0a06e203640700d0b001c440700d032080c0600d40001207040c481c1e22032078005440c0360450f1186119544d110f102002070009005000402c0100740f0b0701182c41c5c10401032400c1c1c4000b0000d20000562032a83e03034806403220b50780002842004142c0040c3c1500611080c02c0892407442c02e0030b40b01c0c0d44c030300900340068440d945440000c1c03444940c0e00700300c8030001021704100191310348400d082503407803a29010340020b07580c480300400c2c40d03458242c0c000e00009202c0c2004040300da0810810428031450318803a1000c501f5100701c848002150b00c41c1c484180c68003e2003840c01c440f00311600924240903500040155041000044046040420415400113065070090381d25500c1c999050028411903104000c212070403a00d02c000c0103004281e44646840903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 661077473 1250 661076223 661076237
    0x30f0e010614150a020a060903030207150605040b1503060d050708100e07053c04090b06150304020a12020d02090103050313060306060219330c0512010509091219 71
    0xc0c482c0c50403d03116003400b44e000b40e44034004180014110340c0014034158800c3c5405030525016076500c10001d80032003103a519031521307020140b125092501ca504c4c4c01160848407081913548a0007102c6c0c3c0c46c40080d00f5107000340550f201d48808e01c2804c101403030040030204100d5100f595129100b00007003500b00412442401030b113800007003614148030381707118000c1b110b0041c00c0e80e8804410000b4048814200804d00807004101c24945581c2d1486500c18943c02030300c07814040d16140040180c200e003462810b50f2407640038070500c805a2030352146141030340c1c100700b050100b5000c03500010301c44140c2d440001354066008000030040000202c0600300542d0090904020710307460702c01c10340603103d01d4026640160711a0302c100356100c0014151303070011030082d50b182800d00f450381c0c1d03114910050100b004da50b002c402c18200e0b00b10103007841803107a2000c152502070700700100190413044540041c840c3c5441030100c4408100c09030414440070f000141d0001c0c1c12581c800486811a41c01d840a0007420081105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 661078723 1250 661077473 661077499
    0xc0604050d0c03080f0a14090c030f0604080405060705100f0b0306061008191b05030108060109050c040e04050c090405160f0b0415050f030a06052e030f0e010614 71
    0x26401070003065a258841d10080d07610303c3c403904c01e4050010700f20002c2540f0303580100c7c400c0d01030181c518010352000000e031182800b02024103181c0303c82107405c0c0c1c01e1a0300010404c40883c04020903641640c00896501303035100400d080641c0303015210301c0700c2d50605241400b50018401c1a5000d00580d0109800f681c840da1360750810080880350100c5400040f07038210002655a88005400b8500003030158000a205191440e50703403540303051204c4000200350000018003c5100c200011401444207141c1400070346840495015140140c2c411006460300030800300301004010b04c06141c1d244070252016032a85001e050042e0764040035003514881c9004000c0229001490300151820b0f02da84000e40781c074003403608880404070008082030703c04000701849140d4990401d0f4000b14007c43c240c003c0482c0c40b60901341000345111440c6942020440d400301101107240812040d411924060300b000600c00003c9102d280103000400700c2c12001e07501e0207401107003d2186c0e0340592229a0150341e071501c0d00d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 661079973 1250 661078723 661078727
    0x1090509190303021e070f0501111303030e1c050705040c0c021f0c0b0a0e24040b060604150c05010b060a020a1719050901030b04020306010f1d060c0604050d 69
    0x24860040407000c0c0c0380018500c010074001c0d0010000c0300f0051882103202c00f90111156025084810102d5250f0041500311082c01803d0042154100b00da200c16898015100b100d10180c40039071000a050043d40c62641c42e069403500c00314000c400d80340c039401005c0031461811a803200301500600c2e00c50741c5040025602d507031150079001c07a00c59025200c0070130b2800c41341d4102140b10701c4000040812150640e05800960400d43d0a4010304040c800800d03d64101d10070942030841000a0b40500300200c2d42440b510044071355006e4110360068144003158407018042007892103181c218208800c103203094410640d60114902c0445c500410013006140110350400c00b0b035200780604140103900060103031000c00c980d444940e440600c0842000d15082400c0d0b85038000e1050151040b011500210301c02c116540c140c05640084801143c0c21861803810b000080c04143c803034240081042421001800040014510110501001042c01e038036411120050340e41c0b003008a6044a4a019881c0103000180c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 661081223 1250 661079973 661079983
    0xb0913021309022d07030f0e1e040f020f071109010510050c01240e060102161401111006050a12020d021314070f110c0a09090206071a01090509 63
    0x9103800c084124981e00d0451084069000f8480418000301c00701300402c400c245404120f84040200004584c8440da1420054000c0d0b03a086002c40a01c07108420920456a4001c14500316250603e0280d4541c1c0f158008140200051343c0c0481101d4400280c1c45402e445030806410410b200c2c00b40014a00c40742010b01040410078803130150403000071844d410f04240034802410320701c7c4040d8000582103c0804005151551160100110b0310000f02c040c8251842414102ea100c2400e0000b000c501c402002840f884901912800c958200f403c0c10540c044d07032060a4544c00030403c2d0044030310b042c85040e9134030002c2c5950700c14280300328042280011040200342010703545e56001415103d00b6080382e0248200c25080c44101d455140c1c0d02c40e031159400c440c0048040c01100b40d40d03100c040200d581c450141000a030f0001081c1154080c42207104143c0d5024030840645180c0740300480c0041d000c0c070201d101d5006005009000f05004010081c52503c45000e8034120b4425000c180300b55190180810307114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 661082473 1250 661081223 661081237
    0xc180303090a050f031f050601090603020a0801050f150d0e0c03070e070c0f0b180111070f0f08040b0d0509070b271504030303020c0706020d02151e010b091302 70
    0x2040822400f04903034a82520030042c4180090151440052010b20544034030011160b03212400742d0341e009010030395911010400203000c40d03040c11481c0c2402620007400740c90051080324420340b280100c030360468a0305180d00b0250302d44104040d4483d10f641c007081e00034060305e00894056114000d100103861600080c1902200c444041c2d6040b5615006001c407140500c2d0718054031400c0441d000c41c8005082600740354405c07541052000a40c14030003607160309542c1254a090394a503004e0104502164a500501c4645a0720218820341e0240707510b4881003c1c0142e078046880e42d4404102a400390170903402241c420301286003681d08603500c43d4401d0905004080401d2621307490030100c48241c005003141d04081d070100420384021b1b148030b2680c0b0783c41c0d0b031b1094008400080e00801c0038280403a040203031401501e0240090611082060b400a6968a11030840486504a500030911b4180b0403608000c0794104e100e800c91642d078440b0fa03c00d1082d4441c1082e1401000e004240d180611424402c0d5650 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 661083723 1250 661082473 661082479
    0xd11030106080c0d02041809020906090c251b15080403050901030504060b132301080a080d0e07171005010b0d0c1b0b090d1d091e0c18030309 62
    0x10507190101d010103c0c0d00070520211000b5420071000c10210000700c102000c0e50b00c8024041040d01c141d106010705d10030080c0c561801024101c040c040054140c1007526501c40c10751000481b10041c0703e0484125601c48100542001d415624444450b083c0420392015a40f90a644200c1c014030f0700340c211060141150081d0020350184000005988aa0450754100f40685008a0b060660000141011040911143d4059959429081c420704408005200c0c8080d0688040e0340358034103a04191118000310004105076000104100b001034168801c14100c2407400407201c1c001d80f84c05410810a805032a41d00852003414003000f09000036004840c140c91070751510728200004507049401508a01e940c5105019030002503100400354122600c1c8994040c4014100034108807841a09100450480c0d10400650040c41c0040303545101c8040e165582c01d50302c010312580c0d0045011002d07003450000c0e10f0b98041079400e0228466400016010510b03080e81c407a00380700c0d41c40c410540d40384244911250 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 661084973 1250 661083723 661083737
    0x1060807050301091d0f0f0d1706240c0703021507030f08060612150a05060406050702060d020c100509060a180f14030d0c09050f0f1207050d06020d11030106 69
    0x1040c11842c1e080380c03100c2e4001c5d100c02c4002c3e00d04d221500c1d003000342c1284040c900d0341c09003031010b040d260308202c072034440c020900b40040ca110b119441001846401820a401901841d141e4150102e404101440c00310205c500c0d503440e195030b10000da8540c0c1c502d1005030301c507003076070030002c0b03901c80d40c003021501683d50648407450403400d1204251402d40004040e40e51107041844401c00344ad8001d061a4070442d4030054001c1d16014280c04c024552006420050151405000502060307801000704c4040d55011650035860320940d00c000d8000e417190400704200c90103010b080b0090341c20507800071402200d603a41600c200d5503503524008100d8a201d00c14421a030754280e9402c0104520414050409006680b044910404003141900c4d541c0a00912400c1964601c0781c40e10690340410307003001410301102d00c4580180a10300181c2e00340300e00382503284580241103000c11590401c1024000800c00038008118400982c02c118009402c1170050240007030138841103d4420f6480c3c3c040b41c0c10394a40c3d444200c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 661086223 1250 661084973 661084979
    0x30f0601031d0a0f121e030b0604030602070f03030f200c03040807030f03080106030c080c0d0b03070b040f0b041508070e06040306020301150f050a12060f0305030a0801060807050301 80
    0x402400315811a001091071882d0209120341003842245201c1c1e001e841d07100150340c0585040c1ca4a13041e1400090104281060741e0b03080c0d01c00c4103103512091403103440c0124006240c040007500a208a41c070080016200180f81c0d41005010010301c20541d019440c100401035400c1410130a03650701710040c0c1020313907030130030170910048101000c0d040340201281124286622080701d64a003150030b0700107a40400d0300301a90001c04d58468422030240c0b0041c9800c2c01580c0e00842d010b00303c00c0d4003034043c40b0180c002041406140040790f0003001205c0004003142c0049a4451500a89612500910078100282d403000b25466811004880840c0c1040650100310064004110341c2401d029080c1001c2107251640b0b10703126694030020b0005507000303400060303581d49000304000040004140040a01c8141030584800326004401c3c0e490512032170425082c1002e110b01c1c681d004101540000160311501d401c08014001d0000107806944c620380c4601001d640c803524181ca980c041100c0b80303000104204014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 661087473 1250 661086223 661086227
    0x90f010b102105130b0c0c1203180706180501020615010c050703050601032f030a060e070e090a0303051e1306111602151c02090a0302030a1214030f0601 67
    0x41280880b141e42486012540c0d9108082500d40c10703510b0400d01c040c0d5000312003d0121104215820030401042c003454014150038031a181c0c4241800300b42103d00c08030000e4960810b15a854280c881d40c003060322011602c0e2030002d482650094007035602e50510800100340c9500024189018014800314002070104140c01181c55401602080b640d60003500800000541e0820019028510034280b000740c070904405c01e040781d02d030b18142400151501095940e60b6444c041490b1040d10341005002c02c14112070b400c440c3c5442626401004142c1c0301c0d10810101e00c2d000b10f94224424447c0c4c2c2c050003551900426400000b00405141055011180c0460300f005070703c00511860603c20350012400c08024019441c690f08001d07180c030340098503040a00300318507003400d249069614101586081c003030441a13000340000c0504c05041c00a500044070120366444001850007554003c0450f100c450341850f0800046c42400c04600100d0001c0400c00011012034041e01e106540340c503040e0380786640d0301c801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 661088723 1250 661087473 661087487
    0x40b03010c11240c07260d0f18020d03110d2114010605070f020901140306010b0f07081b030c0a0308152826060c0711012d0305090f010b10 61
    0x4100e5006c40840e10754a590098030055659507103205c4800c03607c40441d0400441501c00c000c943d81011494450494007a812205d52040c1d02034050341e01e4840c81c006031500340d603c203000d6003260207035102d001d6524201c0d580c85170743e001504211101410f00200e246002d14280d50440071001d035485020401031003550311440150604500981d0f101001040c0c1e6004610b016a01b0b801c02c2d110105e207038490a6036410f041103050b00400742408000c0ca0000da0b514008407502038460700a0104200140070703899402082203802c41c8414050036207a8400c0c2d468001a51000300700c3c41140894440c400140e540d900c09140f018021401070300842e00c01b40798007003081800e01c2c92074541100101d0283c020480701079080d4116010801da1003030200f64082107441914282000340200180c001c20800e1400107504030f411000542e00a092007441c1c50301c0000721414038507901408419007046100c100904070f5241e04403901031600c007805d8440a01e00740000f0f07407c1c0ca0011041c2900008010701e01603146200c0c2407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 661089973 1250 661088723 661088737
    0x15010609060c0c1e0305010e0a0b060f0f1c03020d02011503020105070813080d02010e0307020a0b0901110f010c091203090b09040204030203070806150a030f03030209040b03010c11240c 81
    0x1200031284d1521207240b50190f0303a15182080300350001051040150900c0b884c032040b074448000f061000030343c1d074525500040080c0501c0c0203040c015420310075038507100d030290083c1070300400744000041040c00727000300d520322000180e00620070722007100c1140c1d0040c862110a042d400e001010100d046800650315076224020444030308004002c810010968240d1050182107440068000c0d80e4080000074251180c0c0810f94505400c10080c1d0401640c696104000b1950031038078003030b00c03240381000507180c00c5d68400403403181c2c0c00384204c0d80000e09810750001c1c1c000c10407929004a260b4440c00800160000003000501082c02c000b010f00a00844030050000d0b0000244098507068a946c0031070304140301035121144950284080c00003092a0309880c0800130819112036810a2858541000c14020000c4c040c0a05a00103040c250a841d030740c0280702c1600c2d000c0c0090080d00010000244901c0e400c1011403071034080d00040c4404c803003481d424164850034a114050311521141c90407515980510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 661091223 1250 661089973 661089983
    0x3070503040b060a08060f0a050106110709090203031201030309230d0f110d150f05090706050f2a100b0303090f0a05030a080406080105011b030507031205150315010609060c 76
    0x5013002070914000c11040388908959200d0301414240b0b01d106000f540c006811200034007280080c050940180069002c0c11901d100c5408180030126001213400d42c40342003400c6510362440400441407580003151901215014441c495105400686150850101003000380d405646a1034000200d00c241071181d1019018401c1070700f81c2141c20700014180100d0200c11a024481d6064105214a192080907145034003900180414076020000f191503040d68022801407040125481c1025600c04050f21143c0700d12524064040c8005c15202210352010100d0380c13468030888035100e9500403503000301f032459030000d8011810b0403d40020040f61851211080b81c204086540028642d0340811103002000d00075100709681c3d0b82410001408008140c01450511003010310846040344000b0000d1740300b0303802d4074045440c2e41503450100e40c5000410141214541071400b4451082105c802820b146a412421038011142c0f401c10620740074403d10070700b0007040380c1c0030042141600400004014a200da = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 661092473 1250 661091223 661091239
    0x301230f0f0f03011b0e0415050319060605030a0602090906030c06040902090411031f0e0118020f190504081e121b010501120b0105010302031006050c0709181703070503040b06 77
    0x841e05d18240d6100300003080005a0102c0800b50a0410f071003907849020000c0d1000b4500703401e080100e0350300c0007581c101c1e20f04000031100910910806510100180c03a005007903522a40490900d00c0c040c3d04080312441c031411580002c070300c6074a00026050301507000544054102850135500b80001e402c03c0481680094072580d8030301010070400000e500c521503134111010004d80112104868041d1600070b02d1401c1c9042c0014806045400f00041010994410150b5a81c00300c680d0f01d13a2078000d40542c0c05c0401003001110b210142c001e80648142d510324012a004070142488880c4030b4000402141c005810907071001540c124024010710b50150b459501c0c404440e40f8845090071540c099100d443c0d900c03c2d5501c0e40042080d40819140109024607003981581458004201075502b58441d44003842000140744007000c0b41444680c0c02042044002c0114180f182c403148050345861100b00c445e0900c40b01c900581104440a8034025441a65424116580c941c1c0b1400c0c003020141c0703034561103040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 661093723 1250 661092473 661092491
    0x32703050f0928050d0f0b060a150906031b051204051e0120092815050c0d09030c060e1903060e100b01170c0c030301230f0f0f0301 58
    0xd060301200f1950360381054072003120a204925400b0403568014510600314080550007040c4800b9030a28850781001035058182c4900c000101c01042c40c1d0b105403407005100c1c2c0075140da00d0b0440110422100c5030348007402034110728801500e204031b000d01c1c00004600284450b890540d030401c00190710600c28400c0700e4017003a28843c00607401c9643e040b4464141c1d115504051407100c400c15030700b08005c010000034103080340030700000c03550065540850a80310001461034141910b2510200050a05610018862401105c010042d511003031481401c0c0c0701d003420001c00c00c8c1c4030b0781c010b500b226000303442541e180d81001c2d8200d405012082701d2aa10111102e003000090550205a4004510030140000d5403d9003000040c10310b0b5040c1c3c810001285015a01071050341c025802d0341c60702d5245100c85a1036a18180d21918a0180c07620010a6100210010400030141c0f1010000f011200030040041e56002042042039185151043c1c0c004003005903080c5203003480201445a400e0040000c10041c00e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 661094973 1250 661093723 661093729
    0x30030f150f150504050f0d03031e020903012003040803131b060f0809061911070302010b0a0824071e27031722080d032703050f09 57
    0x11450300000100719441404020810707003840b020481c01d641d4209181003610304030005c1c00c40311140e007410b8007a246202d000c01c20544039a11604201c4070320aa5450440302e01c0380910000c0d00041072540c0291300e0300301c00c1106540d2000403403d4603500403006510350340ea6a56525a6600042d06a40540e24088443c1c4c0004213084141400e00c1c03611100450818504174000f88103003940308031b102c140110030040c0800c00f03c002c40c00301e40c400088040d0142d1581c2140c0103500600084241000440d404500c020426506401080a240c01240c9620145448095a6072508038000c002607a8145030604020794101c048240c03035000d160342c204072004c800005404c10500b5020032000740092159000c070480320117980c05007400605002400b1003c01d007590b54801d45150400104113141a000c69a005183c0011401c410008251004041e0301035503948011f554503081e00d44800841d044c0240c50041d44400c0506955075000c80d555002c04522036103055816030720004081146490400002c0404d807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 661096223 1250 661094973 661095011
    0x9050907030c170f0a0507210b032d0d0219030e1314090f01020a0206010e041b0b04090b0603071e02030c01060e0415051303030f020d060305030730030f 67
    0x5100101003131824640001e01c00d0840790010803446c240082044c880c042d5020a18603403404001c07050f000116410340c0400030b403034080704d01945d12082e6130000308184520560f034402280030151004a848650b14510180d8841d80c40c0c510a14101684c8105070001c240b0a43d4511403040c0d010380848860701011206c4010781c0c0c0310002c0c80c01d4608404003400b0b11000e00b0403c11541f03000c2c01000b1800d2040c803c1000313403111018072403420030000c0d1a012070107200e48000320082d041561210750b100580d03500d0264506800500c03540c030203145040d050150504048040324481c0070300d551040740399009402c8801c3c904c0b001c60004000c620007400380e00802c8100344103000181c201e1446d0a0003500e480e01e04041c8080c0300c000b10480f50740c10302c0c00348608681400da450070400d906050115500d03284c1805c4000a02074501c403492041d0500800105104012000700100d90041099014900151030580800400850340594146880c042040c10301d1099000201e0108044c1011814102c206840d410b00c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 661097473 1250 661096223 661096231
    0x608031e0d1116031806021e16080d0305010f1401030f0e01180209010503120a0f05090d0b040201080f0108061305071a220b0301090b010302070609110f0109050907030c17 75
    0x1083c2e8a100110a00d5000080070b440648020130818502d1b042c61402515503541d903054044070743c204414001940418080841001030003801d00200b142c0c0c42164075646c00d0300c910700c00c0209280c00000320f4080007101203642990302d0f00384d4607154040540e00440c010186018030906403992903440060192080c01044041603c0c1c10300c1c0c28136900c481c010401d0081c01070388458401e42c400b1000081c00103012056919000c0319050a60403401220030a450710310850341000d511030601000d000c1000300c0f0641141c0280d0003a03075011030304d56038641c40030510003080c003e548566102c0c90004205403020324184024034400c50070794149540e2000241c128840e00078410710804000318149041e00c4a00340d010074001c0c00d09120100d02031034800422003c0c44180111a501900c404140d0110390103501161240f90780400300b0001d5490a0401c0850303485110003280c03142d010412540900d42c0308078286001c0d681300500504250f22044425401000ca288800c0240b141042d19035081041c0e400100d441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 661098723 1250 661097473 661097497
    0x601020a021e10052d0d0e030d0609020a08160c0213060503060708150d0201030905160807050307060212090d0203030c0f0105010509092505030106030807060608031e0d11 75
    0x2d1148610030410720b04002c2040b6010464140543c0d00d078900651140040f114600e40d0381c5000e0311704800c01c40300e140b007003500e041d042ea0700344050446c580e48000300500a50100002c00c000482d1512202020387c071821894500007843c60012502507001c0161414503031401c1d0803c0201c420b500d40c0410078140811039008100369032030701c041100d410705109a55000c90785240c0f111052620032040f200c0403a801c1c1003035016800c0034000004590282d408061066081801c9804210210b00311000500032801002d000703000310000018682000215441030300e009030060198000c030080c0a01d01c9030481210740d903100c14007520880258130300780001d00340100c000303024144600d109200503007516010382c008d5000c0c0846204021102e5400f180c0340c2c071100c8a9148007800b480e10b09007403404203485900010f0341940307800b03400400c10280200801c01c40d403081c0381c02d100c1c3c99a201c4119489004014240241b02c4a06040325104940c84000300b41101601c900011602c0100301e1120441e0050245205 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 661099973 1250 661098723 661098769
    0x60c09090609050405160320010309020a0806041a1501051c1103010f0f03020a0315091e02190b03040f08040e040b0a0e120f0703030b090c0334080601020a02 69
    0x2400307000d01040050840306c0d004600500c1c61541e031420742c401352075403c4910041c1551110241e0780300350801d44081d134009004501a50300c07910440d446090a460880360005c0355800d00b04120714004041e03209980d150202e100805034400195009e40c0a0b10005a040d000d03124480005203803071065102d50b550340c16046880c0d60508103054201c4415400003140003e20200810040e61505421000c1e240d01907195020020386a8546016210b482c800500c25035140206504801e00c51056044950003141c400048101d424150190032090380254001008100000f4010488190034256414403610b906481d00e559501c00c01c11101054400311101004c2d00c0038400c11010502460310101d0b0f10300b0282602c07800c143d00e2002c2030b01c5005803518408401040706001c1c14002d40c0119400302010308600c0c85441d203004491410340c0102c501c0c1c2c400c41281d12008250803485244001204040d9100e103900c108405e009403003803a402000c86045124a2208100585a4608414107002e5101e2242 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 661101223 1250 661099973 661099981
    0xe030d090c05130e070b090a06031a030a08360105030601050c1005070908010209130506030a050f0c0910152d020109030f0212030a180818010201050105060702060304060c0909060905 80
    0x50170010307554401348100b42d0500c059105942c5408881c001c030340d0036080010704042c10800407625a100c409e492a458068109884240a0722000500c0c40c8130031980c0790040c2c907140c0c1c410840760502c0c002d1044010103450702c2d91040d42d40200021900031034141011810134285009840c6052665506605540c4e240d1003032000080d001659070001d003180f2002541000380000208007964140e1406458294440c1c000c03a619407410b01c0400c1c1c0d403036042025a41800321440800b507440907410701150181004000040113a103100c000041039444440000e1352081400e40300301c4050030204401d001c0070340c40d1001e0742c601d0359003070b001c0b5035400030a070700045201041800c0103007000006c1e08800065400ca00e419400700c1c2c6400c8201c0341c0c00803030440d0000b0844039000d0769504000c00d10000805134000043d04460f4112807010700002c8801c00d0b802030110341c0e01e810601c0500c1c001c0900094209005001250000344aa0800c0c1e0340914030b441c2c41d0034450360301c1714848107681c020341c84604501d6941041c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 661102473 1250 661101223 661101251
    0x414100311040f14060a05031501030612060204050a1202010210020c0309100c150e070320100801080601090204050f04201308060f100b030c07020904060b130e030d090c0513 76
    0x44c05407031022102e290030500004400703002031200402d000f6503503103040c00200d144d0f8007a9201d18080c0c01d118641611240c04c52030014000d5015006252080540d107500066a003501310200788842d5069002c1d050300025605480e010b13400c41c11150005010600825031503072030780c03003050340010340969804060790310f2824001c00c4a480300d041c1c030b500b45003080c45407006e80d100004c494080b6544001032807603070a809281800c107404040004d50380800401d500002d51a40301402c28140d401c003d00b40e600f26682c1e004410101e01ca5403203402d82200003140c00e100e0034034044d8001840c00c0b1100c4070b01c0512340c810101c1314489a0107005403420f40442380d20240b080b0b120401280d588100d51a83e1075105041c4403000b041e038120036210301c0e80000301c00000a034010081e0016a0340482c0d001e000d0182a0405280c00806825501982030103414440395039204500c0d14020300c0d50746030414002c0d40c5424040400c40001d0035980700c017660301e036500c68400a19a1280000741c1c8a10424840c0007072030a4400590b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 661103723 1250 661102473 661102499
    0x9020d060c0e01030624030e01050702010e1c0f08060f040609240e0604090309090906061d1302090a0b0916020d0908072304020a090501140414100311040f 68
    0x503181010b2038980c050088031b0030000040e2001400c1d0030420301130602e0760411009030500060300d030280c7d400d0a0500000c41d405401c1040c240d2120002e45100124101c00070b4202452075101c10f0024101d0304480141602a00301c80d82c002001401c50f9a0b03c180c038001180c243c0e070465204640459452211a65201c1156000114001042c0003008040d18044d0120a0740c0e2000d00824452075684c0203210400d4022510040149402102030051a0711801c0c0480108114450300e44951756000c0405a03c0c060b0020040c4100e0001d0b482812200b020740a20800b442c001700090703151a03503150f48006030750303417181a0f611920014812150800300000001e0034024002020b10600c10104000c2c0018007002c24200261004200600001140c0e00d00040720f002010b1788268000f44009209484140d018682c441034407403e80390f0166110410003e16440d210782d123301d04c112074a1500c2d4803001e203445250b010940a41e0302d000710304004103031298019907026a202c03030001100620204002225440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 661104973 1250 661103723 661103747
    0x22051c020f0d020d0315350a0c0902181801030201080f1306090c0b040b0903010e0304060f0c17030f1509190e2b08130c030303050907080105010b0901030b0f010f080a09020d060c 78
    0xd130850070102d9030745008189c16801110110780c2c000c5042a826841480e0b0213071080790081084400741c14107500e0f030005c00000c0c002680080d0780c0e04001030411032a541c4031409810080c21001100c56581c072070f400200b440a204581c80101e41c0d400003000c0d4940ac4c098005407180400c120380c3c032542d0b0303804c0500315a0500c0100946800500040081c0d58001300201520300450510080f110203074540900c0030022182c552218242c0407042c000550703450143c41e8801e000006003071b005640b40360b08003e0727601001c81d003800c091000c0794805000303a80395030007220f0094a05000c8a9080e407004d104d400b58030342101c04076034205c0701c000c80ba4103009602039a840c1d080500507202c409401e14075210401c01080602002d03041c942c4941c0458a0100d01304291402024a08001c00465840b034010041c0d90b40100c030040d0019090480c140024a1300f81080241d2000c146c4030141d06521800080e10601030042c809011036503140c90020243e04c2d0354080664251081c00000f850a84c084409002142011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 661106223 1250 661104973 661105079
    0x1020a030b030f070b0c010e01020a050a021006051507030212071109150607080a02030d0507091d0c0711061612030f1422051c020f0d020d0315 63
    0x80c0654000710021400c24141c5401c800d005c2e548001c0e000249015140203004041250703c0003c00c0da01466210014200722181542902c0380704007038494031410307030782c07a80103044e880402a8030484500e0512002441924070a00542d40c02480e100300441c07050f00583c00507994141c01c80800c6c0b800d440c0c0142d0709603111422441c0641e5005050020810074042e0000c0142103030000146c1590540c020025a0074002d030f021824041072602003c01001c40c13600e0700c41d0085043e02c0c0d0707109060380c0082a589030311a414140b9014280611610b03990344040c000b0f1107403034025108000070351201f040718440fa42ca09000d403d901000000c2e5060090403030310484900c0c41120300d8406002943c100714411160415088840d04d40a0301070340842494818026a0041141c07144950030f40b001305810500e44003200d401d03025186083c1c800c081c1142c540080008100c01030b080400c0f00c3d40194002d90000d09251341a84130f464005489010190703201600c81c5030500221115003c6040e044200e00d80380301c5010b240c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 661107473 1250 661106223 661106233
    0x3010e070f0f18030609031d0a060c0b07110f0105011509051003150b12090706050c060406090f0206360607020f130504120e0603040c050607030c080c01020a030b03 72
    0x1d030700002c0400100010500410402410604580400c20390040c0a140c0207001003040ba1904e18001c0c08503294250070f640d9a150f408043d003145e1078000000000c8512075110050000c0301e6036a107144e040b000810007805e2003020101d04184040401c88a425529000000905541003442000290300102c5d011810856042d8040c442c0c0d40785c00495108400e03c0c5d007030200d00c00701c808220032424082ea402c44051030b07401148c40ea40e00200d002245000320011010b4540ca40d8891404030f90b10720a0154444043e4800e00100b00041d00940c4214141760042c0e0707240c0d201030350aa00040c0c09a00120502d00c00020007600075010700300701420b41c1d000701c441c2c1411205000c3e0300c0d80800c40c503014527240030340b00d0721020b4000c0c1c41d04e40f204c01c541700c0c4c00e00240710100036600d85840d00250710518003542c0d000240b202e002c2c41100d4101081200c4c001c030340040b4031b40c208a20b01820040303150b024503021800c200041c40b0000024035040c01902c24002000009a00d9848099005048030358940074148680e001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 661108723 1250 661107473 661107497
    0x9010506060412111009030212030702090f040302010b0d230601050109170309030304090501080d05120103020d031205010824040b0c071b03060c030608010207030801140a05031203010e07 82
    0x9a00700301d4046400704540c1094802e428240804078507548100c543d0080038007000098219404034005d01540d2088803801800c079900c003511640c0380140f18009402903c10404a180d480080e4020769100744a4030000c10701504120106801c0a250081280c4120764503d400c40c40301c000c1030b41d40003071a40c41802043c1541c50600000e24080d03035440b400c030503861380800050054006100711f4030072034005402c6071350700d5594035100b070010102441441c0321405910000c0c10298401c01c02c59102d83c110032105c1e5800c1e400c54003001622402c0741c0080b0284400d119040359605800c0c0640c034001c0241401400010641e2156004107000c440301001d5003036107110400c030001d10714100c065007106101d01c00649828162910b060b04002868081c50280750f1413000100304255a00b14040c140083e40d070034800d042d0b030340b8020340c05e0340606d401c01404540c2c50320042c03040108144c1403217960f0000800c9524490369440100e418800c074205040740c403060010041c00300d200c03c4d01c1c00e0307500001280b9005412684d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 661109973 1250 661108723 661108729
    0xc38070e01020a1b030203150a060b0f22120f050106270b0d080c060610030603050d030f0b0406080604050c03280f150c020106060203040b04030308061504060203070b09010506 77
    0x2c3d203030b00028241e204000c8014101103020190f080516030140c01c9544000c6144c882e40c40c00c0504591a0f00c41504059010910301d1680c41a03607404010500d03c82c0c00d010301414608041800c0780905c82000d561070f20700191080d102c503500084240207042040d400c84944c10481e0030342e94a5003001d0321440d480210900f9030300f0060026540c01103e580300007829079400000906215000e03801404d400d0b4041180300c1801004030305180190000ca80c1901071070700b4910160f00b610054440680710b0703040b109070318003510b000c1e4100032081507404400040301d020000000e421104150404011548498100f00400100b0003002203403c604400400b8462400311341008000c840d9203281c800716040600402c00c2181c03110b2000000c3d07a0040001d40c00700c6401c0140e0b0002c0c840080413800540c20315100045c1ea50000c411642981c0e80300810a15080c00c603181590300c250054800ca41012030346801500006401c0050009050b41d0741c065940c4088509250403195030181c040c01c00e69240c502403014940d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 661111223 1250 661109973 661109983
    0x15060f110d0e060721020d02010515010507110328020f180402060c1903030e0c010c03020d05070507080a05070e010905060904140f0a08040510020601150c38070e0102 73
    0x10204a0742a95502c010b0324280e501141a24902c5c1d55540e0440d01208000e0380205040801c4291580204199500d100000c6200f4180040b004d01103541000940046100c02900c425070040140c00c543c0c00c0d02281400000300c024070705445c4440381400c081c0e03074210300d800300c4030180c0020100e03451b1170007600303130100c080d420345003d00001d101e0303e0001940a6240e6003401405c102030400b4058104c2c0318810700300540500b0364002c000055000d4140500b40640c010441d040c001905540240011040c407101502c842d1710140054031603128088000665030300030050417011610502c09000d82500e010749400455006800c03a0360341906180400903242c03286034141d6801504074803115640b26140c050a8201607a014035810b0780d025200a007428029040010406c507442542c49a2040c2c251600c22078440d1001c2c0280c41a0040044680d2041c40c4504c0440a205016044420840c220954146030213802a00188502c01109142c0e050080d0744075803440d48038106003081d08042c1d86900000b5120 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 661112473 1250 661111223 661111247
    0x916030e070815092b1103120a050c09131505150f0d0e0313031202070317030c0f13061e0e120f010911030609070f0e070315060f110d 59
    0x540d03c0000100c0c40e030000c00030b031a900e039070490900540d0000114100c2034007982500f18008a0f0b030301c01407440700150002c21584080140d200311400c907100c0260b0407003c0e000240906100d81000d0150b0011031780c41c80140c0c4010070100d0320000c3c1445080402a15520b0b09510491140049994540100d10302204035200d0900c0d101c1c0d00b603550314020329648001e180c0c01e4080901440042500d00b69460700b2140d0f01c0a4034002d207c440c864440a0303204a1ba41c20050000414505100340f108045c03601500140d42c0022007440004c0c00c201081410100d20f0700140d031400d048a02d900000c0100503000414086080c0c1c92100746d9210021207800680421500c1900c0e5005202d0600c540005600520228503402e2070070700240000301d65030070031201c02e643d2046818802d0080c0f40220300341c1500014044203c40e80803078096206807a003988107203400001400c44060589448501c413603041000f0450002d0306035601c0d145100510010b00421a04c00650800015030004103c11407040e001000030311a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 661113723 1250 661112473 661112503
    0xf12011d010b090109090c03050712051005090c0d240911120403020109020303040b0901030b12060c0d0b0409150e151602010608030307080f0906010e071d0916030e0708 74
    0x3441010f000104d0351540c65502c882c510918013542c0600e02035040c1c105c0f900554450303540d8051000e41c41c0781c01b0100c64080c5c803903500e0116002d50410050401d4070000790b102c200d6185107401d12020008a50550b0350b00c045800f4880c03441d10708410f8045c0c10b4250b08000e0008181b0070010f03000303040c0c2580c84d03501c01c4003500590201c0c2000002c040504c00d40094042070790180980352140e98806640030641c100080d21400310b810110a44100e05041e03440043c1c090840005010342d880321a0855003030341c0034181410401d0780f1141c131001c09403210301541c4c0a5601c503401e15042800750540a0046a4505050030b00302d0300507214104003078080c400c1c81500075249403c04a1015201c91040e4018109640242c20a0002204001c0820f0b0480c0205100b01c1d40040031701e04664401c0041505c4010900440d104401d2120200312640e201e044000002514203031400c80384070101d4002a82c0c0042200e010a106045c0040303000655414020001c1a030003e80092100364140310040ea165410540c908038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 661114973 1250 661113723 661113727
    0x81308090d080c01060311010f0216030209040f060c080f1303080601050c21040602010605010f170a0905100b030705040603050715051207121a13050415020f12011d010b 74
    0x709001e141001c03211102810402000107955a19280c0203139007000b240035002ca1803400c1203807062070000c294188900c00c1e03454070000c0c032802d5030f0030000d25540150041e60541c285101007000598107100744240f44400b41c40340000c52900c28884c1d0310030500204010104828202403000280e0800300154015409080164480c40b085008c2c0b032a012100304030402c004d1203c6001080918464000c00c140c40c05540280a00b03a00d6034010348541440b10060400a2400e89100f04d9101082e100760f6040058100702054440c108d4681c245800301c0030b01c1c0c03951110fa03142c040642d1880c0410107940241b40c10b0707406000e91440d50315459100d80d100c1c4a0300040b0004001c11407401446a401c030b840a40c0c1e02d1342802c00e0b90900c00380c003c11000012442e003148610b0840c0341e41090408404080b806500244445c00d490030f200e94410140c00094800c81c3d28102c2c1c580c8020b400a01030018010348030b244501c0755100c0500303541c01074001c10103034800490003d0894083c0e80e0742c03104c602010705403151203060503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 661116223 1250 661114973 661114999
    0xc030d181203050a0c05251e0b0105030610030803071407020a0b0d06080105060d030e06120403080403030e12071e0204051503161508070e030a0b01031218050d0501021309060608130809 81
    0x211923240755010241c688211007401c4082214604070306041e00d0054044a18581d01d824080c60315040318040504031003001d100042085110300c2d85280030307c04484c5001d0078001c031640495100040c50300410001400803078544013865141c8034000082003200000e20240c01c000c40420300e043c403480c0740601001103181402041d40c0f03d010480d0000006403045034443d150605005140e414142c9d02140020b04180002182240c000f074a040181c54050f0803a03d4210255189000d5116140e540c0400b20080a43c0c000980e0300c03442a94415140c4031040b03148101003c0030035052062494080002000d4602e003071020460444802030900c216041c000f4080d140d8000c20b03200300d41d0000780d103a0303d4814507440c6010059074621041c101d0344584d94070100441070070340c2a207103c601c00310024040014400200700b10303e4800100e07024540500001072400b4540d4801c01e021101c81c0d00540407403500c40104010007644002000c0c0d001c1201c00c61445071404a07559020700348640d60540d84a00c107028040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 661117473 1250 661116223 661116233
    0x6030c0a0509030604060b03061311130f0509011a0d050c0405060607050609010b012d05032e050907080c030c0904020d090c0306060b0c030d181203050a0c0525 70
    0x280c0d0102d5000b02200c44600e000c1c40d046002c0c001c0c015150f806802074401042c00d107c0400f00e01c06115501200d0450405140001c1c00142816800c00c0e031405921003101e5805070486102e81070082e103200300089144a0062100c5030384c03180201c111742c0610b42e4640c41402182000c150300e421300c4011500810300d03840344d0700001d105002c1c40b04041c005005070010301c04002030541c403070b10b8005400c1c0c84074008460300038401d26507001c0003504580b2030745045000d405c1c032234416030003540d01070841c14481e12a003404001c00c941e13265441c4640e40f02008003620500c00c901d0708280b110390000032440d102a40f40307408803080c40f450201504044014002164910341380c1e4076501600c0041c1d180c10b00422078800182841c2014140c180300940d90b20340340c44804900d0200d444111642243c0d0340005524140760405200010000c0e0249407050359044410354000410441004c040700125a8010581d07043c81c1c05030408550039100320806204041104282d0300105d00c0c8407000311a101030301c00c0f06160890a02e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 661118723 1250 661117473 661117477
    0xd080f0403020a080c030703030501090b0d0210050d0905030408100c0507060b1c030806041a01021e010b15040906080c0a061107030605100e01081219111203090d030b06030c0a05 78
    0x3004013850380110782c401c02c402000000e0802e840c040c3e9418800759a03184901c60031143c400d0100303a00984421a40e40141c00d180103810040e000500e407203072401d42046e282101b12803110004039400e400001d010000303c6000c102c0b0484c00e044941c4104010b42c500c0300003805a11a1403002418035031214100c40d000d40d101d0403c00703492241c480f800c05110f2500d2500626030102120703054461441d061541d0b102159800c04d103150040103070020405051002c0c0301c9100d408100001e100159240c080040041d25003c01404050405682c01ca0702c0741d0815800c42c0c19900b0580101041d42d2020b0861490ba688624907001198004d007400b03480c0c075003141c0c161820710310189c001900007410314080c010420400d034241401c8900041d110301540c0d072100c03d0305d5120b01100c0ba6002d030b0f801050050003407007040c000000420340340e14148050796405c0744240500341041c1010b00c00510001108010070804207000100740c0100501d000c00161000100041060101030704000300020302051045082e4000c0e41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 661119973 1250 661118723 661118743
    0xf031a01290d020310030615050616020402070f0f1208090a0305030a020d050c0c01110306060409020306031e0d08060105090904030806041e05090c0a0f140414040b060f01020d080f040302 82
    0x19035a900d8010070100d11780300c50b880704460a514003a43c900c00440008031010588070b008004528116203108032440343c0a6691003179078015030803c601c6001428000015105078480c0c40030301c4684c0c40c40d0030a00e00c42802c5506030780c1840150410000a0040031907101800ca44c5400c0460703c80d120040024002d0040000304113100c0c0c40c00c01800b900d203039204050041d40340300750001e206650750f409540344030303010030b440c1070382c0107507003800309102030780306178000d5507114401800321280601c4141240114000e442c0c611101504015042461b8640c070101007607001c0800c1c20400d1910100ca80850b40784480104060100004d82002c1181590341e9005103d005d00c603910244a403900641c100002440244c8001030f1a11034850900664100355030410704546203907006030703407044ca4800f0101d00c419113000040e40c400d13694a003100814852081c1140a1805032404000c64600340d414400560003100a190540d404440350343c0e00140d10440503a8007640c011614011a1900e143c03e07481c3c40c003081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 661121223 1250 661119973 661119997
    0xe1306170c040c030b09060d1110050306040c0c020f0d1722050312071b0b0304050c03010606050c19080c060405060a050610080f1e010f031a0129 64
    0x1541104034090004021449010031503042002001c01441a004c84905a40442e0031402d1000000c3c0c07c3d1400780002040030b4001c81e89040705000e000006121100348e86504408602c0100600c0b4683c20a80b142051020080c20136814004454000500026854070241e01c1001c004030407030204540c41f04140440302c1003035041074445101c0f094a110440304c11142d1020481a2240040c19240006030101c0d00d030700d0456141c0c542840e546030f0075201c80c41d6201030800043d8008001078980340010041d8403da028402604076075020104247c25103c041c1d01c01d070308200b400d01c42c400318910080b40c01450b410240d40c10048581461821412a01a6000da122107014550821080c001c0100341d10f88941d5170100308100f1303541d171741f010080f481624500340302c00202c2000003e125030f603090318003a400404502001c140e10503121110803003020240c011002c0703402d48420070402c10015601040d805802c0350400c20444d810405144021012801c0ca0100880035400080c46c22030030200301c68800040c2e0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 661122473 1250 661121223 661121249
    0x902040b0d0e07050d15202104110d05010f0f020c0f06160503090a21020111040e04081c020307081b0a2102250b010e0103030e1306 58
    0x10032900040ea0440c48045030072600385100c06410420100d07165040d030380c2c02050742d8078a01c1140c4500d0040b01e003507082c03681402e03900c2103135990403155541125072107800c03c0301031035a5181c2010900000ca244c81c400c01c0c20914500141710001e040c0040d40d07012018282da50702040541401c18034054004840f01d041c80c1807038078000580c0c0d04616001441c03510200d41c100c41320a06582003c6640d08000c94000414407482103450b01c010780310700b00954102c0070310011a00350f1102529024030040c018207030310041101c2106444049a0203004005180005c140342600b41850002800c1d41202c00800c0140403100029041c90b0003900980341c070101040306081152685850140a0402d10301070703c020380440325042c818911341072040202c41100c0216643ca4442001403d4900a04000a0381c0c2d070710429007d1100780d244551000e072240c1c00d00110350001381100d103141000140444180c224400d18600d140040c008607400c030a941d02c2862003600c2e02d071810300d104540341000707000d150400e180048007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 661123723 1250 661122473 661122479
    0xc120909060b180303030106020322051002060a0b060a17060a121101120e1c090503030a051201050102161e03120c050c09060f0108041406130606060e0a050d0606090204 74
    0x7041d8083d09902280ca04502c101424020401d075880c0024855440144d00030000106100c80403401340c0312152014030740d503680984450000304141c1e003484042006034020000c00c40645000c3c0078007000c645c02a1813043c60004481e074001c148144942210502c0062000484d6941e01ca0500c113000030a0700760500601d203016454040c151900c1e03049641e00052500c074021b0780c841002d2080802c0704c0d041c140244028a0a541038003480c00b01d4413450014040c00020004468a09000a0803085a50b03547c4586d1281030f0440c24591307843c107822982c119445001c60300c03c803001ea01100b030b081d51400c9500d50605009040403c0044100d40c000401c070b0a01211003004280c2c000c1c080c18006449a02514081c4481c03a050120751034003158030cd684412021031280e50355004440d0f071604a4000c440daa086150f511058a01e041015582c00800b0380144800c3d800748403541c030804010b00928507100490b600880c0002d0f610003018040d00c1c0c0b180c5d40840300305042100561004004102080c000c0d900c1d20b03a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 661124973 1250 661123723 661123739
    0x309041112041b090501060503190f150e0117070b0c030c01020414010324060c0f020909060601120903020331230a03080d2f0d0e0d0c12090906 63
    0x41c0f10502500c0c0a2448000070030300d12400c0c09014180c418681e01c070340c21035466a222840c0d110840084030442c3e560b5001e5681700305018011510724006440c003035007501c0c1c904100f01d070031400d05a1040101c08204500da41c2140d83c049081400c803590510354a8440034200031a6003144145400c0d03004542c40010001103001940e000132284c21426281049000b0041e1109004925042d0342c100404118030340901042c1c1c0140e041084aa004101100d1701002c0c50340480c0761040281d90301c8100d0b030f101d1801c000040d030b84804442101554960240148043c9560107566401540e10031010000f02c01c400c8070a501036030209410131182034004d60023240c0d440810305e94004010b550b0754100103214a4030060b608101c05030300c00700c0f81c1c048141480c28900f240d0100080000c40185c0604e04094403a881c0c40c1641d01401001000c0007002a0765110002c610800c00c1340c000c00c0c20741d0181d41006590114072900003a2102c51103400c4485e00500c12003040d0203d50307021140d00900c90140c50400e000c2070104c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 661126223 1250 661124973 661124993
    0x70b12010e01080606010903120318060603060b03032712100c0e040204030309050f0120010527060f07050d0c02030318010b1315180b19050102030904111204 69
    0x585410030422481c3d0700c62500035240c80f0100e690a000c144200c2041000416152040c3ca1069452500043c0715410348010b0b180c0c884186010b8803411381310350080c010300055119050310b5a800311300641ca800704510603079000414200344241701030b030318543e07980c03503900c0754103c010070450800c003078810350342000d44014003d041030440d0100151001481c0c0c1500d0501e071003101d0560740c15803a1071802e245088100003155550030030b103034100500c03040c0300e0400000c0c01652600442e0103200108852401056004440792035040d10140f0074000501001c914401007280c5ea00000058404401b1b07070344100081d0307414070034403488130320103441c0641815107250301001440c0102c1e101080500c0064a4044860030786003243d61040e44221030000c1c520f403040c9158010000302c41c0c00120740076916661168072801003400000a000c00c1d845020007811850031600e00350741d248020070365459070380c20240000e5a900451071000d004c1c0c1e98070b01600718282d02e490281e900417542ca4002003c68680340c07905203802c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 661127473 1250 661126223 661126229
    0x17010b12150c0406050d20040305060a0c090b0301090209010e09010602070e0c0a0801051c0501020d2c030d09150e0d020d0e010807030902190e1902070b0609060102070b1201 76
    0x15610400407800d42e02c4290308a50807110959651410520b008102c4002000e44101e0103090981c0e04100090348800d41001e40029400798025129501c1c0c0b0030300a100355141a101d9504106c49000d0a0043c0311204081e20b044d02c0410b0b00050305e81d500b510050701e507180e103a40140d038000d45c0900001242580040c40000f903600340c910f81d400c0f0740c69058281441e8051050041c020030082070041c0101e04100c4010041000f0010040301c0c0c1f9001925490b00326803040c815800825190070380c6590b606202d0b14003a4450749904c3c0400341800c41000318a03140c1c0250141c091401d0344950b4024107005044904c50300c0c160600c107042004840b11810b10b60742d114803c54500242c042c0413905045a070003200609a1810181c440358155a51314600b2801400ea0341d07007c9911441e10540404400b4520f203400003e440b54034008265400d001115a180c0800c17014025655401040618002070003801d1843d007164094803004129120100140d0420b51142c06c491200c44d0040341003c403030081d8900d001d0403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 661128723 1250 661127473 661127503
    0x415080901150e011a090607170f0a030212130f020108070e0301050c120f0f13061407020d03110c0309090907030209091f06050d1502040504020c0a151517010b12 71
    0x3d6a00d2183d240041b0700980911301e81c000c0080c000140401d5211900105102c0c0c420981ca2800c10100c0c4c940207160054005507000a60104204429142c0840507541080c4090040480010555210400f09442c014000d040020640c00b184505006418140110100500070b000b1850210040c24090300b14000400108a040c40030542e9829850b807030500507015600308140e5030341c5210580d805404c1c4040304444ca2a03441c0b003064070700c000a0807660f0092095a010300340d4540c5206004056819140000707044540402c100c00014800000b1074003440382c10ba52207003c95940020081c14a022544084c1d00700f80341808010056002080c43c01d506c64041c0f0000e04074107041140b982c100c81a50041d15006055000f1a401156a0900140410651100c094501915a0049070a0341c120501800003980b00081d51703010051100f4141e010320284000c01c100c0700c0b111007020511514140b04200081d001c8080b46101d201b0290401c1c10040030180c46a0041d04030360842540d05c085851046403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 661129973 1250 661128723 661128749
    0x3060b0406050909030304140307061a03070b0315011809090f03110a1509060f060f03020a080105061f020316210207140616050f03031603020415080901150e01 70
    0xb034a031a1a00c81c00e801a1076010055055598541c1d40c60b01078080e0422481c014402840003000040c418000c25500032100350030701e0107041074003050524004a07900503004c0d5110038001c11050300350003401054040300902e410b5910000f40d003c50509400c50b604003080e01401d101c136031000d106104041c0b030002880b0741d983d280c080780071b8802c594a03000c4100300205030300c0c28007409136220b11319a000101080e000b06d10000301540c01d8000d040450b1001d500c42244501448001c209500d070001d2000000c042e000d000703000710720305a800602c07600105641c1896026140a03d200c0142c420000d82d06a0b801c0180390b1641c0c15401d0403d00824240540c0c141c00c6a144c0b84020420b04c2d2003c100e031005ca8103204980b440440300801001055000406900400e00710040c00b030020410401400c2240708200000d96035070b00700060340c0070040c600200c1200070315004220170090344098101d800c05403600c038030b00b900060320751038199805844004560055011455000b00b401004020414101c40c0395020484c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 661131223 1250 661129973 661129979
    0x2030d020d110c090f1807030b0703111204020d05070f140f030102090901062312150a0608010306090305042403201605011b091d24150403060b0406 65
    0x169444011150103a008441c0c1d2020540e005c071044801c07134006180f031040d04c2d4285900740340e480c0b81002030350040d0b074044001024014256094411a41d0810791160014070340540509482260040900000e000d021800f5a91007805000c2c0141c1c000b920501d460461002d41c0d44c2e40f1a0041221800128410a8155000b4442d845c0c14400c079180c0010240c80780c400f03a8a030000603030b103000940520710f2180304201e5000100b22010f10040000090b01541c40c19a8248111845204d1450150301c0340910350140060001c6c80d0820401411030394070960105d1110418034040304d0a00550384a0b040c1d9402d240c103180411554905850b245603c0359500304030081e10f1002c9503c44100018458590000401c40c00341c94241c8110125580d40c020700000c2150303401d0020345c070411905003c50200041040d403040c04004800a00c0080b400921445210356040088607205607513805000d40c0d0007440003110440450f10740d40c1f02854138060400078281c641d680c0b42001d41c040e0a03182c0040d44900c2c074043e408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 661132473 1250 661131223 661131257
    0x6010305010e0d05031e04020310020d09060e070302010507060c022a120105060d030309050a0203190c0504050708221401020d151d1b0301230409260702030d020d 71
    0x14903c60180201d04c003a1065540100807000c88000c7d1081c5d03098018030000015541d40340c0020f0000c60041e00d0300185c800300608010040f20211701e000504d6030440001080543c2e84042070ba0050742c1c01100003c1e41352900b107001da18050207500d80300b0380a078264400c1c014480040c0204060264145d46030f0307400c991015900740c200c070300480e00c85034000107229064010a200c0c0d40501c00030ba2081e02150030b1100030b500007038508081c0010f2018680c00416200301081a204000b0004103001d03a0b06000c2800c1000c00505014002000d1101044c01e5801c420710b4112141c08400450b038000c140d052405030201d4100e4081c0d03001001c0409840d0501c0c03080c180d041c2c10004894112400c1c41400a4030280310340004069901c040d180d4190303d400d400c40b5421510441c0700441c001d114419a0700901c13240907040c4034142c0c4550101c00d11907882e18800b00d010034070031920100300400d81c0d1111694500310403a200124000c404020750580b087ca98445901900001c1c80515805c031a15440140b02c1e0107004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 661133723 1250 661132473 661132477
    0x3060408160605102c16050f04090501061101151418010b03062d060a0504080318040c170604020c01020c0f03030414030733150e100b03040206091206010305010e0d05 73
    0x4020821a90280003035503030100d0007007a0006c034902d03140c8103182000001125089070080c0d00310102c2c103603440c401004901d030805031614103103260340024410440a01105d140000c0c0310305c2000b00e80c0b041280b12038200d07580d0a00c0c50680362501c200c00800703940c40704941c80441e0411140c140c00780c400c0000211280141050101da80c802944c2000555220030f024484070740c20191099050100c00d00c000b041c248001c0c40a480c501092010344200c441c5088100010759440d502e140040c40f00160480d41e803044144091070380800140c40160366040042455802841100ca4040045c02010024000408040300440c0507500174021400c8144645482d03540740e10030036100074502e061202c8100c0d00310340c1102c1400c0d01028541c1c509044d041031445001e043c2d40b0b1004503003100030341b254410b002c50132034603030344541100ca80ca00c850455420001011003905c0054800303403180e040400d070002a0b690342e05a00c0604040501603520659491030080d01810f4003408045c0140580f00d4860100c500c2070b82 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 661134973 1250 661133723 661133789
    0x3020604031d0a141f11010f3b01180209100509040b100f151205070e04150b040e0a0e06060a03024501080304050306040816060510 58
    0x10014008a240c500190481036003008002d8002e44603000340d05d8011a0919001042502e58452500b04020700d6009400c4030326400550008524103c0c00040404540e810b108114a0b02c8400c068030384450040c08206544c551400384081d0b080c80429250f2000d071411f0150124800d40e0b440500e5121003a180384d4600540c01119089142600002c0106400b0110b0540111a241b203851b2010b482c1d401d0750000c001d040d00301c4600545e003007004d07070000b65010940180030b03030040388200000e05102c00c005080320080c402e15480340d80c40742d00300351942078030045800c02460b003882603550303c0381d4070145100170b01012251300f1126490866003080c072010115440380b01d200000c00d1410164296030800451040030b1007200092000b49440082d142006181400940e410680089156064013114200c00340305800000241e0030a000070071403074030005502070304541e1180c011911051112881d80862914040c00307030560703080909124190b400d0b10301d80d805442c40d8000480d100401c400009a082203403038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 661136223 1250 661134973 661134979
    0xb0409030804020915090112020f011706041e050720120906032502010203090c03190308061c0309140108090d0e031608010615020708030a0516020d03020604031d 71
    0x1c00280041c98011811540619100c0050036450702ca2404101895001d0b000381c440e840c4814208000e61910076404036200c40e0034a481031200c1035072051144406806045640115111000700c6502502c00c06150080103018000300441c0c500b0100041015401480c4038290404850b81034034045404548001c0b0f0581134110075103801d0301642405601d41c4000d220a1601d00c240f07500b19540043d00301c8444d400d130300c50742c00980c4074101070b50354134207050550341030304d1081d44866510220642810340f90407100c0d406080202103030b56030802050098070351a00c911243c0482114041c02c041e0001010000d07105070b465038022185040d0019680d03d40e040d10340d01e00c9a80f00c00d684480103403081c180210003030702c09419100400501090030081d859a07030081d424a944902c0f06010091765404207228400e81d40c03004084003072610007601d40728450300344080c0401000007840d1080d050040f0703c060b09a5030160400300510400d007030085d169101990b0490000d210b04800e20b009040c0402c01c154810001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 661137473 1250 661136223 661136237
    0x90f09030a0c060b04020a03060f080106081507030605030601080703060c1d1516060e37050c150901090501050a120b040906110a1215030b062d040b040903 68
    0x2244103403642050760b4000c982d1a03442e20300f1040d5945550024040d404070300e46003c101d940c00e008a55000301c2081d00aa107580c1c0c901001040b0880e0001603204000915440c04c00c2d194480360b1044000d005150003007a014403c05000182c00000007900c0800c40c0c2c010305003003200d010345c000c0458a080d401400c04401d02030000608040f89485010740c400104400e940c3d500d000c118400800b03018a068009440ca0340d910a00900d10070700a1081c0004014584440c0310810303030542c03c2c45c4043c58044c0f040d0000d90303c0d040c0b01d00c04120040100354a40d54008043c40750180e0041090300c030742e40c0320700ca80a00244020b400040c55500607019541d00c40466100c2448105072030190310010101c1151f1036030b0081c1c40388100004550302d03110380340c10100c072203201e95640c1480260190180701c015140b0440c161071b060031085120f403181240d100b41e0b03038403070128592070304e8840c0010103401d410503a1100008a4400600500401c501d040440131030944042c0300060140080000302e07108184090045074038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 661138723 1250 661137473 661137487
    0xd0c0201110f06150f0d08030412030f051503150f18100606020c1801031101080c090301060e100509160302130902030708040606092d020408011109090f0903 69
    0x508080008200e00d00100d4484103001e002940ca0120155a015109035040031350440c2405c2034111484680d00a0b14510803805c0c440d034628030700c0d2000802c06482c200018200700d080a12a4100f9411030200312024490303400c0c184503040921860805061003481030b016500c801901d942c0d40c440c0b15002117984040ea584e0340d41e002010304607124443c40418000c540082c550803070f151040101038013083c1c1c010644500305001f031150549030340b0f20028828245500402c0011a40c1a21000084d03085c6803004d010740390ba800383c41550180211440e4154207014010400612045050303126a030340184000751a5528024042070060580340a00700300c2980a0f1426401d00070340040051883c49507a100d581c0340d842d21154203c2e00196440c60020303460b00203120500c4003501581014080c00c800800c00c44600c8100a40d4160082e1104d4560130703c0c240380801455140c0e81501c0091110b00003d210801d0350b203104070900d60001d2000c910602d4103802140960980342c01480c03140034071000a40ca441c134 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 661139973 1250 661138723 661138727
    0x623060a180e090706021207021009030f1a0604020f03150a03020a17010501060504050d0201081b040e010e0709050a172404050705060f0f1b060124020d0c0201 70
    0xc000055a01032182a44000c8100440d036006040204011003018120703041446445007050300da41d0156045511524801d4a245003090480e1030681d4111171100600a100c0d0040d142038900d035101511000034580f10b00e050015500d90070303609058428481c200d0f5070398003003044100c0c0a00c0580040944e010f000081100d03105429400c0351352002809050103680e25400682d10a071070760890206161400c2440765a20024010503000d043c041c1411820142418040348030340da4600d4010b81008181e9000c80c080000e0f0f00b03c01020030b03e07003010003959103882d1030704150841800c0c03081c1101e6042d803500142c0018450424481502c00050600c10800c1c0351006500c0d03001c8803d03c4150041c050110702403c07440e000703d010004414035100302401480c1c5410140d003030006540c0900c1c06200208a05108651320404480e0a00d148110082d1914400f201302e100078a09500d400d2214840d602c004102940100a040001010300c1c2a0308503100c225013003287c84100c02e0701254045110609180e0041d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 661141223 1250 661139973 661139977
    0x6010b090f0310090503040906050d240f0c020a2603040f1e030f0f020105040c0909050a020904030e1306030c051522090606050414040c020f0a080904062306 69
    0x2000c010100c8050a025180f10400c81d11400f5045442d64000901005045040d002c0c1800808046684000300201d58440483c40c0c40d0f00291901428074a00c0e005110242541c084c0025040310402000a0141140081e56401c10441c064409035000c4908030f004035264880318403425075a148090458555903a4180d044c3c40214003110041c04550901071040e0060807813043c203030b002c0d603268007038401140409481d00c18542021011641010f04110200300b009900204881c0e848000181c0c0002c0d07801d0440c200707500b034070000394091210b006010505500a110000701e00c0100c402031000c0c200c3e0b41d46041144d0300e078070008114242815040159150480c03520101c064040381c001c1c9802c11822110910325212100300c18090312189003880700d94140e10900024080605050340742c1030402000c00348841440c140a40310f81d8542c002101a50300c04e10884d01d41c0f1001004580d01c510092400046a070400c181d41030086141c000c2c0040c0f043c50300d2a004124030440d02031481800c4001c4180491a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 661142473 1250 661141223 661141249
    0x22a0616051203040b1009020a171018050f07050c0606040f060308191206050901120503070c08060405100b22180b0f0601020f2505061c060806010b09 66
    0xb4002d80b034881e141e40100500451081c1c1c8100c1c1e000c01c01c1c0c980441111552040d81d005400c816106100c661b41c007941221001e000840a048520402c0d0790700b00d000c902c1c201e0b0a8010508030314000c2035500d5020350603000a40290306250710250155545c1900f110580982030200740030b944580c001c50f0b170310704280d07015084001e549400130075041c1c0c03680c661b0310041c1e028107403030300d200505881c031109038982c00031608550006003a0240826480e100020b001e2503410300400a100518502200c1040f8040003111f02e00ca51040e136000e18540d4954030f0300e850302400c4505076500d01941c2c2408800c5095845400c1508100030181024454080218003520000c0c00360b5101c050ba0310907030242d40c65480300c400c600052141b2019080e51900a1500790314250140503c0e05550000120310910130010580340d1030814070301c140032002000e07403542d00b110000503072041d82c02150001c1c081e0250407030b0040002185088120921070a03a079500d003a82c0d1010240f00340c50090409018a05861038500203403019 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 661143723 1250 661142473 661142483
    0x141306230f031507030e010f091101020115270b030a030207030c090219030b0a05031609110a090605161e050105070e030c151207030e150c0a050a1e022a0616 69
    0x22310300650b10380c40480754140d4060b900fa06480f60403003195a42401440c2e500000c0c503103400a40b074a04500b080340c0d41252650302c5c00744e00103082c40c0b1050b25820f610030345407120018119204036480d400e01a44a070301500007518004078503500820980001d00032a0118600302845002c01e01340c900003240200f03180103a144c0e11a12010b03001806036420003100058081c0c0000700600c01d45040301c010304aa1030f003060000c0070ba105008107408543c1210a80701144c409041590756081040310380c0b6078849050b40010f24241c1d00b0700903545280c8001082d40d54091280d070080001d80c440c0030058a50b111400303001e41e4554486103204005040c0300084140c05c031012100c0c507080c207680603220803690300c08840c40c1d00026501c1c0c401c00c1d403c500c10404203018a00e6120313880c0d11800c1a01c4801c0c803038861070a0030418440700240b16490300d403245900c25906000d01051804250801a0094803401d00e422030006000d102e1614500c0840c10342841c034501394005000c940740c04000d80c0030b41444d15410a060351 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 661144973 1250 661143723 661143731
    0x304121103060702030307020d02070b190909020a0818010e0607050c100608010207020a050111030a08040f0b090c0109060314040204051806040f02031501141306230f031507030e01 79
    0x1240e1010000b031401075030190040d5450f4904600001d251240d14482d02d4115406a40108441c1d010541114076000741c0c2e03500d880c16450561820b0360182e000c1d03800716074010b1001a584c114503074402040c900400801548401d031800c11405582650b020918121441d0000303404141d2541c02000100740740054401955a0030080034880c0341104c91070351114400d0303500040d4080440c0340241d0f03400301929003400d040450085a03003286035680a1907048100f03124031400824240701c9002c0358040000e0f0b02c519401c0d120314100020726103c02130b2031005404100e6800010a0540c0640034809900c0100514141030f9a00c5808100c09824081c2c00c4110441c0c00c941d00000342c0d1024050310b03101e10300828020200560700c0c8180b41c0ba00440b83c0d4201c41044800c4014440181d001e0303800003500070200d9000b103007900700012800050a050340041e10300c48288264000000c83c03101d01d61444442114051410b01c03008040c547c5411040216041260b01c590001c0c00507406540b00130075044207100006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 661146223 1250 661144973 661145003
    0x30d0f0e030c07140406150c060204050d062c0a031b0501050403080421050418060509190608061b0d14071e0c0203030d020a02010207021903120f02030412 68
    0x1415544201014145a0800da000340600a54013450381448002a41c003046024900304403490020b0307400e41030b0303004c0006005586061061a4050700c0280c00c000304600d0324000700c2c2c43c0c000c0007003511881c07140054050011181030317200310000300c00b24400e0010152070990800c0d034048412142c00c00b03807050144100d5a20201040c3c0074403c861040740b01c0d403200d81076030900c0c3c24140c001010712050100300a800c440d135100500d50040584046500c4108800c0f401c0d02024860006407142c0d800032030300624881d00f000f5105280c1610406002c1400401300000d6403107001a90712030004681e0146a4000c900003035018619403030080660380305554000803030804000d1025400042640c2440000307124805c03035441035410441c201643d600300e0400e24a514690b1340440e89900170b19406460782c03039011a00c0c09030f0f80d00070b404661440354002d140420002d09541c400d80844a03601055840c0c0b9100080401014000d84211207412040e80045040600d01120406031508000f01102d1403040c0040d20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 661147473 1250 661146223 661146251
    0x2a0b04262503140a0302040f0f030b0f0601020a0b0a092117040c0618150201020d0606080403020c011413150e03030a0903060b0a0308030403020604050606100816090b1b0c040905030d0f 81
    0x40030b410141e9443c0c00141c514249030bc4013481c0030340400e41c203880c101f050080d02c0c0c0c0c0002e141d0070b240c1d40c440c01804050741c81850160040405810150442e4000030640d54448245d80f0030a642480c5034540c51401c406c01c41d01e1841482d001c0381c0003030100b450200b05000150182d10500c2c1c10040f4402c403c0340c20340d00e070b26040c031072424120340305c0002d40c3d0046400c01014100303001d200c000d403405203401d0a19182c41d882c02540c40400c80c0c031030360503c810703d24408000c1503000100d45a00224602e80d41c0541d81e180038141c03144043e0b505003000100e02d080f0340780709441c012007119039800c0b06036a120021815501c0d000010b0403d040004e5002c0c1c0d00000c004005030014000d140324500940281ca0140ba2a007002410558020249881180510400840d15170091400b0b50405200002902070851040c0150307030a120a030400b4003800c1c00400d9480741800b0440004940c00301e41000e862000701a081800140c1d1103140c0010682e400601c00022101c0303103640a00111074401c00041540240c0d2280 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 661148723 1250 661147473 661147499
    0x1c02030c040f03112b17090411040806090f030d0b0d0b07030209090105240c0109050601031202010b0402090607030e210a032a0b04262503140a030204 66
    0x454500300d140c4d40b0103005190102e40c000a5841064204c5054a0a44c5041d5012010110010700e140000c0d84010307502d50441c016121582c102510800c040d4101c00c0b200500e84c0c0052060160701c1c4100b1000482101c800f064240d5951007040c019070038112403a07440c001400404030a135810090500000000c40c5021210a004802c151401030740d03140c0e4042403120001051b007115025451024485402480300000c03841d041c00100080c42d11280c00064035409000d1510000d041846032100200910641540c14038441ca02c640003040360a844805000590003000c00c440d50081e411300044010901a40701d2101d0901c004040711900c0d400c0d144d1041c04213032500540300440c0e100c0c040c500101a007042c503000070710800c001c07860014030500362504080740307408000800070b60b641c90104080041c41c00303da900910600f00c08a0765451200000786040d00081c494011442078440105001441d0b0f00d0144003c50b05643e410341844002010342c0c48a90003028044205542000000350182540345 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 661149973 1250 661148723 661148729
    0x15030606060306082b12110f0a020f01050c0409020903030f0724050106022a0d03050c190c120213050906040209161e0e040e03070227060405070c0b1612021c02030c040f 74
    0x1032001d8403008509c02c02403400544a01c0841703143c0c508001d00000d0300000b4107807003c64000400240e03a804414000c28118051400c41e2242250042020760070802d010070540e840303100503000e6214a040d8900c10405544080c030035140581c0144070300e0f00904584103100b0b004a40e0300e240ca100c40c44c00c40c00100302d003000010070540001d034001c1180c00d000602403015405034243c0d4401410100342580341c0c2d2001d55141c1c80341c01072006e104d100d24800c43d00d4911b00801c1030030111004018900c2c06800c10394035050102d40c100c0c414226080001d104180191811610b85155035885000f51807000061900d1003403130048900344030111110b55110f544a000e94120b1980103006162581d03c1d82c41030003440c0c41c440c3c2107481e0b060074208501c40b00170300513082e06500140898000c541038468420588804a000c0c4019050215541c20810350a45829070f06901030020f6580d04918260001c0d8201280a014010082420445407550300200e058014540003031102000c5441e0079175511030490520302680c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 661151079 1106 661149973 661149997
    0x102010b090c030103110d0f060911060d02040f05091b0307140c0c1305070c030c024902011215030606060306082b1211 53
    0x140110322403100240541e1a6401d042e422411103501c2408159030029071103013203000e14100400c9403401c10b6040b01818081c0851582d0301c00c042c2c503078158141e4460003c0b0812030b010f6030b41c4100500003205406001681c0f00e01d0b1510761465042c0c2c40e4082c510a075501002c0005000c541c0c02c4600c507201c0c10f010f100703a5996801f502528081c4882a0800c24540c02241000690200180e01024000111041d458044807091038070246c0c0d04c110b03445000580a107052100081c010040c810781c0902c02029103804122090030459214a00841c0743c100b01041c0208240285405000b0501d41c11003000d09401240725400107000071a030403c100f040140c0da251440012420640088089e56104800340901d0b0f40e80c2a005004e040c080c02080e16600074804a94145140070017a0b41c2100c001100c07031b00e030141c52000c0588105880c0c0c00480030b460380301c41d0b25100380c44501c1c4c01000c00c0340300702c = true := by decide +kernel

theorem cover : BRFrame.Cov 660971223 661151079 := by
  have h0 := BRFrame.cov_init 660971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 660971223 ≤ n) (h2 : n < 661151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
