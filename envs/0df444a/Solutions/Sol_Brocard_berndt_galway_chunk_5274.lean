-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5274
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:19:42.878215+00:00
-- url     : https://prove2.me/submissions/c1698c47-2bd6-4b0d-878d-514e50653f43

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 948381294 ≤ n < 948561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 948382544 1250 948381294 948381331
    0xb0f101206150b370e0904170f030a0b220f06030206040902070506011517090f0d031a180604021e070317090a0c140a030507240906090b03 61
    0x3025182e0001c2042c04040510b6004124105200903041543c002130780c0c40c082c00b61100f070030068483c1d103114205c540300f02d048100083c04c00a407607982182c00c1601d00800c58845800c60b0903403426420660b8460780d00b6040281c1c4015504200311500d0001903902c1074111a00340c9049980010075003102036044083d1220350100140c1c48460040c8003c1115842c01680d4406a0070850b040003c1038001a00601c401810000701d558400181e486d50384015601c90010344030110380310306d02a40f0001d2204140140b03450800a5500b41c2d22242d82c1300b202480c40050080e80f103003040f00141d01030260041118032040418001d09103980074040c15078141c180600d034280c5810b80100d1980204504030005544690180c1c05200d44501498000d00110020808141e039540c580c204032096010f030351048001001045044d9076107000e0000196000030541f90a6070300d0b0f505844402c4c10700300c4001c00c0460011242e082d9540705418440840d940d680c1c80d0005681003d0381d41005070b1029100440c006030101c250f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 948383794 1250 948382544 948382559
    0x204050a08150133030204091416020307051f06180902030c0d0203030a030905161d010807081902060403080a0e1f0e040915090b0f10120615 62
    0xd4201500601000b0045800e400ca03901c1402481600183c101ca40181d44c4120b14a002c00c424005100c9800c400d9140d078105900700f14001c0c081c680c498000a03081030a00454908281c400e280980c41c881184080d1414400c001c2c0d03907a1084040c02081c551100c07070300e0807251039000e004041c12641340c00f000c107941c0d554001d81146612030412034032a6503900c540810441c6820018403840c102d0580b0829480903880c2c000076203d0244220150625032079407a01810044148a000744500c41784c4441010203460308041030089a15030700c21407864002400204000800040b40380840e080000207241e140000e906240540094180c1203810400c00c0c000480000c43e80c9000c2d000c0807010356140d400e0300d80600108002c01c0035100b030301c44202d4101c80e0201c0c0c400c0e80c0301800410400e01900d0104803180f0794075103411880c0c0482060400d161400300090100054941d2040c0074045c038884a05e0b5a03203507003141084510117442580071921800b40303940c00145e041d400c0098090422821088526610687d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 948385044 1250 948383794 948383809
    0x31b0301060f0b0a080f01050f011b2a0918261b1606020601060c0215030901090210050301060207211505070216081509070906140906041802090a020405 67
    0x82030001001103190642c132a440510290322079201c9814011039403410000c80c0ca4907091500340c82c10841403e1425080707026014856500c42d500004404084940c1c0c048104c101120320b00202881141820000b02449640201010110500a20140c040c520390b9170701f00070704080d07001c400d6203010710340204400da00780c01c00350140c44440031103000030b0414a00c800e410841d00c92a0201e440e001503005002040e400a60603040d6a418100b51031414818000501502c4450704240000c200c00020031000083c10f401200b0800e20999480341d088400c240190707103d010134060840140c5c044075041111a8050f0140120311844158070103080145071145d020500f00d158a10345101d84610a010785194100704400030f1425011074000b10604100c0c480d9118034002c0590082c0002c5440402c10100301881a01d0091068030420082c86a50ba0030846000c1e800c010510701c5044034200185090600d40140c202340320400b20341ca004280290b003040620580601101c0d0b0a907424040464240c41d03044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 948386294 1250 948385044 948385049
    0xe1f0c08040b1f1d060114030702070b030601030f020f070507050d170304020d050f0d02240c07081b100f09080d0908091e03011508060a111c020c010c02010b031b0301060f 75
    0x10b00213545850701d980003400490450340010346240b410030421110903400f0a204080c0c0d194048915540e888080040f00074000c5d401e820f00e00648001401c0c040201d51070002c1000f01d00c54001d9481259540c41041101505800080c0035170f158106112154a2005d00035544188024801c0a400800d42c07a03551038007041c1c0c46045801ea004011240c1c0d8990100702c4081e603030800d402c12550b0740380c0c121805200c4000140043c40e040380041694400c211040d01907490344907408469090b04149408060f40d40c10240c4801c0070348a281443c62100803696000d10708141ea08000303024580182d07804448010401208142c40411051082440503520300c42284500300740d940d240325140c81c50f0020035003116141c80d030709190303a5402e460401852001095080d4000305400380010b8034441c50700e4030315481c450042c8085030404071000c68010103444c0d07405801261501d07402000840d980001c04e90072500c80d120702c07e90503032114020300555040c032114010041d001400104000da40e9810040b4a541d154 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 948387544 1250 948386294 948386339
    0x9020304110a09020c0a03030513022d0307050d081804060b0a0e060c0d110109060c030509010f0b0307180b090901020703080a111b010e1f0c08040b1f 66
    0x1c082007895450400d400303801903d80c2c00421032400c1c0d0010714443d51048452002028503480380001403d59449810302c108958002d400b00d02d85511500350041001000020401d0703d40034002e000c0040d050005901054560180400d400101c940d182d0440e190060009142080e8481800c4034150b00c56010b40300c000c1419017140c40d258000101d001c1c01128072504c0f2540100002d00c05010070040c001402c8c1c080380007038288600312004a074100da014007182e00010300040e0510360070f1046540d06900c41441440030400800280b2042c0c0000800d82e88043c01d0a585a400004144650104c03040c406902c1038070780500150090300d0b03030b0100388030366400c441004141c0d501003011000d1542017036805500400c2c0380d104002c3e00c804261a40602c0c02a1549001c4008070700c5450790000d542540500c107145419811521032450a0044011035000410f04408a50500d6031504c0b082d40100c2d080d80c0a00d41c00084186141d9035140e66800701d440c40100c0f41e145403e20306000502c10050300304007500f030710003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 948388794 1250 948387544 948387563
    0x203190f0b100507020a03170c0105090c010909090b06090702010e070e010527130c0302030a0b06120f07050f0d02130516080c180f1002061501050c07060507030909020304 75
    0x5000402004012840c900b90078004200035080050707440c10b00c4201904d901894401541401c0c500803212400b0717120b6001581d40c6000d05001c080040068000d5010009076034007111582c94011200c00d4603d901e20040004000002042003841c3c010111903011983c0d1000107403080210000380d01e00503481d4411001514800f0043c41a4100f12182c040317050b00d83ca100f000f03d06c4510403a210f00480040c05000060582c6100508002d0321421000c01150014205c410703030304080c20003a16018065402921410203042c840b203442034046020303151a061200a001c0c01403924040c043e440b0205000147d11820000e150401a80e902d010041c034042c0162f00090540380841113415943c0005840b0f006110300c510412840c40000c1088403103ca1031400d509282082e00d0001c900b02c4000e007200640d000840c000031465003a070025080780304400d108045070072040e0400c01590a0300c900040c10246400a00060014500440060901511078500501d080d5a40c40504080b07800c15035007111220701 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 948390044 1250 948388794 948388811
    0xf0b101139060708040b07031803030e0103050a1b4a01020c090705160c0602010e01060e04030512180a0c090b1e042f030702060705040b0d0203190f 65
    0x1081541c600e0407110a071851480c00f00107890b8601580120300c9041d40a80d00040e240c02094403803041800d07031103200e4040300c00c219180d240140c41a500480e0642c0041d02e8800040c0076401c42d40140c0304d0350040001132400600364110200c0f000c8150300308003864500102c0c4402840d194200143c5483d48540080c02e1030306451400b208021140a104181190310101c00d0324446c0c0d842c10341c80c907080790050130425595484411712820201c000c000103003550851a9000580300d4041d0030085501d01400d0003004119243c5d294100b10314020340d0041c002800a00085001240b1124513503000700c115195441c401030303041e160358a07102c40c1c1c80040300c2c8002d0382001040203d01c1d5000c3d0342c4c40100c0450303c60f4030700462074043c0c030060b40760056168401c0361192482d20300112070900c5001c0c0c1501d103a0f20360100850310411540264415640c800c01446070070300040803944110160740560340340c504903503d03102c650541e070006504054440f14000c603002c24401c1c5003451a10494034611a05100404e2419 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 948391294 1250 948390044 948390133
    0x1f0b0d090206132d05060d0f060303230f0702040c090806130614091c090519081204140904170c0f0124030f050a080c07090f0b1011 58
    0x1040b41880e49854a0320300140d15030f070300769500b4117030303901505e0503a1070f00c0c0c1d0f244489016181a0b042c1d541c00c0703440c00ca008420700d5031005448260078420f51046402c00000e0001d03100a00c10095159442d1800b03100070401880c158111038110000c52400e030440a403145421403e0010a403200c0b465103500401c0c10041001038010030b01d0611036109043c6951078502c800f25211180081c000746010741c21030030b0000c0c25002e0309684025100c0904014141c0d0b6080070081d6050780c8a0165071424440c10b128684030581c004100d80a50b0052034080079181e0a14003805104d06002c0d00c01c5811032a02e100700207002c1c012101030b00c0c010600c1e80c0201000400c0004842c01c40305014801e00401c0d50481c40441c1846c082c40301002200c0d8004411508980307241031181c141424484000c011071000502040240d1000860100b82c030100e120800004444000740320859001580c05504940b06502c1e030084240101c1c0240840e0a506081c1c40150104041c0c0c95121182805001500c0199804404800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 948392544 1250 948391294 948391319
    0x30c09030f0a12030603020f240c010504060b10051b01200306090a0515011107050306010b0c0c010903020d0213060314030d0e060702060f0711120705061f0b0d09020613 74
    0x4030f00e604007041004d0654022480d180d1203000c0c104d0050403003442d0380308a810310442444924000d03c01d9070791514aa102c0d5a40607110035102a00c004e41085020641403900c00b0380d800300c11005da16041c1ca4800b46040f005034080d0b2a84a00c03145540e6142041800c100c00b40d4260000b5107000ba40035540d160900810500880207007903818034501d40750401000010f251044058200c0900304084040c1818190300c2c508051900056054050f44000017046010000605815504c000507108000d0000d801100c2441140c40060750180b5005201c001605141d090030401c0c1c05810f101088603070301c0c2d8030b8803004181c0320210002c0c2580000745443d00410b0a100307001c1c0b40e40005000d40564200b0042c02556080080c0a1065014800c8003003080d20b03004000c070440c00d1460f042501c0000410104511194002d03050994072801042c00007a8500107440042d01142140c07a80c5c00c3c80181041e00041d40c0303801c140e05c100b840a0750384a00c1e40150303413820050300084e0440b00b1500341c05401c055050444 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 948393794 1250 948392544 948392573
    0x6020702090f330a120302070b0f040302040911041d070b0405030c040509160b1b0f120309010f0603060f0e06040b0a09081606060509100614030c09030f0a 68
    0x1114010b000303024400070190340c90310034541d607105501c081604401c0300d08404248a40f00c40e40c001c464040015581c01101824443d84e4000d0f02540e45d2143c0e2080310405910075000803501c03030001044207200620b42544080405400b50100c1c00080442c140801c040f10021144182801c4030608400781021301081500050900d0503c003a0920345058082640c82e58508031042c0f02e16122070000380b0046003004429900c1801e902c8000405a9641507112680d0003600b40a41040040001c4800c01e480003c003004007107240e8000303200010451501030724580010b050502c203035403150080a07448000b170281201840c004c02d00010505400c0c20400e040301c40c183d0504000e5000300f404c20021a0b0b10310000e0740e101201e0200031548044520344407219110300c240c0c1c084868907410900042c01a2540800140c9105a03613000d0140c035018031a4044d0300b054464000020b020003290309061031001c000c1d40d0003403108455a0f04000700130300001d00300360302c0640088182d800442c910043c8003100713030750184 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 948395044 1250 948393794 948393811
    0x3060f1d030c03030a18080703030533210a030e0310050c16020607140c010e0a12060e03090402210604060e0610111e0c03060f01060c0f08070602070209 67
    0x280a0294044940300d00005204000e2190742c3c031b01d002c5542003140001c4461651010310356544820301d2402400a102c1034514011140d2141d011402001d0b0305851588c40c100800141401ca0a0f08030800007018410240b00e40d0041c013101044105510801071108458401d031554591061b90400f8146042410740b011042d4500f8030041c4050000c0d1501152201104408403402d14065800402d00c1d6100c1c1039002050400d08000f0a50001c00104108003e81d00981ea841e01c0d08100034100282d400385c60090030708001034000480c001130025400214032501e14429282840c41802c00101207811400000c429219a001d00240142090610719848013044504000060409550007400400244a103015081c1c840d80c84500364010031910403401c1081d070031516546e8503800d4a02c01c1c80d074003c1c461400b600c184002d0824514000c0780301880b80c2100902021540c1c41c1507001c6503100ea000703c050301c007200002610000315114100400c62a1300400001d40e8a818501c140800301500508115 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 948396294 1250 948395044 948395047
    0x1b213b03030f0112050c090114240a030e070e0906040506071b120302070b0412090501032703050f0309010209150702031209150414011413150903060f1d03 68
    0xc101d0700e82c072600c603054504191940e80c1088a80c5001860400340103030481d44000b241c0000a01004224510310308050b054503106000e403882c9a12401035910a42144c3d01003409102200c2003500c07940c401640e04088004840c0c2e010343c0d90240c00c1c82114140c0d11454070383c01401c1008244a0f081211a403c18000e01d480000d4a1305400007028031001c80c00c00903c60030f0510850740710b01d03210781c0541d607885402003416555400c0c03e24110941009400341e0101240403400700090541c064450001c1305424040e02c80600f0010343c02d16070b044a010301c4120300b4480c091201007048503040d0003452003138034075800040c2c2c0c0e9030f81c250030080740741d2210f80349181042d8200100740040e1008900305a09910f1001710944a2207608000f4100c40201c0104108402c0c0c0440c1c0010407405510120302d40b40c000713880390300138210082c1c0d0300e00c0d42c0d00c100c0c001500c4072150303414108101d80c2c0d014000c41d8a0102890491034440d1269100010340d20210501d0500c49d0f03c0c5d521205181d40240b070302860300d290b07510085 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 948397544 1250 948396294 948396301
    0xc070c12050a0818030d090302042f0a030e0f0c0a1424041a070c0e1b0f0d05070806091008070b09031203040309091b213b0303 56
    0x7942d84009940000384144008201c100e60321440c03030b2010900e410000e05070381321440326010041a03c40760348001c0c2c1c40343c1e00b00480203d40200003d01d40e00c141c1800c031020760003c5407c20071000c00d60b210fa02c034403081640c5c41683c668540428842c0308003443c8484d000d0484c258064040005e0541c0540005102c01d50700b9001190940d240481c4000c0d4140300030070388440850150080718180125409600d00c58400402c280c1a8500400140401c920681c180c0c1c0d40ea5817106040ca020000c2100c00741a03421400d06800b1111803800042c0490000e402d204078500391070119010181c3d5000c1c1c503818081420001400f08500d003544003540e01009000420200360314080c0280ea0760802441140c01c4084001440b080c0e0b07842c00c1c4120119003452a4080790340f0300b41481c0003000220248a007111045c504070364030402c041c07290380e92400003241c0c1d95802080c114603031180a99950b0111260780040d6142002c00b01c010a10a8610300075007460b1645000710100c40580e11152105404190950401c0041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 948398794 1250 948397544 948397553
    0x203161703040b1804060314010c03060905060a03020613090617010b031b040c0909060f061d13050703090b04060b040b030327060403061113080105040c1403150c070c12 74
    0x1903503164052140d500e81c1d10303903401300440e0080907540c0028100341c0136401405d1070003905400c4400c00d8503484e98100034842d44e0350702035800c8032801d641066001d0b4030200c0400151a014000d01001c1e1426491011025a44c030007000894829602000400c688030341c84049005c2d003071007800c194103010340140000c010401c000e0603440908045562242d9036400100030a0b40c402d00603680a4405139804000840c0c80780784040d401036a80c4907900010f4800914501e100700603a00c80e400c81c5170094242c2060303003d60b079003410203480000e00d4507080640d50000c5078086000c104c0502e0240d80207490000340703000c2000c184000c1d213010484003400b81d402000814814940d0303035030f49030f450710f031040c41070396018480c10010380c4511480c0d002921003810b021011440300d0745030008240210b404403159200968500a050036600110b030040c2850301c0051080040204440d201034203030200409485044c11100c92540d03000c4010313900e40388600000306407541003040c665011070281103880e109040c08005581d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 948400044 1250 948398794 948398797
    0x190f02010e03210a05040816080118031218120c0308060103090b01121703041406010f08101515020a2d0326090f0607080c0a0e0d0203161703040b 64
    0x80a08044000140d03080d05034840c170140c1c0c015007610029100241c0e040302c2140d030004c0081c0983c01c1c40f5441d00d8500313a00800c1d00d00c60040e01540c9600c4168000e9024030012004207041d01d82e0b00c01034410141c544000034001501d00380856821b0f210a041a940390134000e03e900f80045c040780c10b00d803038001c0d51400304082400d2141160151440003041c0030052400c440101c8440030fa0360340050020061008100c0f681d148070300080c035800d0460700940ea8400160000601e0361054400d25000441e20720100c811541040300400041b0003004062035861940c0d1214000d503840b40300058010074248010001004c001111480401c03941e5101e140c1e40414030f490300d2100d224010309028541c418802a450200044540e0440107000e00c0d8142c0b600b0107a89440b40f91240b00d55269005090010f036042d401985514000e4600c110210f04007808013200380c403110141150301c1e1f803090002c0d60800042c1d0741089080905006210554613841c6081210344507801164cc00c20390582080c00184030b800920390 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 948401294 1250 948400044 948400093
    0x906030618091707420b0a0533190c06061d010e0708040309051302220f0b0703020c01080402210c0a0f140d05190f02010e03 55
    0xc0001000039040ca040b0300910f04440d1100c003141004211141800180301105200308200f441e00fa080c00c1070341e072252010703100c41c2c542d1840c04114008112085806517014071a01c2102401c00e405a589850010700158240d003622107545012005000f0f4030007407070307c1c4108928491203030642402040901080e20325001c100000c00c008442800505103c200e800c90801000e01d460004500340c0e1013000001090024003801daa0502c1c80d8005c5202d1134442da490510554041c0e540c585100e003071400304140302c800d40182d000e40c0364082c000034000c0c108107201e560035405000d080000003031814048440c0a4070590200480b8a0b0030300c5424003290b000f08900784803000918007110f10340d8561000606641e070300181010403040e40e0581d0348803250b00089100f401481203629280143d69900c68040d060540d00441d1104840f80a400e0039a04205400005caa0f2148d03081e03540e00c03d8107110800807070303010020545501514a810300103650300002e0340300f140710b030540203440c101300d1103240c01010b00c9c01070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 948402544 1250 948401294 948401339
    0xc030a03020a02030409060609050a060e0306240a1514040305190609060c09091107030504170c0d05060a0f0605010503061e040204030b0103060f140408181003090309060306 76
    0x202001083d02c284110b070042d26003c00c04100d1a40c4858005042040300c3c01542d01071040008080313804c6009200c094504600140108001d90390641c41030462900b07840821400003030b0309116003144c0e440c6503074074000d010405200031100c00e860300000e000c201d5088000c8500c0348100401c0c00840e07004600351220303c2c0d8515010748880b54910702000240b40c3c031003015010b03c3c9480502c82e4003e6120b4101c104072a082002401001340c40c00311070350710f445958402004030b0030401080211611440380c03611515189001d507000c420380700000c5041940e001d041100e085d00302c64100003501c4410b10a21900f03417180d0300100015420b007000604517200142c169481002103091603001540d04d180c40000b42c13030740603009640710303a40c925100d80d01c0301086c0000c54444d81400d41c600100303c8a407040b5100c1007048650005a44ca0795216028582d114464010b0003c0b00c0543c030343c072991a022106182c0c40c0c02958002102c003d41e007070080004180e81c00c00400c05003098400c00140d280d1100e41c01c41d44038031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 948403794 1250 948402544 948402547
    0xd0b16050714030a090f0b2b021c113a060929010801030b0406091205030405010e0a0503030a0c050d0606030b18061c050a0605090f120c030a0302 64
    0x18401035a0a02401800422101071100c1000300c2980210142001c040640c0b84c03c82c40395142c00070301309403885900900c102d503002031281402e17900c6070388582146004000c4d00003010308400100b4400381c0c0d01020241e42c01c003c21960340c000c1d4082c07921940120580000021b4107000604000c6000062003041515039116170403900100401045824440d043c10700600704126682c5030344400c041c082044c84c480742d5000c1c80640c0b040044040da1404201c1005035140301703260707081d9501c104541c00041c0c0301380e07011503a41a1850000e8506e03038036540f8907080303901d44a449250130b16102d402e4800410101c070980e0081050100000d0b40002620b4011564401c003240030745200504a85038042c20320388034802c1b07080590002d002c0b03425a00140c007030002981c65100f00700240c0d0040401e4001950301070342005050381070400500c11080d0021020703100783d064030b08480261b143c1e201900c01c01e80380d59210750443d00300c18000c1c4078100030b0341040c10702020800f414800019100d80e16805940041000c0c987c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 948405044 1250 948403794 948403831
    0x204361101200f0105090d080103080a080c0d05091e0318010302030c0d150e07080907090c0e0310060905060f01021f09020a03030503010f0b04030519020102011d0c0f0d0b 75
    0x16010101080d03012072004940500c00c25103c518003078001a1507241141c00790885007005030748265001816a0b80041e003a030b19007481000e00300d41c1400014100c0107814002e01014074210218000c05000710403140081101039201c441c92800400c1080c4ca59403141d00400c18601500c0307455480f0901d051007401c0044e241d41d541a000d07441880b81400c0c10030700c82c1ca00707d803103403c0020002100d826140e1138603c0c6090365461041c1035520ba02c0c20b4501030250741c004681003003d907216030095041c0b802203141802c03c034141540881d16107c1100303200e05c0559114042407000589511500740e121504a402401394010440040d40310409040d441003808220b4440d0078218285030462602d030307503000c3c00105a050307682c03c00a001390030a01905c1c20b458130303044000900310703440c4e002d55041e43d802c0381c042d14004540e008042e0011000310b800324155525180c1524140720340040d80400903080a01820354080f021f010071681d00c44103001e82e4441c211000c00039002c2071131201019440814030409002c0b046 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 948406294 1250 948405044 948405077
    0xc02060a0b12031b01111e0c160902030912031303181203051c05010303120207030909020a031d0105040803010b0a0e10091d04050d18030204361101 65
    0xe0400c00c00d00b00d40c4030004110034141c0c00c980c60102c00d0300b41100200a41034402c04ca074801c0e0321a0701c956526041a594003882d8806e8104018003101400404403042c500d103662140c2c01079413140d801000740c01d901008205090300180070441c10100c040d150703180380d40780054258818080f0f1042c050100201c1c106e481e001c201c0f0350a0020301800c0746591948045041c2d00d4028000c0d403260740841c0d031701510907003010b82c0840c0f14040c1c20306881c0c3c15143c655912285400480003508041e90a60802c15441c000041400d00c0744010038440c0800d42e008035050104e000288400ca249120034829071380740c802000049035003c020703a81540e0071620080d64034031007400100c41001030841c0c00d580c04032441c0403146440d80c1102d0382070102c620035510080000d05121300d4018400c0200c9010380507800980242054521494510420351821000342035020780360703000316041f90220f44071003c21910b203018224490310007484c02540e00d8102002c00c3d000c04801e5a40105c0c0c08031080b1040d040c402036031307542d42c0c290 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 948407544 1250 948406294 948406309
    0x3108040515071703040512031f17150f181002120f06010f0e01030b2e1106090d050310230906040b03031b070e070809100c02060a0b 58
    0x419005144a07040c000012410301d65500000b421100308104602c0303c07021000e2001a0f1380f090790010090003070070750300c1414101c0079400140303580b50314507c400c07192040714180240c10020780080d1003902441a00060030ba4508801241300100070041b03d03003000301d050860703200d0310b034020358241c0d00101d100ca2080c10186040d0711455441070003070011400e50000803445031924032440b0001078400c15a10390f50010748491100829003400142080001840c5e940281c10055001070050151214006090140818019040c0b0980c20820100c0e010b4141c40d40d0220020b810701c40800094621400e08211041c1c3e82ea818004000500c5804400900202d030f0380c44188000b849c0c44d0310001260b01c0034003850304038842c00060f0640f18221480100d01c0c03500303052003040b411250142c010751610749041080780320203840000340102e92041d10404541203811055560040d000c41e201e614035414060112401d0003001142084400d25108542000c550b0000f03d807500000013181c0050017050300b07800300c0d00c907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 948408794 1250 948407544 948407549
    0x240d08090420030412030c0e0415051c050c1c030f050909040503090a0602120f03150d050a05150c030c1305100e090105041404031101090b0103060e06310804 69
    0x94070194646000c0e401d40c00d0b0000c0d07204d5485180d08140307841004000b51b084402c2c1500306800503000d54102040360605500c0802d914201da213000344c0c03d40d42ca0740051151880050514414407030f500000d02003142c1001042c40b1000304032414081445031640c0f00312000c900d40300c09420003805004d1412014040d0f011141310f0310700940324140903d01400c18683d01c0d440201c03218040d4000e03030380020300742d480403a160a0780410040d08a180c51a10f207003090540e000981014051144020003030001d43d907001d802d0700f003070b841840a070040071860300b0081d0030419034401441062410320100b1444000c100122980640d2450100d600c541d001001d400340907589070170860300003180d04c04040c0181d81005810502400869a000c016a22030080c0010b540059426507503001140001c180000d02035031110850084139000011080510344854060740303c02c0c0e006442480ea5084200c3c00d207401800900d600c08122884459601e8855440103418803e51a0003002c041c00013001d04100304641044400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 948410044 1250 948408794 948408821
    0x1204031206081605030d031b032301171002030402060703050703030e060702160605271c060b01090603090c0e1003080c01060f120b010605031e0906240d080904 70
    0x14400c3d61604680004501c6010303140c400c0c840c1400b6264442c0c403900400c0c82000c040e103d07c90740130716100d4080d07020b45581c40c0d03890310030800240380340d4580010380b0b0494007c0109822207114048109001070510103807a003071200080c010000c01015072103420032518100d0781803038515950380142c1012001070861603d8160350303026203420310102070b0b40018401410b4002100c148001c0742d645005503000c1c412061511443d151402d106040b862100982c221800b90290028410340710200011202a41c1c664044a499942e90022500c55a0182018024141d18181007041c144580c0f00c203500c1d000d0911600c040820342c8400182c030403400c000154000d55208004584a01407410340b1800fa017014001d10325540300116000540502401a0150540d00100a210f06174202081243c8940c8010310000e145007201000007607c0a49140d040c0c840c08089001c0d00b042c0c1440310f4000301130b55a01d40e56000303e14540f0350814040c0e581115000e500e075400810300e95100300c5c580210740580100e143c45072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 948411294 1250 948410044 948410053
    0x120d080a110313060b0f030a060c0314040c1e051f021002070807060e1903080a06171c090f121506030b01080c01020304030309170a080d0b0a0506120403120608 70
    0x500503d80140b04a40c981c4568824010a00c0c05c070203103e0100c1e43c1d103402d294150f10010400000c2502940041400c03c0180340108072040c072212400f6000c00207840444d080801301c00100940103150030300c8854900140b5032000300328580b4001861500c42c002c400e8498040820000000034001c1016070200b02c0d00800c10754490545040c8500207400c802800e94001d818002c0440641801240c1c2d505c00000383d419115041d8060345017120151401005280d40680e2010702152400d00401c8000f02a8020f000410503032200008001c080c40c034902083d0248401c6003001e2184030616440030007500d42d6800790900b20807d506210041000729010660480c0ca8402e0200600509550003410389100d207041310580500f40004980e42e11541c400500000d2a81c5418080300d1042c0015504a03008002126008640798039a200168440c0c0c441040d50303640c83c61a0310283c1071003107800004050480e620b0341041c481d845035000d6440014002000c00501c041c45240c10350440e442a0064072507642190b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 948412544 1250 948411294 948411301
    0x30e0f012405062107020f12041404050702030a050a020102040b030c030405061f0e06180c04050102010614060a0c0201090e01060504061e320c0615120d080a1103 71
    0x401c003030191000700740190311080c2400308003070808004455140007100543e50041e0701c55001e4114a14014050404501400c00358003644030003002900d6a52080403084c903a1580707040300c90900b800307401c1c038014003a6003002e04001c901d46d0040165800071141e8100070740d4544d4142012402481140c12180346003e011041c099a0103405010354402c0d40300e0b2086030340a8960b004840400c0190084c80300300490102824440d0348140212590801c00c0603146008003195a000f00108030411910b0340910710300464108000e42e424016000200800362403440c41104450118040c0e11454082c2c9041c804802035840459100c0c040031802000c10440024695840300300c001d1581d40a40f00f100c00149038180b14080d02c450000e00000040303090b441c4d40850101e80e4038400d404040e181200c1c2258410b800c0200b800460b6980104121091074001d0021440c4c8054584208000f150000d13014044801c1040289200000c5a42150343d55003440251940e031589040d000d003100b00c590380724800021060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 948413794 1250 948412544 948412571
    0xf25140d0f020d051e0c0a090b070f0c05011b080f0c0f0c0a0603020301120210030209040e010e061308040608151012050603010507050d0203100f030b040c080111030601030e0f01 78
    0x6004528030502d070600c41078030351030a80d41c10045c002209805501c0c0362400b2681031548200148550400c03400d01117903187e550007103034005802115050b50b8003c0040c00b120204411300019002921003420000761310000c00e19030740020660807200400c1d1a40c00100015034020740401c0ea00c90b0040f40e400c0b601c010601c03001294840d1a41005039001d003141c114049001b034003d000b928140d60143d20308031000c440a408126000420301c5540040c0740d8200640e002c26181c0e03014030000403000703400104a04134440c4150385844402020160080d0342c0840341000104d411084800303c171114038000e0159240c0d210903240701c4040007c2141d1010701c4660420702e6913005846640c42d110701480c100102e51714241418203842045600d40f00180040215121210455000d503800528444038912255112205203226002c50742094488001e01401c0208214a0781e071000f024001e10b60080c09000e80242008040c0c2c040541118141510b1f0307100f080c00c14004102030142401300500078001602c48040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 948415044 1250 948413794 948413797
    0x11404051e06040f1101170c1305090601050403030f02121c0c1d0607031b030509130212010b1b012c0307050601031103030c0a03080f25140d0f02 64
    0x601e9418100c0020a2038103000c01107440791149410440381003a4034090740d1400e0144000001d0b01c0c1c180314080c101041e01c1104d00e07044911a0313010446007030b6204954588840d00d01c034590300043c46001d040b400c0080e240d1344682030364101d84d0b040c2001d400c45000401d09a040103420407035039070060404542080d10140300040c07044c00c0c98001000700a03070004000c0484480c3c05500308038035484040c0302580c0306810f02000400c04ca90003807600780c900d4020b040c07690054520004090300054400f0480251600e0728600a401007603120600310714006001c4125014a00b05100341c241040c008180a4220710401001e031619140b01d030001c0044c0300000301d408056248044845542c8507902d0100c02d00b64800200715402140c0100040000da885e5941d03468036020303040c0e940c5030180014072110305107810801070000e18a100f84c80c1c0143e58503203900c20030146000204899030b005e044580040c1005d07071814460b04645074034603241d80361008907641541644100701004100300c3c9805040c081e007122660 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 948416294 1250 948415044 948415063
    0x6010f05060c0d050a0302160c0e0c0c06040204020306010e13090c090c1b020612090a0b06040c0f112515020106050a090f0b04050403230301121401140405 68
    0x2240000155261824440140201c60035105103900c03031103801c1c800d14001c001920600c1ea07280750241c03405403d01e40b0030701400300e000002c842c00c035003d80080c010f04845072049079000b6216800c242c00e00e01c055402c15550940500081d01555001002c1032559210300301d0030800c00c1707000d00704481d0a5011344910380284001c41058880c072104000100d0703000d03030350b00503c0101912907643c41510500f2a22400c2c01c020303004400c9130b20410401c0103484d004440038a10303114080c03c5c6c024140c0180e96080400800c02c000f00114031507403038005201c0c6042c0e000842c20318000c0c0d41c1c1c074040850705280001c1d00d190603849030940d030084208500f2107540301031021410044d2410300c10300c03202c40c1d40c0c02c010136402c1c1e62103070245036480f03c083e00c0103010b681d0080e406821151510f4901040c014001404502100c1080c0c03001c0d0000345490721080e001c601c8a00903448158001c54180d0301d150714106001d06404480300b8000c100200f035441d400340780542504040000d005640c107101e01414903242459886000f038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 948417544 1250 948416294 948416309
    0x9011709060f06030d0c030305100e0403020d030f02040609060e04200406021009020a15090e01090b24040504021c1b08150a052b0303021b0a080904091e050601 70
    0xb0004205090100d038000c81404203803202c01044480b50780a030043d20f0014580450b001c50203100240041400151030f0085000ba00503049124200c0401010b983c10100d10803104d500401c0308001080d030121401085400d1460902e00f1140318030009005080610403800c80c55182c001070030700ca041608010811140c0c507400700d80e64490340c1c600c0207094a09154001c3e620110700001001145001101218912494584a0401a06c1d0000d2800c868000e0f002880020b980301124203450034000900303003104030007410348691184100f62003080c038813585c090702e0f014540120b001c904941900c41520504440d0300414402c440e80f01d80c41c0c80142c2001c801c82c1000544007000b01c1c00b0854000c1200002e00400703003030518241d00b80414024010783d03008900040500302c4400904280100c01200c4d03101e0712030b40d00540e80710086240c2207280724114146105a4201d55900400201081c5c2224195001510f02040b0b03c0014100010701c0312200c8818540c0440c201209010428041410341c10303107214 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 948418794 1250 948417544 948417571
    0x3060605101e03020705120a0c02010801050405042001030e060c07020f0607030507080711030114060103050709061b03020a050604031107210b180304030c030c05030f0a06020901170906 81
    0x1d000844641119000074035500301280702030021144203800500200e030240c1c0441d05a0a4a0b8940c3c00d4036502070403100c4001220400710030115a4800400307030040071b00b00c6051219042503165400a1031068070100e080b42a801c00c0320140d82d001e60049001345102e1700644081e45130192607a28141c0c80940c040b40300e01d03004864105145001800d40d1038031501550f58034203100e21a80c6040c41540441400c0c0e607488c0074901202e10703a543c01d008401190a1540d080f621a01b410b0001406460024010005104560400740002d070b500c209200c00c0c2e5500020450501c1c50f4909040e410800106c44c0075100780141e008010604d90408800100c415541085a11680c1c2c2d40b810400e0400c0102e10303c03140b040b0b40d1001e020100c1c1c5c001c61140c1d0003103000c21425003101540c908152442d4095481140d1801042c1000c000744203808116200410095000e08036000306519801e80710f4003031100003004240d002c0b40c0803002d40d21130785e1080400b0301980321122032820103020680e6540c00845005404901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 948420044 1250 948418794 948418819
    0x504112a19060b0f011809090f022d09060114030c0409050c03041407030305031f2d1505041a0909130501050901110d0908090301021902160810020a0203070c03060605 73
    0x2058041003298007106c40c061855905110082014004540301650001d05100d80a809070b511072420413090bc0b800160180c10702030394610003041035907090080b0700c1100c0102c2002281c0c4d030000c2e0000e68120040c01140d50702d6980004032405e50089800c1400424501002c003c08400b6400040d07008070300a034940503504100080c0a9554000c078040140003420901c0800c801c42c035414502000074030013514209c003581d00c40c40721100502c06a1180000c5c150f4598003251880710000e104400b41031b030510310b050102d0402101500d548540d11451480b0000d0307660b1090a245000c0545200720801007205015043c16640d140e0380504409040c4d500307502c1d043c04240c852005102e180b00310180d219202c0d0800e025109d022004010641003070302c0010b003c20050005035000e10003462680c001e40081c0080d1110400001e141016500310882c0025440c0f4003440031000001d940c0c0c00144540b5000f50b40c64130011001c90440c011558000d00480074a82d010040021941110b4103580c81903a01118004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 948421294 1250 948420044 948420047
    0x30914011e0c021e0c01031505030606091003060c0f09140a060509030102040806010f08060105030a0b3601061401031a090403020c06130504112a19060b0f01 69
    0x18031005109180c07a400040404030200d258000e50046103160050b0341c8107041c0300b0380190009030300310468601a04500484006584c00d07118803040d104088012000e51402d100210303030344410180009206002c0300000840c0203034004005400380d54045021701080304e42410140c0b0083c5c0e40c403441c1020a8009802050180507512120703059080200030400c190f2410805039284d500140c0800e4041d5020000492900420002c0354000e005510300002098505801c0c02c2c10b100b0185c100ba0702c01d8110301c030954045000340c0c51481c1c0003a094500141140000c05440d17641c0d000c00603e00aa003d9800e0180e440048190300007001c031090000f07801c110310107031001101118050507160140c0001d20070f00d8600d9042c004902d55000f88240102c58412203030364005001c9802483c141442d040c003144051080c6d0a00f4050740c201254516111070a1000340d1031026482d21031020000d1200e0101901a094103000f0041d1000185031070b0746100e460261410101d02410262041500031104401c403e1f00a5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 948422544 1250 948421294 948421301
    0x1020d0302070f110103060906170111030903041a1b0f0f01150605070c0806010b040f08010c1409012d0801080c0a03200a06053a090609060c03091401 66
    0x683c800100155031440c0d60343d55903405002c4e5400f50406640d11004502c4003100c0c864000500389151203824052021344105094850090300f440d4101d000703106108175180004145d4094400d01e2600048940000141154501400c0140811001d0042501c2c0c218400414800d040c05511b4058032044a0b02208203402e0b030300520803904000d5071110701040028030036806040b140c0d104500180c0d1166413140c036039140c603800f0381021111410000301004100301c8041c058008141e24402070051010001024141249078040c80e00341d2980000d508609a2180002d034401408440501442001d52100340c123241120001c194081280f20001050158000520744d150004c024000200141140d4481da04158040c035060211100a081a5a643d450f100341c04007800095032050313119260941000786900724500001480700301050105005403440100b040c5401c099900031520b404a40b400c17000030700c10307000003900c41d5107807101e59140280e05070007a2074054065907090740003600c00440182203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 948423794 1250 948422544 948422557
    0x230f030f090c010e0f0307170606010f09080604020d0f0516140607020f4f180b1005120a0b010b030702060103030c0c0509090601081e03180f060708040501020d0302 72
    0x82803070b00801c08082e01c3c3c145560050030070040c0684a140340e844234081118540125004d14940142c010032000756800302d06007030303038207603a1404115051a240e2203680b0b07008080c0010780100c0f10000c40e4020f00c400203490b000101c2d40502161b440350320841203034411996a004441d104403600340310f43e54a00c4c00304140d4045640062004481418500030451608007a0040b010580c1c84c0d00c1c0d909a0a05400e1000d0601540d440c5e02020070040700200301c2810a032540111580503c0e015404034843c1c066802100e581d64462284e0040c3e8031001c40103541d00c5016400380d54009020f4540304215400403645422580c4038a100003016602d980d815401d5000c1200c203540107900c810300400101c2e220700c2c100010b0034012412101c0383e80d104e9000c5401e80340100c1d4440102d51100004206480040004051108030301004005800080c58119124410700550340e070107007007d514540c0d180e62100c0d80c4c403410f800700902c201d07a21422803410004a82003441441c0c054090b115088a84034040d0086030361 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 948425044 1250 948423794 948423797
    0x41b030308010b160c0e04020103150b03130804050a1418061c0f02060d0c0f0e1021090302061608040b0a09050a12020a05060a02041401230f030f090c01 67
    0x38103070f0070409484042d801000031041205104041800440c030071000440240401d140f8500c20313450540000340649800b500c0e544998111080c0400110500c442902d42109440d2814061141c3c64101410307140681c2d0081503210180300400500c40c0c1d0920050051070f0b0081e1040540311404228072400c0e84c00c08c440141c1c00220380243d0b079079202c03840400300b4506c91140e0503002d0088815008501f45070405248000c00569809022410f0703a00051500300720a0036203080d4072403100c03141c0800c91200c239501414090100d0225004c1d4102d01c0b0400c0103040c000d00e1482000111401d09000303541c2c0c0c4d01030340e6100c40c4e085100d07803041c00c00d44200750f00c500c01d07500420141010b454021032013000308100c107030664240c020791000100086042c052240e06c0300c0650b008245402a03410441c5c10517401400e00b10205204000c20032a00307450aa8081902d83c09082c10000480d5078041255405080d01c0401400100060b6503000103120708091030256000480400d2940c1d64003039180e03035034603510410740d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 948426294 1250 948425044 948425057
    0x1b0d02030a033605030c0d030519061a0904060830040b250c03120905060c06040f0201180603020a08070518040221040605040302010c050403120c06110d05041b0303 72
    0xf0803806444080d4071a07100300201ca1800c03078810565400c04502003144000603848405028200340c0e20061942d070b405030700c42c04201c440e2906119813549000000321108548020488440942d5a6449600101020815a5000707150311070250a030320f88041200c44520700150003003200ca9000403d55054820304052039181c03443c2c000121441d400c84024489030320000e4074188000480904102008510a4404181200795480054600300071900464011039050040001900000420b150400c0d0171110328640e00003d400100c600c41200c824030f10a12012a100040b62980742e402080f4a503440d81e20030f801d03034032890740440b103a100300e50042c801c2c1d002985040d00782d440c00342e00501d005071504c20040410042c7c00c40b40841c0400032075081d901c041c0e4500800c4145031302801095040c40e076500d4003901e451b08590740c04000d20414008001007100c208111020061181d2025015112003034031141c480d62881003400c06800d040710300f00c800000c80e103140456600c1c3c1252000a0f60341c50385815 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 948427544 1250 948426294 948426371
    0x10f050a02210106050427360206180a0506030915060105161101030b04090503031608040206031603090f050c0102070f14360109140606070303021b0d02030a03 70
    0x44482c491347e0780c80040b20040c00280040002d500c0c031074568050481801440ba09070f030403a00e04600744502844254110b10800c840f8016500c6804071440c610042d860784c1241e00d580030106542071500d400142c0c1001000051003003503a80000d17544419640100a04800c0d9191001180d150041260802d07061200d0b40c900700029000e0310460101c8030b81890001a0102200005026100d0408044c0c0707054000005104801410f50007581015129003001003203400c1560102c0c08612000307043e000356501407001f1400b800d03c207411100400d500f00059400c071880d0b5040c0f140d125044800054058410300000080041c038074440c06007182d00d10095011910491002d1000b844008103d180864000070300036004c101c8284680f06410310441001e214130b60600701c4100884800c00d46000d9034004a8081180301e52f40c5000b203811f840e034946409600d901801a00c2c900381101c08005010070700504640c0c080559000010b440588241c0d60305109211103006402c40910f5410440c0c44032002d070442c1c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 948428794 1250 948427544 948427559
    0xd0c0312050601020f10061a13120615030c051c120f050d0501030b0f1803271e030d03150314121602180601020c01030b03010f050a022101060504 64
    0x280b9441101130058500403030107450041d04120000c004200c216a4516040c04a190420300042d03d40384460394203407901311481c450714050042481202c07402440511540f003045065005200100e961040f140c6c40d0382e840346040d47c250340950141c24042d0030380318002d41c0115204070310100780716000400c048082c52440001c5030000140c000c0c400c28080f0402c4060200400e03889814002c50007031002e52918108145002480d2801030000b9000b0321418010440c021004800c0b6900000080d5900420001d003140050400c0400708400f0785c000c2000300340c1503081c40070440d010a801c1c004c406444407180101d034140e0032100c0c400100041e84c2c0314000280009a040070301805a07201d50012a0061882403d08d140b4a50060080e201d80c40700c561010310860405151212078040c40f61011045450301c0c20000756280c0c2808004c030704040d1500010b020545003035100b50007102c1a0310040c0140e20301800d990020350701c52001110001408000d140d4401040c0c4003203816500265076003890103180124 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 948430044 1250 948428794 948428801
    0x32603040f081b100c09050a0807090c0905030a05010605031011090d02040e07030f11100f140903030a03150e0402010818010f091b080715050d060f0b07050d0c0312 72
    0x400318800803070080801c80d0380c1d03410001d2903810010014042542101d015006181b0002581701d0b0303005e0700c10468140f04a4001103004d4040d184007820004500d090010216910f0034a2341c072032509802120102c4060003070640091090303400a800b224961140d011041084070503a6220b01c0c501070003803045a4652802030220a10703180018800302c0c1031488007034402d003000029030003200c40f284460b49100801c88824008468210125400c0d907040091100140c407c3c500100c0003020440d0140c2900c0f1310321000025030351620006011a5251901060044d00502c0c5071100c1d05440c090141c000075180403100e1f41c541c4150b6040c0d54a00642d11811080c09400c42d0840d81c0400e01d548526080031303d5041882103010150048607204100d411904103d1602050751300400710390341040c2800e0108002103007009094010501c1e0503651440d400603844c00404054000c8034150300482000580b500481010f01202400340007a0744800c00384403016070700b1800304a401404604902c50f49015080795a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 948431294 1250 948430044 948430057
    0x11b020708031e040e1003110405060a05010c020a0314011410081f1407120e0c01140918070203042420151f0e010e060603090313032603040f08 63
    0x103c2d40c81c102600d4280380e419030b81c1d0498655003020341c403007070410074862050b10294071610155400c02850a084011602c0c0302c00600a89042c001d100004908548541084c44015078100d48511241210400090f002e000f00030605190391440c030000c16030284001502c00700326030401d1700034100c80401c1200030b1002803a14500c0000b07540d0318817201c004c0759841402203104e0a8155101c03030805d1500042001220b4801841c596103500005109000741d801076444080da0412005003138407400c00c440004d41130600001c0d0b29080c481c564003130001950b000000b0704240d80020b4182c2c010040005070450019600e990307044005403c002c020847c0e0301030482643c0140d880c5005590458100c8095040410019a00b842c0d503902d4011410a480d1201c001120190080c424078440a51401d04509860000580618854000080401e03003a00f020011a20145c1c5009201c0c40a00d640341011001c031134a98062800842200c3c03121031101e5a01c0c81201d2045900a03042040501036840b05a00c82e003154 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 948432544 1250 948431294 948431347
    0x50109050f0d0320030d0204150503060a091d0f0a0c050d0c09050c0903190b060d08180102150c0a030507080108100b150f0c0d031407050c0109080408011b02070803 72
    0x340307134401500c3c0705000800814400050150b5210318045800d80d9071048000701c00100030050040c07200603901da20442c4120364032802c0124482000800f600420b070062403608289102d444035041c038405001c100c0800f1a401a012000d1641c1d8a80604c002c007920944001c0840001c0d607801c1c4041c80c900d902081d00b0003404885141000440c0b00070030b1070440002119031700403000c5d00e4808100706488224a0b4418801da408049140d4503580380102c50044228408a020768442d425000d80d108104011001ca00500218102c1c01c0a0f41c980c202e592160420b540000d042c940010100c6c1d00135102c06040700c4100c2c0080100d4184202c2c3d580003452840140b981c0000c030f0154104842d042100540303059032740c2c1d0601c03584e0761410f06d04180c900030040d0100750030f040c03d08000600c21140680801c1d4400d030503081460343d90144c0300085005210301c3c6002803115138080340114003400158022089810250168003850006c40300030f0740d685c4c0e401e20031220307075500800c0050b5114009402c841c0e81d42014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 948433794 1250 948432544 948432587
    0x12051207181205101a0a06270f03030305090118030e040e0d032304020d020607080d05040609151b120e0714010f2a03020a02100306050109050f0d03 65
    0x1242c507010105a0681c5059407a50b10201c0c40011822042c82122249134103042c001c1002c80115000ca04900703882d1185c08180034540324200252890355204012201d00080c00d0fa0740c4507180c01c402c860081aa000903000245418002600d0503070503c98480b2400325a880b003005444541c3e41102c00204130070055400544620340e14140e800100a40d44000c8210b440110303050301280841c1900c40090348000d03241900703013020304c805a100c41e540c0019090b0165025551480181064540b61049501b04032119190030104030034810310b940900d40c03c034807452050311420718025410040d00c02403141009500e2400e10900000c5001d981142c0441d07030300c4c1101162180c05001d041e410071701c1076440b50704056150040709204e076a001d0164441c908049c00c180b15541d1829500c442c101aa03170001c20600500c00c00c2c030005040c020000d91103a1507000301201c00c0d80c074400304028040e2055204450108412440c04544d500d8005039081c4690b5004c0d10300c108003102d9440480d81840042c1840c18000071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 948435044 1250 948433794 948433799
    0x9040b03100f06080f2103130f050c18060102060109150801050c03161812140a0f15020403031e09080f0f1e0c1216121205120718 57
    0x40758011440c08482040300010054035020740241090814008000c05400c442c00501d1580008203645452020307122040f600d95903128944940c0359001d40004c0c0070b240342012044108507001404d03129a60090320105030030107468076040082801507816078003503000700c40107016610380ca80c8101c40007054000002100b80d0743e4040c0c0c2d8210340040d100c1e460710480000c2080040380b01c0040c4d890340d0221520f8665a43e071010070580d0346140c50741c080c484d180e0044020201c240701c20400c487c030400300034800341c5079078503018649100b10500d240e004075141220002a424000f086100340d80c12240c0503200d100440854655a50702c11000a0100c1c0c180095408081031030300040000c880310351140e40081840c4181000613a1821580c011a04245007017020840c44552001c030701400c0017041554082400381741d2006082c100044000c10300901c020304400001c00030154001480b10314051511024076400700700c0100c1d0b4500c900c0c0007801c0f07110135001c045000306104090114050403c0c440075005180c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 948436294 1250 948435044 948435073
    0x40f0209150301090c0f2718020a030e07080a0201030e101103090c100c080715150306050604020301060525061107021807120f090f06060608100b09040b03 68
    0x208011500e0a00580c04401484291034034440d4150380812030400a00f03145400038001d00f00702c400102c0a40b0402e0011070b000f10110340300480c4016200f44c030806508c00340c60760017041c025000300da184d07400213090240c807242003603001c81c844081c0c0f490035000e80342400c0c0b5600150050009a03030a0041c1d8820f0606134011000315110b507008504070050b00d190349060080042d450011140340d030350302ca09289240c0c2e00180e90012a0031940d00e80c4441c5039511203000b418265800321003801504641410b05002042d1100300e910000305481c403642040009884100a0001b240002d000d81404204104211020402d58009e03802c08151024600d05842d5181d5441005449004010010090000c6500411860070580b0030024055152105810f0b103003e139001800b0003980a41054a40e95074000d0028440941e007019442c9500700403070f10380500c0e072440d15400030038180c41603400041019011911007000c42148034100c0300000c2c411424010b5071400c100007000d202091030b515200b0340c0e43c5d454406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 948437544 1250 948436294 948436309
    0xf01020301080a140d17070e042d050603060604182a1d0a320a11030c09040b040204031b080c060f03011205120408070603060b070201020a02040f0209 66
    0x80031502c0207410f07110902d03e8071a080403009507410035203030020b032052592150b029009041c0300218140e032480300e4580f24415100e40d03c400d20345540250400400d200f1188244815405c800204940307036001108054400701100d20540741c076035050b0030840210700c50346003507005460301081c260300d9400d1040040d5980041c1d0100040c00c0b5820f0101c8000e80010071104070030010040250502c5014420b40d021200c0b18003d40060481450507502c486480c40e009901900440c9189420711815002c40d250070412900b1008684e10b40541e418059005814019103007640c0c02121600241806c0c035081c10100f0020302280c00002e90401d500f84400001324035514451811482002c1c000e03018182030400450500b2064010b05000f100c08002202001c0140c2045a04403500310103003405441c4145042e509100d00c40b55141c80d0700c0004580400c4001000c107140c0c0c04c8507000d4804001255a032201010103014202010380983c000010480160030550481105612203c900504d0840e85100007602c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 948438794 1250 948437544 948437549
    0x504060c0f0c0b01170124290702040e120a081f060c0807051519050a020a05120c070f03020f06100e0103030e01120221060a03020a1a070c0303080718140607050f01020301 75
    0x1f0000c2590308100e510201001c1c0e00c1030700c4030040542008803400c51580ca0620548100a004036a078518200e01c0c83c1003070002015514132143c402e9505c5681c000b00411243c0c0035540d403072a0b40c40c07003000040b225405d81c1d410360465040303032640001c0c1e00507611441416040301c003054030903005a041c98014903980100081c80758402c00b00303850100800705c00e000101c400051490102510411641000c550482c0c140c1d016003d0300d25440c0c3c40c541e201e2080c04c426002e8400d00030f205501107200c0070101138001c2075490310040000111102da80d04e001d81606490350700c0c4502e01c1e581e24040d0041c00806d100300500c109014060400c01c04050424106000300c2e4402112403040340400107090f00c0051410f45002c0e0001d41c2204d44400440c29900000c031402c1c0b443c070808500c4421600c1101801c0c4085094039440c0340c0000094000503903a05014040c2c410440342d00001038142c8000b8101c000d500c0201d9804d03610314100500e401001c0e1424403d442e800100e007661540704a41c0c002d0150142400218003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 948440044 1250 948438794 948438851
    0x7060903030206070201411e100b0a0c031b050105093a170a150806041518050f0717030403030c030c0c0503010504060c0f0c0b011701 59
    0x11400d145040090920901806120031a41001050100100a68001080010590041c00c44805990304102c074074200c1d010111215540ca07020400010314a40000800542802203001603503145544030041c0e2016005000c460710b010300201c5410341c0b084540048103446420107100110071480c2e4184030742c9034410200c440341c4d112410808044000e12082e00240e2409000150440e0a0040c18042051400f1000c0c00748138400c8021003124491402500d20590001c055040342c1031020708400a448509101e0040c20b4031048001405500011401c0c03290760001510320320801002c40b2a0b024001e1000c0354540340411400100c00300d042400802d040030743c00c9004100407031810017030a8800d01c100c510b005868000340402c1010075000b00c9000c03050340d491700e443c1c0090415868508904140ca402c110742641c030b000c4c2000200000c03039008031003482d1203440f00307003000720010740465018801901c020080d00c80c00004200c8000c01e1110f20344280e0049002180200322030b0b40100c6504160050a031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 948441294 1250 948440044 948440057
    0x20604241811010207060e0a05040c02030f0304050304080d052803021e0d050906070c060e100c030903021b0a14033301061706010809010f020c0d0905121207030309050706 75
    0xc2d00c941c0c04000e284004c02040c10904002c499007000aa0403c0840c45030900032502c403030101000b24401c3c0b044400901080038030366102d0610b400d01d95982d800501440e19240f10f8500e54420081c01070040d07480c82d901a0000c3c25a41d04641c0506892080c0c01d9000028140c082c040d0707001c07000070281e000503201402c644264940649000000a551014003060380c0354001a00344180594000d540d088000d0b0003040105004505145092070708900c0c00c3e1a0384190719040e1902021641034010550540c0a54201e034400016000101d25040c0f8200c01260300c45007000c010004000c8504440005010085c15201410344012110152481107642d11405001e90180c3c20445142d584055000d88400d10340310309074165030f641101541a000d0480750600c088000000c50070300094001da03440d4150030030259200c070f02d808080e40d520300405a021010481c1c00c40f0124190400e05054102290000020507062965030011b80a03a031185106404054840c3c0c10320001c20300400026004202c5681c440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 948442544 1250 948441294 948441323
    0x1207091e0b0603040b0c13030f150f0b0604050f0d080c0726100b06160602040513090f03050f1b0309090901050f073504120206042418 59
    0xd0045550801415100d06800d20030301001c43c0b0020049540080000582699800c3e42406d021070602c456200a2402241c414002c1c20000f400010a8281001c641c0a020003084070700d040080d6040404410380005080c803040002d0b160403000032420f203c0261050255074000e450b072460a40c4950401c0344158042d403802c2102c07148101280501020402694400b00003c0c140d40b501c2c0d041081100b81e5107070b182c5010710301d60b0350b0b60b600701e4005c082800a5141034009515050021b03410511585105402d22450040800c0050060fc03c0c10396000c40300c0031f014803007540c05840d96000303092140158401403203248001c0412407400000e0420200040d91202c03220400c2180c48400102141c032564184000e00031208018140160002a40e0916803240a920302000c13280101515440800d4000840b00741c030301100c48010070b8000d9001b040314042d40751070f4080c141d070f84201c141c034018401a503110203c80402084440099007820400d00402c0d1960010401c40040355911402d990300c0c460701d80c0c1d8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 948443794 1250 948442544 948442601
    0x2130f06091b080c0d0b0a15030b040b150f280815150909331002032a10020a02060f10141201270c0b031302120709 51
    0x40d01410b0000d0b2619400510304208a0b0400d8000c2240101400d034441c1d1441c0b601da560054444060031141944c1d503030700c115401d001000740901e5560076004602d00703400c441443c20241c0400c420480101503c901d400a105942c0300380e40d02150040e1800f1514089940c10000c61581c68030240b402c55407028698280039080b0a22448400000b511456018200140300c0c50742d40d007a00c0510030211800101076640c0c0b2295803d580748203c40c0d01c0d682c0f070014100c0300b00307041c400010080201c0980e806044040e12103416a075a125000507034044610010310802c0d41c65801004a2515001034261100070140c8030b102c6059800ca0740950000d40c00050030424541142800b003644031a1341c0b811041110710300700c200501e02544404550140b11903071a000c0a840c001d4000d03003040d8000324041082003441c20f030081c101c200300c01c01c101c85c03110f286080069070150703100503a0300491100044030b05008040d801c11241c42c04543c1036030030602881a000a21400511842100d602d111100d5112500202c51 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 948445044 1250 948443794 948443831
    0x180f03090105031005212a0907090513090c050306100e09030403021519030605010509011214010801020a1206030506011401031407080106030c05030c03060409140d0509010306080604050a02130f0609 87
    0x48280d4002d5080e0403d141060251f0488011f50409070b44030541a120001c040341d05640c5a044141c0228140b255015203005a50100410500035001151001c2d01c0b001019129641542d01c80d010b810400c405004102d018603502da0400c3c1c0030412645441d0341c0740e0210b40d0f410940b210300041e074880450407a105113600d41c8003c9c0b80004501d420400d81d400c210000c0d01c00d0107619089410481c021641400c2c907152075107c100d0001c44940c03295141c0d1f07520600c49000c1d612181d214800684a40300003c0000c040d0300440b0144c9034080040d14540c1c2c2840b07003154a0b0b00581c6503d50426465000030a00e07070081040319401030486039650b180540c10880017400340c5030040300f804100101001003152800c0e0100c1920307041a801c03100403828040da802c203c601074040d114510703c075003d10340c5c030036400300e1b044002072800341c00a032028000c16544d1212141c0f41d44040b40d014120350807441d034510051512080b0390050784c46006000440d1807c00310031a084401c0d9400020819030340d050b079103400440d05203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 948446294 1250 948445044 948445063
    0xf030307030c08132a0b04090b01110705060d0216110a0506040806010e070c0c0b0a1e05031303020f0a11090a0b0a060e04061805180f0309010503100521 67
    0xc103141e41342080005042e0030600304030301500c04101c0c00e0181c0c2c001c4484682003c4e2000b14082d00c401c010f5100c800e2139056070302030302c18006002d151006004241d4007405040101802c2c00d4041c06847d4503080520086501215043c40702c5582080964030303500c4c41c1640b044a003030068100b14824201241802255501034000c6441103d00340300405c9240d40000c0c1d07980c1501c11040f500d4002d91a02181541d0f0805c0404006108641c0c520021070020009000f07816401400d65804200c0e21442403e5502c500c0150709034000280c2c10030002c1c102030511030410b910036109104807900029111001414111070140031a0701414034420940549880410244c008810020422943c1800030005689041520a031410300000110590b82641c465010030001d100780b040f9020041d049010040040904071070000d0451440306d94180103500001d405421509010021484d0070b08100055071241c000801505028003000c0c80421240c6403404182e66007086241140007162001c0c1c070540c00c220110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 948447544 1250 948446294 948446297
    0xf0605090a02030721021c0807050f010c0e0d030f11070602012c0c0d03110706050a030c08011505090319122007030204020a1116090b0a0b03270f030307030c 69
    0x101240c0b010040d007451741041c00c642c1103400c22600c0c203941344038002d00e07404500042d140c4000441e0400c2448008226a108c2e0307176840c0300030004400c10700c1c0c0584165010307020039a000b01240921708002405040c11030210056410002041c04a0100c150300c2d00c1040e41056006035110941107005003921460030344540440c1c04090000d102540c00a80d03200510a9844e2017a22206907400603d40950200ca401c1c4031044192114692a00009026036000d403000400292418400030780c15445800030b1816581080882c07020200b00010407240340d0020114240d2602620f04014802c1181000300711800b84520341e520f4460074441d07000343c151004c1d1035003813652810342d09910400c50004a02841a43c4d4111401600c4008040b005c480320310180b2900000c0b031081c0440d0102d14042007142d4021114030060034454504181c00740448030400d4800c00c1070190092020032103a0107200c1141c2001c00b001600d908032600410552854614019001c100641000041c071120560500031001c10707191a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 948448794 1250 948447544 948447569
    0x21201020d18020d0f0212190c05030d090b130f0f0303030b120d120905011401230d080a1412010f05060301030f021003060b0f04090506030d0f03090f0605090a020307 73
    0x85401081030b03103011400c0244109200d021000031503032046940010031414004a90704049040002114103178421010b03192700c1428200000d16250014580744800b9482d5125031600d4500301002150b508010b040542614030071310b003c00c80d140c001d6000e400420306402510082c42c9507080203403c030703090074010700d000705640c1d002404101400981d40c20b080c42c03286020043c02c030200991200034481c00c48002c00c25402d20202c514502218006076050310800203440520b4084c02c440d00c0d501c40e8800032001e4000d00270250440200d0903810181240e2030080c1001010b01100e0380020100e58014122411403801d445c005000c0c050701c450202010308400d40c0c40d140b0710350640c2c40354520704800c210002e02c074180c84d400f2071145a10030780004004201104d0f2147d2509038849069520f40c1007409100c03040c81c42e050014003640303800200002010003030f0721a01c00184250404034007806610a00f903036101c04886962000600600c5128802c20000d03000d0480a216031041604050095100b841800071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 948450044 1250 948448794 948448841
    0x2120a0b030c0a180f0c08180601230a1e14040903050d0209040b040f0905010506030a0201050301030813181d0a02010e04091401182105030708090307021201020d 71
    0x48005114041d40c07032492042c50381c0c4a01d040b04401800178010001440c40c10042d4401c03900d43c1000c9014040c10062034115506030f031500e8100d81d01e03d000d00c40e102c628001e401c1c0d04201d840a07502440c0300110041e017015500c5854180c074844030300d10505100b0101032501c034108058040a4600c0e0001542110140111a15610010200c0c0240e10000490b254006024046d0340d855038428986900054003d20000c40751906010044c100c240c8241c4440d428880040c440c2c1c64085801700302c65038140c5980e8216421500c580e01d5541103c2200c004448540d80081380071188e03074036040c0110a00c1c10000c240320888640060300c40300301c106500c8896000c080340b0300041c0e8100f40340410081d81a00c00040002260411025250f501d0074014000e500c0e042e00c1c680640d400e640913040301402005011202103140f040b2841140c2940c5285000680a00101e07a105101d400b4450f0880c02203000c60f41420700781e4002500a50080014800342d039400654261000e03814005c01e82c48051103002040b41c50b1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 948451294 1250 948450044 948450049
    0x7030e040e34060807020a050d081e010803040b030c07061b271703090a030b182b110d082403030d0e120304050303040203122701050d02120a0b030c 65
    0x1502c600654092111600005401038800c000750f0a542d604003048640400c8500070203852448151840c44903000c40455102066003c2e21046040b502207000640c60103103401310180c44d03600058010042110100030040118426002c1c0110f035490a1075403080c440f00504001e4101e0481d2040d20001d6110180c045040f07a8a22400302c007100c8400401080c4440e80e403004c142184a02c01c3d189900500d134820100c28000705030812845401000d03142001c1b40f0202d140310f5503518440759803103015418101e960591f000082a01a940e04c02d6040603071181840e11091030500303240b0400400010318502c03c004a00c4420030401c0c04407581542d584084510240100f5124443c0f05024402d003038a4404c203441c000c408000c00c06409a0740d900302910390409242c00b68985d401510113070b06c2403146540c070485441112080300d2030084d0719914111010300340901100344a120302d00300d80c10311800b4030402401c0012400101b106112041c184116890003201c06030481d00080c9009001b03500c070fa14a40d0058 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 948452544 1250 948451294 948451393
    0x1060e0d021207180f020c06071d040f0902010e010906050d0203101716060302130e0703090b0c0a08010f0b3c181203090607030e040e 59
    0x4080540324111111210300201d00c01d104442100001e41c81410030000d40566000c940040141540405001c000d0b60300d51248141d008007907142210f40c00440205e031a4a008e030101004548244107017400da005107100280417160366150204c045600c0300100c3d000c41d80d101a40d0409040309027000c0341000e0400c2001000c1c0c4c000e5600e40451260300001282c0210401c0441030010034010009800100c00801010f03122880c4004103052924420f10100d80e4a011340203891a42d42220384049401d407400318074803c0c0c5103003d0301c070405065032200c2c080c000c2122414605d21032801310342050744d24080c0f441c2c020503421059124503a8076240200a004040340e280440d50303d001180d00340480d0000c4010f15500c650b4504108a5400b0000c807030091200e41554090244140c160000c0e04e44400e410050150b8144290030340401904100410b809500d01a0041d010381400303464902840090880131a0480d42045820755441d130007400b15005030301d00a00c0040c0d050318043c0000c80c800c0044132060b55039 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 948453794 1250 948452544 948452567
    0xb04051e0907031211030909090c0310060e0c0a030f09111201020319052701050703050c160201030e0c0406030b01080c1203184b0105032202030a060204050907080106 73
    0x108201c100c0c8050b1017401c1003003a202d44000c002c0c000802030170682c0341e055885114940300c5001e03010b055103008000410b840b4407002c40b07006243c82d5034a540c88440c0c48646d40c0c80440303018141a03507030300091510010f51140c1c00085104400380300c0c5d02001c41003086401120b203086480903a00400400c4001409402c2c803041044c112000420070740c0310460f0120345900c2c3d01d0581e440b40c0e807202846100e40300c01504814042c8245440070070042e250740c08080f066104401100300c0303440c105c4454034010b500ca68003410300c401c0d511043c0e408045821300003c0544080d58020b803034428440e00107000140c400e0201240b0b0700320458980020011902c501c1d91203004401880c514040c5d0510346244907100c600d610048074401490514010805002c100800003181a00410100c0d0100e0310110341e0240000000c8901c405840f100d09543c1c0d6555110400310541720140f01600848003440d00688041103031a481c03600c61900540c0380c41c02c00050250281c2c00800003000c04c441503004101460700140c11230b55 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 948455044 1250 948453794 948453797
    0x1407030203190204020c03190306060c0221011b030902030721080a1205090f070506040515160804030b01060f0804080403120309021011060108010525030b04051e09070312 75
    0x90a0900005000b401048000001ba020001e62940012144410b2508401c3d164030304000c0261540400c94840c000d4042c001c3d007041030301c195030b041c0e8106417404a80d60341001e000440c001d603404400401503006003001c1c1c00440d4458103003408500d0300303100340d602800001104122005d4041131182e084c1005100107008418001581044c50b8071070b90a03085500006082031146041c1001342a584464040f0000954007850030302084502c0c01500b210200c0380700414080341010400c03040d410550041090001c0d503814000e402c0d000861100241c00110b019200b07041c0c2d550b162100c09041c00340e60b80d1400040040c007408001c0060422429282620b81120300021131900001d07068004112000d0301a40c40000b4402c903c80c982d50240c3c0c0c980381e0185c91010741e101640d1b688010360a03500c094841e503e044c01c4203110800500d12211440500603098034002c038004840c100810201c035401d451215445016400c00c01036040100890790b00811441c2c001c0c4107140c0740d91a642c80490a500d500d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 948456294 1250 948455044 948455083
    0x70f0e090c210a02310c021213030c0b0a020709020903030703050705100e010b1815040c2102030a0c17012105070b0d0510060c02090a0603050303131407030203 70
    0xe0b01a04100c0c0d5071076994040c101c01e010f80b031030340f5904c000e8145004a088008401c4090004000454095900c010241da0001c0424100344804c0160a4004a00c41a2254100034000004c25000c80e040c04c0141402000d2a58038021064000d0510356070303410002151740108608405514000300312840a0b0701071802548403842841e0080c00c184030700c00d1180b400c1d41000c881c91012207040d400030a2411048407100703072103101149602400a41190a01d10800076480000c1807820715030003500100e551450004405034911529a482070740e000030712413480b070f80030041014035042c52103509001440b40c200103041341400206101014414058540052844c52242d00503030240380d0702d00507440d0f2040c103460043d43c8860025581e60800000c03845081c0c1020081a1080c5030000404103584035030751103070841c4810307800b40b0140502c06040d80422a42d2003800001054051000c1c41c001e5800300c0c40212101c4490603d41c6000d40390440c500e8407038001441c02c2006a030000341040c04500c02c6204c02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 948457544 1250 948456294 948456349
    0x103030903060f1b030c030b0d0308150622050a1d1515040306050a0b0a0f06030203040305070b01030b070f020303160810051215091603080306040608070f0e090c 71
    0x41e0f000d8115100b003d1060820795002c556000d070140c21508024049039000c0007000303103450800c18181e00455014012a101901185045000e4243c54030505809072001d4a4a402c1000311700b9803082c2c604104560f0080340320240701038603050b00c41070010500c200e103210020100300204550349102600e0701c03014540580b84d0103482c0d100e1003440703154030002c6503509446642d02e0600030080d1000300e8400c04206e20703142030680d00340707498643d20096440e009c0601c641d1a0030510b05030b0096002078419030a0003414030581001070009078034613019602c41c41400e00a801e00d010081d004c00d40e2560a1400d40d00248200800880c1c5410a240a00c0c40d62034104103644800c26000241e001301d4111540040c082030100450480014a40c440700004001244582c2c0d1005410f5032540c030a001104440007500004002050100000e1504004024000101c042d5943c291525022090340710354644805100304214104410250b50b43c40440ca0004d000d07240004c40004c0c0c100e4022800b03d001c4080e00d01d510 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 948458794 1250 948457544 948457571
    0x60f06210b0a08031e0a050a26160215090c04092120150103060203060f0d11040e03031317073c02010914060d0501091a09010303090306 60
    0xd80360201a0502c05a19164030780b00d616503010100d11064900701c1c64108003030b021000220b6000824a035159420581071000480d403007060580c0d03100d544921500d25003514012005018015044800d03200841c081c2014042d00b00744a902c4400b1100561400b00605003c0101d441c16076590304843c00a1001640e141c000f2103000c1140c00c403622140d03190000e00c02580c00210121101c42d0841032440d005a001e484540c1c1c44803131034960b500408400e80100300054140d0055a00810010b015204441240d0045900c2405060701950000802c1e08003540341d0a01d4807031001041c07900005035107103113001c20508240e1640f20300c000305240102112600006402802e0741c004d00d90001015064200c4802c160031003040443c0780d1007080c41c101d0340083e903001940b030f00150b001303506840e000e29542c034003104401d01c0f41d2000303c402d40255003003200050701a13031032180502a1200c000000b915448071303400300d1030300c1d0080e50b0080d0080029400500110342c103d20210300b260f030f00160108180c13548807103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 948460044 1250 948458794 948458801
    0x1080f0c040b030a050103020f090405032505030a0e1311160602070206071406070f210e0d0201050f06090c043b0a0f0203010b0a0c0f0206040612060f0621 68
    0xb2200ca2208040140300c5915082d41155040b40e000320351003610003100034100040508141c0f0002e280381d20801084034800b8005903200c210031051140d8a00c5051103451b040e065503c00806800001e203c0c07142d0038420b103000803d0055001a85004201501301c07801e41c0d9070310384541c040310046410112101020045250100d0b0545039014202c03030f854490302e2802da00c2450b03001e241a803170b9008207000211024807174140070200101c02c3d581c401d14164010b040c01c1c08100f07580210100e99071aa052180c060390200911030a000e03083d0f0000965140c08811001c410801429031407040b046003007803014007030050702503030103440c06540380c1242d03005da01881c0c2d400340760803810032600c011780b1b074990401d540000d414091003500030003000e05c400c00c40700d14a0300c02c0780310901500344055000c0c0b0078288480d01c644203030040b41d0320800f016080c04005800041c42c030f1b0800d500c5880003464405034003181090700d015190090030404500050103080c4035020b8418441c0c80d081000303040a000320f0b00981400b640 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 948461294 1250 948460044 948460049
    0xf07050f0a050a0f060f031a090603160f0509130c06120905011a12010624030609140105130c1409190303270b121b030c0703080a0b01080f0c04 63
    0x500c1504480d54810031350342c0c11340e020b1040401046440040325103d50090140e80440b4a004101005000703104c0e0401c84c40c0f40300544081e0305485500e9100c03900700d8030400d81e01d01034208450100700d903510706020010700e10801001e0713005819411412000007a903020a00b41076807124180b02000e501281017020041010140c06042507007401d003002c17942e0300341c1c104290800c0301c25525092100142202a03003030b05d010b0700c96a034030500e4200500c440380e19441c5080e10746182a2070701150701c554a0715000d0030f03200c485e40d04140d00110f44004000500c0c0050402d4850b462545051199041005020340002a00d406031944000002140300d0682d40340000150200505a0091303540e54807400c00405030080203411901940e100007c1105d04618084c1d00310031162030100390742c64442c159540c3d43e00307440302515210710342c41c0100300c46a17822003001c0a1441440c0c8014166101e6200c2e041c02003152001030065000c1501c3c010302c4c100c0d2079034880b550551100e40098020080d490340f10050209100b04c0e03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 948462544 1250 948461294 948461299
    0x51e12121b121e090a030f14071211070e130201111006140303121f0503061501020607030203060d030c02010e0406062012191704050114090f07050f0a05 67
    0x207a07030001c0580b1022454059034912034400c1c50002400840091014141c8420079658041602800043d1255820000f1940c07189800f42650898000340c3e0100c5c1c2203140c04441e0498840350b00b140059101010701c1030480da070340051041c0c9150502400381084090301c80b17451a41c1c05400301040d07902039040074410540d8403003218034035045004da03240149250700400103560300d881c034900d000d0703c1c2c000280c03411039044140d415440c1c1c4500410507150100e01a129800c0550010001110307038003071080900c500c0c3c5a10040200c0c0725802c000900f803000013007035001030510601c2809000d49440c0c48124040c0c2e41410501d00b88000b41c00140da00300030030301030030f0390142c10f22a01044c019403045440c01100789044840810010607100c0b2500ca10740500c105181a01c1403183c504c004862030b0892943c0300050401c98100d60381c182d207540441108946c2510784d691540f0007500c0903400641c0159001e802030002e04282800c80350040d48840e52449020f108545514030500580c0d02c2c616250001c1100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 948463794 1250 948462544 948462547
    0x15060e030c100f030614100509210a110117060f0d080a0201091e05030f130e0f06090709240e0604060c03140304020108040f110409051e12121b 63
    0x220b060042151004480d518006420140006a42c2a441681d0740b140c1c24001c2c000005c14011040c1220340d500303c4990550301001485905501c0a28503202200b4a00d1440140c11699801d00f084241c01c0d02400c5050f04100201003801d6050032a540305603004001101e808181001000c00a02d000011400c06465008000303600706050f40c05510003c1400d11407010510801ea0300e56141003070751408000a480c40c1c004200754070301500800c00a024009001c1d03003803803807152525040a100d603c00c9903800360070900c09060020074507082c920264000c03000e20f41894010300704402036880085281d0300403902c140503541021400d00a0450104a1101030640740d142c0c2da8480c4000c240c0f160014049c1c0214162507041e100301100c140840b8427694041c0c64440750350702c072591100d02c8a070310000c080c2c40d0a50144100b0007996507601500d0103c03400b0b54000c010302403503600e004601820b180182141030b40440c0c54a800072440d5030950306845140072491000e981e81d0409061032541103154006541d40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 948465044 1250 948463794 948463819
    0x240b12150118140109050d0b0a09080d05040807060b1905150918010e010b030702071a07021e030c0618042f03070e0a080a0605101a090906030115060e030c 68
    0x38540c114401c654240e8036990500d554000788019150040c002600c180b034450005082c9c00c4543c1c0104040f0b921509459103800785002d81b83c006c94000781c0b011107003814001607200602645009190030008103c46d010001c5508020401c0d074916144202c0c0c0c010360315054401c4952130317400107a40107600d000d03160101044412030110f035280790134011030440040d80c0b0008039000c02d20a09480c800c40d00c640040c080c4904203da4222003900f030360250035150008101c0840107885886000f41c0501c1e040303110309040c0030b0140c1014107180241001c540510400d0109640300408100142880a4107460003d82c01c4884107400700f611900c0036449000340c2c498401891640c40c4080158400c01341941c80d10b10302943d030010808102860312803038805501002e40c001c040340d52a40800c0d0440054a0b070301850303d54411803a40b221503c07011019480b8804106014a41003020401e0780c8200c04400800c80c1d104030070344515844084e400389804000d0709a8044030503442c10881c41c0000d90b401080c41c001c06a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 948466294 1250 948465044 948465059
    0x50609160b0c06162703020315010305190c0306020f0d0c030209130506040b030105041a0601030504030c06020a11060901020c073512030c07060b0d02090106140d240b12150118 77
    0x105d02d803208a00030b02c81d0140d00c40c203040b50182c00364162944940039041c0c6c80c801c0c1c054080c030f81040490507608100303072510020000d1058801400c1c0c0758130010302c060b192000c81074a01c04690f45102c03001d0506004014241071540e5090f00d81c05c601c2814080058280c46403030104005000ca040c40503019803a040920040c8500c3e4502c686011300b202e0040c184640d035a070011016a20150780080c0441d0800040344c0000f032081e00035000300780381850210810f18a00d03e0b0189840030036034000105035400580c0c80f10800c001d00168000d03107240c0e94807042a0958159100c140d001f0821070503910100a401e004000b82c003070113808583d00182c0c0710144ca07800c2c58141c014082d48904021180640350060504803810000c10201c1e1841c0c00400c2d20586170310701001038440d00d83d10001182e101c030041011048010441c031600c58078140c0480c3c4030204c400300c56503520040840b504900010300c0217200e60f50094001a1036182d01c02c020060301d440c0d080d00c82c0010b032618030798598240308245800c00c022a00740f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 948467544 1250 948466294 948466367
    0x305060414150403080a0f11030108011a030304051507080a030501051003050601021209010212070b0f01231e09090606041b091203020a050609160b0c0616 68
    0x3103009904038200101686901580d4100180c48020303260314800c00079001c40d001d08080ca0b807001a140d0b02186044210400c1d00480301c4503078103204e02041c0070006000f0903a003482884a020520580e81d1a40c0310301038006980c0f805903204241c820180004804000c10000041e1414641d200c0c22302a201c0921040250143c00c0900881c1c0c041c119010b61000424800d0007054002c4406801030411030405000c0c070000e5a0000300410f0641c8214804c0c1c96507024031400a0004d07601803003d906550070000c20904090301c0681c0701500d5200b8024140344440780c8102c0401c5171407001c4130040701c20b50040500c3c00400d00c61700059070740f10307603003408100900d080441c0c0305108900032242017003d00203400118142010310b60006002a00460041c483c51511080345d60455000c0e00486c4c2481106641c5c0b20300e0031070202d414000e140c10612054134403400000d402c2001e044241110390070700e205140103507a110801007000c030541200c021904070303580c003d0480c3c040342102005808003200307403207200d80301c1d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 948468794 1250 948467544 948467551
    0x150c0d020109020f0a0506030a0f0608030d090b060d030f031a040c030c080106081509040215071208061c0b2505120f1521070608090d0914100513030506 67
    0x2c48024050305104d140105d0080e040e43d000501741429900c0e44003d8900410a40c2210005195200340200e1206420400b411440c8015003010407100007500d485100c605020f40384c27500545108503c0c0340007a4002b2807841507801c50b4a0002510000068202c0d54000302000003508240f40000307800030503506802c080c8880c4a2900e500d100c0e41d90707a00c4105d500b0b010488002913520400681c0790503e28048003da41c0142c001011480a085103070034407560f0f82d2010104a400103803005046180c030ba00304400d82c0e070011080320320106c1d07809040481c101f146100700f170003010720005400054040030340b4204012000d1280740b07984240654503901400c01d030b001400020b940d40c2a44005540070b42c0150384584102e160881c000c0848401364207110425401c840c02c3c4442c6001005402121041040030700700520b00c966480312241082944036090148100040d01005210507042c80f141018403580041c1c1101603414000504400d03800311094094000100414080582c00005100001501601 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 948470044 1250 948468794 948468799
    0xf06090f0506030f070c02152808010902070f080d020405030709060302100309050a050a03050301181a010f14220b031312140d05100f031113110c06010905060d050705150c0d02010902 80
    0x480381049c20440c00501c800b150200001c602303000600c00341040350054403d9a215004480c2c210150341e80d1a00c0c139420091001e071405602203810001498108143c60040c412102d0030051241580c0105080b80d44001c0d2100600d0380301e908840070070004014144aa6401105484068003180340003412036101380b02d070107440320382d13000d080011490b00d1160701c8282c0b00803152494503d074940f005603621610715a95405220413189a01200c074010740040000d40400804086003e550000140f1001c50640049074074110500030880d011b0359015081c2652a0013200c0180c012030890030480d040386880210045c8030350003090520785000701c3c1d00b00f0340c09260001e0341c43e010141c0342c2000650b031510034400601701c3c81d20552446941d050400d8020101c0c0701030340020a01d840c078405003881c140d109928a102d198000c00040210681902c40d182c0c2000c0c0407a0b84040340407450f120203a40d40054010b052184c82e840030821320300140c1800700c074510401103054814a03180c07540d01038001c00240000b80e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 948471294 1250 948470044 948470077
    0x806150417060a151d09280303230f0a1b110d0f0207031202160b09011d0a0e06121e19080316020f06010f06090f0506030f070c0215 58
    0x41048440e030313085805440740040403040e040075030006560006000340c101c01c0700b80100011100301aa915102940103c208248a4440d0849241c014111100c520090485403103001c0450942043c00035070680049a90700c0c902210780702c1c1c5281c4001002d4080c260510010403a6003088580e030001000ca5041c07070b14a094580311000c8240c2510300068660015005030072040003130000800754450040110744920444e0200741c44010a0904000a43c102480e0000d010850340411340c6c0c003c8400483c9141611552801c09501f400b06080f44018054840509540000915107882d01c0e4038071131100c0401800c40b00c0071011851340411801c9490049000f034000c041b6405034041c011101c1105943d0300c845820324583c2e91401c544948010101040d086000700024850aa0400c200c1c40e03001e44109510180c0280c941040502003031055401840c80c003488100400940d580c04040c1e960014105010008561b5031040440d1040b42c00d110080d44408010802105403441c6805031164004207030451 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 948472544 1250 948471294 948471311
    0x1030b010201060b16052a01120603050a0c080c01032705030f031501110f060609130c061d03160e07090905090303040605070e0f060a0210021b0c0901060806150417060a 74
    0x41d101f000d407c0490721079085500d0582c840e194480d015030b90700740c204040002a2aa01e07036070344905000b145a8251a41d140d107c0c41404040001e20030000503107001d0904000e001d0303281e0150f440d02410011010340d2240003031400801d1002c144102e811b011802c03000c80365a03103060411041e60700c1210341c105001a45540c40c140d08a400062500045141c0000801155491604110b2840c0004103060b01d45601d144150307001446401c0c10b0320140c21552600691900c05030400901d0100d41c20b41c080c031a40c0528080080d264000712040192500a000506103940301d00c01074400d00110392003001458138000c20001085404805103000341c0c8200c030140125100c0441c00c0fa05943d500c03050740e500268001e00c0c4481880d00b9001042d4039400d0740103079640e03c0100010841260400d814503108131070740d054035030140d80050050060028007141c0300362581d410080010480d00c4000c12840c01008404485100c0e00460400c2d1001485880d181ca00e6482203203403881d8a410054075030721a414103000c100c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 948473794 1250 948472544 948472573
    0x303160305010f120f030c141506060432031903030c030905031c0e010e0c090f250210050901021b0f0d03020d0603060615080703020406080601030b010201060b1605 72
    0x3030116610245000042460707503d8100c040c0d13194100440a00c47c0301840c0100065500e0401c04450020310050000b9817540c405148020300c00801152003404200818090b101003000542822502104080010070f880e03200d140c0310820b00150907a051086007038250901803290403001d21103100e40d030280701e40f40c01190240c0640e000303402d0007000c6400511240400100c10151400c00118607000450750080c1d01e00307420300f100c00440d01c03400c032078109441c2d0034484e0030b2500c80242c01882c2103814080d245056a100e2000101c0156000905c10840750140c5440b80b0800108200d00e074403c1d0308100d40e040c2005114003e52040304202c2c03a401e901d440b00c03c0d40000110368401d194240c1c0c40600403062103240110025800103d001b000c00d50796110210114013203100396006800303002183712100c00203a1014100b868010100320030140108001d0040035400b07842a42c20410030300700440d030f100206006070b01610031a0000c0500c100c0124800d4103405010104000b138500880c291510b0f01d400941 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 948475044 1250 948473794 948473819
    0xf06020c0316050103051302120a051908090d050307050d270e060d02150a030c080a2a0c051605010e041116020a0b0a03020d180f1211030316030501 65
    0x10038a04400e02c4010822407540a85c0090354050724003c0700601000403640012407003101c007200c0450960000064404105041082a1101c00c401c10101d50440d01603035200c00078850a085580600c081003440700c10400d00300151520594044159020000448402841e0300074668102c6078400d02d00a00108128032318072000c0075680621881003907135880c1c0007400748901c0100800c98006007100314090399410700d900904205211517502140c004800640100a59406401d41e006d07030b03103002c0310405983c9400d810f0301d2038a004100005c90322090840140c2c0d5080701350304040c10078040c501d108451080420618401e03150240c0700c4519424800f4240000c5070000d00b0a0401408200041d1a0300302d0360100102d04a032008200080c5181c80b100801155008240800c0110341c020411150400803401409403082c180d040203c004030f0543c6030040641e812070000381c60000e1000d8007010390342c414646030345913a490104499a900301080520601800740d040480024580304c00480c00030202d20 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 948476294 1250 948475044 948475063
    0x4141e0d0912150b0607020d200603130609061113050909150a0504020f1c0c050f100f030f060f090e010501080307080c01270605010e01120b090c09010f06020c03 71
    0xd98910441e035070f00462000806200d0161588584248450001130b036a40c115001c0b031302d1050171407201d030003480703802c810102c0e44500c2240e00c50382080c000c03c00443e000d070304420030a64014801103562200b505182009203d11403c01da4000800900d00d1722000c00d0700a988103c54090320000c52580d40c2086503512007003a880451640c504010100c8c901da9190b41100e900709000400b800c00101e1180000713140118040c2c17200c2448949540b4441c14000380d80c2c000b4004000036100404a50003a1001900c200307110400007081c89852403091075024400d5124586045c0118820050380742c03070710000066a030092154100141c240058180382d0b20060207010304a0f2900001927052038100c1e40c540c51640c0002e449100310303650300d01c075803054a07800ac180510150403658a2185203651818058203848050700030b8034001008c1401044540c0c0b007130b07800d0000c0d160064020401d54440c450070905140100c004c441d880f211980011560300e0191203140700303d42040c2c088034001045401416291003002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 948477544 1250 948476294 948476303
    0xb0307020a1b090e07080607020102070b010312030608100b04111201030b1e0a0603020f011806030e10060b120a05011a0c0c0a0308210f04141e0d0912 66
    0x41c4110000030780002c0e80c41c28401100c2c8800841c564455644074115400d5074100c040c990300c204010401c0c09401e02005800c42ca140c030080d0324000300e5840c0c0c080e10241c188001000340c107041590f0050b551080d27100340050000401a40e0701e8038058140c482c0034010b01e83e07259118910b0244122014001d200440d458070049021601441e8a16204c40d02c0502004040f03900c0d0034040c0c1e0400a81d03924503149144581c1200000040160031401130103041540c10301882e0510039503070042d0201400c0b0303000c0300d8100d80091902164140079680f078207003070141c2e225100200764204000801d1404000d4082e012640303640402280c181d6442400d90700b41c500030300c16040030303200c1c840801041ca91307100002c010010b0316004890351240301902041c0e000000e64001e803070000b400b1544007110303507044100325084001420380e1070300350030710303540c103210902b40600b0080c040029596001d40c204002d04c41c42200c60f080c00c1d200a0802040e1500c030341c070340c080c1c40011b0000506592001c541416081c1420b5200d5410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 948478794 1250 948477544 948477553
    0x807120b0403201504111909020a090302060d230403080406020f0c1603030f21150506041e05011d01030b0103200415080405030d0b0a121a010b030702 66
    0x65803010b42d8003203d90b089035440c41e4000a0b1001d200c0400b003119004c0e88210000c5225a4980703414002440300b41c0c0c0f4070003446001c842c2188100b40102207800010713035001c4c0000583e581c4502c0c0c401e58000890790b10080d0480070224111454016543c050200803205000052400e10b03141012281244200c0b002404108401e000c20049155a40509110602000340c80d16114100c07030094a0403106c3d680445640300044401c0c001c05511000c0c429892026042180100c10341c04c01d40740c600301201d8032a99950303a4500c216002c40d5900c2c58644000e04004c0d10b40341c0d5a03515152955541c9098000e040c504e0490310f030000800d54803070b40c0180b00c40c9090780031260007010329500440142032000b45550402da100d07400050756010500d00c4042e58212400b81658a0b031410014000022442c08070b4824030003020b04000100784040200c40450a00e03c500050348001d0a00060000310250030900c3c0b140e2000c0b83d41e008001c550340484a819890f6501680341c0d03030341c80f459180030344421204d0b030300103030003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 948480044 1250 948478794 948478801
    0x10e06040306090611030901020c0c01020c030703031103071208240603060405041a0a09060506030601080d05030a060b03040c18110f0a0507050a06050105090c03060a031101031d03040807120b 84
    0xb698840341e40144126004920800345036228295074100b62101691769600103100400960304200d80071042e42c1c20f0010303100f007800900020b51141e134103110150521150340c01c1c0111103203044c030488001d9503200565802409400500902800f400c8590b1088a2801500710030100d0207008909000c8400800492550350341c00c090001400002e44102c5412501810000d191341c42212118881c8040710b00029014000341410000d54001a0029000c0d030407245c0140442039000c243c0c04500e8201c0d0810070b683c0c0c0c80f81c154160041c03080307504c902c0f0b00034804001e002c01c1014000d540d008842001c48a40f4043c04d5190000044804003500a10003180c104800098443c081d009041080700c1410502c1c109855515560705000d0801d008440c080e5455006002d60b1400703030b036015001402c10300c2c0c090131407601c40c01140000d00207010290645d0f038650400780c2503030710a81000e00c01d0070310840f20304241c200c000702450b0f80303070050b0064202d240240400030a00ca061030307040c1e0084030313000f044002e45500d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 948481294 1250 948480044 948480053
    0x70501052a01050a06090902030d030c231207020c0306181f0203060301061d0a0531050f0d0203092701030c03020f01210c020c04060e01050906010e060403 68
    0x41c003031102810803125010319001021042004003040031036a5001264616001c204002182c20300d41007413000520306200d00c80940c50000d0702c07080c018600c1c00c00040004800c001901c03802101e195900f9508800700001900e049400042c100824891107075543e59220002e06984850b170082210760143d01c480c0000d01c1081040451440710ba058405440c440440e801084401c089020443e2a8081d000401e104150900b44244801004c0d84a013000d0755448440240072804005422400413603112400706030f42800304135500b81c25407014510010720644940030581001c0919100380d0f03441c0501c000c04410840c002c50402e00c241c1059019504d00b880315010005420340c0c034160042041c003a44450b0005558500340c0318065801745103807807980f0380b171481002a1005480102410130186100000c00c0780300103081d01220b4581514080350f0034201400480c5400c000c00d15059209042c0940007800f18604490039041e03440c19200c0c1c003c5685c1d42c000559911190302c0c00c442d0001c208101c10400705 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 948482544 1250 948481294 948481297
    0x219061d0d020130020301050a0f050904170d05041101080f070c0f150213080d02010c1d01020a020301052d0c070b100906090e010f090503041403240708011707050105 73
    0x80005007130021204a081c800c3c0072a5002c601d20300c51040d4004014840b0303107082c440000091461400f118660b500b03101c041064260081e000404034a60700302d8100c528084035050301d030742136070085003002249800c2c1000b044500fa4010b8080c0403070000400f040034980c180d08107500c40e0340141ca5814920361250b0300c5600780c10780100140c1c1c81c40d0580d00e6034070341d060b01c2d40010b0004204900034603454500b4215401c0c2003000300c4882a003503a240c5030800340886d81040c0d1a080245140030424015180d03580107034103004035403100079419464101000503117840001001014003020515a41e450710000094a203610160740c4001d001c1c034203012040c00944100203090f4880c3d02e200c00700c2e240507960001c40090b50500d400c8907400700d03210f48801609010910a1004a81c40503c09000313817907898403003d480340b095008001a440100d40070b00460340b810051b84161034607051040d20469640c80c5240c0e215030f801c0d2002000151f00c840006803643e10b40c0100084800d9003006082113515140040d5160b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 948483794 1250 948482544 948482567
    0x3063303030a0e0a1a07120801060e0d08190503190203091c11060403020102030a0c230c030417010b100f0504090b0d05060a051812030615070219061d0d0201 69
    0x401504007020840c85c65204004d0290325180506903202d80c1607140c600300400194440c0010043d0800041004035400342c55000940d405441d5048090f03110f041071062485251a80392030710a40c508404400c9500600035481140b0f0601140e505104610500e002d91000341d0b290702e4664001c1d044010051688403c10840140d0790030841c820608000065060000c02c540c190f0250354080100183d00126004003161101140f41010344000d80903900102089807c8200d4825000856151004c070420403c840140000700481d0464040c94101103020786a51408140602858051044554021000003031000c10640720715041c2400c012228004100700c0903450307401001d441900380400e40c2031000c00e0059000110201d070074988840201c801c12140300000c0003d900c01c00c3d1150310f00c07400710141d81e0012011611284640605010201720380141c200195002181d030348001e41001c0500c2902c4100c500e9a19000310040c50146640e0040b903080404d0ba170414442c0a40304015889440714500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 948485044 1250 948483794 948483799
    0x60b090d08090a030b011401020d0306051f02070515131202010c0b06040f0507050306031509032b2f04050603040605040201111020031b030702030903063303030a0e 72
    0x40f8540d60303280d12910180070303400741c02d21500343d40b0207002e035503414402400340ba0040e0030306008451901012429401c074401c401404c1702c4207d042c0c810103038828410407004000c01014505038403078010228a0030b40c4824017040040d0344080002034025489003203c0e00c80d039016111000c90609948a615620b07200400380c07648940c0c0e5100000002805101c0e250003809103541c0d06440e840c040080c94900070902005100607440c40040080e002000011500c440d00d00616014200b040340c82062014a00e811052000c6400d0201c0c4041c403d05072a80300603000d0008072444514000d2241d9141948128001d00da040601000040c0200c9d4281c1c00003a0800d1042c50b041703c1c0304150111042c180300ca0407606000d030545500c200f454258070b4030040030344244640c20840c40c60404c11007100a041c40203900c2d8030a01000310029400c54001d00c00d40320390b114013409031201c41ca82449141c002c2641190303002c0b515400098280400030311039006a0740d042015005510303260001310213031180200100c0e003e5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 948486294 1250 948485044 948485059
    0x1a1209250e1e06010f02030c0303010e011508041e0618050312070c03140c151609140a060c020307090f0203010504050a0e1b060d060801060503010b120718060b03090f01060b090d0809 80
    0x1008c80c5000c02c0194000e00a0b00003035080d039418180695000300c041400361040049280070b1002240515038241e200d825098601801c4600c98a0000060542506006540c00c038081140050040100040070080e0407000380d00048e5807001d0060341c810011410180c005040f00c030548002d290f414006143d040c401c0000c850400c01c0040d010b1001d031401b210644a6404c0702c84a4040050304004180e010308010340c003500e442012203001c60b503c07080a00c00c00081140b2154030340291f4038140f1070b09018204068085c400880d590001c107004e0b5101313100e03150140f80744ca030000381c200849200e08241d0001e440054858403100c0002c3c0c080400e0003001450b0f1002007040020310840d0103110702401407140e00c00106006181004150071100145071300350285081042050545401050807020b80342505035114140621050385402042c5941014450b035000009002040000161070100c08080301c00a114060721007820408078051303e0720b1a5001072540c10b0800000d600c510240c11103920180104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 948487544 1250 948486294 948486307
    0x307030b06090a0228090501020a17030c1c02120c040308181201020a08090d141204030e1c0c0512030421050105100f1a1209250e1e06010f0203 63
    0x200c405003005d00c1603110b000d102050031180a03080106040104824005441003940c151680c6000d000b00c86103a02c0e2012001000800c1c850b200c505070741c0500506070704c0c8203500341101c1041c4001d40c022141e11110300040b0b00010750410910003120140c0b41e02085250910500c4d820980c0044070360300d100d583c0032008200c2903100b010b00340301605d4052400d564040b55414139980d001e08214000300220108407041d5807a481c0620210202d642c041040850b4421990300d0b82001c03038290011041e50f55200701496200540c80070180e8903216a00d004500105401e070740c680411210290040c0c03441c1c42a0411700c003c011100f042502144c540b000e0024040014605075606400c441c0111284201c501c03013002c0502c945140512040b0140107099010b00c410380c9a010040d526000e41890158032801480018035810000c0c003410b0540c0c5824054440710901d0180784c0041d00031540501d80300a9035110003d50302c0c041c2101c210746102c40c07040110445031100001160241d11443e500410b5100c200200c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 948488794 1250 948487544 948487567
    0x4020409121701080313050603070c1a07080a05160315050d1a10050a090f1d1e1c08041a15040b01050909220c12020f0307030b06090a02 60
    0xa01c0d400c00c54070768500c0c4001180700020903032a034040e000b40306554000d110401800031050094425604215201031716aa59002e08030380000c00490f00400728600c1106c20795180c00d0741c51085006014a4847d10990b40d01c03020018102c400480d00310070001ca003d007a1071049402079000d101c640c1000c800c5580c42a450b00085403c40300c0707402d012034282c0b0000b421010031044d80044039402500550070a000140382000241d8100300e10f0045100c1c0c580e80c0d0760328401c0f429440c0d000515034600c40500461828040d0205622401e1014141210f10f10801045070902c0001c00e400a120040300d440c0d03c00240d11100407214404018412201c0115019500181c00121940107100d101c9074004d03d5400119501408262100d1034851410f0001c18403a00e4034566813110580d80c0300ca9100b8410008400000c2075180c0c103a050328000d06000380d40100410140c01c01c0c070b9103403426802926403c406c0900d0f1424036548031307a42e110282240d0a0840801d5161600541c050b41022415101504200c1d92201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 948490044 1250 948488794 948488813
    0x9020a0c0813050102120712080c0433141e0f040f140909192105090f18040b07090f0e040606090608030a050906071e050105090a02060901050304020409 67
    0x11a04201940d4402c10852580d0421031400040031032040603040040558810031a05a1001c919050011070070010701c1d01200da00c243e0300140303075846046015404006544103540c070381090550207030940280d200c10305401009001000c0040c10004c62904007100d1004081203020702d0050103086041001e0460240c0138405840606460240010024501190040500860294a4020a080020004040300c04901c0850140c10101e42d60404c402d07034500105540c09440104018a207060f94049038968000007070400700300242c9210100e0030f030460411004e19010307144440d10304240d00006000a00110303c29400141506007500c03441c0d00c80107400c00150f40ca808c41118214204e0030003060100c0da0081e20f000b4246650700300000740c20043d640303882e4451080128184000020300362900e803103040c125a1035076000640d581101070050310b460311480c00c0820950b115801d0001180c8546c002081490b511756005265515001060303005503466040100280e07400b690751075024022400307041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 948491294 1250 948490044 948490057
    0x607050c2806050c030a0b37090c230405061603030f020d14070908060705090109181b090501021b0f09040305030a1a100311040801020c1608010507080109020a0c08 72
    0x41c04161680b8104088a046440d4041d0387c17031040c2c280c88146101419440c84500001c03025814505400c0a00044030005102550040c3c1c40319180c400782c2d84806030300810a0700c604000c4215401d00d50a0702c141e010702405603008065102c0020403081d425a640f1100085c1c5240c420704011030181d41a062440480c1c00c004200300f00103413104603229054403407042341035000105040408000e4105403101ea540c010003042807082c807000003241d0034580e0060200500514444100d002c0ca00166144180a440300c5030495020424205036031100c180640304920555406078000d118841c4d1703440b11500034182c4201d241b40c200841d0341403298592104070256219500076103e10740e9034207022031b8540468610814041000c0e002c05d0400c2d0003990355a80c42c2d10160950f1902080491041c0000700b0103208aa2100240b5032001841c40d00c10b00b008161010b00366040800218001d51310480a07080c0d80c0308550080c0094110702c014490b4603036070380c0600f000890616002520601c01da450761136692140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 948492544 1250 948491294 948491311
    0x9020a02160608070e180c18090103051509030f0a030c0c0615031104060b040302040c030605030d02150a050f0406090602040816080709061a07060b06040b0c0607050c280605 76
    0x11000c0081c082d4025442500e0128256182d01c01106101000b0b0303410318000d402c10308107c40000301300f444d210b80d801440a2812004111100d20b59481c1f600c1943c0741202c1f89041c0e410054040007039401103000c0280d035000280c06411a2501000c0403084009088038000103090004100220020640308d10550341c094500280c1100d40d24114142040041420042c540c0700d40d0905406112031201001a42c088036410703034012902c00503081c42a009000240c2290350903204e181c1c0804c84951b40060624107100c802c88140c6d840d0f80304c4502a0040d80c0e412a02e40304005660804200040c40640c4969503c50042c3d50041c1065101c18065083c0200b02044040b2503000c80f80074080301741c0c14010038004100009003008064501001c82204042c003c04800c143d010102d00642400b6080e042070240c94001000555181d2310798000c203c0b0350704080e84000082c030071000001d41c0725000b20111040d4522100007003840608408a4a91100c0000c0300002c0c188441c1c2c405100164440c0900c50140c80030b03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 948493794 1250 948492544 948492557
    0x150a0b0301050603120f0304080f1c0f02070f030c0c08010c0504090612020d171e0304030f09050307050d060f0905030c1011030a0c0e0d0303020316090f09020a021606 73
    0x48200301425100c0c041d00a40c880d03000310194a24408031841154903003201d28a015840c1d9480f820200d40c1801046d058400183d03002840c0003c021900120140c06503401e0001c01c821084000c40004a00810030014807454402e200c0301c02107406408a040318a128026010040d92030720070907401d65214080780d20100d0008641801a5030050190002030030200345110005809600062004003503884050849401c01001d80418058042169012520048115020342a4145010481c1d00441d01940002e0340d008150780c2c040e104072050b000722400100180340c411306180030000e005d506108200c4072550345401c1d1240d109100d0041c00701e940d001d1405540c0b40c1103101100c906042c41c007031380000814138284040354a100710742d0a03260054421180000c81c4c120080c01565450403984040e503018040110b003c00301a815002188160411000c0200e101c0e0b42039001c1d070340d01d2614040d1070412006044203125006066014241e44a02c070700c101c9225138802b901600c3d030310146070041400070f0030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 948495044 1250 948493794 948493811
    0xb0919080d0f1715012003212703040504110306150c0a030309060902181b0c06150d08040815010b040303051b010209060c031b0114041103150a 63
    0x800191800080360a400c200c4400d00c2188498030320f80200605500c90751101040800b4a64070948503415091850303031308880455058001d15507207400c43c45e11004410b2841610034460340c00080f0300d9014130040c03c400c402c6c500302035440510a07204051001c285110a000010340342d40c0350b011700110a06044505c0d070b52410480d050188010f407110241300005001c00100b44006000a401003140d1340502d0000303800740880c41c05802500c40b1000182d805440850701c9400851800c0074107004107110b019039068554152110402c0d402000c031344c42c0c001e8010000280003180061840d482082d0300504146c071240403960380e100300d070300a42c00c0001d00d6031181c006401e8000d882c440090241c2f0606001320708003851580d00404a02c205820000140440c0c801007828001c250180c8820700c40060869803078413000100d199a94004242c0c0e1111007620044043e803905061041101d000020704e01e141f03169541e5124409100b17040c00c83c05406104101071881c8151a0490060040100f02c00c041415074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 948496294 1250 948495044 948495047
    0x1d04140a210318031b0b0a0b100311070f060204120510060f030b041b21020901090b060306091509040804050f09101503020f0409020c0601090608070b0919080d 70
    0xa00d20040030070b0500e400440b20380e580c0c15001c410145941450410203001c00c0c907800104181c1d40c050f00805100e0900c0c28004e07112200c1d04041c0310402c0c26240c3c2c2400901203030003101625200c1558a08000040041c2004120320303c1f104882d050045078054940360381c580b45080504c062030000d494542024030b4828645202d40a50401409500303030002005041d502e039030300711110152009002c407c440310b01040701d510b0321007801c005201d0481d401c0c5c1016003e112141100c54082000c910942d00d0800205120380c80d403003840043d01018160350f0131550380d8414000c4450001d000d85400c440c82d82e0708036105944480074244100e200d00740c81d5484924100911608800d4524928031526042003000310781098036104030b08840c02240164012a9000c0050b40244039040c0e110041510000e0702003458005a0002c00a030b40000f8200c4e01e20360380ea25440d03000c448040c002c40d0850f4110303040030030482c000c0710041d04403c0c000810105c46140204001c9148040380d03801010540c0080d4070200f03500303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 948497544 1250 948496294 948496343
    0x18090c1a0304150203040b071d030609070f0b0c0d0c03050c1906060b0304121803020d0b070f020d020c0114040504050901050a1a0d060e150901060f0504061d04140a 72
    0x820f800d0075401c500703281c0c1d01c01110050041001040200038590300a654500200a40c0c040c48003500380c0341c4904007a8041512002239000780f000d1925515000144c894040c1c0803034901689041c0a031041d85202d8100b21104e00f96107030306400304503040c03040c0346404806211102d40704c10b0542c034501500b922854070b401075811f00e5001490303041c0b00344104000701e01c101d080c1c00b1140b001032400f01c0303414244440010750815a0381000e03400a0980c43e41c041003202180406005102eaa00d03040e8050220b20400c03030b81d4030a101849001030b04441103075405075019071005038049060400c07050400b600c44021404940040381c1e00c0035aa91a401800456842d5102d9202034454803605030070300c0c4610401040084100440007010995903c02c01038480400340a524000b40d0303094150042c0d41032443c0b41d14040c140b54025000010100340001a80c0d203810f00c505001c448500c035040500d0f50310b02c001144041c80051003138856400100141c0c10242080c0b01d408000c034801c0c11002d0260b4000540260701 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 948498794 1250 948497544 948497573
    0x1207092303030304020d050f0d03020306030f1f05040c170309010e09070e1912140706080105153a0f05131707150501170718090c1a0304 60
    0x84040d4416040c426072004400c49a02940542e021098898070303141440c81e06c07040c59940c4a8502030350b28a4202e49a06070021360046c4011000c5070380b02d210b144d8801740c4a4212800c0c105140c100d14122484100345a04090f40c0203000d1103800c0e080c0d030360700c00c500190015512820040f0b03800000e042c01040d0b801c0655420140420746001c0d40340c0c548988003620710745c10b501180340300d01c50307100d56440c6000b440ca414070003800c00084e04114001042c548194048802d40c040d121328002e042001c9615407042da41c10741220002000119640c03103010702403003581d01c0100e009100829a10440c800c022220b00008040c00f648205100101e0581b0141d90071123034051410006c2500303140c18400c008c400405411240c0c1e800c04206044960000e4044080f803180360002000803081e0180310014000c1948814103c0b2003094149031405914640a9219001402101483c044001c5243e0f6023111a6002c1c0440a01c1444c1da165201e031121000c224034912240080d11014002080000300714041044034807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 948500044 1250 948498794 948498839
    0x1401090e0111040b0d0b06070317010e130f031701082a0607060e2a13020c0616020a0501050c031006021b0910031202060f060109060c0803070203120709 67
    0x10488030741da0b405000b403085120f51900c1240204903444181c5140d40001c41e01480184015581e050702d20f409841c42c00c030480308201000c80c80000103040b010300100c2920642d0040645000402c0e10b5403040c0d40864072841c1602003000f40d24140500c0416560864081c24001c0010725200c040b214040036021141400150108a1001003d00b15107601d0152100280d21400c04912156414240751070071a182e243d9581509080900aa01a8844806481b0700d00b0039100412000c0c001c54080341a0700c80c601901e0b20a40c4540300191820342203c5840038114054030640d04e040744103482c2c0b80d0941d44251141036103071400000f80424800392a00001c01031843e80050701444019400d90307081d02c00d1240250780103201c14400078202c440e00c5c80800015680c05240c449000ba1542c80c001d40c0e0301c0e01200c2400e100c00009010512031340c0904c401c00b080b108203544440200d04a580c91408c02d0700f01600840c103502c410302c0320407810b91040c0f100f02d22800441d5600c2c072071945031642030901148400c04004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 948501294 1250 948500044 948500051
    0x509060703140609070e27010909080706110903010905032802060115020109020a060309030f0305160309060b0a170613031709070b0301230303030609010302130207061401090e01 78
    0x14100c030300b6016140e8801c0d02112140416a07540c1810b80b010740c6044400d507440381c10f61980400b121003403400100119000c2c03042d5101a030701c07003106030211402403402070100342041c403418000881942006030030a81a50f6040d05081845006c07d0940f00e2400b000c032010742021401780d01140106039206691260910200307900c1e000108043d413550f2040c061985400d9031024006d16140c000d4110242166000c0c0180700380c0b0b43c4d14240140201a16101100040c545241f080036840c4203000d41c034000d1184820070109100c1000c829002400b50410440e00c142e22602103004030360b80c1d00700e40001400e5145601e0420032120a10074105040200210030002c000340446c0f02080d03004003600d44240c03421440070f040b40ca4402186207004000c1d0301004103810008004503003c21064901c00503810703000104055140d610b01015181d00080300c0c0c03550040c0880004002624295004040382c1540200041ca458050740f80d103019944030b50010402c203c400c600400429245205004480d95188000c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 948502544 1250 948501294 948501311
    0x2040f06050603270a0b07021504110105071b1509080f030409110c010e010b0307050a0e061027061b05060f2809110901060504060507081b010509060703 67
    0x621607000181c41c605900b003002c0c010510148034605440c407801d91100c101c07605e44a451514441e400c17411518600140591140418080103030841d40d8001c40e070210b01c040368402408011150384d000721606482c0c0c5403104c2d02241500c2555054a8060301c911179404200701d04072207010f8076990055101c5075040e407120b444d203e49001c000c02681c09035402d002c8041950b61080120044e180910120b1080c2541381229007512620b0550001d42d50768001d41c15210803d40d04c40810448512900c41e00c807081c5550340019505140800b20840070507118204281003c140c5205a2115030b0840c40e5070040f01900e007001d02c0f0b0103410131716481300e00208181800e030021540e56582d07251070003e003240c2c0c01c880511002c05d0481c008444d0144805200d08404040302004c17002407000b4101c0640161440b0085c1d0214440c06d0500d0f81d08241070315001d440e541d1400e840c108007200c6075030080c0c9050b1045c007000d2000c030803204025035585078525410310010440f401d120511718100407014040c8001c2c103180c01c520307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 948503794 1250 948502544 948502549
    0x1030e1623090c0d0e06150f0d02061201090615140a0c20030105010b03041109090c040c0e1305091e0a060216061d07060e120f070806150108150a08011802040f0605 72
    0x7c20380c1d00e100580d10003480c2e600e4040414005c04501030001c1d071011010461484421445120034102c82c031000090040c80d98541e540131012080301c0d81031001501c01185a507580000d000200b45a00d081c6c9081c00090b9000c0d01c82d0780c0d05030030401c03480e506406045141251440d003401850702400400c2112840e500345562104898800301c02118091100030000034440d0800340038001801c0c101602c1404400c280e60070086c003242c144490740f4412003410024681c01116840741c180308042100c0140301006803505400890030001485100b640f144200d54000104a400a00302d4450800c1c2c240740407610600d00501503400f80002c48014404400c41c0c90b10300300001804908071007040c2000300414a601c0003081c50742a00889020a92140400107405180c001980c0b01c1250b540c0c405035811502c601e00304540f007021142e040e50010340e8440200d07185060281d11110003001c010424520303250b48140d07032802e649900c40d0011207075007101d640303005609080c02501c1100a0120041011b10f050400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 948505044 1250 948503794 948503821
    0x406140310140d080d1508010b0303090d080c2d120d0c050f07050c030d0503100b031e0907050a120209040308220b0601030e1623090c0d0e06 62
    0x10340c19511a82d5010004103481d403030351075510b880c0c00c00d19140c0c2d40c10405500b5000340411070780c0031010600807180060021810302c50701d407800390010050342c44c00000004101601907510000c1c0c1e4a890300b0003004a0100c0200001d410030ac04050011501000011421625100e4246242c2d440d03000b03403801580202c554411510142142e620010b144030705244215030034000c00070502c6099200050040034050002440d4000500c00c8080701c110142d01203003212180801d4801031b4a010102c24140409580c040107580d000121000c424450300c0c3c51582e40068000680300000c0d9a00404002c0c0700318180160741c00040c00c0d428031400b00d5450150b01182c0021002000a81004441004030340e20030014050074001c610807110020310300032030b804c1a11700f40c501a2000b0380840d140c086121082d03803021403055200e01404070011245d074500b04403c40e2611161202e03080d440c01c2c1700c3d040f405640d6400815402070507181e1007103441d6160141c1c0c0c80200e4030f8000c49c2810742d91003030701000f201840c03020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 948506294 1250 948505044 948505049
    0x16090803130f382a010c091202060a030905100e06090312061e0a0303050a26280603030818010608030a05071a0403081015141812030406140310 63
    0x18010b8011801d6885044542c05002400a083d03040140703003021480d0191007030b844d07810441008011008007080d060300c0c400741a02c601c0045040300d0402c8030162410308080c02c00a82182401702d0000b00c80d580700d500303220f070903480144107980c0c80190060070401084000c0c0e000c1c818800941c134140b101c02c410344680306c004208034420301c2000c0c003d621100c0350480c41000c1050180911311425100c3c030700500a0b030481c448000003c0c500505000e15100c07000b5080000748101b40321038a582e02e03803100e050083c0d002c50300503000c01c1e600d40c0e42c401400011ba108100055010b42e880540b54240035903031a03449403500180720031507030501c0b9091011290100842d039600c95203013030043e510a61450103401000c8040b50600c0c6082201d4204000d050308000103a11419400902e80d1101741c0780c81c1150b110391500780d1420000343c00d01c2c070500c0d0300b540f5600c010102c40c41c0984d20b101c03400c3e24003400a81805600701544020340c00c04142008601d07001100c0303100b000781280d5498114641142103104c0c2c03c03403a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 948507544 1250 948506294 948506369
    0x1140c0d0b13020307050c120a0e011d06030702010905010e010b01140a020a0816050f0111090f1309060c080f040f020103050a1e150b090916090803130f 67
    0x1440c80310303000d507100081900d0b04804204250344034a0800c4000c1c0058005145c2c41c400c5014420004a41042001c11910303200144d8407050702e1030b15541c2c01190000402c1410310301000303d41c049484142d95a0010314881c3c0095030010410801504d4444d007500d00341ea1400361540e04209001032540e8100350b0702000400510103558446203285030032172410f16550b1000c0c0c908200000e08040d040701c0e000815500d00e000340102c8141d0b0944070b804500b00d84015460464a40c4180030b00e04946c90910b0303801e80d040d90020b081c43c110403242d602c0e000032260000c80460fa055903808400341d0040c3c01180c89a446148a0a40c507007e182a488054030482e0004009041603528400140d030003100d5480104200310a5100d03800903000d5060800041001107100926a10007480020380c070640101254460306015088214a49a50052030800390040050b2001e11a0300c100114a049040020b0700494101c3c40060301902d181c03da20b2520002d0030b8001490210b020542165840d405100f19440104d8a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 948508794 1250 948507544 948507551
    0xe0a05031b0d0b0411180f0109150504020f030403090b03070813230d020628091a04061a01030c02060414071502070806071e080712020409050901140c0d 67
    0x14200011811119402c000b001810203c0c180810f020210360f100001340c1066802d40c121400c810203104440030101c601162030001d01c0010b000000b0319403c200020b20840034040701c650b0b01d03000020180d0304280e422003105000481000705066012102200504495000c44c2c0b5508261070028294600100410700d403032050030510040050500c1d0044d8456000b039040207043ca040401103490345050320390b250040c40350740c01185d50005001014010100110f1180c0b00c485915803040d401703007074441406d4644510405010040442d051030b06071040780701d4000000d400c2d06006103a0082811119828101841e01070703009940b42d0002400741c2c01640100000310000f01c034250b511301d051800d8200c40303d1480e03198000d024041d0001880b00c00d072a0203034140c9201e6a2500000c907a4021155a441d4101744020359418640e4090400b0640001071b07450904000645905a80c003aa401a444030350100c0d0342d582000440c407020720036429040c0c85001503110504020b1301c080518000c403065040741c15503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 948510044 1250 948508794 948508843
    0x80a05100f060206160e031504020402070b0c0c010f021603031e0c021e0d020d1101140412030f0c0e101704061b0807021e0c031b010e0a0503 62
    0x40085034038014141242440780c07141e1244002500e034a419a41584083c00503d90b21140c5401215102c05241000c0e00410400c198603407046490708014009070b030000c0e82001381c0008070340c556039094072803418001c03c9959018240e40c59400c41c0c9540c02c3c40c1d1039043c03043c0600c2c03a03e80200034440300d145416240103d0307030440651120701a042c40903d0000c4551510b014242d10a0700421a11444005a200b6000482d0302d0496262a211150142401604500a614a081d0144c2c10151524019500014020307079108294004081c054405a8a45040031001d140c030690600038080380d28150701c41800050701c50300000d020310412145692041c6804042d582c4001c1c46241508041201c1c81c0b0400c0745810542040001807400c006105201d12840400720001801003520900401c031650090035085490154022044d440f840301048902a0458940035075808000190b02d100b2054421403101100100260900310104c2e842d40c011204008100a1541e011420028400e1064a681600c11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 948511294 1250 948510044 948510061
    0x105030405030c0a110f0d0c09020c0f0d09151107031101050c070b0d0501080318010305040212151510050909040302150903031504090807110303040f14090c040501080a05 75
    0x40d0f4111406a00c10700000700300f0300c1401e001030340342c1000c20b83d60651744441000900c1051958000081c0508448040401042d1540e50041020f44111001d4850000800c0012410003040e8203103540090710000c0280b10a8800000b00703009010581445200d441c0312800c040d031690380c0b511000d0205034a030146480c582e4021011190f85044600a640c480c58070741140c1580703500312403468a09140390000100300c1d01c000204650050710410b000c0040b80424400450180c0001802260420300000d04216030000400c001c4034a08881c5005441c13616000b0381500034849400b00e254402c0403031f0811680902d8001040303400c0001c05442e9841c1682d543d003000c0e031901c1d03103e49059080511900810404050200240d030090300e4a81000d10f62184500c00c0005031000400d0152000784100002400070b0385040080145070005400e480c20156204092880d108199028410310601620001180e02e88501790f603520211036a07406051909110009101c03090091000202c9586d400109a045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 948512544 1250 948511294 948511297
    0x4030510050a39050f31030305030a02030a0b04020d09032c041d030309070e0a150e1312020a050f03070503041502070807060c02010e01030b060307030b0114030906070207080f0705010503040503 85
    0x84410044141e131140651814640c007291003d68003200e505070724480b103c0800d9910346c0d07811240c02d562041e08503107451110f40029407000d8000c10200b592400d1400b0f8507250b1b4005850710720100c120003c2d07408003604029040e08001e48106482c5000041d010182c2c40740c00da0038030300311401500c000420080e138204100220003060380c40c1d5501c0c40f001c41081080c03040003690200b1b8600701d1300d040e03d0503120420b905059074159098140c0d114420785050080b906007503c4d5961206c8132203803444600101d0344a0840f28040114041d0060b0032004440301484800c02808008282c001c3c0154500140c2ea124592039005034003502c00305000b11000041f1031882003141402405080c404d80756071640c0ea2001412150701c500d0704a000c10035020a656031036010703200714440e070f0300b0150195140d581d44180440040c04256410f60501c14154140e440d50004a07020310320402c43c11000300722030700301403001a24204c580d50041c211980203a105400c00c07640800d403d01150001e00303000d5180d490328500710303066 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 948513794 1250 948512544 948512557
    0x3140601270e0c0c070819060c05070c090204140d0b0406021b030a1e050a020d0e0d0c08010e1e0715120e060a0b010905031b01030204030510050a3905 66
    0x1080c114400380025200d0b040001e11128013404200c0b140256905804d03a102e04a03c00c2482034016900007007000708001d500041e20080c580e01e01185000746c10f40c0da5401d032201c141c02001400340e0100b0305004144000c11800d00e4443c0481c0c0e602e0a80c20241d841c00f000950041c0020f0501e134010441580c28081c0c41c0030500e010640c5c4068035102c60200300300400d20100108d04e180c4401031503c1030004180600100e5524114641c06445c044104400580d0060210320300142c000300c6142ca01e6020982d03000c507020103080e42c20f0000c02e031032a09a40036450913035031a0100706800d204515a070280c04001881000300d40e284140b0790301c06c82c2000b1050301c0030720705082e0002c071560400c003107c18544c4000c5081ca2264920103400c0066a08100044440c0324030780c0a0950150701410ba10406500d07601c0000801ca41c051501525040cfc89aa4903400c103c21000c0b0400311507222402c0c01046951170003070749d40102080440490201c11102203a9182c40520f220b9400c3c00e00c184501c58801d03102c3c1040310325 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 948515044 1250 948513794 948513809
    0x6050307120201080a0e030910090f030303140c0901200c12010b100827010f020c160b031311280302030601090e210706060e01060314060127 62
    0x1855541d1600c49402944070a8200c2c00664034000081000503948104014401558004d506002164090111260014451383c00f8496212070016212841e461190041c6110b6540404e106d1452001c0101240c806000840c010805100c0082c0c1070340d12844102607145002d0111020b4000045040d0418840c0101c054203c24004458012400150801c00c44860306232813a100d0420350040071540300e001500e000481c00c01b020079480310a94500154250081305000010f0300f00034560a620407030f4018588185a90442285038135148600110311004001000d200c51651928519005541c0741d0108010101032000840c1750482d00c50304030301600445a8040c0c1003200c018070780b06041c85807203031004a2080c4154800462000c9040c001e40080220810051040140f1000001c1d18800b6250840d05000c07402d01204020581901840009290550985965504200004003034a40c030140310302d024400b15051001e6070341e000102458050f580c00039042080c03c01ba843c41404002c5500551 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 948516294 1250 948515044 948515053
    0x1205061513050307061e020109030e040e0c0603090607080f04051f09020901083403020d05030706060f060305060f03061b0d023103202110110f1c060503 67
    0x6071150300f10100c0e64085251440304000003581c1b150880c241c60440300b00a001a0ac84511804141007981040031b2412030301042d11061070004000c20115001101c0c28041c684c00304003400360301600211400e810200c0040324010a10b40741e19007030303520b0000d140c0c500480052185d54541128035548a148842e86c002c1c840f039102d50703441d0302182d030301e5440c0b1010040c03029020021030003034191609030441c0340b400003001c0107903a8a10f03000c001241d50026001d407220f000400ca150300044503446410042d21804000ca400141085401070803610020001401416509045c030307200c0d900007407050740c0100780e0051400da0800003010f03295a402400400d560090000c1031921402c1d000d120240035004424080c400d203100c4008820031051090320024040c0c21003c1041241018071905159042030003411040800c204400545503010508a069400f40c0024114002c1000980100c240c0381c1c030000199401c044183e0200204e0f4441d003080c1e1185601200c6554801e050103400000041c0070060584 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 948517544 1250 948516294 948516299
    0xa0b0a1508150d12110312040206090a0b030907080601210605100b07081c0b060316050708040e040c0902130b090a080d081803041a0a0309051209011205061513050307 73
    0xb8440a1403411258000c50980e0043c0b0006045c00020b0b00c95130464140307d0300545d15141c00f4461280c0c410f11009402c10a6054049844e420000c000c5014007042401040caa42c80c000c0b0840c140030701a00440c03440307940400c0802e90328460700c5000920f5500314000240340e4441c0c03003103c254006140e0104054460114000e0b0510140700d025107808480810240308210715003015a084500e907510031580150240b001c103003140f0f81e0303003403543d68500c6a0411900d00402ca403600382294026a00c0b000a40341078208008c10800414200700c018282c0c000194107046080b000c0300030101e100d00490300c003008081080603165940b210316000030080d110641e262508600001030141c18201e400c0741c000541a010410310040c0041106c007240c8a0000c04043d8071503102118526038004101d4408041d05d070218080492014001500042c800c0f50728140d0f6047d640b0300151541800f981c40622080c0383c0000c101a40d180c0c07107aa400030400300c1d1040740c0c4d54001c2c040c4101c045000c0b500b11940602c01c50704007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 948518794 1250 948517544 948517553
    0x309061c0b09100620190614040c090c080f0a09020102100c0e01090b04030503090405040312150602010b010207030b04081e04080705040b04150b03090a15050a0b0a1508150d 76
    0x500c002d40342e49907652058001d81e084110800d2401c144030700006e600407588a41c0d6170040e00002003500d4815800883d03002003034a980c087c00d070002e450503120318422100070024030740288a9003007040b50030300303001170540780c11849180241c00007002c145440d40c4031380c4160110381c402d0040541800a0399400c112040040030001c04218841007194040380f5a510b011031403903200381c1950304a0752b1010003980342030101803d0002400016001302d081c82080d085a0485000c98000d50a0000341c001130401c0315854407900030700b912850080103055412400040c40402c1c132940781c0507480340c0c2145101b130343e600c1000e41c070a2901d1440001181c500c0d00100e0040358081d800b0a000040328412907060040190260822003200d0043ca4002005104400b040040f04003000c0a507610001c0c1d502690400d40440e1038000300b4484683c0c01c12620740e5240100003010b180b034416007008200940308010b01509045541c0120102c0c0702c0103806101c2543c000400903203030710380501c40558001d852181c0341d802d645070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 948520044 1250 948518794 948518821
    0x9060103270204050601141911030d0b0a17071a27030c09010608071202040f0b030f090d09120501020706062909010c1e02030a0c0e07020309061c0b09 66
    0x40c02c80c400c030309001c0460040d41c450510170f03910103240000309140007919107041c0e07003007880041150f081c0038031400b0a00c1c0e0100180090582d11a601c02e0210345a51540100030300141c8580000324030741e40710001d102c0718440010318902511070310810f0041c2d2218107062840c0742c1c0120303039503446402ea807441c15020310305401c640424005000d0341102c22080d01401001a11082405014001402240007902c03045c400c0d01e000301900304071100140340503150b00d5039a41c06041031f000484504000001d01c0090303090800303100d60001c090806032154400250009241e4901c1b4440d020002d1110f14640302402000e41c11035442e2a44224108400c99445d2292075020303000c2110920045c120007110b0944803660403c850407085c050351003c414112941c0c60301100824072441c200000b562242d03410050724100010001c280c040d001c00c40303a0a140c81c08054644c0070041c60382085400c14400b055407501d0b00020340d81d0f50350302c0346021404801c50f100014014551891075a81c00001207041c802c040c0c404c0329 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 948521294 1250 948520044 948520121
    0x90307052808030304120305070c0605070f02100b03120f09041401090509010b0307061101200702030706020d080708180709231b070c240f03090f0209060103 69
    0x11208040070355640311240c0c890104480180c90440a03440c0400d00e980309920440c0d00914609210021080c00e8854400711501244c190340414810b10f01605503a8041050425807004100c040c01040401d1011030340795900322149102c00800410300021104d05c078000d440464001800800c60a101720f40d0801020341e00713100343d0300c10b1450039011805a200600400300382c44000381c01091a0703071030454125070050340e90f0b28803081e655a40d04080d01ea404c29210b00826561441e0a05448559138010141070651070391015056602541e00c8007280c681014045600c0189420400d00c42d55600054205115182172051001d0189040204400c5280c0d802040783d070054004000080350ba00f26081045081070720401401244440c2240b610f95001d80148040ca1290401d40d50030307030b51140c1c0d8501d500d0300291070014600000c0c1d902e014444d032281103502802e03c5441e06000040c21512026082c1c0d08d84207019000b10741100000d4466402900704c1c071860301c13400c0f5034204440c40c14401d2820180d12035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 948522544 1250 948521294 948521359
    0x80a03062c010303052104050109030e0907080c031305032205120303010504050405480d030309020103110d02090f0a0e0f0621030c01141501030209030705 68
    0x86648101c050160560011550300c00e4400c000243d0a545055406800000d241080003007110b030042d00e200090f901080c065403080f03001090401181c81c0c060140000a450540100100720410034441d40c000c54440c1c04c8050000569680d8580c004446a204d508000103403c03440002031421852403c0e4641c60388404079044003080c4951220100040be10a8820700c8105610500042c00a8501907020542280c454011102c90441007440001d5801642c0c820505c14454103034180079030103000003150160459003c0a90394080c01100045070790b546e01202504042d9a559000c00b11b90013607210048096241074071588409828041e01e001c0d41c003849419008014600029159003000801c0106603034a111103070742d1940c0c5036044014414030041005510001b0500320800e0303d4600d209c2c055138141c0b10b001442c2e44000301c081250a4036110503150401949a50030071405481c50502c8980100003480c015a0741c8000c0c40010385020b1407034100b41c1d0704c43c600308da00d80843d07011011050074a0030403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 948523794 1250 948522544 948522569
    0x3180f0302030d0f06080a230d200109021c060f0e030c1002041a0c160e0a0506030d200106090e010b100509061e0712080a150807060f020307080a0306 66
    0x6081340b1000f9213400d84110440c40c1c0c064849030300083d00c2440341d540a24800840e00045501920340140340c014808420004510a40c020700050410094a6044054014020301c1606060f6001c1030452007158608140d8000c100900c074100b00c15500040c4007000c08250a010109024408a40f40c1d4048606141c80c0e03c02c000b0380b0440c05216009650440f1111814140485142031440e0084d600a4001e09a03500801e2450010300c4e492851030b401903c0300c2583c94074140340898281c011640003910162090b8060340e92054401da00080c0845031481107440e2080e001014510a4090400b6401c080c04080c1049002044240c055216422888045a40c0140c17000305150684040c810110881d4009004000407051050500c80d5891007000700e10006107130020035120008a141004846400507110105201c83c030031881c002c040394014643c080c852442d1034624155528041c44c49084144040250307a62002e5000348191107540c1e4101d51780541c2c4609850005005040c18000d90008051 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 948525044 1250 948523794 948523811
    0xa0c050f2404120503100801140609060613062f03030702120406050a0e0d02100305090c0604050303030a230103060912030c0e09040813030602090a05040b09010603180f0302030d 78
    0x503100c21071400b86070494400b81403080510f008851650004140180307240410308001900c0030244601f202480722103080312000d09204040207507841002d40494451341060110801c2280550494000c075600ba0600c07689c160a0085002c0c22407211170300300100344208582c0008035140100003144a020580d007a07404000e01c5011402c030303d010314010385000500a03c02600c2e070a000d5402042014401022158900400d0380081d039100250a410030020791500c0500c0751210080201c100c0c2400700300c031b1545c00c1a0404010070358034040240740001d020789500030520040204042295201c08407207041d40b00c3d41c0c43e8100b01c0080e1101c4441160034003581002048002e02c00d10070450362007010351340c1caa6600d0030101000580d590181045d20409400c11800d100250f20f00800401184100409a210b004203000c00c010f100e8180c2c4003034061400e00265a000d90340f910002c90540d10b4501300021415103005080e145c1829216009003003c2c020400d207020f254000000e061240100c0d003080c0140030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 948526294 1250 948525044 948525103
    0x114060108040309030318032a06020304080309040b0a080706020d020d0825020c06181302070f080c0a020402130801051302010906030b0f03070f2115020a0c050f 71
    0x2002c850240020302807100c1440041d100d0060107003843e100d1900400702c59200e8940343c0e038a102d5141204201300721500139000b04503001d02600000c00450001c1e604040c40c00401030317182d106034500740741302d00d9070340c00300306a82c0c3d4079451000c0192907880c04980c4180d4961001a58880e52040c00f00051f04c178100c0b20040c101e1141d010f01d440b41d0350300706904030302d2006140304e5100b003070000300301c031040d80901000b18004e034075900068014415001d4800d80f20414075014401d01c5528030710030102003401048820082000c01d800e0414595000c00c10070342c1c1d200602101810f000103581d00a5000d80002400c1d90350030104107001042d905190000c00c12901d40d03000d001c04a0194880c000d0110b0300302c50041000500a500203003040f50090031029400b50100d000074240b02844c1c10801164034151003d00070080523405107c410380e20501100c500e02d0f22510303080100216111781c0c0081c07940006401820030301c04c040001400343d00c542156107140c0340e00f140c0c075100c0e0031707020ba409045c064480c551a82c12 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 948527544 1250 948526294 948526307
    0x5090f040807110105070b09100e030426070e010b030f0901020c100f0b060c0d020c060705370b071e08040204090c03021519031103160e060c01140601 66
    0x1150721110322442c00080da40d4154251078203940080c148503080c419540418503203007002c0e119140060180099640b19104a401c40f0403e80180115600c107020034001302414101c00340c7d150b291840012540000b0080706032074841c480e00724548910f145400001d1051819018602599282650251584d54950141c2c01c07801810020041c0740d0114080e010b803003002c1d50241d024800c610741c004c2950f6402d0f80104406a201c0050785000b90301c81c0b003018481c2c680c14041c2c027610b054220742481c42c0143c1512065510190300040c40c2721500e07440f030580d440066400194541c151034510544e52040303541482a05580221441800300c1c07200c100703440b5402d503075078400c101c40041519100b00c90786403031302400003c107103040c0e04903403800001c2c1c000300259443c2e41c0c84011043c00c816501e0303030300c05004040804410400d9401020b040c140601d140d00f41c2240015203500c016005461075000440c041c3c2100c1c0042c420000b0364018000054034074403440107400000300c41313816588040f01501c0303500044852 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 948528794 1250 948527544 948527551
    0xd02090f010f1b140a11030f010603121202090d1b060819050c04030212071a030708240a0b090a0b0702061905070c23040501030b13020310140105090f 66
    0x4011000d5a5140030481c150241c3d00c0c1d000d254080011280000c41c203140081001050b600310349403040c00041e515003003005585090f59040280400c82c80c5694100e564015200c8180c140072940c00014072001040c0d050751500f41c0028044041c03214141401c502c2180300c0003a045841d030402c0d402290300c80c001d0090710b0003104000540e0896003a4840c1ca400102009070102c9601c0c602007200001682d079802c05052180b01d64409406000e16101f0841380b11003c030824044010424400c2100c000e0300410074580c02950140c0e11414030101c0c03084811100f0340400a1070303101ca101c1d80003240500c0c0443c040d2524030f5013038400304245230300c40d090001c0318010034100a5000c081005480300d054884d2065034119003040c14200e0400f4842d90324001042040d4000410702c49007810f058101000103406c240c903201047d5410481b55055488220840400401b0b0088241c10000b0030001c54608025038000509284010003c4404a0200300750b4400207102d1148601c00c1040800c2e07040c481a0403844c007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 948530044 1250 948528794 948528797
    0x15120212150a0e070f06110f06060d290c0a0f050f1819030602130509090607031109180702010b15030f2d0a0c0302040f0b03090f030d02090f010f 64
    0x381d0b2402c560601600081800070014020150b000408216182801d0060000f03503c2d90800300150030441890503074002c4d9642415400181030080710340301e83d0442c0d498690842440c040d040500071010f2808880e00c143c40c07910104440400040c0311408001d0300c01244180e46070007500342034800449042c0148008954034103001c001c8041008080d03030000c600c0b40c0c006001c61010b6580c018500b024201d495205541054001880d21a001441d402d90005000201d031054000d092210b41250f0782d15009140405050751509240000401d24007078440c4080001c0520400f5002180d590380400c200751104c4000d5801c010844501d40360100604180382d1030248114110358401006e441b511001170f000520500c0045a2954035000010b0101100400c28078291a10f041c921011000c45589082060401d1f1040c8000d10903180201071000440700c125612a8407a203514000900385401c0700b40803500ca11000480c2e070300f208071075006001401c10480701c8290b120300c502c0041d5101d100020b02c00c070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 948531294 1250 948530044 948530083
    0x705010f021504050106170106090f0c0c060506040b03031b120702010c030f030908040b0a0e0625020402120907030c0f0608010b0c010b03030a020a020a09020a020d1215120212 77
    0x2c08585481c050642c1c002e000700000b083c915601d0704007032012032000e030f21500280d440340c030b0921000341c0070b00883d60741c80c41c4840708003d90080720800800407041e00d000201180e80b500c000c900d05540301d0b004100e0040c1e00509a0399036020f071040c0301e100c0b81003031305080d01180618070207040144a81d07001c0c1d9043c550180c544500d4034040b40e40441c2d02c0302911800c9810302d5034615134074000c9401440900060728540a28036a5118602400341ca410011882c0d02e100f0601005441214501c83c0b0300b56100ac0d801c40c07580060680c0f60710018010b40100c9101210500800080000382c80000031810112400f9101da5210161103000f041c407629800d0007004081500e03140108240110783c030040074441300c0e4900010304407543c5000281036030b001c0b0302400d005a03c414140300641c54265441001011080011446c10410f480042c0d01c0c0d00c8450180300610449101c0c5203005002508548185804500201c803030580742e5129080e4a10031000c264090340d510401240035440010f19010350514015841 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 948532544 1250 948531294 948531313
    0x403020d0323030f040b150a0501140d1a1201020906070f0221030904060501020a050a030305070516050601170307050a080c0a06020d06051c030e090615030a0e0705010f02 75
    0x780c64201c0900311082504440ea021903440b00e5214010358050120340090a90038106810400402000901206881000c8070542c0d41d05544500a440c1265001c0c00e1428240e0ba5a4181103454002d42200b10100c50805502c50815009560741180320541141e0790500c0e03599181381e96080303018001103240c000004104240100c1c00440d80110054801001c0e03602e00c0036000d40000306900690303011443c660011964029514050044c0d2026050a10082c0b182d00c006440c4c0560b035000080003e400d041e80d0743c0c08614000e200d40300b29051180d84c0c0304c1000c1c018420f4640300340d9a030401d00c40d075140c280e54881403103100d81d0003208490016070094014075440110341c44911090740103112140441c81440503480c00201203002401103203684010000b1154070f04014808071a0b0359044501c000001c04a800000035003200418065000984149540796500400304841c200c90780c0c1c0568403090007108201c440907840e0000002510700c00181d442c443d07a100c005481d698103100101001d60030040b040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 948533794 1250 948532544 948532547
    0xd1404140607080d1407080117031b03041d0709050f0d0201110f0f010b2e0e0f04020c100f150618030c241806030207021219060e030403020d03 63
    0x54400c8500401c1511301e0044200c42d81021034200080340310b00d6040744000c0090454000a2150040204100104458110b1103101d070b168441c800380d01600c0c5c010f2504800070490200309550207455804814804072105d0000f43c41001404c0700c0c0b120015a103840003041604200c05910008080034011501e10340950b030042d41e42d194084912407092089244c6400d0480c0104141c0e89841e00900000401c41404000e200980c22908801d4524628602c2c44400079140c1d003003101305011041c81c02e20001007030040002c0c01c0c1c2e09912002588a030020803d0802c030074011403620ad03210190101004001c1600300d00b1800e540450780700e0140b0b889000820031045e80941030a0b0584e03038455605080d016226a1022114103d0742c10500b420a080b2511100011500d11100842041424080704c10310320001c524211041a000782c030304160b00440c3c40801c42d12082d40c1524079081e80c00c1640c40c02e00403460028a10701e00701034280d44071803e02c03c0006107114084101d50680b50050210b42c0181c095460 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 948535044 1250 948533794 948533797
    0x6071a0f1504060522152c090c2202034303020a0908030307030209012c0105070218070302130501031109060306270a0e010c09090c0201020412050d14041406 69
    0xe00c034508031b40350640d8099100000540002400c030000450440c0700881c079848140d000c0001e410081e1400c02410b01c204c0c42000691107007020750440759411160f91810b00e100c090704a08001041c030600100034040b418100b4105007030a00011000d09140c14041e421446121045a00010158540103000401c603882500188854050f608101c0e800c1c2e0b0303454044501d16401180d010300040d5001c2649101581c0c8481a0303c0342141444008450a0b101031500918513641c620040c14898000344200442d250f407042e94400c0b181140030b03101d55141101024010307600039032551032000313040b040c08106980030f44a841c0003007121036056030800f800035003400420361018180d00d500c0010031032002e4100c4642030810515a0b0744140c02c800605140b80340e5070540ea140a003e20131a41400d40b05215994052120001c48904440100301240c0f1004203a009121f40e4020902c10b110151b1840d00340000050900c900c09165070349c0c0c0141920280001c00e5a000d5409060a0120785440841c0645410700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 948536294 1250 948535044 948535099
    0x1606050306060f041d06090108030a120b030d0306030b060102150c0703020a02030303010810060506040302090a05060a1703090901060819020a021504061b020706050906071a0f15040605 81
    0x2810b0301e18010380d102014049801130340c0164441d004503100039401e070f104543c3d4250829419a081c02465042c0b00c1c01e43c1d00c0f80112400c4d58100018010b80160880c0d20341c01c034008600c0040c0c15180010f84030346005000e041d2900040e10034566000206031907520000313848989016600ea00c1c081740c1c44020840b0b01c190300034001507003144100140d071005a50184011802800404020819900090203000c2958115440b10348207036010721041000d40c5403000c0e001e51141c0783c20380018007680c618000540019058102c0c209404400c0c000e0041e40100100a10001c441120781030707440d82e41c810003150b01141c00ca910449116240c00011042c0c0700d150042c3c41d004055006032540e004600d06060f49040d01128243c2c0c9503078588548000040c59038181800460803072006d07011541c01c0100180c00c9110341031140307004540000700c0b80c092052130817080200b6a10340c00b0312000c0f414101003000075403e06a61541f80c13005001c40c10043c40c07406200b58811540c01030710002c40609454103402810b207a05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 948537544 1250 948536294 948536299
    0xc010e0c30010204060908010f0c0c030507060e0118030806120706200d0c0311010903080121060207050c0a060306050901050405041109090f0d05030c0d0b01050f0c0a0b091606050306 80
    0x1800d07070085000c1c00038101525a17a690311845c02d2400164a0948805c081d01040f114a442031a084599200d1020140249c050400c26500e032032500c0d002c0003c1c0051a07128003194030308007000039201038a1360100c61040c0a5a83d0400e90340b124010403460a26880c420708241d4880c45e0100001c0c1d003e031600741c01450000d078400182c2018501c55a040110000500d0009099040764204054002141881d00c8420000821189032180e034050428541030084400e10400f160404440b006c00040e0f680b000f5034090000c1d505e40f116403419070b0f40c3c3d040e4031141c58424911f44a003c59054424410241111001051704102d6403800c41404010700d409001034450820410074011103403981c00c00c141c06852560020011041855801424054041e0028041090410912510515040640743c0310222554005030702e0300c5a8005840c01d10031070aa0b90b071030740c1c0c0110b2144041000031604101842c000d984942c81903441349041620b803201c0311a80c4406559014050003460b100d60041c55228501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 948538794 1250 948537544 948537619
    0x606010f051624150f15201f0504020111120301050f010309120e0307090b030a110117040308010f1202010c0b07090f0e10080609100b04200c010e0c 65
    0xa205810090315001d00c1c0620046400a20811185c1e8955031132070000c1c003001040940c0910604002445509600310103504940e12020074481e42c8802c1c410710048540b449076291181241200c40f00c00703004c085400f41d0200b40d41040d200c10520001c540f104448860714401b91540e82084204410000f20684142c105951000109c0c0020007a15506c070005442c0c0e1a5420700d0064103041506c0c0940f160400482c0f1400c0100c0c1a24507140000d1b10200a680107250b002c00412000040318400300351803141803c039038100203000074141c01c40d4a03d81a210100c034541030036074036091f0488141142080081c00121070781c01c258080703076107051400c1c0c00a80b54604141c00507a50807124500c521540c0043c1e0048034201b0902c0b4851044c8072070140100000030143c100e03498400340303803074690a800340017040396500e440c0026203940d110303800610a040c0018450001128894290007d504011415600c543c6803266030381c542d55001400ca8400c0500030801c0340d01b003a680058184c00304c405003884003a07500b0b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 948540044 1250 948538794 948538853
    0x20d0c15111206040c2f030705030301151803020609060315060d020c010605030d0e060d0f09080c010506041103060d03020102070609060506030d0908072d03050606010f0516 76
    0x48402001140c248007801000c0b41020010002211806240c0c40180314041e00c00782c000e0b00d482c590071b00c101103450030a030f4660002c0c2c1c144c10b4114031234240014090b000010010031701184e030440940000c94075a441420351903c1040e00100d0300d94600000c0c0d4400c0050010800074a0321200569215450644131a001010711022079420740260703c1c001c541d982c02042c0003444500c00d104e4040200300480051820900703104020f0b10049640caa01c034000c172130015001c050450341e500120b00403514160104050300080c20021825002140342c5800e550800011812074034042c081c0c0340860041d608554038503120b0030100305264168040441c20341d50244011808200f061050744007a9010302c10106107460140c040604000360350700ca88041c4400c40d0002d0004460024550f01034a02e0061000600c080e04682c49088030100c000502d0140e142c60340c044104400841d809029400a0704d0340031b13a21040102c00d803142c8c091072019000f1942c1d0721410f000820724036442e1203405410302c240c3c10320440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 948541294 1250 948540044 948540071
    0x403032f120405040b040b10050703050705060702030a0816120b0a03021905191a090103060806071701051c020f0a1701020309060705070203190c08030c011b020d0c15 73
    0x1801601c0c0703003803040c801250812490a06004e0b040303075008116004c0041c0d41c0342c5400110020101c500e074200300719000c90603504150241003120901600402200c0003468900d070029501d5215000d175100248002d008218481864241400301c019582c44208c0740048402c132204c0185110001c0b039901400c22034000000d0388034912400e064141c1d502941d8400c505040900400c143c0d10f881017107440c42d2118080000b6155a1507403000101142e90481e5500c0c3c0c00700040f40909600e40040b4076a00500e070900c0081c0e80c0000076130f40f500c41215140d1410740c0c1d0762000c1048003245c102010085185033f504034001032038480d007061b50440307004115410094490001c0c03220010101e143d13a505030340c00018400c1000c07082001c0c541c0501d40749400ca15044141e400f0940750f401450000402c004000f507011704110024151710041c021304030841351501050740d840d07800380142c01100f0364079503051992101c2c103620105018440c140c1c01c1d240e4041507074442d5034140000c030032001c403040311a40d2040081a0203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 948542544 1250 948541294 948541303
    0x80a0f0537022206031106090607080306041407050d0501140d02090a020408071502070504050105060f1305060a2a02010903240c030c02100b09010626040b1b0403032f 73
    0x40ca840f2600050341c03411881c10b0201035503a44031441c07140c003091014140981d510011203101c3c03a0300a510544a0b00c40c41d000c10050000024140764070010441000441a4044082c1c40012503014081c0600d90fa100305541d441817901040c0c0b40c01c000c2c1c0c2c400d22009420f0990a4a80044003101d00500d010341d80d180150402e801c40d001640000501460200410360401240001c2e00c0c00300c904100651502e00003030f85500c02c1e403003d920a084085500801c282440807110300a04016240942e2103031400001001d48074a0b149144044030f6400c4c0d652402559401c60241c05079045e1140705d83c0c14295211a450344034a0b6a912514448000b0b50345001e81c0c82d0302413007124a00585020508407a246006420601d4040070a41850318201904449a692030202c0f41140d80e10304000c840e01400148042004c100d072041c0f102110f00940501c02006085a80340e071048265100a10020441c0c24030748001e44500d100103400a442c0100d51156255200c40582166007104480a0042881d81929041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 948543794 1250 948542544 948542599
    0x50c04060c23030702130204051f03022a070806061305041b0e0403030c020a031418090f0609251b060507030e0c0d0b04080310080a0f053702 62
    0x6940020400c5021410560880a907001b480300c0194100b500700004078001107500d42800c0e410703400808050219a01036812518485202200c0d85900c49114104e100703608001e9860b000a071054039400a01945e010034601c2c0201c100800c2c11249181100055016120150050701c6552020210681c40b0036120b40840043c0641d0119000d5854a0b0601800300d030754a411005c1903401003111900065801520282c252840e00c16813902c40c644c108445201c807400d2801c17240c11000d8001840002d840601c0000c0c4141d07412240880c49943c0c42111000120201080c1c908405449040081e01d6001d00c2110200c210140f550186201e82920740c102039600030384800c00030070755403101038800440c01d00c01701800030419600e079004c2525903502d28090f00402032028015160100128135480059110340c0c0041a87e04100c40e40d22903c0e04080d40a2100404216110310515200399600c07144110184000b031001d12410b200c0480c4604010502405641c0032070340250381a0b00c442074003401c0d603d078108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 948545044 1250 948543794 948543863
    0xe070801091a010506070b0709050409082d04091116120908030f0a030209030109080c06011503090c030f0516150e0303040305030a110a05010f1e050c04060c 69
    0x40c00c00c41c505040100b071148048512081421000500642e02e610045034401c0780e0020060741c0690b9051422a550700b4140c000d01c0d4828101060304007441604000751042524402480c12140e41181304180144003610903014081000d010800c04500c0075030115880940303040302a07203003030301064042e4040a200c0308202d981100000d04400d6550380009420007030f0010700019407a00080020b00030303c034012070948100301758002403c02c1464500f9004440d095512203100b41c2c03115962501c00c4d483d04801d0140d40104802c0030b402100700780c82409101e4565801208030508542903403a0305584511200342500c292240f000d22284c0084c440a055004048142801010b4001083c0052050203441d500d03511992040c8410301c00b045010040300c3c6004503034140502001a088c46441c144981c01c0c0001d04594038203011ba25002400f50846003549031282245c041c80300a00759414100c1e801900c801125035814801809500d000d0401900c205000710041d0581201c9114a0020200601341842 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 948546294 1250 948545044 948545051
    0x70b0a0306030b07030c12090f0506040f030807031a1201090f050f010c0507020a0e07020a0609031d1215060a0306090c1a0a1d06040e070e03100c090302090a0e070801 73
    0x4240300040701184d401080d11700c0d06000d407920315030005018050070301c41e8616480c2e603001c4803c10000601c3c46101516881030503200c2600d414141110309900007a4141d010070b000d0340004202c180f0074030a0700c6074061003144148104481078144445021010001c0c5103d660f14030152001c181441d0091aa10344550b0040c402489912843c50a50b0394100341b41090000500000e030050350365209141c1580e44078810701303c055607140380803450208080c501400503494000c11100b45640280520025500403056403180d00c42c417400c0c8020402c0d00016000c182d0046007440d40003c00b450505900300748010300c005c40e003c1c0c40b52540d80172610100d000f1261840c1c149400c04c498030700292020110448440c140f03061001d6034502901c03410150b46c8074506900c068203008050f9403110b05403005403c03000300034005454100c4015210742c04504a1900c02d01c2496090740110b80c0a000e20141110745946500696180d0741c2400340c9810040e05910209072905201c05a0340001c009140041c0106030012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 948547544 1250 948546294 948546299
    0xa0c08120a0c09210620030a0209010905121b0102010e0f07090522141f0b190617060301020f0c06010936110a0f0f090218060a02070b0a0306 62
    0x10f48040c00582c04000c60f41c030250b4505030300303482c06007030356a446410210101d00121403203100103145102010481010704044240b16269400ba40640b200390b4080e2180c030707100c0392202e0030001d440c143d20300d004900f03a000001082c0e4020728481c188200c8601800081b1b8034008010701c59050000a54a0600c19030069a040000d4042c42c01103c0d000845c804046002c040d150000b25516641800b021340b02001c1002e20b0b0300c1390030307042090200000c00c5030305950194000d2807111000c4c08071910028450300710b041d440025641c0c02a060b0045034000d8642d03120084009511140d1048010085a0715540c233005040c40220954014462856541c0183c58158100902402220140c8140140c5050307901c0c0b501d0804a100f060802100b806040a40c519000a14002d148c1041c1001041e070405801c840c00100030850522000644d2000e4504410035030700c4400c120b0480c040e44141040b110303003082d00c000341400c0210003464080940d20580390003e440300001034050740182129030002e9943c1004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 948548794 1250 948547544 948547547
    0x52b1e020c01151511071d04290112080d05040b06100c0b3904060e0904020f090606130e0604060504020a0c0818130e210a0c08120a0c 59
    0x1607a02e40c0a100d1003d104090401c0702d124401070503013590304180110000c404603400010403140c801406075010345c126240b03035803802a001120a99084030140040e07449036040b4009005151b0442c1034603c552205070303290011a9501080c0c80c0c5081e07520010402600740c404c08140940d038825030080b07844500b01e0500e40203014a15210082d140204103050f00500000351140503040c2c0c200100002d5180b18a0040d9106150001a0b42002410b0001c0d10382c4000c124041d03a0180046807415181d0b810014000401e11082d4581114001e501c081c440300400365501e0b00800b425045080580081c0c1450310380004041452501d4011401d641002d004011061502e405100c019003400e076025800c000b4920006803080d1178100009003038000115805410f80c5a003850407030204001400044a65840c40e5150003c3c108640d80303240c03074084d0092542d005e01005c00300000308030751034140902d0000700e000221000c1d110458100e8425004100c01240060088141130080d10070306d4000410307900c030140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 948550044 1250 948548794 948548801
    0x110a110a080307030c0803060406081006080c01031401030b0705091003141602100b030c040c090f05030111030118060e040b100e07231603080108010c052b1e020c01 72
    0x50703201c1e94410040d80b00003950110302010131580c0b00403065100d45074503000602406150b0003440302881412410001e0b00c3d49500541f08a424200a40e1300d100303884801101591085c0710300c0050481413100400010703011f000c5c56940280d02c2d150141c1081c0002d400076503880d0103a144800007a444000b41520309980c0c0080940001100d07092150a4041c0d800180d2101c00d0a040b525403a55034902d50600c5883c148040240302c0401001000840d520800203003901520303000300c441c1450203c2c40481e11781030501c1500e015181402c0c1140c00e6070b281120801d0b0151104510b034149640710f01c00018000780c413001181c05180321b62010b018504c3c18001001c0c030803115901004c1c2c582030007010320510707540144010003004000c1c2d100c0c4403482119124070126103d401d100140e664501d00902c03083c03590024109050b52000c2c0300900c0307544215801101d081c05689030020314000d0070140174061000c44804503d00180303901d40404c945500d04503401d404019084860311490b00090000701d648002c3c070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 948551294 1250 948550044 948550049
    0xd020f03071a0402010e0301020f1804020f070b07030902040f0906050a0605100509031e0f12090102100902030a0c06050c0f1c0f0908010504050a020108010b18040c110a110a 76
    0x1001903003000402c1d01c442040d00c82100211007440076541c003140c1564464040b09010780c0018000799543c1213188061900d0703901802e005041c140710030840039200d1606008445010604992403410a901601c0700c100301e000240052090554580a060060711507020700002e240852600141051060038000b00342c0701d004140007400d0b45861810300c0142c1d20301c0240c80d009111442c00c3d40c1c07103d40e110082494010028100b80181d4402c1ca040c4100184c0002d03c80c60036601c05043d01c0400001705a0307c000d500681c4d80d514003503042074103514401c00843e03211841d007d000408035103d000f181c2e16115400d10302504500001540001c003035514840c10000b0201c0c0080d600e00a181042611444912014030b010b0341d8405c01801204100165100d0200c0c100a804050000c00072410309141540e0b542d2002d490480c0421b5004000003003511903070301610015100e00946112615205c401c000c000d0403084441d906002440110a80c2c0c20406c2000003180ca00c5428404017101caa034040181d01c2c030035507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 948552544 1250 948551294 948551323
    0x5010603020715020a021516140a1409040f09030201090c050d030207030b040204090b07020a0c0e0c031603020f04030f060608071d07232205010509010e06040b03090d02 74
    0x4100c10b40000703640e0240f03254511115500181c0f2000d003881c4c00c03405d0621034000c014600404800340320703d10400c560a001b00795038540392500028020486182d071070056824100200740248a0309000200401c028104034600820028850204041349001c0350000101036005039980e011110402c40481300d04005000d088404441586203580c000350f44002c107010051050048401103011502e803034110004050380b020440c8001d00e01450f000395542c482c580c00703a8003131007142d1300080d12007000d14889000ea50942c501c54610358558090703290a032954010041010f500300640e54004c0308180190000d103214441d070510354a01414194140d44190b000303400c55420488041211640f00b440c040300b4003039500b02d91201b0b90344004064620844080d59000b920320607845400075503401200501c2803404080d0710b84948221417640f00da01c2e0510b8094240840c3c03041109040b80d40c007440a0110f0480018400f5140544607000c1002c0c0e070b00140c1b8454450380c890325141da5115014490641400e00310f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 948553794 1250 948552544 948552547
    0x114030705061605030f0c1002070221100e0102040513050f04200301140403171b0f0d09082701050f030702010221070e181803040314100501060302 65
    0x404000949828040c400c051180200040e5650b9600891450080058025044c0c948601210300520496480140198494041c0c40d644100742030143c420303194510340280c080b4580d0340080c0000d260080460034500c41c0341c0308001d40190030b10054000c0140c945040030016032124944014005001000b40c3c91a140ca42000700700014400c245046940c000e412039909011441d00142071401014110354540e0075500b00303510340b00c2c207401c0380c440d04e800b40d8443d42d100c6011103007000c4240c1749400d0036954051080c0f03c0310500d44614403214080c00c00341c0d032035a1060303180620803203d80c41101e150038401c5070b1ba0007022a40c06c60b51203a810700003400e507601f01070f088016442100000c02c00c0c40b8842c00e80e010104003101048946100354142d480d000103002d10ba80b50300c0450001002c1206007242d210000480c2a03081d000f181c2480038410000b0801c050160303000740c840d003800342804200c0e20928285803106200000201c6e01030300d103020002d031616026220140c192a00e650603184140c210b60b091500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 948555044 1250 948553794 948553829
    0x3601030504150216050313061101020304030c02101b0c03050f06100312090902161203021c05090a0812040302010b10020a1103030d110c070504090f1205040f06021501 73
    0xa6040442d0400084048016564a011001401449070110010b0454440414519401c0c051303442e41c0800c0e912a9200c01c403607840c1e0601914280c0c48110340c0140066080465000182045040601c00040b41d007040d040640d022110315002d6040c44405a80600c0f049a0070000d01c0014000d110341d4402c03490103050b6501d001c54001003c0665031000601c11035060b40040a02840380b200003024024049081d541c1d2040c104c1c03800b1280300c1200056071850040d00b181d00f142c50180c421218551080107182590003c41552a4000c0034003d01c146242d0192900346c0001800c2c14008050642900d000880a8206410000d08440001304001c1c0101c00c205800d01c041900002da443c0303603a40c0b00c600b41c841500c0d10004a82940030b0103800b03416682c103081c0d5091810324544054011040f01000311489103954000b00000e490300e4180151a0309280c0145d038000c02d00d0820300c0a4003600900b049850190344101c072000381d012590000340160018045000c840c8803040c3c01500500d502032440a8201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 948556294 1250 948555044 948555053
    0x70b06030a17030406060314011a0108090c040906020c01050915090106050d0b070e03121e0301050d0b07030e06180d080103050d120f0608150f040b18033601030504 72
    0x1c1910b40c10910300c00201c0083e0812085420000146031712070703030030201812454a80d9000e42030100070801c3c0311030440c1d61414154030941001c1d214010500007068040c0c0c40e10180001081d09240c04d4409e50380030003d500050b41c007401100c5c0a42580401040c045038100c0016108480190031800140d04103c420042950b510f00c080510740d402c500004c0b10340c0c407101000c0c0e408000600c00302e5094060a0b4000300c03c5c0d100c0c0c00140070312808c00050a040705001610340c908030b01c024001c45500550300000e41002c0740c48130303041c60b602034414180001c50b512940110b61a0000803180b01d0b0341c0c004689031645a42501b4007008019044500702450503506540c0c803503807034500300c0401d48108898401180e820079440d4000c6e9602c83e00306601000030301d4940031415120003442c61021481049c100c04142d507106100c4190f03101d260065202401926281c01e03620005001844542003440140009038408801114110b400f65507012a25001c454444128000d02c080407945414145440c0030800402c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 948557544 1250 948556294 948556313
    0xf060b130b030c07032a12020f0f1903022a2d1c080d05010e100303090e100e16030b0d0201051e070f05033619090908070b06030a 57
    0x1d581350419031b0241c8800d000c030040085a5859111081d070302c07010b0b82d000340004003a20b02e090b020b550b030940340d00c1c88810880e03c1d0780e100900030340341c0c0a0380704184d403035503080c100c0b00c110811501c42d1064a501c0090380d150080c2c020110100701d0130511302d141d01e218007031408101a80c100212180740c0101c450703040503c0b0f102501300c0120035001d0350440380d2280c4c01007601074690031920350003003074141c450308541080f00060409001d0036005004030008500c1d0b490080c80217200b120361590390000c1590420340c0100080783c000d007600e1205000508080f0707007040c101700c119100750045001c003408901c0f8100e0003015100e80c5c0d0030090058890b03009142c051f0342d008080f01c00d101d04bc07805500caa00c0000c02c4810309849071a00c081d005100c0f40449804000c80031004004010521103040304207009420754200b5041c011442c1c1004582c5e440303601c9582c0c2803192803207141030003603403400c0042940c84807a4001d4804031501180d10b2100000c000301080051066590440419001054081c91594412040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 948558794 1250 948557544 948557557
    0x810181104050c0c07030501050f090c03071509091b090b090d1e020301180507050118171c02070801060f26030903030a032a02120a030f060b130b030c 66
    0x140d8070b800025040708016822101c1c201e5003a0100ca40d50b43c0da07030500b1402086c007a151591291803000108403a0345001451000d5000001c001c0d140e8507140c0000000c1c3e003004590480c05110400e82c00143e1003a0a00c501c580e03840030300210000f001800c0b5801801e0078040e401c04a03110b28140090700c40c07520b40d200c611582c7d0b40e03c607203d04410018a903103500690884e0f0303002035146d030820f50b40f80d98002d8401c1208222600c65422a00c1e0181c94000548143e0f0207000a10b40784803c034442007268481d0742c00d65614030f40301041992034060038402c0010410840e0b0780464050381c0b101904101403c0240300e228000c203c0e400c107a115550030310014000030b1101c403000c0c940c4440c28fd15000380c0c100d014011222501401422030b0f0781d454501101502411002e1540780c03000c011341c04070001b92440614000c003640c0c01580909524070382030f40e9041494008030030000c20580d0340c0c03190850300ca031f980c801d0002509140c4003268030303040c0c900080d9060101d40d4002481c20300d010300c148401d0007502002d0714034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 948560044 1250 948558794 948558799
    0x19261305010c0f0905311e0605010f030504031106040309210503040b03040c0b030a0c030c0e030a030f090302090a02030a05090a030914010c02063622140108101811 72
    0xc411b100c1415050f41101c08086820205890110201e80646250302c022a2000809494030002c030743c007039941e01190b119109541c042600445c2d840c51180c40303603100700c1d44648030381043c003c1c0c00e0119001c01d01e4150115030440120703003203910a010382510145440c14030006100e100e04800d50940c4c1d0701d5224062481164a800d0011001c82d08024941070083e01a05d40c0c40d01c0380391245071105562014012050410001c6031a2514041c5124421010800403040c090000c2110031903940c0c04581c0307a1032400071141000560640403005a0314402e403d4003402071244050f0300c900f8640310b80400c6501c084c00201866010700e0b24080065041040d810490395914820300e651405140181c610800c0e406000350700503800a00580003d0495a40c4450000b0242480c1c2c40d02d1640c48440c141035071000071a03588180303044c00030010204468a48030000600c00e602161413649030605075000542a00880180c2c0c20207200b8200311400c0d031250388100220036150703481c115500d4842400700c0728100603890 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 948561151 1107 948560044 948560059
    0x31401060e0f0906010509100e0312040e0a0e01020d0603050109030305100f0b09030c101d0406030c0618030215040302010e0619261305010c0f0905 65
    0x900980c01401c554080800c2d0020400c0951000f00403504002d0100f18042c12625000700040400c560394403000d1100c05005c2c100340c1002d040300c5400248082c2803208205100d6071071100340d0040c400f00c1000680404a0404a02911498012a41c1181007040010400205601035101c0b075010340d0f400c110580714400001d0460440e403182c100d0482e000042071044103401c2008240b0b6140040803109004610300209414148501c100004190302d04000e010084020034010a2000221741c2003055505560302c0000401a9000d90000c1040c0503080c50800c1d2107507030020014640040a03c001d200008034101640d50207804100e0026400c1d103c50351713103814580e09541780740709049022600c103010200c085821200d07851107004145c0d1950501e12050a0307001c90b0710300809242d034101c803120419050139130135a10705051490401a1320000a0700481c0c2c81645102964821039100 = true := by decide +kernel

theorem cover : BRFrame.Cov 948381294 948561151 := by
  have h0 := BRFrame.cov_init 948381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 948381294 ≤ n) (h2 : n < 948561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
